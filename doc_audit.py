#!/usr/bin/env python3
"""Staleness gate for the three project documents.

`README.md`, `DESIGN.md` and `STATUS.md` are the only prose the project keeps,
and they are read by agents as if they were receipts.  They are not: they are
written ahead of the work, and they drift.  Every drift found so far has been
one of three shapes, and each is mechanically detectable:

1. **Phantom declarations** — a doc names a Lean declaration that exists
   nowhere.  `DESIGN.md` §9.0 carried three such names for months
   (`systemFactor_eq_fixedQueryTranscriptDist`, `oneSided_hTechnique_adaptive`)
   because the paragraph was written as a *plan* and read as a *receipt*.
2. **Phantom paths** — a doc (or an audit allow-list) points at a file that has
   been moved or deleted.  The H-technique gate sat red for weeks naming four
   deleted modules; `U05` moved two modules between packages.
3. **Withdrawn claims** — a phrasing we have retired reappears, or survives in a
   corner nobody swept.  "CR18's deletion rule is a rewind oracle" propagated
   into eleven places and was load-bearing for a whole interpretive layer before
   anyone re-opened the PDF.

The gate is deliberately conservative: it only inspects backticked tokens, and
only those shaped like Lean identifiers or paths, so ordinary prose cannot trip
it.  A finding is either a real drift or an entry for `DOC_AUDIT_ALLOW`.

Run: `python3 doc_audit.py` or `lake run docAudit`.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DOCS = ["README.md", "DESIGN.md", "STATUS.md"]

# Trees scanned for declaration names.  Mathlib and the sibling AC package are
# included because the docs legitimately cite them.
LEAN_TREES = [
    ROOT,
    ROOT.parent / "abstract-crypto",
    ROOT / ".lake" / "packages" / "mathlib" / "Mathlib",
    ROOT / ".lake" / "packages" / "batteries",
]

# The leading atom of a tactic/command declaration.  `\s*` inside the quotes is
# not cosmetic: a leading atom is very often written with a trailing space
# (`"ac_compose "`, `"ac_simulator "`, `"ac_context_left "`) so that the
# pretty-printer separates it from the following term.  Without the `\s*` this
# scanner silently missed seven of `AbstractCrypto.ProofAutomation`'s sixteen
# commands, which is how a task card came to assert that `ac_compose`,
# `ac_simulator`, `ac_context_left` and `ac_transfer_property` "do not exist"
# (STATUS §11.34).
TACTIC = re.compile(
    r"(?:syntax|macro|elab|register_simp_attr|declare_simp_like_tactic)\b[^\n]*?"
    r"\"\s*([a-z_][A-Za-z0-9_'!?]*)\s*\""
)
SIMP_ATTR = re.compile(r"register_simp_attr\s+([A-Za-z_][A-Za-z0-9_']*)")

# A `syntax`/`macro`/`elab` header often carries only `(name := …)`, with the
# leading atom on the next line.  `TACTIC` is line-based, so without this the
# scanner missed `ac_compose_simulators`, `ac_context_left`, `ac_context_right`
# and `ac_transfer_property` (STATUS §11.34).
TACTIC_HEADER = re.compile(r"^\s*(?:syntax|macro|elab)\b")
TACTIC_CONTINUATION = re.compile(r"^\s*\"\s*([a-z_][A-Za-z0-9_'!?]*)\s*\"")

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+"
    r"|scoped\s+|local\s+|nonrec\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque"
    r"|axiom|macro|elab|syntax|notation)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*)"
)
CONSTRUCTOR = re.compile(r"^\s*\|\s*([a-z_][A-Za-z0-9_'!?₀-₉]*)")
FIELD = re.compile(r"^\s{2,}([a-z_][A-Za-z0-9_'!?₀-₉]*)\s*:")

# A backticked token is checked only if it looks like a Lean name: it must
# contain `_` or `.` and consist solely of identifier characters.  This keeps
# prose words, notation (`Δ`, `‖`), and type names like `Par` out of scope.
TOKEN = re.compile(r"`([A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*)`")
PATH = re.compile(r"`([A-Za-z0-9_./-]+\.(?:lean|py|json|md|toml))`")

# Single-capital-letter math variables with a short subscript — `Z_A`, `H_min`,
# `Q_3`.  The documents quote these constantly when reproducing a paper's
# argument, and no Lean declaration in this estate has that shape (they are
# lowerCamel or dotted namespaces), so this cannot mask a real phantom.
MATH_VARIABLE = re.compile(r"[A-Z]_[A-Za-z0-9]{1,3}'?")

# Claims that have been withdrawn.  A match is a failure: either the sweep
# missed a corner, or someone is reintroducing the claim.  Keep the reason —
# a bare blocklist decays into noise nobody can adjudicate.
WITHDRAWN: list[tuple[str, str]] = [
    (
        r"is a rewind oracle",
        "CR18 Def 3.3 grants a free domain-membership probe, not a rewind: "
        "nothing advances on a refusal, so there is no earlier state to return "
        "to, and an accepted query can never be un-asked (STATUS 11.12).",
    ),
    (
        r"deletion[- ]rule rewind|deletion rewind|completion(?:'s)? rewind",
        "Same misreading under another spelling (STATUS 11.12).",
    ),
]

# Names that are legitimately mentioned but declared outside any scanned tree,
# or are prose that happens to look like an identifier.
DOC_AUDIT_ALLOW: set[str] = {
    "lake.env.lean",
    "audit_surface.py",
    "doc_audit.py",
    "audit_baseline.json",
    # Lean *keywords* that happen to be shaped like identifiers.  The docs cite
    # them when recording that a proof uses none of them ("no `set_option`, no
    # `native_decide`"), and no declaration will ever carry the name.
    "set_option",
    "lake_env",
}


def declared_names() -> set[str]:
    """Every name declared anywhere we scan, as both full and base names."""
    names: set[str] = set()
    for tree in LEAN_TREES:
        if not tree.exists():
            continue
        for path in tree.rglob("*.lean"):
            if ".lake" in path.parts and "packages" not in path.parts:
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            pending_atom = False
            for line in text.splitlines():
                for pattern in (DECL, CONSTRUCTOR, FIELD):
                    found = pattern.match(line)
                    if found:
                        full = found.group(1)
                        names.add(full)
                        names.add(full.split(".")[-1])
                        break
                # Tactic and simp-set names live in string literals, not after
                # the keyword, so the declaration regex cannot see them.
                atoms = TACTIC.findall(line)
                names.update(atoms)
                names.update(SIMP_ATTR.findall(line))
                if pending_atom:
                    continuation = TACTIC_CONTINUATION.match(line)
                    if continuation:
                        names.add(continuation.group(1))
                pending_atom = bool(TACTIC_HEADER.match(line)) and not atoms

    # Module names are legitimately cited in prose (`RandomSystems.Complexity.PRG`,
    # and often by tail, `Complexity.PRG`).  They look exactly like declarations to
    # the token scanner, so register every module and every dotted suffix of it.
    for tree in LEAN_TREES:
        if not tree.exists():
            continue
        for path in tree.rglob("*.lean"):
            try:
                relative = path.relative_to(tree)
            except ValueError:
                continue
            parts = relative.with_suffix("").parts
            for start in range(len(parts)):
                names.add(".".join(parts[start:]))
    return names


def known_paths() -> set[str]:
    """Every file, by full relative path AND by basename.

    The documents cite files both ways — `RandomSystems/Dist.lean` and a bare
    `Derivation.lean` — and a basename is a legitimate reference as long as
    exactly such a file exists somewhere in the tree.
    """
    found: set[str] = set()
    for tree in (ROOT, ROOT.parent / "abstract-crypto"):
        if not tree.exists():
            continue
        for path in tree.rglob("*"):
            if ".lake" in path.parts or not path.is_file():
                continue
            found.add(path.name)
            found.add(str(path.relative_to(tree)))
    return found


def is_retraction(line: str) -> bool:
    """A line that RETIRES a claim must be allowed to quote it.

    Without this, correcting a claim in prose is itself a gate failure, and the
    only way to pass would be to delete the record of the correction — exactly
    the amnesia this gate exists to prevent.
    """
    lowered = line.lower()
    return any(
        marker in lowered
        for marker in (
            "previously said",
            "was wrong",
            "is wrong",
            "withdrawn",
            "misreading",
            "corrected",
            "correction",
            "not a rewind",
            "no longer",
        )
    )


def is_absence_claim(line: str) -> bool:
    """A line that *reports* a name as missing must not itself be a finding."""
    lowered = line.lower()
    return any(
        marker in lowered
        for marker in (
            "do not exist",
            "does not exist",
            "no longer exist",
            "phantom",
            "drifted",
            "was renamed",
            "deleted",
            # A line REPORTING a search that found nothing is an absence claim
            # too — "`minEntropy`/`H_min`: zero hits outside `.lake`" names the
            # thing precisely in order to say it is not there.
            "zero hits",
            "non-existent",
            "nonexistent",
            "no hits",
            "none anywhere",
        )
    )


BASELINE = ROOT / "doc_audit_baseline.json"


def load_baseline() -> set[str]:
    if not BASELINE.exists():
        return set()
    return set(json.loads(BASELINE.read_text()).get("known_stale", []))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="record today's findings as the accepted backlog",
    )
    options = parser.parse_args()

    findings: list[str] = []
    names = declared_names()
    paths = known_paths()

    for doc in DOCS:
        path = ROOT / doc
        if not path.exists():
            findings.append(f"{doc}: MISSING — the three-document rule names it")
            continue
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()

        for number, line in enumerate(lines, start=1):
            for phrase, reason in WITHDRAWN:
                if re.search(phrase, line, flags=re.IGNORECASE) and not is_retraction(line):
                    findings.append(
                        f"{doc}:{number}: WITHDRAWN CLAIM — {reason}\n    {line.strip()[:140]}"
                    )

            absence = is_absence_claim(line)

            for referenced in PATH.findall(line):
                if referenced in DOC_AUDIT_ALLOW or absence:
                    continue
                if referenced in paths or Path(referenced).name in paths:
                    continue
                findings.append(f"{doc}: PHANTOM PATH `{referenced}`")

            for token in TOKEN.findall(line):
                if token in DOC_AUDIT_ALLOW or token in names or absence:
                    continue
                if "_" not in token and "." not in token:
                    continue
                if token.startswith("_") or token.endswith("_"):
                    continue  # a naming-convention fragment, not a name
                if MATH_VARIABLE.fullmatch(token):
                    continue  # paper notation (`Z_A`, `H_min`), not a Lean name
                if token.endswith((".lean", ".py", ".json", ".md", ".toml")):
                    continue
                if token.split(".")[-1] in names:
                    continue
                findings.append(f"{doc}: PHANTOM DECLARATION `{token}`")

    # A withdrawn claim is never baselined: reintroducing one is always a
    # failure, and the whole point of the list is that it cannot decay.
    fatal = sorted({f for f in findings if "WITHDRAWN CLAIM" in f})
    baselineable = sorted({f for f in findings if "WITHDRAWN CLAIM" not in f})

    if options.write_baseline:
        BASELINE.write_text(
            json.dumps({"known_stale": baselineable}, indent=2, sort_keys=True) + "\n"
        )
        print(f"Wrote {BASELINE.name}: {len(baselineable)} accepted stale reference(s).")
        return 0

    baseline = load_baseline()
    new = [f for f in baselineable if f not in baseline]
    resolved = sorted(baseline - set(baselineable))

    print(
        f"doc staleness audit — {len(names)} declarations known, "
        f"{len(DOCS)} documents, {len(baselineable)} known-stale in baseline"
    )
    if resolved:
        print(
            f"\n{len(resolved)} baseline entry/entries no longer stale — "
            "re-run with `--write-baseline` to shrink the backlog:"
        )
        for entry in resolved[:20]:
            print(f"  + {entry}")

    if fatal or new:
        if fatal:
            print(f"\n{len(fatal)} WITHDRAWN CLAIM(S) — never baselineable:\n")
            for finding in fatal:
                print(f"  - {finding}")
        if new:
            print(f"\n{len(new)} NEW stale reference(s):\n")
            for finding in new:
                print(f"  - {finding}")
        print(
            "\nEach is a real drift or an entry for `DOC_AUDIT_ALLOW`.\n"
            "Do not silence one without reading what it points at."
        )
        return 1
    print("\nNo new stale references and no withdrawn claims. Audit passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
