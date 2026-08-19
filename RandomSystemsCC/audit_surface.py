#!/usr/bin/env python3
"""Audit the RS -> AC bridge surface (`RandomSystemsCC/`) against a baseline.

Sibling of `RandomSystems/HTechnique/audit_surface.py`: intentionally a small
syntactic guard plus one Lean query, not a Lean parser.  It mechanizes the
checkable half of `STATUS.md` §11.2 for the bridge library, which is where
every current admission lives:

1. **admissions** — every `sorry` / `admit` / declared `axiom` under
   `RandomSystemsCC/` (including `Symmetric/` and `Frost/`), keyed by
   *enclosing declaration* rather than by line number so the gate survives
   ordinary editing;
2. **statement surface** — §11.2 rule 5 / §10's G0 token list checked on the
   *derived* public construction endpoints (`Pi.mulSingle`,
   `Gamma.ofPrimitive`, `protocolOfPrimitive`, raw `.act`, `statDist`, `Adv`,
   `Delta`, `ZMod`);
3. **performance escapes** — §11.2 rule 4 (`maxHeartbeats`, `maxRecDepth`,
   `native_decide`, any `set_option … in` override);
4. **endpoint axiom footprints** — §11.2 rule 3: `#print axioms` on every
   derived public endpoint must report exactly `propext`, `Classical.choice`,
   `Quot.sound`, plus `sorryAx` only where the baseline records a known
   admission.  Run with `--axioms`; a module that does not build is reported
   as *unaudited*, never as a pass.

Every finding is compared against `RandomSystemsCC/audit_baseline.json`.  New
findings and disappeared-but-still-recorded findings are both reported; only
new ones are regressions.  Regenerate the baseline with `--write-baseline`
(and say why in `STATUS.md`).

Usage:
    python3 RandomSystemsCC/audit_surface.py [--axioms] [--json PATH]
    python3 RandomSystemsCC/audit_surface.py --write-baseline [--axioms]

Exit codes: 0 clean, 1 regression, 2 no regression but the audit is
incomplete (an axiom-audit module failed to build).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BRIDGE_DIR = ROOT / "RandomSystemsCC"
BRIDGE_ROOT_FILE = ROOT / "RandomSystemsCC.lean"
BASELINE_FILE = BRIDGE_DIR / "audit_baseline.json"

# `#print axioms` may only ever report these three for a closed endpoint
# (`STATUS.md` §11.2 rule 3).
FOUNDATIONAL_AXIOMS = ("Classical.choice", "Quot.sound", "propext")

# Files whose *whole purpose* is to name the plumbing the surface rule forbids
# elsewhere.  `TypedFinite.lean` defines the embedding itself (`Pi.mulSingle`,
# `Gamma.ofPrimitive`, `Primitive.act`) and states the generic lifting receipt
# `primitive_constructs`, self-described as "an integration test, not an
# application model"; `TypedFiniteChecks.lean` is the permanent generic
# carrier-contract regression target (`RandomSystemsCC.lean` docstring).  For
# both, exhibiting the embedding *is* the content, so §11.2 rule 5 — which
# governs application endpoints — cannot apply.  Nothing else is exempt:
# `CBC`, `Frost`, `LiftingExample`, `ResourceLift` and all of `Symmetric` are
# scanned strictly.
SURFACE_EXEMPT_FILES = {
    BRIDGE_DIR / "TypedFinite.lean",
    BRIDGE_DIR / "TypedFiniteChecks.lean",
}

# --- token vocabulary -------------------------------------------------------

FORBIDDEN_SURFACE_RE = re.compile(
    r"\bPi\.mulSingle\b"
    r"|\bGamma\.ofPrimitive\b"
    r"|\bprotocolOfPrimitive\b"
    r"|\.act\b"
    r"|\bstatDist\b"
    r"|\bAdv\b"
    r"|\bDelta\b"
    r"|\bZMod\b"
)

# The construction judgments this library exists to state.  A public
# `theorem`/`lemma` whose statement mentions one of these *is* an endpoint;
# the list is what makes the endpoint set derived rather than hand-maintained.
ENDPOINT_STATEMENT_RE = re.compile(
    r"\bSecurelyConstructs\b"
    r"|\bApproximatelyConstructs\b"
    r"|\bConstructsForAll\b"
    r"|\bConstructs\b"
    r"|—\["
    r"|\bRelaxation\.eball\b"
    r"|\bgameSpec\b"
    r"|\bpropSpec\b"
)

ADMISSION_RE = re.compile(r"\bsorry\b|\badmit\b")
PERFORMANCE_RE = re.compile(
    r"\bmaxHeartbeats\b|\bmaxRecDepth\b|\bnative_decide\b|^set_option\b.*\bin\b"
)
SET_OPTION_IN_RE = re.compile(r"^set_option\s+(?P<body>.*?)\s+in\s*$")

DECL_MODIFIERS = r"(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+"
DECL_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
    "structure",
    "inductive",
    "class",
    "axiom",
    "opaque",
)
DECL_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    rf"(?P<mods>(?:{DECL_MODIFIERS})*)(?P<kind>{'|'.join(DECL_KINDS)})(?![A-Za-z0-9_'])"
    r"(?P<rest>.*)$"
)
NAME_RE = re.compile(r"^\s*(?P<name>[^\s(){}\[\]⦃:]+)")
NAMESPACE_RE = re.compile(r"^namespace\s+(?P<name>\S+)")
SECTION_RE = re.compile(r"^section(?:\s+(?P<name>\S+))?\s*$")
END_RE = re.compile(r"^end(?:\s+(?P<name>\S+))?\s*$")
PRINT_AXIOMS_RE = re.compile(r"'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")
NO_AXIOMS_RE = re.compile(r"'(?P<name>[^']+)' does not depend on any axioms")


# --- lexing -----------------------------------------------------------------


def strip_noise(text: str) -> str:
    """Blank out comments and string literals, preserving every position.

    Positions are preserved so line/column numbers stay usable.  Stripping is
    not optional: a raw grep reports `Frost/Group.lean`'s three prose mentions
    of `axiom`/`sorry` (lines 135, 148, 183) as admissions.
    """
    out = list(text)
    i = 0
    n = len(text)
    depth = 0  # nesting depth of `/- … -/`
    while i < n:
        ch = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if ch != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if ch == '"':
            out[i] = " "
            i += 1
            while i < n:
                if text[i] == "\\":
                    out[i] = " "
                    if i + 1 < n and text[i + 1] != "\n":
                        out[i + 1] = " "
                    i += 2
                    continue
                if text[i] == '"':
                    out[i] = " "
                    i += 1
                    break
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


# --- declarations -----------------------------------------------------------


@dataclass
class Decl:
    line: int  # 1-based line of the declaration keyword
    kind: str
    name: str  # fully qualified, or `<anonymous kind>@line`
    is_private: bool
    header: str  # statement text, proof dropped
    header_line: int


@dataclass
class Source:
    path: Path
    module: str
    lines: list[str]  # comment/string-stripped
    decls: list[Decl]

    @property
    def rel(self) -> str:
        return self.path.relative_to(ROOT).as_posix()


def path_to_module(path: Path) -> str:
    if path == BRIDGE_ROOT_FILE:
        return "RandomSystemsCC"
    return (
        "RandomSystemsCC."
        + path.relative_to(BRIDGE_DIR).with_suffix("").as_posix().replace("/", ".")
    )


def module_to_path(module: str) -> Path | None:
    if module == "RandomSystemsCC":
        return BRIDGE_ROOT_FILE
    prefix = "RandomSystemsCC."
    if not module.startswith(prefix):
        return None
    return BRIDGE_DIR / (module.removeprefix(prefix).replace(".", "/") + ".lean")


OPEN_BRACKETS = "([{⟨⦃⟪"
CLOSE_BRACKETS = ")]}⟩⦄⟫"


def statement_of(lines: list[str], start: int, column: int = 0) -> str:
    """Declaration text from `start` (0-based) up to the proof, proof dropped.

    The statement ends at the first *top-level* `:=`.  Bracket depth is
    tracked because named arguments (`(T := T)`) and the construction notation
    (`⟪R⟫ —[π; ε]→ ⟪S⟫`) both put `:=` inside brackets; cutting at the first
    `:=` outright would truncate every `—[·;·]→` endpoint before its judgment.
    `column` skips a same-line attribute prefix, which is not statement text.
    """
    text = "\n".join(lines[start : start + 120])[column:]
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in OPEN_BRACKETS:
            depth += 1
        elif char in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", index):
            return text[:index]
        index += 1
    return text


def scan_decls(lines: list[str]) -> list[Decl]:
    """Top-level declarations with their namespace-qualified names.

    Only column-0 declarations are recognized (the bridge library has no
    indented ones); namespaces and named sections are tracked so the reported
    name is the one `#print axioms` accepts.
    """
    decls: list[Decl] = []
    scope: list[tuple[str, str | None]] = []
    for index, line in enumerate(lines):
        namespace = NAMESPACE_RE.match(line)
        if namespace:
            scope.append(("namespace", namespace.group("name")))
            continue
        section = SECTION_RE.match(line)
        if section:
            scope.append(("section", section.group("name")))
            continue
        closing = END_RE.match(line)
        if closing:
            name = closing.group("name")
            if name is None:
                if scope:
                    scope.pop()
            else:
                for position in range(len(scope) - 1, -1, -1):
                    if scope[position][1] == name:
                        del scope[position:]
                        break
                else:
                    if scope:
                        scope.pop()
            continue
        decl = DECL_RE.match(line)
        if not decl:
            continue
        kind = decl.group("kind")
        matched = NAME_RE.match(decl.group("rest"))
        raw = matched.group("name") if matched else None
        prefix = ".".join(
            part for entry, part in scope if entry == "namespace" and part
        )
        if raw:
            name = f"{prefix}.{raw}" if prefix else raw
        else:  # `instance : Foo := …`, `example : … := …`
            name = f"<anonymous {kind}>@{index + 1}"
        decls.append(
            Decl(
                line=index + 1,
                kind=kind,
                name=name,
                is_private="private" in decl.group("mods"),
                header=statement_of(lines, index, len(decl.group("attrs"))),
                header_line=index + 1,
            )
        )
    return decls


def sources() -> list[Source]:
    paths = [BRIDGE_ROOT_FILE] + sorted(BRIDGE_DIR.rglob("*.lean"))
    result: list[Source] = []
    for path in paths:
        if not path.exists():
            continue
        lines = strip_noise(path.read_text()).splitlines()
        result.append(
            Source(
                path=path,
                module=path_to_module(path),
                lines=lines,
                decls=scan_decls(lines),
            )
        )
    return result


def enclosing(source: Source, line: int) -> Decl | None:
    found = None
    for decl in source.decls:
        if decl.line <= line:
            found = decl
        else:
            break
    return found


def following(source: Source, line: int) -> Decl | None:
    for decl in source.decls:
        if decl.line >= line:
            return decl
    return None


# --- findings ---------------------------------------------------------------

# A finding is baseline-compared on `key`; `where` is informational only, so
# line drift never trips the gate.


@dataclass(frozen=True)
class Finding:
    gate: str
    key: str
    where: str
    detail: str

    def as_dict(self) -> dict[str, str]:
        return {"gate": self.gate, "key": self.key, "where": self.where, "detail": self.detail}


def scan_admissions(all_sources: list[Source]) -> list[Finding]:
    findings: list[Finding] = []
    for source in all_sources:
        for index, line in enumerate(source.lines, start=1):
            for match in ADMISSION_RE.finditer(line):
                token = match.group(0)
                owner = enclosing(source, index)
                owner_name = owner.name if owner else "<file scope>"
                owner_kind = owner.kind if owner else "file"
                visibility = "private " if owner and owner.is_private else ""
                findings.append(
                    Finding(
                        gate="admission",
                        key=f"{source.module}::{owner_name}::{token}",
                        where=f"{source.rel}:{index}",
                        detail=(
                            f"`{token}` in {visibility}{owner_kind} `{owner_name}`"
                            + (f" (declared at line {owner.line})" if owner else "")
                        ),
                    )
                )
        for decl in source.decls:
            if decl.kind != "axiom":
                continue
            findings.append(
                Finding(
                    gate="admission",
                    key=f"{source.module}::{decl.name}::axiom",
                    where=f"{source.rel}:{decl.line}",
                    detail=f"declared `axiom {decl.name}`",
                )
            )
    return findings


def endpoints(all_sources: list[Source]) -> list[tuple[Source, Decl]]:
    """Public construction endpoints, derived from the statement text."""
    found: list[tuple[Source, Decl]] = []
    for source in all_sources:
        for decl in source.decls:
            if decl.kind not in {"theorem", "lemma"} or decl.is_private:
                continue
            if ENDPOINT_STATEMENT_RE.search(decl.header):
                found.append((source, decl))
    return found


def scan_statement_surface(pairs: list[tuple[Source, Decl]]) -> list[Finding]:
    findings: list[Finding] = []
    for source, decl in pairs:
        if source.path in SURFACE_EXEMPT_FILES:
            continue
        for match in FORBIDDEN_SURFACE_RE.finditer(decl.header):
            findings.append(
                Finding(
                    gate="surface",
                    key=f"{source.module}::{decl.name}::{match.group(0)}",
                    where=f"{source.rel}:{decl.line}",
                    detail=(
                        f"endpoint `{decl.name}` states plumbing token "
                        f"`{match.group(0)}` (STATUS.md §11.2 rule 5)"
                    ),
                )
            )
    return findings


def scan_performance(all_sources: list[Source]) -> list[Finding]:
    findings: list[Finding] = []
    for source in all_sources:
        for index, line in enumerate(source.lines, start=1):
            stripped = line.strip()
            if not PERFORMANCE_RE.search(stripped):
                continue
            option = SET_OPTION_IN_RE.match(stripped)
            if option:
                escape = f"set_option {option.group('body')} in"
                owner = following(source, index)
            else:
                escape = PERFORMANCE_RE.search(stripped).group(0)
                owner = enclosing(source, index)
            owner_name = owner.name if owner else "<file scope>"
            findings.append(
                Finding(
                    gate="performance",
                    key=f"{source.module}::{owner_name}::{escape}",
                    where=f"{source.rel}:{index}",
                    detail=f"`{escape}` guarding `{owner_name}`",
                )
            )
    return findings


# --- axiom audit ------------------------------------------------------------


@dataclass
class AxiomAudit:
    footprints: dict[str, list[str]] = field(default_factory=dict)
    unaudited: dict[str, str] = field(default_factory=dict)  # endpoint -> reason
    findings: list[Finding] = field(default_factory=list)
    progress: list[str] = field(default_factory=list)


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args, cwd=ROOT, capture_output=True, text=True, env=os.environ.copy()
    )


def print_axioms(module: str, names: list[str]) -> tuple[dict[str, list[str]], str | None]:
    """`#print axioms` every name against a built `module`."""
    build = run(["lake", "build", module])
    if build.returncode != 0:
        tail = (build.stderr or build.stdout).strip().splitlines()
        return {}, "; ".join(tail[-3:]) or "build failed"
    body = f"import {module}\n\n" + "".join(f"#print axioms {name}\n" for name in names)
    # The probe lives in the workspace root so `lake env lean` resolves the
    # import; it is named recognizably and removed in the `finally` below.
    with tempfile.NamedTemporaryFile(
        "w", prefix="cc_audit_probe_", suffix=".lean", dir=ROOT, delete=False
    ) as handle:
        handle.write(body)
        probe = Path(handle.name)
    try:
        query = run(["lake", "env", "lean", probe.name])
    finally:
        probe.unlink(missing_ok=True)
    if query.returncode != 0:
        tail = (query.stderr or query.stdout).strip().splitlines()
        return {}, "; ".join(tail[-3:]) or "`#print axioms` query failed"
    # `#print axioms` wraps long footprints over several lines.
    flat = re.sub(r"\s+", " ", query.stdout)
    footprints = {
        match.group("name"): sorted(
            item.strip() for item in match.group("axioms").split(",") if item.strip()
        )
        for match in PRINT_AXIOMS_RE.finditer(flat)
    }
    for match in NO_AXIOMS_RE.finditer(flat):
        footprints[match.group("name")] = []
    return footprints, None


def audit_axioms(pairs: list[tuple[Source, Decl]], baseline: dict) -> AxiomAudit:
    audit = AxiomAudit()
    by_module: dict[str, list[tuple[Source, Decl]]] = {}
    for source, decl in pairs:
        by_module.setdefault(source.module, []).append((source, decl))
    expected = baseline.get("endpoint_axioms", {})
    allowed_extra = set(baseline.get("allowed_axioms", []))
    for module, entries in sorted(by_module.items()):
        names = [decl.name for _, decl in entries]
        footprints, error = print_axioms(module, names)
        if error is not None:
            for name in names:
                audit.unaudited[name] = f"`lake build {module}` failed: {error}"
            continue
        for source, decl in entries:
            actual = footprints.get(decl.name)
            if actual is None:
                audit.unaudited[decl.name] = (
                    f"`#print axioms` produced no line for `{decl.name}`"
                )
                continue
            audit.footprints[decl.name] = actual
            if decl.name in expected:
                recorded = sorted(expected[decl.name])
                appeared = [axiom for axiom in actual if axiom not in recorded]
                if appeared:
                    audit.findings.append(
                        Finding(
                            gate="axioms",
                            key=f"{module}::{decl.name}::footprint",
                            where=f"{source.rel}:{decl.line}",
                            detail=(
                                f"footprint gained {appeared}: baseline {recorded}, "
                                f"now {actual}"
                            ),
                        )
                    )
                elif actual != recorded:
                    # Shrinking toward the foundational three is the goal.
                    audit.progress.append(
                        f"{decl.name}: footprint shrank {recorded} → {actual} "
                        "(good — re-baseline)"
                    )
                continue
            surplus = [
                axiom
                for axiom in actual
                if axiom not in FOUNDATIONAL_AXIOMS and axiom not in allowed_extra
            ]
            if surplus:
                audit.findings.append(
                    Finding(
                        gate="axioms",
                        key=f"{module}::{decl.name}::footprint",
                        where=f"{source.rel}:{decl.line}",
                        detail=(
                            f"endpoint is not in the baseline, so it must be "
                            f"axiom-clean; extra {surplus} (full footprint {actual})"
                        ),
                    )
                )
    return audit


# --- baseline ---------------------------------------------------------------


def load_baseline() -> dict:
    if not BASELINE_FILE.exists():
        return {}
    return json.loads(BASELINE_FILE.read_text())


def counted(findings: list[Finding]) -> dict[str, int]:
    tally: dict[str, int] = {}
    for finding in findings:
        tally[finding.key] = tally.get(finding.key, 0) + 1
    return tally


def compare(findings: list[Finding], baseline: dict, gate: str) -> tuple[list[str], list[str]]:
    """Return (regressions, stale baseline entries) for one gate."""
    recorded = {
        entry["key"]: entry.get("count", 1)
        for entry in baseline.get(gate, [])
    }
    actual = counted([f for f in findings if f.gate == gate])
    detail = {f.key: f for f in findings if f.gate == gate}
    regressions: list[str] = []
    stale: list[str] = []
    for key, count in sorted(actual.items()):
        if key not in recorded:
            regressions.append(f"{detail[key].where}: NEW {detail[key].detail}")
        elif count > recorded[key]:
            regressions.append(
                f"{detail[key].where}: {detail[key].detail} — count rose "
                f"{recorded[key]} → {count}"
            )
    for key, count in sorted(recorded.items()):
        if key not in actual:
            stale.append(f"{key}: recorded in the baseline but gone (good — re-baseline)")
        elif actual[key] < count:
            stale.append(f"{key}: {count} → {actual[key]} (good — re-baseline)")
    return regressions, stale


def write_baseline(
    findings: list[Finding], audit: AxiomAudit | None, baseline: dict
) -> None:
    payload: dict = {
        "schema": 1,
        "note": (
            "Baseline for RandomSystemsCC/audit_surface.py.  Keys are "
            "module::declaration::token, deliberately line-number-free.  "
            "Every entry must be named and justified in STATUS.md."
        ),
        # Declared axioms an endpoint footprint may name without re-baselining.
        # `sorryAx` is deliberately NOT here: an admitted endpoint has to be
        # recorded individually under `endpoint_axioms`.
        "allowed_axioms": baseline.get(
            "allowed_axioms", ["RandomSystemsCC.Frost.secp256k1_q_prime"]
        ),
    }
    for gate in ("admission", "surface", "performance"):
        entries: dict[str, Finding] = {}
        tally = counted([f for f in findings if f.gate == gate])
        for finding in findings:
            if finding.gate == gate:
                entries.setdefault(finding.key, finding)
        payload[gate] = [
            {
                "key": key,
                "count": tally[key],
                "first_seen_at": entries[key].where,
                "detail": entries[key].detail,
            }
            for key in sorted(tally)
        ]
    payload["endpoint_axioms"] = (
        dict(sorted(audit.footprints.items()))
        if audit is not None and audit.footprints
        else baseline.get("endpoint_axioms", {})
    )
    BASELINE_FILE.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")


# --- reporting --------------------------------------------------------------

GATE_TITLES = {
    "admission": "1. Admissions (`sorry` / `admit` / declared `axiom`)",
    "surface": "2. Statement surface of the derived public endpoints",
    "performance": "3. Performance escapes",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--axioms",
        action="store_true",
        help="also `#print axioms` every derived endpoint (builds its module)",
    )
    parser.add_argument("--json", metavar="PATH", help="write the machine-readable report")
    parser.add_argument(
        "--write-baseline", action="store_true", help="overwrite the checked-in baseline"
    )
    options = parser.parse_args()

    all_sources = sources()
    pairs = endpoints(all_sources)
    findings = (
        scan_admissions(all_sources)
        + scan_statement_surface(pairs)
        + scan_performance(all_sources)
    )
    baseline = load_baseline()
    audit = audit_axioms(pairs, baseline) if options.axioms else None
    if audit is not None:
        findings = findings + audit.findings

    if options.write_baseline:
        if audit is None:
            print(
                "Refusing to re-baseline without `--axioms`: the endpoint axiom "
                "footprints would be carried over unchecked.",
                file=sys.stderr,
            )
            return 1
        write_baseline(findings, audit, baseline)
        print(
            f"Wrote {BASELINE_FILE.relative_to(ROOT)}: "
            f"{len([f for f in findings if f.gate == 'admission'])} admissions, "
            f"{len([f for f in findings if f.gate == 'surface'])} surface, "
            f"{len([f for f in findings if f.gate == 'performance'])} performance, "
            f"{len(audit.footprints)} endpoint footprints.  Re-run to verify."
        )
        return 0

    regressions: list[str] = []
    stale: list[str] = []
    print("RandomSystemsCC bridge audit (STATUS.md §11.2)")
    print(f"  scanned {len(all_sources)} modules, {len(pairs)} derived public endpoints")
    # A path-keyed allow-list decays into noise the moment the module layout
    # moves: the sibling H-technique audit sat red for weeks because all four of
    # its sanctioned bridge consumers had been deleted, and the red was read as
    # noise rather than as drift.  Renaming an exempt file here would instead
    # dump every plumbing token in it into gate 2, so name the real cause.
    for exempt in sorted(SURFACE_EXEMPT_FILES):
        if not exempt.exists():
            regressions.append(
                f"{exempt.relative_to(ROOT)}: surface-exempt module does not "
                "exist; update SURFACE_EXEMPT_FILES to the live layout"
            )
    for gate in ("admission", "surface", "performance"):
        gate_findings = [f for f in findings if f.gate == gate]
        print(f"\n{GATE_TITLES[gate]}: {len(gate_findings)}")
        for finding in sorted(gate_findings, key=lambda f: f.where):
            print(f"  - {finding.where}: {finding.detail}")
        new, gone = compare(findings, baseline, gate)
        regressions += new
        stale += gone

    if audit is not None:
        print(
            f"\n4. Endpoint axiom footprints: {len(audit.footprints)} audited, "
            f"{len(audit.unaudited)} unaudited"
        )
        for name, footprint in sorted(audit.footprints.items()):
            flag = "" if set(footprint) <= set(FOUNDATIONAL_AXIOMS) else "  <- admitted"
            print(f"  - {name}: [{', '.join(footprint)}]{flag}")
        grouped: dict[str, list[str]] = {}
        for name, reason in sorted(audit.unaudited.items()):
            grouped.setdefault(reason, []).append(name)
        for reason, names in grouped.items():
            print(f"  ! NOT AUDITED — {reason}")
            for name in names:
                print(f"      {name}")
        regressions += [
            f"{finding.where}: {finding.detail}" for finding in audit.findings
        ]
        stale += audit.progress
    else:
        print("\n4. Endpoint axiom footprints: skipped (pass `--axioms`)")

    summary = {
        "endpoints": len(pairs),
        "admissions": len([f for f in findings if f.gate == "admission"]),
        "surface_violations": len([f for f in findings if f.gate == "surface"]),
        "performance_escapes": len([f for f in findings if f.gate == "performance"]),
        "axioms_audited": len(audit.footprints) if audit else 0,
        "axioms_unaudited": len(audit.unaudited) if audit else None,
        "regressions": len(regressions),
        "stale_baseline_entries": len(stale),
    }
    if options.json:
        report = {
            "summary": summary,
            "endpoints": [
                {"name": decl.name, "at": f"{source.rel}:{decl.line}"}
                for source, decl in sorted(pairs, key=lambda p: p[1].name)
            ],
            "findings": [f.as_dict() for f in findings],
            "endpoint_axioms": audit.footprints if audit else {},
            "unaudited_endpoints": audit.unaudited if audit else {},
            "regressions": regressions,
            "stale_baseline_entries": stale,
        }
        Path(options.json).write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")

    print("\ncc-audit-summary: " + json.dumps(summary, sort_keys=True))
    if stale:
        print("\nBaseline is now pessimistic (progress, not a failure):")
        for entry in stale:
            print(f"  - {entry}")
    if regressions:
        print("\nRandomSystemsCC bridge audit FAILED:", file=sys.stderr)
        for entry in regressions:
            print(f"  - {entry}", file=sys.stderr)
        return 1
    if audit is not None and audit.unaudited:
        print(
            "\nRandomSystemsCC bridge audit INCOMPLETE: no regression found, but "
            f"{len(audit.unaudited)} endpoint(s) could not be axiom-audited "
            "(see the `!` lines above). This is not a pass.",
            file=sys.stderr,
        )
        return 2
    print("\nRandomSystemsCC bridge audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
