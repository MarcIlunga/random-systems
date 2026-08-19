#!/usr/bin/env python3
"""Audit the curated H-technique surface for support-type leaks.

This is intentionally a small syntactic guard, not a Lean parser.  It checks
paper-facing declaration headers in the curated surface modules and fails if
they mention representative objects, raw sample spaces, raw random variables,
or raw probability distributions.  Support modules may still expose those
objects while the migration is in progress.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SURFACE_FILE = ROOT / "RandomSystems" / "HTechnique" / "Surface.lean"
PUBLIC_FILES = [
    SURFACE_FILE,
    ROOT / "RandomSystems" / "HTechnique" / "SecurityDefs.lean",
    ROOT / "RandomSystems" / "HTechnique" / "SoPBoundary.lean",
    ROOT / "RandomSystems" / "HTechnique" / "HashThenPRF.lean",
    ROOT / "RandomSystems" / "HTechnique" / "StrongPRP.lean",
]
PUBLIC_HEADER_FILES = PUBLIC_FILES
HTECHNIQUE_ROOT = ROOT / "RandomSystems" / "HTechnique"
CLEAN_SUPPORT_FILES = [
    HTECHNIQUE_ROOT / "FixedQueryLaw.lean",
]
COMPATIBILITY_ONLY_FILES = [
    HTECHNIQUE_ROOT / "AdaptiveBridge.lean",
    HTECHNIQUE_ROOT / "AdaptiveTranscriptAdvantage.lean",
    HTECHNIQUE_ROOT / "Density.lean",
    HTECHNIQUE_ROOT / "FixedQuery.lean",
    HTECHNIQUE_ROOT / "FixedQueryCompatibility.lean",
    HTECHNIQUE_ROOT / "LegacyBoundary.lean",
    HTECHNIQUE_ROOT / "LegacyBoundedTranscript.lean",
    HTECHNIQUE_ROOT / "LegacyStatelessBridge.lean",
    HTECHNIQUE_ROOT / "SoPLegacyBoundary.lean",
    HTECHNIQUE_ROOT / "TranscriptLaw.lean",
    HTECHNIQUE_ROOT / "SoP" / "AdaptiveAdvantage.lean",
    HTECHNIQUE_ROOT / "SoP" / "CompressionLegacy.lean",
    HTECHNIQUE_ROOT / "SoP" / "LegacyVisibleEquiv.lean",
    HTECHNIQUE_ROOT / "SoP" / "XoPLegacyBridge.lean",
]
def path_to_module(path: Path) -> str:
    return (
        "RandomSystems.HTechnique."
        + path.relative_to(HTECHNIQUE_ROOT).with_suffix("").as_posix().replace("/", ".")
    )


COMPATIBILITY_ONLY_MODULES = {path_to_module(path) for path in COMPATIBILITY_ONLY_FILES}

DECL_RE = re.compile(
    r"^\s*(?:@[^\n]*\s*)?"
    r"(?:theorem|lemma|def|abbrev|noncomputable\s+def|noncomputable\s+abbrev)\s+\S+"
)
IMPORT_RE = re.compile(r"^\s*import\s+(\S+)")
VARIABLE_RE = re.compile(r"^\s*variable\b")
FORBIDDEN_RE = re.compile(
    r"\bPDSRepresentative\b"
    r"|\bPDERepresentative\b"
    r"|RandomSystems\.Dist\.ProbDist"
    r"|RandomSystems\.CR18\.PFunPDS\.RV"
    r"|RandomSystems\.CR18\.PFunPDE\.RV"
    r"|\bProbDist\s+Ω\b"
    r"|\bRV\s+Ω\b"
    r"|\{Ω\b"
    r"|\bΩ\s*:"
)
PRIVATE_RE = re.compile(r"^\s*private\s+(?:theorem|lemma|def|abbrev)\b")
PUBLIC_COMPATIBILITY_ALIAS_RE = re.compile(
    r"\bProbPDS\.fixedQueryTranscriptDist_functionEvaluator\b"
)
MIGRATION_ONLY_RE = re.compile(
    r"\b(?:migration-only|compatibility-only|support boundary)\b",
    re.IGNORECASE,
)
def module_to_path(module: str) -> Path | None:
    prefix = "RandomSystems.HTechnique."
    if not module.startswith(prefix):
        return None
    suffix = module.removeprefix(prefix).replace(".", "/")
    return HTECHNIQUE_ROOT / f"{suffix}.lean"


def public_files() -> list[Path]:
    """Curated surface plus reachable non-compatibility H-technique modules."""
    files: list[Path] = []
    stack = [SURFACE_FILE, *PUBLIC_FILES, *CLEAN_SUPPORT_FILES]
    while stack:
        path = stack.pop()
        if path in files or not path.exists():
            continue
        files.append(path)
        for line in path.read_text().splitlines():
            match = IMPORT_RE.match(line)
            if not match:
                continue
            imported = match.group(1)
            imported_path = module_to_path(imported)
            if imported_path is None or not imported_path.exists():
                continue
            if imported in COMPATIBILITY_ONLY_MODULES:
                continue
            stack.append(imported_path)
    return list(dict.fromkeys(files))


def declaration_headers(path: Path) -> list[tuple[int, str]]:
    lines = path.read_text().splitlines()
    headers: list[tuple[int, str]] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if not DECL_RE.match(line):
            i += 1
            continue
        start = i + 1
        chunk = [line]
        i += 1
        while i < len(lines):
            chunk.append(lines[i])
            if ":=" in lines[i]:
                break
            i += 1
        headers.append((start, "\n".join(chunk)))
        i += 1
    return headers


def audit_public_headers() -> list[str]:
    failures: list[str] = []
    for path in PUBLIC_HEADER_FILES:
        for line_no, header in declaration_headers(path):
            match = FORBIDDEN_RE.search(header)
            if match:
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: forbidden public header token `{match.group(0)}`"
                )
    return failures


def audit_public_variables() -> list[str]:
    failures: list[str] = []
    for path in PUBLIC_HEADER_FILES:
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            if not VARIABLE_RE.match(line):
                continue
            match = FORBIDDEN_RE.search(line)
            if match:
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: forbidden public module variable token "
                    f"`{match.group(0)}`"
                )
    return failures


def audit_public_imports() -> list[str]:
    failures: list[str] = []
    for path in public_files():
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            match = IMPORT_RE.match(line)
            if not match:
                continue
            imported = match.group(1)
            if imported in COMPATIBILITY_ONLY_MODULES:
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: public surface imports migration-only "
                    f"module `{imported}`"
                )
    return failures


def audit_public_compatibility_alias_uses() -> list[str]:
    failures: list[str] = []
    for path in public_files():
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            match = PUBLIC_COMPATIBILITY_ALIAS_RE.search(line)
            if match:
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: public proof should use the owner-level "
                    f"CR18 theorem instead of compatibility alias "
                    f"`{match.group(0)}`"
                )
    return failures


def audit_compatibility_markers() -> list[str]:
    failures: list[str] = []
    for path in COMPATIBILITY_ONLY_FILES:
        if not path.exists():
            rel = path.relative_to(ROOT)
            failures.append(f"{rel}: configured compatibility-only file is missing")
            continue
        text = path.read_text()
        if not MIGRATION_ONLY_RE.search(text):
            rel = path.relative_to(ROOT)
            failures.append(
                f"{rel}: compatibility/support module must say "
                "`migration-only`, `compatibility-only`, or `support boundary`"
            )
    return failures


def audit_all_coverage() -> list[str]:
    """Every Lean module in this folder must be reachable from `All`.

    Orphaned modules silently escape the migration build gate
    `lake build RandomSystems.HTechnique.All` (they are still covered by
    the whole-library `lake build RandomSystems`, but the migration gate should be
    self-contained)."""
    all_file = HTECHNIQUE_ROOT / "All.lean"
    legacy_file = HTECHNIQUE_ROOT / "LegacyChecks.lean"
    # Work-in-progress modules not yet wired into the `All` gate.  Build them
    # directly (`lake build RandomSystems.HTechnique.<Module>`).  Empty since
    # the HCTR2 consolidation: every HCTR2 module is reachable from `All` via
    # `HCTR2Paper`, and the retired split files (`HCTR2.lean`, `HCTR2Bit.lean`)
    # are gone.
    wip_exempt: set[Path] = set()
    # Out-of-folder hubs inside the `All` import closure: the consolidated
    # HCTR2 core lives at `RandomSystems/HCTR2.lean` (namespace
    # `RandomSystems.CR18.HCTR2`) and is imported by the HCTR2 consumers in
    # this folder; its own HTechnique imports (e.g. `TweakablePRP`) are
    # therefore genuinely covered by the `All` build gate, so the walk must
    # traverse it.
    external_hubs: dict[str, Path] = {
        "RandomSystems.HCTR2": ROOT / "RandomSystems" / "HCTR2.lean",
    }
    reachable: set[Path] = set(wip_exempt)
    stack = [all_file, legacy_file]
    while stack:
        path = stack.pop()
        if path in reachable or not path.exists():
            continue
        reachable.add(path)
        for line in path.read_text().splitlines():
            match = IMPORT_RE.match(line)
            if not match:
                continue
            imported = match.group(1)
            imported_path = module_to_path(imported) or external_hubs.get(imported)
            if imported_path is not None and imported_path.exists():
                stack.append(imported_path)
    failures: list[str] = []
    for path in sorted(HTECHNIQUE_ROOT.rglob("*.lean")):
        if path not in reachable:
            rel = path.relative_to(ROOT)
            failures.append(
                f"{rel}: module is not reachable from the `All` or"
                " `LegacyChecks` build gates"
            )
    return failures


def audit_all_legacy_free() -> list[str]:
    """`All`'s import closure must not touch `RandomSystems.Legacy.*`.

    Legacy imports belong to the `LegacyChecks` gate only."""
    all_file = HTECHNIQUE_ROOT / "All.lean"
    reachable: set[Path] = set()
    stack = [all_file]
    failures: list[str] = []
    while stack:
        path = stack.pop()
        if path in reachable or not path.exists():
            continue
        reachable.add(path)
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            match = IMPORT_RE.match(line)
            if not match:
                continue
            imported = match.group(1)
            if imported.startswith("RandomSystems.Legacy."):
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: `All` closure imports legacy module"
                    f" `{imported}` (move it behind `LegacyChecks`)"
                )
            imported_path = module_to_path(imported)
            if imported_path is not None and imported_path.exists():
                stack.append(imported_path)
    return failures


# Support legs of the consolidated HCTR2 core (`RandomSystems/HCTR2.lean`),
# relocated into this folder for import-layer reasons only.  They follow the
# core's style (proof-internal `private` helpers, like the core file itself,
# which lives outside this folder and is not scanned); the no-private policy
# governs the curated H-technique surface, which these legs are not part of.
PRIVATE_EXEMPT_FILES = {
    HTECHNIQUE_ROOT / "TweakablePRP.lean",
    # The consolidated HCTR2 paper-theorem file: its two intermediate security
    # theorems (`hctr2Bit_substitution_sigma`,
    # `hctr2Bit_security_computational_sigma`) are deliberate `private`
    # stepping stones — the curated public deliverable is
    # `hctr2_paper_theorem` alone.
    HTECHNIQUE_ROOT / "HCTR2Paper.lean",
}


def audit_private_declarations() -> list[str]:
    failures: list[str] = []
    for path in HTECHNIQUE_ROOT.rglob("*.lean"):
        if path in PRIVATE_EXEMPT_FILES:
            continue
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            if PRIVATE_RE.match(line):
                rel = path.relative_to(ROOT)
                failures.append(f"{rel}:{line_no}: private declaration in HTechnique")
    return failures


# --- Constructive-Cryptography bridge gates (abstract-crypto/AGENTS.md) -------

# The bridge library and its module root.  Everything else in the default
# `RandomSystems` surface must stay independent of the abstract packages.
BRIDGE_DIR = ROOT / "RandomSystemsCC"
BRIDGE_ROOT_FILE = ROOT / "RandomSystemsCC.lean"
# Explicit integration consumers sanctioned to own abstract construction
# statements.  The application-level FROST modules are the live consumers, and
# `LiftingExample.lean` is the canonical worked example of the declare-at-RS /
# prove-by-lifting-to-AC method (`DESIGN.md` §10.11), so it necessarily names
# the AC construction calculus.  Carrier/action support modules remain excluded.
#
# The previous list named `Instantiated.lean`, `FixedSignature/Serial.lean`,
# `FixedSignature/TwoInterface.lean`, and `FrostInstantiation.lean` — all four
# were deleted by the bridge consolidation (`DESIGN.md` §10.9: "the former
# separate exact-operational instance is obsolete"), which left this gate
# permanently red and therefore unread.  Keep this set in step with the live
# consumer modules; an entry that no longer exists is a silent gate failure.
#
# Added 2026-07-26: `ResourceLift.lean` defines the source-facing `constructs`
# judgment itself and documents the `Constructs.eball_trans` contract its
# `IsNonexpandingSMul` instance exists to satisfy; `CBC.lean` owns the CBC-MAC
# constructions including the composed `cbc_urp_randomness_expander`; and
# `TypedPropertyTransfer.lean` is the worked `propSpec`/`gameSpec` consumer.
# All three are genuine construction owners, not carrier/action support.
#
# Added 2026-07-29: `MauRen16Impossibility.lean` states MauRen16 Lemma 6, the
# estate's first impossibility result.  Its endpoint is the *negation* of a
# construction statement (`¬ Constructs …`) plus the sharpness receipt that a
# correlated honest converter does construct, so it necessarily names the AC
# construction calculus; it owns its own concrete carrier rather than reusing
# one, which is why it is a construction owner and not carrier support.
BRIDGE_STATEMENT_FILES = {
    BRIDGE_DIR / "LiftingExample.lean",
    BRIDGE_DIR / "ResourceLift.lean",
    BRIDGE_DIR / "ResourceParallel.lean",
    BRIDGE_DIR / "ParallelChecks.lean",
    BRIDGE_DIR / "CBC.lean",
    BRIDGE_DIR / "TypedPropertyTransfer.lean",
    BRIDGE_DIR / "MauRen16Impossibility.lean",
    BRIDGE_DIR / "Frost.lean",
    BRIDGE_DIR / "Frost" / "Instantiation.lean",
    BRIDGE_DIR / "Frost" / "EndToEnd.lean",
    BRIDGE_DIR / "Frost" / "Reduction.lean",
}

BRIDGE_IMPORT_RE = re.compile(r"^\s*import\s+(?:ConstructiveCrypto|AbstractCrypto)\.")
# Word-boundary match on abstract construction vocabulary that only explicit
# integration consumers may mention (comments included is acceptable).
BRIDGE_STATEMENT_RE = re.compile(r"\b(?:gameSpec|propSpec|Constructs)\b")


def audit_bridge_isolation() -> list[str]:
    """No default-surface module may depend on the abstract packages.

    Only files inside `RandomSystemsCC/` (and the `RandomSystemsCC.lean`
    module root) may `import ConstructiveCrypto.*` / `import AbstractCrypto.*`.
    Every `.lean` under `RandomSystems/` and `RandomSystems.lean` must stay
    independent of the bridge's abstract dependency
    (`abstract-crypto/AGENTS.md`, "Cross-repository work")."""
    failures: list[str] = []
    scan: list[Path] = [ROOT / "RandomSystems.lean"]
    scan += sorted((ROOT / "RandomSystems").rglob("*.lean"))
    for path in scan:
        if not path.exists():
            continue
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            if BRIDGE_IMPORT_RE.match(line):
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: non-bridge module imports the abstract "
                    f"package (`{line.strip()}`); such imports belong under "
                    "`RandomSystemsCC/` only"
                )
    return failures


def audit_bridge_statement_discipline() -> list[str]:
    """Inside `RandomSystemsCC/`, only explicit consumers own abstract
    construction statements.

    Every other bridge file (carrier/action support, RS-level leaves) must not
    mention `gameSpec`, `propSpec`, or `Constructs` (word-boundary match);
    those statements live in the sanctioned consumer modules. This keeps the
    carrier/action layer clean of the abstract theory it feeds while allowing
    the selected fixed-signature AC/CC/CC.MPC receipts to remain next to the
    concrete instance they exercise."""
    failures: list[str] = []
    if not BRIDGE_DIR.exists():
        return failures
    # A sanctioned entry that no longer exists silently widens nothing but
    # signals that the list has drifted from the module layout; report it rather
    # than letting the gate rot unnoticed as it did before the 2026-07-25 audit.
    for sanctioned in sorted(BRIDGE_STATEMENT_FILES):
        if not sanctioned.exists():
            failures.append(
                f"{sanctioned.relative_to(ROOT)}: sanctioned bridge consumer "
                "does not exist; update BRIDGE_STATEMENT_FILES to the live "
                "consumer modules"
            )
    for path in sorted(BRIDGE_DIR.rglob("*.lean")):
        if path in BRIDGE_STATEMENT_FILES:
            continue
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            match = BRIDGE_STATEMENT_RE.search(line)
            if match:
                rel = path.relative_to(ROOT)
                failures.append(
                    f"{rel}:{line_no}: bridge file mentions abstract construction "
                    f"token `{match.group(0)}`; such statements belong in "
                    "an explicitly sanctioned RandomSystemsCC consumer module"
                )
    return failures


def main() -> int:
    failures = (
        audit_public_headers()
        + audit_public_variables()
        + audit_public_imports()
        + audit_public_compatibility_alias_uses()
        + audit_compatibility_markers()
        + audit_all_coverage()
        + audit_all_legacy_free()
        + audit_private_declarations()
        + audit_bridge_isolation()
        + audit_bridge_statement_discipline()
    )
    if failures:
        print("HTechnique surface audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("HTechnique surface audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
