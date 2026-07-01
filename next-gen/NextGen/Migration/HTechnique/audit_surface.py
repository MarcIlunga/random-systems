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


ROOT = Path(__file__).resolve().parents[3]
SURFACE_FILE = ROOT / "NextGen" / "Migration" / "HTechnique" / "Surface.lean"
PUBLIC_FILES = [
    SURFACE_FILE,
    ROOT / "NextGen" / "Migration" / "HTechnique" / "SecurityDefs.lean",
    ROOT / "NextGen" / "Migration" / "HTechnique" / "SoPBoundary.lean",
    ROOT / "NextGen" / "Migration" / "HTechnique" / "HashThenPRF.lean",
    ROOT / "NextGen" / "Migration" / "HTechnique" / "StrongPRP.lean",
]
PUBLIC_HEADER_FILES = PUBLIC_FILES
HTECHNIQUE_ROOT = ROOT / "NextGen" / "Migration" / "HTechnique"
CLEAN_SUPPORT_FILES = [
    HTECHNIQUE_ROOT / "FixedQueryLaw.lean",
]
COMPATIBILITY_ONLY_FILES = [
    HTECHNIQUE_ROOT / "AdaptiveBridge.lean",
    HTECHNIQUE_ROOT / "AdaptiveLawBridge.lean",
    HTECHNIQUE_ROOT / "AdaptiveTranscriptAdvantage.lean",
    HTECHNIQUE_ROOT / "BoundedEnvironment.lean",
    HTECHNIQUE_ROOT / "Density.lean",
    HTECHNIQUE_ROOT / "FixedQuery.lean",
    HTECHNIQUE_ROOT / "FixedQueryCompatibility.lean",
    HTECHNIQUE_ROOT / "FunctionEvaluator.lean",
    HTECHNIQUE_ROOT / "LegacyBoundary.lean",
    HTECHNIQUE_ROOT / "LegacyBoundedTranscript.lean",
    HTECHNIQUE_ROOT / "LegacyStatelessBridge.lean",
    HTECHNIQUE_ROOT / "SoPLegacyBoundary.lean",
    HTECHNIQUE_ROOT / "TranscriptLaw.lean",
    HTECHNIQUE_ROOT / "SoP" / "AdaptiveAdvantage.lean",
    HTECHNIQUE_ROOT / "SoP" / "CompressionLegacy.lean",
]
def path_to_module(path: Path) -> str:
    return (
        "NextGen.Migration.HTechnique."
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
    prefix = "NextGen.Migration.HTechnique."
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


def audit_private_declarations() -> list[str]:
    failures: list[str] = []
    for path in HTECHNIQUE_ROOT.rglob("*.lean"):
        for line_no, line in enumerate(path.read_text().splitlines(), start=1):
            if PRIVATE_RE.match(line):
                rel = path.relative_to(ROOT)
                failures.append(f"{rel}:{line_no}: private declaration in HTechnique")
    return failures


def main() -> int:
    failures = (
        audit_public_headers()
        + audit_public_variables()
        + audit_public_imports()
        + audit_public_compatibility_alias_uses()
        + audit_compatibility_markers()
        + audit_private_declarations()
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
