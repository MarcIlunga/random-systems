#!/usr/bin/env python3
"""Reachability gate: which live modules is some declared build target gating?

`lean_lib RandomSystems` declares **no globs**, so it builds exactly what
`RandomSystems.lean` transitively imports — and nothing else.  A module that no
declared `lean_lib` reaches is therefore not merely undocumented: it is **not
compiled by any build target, not covered by the audits, and free to rot
silently.**

An **orphan** here means: reachable from **no declared `lean_lib` target at
all**.  Being outside the *foundation* is not a defect — the
applications/foundation line is deliberate and load-bearing:

* A sweep on 2026-07-27 found 49 live modules (19,642 lines) outside the
  then-declared roots.  The owner's classification
  (`module_audit_baseline.json`, classes `application` / `legacy-bridge` /
  `foundation-unwired`) resolved them as follows, same day:
  - **35 `application` modules (16,892 lines)** — HCTR2, CBC-MAC, the
    Boneh–Shoup game layer, sum-of-permutations — are built *on* the
    foundation and deliberately not part of it.  They now have their own
    target, `lean_lib RandomSystemsApplications`, rooted at the explicit
    aggregator `RandomSystemsApplications.lean`; dropping an import there
    strands the module and fails this gate.
  - **8 `legacy-bridge` modules (969 lines)** bridge to the quarantined
    `RandomSystems.Legacy` tree and are covered by
    `lean_lib RandomSystemsLegacyBridge` (rooted at the existing
    `RandomSystems.HTechnique.LegacyChecks` aggregator).
  - **6 `foundation-unwired` modules (1,781 lines)** were real debt and are
    now imported by `RandomSystems.lean` — including `RandomSystemMetric`,
    the `MetricSpace` installer that `RandomSystemQuotient` had been
    advertising while nothing imported it.

The report keeps that classification visible: it prints the per-library
coverage breakdown (foundation vs application layer vs legacy bridges) and
the `class` breakdown of any baselined orphans, so the applications/
foundation distinction survives even with an empty backlog.

The gate is baseline-driven, like `ccSurfaceAudit` and `doc_audit.py`: known
orphans are recorded in `module_audit_baseline.json` with a class and a reason
for each, and the gate fails when a **new** module falls out of reach, when a
baselined orphan becomes reachable (so the backlog shrinks rather than rots),
or when `lakefile.lean` declares a `lean_lib` this audit does not know about.

Deliberately out of scope: `RandomSystems/Legacy/**` (its own `lean_lib`
target), and the `attic/`, `scratch/`, `scratchpad/`, `sequence-hash/` trees.

Run: `python3 module_audit.py` or `lake run moduleAudit`.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASELINE = ROOT / "module_audit_baseline.json"
LAKEFILE = ROOT / "lakefile.lean"

# The declared `lean_lib` targets and their root modules, read off
# `lakefile.lean`.  A module is an orphan only if NO entry here reaches it.
# The lakefile consistency check below fails if a `lean_lib` appears in the
# lakefile that is neither listed here nor exempted with a reason.
LIB_ROOTS: dict[str, list[str]] = {
    "RandomSystems": ["RandomSystems"],
    "RandomSystemsCC": ["RandomSystemsCC", "RandomSystemsCC.Frost"],
    "RandomSystemsSwitchingDemo": ["RandomSystemsSwitchingDemo"],
    "RandomSystemsApplications": ["RandomSystemsApplications"],
    "RandomSystemsLegacyBridge": ["RandomSystems.HTechnique.LegacyChecks"],
}

# The foundation surface; everything else covered is layered on top of it.
FOUNDATION_LIBS = ("RandomSystems", "RandomSystemsCC", "RandomSystemsSwitchingDemo")

# Declared libs living entirely in trees this audit excludes by design.
EXEMPT_LIBS = {
    "RandomSystemsLegacy": "the quarantined Legacy tree (its own target)",
    "SequenceHash": "its own source tree (sequence-hash/)",
}

EXCLUDED_TREES = ("attic", "scratch", "scratchpad", "sequence-hash")

# Trees another session actively owns, under a standing hands-off instruction.
# These are NOT silently dropped: every run prints them with line counts, so the
# coverage they still owe stays visible.  They simply do not *fail* the gate,
# because a gate that reddens every time their owner adds a file is a gate
# nobody reads — the exact decay this audit was written to prevent.  Remove the
# entry (and wire the modules into a target) once the owner lands the tree.
OWNER_RESERVED_TREES: dict[str, str] = {
    "RandomSystems/BonehShoup": (
        "Boneh-Shoup development owned by a concurrent session; wire into "
        "RandomSystemsApplications once landed"
    ),
    "RandomSystems/SoP": (
        "sum-of-permutations development owned by a concurrent session; "
        "wire into RandomSystemsApplications once landed"
    ),
}
IMPORT = re.compile(r"^import\s+([A-Za-z_][\w.]*)")
LEAN_LIB = re.compile(r"^lean_lib\s+([A-Za-z_]\w*)", re.MULTILINE)


def live_modules() -> dict[str, Path]:
    """Every module the declared targets could plausibly be expected to cover."""
    modules: dict[str, Path] = {}
    for path in ROOT.rglob("*.lean"):
        parts = path.parts
        if ".lake" in parts or path.name == "lakefile.lean":
            continue
        relative = path.relative_to(ROOT)
        if relative.parts[0] in EXCLUDED_TREES:
            continue
        if "Legacy" in relative.parts:
            continue  # its own lean_lib target, excluded by design
        modules[str(relative.with_suffix("")).replace("/", ".")] = path
    return modules


def import_edges(modules: dict[str, Path]) -> dict[str, set[str]]:
    edges: dict[str, set[str]] = collections.defaultdict(set)
    for name, path in modules.items():
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            found = IMPORT.match(line)
            if found:
                edges[name].add(found.group(1))
    return edges


def reachable(
    modules: dict[str, Path], edges: dict[str, set[str]], roots: list[str]
) -> set[str]:
    seen: set[str] = set()
    stack = [root for root in roots if root in modules]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(child for child in edges[current] if child in modules)
    return seen


def unknown_libs() -> list[str]:
    """`lean_lib` declarations in the lakefile this audit does not account for."""
    text = LAKEFILE.read_text(encoding="utf-8")
    return [
        name
        for name in LEAN_LIB.findall(text)
        if name not in LIB_ROOTS and name not in EXEMPT_LIBS
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="record the current orphans as the accepted backlog",
    )
    options = parser.parse_args()

    previous = {}
    if BASELINE.exists():
        previous = json.loads(BASELINE.read_text()).get("known_orphans", {})

    modules = live_modules()
    edges = import_edges(modules)
    per_lib = {lib: reachable(modules, edges, roots) for lib, roots in LIB_ROOTS.items()}
    covered = set().union(*per_lib.values())
    all_orphans = sorted(set(modules) - covered)
    reserved_prefixes = {t.replace("/", "."): why
                         for t, why in OWNER_RESERVED_TREES.items()}
    def reserved_by(name: str) -> str | None:
        for prefix, why in reserved_prefixes.items():
            if name == prefix or name.startswith(prefix + "."):
                return why
        return None
    reserved = [n for n in all_orphans if reserved_by(n)]
    orphans = [n for n in all_orphans if not reserved_by(n)]
    sizes = {
        name: len(modules[name].read_text(encoding="utf-8", errors="ignore").splitlines())
        for name in modules
    }

    if options.write_baseline:
        BASELINE.write_text(
            json.dumps(
                {
                    "note": (
                        "Modules reachable from NO declared lean_lib target, so "
                        "compiled by no build. The 2026-07-27 classification "
                        "(application / legacy-bridge / foundation-unwired) is "
                        "resolved: applications live in lean_lib "
                        "RandomSystemsApplications, legacy bridges in lean_lib "
                        "RandomSystemsLegacyBridge, and the foundation-unwired "
                        "modules are imported by RandomSystems.lean. Anything "
                        "listed here is NEW debt: classify it or wire it."
                    ),
                    "known_orphans": {
                        name: (
                            previous.get(name)
                            or {"lines": sizes[name], "class": "unclassified",
                                "reason": "REVIEW — classify this"}
                        )
                        for name in orphans
                    },
                },
                indent=2,
                sort_keys=True,
            )
            + "\n"
        )
        print(f"Wrote {BASELINE.name}: {len(orphans)} accepted orphan(s), "
              f"{sum(sizes[name] for name in orphans)} lines.")
        return 0

    baseline = {}
    if BASELINE.exists():
        baseline = json.loads(BASELINE.read_text()).get("known_orphans", {})

    failures = 0

    foundation = set().union(*(per_lib[lib] for lib in FOUNDATION_LIBS))
    app_only = per_lib["RandomSystemsApplications"] - foundation
    bridge_only = per_lib["RandomSystemsLegacyBridge"] - foundation - app_only

    print(
        f"module reachability — {len(modules)} live modules, {len(covered)} covered "
        f"by a declared lean_lib, {len(orphans)} orphaned "
        f"({sum(sizes[name] for name in orphans)} lines), {len(baseline)} in baseline"
    )
    print(
        f"  foundation ({', '.join(FOUNDATION_LIBS)}): "
        f"{len(foundation)} modules, {sum(sizes[m] for m in foundation)} lines"
    )
    print(
        f"  application layer (only via RandomSystemsApplications): "
        f"{len(app_only)} modules, {sum(sizes[m] for m in app_only)} lines"
    )
    print(
        f"  legacy bridges (only via RandomSystemsLegacyBridge): "
        f"{len(bridge_only)} modules, {sum(sizes[m] for m in bridge_only)} lines"
    )

    if baseline:
        by_class: dict[str, list[str]] = collections.defaultdict(list)
        for name, entry in baseline.items():
            by_class[entry.get("class", "unclassified") if isinstance(entry, dict)
                     else "unclassified"].append(name)
        print("\nbaselined orphan backlog by class:")
        for cls in sorted(by_class):
            names = by_class[cls]
            lines = sum(
                baseline[n].get("lines", 0) for n in names
                if isinstance(baseline[n], dict)
            )
            print(f"  {cls}: {len(names)} module(s), {lines} lines")
    else:
        print("\nbaselined orphan backlog: empty")

    debt = [
        name
        for name, entry in baseline.items()
        if isinstance(entry, dict) and entry.get("class") == "foundation-unwired"
    ]
    if debt:
        print(
            f"\n{len(debt)} module(s) classed `foundation-unwired` — real debt, "
            "not applications:"
        )
        for name in sorted(debt):
            print(f"  ! {name}  ({baseline[name]['reason']})")
    else:
        print("foundation-unwired debt: none — the foundation import list is complete")

    if reserved:
        print(
            f"\nowner-reserved (reported, not gating): {len(reserved)} module(s), "
            f"{sum(sizes[n] for n in reserved)} lines"
        )
        for name in sorted(reserved):
            print(f"  ~ {sizes[name]:6d} lines  {name}  ({reserved_by(name)})")

    unknown = unknown_libs()
    if unknown:
        failures += 1
        print(f"\n{len(unknown)} lean_lib target(s) unknown to this audit:")
        for name in unknown:
            print(f"  * {name}")
        print(
            "\nAdd its roots to LIB_ROOTS (so its modules count as covered) or\n"
            "exempt it in EXEMPT_LIBS with a reason."
        )

    unclassified = [
        name
        for name, entry in baseline.items()
        if isinstance(entry, dict) and entry.get("class") == "unclassified"
    ]
    if unclassified:
        print(f"\n{len(unclassified)} baselined orphan(s) still unclassified:")
        for name in unclassified:
            print(f"  ? {name}")

    rescued = sorted(set(baseline) - set(orphans))
    if rescued:
        failures += 1
        print(
            f"\n{len(rescued)} baselined orphan(s) now reachable — re-run with "
            "`--write-baseline` to shrink the backlog:"
        )
        for name in rescued:
            print(f"  + {name}")

    new = [name for name in orphans if name not in baseline]
    if new:
        failures += 1
        print(f"\n{len(new)} NEW ORPHAN(S) — unreachable from every lean_lib target:\n")
        for name in new:
            print(f"  - {sizes[name]:6d} lines  {name}")
        print(
            "\nA new orphan means every build target stopped covering it.  Either\n"
            "wire it into a target root's import list, or baseline it with a reason."
        )

    if failures:
        return 1
    print("\nNo new orphans. Audit passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
