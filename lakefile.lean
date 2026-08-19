import Lake
open Lake DSL

package RandomSystems where
  buildDir := (get_config? verificationBuildDir).getD ".lake/build"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

def dependencyVerificationOptions : Lean.NameMap String :=
  match get_config? verificationBuildDir with
  | some directory => ({} : Lean.NameMap String).insert `verificationBuildDir directory
  | none => {}

/-- The sibling abstract Constructive-Cryptography layer
(`../abstract-crypto/LIBRARY_GUIDE.md`).
The dependency is one-way: RS instantiates the abstract carrier contract;
nothing in the abstract package depends back on RS. -/
require AbstractCrypto from ".." / "abstract-crypto" with dependencyVerificationOptions

/-- The main random-systems surface: the PFun/CR18 formalization plus the
promoted H-technique application layer.  The pre-migration bounded-system
API and its applications live under `RandomSystems.Legacy`. -/
@[default_target]
lean_lib RandomSystems

/-- Historical bounded modules, retained for explicit downstream imports but
excluded from the selected default build. -/
lean_lib RandomSystemsLegacy where
  globs := #[.andSubmodules `RandomSystems.Legacy]

/-- The application layer built ON the foundation: HCTR2, CBC-MAC, the
Boneh–Shoup game layer, sum-of-permutations, and the H-technique application
machinery (the modules classed `application` in `module_audit_baseline.json`).
Coverage, not coupling: NOT a `@[default_target]`, and nothing in
`RandomSystems`/`RandomSystemsCC` imports its root — the dependency arrow
points applications → foundation only.  Includes the parked
`RandomSystems.CBCStructureGraph`, so this build prints the one live
`sorry` warning (`mass_cbcGraphBad_le`) by design; it still exits 0.
Build with `lake build RandomSystemsApplications`. -/
lean_lib RandomSystemsApplications

/-- The compatibility bridges to the quarantined `RandomSystems.Legacy` tree
(class `legacy-bridge` in `module_audit_baseline.json`).  They import
`RandomSystems.Legacy.*`, so they cannot join `RandomSystemsApplications`
without dragging the Legacy tree into that target; instead they get their own
target rooted at the existing `LegacyChecks` aggregator, whose import closure
covers all eight bridges.  Verified building cleanly on 2026-07-27 (exit 0).
Build with `lake build RandomSystemsLegacyBridge`. -/
lean_lib RandomSystemsLegacyBridge where
  roots := #[`RandomSystems.HTechnique.LegacyChecks]

/-- The Constructive-Cryptography bridge library. Its dependency and
instantiation rules are in `../abstract-crypto/LIBRARY_GUIDE.md`. RS-side
instances of the abstract carrier contract live under the
top-level `RandomSystemsCC/` module root so the default `RandomSystems`
glob can never sweep it (keeps the default surface free of the bridge's
AbstractCrypto dependency and any staged `sorry`).  NOT a default target;
no module outside `RandomSystemsCC` imports the abstract package —
with one deliberate carve-out: the theory-free `CCWidget` proof-widget
engine (no theory, no `sorry`; imports only ProofWidgets), imported at
the judgment-definition sites (`Distinguishing`, `CondEquiv`) so every
application file draws goal diagrams with zero ceremony. -/
lean_lib RandomSystemsCC where
  roots := #[`RandomSystemsCC, `RandomSystemsCC.Frost]

/-- The SequenceHash development is kept in its own source tree so its pure
encoding/specification layer remains independent of RandomSystems.  Later
modules in this library instantiate the RandomSystems and AbstractCrypto
surfaces without making either foundational library depend on the
construction.  Build with `lake build SequenceHash`. -/
lean_lib SequenceHash where
  srcDir := "sequence-hash"
  globs := #[.andSubmodules `SequenceHash]

/-- Non-default audience demo comparing the condition-C and no-bad
H-coefficient proofs of the URF/URP switching lemma.  Build with
`lake build RandomSystemsSwitchingDemo`. -/
lean_lib RandomSystemsSwitchingDemo where
  globs := #[.one `RandomSystemsSwitchingDemo]

/-- The documentation staleness gate.  `README`/`DESIGN`/`STATUS` are read by
agents as receipts, but they are written ahead of the work and they drift.  This
checks every backticked Lean name and file path in them against the tree, and
refuses a set of claims we have explicitly withdrawn.  Baseline-driven like
`ccSurfaceAudit`: the existing backlog is recorded in `doc_audit_baseline.json`,
so the gate fails only on NEW drift.  Purely syntactic; needs no build. -/
script docAudit do
  let out ← IO.Process.output { cmd := "python3", args := #["doc_audit.py"] }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

/-- The module reachability gate.  The `lean_lib` targets declare no
sweeping globs, so each builds exactly what its root modules transitively
import — a module no declared target reaches is not compiled by any build,
not covered by the audits, and free to rot silently.  Baseline-driven; fails
on NEW orphans (naming the stranded module), on baselined orphans that have
become reachable (shrink the backlog with `--write-baseline`), and on any
`lean_lib` in this file the audit does not account for.  The report keeps
the foundation / application-layer / legacy-bridge coverage breakdown
visible. -/
script moduleAudit do
  let out ← IO.Process.output { cmd := "python3", args := #["module_audit.py"] }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

script htechniqueSurfaceAudit do
  let out ← IO.Process.output {
    cmd := "python3",
    args := #["RandomSystems/HTechnique/audit_surface.py"]
  }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

script htechniqueCheck do
  let audit ← IO.Process.output {
    cmd := "python3",
    args := #["RandomSystems/HTechnique/audit_surface.py"]
  }
  IO.print audit.stdout
  IO.eprint audit.stderr
  if audit.exitCode != 0 then
    return audit.exitCode
  let build ← IO.Process.output {
    cmd := "lake",
    args := #["build", "RandomSystems.HTechnique.Surface"]
  }
  IO.print build.stdout
  IO.eprint build.stderr
  return build.exitCode

/-- The RS→AC bridge gate: admissions, endpoint statement surface, and
performance escapes under `RandomSystemsCC/`, against the checked-in
`RandomSystemsCC/audit_baseline.json` (`STATUS.md` §11.2 rules 2, 4, 5).
Purely syntactic, so it needs no build. -/
script ccSurfaceAudit do
  let out ← IO.Process.output {
    cmd := "python3",
    args := #["RandomSystemsCC/audit_surface.py"]
  }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

/-- `ccSurfaceAudit` plus the focused bridge builds and the endpoint axiom
audit (`STATUS.md` §11.2 rules 1 and 3): every derived public endpoint is
`#print axioms`-checked against its recorded footprint.  Exit code 2 means the
syntactic gates passed but some endpoint could not be audited — not a pass. -/
script ccCheck do
  let build ← IO.Process.output {
    cmd := "lake",
    args := #["build", "RandomSystemsCC.Symmetric.All", "RandomSystemsCC.TypedFinite"]
  }
  IO.print build.stdout
  IO.eprint build.stderr
  if build.exitCode != 0 then
    return build.exitCode
  let audit ← IO.Process.output {
    cmd := "python3",
    args := #["RandomSystemsCC/audit_surface.py", "--axioms"]
  }
  IO.print audit.stdout
  IO.eprint audit.stderr
  return audit.exitCode
