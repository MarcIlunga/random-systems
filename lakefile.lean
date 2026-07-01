import Lake
open Lake DSL

package RandomSystems where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

@[default_target]
lean_lib RandomSystems

/-- `next-gen`: the clean, PFun (function-based) formalization only. No legacy struct code
(`DDS` record / `DDG` / `gameStructure` / struct `Behavior`) lives here. -/
lean_lib NextGen where
  srcDir := "next-gen"
  globs := #[.submodules `NextGen]

script htechniqueSurfaceAudit do
  let out ← IO.Process.output {
    cmd := "python3",
    args := #["next-gen/NextGen/Migration/HTechnique/audit_surface.py"]
  }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

script htechniqueCheck do
  let audit ← IO.Process.output {
    cmd := "python3",
    args := #["next-gen/NextGen/Migration/HTechnique/audit_surface.py"]
  }
  IO.print audit.stdout
  IO.eprint audit.stderr
  if audit.exitCode != 0 then
    return audit.exitCode
  let build ← IO.Process.output {
    cmd := "lake",
    args := #["build", "NextGen.Migration.HTechnique.Surface"]
  }
  IO.print build.stdout
  IO.eprint build.stderr
  return build.exitCode
