import Lake
open Lake DSL

package «informalization» where
  -- Self-contained: depends on the Lean toolchain only (no mathlib / VCVio),
  -- so it builds against the pinned v4.29.0 without the cnl-rs build hell.
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Informalization» where
  globs := #[.andSubmodules `Informalization]

lean_lib «InformalizationExamples» where
  srcDir := "examples"
  globs := #[.andSubmodules `Examples]
