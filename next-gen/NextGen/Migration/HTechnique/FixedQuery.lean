/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.FixedQueryLaw
import NextGen.Migration.HTechnique.TranscriptLaw

/-!
# Fixed-query CR18 transcript laws

Compatibility support for the H-technique migration.  The public fixed-query
law lives in `FixedQueryLaw`; this module adds the representative-level
environment adapter used by proof-support modules.

Migration note: this module is compatibility-only.  New proofs should use
`FixedQueryLaw` and law-level/deterministic CR18 environments instead of
representative adapters.
-/

namespace NextGen
namespace Migration
namespace HTechnique

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **Source-theorem bridge; candidate for upstream.** Package the exact
fixed-query CR18 environment as the representative-level environment object
used by transcript-law endpoints.  The unit sample space and deterministic
environment RV are construction details, not theorem-facing parameters. -/
noncomputable def fixedQueryRepresentative (xs : Fin q → X) :
    PDERepresentative.{u, v, 0} X Y :=
  PDERepresentative.deterministic (fixedQueryEnvironment (Y := Y) xs)

end HTechnique
end Migration
end NextGen
