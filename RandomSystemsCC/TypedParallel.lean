/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedParallel
import RandomSystemsCC.TypedFinite

/-!
# The parallel-composition axis on the `Phi` carrier

`Phi I U` is the carrier every CC endpoint of this estate lives on
(`CC.SecurelyConstructs` statements are all phrased over it), so this is
where Abstract Cryptography's `∥` must be installed for the canonical
statement `AUT ∥ KEY ⟶ SEC` to be *expressible*.  The mathematics is
entirely on the RS side (`RandomSystems.TypedParallel`): parallel
composition of typed resources with unique decomposition and eq. (3)
non-expansion, obtained by transporting P1's flat parallel through metric
full abstraction and the relabelling isometry.  This module only exposes
it through AC's classes:

* `Par (Phi I U)` — `R ∥ R'` is `Resource.parallel`: the same interfaces,
  each carrying both components' signatures (`sumBoundary`), with the
  parallel of the contextual classes in the fibre;
* `IsNonexpandingPar (Phi I U)` — MauRen11 §4.4 Definition 3 / eq. (3),
  repackaging `Resource.edist_parallel_le`;
* `Resource.par_inj` / `Resource.par_ne_left` — uniqueness of the parallel
  decomposition and its non-vacuity receipt, in `∥` notation.

**Deliberately absent** (STATUS §11.5, settled by counterexample): a `par`
constructor on `ConverterTerm`/`Gamma`, `Par (Protocol I U)`, and
`SMulParClass`.  The parallel *action* is not non-expanding — a mixture of
a product law with a correlating one does not decompose, so the
componentwise action pins it while moving the product — and
`ConverterTerm.eval` lands in `nonexpandingEnd (Phi I U)`, so a
protocol-side `par` would assert something false.  What the canonical CC
statement needs is only the resource-side `∥`: in `π • (AUT ∥ KEY) ≈ SEC`
the protocol `π` is *serial*.

**Consequence, measured.**  The two classes installed here are the
resource-side *half* of AC's parallel requirement.  AC's five parallel rules
(`eball_par`, `relax_par` and `simulator_par` on the construction judgment,
plus `CC.SecurelyConstructs.par`/`par_left`) each additionally require `Par M` on
the protocol monoid and `SMulParClass M Φ`, and the estate's only instance of
either is `RandomSystemsCC.ResourceParallel`'s syntactic `ParProtocol U`, on
the single-code `ResourceLift` carrier.  That pattern escapes §11.5 by
interpreting into plain `Function.End` rather than `nonexpandingEnd`, so it
asserts no metric law; porting it here is deferred (§11.5 prefers restricting
the action to the decomposable sub-carrier over totalizing, and it has no
consumer on `Phi` today).  So `AUT ∥ KEY ⟶ SEC` is now *expressible* on
`Phi`, but AC's parallel composition rules are not yet *applicable* to it,
and `RandomSystemsCC.ParallelChecks.extract_constructs_par` remains the
estate's only firing of that calculus.
-/

namespace RandomSystemsCC.TypedFinite

open AbstractCrypto
open RandomSystems.CR18.TypedResource
open scoped AbstractCrypto

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [DecidableEq I] [DecidableEq U.Code] [HasSumCode U]

/-- AC's parallel operator on the `Phi` carrier is the typed resource
parallel. -/
noncomputable instance Resource.instPar : Par (Phi I U) :=
  ⟨Resource.parallel⟩

namespace Resource

theorem par_def (leftResource rightResource : Phi I U) :
    leftResource ∥ rightResource =
      Resource.parallel leftResource rightResource :=
  rfl

@[simp]
theorem par_boundary (leftResource rightResource : Phi I U) :
    (leftResource ∥ rightResource).boundary =
      sumBoundary leftResource.boundary rightResource.boundary :=
  rfl

/-- **The parallel decomposition of a `Phi` resource is unique**: sum
boundaries are injective and the parallel decomposition of a contextual
class is unique (`DependentRandomSystem.parallel_inj`, the typed mirror of
strict cancellation). -/
theorem par_inj {leftA leftB rightA rightB : Phi I U}
    (same : leftA ∥ rightA = leftB ∥ rightB) :
    leftA = leftB ∧ rightA = rightB :=
  Resource.parallel_inj same

/-- Non-vacuity receipt for `Par (Phi I U)`: the operation genuinely
remembers both components. -/
theorem par_ne_left {leftA leftB rightComponent : Phi I U}
    (different : leftA ≠ leftB) :
    leftA ∥ rightComponent ≠ leftB ∥ rightComponent :=
  Resource.parallel_ne_left different

end Resource

/-- **MauRen11 §4.4 Definition 3 / eq. (3) on the `Phi` carrier**: the
contextual metric is `‖`-non-expanding.  This is the metric premise of
`CC.SecurelyConstructs.par`/`par_left`, so the parallel composition rules
of constructive cryptography now apply to typed random-systems
resources. -/
instance : IsNonexpandingPar (Phi I U) :=
  ⟨Resource.edist_parallel_le⟩

end RandomSystemsCC.TypedFinite
