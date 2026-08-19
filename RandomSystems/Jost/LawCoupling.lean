/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ResourceMachine
import RandomSystems.HTechnique.Derivation

/-!
# Coupling congruence for package laws (`Machine.lawOf`)

The reasoning principle behind a Jost-§2.2.6-style "proof by observing": two
seeded pseudocode boxes denote the *same* law over deterministic resources
whenever their seeds can be coupled so that every coupled pair of fibres is
the same deterministic system.  Per fibre, that equality is discharged by
`Machine.toDDS_eq_of_bisim` — so the paper step "couple the two systems on
the key and compare answers along the transcript" becomes: name a coupling,
name a bisimulation relation.

Three forms:

* `Machine.lawOf_congr` — the diagonal case (shared seed law), which is what
  both leaves of Prop. 2.2.17 use: the identity coupling of the key-and-tape
  seed.
* `Machine.lawOf_eq_of_coupling` — the general equality case, for pairs
  whose seed spaces differ (a one-time-pad-style leaf couples a key against
  a simulator's ciphertext choice).
* `Machine.lawOf_lawStatDist_le_of_coupling` — the Δ-face: when the coupled
  fibres agree only off a bad seed set, the law distance is bounded by the
  joint mass of the bad set.  This is the package-level conditional
  equivalence entry point (e.g. statistical rather than perfect correctness
  in a Prop.-2.2.17 leaf).

Couplings are stated by their two pushforward marginals directly, because
the seed spaces are heterogeneous; the homogeneous `DistCoupling` record of
`Coupling.lean` does not apply.  The `Dist`-level content lives upstream:
`Dist.fTransform_congr` / `Dist.fTransform_eq_of_coupling` (`Dist.lean`) and
`HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne`
(`HTechnique/Derivation.lean`).
-/

namespace RandomSystems.CR18.TypedResource.Machine

open RandomSystems (Dist)
open scoped RandomSystems.CR18.HTechniqueDerivation

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}} {sigma : Boundary U I}

/-- **Diagonal congruence for package laws**: one seed law, two seed-indexed
packages whose fibres denote the same resource at every seed in the support.
This is the identity-coupling case, and it is the entire probabilistic
content of a Prop-2.2.17-style leaf: the per-seed hypothesis is discharged by
`toDDS_eq_of_bisim`. -/
theorem lawOf_congr {Omega : Type*}
    {machine₁ machine₂ : Omega → Machine U sigma} {seed : Dist Omega}
    (normalized : seed.isProbDist)
    (fibres : ∀ omega ∈ seed.support,
      (machine₁ omega).toDDS = (machine₂ omega).toDDS) :
    lawOf machine₁ seed normalized = lawOf machine₂ seed normalized :=
  Subtype.ext (Dist.fTransform_congr seed fibres)

/-- **Coupling congruence for package laws** (the general form of
`lawOf_congr`): if the two seed laws admit a joint law with the right
marginals, and every coupled seed pair denotes the same resource, the two
package laws are equal.  "Couple on the key, then compare answers along the
transcript" — the transcript comparison is `toDDS_eq_of_bisim` per coupled
pair. -/
theorem lawOf_eq_of_coupling {Omega₁ Omega₂ : Type*}
    {machine₁ : Omega₁ → Machine U sigma} {machine₂ : Omega₂ → Machine U sigma}
    {seed₁ : Dist Omega₁} {seed₂ : Dist Omega₂}
    (normalized₁ : seed₁.isProbDist) (normalized₂ : seed₂.isProbDist)
    (joint : Dist (Omega₁ × Omega₂))
    (marginal_fst : Dist.fTransform Prod.fst joint = seed₁)
    (marginal_snd : Dist.fTransform Prod.snd joint = seed₂)
    (fibres : ∀ pair ∈ joint.support,
      (machine₁ pair.1).toDDS = (machine₂ pair.2).toDDS) :
    lawOf machine₁ seed₁ normalized₁ = lawOf machine₂ seed₂ normalized₂ :=
  Subtype.ext
    (Dist.fTransform_eq_of_coupling joint marginal_fst marginal_snd fibres)

/-- **Bad-set coupling bound for package laws** (the Δ-face of
`lawOf_eq_of_coupling`): if the coupled fibres denote the same resource off
a bad seed set, the law distance is bounded by the joint mass of the bad
set.  With `lawStatDist_eq_statDist` this transports to `statDist` on
finite carriers, and through the fundamental-theorem layer to any
transcript advantage. -/
theorem lawOf_lawStatDist_le_of_coupling {Omega₁ Omega₂ : Type*}
    {machine₁ : Omega₁ → Machine U sigma} {machine₂ : Omega₂ → Machine U sigma}
    {seed₁ : Dist Omega₁} {seed₂ : Dist Omega₂}
    (normalized₁ : seed₁.isProbDist) (normalized₂ : seed₂.isProbDist)
    {joint : Dist (Omega₁ × Omega₂)} (jointNonNeg : joint.NonNeg)
    (marginal_fst : Dist.fTransform Prod.fst joint = seed₁)
    (marginal_snd : Dist.fTransform Prod.snd joint = seed₂)
    (Bad : Omega₁ × Omega₂ → Prop)
    (fibres : ∀ pair ∈ joint.support, ¬ Bad pair →
      (machine₁ pair.1).toDDS = (machine₂ pair.2).toDDS) :
    HTechniqueDerivation.lawStatDist
        (lawOf machine₁ seed₁ normalized₁).val
        (lawOf machine₂ seed₂ normalized₂).val ≤
      joint.mass Bad := by
  refine (HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne
    (fun omega => (machine₁ omega).toDDS) (fun omega => (machine₂ omega).toDDS)
    jointNonNeg marginal_fst marginal_snd).trans ?_
  exact Dist.mass_mono_on_support jointNonNeg fun pair mem disagree =>
    Classical.byContradiction fun notBad => disagree (fibres pair mem notBad)

end RandomSystems.CR18.TypedResource.Machine
