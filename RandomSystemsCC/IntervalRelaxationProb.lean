/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DistCoupling
import RandomSystemsCC.IntervalRelaxation

/-!
# The from-until relaxations commute for *probabilistic* resources

`RandomSystemsCC.IntervalRelaxation` answers the open question of Jost's p. 101
on the deterministic event carrier `DependentDDS (withEvents U N) σ`.  Jost's
resources are random systems, so the theorem there covers only the deterministic
sub-case.  This module lifts it to the probabilistic carrier, in the two shapes
that carrier has here:

* laws — `DependentPDS (withEvents U N) σ = Dist (DependentDDS (withEvents U N) σ)`;
* normalized laws — `DependentPDS.Prob (withEvents U N) σ`, the carrier directly
  underneath the contextual quotient of `Resource`.

At both levels

    (𝓡^{[P₁})^{P₂]}  =  𝓡^{[P₁,P₂]}  =  (𝓡^{P₂]})^{[P₁}

(`probFromThenUntil_eq_probIntervalRelax`, `probUntilThenFrom_eq_probIntervalRelax`,
`normFromThenUntil_eq_normIntervalRelax`, `normUntilThenFrom_eq_normIntervalRelax`),
Theorem 5.3.12's union over `n` still collapses at `n = 2`
(`probIntervalRelax_union_collapse`), and the specification level follows
(`probSpec_untilRelax_fromRelax`, `probSpec_fromRelax_untilRelax`).

## What a projection of a *law* is

Applying a deterministic wrapper to a law is applying it to every sample, i.e.
the pushforward — this is exactly how `RandomSystems.CR18.StrictContext.applyLaw`
attaches a deterministic converter to a `PFunPDS`.  So `until_{P₂}` and
`from_{P₁}` act on laws as `Dist.fTransform`, and the relaxations are again
fibres of projections, now of `lawUntilP`, `lawFromP` and `lawIntervalP`.

## The two new ingredients

**One inclusion is a factorization.**  `until_{P₂} ∘ from_{P₁}` factors through
`from_{P₁}` by definition, and it factors through `until_{P₂}` as well:
`untilP_fromP_untilP` says `until_{P₂}(from_{P₁}(until_{P₂}(b))) =
until_{P₂}(from_{P₁}(b))`, because `from_{P₁}` reads its argument only at the
accepted sub-transcript, which is a sublist of the transcript and so still in the
until-window.  Pushforward is functorial, so both factorizations survive to laws
and give `(𝓡^{[P₁})^{P₂]} ⊆ 𝓡^{[P₁,P₂]}` without any coupling.

**The other inclusion is a coupling.**  The deterministic witness `glue P₁ P₂ R S`
needs *one* `R` and *one* `S` with `until_{P₂}(from_{P₁}(R)) =
until_{P₂}(from_{P₁}(S))`.  Two laws with equal interval-projection need not be
supported on such pairs sample-by-sample — they only agree in aggregate — so the
lift is a measure-gluing step: `Dist.exists_coupling_of_fTransform_eq` produces a
joint law carried by the fibre relation of the interval projection, and pushing
it forward along `fun p => glue P₁ P₂ p.1 p.2` is the middle law.  Its two
projections are the required ones because the glued sample agrees with its left
component through `from_{P₁}` and with its right component through `until_{P₂}`
(`fromP_answers_glue`, `untilP_answers_glue`), and a pushforward only sees the
map on the support (`Dist.fTransform_congr`).  The coupling preserves total mass,
so the witness is normalized whenever the given law is — that is what carries the
statement to `DependentPDS.Prob`.

## The contextual quotient

`Resource I U` is `DependentRandomSystem`, a quotient of `DependentPDS.Prob` by
strict contextual equivalence.  `randomSystem_fromThenUntil_eq_intervalRelax`
carries the collapse there, but *conditionally*: it takes as hypotheses that the
three projections factor through the quotient at all.  That hypothesis is not
discharged here, and it is not a technicality — it is the statement that strict
contextual equivalence determines the law over projected behaviours, i.e. that
the strict-context action on `DependentPDS` is faithful.
`exists_randomSystem_collapse_of_faithful` states that dependence as a Lean
hypothesis rather than as prose: assume faithfulness and the projections are
`Quotient.lift`s and the collapse holds on the quotient carrier outright.
-/

namespace RandomSystemsCC.IntervalWise

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Events

universe c i u

/-- **A law over projected behaviours** — what `until_P` and `from_P` turn a
probabilistic resource into.  Named because `Dist` alone is ambiguous with
Mathlib's metric-space class in this namespace. -/
abbrev BehaviourLaw {I : Type i} (U : SignatureUniverse.{c, u, u}) (N : Type u)
    (σ : Boundary U I) : Type (max u i) :=
  RandomSystems.Dist (Answers U N σ)

/-! ## The projection identity behind the factorization -/

section Factorization

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- **`until_{P₂} ∘ from_{P₁}` factors through `until_{P₂}`.**  Jost's p. 101
observation is that the two *projections* commute; this is the sharper fact the
composite relaxation needs, namely that pre-composing with `until_{P₂}` changes
nothing.  The reason is structural: `from_{P₁}` reads its argument at the
accepted sub-transcript, which is a sublist of the transcript, and the
until-window is sublist-closed. -/
theorem untilP_fromP_untilP (P₁ P₂ : CompositeEvent N) (behaviour : Answers U N σ) :
    untilP P₂ (fromP P₁ (untilP P₂ behaviour)) = untilP P₂ (fromP P₁ behaviour) := by
  classical
  funext transcript
  by_cases window : UntilWindow (U := U) (σ := σ) P₂ transcript
  · rw [untilP_apply_of_window window, untilP_apply_of_window window]
    by_cases last : AcceptsLast (U := U) (σ := σ) P₁ transcript
    · rw [fromP_apply_of_acceptsLast last, fromP_apply_of_acceptsLast last]
      exact untilP_apply_of_window (Window.sublist (accepted_sublist P₁ transcript) window)
    · rw [fromP_apply_of_not_acceptsLast last, fromP_apply_of_not_acceptsLast last]
  · rw [untilP_apply_of_not_window window, untilP_apply_of_not_window window]

end Factorization

/-! ## The glued witness, read through the two projections -/

section Glue

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
variable {P₁ P₂ : CompositeEvent N} {R S : DependentDDS (withEvents U N) σ}

/-- Through `from_{P₁}` the glued witness is its left component. -/
theorem fromP_answers_glue (agree : AgreeOn (IntervalWindow P₁ P₂) R S) :
    fromP P₁ (answers (glue P₁ P₂ R S)) = fromP P₁ (answers R) :=
  fromP_eq_iff.2 fun _ window => answers_glue_of_fromWindow agree window

/-- Through `until_{P₂}` the glued witness is its right component. -/
theorem untilP_answers_glue (agree : AgreeOn (IntervalWindow P₁ P₂) R S) :
    untilP P₂ (answers (glue P₁ P₂ R S)) = untilP P₂ (answers S) :=
  untilP_eq_iff.2 fun _ window => answers_glue_of_untilWindow agree window

end Glue

/-! ## The projections of a law -/

section Laws

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- **Definition 5.3.1 on a law**: `until_{P₂}` applied to every sample. -/
noncomputable def lawUntilP (P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : BehaviourLaw U N σ :=
  Dist.fTransform (fun R => untilP P₂ (answers R)) law

/-- **Definition 5.3.6 on a law**: `from_{P₁}` applied to every sample. -/
noncomputable def lawFromP (P₁ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : BehaviourLaw U N σ :=
  Dist.fTransform (fun R => fromP P₁ (answers R)) law

/-- **Definition 5.3.11's projection on a law**, in the printed orientation. -/
noncomputable def lawIntervalP (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : BehaviourLaw U N σ :=
  Dist.fTransform (fun R => untilP P₂ (fromP P₁ (answers R))) law

/-- The interval projection of a law factors through its from-projection. -/
theorem lawIntervalP_eq_fTransform_lawFromP (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) :
    lawIntervalP P₁ P₂ law =
      Dist.fTransform (untilP (U := U) (σ := σ) P₂) (lawFromP P₁ law) := by
  simp only [lawIntervalP, lawFromP, Dist.fTransform_comp]
  rfl

/-- The interval projection of a law factors through its until-projection too —
this is `untilP_fromP_untilP` pushed forward. -/
theorem lawIntervalP_eq_fTransform_lawUntilP (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) :
    lawIntervalP P₁ P₂ law =
      Dist.fTransform (fun behaviour => untilP P₂ (fromP P₁ behaviour)) (lawUntilP P₂ law) := by
  simp only [lawIntervalP, lawUntilP, Dist.fTransform_comp]
  exact congrArg (fun projection => Dist.fTransform projection law)
    (funext fun R => (untilP_fromP_untilP P₁ P₂ (answers R)).symm)

/-! ## The relaxations of a law -/

/-- **Jost Definition 5.3.2 for a probabilistic resource**, `𝓡^{P₂]}`. -/
noncomputable def probUntilRelax (P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : Set (DependentPDS (withEvents U N) σ) :=
  fibre (lawUntilP P₂) law

/-- **Jost Definition 5.3.7 for a probabilistic resource**, `𝓡^{[P₁}`. -/
noncomputable def probFromRelax (P₁ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : Set (DependentPDS (withEvents U N) σ) :=
  fibre (lawFromP P₁) law

/-- **Jost Definition 5.3.11 for a probabilistic resource**, `𝓡^{[P₁,P₂]}`. -/
noncomputable def probIntervalRelax (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : Set (DependentPDS (withEvents U N) σ) :=
  fibre (lawIntervalP P₁ P₂) law

/-- `(𝓡^{[P₁})^{P₂]}` for laws. -/
noncomputable def probFromThenUntil (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : Set (DependentPDS (withEvents U N) σ) :=
  fibreComp (lawFromP P₁) (lawUntilP P₂) law

/-- `(𝓡^{P₂]})^{[P₁}` for laws. -/
noncomputable def probUntilThenFrom (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS (withEvents U N) σ) : Set (DependentPDS (withEvents U N) σ) :=
  fibreComp (lawUntilP P₂) (lawFromP P₁) law

/-! ## The middle law -/

/-- **The witness at the level of laws.**  Two laws with the same interval
projection are joined by a coupling carried by the fibre relation of that
projection; gluing sample-wise along the coupling produces a law that is the
first one through `from_{P₁}` and the second one through `until_{P₂}`.  The total
mass is preserved, which is what carries the statement to normalized laws. -/
theorem exists_middle_of_lawIntervalP_eq (P₁ P₂ : CompositeEvent N)
    (law other : DependentPDS (withEvents U N) σ)
    (project : lawIntervalP P₁ P₂ other = lawIntervalP P₁ P₂ law) :
    ∃ middle : DependentPDS (withEvents U N) σ, middle.weight = law.weight ∧
      lawFromP P₁ middle = lawFromP P₁ law ∧ lawUntilP P₂ other = lawUntilP P₂ middle := by
  obtain ⟨joint, carried, marginalFst, marginalSnd⟩ :=
    Dist.exists_coupling_of_fTransform_eq
      (fun R => untilP P₂ (fromP P₁ (answers R))) law other project.symm
  have agree : ∀ pair ∈ joint.support, AgreeOn (IntervalWindow P₁ P₂) pair.1 pair.2 :=
    fun pair member => untilP_fromP_eq_iff.1 (carried pair member)
  refine ⟨Dist.fTransform (fun pair => glue P₁ P₂ pair.1 pair.2) joint, ?_, ?_, ?_⟩
  · rw [Dist.weight_fTransform, ← marginalFst, Dist.weight_fTransform]
  · rw [← marginalFst]
    simp only [lawFromP, Dist.fTransform_comp]
    exact Dist.fTransform_congr _
      (fun pair member => fromP_answers_glue (agree pair member))
  · rw [← marginalSnd]
    simp only [lawUntilP, Dist.fTransform_comp]
    exact (Dist.fTransform_congr _
      (fun pair member => untilP_answers_glue (agree pair member))).symm

/-- The middle law can be chosen **non-negative** when both ends are — the
form the `Prob`-level collapse needs.  Same construction, over the
non-negative gluing witness. -/
theorem exists_nonneg_middle_of_lawIntervalP_eq (P₁ P₂ : CompositeEvent N)
    {law other : DependentPDS (withEvents U N) σ}
    (hlaw : law.NonNeg) (hother : other.NonNeg)
    (project : lawIntervalP P₁ P₂ other = lawIntervalP P₁ P₂ law) :
    ∃ middle : DependentPDS (withEvents U N) σ, middle.NonNeg ∧
      middle.weight = law.weight ∧
      lawFromP P₁ middle = lawFromP P₁ law ∧
      lawUntilP P₂ other = lawUntilP P₂ middle := by
  obtain ⟨joint, jointNonNeg, carried, marginalFst, marginalSnd⟩ :=
    Dist.exists_nonneg_coupling_of_fTransform_eq
      (fun R => untilP P₂ (fromP P₁ (answers R))) hlaw hother project.symm
  have agree : ∀ pair ∈ joint.support, AgreeOn (IntervalWindow P₁ P₂) pair.1 pair.2 :=
    fun pair member => untilP_fromP_eq_iff.1 (carried pair member)
  refine ⟨Dist.fTransform (fun pair => glue P₁ P₂ pair.1 pair.2) joint,
    jointNonNeg.fTransform _, ?_, ?_, ?_⟩
  · rw [Dist.weight_fTransform, ← marginalFst, Dist.weight_fTransform]
  · rw [← marginalFst]
    simp only [lawFromP, Dist.fTransform_comp]
    exact Dist.fTransform_congr _
      (fun pair member => fromP_answers_glue (agree pair member))
  · rw [← marginalSnd]
    simp only [lawUntilP, Dist.fTransform_comp]
    exact (Dist.fTransform_congr _
      (fun pair member => untilP_answers_glue (agree pair member))).symm

/-- **The factorization inclusion.**  A middle law that is `law` through
`from_{P₁}` and `other` through `until_{P₂}` forces the two interval projections
to agree, because the interval projection factors through *each* of the two
atomic ones. -/
theorem lawIntervalP_eq_of_middle {P₁ P₂ : CompositeEvent N}
    {law other middle : DependentPDS (withEvents U N) σ}
    (hFrom : lawFromP P₁ middle = lawFromP P₁ law)
    (hUntil : lawUntilP P₂ other = lawUntilP P₂ middle) :
    lawIntervalP P₁ P₂ other = lawIntervalP P₁ P₂ law := by
  rw [lawIntervalP_eq_fTransform_lawUntilP, hUntil,
    ← lawIntervalP_eq_fTransform_lawUntilP, lawIntervalP_eq_fTransform_lawFromP, hFrom,
    ← lawIntervalP_eq_fTransform_lawFromP]

/-! ## The collapse for laws -/

variable (P₁ P₂ : CompositeEvent N) (law : DependentPDS (withEvents U N) σ)

/-- **The collapse for probabilistic resources**, Jost's printed orientation:
`(𝓡^{[P₁})^{P₂]} = 𝓡^{[P₁,P₂]}`. -/
theorem probFromThenUntil_eq_probIntervalRelax :
    probFromThenUntil P₁ P₂ law = probIntervalRelax P₁ P₂ law := by
  ext other
  constructor
  · intro member
    obtain ⟨middle, hMiddle, hOther⟩ := mem_fibreComp.1 member
    exact mem_fibre.2 (lawIntervalP_eq_of_middle hMiddle hOther)
  · intro member
    obtain ⟨middle, -, hFrom, hUntil⟩ :=
      exists_middle_of_lawIntervalP_eq P₁ P₂ law other (mem_fibre.1 member)
    exact mem_fibreComp.2 ⟨middle, hFrom, hUntil⟩

/-- **The mirror orientation**, free from `fibreComp_swap_of_eq_fibre`:
`(𝓡^{P₂]})^{[P₁} = 𝓡^{[P₁,P₂]}`.  Together with the previous theorem this is the
affirmative answer to Jost's p. 101 question for probabilistic resources. -/
theorem probUntilThenFrom_eq_probIntervalRelax :
    probUntilThenFrom P₁ P₂ law = probIntervalRelax P₁ P₂ law :=
  fibreComp_swap_of_eq_fibre
    (fun law' => probFromThenUntil_eq_probIntervalRelax P₁ P₂ law') law

/-- The two two-fold composites agree. -/
theorem probFromThenUntil_eq_probUntilThenFrom :
    probFromThenUntil P₁ P₂ law = probUntilThenFrom P₁ P₂ law :=
  (probFromThenUntil_eq_probIntervalRelax P₁ P₂ law).trans
    (probUntilThenFrom_eq_probIntervalRelax P₁ P₂ law).symm

/-- **Theorem 5.3.12's union collapses at `n = 2`** for probabilistic
resources. -/
theorem probIntervalRelax_union_collapse :
    (⋃ steps : List Bool, fibreChain (lawFromP P₁) (lawUntilP P₂) steps law)
      = probIntervalRelax P₁ P₂ law :=
  iUnion_fibreChain_eq_fibre
    (fun law' => probFromThenUntil_eq_probIntervalRelax P₁ P₂ law') law

/-! ## The specification level for laws -/

variable (spec : Set (DependentPDS (withEvents U N) σ))

/-- `𝓡^{P₂]}` for a specification of laws. -/
noncomputable def probSpecUntilRelax : Set (DependentPDS (withEvents U N) σ) :=
  specFibre (lawUntilP P₂) spec

/-- `𝓡^{[P₁}` for a specification of laws. -/
noncomputable def probSpecFromRelax : Set (DependentPDS (withEvents U N) σ) :=
  specFibre (lawFromP P₁) spec

/-- `𝓡^{[P₁,P₂]}` for a specification of laws. -/
noncomputable def probSpecIntervalRelax : Set (DependentPDS (withEvents U N) σ) :=
  specFibre (lawIntervalP P₁ P₂) spec

/-- The two-fold composite is the specification-level until-relaxation of the
from-relaxation of a single law — the reading of Jost's nested notation, made
unambiguous on the probabilistic carrier. -/
theorem probFromThenUntil_eq_spec :
    probFromThenUntil P₁ P₂ law = probSpecUntilRelax P₂ (probFromRelax P₁ law) := rfl

/-- Likewise for the mirror composite. -/
theorem probUntilThenFrom_eq_spec :
    probUntilThenFrom P₁ P₂ law = probSpecFromRelax P₁ (probUntilRelax P₂ law) := rfl

/-- **The collapse at the specification level for laws**, printed orientation. -/
theorem probSpec_untilRelax_fromRelax :
    probSpecUntilRelax P₂ (probSpecFromRelax P₁ spec) = probSpecIntervalRelax P₁ P₂ spec :=
  specFibre_specFibre_of_collapse
    (fun law' => probFromThenUntil_eq_probIntervalRelax P₁ P₂ law') spec

/-- **The collapse at the specification level for laws**, mirror orientation. -/
theorem probSpec_fromRelax_untilRelax :
    probSpecFromRelax P₁ (probSpecUntilRelax P₂ spec) = probSpecIntervalRelax P₁ P₂ spec :=
  specFibre_specFibre_of_collapse
    (fun law' => probUntilThenFrom_eq_probIntervalRelax P₁ P₂ law') spec

end Laws

/-! ## Normalized laws — the carrier under the contextual quotient -/

section Normalized

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- `until_{P₂}` on a normalized law. -/
noncomputable def normUntilP (P₂ : CompositeEvent N)
    (law : DependentPDS.Prob (withEvents U N) σ) : BehaviourLaw U N σ :=
  lawUntilP P₂ law.val

/-- `from_{P₁}` on a normalized law. -/
noncomputable def normFromP (P₁ : CompositeEvent N)
    (law : DependentPDS.Prob (withEvents U N) σ) : BehaviourLaw U N σ :=
  lawFromP P₁ law.val

/-- The combined projection on a normalized law. -/
noncomputable def normIntervalP (P₁ P₂ : CompositeEvent N)
    (law : DependentPDS.Prob (withEvents U N) σ) : BehaviourLaw U N σ :=
  lawIntervalP P₁ P₂ law.val

variable (P₁ P₂ : CompositeEvent N) (law : DependentPDS.Prob (withEvents U N) σ)

/-- **The collapse for normalized probabilistic resources**, printed
orientation.  The witness stays normalized because a coupling preserves total
mass. -/
theorem normFromThenUntil_eq_normIntervalRelax :
    fibreComp (normFromP P₁) (normUntilP P₂) law = fibre (normIntervalP P₁ P₂) law := by
  ext other
  constructor
  · intro member
    obtain ⟨middle, hMiddle, hOther⟩ := mem_fibreComp.1 member
    exact mem_fibre.2 (lawIntervalP_eq_of_middle
      (law := law.val) (other := other.val) (middle := middle.val) hMiddle hOther)
  · intro member
    obtain ⟨middle, middleNonNeg, mass, hFrom, hUntil⟩ :=
      exists_nonneg_middle_of_lawIntervalP_eq P₁ P₂ law.property.nonNeg
        other.property.nonNeg (mem_fibre.1 member)
    refine mem_fibreComp.2 ⟨⟨middle, middleNonNeg, ?_⟩, hFrom, hUntil⟩
    show middle.weight = 1
    rw [mass]
    exact law.property.2

/-- **The mirror orientation for normalized probabilistic resources.** -/
theorem normUntilThenFrom_eq_normIntervalRelax :
    fibreComp (normUntilP P₂) (normFromP P₁) law = fibre (normIntervalP P₁ P₂) law :=
  fibreComp_swap_of_eq_fibre
    (fun law' => normFromThenUntil_eq_normIntervalRelax P₁ P₂ law') law

end Normalized

/-! ## The contextual quotient

`Resource I U` carries `DependentRandomSystem`, the quotient of
`DependentPDS.Prob` by strict contextual equivalence.  The collapse transports
there as soon as the three projections are *defined* on the quotient, and not
before; the following theorem takes exactly that as its hypothesis and nothing
else, by `fibreComp_quotient_eq_fibre`.

The hypothesis is not a formality.  `lawUntilP` and `lawFromP` are equalities of
*laws over projected behaviours*, whereas contextual equivalence compares only
acceptance masses of deterministic tests.  Discharging the hypothesis is
therefore precisely the claim that the strict-context action on `DependentPDS`
is faithful — that contextually equivalent laws are equal — which this
development does not have. -/

section ContextualQuotient

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
variable [DecidableEq I] [DecidableEq U.Code]

/-- **The collapse on the contextual quotient carrier**, conditional on the three
projections descending to it.  Nothing else is needed: once the projections are
well-defined on classes, a class lies in the composite exactly when its
representatives do. -/
theorem randomSystem_fromThenUntil_eq_intervalRelax (P₁ P₂ : CompositeEvent N)
    {quotFrom quotUntil quotInterval :
      DependentRandomSystem (withEvents U N) σ → BehaviourLaw U N σ}
    (factorFrom : ∀ law : DependentPDS.Prob (withEvents U N) σ,
      quotFrom (DependentRandomSystem.ofProb law) = normFromP P₁ law)
    (factorUntil : ∀ law : DependentPDS.Prob (withEvents U N) σ,
      quotUntil (DependentRandomSystem.ofProb law) = normUntilP P₂ law)
    (factorInterval : ∀ law : DependentPDS.Prob (withEvents U N) σ,
      quotInterval (DependentRandomSystem.ofProb law) = normIntervalP P₁ P₂ law)
    (system : DependentRandomSystem (withEvents U N) σ) :
    fibreComp quotFrom quotUntil system = fibre quotInterval system :=
  fibreComp_quotient_eq_fibre factorFrom factorUntil factorInterval
    (fun law => normFromThenUntil_eq_normIntervalRelax P₁ P₂ law) system

/-- **The mirror orientation on the contextual quotient carrier.** -/
theorem randomSystem_untilThenFrom_eq_intervalRelax (P₁ P₂ : CompositeEvent N)
    {quotFrom quotUntil quotInterval :
      DependentRandomSystem (withEvents U N) σ → BehaviourLaw U N σ}
    (factorFrom : ∀ law : DependentPDS.Prob (withEvents U N) σ,
      quotFrom (DependentRandomSystem.ofProb law) = normFromP P₁ law)
    (factorUntil : ∀ law : DependentPDS.Prob (withEvents U N) σ,
      quotUntil (DependentRandomSystem.ofProb law) = normUntilP P₂ law)
    (factorInterval : ∀ law : DependentPDS.Prob (withEvents U N) σ,
      quotInterval (DependentRandomSystem.ofProb law) = normIntervalP P₁ P₂ law)
    (system : DependentRandomSystem (withEvents U N) σ) :
    fibreComp quotUntil quotFrom system = fibre quotInterval system :=
  fibreComp_swap_of_eq_fibre
    (fun system' => randomSystem_fromThenUntil_eq_intervalRelax P₁ P₂
      factorFrom factorUntil factorInterval system') system

/-- **Exactly what is missing**, as a hypothesis rather than as prose.  If the
strict-context action is faithful — contextually equivalent normalized laws are
equal — then the three projections lift to the quotient by `Quotient.lift` and
the collapse holds on `Resource`'s carrier with no side condition at all.

By `DependentPDS.contextually_equivalent_iff_flatten_equivalent` and
`DependentDDS.flatten_injective`, that hypothesis is equivalent to
`StrictContext.Equivalent left right → left = right` for finite-support laws over
deterministic partial systems, i.e. to strict deterministic tests separating such
laws.  This development does not have it, and it is not specific to the
relaxations: no projection of a law that is finer than acceptance mass descends
to this quotient without it. -/
theorem exists_randomSystem_collapse_of_faithful
    (faithful : ∀ left right : DependentPDS.Prob (withEvents U N) σ,
      DependentPDS.ContextuallyEquivalent left.val right.val → left = right)
    (P₁ P₂ : CompositeEvent N) :
    ∃ quotFrom quotUntil quotInterval :
        DependentRandomSystem (withEvents U N) σ → BehaviourLaw U N σ,
      (∀ law, quotFrom (DependentRandomSystem.ofProb law) = normFromP P₁ law) ∧
        (∀ law, quotUntil (DependentRandomSystem.ofProb law) = normUntilP P₂ law) ∧
        (∀ law, quotInterval (DependentRandomSystem.ofProb law) = normIntervalP P₁ P₂ law) ∧
        ∀ system, fibreComp quotFrom quotUntil system = fibre quotInterval system := by
  have respects : ∀ (projection : DependentPDS.Prob (withEvents U N) σ → BehaviourLaw U N σ)
      (left right : DependentPDS.Prob (withEvents U N) σ),
      (DependentPDS.Prob.contextualSetoid (withEvents U N) σ).r left right →
        projection left = projection right :=
    fun _ left right same => by rw [faithful left right same]
  exact ⟨Quotient.lift (normFromP P₁) (respects _), Quotient.lift (normUntilP P₂) (respects _),
    Quotient.lift (normIntervalP P₁ P₂) (respects _), fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun system => randomSystem_fromThenUntil_eq_intervalRelax P₁ P₂
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) system⟩

end ContextualQuotient

end RandomSystemsCC.IntervalWise
