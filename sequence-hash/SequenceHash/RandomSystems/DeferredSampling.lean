import RandomSystems.Counting
import RandomSystems.Dist

/-!
# Deferred sampling along an adaptive fresh path

An eager random function may be evaluated at points chosen from its previous
answers.  This module proves the exact lazy/deferred replacement needed by the
SequenceHash graph argument: on answer vectors whose induced query points are
distinct, the vector has the same mass as an independent uniform vector.

The final restricted-law equality is a conditional-equivalence statement at
the distribution level.  It is not a heuristic lazy-sampling assertion: the
proof identifies every adaptive transcript fibre with an ordinary
multi-point function fibre and counts it exactly.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems

universe u v

/-- An adaptive query schedule.  At step `m`, the next primitive point may
depend on all `m` previous answers. -/
structure AdaptiveSchedule (Q : Type u) (A : Type v) where
  next : {m : ℕ} → (Fin m → A) → Q

/-- Eager evaluation of an adaptive schedule against a complete function. -/
def adaptiveRun {Q : Type u} {A : Type v}
    (schedule : AdaptiveSchedule Q A) (oracle : Q → A) :
    (m : ℕ) → Fin m → A
  | 0 => Fin.elim0
  | m + 1 =>
      let history := adaptiveRun schedule oracle m
      Fin.snoc history (oracle (schedule.next history))

@[simp]
theorem adaptiveRun_zero {Q : Type u} {A : Type v}
    (schedule : AdaptiveSchedule Q A) (oracle : Q → A) :
    adaptiveRun schedule oracle 0 = Fin.elim0 := by
  rfl

@[simp]
theorem adaptiveRun_succ {Q : Type u} {A : Type v}
    (schedule : AdaptiveSchedule Q A) (oracle : Q → A) (m : ℕ) :
    adaptiveRun schedule oracle (m + 1) =
      Fin.snoc (adaptiveRun schedule oracle m)
        (oracle (schedule.next (adaptiveRun schedule oracle m))) := by
  rfl

/-- Primitive point prescribed at coordinate `i` by a completed answer
vector.  Only the strict prefix before `i` is supplied to the schedule. -/
def adaptivePointAt {Q : Type u} {A : Type v} {m : ℕ}
    (schedule : AdaptiveSchedule Q A) (values : Fin m → A)
    (index : Fin m) : Q :=
  schedule.next fun earlier : Fin index.1 =>
    values ⟨earlier.1, Nat.lt_trans earlier.2 index.2⟩

theorem adaptivePointAt_castSucc {Q : Type u} {A : Type v} {m : ℕ}
    (schedule : AdaptiveSchedule Q A) (values : Fin (m + 1) → A)
    (index : Fin m) :
    adaptivePointAt schedule values index.castSucc =
      adaptivePointAt schedule (Fin.init values) index := by
  apply congrArg schedule.next
  funext earlier
  rfl

theorem adaptivePointAt_last {Q : Type u} {A : Type v} {m : ℕ}
    (schedule : AdaptiveSchedule Q A) (values : Fin (m + 1) → A) :
    adaptivePointAt schedule values (Fin.last m) =
      schedule.next (Fin.init values) := by
  apply congrArg schedule.next
  funext earlier
  rfl

/-- An answer vector is fresh when the adaptive points it induces are all
distinct.  This is exactly the no-join premise used by the MD graph. -/
def FreshAt {Q : Type u} {A : Type v} {m : ℕ}
    (schedule : AdaptiveSchedule Q A) (values : Fin m → A) : Prop :=
  Function.Injective (adaptivePointAt schedule values)

/-- Fibre characterization of adaptive evaluation.  Lean proves it by
splitting a vector into its generated prefix and final coordinate; no
probability enters here. -/
theorem adaptiveRun_eq_iff {Q : Type u} {A : Type v}
    (schedule : AdaptiveSchedule Q A) (oracle : Q → A)
    {m : ℕ} (values : Fin m → A) :
    adaptiveRun schedule oracle m = values ↔
      ∀ index, oracle (adaptivePointAt schedule values index) = values index := by
  induction m with
  | zero =>
      constructor
      · intro _equal index
        exact Fin.elim0 index
      · intro _assignments
        exact Subsingleton.elim _ _
  | succ m inductionHypothesis =>
      constructor
      · intro equal index
        have prefixEqual :
            adaptiveRun schedule oracle m = Fin.init values := by
          have := congrArg Fin.init equal
          simpa using this
        rcases Fin.eq_castSucc_or_eq_last index with ⟨earlier, rfl⟩ | rfl
        · have assignment :=
            (inductionHypothesis (Fin.init values)).mp prefixEqual earlier
          simpa only [adaptivePointAt_castSucc] using assignment
        · rw [adaptivePointAt_last, ← prefixEqual]
          have finalEqual := congrFun equal (Fin.last m)
          simpa using finalEqual
      · intro assignments
        have prefixAssignments : ∀ index : Fin m,
            oracle (adaptivePointAt schedule (Fin.init values) index) =
              Fin.init values index := by
          intro index
          have assignment := assignments index.castSucc
          simpa only [adaptivePointAt_castSucc] using assignment
        have prefixEqual :
            adaptiveRun schedule oracle m = Fin.init values :=
          (inductionHypothesis (Fin.init values)).mpr prefixAssignments
        have finalAssignment := assignments (Fin.last m)
        rw [adaptivePointAt_last] at finalAssignment
        rw [adaptiveRun_succ, prefixEqual, finalAssignment]
        exact Fin.snoc_init_self values

/-- Exact mass of one fresh adaptive transcript fibre. -/
theorem uniform_mass_adaptiveRun_eq
    {Q : Type u} {A : Type v}
    [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (schedule : AdaptiveSchedule Q A) {m : ℕ}
    (values : Fin m → A) (fresh : FreshAt schedule values) :
    (Dist.uniform (Q → A)).mass
        (fun oracle => adaptiveRun schedule oracle m = values) =
      1 / (Fintype.card A : ℝ) ^ m := by
  classical
  have eventEquality :
      ((Finset.univ : Finset (Q → A)).filter
          (fun oracle => adaptiveRun schedule oracle m = values)) =
        (Finset.univ.filter fun oracle : Q → A =>
          (fun index => oracle (adaptivePointAt schedule values index)) =
            values) := by
    ext oracle
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [adaptiveRun_eq_iff]
    exact funext_iff.symm
  rw [Dist.uniform_mass_eq_card_filter, eventEquality,
    RandomSystems.CR18.Counting.card_function_fiber_multipoint
      (adaptivePointAt schedule values) values fresh,
    Fintype.card_fun]
  have pointCount : m ≤ Fintype.card Q := by
    simpa using Fintype.card_le_of_injective
      (adaptivePointAt schedule values) fresh
  have cardNonzero : (Fintype.card A : ℝ) ≠ 0 := by
    positivity
  simp only [Nat.cast_pow]
  have powerSplit :
      (Fintype.card A : ℝ) ^ Fintype.card Q =
        (Fintype.card A : ℝ) ^ (Fintype.card Q - m) *
          (Fintype.card A : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel pointCount]
  rw [powerSplit]
  field_simp

/-- Restricted eager evaluation equals restricted independent deferred
sampling for every good predicate that guarantees freshness. -/
theorem restrict_adaptiveRun_uniform_eq_restrict_uniform
    {Q : Type u} {A : Type v}
    [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (schedule : AdaptiveSchedule Q A) (m : ℕ)
    (good : (Fin m → A) → Prop) [DecidablePred good]
    (goodFresh : ∀ values, good values → FreshAt schedule values) :
    (Dist.fTransform (fun oracle => adaptiveRun schedule oracle m)
          (Dist.uniform (Q → A))).restrict good =
      (Dist.uniform (Fin m → A)).restrict good := by
  ext values
  rw [Dist.restrict_apply, Dist.restrict_apply]
  by_cases isGood : good values
  · rw [if_pos isGood, if_pos isGood,
      Dist.fTransform_apply_eq_mass,
      uniform_mass_adaptiveRun_eq schedule values (goodFresh values isGood),
      Dist.uniform_apply, Fintype.card_fun, Fintype.card_fin]
    simp only [Nat.cast_pow]
  · rw [if_neg isGood, if_neg isGood]

/-- Any deterministic observation of the good deferred transcript has the
same subdistribution in the eager and lazy representatives. -/
theorem fTransform_restrict_adaptiveRun_uniform_eq
    {Q : Type u} {A : Type v} {T : Type*}
    [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (schedule : AdaptiveSchedule Q A) (m : ℕ)
    (good : (Fin m → A) → Prop) [DecidablePred good]
    (goodFresh : ∀ values, good values → FreshAt schedule values)
    (observe : (Fin m → A) → T) :
    Dist.fTransform observe
        ((Dist.fTransform (fun oracle => adaptiveRun schedule oracle m)
          (Dist.uniform (Q → A))).restrict good) =
      Dist.fTransform observe
        ((Dist.uniform (Fin m → A)).restrict good) := by
  rw [restrict_adaptiveRun_uniform_eq_restrict_uniform
    schedule m good goodFresh]

/-- The restricted-law identity also identifies the probability of the first
freshness failure.  This complement form is what a first-bad graph argument
uses: once `good` implies that all adaptively selected primitive points are
distinct, the eager random-function execution and an independent answer tape
put exactly the same mass on `not good`. -/
theorem adaptiveRun_compl_mass_eq_uniform
    {Q : Type u} {A : Type v}
    [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (schedule : AdaptiveSchedule Q A) (m : ℕ)
    (good : (Fin m → A) → Prop) [DecidablePred good]
    (goodFresh : ∀ values, good values → FreshAt schedule values) :
    (Dist.fTransform (fun oracle => adaptiveRun schedule oracle m)
      (Dist.uniform (Q → A))).mass (fun values => ¬ good values) =
      (Dist.uniform (Fin m → A)).mass (fun values => ¬ good values) := by
  let eager := Dist.fTransform (fun oracle => adaptiveRun schedule oracle m)
    (Dist.uniform (Q → A))
  let lazy := Dist.uniform (Fin m → A)
  have restricted : eager.restrict good = lazy.restrict good := by
    exact restrict_adaptiveRun_uniform_eq_restrict_uniform
      schedule m good goodFresh
  have goodMass : eager.mass good = lazy.mass good := by
    have weightEquality := congrArg Dist.weight restricted
    simpa only [Dist.weight_restrict] using weightEquality
  have eagerWeight : eager.weight = 1 := by
    dsimp only [eager]
    rw [Dist.weight_fTransform, Dist.uniform_isProbDist.weight_eq]
  have lazyWeight : lazy.weight = 1 := Dist.uniform_isProbDist.weight_eq
  have eagerPartition := Dist.mass_add_compl eager good
  have lazyPartition := Dist.mass_add_compl lazy good
  dsimp only [eager, lazy] at goodMass ⊢
  linarith

/-- If every completed answer vector induces distinct adaptive query points,
then eager evaluation of a uniform random function produces an exactly
uniform answer tape.  This is the unconditional form used by the cached
exposure construction: repeated semantic queries are routed to disjoint
padding coordinates, so freshness becomes a theorem rather than a premise on
the retained event. -/
theorem adaptiveRun_uniform_eq_uniform_of_fresh
    {Q : Type u} {A : Type v}
    [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (schedule : AdaptiveSchedule Q A) (m : ℕ)
    (fresh : ∀ values : Fin m → A, FreshAt schedule values) :
    Dist.fTransform (fun oracle => adaptiveRun schedule oracle m)
        (Dist.uniform (Q → A)) =
      Dist.uniform (Fin m → A) := by
  ext values
  rw [Dist.fTransform_apply_eq_mass,
    uniform_mass_adaptiveRun_eq schedule values (fresh values),
    Dist.uniform_apply, Fintype.card_fun, Fintype.card_fin]
  simp only [Nat.cast_pow]

end MDSimulator
end RandomSystemsModel
end SequenceHash
