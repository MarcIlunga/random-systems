/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.SoP.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Broken-circuit cancellation for signed gain-graph expansions

This file contains the finite sign-reversing involution behind the
Dohmen--Trinks form of Whitney's broken-circuit theorem.  It is stated for an
arbitrary finite ordered ground set and an arbitrary additive target, so the
result can be reused before an inclusion-exclusion expression is cast from
integers into reals.

The gain-graph specialization at the end identifies a circuit whose maximal
edge is already implied by the other labelled equations.  Such a circuit has
the same solution set with or without its maximal edge, while the
inclusion-exclusion sign changes.  No probability or positivity is involved:
this is exact cancellation in the signed virtual layer.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.GainGraphCancellation

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-! ## Ordered broken circuits -/

/-- A nonempty finite circuit in an ordered ground type. -/
abbrev OrderedCircuit (alpha : Type*) [LinearOrder alpha] :=
  {C : Finset alpha // C.Nonempty}

namespace OrderedCircuit

variable {alpha : Type*} [LinearOrder alpha]

/-- The distinguished edge is the largest edge of the circuit. -/
def pivot (C : OrderedCircuit alpha) : alpha :=
  C.1.max' C.2

/-- The broken circuit obtained by deleting the distinguished edge. -/
def broken (C : OrderedCircuit alpha) : Finset alpha :=
  C.1.erase C.pivot

@[simp]
theorem pivot_mem (C : OrderedCircuit alpha) : C.pivot ∈ C.1 :=
  Finset.max'_mem C.1 C.2

@[simp]
theorem pivot_not_mem_broken (C : OrderedCircuit alpha) : C.pivot ∉ C.broken := by
  simp [broken]

theorem insert_pivot_broken (C : OrderedCircuit alpha) :
    insert C.pivot C.broken = C.1 := by
  simp [broken, Finset.insert_erase C.pivot_mem]

theorem le_pivot_of_mem {C : OrderedCircuit alpha} {e : alpha} (he : e ∈ C.1) :
    e ≤ C.pivot :=
  Finset.le_max' C.1 e he

end OrderedCircuit

variable {alpha : Type*} [LinearOrder alpha]

/-- Circuits whose broken part is contained in a selected edge family. -/
def witnessCircuits (circuits : Finset (OrderedCircuit alpha))
    (A : Finset alpha) : Finset (OrderedCircuit alpha) :=
  circuits.filter (fun C => C.broken ⊆ A)

/-- Whether an edge family contains one of the designated broken circuits. -/
def ContainsBrokenCircuit (circuits : Finset (OrderedCircuit alpha))
    (A : Finset alpha) : Prop :=
  (witnessCircuits circuits A).Nonempty

/-- The possible pivot edges of broken circuits contained in `A`. -/
def witnessPivots (circuits : Finset (OrderedCircuit alpha))
    (A : Finset alpha) : Finset alpha :=
  (witnessCircuits circuits A).image OrderedCircuit.pivot

theorem witnessPivots_nonempty {circuits : Finset (OrderedCircuit alpha)}
    {A : Finset alpha} (hA : ContainsBrokenCircuit circuits A) :
    (witnessPivots circuits A).Nonempty := by
  rcases hA with ⟨C, hC⟩
  exact ⟨C.pivot, by
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩⟩

/-- The least pivot among all broken circuits contained in `A`.  Choosing the
least pivot is what makes the edge toggle a global involution even when many
broken circuits overlap. -/
def chosenPivot (circuits : Finset (OrderedCircuit alpha)) (A : Finset alpha)
    (hA : ContainsBrokenCircuit circuits A) : alpha :=
  (witnessPivots circuits A).min' (witnessPivots_nonempty hA)

theorem chosenPivot_mem_witnessPivots
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A) :
    chosenPivot circuits A hA ∈ witnessPivots circuits A :=
  Finset.min'_mem _ _

theorem chosenPivot_le_of_mem_witnessPivots
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A) {e : alpha}
    (he : e ∈ witnessPivots circuits A) :
    chosenPivot circuits A hA ≤ e :=
  Finset.min'_le _ _ he

theorem exists_witnessCircuit_pivot_eq_chosen
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A) :
    ∃ C ∈ circuits,
      C.broken ⊆ A ∧ C.pivot = chosenPivot circuits A hA := by
  have hp := chosenPivot_mem_witnessPivots hA
  rcases Finset.mem_image.mp hp with ⟨C, hC, hCpivot⟩
  simp only [witnessCircuits, Finset.mem_filter] at hC
  exact ⟨C, hC.1, hC.2, hCpivot⟩

/-! ## Toggling the least pivot -/

/-- Toggle one edge in a finite edge family. -/
def toggle (A : Finset alpha) (e : alpha) : Finset alpha :=
  if e ∈ A then A.erase e else insert e A

omit [LinearOrder alpha] in
@[simp]
theorem mem_toggle_same (A : Finset alpha) (e : alpha) :
    e ∈ toggle A e ↔ e ∉ A := by
  by_cases he : e ∈ A <;> simp [toggle, he]

omit [LinearOrder alpha] in
theorem mem_toggle_of_ne {A : Finset alpha} {e x : alpha} (hxe : x ≠ e) :
    x ∈ toggle A e ↔ x ∈ A := by
  by_cases he : e ∈ A <;> simp [toggle, he, hxe]

omit [LinearOrder alpha] in
theorem toggle_ne_self (A : Finset alpha) (e : alpha) : toggle A e ≠ A := by
  intro h
  by_cases he : e ∈ A
  · have he' := he
    rw [← h] at he'
    simp [toggle, he] at he'
  · have he' : e ∈ toggle A e := by simp [toggle, he]
    rw [h] at he'
    exact he he'

omit [LinearOrder alpha] in
@[simp]
theorem toggle_toggle (A : Finset alpha) (e : alpha) :
    toggle (toggle A e) e = A := by
  ext x
  by_cases hxe : x = e
  · subst x
    simp
  · simp [mem_toggle_of_ne hxe]

omit [LinearOrder alpha] in
theorem subset_toggle_of_subset_of_not_mem
    {B A : Finset alpha} {e : alpha} (hBA : B ⊆ A) (heB : e ∉ B) :
    B ⊆ toggle A e := by
  intro x hx
  have hxe : x ≠ e := by
    intro h
    subst x
    exact heB hx
  exact (mem_toggle_of_ne hxe).2 (hBA hx)

omit [LinearOrder alpha] in
theorem subset_of_subset_toggle_of_not_mem
    {B A : Finset alpha} {e : alpha} (hBA : B ⊆ toggle A e) (heB : e ∉ B) :
    B ⊆ A := by
  have h := subset_toggle_of_subset_of_not_mem hBA heB
  simpa using h

omit [LinearOrder alpha] in
theorem toggle_subset_of_subset {S A : Finset alpha} {e : alpha}
    (hAS : A ⊆ S) (heS : e ∈ S) :
    toggle A e ⊆ S := by
  intro x hx
  by_cases hxe : x = e
  · simpa [hxe] using heS
  · exact hAS ((mem_toggle_of_ne hxe).1 hx)

/-! ## Stability of the least-pivot selector -/

theorem containsBrokenCircuit_toggle_chosen
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A) :
    ContainsBrokenCircuit circuits
      (toggle A (chosenPivot circuits A hA)) := by
  rcases exists_witnessCircuit_pivot_eq_chosen hA with
    ⟨C, hCcircuits, hCbroken, hCpivot⟩
  refine ⟨C, ?_⟩
  simp only [witnessCircuits, Finset.mem_filter]
  refine ⟨hCcircuits, ?_⟩
  rw [← hCpivot]
  exact subset_toggle_of_subset_of_not_mem hCbroken C.pivot_not_mem_broken

/-- Toggling the least pivot does not change which pivot is least.  Circuits
with smaller pivots cannot be created by the toggle, because all of their
edges are smaller than the toggled edge. -/
theorem chosenPivot_toggle_eq
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A)
    (hToggle : ContainsBrokenCircuit circuits
      (toggle A (chosenPivot circuits A hA))) :
    chosenPivot circuits (toggle A (chosenPivot circuits A hA)) hToggle =
      chosenPivot circuits A hA := by
  let e := chosenPivot circuits A hA
  let e' := chosenPivot circuits (toggle A e) hToggle
  have he_mem : e ∈ witnessPivots circuits (toggle A e) := by
    rcases exists_witnessCircuit_pivot_eq_chosen hA with
      ⟨C, hCcircuits, hCbroken, hCpivot⟩
    refine Finset.mem_image.mpr ⟨C, ?_, hCpivot⟩
    simp only [witnessCircuits, Finset.mem_filter]
    refine ⟨hCcircuits, ?_⟩
    simpa [e, hCpivot] using
      (subset_toggle_of_subset_of_not_mem hCbroken C.pivot_not_mem_broken)
  have he'_le_e : e' ≤ e :=
    chosenPivot_le_of_mem_witnessPivots hToggle he_mem
  have he_le_e' : e ≤ e' := by
    apply le_of_not_gt
    intro he'_lt_e
    have he'_mem := chosenPivot_mem_witnessPivots hToggle
    rcases Finset.mem_image.mp he'_mem with ⟨C, hC, hCpivot⟩
    simp only [witnessCircuits, Finset.mem_filter] at hC
    have he_not_mem_C : e ∉ C.broken := by
      intro heC
      have heCedges : e ∈ C.1 := Finset.mem_of_mem_erase heC
      have hle : e ≤ C.pivot := C.le_pivot_of_mem heCedges
      rw [hCpivot] at hle
      exact (not_le_of_gt he'_lt_e) hle
    have hCbrokenA : C.broken ⊆ A :=
      subset_of_subset_toggle_of_not_mem hC.2 he_not_mem_C
    have he'_old : e' ∈ witnessPivots circuits A := by
      exact Finset.mem_image.mpr ⟨C,
        (Finset.mem_filter.mpr ⟨hC.1, hCbrokenA⟩), hCpivot⟩
    have := chosenPivot_le_of_mem_witnessPivots hA he'_old
    exact (not_le_of_gt he'_lt_e) this
  exact le_antisymm he'_le_e he_le_e'

/-- Toggle the least pivot of a contained broken circuit. -/
def toggleChosen (circuits : Finset (OrderedCircuit alpha)) (A : Finset alpha)
    (hA : ContainsBrokenCircuit circuits A) : Finset alpha :=
  toggle A (chosenPivot circuits A hA)

theorem containsBrokenCircuit_toggleChosen
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A) :
    ContainsBrokenCircuit circuits (toggleChosen circuits A hA) := by
  simpa [toggleChosen] using containsBrokenCircuit_toggle_chosen hA

theorem toggleChosen_ne_self
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A) :
    toggleChosen circuits A hA ≠ A := by
  exact toggle_ne_self A (chosenPivot circuits A hA)

theorem toggleChosen_involutive
    {circuits : Finset (OrderedCircuit alpha)} {A : Finset alpha}
    (hA : ContainsBrokenCircuit circuits A)
    (hToggle : ContainsBrokenCircuit circuits (toggleChosen circuits A hA)) :
    toggleChosen circuits (toggleChosen circuits A hA) hToggle = A := by
  unfold toggleChosen
  rw [chosenPivot_toggle_eq hA hToggle]
  exact toggle_toggle A (chosenPivot circuits A hA)

/-! ## The abstract broken-circuit theorem -/

theorem toggleChosen_subset
    {S : Finset alpha} {circuits : Finset (OrderedCircuit alpha)}
    (hcircuits : ∀ C ∈ circuits, C.1 ⊆ S)
    {A : Finset alpha} (hAS : A ⊆ S)
    (hA : ContainsBrokenCircuit circuits A) :
    toggleChosen circuits A hA ⊆ S := by
  rcases exists_witnessCircuit_pivot_eq_chosen hA with
    ⟨C, hCcircuits, _hCbroken, hCpivot⟩
  have heS : chosenPivot circuits A hA ∈ S := by
    rw [← hCpivot]
    exact hcircuits C hCcircuits C.pivot_mem
  exact toggle_subset_of_subset hAS heS

/-- The selected pair of terms cancels whenever deleting the pivot of a
designated circuit leaves the value unchanged up to sign. -/
theorem value_add_toggleChosen_eq_zero
    {B : Type*} [AddCommGroup B]
    {S : Finset alpha} {circuits : Finset (OrderedCircuit alpha)}
    (hcircuits : ∀ C ∈ circuits, C.1 ⊆ S)
    (f : Finset alpha → B)
    (hcancel : ∀ C ∈ circuits, ∀ A : Finset alpha,
      A ⊆ S → C.1 ⊆ A → f A + f (A.erase C.pivot) = 0)
    {A : Finset alpha} (hAS : A ⊆ S)
    (hA : ContainsBrokenCircuit circuits A) :
    f A + f (toggleChosen circuits A hA) = 0 := by
  rcases exists_witnessCircuit_pivot_eq_chosen hA with
    ⟨C, hCcircuits, hCbroken, hCpivot⟩
  let e := chosenPivot circuits A hA
  have heS : e ∈ S := by
    simpa [e, hCpivot] using
      (hcircuits C hCcircuits C.pivot_mem)
  by_cases heA : e ∈ A
  · have hCsubset : C.1 ⊆ A := by
      rw [← C.insert_pivot_broken]
      have hCpivotA : C.pivot ∈ A := by
        rw [hCpivot]
        exact heA
      exact Finset.insert_subset_iff.mpr ⟨hCpivotA, hCbroken⟩
    have h := hcancel C hCcircuits A hAS hCsubset
    simpa [toggleChosen, toggle, e, heA, hCpivot] using h
  · have hInsertS : insert e A ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨heS, hAS⟩
    have hCsubset : C.1 ⊆ insert e A := by
      rw [← C.insert_pivot_broken]
      refine Finset.insert_subset_iff.mpr ⟨?_, ?_⟩
      · rw [hCpivot]
        exact Finset.mem_insert_self e A
      · exact hCbroken.trans (Finset.subset_insert e A)
    have h := hcancel C hCcircuits (insert e A) hInsertS hCsubset
    simpa [toggleChosen, toggle, e, heA, hCpivot, add_comm] using h

/-- Every term indexed by a family containing a selected broken circuit
cancels under the least-pivot involution. -/
theorem sum_containingBrokenCircuit_eq_zero
    {B : Type*} [AddCommGroup B]
    (S : Finset alpha) (circuits : Finset (OrderedCircuit alpha))
    (hcircuits : ∀ C ∈ circuits, C.1 ⊆ S)
    (f : Finset alpha → B)
    (hcancel : ∀ C ∈ circuits, ∀ A : Finset alpha,
      A ⊆ S → C.1 ⊆ A → f A + f (A.erase C.pivot) = 0) :
    (∑ A ∈ S.powerset with ContainsBrokenCircuit circuits A, f A) = 0 := by
  let bad : Finset (Finset alpha) :=
    S.powerset.filter (ContainsBrokenCircuit circuits)
  let g : ∀ A ∈ bad, Finset alpha := fun A hA =>
    toggleChosen circuits A (by
      exact (Finset.mem_filter.mp hA).2)
  have hgmem : ∀ A (hA : A ∈ bad), g A hA ∈ bad := by
    intro A hA
    have hmem := Finset.mem_filter.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr
        (toggleChosen_subset hcircuits (Finset.mem_powerset.mp hmem.1) hmem.2)
    · exact containsBrokenCircuit_toggleChosen hmem.2
  change (∑ A ∈ bad, f A) = 0
  refine Finset.sum_involution g ?_ ?_ hgmem ?_
  · intro A hA
    have hmem := Finset.mem_filter.mp hA
    exact value_add_toggleChosen_eq_zero hcircuits f hcancel
      (Finset.mem_powerset.mp hmem.1) hmem.2
  · intro A hA _hf
    exact toggleChosen_ne_self (Finset.mem_filter.mp hA).2
  · intro A hA
    have hmem := Finset.mem_filter.mp hA
    have htoggle := (Finset.mem_filter.mp (hgmem A hA)).2
    simpa [g] using toggleChosen_involutive hmem.2 htoggle

/-- Abstract Dohmen--Trinks/Whitney broken-circuit restriction: a powerset sum
may be restricted to families avoiding every designated broken circuit. -/
theorem sum_powerset_eq_sum_avoidingBrokenCircuits
    {B : Type*} [AddCommGroup B]
    (S : Finset alpha) (circuits : Finset (OrderedCircuit alpha))
    (hcircuits : ∀ C ∈ circuits, C.1 ⊆ S)
    (f : Finset alpha → B)
    (hcancel : ∀ C ∈ circuits, ∀ A : Finset alpha,
      A ⊆ S → C.1 ⊆ A → f A + f (A.erase C.pivot) = 0) :
    (∑ A ∈ S.powerset, f A) =
      ∑ A ∈ S.powerset with ¬ ContainsBrokenCircuit circuits A, f A := by
  have hbad := sum_containingBrokenCircuit_eq_zero
    S circuits hcircuits f hcancel
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := S.powerset) (f := f) (p := ContainsBrokenCircuit circuits)]
  rw [hbad, zero_add]

/-! ## Collision gain-graph specialization -/

open RandomSystems.Applications.SoP

/-- The fixed order `hidden < shifted` on the two collision-edge colors. -/
def collisionKindOrderKey : CollisionKind → Fin 2
  | CollisionKind.hidden => 0
  | CollisionKind.shifted => 1

theorem collisionKindOrderKey_injective : Function.Injective collisionKindOrderKey := by
  intro a b h
  cases a <;> cases b <;> simp [collisionKindOrderKey] at h ⊢

instance collisionKindLinearOrder : LinearOrder CollisionKind :=
  LinearOrder.lift' collisionKindOrderKey collisionKindOrderKey_injective

/-- A fixed total order on the finite collision-event type.  The mathematics
of broken-circuit cancellation is independent of which total order is chosen. -/
noncomputable def collisionEventEquivFin (q : Nat) :
    CollisionEvent q ≃ Fin (Fintype.card (CollisionEvent q)) :=
  Fintype.equivFin _

instance collisionEventLinearOrder (q : Nat) : LinearOrder (CollisionEvent q) :=
  LinearOrder.lift' (collisionEventEquivFin q) (collisionEventEquivFin q).injective

/-- A constrained balanced-cycle certificate: after deleting the maximal
edge, the remaining labelled edges contain a path with exactly the deleted
edge's endpoints and gain.  Simple balanced gain cycles are instances, while
this semantic path form is the precise hypothesis needed by cancellation. -/
def IsBalancedCycleCertificate
    {G : Type*} [AddGroup G] {q : Nat} (y : Fin q → G)
    (C : OrderedCircuit (CollisionEvent q)) : Prop :=
  collisionSubfamilyLabelReach (G := G) (q := q) y C.broken
    (collisionEventLeft C.pivot) (collisionEventRight C.pivot)
    (collisionEventLabel y C.pivot)

/-- All balanced-cycle certificates for one realized visible transcript. -/
def balancedCycleCertificates
    {G : Type*} [AddGroup G] [DecidableEq G] {q : Nat} (y : Fin q → G) :
    Finset (OrderedCircuit (CollisionEvent q)) :=
  Finset.univ.filter (IsBalancedCycleCertificate y)

theorem mem_balancedCycleCertificates_iff
    {G : Type*} [AddGroup G] [DecidableEq G] {q : Nat} (y : Fin q → G)
    (C : OrderedCircuit (CollisionEvent q)) :
    C ∈ balancedCycleCertificates y ↔ IsBalancedCycleCertificate y C := by
  simp [balancedCycleCertificates]

/-- The two parallel hidden/shifted edges on one query pair, packaged as an
ordered circuit. -/
def pairParallelCircuit {q : Nat} (p : PairIndex q) :
    OrderedCircuit (CollisionEvent q) :=
  ⟨collisionPairEvents p, ⟨(p, CollisionKind.hidden), by
    simp [collisionPairEvents]⟩⟩

@[simp]
theorem pairParallelCircuit_coe {q : Nat} (p : PairIndex q) :
    (pairParallelCircuit p).1 = collisionPairEvents p := rfl

/-- One labelled edge gives the canonical one-step reach between its
endpoints. -/
theorem collisionSubfamilyLabelReach_singleton
    {G : Type*} [AddGroup G] {q : Nat} (y : Fin q → G)
    (e : CollisionEvent q) :
    collisionSubfamilyLabelReach (G := G) (q := q) y {e}
      (collisionEventLeft e) (collisionEventRight e)
      (collisionEventLabel y e) := by
  simpa using collisionSubfamilyLabelReach.tail
    (collisionSubfamilyLabelReach.refl
      (y := y) (T := ({e} : Finset (CollisionEvent q))) (collisionEventLeft e))
    (show collisionSubfamilyStepLabel (G := G) (q := q) y {e}
        (collisionEventLeft e) (collisionEventRight e)
        (collisionEventLabel y e) from
      ⟨e, by simp, Or.inl ⟨rfl, rfl, rfl⟩⟩)

/-- The smallest balanced gain circuit is exactly a visible answer collision:
the hidden and shifted parallel edges form a balanced two-edge cycle iff their
two visible coordinates are equal. -/
theorem pairParallelCircuit_isBalanced_iff
    {G : Type*} [AddCommGroup G] {q : Nat} (y : Fin q → G)
    (p : PairIndex q) :
    IsBalancedCycleCertificate y (pairParallelCircuit p) ↔
      y p.1.2 = y p.1.1 := by
  let eh : CollisionEvent q := (p, CollisionKind.hidden)
  let es : CollisionEvent q := (p, CollisionKind.shifted)
  have hne : eh ≠ es := by
    intro h
    exact collisionKind_hidden_ne_shifted (congrArg Prod.snd h)
  have hpivot : (pairParallelCircuit p).pivot = eh ∨
      (pairParallelCircuit p).pivot = es := by
    have hmem := (pairParallelCircuit p).pivot_mem
    simpa [pairParallelCircuit, collisionPairEvents, eh, es] using hmem
  rcases hpivot with hpivot | hpivot
  · have hbroken : (pairParallelCircuit p).broken = {es} := by
      unfold OrderedCircuit.broken
      rw [hpivot]
      ext x
      simp only [pairParallelCircuit, collisionPairEvents, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxne, hx | hx⟩
        · exact (hxne hx).elim
        · exact hx
      · intro hx
        exact ⟨fun hxe => hne (hxe.symm.trans hx), Or.inr hx⟩
    constructor
    · intro hbalanced
      have hbalanced' :
          collisionSubfamilyLabelReach (G := G) (q := q) y {es}
            (collisionEventLeft eh) (collisionEventRight eh)
            (collisionEventLabel y eh) := by
        simpa [IsBalancedCycleCertificate, hbroken, hpivot] using hbalanced
      have hstep := collisionSubfamilyLabelReach_singleton y es
      have hcyc := collisionSubfamilyCycleConsistent_singleton
        (G := G) (q := q) y es
      have hlabels := collisionSubfamilyLabelReach_label_unique
        (G := G) (q := q) hcyc hbalanced' (by
          simpa [eh, es, collisionEventLeft, collisionEventRight] using hstep)
      exact (collisionEventLabel_hidden_eq_shifted_iff
        (G := G) (q := q) y p).mp (by simpa [eh, es] using hlabels)
    · intro hy
      have hlabels := (collisionEventLabel_hidden_eq_shifted_iff
        (G := G) (q := q) y p).mpr hy
      have hstep := collisionSubfamilyLabelReach_singleton y es
      simpa [IsBalancedCycleCertificate, hbroken, hpivot, eh, es, hlabels] using hstep
  · have hbroken : (pairParallelCircuit p).broken = {eh} := by
      unfold OrderedCircuit.broken
      rw [hpivot]
      ext x
      simp only [pairParallelCircuit, collisionPairEvents, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxne, hx | hx⟩
        · exact hx
        · exact (hxne hx).elim
      · intro hx
        exact ⟨fun hxe => hne (hx.symm.trans hxe), Or.inl hx⟩
    constructor
    · intro hbalanced
      have hbalanced' :
          collisionSubfamilyLabelReach (G := G) (q := q) y {eh}
            (collisionEventLeft es) (collisionEventRight es)
            (collisionEventLabel y es) := by
        simpa [IsBalancedCycleCertificate, hbroken, hpivot] using hbalanced
      have hstep := collisionSubfamilyLabelReach_singleton y eh
      have hcyc := collisionSubfamilyCycleConsistent_singleton
        (G := G) (q := q) y eh
      have hlabels := collisionSubfamilyLabelReach_label_unique
        (G := G) (q := q) hcyc (by
          simpa [eh, es, collisionEventLeft, collisionEventRight] using hstep)
        hbalanced'
      exact (collisionEventLabel_hidden_eq_shifted_iff
        (G := G) (q := q) y p).mp (by simpa [eh, es] using hlabels)
    · intro hy
      have hlabels := (collisionEventLabel_hidden_eq_shifted_iff
        (G := G) (q := q) y p).mpr hy
      have hstep := collisionSubfamilyLabelReach_singleton y eh
      simpa [IsBalancedCycleCertificate, hbroken, hpivot, eh, es, hlabels] using hstep

/-- A balanced-cycle pivot equation is forced by the remaining circuit
equations inside every larger selected family. -/
theorem balancedCycle_pivot_equation_of_erase
    {G : Type*} [AddCommGroup G] {q : Nat} {y : Fin q → G}
    {C : OrderedCircuit (CollisionEvent q)}
    (hC : IsBalancedCycleCertificate y C)
    {A : Finset (CollisionEvent q)} (hCA : C.1 ⊆ A)
    {base : Fin q → G}
    (hbase : ∀ e ∈ A.erase C.pivot,
      collisionEventEquation (G := G) (q := q) y e base) :
    collisionEventEquation (G := G) (q := q) y C.pivot base := by
  apply collisionSubfamilyLabelReach_equation (G := G) (q := q)
    (y := y) (T := C.broken) (a := base) (hreach := hC)
  intro e he
  apply hbase e
  apply Finset.mem_erase.mpr
  have he' : e ∈ C.1.erase C.pivot := by
    simpa [OrderedCircuit.broken] using he
  exact ⟨(Finset.mem_erase.mp he').1, hCA (Finset.mem_of_mem_erase he')⟩

/-- Adding a redundant balanced-cycle pivot does not change the set of hidden
solutions. -/
theorem equations_family_iff_erase_of_balancedCycle
    {G : Type*} [AddCommGroup G] {q : Nat} {y : Fin q → G}
    {C : OrderedCircuit (CollisionEvent q)}
    (hC : IsBalancedCycleCertificate y C)
    {A : Finset (CollisionEvent q)} (hCA : C.1 ⊆ A)
    (base : Fin q → G) :
    (∀ e ∈ A, collisionEventEquation (G := G) (q := q) y e base) ↔
      ∀ e ∈ A.erase C.pivot,
        collisionEventEquation (G := G) (q := q) y e base := by
  constructor
  · intro hbase e he
    exact hbase e (Finset.mem_of_mem_erase he)
  · intro hbase e heA
    by_cases hepivot : e = C.pivot
    · subst e
      exact balancedCycle_pivot_equation_of_erase hC hCA hbase
    · exact hbase e (Finset.mem_erase.mpr ⟨hepivot, heA⟩)

/-- A balanced-cycle pivot has exactly the same solution count with or without
the pivot edge. -/
theorem collisionSubfamilySolutionCount_eq_erase_of_balancedCycle
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {q : Nat} {y : Fin q → G}
    {C : OrderedCircuit (CollisionEvent q)}
    (hC : IsBalancedCycleCertificate y C)
    {A : Finset (CollisionEvent q)} (hCA : C.1 ⊆ A) :
    collisionSubfamilySolutionCount (G := G) (q := q) y A =
      collisionSubfamilySolutionCount (G := G) (q := q) y (A.erase C.pivot) := by
  rw [collisionSubfamilySolutionCount_eq_card_filter_forall_equations,
    collisionSubfamilySolutionCount_eq_card_filter_forall_equations]
  congr 1
  ext base
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact equations_family_iff_erase_of_balancedCycle hC hCA base

/-- One signed inclusion-exclusion term of the collision gain graph. -/
def gainGraphTermInt
    {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) (A : Finset (CollisionEvent q)) : Int :=
  (-1 : Int) ^ A.card *
    (collisionSubfamilySolutionCount (G := G) (q := q) y A : Int)

theorem gainGraphTerm_add_erase_eq_zero_of_balancedCycle
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {q : Nat} {y : Fin q → G}
    {C : OrderedCircuit (CollisionEvent q)}
    (hC : IsBalancedCycleCertificate y C)
    {A : Finset (CollisionEvent q)} (hCA : C.1 ⊆ A) :
    gainGraphTermInt y A + gainGraphTermInt y (A.erase C.pivot) = 0 := by
  have hpivotA : C.pivot ∈ A := hCA C.pivot_mem
  have hcard : A.card = (A.erase C.pivot).card + 1 := by
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨C.pivot, hpivotA⟩
    rw [Finset.card_erase_of_mem hpivotA]
    omega
  have hcount := collisionSubfamilySolutionCount_eq_erase_of_balancedCycle hC hCA
  unfold gainGraphTermInt
  rw [hcount, hcard, pow_succ]
  ring

/-- Exact broken-circuit-restricted gain-graph formula for the compatible
hidden-state count. -/
theorem compatibleCountNat_eq_brokenCircuitGainGraph
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : Int) =
      ∑ A ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          ¬ ContainsBrokenCircuit (balancedCycleCertificates y) A,
        gainGraphTermInt y A := by
  rw [compatibleCountNat_eq_inclusionExclusion_collisionSubfamilies]
  change (∑ A ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
      gainGraphTermInt y A) = _
  apply sum_powerset_eq_sum_avoidingBrokenCircuits
    (S := (Finset.univ : Finset (CollisionEvent q)))
    (circuits := balancedCycleCertificates y)
  · intro C _hC
    exact Finset.subset_univ C.1
  · intro C hC A _hAuniv hCA
    have h := gainGraphTerm_add_erase_eq_zero_of_balancedCycle
      ((mem_balancedCycleCertificates_iff y C).mp hC) hCA
    convert h using 1
    apply congrArg (fun Z : Finset (CollisionEvent q) =>
      gainGraphTermInt y A + gainGraphTermInt y Z)
    ext e
    simp

/-- The same restricted formula with each surviving family evaluated as zero
or one free group value per support component. -/
theorem compatibleCountNat_eq_brokenCircuitGainGraph_evaluated
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) :
    (compatibleCountNat (G := G) (q := q) y : Int) =
      ∑ A ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          ¬ ContainsBrokenCircuit (balancedCycleCertificates y) A,
        (-1 : Int) ^ A.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y A then
              (Fintype.card G) ^ collisionSubfamilyComponentCount (q := q) A
            else 0) : Int) := by
  rw [compatibleCountNat_eq_brokenCircuitGainGraph]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [gainGraphTermInt,
    collisionSubfamilySolutionCount_eq_ite_cycleConsistent]
  simp

end RandomSystems.SoP.GainGraphCancellation
