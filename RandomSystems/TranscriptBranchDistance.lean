/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem

/-!
# Statistical distance of first-answer transcript branches

Lanzenberger--Maurer Lemma 2 (printed page 10) makes statistical distance
additive across disjoint support cells, without requiring probability
normalization.  Its use in the attainment proof (printed page 17, and thesis
Theorem 2.31 on printed page 22) partitions transcript laws by their first
answer.  This module packages that pure distribution-level step for an
explicit finite set of realized `Option` answers; the ambient query and answer
types remain arbitrary.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

open Classical in
/-- Statistical distance is additive across finitely many transcript branches
whose distinct first answers make their pushed-forward supports disjoint.

`Tf` must be non-negative branchwise.  This is Lemma 2's own hypothesis, not an
artifact: `δ μ ν = ∑ₐ max(μ a − ν a, 0)` counts a cell where `ν` is negative and
`μ` vanishes, so additivity across cells fails outright for signed `ν`.  Weight
is still unconstrained — the thesis's distributions are non-negative of
arbitrary weight (Def 2.1), and it is *normalization*, not sign, that this
module does without. -/
theorem delta_sum_cons_pushforwards_eq_sum_of_deltas_of_finite_answers
    {X : Type u} {Y : Type v} (x : X) (ys : Finset (Option Y))
    (Sf Tf : Option Y → Dist (List (X × Option Y)))
    (hTf : ∀ y ∈ ys, (Tf y).NonNeg) :
    δ (∑ y ∈ ys, Dist.fTransform (fun t => (x, y) :: t) (Sf y))
        (∑ y ∈ ys, Dist.fTransform (fun t => (x, y) :: t) (Tf y)) =
      ∑ y ∈ ys, δ (Sf y) (Tf y) := by
  have hdisj : (↑ys : Set (Option Y)).PairwiseDisjoint fun y =>
      (Dist.fTransform (fun t => (x, y) :: t) (Sf y)).support ∪
        (Dist.fTransform (fun t => (x, y) :: t) (Tf y)).support := by
    intro y _ y' _ hne
    refine Finset.disjoint_left.mpr fun t ht ht' => ?_
    have hleft : ∃ s, t = (x, y) :: s := by
      rcases Finset.mem_union.mp ht with hs | hs
      · obtain ⟨s, _, hs⟩ := Dist.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
      · obtain ⟨s, _, hs⟩ := Dist.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
    have hright : ∃ s, t = (x, y') :: s := by
      rcases Finset.mem_union.mp ht' with hs | hs
      · obtain ⟨s, _, hs⟩ := Dist.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
      · obtain ⟨s, _, hs⟩ := Dist.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
    obtain ⟨s, hs⟩ := hleft
    obtain ⟨s', hs'⟩ := hright
    exact hne (congrArg Prod.snd (List.cons.inj (hs.symm.trans hs')).1)
  refine Eq.trans
    (δ_sum_of_disjoint_support _ _ (fun y hy => (hTf y hy).fTransform _) hdisj) ?_
  exact Finset.sum_congr rfl fun y hy =>
    δ_fTransform_eq_of_injective
      (fun _ _ h => (List.cons.inj h).2) (Sf y) (hTf y hy)

end RandomSystems.CR18
