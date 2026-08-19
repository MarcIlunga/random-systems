/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.XoPModel

/-!
# XoP Analytic Target

This file contains the pure visible-output analytic expression left by the
model-to-density bridge.  The main remaining theorem is a finite combinatorics
bound on this expression, independent of any fixed input sequence.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Analytic

open Combinatorics

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- The pure visible-output positive-error expression left by the XoP
model-to-density bridge.

For the final target, this expression should be bounded by `C * q^2 / N^2`,
where `N = Fintype.card G`. -/
def pureVisiblePositiveError (q : Nat) : NNReal :=
  ⟨∑ y : Fin q → G,
      max
        (((compatibleCountNNReal y /
            ((((Fintype.card G).descFactorial q *
                (Fintype.card G).descFactorial q : Nat) : NNReal) /
              (((Fintype.card G ^ q : Nat) : NNReal)))) : Real) *
          (Dist.uniform (Fin q → G) y) -
          Dist.uniform (Fin q → G) y) 0,
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)⟩

omit [DecidableEq G] in
/-- With no queries, the pure visible XoP positive-error expression is zero. -/
theorem pureVisiblePositiveError_zero :
    pureVisiblePositiveError (G := G) 0 = 0 := by
  apply NNReal.coe_injective
  simp [pureVisiblePositiveError, compatibleCountNNReal, compatibleCountNat]
  rfl

omit [Fintype G] [DecidableEq G] [Nonempty G] in
/-- For two visible outputs, compatibility is exactly the two pairwise
inequalities at indices `0` and `1`. -/
theorem compatibleHiddenState_fin_two_iff (y a : Fin 2 → G) :
    CompatibleHiddenState y a ↔ a 0 ≠ a 1 ∧ a 0 + y 0 ≠ a 1 + y 1 := by
  unfold CompatibleHiddenState shifted
  constructor
  · intro h
    constructor
    · intro heq
      have hz : (0 : Fin 2) = 1 := h.1 heq
      exact Fin.zero_ne_one hz
    · intro heq
      have hz : (0 : Fin 2) = 1 := h.2 heq
      exact Fin.zero_ne_one hz
  · intro h
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact (h.1 hij).elim
      · exact (h.1 hij.symm).elim
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact (h.2 hij).elim
      · exact (h.2 hij.symm).elim

omit [Fintype G] [DecidableEq G] [Nonempty G] in
/--
Two-query compatible hidden states are equivalent to choosing the first hidden
value and a nonzero difference `d = -a₀ + a₁` that avoids the visible collision
constraint.
-/
def compatibleFinTwoDiffEquiv (y : Fin 2 → G) :
    { a : Fin 2 → G // CompatibleHiddenState y a } ≃
      G × { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 } where
  toFun a :=
    (a.1 0, ⟨-a.1 0 + a.1 1, by
      have hpair := (compatibleHiddenState_fin_two_iff y a.1).mp a.2
      constructor
      · intro hd
        exact hpair.1 (neg_add_eq_zero.mp hd)
      · intro hd
        apply hpair.2
        have hcalc :
            a.1 0 + y 0 = a.1 0 + ((-a.1 0 + a.1 1) + y 1) := by
          rw [hd]
        calc
          a.1 0 + y 0 = a.1 0 + ((-a.1 0 + a.1 1) + y 1) := hcalc
          _ = a.1 1 + y 1 := by simp [add_assoc]⟩)
  invFun p :=
    ⟨![p.1, p.1 + p.2.1], by
      rw [compatibleHiddenState_fin_two_iff]
      constructor
      · intro h01
        have h' : p.1 + p.2.1 = p.1 + 0 := by simpa using h01.symm
        exact p.2.2.1 (add_left_cancel h')
      · intro hshift
        apply p.2.2.2
        have h' : p.1 + y 0 = p.1 + (p.2.1 + y 1) := by
          simpa [add_assoc] using hshift
        have hcancel : y 0 = p.2.1 + y 1 := add_left_cancel h'
        simpa using hcancel.symm⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  right_inv p := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

omit [Nonempty G] in
/-- Cardinal form of `compatibleFinTwoDiffEquiv`, stated for the concrete
`compatibleCountNat` to avoid exporting a special-purpose subtype instance. -/
theorem compatibleCountNat_fin_two_diff (y : Fin 2 → G) :
    compatibleCountNat y =
      Fintype.card G *
        ((Finset.univ : Finset G).filter (fun d => d ≠ 0 ∧ d + y 1 ≠ y 0)).card := by
  classical
  let sA := (Finset.univ : Finset (Fin 2 → G)).filter (fun a => CompatibleHiddenState y a)
  have hmem : ∀ a : Fin 2 → G, a ∈ sA ↔ CompatibleHiddenState y a := by
    intro a
    simp [sA]
  letI : Fintype { a : Fin 2 → G // CompatibleHiddenState y a } :=
    Fintype.ofFinset sA hmem
  have hAcard :
      Fintype.card { a : Fin 2 → G // CompatibleHiddenState y a } =
        compatibleCountNat y := by
    calc
      Fintype.card { a : Fin 2 → G // CompatibleHiddenState y a } = sA.card := by
        exact Fintype.card_ofFinset sA hmem
      _ = compatibleCountNat y := by
        rfl
  calc
    compatibleCountNat y =
        Fintype.card { a : Fin 2 → G // CompatibleHiddenState y a } := hAcard.symm
    _ = Fintype.card (G × { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 }) := by
          exact Fintype.card_congr (compatibleFinTwoDiffEquiv y)
    _ = Fintype.card G * Fintype.card { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 } := by
          rw [Fintype.card_prod]
    _ = Fintype.card G *
        ((Finset.univ : Finset G).filter (fun d => d ≠ 0 ∧ d + y 1 ≠ y 0)).card := by
          rw [← Fintype.card_subtype]

omit [DecidableEq G] [Nonempty G] in
/-- With one query, every hidden tuple is compatible with every visible output. -/
theorem compatibleCountNNReal_one (y : Fin 1 → G) :
    compatibleCountNNReal y = (Fintype.card G : NNReal) := by
  rw [compatibleCountNNReal_eq_coe_nat]
  unfold compatibleCountNat
  simp [compatibleHiddenState_one]

omit [DecidableEq G] in
/-- With one query, XoP is exactly uniform at the pure visible level. -/
theorem pureVisiblePositiveError_one :
    pureVisiblePositiveError (G := G) 1 = 0 := by
  apply NNReal.coe_injective
  simp [pureVisiblePositiveError]
  rfl

/-- A pure visible analytic estimate is enough to obtain the concrete
injective-input restricted XoP `advantageOn` theorem. -/
theorem xop_advantageOn_injective_of_pureVisiblePositiveError
    {q : Nat} (ε : NNReal)
    (hpure : ∀ _hq : q ≤ Fintype.card G,
      pureVisiblePositiveError (G := G) q ≤ ε) :
    advantageOn (Model.xopRealPDS (G := G) (q := q))
        (Model.xopIdealPDS (G := G) (q := q))
        (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine Model.xop_advantageOn_injective_of_pure_visible_positiveError
    (G := G) (q := q) ε ?_
  intro hq
  simpa [pureVisiblePositiveError] using hpure hq

omit [Nonempty G] in
/-- The `q = 2` compatible count factors through the hidden starting point and difference. -/
theorem compatibleCountNat_two_eq_card_diff (y : Fin 2 → G) :
    compatibleCountNat y =
      Fintype.card G * Fintype.card { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 } := by
  classical
  rw [compatibleCountNat_fin_two_diff]
  rw [← Fintype.card_subtype]

omit [Nonempty G] in
/-- If the two visible outputs agree, only the nonzero hidden difference is excluded. -/
theorem compatibleDiffCard_two_eq_of_eq (y : Fin 2 → G) (hy : y 0 = y 1) :
    Fintype.card { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 } = Fintype.card G - 1 := by
  classical
  have hpred : ∀ d : G, (d ≠ 0 ∧ d + y 1 ≠ y 0) ↔ d ≠ 0 := by
    intro d
    constructor
    · intro h
      exact h.1
    · intro hd
      constructor
      · exact hd
      · intro hdy
        apply hd
        have : d + y 1 = 0 + y 1 := by simpa [hy] using hdy
        exact add_right_cancel this
  calc
    Fintype.card { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 }
        = Fintype.card { d : G // d ≠ 0 } :=
          Fintype.card_congr (Equiv.subtypeEquivRight hpred)
    _ = Fintype.card G - Fintype.card { d : G // d = 0 } := by
          rw [Fintype.card_subtype_compl (fun d : G => d = 0)]
    _ = Fintype.card G - 1 := by
          rw [Fintype.card_subtype_eq]

omit [Nonempty G] in
/-- Excluding two distinct elements leaves `N - 2` choices. -/
theorem card_subtype_ne_zero_and_ne (c : G) (hc : c ≠ 0) :
    Fintype.card { d : G // d ≠ 0 ∧ d ≠ c } = Fintype.card G - 2 := by
  classical
  let s := (Finset.univ.erase (0 : G)).erase c
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter (fun d : G => d ≠ 0 ∧ d ≠ c)) = s := by
    ext d
    simp [s, and_comm]
  rw [hfilter]
  calc
    s.card = (Finset.univ.erase (0 : G)).card - 1 := by
      exact Finset.card_erase_of_mem (by simp [hc])
    _ = (Fintype.card G - 1) - 1 := by
      rw [Finset.card_erase_of_mem (by simp)]
      simp
    _ = Fintype.card G - 2 := by omega

omit [Nonempty G] in
/-- If the two visible outputs differ, both zero and the visible difference are excluded. -/
theorem compatibleDiffCard_two_eq_of_ne (y : Fin 2 → G) (hy : y 0 ≠ y 1) :
    Fintype.card { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 } = Fintype.card G - 2 := by
  classical
  have hpred :
      ∀ d : G, (d ≠ 0 ∧ d + y 1 ≠ y 0) ↔ d ≠ 0 ∧ d ≠ y 0 - y 1 := by
    intro d
    constructor
    · intro h
      constructor
      · exact h.1
      · intro hd
        exact h.2 (eq_sub_iff_add_eq.mp hd)
    · intro h
      constructor
      · exact h.1
      · intro hd
        exact h.2 (eq_sub_iff_add_eq.mpr hd)
  calc
    Fintype.card { d : G // d ≠ 0 ∧ d + y 1 ≠ y 0 }
        = Fintype.card { d : G // d ≠ 0 ∧ d ≠ y 0 - y 1 } :=
          Fintype.card_congr (Equiv.subtypeEquivRight hpred)
    _ = Fintype.card G - 2 := by
          exact card_subtype_ne_zero_and_ne (y 0 - y 1) (sub_ne_zero.mpr hy)

omit [Nonempty G] in
/-- Exact `q = 2` compatible hidden-state count for repeated visible outputs. -/
theorem compatibleCountNat_two_eq_of_eq (y : Fin 2 → G) (hy : y 0 = y 1) :
    compatibleCountNat y = Fintype.card G * (Fintype.card G - 1) := by
  rw [compatibleCountNat_two_eq_card_diff, compatibleDiffCard_two_eq_of_eq y hy]

omit [Nonempty G] in
/-- Exact `q = 2` compatible hidden-state count for distinct visible outputs. -/
theorem compatibleCountNat_two_eq_of_ne (y : Fin 2 → G) (hy : y 0 ≠ y 1) :
    compatibleCountNat y = Fintype.card G * (Fintype.card G - 2) := by
  rw [compatibleCountNat_two_eq_card_diff, compatibleDiffCard_two_eq_of_ne y hy]

omit [Nonempty G] in
/-- `NNReal` `q = 2` compatible count for repeated visible outputs. -/
theorem compatibleCountNNReal_two_eq_of_eq (y : Fin 2 → G) (hy : y 0 = y 1) :
    compatibleCountNNReal y =
      ((Fintype.card G * (Fintype.card G - 1) : Nat) : NNReal) := by
  rw [compatibleCountNNReal_eq_coe_nat, compatibleCountNat_two_eq_of_eq y hy]

omit [Nonempty G] in
/-- `NNReal` `q = 2` compatible count for distinct visible outputs. -/
theorem compatibleCountNNReal_two_eq_of_ne (y : Fin 2 → G) (hy : y 0 ≠ y 1) :
    compatibleCountNNReal y =
      ((Fintype.card G * (Fintype.card G - 2) : Nat) : NNReal) := by
  rw [compatibleCountNNReal_eq_coe_nat, compatibleCountNat_two_eq_of_ne y hy]

/-- The contribution of a repeated `q = 2` visible pair to the positive-error sum. -/
theorem pureVisiblePositiveError_two_summand_eq_of_eq
    (hG : 2 ≤ Fintype.card G) (y : Fin 2 → G) (hy : y 0 = y 1) :
    max
      (((compatibleCountNNReal y /
          ((((Fintype.card G).descFactorial 2 *
              (Fintype.card G).descFactorial 2 : Nat) : NNReal) /
            (((Fintype.card G ^ 2 : Nat) : NNReal)))) : Real) *
        (Dist.uniform (Fin 2 → G) y) -
        Dist.uniform (Fin 2 → G) y) 0 =
    (1 : Real) / (((Fintype.card G ^ 2 : Nat) : Real) *
      ((Fintype.card G - 1 : Nat) : Real)) := by
  let A : Real :=
    ((compatibleCountNNReal y /
        ((((Fintype.card G).descFactorial 2 *
            (Fintype.card G).descFactorial 2 : Nat) : NNReal) /
          (((Fintype.card G ^ 2 : Nat) : NNReal)))) : Real) *
      (Dist.uniform (Fin 2 → G) y)
  let B : Real := Dist.uniform (Fin 2 → G) y
  let C : Real :=
    1 / (((Fintype.card G ^ 2 : Nat) : Real) *
      ((Fintype.card G - 1 : Nat) : Real))
  have hdecomp : A = C + B := by
    subst A
    subst B
    subst C
    rw [compatibleCountNNReal_two_eq_of_eq y hy]
    rw [Dist.uniform_apply]
    rw [visibleTupleCount_eq_pow]
    simp only [NNReal.coe_natCast]
    have hN : ((Fintype.card G : Nat) : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hG) : Fintype.card G ≠ 0)
    have hNm1 : (((Fintype.card G - 1 : Nat) : Real)) ≠ 0 := by
      exact_mod_cast (by omega : Fintype.card G - 1 ≠ 0)
    have hNdecomp :
        (Fintype.card G : Real) = 1 + ((Fintype.card G - 1 : Nat) : Real) := by
      exact_mod_cast (by omega : Fintype.card G = 1 + (Fintype.card G - 1))
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.mul_comm, Nat.mul_left_comm]
    field_simp [hN, hNm1]
    nlinarith [hNdecomp]
  change max (A - B) 0 = C
  rw [hdecomp]
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  rw [show C + B - B = C by ring, max_eq_left hC]

/-- Distinct `q = 2` visible pairs have no positive-error contribution. -/
theorem pureVisiblePositiveError_two_summand_eq_of_ne
    (hG : 2 ≤ Fintype.card G) (y : Fin 2 → G) (hy : y 0 ≠ y 1) :
    max
      (((compatibleCountNNReal y /
          ((((Fintype.card G).descFactorial 2 *
              (Fintype.card G).descFactorial 2 : Nat) : NNReal) /
            (((Fintype.card G ^ 2 : Nat) : NNReal)))) : Real) *
        (Dist.uniform (Fin 2 → G) y) -
        Dist.uniform (Fin 2 → G) y) 0 = 0 := by
  rw [max_eq_right]
  rw [compatibleCountNNReal_two_eq_of_ne y hy]
  rw [Dist.uniform_apply]
  rw [visibleTupleCount_eq_pow]
  simp only [NNReal.coe_natCast]
  have hN : ((Fintype.card G : Nat) : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hG) : Fintype.card G ≠ 0)
  have hNm1 : (((Fintype.card G - 1 : Nat) : Real)) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card G - 1 ≠ 0)
  simp [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.mul_comm, Nat.mul_left_comm]
  field_simp [hN, hNm1]
  have hineqNat :
      (Fintype.card G : Nat) * ((Fintype.card G : Nat) - 2) ≤
        ((Fintype.card G : Nat) - 1) ^ 2 := by
    have htmp : ∀ n : Nat, 2 ≤ n → n * (n - 2) ≤ (n - 1) ^ 2 := by
      intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [Nat.add_sub_cancel_left, show 2 + k - 1 = k + 1 by omega]
      nlinarith
    exact htmp (Fintype.card G) hG
  exact_mod_cast hineqNat

/-- Exact pure visible positive-error expression for two XoP queries. -/
theorem pureVisiblePositiveError_two (hG : 2 ≤ Fintype.card G) :
    pureVisiblePositiveError (G := G) 2 =
      1 / ((Fintype.card G : NNReal) * ((Fintype.card G - 1 : Nat) : NNReal)) := by
  apply NNReal.coe_injective
  let c : Real :=
    1 / (((Fintype.card G ^ 2 : Nat) : Real) *
      ((Fintype.card G - 1 : Nat) : Real))
  have hsum :
      (pureVisiblePositiveError (G := G) 2 : Real) =
        ∑ y : Fin 2 → G, if y 0 = y 1 then c else 0 := by
    change (∑ y : Fin 2 → G,
      max
        (((compatibleCountNNReal y /
            ((((Fintype.card G).descFactorial 2 *
                (Fintype.card G).descFactorial 2 : Nat) : NNReal) /
              (((Fintype.card G ^ 2 : Nat) : NNReal)))) : Real) *
          (Dist.uniform (Fin 2 → G) y) -
          Dist.uniform (Fin 2 → G) y) 0) = _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = y 1
    · rw [if_pos hy]
      simpa [c] using
        pureVisiblePositiveError_two_summand_eq_of_eq (G := G) hG y hy
    · rw [if_neg hy]
      exact pureVisiblePositiveError_two_summand_eq_of_ne (G := G) hG y hy
  rw [hsum]
  calc
    (∑ y : Fin 2 → G, if y 0 = y 1 then c else 0)
        = (Fintype.card G : Real) * c := by
          calc
            (∑ y : Fin 2 → G, if y 0 = y 1 then c else 0)
                = ∑ p : G × G, if p.1 = p.2 then c else 0 := by
                  refine Fintype.sum_equiv (finTwoArrowEquiv G) _ _ ?_
                  intro y
                  simp [finTwoArrowEquiv]
            _ = (Fintype.card G : Real) * c := by
                  rw [Fintype.sum_prod_type]
                  simp
    _ = (1 : Real) /
        ((Fintype.card G : Real) * ((Fintype.card G - 1 : Nat) : Real)) := by
          subst c
          have hN : ((Fintype.card G : Nat) : Real) ≠ 0 := by
            exact_mod_cast
              (ne_of_gt (lt_of_lt_of_le (by norm_num) hG) : Fintype.card G ≠ 0)
          have hNm1 : (((Fintype.card G - 1 : Nat) : Real)) ≠ 0 := by
            exact_mod_cast (by omega : Fintype.card G - 1 ≠ 0)
          field_simp [hN, hNm1]
          rw [Nat.cast_pow]
    _ = ((1 / ((Fintype.card G : NNReal) *
          ((Fintype.card G - 1 : Nat) : NNReal)) : NNReal) : Real) := by
          simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul,
            NNReal.coe_natCast]

/-- The exact `q = 2` expression implies the theorem-facing quadratic bound
with constant `1`. -/
theorem pureVisiblePositiveError_two_le_quadratic (hG : 2 ≤ Fintype.card G) :
    pureVisiblePositiveError (G := G) 2 ≤
      (2 : NNReal) ^ 2 / ((Fintype.card G : NNReal) ^ 2) := by
  rw [pureVisiblePositiveError_two (G := G) hG]
  have hNpos : 0 < (Fintype.card G : NNReal) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hG)
  have hNm1pos : 0 < ((Fintype.card G - 1 : Nat) : NNReal) := by
    exact_mod_cast (by omega : 0 < Fintype.card G - 1)
  field_simp [ne_of_gt hNpos, ne_of_gt hNm1pos]
  rw [pow_two]
  norm_num
  have hineqNat : Fintype.card G ≤ (Fintype.card G - 1) * 4 := by
    omega
  exact_mod_cast hineqNat

/-- Concrete theorem-facing restricted XoP security bound for two injective
queries, obtained by routing the exact visible analytic estimate through the
model bridge. -/
theorem xop_advantageOn_injective_two_le_quadratic :
    advantageOn (Model.xopRealPDS (G := G) (q := 2))
        (Model.xopIdealPDS (G := G) (q := 2))
        (InjectiveInputs (X := G) (q := 2)) ≤
      (2 : NNReal) ^ 2 / ((Fintype.card G : NNReal) ^ 2) := by
  refine xop_advantageOn_injective_of_pureVisiblePositiveError
    (G := G) (q := 2)
    ((2 : NNReal) ^ 2 / ((Fintype.card G : NNReal) ^ 2)) ?_
  intro hq
  exact pureVisiblePositiveError_two_le_quadratic (G := G) hq

end Analytic
end XoP
end Applications
end RandomSystems
