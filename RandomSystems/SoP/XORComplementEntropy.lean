/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementSquareRoot
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Elementary aggregation of the XOR complement profile bound

`XORComplementSquareRoot` bounds one row profile by an exact multinomial
envelope.  This file sums those envelopes.  The proof is finite and
elementary: split every separated histogram into two blocks of comparable
mass, lower-bound its multinomial orbit, count support layers, and sum the
resulting exponential series.
-/

noncomputable section
open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORBounds

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- If all summands are smaller than `L` but their total reaches `L`, some
subcollection first crosses `L` before reaching `2L`. -/
lemma exists_subset_sum_ge_lt_two_mul
    {A : Type*} (K : Finset A) (f : A → Nat) (L : Nat)
    (hLpos : 0 < L) (htotal : L ≤ ∑ x ∈ K, f x)
    (hsmall : ∀ x ∈ K, f x < L) :
    ∃ J : Finset A, J ⊆ K ∧
      L ≤ ∑ x ∈ J, f x ∧ ∑ x ∈ J, f x < 2 * L := by
  induction K using Finset.induction_on with
  | empty => simp at htotal; omega
  | @insert a K ha ih =>
      by_cases hrest : L ≤ ∑ x ∈ K, f x
      · obtain ⟨J, hJK, hJlow, hJhigh⟩ := ih hrest (fun x hx =>
          hsmall x (Finset.mem_insert_of_mem hx))
        exact ⟨J, hJK.trans (Finset.subset_insert a K), hJlow, hJhigh⟩
      · refine ⟨insert a K, Finset.Subset.rfl, ?_, ?_⟩
        · simpa [Finset.sum_insert ha] using htotal
        · have haSmall := hsmall a (Finset.mem_insert_self a K)
          have hrest' : ∑ x ∈ K, f x < L := Nat.lt_of_not_ge hrest
          simp only [Finset.sum_insert ha]
          omega

/-- A histogram with no cell above three quarters has a subset of support
carrying between one and three quarters of its total mass. -/
lemma exists_multiset_quarter_mass_split
    {A : Type*} [DecidableEq A] (s : Multiset A) (m : Nat)
    (hm : 0 < m) (hcard : s.card = 4 * m)
    (hsep : ∀ x : A, s.count x ≤ 3 * m) :
    ∃ J : Finset A, J ⊆ s.toFinset ∧
      m ≤ ∑ x ∈ J, s.count x ∧
      ∑ x ∈ J, s.count x ≤ 3 * m ∧
      J.Nonempty ∧ (s.toFinset \ J).Nonempty := by
  let K := s.toFinset
  by_cases hlarge : ∃ x ∈ K, m ≤ s.count x
  · obtain ⟨x, hxK, hxm⟩ := hlarge
    refine ⟨{x}, Finset.singleton_subset_iff.mpr hxK, ?_, ?_,
      Finset.singleton_nonempty x, ?_⟩
    · simpa using hxm
    · simpa using hsep x
    · rw [Finset.sdiff_nonempty]
      intro hKx
      have hK : K = {x} :=
        Finset.Subset.antisymm hKx (Finset.singleton_subset_iff.mpr hxK)
      have htotal : ∑ y ∈ K, s.count y = 4 * m := by
        dsimp [K]
        rw [Multiset.toFinset_sum_count_eq, hcard]
      rw [hK] at htotal
      have hxupper := hsep x
      simp only [Finset.sum_singleton] at htotal
      omega
  · have hsmall : ∀ x ∈ K, s.count x < m := by
      intro x hx
      exact Nat.lt_of_not_ge (fun hxm => hlarge ⟨x, hx, hxm⟩)
    have htotal : m ≤ ∑ x ∈ K, s.count x := by
      dsimp [K]
      rw [Multiset.toFinset_sum_count_eq, hcard]
      omega
    obtain ⟨J, hJK, hJlow, hJhigh⟩ :=
      exists_subset_sum_ge_lt_two_mul K (fun x => s.count x) m
        hm htotal hsmall
    refine ⟨J, hJK, hJlow, by omega, ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      intro hJ
      subst J
      simp at hJlow
      omega
    · rw [Finset.sdiff_nonempty]
      intro hKJ
      have hK : K = J := Finset.Subset.antisymm hKJ hJK
      have htotal' : ∑ x ∈ K, s.count x = 4 * m := by
        dsimp [K]
        rw [Multiset.toFinset_sum_count_eq, hcard]
      rw [hK] at htotal'
      omega

/-- Splitting a positive histogram into `r` nonempty cells leaves at least an
`r!` factor in its multinomial coefficient. -/
lemma card_factorial_mul_prod_factorial_le_sum_factorial
    {A : Type*} (T : Finset A) (f : A → Nat)
    (hpos : ∀ x ∈ T, 0 < f x) :
    T.card.factorial * ∏ x ∈ T, (f x).factorial ≤
      (∑ x ∈ T, f x).factorial := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      let r := T.card
      let R := ∑ x ∈ T, f x
      have hposT : ∀ x ∈ T, 0 < f x := fun x hx =>
        hpos x (Finset.mem_insert_of_mem hx)
      have hi : r.factorial * ∏ x ∈ T, (f x).factorial ≤ R.factorial :=
        ih hposT
      have hrR : r ≤ R := by
        calc
          r = ∑ _x ∈ T, 1 := by simp [r]
          _ ≤ ∑ x ∈ T, f x := Finset.sum_le_sum fun x hx => hposT x hx
          _ = R := rfl
      have hfa : 0 < f a := hpos a (Finset.mem_insert_self a T)
      have hchoose : r + 1 ≤ (R + f a).choose (f a) := by
        calc
          r + 1 ≤ R + 1 := Nat.add_le_add_right hrR 1
          _ = (R + 1).choose R := (Nat.choose_succ_self_right R).symm
          _ ≤ (R + f a).choose R :=
            Nat.choose_le_choose R (by omega)
          _ = (R + f a).choose (f a) := Nat.choose_symm_add
      calc
        (insert a T).card.factorial *
            ∏ x ∈ insert a T, (f x).factorial =
          (r + 1) * (r.factorial * ∏ x ∈ T, (f x).factorial) *
            (f a).factorial := by
              simp [Finset.card_insert_of_notMem ha, Finset.prod_insert ha,
                Nat.factorial_succ, r]
              ac_rfl
        _ ≤ (r + 1) * R.factorial * (f a).factorial := by gcongr
        _ ≤ (R + f a).choose (f a) * R.factorial * (f a).factorial := by
          gcongr
        _ = (R + f a).factorial :=
          Nat.add_choose_mul_factorial_mul_factorial R (f a)
        _ = (∑ x ∈ insert a T, f x).factorial := by
          simp [Finset.sum_insert ha, R, add_comm]

lemma countPerms_mul_prod_support_factorial
    {A : Type*} [DecidableEq A] (s : Multiset A) :
    s.countPerms * ∏ x ∈ s.toFinset, (s.count x).factorial =
      s.card.factorial := by
  have hspec := Nat.multinomial_spec
    (s := (Finset.univ : Finset s.toFinset))
    (fun x : s.toFinset => s.count (x : A))
  rw [← countPerms_eq_support_multinomial] at hspec
  have hsum : (∑ x : s.toFinset, s.count (x : A)) = s.card := by
    simpa only using (Finset.sum_attach s.toFinset (fun x => s.count x)).trans
      s.toFinset_sum_count_eq
  have hprod : (∏ x : s.toFinset, (s.count (x : A)).factorial) =
      ∏ x ∈ s.toFinset, (s.count x).factorial := by
    simpa using Finset.prod_attach s.toFinset
      (fun x => (s.count x).factorial)
  rw [hsum, hprod] at hspec
  simpa [mul_comm] using hspec

/-- A two-block split lower-bounds the full multinomial orbit by the binomial
choice of block positions and the permutations internal to each support
block. -/
lemma multiset_countPerms_ge_choose_mul_support_factorials
    {A : Type*} [DecidableEq A] (s : Multiset A) (J : Finset A)
    (hJK : J ⊆ s.toFinset) :
    s.card.choose (∑ x ∈ J, s.count x) * J.card.factorial *
        (s.toFinset \ J).card.factorial ≤ s.countPerms := by
  let K := s.toFinset
  let C := K \ J
  let b := ∑ x ∈ J, s.count x
  let c := ∑ x ∈ C, s.count x
  let PJ := ∏ x ∈ J, (s.count x).factorial
  let PC := ∏ x ∈ C, (s.count x).factorial
  let P := ∏ x ∈ K, (s.count x).factorial
  have hposK : ∀ x ∈ K, 0 < s.count x := by
    intro x hx
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hx)
  have hposJ : ∀ x ∈ J, 0 < s.count x := fun x hx =>
    hposK x (hJK hx)
  have hposC : ∀ x ∈ C, 0 < s.count x := by
    intro x hx
    exact hposK x (Finset.sdiff_subset hx)
  have hsum : c + b = s.card := by
    have h := Finset.sum_sdiff hJK (f := fun x => s.count x)
    rw [Multiset.toFinset_sum_count_eq] at h
    exact h
  have hJ : J.card.factorial * PJ ≤ b.factorial :=
    card_factorial_mul_prod_factorial_le_sum_factorial J
      (fun x => s.count x) hposJ
  have hC : C.card.factorial * PC ≤ c.factorial :=
    card_factorial_mul_prod_factorial_le_sum_factorial C
      (fun x => s.count x) hposC
  have hprod : PC * PJ = P := by
    exact Finset.prod_sdiff hJK
  have hblocks :
      (J.card.factorial * C.card.factorial) * P ≤
        b.factorial * c.factorial := by
    calc
      (J.card.factorial * C.card.factorial) * P =
          (J.card.factorial * PJ) * (C.card.factorial * PC) := by
            rw [← hprod]
            ac_rfl
      _ ≤ b.factorial * c.factorial := Nat.mul_le_mul hJ hC
  have hb : b ≤ s.card := by omega
  have hmul := Nat.mul_le_mul_left (s.card.choose b) hblocks
  have hmul' :
      (s.card.choose b * J.card.factorial * C.card.factorial) * P ≤
        s.countPerms * P := by
    calc
      (s.card.choose b * J.card.factorial * C.card.factorial) * P =
          s.card.choose b * ((J.card.factorial * C.card.factorial) * P) := by
            ac_rfl
      _ ≤ s.card.choose b * (b.factorial * c.factorial) := hmul
      _ = s.card.factorial := by
        rw [show c = s.card - b by omega]
        simpa [mul_assoc] using Nat.choose_mul_factorial_mul_factorial hb
      _ = s.countPerms * P := by
        exact (countPerms_mul_prod_support_factorial s).symm
  have hP : 0 < P := by
    dsimp [P]
    positivity
  exact Nat.le_of_mul_le_mul_right hmul' hP

lemma choose_mono_right_of_le_half {N a b : Nat}
    (hab : a ≤ b) (hb : b ≤ N / 2) :
    N.choose a ≤ N.choose b := by
  exact Nat.decreasingInduction
    (fun k hk ih =>
      (Nat.choose_le_succ_of_lt_half_left (by omega)).trans ih)
    (le_refl _) hab

/-- On the interval from one quarter to three quarters, the binomial
coefficient is no smaller than the quarter coefficient. -/
lemma choose_quarter_le_of_mem_Icc (m b : Nat)
    (hlow : m ≤ b) (hhigh : b ≤ 3 * m) :
    (4 * m).choose m ≤ (4 * m).choose b := by
  by_cases hb : b ≤ 2 * m
  · exact choose_mono_right_of_le_half hlow (by omega)
  · have hbN : b ≤ 4 * m := by omega
    have hcompLow : m ≤ 4 * m - b := by omega
    have hcompHigh : 4 * m - b ≤ 2 * m := by omega
    calc
      (4 * m).choose m ≤ (4 * m).choose (4 * m - b) :=
        choose_mono_right_of_le_half hcompLow (by omega)
      _ = (4 * m).choose b := Nat.choose_symm hbN

/-- A quarter slice already supplies an exponential binomial factor. -/
lemma three_pow_le_choose_four_mul_quarter (m : Nat) :
    3 ^ m ≤ (4 * m).choose m := by
  have hfac : (0 : Real) < (m.factorial : Real) := by positivity
  have hpre :
      (3 : Real) ^ m ≤ (((3 * m + 1 : Nat) : Real) ^ m) / m.factorial := by
    rw [le_div_iff₀ hfac]
    calc
      (3 : Real) ^ m * (m.factorial : Real) ≤
          (3 : Real) ^ m * (m : Real) ^ m := by
            gcongr
            exact_mod_cast Nat.factorial_le_pow m
      _ = ((3 * m : Nat) : Real) ^ m := by
        push_cast
        rw [mul_pow]
      _ ≤ (((3 * m + 1 : Nat) : Real) ^ m) := by
        gcongr
        norm_num
  have hchoose := Nat.pow_le_choose (α := Real) m (4 * m)
  have hshape : 4 * m + 1 - m = 3 * m + 1 := by omega
  rw [hshape] at hchoose
  exact_mod_cast hpre.trans hchoose

lemma three_pow_le_choose_of_quarter_mass (m b : Nat)
    (hlow : m ≤ b) (hhigh : b ≤ 3 * m) :
    3 ^ m ≤ (4 * m).choose b :=
  (three_pow_le_choose_four_mul_quarter m).trans
    (choose_quarter_le_of_mem_Icc m b hlow hhigh)

/-- Among two support blocks of fixed total cardinality, the product of
factorials is minimized at the middle split. -/
lemma factorial_half_sq_le_mul_factorials (s t k : Nat)
    (hst : s + t = k) :
    (k / 2).factorial ^ 2 ≤ s.factorial * t.factorial := by
  let j := k / 2
  have hs : s ≤ k := by omega
  have hj : j ≤ k := by
    dsimp [j]
    omega
  have hjcomp : j ≤ k - j := by
    dsimp [j]
    omega
  have hchoose : k.choose s ≤ k.choose j := Nat.choose_le_middle s k
  have hAs : k.choose s * s.factorial * t.factorial = k.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hs
    rw [show k - s = t by omega] at h
    exact h
  have hAj : k.choose j * j.factorial * (k - j).factorial = k.factorial :=
    Nat.choose_mul_factorial_mul_factorial hj
  have hApos : 0 < k.choose s := Nat.choose_pos hs
  have hbalanced : j.factorial * (k - j).factorial ≤
      s.factorial * t.factorial := by
    apply Nat.le_of_mul_le_mul_left (c := k.choose s) _ hApos
    calc
      k.choose s * (j.factorial * (k - j).factorial) ≤
          k.choose j * (j.factorial * (k - j).factorial) := by
            gcongr
      _ = k.factorial := by simpa [mul_assoc] using hAj
      _ = k.choose s * (s.factorial * t.factorial) := by
        simpa [mul_assoc] using hAs.symm
  calc
    j.factorial ^ 2 ≤ j.factorial * (k - j).factorial := by
      rw [pow_two]
      gcongr
    _ ≤ s.factorial * t.factorial := hbalanced

/-- Exact quarter size for a power-of-two carrier. -/
def xorQuarterSize (n : Nat) : Nat := 2 ^ (n - 2)

lemma four_mul_xorQuarterSize {n : Nat} (hn : 2 ≤ n) :
    4 * xorQuarterSize n = 2 ^ n := by
  have hn' : n - 2 + 2 = n := by omega
  rw [← hn', pow_add]
  simp [xorQuarterSize]
  ring

lemma xorQuarterSize_pos (n : Nat) : 0 < xorQuarterSize n := by
  unfold xorQuarterSize
  positivity

/-- The multinomial orbit of every separated XOR profile contains both an
exponential quarter factor and the balanced support-factorial factor. -/
theorem separated_profile_countPerms_lower {n : Nat} (hn : 2 ≤ n)
    (s : Sym (XorSpace n) (2 ^ n))
    (hsep : IsThreeQuarterSeparatedProfile s) :
    3 ^ xorQuarterSize n *
        ((s.1.toFinset.card / 2).factorial ^ 2) ≤ s.1.countPerms := by
  let m := xorQuarterSize n
  let K := s.1.toFinset
  have hNm : 2 ^ n = 4 * m := (four_mul_xorQuarterSize hn).symm
  have hcard : s.1.card = 4 * m := by simpa [hNm] using s.2
  have hcount : ∀ x : XorSpace n, s.1.count x ≤ 3 * m := by
    intro x
    have hx := hsep x
    omega
  obtain ⟨J, hJK, hJlow, hJhigh, _hJne, _hCne⟩ :=
    exists_multiset_quarter_mass_split s.1 m
      (xorQuarterSize_pos n) hcard hcount
  let b := ∑ x ∈ J, s.1.count x
  let C := K \ J
  have hchoose : 3 ^ m ≤ s.1.card.choose b := by
    rw [hcard]
    exact three_pow_le_choose_of_quarter_mass m b hJlow hJhigh
  have hcards : J.card + C.card = K.card := by
    have hJK' : J ⊆ K := by simpa [K] using hJK
    have h := Finset.card_sdiff_add_card K J
    rw [Finset.union_eq_left.mpr hJK'] at h
    dsimp [C]
    omega
  have hfactor : (K.card / 2).factorial ^ 2 ≤
      J.card.factorial * C.card.factorial :=
    factorial_half_sq_le_mul_factorials J.card C.card K.card hcards
  have horbit :=
    multiset_countPerms_ge_choose_mul_support_factorials s.1 J hJK
  change 3 ^ m * ((K.card / 2).factorial ^ 2) ≤ s.1.countPerms
  calc
    3 ^ m * ((K.card / 2).factorial ^ 2) ≤
        s.1.card.choose b * (J.card.factorial * C.card.factorial) :=
      Nat.mul_le_mul hchoose hfactor
    _ = s.1.card.choose b * J.card.factorial * C.card.factorial := by
      rw [mul_assoc]
    _ ≤ s.1.countPerms := horbit

def xorEighthSize (n : Nat) : Nat := 2 ^ (n - 3)

lemma two_mul_xorEighthSize_eq_quarter {n : Nat} (hn : 3 ≤ n) :
    2 * xorEighthSize n = xorQuarterSize n := by
  have hn' : n - 3 + 1 = n - 2 := by omega
  unfold xorEighthSize xorQuarterSize
  rw [← hn', pow_add]
  simp
  ring

/-- Real square-root form of the separated multinomial lower bound. -/
theorem separated_profile_sqrt_countPerms_lower {n : Nat} (hn : 3 ≤ n)
    (s : Sym (XorSpace n) (2 ^ n))
    (hsep : IsThreeQuarterSeparatedProfile s) :
    (3 : Real) ^ xorEighthSize n *
        ((s.1.toFinset.card / 2).factorial : Real) ≤
      Real.sqrt (s.1.countPerms : Real) := by
  apply Real.le_sqrt_of_sq_le
  have h := separated_profile_countPerms_lower (by omega) s hsep
  rw [mul_pow, ← pow_mul]
  rw [show xorEighthSize n * 2 = xorQuarterSize n by
    rw [mul_comm, two_mul_xorEighthSize_eq_quarter hn]]
  exact_mod_cast h

theorem separated_profileCubicEnvelope_le {n : Nat} (hn : 3 ≤ n)
    (s : Sym (XorSpace n) (2 ^ n))
    (hsep : IsThreeQuarterSeparatedProfile s) :
    profileCubicEnvelope s ≤
      ((profileChooseBound s : Real) *
          Real.sqrt (profileChooseBound s : Real)) /
        ((3 : Real) ^ xorEighthSize n *
          ((s.1.toFinset.card / 2).factorial : Real)) := by
  have hsqrt := separated_profile_sqrt_countPerms_lower hn s hsep
  have hden : 0 < (3 : Real) ^ xorEighthSize n *
      ((s.1.toFinset.card / 2).factorial : Real) := by positivity
  unfold profileCubicEnvelope
  rw [Real.sqrt_div (by positivity)]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hden hsqrt

/-! ## Counting profiles by support size -/

/-- Lift every occurrence of a multiset to its actual support. -/
def multisetSupportLift {A : Type*} [DecidableEq A] (m : Multiset A) :
    Multiset m.toFinset :=
  m.pmap (fun x hx => ⟨x, Multiset.mem_toFinset.mpr hx⟩)
    (fun _x hx => hx)

@[simp]
lemma card_multisetSupportLift {A : Type*} [DecidableEq A]
    (m : Multiset A) :
    (multisetSupportLift m).card = m.card := by
  simp [multisetSupportLift]

@[simp]
lemma map_coe_multisetSupportLift {A : Type*} [DecidableEq A]
    (m : Multiset A) :
    (multisetSupportLift m).map (fun x : m.toFinset => (x : A)) = m := by
  unfold multisetSupportLift
  rw [Multiset.map_pmap]
  rw [Multiset.pmap_eq_map]
  simp

def profileSupportLift {A : Type*} [DecidableEq A] {N : Nat}
    (s : Sym A N) : Sym s.1.toFinset N :=
  ⟨multisetSupportLift s.1, by simp [s.2]⟩

/-- A profile of support size `k` is encoded by its support and a weak
histogram on that support. -/
def profileSupportLayerCode {A : Type*} [Fintype A] [DecidableEq A]
    (N k : Nat) :
    {s : Sym A N // s.1.toFinset.card = k} →
      Σ K : {K : Finset A // K.card = k}, Sym K.1 N := fun s =>
  ⟨⟨s.1.1.toFinset, s.2⟩, profileSupportLift s.1⟩

lemma profileSupportLayerCode_injective
    {A : Type*} [Fintype A] [DecidableEq A] (N k : Nat) :
    Function.Injective (profileSupportLayerCode (A := A) N k) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  have hmapped := congrArg
    (fun z : Σ K : {K : Finset A // K.card = k}, Sym K.1 N =>
      z.2.1.map (fun x : z.1.1 => (x : A))) h
  simpa [profileSupportLayerCode, profileSupportLift] using hmapped

lemma card_profile_support_layer_le
    {A : Type*} [Fintype A] [DecidableEq A] (N k : Nat) :
    Fintype.card {s : Sym A N // s.1.toFinset.card = k} ≤
      (Fintype.card A).choose k * (k + N - 1).choose N := by
  calc
    Fintype.card {s : Sym A N // s.1.toFinset.card = k} ≤
        Fintype.card (Σ K : {K : Finset A // K.card = k}, Sym K.1 N) :=
      Fintype.card_le_of_injective
        (profileSupportLayerCode (A := A) N k)
        (profileSupportLayerCode_injective (A := A) N k)
    _ = ∑ K : {K : Finset A // K.card = k},
          Fintype.card (Sym K.1 N) := Fintype.card_sigma
    _ = ∑ _K : {K : Finset A // K.card = k},
          (k + N - 1).choose N := by
      apply Finset.sum_congr rfl
      intro K _hK
      rw [Sym.card_sym_eq_choose]
      simp [K.2]
    _ = (Fintype.card A).choose k * (k + N - 1).choose N := by
      simp [Fintype.card_finset_len]

def profileLayerChooseBound (N k : Nat) : Nat :=
  (N + k - 1).choose (k - 1)

lemma weak_profile_count_eq_profileLayerChooseBound
    {N k : Nat} (hN : 0 < N) (hk : 0 < k) :
    (k + N - 1).choose N = profileLayerChooseBound N k := by
  have htop : k + N - 1 = N + (k - 1) := by omega
  unfold profileLayerChooseBound
  rw [htop, Nat.choose_symm_add]
  congr 2 <;> omega

lemma profileChooseBound_eq_layer {n k : Nat}
    (s : Sym (XorSpace n) (2 ^ n))
    (hk : s.1.toFinset.card = k) :
    profileChooseBound s = profileLayerChooseBound (2 ^ n) k := by
  unfold profileChooseBound profileLayerChooseBound
  rw [hk]

lemma card_xor_profile_support_layer_le (n k : Nat) (hk : 0 < k) :
    Fintype.card
        {s : Sym (XorSpace n) (2 ^ n) // s.1.toFinset.card = k} ≤
      (2 ^ n).choose k * profileLayerChooseBound (2 ^ n) k := by
  have h := card_profile_support_layer_le
    (A := XorSpace n) (2 ^ n) k
  rw [card_xorSpace] at h
  rw [weak_profile_count_eq_profileLayerChooseBound (by positivity) hk] at h
  exact h

def separatedProfileEnvelopeLayer (n k : Nat) : Real :=
  ∑ s : Sym (XorSpace n) (2 ^ n),
    if IsThreeQuarterSeparatedProfile s ∧ s.1.toFinset.card = k then
      profileCubicEnvelope s else 0

def profileEnvelopeLayerUpper (n k : Nat) : Real :=
  (((2 ^ n).choose k : Nat) : Real) *
      (profileLayerChooseBound (2 ^ n) k : Real) ^ 2 *
      Real.sqrt (profileLayerChooseBound (2 ^ n) k : Real) /
    ((3 : Real) ^ xorEighthSize n * ((k / 2).factorial : Real))

theorem separatedProfileEnvelopeLayer_le {n k : Nat}
    (hn : 3 ≤ n) (hk : 0 < k) :
    separatedProfileEnvelopeLayer n k ≤ profileEnvelopeLayerUpper n k := by
  let B : Real := profileLayerChooseBound (2 ^ n) k
  let D : Real := (3 : Real) ^ xorEighthSize n * ((k / 2).factorial : Real)
  let T : Finset (Sym (XorSpace n) (2 ^ n)) :=
    Finset.univ.filter (fun s =>
      IsThreeQuarterSeparatedProfile s ∧ s.1.toFinset.card = k)
  have hpoint : ∀ s ∈ T,
      profileCubicEnvelope s ≤ B * Real.sqrt B / D := by
    intro s hs
    have hcond := (Finset.mem_filter.mp hs).2
    have h := separated_profileCubicEnvelope_le hn s hcond.1
    rw [profileChooseBound_eq_layer s hcond.2] at h
    rw [hcond.2] at h
    simpa [B, D] using h
  have hcardNat : T.card ≤
      (2 ^ n).choose k * profileLayerChooseBound (2 ^ n) k := by
    have hsubset : T ⊆ (Finset.univ : Finset
        (Sym (XorSpace n) (2 ^ n))).filter
          (fun s => s.1.toFinset.card = k) := by
      intro s hs
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact hs.2
    have hlayer : ((Finset.univ : Finset
        (Sym (XorSpace n) (2 ^ n))).filter
          (fun s => s.1.toFinset.card = k)).card =
        Fintype.card
          {s : Sym (XorSpace n) (2 ^ n) // s.1.toFinset.card = k} := by
      exact (Fintype.card_subtype
        (fun s : Sym (XorSpace n) (2 ^ n) =>
          s.1.toFinset.card = k)).symm
    have hfilter : T.card ≤ Fintype.card
        {s : Sym (XorSpace n) (2 ^ n) // s.1.toFinset.card = k} := by
      rw [← hlayer]
      exact Finset.card_le_card hsubset
    exact hfilter.trans (card_xor_profile_support_layer_le n k hk)
  have hcard : (T.card : Real) ≤
      ((2 ^ n).choose k : Nat) * profileLayerChooseBound (2 ^ n) k := by
    exact_mod_cast hcardNat
  have hboundNonneg : 0 ≤ B * Real.sqrt B / D := by
    dsimp [B, D]
    positivity
  unfold separatedProfileEnvelopeLayer
  rw [← Finset.sum_filter]
  change (∑ s ∈ T, profileCubicEnvelope s) ≤ _
  calc
    (∑ s ∈ T, profileCubicEnvelope s) ≤
        ∑ _s ∈ T, B * Real.sqrt B / D :=
      Finset.sum_le_sum fun s hs => hpoint s hs
    _ = (T.card : Real) * (B * Real.sqrt B / D) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((2 ^ n).choose k : Nat) : Real) * B *
          (B * Real.sqrt B / D) := by
      have := mul_le_mul_of_nonneg_right hcard hboundNonneg
      simpa [mul_assoc] using this
    _ = profileEnvelopeLayerUpper n k := by
      unfold profileEnvelopeLayerUpper
      dsimp [B, D]
      ring

/-! ## Exact support-layer reindexing -/

lemma xor_profile_support_card_le (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) :
    s.1.toFinset.card ≤ 2 ^ n := by
  exact (Multiset.toFinset_card_le s.1).trans_eq s.2

lemma two_le_xor_profile_support_card_of_separated (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n))
    (hsep : IsThreeQuarterSeparatedProfile s) :
    2 ≤ s.1.toFinset.card := by
  have hnonempty : s.1.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    intro hs
    have hzero : s.1.card = 0 := by
      simpa only [Multiset.card_zero] using congrArg Multiset.card hs
    have hcard : 0 = 2 ^ n := hzero.symm.trans s.2
    have hN : 0 < 2 ^ n := by positivity
    omega
  by_contra hnot
  have hcardOne : s.1.toFinset.card = 1 := by
    have hpos := Finset.card_pos.mpr hnonempty
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardOne
  have hcount : s.1.count x = 2 ^ n := by
    have hsum := Multiset.toFinset_sum_count_eq s.1
    rw [hx, Finset.sum_singleton, s.2] at hsum
    exact hsum
  have hxsep := hsep x
  rw [hcount] at hxsep
  have hN : 0 < 2 ^ n := by positivity
  omega

theorem highEntropyProfileCubicEnvelope_eq_sum_layers (n : Nat) :
    highEntropyProfileCubicEnvelope n =
      ∑ k ∈ Finset.Icc 2 (2 ^ n), separatedProfileEnvelopeLayer n k := by
  unfold highEntropyProfileCubicEnvelope separatedProfileEnvelopeLayer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hsep : IsThreeQuarterSeparatedProfile s
  · have hk : s.1.toFinset.card ∈ Finset.Icc 2 (2 ^ n) := by
      simp only [Finset.mem_Icc]
      exact ⟨two_le_xor_profile_support_card_of_separated n s hsep,
        xor_profile_support_card_le n s⟩
    rw [if_pos hsep]
    symm
    rw [Finset.sum_eq_single s.1.toFinset.card]
    · simp [hsep]
    · intro k _hk hne
      rw [if_neg]
      intro hcond
      exact hne hcond.2.symm
    · exact fun hnot => (hnot hk).elim
  · simp [hsep]

/-! ## Elementary factorial and binomial estimates for one layer -/

lemma factorial_sq_le_factorial_two_mul_sub_one {j : Nat} (hj : 1 ≤ j) :
    j.factorial ^ 2 ≤ (2 * j - 1).factorial := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      have hquad : (j + 1) ^ 2 ≤ (2 * j) * (2 * j + 1) := by
        nlinarith
      calc
        (j + 1).factorial ^ 2 =
            (j + 1) ^ 2 * j.factorial ^ 2 := by
          rw [Nat.factorial_succ]
          ring
        _ ≤ (j + 1) ^ 2 * (2 * j - 1).factorial := by gcongr
        _ ≤ ((2 * j) * (2 * j + 1)) * (2 * j - 1).factorial := by
          gcongr
        _ = (2 * (j + 1) - 1).factorial := by
          have hfac : (2 * j).factorial =
              (2 * j) * (2 * j - 1).factorial := by
            conv_lhs =>
              rw [show 2 * j = (2 * j - 1) + 1 by omega,
                Nat.factorial_succ]
            congr 1 <;> omega
          rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
            Nat.factorial_succ, hfac]
          ring

lemma factorial_half_sq_le_pred_factorial {k : Nat} (hk : 2 ≤ k) :
    (k / 2).factorial ^ 2 ≤ (k - 1).factorial := by
  have hj : 1 ≤ k / 2 := by omega
  exact (factorial_sq_le_factorial_two_mul_sub_one hj).trans
    (Nat.factorial_le (by omega))

lemma factorial_half_sq_le_factorial {k : Nat} (hk : 2 ≤ k) :
    (k / 2).factorial ^ 2 ≤ k.factorial :=
  (factorial_half_sq_le_pred_factorial hk).trans
    (Nat.factorial_le (by omega))

lemma profileLayerChooseBound_le_pow_div {N k : Nat} (hN : 0 < N)
    (hk : 0 < k) (hkle : k ≤ N) :
    (profileLayerChooseBound N k : Real) ≤
      ((2 * N : Nat) : Real) ^ (k - 1) / ((k - 1).factorial : Real) := by
  have hchoose : (profileLayerChooseBound N k : Real) ≤
      ((N + k - 1 : Nat) : Real) ^ (k - 1) /
        ((k - 1).factorial : Real) := by
    unfold profileLayerChooseBound
    exact Nat.choose_le_pow_div (α := Real) (k - 1) (N + k - 1)
  have hbase : N + k - 1 ≤ 2 * N := by omega
  calc
    (profileLayerChooseBound N k : Real) ≤
        ((N + k - 1 : Nat) : Real) ^ (k - 1) /
          ((k - 1).factorial : Real) := hchoose
    _ ≤ ((2 * N : Nat) : Real) ^ (k - 1) /
          ((k - 1).factorial : Real) := by
      gcongr

/-- After squaring, the layer envelope is dominated by one term of an
eighth-power exponential series. -/
theorem profileEnvelopeLayerUpper_sq_le_series_term {n k : Nat}
    (hk : 2 ≤ k) (hkle : k ≤ 2 ^ n) :
    profileEnvelopeLayerUpper n k ^ 2 ≤
      ((((2 * (2 ^ n) : Nat) : Real) ^ (7 * (k / 2) + 1)) /
        ((3 : Real) ^ xorEighthSize n *
          (((k / 2).factorial : Real) ^ 8))) ^ 2 := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let A : Real := (((2 ^ n).choose k : Nat) : Real)
  let B : Real := (profileLayerChooseBound (2 ^ n) k : Real)
  let F : Real := ((k / 2).factorial : Real)
  let C : Real := (3 : Real) ^ xorEighthSize n
  let AU : Real := N ^ k / (k.factorial : Real)
  let BU : Real := (2 * N) ^ (k - 1) / ((k - 1).factorial : Real)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hA : A ≤ AU := by
    dsimp [A, AU, N]
    exact Nat.choose_le_pow_div (α := Real) k (2 ^ n)
  have hB : B ≤ BU := by
    dsimp [B, BU, N]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      profileLayerChooseBound_le_pow_div (N := 2 ^ n) (k := k)
        (by positivity) (by omega) hkle
  have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hAUnonneg : 0 ≤ AU := by dsimp [AU]; positivity
  have hBUnonneg : 0 ≤ BU := by dsimp [BU]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hFpos : 0 < F := by dsimp [F]; positivity
  have hexact : profileEnvelopeLayerUpper n k ^ 2 =
      A ^ 2 * B ^ 5 / (C ^ 2 * F ^ 2) := by
    change (A * B ^ 2 * Real.sqrt B / (C * F)) ^ 2 = _
    calc
      (A * B ^ 2 * Real.sqrt B / (C * F)) ^ 2 =
          A ^ 2 * B ^ 4 * (Real.sqrt B) ^ 2 / (C ^ 2 * F ^ 2) := by
        ring
      _ = A ^ 2 * B ^ 5 / (C ^ 2 * F ^ 2) := by
        rw [Real.sq_sqrt hBnonneg]
        ring
  have hAB : A ^ 2 * B ^ 5 ≤ AU ^ 2 * BU ^ 5 := by
    gcongr
  have hfirst : profileEnvelopeLayerUpper n k ^ 2 ≤
      AU ^ 2 * BU ^ 5 / (C ^ 2 * F ^ 2) := by
    rw [hexact]
    exact div_le_div_of_nonneg_right hAB (by positivity)
  let Rnum : Real := N ^ (2 * k) * (2 * N) ^ (5 * (k - 1))
  let Rden : Real :=
    (k.factorial : Real) ^ 2 * ((k - 1).factorial : Real) ^ 5 *
      C ^ 2 * F ^ 2
  have hrewrite : AU ^ 2 * BU ^ 5 / (C ^ 2 * F ^ 2) =
      Rnum / Rden := by
    dsimp [AU, BU, Rnum, Rden]
    field_simp
    ring
  have hnum : Rnum ≤ (2 * N) ^ (14 * (k / 2) + 2) := by
    have hNle : N ≤ 2 * N := by linarith
    have hbase : 1 ≤ 2 * N := by
      have : (1 : Real) ≤ N := by
        dsimp [N]
        exact_mod_cast (show 1 ≤ 2 ^ n by
          have hp : 0 < 2 ^ n := by positivity
          omega)
      linarith
    have hexp : 2 * k + 5 * (k - 1) ≤ 14 * (k / 2) + 2 := by
      omega
    dsimp [Rnum]
    calc
      N ^ (2 * k) * (2 * N) ^ (5 * (k - 1)) ≤
          (2 * N) ^ (2 * k) * (2 * N) ^ (5 * (k - 1)) := by
        gcongr
      _ = (2 * N) ^ (2 * k + 5 * (k - 1)) := by
        rw [← pow_add]
      _ ≤ (2 * N) ^ (14 * (k / 2) + 2) :=
        pow_le_pow_right₀ hbase hexp
  have hkfac : F ^ 2 ≤ (k.factorial : Real) := by
    dsimp [F]
    exact_mod_cast factorial_half_sq_le_factorial hk
  have hpredfac : F ^ 2 ≤ ((k - 1).factorial : Real) := by
    dsimp [F]
    exact_mod_cast factorial_half_sq_le_pred_factorial hk
  have hfactor : F ^ 16 ≤
      (k.factorial : Real) ^ 2 * ((k - 1).factorial : Real) ^ 5 *
        F ^ 2 := by
    calc
      F ^ 16 = (F ^ 2) ^ 2 * (F ^ 2) ^ 5 * F ^ 2 := by ring
      _ ≤ (k.factorial : Real) ^ 2 *
          ((k - 1).factorial : Real) ^ 5 * F ^ 2 := by
        gcongr
  have hden : C ^ 2 * F ^ 16 ≤ Rden := by
    dsimp [Rden]
    calc
      C ^ 2 * F ^ 16 ≤ C ^ 2 *
          ((k.factorial : Real) ^ 2 *
            ((k - 1).factorial : Real) ^ 5 * F ^ 2) := by
        gcongr
      _ = (k.factorial : Real) ^ 2 *
          ((k - 1).factorial : Real) ^ 5 * C ^ 2 * F ^ 2 := by ring
  have hratio : Rnum / Rden ≤
      (2 * N) ^ (14 * (k / 2) + 2) / (C ^ 2 * F ^ 16) := by
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  calc
    profileEnvelopeLayerUpper n k ^ 2 ≤
        AU ^ 2 * BU ^ 5 / (C ^ 2 * F ^ 2) := hfirst
    _ = Rnum / Rden := hrewrite
    _ ≤ (2 * N) ^ (14 * (k / 2) + 2) / (C ^ 2 * F ^ 16) := hratio
    _ = ((((2 * (2 ^ n) : Nat) : Real) ^ (7 * (k / 2) + 1)) /
        ((3 : Real) ^ xorEighthSize n *
          (((k / 2).factorial : Real) ^ 8))) ^ 2 := by
      dsimp [N, C, F]
      push_cast
      ring

theorem profileEnvelopeLayerUpper_le_series_term {n k : Nat}
    (hk : 2 ≤ k) (hkle : k ≤ 2 ^ n) :
    profileEnvelopeLayerUpper n k ≤
      (((2 * (2 ^ n) : Nat) : Real) ^ (7 * (k / 2) + 1)) /
        ((3 : Real) ^ xorEighthSize n *
          (((k / 2).factorial : Real) ^ 8)) := by
  apply (sq_le_sq₀ (by unfold profileEnvelopeLayerUpper; positivity)
    (by positivity)).mp
  exact profileEnvelopeLayerUpper_sq_le_series_term hk hkle

def xorSixteenthSize (n : Nat) : Nat := 2 ^ (n - 4)

lemma sixteen_mul_xorSixteenthSize {n : Nat} (hn : 4 ≤ n) :
    16 * xorSixteenthSize n = 2 ^ n := by
  have hn' : n - 4 + 4 = n := by omega
  rw [← hn', pow_add]
  simp [xorSixteenthSize]
  ring

lemma two_mul_xorSixteenthSize_eq_eighth {n : Nat} (hn : 4 ≤ n) :
    2 * xorSixteenthSize n = xorEighthSize n := by
  have hn' : n - 4 + 1 = n - 3 := by omega
  unfold xorSixteenthSize xorEighthSize
  rw [← hn', pow_add]
  simp
  ring

/-- The threshold `n = 63` is exactly where the elementary scaling
`(2N)^7 ≤ (N/128)^8` starts to hold for `N = 2^n`. -/
lemma two_mul_pow_seven_le_div_128_pow_eight {n : Nat} (hn : 63 ≤ n) :
    (2 * (((2 ^ n : Nat) : Real))) ^ 7 ≤
      ((((2 ^ n : Nat) : Real)) / 128) ^ 8 := by
  let N : Real := ((2 ^ n : Nat) : Real)
  have hlargeNat : 2 ^ 63 ≤ 2 ^ n :=
    pow_le_pow_right' (by omega : 1 ≤ 2) hn
  have hlarge : ((2 ^ 63 : Nat) : Real) ≤ N := by
    dsimp [N]
    exact_mod_cast hlargeNat
  have hNnonneg : 0 ≤ N := by dsimp [N]; positivity
  change (2 * N) ^ 7 ≤ (N / 128) ^ 8
  rw [div_pow]
  apply (le_div_iff₀ (by positivity : (0 : Real) < 128 ^ 8)).2
  calc
    (2 * N) ^ 7 * 128 ^ 8 = ((2 ^ 63 : Nat) : Real) * N ^ 7 := by
      norm_num [mul_pow]
      ring
    _ ≤ N * N ^ 7 := by gcongr
    _ = N ^ 8 := by ring

/-- The eighth-power exponential series absorbs the support-layer term. -/
lemma profile_series_ratio_le_three_pow_sixteenth {n k : Nat}
    (hn : 63 ≤ n) :
    (((2 * (2 ^ n) : Nat) : Real) ^ 7) ^ (k / 2) /
        (((k / 2).factorial : Real) ^ 8) ≤
      (3 : Real) ^ xorSixteenthSize n := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let j : Nat := k / 2
  let x : Real := N / 128
  let F : Real := (j.factorial : Real)
  have hx : 0 ≤ x := by dsimp [x, N]; positivity
  have hscale : (2 * N) ^ 7 ≤ x ^ 8 := by
    dsimp [x, N]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      two_mul_pow_seven_le_div_128_pow_eight hn
  have hpow : ((2 * N) ^ 7) ^ j ≤ (x ^ 8) ^ j := by
    exact pow_le_pow_left₀ (by positivity) hscale j
  have hseries : x ^ j / F ≤ Real.exp x := by
    dsimp [F]
    exact Real.pow_div_factorial_le_exp x hx j
  have hseriesNonneg : 0 ≤ x ^ j / F := by positivity
  have hexpBound : (Real.exp x) ^ 8 ≤
      (3 : Real) ^ xorSixteenthSize n := by
    have hNrNat := sixteen_mul_xorSixteenthSize (by omega : 4 ≤ n)
    have hNr : N = 16 * (xorSixteenthSize n : Real) := by
      dsimp [N]
      exact_mod_cast hNrNat.symm
    calc
      (Real.exp x) ^ 8 = Real.exp ((8 : Real) * x) := by
        simpa using (Real.exp_nat_mul x 8).symm
      _ = Real.exp (xorSixteenthSize n : Real) := by
        congr 1
        dsimp [x]
        rw [hNr]
        ring
      _ = Real.exp 1 ^ xorSixteenthSize n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (3 : Real) ^ xorSixteenthSize n := by
        exact pow_le_pow_left₀ (by positivity)
          (le_of_lt Real.exp_one_lt_three) _
  have hfinal : (((2 * N) ^ 7) ^ j) / F ^ 8 ≤
      (3 : Real) ^ xorSixteenthSize n := by
    calc
      ((2 * N) ^ 7) ^ j / F ^ 8 ≤ (x ^ 8) ^ j / F ^ 8 := by
        exact div_le_div_of_nonneg_right hpow (by positivity)
      _ = (x ^ j) ^ 8 / F ^ 8 := by
        congr 1
        rw [← pow_mul, ← pow_mul, mul_comm 8 j]
      _ = (x ^ j / F) ^ 8 := (div_pow (x ^ j) F 8).symm
      _ ≤ (Real.exp x) ^ 8 := by
        exact pow_le_pow_left₀ hseriesNonneg hseries 8
      _ ≤ (3 : Real) ^ xorSixteenthSize n := hexpBound
  simpa only [N, j, F, Nat.cast_mul, Nat.cast_ofNat] using hfinal

theorem profileEnvelopeLayerUpper_le_geometric {n k : Nat}
    (hn : 63 ≤ n) (hk : 2 ≤ k) (hkle : k ≤ 2 ^ n) :
    profileEnvelopeLayerUpper n k ≤
      (2 * (((2 ^ n : Nat) : Real))) /
        ((3 : Real) ^ xorSixteenthSize n) := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let j : Nat := k / 2
  let F : Real := (j.factorial : Real)
  let C : Real := (3 : Real) ^ xorEighthSize n
  let R : Real := (3 : Real) ^ xorSixteenthSize n
  have hterm := profileEnvelopeLayerUpper_le_series_term hk hkle
  have hratio : (((2 * N) ^ 7) ^ j) / F ^ 8 ≤ R := by
    dsimp [N, j, F, R]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      profile_series_ratio_le_three_pow_sixteenth (n := n) (k := k) hn
  have hshape :
      ((2 * N) ^ (7 * j + 1)) / (C * F ^ 8) =
        (2 * N / C) * ((((2 * N) ^ 7) ^ j) / F ^ 8) := by
    rw [show 7 * j + 1 = 1 + 7 * j by omega, pow_add,
      pow_mul]
    ring
  have hCshape : C = R ^ 2 := by
    dsimp [C, R]
    rw [show xorEighthSize n = xorSixteenthSize n * 2 by
      have h := two_mul_xorSixteenthSize_eq_eighth (by omega : 4 ≤ n)
      omega]
    exact pow_mul 3 (xorSixteenthSize n) 2
  calc
    profileEnvelopeLayerUpper n k ≤
        ((2 * N) ^ (7 * j + 1)) / (C * F ^ 8) := by
      simpa only [N, j, F, C, Nat.cast_mul, Nat.cast_ofNat] using hterm
    _ = (2 * N / C) * ((((2 * N) ^ 7) ^ j) / F ^ 8) := hshape
    _ ≤ (2 * N / C) * R := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2 * N / R := by
      rw [hCshape]
      field_simp
    _ = 2 * (((2 ^ n : Nat) : Real)) /
        ((3 : Real) ^ xorSixteenthSize n) := by rfl

/-- Summing the exact support layers costs fewer than `N` copies of the
uniform geometric majorant. -/
theorem highEntropyProfileCubicEnvelope_le_explicit {n : Nat}
    (hn : 63 ≤ n) :
    highEntropyProfileCubicEnvelope n ≤
      2 * (((2 ^ n : Nat) : Real)) ^ 2 /
        ((3 : Real) ^ xorSixteenthSize n) := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let R : Real := (3 : Real) ^ xorSixteenthSize n
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hconst : 0 ≤ 2 * N / R := by positivity
  rw [highEntropyProfileCubicEnvelope_eq_sum_layers]
  calc
    (∑ k ∈ Finset.Icc 2 (2 ^ n), separatedProfileEnvelopeLayer n k) ≤
        ∑ _k ∈ Finset.Icc 2 (2 ^ n), 2 * N / R := by
      apply Finset.sum_le_sum
      intro k hk
      have hki := Finset.mem_Icc.mp hk
      exact (separatedProfileEnvelopeLayer_le (by omega) (by omega)).trans
        (by
          simpa only [N, R] using
            profileEnvelopeLayerUpper_le_geometric hn hki.1 hki.2)
    _ = ((Finset.Icc 2 (2 ^ n)).card : Real) * (2 * N / R) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * (2 * N / R) := by
      apply mul_le_mul_of_nonneg_right _ hconst
      have hcardNat : (Finset.Icc 2 (2 ^ n)).card ≤ 2 ^ n := by
        rw [Nat.card_Icc]
        have hNnat : 1 ≤ 2 ^ n := by
          have hp : 0 < 2 ^ n := by positivity
          omega
        omega
      dsimp [N]
      exact_mod_cast hcardNat
    _ = 2 * (((2 ^ n : Nat) : Real)) ^ 2 /
        ((3 : Real) ^ xorSixteenthSize n) := by
      dsimp [N, R]
      ring

lemma one_add_three_mul_le_two_pow_sub_four {n : Nat} (hn : 10 ≤ n) :
    1 + 3 * n ≤ 2 ^ (n - 4) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hthree : 3 ≤ 2 ^ (n - 4) := by
        calc
          3 ≤ 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (n - 4) :=
            pow_le_pow_right' (by omega : 1 ≤ 2) (by omega)
      rw [show n + 1 - 4 = (n - 4) + 1 by omega, pow_succ]
      omega

lemma two_mul_cube_pow_two_le_three_pow_sixteenth {n : Nat}
    (hn : 63 ≤ n) :
    2 * (2 ^ n) ^ 3 ≤ 3 ^ xorSixteenthSize n := by
  have hexp : 1 + 3 * n ≤ xorSixteenthSize n := by
    exact one_add_three_mul_le_two_pow_sub_four (by omega)
  calc
    2 * (2 ^ n) ^ 3 = 2 ^ (1 + 3 * n) := by
      rw [pow_add, show 3 * n = n * 3 by omega, pow_mul]
      norm_num
    _ ≤ 2 ^ xorSixteenthSize n :=
      pow_le_pow_right' (by omega : 1 ≤ 2) hexp
    _ ≤ 3 ^ xorSixteenthSize n :=
      Nat.pow_le_pow_left (by omega) _

lemma explicit_profile_envelope_le_inv {n : Nat} (hn : 63 ≤ n) :
    2 * (((2 ^ n : Nat) : Real)) ^ 2 /
        ((3 : Real) ^ xorSixteenthSize n) ≤
      1 / (((2 ^ n : Nat) : Real)) := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let R : Real := (3 : Real) ^ xorSixteenthSize n
  have hN : 0 < N := by dsimp [N]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hpowNat := two_mul_cube_pow_two_le_three_pow_sixteenth hn
  have hpow : 2 * N ^ 3 ≤ R := by
    dsimp [N, R]
    exact_mod_cast hpowNat
  change 2 * N ^ 2 / R ≤ 1 / N
  apply (div_le_iff₀ hR).2
  rw [show (1 : Real) / N * R = R / N by ring]
  apply (le_div_iff₀ hN).2
  nlinarith

/-- Closed aggregate endpoint: the separated full cubic mass is at most
`1/N`, with every finite constant explicit. -/
theorem highEntropyProfileCubicEnvelope_le_inv {n : Nat} (hn : 63 ≤ n) :
    highEntropyProfileCubicEnvelope n ≤
      1 / (((2 ^ n : Nat) : Real)) :=
  (highEntropyProfileCubicEnvelope_le_explicit hn).trans
    (explicit_profile_envelope_le_inv hn)

theorem highEntropyFullCubicMass_le_inv {n : Nat} (hn : 63 ≤ n) :
    highEntropyFullCubicMass n ≤
      1 / (((2 ^ n : Nat) : Real)) :=
  (highEntropyFullCubicMass_le_profileCubicEnvelope n).trans
    (highEntropyProfileCubicEnvelope_le_inv hn)

theorem separatedAnchoredCubicMass_le_inv_sq {n : Nat} (hn : 63 ≤ n) :
    separatedAnchoredCubicMass n ≤
      1 / (((2 ^ n : Nat) : Real)) ^ 2 := by
  let N : Real := ((2 ^ n : Nat) : Real)
  have hN : 0 < N := by dsimp [N]; positivity
  calc
    separatedAnchoredCubicMass n ≤ highEntropyFullCubicMass n / N :=
      separatedAnchoredCubicMass_le_highEntropy_div n
    _ ≤ (1 / N) / N := by
      exact div_le_div_of_nonneg_right
        (by simpa only [N] using highEntropyFullCubicMass_le_inv hn)
        (le_of_lt hN)
    _ = 1 / N ^ 2 := by ring
    _ = 1 / (((2 ^ n : Nat) : Real)) ^ 2 := by rfl

/-- The previously conditional full-deck residual theorem is now
unconditional for `n ≥ 63`. -/
theorem fullResidualAdvantage_le_closed {n : Nat} (hn : 63 ≤ n) :
    fullResidualAdvantage n ≤
      (1 / 2 : Real) * Real.sqrt
        (quotientSparseEnergyBound n +
          1 / (((2 ^ n : Nat) : Real)) ^ 2) := by
  exact fullResidualAdvantage_le_of_separated_cubic (by omega)
    (separatedAnchoredCubicMass_le_inv_sq hn)

/-- A compact numerical form of the closed quotient energy.  The exact
expression above is retained; this rounds only at the final public endpoint. -/
theorem quotientSparseEnergyBound_add_inv_sq_le {n : Nat} (hn : 63 ≤ n) :
    quotientSparseEnergyBound n +
        1 / (((2 ^ n : Nat) : Real)) ^ 2 ≤
      196 / (((2 ^ n : Nat) : Real)) ^ 2 := by
  let N : Nat := 2 ^ n
  let NR : Real := (N : Real)
  have hNlarge : 128 ≤ N := by
    have h := hundred_mul_le_two_pow (by omega : 10 ≤ n)
    dsimp [N]
    omega
  have hNRlarge : (128 : Real) ≤ NR := by
    dsimp [NR]
    exact_mod_cast hNlarge
  have hNRpos : 0 < NR := by linarith
  have hsub1 : NR / 2 ≤ ((N - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    linarith
  have hsub2 : NR / 2 ≤ ((N - 2 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    linarith
  have hchoose : ((N.choose 3 : Nat) : Real) ≤ NR ^ 3 / 6 := by
    have h := Nat.choose_le_pow_div (α := Real) 3 N
    norm_num at h ⊢
    exact h
  have hden : (NR / 2) ^ 6 ≤
      (((N - 1 : Nat) : Real) ^ 3) *
        (((N - 2 : Nat) : Real) ^ 3) := by
    calc
      (NR / 2) ^ 6 = (NR / 2) ^ 3 * (NR / 2) ^ 3 := by ring
      _ ≤ (((N - 1 : Nat) : Real) ^ 3) *
          (((N - 2 : Nat) : Real) ^ 3) := by gcongr
  have hfirst :
      16 * ((N.choose 3 : Nat) : Real) /
          ((((N - 1 : Nat) : Real) ^ 3) *
            (((N - 2 : Nat) : Real) ^ 3)) ≤
        (4 / 3 : Real) / NR ^ 2 := by
    calc
      16 * ((N.choose 3 : Nat) : Real) /
          ((((N - 1 : Nat) : Real) ^ 3) *
            (((N - 2 : Nat) : Real) ^ 3)) ≤
          (16 * (NR ^ 3 / 6)) / ((NR / 2) ^ 6) := by
        exact div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
      _ = (512 / 3 : Real) / NR ^ 3 := by
        field_simp
        ring
      _ ≤ (4 / 3 : Real) / NR ^ 2 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have : (512 : Real) ≤ 4 * NR := by linarith
        nlinarith
  unfold quotientSparseEnergyBound
  change
    16 * ((N.choose 3 : Nat) : Real) /
          ((((N - 1 : Nat) : Real) ^ 3) *
            (((N - 2 : Nat) : Real) ^ 3)) +
        (580 / 3 : Real) / NR ^ 2 + 1 / NR ^ 2 ≤
      196 / NR ^ 2
  calc
    16 * ((N.choose 3 : Nat) : Real) /
          ((((N - 1 : Nat) : Real) ^ 3) *
            (((N - 2 : Nat) : Real) ^ 3)) +
        (580 / 3 : Real) / NR ^ 2 + 1 / NR ^ 2 ≤
      (4 / 3 : Real) / NR ^ 2 +
        (580 / 3 : Real) / NR ^ 2 + 1 / NR ^ 2 := by linarith
    _ ≤ 196 / NR ^ 2 := by
      have hsq : 0 < NR ^ 2 := by positivity
      rw [show (4 / 3 : Real) / NR ^ 2 +
          (580 / 3 : Real) / NR ^ 2 + 1 / NR ^ 2 =
        (587 / 3 : Real) / NR ^ 2 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hsq.le

theorem fullResidualAdvantage_le_seven_div {n : Nat} (hn : 63 ≤ n) :
    fullResidualAdvantage n ≤
      7 / (((2 ^ n : Nat) : Real)) := by
  let N : Real := ((2 ^ n : Nat) : Real)
  have hN : 0 < N := by dsimp [N]; positivity
  calc
    fullResidualAdvantage n ≤
        (1 / 2 : Real) * Real.sqrt
          (quotientSparseEnergyBound n + 1 / N ^ 2) := by
      simpa only [N] using fullResidualAdvantage_le_closed hn
    _ ≤ (1 / 2 : Real) * Real.sqrt (196 / N ^ 2) := by
      gcongr
      simpa only [N] using quotientSparseEnergyBound_add_inv_sq_le hn
    _ = 7 / N := by
      rw [show (196 : Real) / N ^ 2 = (14 / N) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = 7 / (((2 ^ n : Nat) : Real)) := by rfl

end RandomSystems.SoP.XORComplement
