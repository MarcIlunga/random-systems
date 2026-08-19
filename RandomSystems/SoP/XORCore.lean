/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORInjection

/-!
# Closed checkerboard cores for XOR SoP

This file starts the quantitative part of the broken-cycle proof.  It keeps
the exact level-three boundary separate from the general high-level tail.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.SoP.XORCore

open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Replace a sum over embeddings by a sum over all functions with the
injectivity indicator left explicit. -/
theorem sum_embedding_eq_sum_if_injective
    {G : Type*} [Fintype G] [DecidableEq G] {k : Nat}
    (F : (Fin k -> G) -> Real) :
    (∑ e : Fin k ↪ G, F e) =
      ∑ x : Fin k -> G, if Function.Injective x then F x else 0 := by
  calc
    (∑ e : Fin k ↪ G, F e) =
        ∑ x : {x : Fin k -> G // Function.Injective x}, F x.1 := by
      exact Fintype.sum_equiv
        (Equiv.subtypeInjectiveEquivEmbedding (Fin k) G).symm
        (fun e : Fin k ↪ G => F e)
        (fun x : {x : Fin k -> G // Function.Injective x} => F x.1)
        (fun _e => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset (Fin k -> G)).filter
          Function.Injective, F x := by
      symm
      rw [Finset.sum_subtype]
      intro x
      simp
    _ = ∑ x : Fin k -> G,
        if Function.Injective x then F x else 0 := by
      rw [Finset.sum_filter]

/-- Functions on three coordinates as ordinary triples. -/
def finThreeArrowEquiv (G : Type*) : (Fin 3 -> G) ≃ G × G × G where
  toFun x := (x 0, x 1, x 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv t := by
    rcases t with ⟨u, v, w⟩
    rfl

theorem injective_fin_three_iff {G : Type*} (x : Fin 3 -> G) :
    Function.Injective x ↔
      x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2 := by
  constructor
  · intro hx
    exact ⟨fun h => Fin.zero_ne_one (hx h),
      fun h => by
        have : (0 : Fin 3) = 2 := hx h
        omega,
      fun h => by
        have : (1 : Fin 3) = 2 := hx h
        omega⟩
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Sum over three-point injections as a sum over pairwise-distinct ordered
triples. -/
theorem sum_embedding_three
    {G : Type*} [Fintype G] [DecidableEq G]
    (F : G -> G -> G -> Real) :
    (∑ e : Fin 3 ↪ G, F (e 0) (e 1) (e 2)) =
      ∑ u : G, ∑ v : G, ∑ w : G,
        if u ≠ v ∧ u ≠ w ∧ v ≠ w then F u v w else 0 := by
  calc
    (∑ e : Fin 3 ↪ G, F (e 0) (e 1) (e 2)) =
      ∑ x : Fin 3 -> G,
        if Function.Injective x then F (x 0) (x 1) (x 2) else 0 :=
      sum_embedding_eq_sum_if_injective
        (fun x : Fin 3 -> G => F (x 0) (x 1) (x 2))
    (∑ x : Fin 3 -> G,
        if Function.Injective x then F (x 0) (x 1) (x 2) else 0) =
      ∑ t : G × G × G,
        if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then
          F t.1 t.2.1 t.2.2 else 0 := by
      exact Fintype.sum_equiv (finThreeArrowEquiv G)
        (fun x : Fin 3 -> G =>
          if Function.Injective x then F (x 0) (x 1) (x 2) else 0)
        (fun t : G × G × G =>
          if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then
            F t.1 t.2.1 t.2.2 else 0)
        (fun x => by
          dsimp [finThreeArrowEquiv]
          have hiff := injective_fin_three_iff x
          by_cases hx : Function.Injective x
          · have hp := hiff.mp hx
            simp [hx, hp]
          · have hp :
                ¬(x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2) :=
              fun h => hx (hiff.mpr h)
            simp [hx, hp])
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]

/-- Inclusion-exclusion for the three distinctness constraints. -/
theorem distinct_three_indicator {G : Type*} [DecidableEq G]
    (u v w : G) (z : Real) :
    (if u ≠ v ∧ u ≠ w ∧ v ≠ w then z else 0) =
      z - (if u = v then z else 0) -
        (if u = w then z else 0) -
        (if v = w then z else 0) +
        2 * (if u = v ∧ u = w then z else 0) := by
  by_cases huv : u = v <;> by_cases huw : u = w <;>
    by_cases hvw : v = w <;> simp_all <;> ring

/-- Unnormalized three-fold finite sum. -/
def tripleSum {G : Type*} [Fintype G] (F : G -> G -> G -> Real) : Real :=
  ∑ u : G, ∑ v : G, ∑ w : G, F u v w

theorem tripleSum_add {G : Type*} [Fintype G]
    (F H : G -> G -> G -> Real) :
    tripleSum (fun u v w => F u v w + H u v w) =
      tripleSum F + tripleSum H := by
  unfold tripleSum
  simp_rw [Finset.sum_add_distrib]

theorem tripleSum_sub {G : Type*} [Fintype G]
    (F H : G -> G -> G -> Real) :
    tripleSum (fun u v w => F u v w - H u v w) =
      tripleSum F - tripleSum H := by
  unfold tripleSum
  simp_rw [Finset.sum_sub_distrib]

theorem tripleSum_const_mul {G : Type*} [Fintype G] (c : Real)
    (F : G -> G -> G -> Real) :
    tripleSum (fun u v w => c * F u v w) = c * tripleSum F := by
  unfold tripleSum
  simp_rw [Finset.mul_sum]

theorem tripleSum_eq01 {G : Type*} [Fintype G] [DecidableEq G]
    (F : G -> G -> G -> Real) :
    tripleSum (fun u v w => if u = v then F u v w else 0) =
      ∑ u : G, ∑ w : G, F u u w := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro u _hu
  rw [show
      (∑ v : G, ∑ w : G, if u = v then F u v w else 0) =
        ∑ v : G, if u = v then (∑ w : G, F u v w) else 0 by
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases huv : u = v <;> simp [huv]]
  simpa [eq_comm] using
    (Finset.sum_ite_eq' (Finset.univ : Finset G) u
      (fun v => ∑ w : G, F u v w))

theorem tripleSum_eq02 {G : Type*} [Fintype G] [DecidableEq G]
    (F : G -> G -> G -> Real) :
    tripleSum (fun u v w => if u = w then F u v w else 0) =
      ∑ u : G, ∑ v : G, F u v u := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro v _hv
  simpa [eq_comm] using
    (Finset.sum_ite_eq' (Finset.univ : Finset G) u
      (fun w => F u v w))

theorem tripleSum_eq12 {G : Type*} [Fintype G] [DecidableEq G]
    (F : G -> G -> G -> Real) :
    tripleSum (fun u v w => if v = w then F u v w else 0) =
      ∑ u : G, ∑ v : G, F u v v := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro v _hv
  simpa [eq_comm] using
    (Finset.sum_ite_eq' (Finset.univ : Finset G) v
      (fun w => F u v w))

theorem tripleSum_eq012 {G : Type*} [Fintype G] [DecidableEq G]
    (F : G -> G -> G -> Real) :
    tripleSum (fun u v w => if u = v ∧ u = w then F u v w else 0) =
      ∑ u : G, F u u u := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro u _hu
  rw [show
      (∑ v : G, ∑ w : G, if u = v ∧ u = w then F u v w else 0) =
        ∑ v : G, if u = v then F u v u else 0 by
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases huv : u = v
    · subst v
      simpa [eq_comm] using
        (Finset.sum_ite_eq' (Finset.univ : Finset G) u
          (fun w => F u u w))
    · simp [huv]]
  simpa [eq_comm] using
    (Finset.sum_ite_eq' (Finset.univ : Finset G) u
      (fun v => F u v u))

/-- Three-row mask. -/
def threeMask {n : Nat} (a b c : XorSpace n) : BitMatrix 3 n := ![a, b, c]

@[simp]
theorem walsh_threeMask {n : Nat} (a b c : XorSpace n)
    (x : BitMatrix 3 n) :
    walsh (threeMask a b c) x =
      vectorWalsh a (x 0) * vectorWalsh b (x 1) *
        vectorWalsh c (x 2) := by
  have hdot : dot (threeMask a b c) x =
      vectorDot a (x 0) + vectorDot b (x 1) + vectorDot c (x 2) := by
    unfold dot
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [threeMask, vectorDot]
    abel
  unfold walsh
  rw [hdot]
  simp [vectorWalsh, bitSign_add]

/-- Product of three one-word checkerboards. -/
def threeCharacter {n : Nat} (a b c : XorSpace n)
    (u v w : XorSpace n) : Real :=
  vectorWalsh a u * vectorWalsh b v * vectorWalsh c w

theorem tripleSum_threeCharacter_eq_zero {n : Nat} (a b c : XorSpace n)
    (hc : c ≠ 0) : tripleSum (threeCharacter a b c) = 0 := by
  unfold tripleSum threeCharacter
  apply Finset.sum_eq_zero
  intro u _hu
  apply Finset.sum_eq_zero
  intro v _hv
  calc
    (∑ w : XorSpace n,
        vectorWalsh a u * vectorWalsh b v * vectorWalsh c w) =
        (vectorWalsh a u * vectorWalsh b v) *
          ∑ w : XorSpace n, vectorWalsh c w := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [sum_vectorWalsh, if_neg hc]; ring

theorem tripleSum_threeCharacter_eq01_zero {n : Nat}
    (a b c : XorSpace n) (hc : c ≠ 0) :
    tripleSum (fun u v w =>
      if u = v then threeCharacter a b c u v w else 0) = 0 := by
  rw [tripleSum_eq01]
  apply Finset.sum_eq_zero
  intro u _hu
  calc
    (∑ w : XorSpace n, threeCharacter a b c u u w) =
        (vectorWalsh a u * vectorWalsh b u) *
          ∑ w : XorSpace n, vectorWalsh c w := by
      unfold threeCharacter
      rw [Finset.mul_sum]
    _ = 0 := by rw [sum_vectorWalsh, if_neg hc]; ring

theorem tripleSum_threeCharacter_eq02_zero {n : Nat}
    (a b c : XorSpace n) (hb : b ≠ 0) :
    tripleSum (fun u v w =>
      if u = w then threeCharacter a b c u v w else 0) = 0 := by
  rw [tripleSum_eq02]
  apply Finset.sum_eq_zero
  intro u _hu
  calc
    (∑ v : XorSpace n, threeCharacter a b c u v u) =
        (vectorWalsh a u * vectorWalsh c u) *
          ∑ v : XorSpace n, vectorWalsh b v := by
      unfold threeCharacter
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      ring
    _ = 0 := by rw [sum_vectorWalsh, if_neg hb]; ring

theorem tripleSum_threeCharacter_eq12_zero {n : Nat}
    (a b c : XorSpace n) (ha : a ≠ 0) :
    tripleSum (fun u v w =>
      if v = w then threeCharacter a b c u v w else 0) = 0 := by
  rw [tripleSum_eq12]
  calc
    (∑ u : XorSpace n, ∑ v : XorSpace n,
        threeCharacter a b c u v v) =
        (∑ u : XorSpace n, vectorWalsh a u) *
          (∑ v : XorSpace n, vectorWalsh b v * vectorWalsh c v) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _hu
      unfold threeCharacter
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      ring
    _ = 0 := by rw [sum_vectorWalsh, if_neg ha]; ring

theorem tripleSum_threeCharacter_eq012 {n : Nat}
    (a b c : XorSpace n) :
    tripleSum (fun u v w =>
      if u = v ∧ u = w then threeCharacter a b c u v w else 0) =
      if a + b + c = 0 then (2 ^ n : Nat) else 0 := by
  rw [tripleSum_eq012]
  rw [show
      (∑ u : XorSpace n, threeCharacter a b c u u u) =
        ∑ u : XorSpace n, vectorWalsh (a + b + c) u by
    apply Finset.sum_congr rfl
    intro u _hu
    simp [threeCharacter, vectorWalsh_add_left, mul_assoc]]
  exact sum_vectorWalsh (a + b + c)

/-- Exact inclusion-exclusion cancellation for a full-support three-row
checkerboard over ordered distinct samples. -/
theorem tripleSum_distinct_threeCharacter {n : Nat} (a b c : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    tripleSum (fun u v w =>
      if u ≠ v ∧ u ≠ w ∧ v ≠ w then
        threeCharacter a b c u v w else 0) =
      if a + b + c = 0 then 2 * ((2 ^ n : Nat) : Real) else 0 := by
  rw [show
      (fun u v w =>
        if u ≠ v ∧ u ≠ w ∧ v ≠ w then
          threeCharacter a b c u v w else 0) =
      (fun u v w =>
        threeCharacter a b c u v w -
          (if u = v then threeCharacter a b c u v w else 0) -
          (if u = w then threeCharacter a b c u v w else 0) -
          (if v = w then threeCharacter a b c u v w else 0) +
          2 * (if u = v ∧ u = w then
            threeCharacter a b c u v w else 0)) by
    funext u v w
    exact distinct_three_indicator u v w (threeCharacter a b c u v w)]
  rw [tripleSum_add, tripleSum_sub, tripleSum_sub, tripleSum_sub,
    tripleSum_const_mul]
  rw [tripleSum_threeCharacter_eq_zero a b c hc,
    tripleSum_threeCharacter_eq01_zero a b c hc,
    tripleSum_threeCharacter_eq02_zero a b c hb,
    tripleSum_threeCharacter_eq12_zero a b c ha,
    tripleSum_threeCharacter_eq012]
  by_cases hsum : a + b + c = 0 <;> simp [hsum]

/-- Exact coefficient of a full-support three-row checkerboard under sampling
without replacement. -/
theorem average_embedding_three_walsh {n : Nat} (a b c : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hN : 3 ≤ 2 ^ n) :
    average (Fin 3 ↪ XorSpace n)
        (fun e => vectorWalsh a (e 0) * vectorWalsh b (e 1) *
          vectorWalsh c (e 2)) =
      if a + b + c = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real)) else 0 := by
  let N : Nat := 2 ^ n
  have hNreal : (N : Real) ≠ 0 := by positivity
  have hN1 : ((N - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : N - 1 ≠ 0)
  have hN2 : ((N - 2 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : N - 2 ≠ 0)
  unfold average
  rw [sum_embedding_three (fun u v w : XorSpace n =>
    vectorWalsh a u * vectorWalsh b v * vectorWalsh c w)]
  change
    tripleSum (fun u v w =>
      if u ≠ v ∧ u ≠ w ∧ v ≠ w then
        threeCharacter a b c u v w else 0) /
        (Fintype.card (Fin 3 ↪ XorSpace n) : Real) = _
  rw [tripleSum_distinct_threeCharacter a b c ha hb hc]
  rw [Fintype.card_embedding_eq, Fintype.card_fin, card_xorSpace]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, Nat.mul_one]
  norm_num [Nat.cast_mul]
  dsimp [N] at hNreal hN1 hN2
  by_cases hsum : a + b + c = 0
  · simp only [hsum, if_pos]
    field_simp [hNreal, hN1, hN2]
  · simp [hsum]

/-- Fourier form of the exact three-row coefficient. -/
theorem fourier_injectionDensity_threeMask {n : Nat}
    (a b c : XorSpace n) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hN : 3 ≤ 2 ^ n) :
    XORFourier.fourier (injectionDensity n 3) (threeMask a b c) =
      if a + b + c = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real)) else 0 := by
  rw [fourier_injectionDensity_eq_average_embedding hN]
  simpa only [walsh_threeMask] using
    average_embedding_three_walsh a b c ha hb hc hN

/-! ## Exact level-three coefficients on an arbitrary query support -/

/-- XOR of all query-row masks.  Rows outside the row support contribute
zero, so this is also the XOR around the checkerboard core. -/
def maskRowSum {n q : Nat} (a : BitMatrix q n) : XorSpace n :=
  ∑ i : Fin q, a i

/-- Reindex the XOR of a mask along an embedding containing every nonzero
row. -/
theorem maskRowSum_eq_sum_restrictMask {n q k : Nat}
    (r : Fin k ↪ Fin q) (a : BitMatrix q n)
    (hout : ∀ i, i ∉ Set.range r -> a i = 0) :
    maskRowSum a = ∑ i : Fin k, restrictMask r a i := by
  unfold maskRowSum restrictMask
  symm
  apply Fintype.sum_of_injective r r.injective
    (fun i : Fin k => a (r i)) (fun i : Fin q => a i)
  · intro i hi
    exact hout i hi
  · intro i
    rfl

/-- Every level-three injection coefficient is the same closed-triangle
coefficient, and all open three-row checkerboards cancel exactly. -/
theorem fourier_injectionDensity_of_level_eq_three
    {n q : Nat} (hq : q ≤ 2 ^ n) (a : BitMatrix q n)
    (haLevel : level a = 3) :
    XORFourier.fourier (injectionDensity n q) a =
      if maskRowSum a = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real)) else 0 := by
  let S : Finset (Fin q) := rowSupport a
  have hScard : S.card = 3 := by simpa [S, level] using haLevel
  have hFcard : Fintype.card S = 3 := by simpa using hScard
  let e : Fin 3 ≃ S :=
    (finCongr hFcard).symm.trans (Fintype.equivFin S).symm
  let r : Fin 3 ↪ Fin q :=
    e.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))
  have hr_mem (t : Fin 3) : r t ∈ rowSupport a := by
    exact (e t).2
  have hr_ne (t : Fin 3) : a (r t) ≠ 0 :=
    (mem_rowSupport a (r t)).mp (hr_mem t)
  have hout : ∀ i, i ∉ Set.range r -> a i = 0 := by
    intro i hi
    by_contra hne
    have hiS : i ∈ S := by
      dsimp [S]
      exact (mem_rowSupport a i).mpr hne
    apply hi
    let is : S := ⟨i, hiS⟩
    refine ⟨e.symm is, ?_⟩
    change (e (e.symm is)).1 = i
    simp [is]
  have hmask :
      restrictMask r a = threeMask (a (r 0)) (a (r 1)) (a (r 2)) := by
    funext i j
    fin_cases i <;> rfl
  have hsum :
      maskRowSum a = a (r 0) + a (r 1) + a (r 2) := by
    rw [maskRowSum_eq_sum_restrictMask r a hout, hmask]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [threeMask]
    abel
  have hthreeq : 3 ≤ q := by
    calc
      3 = S.card := hScard.symm
      _ ≤ (Finset.univ : Finset (Fin q)).card :=
        Finset.card_le_card (by simp)
      _ = q := by simp
  have hN : 3 ≤ 2 ^ n := hthreeq.trans hq
  rw [fourier_injectionDensity_eq_restrictMask hq r a hout, hmask]
  rw [fourier_injectionDensity_threeMask
    (a (r 0)) (a (r 1)) (a (r 2)) (hr_ne 0) (hr_ne 1) (hr_ne 2) hN]
  rw [← hsum]

/-! ## Counting the closed level-three cores -/

/-- A mask supported on `S`, obtained by extending a function on `S` by
zero. -/
def supportExtension {n q : Nat} (S : Finset (Fin q))
    (f : S → XorSpace n) : BitMatrix q n :=
  fun i => if hi : i ∈ S then f ⟨i, hi⟩ else 0

@[simp]
theorem supportExtension_apply_mem {n q : Nat} (S : Finset (Fin q))
    (f : S → XorSpace n) (i : S) :
    supportExtension S f i = f i := by
  simp [supportExtension, i.2]

theorem rowSupport_supportExtension {n q : Nat} (S : Finset (Fin q))
    (f : S → XorSpace n) (hf : ∀ i, f i ≠ 0) :
    rowSupport (supportExtension S f) = S := by
  ext i
  rw [mem_rowSupport]
  by_cases hi : i ∈ S
  · simp [supportExtension, hi, hf ⟨i, hi⟩]
  · simp [supportExtension, hi]

theorem supportExtension_rowSupport {n q : Nat} (a : BitMatrix q n) :
    supportExtension (rowSupport a) (fun i => a i) = a := by
  funext i j
  by_cases hi : i ∈ rowSupport a
  · simp [supportExtension, hi]
  · have hz : a i = 0 := by simpa using hi
    simp [supportExtension, hi, hz]

theorem maskRowSum_supportExtension {n q : Nat} (S : Finset (Fin q))
    (f : S → XorSpace n) :
    maskRowSum (supportExtension S f) = ∑ i : S, f i := by
  unfold maskRowSum
  calc
    (∑ i : Fin q, supportExtension S f i) =
        ∑ i ∈ S, supportExtension S f i := by
      symm
      apply Finset.sum_subset (by simp)
      intro i _hi hiS
      simp [supportExtension, hiS]
    _ = ∑ i : S, supportExtension S f i := by
      exact Finset.sum_subtype S (fun _ => Iff.rfl) (supportExtension S f)
    _ = ∑ i : S, f i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact supportExtension_apply_mem S f i

/-- Every word in `F_2^n` is its own additive inverse. -/
@[simp]
theorem xorSpace_add_self_eq_zero {n : Nat} (a : XorSpace n) :
    a + a = 0 := by
  funext j
  change a j + a j = 0
  rw [← two_nsmul]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  rw [CharP.cast_eq_zero (ZMod 2) 2]
  simp

theorem xorSpace_add_eq_zero_iff_eq {n : Nat} (a b : XorSpace n) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg (fun z => z + b) h
    simpa [add_assoc] using h'
  · rintro rfl
    exact xorSpace_add_self_eq_zero a

/-- Full-support, zero-XOR assignments on a finite coordinate type. -/
abbrev FullZeroSumAssignment (n : Nat) (I : Type*)
    [Fintype I] [DecidableEq I] :=
  {f : I → XorSpace n // (∀ i, f i ≠ 0) ∧ ∑ i, f i = 0}

/-- Reindex a full-support zero-XOR assignment. -/
def fullZeroSumAssignmentCongr {n : Nat} {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) :
    FullZeroSumAssignment n I ≃ FullZeroSumAssignment n J where
  toFun f := ⟨fun j => f.1 (e.symm j), by
    constructor
    · intro j
      exact f.2.1 (e.symm j)
    · rw [(e.symm.sum_comp f.1)]
      exact f.2.2⟩
  invFun f := ⟨fun i => f.1 (e i), by
    constructor
    · intro i
      exact f.2.1 (e i)
    · rw [e.sum_comp f.1]
      exact f.2.2⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    simp
  right_inv f := by
    apply Subtype.ext
    funext j
    simp

/-- Ordered pairs of distinct nonzero words. -/
abbrev DistinctNonzeroPair (n : Nat) :=
  {p : XorSpace n × XorSpace n //
    p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2}

/-- A zero-XOR nonzero triple is uniquely determined by its first two,
which must be distinct. -/
def fullZeroSumThreeEquivPair (n : Nat) :
    FullZeroSumAssignment n (Fin 3) ≃ DistinctNonzeroPair n where
  toFun f := ⟨(f.1 0, f.1 1), f.2.1 0, f.2.1 1, by
    intro h01
    have hsum := f.2.2
    rw [Fin.sum_univ_three] at hsum
    change f.1 0 = f.1 1 at h01
    rw [h01] at hsum
    have hz : f.1 2 = 0 := by
      simpa [← add_assoc] using hsum
    exact f.2.1 2 hz⟩
  invFun p := ⟨![p.1.1, p.1.2, p.1.1 + p.1.2], by
    constructor
    · intro i
      fin_cases i
      · exact p.2.1
      · exact p.2.2.1
      · simpa [xorSpace_add_eq_zero_iff_eq] using p.2.2.2
    · rw [Fin.sum_univ_three]
      change p.1.1 + p.1.2 + (p.1.1 + p.1.2) = 0
      calc
        p.1.1 + p.1.2 + (p.1.1 + p.1.2) =
            (p.1.1 + p.1.1) + (p.1.2 + p.1.2) := by abel
        _ = 0 := by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · have hsum := f.2.2
      rw [Fin.sum_univ_three] at hsum
      have h := congrArg (fun z => z + f.1 2) hsum
      simpa [add_assoc] using h
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Nonzero words have cardinality `N-1`. -/
theorem card_xorSpace_ne_zero (n : Nat) :
    Fintype.card {a : XorSpace n // a ≠ 0} = 2 ^ n - 1 := by
  let e : {a : XorSpace n // a ≠ 0} ≃
      {a : XorSpace n // a ∈ (Finset.univ : Finset (XorSpace n)).erase 0} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun a => by simp)
  rw [Fintype.card_congr e]
  simp [card_xorSpace]

/-- After excluding zero and one fixed nonzero word, `N-2` words remain. -/
theorem card_xorSpace_ne_zero_ne {n : Nat} (a : XorSpace n) (ha : a ≠ 0) :
    Fintype.card {b : XorSpace n // b ≠ 0 ∧ b ≠ a} = 2 ^ n - 2 := by
  let e : {b : XorSpace n // b ≠ 0 ∧ b ≠ a} ≃
      {b : XorSpace n //
        b ∈ ((Finset.univ : Finset (XorSpace n)).erase 0).erase a} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun b => by simp [and_comm])
  rw [Fintype.card_congr e]
  rw [Fintype.card_coe]
  rw [Finset.card_erase_of_mem (by simp [ha])]
  rw [Finset.card_erase_of_mem (by simp)]
  simp [card_xorSpace]
  omega

theorem card_xorSpace_ne_zero_ne_subtype {n : Nat}
    (a : {a : XorSpace n // a ≠ 0}) :
    Fintype.card {b : XorSpace n // b ≠ 0 ∧ b ≠ a.1} = 2 ^ n - 2 :=
  card_xorSpace_ne_zero_ne a.1 a.2

/-- Split an ordered distinct-nonzero pair into its first word and the second
word with the two exclusions recorded in its fiber. -/
def distinctNonzeroPairSigmaEquiv (n : Nat) :
    DistinctNonzeroPair n ≃
      Σ a : {a : XorSpace n // a ≠ 0},
        {b : XorSpace n // b ≠ 0 ∧ b ≠ a.1} where
  toFun p := ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1, Ne.symm p.2.2.2⟩⟩
  invFun p := ⟨(p.1.1, p.2.1), p.1.2, p.2.2.1, Ne.symm p.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨a, b⟩
    rfl

/-- Exact number of full-support zero-XOR triples. -/
theorem card_fullZeroSumAssignment_fin_three (n : Nat) :
    Fintype.card (FullZeroSumAssignment n (Fin 3)) =
      (2 ^ n - 1) * (2 ^ n - 2) := by
  rw [Fintype.card_congr (fullZeroSumThreeEquivPair n)]
  rw [Fintype.card_congr (distinctNonzeroPairSigmaEquiv n)]
  rw [Fintype.card_sigma]
  simp_rw [card_xorSpace_ne_zero_ne_subtype]
  rw [Finset.sum_const]
  change Fintype.card {a : XorSpace n // a ≠ 0} * (2 ^ n - 2) = _
  rw [card_xorSpace_ne_zero]

/-- Three-element query supports. -/
abbrev ThreeSupport (q : Nat) :=
  {S : Finset (Fin q) // S.card = 3}

theorem card_threeSupport (q : Nat) :
    Fintype.card (ThreeSupport q) = q.choose 3 := by
  let e : ThreeSupport q ≃
      {S : Finset (Fin q) //
        S ∈ (Finset.univ : Finset (Fin q)).powersetCard 3} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun S => by simp)
  rw [Fintype.card_congr e]
  rw [Fintype.card_coe]
  simp [Finset.card_powersetCard]

/-- Level-three masks whose checkerboard closes. -/
abbrev LevelThreeZeroMask (n q : Nat) :=
  {a : BitMatrix q n // level a = 3 ∧ maskRowSum a = 0}

/-- The support map on closed level-three masks. -/
def levelThreeSupportOf {n q : Nat} (a : LevelThreeZeroMask n q) :
    ThreeSupport q :=
  ⟨rowSupport a.1, by simpa [level] using a.2.1⟩

/-- A fiber of the support map is exactly the full-support zero-XOR
assignments on that fixed support. -/
def levelThreeZeroFiberEquiv {n q : Nat} (S : ThreeSupport q) :
    {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S} ≃
      FullZeroSumAssignment n S.1 where
  toFun a := ⟨fun i => a.1.1 i, by
    have hsupp : rowSupport a.1.1 = S.1 :=
      congrArg Subtype.val a.2
    constructor
    · intro i
      apply (mem_rowSupport a.1.1 i).mp
      rw [hsupp]
      exact i.2
    · have hext : supportExtension S.1 (fun i => a.1.1 i) = a.1.1 := by
        funext i j
        by_cases hi : i ∈ S.1
        · simp [supportExtension, hi]
        · have hz : a.1.1 i = 0 := by
            rw [← hsupp] at hi
            simpa using hi
          simp [supportExtension, hi, hz]
      have hsum := maskRowSum_supportExtension S.1 (fun i => a.1.1 i)
      rw [hext] at hsum
      rw [← hsum]
      exact a.1.2.2⟩
  invFun f := ⟨⟨supportExtension S.1 f.1, by
      constructor
      · unfold level
        rw [rowSupport_supportExtension S.1 f.1 f.2.1]
        exact S.2
      · rw [maskRowSum_supportExtension]
        exact f.2.2⟩, by
    apply Subtype.ext
    exact rowSupport_supportExtension S.1 f.1 f.2.1⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    have hsupp : rowSupport a.1.1 = S.1 :=
      congrArg Subtype.val a.2
    funext i j
    by_cases hi : i ∈ S.1
    · simp [supportExtension, hi]
    · have hz : a.1.1 i = 0 := by
        rw [← hsupp] at hi
        simpa using hi
      simp [supportExtension, hi, hz]
  right_inv f := by
    apply Subtype.ext
    funext i j
    simp [supportExtension]

/-- Exact number of closed level-three checkerboards on `q` query rows. -/
theorem card_levelThreeZeroMask (n q : Nat) :
    Fintype.card (LevelThreeZeroMask n q) =
      q.choose 3 * ((2 ^ n - 1) * (2 ^ n - 2)) := by
  calc
    Fintype.card (LevelThreeZeroMask n q) =
        Fintype.card (Σ S : ThreeSupport q,
          {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S}) :=
      (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (levelThreeSupportOf (n := n) (q := q)))).symm
    _ = ∑ S : ThreeSupport q,
        Fintype.card {a : LevelThreeZeroMask n q //
          levelThreeSupportOf a = S} := Fintype.card_sigma
    _ = ∑ _S : ThreeSupport q,
        ((2 ^ n - 1) * (2 ^ n - 2)) := by
      apply Finset.sum_congr rfl
      intro S _hS
      rw [Fintype.card_congr (levelThreeZeroFiberEquiv S)]
      have hScard : Fintype.card S.1 = 3 := by simpa using S.2
      let e : Fin 3 ≃ S.1 :=
        (finCongr hScard).symm.trans (Fintype.equivFin S.1).symm
      rw [← card_fullZeroSumAssignment_fin_three n]
      exact Fintype.card_congr (fullZeroSumAssignmentCongr e.symm)
    _ = q.choose 3 * ((2 ^ n - 1) * (2 ^ n - 2)) := by
      rw [Finset.sum_const]
      change Fintype.card (ThreeSupport q) *
        ((2 ^ n - 1) * (2 ^ n - 2)) = _
      rw [card_threeSupport]

/-! ## Exact level-three Fourier energy -/

/-- Fourth-power Fourier energy on one exact row level. -/
def injectionLevelEnergy (n q k : Nat) : Real :=
  ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
      (fun a => level a = k),
    (XORFourier.fourier (injectionDensity n q) a) ^ 4

/-- Exact `V₃`: every closed triple contributes the same fourth power and
there are `choose(q,3) * (N-1) * (N-2)` such triples. -/
theorem injectionLevelEnergy_three_eq {n q : Nat}
    (hN : 3 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) :
    injectionLevelEnergy n q 3 =
      16 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
          (((2 ^ n - 2 : Nat) : Real) ^ 3)) := by
  let c : Real :=
    2 / (((2 ^ n - 1 : Nat) : Real) *
      ((2 ^ n - 2 : Nat) : Real))
  let closed : BitMatrix q n → Prop :=
    fun a => level a = 3 ∧ maskRowSum a = 0
  have hcard :
      ((Finset.univ : Finset (BitMatrix q n)).filter closed).card =
        q.choose 3 * ((2 ^ n - 1) * (2 ^ n - 2)) := by
    let e : LevelThreeZeroMask n q ≃
        {a : BitMatrix q n //
          a ∈ (Finset.univ : Finset (BitMatrix q n)).filter closed} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun a => by
        simp [closed])
    calc
      ((Finset.univ : Finset (BitMatrix q n)).filter closed).card =
          Fintype.card {a : BitMatrix q n //
            a ∈ (Finset.univ : Finset (BitMatrix q n)).filter closed} := by
        rw [Fintype.card_coe]
      _ = Fintype.card (LevelThreeZeroMask n q) :=
        (Fintype.card_congr e).symm
      _ = q.choose 3 * ((2 ^ n - 1) * (2 ^ n - 2)) :=
        card_levelThreeZeroMask n q
  have hN1 : ((2 ^ n - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : 2 ^ n - 1 ≠ 0)
  have hN2 : ((2 ^ n - 2 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : 2 ^ n - 2 ≠ 0)
  unfold injectionLevelEnergy
  calc
    (∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
        (fun a => level a = 3),
        (XORFourier.fourier (injectionDensity n q) a) ^ 4) =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun a => level a = 3),
        if maskRowSum a = 0 then c ^ 4 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have haLevel : level a = 3 := by simpa using ha
      rw [fourier_injectionDensity_of_level_eq_three hq a haLevel]
      by_cases hclosed : maskRowSum a = 0 <;> simp [hclosed, c]
    _ = ∑ a ∈ ((Finset.univ : Finset (BitMatrix q n)).filter
          (fun a => level a = 3)).filter (fun a => maskRowSum a = 0),
        c ^ 4 := by
      exact (Finset.sum_filter (fun a : BitMatrix q n => maskRowSum a = 0)
        (fun _a => c ^ 4)).symm
    _ = ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter closed,
        c ^ 4 := by
      rw [Finset.filter_filter]
    _ = (((Finset.univ : Finset (BitMatrix q n)).filter closed).card : Real) *
        c ^ 4 := by simp
    _ = ((q.choose 3 * ((2 ^ n - 1) * (2 ^ n - 2)) : Nat) : Real) *
        c ^ 4 := by rw [hcard]
    _ = 16 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
          (((2 ^ n - 2 : Nat) : Real) ^ 3)) := by
      dsimp [c]
      norm_num [Nat.cast_mul]
      field_simp [hN1, hN2]
      ring

end RandomSystems.SoP.XORCore
