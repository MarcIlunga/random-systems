/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORFourier
import RandomSystems.SoP.XORCollisionProxy

/-!
# The uniform-injection representative for XOR SoP

This file connects the checkerboard transform to the concrete Lanzenberger
representative used in the collision-proxy proof.  A single permutation tape
is represented by the sampling-without-replacement density

`mu(x) = N^q / (N)_q` on injective tapes and `0` elsewhere.

The first main identity is pointwise, with no inequality: normalized XOR
convolution of two copies of `mu` is exactly the visible SoP likelihood ratio.
The general gain-graph representative remains outside this XOR-only module.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.SoP.XORInjection

open RandomSystems.CompatibleCount
open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.XORFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The XOR carrier used by DNS and by the constrained collision proof. -/
abbrev XorSpace (n : Nat) := Fin n -> ZMod 2

@[simp]
theorem card_xorSpace (n : Nat) : Fintype.card (XorSpace n) = 2 ^ n := by
  simp [XorSpace]

/-! ## Uniform injections as permutation restrictions -/

/-- Restrict a permutation to a fixed injective schedule. -/
def permEvalEmbedding {G : Type*} {q : Nat}
    (xs : Fin q ↪ G) (pi : Equiv.Perm G) : Fin q ↪ G :=
  ⟨fun i => pi (xs i), pi.injective.comp xs.injective⟩

@[simp]
theorem permEvalEmbedding_apply {G : Type*} {q : Nat}
    (xs : Fin q ↪ G) (pi : Equiv.Perm G) (i : Fin q) :
    permEvalEmbedding xs pi i = pi (xs i) := rfl

/-- Fiberwise sum for the map taking a permutation to its values on an
injective schedule.  Every injection has exactly `(N-q)!` extensions. -/
theorem sum_permEvalEmbedding {G : Type*} [Fintype G] [DecidableEq G]
    {q : Nat} (hq : q <= Fintype.card G) (xs : Fin q ↪ G)
    (F : (Fin q ↪ G) -> Real) :
    (∑ pi : Equiv.Perm G, F (permEvalEmbedding xs pi)) =
      ((Fintype.card G - q).factorial : Real) *
        ∑ e : Fin q ↪ G, F e := by
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (Equiv.Perm G)))
    (g := permEvalEmbedding xs) (f := fun pi => F (permEvalEmbedding xs pi))]
  calc
    (∑ e : Fin q ↪ G,
        ∑ pi ∈ (Finset.univ : Finset (Equiv.Perm G)).filter
          (fun pi => permEvalEmbedding xs pi = e),
          F (permEvalEmbedding xs pi)) =
      ∑ e : Fin q ↪ G,
        (((Finset.univ : Finset (Equiv.Perm G)).filter
          (fun pi => permEvalEmbedding xs pi = e)).card : Real) * F e := by
      apply Finset.sum_congr rfl
      intro e _he
      calc
        (∑ pi ∈ (Finset.univ : Finset (Equiv.Perm G)).filter
            (fun pi => permEvalEmbedding xs pi = e),
            F (permEvalEmbedding xs pi)) =
          ∑ _pi ∈ (Finset.univ : Finset (Equiv.Perm G)).filter
            (fun pi => permEvalEmbedding xs pi = e), F e := by
            apply Finset.sum_congr rfl
            intro pi hpi
            have heval : permEvalEmbedding xs pi = e := by simpa using hpi
            rw [heval]
        _ = (((Finset.univ : Finset (Equiv.Perm G)).filter
              (fun pi => permEvalEmbedding xs pi = e)).card : Real) * F e := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ e : Fin q ↪ G,
        ((Fintype.card G - q).factorial : Real) * F e := by
      apply Finset.sum_congr rfl
      intro e _he
      congr 1
      norm_cast
      have hfiber := RandomSystems.CR18.Counting.card_perm_fiber
        (X := G) (q := q) xs xs.injective e e.injective hq
      apply Eq.trans _ hfiber
      apply congrArg Finset.card
      ext pi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h i
        exact congrFun (congrArg DFunLike.coe h) i
      · intro h
        ext i
        exact h i
    _ = ((Fintype.card G - q).factorial : Real) *
        ∑ e : Fin q ↪ G, F e := by
      rw [Finset.mul_sum]

/-- A uniform ordered injection is exactly the restriction of a uniform
permutation, at the level of normalized expectations. -/
theorem average_permEvalEmbedding_eq_average_embedding
    {G : Type*} [Fintype G] [DecidableEq G]
    {q : Nat} (hq : q <= Fintype.card G) (xs : Fin q ↪ G)
    (F : (Fin q ↪ G) -> Real) :
    average (Equiv.Perm G) (fun pi => F (permEvalEmbedding xs pi)) =
      average (Fin q ↪ G) F := by
  unfold average
  rw [sum_permEvalEmbedding hq xs F]
  rw [Fintype.card_perm, Fintype.card_embedding_eq, Fintype.card_fin]
  let N := Fintype.card G
  let D := N.descFactorial q
  have hD : D ≠ 0 := (Nat.descFactorial_pos.mpr (by simpa [N] using hq)).ne'
  have hfac : (N - q).factorial * D = N.factorial :=
    Nat.factorial_mul_descFactorial (by simpa [N] using hq)
  have hfacR : (((N - q).factorial : Nat) : Real) * (D : Real) =
      (N.factorial : Real) := by exact_mod_cast hfac
  have hDR : (D : Real) ≠ 0 := by exact_mod_cast hD
  have hfactR : (N.factorial : Real) ≠ 0 := by positivity
  change (((N - q).factorial : Nat) : Real) *
      (∑ e : Fin q ↪ G, F e) / (N.factorial : Real) =
    (∑ e : Fin q ↪ G, F e) / (D : Real)
  field_simp [hDR, hfactR]
  rw [← hfacR]
  ring

/-- Restricting a uniform injection along any index embedding produces a
uniform injection on the smaller index set. -/
theorem average_embedding_comp
    {G : Type*} [Fintype G] [DecidableEq G]
    {q k : Nat} (hq : q <= Fintype.card G) (r : Fin k ↪ Fin q)
    (F : (Fin k ↪ G) -> Real) :
    average (Fin q ↪ G) (fun e => F (r.trans e)) =
      average (Fin k ↪ G) F := by
  obtain ⟨xs⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin q) (β := G) (by simpa using hq)
  have hk : k <= Fintype.card G := by
    have hr : k <= q := by
      simpa using Fintype.card_le_of_injective r r.injective
    exact hr.trans hq
  calc
    average (Fin q ↪ G) (fun e => F (r.trans e)) =
        average (Equiv.Perm G)
          (fun pi => F (r.trans (permEvalEmbedding xs pi))) :=
      (average_permEvalEmbedding_eq_average_embedding hq xs
        (fun e => F (r.trans e))).symm
    _ = average (Equiv.Perm G)
          (fun pi => F (permEvalEmbedding (r.trans xs) pi)) := by
      apply congrArg (average (Equiv.Perm G))
      funext pi
      rfl
    _ = average (Fin k ↪ G) F :=
      average_permEvalEmbedding_eq_average_embedding hk (r.trans xs) F

/-- Density, relative to a uniform tape, of a uniform ordered injection. -/
def injectionDensity (n q : Nat) (x : BitMatrix q n) : Real :=
  if Function.Injective x then
    ((2 ^ n : Nat) : Real) ^ q /
      (((2 ^ n).descFactorial q : Nat) : Real)
  else 0

/-- Compatible-count likelihood written directly over `Real`. -/
def compatibleDensity (n q : Nat) (y : BitMatrix q n) : Real :=
  (compatibleCountNat y : Real) * ((2 ^ n : Nat) : Real) ^ q /
    ((((2 ^ n).descFactorial q : Nat) : Real) ^ 2)

private theorem card_bitMatrix (n q : Nat) :
    Fintype.card (BitMatrix q n) = (2 ^ n) ^ q := by
  simp [BitMatrix]

private theorem descFactorial_real_ne_zero {n q : Nat} (hq : q <= 2 ^ n) :
    ((((2 ^ n).descFactorial q : Nat) : Real)) ≠ 0 := by
  exact_mod_cast (Nat.descFactorial_pos.mpr hq).ne'

/-- The injection density is normalized. -/
theorem average_injectionDensity_eq_one {n q : Nat} (hq : q <= 2 ^ n) :
    average (BitMatrix q n) (injectionDensity n q) = 1 := by
  let N : Nat := 2 ^ n
  let D : Nat := N.descFactorial q
  have hD : D ≠ 0 := (Nat.descFactorial_pos.mpr (by simpa [N] using hq)).ne'
  have hDR : (D : Real) ≠ 0 := by exact_mod_cast hD
  have hcardInjective :
      ((Finset.univ : Finset (BitMatrix q n)).filter
        (fun x => Function.Injective x)).card = D := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr
      (Equiv.subtypeInjectiveEquivEmbedding (Fin q) (XorSpace n))]
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    simp [D, N, card_xorSpace]
  unfold average injectionDensity
  rw [show
      (∑ x : BitMatrix q n,
        if Function.Injective x then (N : Real) ^ q / (D : Real) else 0) =
      (((Finset.univ : Finset (BitMatrix q n)).filter
        (fun x => Function.Injective x)).card : Real) *
          ((N : Real) ^ q / (D : Real)) by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]]
  rw [hcardInjective]
  rw [card_bitMatrix]
  change (D : Real) * ((N : Real) ^ q / (D : Real)) /
      (((N ^ q : Nat) : Real)) = 1
  norm_num [Nat.cast_pow]
  have hNR : (N : Real) ≠ 0 := by dsimp [N]; positivity
  field_simp [hDR, hNR]

/-- Walsh coefficients of the density are ordinary expectations over a
uniform embedding.  This is the exact change from a density on all tapes to
the explanation-deck view. -/
theorem fourier_injectionDensity_eq_average_embedding
    {n q : Nat} (hq : q <= 2 ^ n) (a : BitMatrix q n) :
    XORFourier.fourier (injectionDensity n q) a =
      average (Fin q ↪ XorSpace n) (fun e => walsh a e) := by
  let N : Nat := 2 ^ n
  let D : Nat := N.descFactorial q
  have hDR : (D : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by simpa [N] using hq)).ne'
  have hNR : (N : Real) ≠ 0 := by dsimp [N]; positivity
  have hfilter :
      (∑ x ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun x => Function.Injective x), walsh a x) =
        ∑ e : Fin q ↪ XorSpace n, walsh a e := by
    calc
      (∑ x ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun x => Function.Injective x), walsh a x) =
          ∑ x : {x : BitMatrix q n // Function.Injective x}, walsh a x.1 := by
            rw [Finset.sum_subtype]
            intro x
            simp
      _ = ∑ e : Fin q ↪ XorSpace n, walsh a e := by
        exact Fintype.sum_equiv
          (Equiv.subtypeInjectiveEquivEmbedding (Fin q) (XorSpace n))
          (fun x : {x : BitMatrix q n // Function.Injective x} => walsh a x.1)
          (fun e : Fin q ↪ XorSpace n => walsh a e)
          (fun _x => rfl)
  unfold XORFourier.fourier average injectionDensity
  rw [show
      (∑ x : BitMatrix q n,
        (if Function.Injective x then (N : Real) ^ q / (D : Real) else 0) *
          walsh a x) =
        ((N : Real) ^ q / (D : Real)) *
          ∑ e : Fin q ↪ XorSpace n, walsh a e by
      calc
        (∑ x : BitMatrix q n,
          (if Function.Injective x then (N : Real) ^ q / (D : Real) else 0) *
            walsh a x) =
          ∑ x ∈ (Finset.univ : Finset (BitMatrix q n)).filter
            (fun x => Function.Injective x),
              ((N : Real) ^ q / (D : Real)) * walsh a x := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro x _hx
                by_cases hinj : Function.Injective x <;> simp [hinj]
        _ = ((N : Real) ^ q / (D : Real)) *
            ∑ x ∈ (Finset.univ : Finset (BitMatrix q n)).filter
              (fun x => Function.Injective x), walsh a x := by
                rw [Finset.mul_sum]
        _ = ((N : Real) ^ q / (D : Real)) *
            ∑ e : Fin q ↪ XorSpace n, walsh a e := by rw [hfilter]]
  rw [card_bitMatrix, Fintype.card_embedding_eq, Fintype.card_fin,
    card_xorSpace]
  change
    ((N : Real) ^ q / (D : Real)) *
        (∑ e : Fin q ↪ XorSpace n, walsh a e) /
      (((N ^ q : Nat) : Real)) =
    (∑ e : Fin q ↪ XorSpace n, walsh a e) / (D : Real)
  norm_num [Nat.cast_pow]
  field_simp [hDR, hNR]

/-! ## The exact two-row checkerboard coefficient -/

/-- Parity pairing on one XOR word. -/
def vectorDot {n : Nat} (a x : XorSpace n) : ZMod 2 :=
  ∑ j : Fin n, a j * x j

/-- One-word Walsh sign. -/
def vectorWalsh {n : Nat} (a x : XorSpace n) : Real :=
  bitSign (vectorDot a x)

@[simp]
theorem vectorWalsh_zero_left {n : Nat} (x : XorSpace n) :
    vectorWalsh 0 x = 1 := by
  simp [vectorWalsh, vectorDot]

@[simp]
theorem vectorWalsh_zero_right {n : Nat} (a : XorSpace n) :
    vectorWalsh a 0 = 1 := by
  simp [vectorWalsh, vectorDot]

@[simp]
theorem vectorWalsh_add_left {n : Nat} (a b x : XorSpace n) :
    vectorWalsh (a + b) x = vectorWalsh a x * vectorWalsh b x := by
  simp only [vectorWalsh, vectorDot, Pi.add_apply, add_mul,
    Finset.sum_add_distrib, bitSign_add]

@[simp]
theorem vectorWalsh_add_right {n : Nat} (a x y : XorSpace n) :
    vectorWalsh a (x + y) = vectorWalsh a x * vectorWalsh a y := by
  simp only [vectorWalsh, vectorDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, bitSign_add]

/-- One-word checkerboards as additive characters. -/
def vectorWalshChar {n : Nat} (a : XorSpace n) : AddChar (XorSpace n) Real where
  toFun := vectorWalsh a
  map_zero_eq_one' := vectorWalsh_zero_right a
  map_add_eq_mul' := vectorWalsh_add_right a

@[simp]
theorem vectorWalshChar_apply {n : Nat} (a x : XorSpace n) :
    vectorWalshChar a x = vectorWalsh a x := rfl

private def vectorSingleBit {n : Nat} (j : Fin n) : XorSpace n :=
  fun j' => if j' = j then 1 else 0

@[simp]
private theorem vectorDot_singleBit {n : Nat} (a : XorSpace n) (j : Fin n) :
    vectorDot a (vectorSingleBit j) = a j := by
  simp [vectorDot, vectorSingleBit]

theorem vectorWalshChar_injective {n : Nat} :
    Function.Injective (vectorWalshChar : XorSpace n -> AddChar (XorSpace n) Real) := by
  intro a b h
  funext j
  apply bitSign_injective
  simpa [vectorWalsh, vectorDot_singleBit] using
    DFunLike.congr_fun h (vectorSingleBit j)

@[simp]
theorem vectorWalshChar_eq_zero_iff {n : Nat} (a : XorSpace n) :
    vectorWalshChar a = 0 ↔ a = 0 := by
  have hzero : vectorWalshChar (0 : XorSpace n) = 0 := by
    ext x
    simp [vectorWalshChar]
  rw [← hzero]
  exact vectorWalshChar_injective.eq_iff

/-- Complete character sum on one XOR word. -/
theorem sum_vectorWalsh {n : Nat} (a : XorSpace n) :
    (∑ x : XorSpace n, vectorWalsh a x) =
      if a = 0 then (2 ^ n : Nat) else 0 := by
  have h := AddChar.expect_eq_ite (vectorWalshChar a)
  have h' :
      (∑ x : XorSpace n, vectorWalsh a x) /
          (Fintype.card (XorSpace n) : Real) =
        if a = 0 then 1 else 0 := by
    simpa only [vectorWalshChar_apply, vectorWalshChar_eq_zero_iff,
      Fintype.expect_eq_sum_div_card] using h
  rw [card_xorSpace] at h'
  have hN : ((2 ^ n : Nat) : Real) ≠ 0 := by positivity
  have hsum :
      (∑ x : XorSpace n, vectorWalsh a x) =
        (if a = 0 then (2 ^ n : Real) else 0) := by
    by_cases ha : a = 0
    · rw [if_pos ha]
      have hha := h'
      rw [if_pos ha] at hha
      convert (div_eq_one_iff_eq hN).mp hha using 1 <;>
        norm_num [Nat.cast_pow]
    · rw [if_neg ha]
      have hha := h'
      rw [if_neg ha] at hha
      exact (div_eq_zero_iff).mp hha |>.resolve_right hN
  simpa using hsum

/-- Two-row mask with rows `a` and `b`. -/
def twoMask {n : Nat} (a b : XorSpace n) : BitMatrix 2 n := ![a, b]

@[simp]
theorem walsh_twoMask {n : Nat} (a b : XorSpace n) (x : BitMatrix 2 n) :
    walsh (twoMask a b) x = vectorWalsh a (x 0) * vectorWalsh b (x 1) := by
  simp [walsh, dot, twoMask, vectorWalsh, vectorDot]

/-- Embeddings of two points are ordered unequal pairs. -/
def embeddingTwoEquivNeProd (G : Type*) [DecidableEq G] :
    (Fin 2 ↪ G) ≃ {p : G × G // p.1 ≠ p.2} where
  toFun e := ⟨(e 0, e 1), fun h => Fin.zero_ne_one (e.injective h)⟩
  invFun p :=
    ⟨![p.1.1, p.1.2], by
      intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exact (p.2 h).elim
      · exact (p.2 h.symm).elim
      · rfl⟩
  left_inv e := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Sum over two-point injections as a sum over unequal ordered pairs. -/
theorem sum_embedding_two {G : Type*} [Fintype G] [DecidableEq G]
    (F : G -> G -> Real) :
    (∑ e : Fin 2 ↪ G, F (e 0) (e 1)) =
      ∑ u : G, ∑ v : G, if u ≠ v then F u v else 0 := by
  calc
    (∑ e : Fin 2 ↪ G, F (e 0) (e 1)) =
        ∑ p : {p : G × G // p.1 ≠ p.2}, F p.1.1 p.1.2 := by
      exact Fintype.sum_equiv (embeddingTwoEquivNeProd G)
        (fun e : Fin 2 ↪ G => F (e 0) (e 1))
        (fun p : {p : G × G // p.1 ≠ p.2} => F p.1.1 p.1.2)
        (fun _e => rfl)
    _ = ∑ p ∈ (Finset.univ : Finset (G × G)).filter
          (fun p => p.1 ≠ p.2), F p.1 p.2 := by
      symm
      apply Finset.sum_subtype
      intro p
      simp
    _ = ∑ p : G × G, if p.1 ≠ p.2 then F p.1 p.2 else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ u : G, ∑ v : G, if u ≠ v then F u v else 0 := by
      rw [Fintype.sum_prod_type]

/-- Removing the diagonal from a product sum. -/
theorem sum_ne_mul_eq_mul_sum_sub_diag
    {G : Type*} [Fintype G] [DecidableEq G] (f g : G -> Real) :
    (∑ u : G, ∑ v : G, if u ≠ v then f u * g v else 0) =
      (∑ u : G, f u) * (∑ v : G, g v) -
        ∑ u : G, f u * g u := by
  calc
    (∑ u : G, ∑ v : G, if u ≠ v then f u * g v else 0) =
        ∑ u : G, f u * ∑ v ∈ (Finset.univ : Finset G).erase u, g v := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr
      · ext v
        simp [ne_comm]
      · intro v _hv
        rfl
    _ = ∑ u : G, f u * ((∑ v : G, g v) - g u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      congr 1
      have herase := Finset.sum_erase_add (s := (Finset.univ : Finset G)) g
        (Finset.mem_univ u)
      linarith
    _ = (∑ u : G, f u) * (∑ v : G, g v) -
        ∑ u : G, f u * g u := by
      rw [show (fun u => f u * ((∑ v : G, g v) - g u)) =
          (fun u => f u * (∑ v : G, g v) - f u * g u) by
        funext u
        ring]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]

private theorem xorVector_add_eq_zero_iff_eq {n : Nat} (a b : XorSpace n) :
    a + b = 0 ↔ a = b := by
  have selfZero (x : XorSpace n) : x + x = 0 := by
    funext j
    change x j + x j = 0
    rw [← two_nsmul]
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    rw [CharP.cast_eq_zero (ZMod 2) 2]
    simp
  constructor
  · intro h
    have h' := congrArg (fun z => z + b) h
    simpa [add_assoc, selfZero b] using h'
  · intro h
    subst a
    exact selfZero b

/-- Exact signed average of a full-support two-row checkerboard under a
uniform ordered injection. -/
theorem average_embedding_two_walsh {n : Nat} (a b : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    average (Fin 2 ↪ XorSpace n)
        (fun e => vectorWalsh a (e 0) * vectorWalsh b (e 1)) =
      if a = b then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0 := by
  let N : Nat := 2 ^ n
  have hN2 : 2 <= N := by
    dsimp [N]
    have hn : n ≠ 0 := by
      intro hn
      subst n
      apply ha
      exact Subsingleton.elim _ _
    exact Nat.one_lt_two_pow hn
  have hNm1R : ((N - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : N - 1 ≠ 0)
  unfold average
  change
    (∑ e : Fin 2 ↪ XorSpace n,
      vectorWalsh a (e 0) * vectorWalsh b (e 1)) /
        (Fintype.card (Fin 2 ↪ XorSpace n) : Real) = _
  rw [sum_embedding_two
    (fun u v : XorSpace n => vectorWalsh a u * vectorWalsh b v)]
  rw [sum_ne_mul_eq_mul_sum_sub_diag]
  rw [sum_vectorWalsh a, sum_vectorWalsh b, if_neg ha, if_neg hb]
  rw [show (∑ u : XorSpace n, vectorWalsh a u * vectorWalsh b u) =
      ∑ u : XorSpace n, vectorWalsh (a + b) u by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [vectorWalsh_add_left]]
  rw [sum_vectorWalsh]
  rw [Fintype.card_embedding_eq, Fintype.card_fin, card_xorSpace]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    Nat.mul_one]
  by_cases hab : a = b
  · have hz : a + b = 0 := (xorVector_add_eq_zero_iff_eq a b).mpr hab
    rw [if_pos hz, if_pos hab]
    norm_num only [Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat, zero_mul, zero_sub]
    norm_num [Nat.cast_mul]
    have hpowR : (2 : Real) ^ n ≠ 0 := by positivity
    field_simp [hpowR, hNm1R]
  · have hz : a + b ≠ 0 := fun h => hab ((xorVector_add_eq_zero_iff_eq a b).mp h)
    rw [if_neg hz, if_neg hab]
    simp

/-- The exact full-support two-row Fourier coefficient of the injection
density. -/
theorem fourier_injectionDensity_twoMask {n : Nat} (a b : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    XORFourier.fourier (injectionDensity n 2) (twoMask a b) =
      if a = b then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0 := by
  have hN2 : 2 <= 2 ^ n := by
    have hn : n ≠ 0 := by
      intro hn
      subst n
      apply ha
      exact Subsingleton.elim _ _
    exact Nat.one_lt_two_pow hn
  rw [fourier_injectionDensity_eq_average_embedding hN2]
  simpa only [walsh_twoMask] using average_embedding_two_walsh a b ha hb

/-! ## Restricting a checkerboard to the rows it uses -/

/-- Pull a mask back along an embedding of query coordinates. -/
def restrictMask {n q k : Nat} (r : Fin k ↪ Fin q)
    (a : BitMatrix q n) : BitMatrix k n :=
  fun i => a (r i)

/-- A checkerboard whose mask vanishes off `range r` only sees the restricted
injection. -/
theorem walsh_eq_walsh_restrictMask {n q k : Nat}
    (r : Fin k ↪ Fin q) (a : BitMatrix q n)
    (hout : ∀ i, i ∉ Set.range r -> a i = 0)
    (x : Fin q ↪ XorSpace n) :
    walsh a x = walsh (restrictMask r a) (r.trans x) := by
  unfold walsh dot restrictMask
  congr 1
  symm
  apply Fintype.sum_of_injective r r.injective
    (fun i : Fin k => ∑ j : Fin n, a (r i) j * x (r i) j)
    (fun i : Fin q => ∑ j : Fin n, a i j * x i j)
  · intro i hi
    rw [hout i hi]
    simp
  · intro i
    rfl

/-- Fourier coefficients only depend on the rows used by their mask. -/
theorem fourier_injectionDensity_eq_restrictMask
    {n q k : Nat} (hq : q <= 2 ^ n) (r : Fin k ↪ Fin q)
    (a : BitMatrix q n) (hout : ∀ i, i ∉ Set.range r -> a i = 0) :
    XORFourier.fourier (injectionDensity n q) a =
      XORFourier.fourier (injectionDensity n k) (restrictMask r a) := by
  have hkq : k <= q := by
    simpa using Fintype.card_le_of_injective r r.injective
  have hk : k <= 2 ^ n := hkq.trans hq
  rw [fourier_injectionDensity_eq_average_embedding hq]
  rw [fourier_injectionDensity_eq_average_embedding hk]
  rw [show
      (fun e : Fin q ↪ XorSpace n => walsh a e) =
        (fun e => walsh (restrictMask r a) (r.trans e)) by
      funext e
      simpa using walsh_eq_walsh_restrictMask r a hout e]
  have hqG : q <= Fintype.card (XorSpace n) := by simpa using hq
  simpa using average_embedding_comp (G := XorSpace n) hqG r
    (fun e : Fin k ↪ XorSpace n => walsh (restrictMask r a) e)

/-- The two nonzero rows of a level-two checkerboard have a common value. -/
def supportRowsEqual {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∀ i, i ∈ rowSupport a -> ∀ j, j ∈ rowSupport a -> a i = a j

/-- Every level-two coefficient is either the equality coefficient
`-1/(N-1)` or zero. -/
theorem fourier_injectionDensity_of_level_eq_two
    {n q : Nat} (hq : q <= 2 ^ n) (a : BitMatrix q n)
    (haLevel : level a = 2) :
    XORFourier.fourier (injectionDensity n q) a =
      if supportRowsEqual a then
        -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0 := by
  let S : Finset (Fin q) := rowSupport a
  have hScard : S.card = 2 := by simpa [S, level] using haLevel
  have hFcard : Fintype.card S = 2 := by simpa using hScard
  let e : Fin 2 ≃ S :=
    (finCongr hFcard).symm.trans (Fintype.equivFin S).symm
  let r : Fin 2 ↪ Fin q :=
    e.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))
  have hr_mem (t : Fin 2) : r t ∈ rowSupport a := by
    exact (e t).2
  have hr_ne (t : Fin 2) : a (r t) ≠ 0 :=
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
      restrictMask r a = twoMask (a (r 0)) (a (r 1)) := by
    funext i j
    have hi : i = 0 ∨ i = 1 := by
      have hiv : i.val ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hiv with hi | hi
      · left
        apply Fin.ext
        simpa using hi
      · right
        apply Fin.ext
        simpa using hi
    rcases hi with rfl | rfl <;> rfl
  have heq : supportRowsEqual a ↔ a (r 0) = a (r 1) := by
    constructor
    · intro h
      exact h (r 0) (hr_mem 0) (r 1) (hr_mem 1)
    · intro h i hi j hj
      let is : S := ⟨i, by simpa [S] using hi⟩
      let js : S := ⟨j, by simpa [S] using hj⟩
      let ti : Fin 2 := e.symm is
      let tj : Fin 2 := e.symm js
      have hir : r ti = i := by
        change (e (e.symm is)).1 = i
        simp [is]
      have hjr : r tj = j := by
        change (e (e.symm js)).1 = j
        simp [js]
      rw [← hir, ← hjr]
      have finTwoCases (t : Fin 2) : t = 0 ∨ t = 1 := by
        have htv : t.val ≤ 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp htv with ht | ht
        · left
          apply Fin.ext
          simpa using ht
        · right
          apply Fin.ext
          simpa using ht
      rcases finTwoCases ti with hti | hti <;>
        rcases finTwoCases tj with htj | htj <;>
          simp [hti, htj, h]
  rw [fourier_injectionDensity_eq_restrictMask hq r a hout, hmask]
  rw [fourier_injectionDensity_twoMask (a (r 0)) (a (r 1)) (hr_ne 0) (hr_ne 1)]
  by_cases h : supportRowsEqual a
  · rw [if_pos h, if_pos (heq.mp h)]
  · have hne : a (r 0) ≠ a (r 1) := fun hr => h (heq.mpr hr)
    rw [if_neg h, if_neg hne]

/-- The convolution summand is constant exactly on a compatible hidden
state. -/
private theorem injectionDensity_mul_shift (n q : Nat)
    (y x : BitMatrix q n) :
    injectionDensity n q x * injectionDensity n q (y + x) =
      if CompatibleHiddenState y x then
        ((((2 ^ n : Nat) : Real) ^ q /
          (((2 ^ n).descFactorial q : Nat) : Real)) ^ 2)
      else 0 := by
  unfold injectionDensity CompatibleHiddenState shifted
  have hshift : (fun i => x i + y i) = y + x := by
    funext i j
    simp [add_comm]
  rw [hshift]
  by_cases hx : Function.Injective x <;>
    by_cases hshiftx : Function.Injective (y + x) <;>
      simp [hx, hshiftx] <;> ring

/-- Exact card-count form of the two-injection convolution. -/
theorem convolution_injectionDensity_eq_compatibleDensity
    {n q : Nat} (hq : q <= 2 ^ n) (y : BitMatrix q n) :
    convolution (injectionDensity n q) (injectionDensity n q) y =
      compatibleDensity n q y := by
  let N : Nat := 2 ^ n
  let D : Nat := N.descFactorial q
  have hDR : (D : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by simpa [N] using hq)).ne'
  unfold convolution
  rw [show
      (fun x : BitMatrix q n =>
        injectionDensity n q x * injectionDensity n q (y + x)) =
      (fun x => if CompatibleHiddenState y x then
        (((N : Real) ^ q / (D : Real)) ^ 2) else 0) by
      funext x
      simpa [N, D] using injectionDensity_mul_shift n q y x]
  unfold average compatibleDensity
  rw [show
      (∑ x : BitMatrix q n,
        if CompatibleHiddenState y x then
          (((N : Real) ^ q / (D : Real)) ^ 2) else 0) =
      (compatibleCountNat y : Real) *
        (((N : Real) ^ q / (D : Real)) ^ 2) by
      unfold compatibleCountNat
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]]
  rw [card_bitMatrix]
  change
    (compatibleCountNat y : Real) *
          (((N : Real) ^ q / (D : Real)) ^ 2) /
        (((N ^ q : Nat) : Real)) =
      (compatibleCountNat y : Real) * (N : Real) ^ q / (D : Real) ^ 2
  norm_num [Nat.cast_pow]
  field_simp [hDR]

/-- The compatible-density expression is the repository's exact visible SoP
likelihood ratio. -/
theorem compatibleDensity_eq_visibleDensityRatioReal
    {n q : Nat} (hq : q <= 2 ^ n) (y : BitMatrix q n) :
    compatibleDensity n q y =
      visibleDensityRatioReal (G := XorSpace n) (q := q) y := by
  let N : Nat := 2 ^ n
  let D : Nat := N.descFactorial q
  have hDR : (D : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by simpa [N] using hq)).ne'
  rw [visibleDensityRatioReal_eq]
  unfold compatibleDensity visibleNormalizerNNReal
  rw [compatibleCountNNReal_eq_coe_nat]
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  simp only [card_xorSpace]
  change
    (compatibleCountNat y : Real) * (N : Real) ^ q / (D : Real) ^ 2 =
      (compatibleCountNat y : Real) /
        (((D * D : Nat) : Real) / (((N ^ q : Nat) : Real)))
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hDR]

/-- Pointwise representative identity: SoP likelihood equals the
self-convolution of the uniform-injection likelihood. -/
theorem visibleDensityRatioReal_eq_convolution_injectionDensity
    {n q : Nat} (hq : q <= 2 ^ n) (y : BitMatrix q n) :
    visibleDensityRatioReal (G := XorSpace n) (q := q) y =
      convolution (injectionDensity n q) (injectionDensity n q) y := by
  rw [convolution_injectionDensity_eq_compatibleDensity hq]
  exact (compatibleDensity_eq_visibleDensityRatioReal hq y).symm

/-- The constant Walsh coefficient of `mu` is one. -/
theorem fourier_injectionDensity_zero {n q : Nat} (hq : q <= 2 ^ n) :
    XORFourier.fourier (injectionDensity n q) 0 = 1 := by
  unfold XORFourier.fourier
  simpa using average_injectionDensity_eq_one hq

/-! ## The level-two spectrum is the collision kernel -/

open RandomSystems.Applications.SoP
open RandomSystems.SoP.CollisionProxy

/-- The checkerboard carried by one unordered query pair and one nonzero
one-word mask. -/
def pairMask {n q : Nat} (p : PairIndex q) (alpha : XorSpace n) :
    BitMatrix q n :=
  fun i => if i = p.1.1 then alpha else if i = p.1.2 then alpha else 0

@[simp]
theorem pairMask_left {n q : Nat} (p : PairIndex q) (alpha : XorSpace n) :
    pairMask p alpha p.1.1 = alpha := by
  simp [pairMask]

@[simp]
theorem pairMask_right {n q : Nat} (p : PairIndex q) (alpha : XorSpace n) :
    pairMask p alpha p.1.2 = alpha := by
  simp [pairMask, ne_of_gt p.2]

@[simp]
theorem rowSupport_pairMask {n q : Nat} (p : PairIndex q)
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    rowSupport (pairMask p alpha) = {p.1.1, p.1.2} := by
  ext i
  simp only [mem_rowSupport, Finset.mem_insert, Finset.mem_singleton]
  unfold pairMask
  by_cases hil : i = p.1.1
  · simp [hil, halpha]
  · by_cases hir : i = p.1.2
    · simp [hil, hir, halpha]
    · simp [hil, hir]

@[simp]
theorem level_pairMask {n q : Nat} (p : PairIndex q)
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    level (pairMask p alpha) = 2 := by
  rw [level, rowSupport_pairMask p alpha halpha]
  simp [ne_of_lt p.2]

theorem supportRowsEqual_pairMask {n q : Nat} (p : PairIndex q)
    (alpha : XorSpace n) : supportRowsEqual (pairMask p alpha) := by
  intro i hi j hj
  simp only [mem_rowSupport] at hi hj
  unfold pairMask at hi hj ⊢
  by_cases hil : i = p.1.1 <;> by_cases hir : i = p.1.2 <;>
    by_cases hjl : j = p.1.1 <;> by_cases hjr : j = p.1.2 <;>
      simp [hil, hir, hjl, hjr] at hi hj ⊢

/-- A pair mask evaluates as the character of the XOR difference between its
two endpoint words. -/
theorem walsh_pairMask {n q : Nat} (p : PairIndex q)
    (alpha : XorSpace n) (y : BitMatrix q n) :
    walsh (pairMask p alpha) y =
      vectorWalsh alpha (y p.1.1 + y p.1.2) := by
  have hlr : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hrow (i : Fin q) :
      (∑ j : Fin n, pairMask p alpha i j * y i j) =
        if i = p.1.1 then vectorDot alpha (y i)
        else if i = p.1.2 then vectorDot alpha (y i) else 0 := by
    by_cases hil : i = p.1.1 <;> by_cases hir : i = p.1.2 <;>
      simp [pairMask, vectorDot, hil, hir]
  unfold walsh dot
  rw [show
      (∑ i : Fin q, ∑ j : Fin n, pairMask p alpha i j * y i j) =
        vectorDot alpha (y p.1.1) + vectorDot alpha (y p.1.2) by
    simp_rw [hrow]
    rw [show
        (∑ i : Fin q, if i = p.1.1 then vectorDot alpha (y i)
          else if i = p.1.2 then vectorDot alpha (y i) else 0) =
        (∑ i : Fin q, if i = p.1.1 then vectorDot alpha (y i) else 0) +
        (∑ i : Fin q, if i = p.1.2 then vectorDot alpha (y i) else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hil : i = p.1.1 <;> by_cases hir : i = p.1.2 <;>
        simp [hil, hir, hlr, hlr.symm]]
    simp]
  simp [vectorWalsh, vectorDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem vectorDot_comm {n : Nat} (a x : XorSpace n) :
    vectorDot a x = vectorDot x a := by
  unfold vectorDot
  apply Finset.sum_congr rfl
  intro j _hj
  exact mul_comm _ _

theorem vectorWalsh_comm {n : Nat} (a x : XorSpace n) :
    vectorWalsh a x = vectorWalsh x a := by
  simp only [vectorWalsh, vectorDot_comm]

/-- Character orthogonality with the summation variable in the mask slot. -/
theorem sum_vectorWalsh_dual {n : Nat} (x : XorSpace n) :
    (∑ a : XorSpace n, vectorWalsh a x) =
      if x = 0 then (2 ^ n : Nat) else 0 := by
  simpa only [vectorWalsh_comm] using sum_vectorWalsh x

/-- Removing the trivial character leaves `N-1` on zero and `-1` elsewhere. -/
theorem sum_nonzero_vectorWalsh {n : Nat} (x : XorSpace n) :
    (∑ a ∈ (Finset.univ : Finset (XorSpace n)).filter (fun a => a ≠ 0),
        vectorWalsh a x) =
      if x = 0 then ((2 ^ n - 1 : Nat) : Real) else -1 := by
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (XorSpace n)))
    (f := fun a => vectorWalsh a x) (Finset.mem_univ (0 : XorSpace n))
  have hfilter :
      (Finset.univ : Finset (XorSpace n)).filter (fun a => a ≠ 0) =
        Finset.univ.erase 0 := by
    ext a
    simp [ne_comm]
  rw [hfilter]
  change
    (∑ a ∈ Finset.univ.erase (0 : XorSpace n), vectorWalsh a x) +
        vectorWalsh 0 x =
      ∑ a : XorSpace n, vectorWalsh a x at hsplit
  rw [vectorWalsh_zero_left] at hsplit
  calc
    (∑ a ∈ Finset.univ.erase (0 : XorSpace n), vectorWalsh a x) =
        (∑ a : XorSpace n, vectorWalsh a x) - 1 := by linarith
    _ = if x = 0 then ((2 ^ n - 1 : Nat) : Real) else -1 := by
      rw [sum_vectorWalsh_dual]
      by_cases hx : x = 0
      · simp only [hx, if_pos]
        have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        rw [Nat.cast_sub hpow]
        norm_num [Nat.cast_pow]
      · simp only [hx, if_neg]
        norm_num

/-- Increasing query pairs are determined by their unordered endpoint set. -/
theorem pairIndex_eq_of_endpointSet_eq {q : Nat} (p r : PairIndex q)
    (hset : ({p.1.1, p.1.2} : Finset (Fin q)) = {r.1.1, r.1.2}) :
    p = r := by
  have hp_left_mem : p.1.1 ∈ ({r.1.1, r.1.2} : Finset (Fin q)) := by
    rw [← hset]
    simp
  have hp_right_mem : p.1.2 ∈ ({r.1.1, r.1.2} : Finset (Fin q)) := by
    rw [← hset]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp_left_mem hp_right_mem
  rcases hp_left_mem with hll | hlr
  · rcases hp_right_mem with hrl | hrr
    · exfalso
      exact (ne_of_lt p.2) (hll.trans hrl.symm)
    · apply Subtype.ext
      exact Prod.ext hll hrr
  · rcases hp_right_mem with hrl | hrr
    · exfalso
      have hbad : r.1.2 < r.1.1 := by
        calc
          r.1.2 = p.1.1 := hlr.symm
          _ < p.1.2 := p.2
          _ = r.1.1 := hrl
      exact (not_lt_of_ge (le_of_lt r.2)) hbad
    · exfalso
      exact (ne_of_lt p.2) (hlr.trans hrr.symm)

/-- Parameters for the nonzero equal-row checkerboards at level two. -/
abbrev PairMaskParameter (n q : Nat) :=
  PairIndex q × {alpha : XorSpace n // alpha ≠ 0}

/-- The level-two masks whose two nonzero rows carry the same word mask. -/
abbrev EqualLevelTwoMask (n q : Nat) :=
  {a : BitMatrix q n // level a = 2 ∧ supportRowsEqual a}

/-- Construct an equal-row level-two mask from its pair and word mask. -/
def pairMaskParameterToMask {n q : Nat} (z : PairMaskParameter n q) :
    EqualLevelTwoMask n q :=
  ⟨pairMask z.1 z.2.1,
    level_pairMask z.1 z.2.1 z.2.2, supportRowsEqual_pairMask z.1 z.2.1⟩

/-- The pair-mask parametrization is injective. -/
theorem pairMaskParameterToMask_injective {n q : Nat} :
    Function.Injective
      (pairMaskParameterToMask : PairMaskParameter n q -> EqualLevelTwoMask n q) := by
  rintro ⟨p, alpha⟩ ⟨r, beta⟩ h
  have hmask : pairMask p alpha.1 = pairMask r beta.1 :=
    congrArg Subtype.val h
  have hsupport := congrArg rowSupport hmask
  rw [rowSupport_pairMask p alpha.1 alpha.2,
    rowSupport_pairMask r beta.1 beta.2] at hsupport
  have hpr : p = r := pairIndex_eq_of_endpointSet_eq p r hsupport
  subst r
  have hab : alpha.1 = beta.1 := by
    have happ := congrFun hmask p.1.1
    simpa using happ
  have habSub : alpha = beta := Subtype.ext hab
  subst beta
  rfl

/-- Every equal-row level-two mask has a pair-mask representation. -/
theorem pairMaskParameterToMask_surjective {n q : Nat} :
    Function.Surjective
      (pairMaskParameterToMask : PairMaskParameter n q -> EqualLevelTwoMask n q) := by
  intro a
  let S : Finset (Fin q) := rowSupport a.1
  have hScard : S.card = 2 := by
    simpa [S, level] using a.2.1
  have hFcard : Fintype.card S = 2 := by simpa using hScard
  let e : Fin 2 ≃ S :=
    (finCongr hFcard).symm.trans (Fintype.equivFin S).symm
  let i : Fin q := (e 0).1
  let j : Fin q := (e 1).1
  have hi : i ∈ rowSupport a.1 := by
    exact (e 0).2
  have hj : j ∈ rowSupport a.1 := by
    exact (e 1).2
  have hij : i ≠ j := by
    intro hij
    apply Fin.zero_ne_one
    apply e.injective
    apply Subtype.ext
    exact hij
  have hS : rowSupport a.1 = {i, j} := by
    ext t
    constructor
    · intro ht
      let ts : S := ⟨t, by simpa [S] using ht⟩
      have htCases : e.symm ts = 0 ∨ e.symm ts = 1 := by
        have hval : (e.symm ts).val ≤ 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hval with hzero | hone
        · left
          apply Fin.ext
          simpa using hzero
        · right
          apply Fin.ext
          simpa using hone
      rcases htCases with ht0 | ht1
      · have : t = i := by
          change ts.1 = (e 0).1
          rw [← ht0]
          simp [ts]
        simp [this]
      · have : t = j := by
          change ts.1 = (e 1).1
          rw [← ht1]
          simp [ts]
        simp [this]
    · intro ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hi
      · exact hj
  let p : PairIndex q := pairIndexOfNe i j hij
  have hpEnds : ({p.1.1, p.1.2} : Finset (Fin q)) = {i, j} := by
    simpa [p] using pairIndexOfNe_endpointSet hij
  have halpha : a.1 i ≠ 0 := (mem_rowSupport a.1 i).mp hi
  let z : PairMaskParameter n q := ⟨p, ⟨a.1 i, halpha⟩⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change pairMask p (a.1 i) = a.1
  funext t
  by_cases ht : t ∈ rowSupport a.1
  · have htPair : t ∈ ({p.1.1, p.1.2} : Finset (Fin q)) := by
      rw [hpEnds, ← hS]
      exact ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at htPair
    rcases htPair with htl | htr
    · subst t
      rw [pairMask_left]
      exact a.2.2 i hi p.1.1 (by
        rw [hS, ← hpEnds]
        simp)
    · subst t
      rw [pairMask_right]
      exact a.2.2 i hi p.1.2 (by
        rw [hS, ← hpEnds]
        simp)
  · have hzero : a.1 t = 0 := by
      simpa using ht
    have htNotPair :
        t ≠ p.1.1 ∧ t ≠ p.1.2 := by
      constructor <;> intro heq <;> apply ht
      · rw [hS, ← hpEnds]
        simp [heq]
      · rw [hS, ← hpEnds]
        simp [heq]
    simp [pairMask, htNotPair.1, htNotPair.2, hzero]

/-- Equal-row level-two masks are canonically a query pair together with one
nonzero XOR character. -/
noncomputable def pairMaskParameterEquiv (n q : Nat) :
    PairMaskParameter n q ≃ EqualLevelTwoMask n q :=
  Equiv.ofBijective pairMaskParameterToMask
    ⟨pairMaskParameterToMask_injective,
      pairMaskParameterToMask_surjective⟩

/-- The complete level-two part of the self-convolution, reindexed by query
pairs and nonzero one-word characters. -/
theorem levelTwoSpectrum_eq_pairMaskSum {n q : Nat} (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) :
    spectralPart (fun a : BitMatrix q n => level a = 2)
        (convolution (injectionDensity n q) (injectionDensity n q)) y =
      ∑ p : PairIndex q,
        ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
            (fun alpha => alpha ≠ 0),
          (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
            walsh (pairMask p alpha) y := by
  let c : Real := 1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)
  calc
    spectralPart (fun a : BitMatrix q n => level a = 2)
        (convolution (injectionDensity n q) (injectionDensity n q)) y =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun a => level a = 2 ∧ supportRowsEqual a),
        c * walsh a y := by
      unfold spectralPart
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hlevel : level a = 2
      · rw [if_pos hlevel]
        rw [fourier_convolution]
        rw [fourier_injectionDensity_of_level_eq_two hq a hlevel]
        by_cases hequal : supportRowsEqual a
        · simp only [hequal, if_pos, hlevel, and_self]
          dsimp [c]
          simp only [one_div]
          rw [← inv_pow]
          ring
        · simp [hlevel, hequal]
      · simp [hlevel]
    _ = ∑ a : EqualLevelTwoMask n q, c * walsh a.1 y := by
      rw [Finset.sum_subtype]
      intro a
      simp
    _ = ∑ z : PairMaskParameter n q,
        c * walsh (pairMask z.1 z.2.1) y := by
      symm
      exact Fintype.sum_equiv (pairMaskParameterEquiv n q)
        (fun z : PairMaskParameter n q =>
          c * walsh (pairMask z.1 z.2.1) y)
        (fun a : EqualLevelTwoMask n q => c * walsh a.1 y)
        (fun _z => rfl)
    _ = ∑ p : PairIndex q, ∑ alpha : {alpha : XorSpace n // alpha ≠ 0},
        c * walsh (pairMask p alpha.1) y := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p : PairIndex q,
        ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
            (fun alpha => alpha ≠ 0),
          c * walsh (pairMask p alpha) y := by
      apply Finset.sum_congr rfl
      intro p _hp
      symm
      rw [Finset.sum_subtype]
      intro alpha
      simp
    _ = _ := by rfl

/-- The character sum carried by one query pair is the centered collision
indicator for that pair. -/
theorem sum_pairMask_walsh {n q : Nat} (p : PairIndex q)
    (y : BitMatrix q n) :
    (∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
        (fun alpha => alpha ≠ 0), walsh (pairMask p alpha) y) =
      if y p.1.2 = y p.1.1 then ((2 ^ n - 1 : Nat) : Real) else -1 := by
  simp_rw [walsh_pairMask]
  rw [sum_nonzero_vectorWalsh]
  have hzero : y p.1.1 + y p.1.2 = 0 ↔ y p.1.2 = y p.1.1 := by
    rw [xorVector_add_eq_zero_iff_eq]
    exact eq_comm
  by_cases hcollision : y p.1.2 = y p.1.1
  · rw [if_pos hcollision, if_pos (hzero.mpr hcollision)]
  · rw [if_neg hcollision, if_neg (fun h => hcollision (hzero.mp h))]

/-- The exact degree-two Walsh component of the SoP likelihood ratio is the
centered pair-collision kernel.  No approximation or triangle inequality is
used here. -/
theorem levelTwoSpectrum_eq_collisionKernel {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    spectralPart (fun a : BitMatrix q n => level a = 2)
        (convolution (injectionDensity n q) (injectionDensity n q)) y =
      collisionKernel (XorSpace n) q y := by
  let N : Nat := 2 ^ n
  let D : Real := ((N - 1 : Nat) : Real)
  have hNpos : 0 < N := by omega
  have hNreal : (N : Real) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hDnat : N - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (by omega)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast hDnat
  rw [levelTwoSpectrum_eq_pairMaskSum hq]
  simp_rw [← Finset.mul_sum, sum_pairMask_walsh]
  have hcastD : D = (N : Real) - 1 := by
    dsimp [D]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hterm (p : PairIndex q) :
      (if y p.1.2 = y p.1.1 then D else -1) =
        (N : Real) * (if y p.1.2 = y p.1.1 then 1 else 0) - 1 := by
    by_cases hp : y p.1.2 = y p.1.1
    · simp [hp, hcastD]
    · simp [hp]
  change
    (1 / D ^ 2) *
      ∑ p : PairIndex q,
        (if y p.1.2 = y p.1.1 then D else -1) = _
  simp_rw [hterm]
  have hcollision :
      (∑ p : PairIndex q,
        (if y p.1.2 = y p.1.1 then 1 else 0 : Real)) =
        collisionCount q y := by
    change
      (∑ p : PairIndex q,
        (if y p.1.2 = y p.1.1 then 1 else 0 : Real)) =
        pairCollisionCountReal (XorSpace n) q y
    rw [pairCollisionCountReal_eq_pairCollisionCountNat]
    unfold pairCollisionCountNat
    norm_cast
  rw [show
      (∑ p : PairIndex q,
        ((N : Real) * (if y p.1.2 = y p.1.1 then 1 else 0) - 1)) =
        (N : Real) * collisionCount q y - (pairCount q : Real) by
    calc
      (∑ p : PairIndex q,
        ((N : Real) * (if y p.1.2 = y p.1.1 then 1 else 0) - 1)) =
          (N : Real) *
              (∑ p : PairIndex q,
                (if y p.1.2 = y p.1.1 then 1 else 0 : Real)) -
            ∑ _p : PairIndex q, (1 : Real) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (N : Real) * collisionCount q y - (pairCount q : Real) := by
        rw [hcollision]
        simp [pairCount]]
  unfold collisionKernel centeredCollisionCount collisionMean
  simp only [card_xorSpace]
  change
    (1 / D ^ 2) * ((N : Real) * collisionCount q y - pairCount q) =
      (N : Real) / D ^ 2 *
        (collisionCount q y - (pairCount q : Real) / (N : Real))
  field_simp [hNreal, hD]

/-! ## Removing levels zero and one -/

/-- A one-row mask. -/
def oneMask {n : Nat} (alpha : XorSpace n) : BitMatrix 1 n := ![alpha]

@[simp]
theorem walsh_oneMask {n : Nat} (alpha : XorSpace n) (x : BitMatrix 1 n) :
    walsh (oneMask alpha) x = vectorWalsh alpha (x 0) := by
  simp [walsh, dot, oneMask, vectorWalsh, vectorDot]

/-- A one-point ordered injection is just its selected point. -/
def embeddingOneEquiv (G : Type*) : (Fin 1 ↪ G) ≃ G where
  toFun e := e 0
  invFun x :=
    ⟨![x], by
      intro i j _h
      fin_cases i
      fin_cases j
      rfl⟩
  left_inv e := by
    ext i
    fin_cases i
    rfl
  right_inv _x := rfl

/-- A nontrivial one-row checkerboard has zero expectation under a uniform
one-point injection. -/
theorem fourier_injectionDensity_oneMask {n : Nat} (alpha : XorSpace n)
    (halpha : alpha ≠ 0) :
    XORFourier.fourier (injectionDensity n 1) (oneMask alpha) = 0 := by
  have hN : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  rw [fourier_injectionDensity_eq_average_embedding hN]
  unfold average
  rw [show
      (∑ e : Fin 1 ↪ XorSpace n, walsh (oneMask alpha) e) =
        ∑ x : XorSpace n, vectorWalsh alpha x by
      exact Fintype.sum_equiv (embeddingOneEquiv (XorSpace n))
        (fun e : Fin 1 ↪ XorSpace n => walsh (oneMask alpha) e)
        (fun x : XorSpace n => vectorWalsh alpha x)
        (fun e => walsh_oneMask alpha e)]
  rw [sum_vectorWalsh, if_neg halpha]
  simp

/-- Every level-one injection coefficient vanishes. -/
theorem fourier_injectionDensity_of_level_eq_one
    {n q : Nat} (hq : q ≤ 2 ^ n) (a : BitMatrix q n)
    (haLevel : level a = 1) :
    XORFourier.fourier (injectionDensity n q) a = 0 := by
  have hcard : (rowSupport a).card = 1 := by
    simpa [level] using haLevel
  obtain ⟨i, hiSupport⟩ := Finset.card_eq_one.mp hcard
  have hi : i ∈ rowSupport a := by simp [hiSupport]
  have hai : a i ≠ 0 := (mem_rowSupport a i).mp hi
  let r : Fin 1 ↪ Fin q :=
    ⟨![i], by
      intro u v _h
      fin_cases u
      fin_cases v
      rfl⟩
  have hrange : Set.range r = {i} := by
    ext t
    constructor
    · rintro ⟨u, rfl⟩
      fin_cases u
      simp [r]
    · intro ht
      have ht' : t = i := by simpa using ht
      subst t
      exact ⟨0, by simp [r]⟩
  have hout : ∀ t, t ∉ Set.range r -> a t = 0 := by
    intro t ht
    have htSupport : t ∉ rowSupport a := by
      rw [hiSupport]
      simpa [hrange] using ht
    simpa using htSupport
  have hrestrict : restrictMask r a = oneMask (a i) := by
    funext u j
    fin_cases u
    rfl
  rw [fourier_injectionDensity_eq_restrictMask hq r a hout]
  rw [hrestrict]
  exact fourier_injectionDensity_oneMask (a i) hai

/-- The level-zero piece of the self-convolution is the constant density
one. -/
theorem levelZeroSpectrum_eq_one {n q : Nat} (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) :
    spectralPart (fun a : BitMatrix q n => level a = 0)
        (convolution (injectionDensity n q) (injectionDensity n q)) y = 1 := by
  unfold spectralPart
  rw [Finset.sum_filter]
  simp_rw [level_eq_zero_iff]
  rw [Finset.sum_ite_eq' Finset.univ 0]
  simp [fourier_convolution, fourier_injectionDensity_zero hq]

/-- The level-one piece of the self-convolution vanishes. -/
theorem levelOneSpectrum_eq_zero {n q : Nat} (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) :
    spectralPart (fun a : BitMatrix q n => level a = 1)
        (convolution (injectionDensity n q) (injectionDensity n q)) y = 0 := by
  unfold spectralPart
  apply Finset.sum_eq_zero
  intro a ha
  have hlevel : level a = 1 := by simpa using ha
  rw [fourier_convolution]
  rw [fourier_injectionDensity_of_level_eq_one hq a hlevel]
  simp

/-- Fourier inversion split into the only four possible level ranges needed
by the collision-proxy proof. -/
theorem spectralPartition_zero_one_two_geThree {n q : Nat}
    (f : BitMatrix q n -> Real) (y : BitMatrix q n) :
    spectralPart (fun a => level a = 0) f y +
        spectralPart (fun a => level a = 1) f y +
        spectralPart (fun a => level a = 2) f y +
        levelGePart 3 f y = f y := by
  rw [← fourier_inversion f y]
  unfold levelGePart
  unfold spectralPart
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h0 : level a = 0
  · simp [h0]
  · by_cases h1 : level a = 1
    · simp [h0, h1]
    · by_cases h2 : level a = 2
      · simp [h0, h1, h2]
      · have h3 : 3 ≤ level a := by omega
        simp [h0, h1, h2, h3]

/-- Exact broken-cycle decomposition: after subtracting the constant density
and the collision proxy, precisely the level-three-and-higher Walsh modes
remain. -/
theorem remainderDensity_eq_levelGePart {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    remainderDensity (G := XorSpace n) q y =
      levelGePart 3
        (convolution (injectionDensity n q) (injectionDensity n q)) y := by
  have hpartition := spectralPartition_zero_one_two_geThree
    (convolution (injectionDensity n q) (injectionDensity n q)) y
  rw [levelZeroSpectrum_eq_one hq y, levelOneSpectrum_eq_zero hq y,
    levelTwoSpectrum_eq_collisionKernel hN hq y] at hpartition
  rw [remainderDensity, proxyDensity,
    visibleDensityRatioReal_eq_convolution_injectionDensity hq]
  linarith

/-- Exact `L2` identity for the broken-cycle remainder.  Bounding the right
side is now a coefficient-energy problem, not a loss from the representative
or from conditioning. -/
theorem average_remainderDensity_sq_eq_fourierTail {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) :
    average (BitMatrix q n)
        (fun y => (remainderDensity (G := XorSpace n) q y) ^ 2) =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun a => 3 ≤ level a),
        (XORFourier.fourier (injectionDensity n q) a) ^ 4 := by
  rw [show
      (fun y => (remainderDensity (G := XorSpace n) q y) ^ 2) =
        (fun y =>
          (levelGePart 3
            (convolution (injectionDensity n q) (injectionDensity n q)) y) ^ 2) by
      funext y
      rw [remainderDensity_eq_levelGePart hN hq y]]
  unfold levelGePart
  rw [parseval_selected_convolution_sq]
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _ha
    rfl

end RandomSystems.SoP.XORInjection
