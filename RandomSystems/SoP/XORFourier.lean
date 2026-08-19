/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Data.ZMod.Basic

/-!
# A finite real Walsh transform for XOR tapes

This is the constrained spectral layer used by the collision-proxy proof.  It
is deliberately specialized to matrices of bits.  The public gain-graph
generalization is not routed through this file.

All normalizations are probability normalizations:

* `average f = (1 / |X|) * sum_x f x`;
* `fourier f a = average_x (f x * walsh a x)`;
* `convolution f g y = average_x (f x * g (y + x))`.

With these conventions Fourier inversion has no outer factor, Parseval has no
factor on the coefficient sum, and convolution turns into pointwise
multiplication.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- A `q` by `n` matrix of bits.  Depending on use it is a visible XOR tape
or a Walsh mask. -/
abbrev BitMatrix (q n : Nat) := Fin q -> Fin n -> ZMod 2

/-- Uniform finite average of a real-valued function. -/
def average (A : Type*) [Fintype A] (f : A -> Real) : Real :=
  (∑ x : A, f x) / (Fintype.card A : Real)

@[simp]
theorem average_const {A : Type*} [Fintype A] [Nonempty A] (c : Real) :
    average A (fun _x => c) = c := by
  unfold average
  have hcard : (Fintype.card A : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  simp [Finset.sum_const, nsmul_eq_mul, hcard]

theorem average_add {A : Type*} [Fintype A] (f g : A -> Real) :
    average A (fun x => f x + g x) = average A f + average A g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_const_mul {A : Type*} [Fintype A]
    (c : Real) (f : A -> Real) :
    average A (fun x => c * f x) = c * average A f := by
  unfold average
  rw [← Finset.mul_sum, mul_div_assoc]

theorem average_mul_const {A : Type*} [Fintype A]
    (f : A -> Real) (c : Real) :
    average A (fun x => f x * c) = average A f * c := by
  unfold average
  rw [← Finset.sum_mul]
  ring

theorem average_fintype_sum {A B : Type*} [Fintype A] [Fintype B]
    (f : B -> A -> Real) :
    average A (fun x => ∑ b : B, f b x) =
      ∑ b : B, average A (f b) := by
  unfold average
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]

theorem average_finset_sum {A B : Type*} [Fintype A]
    (s : Finset B) (f : B -> A -> Real) :
    average A (fun x => ∑ b ∈ s, f b x) =
      ∑ b ∈ s, average A (f b) := by
  unfold average
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]

/-- Uniform averaging is invariant under a permutation of the carrier. -/
theorem average_comp_equiv {A : Type*} [Fintype A]
    (e : A ≃ A) (f : A -> Real) :
    average A (fun x => f (e x)) = average A f := by
  unfold average
  rw [Equiv.sum_comp e]

/-- Finite Fubini theorem for two uniform averages. -/
theorem average_average_comm {A B : Type*} [Fintype A] [Fintype B]
    (f : A -> B -> Real) :
    average A (fun a => average B (fun b => f a b)) =
      average B (fun b => average A (fun a => f a b)) := by
  unfold average
  simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- The real sign attached to one parity bit. -/
def bitSign (z : ZMod 2) : Real := if z = 0 then 1 else -1

@[simp]
theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]

@[simp]
theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

/-- The sole nonzero bit is `1`. -/
theorem zmodTwo_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective
  have hxv : x.val ≠ 0 := by
    intro hxv
    apply hx
    apply ZMod.val_injective
    simpa using hxv
  have hlt := x.val_lt
  norm_num [ZMod.val_one] at ⊢
  omega

theorem bitSign_injective : Function.Injective bitSign := by
  intro x y h
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · exact hy.symm
    · norm_num [bitSign, hy] at h
  · by_cases hy : y = 0
    · subst y
      norm_num [bitSign, hx] at h
    · rw [zmodTwo_eq_one_of_ne_zero x hx,
        zmodTwo_eq_one_of_ne_zero y hy]

@[simp]
theorem bitSign_add (x y : ZMod 2) :
    bitSign (x + y) = bitSign x * bitSign y := by
  by_cases hx : x = 0
  · subst x
    simp [bitSign]
  · by_cases hy : y = 0
    · subst y
      simp [bitSign]
    · rw [zmodTwo_eq_one_of_ne_zero x hx,
        zmodTwo_eq_one_of_ne_zero y hy]
      have htwo : (1 + 1 : ZMod 2) = 0 := by decide
      simp [bitSign, htwo]

@[simp]
theorem bitSign_mul_self (x : ZMod 2) : bitSign x * bitSign x = 1 := by
  by_cases hx : x = 0
  · simp [bitSign, hx]
  · rw [zmodTwo_eq_one_of_ne_zero x hx]
    norm_num [bitSign]

@[simp]
theorem abs_bitSign (x : ZMod 2) : |bitSign x| = 1 := by
  by_cases hx : x = 0
  · simp [bitSign, hx]
  · rw [zmodTwo_eq_one_of_ne_zero x hx]
    norm_num [bitSign]

/-- Bilinear parity pairing of a mask and a tape. -/
def dot {q n : Nat} (a x : BitMatrix q n) : ZMod 2 :=
  ∑ i : Fin q, ∑ j : Fin n, a i j * x i j

@[simp]
theorem dot_zero_left {q n : Nat} (x : BitMatrix q n) : dot 0 x = 0 := by
  simp [dot]

@[simp]
theorem dot_zero_right {q n : Nat} (a : BitMatrix q n) : dot a 0 = 0 := by
  simp [dot]

theorem dot_add_left {q n : Nat} (a b x : BitMatrix q n) :
    dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {q n : Nat} (a x y : BitMatrix q n) :
    dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_comm {q n : Nat} (a x : BitMatrix q n) : dot a x = dot x a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  exact mul_comm _ _

/-- Real Walsh checkerboard indexed by a bit mask. -/
def walsh {q n : Nat} (a x : BitMatrix q n) : Real := bitSign (dot a x)

@[simp]
theorem walsh_zero_left {q n : Nat} (x : BitMatrix q n) : walsh 0 x = 1 := by
  simp [walsh]

@[simp]
theorem walsh_zero_right {q n : Nat} (a : BitMatrix q n) : walsh a 0 = 1 := by
  simp [walsh]

@[simp]
theorem walsh_add_left {q n : Nat} (a b x : BitMatrix q n) :
    walsh (a + b) x = walsh a x * walsh b x := by
  simp [walsh, dot_add_left]

@[simp]
theorem walsh_add_right {q n : Nat} (a x y : BitMatrix q n) :
    walsh a (x + y) = walsh a x * walsh a y := by
  simp [walsh, dot_add_right]

theorem walsh_comm {q n : Nat} (a x : BitMatrix q n) : walsh a x = walsh x a := by
  simp [walsh, dot_comm]

@[simp]
theorem walsh_mul_self {q n : Nat} (a x : BitMatrix q n) :
    walsh a x * walsh a x = 1 := by
  simp [walsh]

@[simp]
theorem abs_walsh {q n : Nat} (a x : BitMatrix q n) : |walsh a x| = 1 := by
  simp [walsh]

/-- Matrix supported on one bit. -/
def singleBit {q n : Nat} (i : Fin q) (j : Fin n) : BitMatrix q n :=
  fun i' j' => if i' = i then if j' = j then 1 else 0 else 0

@[simp]
theorem dot_singleBit {q n : Nat} (a : BitMatrix q n) (i : Fin q) (j : Fin n) :
    dot a (singleBit i j) = a i j := by
  simp [dot, singleBit]

@[simp]
theorem walsh_singleBit {q n : Nat} (a : BitMatrix q n) (i : Fin q) (j : Fin n) :
    walsh a (singleBit i j) = bitSign (a i j) := by
  simp [walsh]

/-- Walsh masks embed into real additive characters. -/
def walshChar {q n : Nat} (a : BitMatrix q n) : AddChar (BitMatrix q n) Real where
  toFun := walsh a
  map_zero_eq_one' := walsh_zero_right a
  map_add_eq_mul' := walsh_add_right a

@[simp]
theorem walshChar_apply {q n : Nat} (a x : BitMatrix q n) :
    walshChar a x = walsh a x := rfl

@[simp]
theorem walshChar_zero {q n : Nat} : walshChar (0 : BitMatrix q n) = 0 := by
  ext x
  simp [walshChar]

theorem walshChar_injective {q n : Nat} :
    Function.Injective (walshChar : BitMatrix q n -> AddChar (BitMatrix q n) Real) := by
  intro a b h
  funext i j
  apply bitSign_injective
  simpa using DFunLike.congr_fun h (singleBit i j)

@[simp]
theorem walshChar_eq_zero_iff {q n : Nat} (a : BitMatrix q n) :
    walshChar a = 0 ↔ a = 0 := by
  rw [← walshChar_zero]
  exact walshChar_injective.eq_iff

/-- Mean of one Walsh checkerboard. -/
theorem average_walsh {q n : Nat} (a : BitMatrix q n) :
    average (BitMatrix q n) (walsh a) = if a = 0 then 1 else 0 := by
  have h := AddChar.expect_eq_ite (walshChar a)
  simpa only [walshChar_apply, walshChar_eq_zero_iff, average,
    Fintype.expect_eq_sum_div_card] using h

/-- Every bit is its own additive inverse. -/
@[simp]
theorem neg_eq_self {q n : Nat} (a : BitMatrix q n) : -a = a := by
  funext i j
  change -(a i j) = a i j
  by_cases h : a i j = 0
  · simp [h]
  · rw [zmodTwo_eq_one_of_ne_zero (a i j) h]
    exact by decide

@[simp]
theorem add_self_eq_zero {q n : Nat} (a : BitMatrix q n) : a + a = 0 := by
  funext i j
  change a i j + a i j = 0
  by_cases h : a i j = 0
  · simp [h]
  · rw [zmodTwo_eq_one_of_ne_zero (a i j) h]
    exact by decide

@[simp]
theorem add_eq_zero_iff_eq {q n : Nat} (a b : BitMatrix q n) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun z => z + b) h
    simpa [add_assoc] using this
  · rintro rfl
    exact add_self_eq_zero a

/-- Walsh orthogonality in the mask variable. -/
theorem average_walsh_mul_walsh {q n : Nat} (a b : BitMatrix q n) :
    average (BitMatrix q n) (fun x => walsh a x * walsh b x) =
      if a = b then 1 else 0 := by
  rw [show (fun x => walsh a x * walsh b x) = walsh (a + b) by
    funext x
    exact (walsh_add_left a b x).symm]
  rw [average_walsh]
  by_cases h : a = b <;> simp [h, add_eq_zero_iff_eq]

/-- Dual Walsh orthogonality in the tape variable. -/
theorem average_walsh_mul_walsh_dual {q n : Nat} (x y : BitMatrix q n) :
    average (BitMatrix q n) (fun a => walsh a x * walsh a y) =
      if x = y then 1 else 0 := by
  simpa only [walsh_comm] using average_walsh_mul_walsh x y

/-- Unnormalized dual orthogonality. -/
theorem sum_walsh_mul_walsh_dual {q n : Nat} (x y : BitMatrix q n) :
    (∑ a : BitMatrix q n, walsh a x * walsh a y) =
      if x = y then (Fintype.card (BitMatrix q n) : Real) else 0 := by
  have h := average_walsh_mul_walsh_dual x y
  unfold average at h
  have hcard : (Fintype.card (BitMatrix q n) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (BitMatrix q n) ≠ 0)
  by_cases hxy : x = y
  · rw [if_pos hxy] at h ⊢
    exact (div_eq_one_iff_eq hcard).mp h
  · rw [if_neg hxy] at h ⊢
    exact (div_eq_zero_iff).mp h |>.resolve_right hcard

/-- Probability-normalized Walsh coefficient. -/
def fourier {q n : Nat} (f : BitMatrix q n -> Real) (a : BitMatrix q n) : Real :=
  average (BitMatrix q n) (fun x => f x * walsh a x)

/-- Normalized XOR convolution. -/
def convolution {q n : Nat} (f g : BitMatrix q n -> Real) (y : BitMatrix q n) : Real :=
  average (BitMatrix q n) (fun x => f x * g (y + x))

/-- Fourier inversion on a finite XOR tape. -/
theorem fourier_inversion {q n : Nat} (f : BitMatrix q n -> Real)
    (x : BitMatrix q n) :
    (∑ a : BitMatrix q n, fourier f a * walsh a x) = f x := by
  have hcard : (Fintype.card (BitMatrix q n) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (BitMatrix q n) ≠ 0)
  calc
    (∑ a : BitMatrix q n, fourier f a * walsh a x) =
      ∑ a : BitMatrix q n,
        average (BitMatrix q n)
          (fun y => f y * (walsh a y * walsh a x)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      unfold fourier
      rw [← average_mul_const]
      apply congrArg (average (BitMatrix q n))
      funext y
      ring
    _ = average (BitMatrix q n)
        (fun y => ∑ a : BitMatrix q n,
          f y * (walsh a y * walsh a x)) := by
      exact (average_fintype_sum
        (fun a y => f y * (walsh a y * walsh a x))).symm
    _ = average (BitMatrix q n)
        (fun y => f y *
          (∑ a : BitMatrix q n, walsh a y * walsh a x)) := by
      apply congrArg (average (BitMatrix q n))
      funext y
      rw [Finset.mul_sum]
    _ = average (BitMatrix q n)
        (fun y => f y *
          (if y = x then (Fintype.card (BitMatrix q n) : Real) else 0)) := by
      apply congrArg (average (BitMatrix q n))
      funext y
      rw [sum_walsh_mul_walsh_dual]
    _ = f x := by
      unfold average
      simp [hcard]

/-- Parseval identity for the probability-normalized transform. -/
theorem parseval_sq {q n : Nat} (f : BitMatrix q n -> Real) :
    average (BitMatrix q n) (fun x => (f x) ^ 2) =
      ∑ a : BitMatrix q n, (fourier f a) ^ 2 := by
  rw [show (fun x : BitMatrix q n => (f x) ^ 2) =
      (fun x => f x * ∑ a : BitMatrix q n, fourier f a * walsh a x) by
      funext x
      rw [fourier_inversion]
      ring]
  rw [show (fun x : BitMatrix q n =>
      f x * ∑ a : BitMatrix q n, fourier f a * walsh a x) =
      (fun x => ∑ a : BitMatrix q n,
        fourier f a * (f x * walsh a x)) by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring]
  rw [average_fintype_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [average_const_mul]
  unfold fourier
  ring

/-- Translation of a Walsh-weighted finite sum. -/
theorem average_translate_mul_walsh {q n : Nat}
    (g : BitMatrix q n -> Real) (a x : BitMatrix q n) :
    average (BitMatrix q n) (fun y => g (y + x) * walsh a y) =
      walsh a x * fourier g a := by
  let e : BitMatrix q n ≃ BitMatrix q n :=
    { toFun := fun y => y + x
      invFun := fun z => z + x
      left_inv := fun y => by simp [add_assoc]
      right_inv := fun z => by simp [add_assoc] }
  let F : BitMatrix q n -> Real := fun y => g (y + x) * walsh a y
  calc
    average (BitMatrix q n) (fun y => g (y + x) * walsh a y) =
        average (BitMatrix q n) F := rfl
    _ = average (BitMatrix q n) (fun z => F (e z)) :=
      (average_comp_equiv e F).symm
    _ = average (BitMatrix q n)
        (fun z => walsh a x * (g z * walsh a z)) := by
      apply congrArg (average (BitMatrix q n))
      funext z
      dsimp [F, e]
      rw [show (z + x) + x = z by simp [add_assoc]]
      rw [walsh_add_right]
      ring
    _ = walsh a x * fourier g a := by
      rw [average_const_mul]
      rfl

/-- XOR convolution is diagonal in the Walsh basis. -/
theorem fourier_convolution {q n : Nat}
    (f g : BitMatrix q n -> Real) (a : BitMatrix q n) :
    fourier (convolution f g) a = fourier f a * fourier g a := by
  unfold fourier convolution
  calc
    average (BitMatrix q n)
        (fun y => average (BitMatrix q n)
          (fun x => f x * g (y + x)) * walsh a y) =
      average (BitMatrix q n)
        (fun y => average (BitMatrix q n)
          (fun x => f x * (g (y + x) * walsh a y))) := by
      apply congrArg (average (BitMatrix q n))
      funext y
      rw [← average_mul_const]
      apply congrArg (average (BitMatrix q n))
      funext x
      ring
    _ = average (BitMatrix q n)
        (fun x => average (BitMatrix q n)
          (fun y => f x * (g (y + x) * walsh a y))) := by
      exact average_average_comm
        (fun y x => f x * (g (y + x) * walsh a y))
    _ = average (BitMatrix q n)
        (fun x => f x * average (BitMatrix q n)
          (fun y => g (y + x) * walsh a y)) := by
      apply congrArg (average (BitMatrix q n))
      funext x
      rw [average_const_mul]
    _ = average (BitMatrix q n)
        (fun x => f x * (walsh a x * fourier g a)) := by
      apply congrArg (average (BitMatrix q n))
      funext x
      rw [average_translate_mul_walsh]
    _ = fourier f a * fourier g a := by
      rw [show (fun x => f x * (walsh a x * fourier g a)) =
          (fun x => (f x * walsh a x) * fourier g a) by
        funext x
        ring]
      rw [average_mul_const]
      rfl

/-- Parseval after convolution. -/
theorem parseval_convolution_sq {q n : Nat}
    (f g : BitMatrix q n -> Real) :
    average (BitMatrix q n) (fun y => (convolution f g y) ^ 2) =
      ∑ a : BitMatrix q n, (fourier f a) ^ 2 * (fourier g a) ^ 2 := by
  rw [parseval_sq]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_convolution]
  ring

/-! ## Row support and spectral selectors -/

/-- Query coordinates on which a Walsh mask is nonzero.  These are the
coordinates used by the corresponding checkerboard. -/
def rowSupport {q n : Nat} (a : BitMatrix q n) : Finset (Fin q) :=
  Finset.univ.filter (fun i => a i ≠ 0)

/-- Number of visible coordinates used by a Walsh checkerboard. -/
def level {q n : Nat} (a : BitMatrix q n) : Nat := (rowSupport a).card

@[simp]
theorem mem_rowSupport {q n : Nat} (a : BitMatrix q n) (i : Fin q) :
    i ∈ rowSupport a ↔ a i ≠ 0 := by
  simp [rowSupport]

@[simp]
theorem rowSupport_zero {q n : Nat} :
    rowSupport (0 : BitMatrix q n) = ∅ := by
  ext i
  simp

@[simp]
theorem level_zero {q n : Nat} : level (0 : BitMatrix q n) = 0 := by
  simp [level]

theorem rowSupport_eq_empty_iff {q n : Nat} (a : BitMatrix q n) :
    rowSupport a = ∅ ↔ a = 0 := by
  constructor
  · intro h
    funext i j
    have hi : i ∉ rowSupport a := by simp [h]
    have hi' : a i = 0 := by simpa using hi
    exact congrFun hi' j
  · rintro rfl
    exact rowSupport_zero

theorem level_eq_zero_iff {q n : Nat} (a : BitMatrix q n) :
    level a = 0 ↔ a = 0 := by
  rw [level, Finset.card_eq_zero, rowSupport_eq_empty_iff]

/-- Sum of precisely those Walsh modes satisfying `p`. -/
def spectralPart {q n : Nat} (p : BitMatrix q n -> Prop)
    (f : BitMatrix q n -> Real) (x : BitMatrix q n) : Real :=
  ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
    fourier f a * walsh a x

/-- The selector retaining exactly the modes whose row support is `S`. -/
def supportPart {q n : Nat} (S : Finset (Fin q))
    (f : BitMatrix q n -> Real) : BitMatrix q n -> Real :=
  spectralPart (fun a => rowSupport a = S) f

/-- The selector retaining every mode involving at least `k` query rows. -/
def levelGePart {q n : Nat} (k : Nat)
    (f : BitMatrix q n -> Real) : BitMatrix q n -> Real :=
  spectralPart (fun a => k ≤ level a) f

theorem spectralPart_apply {q n : Nat} (p : BitMatrix q n -> Prop)
    (f : BitMatrix q n -> Real) (x : BitMatrix q n) :
    spectralPart p f x =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
        fourier f a * walsh a x := rfl

/-- A spectral selector really keeps exactly the requested coefficients. -/
theorem fourier_spectralPart {q n : Nat} (p : BitMatrix q n -> Prop)
    (f : BitMatrix q n -> Real) (b : BitMatrix q n) :
    fourier (spectralPart p f) b = if p b then fourier f b else 0 := by
  unfold fourier spectralPart
  rw [show
      (fun x =>
        (∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
          fourier f a * walsh a x) * walsh b x) =
      (fun x =>
        ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
          fourier f a * (walsh a x * walsh b x)) by
        funext x
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        ring]
  rw [average_finset_sum]
  simp_rw [average_const_mul, average_walsh_mul_walsh]
  by_cases hb : p b
  · rw [if_pos hb]
    simp [hb]
    rfl
  · rw [if_neg hb]
    simp [hb]

/-- Parseval restricted to a selected family of checkerboards. -/
theorem parseval_spectralPart_sq {q n : Nat}
    (p : BitMatrix q n -> Prop) (f : BitMatrix q n -> Real) :
    average (BitMatrix q n) (fun x => (spectralPart p f x) ^ 2) =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
        (fourier f a) ^ 2 := by
  rw [parseval_sq]
  simp_rw [fourier_spectralPart]
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hpa : p a <;> simp [hpa]

/-- Disjoint spectral selectors are orthogonal. -/
theorem average_spectralPart_mul_eq_zero {q n : Nat}
    (p r : BitMatrix q n -> Prop) (f g : BitMatrix q n -> Real)
    (hdisj : ∀ a, p a -> r a -> False) :
    average (BitMatrix q n)
      (fun x => spectralPart p f x * spectralPart r g x) = 0 := by
  unfold spectralPart
  rw [show
      (fun x =>
        (∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
          fourier f a * walsh a x) *
        (∑ b ∈ (Finset.univ : Finset (BitMatrix q n)).filter r,
          fourier g b * walsh b x)) =
      (fun x =>
        ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
          ∑ b ∈ (Finset.univ : Finset (BitMatrix q n)).filter r,
            (fourier f a * fourier g b) * (walsh a x * walsh b x)) by
        funext x
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring]
  rw [average_finset_sum]
  simp_rw [average_finset_sum]
  simp_rw [average_const_mul, average_walsh_mul_walsh]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have hpa : p a := by simpa using ha
  have hrb : r b := by simpa using hb
  by_cases hab : a = b
  · subst b
    exact (hdisj a hpa hrb).elim
  · simp [hab]

/-- Fourier inversion regrouped by exact query-row support. -/
theorem supportPart_reconstruction {q n : Nat}
    (f : BitMatrix q n -> Real) (x : BitMatrix q n) :
    ∑ S ∈ (Finset.univ : Finset (Fin q)).powerset, supportPart S f x = f x := by
  rw [← fourier_inversion f x]
  unfold supportPart spectralPart
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  have hs : rowSupport a ∈ (Finset.univ : Finset (Fin q)).powerset :=
    Finset.mem_powerset.mpr (by simp)
  simp_rw [eq_comm]
  simp [hs]

/-- Self-convolution reconstructed with squared Walsh coefficients. -/
theorem convolution_self_eq_spectral_sq {q n : Nat}
    (f : BitMatrix q n -> Real) (x : BitMatrix q n) :
    convolution f f x =
      ∑ a : BitMatrix q n, (fourier f a) ^ 2 * walsh a x := by
  rw [← fourier_inversion (convolution f f) x]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_convolution]
  ring

/-- Exact squared energy of any selected self-convolution modes. -/
theorem parseval_selected_convolution_sq {q n : Nat}
    (p : BitMatrix q n -> Prop) (f : BitMatrix q n -> Real) :
    average (BitMatrix q n)
      (fun x => (spectralPart p (convolution f f) x) ^ 2) =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter p,
        (fourier f a) ^ 4 := by
  rw [parseval_spectralPart_sq]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_convolution]
  ring

end RandomSystems.SoP.XORFourier
