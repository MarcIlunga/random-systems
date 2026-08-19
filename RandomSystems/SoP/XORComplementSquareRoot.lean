/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementProfiles
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators ComplexConjugate

open Finset
open ZMod

noncomputable section

namespace RandomSystems.SoP.XORComplement

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma sum_stdAddChar_mul (N : Nat) (c : ZMod (N + 1)) :
    (∑ t : ZMod (N + 1), stdAddChar (t * c)) =
      if c = 0 then ((N + 1 : Nat) : Complex) else 0 := by
  letI : NeZero (N + 1) := ⟨Nat.succ_ne_zero N⟩
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc]
    have hne : (stdAddChar (N := N + 1)).mulShift c ≠ 1 :=
      isPrimitive_stdAddChar (N + 1) hc
    simpa only [AddChar.mulShift_apply, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one hne)

def phaseMonomial {ι : Type*} [Fintype ι] (N : Nat)
    (d : ι → Nat) (t : ι → ZMod (N + 1)) : Complex :=
  ∏ i, stdAddChar (t i * (d i : ZMod (N + 1)))

lemma sum_phaseDifference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Nat) [NeZero (N + 1)] (d e : ι → Nat) :
    (∑ t : ι → ZMod (N + 1),
      ∏ i, stdAddChar
        (t i * ((e i : ZMod (N + 1)) - (d i : ZMod (N + 1))))) =
      ∏ i, if (e i : ZMod (N + 1)) = (d i : ZMod (N + 1)) then
        ((N + 1 : Nat) : Complex) else 0 := by
  have h := Finset.sum_prod_piFinset (ι := ι)
    (s := (Finset.univ : Finset (ZMod (N + 1))))
    (g := fun i t => stdAddChar
      (t * ((e i : ZMod (N + 1)) - (d i : ZMod (N + 1)))))
  simpa only [Fintype.piFinset_univ,
    sum_stdAddChar_mul, sub_eq_zero] using h

def radiusMonomial {ι : Type*} (r : ι → Real) (d : ι →₀ Nat) : Complex :=
  d.prod fun i m => (r i : Complex) ^ m

def phaseFinsupp {ι : Type*} (N : Nat) (d : ι →₀ Nat)
    (t : ι → ZMod (N + 1)) : Complex :=
  d.prod fun i m => stdAddChar (t i) ^ m

def inversePhase {ι : Type*} [Fintype ι] (N : Nat)
    (d : ι →₀ Nat) (t : ι → ZMod (N + 1)) : Complex :=
  ∏ i, stdAddChar (-(t i * (d i : ZMod (N + 1))))

def torusPoint {ι : Type*} (N : Nat) (r : ι → Real)
    (t : ι → ZMod (N + 1)) (i : ι) : Complex :=
  (r i : Complex) * stdAddChar (t i)

lemma phaseFinsupp_eq_phaseMonomial {ι : Type*} [Fintype ι]
    (N : Nat) [NeZero (N + 1)] (d : ι →₀ Nat)
    (t : ι → ZMod (N + 1)) :
    phaseFinsupp N d t = phaseMonomial N d t := by
  unfold phaseFinsupp phaseMonomial
  rw [Finsupp.prod_fintype _ _ (by simp)]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← AddChar.map_nsmul_eq_pow]
  congr 2
  simp [nsmul_eq_mul, mul_comm]

lemma finsupp_prod_torusPoint {ι : Type*} [Fintype ι]
    (N : Nat) [NeZero (N + 1)] (r : ι → Real)
    (d : ι →₀ Nat) (t : ι → ZMod (N + 1)) :
    d.prod (fun i m => torusPoint N r t i ^ m) =
      radiusMonomial r d * phaseFinsupp N d t := by
  unfold torusPoint radiusMonomial phaseFinsupp
  rw [← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro i hi
  rw [mul_pow]

lemma inversePhase_mul_phaseFinsupp {ι : Type*} [Fintype ι]
    (N : Nat) [NeZero (N + 1)] (d e : ι →₀ Nat)
    (t : ι → ZMod (N + 1)) :
    inversePhase N d t * phaseFinsupp N e t =
      ∏ i, stdAddChar
        (t i * ((e i : ZMod (N + 1)) - (d i : ZMod (N + 1)))) := by
  rw [phaseFinsupp_eq_phaseMonomial]
  unfold inversePhase phaseMonomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

lemma sum_inversePhase_mul_phaseFinsupp {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N : Nat) [NeZero (N + 1)] (d e : ι →₀ Nat)
    (hd : ∀ i, d i ≤ N) (he : ∀ i, e i ≤ N) :
    (∑ t : ι → ZMod (N + 1),
      inversePhase N d t * phaseFinsupp N e t) =
      if e = d then ((N + 1 : Nat) : Complex) ^ Fintype.card ι else 0 := by
  simp_rw [inversePhase_mul_phaseFinsupp]
  rw [sum_phaseDifference]
  by_cases hed : e = d
  · subst e
    simp
  · rw [if_neg hed]
    have hex : ∃ i, e i ≠ d i := by
      simpa only [Finsupp.ext_iff, not_forall] using hed
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (i := i)
    · simp
    · rw [if_neg]
      intro hcast
      apply hi
      exact CharP.natCast_injOn_Iio (ZMod (N + 1)) (N + 1)
        (by simpa using Nat.lt_succ_iff.mpr (he i))
        (by simpa using Nat.lt_succ_iff.mpr (hd i)) hcast

theorem torus_coefficient_extraction {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N : Nat) [NeZero (N + 1)] (r : ι → Real)
    (p : MvPolynomial ι Complex) (d : ι →₀ Nat)
    (hp : p.totalDegree ≤ N) (hd : ∀ i, d i ≤ N) :
    (∑ t : ι → ZMod (N + 1),
      inversePhase N d t *
        MvPolynomial.eval (torusPoint N r t) p) =
      ((N + 1 : Nat) : Complex) ^ Fintype.card ι *
        MvPolynomial.coeff d p * radiusMonomial r d := by
  simp_rw [MvPolynomial.eval_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ p.support,
        ∑ t : ι → ZMod (N + 1),
          inversePhase N d t *
            (MvPolynomial.coeff e p *
              ∏ i ∈ e.support, torusPoint N r t i ^ e i)) =
        ∑ e ∈ p.support,
          MvPolynomial.coeff e p * radiusMonomial r e *
            (∑ t : ι → ZMod (N + 1),
              inversePhase N d t * phaseFinsupp N e t) := by
          apply Finset.sum_congr rfl
          intro e he
          calc
            (∑ t : ι → ZMod (N + 1),
                inversePhase N d t *
                  (MvPolynomial.coeff e p *
                    ∏ i ∈ e.support, torusPoint N r t i ^ e i)) =
              ∑ t : ι → ZMod (N + 1),
                (MvPolynomial.coeff e p * radiusMonomial r e) *
                  (inversePhase N d t * phaseFinsupp N e t) := by
                    apply Finset.sum_congr rfl
                    intro t _ht
                    change inversePhase N d t *
                      (MvPolynomial.coeff e p *
                        e.prod (fun i m => torusPoint N r t i ^ m)) = _
                    rw [finsupp_prod_torusPoint]
                    ring
            _ = _ := by rw [Finset.mul_sum]
    _ = ∑ e ∈ p.support,
          MvPolynomial.coeff e p * radiusMonomial r e *
            (if e = d then
              ((N + 1 : Nat) : Complex) ^ Fintype.card ι else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [sum_inversePhase_mul_phaseFinsupp N d e hd]
          intro i
          have hcomp : e i ≤ e.sum (fun _ m => m) := by
            simpa using (Finsupp.single_le_sum (f := e)
              (g := fun _ m => m) (by simp) i)
          exact hcomp.trans ((MvPolynomial.le_totalDegree he).trans hp)
    _ = ((N + 1 : Nat) : Complex) ^ Fintype.card ι *
          MvPolynomial.coeff d p * radiusMonomial r d := by
          by_cases hdsupp : d ∈ p.support
          · rw [Finset.sum_eq_single d]
            · simp [mul_assoc, mul_left_comm, mul_comm]
            · intro e he hed
              simp [hed]
            · exact fun h => (h hdsupp).elim
          · rw [MvPolynomial.notMem_support_iff.mp hdsupp]
            simp [hdsupp]

@[simp]
lemma norm_stdAddChar (N : Nat) [NeZero N] (x : ZMod N) :
    ‖stdAddChar x‖ = 1 := by
  rw [stdAddChar_apply]
  exact Circle.norm_coe x.toCircle

@[simp]
lemma norm_inversePhase {ι : Type*} [Fintype ι]
    (N : Nat) [NeZero (N + 1)] (d : ι →₀ Nat)
    (t : ι → ZMod (N + 1)) :
    ‖inversePhase N d t‖ = 1 := by
  unfold inversePhase
  rw [norm_prod]
  simp

theorem norm_coeff_mul_radius_le_of_torus_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N : Nat) [NeZero (N + 1)] (r : ι → Real)
    (p : MvPolynomial ι Complex) (d : ι →₀ Nat)
    (hp : p.totalDegree ≤ N) (hd : ∀ i, d i ≤ N)
    {B : Real} (hB : 0 ≤ B)
    (heval : ∀ t : ι → ZMod (N + 1),
      ‖MvPolynomial.eval (torusPoint N r t) p‖ ≤ B) :
    ‖MvPolynomial.coeff d p * radiusMonomial r d‖ ≤ B := by
  have hextract := torus_coefficient_extraction N r p d hp hd
  have hscale : (0 : Real) < ((N + 1 : Nat) : Real) ^ Fintype.card ι := by
    positivity
  have hmul :
      ((N + 1 : Nat) : Real) ^ Fintype.card ι *
          ‖MvPolynomial.coeff d p * radiusMonomial r d‖ ≤
        ((N + 1 : Nat) : Real) ^ Fintype.card ι * B := by
    calc
    ((N + 1 : Nat) : Real) ^ Fintype.card ι *
          ‖MvPolynomial.coeff d p * radiusMonomial r d‖ =
        ‖(((N + 1 : Nat) : Complex) ^ Fintype.card ι) *
          MvPolynomial.coeff d p * radiusMonomial r d‖ := by
            simp only [norm_mul, norm_pow, norm_natCast]
            ring
    _ = ‖∑ t : ι → ZMod (N + 1),
          inversePhase N d t *
            MvPolynomial.eval (torusPoint N r t) p‖ := by rw [hextract]
    _ ≤ ∑ t : ι → ZMod (N + 1),
          ‖inversePhase N d t *
            MvPolynomial.eval (torusPoint N r t) p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _t : ι → ZMod (N + 1), B := by
      apply Finset.sum_le_sum
      intro t _ht
      rw [norm_mul, norm_inversePhase, one_mul]
      exact heval t
    _ = ((N + 1 : Nat) : Real) ^ Fintype.card ι * B := by
      simp
  exact le_of_mul_le_mul_left hmul hscale

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCoefficient
open RandomSystems.SoP.XORComplement

def characterPartitionPolynomial {ι : Type*} [Fintype ι]
    (n : Nat) (rows : ι → XorSpace n) : MvPolynomial ι Complex :=
  ∏ x : XorSpace n,
    ∑ i : ι,
      MvPolynomial.C (vectorWalsh (rows i) x : Complex) * MvPolynomial.X i

lemma characterPartitionPolynomial_totalDegree_le {ι : Type*}
    [Fintype ι] (n : Nat) (rows : ι → XorSpace n) :
    (characterPartitionPolynomial n rows).totalDegree ≤ 2 ^ n := by
  unfold characterPartitionPolynomial
  calc
    (∏ x : XorSpace n,
        ∑ i : ι,
          MvPolynomial.C (vectorWalsh (rows i) x : Complex) *
            MvPolynomial.X i).totalDegree ≤
      ∑ _x : XorSpace n,
        (∑ i : ι,
          MvPolynomial.C (vectorWalsh (rows i) _x : Complex) *
            MvPolynomial.X i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod Finset.univ _
    _ ≤ ∑ _x : XorSpace n, 1 := by
      apply Finset.sum_le_sum
      intro x _hx
      refine (MvPolynomial.totalDegree_finset_sum Finset.univ _).trans ?_
      rw [Finset.sup_le_iff]
      intro i _hi
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    _ = 2 ^ n := by simp [card_xorSpace]

def characterLinearForm {ι : Type*} [Fintype ι]
    {n : Nat} (rows : ι → XorSpace n) (z : ι → Complex)
    (x : XorSpace n) : Complex :=
  ∑ i : ι, (vectorWalsh (rows i) x : Complex) * z i

lemma characterPartitionPolynomial_eval {ι : Type*} [Fintype ι]
    (n : Nat) (rows : ι → XorSpace n) (z : ι → Complex) :
    MvPolynomial.eval z (characterPartitionPolynomial n rows) =
      ∏ x : XorSpace n, characterLinearForm rows z x := by
  simp [characterPartitionPolynomial, characterLinearForm]

lemma sum_vectorWalsh_mul_vectorWalsh {n : Nat} (a b : XorSpace n) :
    (∑ x : XorSpace n, vectorWalsh a x * vectorWalsh b x) =
      if a = b then ((2 ^ n : Nat) : Real) else 0 := by
  rw [show (∑ x : XorSpace n, vectorWalsh a x * vectorWalsh b x) =
      ∑ x : XorSpace n, vectorWalsh (a + b) x by
    apply Finset.sum_congr rfl
    intro x _hx
    rw [vectorWalsh_add_left]]
  rw [sum_vectorWalsh]
  by_cases hab : a = b
  · subst b
    simp
  · have hsum : a + b ≠ 0 := by
      intro h
      apply hab
      simpa [ZModModule.neg_eq_self] using
        (eq_neg_of_add_eq_zero_left h)
    simp [hab, hsum]

lemma sum_normSq_characterLinearForm {ι : Type*} [Fintype ι]
    {n : Nat} {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (z : ι → Complex) :
    (∑ x : XorSpace n, Complex.normSq (characterLinearForm rows z x)) =
      ((2 ^ n : Nat) : Real) * ∑ i : ι, Complex.normSq (z i) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  unfold characterLinearForm
  calc
    (∑ x : XorSpace n,
        (starRingEnd Complex
          (∑ i : ι, (vectorWalsh (rows i) x : Complex) * z i)) *
          (∑ j : ι, (vectorWalsh (rows j) x : Complex) * z j)) =
      ∑ i : ι, ∑ j : ι,
        (starRingEnd Complex (z i) * z j) *
          (∑ x : XorSpace n,
            ((vectorWalsh (rows i) x : Real) : Complex) *
              ((vectorWalsh (rows j) x : Real) : Complex)) := by
        simp_rw [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _hj
        calc
          (∑ x : XorSpace n,
              ((vectorWalsh (rows i) x : Real) : Complex) *
                  starRingEnd Complex (z i) *
                (((vectorWalsh (rows j) x : Real) : Complex) * z j)) =
            ∑ x : XorSpace n,
              (starRingEnd Complex (z i) * z j) *
                (((vectorWalsh (rows i) x : Real) : Complex) *
                  ((vectorWalsh (rows j) x : Real) : Complex)) := by
                    apply Finset.sum_congr rfl
                    intro x _hx
                    ring
          _ = _ := rfl
    _ = ∑ i : ι, ∑ j : ι,
        (starRingEnd Complex (z i) * z j) *
          (if rows i = rows j then ((2 ^ n : Nat) : Complex) else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        by_cases hij : rows i = rows j
        · simpa [hij] using congrArg Complex.ofReal
            (sum_vectorWalsh_mul_vectorWalsh (rows i) (rows j))
        · simpa [hij] using congrArg Complex.ofReal
            (sum_vectorWalsh_mul_vectorWalsh (rows i) (rows j))
    _ = ((2 ^ n : Nat) : Complex) *
        ∑ i : ι, starRingEnd Complex (z i) * z i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_eq_single i]
      · simp [mul_assoc, mul_comm]
      · intro j _hj hji
        have hne : rows i ≠ rows j := fun h => hji (hrows h.symm)
        simp [hne]
      · simp
    _ = _ := by norm_num [Nat.cast_pow]

@[simp]
lemma normSq_torusPoint_sqrt {ι : Type*}
    (N : Nat) [NeZero (N + 1)] (a : ι → Nat)
    (t : ι → ZMod (N + 1)) (i : ι) :
    Complex.normSq (torusPoint N (fun i => Real.sqrt (a i : Real)) t i) =
      (a i : Real) := by
  rw [← Complex.sq_norm]
  simp [torusPoint, Real.sq_sqrt]

lemma sum_normSq_characterLinearForm_torus {ι : Type*} [Fintype ι]
    {n : Nat} {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (a : ι → Nat) (ha : ∑ i : ι, a i = 2 ^ n)
    (t : ι → ZMod (2 ^ n + 1)) :
    (∑ x : XorSpace n,
      Complex.normSq (characterLinearForm rows
        (torusPoint (2 ^ n) (fun i => Real.sqrt (a i : Real)) t) x)) =
      (((2 ^ n : Nat) : Real) ^ 2) := by
  rw [sum_normSq_characterLinearForm hrows]
  simp only [normSq_torusPoint_sqrt]
  norm_cast
  rw [ha]
  ring

/-- The division-free finite AM--GM form used below. -/
lemma finset_prod_le_pow_average {α : Type*} [Fintype α]
    (z : α → Real) (hz : ∀ i, 0 ≤ z i)
    (hcard : Fintype.card α ≠ 0) :
    (∏ i : α, z i) ≤
      ((∑ i : α, z i) / (Fintype.card α : Real)) ^ Fintype.card α := by
  have hsum : (0 : Real) < ∑ _i : α, (1 : Real) := by
    simpa using (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard) :
      (0 : Real) < Fintype.card α)
  have hgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset α) (fun _ => (1 : Real)) z
    (fun _ _ => zero_le_one) hsum (fun i _ => hz i)
  have hgm' :
      (∏ i : α, z i) ^ ((Fintype.card α : Real)⁻¹) ≤
        (∑ i : α, z i) / (Fintype.card α : Real) := by
    simpa using hgm
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hz i)) _)
    hgm' (Fintype.card α)
  have hprod : 0 ≤ ∏ i : α, z i :=
    Finset.prod_nonneg (fun i _ => hz i)
  rw [Real.rpow_inv_natCast_pow hprod hcard] at hpow
  exact hpow

lemma prod_normSq_characterLinearForm_torus_le {ι : Type*} [Fintype ι]
    {n : Nat} {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (a : ι → Nat) (ha : ∑ i : ι, a i = 2 ^ n)
    (t : ι → ZMod (2 ^ n + 1)) :
    (∏ x : XorSpace n,
      Complex.normSq (characterLinearForm rows
        (torusPoint (2 ^ n) (fun i => Real.sqrt (a i : Real)) t) x)) ≤
      (((2 ^ n : Nat) : Real) ^ (2 ^ n)) := by
  calc
    (∏ x : XorSpace n,
        Complex.normSq (characterLinearForm rows
          (torusPoint (2 ^ n) (fun i => Real.sqrt (a i : Real)) t) x)) ≤
      ((∑ x : XorSpace n,
          Complex.normSq (characterLinearForm rows
            (torusPoint (2 ^ n) (fun i => Real.sqrt (a i : Real)) t) x)) /
        (Fintype.card (XorSpace n) : Real)) ^ Fintype.card (XorSpace n) :=
          finset_prod_le_pow_average _ (fun _ => Complex.normSq_nonneg _)
            (by simp [card_xorSpace])
    _ = (((2 ^ n : Nat) : Real) ^ (2 ^ n)) := by
      rw [sum_normSq_characterLinearForm_torus hrows a ha]
      rw [RandomSystems.SoP.XORInjection.card_xorSpace n]
      change ((((2 ^ n : Nat) : Real) ^ 2) /
        ((2 ^ n : Nat) : Real)) ^ (2 ^ n) = _
      have hN : (((2 ^ n : Nat) : Real)) ≠ 0 := by positivity
      rw [show (((2 ^ n : Nat) : Real) ^ 2) /
          ((2 ^ n : Nat) : Real) = ((2 ^ n : Nat) : Real) by
        rw [pow_two]
        exact mul_div_cancel_left₀ _ hN]

lemma sq_norm_characterPartitionPolynomial_eval_torus_le
    {ι : Type*} [Fintype ι] {n : Nat}
    {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (a : ι → Nat) (ha : ∑ i : ι, a i = 2 ^ n)
    (t : ι → ZMod (2 ^ n + 1)) :
    ‖MvPolynomial.eval
      (torusPoint (2 ^ n) (fun i => Real.sqrt (a i : Real)) t)
      (characterPartitionPolynomial n rows)‖ ^ 2 ≤
      (((2 ^ n : Nat) : Real) ^ (2 ^ n)) := by
  rw [characterPartitionPolynomial_eval, norm_prod, ← Finset.prod_pow]
  simpa only [Complex.sq_norm] using
    prod_normSq_characterLinearForm_torus_le hrows a ha t

lemma norm_characterPartitionPolynomial_eval_torus_le
    {ι : Type*} [Fintype ι] {n : Nat}
    {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (a : ι → Nat) (ha : ∑ i : ι, a i = 2 ^ n)
    (t : ι → ZMod (2 ^ n + 1)) :
    ‖MvPolynomial.eval
      (torusPoint (2 ^ n) (fun i => Real.sqrt (a i : Real)) t)
      (characterPartitionPolynomial n rows)‖ ≤
      Real.sqrt (((2 ^ n : Nat) : Real) ^ (2 ^ n)) := by
  exact Real.le_sqrt_of_sq_le
    (sq_norm_characterPartitionPolynomial_eval_torus_le hrows a ha t)

theorem norm_characterPartitionCoefficient_mul_radius_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (a : ι → Nat) (ha : ∑ i : ι, a i = 2 ^ n) :
    let d : ι →₀ Nat := Finsupp.equivFunOnFinite.symm a
    ‖MvPolynomial.coeff d (characterPartitionPolynomial n rows) *
        radiusMonomial (fun i => Real.sqrt (a i : Real)) d‖ ≤
      Real.sqrt (((2 ^ n : Nat) : Real) ^ (2 ^ n)) := by
  letI : NeZero (2 ^ n + 1) := ⟨Nat.succ_ne_zero (2 ^ n)⟩
  let d : ι →₀ Nat := Finsupp.equivFunOnFinite.symm a
  have hd : ∀ i, d i ≤ 2 ^ n := by
    intro i
    have hi : a i ≤ ∑ j : ι, a j := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [d, ha] using hi
  exact norm_coeff_mul_radius_le_of_torus_bound
    (2 ^ n) (fun i => Real.sqrt (a i : Real))
    (characterPartitionPolynomial n rows) d
    (characterPartitionPolynomial_totalDegree_le n rows) hd
    (Real.sqrt_nonneg _)
    (norm_characterPartitionPolynomial_eval_torus_le hrows a ha)

/-- Occupancy vector of a finite labeling. -/
def functionHistogram {α ι : Type*} [Fintype α] [DecidableEq ι]
    (f : α → ι) : ι →₀ Nat :=
  ∑ x : α, Finsupp.single (f x) 1

@[simp]
lemma functionHistogram_apply {α ι : Type*} [Fintype α] [DecidableEq ι]
    (f : α → ι) (i : ι) :
    functionHistogram f i = ((Finset.univ : Finset α).filter (fun x => f x = i)).card := by
  unfold functionHistogram
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simpa using
    (Finset.sum_boole (R := Nat) (fun x : α => f x = i) Finset.univ)

lemma prod_X_eq_monomial_functionHistogram
    {α ι R : Type*} [Fintype α] [DecidableEq ι] [CommSemiring R]
    (f : α → ι) :
    (∏ x : α, MvPolynomial.X (R := R) (f x)) =
      MvPolynomial.monomial (functionHistogram f) 1 := by
  classical
  unfold functionHistogram
  induction (Finset.univ : Finset α) using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.prod_insert hx, Finset.sum_insert hx]
      rw [ih, MvPolynomial.X, MvPolynomial.monomial_mul]
      simp [add_comm]

lemma coeff_characterPartitionPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    (rows : ι → XorSpace n) (d : ι →₀ Nat) :
    MvPolynomial.coeff d (characterPartitionPolynomial n rows) =
      ∑ f : XorSpace n → ι,
        if functionHistogram f = d then
          (∏ x : XorSpace n, (vectorWalsh (rows (f x)) x : Complex))
        else 0 := by
  unfold characterPartitionPolynomial
  rw [Fintype.prod_sum]
  simp_rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro f _hf
  rw [Finset.prod_mul_distrib]
  rw [← map_prod]
  rw [prod_X_eq_monomial_functionHistogram]
  rw [MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.coeff_monomial]
  by_cases hfd : functionHistogram f = d
  · simp [hfd]
  · simp [hfd]

lemma functionHistogram_comp_perm {α ι : Type*}
    [Fintype α] [DecidableEq ι] (p : α → ι) (sigma : Equiv.Perm α) :
    functionHistogram (p ∘ sigma) = functionHistogram p := by
  ext i
  rw [functionHistogram_apply, functionHistogram_apply]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  change Fintype.card {x : α // p (sigma x) = i} =
    Fintype.card {x : α // p x = i}
  exact Fintype.card_congr
    (Equiv.subtypeEquiv sigma (fun _x => Iff.rfl))

lemma exists_perm_comp_of_functionHistogram_eq
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    {p f : α → ι} (h : functionHistogram f = functionHistogram p) :
    ∃ sigma : Equiv.Perm α, p ∘ sigma = f := by
  have hcard (i : ι) :
      Fintype.card {x : α // f x = i} =
        Fintype.card {x : α // p x = i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [functionHistogram_apply] using
      congrFun (congrArg DFunLike.coe h) i
  let E : ∀ i : ι, {x : α // f x = i} ≃ {x : α // p x = i} :=
    fun i => Fintype.equivOfCardEq (hcard i)
  let sigma : Equiv.Perm α :=
    (Equiv.sigmaFiberEquiv f).symm |>.trans
      ((Equiv.sigmaCongr (Equiv.refl _) E).trans
        (Equiv.sigmaFiberEquiv p))
  refine ⟨sigma, ?_⟩
  funext x
  change p ((E (f x) ⟨x, rfl⟩).1) = f x
  exact (E (f x) ⟨x, rfl⟩).2

noncomputable def stabilizerEquivPermCompFiber
    {α ι : Type*} [Fintype α] [DecidableEq α]
    (p f : α → ι) (tau : Equiv.Perm α) (htau : p ∘ tau = f) :
    {rho : Equiv.Perm α // p ∘ rho = p} ≃
      {sigma : Equiv.Perm α // p ∘ sigma = f} where
  toFun rho := ⟨rho.1 * tau, by
    rw [show p ∘ (rho.1 * tau) = (p ∘ rho.1) ∘ tau by rfl,
      rho.2, htau]⟩
  invFun sigma := ⟨sigma.1 * tau.symm, by
    rw [show p ∘ (sigma.1 * tau.symm) = (p ∘ sigma.1) ∘ tau.symm by rfl,
      sigma.2, ← htau]
    funext x
    simp⟩
  left_inv rho := by
    apply Subtype.ext
    change rho.1 * tau * tau.symm = rho.1
    rw [mul_assoc, Equiv.Perm.mul_symm, mul_one]
  right_inv sigma := by
    apply Subtype.ext
    change sigma.1 * tau.symm * tau = sigma.1
    rw [mul_assoc, Equiv.Perm.symm_mul, mul_one]

lemma card_perm_comp_fiber_eq
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (p f : α → ι) (h : functionHistogram f = functionHistogram p) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter
      (fun sigma : Equiv.Perm α => p ∘ sigma = f)).card =
      ∏ i : ι, (Fintype.card {x : α // p x = i}).factorial := by
  obtain ⟨tau, htau⟩ := exists_perm_comp_of_functionHistogram_eq h
  calc
    ((Finset.univ : Finset (Equiv.Perm α)).filter
        (fun sigma : Equiv.Perm α => p ∘ sigma = f)).card =
      Fintype.card {sigma : Equiv.Perm α // p ∘ sigma = f} := by
        rw [Fintype.card_subtype]
    _ = Fintype.card {rho : Equiv.Perm α // p ∘ rho = p} :=
      Fintype.card_congr (stabilizerEquivPermCompFiber p f tau htau).symm
    _ = ∏ i : ι, (Fintype.card {x : α // p x = i}).factorial :=
      DomMulAct.stabilizer_card p

theorem sum_perm_comp_eq_stabilizer_mul_sum_histogram
    {α ι R : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] [CommSemiring R]
    (p : α → ι) (W : (α → ι) → R) :
    (∑ sigma : Equiv.Perm α, W (p ∘ sigma)) =
      ((∏ i : ι, (Fintype.card {x : α // p x = i}).factorial : Nat) : R) *
        ∑ f : α → ι,
          if functionHistogram f = functionHistogram p then W f else 0 := by
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset (Equiv.Perm α)))
    (g := fun sigma : Equiv.Perm α => p ∘ sigma)
    (f := fun sigma => W (p ∘ sigma))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases hhist : functionHistogram f = functionHistogram p
  · calc
      (∑ sigma ∈ (Finset.univ : Finset (Equiv.Perm α)).filter
          (fun sigma : Equiv.Perm α => p ∘ sigma = f), W (p ∘ sigma)) =
        ∑ _sigma ∈ (Finset.univ : Finset (Equiv.Perm α)).filter
          (fun sigma : Equiv.Perm α => p ∘ sigma = f), W f := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            rw [(Finset.mem_filter.mp hsigma).2]
      _ = (((Finset.univ : Finset (Equiv.Perm α)).filter
          (fun sigma : Equiv.Perm α => p ∘ sigma = f)).card : R) * W f := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((∏ i : ι,
          (Fintype.card {x : α // p x = i}).factorial : Nat) : R) *
            (if functionHistogram f = functionHistogram p then W f else 0) := by
              rw [card_perm_comp_fiber_eq p f hhist]
              simp [hhist]
  · have hempty :
        (Finset.univ : Finset (Equiv.Perm α)).filter
          (fun sigma : Equiv.Perm α => p ∘ sigma = f) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro sigma _hsigma heq
      apply hhist
      rw [← heq]
      exact functionHistogram_comp_perm p sigma
    simp [hempty, hhist]

/-- Once source and target have the same finite cardinality, an embedding is
just a permutation after choosing one reference enumeration. -/
noncomputable def fullEmbeddingEquivPerm
    {A G : Type*} [Finite G] (e0 : A ≃ G) :
    (A ↪ G) ≃ Equiv.Perm G :=
  let reindex : (A ↪ G) ≃ (G ↪ G) :=
    { toFun := fun e => e0.symm.toEmbedding.trans e
      invFun := fun e => e0.toEmbedding.trans e
      left_inv := fun e => by
        ext i
        simp
      right_inv := fun e => by
        ext x
        simp }
  reindex.trans (Equiv.embeddingEquivOfFinite G)

@[simp]
lemma fullEmbeddingEquivPerm_apply
    {A G : Type*} [Finite G] (e0 : A ≃ G)
    (e : A ↪ G) (x : G) :
    fullEmbeddingEquivPerm e0 e x = e (e0.symm x) := by
  unfold fullEmbeddingEquivPerm
  rw [Equiv.trans_apply]
  change (e0.symm.toEmbedding.trans e).equivOfFiniteSelfEmbedding x = _
  exact congrArg
    (fun h : G ↪ G => h x)
    (Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding
      (e0.symm.toEmbedding.trans e))

lemma checkerProduct_of_labels {ι : Type*} [Fintype ι]
    {n : Nat} (rows : ι → XorSpace n)
    (p : Fin (2 ^ n) → ι) (e : Fin (2 ^ n) ↪ XorSpace n) :
    checkerProduct (fun i => rows (p i)) e =
      ∏ i : Fin (2 ^ n), vectorWalsh (rows (p i)) (e i) := by
  rfl

lemma sum_checkerProduct_labels_eq_sum_perm_histogram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Nat} (rows : ι → XorSpace n)
    (p : Fin (2 ^ n) → ι)
    (e0 : Fin (2 ^ n) ≃ XorSpace n) :
    (∑ e : Fin (2 ^ n) ↪ XorSpace n,
        (checkerProduct (fun i => rows (p i)) e : Complex)) =
      ∑ sigma : Equiv.Perm (XorSpace n),
        ∏ x : XorSpace n,
          (vectorWalsh
            (rows (((p ∘ e0.symm) ∘ sigma) x)) x : Complex) := by
  calc
    (∑ e : Fin (2 ^ n) ↪ XorSpace n,
        (checkerProduct (fun i => rows (p i)) e : Complex)) =
      ∑ sigma : Equiv.Perm (XorSpace n),
        (checkerProduct (fun i => rows (p i))
          ((fullEmbeddingEquivPerm e0).symm sigma) : Complex) := by
            exact Fintype.sum_equiv (fullEmbeddingEquivPerm e0)
              _ _ (fun e => by simp)
    _ = ∑ sigma : Equiv.Perm (XorSpace n),
        ∏ x : XorSpace n,
          (vectorWalsh
            (rows (((p ∘ e0.symm) ∘ sigma.symm) x)) x : Complex) := by
          apply Finset.sum_congr rfl
          intro sigma _hsigma
          unfold checkerProduct
          push_cast
          rw [show (∏ i : Fin (2 ^ n),
              (vectorWalsh (rows (p i))
                ((fullEmbeddingEquivPerm e0).symm sigma i) : Complex)) =
              ∏ x : XorSpace n,
                (vectorWalsh
                  (rows (((p ∘ e0.symm) ∘ sigma.symm) x)) x : Complex) by
            apply Fintype.prod_equiv (e0.trans sigma)
            intro i
            have he : ((fullEmbeddingEquivPerm e0).symm sigma) i =
                sigma (e0 i) := by
              have h := fullEmbeddingEquivPerm_apply e0
                ((fullEmbeddingEquivPerm e0).symm sigma) (e0 i)
              simpa using h.symm
            simp [he]]
    _ = _ := by
      simpa using (Equiv.sum_comp
        (Equiv.inv (Equiv.Perm (XorSpace n)))
        (fun sigma : Equiv.Perm (XorSpace n) =>
          ∏ x : XorSpace n,
            (vectorWalsh
              (rows (((p ∘ e0.symm) ∘ sigma) x)) x : Complex)))

lemma sum_checkerProduct_labels_eq_stabilizer_mul_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Nat} (rows : ι → XorSpace n)
    (p : Fin (2 ^ n) → ι)
    (e0 : Fin (2 ^ n) ≃ XorSpace n) :
    (∑ e : Fin (2 ^ n) ↪ XorSpace n,
        (checkerProduct (fun i => rows (p i)) e : Complex)) =
      ((∏ i : ι,
          (Fintype.card {x : XorSpace n // (p ∘ e0.symm) x = i}).factorial : Nat) :
        Complex) *
        MvPolynomial.coeff (functionHistogram (p ∘ e0.symm))
          (characterPartitionPolynomial n rows) := by
  rw [sum_checkerProduct_labels_eq_sum_perm_histogram rows p e0]
  rw [sum_perm_comp_eq_stabilizer_mul_sum_histogram
    (p ∘ e0.symm)
    (fun f : XorSpace n → ι =>
      ∏ x : XorSpace n,
        (vectorWalsh (rows (f x)) x : Complex))]
  rw [← coeff_characterPartitionPolynomial rows
    (functionHistogram (p ∘ e0.symm))]

/-- Number of labelings with the same occupancy vector as `p`. -/
def histogramOrbitSize {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (p : α → ι) : Nat :=
  ((Finset.univ : Finset (α → ι)).filter
    (fun f => functionHistogram f = functionHistogram p)).card

lemma histogramOrbitSize_pos {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (p : α → ι) :
    0 < histogramOrbitSize p := by
  unfold histogramOrbitSize
  rw [Finset.card_pos]
  exact ⟨p, by simp⟩

lemma card_perm_eq_stabilizer_mul_histogramOrbitSize
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (p : α → ι) :
    Fintype.card (Equiv.Perm α) =
      (∏ i : ι, (Fintype.card {x : α // p x = i}).factorial) *
        histogramOrbitSize p := by
  have h := sum_perm_comp_eq_stabilizer_mul_sum_histogram
    (R := Nat) p (fun _ => 1)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    histogramOrbitSize, Finset.sum_boole] using h

theorem histogramOrbitSize_mul_checkerCorrelation_eq_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : Nat} (rows : ι → XorSpace n)
    (p : Fin (2 ^ n) → ι)
    (e0 : Fin (2 ^ n) ≃ XorSpace n) :
    ((histogramOrbitSize (p ∘ e0.symm) : Nat) : Complex) *
        (checkerCorrelation (fun i => rows (p i)) : Complex) =
      MvPolynomial.coeff (functionHistogram (p ∘ e0.symm))
        (characterPartitionPolynomial n rows) := by
  let K : Nat :=
    ∏ i : ι,
      (Fintype.card {x : XorSpace n // (p ∘ e0.symm) x = i}).factorial
  let M : Nat := histogramOrbitSize (p ∘ e0.symm)
  have hK : K ≠ 0 := by
    unfold K
    positivity
  have hM : M ≠ 0 := (histogramOrbitSize_pos (p ∘ e0.symm)).ne'
  have hsum := sum_checkerProduct_labels_eq_stabilizer_mul_coeff rows p e0
  have hcardEmb : Fintype.card (Fin (2 ^ n) ↪ XorSpace n) =
      Fintype.card (Equiv.Perm (XorSpace n)) :=
    Fintype.card_congr (fullEmbeddingEquivPerm e0)
  have hcardPerm := card_perm_eq_stabilizer_mul_histogramOrbitSize
    (p ∘ e0.symm)
  change (M : Complex) *
      (((∑ e : Fin (2 ^ n) ↪ XorSpace n,
          checkerProduct (fun i => rows (p i)) e) /
        (Fintype.card (Fin (2 ^ n) ↪ XorSpace n) : Real) : Real) : Complex) = _
  push_cast
  rw [hsum, hcardEmb, hcardPerm]
  change (M : Complex) * ((K : Complex) * _ / ((K * M : Nat) : Complex)) = _
  push_cast
  field_simp [hK, hM]

/-! ## Instantiation at one exact XOR row profile -/

/-- The distinct Walsh characters occurring in a row profile. -/
def profileSupport {n : Nat} (s : Sym (XorSpace n) (2 ^ n)) :=
  s.1.toFinset

instance {n : Nat} (s : Sym (XorSpace n) (2 ^ n)) :
    Fintype (profileSupport s) := inferInstance

instance {n : Nat} (s : Sym (XorSpace n) (2 ^ n)) :
    DecidableEq (profileSupport s) := inferInstance

/-- Inclusion of the support into the full character group. -/
def profileRows {n : Nat} (s : Sym (XorSpace n) (2 ^ n)) :
    profileSupport s → XorSpace n := Subtype.val

lemma profileRows_injective {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    Function.Injective (profileRows s) := Subtype.val_injective

/-- The canonical row enumeration, with its codomain restricted to the
characters that actually occur. -/
def profileLabel {n : Nat} (s : Sym (XorSpace n) (2 ^ n)) :
    Fin (2 ^ n) → profileSupport s := fun i =>
  ⟨rowSymRepresentative s i, by
    change rowSymRepresentative s i ∈ s.1.toFinset
    rw [Multiset.mem_toFinset]
    rw [← rowMultiset_rowSymRepresentative s]
    unfold rowMultiset
    simp⟩

@[simp]
lemma profileRows_profileLabel {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) (i : Fin (2 ^ n)) :
    profileRows s (profileLabel s i) = rowSymRepresentative s i := rfl

/-- One fixed enumeration of the XOR group. -/
noncomputable def finXorEquiv (n : Nat) : Fin (2 ^ n) ≃ XorSpace n :=
  Fintype.equivOfCardEq (by simp [card_xorSpace])

lemma histogram_sum {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (p : α → ι) :
    ∑ i : ι, Fintype.card {x : α // p x = i} = Fintype.card α := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv p)

lemma histogramOrbitSize_eq_multinomial
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (p : α → ι) :
    histogramOrbitSize p = Nat.multinomial Finset.univ
      (fun i : ι => Fintype.card {x : α // p x = i}) := by
  let m : ι → Nat := fun i => Fintype.card {x : α // p x = i}
  have hfact : Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial :=
    Fintype.card_perm
  have horbit := card_perm_eq_stabilizer_mul_histogramOrbitSize p
  have hmulti := Nat.multinomial_spec (s := (Finset.univ : Finset ι)) m
  have hm_sum : ∑ i, m i = Fintype.card α := histogram_sum p
  have hstab_pos : 0 < ∏ i : ι, (m i).factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hstab_pos
  calc
    (∏ i : ι, (m i).factorial) * histogramOrbitSize p =
        Fintype.card (Equiv.Perm α) := horbit.symm
    _ = (Fintype.card α).factorial := hfact
    _ = (∑ i, m i).factorial := by rw [hm_sum]
    _ = (∏ i ∈ (Finset.univ : Finset ι), (m i).factorial) *
          Nat.multinomial Finset.univ m := hmulti.symm
    _ = (∏ i : ι, (m i).factorial) * Nat.multinomial Finset.univ m := by simp

lemma functionHistogram_eq_equivFunOnFinite_symm_fiberCard
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (p : α → ι) :
    functionHistogram p = Finsupp.equivFunOnFinite.symm
      (fun i : ι => Fintype.card {x : α // p x = i}) := by
  ext i
  rw [functionHistogram_apply]
  simp [Fintype.card_subtype]

lemma radiusMonomial_equivFunOnFinite_symm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Real) (a : ι → Nat) :
    radiusMonomial r (Finsupp.equivFunOnFinite.symm a) =
      ∏ i : ι, (r i : Complex) ^ a i := by
  unfold radiusMonomial
  rw [Finsupp.prod_fintype _ _ (by simp)]
  rfl

lemma countPerms_eq_support_multinomial
    {A : Type*} [DecidableEq A] (s : Multiset A) :
    s.countPerms = Nat.multinomial (Finset.univ : Finset s.toFinset)
      (fun i : s.toFinset => s.count (i : A)) := by
  unfold Multiset.countPerms
  rw [Finsupp.multinomial_eq, Multiset.toFinsupp_support]
  unfold Nat.multinomial
  have hsum : (∑ x : s.toFinset, s.count (x : A)) = s.card := by
    calc
      ∑ x : s.toFinset, s.count (x : A) =
          ∑ a ∈ s.toFinset, s.count a := by
            simpa only using
              Finset.sum_attach s.toFinset (fun a => s.count a)
      _ = s.card := s.toFinset_sum_count_eq
  have hprod : (∏ x : s.toFinset, (s.count (x : A)).factorial) =
      ∏ a ∈ s.toFinset, (s.count a).factorial := by
    simpa using Finset.prod_attach s.toFinset
      (fun a => (s.count a).factorial)
  simp only [Multiset.toFinsupp_apply]
  rw [hsum, hprod]
  rw [Multiset.toFinset_sum_count_eq]

def profileOccupancy {n : Nat} (s : Sym (XorSpace n) (2 ^ n))
    (i : profileSupport s) : Nat := s.1.count (i : XorSpace n)

lemma profileFiberCard_eq_occupancy {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) (i : profileSupport s) :
    Fintype.card {x : XorSpace n //
        (profileLabel s ∘ (finXorEquiv n).symm) x = i} =
      profileOccupancy s i := by
  have hreindex :
      Fintype.card {x : XorSpace n //
          (profileLabel s ∘ (finXorEquiv n).symm) x = i} =
        Fintype.card {j : Fin (2 ^ n) // profileLabel s j = i} := by
    exact Fintype.card_congr
      (Equiv.subtypeEquiv (finXorEquiv n).symm (fun _ => Iff.rfl))
  rw [hreindex, Fintype.card_subtype]
  unfold profileOccupancy
  rw [← rowMultiset_rowSymRepresentative s]
  rw [count_rowMultiset]
  unfold rowMultiplicity
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Subtype.ext_iff

lemma profileOccupancy_sum {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    ∑ i : profileSupport s, profileOccupancy s i = 2 ^ n := by
  rw [show (∑ i : profileSupport s, profileOccupancy s i) =
      ∑ i : profileSupport s,
        Fintype.card {x : XorSpace n //
          (profileLabel s ∘ (finXorEquiv n).symm) x = i} by
    apply Finset.sum_congr rfl
    intro i _hi
    exact (profileFiberCard_eq_occupancy s i).symm]
  rw [histogram_sum]
  simp [card_xorSpace]

lemma functionHistogram_profileLabel {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    functionHistogram (profileLabel s ∘ (finXorEquiv n).symm) =
      Finsupp.equivFunOnFinite.symm (profileOccupancy s) := by
  rw [functionHistogram_eq_equivFunOnFinite_symm_fiberCard]
  congr 1
  funext i
  exact profileFiberCard_eq_occupancy s i

lemma profileHistogramOrbitSize_eq_countPerms {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    histogramOrbitSize (profileLabel s ∘ (finXorEquiv n).symm) =
      s.1.countPerms := by
  rw [histogramOrbitSize_eq_multinomial,
    countPerms_eq_support_multinomial]
  congr 1
  funext i
  exact profileFiberCard_eq_occupancy s i

theorem profile_countPerms_mul_checkerCorrelation_eq_coeff {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    ((s.1.countPerms : Nat) : Complex) *
        (checkerCorrelation (rowSymRepresentative s) : Complex) =
      MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm (profileOccupancy s))
        (characterPartitionPolynomial n (profileRows s)) := by
  have h := histogramOrbitSize_mul_checkerCorrelation_eq_coeff
    (profileRows s) (profileLabel s) (finXorEquiv n)
  rw [profileHistogramOrbitSize_eq_countPerms,
    functionHistogram_profileLabel] at h
  simpa only [profileRows_profileLabel] using h

lemma sq_prod_sqrt_pow
    {J : Type*} [Fintype J] (p : J → Real) (hp : ∀ j, 0 ≤ p j)
    (d : J → Nat) :
    (∏ j, (Real.sqrt (p j)) ^ d j) ^ 2 = ∏ j, (p j) ^ d j := by
  rw [← Finset.prod_pow (Finset.univ : Finset J) 2]
  apply Finset.prod_congr rfl
  intro j _
  rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (hp j)]

lemma card_piAntidiag_nat_eq_choose {I : Type*} [DecidableEq I]
    (s : Finset I) (N : Nat) :
    (s.piAntidiag N).card = (s.card + N - 1).choose N := by
  rw [← Finset.card_finsuppAntidiag_nat_eq_choose (s := s) N]
  simp [Finset.finsuppAntidiag]

/-- The integer `m` is a mode of the sequence `m^t / t!`. -/
lemma pow_mul_factorial_le_at_mode (m t : Nat) :
    m ^ t * m.factorial ≤ m ^ m * t.factorial := by
  rcases le_total m t with hmt | htm
  · have htail := Nat.factorial_mul_pow_sub_le_factorial hmt
    calc
      m ^ t * m.factorial = (m ^ m * m ^ (t - m)) * m.factorial := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hmt]
      _ = m ^ m * (m.factorial * m ^ (t - m)) := by ac_rfl
      _ ≤ m ^ m * t.factorial := Nat.mul_le_mul_left _ htail
  · have hdesc := Nat.descFactorial_le_pow m (m - t)
    have hfactorial : m.factorial = t.factorial * m.descFactorial (m - t) := by
      have h := Nat.factorial_mul_descFactorial
        (n := m) (k := m - t) (Nat.sub_le _ _)
      rw [Nat.sub_sub_self htm] at h
      exact h.symm
    rw [hfactorial]
    calc
      m ^ t * (t.factorial * m.descFactorial (m - t)) ≤
          m ^ t * (t.factorial * m ^ (m - t)) := by gcongr
      _ = (m ^ t * m ^ (m - t)) * t.factorial := by ac_rfl
      _ = m ^ m * t.factorial := by
        rw [← Nat.pow_add, Nat.add_sub_of_le htm]

lemma pow_div_factorial_le_at_mode (m t : Nat) :
    (m : Real) ^ t / t.factorial ≤ (m : Real) ^ m / m.factorial := by
  rw [div_le_div_iff₀ (by positivity : (0 : Real) < t.factorial)
    (by positivity : (0 : Real) < m.factorial)]
  exact_mod_cast pow_mul_factorial_le_at_mode m t

lemma prod_pow_div_factorial_le_at_mode
    {J : Type*} [Fintype J] (m t : J → Nat) :
    ∏ i, (m i : Real) ^ t i / (t i).factorial ≤
      ∏ i, (m i : Real) ^ m i / (m i).factorial := by
  exact Finset.prod_le_prod (fun i _ => by positivity)
    (fun i _ => pow_div_factorial_le_at_mode (m i) (t i))

lemma multinomial_mul_prod_pow_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    (m t : J → Nat) (hsum : ∑ i, t i = ∑ i, m i) :
    (Nat.multinomial Finset.univ t : Real) * ∏ i, (m i : Real) ^ t i =
      ((∑ i, m i).factorial : Real) *
        ∏ i, (m i : Real) ^ t i / (t i).factorial := by
  rw [Finset.prod_div_distrib, ← mul_div_assoc]
  have hden : (∏ i, ((t i).factorial : Real)) ≠ 0 := by positivity
  apply (eq_div_iff hden).2
  have hspec := Nat.multinomial_spec (s := (Finset.univ : Finset J)) t
  calc
    _ = ((∏ i, ((t i).factorial : Real)) *
          (Nat.multinomial Finset.univ t : Real)) *
            ∏ i, (m i : Real) ^ t i := by ring
    _ = (((∑ i, t i).factorial : Nat) : Real) *
          ∏ i, (m i : Real) ^ t i := by
            norm_cast
            rw [← hspec]
    _ = ((∑ i, m i).factorial : Real) *
          ∏ i, (m i : Real) ^ t i := by rw [hsum]

lemma multinomial_mul_prod_pow_le_at_mode
    {J : Type*} [Fintype J] [DecidableEq J]
    (m t : J → Nat) (hsum : ∑ i, t i = ∑ i, m i) :
    (Nat.multinomial Finset.univ t : Real) * ∏ i, (m i : Real) ^ t i ≤
      (Nat.multinomial Finset.univ m : Real) * ∏ i, (m i : Real) ^ m i := by
  rw [multinomial_mul_prod_pow_eq m t hsum,
    multinomial_mul_prod_pow_eq m m rfl]
  exact mul_le_mul_of_nonneg_left
    (prod_pow_div_factorial_le_at_mode m t) (by positivity)

lemma prod_normalized_pow_eq
    {J : Type*} [Fintype J] (m t : J → Nat) (N : Nat) :
    ∏ i, ((m i : Real) / N) ^ t i =
      (∏ i, (m i : Real) ^ t i) / (N : Real) ^ ∑ i, t i := by
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

lemma multinomial_probability_le_at_mode
    {J : Type*} [Fintype J] [DecidableEq J]
    (m t : J → Nat) (N : Nat) (hN : 0 < N)
    (hm_sum : ∑ i, m i = N) (ht_sum : ∑ i, t i = N) :
    (Nat.multinomial Finset.univ t : Real) *
        ∏ i, ((m i : Real) / N) ^ t i ≤
      (Nat.multinomial Finset.univ m : Real) *
        ∏ i, ((m i : Real) / N) ^ m i := by
  rw [prod_normalized_pow_eq, prod_normalized_pow_eq, ht_sum, hm_sum,
    ← mul_div_assoc, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right
  exact multinomial_mul_prod_pow_le_at_mode m t
    (ht_sum.trans hm_sum.symm)
  positivity

lemma multinomial_mode_lower_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (m : J → Nat) (N : Nat) (hN : 0 < N)
    (hm_sum : ∑ i, m i = N) :
    1 ≤ (((Fintype.card J + N - 1).choose N : Nat) : Real) *
      ((Nat.multinomial Finset.univ m : Real) *
        ∏ i, ((m i : Real) / N) ^ m i) := by
  let p : J → Real := fun i => (m i : Real) / N
  have hp_sum : ∑ i, p i = 1 := by
    simp only [p, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hm_sum]
    field_simp
  have hmulti := Finset.sum_pow_eq_sum_piAntidiag
    (s := (Finset.univ : Finset J)) p N
  have hone :
      1 = ∑ t ∈ Finset.piAntidiag (Finset.univ : Finset J) N,
        (Nat.multinomial Finset.univ t : Real) * ∏ i, p i ^ t i := by
    simpa [hp_sum] using hmulti
  calc
    1 = ∑ t ∈ Finset.piAntidiag (Finset.univ : Finset J) N,
        (Nat.multinomial Finset.univ t : Real) * ∏ i, p i ^ t i := hone
    _ ≤ ∑ _t ∈ Finset.piAntidiag (Finset.univ : Finset J) N,
        ((Nat.multinomial Finset.univ m : Real) *
          ∏ i, ((m i : Real) / N) ^ m i) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_piAntidiag] at ht
          simpa only [p] using
            multinomial_probability_le_at_mode m t N hN hm_sum ht.1
    _ = ((Finset.piAntidiag (Finset.univ : Finset J) N).card : Real) *
        ((Nat.multinomial Finset.univ m : Real) *
          ∏ i, ((m i : Real) / N) ^ m i) := by
          simp [nsmul_eq_mul]
    _ = (((Fintype.card J + N - 1).choose N : Nat) : Real) *
        ((Nat.multinomial Finset.univ m : Real) *
          ∏ i, ((m i : Real) / N) ^ m i) := by
          rw [card_piAntidiag_nat_eq_choose]
          simp

lemma histogramOrbitSize_weight_mode_lower_bound
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (p : α → ι) (hα : 0 < Fintype.card α) :
    1 ≤ (((Fintype.card ι + Fintype.card α - 1).choose
            (Fintype.card α) : Nat) : Real) *
      (histogramOrbitSize p : Real) *
        ∏ i : ι,
          ((Fintype.card {x : α // p x = i} : Real) /
            Fintype.card α) ^ Fintype.card {x : α // p x = i} := by
  let m : ι → Nat := fun i => Fintype.card {x : α // p x = i}
  have hm_sum : ∑ i, m i = Fintype.card α := histogram_sum p
  have hmode := multinomial_mode_lower_bound m (Fintype.card α) hα hm_sum
  rw [← histogramOrbitSize_eq_multinomial p] at hmode
  simpa only [m, mul_assoc] using hmode

/-- Pure algebraic last step of the square-root cancellation argument. -/
lemma finish_square_root_bound
    {C M : Nat} {c weight : Real}
    (hC : 0 < C) (hw : 0 ≤ weight)
    (henergy : (C : Real) ^ 2 * c ^ 2 * weight ≤ 1)
    (hmode : 1 ≤ (M : Real) * (C : Real) * weight) :
    (C : Real) * c ^ 2 ≤ M := by
  have hC0 : (0 : Real) < C := by exact_mod_cast hC
  have hwpos : 0 < weight := lt_of_le_of_ne hw <| by
    intro hw0
    subst weight
    norm_num at hmode
  calc
    (C : Real) * c ^ 2 =
        ((C : Real) ^ 2 * c ^ 2 * weight) / ((C : Real) * weight) := by
          field_simp [ne_of_gt hC0, ne_of_gt hwpos]
    _ ≤ 1 / ((C : Real) * weight) := by gcongr
    _ ≤ M := by
      rw [div_le_iff₀ (mul_pos hC0 hwpos)]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmode

theorem histogramOrbitSize_checkerCorrelation_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (p : Fin (2 ^ n) → ι) (e0 : Fin (2 ^ n) ≃ XorSpace n) :
    (histogramOrbitSize (p ∘ e0.symm) : Real) ^ 2 *
        checkerCorrelation (fun i => rows (p i)) ^ 2 *
        (∏ i : ι,
          ((Fintype.card {x : XorSpace n // (p ∘ e0.symm) x = i} : Real) /
            (2 ^ n : Nat)) ^
              Fintype.card {x : XorSpace n // (p ∘ e0.symm) x = i}) ≤ 1 := by
  let label : XorSpace n → ι := p ∘ e0.symm
  let a : ι → Nat := fun i => Fintype.card {x : XorSpace n // label x = i}
  let C : Nat := histogramOrbitSize label
  let c : Real := checkerCorrelation (fun i => rows (p i))
  have ha : ∑ i, a i = 2 ^ n := by
    rw [histogram_sum label]
    exact card_xorSpace n
  have hd : functionHistogram label = Finsupp.equivFunOnFinite.symm a :=
    functionHistogram_eq_equivFunOnFinite_symm_fiberCard label
  have hcoeff := histogramOrbitSize_mul_checkerCorrelation_eq_coeff rows p e0
  change (C : Complex) * (c : Complex) = _ at hcoeff
  rw [hd] at hcoeff
  have hnorm := norm_characterPartitionCoefficient_mul_radius_le hrows a ha
  dsimp only at hnorm
  rw [← hcoeff, radiusMonomial_equivFunOnFinite_symm] at hnorm
  have hpow_nonneg :
      (0 : Real) ≤ ((2 ^ n : Nat) : Real) ^ (2 ^ n) := by positivity
  have hsq :
      ‖((C : Complex) * (c : Complex)) *
          ∏ i : ι, ((Real.sqrt (a i) : Real) : Complex) ^ a i‖ ^ 2 ≤
        ((2 ^ n : Nat) : Real) ^ (2 ^ n) := by
    nlinarith [Real.sq_sqrt hpow_nonneg,
      norm_nonneg (((C : Complex) * (c : Complex)) *
        ∏ i : ι, ((Real.sqrt (a i) : Real) : Complex) ^ a i)]
  have hleft :
      ‖((C : Complex) * (c : Complex)) *
          ∏ i : ι, ((Real.sqrt (a i) : Real) : Complex) ^ a i‖ ^ 2 =
        (C : Real) ^ 2 * c ^ 2 * ∏ i : ι, (a i : Real) ^ a i := by
    rw [norm_mul, norm_mul, norm_prod]
    simp only [Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    simp_rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow, mul_pow, sq_abs,
      sq_prod_sqrt_pow (fun i => (a i : Real)) (fun _ => by positivity) a]
  rw [hleft] at hsq
  have hN : (0 : Real) < (2 ^ n : Nat) := by positivity
  change (C : Real) ^ 2 * c ^ 2 *
      (∏ i : ι, ((a i : Real) / (2 ^ n : Nat)) ^ a i) ≤ 1
  rw [prod_normalized_pow_eq]
  rw [ha]
  rw [show (C : Real) ^ 2 * c ^ 2 *
      ((∏ i : ι, (a i : Real) ^ a i) / ((2 ^ n : Nat) : Real) ^ (2 ^ n)) =
      ((C : Real) ^ 2 * c ^ 2 * (∏ i : ι, (a i : Real) ^ a i)) /
        ((2 ^ n : Nat) : Real) ^ (2 ^ n) by ring]
  rw [div_le_one (pow_pos hN _)]
  exact hsq

theorem histogramOrbitSize_mul_checkerCorrelation_sq_le_choose
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    {rows : ι → XorSpace n} (hrows : Function.Injective rows)
    (p : Fin (2 ^ n) → ι) (e0 : Fin (2 ^ n) ≃ XorSpace n) :
    (histogramOrbitSize (p ∘ e0.symm) : Real) *
        checkerCorrelation (fun i => rows (p i)) ^ 2 ≤
      (((2 ^ n + Fintype.card ι - 1).choose
        (Fintype.card ι - 1) : Nat) : Real) := by
  let label : XorSpace n → ι := p ∘ e0.symm
  let C : Nat := histogramOrbitSize label
  let c : Real := checkerCorrelation (fun i => rows (p i))
  let weight : Real :=
    ∏ i : ι,
      ((Fintype.card {x : XorSpace n // label x = i} : Real) /
        Fintype.card (XorSpace n)) ^
          Fintype.card {x : XorSpace n // label x = i}
  have hC : 0 < C := histogramOrbitSize_pos label
  have henergy : (C : Real) ^ 2 * c ^ 2 * weight ≤ 1 := by
    simpa only [C, c, weight, card_xorSpace] using
      histogramOrbitSize_checkerCorrelation_energy hrows p e0
  have hmode := histogramOrbitSize_weight_mode_lower_bound label
    (by simp [card_xorSpace])
  have hraw :
      (C : Real) * c ^ 2 ≤
        (((Fintype.card ι + 2 ^ n - 1).choose (2 ^ n) : Nat) : Real) := by
    apply finish_square_root_bound hC (by positivity) henergy
    simpa only [C, weight, card_xorSpace, mul_assoc] using hmode
  have hk : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨p 0⟩
  have hNnat : 0 < 2 ^ n := by positivity
  have hchoose :
      (Fintype.card ι + 2 ^ n - 1).choose (2 ^ n) =
        (2 ^ n + Fintype.card ι - 1).choose (Fintype.card ι - 1) := by
    have htop : Fintype.card ι + 2 ^ n - 1 =
        2 ^ n + (Fintype.card ι - 1) := by omega
    rw [htop, Nat.choose_symm_add]
    congr 2 <;> omega
  change (C : Real) * c ^ 2 ≤ _
  rw [← hchoose]
  exact hraw

/-- The exact square-root profile estimate.  Its only profile parameter is
the number of distinct rows; no ambient-size labels are charged. -/
theorem countPerms_mul_checkerCorrelation_sq_le_choose {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    (s.1.countPerms : Real) *
        checkerCorrelation (rowSymRepresentative s) ^ 2 ≤
      (((2 ^ n + s.1.toFinset.card - 1).choose
        (s.1.toFinset.card - 1) : Nat) : Real) := by
  have h := histogramOrbitSize_mul_checkerCorrelation_sq_le_choose
    (profileRows_injective s) (profileLabel s) (finXorEquiv n)
  rw [profileHistogramOrbitSize_eq_countPerms] at h
  simpa only [profileRows_profileLabel, Fintype.card_coe] using h

/-- The weak-composition count appearing in the exact profile estimate. -/
def profileChooseBound {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) : Nat :=
  (2 ^ n + s.1.toFinset.card - 1).choose (s.1.toFinset.card - 1)

theorem countPerms_mul_fullFourier_sq_le_profileChooseBound {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    (s.1.countPerms : Real) *
        (fourier (injectionDensity n (2 ^ n))
          (rowSymRepresentative s)) ^ 2 ≤
      profileChooseBound s := by
  have h := countPerms_mul_checkerCorrelation_sq_le_choose s
  have hcoeff :
      fourier (injectionDensity n (2 ^ n)) (rowSymRepresentative s) =
        checkerCorrelation (rowSymRepresentative s) := by
    exact fourier_injectionDensity_eq_average_checkerProduct
      (le_refl (2 ^ n)) (rowSymRepresentative s)
  rw [← hcoeff] at h
  exact h

/-- Cubic contribution allowed by the exact square-root profile estimate. -/
def profileCubicEnvelope {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) : Real :=
  (profileChooseBound s : Real) *
    Real.sqrt ((profileChooseBound s : Real) / (s.1.countPerms : Real))

theorem rowProfileCubicContribution_le_profileCubicEnvelope {n : Nat}
    (s : Sym (XorSpace n) (2 ^ n)) :
    rowProfileCubicContribution n s ≤ profileCubicEnvelope s := by
  let M : Real := s.1.countPerms
  let B : Real := profileChooseBound s
  let c : Real := fourier (injectionDensity n (2 ^ n))
    (rowSymRepresentative s)
  have hMnat : 0 < s.1.countPerms := by
    rw [countPerms_eq_support_multinomial]
    exact Nat.multinomial_pos _ _
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast hMnat
  have hB : 0 ≤ B := by positivity
  have hsq : M * |c| ^ 2 ≤ B := by
    rw [sq_abs]
    exact countPerms_mul_fullFourier_sq_le_profileChooseBound s
  have habs : |c| ≤ Real.sqrt (B / M) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hM]
    simpa [mul_comm] using hsq
  rw [rowProfileCubicContribution_eq_countPerms_mul]
  change M * |c| ^ 3 ≤ B * Real.sqrt (B / M)
  calc
    M * |c| ^ 3 = (M * |c| ^ 2) * |c| := by ring
    _ ≤ B * |c| := mul_le_mul_of_nonneg_right hsq (abs_nonneg c)
    _ ≤ B * Real.sqrt (B / M) := mul_le_mul_of_nonneg_left habs hB

/-- Explicit finite sum left after the torus coefficient estimate. -/
def highEntropyProfileCubicEnvelope (n : Nat) : Real :=
  ∑ s : Sym (XorSpace n) (2 ^ n),
    if IsThreeQuarterSeparatedProfile s then profileCubicEnvelope s else 0

theorem highEntropyFullCubicMass_le_profileCubicEnvelope (n : Nat) :
    highEntropyFullCubicMass n ≤ highEntropyProfileCubicEnvelope n := by
  rw [highEntropyFullCubicMass_eq_profileCubicMass]
  unfold highEntropyProfileCubicMass highEntropyProfileCubicEnvelope
  apply Finset.sum_le_sum
  intro s _hs
  by_cases hsep : IsThreeQuarterSeparatedProfile s
  · simp only [hsep, if_true]
    exact rowProfileCubicContribution_le_profileCubicEnvelope s
  · simp [hsep]

end RandomSystems.SoP.XORComplement
