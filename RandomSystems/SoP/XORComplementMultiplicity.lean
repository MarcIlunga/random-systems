/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementSpectrum
import RandomSystems.SoP.XORBounds

/-!
# Majority quotient for the full-domain XOR SoP residual

This file splits the positive Fourier tail left after exact proxy cancellation
into two disjoint profile types.  A mask with a strict-majority row value is
translated by that value into a mask of support below half the deck.  The
global-shift cross-section makes this an exact reindexing, so no factor is lost.
The only remaining genuinely dense contribution consists of balanced masks,
where no row value occurs more than half the time.

Modes of translated support below three are already proxy modes or have zero
injection coefficient.  Thus the strict-majority contribution starts at
Fourier level three and is governed by the existing Pascal tail estimates.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail
open RandomSystems.SoP.XORBounds

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def rowMultiplicity {n q : Nat} (a : BitMatrix q n)
    (beta : XorSpace n) : Nat :=
  ((Finset.univ : Finset (Fin q)).filter (fun i => a i = beta)).card

theorem rowSupport_add_constantMask {n q : Nat} (a : BitMatrix q n)
    (beta : XorSpace n) :
    rowSupport (a + constantMask beta) =
      (Finset.univ : Finset (Fin q)).filter (fun i => a i ≠ beta) := by
  ext i
  rw [mem_rowSupport]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change a i + beta ≠ 0 ↔ a i ≠ beta
  exact not_congr (xorSpace_add_eq_zero_iff_eq (a i) beta)

theorem level_add_constantMask {n q : Nat} (a : BitMatrix q n)
    (beta : XorSpace n) :
    level (a + constantMask beta) = q - rowMultiplicity a beta := by
  unfold level rowMultiplicity
  rw [rowSupport_add_constantMask]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin q))) (p := fun i => a i = beta)
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  have heq :
      ((Finset.univ : Finset (Fin q)).filter (fun i => ¬a i = beta)).card =
        q - ((Finset.univ : Finset (Fin q)).filter (fun i => a i = beta)).card := by
    omega
  simpa only [ne_eq] using heq

def HasStrictMajority {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∃ beta : XorSpace n, q < 2 * rowMultiplicity a beta

def IsBalancedProfile {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∀ beta : XorSpace n, 2 * rowMultiplicity a beta ≤ q

theorem not_balancedProfile_iff_strictMajority {n q : Nat}
    (a : BitMatrix q n) :
    ¬ IsBalancedProfile a ↔ HasStrictMajority a := by
  unfold IsBalancedProfile HasStrictMajority
  push Not
  rfl

def strictMajorityCoverEnergy (n : Nat) : Real :=
  ∑ beta : XorSpace n,
    ∑ b : AnchoredMask n,
      if 2 ^ n < 2 * rowMultiplicity b.1 beta ∧
          ¬ IsFullProxyMode b.1 then
        fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
      else 0

def balancedAnchoredFourthTail (n : Nat) : Real :=
  ∑ b : AnchoredMask n,
    if IsBalancedProfile b.1 ∧ ¬ IsFullProxyMode b.1 then
      fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
    else 0

theorem anchoredInjectionFourthTail_le_majority_add_balanced (n : Nat) :
    anchoredInjectionFourthTail n ≤
      strictMajorityCoverEnergy n + balancedAnchoredFourthTail n := by
  unfold anchoredInjectionFourthTail strictMajorityCoverEnergy
    balancedAnchoredFourthTail
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _hb
  by_cases hp : IsFullProxyMode b.1
  · simp [hp]
  · by_cases hbal : IsBalancedProfile b.1
    · simp only [hp, not_false_eq_true, hbal, true_and, if_true]
      exact le_add_of_nonneg_left (by positivity)
    · have hmaj : HasStrictMajority b.1 :=
        (not_balancedProfile_iff_strictMajority b.1).mp hbal
      obtain ⟨beta, hbeta⟩ := hmaj
      simp only [hp, not_false_eq_true, hbal, if_false, add_zero,
        and_true]
      have hmem : beta ∈ (Finset.univ : Finset (XorSpace n)) := Finset.mem_univ _
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset (XorSpace n)))
        (f := fun gamma =>
          if 2 ^ n < 2 * rowMultiplicity b.1 gamma then
            fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
          else 0)
        (fun gamma _hgamma => by positivity) hmem
      simpa [hbeta] using hs

def strictLowFullFourthTail (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if 2 * level a < 2 ^ n ∧ ¬ IsFullProxyMode a then
      fourier (injectionDensity n (2 ^ n)) a ^ 4
    else 0

theorem isFullProxyMode_add_constantMask_iff {n : Nat}
    (a : BitMatrix (2 ^ n) n) (beta : XorSpace n) :
    IsFullProxyMode (a + constantMask beta) ↔ IsFullProxyMode a := by
  have hcancel (x : BitMatrix (2 ^ n) n) :
      (x + constantMask beta) + constantMask beta = x := by
    funext i j
    simp [constantMask, add_assoc, CharTwo.add_self_eq_zero]
  have himp (x : BitMatrix (2 ^ n) n) :
      IsFullProxyMode (x + constantMask beta) → IsFullProxyMode x := by
    rintro (hc | hp)
    · left
      obtain ⟨gamma, hgamma⟩ := hc
      refine ⟨gamma + beta, ?_⟩
      calc
        x = (x + constantMask beta) + constantMask beta := (hcancel x).symm
        _ = constantMask gamma + constantMask beta := by rw [hgamma]
        _ = constantMask (gamma + beta) := by
          funext i j
          simp [constantMask]
    · right
      obtain ⟨⟨gamma, ⟨p, ⟨alpha, halpha⟩⟩⟩, hmode⟩ := hp
      refine ⟨⟨gamma + beta, ⟨p, ⟨alpha, halpha⟩⟩⟩, ?_⟩
      calc
        x = (x + constantMask beta) + constantMask beta := (hcancel x).symm
        _ = translatedPairParameterToMask
              ⟨gamma, ⟨p, ⟨alpha, halpha⟩⟩⟩ + constantMask beta := by
          rw [hmode]
        _ = translatedPairParameterToMask
              ⟨gamma + beta, ⟨p, ⟨alpha, halpha⟩⟩⟩ := by
          funext i j
          simp [translatedPairParameterToMask, constantMask]
          abel
  constructor
  · exact himp a
  · intro h
    apply himp (a + constantMask beta)
    simpa only [hcancel] using h

theorem strictMajorityCoverEnergy_eq_strictLowFullFourthTail (n : Nat) :
    strictMajorityCoverEnergy n = strictLowFullFourthTail n := by
  unfold strictMajorityCoverEnergy strictLowFullFourthTail
  calc
    (∑ beta : XorSpace n,
        ∑ b : AnchoredMask n,
          if 2 ^ n < 2 * rowMultiplicity b.1 beta ∧
              ¬IsFullProxyMode b.1 then
            fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
          else 0) =
        ∑ z : XorSpace n × AnchoredMask n,
          if 2 ^ n < 2 * rowMultiplicity z.2.1 z.1 ∧
              ¬IsFullProxyMode z.2.1 then
            fourier (injectionDensity n (2 ^ n)) z.2.1 ^ 4
          else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : BitMatrix (2 ^ n) n,
          if 2 * level a < 2 ^ n ∧ ¬IsFullProxyMode a then
            fourier (injectionDensity n (2 ^ n)) a ^ 4
          else 0 := by
      apply Fintype.sum_equiv (globalShiftOrbitEquiv n)
      rintro ⟨beta, b⟩
      change
        (if 2 ^ n < 2 * rowMultiplicity b.1 beta ∧
            ¬IsFullProxyMode b.1 then
          fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
        else 0) =
          if 2 * level (b.1 + constantMask beta) < 2 ^ n ∧
              ¬IsFullProxyMode (b.1 + constantMask beta) then
            fourier (injectionDensity n (2 ^ n))
              (b.1 + constantMask beta) ^ 4
          else 0
      rw [level_add_constantMask]
      rw [isFullProxyMode_add_constantMask_iff]
      have hcoef := fourier_injection_density_sq_add_constant_mask_full b.1 beta
      have hmult : rowMultiplicity b.1 beta ≤ 2 ^ n := by
        unfold rowMultiplicity
        simpa using Finset.card_le_card
          (Finset.filter_subset (fun i : Fin (2 ^ n) => b.1 i = beta)
            (Finset.univ : Finset (Fin (2 ^ n))))
      by_cases hmajor : 2 ^ n < 2 * rowMultiplicity b.1 beta
      · have hlevel : 2 * (2 ^ n - rowMultiplicity b.1 beta) < 2 ^ n := by omega
        by_cases hp : IsFullProxyMode b.1
        · simp [hmajor, hlevel, hp]
        · simp only [hmajor, hlevel, hp, not_false_eq_true, and_self, if_true]
          nlinarith [sq_nonneg (fourier (injectionDensity n (2 ^ n))
            (b.1 + constantMask beta))]
      · have hlevel : ¬2 * (2 ^ n - rowMultiplicity b.1 beta) < 2 ^ n := by omega
        simp [hmajor, hlevel]

theorem fourier_full_eq_zero_of_level_lt_three_of_not_proxy {n : Nat}
    (a : BitMatrix (2 ^ n) n) (hlevel : level a < 3)
    (hproxy : ¬IsFullProxyMode a) :
    fourier (injectionDensity n (2 ^ n)) a = 0 := by
  interval_cases h : level a
  · have ha : a = 0 := (level_eq_zero_iff a).mp h
    exfalso
    apply hproxy
    left
    refine ⟨0, ?_⟩
    rw [ha]
    rfl
  · exact fourier_injectionDensity_of_level_eq_one (le_refl (2 ^ n)) a h
  · rw [fourier_injectionDensity_of_level_eq_two (le_refl (2 ^ n)) a h]
    by_cases heq : supportRowsEqual a
    · exfalso
      apply hproxy
      right
      let A : EqualLevelTwoMask n (2 ^ n) := ⟨a, h, heq⟩
      obtain ⟨z, hz⟩ := pairMaskParameterToMask_surjective A
      refine ⟨⟨0, z⟩, ?_⟩
      have hmask : pairMask z.1 z.2.1 = a :=
        congrArg Subtype.val hz
      change a = constantMask 0 + pairMask z.1 z.2.1
      rw [hmask]
      have hzero : (constantMask 0 : BitMatrix (2 ^ n) n) = 0 := by
        rfl
      rw [hzero, zero_add]
    · rw [if_neg heq]

def strictLowLevelFourthTail (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if 3 ≤ level a ∧ 2 * level a < 2 ^ n then
      fourier (injectionDensity n (2 ^ n)) a ^ 4
    else 0

theorem strictLowFullFourthTail_le_strictLowLevelFourthTail (n : Nat) :
    strictLowFullFourthTail n ≤ strictLowLevelFourthTail n := by
  unfold strictLowFullFourthTail strictLowLevelFourthTail
  apply Finset.sum_le_sum
  intro a _ha
  by_cases hlow : 2 * level a < 2 ^ n
  · by_cases hp : IsFullProxyMode a
    · by_cases h3 : 3 ≤ level a <;> simp [hp, h3, hlow] <;> positivity
    · by_cases h3 : 3 ≤ level a
      · simp [hlow, hp, h3]
      · have hz := fourier_full_eq_zero_of_level_lt_three_of_not_proxy
          a (by omega) hp
        simp [hlow, hp, h3, hz]
  · simp [hlow]

theorem strictLowLevelFourthTail_eq_sum_levels (n : Nat) :
    strictLowLevelFourthTail n =
      ∑ k ∈ Finset.range (2 ^ n + 1),
        if 3 ≤ k ∧ 2 * k < 2 ^ n then injectionLevelEnergy n (2 ^ n) k
        else 0 := by
  unfold strictLowLevelFourthTail
  rw [sum_eq_sum_levels]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hcond : 3 ≤ k ∧ 2 * k < 2 ^ n
  · rw [if_pos hcond]
    unfold injectionLevelEnergy
    apply Finset.sum_congr rfl
    intro a ha
    have hlevel : level a = k := by simpa using ha
    rw [hlevel, if_pos hcond]
  · rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro a ha
    have hlevel : level a = k := by simpa using ha
    rw [hlevel, if_neg hcond]

end RandomSystems.SoP.XORComplement
