/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.SoP2

/-!
# The Dutta--Nandi--Saha mirror theorem, on its published XOR carrier

This file deliberately fixes the carrier to `n` bits, represented by
`Fin n -> ZMod 2`.  The theorem proved here is the independent-permutation
case of Dutta--Nandi--Saha (ePrint 2020/669, Lemma 8), with its published
assumptions `7 <= n` and `17 * q <= 2^n`.

The group-general predicate in `SumOfPermutationsOptimal.lean` remains a
separate open generalization.  In particular, no step in this file silently
promotes an XOR identity to an arbitrary finite abelian group.
-/

noncomputable section

namespace RandomSystems.SoP.DNS

/-- The published DNS carrier: `n` bits with componentwise XOR. -/
abbrev XorSpace (n : Nat) := Fin n -> ZMod 2

@[simp]
theorem card_xorSpace (n : Nat) : Fintype.card (XorSpace n) = 2 ^ n := by
  simp [XorSpace]

/-- XOR is self-inverse on the DNS carrier.  Kept explicit because this is
exactly the characteristic-two fact that the group-general reach theorem may
not use without a replacement argument. -/
theorem add_self_eq_zero (n : Nat) (x : XorSpace n) : x + x = 0 := by
  funext i
  change x i + x i = 0
  rw [<- two_nsmul]
  rw [<- Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  rw [CharP.cast_eq_zero (ZMod 2) 2]
  simp

/-! ## DNS's recursive-inequality engine

The paper uses the numerical ratio `1/(4e)`.  Under `17*q <= 2^n`, the
normalized differential terms actually satisfy the stronger rational bound
`(1/15)^d`.  Using the rational bound avoids importing transcendental
estimates and gives a shorter Pascal-tree argument.

The weight `B(d,l) = (1/15)^d * 3^l` contracts by

* `1/3` on the `(d,l-1)` branch, and
* `1/5` on the `(d+1,l+1)` branch.

Their sum is `8/15`.  Iterating the recurrence therefore leaves a geometric
terminal term plus at most three times the per-level error. -/

/-- A rational, slightly stronger version of DNS Lemma 1. -/
theorem recursive_inequality
    (a : Nat -> Nat -> Real) (c : Real) (hc : 0 <= c)
    (hinit : forall d l, a d l <= (1 / 15 : Real) ^ d)
    (hrec_zero : forall d,
      a d 0 <= a (d + 1) 1 + c * (1 / 15 : Real) ^ d)
    (hrec_succ : forall d l,
      a d (l + 1) <=
        a d l + a (d + 1) (l + 2) + c * (1 / 15 : Real) ^ d)
    (depth : Nat) :
    a 0 0 <= (8 / 15 : Real) ^ depth + 3 * c := by
  let r : Real := 1 / 15
  let s : Real := 8 / 15
  have hr : 0 <= r := by dsimp [r]; positivity
  have hs : 0 <= s := by dsimp [s]; positivity
  have hclaim : forall t d l, l <= d ->
      a d l <= r ^ d * 3 ^ l * (s ^ t + 3 * c) := by
    intro t
    induction t with
    | zero =>
        intro d l _hld
        have hpow3 : (1 : Real) <= 3 ^ l :=
          one_le_pow₀ (by norm_num : (1 : Real) <= 3)
        have hrd : 0 <= r ^ d := pow_nonneg hr _
        have hfactor : 1 <= (3 : Real) ^ l * (1 + 3 * c) := by
          nlinarith [pow_nonneg (by norm_num : (0 : Real) <= 3) l]
        calc
          a d l <= r ^ d := by simpa [r] using hinit d l
          _ <= r ^ d * (3 ^ l * (1 + 3 * c)) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hrd
          _ = r ^ d * 3 ^ l * (s ^ 0 + 3 * c) := by ring
    | succ t ih =>
        intro d l hld
        have hX : 0 <= s ^ t + 3 * c := by positivity
        have hrd : 0 <= r ^ d := pow_nonneg hr _
        cases l with
        | zero =>
            have hchild := ih (d + 1) 1 (by omega)
            have hscale :
                r ^ (d + 1) * 3 ^ 1 * (s ^ t + 3 * c) =
                  r ^ d * ((1 : Real) / 5) * (s ^ t + 3 * c) := by
              dsimp [r]
              rw [pow_succ]
              ring
            have hstep :
                a d 0 <= r ^ d * ((1 : Real) / 5) * (s ^ t + 3 * c) +
                    c * r ^ d := by
              calc
                a d 0 <= a (d + 1) 1 + c * r ^ d := by
                  simpa [r] using hrec_zero d
                _ <= (r ^ (d + 1) * 3 ^ 1 * (s ^ t + 3 * c)) +
                    c * r ^ d := by gcongr
                _ = _ := by rw [hscale]
            have hcoef :
                ((1 : Real) / 5) * (s ^ t + 3 * c) + c <=
                  s * (s ^ t + 3 * c) + c := by
              gcongr
              dsimp [s]
              norm_num
            calc
              a d 0 <= r ^ d * ((1 : Real) / 5) * (s ^ t + 3 * c) +
                    c * r ^ d := hstep
              _ = r ^ d * (((1 : Real) / 5) * (s ^ t + 3 * c) + c) := by ring
              _ <= r ^ d * (s * (s ^ t + 3 * c) + c) :=
                mul_le_mul_of_nonneg_left hcoef hrd
              _ <= r ^ d * (s ^ (t + 1) + 3 * c) := by
                apply mul_le_mul_of_nonneg_left _ hrd
                rw [pow_succ]
                dsimp [s]
                nlinarith
              _ = r ^ d * 3 ^ 0 * (s ^ (t + 1) + 3 * c) := by ring
        | succ l =>
            have hld' : l <= d := by omega
            have hrightIndex : l + 2 <= d + 1 := by omega
            have hleft := ih d l hld'
            have hright := ih (d + 1) (l + 2) hrightIndex
            have hcombine :
                r ^ d * 3 ^ l * (s ^ t + 3 * c) +
                    r ^ (d + 1) * 3 ^ (l + 2) * (s ^ t + 3 * c) =
                  r ^ d * 3 ^ (l + 1) * (s * (s ^ t + 3 * c)) := by
              dsimp [r, s]
              rw [pow_succ r d, pow_succ (3 : Real) l,
                show l + 2 = (l + 1) + 1 by omega,
                pow_succ (3 : Real) (l + 1)]
              ring
            have hparent : 0 <= r ^ d * 3 ^ (l + 1) := by positivity
            have herr :
                c * r ^ d <= c * (r ^ d * 3 ^ (l + 1)) := by
              apply mul_le_mul_of_nonneg_left _ hc
              have hp3 : (1 : Real) <= 3 ^ (l + 1) :=
                one_le_pow₀ (by norm_num : (1 : Real) <= 3)
              nlinarith
            calc
              a d (l + 1) <= a d l + a (d + 1) (l + 2) + c * r ^ d := by
                simpa [r] using hrec_succ d l
              _ <= (r ^ d * 3 ^ l * (s ^ t + 3 * c) +
                    r ^ (d + 1) * 3 ^ (l + 2) * (s ^ t + 3 * c)) +
                    c * r ^ d := by gcongr
              _ = r ^ d * 3 ^ (l + 1) * (s * (s ^ t + 3 * c)) +
                    c * r ^ d := by rw [hcombine]
              _ <= r ^ d * 3 ^ (l + 1) * (s * (s ^ t + 3 * c)) +
                    c * (r ^ d * 3 ^ (l + 1)) := by gcongr
              _ = (r ^ d * 3 ^ (l + 1)) *
                    (s * (s ^ t + 3 * c) + c) := by ring
              _ <= (r ^ d * 3 ^ (l + 1)) * (s ^ (t + 1) + 3 * c) := by
                apply mul_le_mul_of_nonneg_left _ hparent
                rw [pow_succ]
                dsimp [s]
                nlinarith
  simpa [r, s] using hclaim depth 0 0 (by omega)

/-- The terminal contraction after the DNS depth `2*n`. -/
theorem recursive_terminal_le (n : Nat) :
    (8 / 15 : Real) ^ (2 * n) <= 1 / ((2 ^ n : Nat) : Real) := by
  have hsquare : (8 / 15 : Real) ^ 2 <= (1 / 2 : Real) := by norm_num
  calc
    (8 / 15 : Real) ^ (2 * n) = ((8 / 15 : Real) ^ 2) ^ n := by rw [pow_mul]
    _ <= (1 / 2 : Real) ^ n :=
      pow_le_pow_left₀ (by positivity) hsquare n
    _ = 1 / ((2 ^ n : Nat) : Real) := by
      rw [one_div_pow]
      norm_num

/-! ## Exact linked-label semantics

DNS samples one distinguished value `r0` and one independent value `r i` for
each base label.  A left link `s` denotes `r0 + s`; a right link `t` denotes
`r0 + t`.  The following definition spells out distinctness without hiding it
behind a graph encoding.  Distinct link values need no separate hypothesis:
translation by `r0` is injective and the links are stored in `Finset`s. -/

section Labels

universe u v

variable {G : Type u} {I : Type v}

/-- A DNS independent-permutation label with an arbitrary finite base index. -/
structure Label (I : Type v) (G : Type u) where
  base : I -> G
  left : Finset G
  right : Finset G

variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [Fintype I] [DecidableEq I]

/-- Distinctness on the first permutation side. -/
def Label.LeftGood (L : Label I G) (r0 : G) (r : I -> G) : Prop :=
  Function.Injective r /\
  (forall i, r i ≠ r0) /\
  0 ∉ L.left /\
  forall i s, s ∈ L.left -> r i ≠ r0 + s

/-- Distinctness on the second permutation side. -/
def Label.RightGood (L : Label I G) (r0 : G) (r : I -> G) : Prop :=
  Function.Injective (fun i => r i + L.base i) /\
  forall i t, t ∈ L.right -> r i + L.base i ≠ r0 + t

/-- DNS's event `dist(L | (r0,r))`. -/
def Label.Good (L : Label I G) (z : G × (I -> G)) : Prop :=
  L.LeftGood z.1 z.2 /\ L.RightGood z.1 z.2

noncomputable instance Label.goodDecidable (L : Label I G) (z : G × (I -> G)) :
    Decidable (L.Good z) := Classical.dec _

/-- The finite realization type of a linked label. -/
def Label.Realization (L : Label I G) := {z : G × (I -> G) // L.Good z}

noncomputable instance Label.realizationFintype (L : Label I G) :
    Fintype L.Realization := by
  classical
  change Fintype {z : G × (I -> G) // L.Good z}
  exact Fintype.ofFinite _

/-- Exact realization count.  Probabilities are obtained by dividing this by
`|G|^(|I|+1)`. -/
def Label.count (L : Label I G) : Nat := Fintype.card L.Realization

/-- The base type with one distinguished coordinate removed. -/
abbrev Without (i : I) := {j : I // j ≠ i}

/-- Restrict a base-indexed family away from `i`. -/
def restrictAway (i : I) (r : I -> G) : Without i -> G := fun j => r j.1

/-- Insert a prescribed value at `i`. -/
def insertAt (i : I) (x : G) (r : Without i -> G) : I -> G :=
  fun j => if h : j = i then x else r ⟨j, h⟩

@[simp]
theorem insertAt_same (i : I) (x : G) (r : Without i -> G) :
    insertAt i x r i = x := by
  simp [insertAt]

@[simp]
theorem insertAt_ne (i j : I) (hji : j ≠ i) (x : G) (r : Without i -> G) :
    insertAt i x r j = r ⟨j, hji⟩ := by
  simp [insertAt, hji]

@[simp]
theorem restrictAway_insertAt (i : I) (x : G) (r : Without i -> G) :
    restrictAway i (insertAt i x r) = r := by
  funext j
  simp [restrictAway, insertAt, j.2]

@[simp]
theorem insertAt_restrictAway (i : I) (r : I -> G) :
    insertAt i (r i) (restrictAway i r) = r := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [insertAt, restrictAway, h]

/-- Remove a right link, leaving the base coordinates unchanged. -/
def Label.eraseRight (L : Label I G) (x : G) : Label I G :=
  { L with right := L.right.erase x }

/-- The DNS right-link push `L_{i -> x}`: retain the right link `x`, remove
base coordinate `i`, and insert its transferred label `x + base i` on the
left. -/
def Label.pushRight (L : Label I G) (i : I) (x : G) : Label (Without i) G where
  base j := L.base j.1
  left := insert (x + L.base i) L.left
  right := L.right

/-- Coordinates which can genuinely collide with the removed right link.
If the transferred label is already on the left, left distinctness makes the
collision impossible. -/
def Label.RightEligible (L : Label I G) (x : G) :=
  {i : I // x + L.base i ∉ L.left}

noncomputable instance Label.rightEligibleFintype (L : Label I G) (x : G) :
    Fintype (L.RightEligible x) := by
  classical
  unfold Label.RightEligible
  infer_instance

theorem Label.good_eraseRight_of_good (L : Label I G) (x : G)
    {z : G × (I -> G)} (hz : L.Good z) : (L.eraseRight x).Good z := by
  rcases hz with ⟨hleft, hinj, hlinks⟩
  exact ⟨hleft, hinj, fun i t ht => hlinks i t (Finset.mem_of_mem_erase ht)⟩

theorem Label.exists_collision_of_good_eraseRight_not_good
    (L : Label I G) {x r0 : G} {r : I -> G}
    (hx : x ∈ L.right) (herase : (L.eraseRight x).Good (r0, r))
    (hnot : ¬ L.Good (r0, r)) :
    ∃ i, r i + L.base i = r0 + x := by
  classical
  by_contra hnone
  apply hnot
  rcases herase with ⟨hleft, hinj, hlinks⟩
  refine ⟨hleft, hinj, ?_⟩
  intro i t ht
  by_cases htx : t = x
  · subst t
    exact fun h => hnone ⟨i, h⟩
  · exact hlinks i t (Finset.mem_erase.mpr ⟨htx, ht⟩)

theorem Label.rightEligible_of_collision
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    {x r0 : G} {r : I -> G} {i : I}
    (hleft : L.LeftGood r0 r)
    (hcollision : r i + L.base i = r0 + x) :
    x + L.base i ∉ L.left := by
  intro hmem
  have hri : r i = r0 + (x + L.base i) := by
    calc
      r i = r i + 0 := by simp
      _ = r i + (L.base i + L.base i) := by rw [hxor]
      _ = (r i + L.base i) + L.base i := by abel
      _ = (r0 + x) + L.base i := by rw [hcollision]
      _ = r0 + (x + L.base i) := by abel
  exact hleft.2.2.2 i (x + L.base i) hmem hri

theorem Label.good_pushRight_of_collision
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    {x r0 : G} {r : I -> G} {i : I}
    (hx : x ∈ L.right)
    (hi : x + L.base i ∉ L.left)
    (herase : (L.eraseRight x).Good (r0, r))
    (hcollision : r i + L.base i = r0 + x) :
    (L.pushRight i x).Good (r0, restrictAway i r) := by
  rcases herase with ⟨hleft, hrightInj, hrightLinks⟩
  have hri : r i = r0 + (x + L.base i) := by
    calc
      r i = r i + 0 := by simp
      _ = r i + (L.base i + L.base i) := by rw [hxor]
      _ = (r i + L.base i) + L.base i := by abel
      _ = (r0 + x) + L.base i := by rw [hcollision]
      _ = r0 + (x + L.base i) := by abel
  have hs0 : x + L.base i ≠ 0 := by
    intro hs
    have : r i = r0 := by simpa [hs] using hri
    exact hleft.2.1 i this
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j k hjk
      apply Subtype.ext
      exact hleft.1 hjk
    · exact fun j => hleft.2.1 j.1
    · change 0 ∉ insert (x + L.base i) L.left
      simpa only [Finset.mem_insert, not_or] using ⟨hs0.symm, hleft.2.2.1⟩
    · intro j s hs
      change s ∈ insert (x + L.base i) L.left at hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · intro hbad
        have hrji : r j.1 = r i := by simpa [restrictAway, hri] using hbad
        exact j.2 (hleft.1 hrji)
      · exact hleft.2.2.2 j.1 s hs
  · intro j k hjk
    apply Subtype.ext
    exact hrightInj hjk
  · intro j t ht
    by_cases htx : t = x
    · subst t
      intro hbad
      have heq : r j.1 + L.base j.1 = r i + L.base i := by
        rw [hcollision]
        simpa [restrictAway, Label.pushRight] using hbad
      exact j.2 (hrightInj heq)
    · exact hrightLinks j.1 t (Finset.mem_erase.mpr ⟨htx, ht⟩)

/-- Reconstruct the deleted base value from a pushed right-link realization. -/
def Label.rebuildRight (L : Label I G) (i : I) (x r0 : G)
    (r : Without i -> G) : I -> G :=
  insertAt i (r0 + (x + L.base i)) r

@[simp]
theorem Label.rebuildRight_same (L : Label I G) (i : I) (x r0 : G)
    (r : Without i -> G) :
    L.rebuildRight i x r0 r i = r0 + (x + L.base i) := by
  simp [Label.rebuildRight]

theorem Label.collision_rebuildRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (i : I) (x r0 : G)
    (r : Without i -> G) :
    L.rebuildRight i x r0 r i + L.base i = r0 + x := by
  rw [Label.rebuildRight_same]
  calc
    r0 + (x + L.base i) + L.base i = r0 + x + (L.base i + L.base i) := by abel
    _ = r0 + x := by rw [hxor]; simp

theorem Label.good_eraseRight_rebuildRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    {x r0 : G} {i : I} {r : Without i -> G}
    (hx : x ∈ L.right)
    (hi : x + L.base i ∉ L.left)
    (hpush : (L.pushRight i x).Good (r0, r)) :
    (L.eraseRight x).Good (r0, L.rebuildRight i x r0 r) := by
  rcases hpush with ⟨hleft, hrightInj, hrightLinks⟩
  let s : G := x + L.base i
  let v : G := r0 + s
  have hv : L.rebuildRight i x r0 r i = v := by simp [v, s]
  have hrest (j : Without i) : L.rebuildRight i x r0 r j.1 = r j := by
    simp [Label.rebuildRight, insertAt, j.2]
  have hs0 : s ≠ 0 := by
    intro hs
    have hzero : (0 : G) ∈ (L.pushRight i x).left := by
      change 0 ∈ insert s L.left
      simp [hs]
    exact hleft.2.2.1 hzero
  have hcollision := L.collision_rebuildRight hxor i x r0 r
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact hki.symm
        · exfalso
          have hkval : L.rebuildRight i x r0 r k = r ⟨k, hki⟩ := by
            simp [Label.rebuildRight, insertAt, hki]
          have havoid := hleft.2.2.2 ⟨k, hki⟩ s (by
            change s ∈ insert s L.left
            simp)
          apply havoid
          change L.rebuildRight i x r0 r i = L.rebuildRight i x r0 r k at hjk
          calc
            r ⟨k, hki⟩ = L.rebuildRight i x r0 r k := hkval.symm
            _ = L.rebuildRight i x r0 r i := hjk.symm
            _ = v := hv
      · by_cases hki : k = i
        · subst k
          exfalso
          have hjval : L.rebuildRight i x r0 r j = r ⟨j, hji⟩ := by
            simp [Label.rebuildRight, insertAt, hji]
          have havoid := hleft.2.2.2 ⟨j, hji⟩ s (by
            change s ∈ insert s L.left
            simp)
          apply havoid
          change L.rebuildRight i x r0 r j = L.rebuildRight i x r0 r i at hjk
          calc
            r ⟨j, hji⟩ = L.rebuildRight i x r0 r j := hjval.symm
            _ = L.rebuildRight i x r0 r i := hjk
            _ = v := hv
        · have heq : r ⟨j, hji⟩ = r ⟨k, hki⟩ := by
            simpa [Label.rebuildRight, insertAt, hji, hki] using hjk
          exact congrArg Subtype.val (hleft.1 heq)
    · intro j
      by_cases hji : j = i
      · subst j
        change L.rebuildRight i x r0 r i ≠ r0
        rw [hv]
        exact add_ne_left.mpr hs0
      · simpa [Label.rebuildRight, insertAt, hji] using hleft.2.1 ⟨j, hji⟩
    · exact fun hzero => hleft.2.2.1 (by
        change 0 ∈ insert s L.left
        exact Finset.mem_insert_of_mem hzero)
    · intro j t ht
      by_cases hji : j = i
      · subst j
        change L.rebuildRight i x r0 r i ≠ r0 + t
        rw [hv]
        intro heq
        have hst : s = t := add_left_cancel heq
        exact hi (by simpa [s, hst] using ht)
      · simpa [Label.rebuildRight, insertAt, hji] using
          hleft.2.2.2 ⟨j, hji⟩ t (Finset.mem_insert_of_mem ht)
  · intro j k hjk
    change L.rebuildRight i x r0 r j + L.base j =
      L.rebuildRight i x r0 r k + L.base k at hjk
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · exact hki.symm
      · exfalso
        have havoid := hrightLinks ⟨k, hki⟩ x hx
        apply havoid
        calc
          r ⟨k, hki⟩ + (L.pushRight i x).base ⟨k, hki⟩ =
              L.rebuildRight i x r0 r k + L.base k := by
                simp [Label.rebuildRight, insertAt, hki, Label.pushRight]
          _ = L.rebuildRight i x r0 r i + L.base i := hjk.symm
          _ = r0 + x := hcollision
    · by_cases hki : k = i
      · subst k
        exfalso
        have havoid := hrightLinks ⟨j, hji⟩ x hx
        apply havoid
        calc
          r ⟨j, hji⟩ + (L.pushRight i x).base ⟨j, hji⟩ =
              L.rebuildRight i x r0 r j + L.base j := by
                simp [Label.rebuildRight, insertAt, hji, Label.pushRight]
          _ = L.rebuildRight i x r0 r i + L.base i := hjk
          _ = r0 + x := hcollision
      · have heq :
            r ⟨j, hji⟩ + (L.pushRight i x).base ⟨j, hji⟩ =
              r ⟨k, hki⟩ + (L.pushRight i x).base ⟨k, hki⟩ := by
            simpa [Label.rebuildRight, insertAt, hji, hki, Label.pushRight] using hjk
        exact congrArg Subtype.val (hrightInj heq)
  · intro j t ht
    have htx : t ≠ x := (Finset.mem_erase.mp ht).1
    have htL : t ∈ L.right := (Finset.mem_erase.mp ht).2
    by_cases hji : j = i
    · subst j
      change L.rebuildRight i x r0 r i + L.base i ≠ r0 + t
      rw [hcollision]
      exact fun heq => htx (add_left_cancel heq).symm
    · simpa [Label.rebuildRight, insertAt, hji, Label.pushRight] using
        hrightLinks ⟨j, hji⟩ t htL

theorem Label.not_good_rebuildRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    {x r0 : G} {i : I} {r : Without i -> G}
    (hx : x ∈ L.right) :
    ¬ L.Good (r0, L.rebuildRight i x r0 r) := by
  intro hgood
  have hne := hgood.2.2 i x hx
  exact hne (L.collision_rebuildRight hxor i x r0 r)

/-- The two disjoint outcomes after deleting a right link: either the link was
already fresh, or it collided with one uniquely determined base coordinate. -/
def Label.RightPieces (L : Label I G) (x : G) :=
  L.Realization ⊕ (Σ i : L.RightEligible x, (L.pushRight i.1 x).Realization)

noncomputable instance Label.rightPiecesFintype (L : Label I G) (x : G) :
    Fintype (L.RightPieces x) := by
  classical
  unfold Label.RightPieces
  infer_instance

noncomputable def Label.rightCollisionBase
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) (z : (L.eraseRight x).Realization)
    (hnot : ¬ L.Good z.1) : I :=
  Classical.choose (L.exists_collision_of_good_eraseRight_not_good hx z.2 hnot)

theorem Label.rightCollisionBase_spec
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) (z : (L.eraseRight x).Realization)
    (hnot : ¬ L.Good z.1) :
    z.1.2 (L.rightCollisionBase hxor x hx z hnot) +
        L.base (L.rightCollisionBase hxor x hx z hnot) = z.1.1 + x :=
  Classical.choose_spec (L.exists_collision_of_good_eraseRight_not_good hx z.2 hnot)

noncomputable def Label.rightCollisionIndex
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) (z : (L.eraseRight x).Realization)
    (hnot : ¬ L.Good z.1) : L.RightEligible x :=
  ⟨L.rightCollisionBase hxor x hx z hnot,
    L.rightEligible_of_collision hxor z.2.1
      (L.rightCollisionBase_spec hxor x hx z hnot)⟩

theorem Label.rightCollisionIndex_spec
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) (z : (L.eraseRight x).Realization)
    (hnot : ¬ L.Good z.1) :
    z.1.2 (L.rightCollisionIndex hxor x hx z hnot).1 +
        L.base (L.rightCollisionIndex hxor x hx z hnot).1 = z.1.1 + x :=
  L.rightCollisionBase_spec hxor x hx z hnot

noncomputable def Label.splitRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    (L.eraseRight x).Realization -> L.RightPieces x := fun z =>
  if hgood : L.Good z.1 then
    Sum.inl ⟨z.1, hgood⟩
  else
    let i := L.rightCollisionIndex hxor x hx z hgood
    Sum.inr ⟨i,
      ⟨(z.1.1, restrictAway i.1 z.1.2),
        L.good_pushRight_of_collision hxor hx i.2 z.2
          (L.rightCollisionIndex_spec hxor x hx z hgood)⟩⟩

noncomputable def Label.mergeRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    L.RightPieces x -> (L.eraseRight x).Realization
  | Sum.inl z => ⟨z.1, L.good_eraseRight_of_good x z.2⟩
  | Sum.inr z =>
      ⟨(z.2.1.1, L.rebuildRight z.1.1 x z.2.1.1 z.2.1.2),
        L.good_eraseRight_rebuildRight hxor hx z.1.2 z.2.2⟩

theorem Label.restrictedRebuild_realization_heq
    (L : Label I G) (x : G) {e zi : L.RightEligible x}
    (he : e = zi) (m : G × (I -> G))
    (w : (L.pushRight zi.1 x).Realization)
    (hm : m = (w.1.1, L.rebuildRight zi.1 x w.1.1 w.1.2))
    (hgood : (L.pushRight e.1 x).Good
      (m.1, restrictAway e.1 m.2)) :
    HEq (⟨(m.1, restrictAway e.1 m.2), hgood⟩ :
        (L.pushRight e.1 x).Realization) w := by
  subst e
  apply heq_of_eq
  apply Subtype.ext
  change (m.1, restrictAway zi.1 m.2) = w.1
  rw [hm]
  apply Prod.ext
  · rfl
  · simp [Label.rebuildRight]

theorem Label.mergeRight_splitRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) (z : (L.eraseRight x).Realization) :
    L.mergeRight hxor x hx (L.splitRight hxor x hx z) = z := by
  classical
  unfold Label.splitRight
  split_ifs with hgood
  · apply Subtype.ext
    rfl
  · let hex := L.exists_collision_of_good_eraseRight_not_good hx z.2 hgood
    let i := Classical.choose hex
    have hcollision : z.1.2 i + L.base i = z.1.1 + x := Classical.choose_spec hex
    have hri : z.1.2 i = z.1.1 + (x + L.base i) := by
      calc
        z.1.2 i = z.1.2 i + 0 := by simp
        _ = z.1.2 i + (L.base i + L.base i) := by rw [hxor]
        _ = (z.1.2 i + L.base i) + L.base i := by abel
        _ = (z.1.1 + x) + L.base i := by rw [hcollision]
        _ = z.1.1 + (x + L.base i) := by abel
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change L.rebuildRight i x z.1.1 (restrictAway i z.1.2) = z.1.2
      rw [Label.rebuildRight, ← hri]
      exact insertAt_restrictAway i z.1.2

theorem Label.splitRight_mergeRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) (z : L.RightPieces x) :
    L.splitRight hxor x hx (L.mergeRight hxor x hx z) = z := by
  classical
  cases z with
  | inl z =>
      simp [Label.mergeRight, Label.splitRight, z.2]
  | inr z =>
      rcases z with ⟨zi, w⟩
      let i : I := zi.1
      let merged : (L.eraseRight x).Realization :=
        L.mergeRight hxor x hx (Sum.inr ⟨zi, w⟩)
      have hmergedVal : merged.1 =
          (w.1.1, L.rebuildRight i x w.1.1 w.1.2) := by
        rfl
      have hnot : ¬ L.Good merged.1 := by
        rw [hmergedVal]
        exact L.not_good_rebuildRight hxor hx
      unfold Label.splitRight
      rw [dif_neg hnot]
      have hicollision : merged.1.2 i + L.base i = merged.1.1 + x := by
        rw [hmergedVal]
        exact L.collision_rebuildRight hxor i x w.1.1 w.1.2
      let e := L.rightCollisionIndex hxor x hx merged hnot
      have hecollision : merged.1.2 e.1 + L.base e.1 = merged.1.1 + x :=
        L.rightCollisionIndex_spec hxor x hx merged hnot
      have he : e = zi := by
        apply Subtype.ext
        exact merged.2.2.1 (hecollision.trans hicollision.symm)
      let new : (L.pushRight e.1 x).Realization :=
        ⟨(merged.1.1, restrictAway e.1 merged.1.2),
          L.good_pushRight_of_collision hxor hx e.2 merged.2
            hecollision⟩
      apply congrArg Sum.inr
      change (⟨e, new⟩ : Σ k : L.RightEligible x,
        (L.pushRight k.1 x).Realization) = ⟨zi, w⟩
      apply Sigma.ext he
      change HEq new w
      exact L.restrictedRebuild_realization_heq x he merged.1 w hmergedVal new.2

/-- Exact sample-space form of DNS Lemma 11 for deletion of a right link. -/
noncomputable def Label.rightDeletionEquiv
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    (L.eraseRight x).Realization ≃ L.RightPieces x where
  toFun := L.splitRight hxor x hx
  invFun := L.mergeRight hxor x hx
  left_inv := L.mergeRight_splitRight hxor x hx
  right_inv := L.splitRight_mergeRight hxor x hx

/-- Cardinality form of right-link deletion.  Unlike the paper's probability
identity, this statement has no denominator and therefore exposes exactly why
each pushed term later carries one factor `1 / |G|`: it has one fewer sampled
base coordinate. -/
theorem Label.count_eraseRight
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    (L.eraseRight x).count =
      L.count + ∑ i : L.RightEligible x, (L.pushRight i.1 x).count := by
  classical
  rw [Label.count, Label.count]
  rw [Fintype.card_congr (L.rightDeletionEquiv hxor x hx)]
  change Fintype.card (L.Realization ⊕
      (Σ i : L.RightEligible x, (L.pushRight i.1 x).Realization)) = _
  rw [Fintype.card_sum, Fintype.card_sigma]
  rfl

/-- Rearranged cardinality form of DNS Lemma 11. -/
theorem Label.count_eq_count_eraseRight_sub
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    L.count = (L.eraseRight x).count -
      ∑ i : L.RightEligible x, (L.pushRight i.1 x).count := by
  rw [L.count_eraseRight hxor x hx]
  omega

/-! ### The symmetric (left-link) deletion

The two sides are not literally interchangeable: the distinguished sample
`r0` belongs to the left distinctness list but not the right one.  Consequently
the left identity carries the published well-formedness side condition
`x != 0`; this is exactly the condition saying that the deleted link did not
coincide with the distinguished vertex before any base collision is examined. -/

/-- Remove a left link, leaving the base coordinates unchanged. -/
def Label.eraseLeft (L : Label I G) (x : G) : Label I G :=
  { L with left := L.left.erase x }

/-- The DNS left-link push: retain `x` on the left, delete base coordinate `i`,
and put `x + base i` on the right. -/
def Label.pushLeft (L : Label I G) (i : I) (x : G) : Label (Without i) G where
  base j := L.base j.1
  left := L.left
  right := insert (x + L.base i) L.right

def Label.LeftEligible (L : Label I G) (x : G) :=
  {i : I // x + L.base i ∉ L.right}

noncomputable instance Label.leftEligibleFintype (L : Label I G) (x : G) :
    Fintype (L.LeftEligible x) := by
  classical
  unfold Label.LeftEligible
  infer_instance

theorem Label.good_eraseLeft_of_good (L : Label I G) (x : G)
    {z : G × (I -> G)} (hz : L.Good z) : (L.eraseLeft x).Good z := by
  rcases hz with ⟨⟨hinj, hzero, h0, hlinks⟩, hright⟩
  exact ⟨⟨hinj, hzero, fun hz => h0 (Finset.mem_of_mem_erase hz),
    fun i s hs => hlinks i s (Finset.mem_of_mem_erase hs)⟩, hright⟩

theorem Label.exists_left_collision_of_good_eraseLeft_not_good
    (L : Label I G) {x r0 : G} {r : I -> G}
    (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (herase : (L.eraseLeft x).Good (r0, r))
    (hnot : ¬ L.Good (r0, r)) :
    ∃ i, r i = r0 + x := by
  classical
  by_contra hnone
  apply hnot
  rcases herase with ⟨⟨hinj, hzero, h0, hlinks⟩, hright⟩
  refine ⟨⟨hinj, hzero, ?_, ?_⟩, hright⟩
  · intro hz
    by_cases hzx : (0 : G) = x
    · exact hx0 hzx.symm
    · exact h0 (Finset.mem_erase.mpr ⟨hzx, hz⟩)
  · intro i s hs
    by_cases hsx : s = x
    · subst s
      exact fun h => hnone ⟨i, h⟩
    · exact hlinks i s (Finset.mem_erase.mpr ⟨hsx, hs⟩)

theorem Label.leftEligible_of_collision (L : Label I G)
    {x r0 : G} {r : I -> G} {i : I}
    (hright : L.RightGood r0 r)
    (hcollision : r i = r0 + x) :
    x + L.base i ∉ L.right := by
  intro hmem
  have havoid := hright.2 i (x + L.base i) hmem
  apply havoid
  rw [hcollision]
  abel

theorem Label.good_pushLeft_of_collision
    (L : Label I G) {x r0 : G} {r : I -> G} {i : I}
    (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (hi : x + L.base i ∉ L.right)
    (herase : (L.eraseLeft x).Good (r0, r))
    (hcollision : r i = r0 + x) :
    (L.pushLeft i x).Good (r0, restrictAway i r) := by
  rcases herase with ⟨hleft, hrightInj, hrightLinks⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j k hjk
      apply Subtype.ext
      exact hleft.1 hjk
    · exact fun j => hleft.2.1 j.1
    · intro hzero
      by_cases h0x : (0 : G) = x
      · exact hx0 h0x.symm
      · exact hleft.2.2.1 (Finset.mem_erase.mpr ⟨h0x, hzero⟩)
    · intro j s hs
      by_cases hsx : s = x
      · subst s
        intro hbad
        have hrji : r j.1 = r i := by simpa [restrictAway, hcollision] using hbad
        exact j.2 (hleft.1 hrji)
      · exact hleft.2.2.2 j.1 s (Finset.mem_erase.mpr ⟨hsx, hs⟩)
  · intro j k hjk
    apply Subtype.ext
    exact hrightInj hjk
  · intro j t ht
    change t ∈ insert (x + L.base i) L.right at ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · intro hbad
      have heq : r j.1 + L.base j.1 = r i + L.base i := by
        rw [hcollision]
        simpa only [restrictAway, Label.pushLeft, add_assoc] using hbad
      exact j.2 (hrightInj heq)
    · exact hrightLinks j.1 t ht

/-- Reconstruct the deleted base value from a pushed left-link realization. -/
def Label.rebuildLeft (L : Label I G) (i : I) (x r0 : G)
    (r : Without i -> G) : I -> G :=
  insertAt i (r0 + x) r

@[simp]
theorem Label.rebuildLeft_same (L : Label I G) (i : I) (x r0 : G)
    (r : Without i -> G) :
    L.rebuildLeft i x r0 r i = r0 + x := by
  simp [Label.rebuildLeft]

theorem Label.good_eraseLeft_rebuildLeft
    (L : Label I G) {x r0 : G} {i : I} {r : Without i -> G}
    (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (hi : x + L.base i ∉ L.right)
    (hpush : (L.pushLeft i x).Good (r0, r)) :
    (L.eraseLeft x).Good (r0, L.rebuildLeft i x r0 r) := by
  rcases hpush with ⟨hleft, hrightInj, hrightLinks⟩
  have hrest (j : Without i) : L.rebuildLeft i x r0 r j.1 = r j := by
    simp [Label.rebuildLeft, insertAt, j.2]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact hki.symm
        · exfalso
          have havoid := hleft.2.2.2 ⟨k, hki⟩ x hx
          apply havoid
          calc
            r ⟨k, hki⟩ = L.rebuildLeft i x r0 r k := (hrest ⟨k, hki⟩).symm
            _ = L.rebuildLeft i x r0 r i := hjk.symm
            _ = r0 + x := L.rebuildLeft_same i x r0 r
      · by_cases hki : k = i
        · subst k
          exfalso
          have havoid := hleft.2.2.2 ⟨j, hji⟩ x hx
          apply havoid
          calc
            r ⟨j, hji⟩ = L.rebuildLeft i x r0 r j := (hrest ⟨j, hji⟩).symm
            _ = L.rebuildLeft i x r0 r i := hjk
            _ = r0 + x := L.rebuildLeft_same i x r0 r
        · have heq : r ⟨j, hji⟩ = r ⟨k, hki⟩ := by
            simpa [Label.rebuildLeft, insertAt, hji, hki] using hjk
          exact congrArg Subtype.val (hleft.1 heq)
    · intro j
      by_cases hji : j = i
      · subst j
        change L.rebuildLeft i x r0 r i ≠ r0
        rw [Label.rebuildLeft_same]
        exact add_ne_left.mpr hx0
      · simpa [Label.rebuildLeft, insertAt, hji] using hleft.2.1 ⟨j, hji⟩
    · exact fun hzero => hleft.2.2.1 (Finset.mem_of_mem_erase hzero)
    · intro j t ht
      have htx : t ≠ x := (Finset.mem_erase.mp ht).1
      have htL : t ∈ L.left := (Finset.mem_erase.mp ht).2
      by_cases hji : j = i
      · subst j
        change L.rebuildLeft i x r0 r i ≠ r0 + t
        rw [Label.rebuildLeft_same]
        exact fun heq => htx (add_left_cancel heq).symm
      · simpa [Label.rebuildLeft, insertAt, hji] using hleft.2.2.2 ⟨j, hji⟩ t htL
  · intro j k hjk
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · exact hki.symm
      · exfalso
        have havoid := hrightLinks ⟨k, hki⟩ (x + L.base i) (by
          change x + L.base i ∈ insert (x + L.base i) L.right
          simp)
        apply havoid
        calc
          r ⟨k, hki⟩ + (L.pushLeft i x).base ⟨k, hki⟩ =
              L.rebuildLeft i x r0 r k + L.base k := by
                simp [Label.rebuildLeft, insertAt, hki, Label.pushLeft]
          _ = L.rebuildLeft i x r0 r i + L.base i := hjk.symm
          _ = r0 + (x + L.base i) := by rw [Label.rebuildLeft_same]; abel
    · by_cases hki : k = i
      · subst k
        exfalso
        have havoid := hrightLinks ⟨j, hji⟩ (x + L.base i) (by
          change x + L.base i ∈ insert (x + L.base i) L.right
          simp)
        apply havoid
        calc
          r ⟨j, hji⟩ + (L.pushLeft i x).base ⟨j, hji⟩ =
              L.rebuildLeft i x r0 r j + L.base j := by
                simp [Label.rebuildLeft, insertAt, hji, Label.pushLeft]
          _ = L.rebuildLeft i x r0 r i + L.base i := hjk
          _ = r0 + (x + L.base i) := by rw [Label.rebuildLeft_same]; abel
      · have heq :
            r ⟨j, hji⟩ + (L.pushLeft i x).base ⟨j, hji⟩ =
              r ⟨k, hki⟩ + (L.pushLeft i x).base ⟨k, hki⟩ := by
            simpa [Label.rebuildLeft, insertAt, hji, hki, Label.pushLeft] using hjk
        exact congrArg Subtype.val (hrightInj heq)
  · intro j t ht
    by_cases hji : j = i
    · subst j
      change L.rebuildLeft i x r0 r i + L.base i ≠ r0 + t
      rw [Label.rebuildLeft_same]
      intro heq
      have hlabel : x + L.base i = t :=
        add_left_cancel (a := r0) (by simpa [add_assoc] using heq)
      exact hi (by simpa [hlabel] using ht)
    · simpa [Label.rebuildLeft, insertAt, hji, Label.pushLeft] using
        hrightLinks ⟨j, hji⟩ t (Finset.mem_insert_of_mem ht)

theorem Label.not_good_rebuildLeft (L : Label I G)
    {x r0 : G} {i : I} {r : Without i -> G} (hx : x ∈ L.left) :
    ¬ L.Good (r0, L.rebuildLeft i x r0 r) := by
  intro hgood
  exact hgood.1.2.2.2 i x hx (L.rebuildLeft_same i x r0 r)

def Label.LeftPieces (L : Label I G) (x : G) :=
  L.Realization ⊕ (Σ i : L.LeftEligible x, (L.pushLeft i.1 x).Realization)

noncomputable instance Label.leftPiecesFintype (L : Label I G) (x : G) :
    Fintype (L.LeftPieces x) := by
  classical
  unfold Label.LeftPieces
  infer_instance

noncomputable def Label.leftCollisionBase
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (z : (L.eraseLeft x).Realization) (hnot : ¬ L.Good z.1) : I :=
  Classical.choose
    (L.exists_left_collision_of_good_eraseLeft_not_good hx hx0 z.2 hnot)

theorem Label.leftCollisionBase_spec
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (z : (L.eraseLeft x).Realization) (hnot : ¬ L.Good z.1) :
    z.1.2 (L.leftCollisionBase x hx hx0 z hnot) = z.1.1 + x :=
  Classical.choose_spec
    (L.exists_left_collision_of_good_eraseLeft_not_good hx hx0 z.2 hnot)

noncomputable def Label.leftCollisionIndex
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (z : (L.eraseLeft x).Realization) (hnot : ¬ L.Good z.1) :
    L.LeftEligible x :=
  ⟨L.leftCollisionBase x hx hx0 z hnot,
    L.leftEligible_of_collision z.2.2
      (L.leftCollisionBase_spec x hx hx0 z hnot)⟩

theorem Label.leftCollisionIndex_spec
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (z : (L.eraseLeft x).Realization) (hnot : ¬ L.Good z.1) :
    z.1.2 (L.leftCollisionIndex x hx hx0 z hnot).1 = z.1.1 + x :=
  L.leftCollisionBase_spec x hx hx0 z hnot

noncomputable def Label.splitLeft
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    (L.eraseLeft x).Realization -> L.LeftPieces x := fun z =>
  if hgood : L.Good z.1 then
    Sum.inl ⟨z.1, hgood⟩
  else
    let i := L.leftCollisionIndex x hx hx0 z hgood
    Sum.inr ⟨i,
      ⟨(z.1.1, restrictAway i.1 z.1.2),
        L.good_pushLeft_of_collision hx hx0 i.2 z.2
          (L.leftCollisionIndex_spec x hx hx0 z hgood)⟩⟩

noncomputable def Label.mergeLeft
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    L.LeftPieces x -> (L.eraseLeft x).Realization
  | Sum.inl z => ⟨z.1, L.good_eraseLeft_of_good x z.2⟩
  | Sum.inr z =>
      ⟨(z.2.1.1, L.rebuildLeft z.1.1 x z.2.1.1 z.2.1.2),
        L.good_eraseLeft_rebuildLeft hx hx0 z.1.2 z.2.2⟩

theorem Label.mergeLeft_splitLeft
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (z : (L.eraseLeft x).Realization) :
    L.mergeLeft x hx hx0 (L.splitLeft x hx hx0 z) = z := by
  classical
  unfold Label.splitLeft
  split_ifs with hgood
  · apply Subtype.ext
    rfl
  · let hex := L.exists_left_collision_of_good_eraseLeft_not_good hx hx0 z.2 hgood
    let i := Classical.choose hex
    have hcollision : z.1.2 i = z.1.1 + x := Classical.choose_spec hex
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change L.rebuildLeft i x z.1.1 (restrictAway i z.1.2) = z.1.2
      rw [Label.rebuildLeft, ← hcollision]
      exact insertAt_restrictAway i z.1.2

theorem Label.restrictedRebuildLeft_realization_heq
    (L : Label I G) (x : G) {e zi : L.LeftEligible x}
    (he : e = zi) (m : G × (I -> G))
    (w : (L.pushLeft zi.1 x).Realization)
    (hm : m = (w.1.1, L.rebuildLeft zi.1 x w.1.1 w.1.2))
    (hgood : (L.pushLeft e.1 x).Good (m.1, restrictAway e.1 m.2)) :
    HEq (⟨(m.1, restrictAway e.1 m.2), hgood⟩ :
        (L.pushLeft e.1 x).Realization) w := by
  subst e
  apply heq_of_eq
  apply Subtype.ext
  change (m.1, restrictAway zi.1 m.2) = w.1
  rw [hm]
  apply Prod.ext
  · rfl
  · simp [Label.rebuildLeft]

theorem Label.splitLeft_mergeLeft
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0)
    (z : L.LeftPieces x) :
    L.splitLeft x hx hx0 (L.mergeLeft x hx hx0 z) = z := by
  classical
  cases z with
  | inl z =>
      simp [Label.mergeLeft, Label.splitLeft, z.2]
  | inr z =>
      rcases z with ⟨zi, w⟩
      let i : I := zi.1
      let merged : (L.eraseLeft x).Realization :=
        L.mergeLeft x hx hx0 (Sum.inr ⟨zi, w⟩)
      have hmergedVal : merged.1 =
          (w.1.1, L.rebuildLeft i x w.1.1 w.1.2) := by
        rfl
      have hnot : ¬ L.Good merged.1 := by
        rw [hmergedVal]
        exact L.not_good_rebuildLeft hx
      unfold Label.splitLeft
      rw [dif_neg hnot]
      have hicollision : merged.1.2 i = merged.1.1 + x := by
        rw [hmergedVal]
        exact L.rebuildLeft_same i x w.1.1 w.1.2
      let e := L.leftCollisionIndex x hx hx0 merged hnot
      have hecollision : merged.1.2 e.1 = merged.1.1 + x :=
        L.leftCollisionIndex_spec x hx hx0 merged hnot
      have he : e = zi := by
        apply Subtype.ext
        exact merged.2.1.1 (hecollision.trans hicollision.symm)
      let new : (L.pushLeft e.1 x).Realization :=
        ⟨(merged.1.1, restrictAway e.1 merged.1.2),
          L.good_pushLeft_of_collision hx hx0 e.2 merged.2 hecollision⟩
      apply congrArg Sum.inr
      change (⟨e, new⟩ : Σ k : L.LeftEligible x,
        (L.pushLeft k.1 x).Realization) = ⟨zi, w⟩
      apply Sigma.ext he
      change HEq new w
      exact L.restrictedRebuildLeft_realization_heq x he merged.1 w hmergedVal new.2

noncomputable def Label.leftDeletionEquiv
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    (L.eraseLeft x).Realization ≃ L.LeftPieces x where
  toFun := L.splitLeft x hx hx0
  invFun := L.mergeLeft x hx hx0
  left_inv := L.mergeLeft_splitLeft x hx hx0
  right_inv := L.splitLeft_mergeLeft x hx hx0

/-- Exact cardinality form of DNS Lemma 11 for deletion of a left link. -/
theorem Label.count_eraseLeft
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    (L.eraseLeft x).count =
      L.count + ∑ i : L.LeftEligible x, (L.pushLeft i.1 x).count := by
  classical
  rw [Label.count, Label.count]
  rw [Fintype.card_congr (L.leftDeletionEquiv x hx hx0)]
  change Fintype.card (L.Realization ⊕
      (Σ i : L.LeftEligible x, (L.pushLeft i.1 x).Realization)) = _
  rw [Fintype.card_sum, Fintype.card_sigma]
  rfl

theorem Label.count_eq_count_eraseLeft_sub
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    L.count = (L.eraseLeft x).count -
      ∑ i : L.LeftEligible x, (L.pushLeft i.1 x).count := by
  rw [L.count_eraseLeft x hx hx0]
  omega

/-! ### Probability normalization -/

@[simp]
theorem card_without (i : I) : Fintype.card (Without i) = Fintype.card I - 1 := by
  simp [Without]

/-- Probability of the DNS distinctness event under independent uniform
sampling of `r0` and all base coordinates. -/
def Label.prob (L : Label I G) : Real :=
  (L.count : Real) / (Fintype.card G : Real) ^ (Fintype.card I + 1)

theorem Label.prob_nonneg (L : Label I G) : 0 <= L.prob := by
  unfold Label.prob
  positivity

theorem Label.prob_eq_zero_of_zero_mem_left (L : Label I G)
    (hzero : 0 ∈ L.left) : L.prob = 0 := by
  letI : IsEmpty L.Realization :=
    ⟨fun z => (z.2.1.2.2.1 hzero).elim⟩
  unfold Label.prob Label.count
  rw [Fintype.card_eq_zero]
  simp

private theorem Label.inv_card_mul_prob_pushRight
    (L : Label I G) (i : I) (x : G) :
    (1 / (Fintype.card G : Real)) * (L.pushRight i x).prob =
      ((L.pushRight i x).count : Real) /
        (Fintype.card G : Real) ^ (Fintype.card I + 1) := by
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  have hG : (Fintype.card G : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  unfold Label.prob
  rw [card_without]
  rw [Nat.sub_add_cancel (by omega : 1 <= Fintype.card I)]
  rw [pow_succ]
  field_simp

private theorem Label.inv_card_mul_prob_pushLeft
    (L : Label I G) (i : I) (x : G) :
    (1 / (Fintype.card G : Real)) * (L.pushLeft i x).prob =
      ((L.pushLeft i x).count : Real) /
        (Fintype.card G : Real) ^ (Fintype.card I + 1) := by
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  have hG : (Fintype.card G : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  unfold Label.prob
  rw [card_without]
  rw [Nat.sub_add_cancel (by omega : 1 <= Fintype.card I)]
  rw [pow_succ]
  field_simp

/-- Probability form of DNS Lemma 11, right-link case. -/
theorem Label.prob_eq_prob_eraseRight_sub
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    L.prob = (L.eraseRight x).prob -
      (1 / (Fintype.card G : Real)) *
        ∑ i : L.RightEligible x, (L.pushRight i.1 x).prob := by
  classical
  have hcount := L.count_eraseRight hxor x hx
  have hcountR : ((L.eraseRight x).count : Real) =
      (L.count : Real) +
        ∑ i : L.RightEligible x, ((L.pushRight i.1 x).count : Real) := by
    exact_mod_cast hcount
  change (L.count : Real) / (Fintype.card G : Real) ^ (Fintype.card I + 1) =
    ((L.eraseRight x).count : Real) /
        (Fintype.card G : Real) ^ (Fintype.card I + 1) -
      (1 / (Fintype.card G : Real)) *
        ∑ i : L.RightEligible x, (L.pushRight i.1 x).prob
  rw [Finset.mul_sum]
  simp_rw [L.inv_card_mul_prob_pushRight]
  rw [← Finset.sum_div]
  rw [hcountR]
  ring

/-- Probability form of DNS Lemma 11, left-link case. -/
theorem Label.prob_eq_prob_eraseLeft_sub
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    L.prob = (L.eraseLeft x).prob -
      (1 / (Fintype.card G : Real)) *
        ∑ i : L.LeftEligible x, (L.pushLeft i.1 x).prob := by
  classical
  have hcount := L.count_eraseLeft x hx hx0
  have hcountR : ((L.eraseLeft x).count : Real) =
      (L.count : Real) +
        ∑ i : L.LeftEligible x, ((L.pushLeft i.1 x).count : Real) := by
    exact_mod_cast hcount
  change (L.count : Real) / (Fintype.card G : Real) ^ (Fintype.card I + 1) =
    ((L.eraseLeft x).count : Real) /
        (Fintype.card G : Real) ^ (Fintype.card I + 1) -
      (1 / (Fintype.card G : Real)) *
        ∑ i : L.LeftEligible x, (L.pushLeft i.1 x).prob
  rw [Finset.mul_sum]
  simp_rw [L.inv_card_mul_prob_pushLeft]
  rw [← Finset.sum_div]
  rw [hcountR]
  ring

/-! ### The one-linked fiber is the compatible-assignment fiber -/

/-- A tuple with distinguished coordinate `i`, represented as the DNS
one-linked label whose only right link is the distinguished output label. -/
def compatibleLabel {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) : Label (Without i) G where
  base j := y j.1
  left := ∅
  right := {y i}

/-- Hidden assignments counted by `compatible_count`, before specializing the
index type to `Fin q`. -/
def CompatibleAssignment {J : Type*} [Fintype J]
    (y : J -> G) :=
  {a : J -> G // Function.Injective a /\
    Function.Injective (fun j => a j + y j)}

noncomputable instance compatibleAssignmentFintype
    {J : Type*} [Fintype J] (y : J -> G) :
    Fintype (CompatibleAssignment y) := by
  classical
  unfold CompatibleAssignment
  infer_instance

def compatibleAssignmentToRealization
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) :
    CompatibleAssignment y -> (compatibleLabel y i).Realization := fun a =>
  ⟨(a.1 i, restrictAway i a.1), by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_, by simp [compatibleLabel], ?_⟩
      · intro j k hjk
        apply Subtype.ext
        exact a.2.1 hjk
      · intro j hji
        exact j.2 (a.2.1 hji)
      · simp [compatibleLabel]
    · intro j k hjk
      apply Subtype.ext
      exact a.2.2 hjk
    · intro j t ht
      have hti : t = y i := by simpa [compatibleLabel] using ht
      subst t
      intro hbad
      exact j.2 (a.2.2 hbad)⟩

def realizationToCompatibleAssignment
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) :
    (compatibleLabel y i).Realization -> CompatibleAssignment y := fun z =>
  ⟨insertAt i z.1.1 z.1.2, by
    rcases z.2 with ⟨hleft, hrightInj, hrightLinks⟩
    constructor
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact hki.symm
        · exfalso
          have hk : insertAt i z.1.1 z.1.2 k = z.1.2 ⟨k, hki⟩ := by simp [hki]
          exact hleft.2.1 ⟨k, hki⟩ (by simpa [hk] using hjk.symm)
      · by_cases hki : k = i
        · subst k
          exfalso
          have hj : insertAt i z.1.1 z.1.2 j = z.1.2 ⟨j, hji⟩ := by simp [hji]
          exact hleft.2.1 ⟨j, hji⟩ (by simpa [hj] using hjk)
        · have heq : z.1.2 ⟨j, hji⟩ = z.1.2 ⟨k, hki⟩ := by
            simpa [insertAt, hji, hki] using hjk
          exact congrArg Subtype.val (hleft.1 heq)
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact hki.symm
        · exfalso
          have havoid := hrightLinks ⟨k, hki⟩ (y i) (by simp [compatibleLabel])
          apply havoid
          simpa [insertAt, hki, compatibleLabel] using hjk.symm
      · by_cases hki : k = i
        · subst k
          exfalso
          have havoid := hrightLinks ⟨j, hji⟩ (y i) (by simp [compatibleLabel])
          apply havoid
          simpa [insertAt, hji, compatibleLabel] using hjk
        · have heq :
              z.1.2 ⟨j, hji⟩ + (compatibleLabel y i).base ⟨j, hji⟩ =
                z.1.2 ⟨k, hki⟩ + (compatibleLabel y i).base ⟨k, hki⟩ := by
              simpa [insertAt, hji, hki, compatibleLabel] using hjk
          exact congrArg Subtype.val (hrightInj heq)⟩

theorem compatibleAssignmentToRealization_leftInverse
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) (a : CompatibleAssignment y) :
    realizationToCompatibleAssignment y i
      (compatibleAssignmentToRealization y i a) = a := by
  apply Subtype.ext
  exact insertAt_restrictAway i a.1

theorem compatibleAssignmentToRealization_rightInverse
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) (z : (compatibleLabel y i).Realization) :
    compatibleAssignmentToRealization y i
      (realizationToCompatibleAssignment y i z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · simp [realizationToCompatibleAssignment,
      compatibleAssignmentToRealization]
  · simp [realizationToCompatibleAssignment,
      compatibleAssignmentToRealization]

/-- Exact bijection underlying DNS Theorem 3: a one-linked realization is a
compatible hidden assignment, with no probability or asymptotic reasoning. -/
def compatibleAssignmentEquiv
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) :
    CompatibleAssignment y ≃ (compatibleLabel y i).Realization where
  toFun := compatibleAssignmentToRealization y i
  invFun := realizationToCompatibleAssignment y i
  left_inv := compatibleAssignmentToRealization_leftInverse y i
  right_inv := compatibleAssignmentToRealization_rightInverse y i

theorem compatible_count_eq_label_count {q : Nat}
    (y : Fin q -> G) (i : Fin q) :
    RandomSystems.SoP.compatible_count G y = (compatibleLabel y i).count := by
  classical
  rw [Label.count]
  rw [← Fintype.card_congr (compatibleAssignmentEquiv y i)]
  unfold CompatibleAssignment RandomSystems.SoP.compatible_count
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext a
  simp

theorem compatible_count_div_pow_eq_label_prob {q : Nat}
    (y : Fin q -> G) (i : Fin q) :
    (RandomSystems.SoP.compatible_count G y : Real) /
        (Fintype.card G : Real) ^ q =
      (compatibleLabel y i).prob := by
  rw [compatible_count_eq_label_count y i]
  unfold Label.prob
  congr 1
  rw [card_without]
  have hq : 0 < q := Nat.pos_of_ne_zero (fun h => by simpa [h] using i.isLt)
  simp [Fintype.card_fin, Nat.sub_add_cancel (by omega : 1 <= q)]

/-! ### DNS Lemma 9: one link versus zero links -/

def zeroLabel {J : Type*} [Fintype J] (y : J -> G) : Label J G where
  base := y
  left := ∅
  right := ∅

def FreshFor {J : Type*} [Fintype J] (a : J -> G) :=
  {t : G // ∀ j, t ≠ a j}

noncomputable instance freshForFintype
    {J : Type*} [Fintype J] (a : J -> G) : Fintype (FreshFor a) := by
  classical
  unfold FreshFor
  infer_instance

def zeroRealizationToPieces
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) :
    (zeroLabel y).Realization ->
      Σ a : CompatibleAssignment y, FreshFor a.1 := fun z =>
  ⟨⟨z.1.2, by
      exact ⟨z.2.1.1, by simpa [zeroLabel] using z.2.2.1⟩⟩,
    ⟨z.1.1, fun j h => z.2.1.2.1 j h.symm⟩⟩

def zeroPiecesToRealization
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) :
    (Σ a : CompatibleAssignment y, FreshFor a.1) ->
      (zeroLabel y).Realization := fun z =>
  ⟨(z.2.1, z.1.1), by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨z.1.2.1, fun j h => z.2.2 j h.symm, by simp [zeroLabel], by simp [zeroLabel]⟩
    · simpa [zeroLabel] using z.1.2.2
    · simp [zeroLabel]⟩

theorem zeroRealizationToPieces_leftInverse
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (z : (zeroLabel y).Realization) :
    zeroPiecesToRealization y (zeroRealizationToPieces y z) = z := by
  rfl

theorem zeroRealizationToPieces_rightInverse
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (z : Σ a : CompatibleAssignment y, FreshFor a.1) :
    zeroRealizationToPieces y (zeroPiecesToRealization y z) = z := by
  rfl

def zeroRealizationEquiv
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) :
    (zeroLabel y).Realization ≃
      Σ a : CompatibleAssignment y, FreshFor a.1 where
  toFun := zeroRealizationToPieces y
  invFun := zeroPiecesToRealization y
  left_inv := zeroRealizationToPieces_leftInverse y
  right_inv := zeroRealizationToPieces_rightInverse y

theorem card_freshFor_of_injective
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : J -> G) (ha : Function.Injective a) :
    Fintype.card (FreshFor a) = Fintype.card G - Fintype.card J := by
  classical
  unfold FreshFor
  rw [Fintype.card_subtype]
  let image : Finset G := Finset.univ.image a
  calc
    ((Finset.univ : Finset G).filter (fun t => ∀ j, t ≠ a j)).card =
        ((Finset.univ : Finset G) \ image).card := by
          apply congrArg Finset.card
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff, Finset.mem_image, not_exists, not_and,
            image, forall_exists_index]
          constructor
          · intro h j
            exact fun hj => h j hj.symm
          · intro h j
            exact fun hj => h j hj.symm
    _ = Fintype.card G - image.card := by
      rw [Finset.card_sdiff]
      simp [image]
    _ = Fintype.card G - Fintype.card J := by
      rw [Finset.card_image_of_injective _ ha]
      simp [image]

theorem zeroLabel_count
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) :
    (zeroLabel y).count =
      (compatibleLabel y i).count * (Fintype.card G - Fintype.card J) := by
  classical
  rw [Label.count]
  rw [Fintype.card_congr (zeroRealizationEquiv y)]
  rw [Fintype.card_sigma]
  calc
    ∑ a : CompatibleAssignment y, Fintype.card (FreshFor a.1) =
        ∑ _a : CompatibleAssignment y,
          (Fintype.card G - Fintype.card J) := by
          apply Finset.sum_congr rfl
          intro a _
          exact card_freshFor_of_injective a.1 a.2.1
    _ = Fintype.card (CompatibleAssignment y) *
          (Fintype.card G - Fintype.card J) := by simp
    _ = (compatibleLabel y i).count *
          (Fintype.card G - Fintype.card J) := by
          rw [Label.count, ← Fintype.card_congr (compatibleAssignmentEquiv y i)]

/-- DNS Lemma 9, in the exact normalization used later. -/
theorem zeroLabel_prob_eq_compatibleLabel_prob_mul
    {J : Type*} [Fintype J] [DecidableEq J]
    (y : J -> G) (i : J) :
    (zeroLabel y).prob = (compatibleLabel y i).prob *
      (1 - (Fintype.card J : Real) / (Fintype.card G : Real)) := by
  have hJ : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hJG : Fintype.card J <= Fintype.card G ∨
      Fintype.card G < Fintype.card J := le_or_gt _ _
  rcases hJG with hle | hlt
  · unfold Label.prob
    rw [zeroLabel_count y i]
    rw [card_without]
    rw [Nat.sub_add_cancel (by omega : 1 <= Fintype.card J)]
    rw [pow_succ]
    push_cast [Nat.cast_sub hle]
    have hG : (Fintype.card G : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    field_simp
  · letI : IsEmpty (CompatibleAssignment y) :=
      ⟨fun a => (not_le_of_gt hlt)
        (Fintype.card_le_of_injective a.1 a.2.1)⟩
    have hone : (compatibleLabel y i).count = 0 := by
      rw [Label.count, ← Fintype.card_congr (compatibleAssignmentEquiv y i)]
      exact Fintype.card_eq_zero
    have hzero : (zeroLabel y).count = 0 := by
      rw [zeroLabel_count y i, hone]
      simp
    unfold Label.prob
    rw [hone, hzero]
    simp

/-! ### Collapsing a pair of links -/

def oneLabel (base : I -> G) (link : G) : Label I G where
  base := base
  left := ∅
  right := {link}

def Label.collapseLinksMap
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    (x y : G) (hx : x ∈ L.left) (hy : y ∈ L.right) :
    L.Realization -> (oneLabel L.base (x + y)).Realization := fun z =>
  ⟨(z.1.1 + x, z.1.2), by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨z.2.1.1,
        fun i h => z.2.1.2.2.2 i x hx (by simpa using h),
        by simp [oneLabel], by simp [oneLabel]⟩
    · exact z.2.2.1
    · intro i t ht
      have htxy : t = x + y := by simpa [oneLabel] using ht
      subst t
      have havoid := z.2.2.2 i y hy
      intro hbad
      apply havoid
      calc
        z.1.2 i + L.base i = (z.1.1 + x) + (x + y) := hbad
        _ = z.1.1 + ((x + x) + y) := by abel
        _ = z.1.1 + y := by rw [hxor]; simp⟩

theorem Label.collapseLinksMap_injective
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    (x y : G) (hx : x ∈ L.left) (hy : y ∈ L.right) :
    Function.Injective (L.collapseLinksMap hxor x y hx hy) := by
  intro a b hab
  apply Subtype.ext
  have hv := congrArg Subtype.val hab
  apply Prod.ext
  · apply add_right_cancel (b := x)
    simpa [Label.collapseLinksMap] using congrArg Prod.fst hv
  · simpa [Label.collapseLinksMap] using congrArg Prod.snd hv

/-- The event-monotonicity step in DNS Lemma 10: retaining one left and one
right link and recentering `r0` embeds every realization into the one-linked
label carrying their XOR. -/
theorem Label.prob_le_collapseLinks
    (hxor : ∀ g : G, g + g = 0) (L : Label I G)
    (x y : G) (hx : x ∈ L.left) (hy : y ∈ L.right) :
    L.prob <= (oneLabel L.base (x + y)).prob := by
  have hcard : L.count <= (oneLabel L.base (x + y)).count := by
    rw [Label.count, Label.count]
    exact Fintype.card_le_of_injective
      (L.collapseLinksMap hxor x y hx hy)
      (L.collapseLinksMap_injective hxor x y hx hy)
  unfold Label.prob
  gcongr

/-! ### Inserting one base coordinate -/

def optionInsert (x : G) (r : I -> G) : Option I -> G
  | none => x
  | some i => r i

def Label.extendBase (L : Label I G) (b : G) : Label (Option I) G where
  base
    | none => b
    | some i => L.base i
  left := L.left
  right := L.right

def Label.extensionBudget (L : Label I G) : Nat :=
  1 + 2 * Fintype.card I + L.left.card + L.right.card

def Label.extensionForbidden (L : Label I G) (b : G)
    (z : L.Realization) : Finset G :=
  {z.1.1} ∪
    Finset.univ.image z.1.2 ∪
    L.left.image (fun s => z.1.1 + s) ∪
    Finset.univ.image (fun i => (z.1.2 i + L.base i) - b) ∪
    L.right.image (fun t => (z.1.1 + t) - b)

theorem Label.card_extensionForbidden_le (L : Label I G) (b : G)
    (z : L.Realization) :
    (L.extensionForbidden b z).card <= L.extensionBudget := by
  classical
  let A : Finset G := {z.1.1}
  let B : Finset G := Finset.univ.image z.1.2
  let C : Finset G := L.left.image (fun s => z.1.1 + s)
  let D : Finset G :=
    Finset.univ.image (fun i => (z.1.2 i + L.base i) - b)
  let E : Finset G := L.right.image (fun t => (z.1.1 + t) - b)
  have hAB := Finset.card_union_le A B
  have hABC := Finset.card_union_le (A ∪ B) C
  have hABCD := Finset.card_union_le (A ∪ B ∪ C) D
  have hABCDE := Finset.card_union_le (A ∪ B ∪ C ∪ D) E
  have hA : A.card = 1 := by simp [A]
  have hB : B.card <= Fintype.card I := by
    calc
      B.card <= (Finset.univ : Finset I).card := by
        simpa [B] using Finset.card_image_le (f := z.1.2) (s := (Finset.univ : Finset I))
      _ = Fintype.card I := Finset.card_univ
  have hC : C.card <= L.left.card := Finset.card_image_le
  have hD : D.card <= Fintype.card I := by
    calc
      D.card <= (Finset.univ : Finset I).card := by
        simpa [D] using Finset.card_image_le
          (f := fun i : I => (z.1.2 i + L.base i) - b)
          (s := (Finset.univ : Finset I))
      _ = Fintype.card I := Finset.card_univ
  have hE : E.card <= L.right.card := Finset.card_image_le
  change (A ∪ B ∪ C ∪ D ∪ E).card <=
    1 + 2 * Fintype.card I + L.left.card + L.right.card
  omega

theorem Label.good_extendBase_of_not_mem (L : Label I G) (b x : G)
    (z : L.Realization) (hx : x ∉ L.extensionForbidden b z) :
    (L.extendBase b).Good (z.1.1, optionInsert x z.1.2) := by
  classical
  have hx0 : x ≠ z.1.1 := by
    intro h
    apply hx
    simp [Label.extensionForbidden, h]
  have hxBase (i : I) : x ≠ z.1.2 i := by
    intro h
    apply hx
    simp [Label.extensionForbidden, h]
  have hxLeft (s : G) (hs : s ∈ L.left) : x ≠ z.1.1 + s := by
    intro h
    apply hx
    simp [Label.extensionForbidden, h, hs]
  have hxRightBase (i : I) : x + b ≠ z.1.2 i + L.base i := by
    intro h
    have hpre : x = (z.1.2 i + L.base i) - b := by
      apply add_right_cancel (b := b)
      simpa using h
    apply hx
    simp [Label.extensionForbidden, hpre]
  have hxRight (t : G) (ht : t ∈ L.right) : x + b ≠ z.1.1 + t := by
    intro h
    have hpre : x = (z.1.1 + t) - b := by
      apply add_right_cancel (b := b)
      simpa using h
    apply hx
    simp [Label.extensionForbidden, hpre, ht]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, z.2.1.2.2.1, ?_⟩
    · intro i j hij
      cases i with
      | none =>
          cases j with
          | none => rfl
          | some j => exact (hxBase j hij).elim
      | some i =>
          cases j with
          | none => exact (hxBase i hij.symm).elim
          | some j => exact congrArg Option.some (z.2.1.1 hij)
    · intro i
      cases i with
      | none => exact hx0
      | some i => exact z.2.1.2.1 i
    · intro i s hs
      cases i with
      | none => exact hxLeft s hs
      | some i => exact z.2.1.2.2.2 i s hs
  · intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j => exact (hxRightBase j hij).elim
    | some i =>
        cases j with
        | none => exact (hxRightBase i hij.symm).elim
        | some j => exact congrArg Option.some (z.2.2.1 hij)
  · intro i t ht
    cases i with
    | none => exact hxRight t ht
    | some i => exact z.2.2.2 i t ht

def Label.ExtensionValue (L : Label I G) (b : G) (z : L.Realization) :=
  {x : G // (L.extendBase b).Good (z.1.1, optionInsert x z.1.2)}

noncomputable instance Label.extensionValueFintype
    (L : Label I G) (b : G) (z : L.Realization) :
    Fintype (L.ExtensionValue b z) := by
  classical
  unfold Label.ExtensionValue
  infer_instance

theorem Label.card_extensionValue_lower (L : Label I G) (b : G)
    (z : L.Realization) :
    Fintype.card G - L.extensionBudget <=
      Fintype.card (L.ExtensionValue b z) := by
  classical
  let Allowed := {x : G // x ∉ L.extensionForbidden b z}
  let embed : Allowed -> L.ExtensionValue b z := fun x =>
    ⟨x.1, L.good_extendBase_of_not_mem b x.1 z x.2⟩
  have hinj : Function.Injective embed := by
    intro x y h
    apply Subtype.ext
    simpa [embed] using congrArg Subtype.val h
  have hallowed : Fintype.card Allowed =
      Fintype.card G - (L.extensionForbidden b z).card := by
    unfold Allowed
    rw [Fintype.card_subtype]
    calc
      ((Finset.univ : Finset G).filter
          (fun x => x ∉ L.extensionForbidden b z)).card =
          ((Finset.univ : Finset G) \ L.extensionForbidden b z).card := by
            apply congrArg Finset.card
            ext x
            simp
      _ = Fintype.card G - (L.extensionForbidden b z).card := by
        rw [Finset.card_sdiff]
        simp
  calc
    Fintype.card G - L.extensionBudget <=
        Fintype.card G - (L.extensionForbidden b z).card := by
          exact Nat.sub_le_sub_left (L.card_extensionForbidden_le b z) _
    _ = Fintype.card Allowed := hallowed.symm
    _ <= Fintype.card (L.ExtensionValue b z) :=
      Fintype.card_le_of_injective embed hinj

def Label.extendRealizationToPieces (L : Label I G) (b : G) :
    (L.extendBase b).Realization ->
      Σ z : L.Realization, L.ExtensionValue b z := fun w =>
  let zval : G × (I -> G) := (w.1.1, fun i => w.1.2 (some i))
  let z : L.Realization := ⟨zval, by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨fun _ _ h => Option.some.inj (w.2.1.1 h),
        fun i h => w.2.1.2.1 (some i) h,
        w.2.1.2.2.1,
        fun i s hs => w.2.1.2.2.2 (some i) s hs⟩
    · exact fun _ _ h => Option.some.inj (w.2.2.1 h)
    · exact fun i t ht => w.2.2.2 (some i) t ht⟩
  ⟨z, ⟨w.1.2 none, by
    change (L.extendBase b).Good
      (w.1.1, optionInsert (w.1.2 none) (fun i => w.1.2 (some i)))
    have hpair :
        (w.1.1, optionInsert (w.1.2 none) (fun i => w.1.2 (some i))) = w.1 := by
      apply Prod.ext
      · rfl
      · funext j
        cases j <;> rfl
    rw [hpair]
    exact w.2⟩⟩

def Label.extendPiecesToRealization (L : Label I G) (b : G) :
    (Σ z : L.Realization, L.ExtensionValue b z) ->
      (L.extendBase b).Realization := fun z =>
  ⟨(z.1.1.1, optionInsert z.2.1 z.1.1.2), z.2.2⟩

theorem Label.extendRealizationToPieces_leftInverse
    (L : Label I G) (b : G) (w : (L.extendBase b).Realization) :
    L.extendPiecesToRealization b (L.extendRealizationToPieces b w) = w := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    cases j <;> rfl

theorem Label.extendRealizationToPieces_rightInverse
    (L : Label I G) (b : G)
    (z : Σ z : L.Realization, L.ExtensionValue b z) :
    L.extendRealizationToPieces b (L.extendPiecesToRealization b z) = z := by
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · rfl

def Label.extendRealizationEquiv (L : Label I G) (b : G) :
    (L.extendBase b).Realization ≃
      Σ z : L.Realization, L.ExtensionValue b z where
  toFun := L.extendRealizationToPieces b
  invFun := L.extendPiecesToRealization b
  left_inv := L.extendRealizationToPieces_leftInverse b
  right_inv := L.extendRealizationToPieces_rightInverse b

theorem Label.count_extendBase_lower (L : Label I G) (b : G) :
    L.count * (Fintype.card G - L.extensionBudget) <=
      (L.extendBase b).count := by
  classical
  rw [Label.count, Label.count]
  rw [Fintype.card_congr (L.extendRealizationEquiv b)]
  rw [Fintype.card_sigma]
  calc
    Fintype.card L.Realization *
        (Fintype.card G - L.extensionBudget) =
      ∑ _z : L.Realization,
        (Fintype.card G - L.extensionBudget) := by simp
    _ <= ∑ z : L.Realization, Fintype.card (L.ExtensionValue b z) := by
      exact Finset.sum_le_sum fun z _ => L.card_extensionValue_lower b z

/-- Generic insertion inequality.  It remains valid when the displayed factor
is negative; in that case it follows just from nonnegativity. -/
theorem Label.prob_extendBase_lower (L : Label I G) (b : G) :
    L.prob *
        (1 - (L.extensionBudget : Real) / (Fintype.card G : Real)) <=
      (L.extendBase b).prob := by
  have hG : (0 : Real) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  by_cases hbudget : L.extensionBudget <= Fintype.card G
  · have hcount := L.count_extendBase_lower b
    have hcountR : (L.count : Real) *
          ((Fintype.card G - L.extensionBudget : Nat) : Real) <=
        ((L.extendBase b).count : Real) := by exact_mod_cast hcount
    push_cast [Nat.cast_sub hbudget] at hcountR
    have hG0 : (Fintype.card G : Real) ≠ 0 := ne_of_gt hG
    unfold Label.prob
    rw [Fintype.card_option]
    change (L.count : Real) /
          (Fintype.card G : Real) ^ (Fintype.card I + 1) *
        (1 - (L.extensionBudget : Real) / (Fintype.card G : Real)) <=
      ((L.extendBase b).count : Real) /
        (Fintype.card G : Real) ^ (Fintype.card I + 1 + 1)
    calc
      (L.count : Real) /
            (Fintype.card G : Real) ^ (Fintype.card I + 1) *
          (1 - (L.extensionBudget : Real) / (Fintype.card G : Real)) =
        ((L.count : Real) *
            ((Fintype.card G : Real) - L.extensionBudget)) /
          (Fintype.card G : Real) ^ (Fintype.card I + 1 + 1) := by
            field_simp
            ring
      _ <= ((L.extendBase b).count : Real) /
          (Fintype.card G : Real) ^ (Fintype.card I + 1 + 1) :=
        div_le_div_of_nonneg_right hcountR (by positivity)
  · have hfactor :
        1 - (L.extensionBudget : Real) / (Fintype.card G : Real) <= 0 := by
      rw [sub_nonpos]
      rw [le_div_iff₀ hG]
      simpa using (show Fintype.card G <= L.extensionBudget from
        Nat.le_of_lt (Nat.lt_of_not_ge hbudget))
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos L.prob_nonneg hfactor)
      (L.extendBase b).prob_nonneg

theorem oneLabel_extensionBudget (base : I -> G) (link : G) :
    (oneLabel base link).extensionBudget = 2 * (Fintype.card I + 1) := by
  simp [Label.extensionBudget, oneLabel]
  omega

/-- The first half of DNS Lemma 10 for one insertion. -/
theorem oneLabel_prob_extend_lower (base : I -> G) (link b : G) :
    (oneLabel base link).prob *
        (1 - (2 * (Fintype.card I + 1) : Nat) /
          (Fintype.card G : Real)) <=
      ((oneLabel base link).extendBase b).prob := by
  simpa [oneLabel_extensionBudget] using
    (oneLabel base link).prob_extendBase_lower b

/-! ### Reindexing base coordinates -/

def Label.reindex {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) : Label J G where
  base j := L.base (e j)
  left := L.left
  right := L.right

def Label.reindexRealization
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) :
    L.Realization -> (L.reindex e).Realization := fun z =>
  ⟨(z.1.1, z.1.2 ∘ e), by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨z.2.1.1.comp e.injective,
        fun j => z.2.1.2.1 (e j), z.2.1.2.2.1,
        fun j s hs => z.2.1.2.2.2 (e j) s hs⟩
    · intro j k h
      exact e.injective (z.2.2.1 h)
    · exact fun j t ht => z.2.2.2 (e j) t ht⟩

def Label.unreindexRealization
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) :
    (L.reindex e).Realization -> L.Realization := fun z =>
  ⟨(z.1.1, z.1.2 ∘ e.symm), by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨z.2.1.1.comp e.symm.injective,
        fun i => z.2.1.2.1 (e.symm i), z.2.1.2.2.1,
        fun i s hs => z.2.1.2.2.2 (e.symm i) s hs⟩
    · intro i k h
      have h' :
          z.1.2 (e.symm i) + (L.reindex e).base (e.symm i) =
            z.1.2 (e.symm k) + (L.reindex e).base (e.symm k) := by
        simpa [Label.reindex] using h
      exact e.symm.injective (z.2.2.1 h')
    · intro i t ht
      simpa [Label.reindex] using z.2.2.2 (e.symm i) t ht⟩

theorem Label.unreindex_reindex
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) (z : L.Realization) :
    L.unreindexRealization e (L.reindexRealization e z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    simp [Label.reindexRealization, Label.unreindexRealization]

theorem Label.reindex_unreindex
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) (z : (L.reindex e).Realization) :
    L.reindexRealization e (L.unreindexRealization e z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    simp [Label.reindexRealization, Label.unreindexRealization]

def Label.reindexRealizationEquiv
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) :
    L.Realization ≃ (L.reindex e).Realization where
  toFun := L.reindexRealization e
  invFun := L.unreindexRealization e
  left_inv := L.unreindex_reindex e
  right_inv := L.reindex_unreindex e

theorem Label.count_reindex
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) :
    (L.reindex e).count = L.count := by
  rw [Label.count, Label.count]
  exact Fintype.card_congr (L.reindexRealizationEquiv e).symm

theorem Label.prob_reindex
    {J : Type*} [Fintype J] [DecidableEq J]
    (L : Label I G) (e : J ≃ I) :
    (L.reindex e).prob = L.prob := by
  unfold Label.prob
  rw [L.count_reindex e]
  rw [Fintype.card_congr e]

/-! ### One-linked subtuples of a fixed master tuple -/

def activeOneLabel {q : Nat} (gamma : Fin q -> G)
    (A : Finset (Fin q)) (p : Fin q) : Label {i // i ∈ A} G :=
  oneLabel (fun i => gamma i.1) (gamma p)

theorem activeOneLabel_empty_prob
    {q : Nat} (gamma : Fin q -> G) (p : Fin q) :
    (activeOneLabel gamma ∅ p).prob = 1 := by
  let J := {j : Fin q // j ∈ (∅ : Finset (Fin q))}
  have hempty (i : J) : False := Finset.notMem_empty i.1 i.2
  let emptyFun : J -> G := fun i => (hempty i).elim
  have hgood (r0 : G) : (activeOneLabel gamma ∅ p).Good (r0, emptyFun) := by
    refine ⟨⟨?_, ?_, by simp [activeOneLabel, oneLabel], ?_⟩, ?_, ?_⟩
    · intro i
      exact (hempty i).elim
    · intro i
      exact (hempty i).elim
    · intro i
      exact (hempty i).elim
    · intro i
      exact (hempty i).elim
    · intro i
      exact (hempty i).elim
  let toF : (activeOneLabel gamma ∅ p).Realization -> G := fun z => z.1.1
  let invF : G -> (activeOneLabel gamma ∅ p).Realization :=
    fun r0 => ⟨(r0, emptyFun), hgood r0⟩
  have hleft : Function.LeftInverse invF toF := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact (hempty i).elim
  have hright : Function.RightInverse invF toF := by
    intro r0
    rfl
  let e : (activeOneLabel gamma ∅ p).Realization ≃ G :=
    ⟨toF, invF, hleft, hright⟩
  unfold Label.prob Label.count
  rw [Fintype.card_congr e]
  simp

def finsetInsertEquiv {q : Nat} (A : Finset (Fin q)) (j : Fin q)
    (hj : j ∉ A) : Option {i // i ∈ A} ≃ {i // i ∈ insert j A} where
  toFun
    | none => ⟨j, Finset.mem_insert_self j A⟩
    | some i => ⟨i.1, Finset.mem_insert_of_mem i.2⟩
  invFun i := if h : i.1 = j then none else
    some ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
  left_inv i := by
    cases i with
    | none => simp
    | some i =>
        have hne : i.1 ≠ j := fun h => hj (h ▸ i.2)
        simp [hne]
  right_inv i := by
    by_cases h : i.1 = j
    · apply Subtype.ext
      simp [h]
    · apply Subtype.ext
      simp [h]

theorem activeOneLabel_insert_eq_reindex
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q))
    (p j : Fin q) (hj : j ∉ A) :
    activeOneLabel gamma (insert j A) p =
      ((activeOneLabel gamma A p).extendBase (gamma j)).reindex
        (finsetInsertEquiv A j hj).symm := by
  unfold activeOneLabel oneLabel Label.extendBase Label.reindex
  rw [Label.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  funext i
  by_cases h : i.1 = j
  · simp [finsetInsertEquiv, h]
  · simp [finsetInsertEquiv, h]

theorem activeOneLabel_prob_insert_lower
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q))
    (p j : Fin q) (hj : j ∉ A) :
    (activeOneLabel gamma A p).prob *
        (1 - (2 * (A.card + 1) : Nat) / (Fintype.card G : Real)) <=
      (activeOneLabel gamma (insert j A) p).prob := by
  have hcard : Fintype.card {i // i ∈ A} = A.card := by simp
  have hins := oneLabel_prob_extend_lower
    (G := G) (base := fun i : {i // i ∈ A} => gamma i.1)
    (link := gamma p) (b := gamma j)
  rw [activeOneLabel_insert_eq_reindex gamma A p j hj,
    Label.prob_reindex]
  simpa [activeOneLabel, hcard] using hins

theorem activeOneLabel_prob_insert_masterFactor_lower
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q))
    (p j : Fin q) (hp : p ∉ A) (hj : j ∉ insert p A) :
    (activeOneLabel gamma A p).prob *
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) <=
      (activeOneLabel gamma (insert j A) p).prob := by
  have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
  have hcard : A.card + 1 <= q := by
    have hinsert : (insert p A).card <= Fintype.card (Fin q) :=
      Finset.card_le_univ (insert p A)
    rw [Finset.card_insert_of_notMem hp, Fintype.card_fin] at hinsert
    exact hinsert
  have hfactor :
      1 - (2 * q : Nat) / (Fintype.card G : Real) <=
        1 - (2 * (A.card + 1) : Nat) / (Fintype.card G : Real) := by
    have hG : (0 : Real) < Fintype.card G := by positivity
    gcongr
  calc
    (activeOneLabel gamma A p).prob *
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) <=
        (activeOneLabel gamma A p).prob *
          (1 - (2 * (A.card + 1) : Nat) / (Fintype.card G : Real)) :=
      mul_le_mul_of_nonneg_left hfactor (activeOneLabel gamma A p).prob_nonneg
    _ <= (activeOneLabel gamma (insert j A) p).prob :=
      activeOneLabel_prob_insert_lower gamma A p j hjA

def eraseSubtypeEquiv {q : Nat} (p : Fin q) :
    {i // i ∈ (Finset.univ : Finset (Fin q)).erase p} ≃ Without p where
  toFun i := ⟨i.1, (Finset.mem_erase.mp i.2).1⟩
  invFun i := ⟨i.1, Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩⟩
  left_inv i := rfl
  right_inv i := rfl

theorem activeOneLabel_full_prob_eq_compatibleLabel
    {q : Nat} (gamma : Fin q -> G) (p : Fin q) :
    (activeOneLabel gamma (Finset.univ.erase p) p).prob =
      (compatibleLabel gamma p).prob := by
  let e := eraseSubtypeEquiv p
  have heq : (activeOneLabel gamma (Finset.univ.erase p) p).reindex e.symm =
      compatibleLabel gamma p := by
    unfold activeOneLabel oneLabel compatibleLabel Label.reindex
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    funext i
    rfl
  rw [← heq, Label.prob_reindex]

/-- Iterated form of DNS Lemma 10, specialized to a literal subtuple of one
fixed master tuple. -/
theorem activeOneLabel_mul_masterFactor_pow_le
    {q d : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) (hd : q - (A.card + 1) = d)
    (hfactor : 0 <= 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (activeOneLabel gamma A p).prob *
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d <=
      (compatibleLabel gamma p).prob := by
  induction d generalizing A with
  | zero =>
      have hcardLe : A.card + 1 <= q := by
        have hinsert : (insert p A).card <= Fintype.card (Fin q) :=
          Finset.card_le_univ (insert p A)
        rw [Finset.card_insert_of_notMem hp, Fintype.card_fin] at hinsert
        exact hinsert
      have hcardEq : A.card + 1 = q := by omega
      have hset : A = Finset.univ.erase p := by
        have hsub : A ⊆ Finset.univ.erase p := by
          intro i hi
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          intro hip
          subst i
          exact hp hi
        apply Finset.eq_of_subset_of_card_le hsub
        simp
        omega
      rw [pow_zero, mul_one, hset,
        activeOneLabel_full_prob_eq_compatibleLabel]
  | succ d ih =>
      have hcardLe : A.card + 1 <= q := by
        have hinsert : (insert p A).card <= Fintype.card (Fin q) :=
          Finset.card_le_univ (insert p A)
        rw [Finset.card_insert_of_notMem hp, Fintype.card_fin] at hinsert
        exact hinsert
      have hcardLt : A.card + 1 < q := by omega
      have hex : ∃ j : Fin q, j ∉ insert p A := by
        by_contra hnone
        push_neg at hnone
        have hall : insert p A = Finset.univ := Finset.eq_univ_of_forall hnone
        have := congrArg Finset.card hall
        rw [Finset.card_insert_of_notMem hp, Finset.card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨j, hj⟩ := hex
      have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
      have hjp : j ≠ p := fun h => hj (by simp [h])
      have hp' : p ∉ insert j A := by simp [hp, hjp.symm]
      have hd' : q - ((insert j A).card + 1) = d := by
        rw [Finset.card_insert_of_notMem hjA]
        omega
      have hstep := activeOneLabel_prob_insert_masterFactor_lower
        gamma A p j hp hj
      have htail := ih (insert j A) hp' hd'
      rw [pow_succ]
      have hpow : 0 <=
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := pow_nonneg hfactor d
      calc
        (activeOneLabel gamma A p).prob *
            ((1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d *
              (1 - (2 * q : Nat) / (Fintype.card G : Real))) =
          ((activeOneLabel gamma A p).prob *
              (1 - (2 * q : Nat) / (Fintype.card G : Real))) *
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by ring
        _ <= (activeOneLabel gamma (insert j A) p).prob *
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
          mul_le_mul_of_nonneg_right hstep hpow
        _ <= (compatibleLabel gamma p).prob := htail

theorem activeOneLabel_prob_le_div_masterFactor_pow
    {q d : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) (hd : q - (A.card + 1) = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (activeOneLabel gamma A p).prob <=
      (compatibleLabel gamma p).prob /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
  rw [le_div_iff₀ (pow_pos hfactor d)]
  exact activeOneLabel_mul_masterFactor_pow_le gamma A p hp hd hfactor.le

/-! ### Differential witnesses -/

/-- One concrete term in DNS Definition 2.  The base coordinates are a
literal active subset of the fixed master tuple, and `pivot` is the master
coordinate introduced by double-link separation. -/
structure DiffWitness {q : Nat} (gamma : Fin q -> G) (alpha ell : Nat) where
  active : Finset (Fin q)
  pivot : Fin q
  pivot_not_active : pivot ∉ active
  active_card : active.card + 1 = alpha
  left : Finset G
  right : Finset G
  /-- A zero left link duplicates the distinguished value `r0`, so it is not
  a DNS label that can contribute to the core deletion sum. -/
  left_nonzero : 0 ∉ left
  x : G
  y : G
  x_mem : x ∈ left
  y_mem : y ∈ right
  pair_eq : x + y = gamma pivot
  total_links : left.card + right.card = ell + 2
  balanced : right.card = left.card ∨ right.card = left.card + 1

private structure DiffData (q : Nat) (G : Type u) where
  active : Finset (Fin q)
  pivot : Fin q
  left : Finset G
  right : Finset G
  x : G
  y : G
deriving Fintype

noncomputable instance diffWitnessFintype {q : Nat} (gamma : Fin q -> G)
    (alpha ell : Nat) : Fintype (DiffWitness gamma alpha ell) := by
  classical
  let encode : DiffWitness gamma alpha ell -> DiffData q G := fun w =>
    ⟨w.active, w.pivot, w.left, w.right, w.x, w.y⟩
  apply Fintype.ofInjective encode
  intro a b h
  rcases a with
    ⟨aa, ap, ahp, ahc, al, ar, ahzero, ax, ay, ahx, ahy, ahe, aht, ahb⟩
  rcases b with
    ⟨ba, bp, bhp, bhc, bl, br, bhzero, bx, byv, bhx, bhy, bhe, bht, bhb⟩
  change DiffData.mk aa ap al ar ax ay = DiffData.mk ba bp bl br bx byv at h
  cases h
  rfl

def DiffWitness.label {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) : Label {i // i ∈ w.active} G where
  base i := gamma i.1
  left := w.left
  right := w.right

def DiffWitness.separated {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) :
    Label {i // i ∈ insert w.pivot w.active} G where
  base i := gamma i.1
  left := w.left.erase w.x
  right := w.right.erase w.y

def Label.stripLinks (L : Label I G) : Label I G := zeroLabel L.base

def Label.stripLinksMap (L : Label I G) :
    L.Realization -> L.stripLinks.Realization := fun z =>
  ⟨z.1, by
    exact ⟨⟨z.2.1.1, z.2.1.2.1, by simp [Label.stripLinks, zeroLabel],
      by simp [Label.stripLinks, zeroLabel]⟩,
      z.2.2.1, by simp [Label.stripLinks, zeroLabel]⟩⟩

theorem Label.stripLinksMap_injective (L : Label I G) :
    Function.Injective L.stripLinksMap := by
  intro a b h
  apply Subtype.ext
  simpa [Label.stripLinksMap] using congrArg Subtype.val h

theorem Label.prob_le_stripLinks (L : Label I G) :
    L.prob <= L.stripLinks.prob := by
  unfold Label.prob
  gcongr
  unfold Label.count
  exact Fintype.card_le_of_injective L.stripLinksMap L.stripLinksMap_injective

def activeZeroLabel {q : Nat} (gamma : Fin q -> G)
    (A : Finset (Fin q)) (p : Fin q) :
    Label {i // i ∈ insert p A} G :=
  zeroLabel (fun i => gamma i.1)

def activePivot {q : Nat} (A : Finset (Fin q)) (p : Fin q) :
    {i // i ∈ insert p A} := ⟨p, Finset.mem_insert_self p A⟩

def insertWithoutEquiv {q : Nat} (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) : Without (activePivot A p) ≃ {i // i ∈ A} where
  toFun i := ⟨i.1.1, by
    rcases Finset.mem_insert.mp i.1.2 with h | h
    · exact (i.2 (Subtype.ext h)).elim
    · exact h⟩
  invFun i := ⟨⟨i.1, Finset.mem_insert_of_mem i.2⟩, by
    intro h
    have hv : i.1 = p := by
      simpa [activePivot] using congrArg (fun z => z.1) h
    apply hp
    rw [← hv]
    exact i.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

theorem activeCompatibleLabel_prob_eq_activeOneLabel
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) :
    (compatibleLabel (fun i : {i // i ∈ insert p A} => gamma i.1)
        (activePivot A p)).prob =
      (activeOneLabel gamma A p).prob := by
  let e := insertWithoutEquiv A p hp
  have heq :
      (compatibleLabel (fun i : {i // i ∈ insert p A} => gamma i.1)
        (activePivot A p)).reindex e.symm = activeOneLabel gamma A p := by
    unfold compatibleLabel activeOneLabel oneLabel Label.reindex activePivot
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    funext i
    rfl
  rw [← heq, Label.prob_reindex]

theorem activeZeroLabel_prob_le_activeOneLabel
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) :
    (activeZeroLabel gamma A p).prob <= (activeOneLabel gamma A p).prob := by
  let J := {i // i ∈ insert p A}
  let yy : J -> G := fun i => gamma i.1
  let ip : J := activePivot A p
  have heq := zeroLabel_prob_eq_compatibleLabel_prob_mul yy ip
  have hcardJ : Fintype.card J = A.card + 1 := by
    dsimp [J]
    rw [Fintype.card_coe, Finset.card_insert_of_notMem hp]
  have hfac : 1 - (Fintype.card J : Real) / (Fintype.card G : Real) <= 1 := by
    have : 0 <= (Fintype.card J : Real) / (Fintype.card G : Real) := by positivity
    linarith
  calc
    (activeZeroLabel gamma A p).prob =
        (compatibleLabel yy ip).prob *
          (1 - (Fintype.card J : Real) / (Fintype.card G : Real)) := by
            simpa [activeZeroLabel, yy, ip, J] using heq
    _ <= (compatibleLabel yy ip).prob := by
      nlinarith [(compatibleLabel yy ip).prob_nonneg]
    _ = (activeOneLabel gamma A p).prob := by
      simpa [yy, ip, J] using
        activeCompatibleLabel_prob_eq_activeOneLabel gamma A p hp

theorem activeZeroLabel_prob_eq_activeOneLabel_mul
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) :
    (activeZeroLabel gamma A p).prob =
      (activeOneLabel gamma A p).prob *
        (1 - ((A.card + 1 : Nat) : Real) / (Fintype.card G : Real)) := by
  let J := {i // i ∈ insert p A}
  let yy : J -> G := fun i => gamma i.1
  let ip : J := activePivot A p
  have heq := zeroLabel_prob_eq_compatibleLabel_prob_mul yy ip
  have hcardJ : Fintype.card J = A.card + 1 := by
    dsimp [J]
    rw [Fintype.card_coe, Finset.card_insert_of_notMem hp]
  calc
    (activeZeroLabel gamma A p).prob =
        (compatibleLabel yy ip).prob *
          (1 - (Fintype.card J : Real) / (Fintype.card G : Real)) := by
      simpa [activeZeroLabel, yy, ip, J] using heq
    _ = (activeOneLabel gamma A p).prob *
          (1 - ((A.card + 1 : Nat) : Real) /
            (Fintype.card G : Real)) := by
      rw [activeCompatibleLabel_prob_eq_activeOneLabel gamma A p hp]
      rw [hcardJ]

theorem DiffWitness.label_prob_le_activeOneLabel
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) :
    w.label.prob <= (activeOneLabel gamma w.active w.pivot).prob := by
  have hcollapse := w.label.prob_le_collapseLinks hxor w.x w.y w.x_mem w.y_mem
  simpa [DiffWitness.label, activeOneLabel, w.pair_eq] using hcollapse

theorem DiffWitness.separated_prob_le_activeOneLabel
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) :
    w.separated.prob <= (activeOneLabel gamma w.active w.pivot).prob := by
  calc
    w.separated.prob <= w.separated.stripLinks.prob := w.separated.prob_le_stripLinks
    _ = (activeZeroLabel gamma w.active w.pivot).prob := by
      unfold DiffWitness.separated Label.stripLinks activeZeroLabel zeroLabel
      rfl
    _ <= (activeOneLabel gamma w.active w.pivot).prob :=
      activeZeroLabel_prob_le_activeOneLabel gamma w.active w.pivot
        w.pivot_not_active

def diffValue {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) : NNReal :=
  ⟨|w.label.prob - w.separated.prob|, abs_nonneg _⟩

def differential {q : Nat} (gamma : Fin q -> G) (alpha ell : Nat) : NNReal :=
  Finset.univ.sup (fun w : DiffWitness gamma alpha ell => diffValue w)

def masterProb {q : Nat} (gamma : Fin q -> G) : Real :=
  (RandomSystems.SoP.compatible_count G gamma : Real) /
    (Fintype.card G : Real) ^ q

theorem compatibleLabel_prob_eq_masterProb
    {q : Nat} (gamma : Fin q -> G) (p : Fin q) :
    (compatibleLabel gamma p).prob = masterProb gamma := by
  exact (compatible_count_div_pow_eq_label_prob gamma p).symm

theorem masterProb_nonneg {q : Nat} (gamma : Fin q -> G) :
    0 <= masterProb gamma := by
  unfold masterProb
  positivity

theorem masterProb_pos_of_masterFactor_pos
    {q : Nat} (gamma : Fin q -> G) (p : Fin q)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    0 < masterProb gamma := by
  have hbound := activeOneLabel_mul_masterFactor_pow_le
    (d := q - 1) gamma (∅ : Finset (Fin q)) p (by simp) (by simp) hfactor.le
  rw [activeOneLabel_empty_prob, compatibleLabel_prob_eq_masterProb] at hbound
  have hpow : 0 <
      (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ (q - 1) :=
    pow_pos hfactor _
  simp only [one_mul] at hbound
  exact hpow.trans_le hbound

theorem diffValue_le_differential
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) :
    diffValue w <= differential gamma alpha ell :=
  Finset.le_sup (f := fun w : DiffWitness gamma alpha ell => diffValue w)
    (Finset.mem_univ w)

theorem abs_diff_le_differential
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) :
    |w.label.prob - w.separated.prob| <=
      (differential gamma alpha ell : Real) := by
  exact_mod_cast diffValue_le_differential w

theorem diffValue_le_two_mul_activeOneLabel
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) :
    (diffValue w : Real) <=
      2 * (activeOneLabel gamma w.active w.pivot).prob := by
  change |w.label.prob - w.separated.prob| <= _
  rw [abs_sub_le_iff]
  constructor <;>
    nlinarith [w.label_prob_le_activeOneLabel hxor,
      w.separated_prob_le_activeOneLabel,
      w.label.prob_nonneg, w.separated.prob_nonneg]

theorem differential_le_two_mul_activeOneLabel_bound
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} (gamma : Fin q -> G)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (differential gamma alpha ell : Real) <=
      2 * masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
  let R : Real := 2 * masterProb gamma /
    (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (mul_nonneg (by norm_num) (masterProb_nonneg gamma))
      (pow_nonneg hfactor.le d)
  have hsup : differential gamma alpha ell <= Real.toNNReal R := by
    unfold differential
    apply Finset.sup_le
    intro w _hw
    rw [← NNReal.coe_le_coe]
    rw [Real.coe_toNNReal R hR]
    have hdw : q - (w.active.card + 1) = d := by
      rw [w.active_card]
      exact hd
    have hactive := activeOneLabel_prob_le_div_masterFactor_pow
      gamma w.active w.pivot w.pivot_not_active hdw hfactor
    rw [compatibleLabel_prob_eq_masterProb] at hactive
    have hdiff := diffValue_le_two_mul_activeOneLabel hxor w
    dsimp [R]
    apply le_trans hdiff
    calc
      2 * (activeOneLabel gamma w.active w.pivot).prob <=
          2 * (masterProb gamma /
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d) :=
        mul_le_mul_of_nonneg_left hactive (by norm_num)
      _ = 2 * masterProb gamma /
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by ring
  have hcoe := NNReal.coe_le_coe.mpr hsup
  rw [Real.coe_toNNReal R hR] at hcoe
  exact hcoe

/-! ### Multiplicity and deletion sums -/

def multiplicity {q : Nat} (gamma : Fin q -> G) (v : G) : Nat :=
  ((Finset.univ : Finset (Fin q)).filter (fun i => gamma i = v)).card

def maxMultiplicity {q : Nat} (gamma : Fin q -> G) : Nat :=
  Finset.univ.sup (fun i => multiplicity gamma (gamma i))

theorem multiplicity_le_maxMultiplicity
    {q : Nat} (gamma : Fin q -> G) (v : G) :
    multiplicity gamma v <= maxMultiplicity gamma := by
  classical
  by_cases hempty :
      ((Finset.univ : Finset (Fin q)).filter (fun i => gamma i = v)).Nonempty
  · obtain ⟨i, hi⟩ := hempty
    have hgi : gamma i = v := (Finset.mem_filter.mp hi).2
    rw [← hgi]
    exact Finset.le_sup (f := fun i => multiplicity gamma (gamma i))
      (Finset.mem_univ i)
  · have hzero : multiplicity gamma v = 0 := by
      unfold multiplicity
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    simp [hzero]

theorem card_filter_active_eq_le_maxMultiplicity
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (v : G) :
    (A.filter (fun i => gamma i = v)).card <= maxMultiplicity gamma := by
  apply le_trans (Finset.card_le_card ?_) (multiplicity_le_maxMultiplicity gamma v)
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, hi.2⟩

theorem one_le_maxMultiplicity {q : Nat} (gamma : Fin q -> G) (i : Fin q) :
    1 <= maxMultiplicity gamma := by
  have hmem : i ∈
      (Finset.univ : Finset (Fin q)).filter (fun j => gamma j = gamma i) := by
    simp
  have hone : 1 <= multiplicity gamma (gamma i) := by
    exact Finset.one_le_card.mpr ⟨i, hmem⟩
  exact hone.trans (multiplicity_le_maxMultiplicity gamma (gamma i))

theorem sum_indicator_le_maxMultiplicity_mul
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q))
    (v : G) (R : Real) (hR : 0 <= R) :
    (∑ i : {j // j ∈ A}, if gamma i.1 = v then R else 0) <=
      (maxMultiplicity gamma : Real) * R := by
  let s : Finset {j // j ∈ A} :=
    Finset.univ.filter (fun i => gamma i.1 = v)
  have hcard : s.card <= maxMultiplicity gamma := by
    have hmaps : ∀ i ∈ s,
        i.1 ∈ (Finset.univ : Finset (Fin q)).filter (fun j => gamma j = v) := by
      intro i hi
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    have hinj : Set.InjOn (fun i : {j // j ∈ A} => i.1) ↑s := by
      intro i _ j _ hij
      exact Subtype.ext hij
    have hsle : s.card <= multiplicity gamma v := by
      unfold multiplicity
      exact Finset.card_le_card_of_injOn (fun i : {j // j ∈ A} => i.1)
        hmaps hinj
    exact hsle.trans (multiplicity_le_maxMultiplicity gamma v)
  calc
    (∑ i : {j // j ∈ A}, if gamma i.1 = v then R else 0) =
        ∑ i ∈ s, R := by
      rw [Finset.sum_filter]
    _ = (s.card : Real) * R := by simp
    _ <= (maxMultiplicity gamma : Real) * R := by
      gcongr

def Label.rightDeletionTerm (L : Label I G) (x : G) (i : I) : Real :=
  if h : x + L.base i ∉ L.left then (L.pushRight i x).prob else 0

def Label.leftDeletionTerm (L : Label I G) (x : G) (i : I) : Real :=
  if h : x + L.base i ∉ L.right then (L.pushLeft i x).prob else 0

theorem Label.sum_rightDeletionTerm (L : Label I G) (x : G) :
    ∑ i : I, L.rightDeletionTerm x i =
      ∑ i : L.RightEligible x, (L.pushRight i.1 x).prob := by
  classical
  let s : Finset I := Finset.univ.filter (fun i => x + L.base i ∉ L.left)
  calc
    ∑ i : I, L.rightDeletionTerm x i =
        ∑ i ∈ s, (L.pushRight i x).prob := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : x + L.base i ∈ L.left <;>
            simp [Label.rightDeletionTerm, h]
    _ = ∑ i : L.RightEligible x, (L.pushRight i.1 x).prob := by
      apply Finset.sum_subtype s
      intro i
      simp [s, Label.RightEligible]

theorem Label.sum_leftDeletionTerm (L : Label I G) (x : G) :
    ∑ i : I, L.leftDeletionTerm x i =
      ∑ i : L.LeftEligible x, (L.pushLeft i.1 x).prob := by
  classical
  let s : Finset I := Finset.univ.filter (fun i => x + L.base i ∉ L.right)
  calc
    ∑ i : I, L.leftDeletionTerm x i =
        ∑ i ∈ s, (L.pushLeft i x).prob := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : x + L.base i ∈ L.right <;>
            simp [Label.leftDeletionTerm, h]
    _ = ∑ i : L.LeftEligible x, (L.pushLeft i.1 x).prob := by
      apply Finset.sum_subtype s
      intro i
      simp [s, Label.LeftEligible]

theorem Label.prob_eq_prob_eraseRight_sub_terms
    (hxor : ∀ g : G, g + g = 0) (L : Label I G) (x : G)
    (hx : x ∈ L.right) :
    L.prob = (L.eraseRight x).prob -
      (1 / (Fintype.card G : Real)) *
        ∑ i : I, L.rightDeletionTerm x i := by
  rw [L.prob_eq_prob_eraseRight_sub hxor x hx, L.sum_rightDeletionTerm]

theorem Label.prob_eq_prob_eraseLeft_sub_terms
    (L : Label I G) (x : G) (hx : x ∈ L.left) (hx0 : x ≠ 0) :
    L.prob = (L.eraseLeft x).prob -
      (1 / (Fintype.card G : Real)) *
        ∑ i : I, L.leftDeletionTerm x i := by
  rw [L.prob_eq_prob_eraseLeft_sub x hx hx0, L.sum_leftDeletionTerm]

def eraseActiveEquiv {q : Nat} (A : Finset (Fin q)) (i : {j // j ∈ A}) :
    Without i ≃ {j // j ∈ A.erase i.1} where
  toFun j := ⟨j.1.1, Finset.mem_erase.mpr ⟨by
    intro h
    exact j.2 (Subtype.ext h), j.1.2⟩⟩
  invFun j := ⟨⟨j.1, (Finset.mem_erase.mp j.2).2⟩, by
    intro h
    exact (Finset.mem_erase.mp j.2).1 (congrArg Subtype.val h)⟩
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    rfl

def finsetSubtypeEquivOfEq {q : Nat} {A B : Finset (Fin q)} (h : A = B) :
    {i // i ∈ A} ≃ {i // i ∈ B} where
  toFun i := ⟨i.1, h ▸ i.2⟩
  invFun i := ⟨i.1, h.symm ▸ i.2⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

def DiffWitness.eraseRightWitness
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y) (hell : 0 < ell) :
    DiffWitness gamma alpha (ell - 1) where
  active := w.active
  pivot := w.pivot
  pivot_not_active := w.pivot_not_active
  active_card := w.active_card
  left := w.left
  right := w.right.erase z
  left_nonzero := w.left_nonzero
  x := w.x
  y := w.y
  x_mem := w.x_mem
  y_mem := Finset.mem_erase.mpr ⟨hzy.symm, w.y_mem⟩
  pair_eq := w.pair_eq
  total_links := by
    have ht := w.total_links
    rw [Finset.card_erase_of_mem hz]
    omega
  balanced := Or.inl (by
    have ht := w.total_links
    rw [Finset.card_erase_of_mem hz]
    omega)

def DiffWitness.eraseLeftWitness
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x) (hell : 0 < ell) :
    DiffWitness gamma alpha (ell - 1) where
  active := w.active
  pivot := w.pivot
  pivot_not_active := w.pivot_not_active
  active_card := w.active_card
  left := w.left.erase z
  right := w.right
  left_nonzero := fun h => w.left_nonzero (Finset.mem_of_mem_erase h)
  x := w.x
  y := w.y
  x_mem := Finset.mem_erase.mpr ⟨hzx.symm, w.x_mem⟩
  y_mem := w.y_mem
  pair_eq := w.pair_eq
  total_links := by
    have ht := w.total_links
    rw [Finset.card_erase_of_mem hz]
    omega
  balanced := Or.inr (by
    have ht := w.total_links
    rw [Finset.card_erase_of_mem hz]
    omega)

theorem DiffWitness.eraseRight_label_eq
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y) (hell : 0 < ell) :
    w.label.eraseRight z = (w.eraseRightWitness z hbal hz hzy hell).label := by
  rfl

theorem DiffWitness.eraseRight_separated_eq
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y) (hell : 0 < ell) :
    w.separated.eraseRight z =
      (w.eraseRightWitness z hbal hz hzy hell).separated := by
  unfold DiffWitness.separated Label.eraseRight
  change Label.mk (fun i : {i // i ∈ insert w.pivot w.active} => gamma i.1)
      (w.left.erase w.x)
      ((w.right.erase w.y).erase z) =
    Label.mk (fun i : {i // i ∈ insert w.pivot w.active} => gamma i.1)
      (w.left.erase w.x)
      ((w.right.erase z).erase w.y)
  rw [Label.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  ext a
  simp only [Finset.mem_erase]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨h₂, h₁, h₃⟩

theorem DiffWitness.eraseLeft_label_eq
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x) (hell : 0 < ell) :
    w.label.eraseLeft z = (w.eraseLeftWitness z hbal hz hzx hell).label := by
  rfl

theorem DiffWitness.eraseLeft_separated_eq
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x) (hell : 0 < ell) :
    w.separated.eraseLeft z =
      (w.eraseLeftWitness z hbal hz hzx hell).separated := by
  unfold DiffWitness.separated Label.eraseLeft
  change Label.mk (fun i : {i // i ∈ insert w.pivot w.active} => gamma i.1)
      ((w.left.erase w.x).erase z)
      (w.right.erase w.y) =
    Label.mk (fun i : {i // i ∈ insert w.pivot w.active} => gamma i.1)
      ((w.left.erase z).erase w.x)
      (w.right.erase w.y)
  rw [Label.mk.injEq]
  refine ⟨rfl, ?_, rfl⟩
  ext a
  simp only [Finset.mem_erase]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨h₂, h₁, h₃⟩

theorem DiffWitness.abs_eraseRight_diff_le
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y) (hell : 0 < ell) :
    |(w.label.eraseRight z).prob - (w.separated.eraseRight z).prob| <=
      (differential gamma alpha (ell - 1) : Real) := by
  rw [w.eraseRight_label_eq z hbal hz hzy hell,
    w.eraseRight_separated_eq z hbal hz hzy hell]
  exact abs_diff_le_differential (w.eraseRightWitness z hbal hz hzy hell)

theorem DiffWitness.abs_eraseLeft_diff_le
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x) (hell : 0 < ell) :
    |(w.label.eraseLeft z).prob - (w.separated.eraseLeft z).prob| <=
      (differential gamma alpha (ell - 1) : Real) := by
  rw [w.eraseLeft_label_eq z hbal hz hzx hell,
    w.eraseLeft_separated_eq z hbal hz hzx hell]
  exact abs_diff_le_differential (w.eraseLeftWitness z hbal hz hzx hell)

def DiffWitness.rightChild
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (i : {j // j ∈ w.active})
    (hi : z + gamma i.1 ∉ w.left)
    (hi0 : z + gamma i.1 ≠ 0) :
    DiffWitness gamma (alpha - 1) (ell + 1) where
  active := w.active.erase i.1
  pivot := w.pivot
  pivot_not_active := fun h => w.pivot_not_active (Finset.mem_of_mem_erase h)
  active_card := by
    have hc := w.active_card
    have hpos : 0 < w.active.card := Finset.card_pos.mpr ⟨i.1, i.2⟩
    rw [Finset.card_erase_of_mem i.2]
    omega
  left := insert (z + gamma i.1) w.left
  right := w.right
  left_nonzero := by simpa [hi0, hi0.symm, w.left_nonzero]
  x := w.x
  y := w.y
  x_mem := Finset.mem_insert_of_mem w.x_mem
  y_mem := w.y_mem
  pair_eq := w.pair_eq
  total_links := by
    have ht := w.total_links
    rw [Finset.card_insert_of_notMem hi]
    omega
  balanced := Or.inl (by
    rw [Finset.card_insert_of_notMem hi]
    exact hbal)

def DiffWitness.leftChild
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (i : {j // j ∈ w.active})
    (hi : z + gamma i.1 ∉ w.right) :
    DiffWitness gamma (alpha - 1) (ell + 1) where
  active := w.active.erase i.1
  pivot := w.pivot
  pivot_not_active := fun h => w.pivot_not_active (Finset.mem_of_mem_erase h)
  active_card := by
    have hc := w.active_card
    have hpos : 0 < w.active.card := Finset.card_pos.mpr ⟨i.1, i.2⟩
    rw [Finset.card_erase_of_mem i.2]
    omega
  left := w.left
  right := insert (z + gamma i.1) w.right
  left_nonzero := w.left_nonzero
  x := w.x
  y := w.y
  x_mem := w.x_mem
  y_mem := Finset.mem_insert_of_mem w.y_mem
  pair_eq := w.pair_eq
  total_links := by
    have ht := w.total_links
    rw [Finset.card_insert_of_notMem hi]
    omega
  balanced := Or.inr (by
    rw [Finset.card_insert_of_notMem hi]
    omega)

def liftActive {q : Nat} (A : Finset (Fin q)) (p : Fin q)
    (i : {j // j ∈ A}) : {j // j ∈ insert p A} :=
  ⟨i.1, Finset.mem_insert_of_mem i.2⟩

theorem sum_insertActive {q : Nat} (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) (f : {j // j ∈ insert p A} -> Real) :
    (∑ j, f j) = f (activePivot A p) + ∑ i, f (liftActive A p i) := by
  rw [← Equiv.sum_comp (finsetInsertEquiv A p hp) f, Fintype.sum_option]
  rfl

theorem abs_sum_sub_insert_le
    {q : Nat} (gamma : Fin q -> G) (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) (v : G)
    (a : {j // j ∈ A} -> Real)
    (b : {j // j ∈ insert p A} -> Real)
    (D R : Real) (hD : 0 <= D) (hR : 0 <= R)
    (hpoint : ∀ i,
      |a i - b (liftActive A p i)| <=
        D + if gamma i.1 = v then R else 0)
    (hpivot0 : 0 <= b (activePivot A p))
    (hpivot : b (activePivot A p) <= R) :
    |(∑ i, a i) - ∑ j, b j| <=
      (q : Real) * D + 3 * (maxMultiplicity gamma : Real) * R := by
  rw [sum_insertActive A p hp b]
  have htriangle :
      |(∑ i, a i) - (b (activePivot A p) +
          ∑ i, b (liftActive A p i))| <=
        (∑ i, |a i - b (liftActive A p i)|) + b (activePivot A p) := by
    calc
      |(∑ i, a i) - (b (activePivot A p) +
          ∑ i, b (liftActive A p i))| =
          |(∑ i, (a i - b (liftActive A p i))) -
            b (activePivot A p)| := by
        rw [Finset.sum_sub_distrib]
        ring
      _ <= |∑ i, (a i - b (liftActive A p i))| +
          |-b (activePivot A p)| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (∑ i, (a i - b (liftActive A p i)))
            (-b (activePivot A p))
      _ = |∑ i, (a i - b (liftActive A p i))| +
          b (activePivot A p) := by
        rw [abs_neg, abs_of_nonneg hpivot0]
      _ <= (∑ i, |a i - b (liftActive A p i)|) +
          b (activePivot A p) := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
  have hindicator := sum_indicator_le_maxMultiplicity_mul gamma A v R hR
  have hcard : A.card <= q := by
    simpa using Finset.card_le_univ A
  have hcardR : (A.card : Real) * D <= (q : Real) * D := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD
  have hmult : 1 <= maxMultiplicity gamma := one_le_maxMultiplicity gamma p
  have hmultR : R <= (maxMultiplicity gamma : Real) * R := by
    have hcast : (1 : Real) <= maxMultiplicity gamma := by exact_mod_cast hmult
    simpa using mul_le_mul_of_nonneg_right hcast hR
  have hmultR0 : 0 <= (maxMultiplicity gamma : Real) * R := by positivity
  calc
    |(∑ i, a i) - (b (activePivot A p) +
        ∑ i, b (liftActive A p i))| <=
        (∑ i, |a i - b (liftActive A p i)|) +
          b (activePivot A p) := htriangle
    _ <= (∑ i : {j // j ∈ A},
        (D + if gamma i.1 = v then R else 0)) + R := by
      gcongr with i
      exact hpoint i
    _ = (A.card : Real) * D +
        (∑ i : {j // j ∈ A}, if gamma i.1 = v then R else 0) + R := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]
    _ <= (A.card : Real) * D +
        (maxMultiplicity gamma : Real) * R + R := by gcongr
    _ <= (q : Real) * D +
        ((maxMultiplicity gamma : Real) * R +
          (maxMultiplicity gamma : Real) * R) := by
      nlinarith
    _ <= (q : Real) * D + 3 * (maxMultiplicity gamma : Real) * R := by
      nlinarith

def eraseInsertedActiveEquiv {q : Nat} (A : Finset (Fin q)) (p : Fin q)
    (hp : p ∉ A) (i : {j // j ∈ A}) :
    Without (liftActive A p i) ≃ {j // j ∈ insert p (A.erase i.1)} where
  toFun j := ⟨j.1.1, by
    rcases Finset.mem_insert.mp j.1.2 with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_erase.mpr ⟨fun heq => j.2 (Subtype.ext heq), h⟩))⟩
  invFun j := ⟨⟨j.1, by
    rcases Finset.mem_insert.mp j.2 with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_of_mem_erase h))⟩, by
      intro heq
      have hv := congrArg Subtype.val heq
      rcases Finset.mem_insert.mp j.2 with hjp | hjerase
      · have hpj : p = j.1 := hjp.symm
        have hji : j.1 = i.1 := hv
        have hpi : p = i.1 := hpj.trans hji
        exact hp (hpi ▸ i.2)
      · exact (Finset.mem_erase.mp hjerase).1 (by simpa [liftActive] using hv)⟩
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    rfl

theorem DiffWitness.rightChild_label_prob_eq_push
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (i : {j // j ∈ w.active}) (hi : z + gamma i.1 ∉ w.left)
    (hi0 : z + gamma i.1 ≠ 0) :
    (w.rightChild z hbal i hi hi0).label.prob =
      (w.label.pushRight i z).prob := by
  let e := eraseActiveEquiv w.active i
  have heq : (w.label.pushRight i z).reindex e.symm =
      (w.rightChild z hbal i hi hi0).label := by
    unfold DiffWitness.label DiffWitness.rightChild Label.pushRight Label.reindex
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    funext j
    rfl
  calc
    (w.rightChild z hbal i hi hi0).label.prob =
        ((w.label.pushRight i z).reindex e.symm).prob :=
      congrArg Label.prob heq.symm
    _ = (w.label.pushRight i z).prob := Label.prob_reindex _ _

theorem DiffWitness.leftChild_label_prob_eq_push
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (i : {j // j ∈ w.active}) (hi : z + gamma i.1 ∉ w.right) :
    (w.leftChild z hbal i hi).label.prob =
      (w.label.pushLeft i z).prob := by
  let e := eraseActiveEquiv w.active i
  have heq : (w.label.pushLeft i z).reindex e.symm =
      (w.leftChild z hbal i hi).label := by
    unfold DiffWitness.label DiffWitness.leftChild Label.pushLeft Label.reindex
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    funext j
    rfl
  calc
    (w.leftChild z hbal i hi).label.prob =
        ((w.label.pushLeft i z).reindex e.symm).prob :=
      congrArg Label.prob heq.symm
    _ = (w.label.pushLeft i z).prob := Label.prob_reindex _ _

theorem DiffWitness.rightChild_separated_prob_eq_push
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (i : {j // j ∈ w.active}) (hi : z + gamma i.1 ∉ w.left)
    (hi0 : z + gamma i.1 ≠ 0) :
    (w.rightChild z hbal i hi hi0).separated.prob =
      (w.separated.pushRight (liftActive w.active w.pivot i) z).prob := by
  let e := eraseInsertedActiveEquiv w.active w.pivot w.pivot_not_active i
  have hix : z + gamma i.1 ≠ w.x := by
    intro h
    exact hi (h ▸ w.x_mem)
  have heq :
      (w.separated.pushRight (liftActive w.active w.pivot i) z).reindex e.symm =
        (w.rightChild z hbal i hi hi0).separated := by
    unfold DiffWitness.separated DiffWitness.rightChild Label.pushRight
      Label.reindex liftActive
    rw [Label.mk.injEq]
    refine ⟨?_, ?_, rfl⟩
    · funext j
      rfl
    · ext a
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro (rfl | ha)
        · exact ⟨hix, Or.inl rfl⟩
        · exact ⟨ha.1, Or.inr ha.2⟩
      · rintro ⟨hax, rfl | ha⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hax, ha⟩
  calc
    (w.rightChild z hbal i hi hi0).separated.prob =
        ((w.separated.pushRight (liftActive w.active w.pivot i) z).reindex
          e.symm).prob := congrArg Label.prob heq.symm
    _ = (w.separated.pushRight (liftActive w.active w.pivot i) z).prob :=
      Label.prob_reindex _ _

theorem DiffWitness.leftChild_separated_prob_eq_push
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (i : {j // j ∈ w.active}) (hi : z + gamma i.1 ∉ w.right) :
    (w.leftChild z hbal i hi).separated.prob =
      (w.separated.pushLeft (liftActive w.active w.pivot i) z).prob := by
  let e := eraseInsertedActiveEquiv w.active w.pivot w.pivot_not_active i
  have hiy : z + gamma i.1 ≠ w.y := by
    intro h
    exact hi (h ▸ w.y_mem)
  have heq :
      (w.separated.pushLeft (liftActive w.active w.pivot i) z).reindex e.symm =
        (w.leftChild z hbal i hi).separated := by
    unfold DiffWitness.separated DiffWitness.leftChild Label.pushLeft
      Label.reindex liftActive
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, ?_⟩
    · funext j
      rfl
    · ext a
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro (rfl | ha)
        · exact ⟨hiy, Or.inl rfl⟩
        · exact ⟨ha.1, Or.inr ha.2⟩
      · rintro ⟨hay, rfl | ha⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hay, ha⟩
  calc
    (w.leftChild z hbal i hi).separated.prob =
        ((w.separated.pushLeft (liftActive w.active w.pivot i) z).reindex
          e.symm).prob := congrArg Label.prob heq.symm
    _ = (w.separated.pushLeft (liftActive w.active w.pivot i) z).prob :=
      Label.prob_reindex _ _

/-! Every pushed term on the separated side still contains a left/right pair
whose sum is the master coordinate that was removed.  Collapsing that pair is
the exact DNS reduction from an unmatched deletion term to a one-linked
subtuple. -/

theorem DiffWitness.separated_pushRight_prob_le_activeOneLabel
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hz : z ∈ w.right) (hzy : z ≠ w.y)
    (j : {k // k ∈ insert w.pivot w.active}) :
    (w.separated.pushRight j z).prob <=
      (activeOneLabel gamma
        ((insert w.pivot w.active).erase j.1) j.1).prob := by
  have hzsep : z ∈ w.separated.right := by
    exact Finset.mem_erase.mpr ⟨hzy, hz⟩
  have hnew : z + w.separated.base j ∈
      (w.separated.pushRight j z).left := Finset.mem_insert_self _ _
  have hcollapse := (w.separated.pushRight j z).prob_le_collapseLinks
    hxor (z + w.separated.base j) z hnew hzsep
  have hsum : (z + gamma j.1) + z = gamma j.1 := by
    calc
      (z + gamma j.1) + z = gamma j.1 + (z + z) := by abel
      _ = gamma j.1 := by rw [hxor]; simp
  let e := eraseActiveEquiv (insert w.pivot w.active) j
  have heq :
      (oneLabel (w.separated.pushRight j z).base
        ((z + w.separated.base j) + z)).reindex e.symm =
        activeOneLabel gamma ((insert w.pivot w.active).erase j.1) j.1 := by
    unfold DiffWitness.separated Label.pushRight activeOneLabel oneLabel
      Label.reindex
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, ?_⟩
    · funext k
      rfl
    · simp only [Finset.singleton_inj]
      exact hsum
  calc
    (w.separated.pushRight j z).prob <=
        (oneLabel (w.separated.pushRight j z).base
          ((z + w.separated.base j) + z)).prob := hcollapse
    _ = ((oneLabel (w.separated.pushRight j z).base
          ((z + w.separated.base j) + z)).reindex e.symm).prob :=
      (Label.prob_reindex _ _).symm
    _ = (activeOneLabel gamma
          ((insert w.pivot w.active).erase j.1) j.1).prob :=
      congrArg Label.prob heq

theorem DiffWitness.separated_pushLeft_prob_le_activeOneLabel
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} {gamma : Fin q -> G} {alpha ell : Nat}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hz : z ∈ w.left) (hzx : z ≠ w.x)
    (j : {k // k ∈ insert w.pivot w.active}) :
    (w.separated.pushLeft j z).prob <=
      (activeOneLabel gamma
        ((insert w.pivot w.active).erase j.1) j.1).prob := by
  have hzsep : z ∈ w.separated.left := by
    exact Finset.mem_erase.mpr ⟨hzx, hz⟩
  have hnew : z + w.separated.base j ∈
      (w.separated.pushLeft j z).right := Finset.mem_insert_self _ _
  have hcollapse := (w.separated.pushLeft j z).prob_le_collapseLinks
    hxor z (z + w.separated.base j) hzsep hnew
  have hsum : z + (z + gamma j.1) = gamma j.1 := by
    calc
      z + (z + gamma j.1) = (z + z) + gamma j.1 := by abel
      _ = gamma j.1 := by rw [hxor]; simp
  let e := eraseActiveEquiv (insert w.pivot w.active) j
  have heq :
      (oneLabel (w.separated.pushLeft j z).base
        (z + (z + w.separated.base j))).reindex e.symm =
        activeOneLabel gamma ((insert w.pivot w.active).erase j.1) j.1 := by
    unfold DiffWitness.separated Label.pushLeft activeOneLabel oneLabel
      Label.reindex
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, ?_⟩
    · funext k
      rfl
    · simp only [Finset.singleton_inj]
      exact hsum
  calc
    (w.separated.pushLeft j z).prob <=
        (oneLabel (w.separated.pushLeft j z).base
          (z + (z + w.separated.base j))).prob := hcollapse
    _ = ((oneLabel (w.separated.pushLeft j z).base
          (z + (z + w.separated.base j))).reindex e.symm).prob :=
      (Label.prob_reindex _ _).symm
    _ = (activeOneLabel gamma
          ((insert w.pivot w.active).erase j.1) j.1).prob :=
      congrArg Label.prob heq

theorem DiffWitness.separated_pushRight_prob_le_reference
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hz : z ∈ w.right) (hzy : z ≠ w.y)
    (j : {k // k ∈ insert w.pivot w.active})
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (w.separated.pushRight j z).prob <=
      masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
  have hjnot : j.1 ∉ (insert w.pivot w.active).erase j.1 := by simp
  have hcard :
      q - (((insert w.pivot w.active).erase j.1).card + 1) = d := by
    rw [Finset.card_erase_of_mem j.2,
      Finset.card_insert_of_notMem w.pivot_not_active]
    rw [w.active_card]
    have hc := w.active_card
    have halpha : 0 < alpha := by omega
    omega
  calc
    (w.separated.pushRight j z).prob <=
        (activeOneLabel gamma
          ((insert w.pivot w.active).erase j.1) j.1).prob :=
      w.separated_pushRight_prob_le_activeOneLabel hxor z hz hzy j
    _ <= (compatibleLabel gamma j.1).prob /
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
      activeOneLabel_prob_le_div_masterFactor_pow gamma _ j.1 hjnot hcard hfactor
    _ = masterProb gamma /
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
      rw [compatibleLabel_prob_eq_masterProb]

theorem DiffWitness.separated_pushLeft_prob_le_reference
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hz : z ∈ w.left) (hzx : z ≠ w.x)
    (j : {k // k ∈ insert w.pivot w.active})
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (w.separated.pushLeft j z).prob <=
      masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
  have hjnot : j.1 ∉ (insert w.pivot w.active).erase j.1 := by simp
  have hcard :
      q - (((insert w.pivot w.active).erase j.1).card + 1) = d := by
    rw [Finset.card_erase_of_mem j.2,
      Finset.card_insert_of_notMem w.pivot_not_active]
    rw [w.active_card]
    have hc := w.active_card
    have halpha : 0 < alpha := by omega
    omega
  calc
    (w.separated.pushLeft j z).prob <=
        (activeOneLabel gamma
          ((insert w.pivot w.active).erase j.1) j.1).prob :=
      w.separated_pushLeft_prob_le_activeOneLabel hxor z hz hzx j
    _ <= (compatibleLabel gamma j.1).prob /
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
      activeOneLabel_prob_le_div_masterFactor_pow gamma _ j.1 hjnot hcard hfactor
    _ = masterProb gamma /
          (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
      rw [compatibleLabel_prob_eq_masterProb]

theorem DiffWitness.separated_rightDeletionTerm_le_reference
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hz : z ∈ w.right) (hzy : z ≠ w.y)
    (j : {k // k ∈ insert w.pivot w.active})
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    w.separated.rightDeletionTerm z j <=
      masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
  have hR : 0 <= masterProb gamma /
      (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
    div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  unfold Label.rightDeletionTerm
  split
  · exact w.separated_pushRight_prob_le_reference
      hxor z hz hzy j hd hfactor
  · exact hR

theorem DiffWitness.separated_leftDeletionTerm_le_reference
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hz : z ∈ w.left) (hzx : z ≠ w.x)
    (j : {k // k ∈ insert w.pivot w.active})
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    w.separated.leftDeletionTerm z j <=
      masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d := by
  have hR : 0 <= masterProb gamma /
      (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
    div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  unfold Label.leftDeletionTerm
  split
  · exact w.separated_pushLeft_prob_le_reference
      hxor z hz hzx j hd hfactor
  · exact hR

theorem DiffWitness.abs_rightDeletionTerm_diff_le
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y)
    (i : {j // j ∈ w.active})
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |w.label.rightDeletionTerm z i -
        w.separated.rightDeletionTerm z
          (liftActive w.active w.pivot i)| <=
      (differential gamma (alpha - 1) (ell + 1) : Real) +
        if gamma i.1 = z + w.x then
          masterProb gamma /
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
        else 0 := by
  let s : G := z + gamma i.1
  let R : Real := masterProb gamma /
    (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  have hdiff : 0 <= (differential gamma (alpha - 1) (ell + 1) : Real) :=
    NNReal.coe_nonneg _
  have hsepBase :
      z + w.separated.base (liftActive w.active w.pivot i) = s := by
    rfl
  by_cases hp : s ∉ w.left
  · have hs : s ∉ w.left.erase w.x := fun h => hp (Finset.mem_of_mem_erase h)
    by_cases hs0 : s = 0
    · have hzeroLabel : 0 ∈ (w.label.pushRight i z).left := by
        change 0 ∈ insert s w.left
        simp [hs0]
      have hzeroSep : 0 ∈
          (w.separated.pushRight (liftActive w.active w.pivot i) z).left := by
        change 0 ∈ insert s (w.left.erase w.x)
        simp [hs0]
      have hprobLabel :=
        (w.label.pushRight i z).prob_eq_zero_of_zero_mem_left hzeroLabel
      have hprobSep := Label.prob_eq_zero_of_zero_mem_left
        (w.separated.pushRight (liftActive w.active w.pivot i) z) hzeroSep
      simp only [Label.rightDeletionTerm]
      rw [dif_pos (by simpa [DiffWitness.label, s] using hp),
        dif_pos (by simpa [DiffWitness.separated, hsepBase, s] using hs),
        hprobLabel, hprobSep, sub_zero, abs_zero]
      positivity
    · have hchild := abs_diff_le_differential
          (w.rightChild z hbal i hp hs0)
      rw [w.rightChild_label_prob_eq_push z hbal i hp hs0,
        w.rightChild_separated_prob_eq_push z hbal i hp hs0] at hchild
      simp only [Label.rightDeletionTerm]
      rw [dif_pos (by simpa [DiffWitness.label, s] using hp),
        dif_pos (by simpa [DiffWitness.separated, hsepBase, s] using hs)]
      exact le_add_of_le_of_nonneg hchild (by positivity)
  · have hpMem : s ∈ w.left := by simpa using hp
    by_cases hs : s ∉ w.left.erase w.x
    · have hsx : s = w.x := by
        by_contra hne
        exact hs (Finset.mem_erase.mpr ⟨hne, hpMem⟩)
      have htarget : gamma i.1 = z + w.x := by
        calc
          gamma i.1 = (z + z) + gamma i.1 := by rw [hxor]; simp
          _ = z + (z + gamma i.1) := by abel
          _ = z + w.x := by rw [show z + gamma i.1 = w.x by exact hsx]
      have hbound := w.separated_pushRight_prob_le_reference
        hxor z hz hzy (liftActive w.active w.pivot i) hd hfactor
      simp only [Label.rightDeletionTerm]
      rw [dif_neg (by simpa [DiffWitness.label, s] using hp),
        dif_pos (by simpa [DiffWitness.separated, hsepBase, s] using hs),
        htarget, if_pos rfl]
      have hnonneg :=
        (w.separated.pushRight (liftActive w.active w.pivot i) z).prob_nonneg
      dsimp [R] at hR ⊢
      rw [zero_sub, abs_neg, abs_of_nonneg hnonneg]
      linarith
    · have hsMem : s ∈ w.left.erase w.x := by simpa using hs
      simp only [Label.rightDeletionTerm]
      rw [dif_neg (by simpa [DiffWitness.label, s] using hp),
        dif_neg (by simpa [DiffWitness.separated, hsepBase, s] using hs),
        sub_zero, abs_zero]
      positivity

theorem DiffWitness.abs_leftDeletionTerm_diff_le
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x)
    (i : {j // j ∈ w.active})
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |w.label.leftDeletionTerm z i -
        w.separated.leftDeletionTerm z
          (liftActive w.active w.pivot i)| <=
      (differential gamma (alpha - 1) (ell + 1) : Real) +
        if gamma i.1 = z + w.y then
          masterProb gamma /
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
        else 0 := by
  let s : G := z + gamma i.1
  let R : Real := masterProb gamma /
    (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  have hdiff : 0 <= (differential gamma (alpha - 1) (ell + 1) : Real) :=
    NNReal.coe_nonneg _
  have hsepBase :
      z + w.separated.base (liftActive w.active w.pivot i) = s := by
    rfl
  by_cases hp : s ∉ w.right
  · have hs : s ∉ w.right.erase w.y := fun h => hp (Finset.mem_of_mem_erase h)
    have hchild := abs_diff_le_differential (w.leftChild z hbal i hp)
    rw [w.leftChild_label_prob_eq_push z hbal i hp,
      w.leftChild_separated_prob_eq_push z hbal i hp] at hchild
    simp only [Label.leftDeletionTerm]
    rw [dif_pos (by simpa [DiffWitness.label, s] using hp),
      dif_pos (by simpa [DiffWitness.separated, hsepBase, s] using hs)]
    exact le_add_of_le_of_nonneg hchild (by positivity)
  · have hpMem : s ∈ w.right := by simpa using hp
    by_cases hs : s ∉ w.right.erase w.y
    · have hsy : s = w.y := by
        by_contra hne
        exact hs (Finset.mem_erase.mpr ⟨hne, hpMem⟩)
      have htarget : gamma i.1 = z + w.y := by
        calc
          gamma i.1 = (z + z) + gamma i.1 := by rw [hxor]; simp
          _ = z + (z + gamma i.1) := by abel
          _ = z + w.y := by rw [show z + gamma i.1 = w.y by exact hsy]
      have hbound := w.separated_pushLeft_prob_le_reference
        hxor z hz hzx (liftActive w.active w.pivot i) hd hfactor
      simp only [Label.leftDeletionTerm]
      rw [dif_neg (by simpa [DiffWitness.label, s] using hp),
        dif_pos (by simpa [DiffWitness.separated, hsepBase, s] using hs),
        htarget, if_pos rfl]
      have hnonneg :=
        (w.separated.pushLeft (liftActive w.active w.pivot i) z).prob_nonneg
      dsimp [R] at hR ⊢
      rw [zero_sub, abs_neg, abs_of_nonneg hnonneg]
      linarith
    · have hsMem : s ∈ w.right.erase w.y := by simpa using hs
      simp only [Label.leftDeletionTerm]
      rw [dif_neg (by simpa [DiffWitness.label, s] using hp),
        dif_neg (by simpa [DiffWitness.separated, hsepBase, s] using hs),
        sub_zero, abs_zero]
      positivity

theorem DiffWitness.abs_sum_rightDeletionTerm_diff_le
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |(∑ i : {j // j ∈ w.active}, w.label.rightDeletionTerm z i) -
        ∑ j : {j // j ∈ insert w.pivot w.active},
          w.separated.rightDeletionTerm z j| <=
      (q : Real) * (differential gamma (alpha - 1) (ell + 1) : Real) +
        3 * (maxMultiplicity gamma : Real) *
          (masterProb gamma /
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d) := by
  let D : Real := (differential gamma (alpha - 1) (ell + 1) : Real)
  let R : Real := masterProb gamma /
    (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
  have hD : 0 <= D := by dsimp [D]; positivity
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  have hpivot0 : 0 <=
      w.separated.rightDeletionTerm z (activePivot w.active w.pivot) := by
    unfold Label.rightDeletionTerm
    split
    · exact Label.prob_nonneg _
    · norm_num
  have hpivot :
      w.separated.rightDeletionTerm z (activePivot w.active w.pivot) <= R := by
    dsimp [R]
    exact w.separated_rightDeletionTerm_le_reference hxor z hz hzy
      (activePivot w.active w.pivot) hd hfactor
  simpa [D, R] using abs_sum_sub_insert_le gamma w.active w.pivot
    w.pivot_not_active (z + w.x)
    (fun i => w.label.rightDeletionTerm z i)
    (fun j => w.separated.rightDeletionTerm z j)
    D R hD hR
    (fun i => w.abs_rightDeletionTerm_diff_le hxor z hbal hz hzy i hd hfactor)
    hpivot0 hpivot

theorem DiffWitness.abs_sum_leftDeletionTerm_diff_le
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |(∑ i : {j // j ∈ w.active}, w.label.leftDeletionTerm z i) -
        ∑ j : {j // j ∈ insert w.pivot w.active},
          w.separated.leftDeletionTerm z j| <=
      (q : Real) * (differential gamma (alpha - 1) (ell + 1) : Real) +
        3 * (maxMultiplicity gamma : Real) *
          (masterProb gamma /
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d) := by
  let D : Real := (differential gamma (alpha - 1) (ell + 1) : Real)
  let R : Real := masterProb gamma /
    (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
  have hD : 0 <= D := by dsimp [D]; positivity
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  have hpivot0 : 0 <=
      w.separated.leftDeletionTerm z (activePivot w.active w.pivot) := by
    unfold Label.leftDeletionTerm
    split
    · exact Label.prob_nonneg _
    · norm_num
  have hpivot :
      w.separated.leftDeletionTerm z (activePivot w.active w.pivot) <= R := by
    dsimp [R]
    exact w.separated_leftDeletionTerm_le_reference hxor z hz hzx
      (activePivot w.active w.pivot) hd hfactor
  simpa [D, R] using abs_sum_sub_insert_le gamma w.active w.pivot
    w.pivot_not_active (z + w.y)
    (fun i => w.label.leftDeletionTerm z i)
    (fun j => w.separated.leftDeletionTerm z j)
    D R hD hR
    (fun i => w.abs_leftDeletionTerm_diff_le hxor z hbal hz hzx i hd hfactor)
    hpivot0 hpivot

theorem DiffWitness.abs_diff_le_of_eraseRight
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card + 1)
    (hz : z ∈ w.right) (hzy : z ≠ w.y) (hell : 0 < ell)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |w.label.prob - w.separated.prob| <=
      (differential gamma alpha (ell - 1) : Real) +
        (1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (alpha - 1) (ell + 1) : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma /
                (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
  have hzsep : z ∈ w.separated.right := by
    exact Finset.mem_erase.mpr ⟨hzy, hz⟩
  have hlabel := w.label.prob_eq_prob_eraseRight_sub_terms hxor z hz
  have hsep := w.separated.prob_eq_prob_eraseRight_sub_terms hxor z hzsep
  have herase := w.abs_eraseRight_diff_le z hbal hz hzy hell
  have hsum := w.abs_sum_rightDeletionTerm_diff_le
    hxor z hbal hz hzy hd hfactor
  have hc : 0 <= (1 / (Fintype.card G : Real)) := by positivity
  calc
    |w.label.prob - w.separated.prob| =
        |((w.label.eraseRight z).prob - (w.separated.eraseRight z).prob) -
          (1 / (Fintype.card G : Real)) *
            ((∑ i : {j // j ∈ w.active}, w.label.rightDeletionTerm z i) -
              ∑ j : {j // j ∈ insert w.pivot w.active},
                w.separated.rightDeletionTerm z j)| := by
      rw [hlabel, hsep]
      ring
    _ <= |(w.label.eraseRight z).prob - (w.separated.eraseRight z).prob| +
        |-(1 / (Fintype.card G : Real)) *
          ((∑ i : {j // j ∈ w.active}, w.label.rightDeletionTerm z i) -
            ∑ j : {j // j ∈ insert w.pivot w.active},
              w.separated.rightDeletionTerm z j)| := by
      simpa [sub_eq_add_neg] using abs_add_le
        ((w.label.eraseRight z).prob - (w.separated.eraseRight z).prob)
        (-(1 / (Fintype.card G : Real)) *
          ((∑ i : {j // j ∈ w.active}, w.label.rightDeletionTerm z i) -
            ∑ j : {j // j ∈ insert w.pivot w.active},
              w.separated.rightDeletionTerm z j))
    _ = |(w.label.eraseRight z).prob - (w.separated.eraseRight z).prob| +
        (1 / (Fintype.card G : Real)) *
          |(∑ i : {j // j ∈ w.active}, w.label.rightDeletionTerm z i) -
            ∑ j : {j // j ∈ insert w.pivot w.active},
              w.separated.rightDeletionTerm z j| := by
      rw [abs_mul, abs_neg, abs_of_nonneg hc]
    _ <= (differential gamma alpha (ell - 1) : Real) +
        (1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (alpha - 1) (ell + 1) : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma /
                (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
      exact add_le_add herase (mul_le_mul_of_nonneg_left hsum hc)

theorem DiffWitness.abs_diff_le_of_eraseLeft
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (z : G)
    (hbal : w.right.card = w.left.card)
    (hz : z ∈ w.left) (hzx : z ≠ w.x) (hell : 0 < ell)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |w.label.prob - w.separated.prob| <=
      (differential gamma alpha (ell - 1) : Real) +
        (1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (alpha - 1) (ell + 1) : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma /
                (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    exact w.left_nonzero (hz0 ▸ hz)
  have hzsep : z ∈ w.separated.left := by
    exact Finset.mem_erase.mpr ⟨hzx, hz⟩
  have hlabel := w.label.prob_eq_prob_eraseLeft_sub_terms z hz hz0
  have hsep := w.separated.prob_eq_prob_eraseLeft_sub_terms z hzsep hz0
  have herase := w.abs_eraseLeft_diff_le z hbal hz hzx hell
  have hsum := w.abs_sum_leftDeletionTerm_diff_le
    hxor z hbal hz hzx hd hfactor
  have hc : 0 <= (1 / (Fintype.card G : Real)) := by positivity
  calc
    |w.label.prob - w.separated.prob| =
        |((w.label.eraseLeft z).prob - (w.separated.eraseLeft z).prob) -
          (1 / (Fintype.card G : Real)) *
            ((∑ i : {j // j ∈ w.active}, w.label.leftDeletionTerm z i) -
              ∑ j : {j // j ∈ insert w.pivot w.active},
                w.separated.leftDeletionTerm z j)| := by
      rw [hlabel, hsep]
      ring
    _ <= |(w.label.eraseLeft z).prob - (w.separated.eraseLeft z).prob| +
        |-(1 / (Fintype.card G : Real)) *
          ((∑ i : {j // j ∈ w.active}, w.label.leftDeletionTerm z i) -
            ∑ j : {j // j ∈ insert w.pivot w.active},
              w.separated.leftDeletionTerm z j)| := by
      simpa [sub_eq_add_neg] using abs_add_le
        ((w.label.eraseLeft z).prob - (w.separated.eraseLeft z).prob)
        (-(1 / (Fintype.card G : Real)) *
          ((∑ i : {j // j ∈ w.active}, w.label.leftDeletionTerm z i) -
            ∑ j : {j // j ∈ insert w.pivot w.active},
              w.separated.leftDeletionTerm z j))
    _ = |(w.label.eraseLeft z).prob - (w.separated.eraseLeft z).prob| +
        (1 / (Fintype.card G : Real)) *
          |(∑ i : {j // j ∈ w.active}, w.label.leftDeletionTerm z i) -
            ∑ j : {j // j ∈ insert w.pivot w.active},
              w.separated.leftDeletionTerm z j| := by
      rw [abs_mul, abs_neg, abs_of_nonneg hc]
    _ <= (differential gamma alpha (ell - 1) : Real) +
        (1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (alpha - 1) (ell + 1) : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma /
                (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
      exact add_le_add herase (mul_le_mul_of_nonneg_left hsum hc)

theorem DiffWitness.abs_diff_le_recurrence_of_pos
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) (hell : 0 < ell)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |w.label.prob - w.separated.prob| <=
      (differential gamma alpha (ell - 1) : Real) +
        (1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (alpha - 1) (ell + 1) : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma /
                (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
  rcases w.balanced with hbal | hbal
  · have hcard : 1 < w.left.card := by
      have ht := w.total_links
      omega
    obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne hcard w.x
    exact w.abs_diff_le_of_eraseLeft hxor z hbal hz hzx hell hd hfactor
  · have hcard : 1 < w.right.card := by
      have ht := w.total_links
      omega
    obtain ⟨z, hz, hzy⟩ := Finset.exists_mem_ne hcard w.y
    exact w.abs_diff_le_of_eraseRight hxor z hbal hz hzy hell hd hfactor

theorem differential_recurrence_of_pos
    (hxor : ∀ g : G, g + g = 0)
    {q alpha ell d : Nat} (gamma : Fin q -> G) (hell : 0 < ell)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (differential gamma alpha ell : Real) <=
      (differential gamma alpha (ell - 1) : Real) +
        (1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (alpha - 1) (ell + 1) : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma /
                (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
  let R : Real :=
    (differential gamma alpha (ell - 1) : Real) +
      (1 / (Fintype.card G : Real)) *
        ((q : Real) *
            (differential gamma (alpha - 1) (ell + 1) : Real) +
          3 * (maxMultiplicity gamma : Real) *
            (masterProb gamma /
              (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d))
  have hR : 0 <= R := by
    dsimp [R]
    have href : 0 <= masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
      div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
    apply add_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · exact add_nonneg (by positivity) (mul_nonneg (by positivity) href)
  have hsup : differential gamma alpha ell <= Real.toNNReal R := by
    unfold differential
    apply Finset.sup_le
    intro w _hw
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal R hR]
    exact w.abs_diff_le_recurrence_of_pos hxor hell hd hfactor
  have hcoe := NNReal.coe_le_coe.mpr hsup
  rw [Real.coe_toNNReal R hR] at hcoe
  exact hcoe

/-! ### The zero-link recursion boundary

When `ell = 0`, a differential witness has exactly one link on each side.
DNS recenters the distinguished sample across the left link, turning
`({x},{y})` into `({x},{x+y})`.  Deleting `x` then exposes the same one-linked
label that appears in the exact one-link/zero-link identity. -/

def pairLabel (base : I -> G) (x y : G) : Label I G where
  base := base
  left := {x}
  right := {y}

theorem pairLabel_good_recenter_iff
    (hxor : ∀ g : G, g + g = 0)
    (base : I -> G) (x y r0 : G) (r : I -> G) :
    (pairLabel base x (x + y)).Good (r0 + x, r) ↔
      (pairLabel base x y).Good (r0, r) := by
  have hswap : (r0 + x) + x = r0 := by
    calc
      (r0 + x) + x = r0 + (x + x) := by abel
      _ = r0 := by rw [hxor]; simp
  have hright : (r0 + x) + (x + y) = r0 + y := by
    calc
      (r0 + x) + (x + y) = r0 + (x + x) + y := by abel
      _ = r0 + y := by rw [hxor]; simp
  unfold Label.Good Label.LeftGood Label.RightGood pairLabel
  constructor
  · rintro ⟨⟨hinj, hcenter, hzero, hleft⟩, hrightInj, hlinks⟩
    refine ⟨⟨hinj, ?_, hzero, ?_⟩, hrightInj, ?_⟩
    · intro i hi
      exact hleft i x (by simp) (by simpa [hswap] using hi)
    · intro i s hs
      have hsx : s = x := by simpa using hs
      subst s
      exact hcenter i
    · intro i t ht
      have hty : t = y := by simpa using ht
      subst t
      intro heq
      exact hlinks i (x + y) (by simp) (by simpa [hright] using heq)
  · rintro ⟨⟨hinj, hcenter, hzero, hleft⟩, hrightInj, hlinks⟩
    refine ⟨⟨hinj, ?_, hzero, ?_⟩, hrightInj, ?_⟩
    · intro i hi
      exact hleft i x (by simp) (by simpa using hi)
    · intro i s hs
      have hsx : s = x := by simpa using hs
      subst s
      intro heq
      exact hcenter i (by simpa [hswap] using heq)
    · intro i t ht
      have htxy : t = x + y := by simpa using ht
      subst t
      intro heq
      exact hlinks i y (by simp) (by simpa [hright] using heq)

def pairLabelRecenterEquiv
    (hxor : ∀ g : G, g + g = 0)
    (base : I -> G) (x y : G) :
    (pairLabel base x y).Realization ≃
      (pairLabel base x (x + y)).Realization where
  toFun z := ⟨(z.1.1 + x, z.1.2),
    (pairLabel_good_recenter_iff hxor base x y z.1.1 z.1.2).2 z.2⟩
  invFun z := ⟨(z.1.1 + x, z.1.2), by
    have hswap : (z.1.1 + x) + x = z.1.1 := by
      calc
        (z.1.1 + x) + x = z.1.1 + (x + x) := by abel
        _ = z.1.1 := by rw [hxor]; simp
    apply (pairLabel_good_recenter_iff hxor base x y
      (z.1.1 + x) z.1.2).1
    simpa [hswap] using z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      calc
        (z.1.1 + x) + x = z.1.1 + (x + x) := by abel
        _ = z.1.1 := by rw [hxor]; simp
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      calc
        (z.1.1 + x) + x = z.1.1 + (x + x) := by abel
        _ = z.1.1 := by rw [hxor]; simp
    · rfl

theorem pairLabel_prob_recenter
    (hxor : ∀ g : G, g + g = 0)
    (base : I -> G) (x y : G) :
    (pairLabel base x y).prob = (pairLabel base x (x + y)).prob := by
  unfold Label.prob Label.count
  rw [Fintype.card_congr (pairLabelRecenterEquiv hxor base x y)]

theorem DiffWitness.cards_eq_one_of_ell_zero
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) :
    w.left.card = 1 ∧ w.right.card = 1 := by
  have ht := w.total_links
  rcases w.balanced with hbal | hbal
  · omega
  · omega

theorem DiffWitness.left_eq_singleton_of_ell_zero
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) : w.left = {w.x} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp w.cards_eq_one_of_ell_zero.1
  have hmem := w.x_mem
  rw [ha] at hmem
  have hxa : w.x = a := by simpa using hmem
  simpa [hxa] using ha

theorem DiffWitness.right_eq_singleton_of_ell_zero
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) : w.right = {w.y} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp w.cards_eq_one_of_ell_zero.2
  have hmem := w.y_mem
  rw [ha] at hmem
  have hya : w.y = a := by simpa using hmem
  simpa [hya] using ha

def DiffWitness.zeroStar
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) : Label {i // i ∈ w.active} G :=
  pairLabel (fun i => gamma i.1) w.x (w.x + w.y)

theorem DiffWitness.label_prob_eq_zeroStar
    (hxor : ∀ g : G, g + g = 0)
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) :
    w.label.prob = w.zeroStar.prob := by
  have hlabel : w.label = pairLabel (fun i => gamma i.1) w.x w.y := by
    unfold DiffWitness.label pairLabel
    rw [Label.mk.injEq]
    exact ⟨rfl, w.left_eq_singleton_of_ell_zero,
      w.right_eq_singleton_of_ell_zero⟩
  rw [hlabel]
  change (pairLabel (fun i : {i // i ∈ w.active} => gamma i.1) w.x w.y).prob =
    (pairLabel (fun i : {i // i ∈ w.active} => gamma i.1)
      w.x (w.x + w.y)).prob
  exact pairLabel_prob_recenter (I := {i // i ∈ w.active}) (G := G)
    hxor (fun i => gamma i.1) w.x w.y

theorem DiffWitness.separated_eq_activeZeroLabel
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) :
    w.separated = activeZeroLabel gamma w.active w.pivot := by
  unfold DiffWitness.separated activeZeroLabel zeroLabel
  rw [Label.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · rw [w.left_eq_singleton_of_ell_zero]
    simp
  · rw [w.right_eq_singleton_of_ell_zero]
    simp

theorem DiffWitness.zeroStar_eraseLeft_eq_activeOneLabel
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) :
    w.zeroStar.eraseLeft w.x =
      activeOneLabel gamma w.active w.pivot := by
  unfold DiffWitness.zeroStar pairLabel Label.eraseLeft activeOneLabel oneLabel
  rw [Label.mk.injEq]
  refine ⟨rfl, by simp, ?_⟩
  simp [w.pair_eq]

theorem DiffWitness.x_ne_zero
    {q alpha ell : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha ell) : w.x ≠ 0 := by
  intro hx
  exact w.left_nonzero (hx ▸ w.x_mem)

def DiffWitness.zeroChild
    (hxor : ∀ g : G, g + g = 0)
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0)
    (i : {j // j ∈ w.active})
    (hi : w.x + gamma i.1 ∉ ({w.x + w.y} : Finset G)) :
    DiffWitness gamma (alpha - 1) 1 where
  active := w.active.erase i.1
  pivot := i.1
  pivot_not_active := by simp
  active_card := by
    have hc := w.active_card
    have hpos : 0 < w.active.card := Finset.card_pos.mpr ⟨i.1, i.2⟩
    rw [Finset.card_erase_of_mem i.2]
    omega
  left := {w.x}
  right := insert (w.x + gamma i.1) {w.x + w.y}
  left_nonzero := by simpa using w.x_ne_zero.symm
  x := w.x
  y := w.x + gamma i.1
  x_mem := by simp
  y_mem := by simp
  pair_eq := by
    calc
      w.x + (w.x + gamma i.1) = (w.x + w.x) + gamma i.1 := by abel
      _ = gamma i.1 := by rw [hxor]; simp
  total_links := by simp [hi]
  balanced := Or.inr (by simp [hi])

theorem DiffWitness.zeroChild_label_prob_eq_push
    (hxor : ∀ g : G, g + g = 0)
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0)
    (i : {j // j ∈ w.active})
    (hi : w.x + gamma i.1 ∉ ({w.x + w.y} : Finset G)) :
    (w.zeroChild hxor i hi).label.prob =
      (w.zeroStar.pushLeft i w.x).prob := by
  let e := eraseActiveEquiv w.active i
  have heq : (w.zeroStar.pushLeft i w.x).reindex e.symm =
      (w.zeroChild hxor i hi).label := by
    unfold DiffWitness.zeroStar pairLabel DiffWitness.zeroChild
      DiffWitness.label Label.pushLeft Label.reindex
    rw [Label.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    funext j
    rfl
  calc
    (w.zeroChild hxor i hi).label.prob =
        ((w.zeroStar.pushLeft i w.x).reindex e.symm).prob :=
      congrArg Label.prob heq.symm
    _ = (w.zeroStar.pushLeft i w.x).prob := Label.prob_reindex _ _

theorem DiffWitness.zeroChild_separated_prob_eq_activeOneLabel
    (hxor : ∀ g : G, g + g = 0)
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0)
    (i : {j // j ∈ w.active})
    (hi : w.x + gamma i.1 ∉ ({w.x + w.y} : Finset G)) :
    (w.zeroChild hxor i hi).separated.prob =
      (activeOneLabel gamma w.active w.pivot).prob := by
  have hset : insert i.1 (w.active.erase i.1) = w.active :=
    Finset.insert_erase i.2
  let e := finsetSubtypeEquivOfEq hset
  have heq : (w.zeroChild hxor i hi).separated.reindex e.symm =
      activeOneLabel gamma w.active w.pivot := by
    dsimp [e]
    unfold DiffWitness.zeroChild DiffWitness.separated activeOneLabel oneLabel
      Label.reindex finsetSubtypeEquivOfEq
    rw [Label.mk.injEq]
    refine ⟨?_, by simp, ?_⟩
    · funext j
      rfl
    · have hne : w.x + w.y ≠ w.x + gamma i.1 := by
        intro heqxy
        exact hi (by simpa [heqxy])
      have hne' : w.x + gamma i.1 ≠ w.x + w.y := hne.symm
      have hnePivot : w.x + gamma i.1 ≠ gamma w.pivot := by
        rw [← w.pair_eq]
        exact hne'
      simp [hne, hne', hnePivot, w.pair_eq]
  calc
    (w.zeroChild hxor i hi).separated.prob =
        ((w.zeroChild hxor i hi).separated.reindex e.symm).prob :=
      (Label.prob_reindex _ _).symm
    _ = (activeOneLabel gamma w.active w.pivot).prob :=
      congrArg Label.prob heq

theorem DiffWitness.abs_zeroStarDeletionTerm_sub_core_le
    (hxor : ∀ g : G, g + g = 0)
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0)
    (i : {j // j ∈ w.active}) :
    |w.zeroStar.leftDeletionTerm w.x i -
        (activeOneLabel gamma w.active w.pivot).prob| <=
      (differential gamma (alpha - 1) 1 : Real) +
        if gamma i.1 = w.y then
          (activeOneLabel gamma w.active w.pivot).prob
        else 0 := by
  let s : G := w.x + gamma i.1
  by_cases hi : s ∉ ({w.x + w.y} : Finset G)
  · have hchild := abs_diff_le_differential (w.zeroChild hxor i hi)
    rw [w.zeroChild_label_prob_eq_push hxor i hi,
      w.zeroChild_separated_prob_eq_activeOneLabel hxor i hi] at hchild
    simp only [Label.leftDeletionTerm]
    rw [dif_pos (by simpa [DiffWitness.zeroStar, pairLabel, s] using hi)]
    have hind : 0 <= if gamma i.1 = w.y then
        (activeOneLabel gamma w.active w.pivot).prob else 0 := by
      split
      · exact Label.prob_nonneg _
      · norm_num
    exact le_add_of_le_of_nonneg hchild hind
  · have hmem : s ∈ ({w.x + w.y} : Finset G) := by simpa using hi
    have heq : w.x + gamma i.1 = w.x + w.y := by simpa [s] using hmem
    have htarget : gamma i.1 = w.y := add_left_cancel heq
    have hcore0 := (activeOneLabel gamma w.active w.pivot).prob_nonneg
    simp only [Label.leftDeletionTerm]
    rw [dif_neg (by simpa [DiffWitness.zeroStar, pairLabel, s] using hi),
      htarget, if_pos rfl, zero_sub, abs_neg, abs_of_nonneg hcore0]
    have hD : 0 <= (differential gamma (alpha - 1) 1 : Real) := by positivity
    linarith

theorem DiffWitness.abs_sum_zeroStarDeletionTerm_sub_core_le
    (hxor : ∀ g : G, g + g = 0)
    {q alpha : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0) :
    |(∑ i : {j // j ∈ w.active},
        w.zeroStar.leftDeletionTerm w.x i) -
      ∑ _j : {j // j ∈ insert w.pivot w.active},
        (activeOneLabel gamma w.active w.pivot).prob| <=
      (q : Real) * (differential gamma (alpha - 1) 1 : Real) +
        3 * (maxMultiplicity gamma : Real) *
          (activeOneLabel gamma w.active w.pivot).prob := by
  let D : Real := (differential gamma (alpha - 1) 1 : Real)
  let M : Real := (activeOneLabel gamma w.active w.pivot).prob
  have hD : 0 <= D := by dsimp [D]; positivity
  have hM : 0 <= M := by dsimp [M]; exact Label.prob_nonneg _
  simpa [D, M] using abs_sum_sub_insert_le gamma w.active w.pivot
    w.pivot_not_active w.y
    (fun i => w.zeroStar.leftDeletionTerm w.x i)
    (fun _j => M) D M hD hM
    (fun i => w.abs_zeroStarDeletionTerm_sub_core_le hxor i)
    hM (le_refl M)

theorem DiffWitness.abs_diff_le_recurrence_zero
    (hxor : ∀ g : G, g + g = 0)
    {q alpha d : Nat} {gamma : Fin q -> G}
    (w : DiffWitness gamma alpha 0)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    |w.label.prob - w.separated.prob| <=
      (1 / (Fintype.card G : Real)) *
        ((q : Real) * (differential gamma (alpha - 1) 1 : Real) +
          3 * (maxMultiplicity gamma : Real) *
            (masterProb gamma /
              (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
  let M : Real := (activeOneLabel gamma w.active w.pivot).prob
  let R : Real := masterProb gamma /
    (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d
  let S : Real := ∑ i : {j // j ∈ w.active},
    w.zeroStar.leftDeletionTerm w.x i
  have hM : 0 <= M := by dsimp [M]; exact Label.prob_nonneg _
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
  have hMleR : M <= R := by
    dsimp [M, R]
    rw [← compatibleLabel_prob_eq_masterProb]
    exact activeOneLabel_prob_le_div_masterFactor_pow gamma w.active w.pivot
      w.pivot_not_active (by simpa [w.active_card] using hd) hfactor
  have hstar := w.zeroStar.prob_eq_prob_eraseLeft_sub_terms
    w.x (by simp [DiffWitness.zeroStar, pairLabel]) w.x_ne_zero
  rw [w.zeroStar_eraseLeft_eq_activeOneLabel] at hstar
  have hsepZero := activeZeroLabel_prob_eq_activeOneLabel_mul
    gamma w.active w.pivot w.pivot_not_active
  have hsep : w.separated.prob = M *
      (1 - (alpha : Real) / (Fintype.card G : Real)) := by
    rw [w.separated_eq_activeZeroLabel]
    simpa [M, w.active_card] using hsepZero
  have hsum := w.abs_sum_zeroStarDeletionTerm_sub_core_le hxor
  have hcardInsert : Fintype.card {j // j ∈ insert w.pivot w.active} = alpha := by
    rw [Fintype.card_coe, Finset.card_insert_of_notMem w.pivot_not_active,
      w.active_card]
  have hconst :
      (∑ _j : {j // j ∈ insert w.pivot w.active}, M) = (alpha : Real) * M := by
    rw [Finset.sum_const, Finset.card_univ, hcardInsert, nsmul_eq_mul]
  have hsum' : |(alpha : Real) * M - S| <=
      (q : Real) * (differential gamma (alpha - 1) 1 : Real) +
        3 * (maxMultiplicity gamma : Real) * M := by
    dsimp [S]
    rw [abs_sub_comm]
    rw [hconst] at hsum
    simpa [M] using hsum
  have hc : 0 <= (1 / (Fintype.card G : Real)) := by positivity
  have hformula : w.label.prob - w.separated.prob =
      (1 / (Fintype.card G : Real)) * ((alpha : Real) * M - S) := by
    rw [w.label_prob_eq_zeroStar hxor, hstar, hsep]
    dsimp [S]
    ring
  rw [hformula, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    |(alpha : Real) * M - S| <=
        (q : Real) * (differential gamma (alpha - 1) 1 : Real) +
          3 * (maxMultiplicity gamma : Real) * M := hsum'
    _ <= (q : Real) * (differential gamma (alpha - 1) 1 : Real) +
          3 * (maxMultiplicity gamma : Real) * R := by
      gcongr

theorem differential_recurrence_zero
    (hxor : ∀ g : G, g + g = 0)
    {q alpha d : Nat} (gamma : Fin q -> G)
    (hd : q - alpha = d)
    (hfactor : 0 < 1 - (2 * q : Nat) / (Fintype.card G : Real)) :
    (differential gamma alpha 0 : Real) <=
      (1 / (Fintype.card G : Real)) *
        ((q : Real) * (differential gamma (alpha - 1) 1 : Real) +
          3 * (maxMultiplicity gamma : Real) *
            (masterProb gamma /
              (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d)) := by
  let R : Real :=
    (1 / (Fintype.card G : Real)) *
      ((q : Real) * (differential gamma (alpha - 1) 1 : Real) +
        3 * (maxMultiplicity gamma : Real) *
          (masterProb gamma /
            (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d))
  have hR : 0 <= R := by
    dsimp [R]
    have href : 0 <= masterProb gamma /
        (1 - (2 * q : Nat) / (Fintype.card G : Real)) ^ d :=
      div_nonneg (masterProb_nonneg gamma) (pow_nonneg hfactor.le d)
    positivity
  have hsup : differential gamma alpha 0 <= Real.toNNReal R := by
    unfold differential
    apply Finset.sup_le
    intro w _hw
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal R hR]
    exact w.abs_diff_le_recurrence_zero hxor hd hfactor
  have hcoe := NNReal.coe_le_coe.mpr hsup
  rw [Real.coe_toNNReal R hR] at hcoe
  exact hcoe

/-! ### Normalized DNS recursion and the core estimate -/

theorem dns_beta_bounds
    {q N : Nat} (hN : 0 < N) (hrange : 17 * q <= N) :
    let beta : Real := (q : Real) / (N : Real)
    0 <= beta ∧
      0 < 1 - 2 * beta ∧
      beta / (1 - 2 * beta) <= (1 / 15 : Real) := by
  dsimp
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hrangeR : (17 : Real) * q <= N := by exact_mod_cast hrange
  have hbeta : 0 <= (q : Real) / N := by positivity
  have hbetaLe : (q : Real) / N <= 1 / 17 := by
    rw [div_le_iff₀ hNR]
    nlinarith
  have hfactor : 0 < 1 - 2 * ((q : Real) / N) := by nlinarith
  refine ⟨hbeta, hfactor, ?_⟩
  rw [div_le_iff₀ hfactor]
  nlinarith

def normalizedDifferential
    {q : Nat} (gamma : Fin q -> G) (d ell : Nat) : Real :=
  if d < q then
    (((q : Real) / (Fintype.card G : Real)) ^ d *
      (differential gamma (q - d) ell : Real)) /
        (2 * masterProb gamma)
  else 0

theorem normalizedDifferential_nonneg
    {q : Nat} (gamma : Fin q -> G) (d ell : Nat) :
    0 <= normalizedDifferential gamma d ell := by
  unfold normalizedDifferential
  split
  · exact div_nonneg (mul_nonneg (pow_nonneg (by positivity) d) (by positivity))
      (mul_nonneg (by norm_num) (masterProb_nonneg gamma))
  · norm_num

theorem differential_zero_alpha
    {q ell : Nat} (gamma : Fin q -> G) : differential gamma 0 ell = 0 := by
  apply le_antisymm
  · unfold differential
    apply Finset.sup_le
    intro w _hw
    exfalso
    have hc := w.active_card
    omega
  · exact bot_le

theorem normalizedDifferential_eq_of_lt
    {q : Nat} (gamma : Fin q -> G) {d ell : Nat} (hd : d < q) :
    normalizedDifferential gamma d ell =
      (((q : Real) / (Fintype.card G : Real)) ^ d *
        (differential gamma (q - d) ell : Real)) /
          (2 * masterProb gamma) := by
  simp [normalizedDifferential, hd]

theorem normalizedDifferential_succ_eq_of_lt
    {q : Nat} (gamma : Fin q -> G) {d ell : Nat} (hd : d < q) :
    normalizedDifferential gamma (d + 1) ell =
      (((q : Real) / (Fintype.card G : Real)) ^ (d + 1) *
        (differential gamma (q - (d + 1)) ell : Real)) /
          (2 * masterProb gamma) := by
  by_cases hsucc : d + 1 < q
  · exact normalizedDifferential_eq_of_lt gamma hsucc
  · have heq : d + 1 = q := by omega
    simp [normalizedDifferential, hsucc, heq, differential_zero_alpha]

theorem normalizedDifferential_initial_bound
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} (gamma : Fin q -> G) (p : Fin q)
    (hrange : 17 * q <= Fintype.card G) (d ell : Nat) :
    normalizedDifferential gamma d ell <= (1 / 15 : Real) ^ d := by
  have hN : 0 < Fintype.card G := Fintype.card_pos
  obtain ⟨hbeta, hfactor, hratio⟩ := dns_beta_bounds hN hrange
  let beta : Real := (q : Real) / (Fintype.card G : Real)
  let c : Real := 1 - 2 * beta
  have hfactor' : 0 <
      1 - (2 * q : Nat) / (Fintype.card G : Real) := by
    push_cast
    convert hfactor using 1 <;> ring
  have hc : 0 < c := by simpa [c, beta] using hfactor
  have hratio' : beta / c <= (1 / 15 : Real) := by
    simpa [beta, c] using hratio
  have hP : 0 < masterProb gamma :=
    masterProb_pos_of_masterFactor_pos gamma p hfactor'
  by_cases hdq : d < q
  · rw [normalizedDifferential_eq_of_lt gamma hdq]
    have hdsub : q - (q - d) = d := by omega
    have hdiff := differential_le_two_mul_activeOneLabel_bound
      (ell := ell) hxor gamma hdsub hfactor'
    have hcEq :
        1 - (2 * q : Nat) / (Fintype.card G : Real) = c := by
      dsimp [c, beta]
      push_cast
      ring
    rw [hcEq] at hdiff
    have hmul :
        beta ^ d * (differential gamma (q - d) ell : Real) <=
          beta ^ d * (2 * masterProb gamma / c ^ d) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hbeta d)
      simpa [beta, c] using hdiff
    have hdiv :
        (beta ^ d * (differential gamma (q - d) ell : Real)) /
            (2 * masterProb gamma) <=
          (beta ^ d * (2 * masterProb gamma / c ^ d)) /
            (2 * masterProb gamma) := by
      exact div_le_div_of_nonneg_right hmul (mul_nonneg (by norm_num) hP.le)
    calc
      (((q : Real) / (Fintype.card G : Real)) ^ d *
          (differential gamma (q - d) ell : Real)) /
            (2 * masterProb gamma) <=
          (beta ^ d * (2 * masterProb gamma / c ^ d)) /
            (2 * masterProb gamma) := by simpa [beta] using hdiv
      _ = beta ^ d / c ^ d := by
        field_simp [hP.ne', hc.ne']
      _ = (beta / c) ^ d := by
        dsimp [beta]
        rw [div_pow, div_pow]
        ring
      _ <= (1 / 15 : Real) ^ d :=
        pow_le_pow_left₀ (div_nonneg hbeta hc.le) hratio' d
  · rw [normalizedDifferential]
    simp [hdq]

theorem normalizedDifferential_recurrence_zero
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} (gamma : Fin q -> G) (p : Fin q)
    (hrange : 17 * q <= Fintype.card G) (d : Nat) :
    normalizedDifferential gamma d 0 <=
      normalizedDifferential gamma (d + 1) 1 +
        (3 * (maxMultiplicity gamma : Real) /
          (2 * (Fintype.card G : Real))) * (1 / 15 : Real) ^ d := by
  have hN : 0 < Fintype.card G := Fintype.card_pos
  obtain ⟨hbeta, hfactor, hratio⟩ := dns_beta_bounds hN hrange
  let beta : Real := (q : Real) / (Fintype.card G : Real)
  let c : Real := 1 - 2 * beta
  have hfactor' : 0 <
      1 - (2 * q : Nat) / (Fintype.card G : Real) := by
    push_cast
    convert hfactor using 1 <;> ring
  have hc : 0 < c := by simpa [c, beta] using hfactor
  have hratio' : beta / c <= (1 / 15 : Real) := by
    simpa [beta, c] using hratio
  have hP : 0 < masterProb gamma :=
    masterProb_pos_of_masterFactor_pos gamma p hfactor'
  have hNreal : (0 : Real) < Fintype.card G := by exact_mod_cast hN
  have hC : 0 <= 3 * (maxMultiplicity gamma : Real) /
      (2 * (Fintype.card G : Real)) := by positivity
  by_cases hdq : d < q
  · rw [normalizedDifferential_eq_of_lt gamma hdq,
      normalizedDifferential_succ_eq_of_lt gamma hdq]
    have hdsub : q - (q - d) = d := by omega
    have halpha : q - d - 1 = q - (d + 1) := by omega
    have hrec := differential_recurrence_zero hxor gamma hdsub hfactor'
    rw [halpha] at hrec
    have hcEq :
        1 - (2 * q : Nat) / (Fintype.card G : Real) = c := by
      dsimp [c, beta]
      push_cast
      ring
    rw [hcEq] at hrec
    let K : Real := beta ^ d / (2 * masterProb gamma)
    have hK : 0 <= K := by
      dsimp [K]
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hrec hK
    have hpowratio : (beta / c) ^ d <= (1 / 15 : Real) ^ d :=
      pow_le_pow_left₀ (div_nonneg hbeta hc.le) hratio' d
    have hpowfrac : beta ^ d / c ^ d <= (1 / 15 : Real) ^ d := by
      rw [← div_pow]
      exact hpowratio
    calc
      (((q : Real) / (Fintype.card G : Real)) ^ d *
          (differential gamma (q - d) 0 : Real)) /
            (2 * masterProb gamma) =
          K * (differential gamma (q - d) 0 : Real) := by
        dsimp [K, beta]
        ring
      _ <= K * ((1 / (Fintype.card G : Real)) *
          ((q : Real) *
              (differential gamma (q - (d + 1)) 1 : Real) +
            3 * (maxMultiplicity gamma : Real) *
              (masterProb gamma / c ^ d))) := hscaled
      _ = (beta ^ (d + 1) *
              (differential gamma (q - (d + 1)) 1 : Real)) /
            (2 * masterProb gamma) +
          (3 * (maxMultiplicity gamma : Real) /
            (2 * (Fintype.card G : Real))) * (beta ^ d / c ^ d) := by
        dsimp [K, beta]
        rw [pow_succ]
        field_simp [hP.ne', hNreal.ne', hc.ne']
      _ <= (beta ^ (d + 1) *
              (differential gamma (q - (d + 1)) 1 : Real)) /
            (2 * masterProb gamma) +
          (3 * (maxMultiplicity gamma : Real) /
            (2 * (Fintype.card G : Real))) * (1 / 15 : Real) ^ d := by
        gcongr
  · rw [normalizedDifferential]
    simp only [if_neg hdq]
    exact add_nonneg (normalizedDifferential_nonneg gamma (d + 1) 1)
      (mul_nonneg hC (pow_nonneg (by norm_num) d))

theorem normalizedDifferential_recurrence_succ
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} (gamma : Fin q -> G) (p : Fin q)
    (hrange : 17 * q <= Fintype.card G) (d ell : Nat) :
    normalizedDifferential gamma d (ell + 1) <=
      normalizedDifferential gamma d ell +
        normalizedDifferential gamma (d + 1) (ell + 2) +
        (3 * (maxMultiplicity gamma : Real) /
          (2 * (Fintype.card G : Real))) * (1 / 15 : Real) ^ d := by
  have hN : 0 < Fintype.card G := Fintype.card_pos
  obtain ⟨hbeta, hfactor, hratio⟩ := dns_beta_bounds hN hrange
  let beta : Real := (q : Real) / (Fintype.card G : Real)
  let c : Real := 1 - 2 * beta
  have hfactor' : 0 <
      1 - (2 * q : Nat) / (Fintype.card G : Real) := by
    push_cast
    convert hfactor using 1 <;> ring
  have hc : 0 < c := by simpa [c, beta] using hfactor
  have hratio' : beta / c <= (1 / 15 : Real) := by
    simpa [beta, c] using hratio
  have hP : 0 < masterProb gamma :=
    masterProb_pos_of_masterFactor_pos gamma p hfactor'
  have hNreal : (0 : Real) < Fintype.card G := by exact_mod_cast hN
  have hC : 0 <= 3 * (maxMultiplicity gamma : Real) /
      (2 * (Fintype.card G : Real)) := by positivity
  by_cases hdq : d < q
  · rw [normalizedDifferential_eq_of_lt gamma hdq,
      normalizedDifferential_eq_of_lt gamma hdq,
      normalizedDifferential_succ_eq_of_lt gamma hdq]
    have hdsub : q - (q - d) = d := by omega
    have halpha : q - d - 1 = q - (d + 1) := by omega
    have hrec := differential_recurrence_of_pos hxor gamma
      (ell := ell + 1) (by omega) hdsub hfactor'
    rw [halpha, show ell + 1 - 1 = ell by omega] at hrec
    have hcEq :
        1 - (2 * q : Nat) / (Fintype.card G : Real) = c := by
      dsimp [c, beta]
      push_cast
      ring
    rw [hcEq] at hrec
    let K : Real := beta ^ d / (2 * masterProb gamma)
    have hK : 0 <= K := by dsimp [K]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hrec hK
    have hpowratio : (beta / c) ^ d <= (1 / 15 : Real) ^ d :=
      pow_le_pow_left₀ (div_nonneg hbeta hc.le) hratio' d
    have hpowfrac : beta ^ d / c ^ d <= (1 / 15 : Real) ^ d := by
      rw [← div_pow]
      exact hpowratio
    calc
      (((q : Real) / (Fintype.card G : Real)) ^ d *
          (differential gamma (q - d) (ell + 1) : Real)) /
            (2 * masterProb gamma) =
          K * (differential gamma (q - d) (ell + 1) : Real) := by
        dsimp [K, beta]
        ring
      _ <= K * ((differential gamma (q - d) ell : Real) +
          (1 / (Fintype.card G : Real)) *
            ((q : Real) *
                (differential gamma (q - (d + 1)) (ell + 2) : Real) +
              3 * (maxMultiplicity gamma : Real) *
                (masterProb gamma / c ^ d))) := hscaled
      _ = (beta ^ d * (differential gamma (q - d) ell : Real)) /
              (2 * masterProb gamma) +
          (beta ^ (d + 1) *
              (differential gamma (q - (d + 1)) (ell + 2) : Real)) /
              (2 * masterProb gamma) +
          (3 * (maxMultiplicity gamma : Real) /
            (2 * (Fintype.card G : Real))) * (beta ^ d / c ^ d) := by
        dsimp [K, beta]
        rw [pow_succ]
        field_simp [hP.ne', hNreal.ne', hc.ne']
        ring
      _ <= (beta ^ d * (differential gamma (q - d) ell : Real)) /
              (2 * masterProb gamma) +
          (beta ^ (d + 1) *
              (differential gamma (q - (d + 1)) (ell + 2) : Real)) /
              (2 * masterProb gamma) +
          (3 * (maxMultiplicity gamma : Real) /
            (2 * (Fintype.card G : Real))) * (1 / 15 : Real) ^ d := by
        gcongr
  · rw [normalizedDifferential]
    simp only [if_neg hdq]
    exact add_nonneg
      (add_nonneg (normalizedDifferential_nonneg gamma d ell)
        (normalizedDifferential_nonneg gamma (d + 1) (ell + 2)))
      (mul_nonneg hC (pow_nonneg (by norm_num) d))

theorem normalizedDifferential_zero_bound
    (hxor : ∀ g : G, g + g = 0)
    {q : Nat} (gamma : Fin q -> G) (p : Fin q)
    (hrange : 17 * q <= Fintype.card G) (depth : Nat) :
    normalizedDifferential gamma 0 0 <=
      (8 / 15 : Real) ^ depth +
        9 * (maxMultiplicity gamma : Real) /
          (2 * (Fintype.card G : Real)) := by
  let C : Real := 3 * (maxMultiplicity gamma : Real) /
    (2 * (Fintype.card G : Real))
  have hC : 0 <= C := by dsimp [C]; positivity
  have h := recursive_inequality
    (normalizedDifferential gamma) C hC
    (normalizedDifferential_initial_bound hxor gamma p hrange)
    (normalizedDifferential_recurrence_zero hxor gamma p hrange)
    (normalizedDifferential_recurrence_succ hxor gamma p hrange)
    depth
  dsimp [C] at h
  calc
    normalizedDifferential gamma 0 0 <=
        (8 / 15 : Real) ^ depth +
          3 * (3 * (maxMultiplicity gamma : Real) /
            (2 * (Fintype.card G : Real))) := h
    _ = (8 / 15 : Real) ^ depth +
          9 * (maxMultiplicity gamma : Real) /
            (2 * (Fintype.card G : Real)) := by ring

/-! The geometric terminal term is retained in the primary XOR core bound.
It is strictly smaller than the convenient `1 / 2^n` replacement except at
the degenerate depth zero, so downstream estimates can choose whether to keep
that gain or use the simpler integer coefficient. -/

theorem xor_differential_core_bound_exact
    {n q : Nat} (gamma : Fin q -> XorSpace n) (p : Fin q)
    (hrange : 17 * q <= 2 ^ n) :
    (differential gamma q 0 : Real) <=
      (2 * (8 / 15 : Real) ^ (2 * n) +
          9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real))) *
        masterProb gamma := by
  have hN : Fintype.card (XorSpace n) = 2 ^ n := card_xorSpace n
  have hrange' : 17 * q <= Fintype.card (XorSpace n) := by simpa [hN] using hrange
  have hfactor : 0 <
      1 - (2 * q : Nat) /
        (Fintype.card (XorSpace n) : Real) := by
    obtain ⟨_hb, hf, _hr⟩ := dns_beta_bounds Fintype.card_pos hrange'
    push_cast
    convert hf using 1 <;> ring
  have hP : 0 < masterProb gamma :=
    masterProb_pos_of_masterFactor_pos gamma p hfactor
  have hzero := normalizedDifferential_zero_bound
    (fun g => add_self_eq_zero n g) gamma p hrange' (2 * n)
  have hnorm : normalizedDifferential gamma 0 0 =
      (differential gamma q 0 : Real) / (2 * masterProb gamma) := by
    have hq : 0 < q := by have hp := p.isLt; omega
    rw [normalizedDifferential_eq_of_lt gamma hq]
    simp
  rw [hnorm, hN] at hzero
  rw [div_le_iff₀ (mul_pos (by norm_num) hP)] at hzero
  calc
    (differential gamma q 0 : Real) <=
        ((8 / 15 : Real) ^ (2 * n) +
          9 * (maxMultiplicity gamma : Real) /
            (2 * (((2 ^ n : Nat) : Real)))) *
          (2 * masterProb gamma) := hzero
    _ = (2 * (8 / 15 : Real) ^ (2 * n) +
          9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real))) *
        masterProb gamma := by ring

/-- A denominator-only corollary of the exact core bound.  The formal DNS
recursion gives coefficient `11`, improving the published intermediate
coefficient `16`. -/
theorem xor_differential_core_bound
    {n q : Nat} (gamma : Fin q -> XorSpace n) (p : Fin q)
    (hrange : 17 * q <= 2 ^ n) :
    (differential gamma q 0 : Real) <=
      11 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) *
        masterProb gamma := by
  have hexact := xor_differential_core_bound_exact gamma p hrange
  have hterm := recursive_terminal_le n
  have hmult : 1 <= maxMultiplicity gamma := one_le_maxMultiplicity gamma p
  have hmultR : (1 : Real) <= maxMultiplicity gamma := by exact_mod_cast hmult
  have hNreal : (0 : Real) < ((2 ^ n : Nat) : Real) := by positivity
  have hcoef :
      2 * (8 / 15 : Real) ^ (2 * n) +
          9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) <=
        11 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) := by
    have ht : 2 * (8 / 15 : Real) ^ (2 * n) <=
        2 / (((2 ^ n : Nat) : Real)) := by
      calc
        2 * (8 / 15 : Real) ^ (2 * n) <=
            2 * (1 / (((2 ^ n : Nat) : Real))) :=
          mul_le_mul_of_nonneg_left hterm (by norm_num)
        _ = 2 / (((2 ^ n : Nat) : Real)) := by ring
    calc
      2 * (8 / 15 : Real) ^ (2 * n) +
            9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) <=
          2 / (((2 ^ n : Nat) : Real)) +
            9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) := by
        gcongr
      _ <= 11 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) := by
        calc
          2 / (((2 ^ n : Nat) : Real)) +
                9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) =
              (2 + 9 * (maxMultiplicity gamma : Real)) /
                (((2 ^ n : Nat) : Real)) := by ring
          _ <= 11 * (maxMultiplicity gamma : Real) /
                (((2 ^ n : Nat) : Real)) := by
            gcongr
            nlinarith
  exact hexact.trans (mul_le_mul_of_nonneg_right hcoef (masterProb_nonneg gamma))

/-! ## Adding one output coordinate

The main DNS induction is most naturally run backwards: at each nonempty
tuple choose a coordinate at which the maximum multiplicity is attained and
delete that coordinate.  The remaining tuple is canonically indexed by
`Fin m` through `finSuccAboveEquiv`. -/

theorem maxMultiplicity_attained
    {q : Nat} (gamma : Fin q -> G) (hq : 0 < q) :
    ∃ p : Fin q, maxMultiplicity gamma = multiplicity gamma (gamma p) := by
  have huniv : (Finset.univ : Finset (Fin q)).Nonempty := by
    exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨p, _hp, heq⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin q)) huniv
      (fun i => multiplicity gamma (gamma i))
  exact ⟨p, heq⟩

/-- Delete one coordinate and enumerate its complement in increasing order. -/
def dropCoordinate {m : Nat} (eta : Fin (m + 1) -> G) (p : Fin (m + 1)) :
    Fin m -> G :=
  fun i => eta ((finSuccAboveEquiv p) i).1

theorem multiplicity_comp_embedding_le
    {a b : Nat} (eta : Fin b -> G) (e : Fin a ↪ Fin b) (v : G) :
    multiplicity (fun i => eta (e i)) v <= multiplicity eta v := by
  classical
  unfold multiplicity
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · exact e.injective.injOn

theorem maxMultiplicity_dropCoordinate_le
    {m : Nat} (eta : Fin (m + 1) -> G) (p : Fin (m + 1)) :
    maxMultiplicity (dropCoordinate eta p) <= maxMultiplicity eta := by
  classical
  unfold maxMultiplicity
  apply Finset.sup_le
  intro i _hi
  let e : Fin m ↪ Fin (m + 1) :=
    ⟨fun j => ((finSuccAboveEquiv p) j).1, fun _ _ h =>
      (finSuccAboveEquiv p).injective (Subtype.ext h)⟩
  have hcomp := multiplicity_comp_embedding_le eta
    e (dropCoordinate eta p i)
  have hcomp' : multiplicity (dropCoordinate eta p) (dropCoordinate eta p i) <=
      multiplicity eta (dropCoordinate eta p i) := by
    simpa [dropCoordinate] using hcomp
  exact hcomp'.trans
    (multiplicity_le_maxMultiplicity eta (dropCoordinate eta p i))

theorem compatibleLabel_dropCoordinate_prob
    {m : Nat} (eta : Fin (m + 1) -> G) (p : Fin (m + 1)) :
    (compatibleLabel eta p).prob =
      (oneLabel (dropCoordinate eta p) (eta p)).prob := by
  let e := finSuccAboveEquiv p
  have heq : (compatibleLabel eta p).reindex e =
      oneLabel (dropCoordinate eta p) (eta p) := by
    unfold compatibleLabel oneLabel Label.reindex dropCoordinate
    rw [Label.mk.injEq]
    exact ⟨rfl, rfl, rfl⟩
  rw [← heq, Label.prob_reindex]

theorem masterProb_eq_oneLabel_dropCoordinate
    {m : Nat} (eta : Fin (m + 1) -> G) (p : Fin (m + 1)) :
    masterProb eta = (oneLabel (dropCoordinate eta p) (eta p)).prob := by
  rw [← compatibleLabel_dropCoordinate_prob eta p,
    compatibleLabel_prob_eq_masterProb]

theorem zeroLabel_dropCoordinate_prob
    {m : Nat} (eta : Fin (m + 1) -> G) (p : Fin (m + 1)) (i : Fin m) :
    (zeroLabel (dropCoordinate eta p)).prob =
      masterProb (dropCoordinate eta p) *
        (1 - (m : Real) / (Fintype.card G : Real)) := by
  rw [zeroLabel_prob_eq_compatibleLabel_prob_mul (dropCoordinate eta p) i,
    compatibleLabel_prob_eq_masterProb]
  simp

theorem multiplicity_dropCoordinate_add_one
    {m : Nat} (eta : Fin (m + 1) -> G) (p : Fin (m + 1)) :
    multiplicity eta (eta p) =
      multiplicity (dropCoordinate eta p) (eta p) + 1 := by
  classical
  let s : Finset (Fin (m + 1)) :=
    (Finset.univ.filter (fun j => eta j = eta p)).erase p
  let t : Finset (Fin m) :=
    Finset.univ.filter (fun i => dropCoordinate eta p i = eta p)
  let e := finSuccAboveEquiv p
  have hcard : s.card = t.card := by
    apply Finset.card_bij
      (fun j hj => e.symm ⟨j, (Finset.mem_erase.mp hj).1⟩)
    · intro j hj
      have hjval : eta j = eta p :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      change eta (((finSuccAboveEquiv p)
        (e.symm ⟨j, (Finset.mem_erase.mp hj).1⟩)).1) = eta p
      rw [show finSuccAboveEquiv p = e from rfl, e.apply_symm_apply]
      exact hjval
    · intro j hj k hk heq
      have hsub : (⟨j, (Finset.mem_erase.mp hj).1⟩ : Without p) =
          ⟨k, (Finset.mem_erase.mp hk).1⟩ := by
        simpa using congrArg e heq
      exact congrArg Subtype.val hsub
    · intro i hi
      let j : Fin (m + 1) := (e i).1
      have hjne : j ≠ p := (e i).2
      have hjval : eta j = eta p := by
        have hi' := (Finset.mem_filter.mp hi).2
        simpa [j, dropCoordinate] using hi'
      refine ⟨j, ?_, ?_⟩
      · exact Finset.mem_erase.mpr
          ⟨hjne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjval⟩⟩
      · simp [j, e]
  have hp : p ∈ (Finset.univ.filter (fun j => eta j = eta p)) := by simp
  have herase := Finset.card_erase_add_one hp
  unfold multiplicity
  change (Finset.univ.filter (fun j => eta j = eta p)).card =
    (Finset.univ.filter (fun i => dropCoordinate eta p i = eta p)).card + 1
  change _ = t.card + 1
  rw [← hcard]
  exact herase.symm

/-- The differential witness attached to a genuinely nonzero term in the
right-link deletion of a one-linked label. -/
def oneLinkPushWitness
    (hxor : ∀ g : G, g + g = 0)
    {m : Nat} (gamma : Fin m -> G) (rho : G) (i : Fin m)
    (hne : gamma i ≠ rho) : DiffWitness gamma m 0 where
  active := Finset.univ.erase i
  pivot := i
  pivot_not_active := Finset.notMem_erase i Finset.univ
  active_card := by
    have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simpa [h] using i.isLt)
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  left := {rho + gamma i}
  right := {rho}
  left_nonzero := by
    simp only [Finset.mem_singleton]
    intro hzero
    apply hne
    calc
      gamma i = 0 + gamma i := by simp
      _ = (rho + gamma i) + gamma i := by rw [hzero]
      _ = rho + (gamma i + gamma i) := by abel
      _ = rho := by rw [hxor]; simp
  x := rho + gamma i
  y := rho
  x_mem := Finset.mem_singleton_self _
  y_mem := Finset.mem_singleton_self _
  pair_eq := by
    calc
      (rho + gamma i) + rho = gamma i + (rho + rho) := by abel
      _ = gamma i := by rw [hxor]; simp
  total_links := by simp
  balanced := by simp

theorem oneLinkPushWitness_label_prob
    (hxor : ∀ g : G, g + g = 0)
    {m : Nat} (gamma : Fin m -> G) (rho : G) (i : Fin m)
    (hne : gamma i ≠ rho) :
    (oneLinkPushWitness hxor gamma rho i hne).label.prob =
      ((oneLabel gamma rho).pushRight i rho).prob := by
  let e := eraseSubtypeEquiv i
  have heq : ((oneLabel gamma rho).pushRight i rho).reindex e =
      (oneLinkPushWitness hxor gamma rho i hne).label := by
    unfold oneLinkPushWitness DiffWitness.label oneLabel Label.pushRight
      Label.reindex
    dsimp [e, eraseSubtypeEquiv]
  rw [← heq]
  exact Label.prob_reindex ((oneLabel gamma rho).pushRight i rho) e

theorem oneLinkPushWitness_separated_prob
    (hxor : ∀ g : G, g + g = 0)
    {m : Nat} (gamma : Fin m -> G) (rho : G) (i : Fin m)
    (hne : gamma i ≠ rho) :
    (oneLinkPushWitness hxor gamma rho i hne).separated.prob =
      (zeroLabel gamma).prob := by
  let e : Fin m ≃
      {j // j ∈ insert i ((Finset.univ : Finset (Fin m)).erase i)} :=
    { toFun := fun j => ⟨j, by simp⟩
      invFun := fun j => j.1
      left_inv := fun _ => rfl
      right_inv := fun _ => by apply Subtype.ext; rfl }
  have heq :
      ((oneLinkPushWitness hxor gamma rho i hne).separated.reindex e) =
        zeroLabel gamma := by
    unfold oneLinkPushWitness DiffWitness.separated Label.reindex zeroLabel
    rw [Label.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext j
      rfl
    · simp
    · simp
  rw [← heq]
  exact (Label.prob_reindex
    (oneLinkPushWitness hxor gamma rho i hne).separated e).symm

theorem oneLabel_pushRight_prob_le_exact
    {n m : Nat} (gamma : Fin m -> XorSpace n) (rho : XorSpace n) (i : Fin m)
    (hne : gamma i ≠ rho) (hrange : 17 * m <= 2 ^ n) :
    ((oneLabel gamma rho).pushRight i rho).prob <=
      (zeroLabel gamma).prob +
        (2 * (8 / 15 : Real) ^ (2 * n) +
          9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real))) *
          masterProb gamma := by
  let w := oneLinkPushWitness (fun g => add_self_eq_zero n g) gamma rho i hne
  have habs := abs_diff_le_differential w
  have hcore := xor_differential_core_bound_exact gamma i hrange
  rw [oneLinkPushWitness_label_prob, oneLinkPushWitness_separated_prob] at habs
  have hsub :
      ((oneLabel gamma rho).pushRight i rho).prob - (zeroLabel gamma).prob <=
        (differential gamma m 0 : Real) :=
    (le_abs_self _).trans habs
  linarith

theorem oneLabel_pushRight_prob_eq_zero
    {n m : Nat} (gamma : Fin m -> XorSpace n) (rho : XorSpace n) (i : Fin m)
    (heq : gamma i = rho) :
    ((oneLabel gamma rho).pushRight i rho).prob = 0 := by
  apply Label.prob_eq_zero_of_zero_mem_left
  change 0 ∈ insert (rho + gamma i) ∅
  simp [heq, add_self_eq_zero]

theorem masterProb_addCoordinate_deletion_identity
    {n m : Nat} (eta : Fin (m + 1) -> XorSpace n) (p : Fin (m + 1)) :
    masterProb eta =
      (zeroLabel (dropCoordinate eta p)).prob -
        (1 / (((2 ^ n : Nat) : Real))) *
          ∑ i : Fin m,
            ((oneLabel (dropCoordinate eta p) (eta p)).pushRight i (eta p)).prob := by
  let gamma := dropCoordinate eta p
  let rho := eta p
  have hdel := Label.prob_eq_prob_eraseRight_sub_terms
    (fun g : XorSpace n => add_self_eq_zero n g)
    (oneLabel gamma rho) rho (by simp [oneLabel])
  have herase : (oneLabel gamma rho).eraseRight rho = zeroLabel gamma := by
    unfold oneLabel Label.eraseRight zeroLabel
    simp
  rw [herase] at hdel
  simp only [Label.rightDeletionTerm, oneLabel, Finset.notMem_empty,
    dite_true] at hdel
  rw [card_xorSpace] at hdel
  rw [masterProb_eq_oneLabel_dropCoordinate eta p]
  simpa [gamma, rho] using hdel

theorem sum_oneLabel_pushRight_le_exact
    {n m : Nat} (eta : Fin (m + 1) -> XorSpace n) (p : Fin (m + 1))
    (hmax : maxMultiplicity eta = multiplicity eta (eta p))
    (hrange : 17 * m <= 2 ^ n) :
    (∑ i : Fin m,
        ((oneLabel (dropCoordinate eta p) (eta p)).pushRight i (eta p)).prob) <=
      ((m - multiplicity (dropCoordinate eta p) (eta p) : Nat) : Real) *
        ((zeroLabel (dropCoordinate eta p)).prob +
          (2 * (8 / 15 : Real) ^ (2 * n) +
            9 * ((multiplicity (dropCoordinate eta p) (eta p) + 1 : Nat) : Real) /
              (((2 ^ n : Nat) : Real))) *
            masterProb (dropCoordinate eta p)) := by
  classical
  by_cases hm : m = 0
  · subst m
    simp
  · let gamma := dropCoordinate eta p
    let rho := eta p
    let delta := multiplicity gamma rho
    let B : Real := (zeroLabel gamma).prob +
      (2 * (8 / 15 : Real) ^ (2 * n) +
        9 * ((delta + 1 : Nat) : Real) / (((2 ^ n : Nat) : Real))) *
        masterProb gamma
    have hmaxDrop : maxMultiplicity gamma <= delta + 1 := by
      calc
        maxMultiplicity gamma <= maxMultiplicity eta := by
          simpa [gamma] using maxMultiplicity_dropCoordinate_le eta p
        _ = multiplicity eta rho := by simpa [rho] using hmax
        _ = delta + 1 := by
          simpa [gamma, rho, delta] using multiplicity_dropCoordinate_add_one eta p
    have hB : 0 <= B := by
      dsimp [B]
      exact add_nonneg (zeroLabel gamma).prob_nonneg
        (mul_nonneg (add_nonneg (by positivity) (by positivity))
          (masterProb_nonneg gamma))
    have hpoint (i : Fin m) :
        ((oneLabel gamma rho).pushRight i rho).prob <=
          if gamma i = rho then 0 else B := by
      by_cases hi : gamma i = rho
      · rw [if_pos hi, oneLabel_pushRight_prob_eq_zero gamma rho i hi]
      · rw [if_neg hi]
        have hpush := oneLabel_pushRight_prob_le_exact gamma rho i hi hrange
        have hcoef :
            2 * (8 / 15 : Real) ^ (2 * n) +
                9 * (maxMultiplicity gamma : Real) / (((2 ^ n : Nat) : Real)) <=
              2 * (8 / 15 : Real) ^ (2 * n) +
                9 * ((delta + 1 : Nat) : Real) / (((2 ^ n : Nat) : Real)) := by
          gcongr
        dsimp [B]
        calc
          ((oneLabel gamma rho).pushRight i rho).prob <=
              (zeroLabel gamma).prob +
                (2 * (8 / 15 : Real) ^ (2 * n) +
                  9 * (maxMultiplicity gamma : Real) /
                    (((2 ^ n : Nat) : Real))) * masterProb gamma := hpush
          _ <= (zeroLabel gamma).prob +
              (2 * (8 / 15 : Real) ^ (2 * n) +
                9 * ((delta + 1 : Nat) : Real) /
                  (((2 ^ n : Nat) : Real))) * masterProb gamma := by
            gcongr
            exact masterProb_nonneg gamma
    have hsum :
        (∑ i : Fin m, ((oneLabel gamma rho).pushRight i rho).prob) <=
          ∑ i : Fin m, if gamma i = rho then 0 else B :=
      Finset.sum_le_sum fun i _ => hpoint i
    let s : Finset (Fin m) :=
      Finset.univ.filter (fun i => gamma i ≠ rho)
    have hcard : s.card = m - delta := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (fun i => gamma i = rho)
      have hpart : delta + s.card = m := by
        simpa [delta, multiplicity, s] using hpartition
      omega
    have hsumB :
        (∑ i : Fin m, if gamma i = rho then 0 else B) =
          ((m - delta : Nat) : Real) * B := by
      calc
        (∑ i : Fin m, if gamma i = rho then 0 else B) =
            ∑ i : Fin m, if gamma i ≠ rho then B else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases h : gamma i = rho <;> simp [h]
        _ = ∑ _i ∈ s, B := by rw [Finset.sum_filter]
        _ = (s.card : Real) * B := by simp
        _ = ((m - delta : Nat) : Real) * B := by rw [hcard]
    dsimp [gamma, rho, delta, B] at hsum hsumB ⊢
    exact hsum.trans_eq hsumB

theorem main_step_numeric
    (N m delta t : Real) (hN : 0 < N) (hm : 0 <= m)
    (hdelta : 0 <= delta) (hdeltam : delta <= m)
    (hrange : 17 * m <= N) (ht : 0 <= t) :
    (1 - m / N) ^ 2 - (m / N) * (2 * t + 9 / N) <=
      (1 - m / N) - ((m - delta) / N) *
        ((1 - m / N) + (2 * t + 9 * (delta + 1) / N)) := by
  have hNt : 0 <= 2 * N * t := by positivity
  have hbracket : 0 <= N - 10 * m + 9 * delta + 9 + 2 * N * t := by
    nlinarith
  have hprod := mul_nonneg hdelta hbracket
  field_simp [hN.ne']
  nlinarith

/-- The sharp one-coordinate inequality obtained from the formal DNS core.
The first factor is the exact falling-factorial step.  The second summand is
the only mirror loss, with the geometric terminal term still visible. -/
theorem masterProb_addCoordinate_main_lower_exact
    {n m : Nat} (eta : Fin (m + 1) -> XorSpace n) (p : Fin (m + 1))
    (hm : 0 < m)
    (hmax : maxMultiplicity eta = multiplicity eta (eta p))
    (hrange : 17 * m <= 2 ^ n) :
    masterProb (dropCoordinate eta p) *
        ((1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 -
          ((m : Real) / (((2 ^ n : Nat) : Real))) *
            (2 * (8 / 15 : Real) ^ (2 * n) +
              9 / (((2 ^ n : Nat) : Real)))) <=
      masterProb eta := by
  let gamma := dropCoordinate eta p
  let rho := eta p
  let delta := multiplicity gamma rho
  let N : Real := ((2 ^ n : Nat) : Real)
  let t : Real := (8 / 15 : Real) ^ (2 * n)
  let P : Real := masterProb gamma
  let Z : Real := (zeroLabel gamma).prob
  let B : Real := Z +
    (2 * t + 9 * ((delta + 1 : Nat) : Real) / N) * P
  have hN : 0 < N := by dsimp [N]; positivity
  have hmR : (0 : Real) <= m := by positivity
  have hdelta : (0 : Real) <= delta := by positivity
  have hdeltamNat : delta <= m := by
    dsimp [delta, gamma]
    unfold multiplicity
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hdeltam : (delta : Real) <= m := by exact_mod_cast hdeltamNat
  have hrangeR : 17 * (m : Real) <= N := by
    dsimp [N]
    exact_mod_cast hrange
  have ht : 0 <= t := by dsimp [t]; positivity
  have hnumeric := main_step_numeric N (m : Real) (delta : Real) t hN
    hmR hdelta hdeltam hrangeR ht
  have hP : 0 <= P := by dsimp [P]; exact masterProb_nonneg gamma
  have hnumericP := mul_le_mul_of_nonneg_left hnumeric hP
  have hsum := sum_oneLabel_pushRight_le_exact eta p hmax hrange
  have hsum' :
      (∑ i : Fin m, ((oneLabel gamma rho).pushRight i rho).prob) <=
        ((m : Real) - (delta : Real)) * B := by
    dsimp [gamma, rho, delta, B, Z, t, N, P]
    rw [← Nat.cast_sub hdeltamNat]
    exact hsum
  have hzero := zeroLabel_dropCoordinate_prob eta p ⟨0, hm⟩
  have hzero' : Z = P * (1 - (m : Real) / N) := by
    simpa [Z, P, gamma, N] using hzero
  have hdel := masterProb_addCoordinate_deletion_identity eta p
  have hdel' : masterProb eta = Z - (1 / N) *
      ∑ i : Fin m, ((oneLabel gamma rho).pushRight i rho).prob := by
    simpa [Z, N, gamma, rho] using hdel
  have hinv : 0 <= 1 / N := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum' hinv
  have hsubtract := sub_le_sub_left hmul Z
  calc
    masterProb gamma *
          ((1 - (m : Real) / N) ^ 2 -
            ((m : Real) / N) * (2 * t + 9 / N)) <=
        P * ((1 - (m : Real) / N) -
          (((m : Real) - (delta : Real)) / N) *
            ((1 - (m : Real) / N) +
              (2 * t + 9 * ((delta : Real) + 1) / N))) := by
      simpa [P] using hnumericP
    _ = Z - (1 / N) * (((m : Real) - (delta : Real)) * B) := by
      dsimp [B]
      rw [hzero']
      push_cast
      ring
    _ <= Z - (1 / N) *
        ∑ i : Fin m, ((oneLabel gamma rho).pushRight i rho).prob := hsubtract
    _ = masterProb eta := hdel'.symm

/-! ### The exact DNS product

For the first `2*n` coordinates DNS uses only the elementary insertion
estimate.  Thereafter it uses the sharp deletion estimate above.  Keeping the
two literal step factors gives a stronger and more informative endpoint than
immediately replacing their product by `1 - sum(losses)`. -/

def dnsBaseStepFactor (n m : Nat) : Real :=
  1 - 2 * (m : Real) / (((2 ^ n : Nat) : Real))

def dnsMainStepFactor (n m : Nat) : Real :=
  (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 -
    ((m : Real) / (((2 ^ n : Nat) : Real))) *
      (2 * (8 / 15 : Real) ^ (2 * n) +
        9 / (((2 ^ n : Nat) : Real)))

def dnsStepFactor (n m : Nat) : Real :=
  if m < 2 * n then dnsBaseStepFactor n m else dnsMainStepFactor n m

def dnsExactProduct (n q : Nat) : Real :=
  ∏ m ∈ Finset.range q, dnsStepFactor n m

def dnsBaseStepLoss (n m : Nat) : Real :=
  (m : Real) ^ 2 /
    ((((2 ^ n : Nat) : Real) - (m : Real)) ^ 2)

def dnsMainStepLoss (n m : Nat) : Real :=
  (m : Real) *
      (9 + 2 * (((2 ^ n : Nat) : Real)) * (8 / 15 : Real) ^ (2 * n)) /
    ((((2 ^ n : Nat) : Real) - (m : Real)) ^ 2)

def dnsStepLoss (n m : Nat) : Real :=
  if m < 2 * n then dnsBaseStepLoss n m else dnsMainStepLoss n m

def dnsExactLossProduct (n q : Nat) : Real :=
  ∏ m ∈ Finset.range q, (1 - dnsStepLoss n m)

def dnsExactError (n q : Nat) : Real :=
  ∑ m ∈ Finset.range q, dnsStepLoss n m

def dnsFallingBaseline (n q : Nat) : Real :=
  ((((2 ^ n).descFactorial q : Nat) : Real) /
      (((2 ^ n : Nat) : Real) ^ q)) ^ 2

theorem dnsBaseStepFactor_eq
    {n m : Nat} (hmN : m < 2 ^ n) :
    dnsBaseStepFactor n m =
      (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 *
        (1 - dnsBaseStepLoss n m) := by
  have hden : (((2 ^ n : Nat) : Real) - (m : Real)) ≠ 0 := by
    have : (m : Real) < ((2 ^ n : Nat) : Real) := by exact_mod_cast hmN
    linarith
  unfold dnsBaseStepFactor dnsBaseStepLoss
  field_simp [hden]
  ring

theorem dnsMainStepFactor_eq
    {n m : Nat} (hmN : m < 2 ^ n) :
    dnsMainStepFactor n m =
      (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 *
        (1 - dnsMainStepLoss n m) := by
  have hden : (((2 ^ n : Nat) : Real) - (m : Real)) ≠ 0 := by
    have : (m : Real) < ((2 ^ n : Nat) : Real) := by exact_mod_cast hmN
    linarith
  unfold dnsMainStepFactor dnsMainStepLoss
  field_simp [hden]
  ring

theorem dnsStepFactor_eq
    {n m : Nat} (hmN : m < 2 ^ n) :
    dnsStepFactor n m =
      (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 *
        (1 - dnsStepLoss n m) := by
  by_cases hbase : m < 2 * n
  · simp only [dnsStepFactor, dnsStepLoss, if_pos hbase]
    exact dnsBaseStepFactor_eq hmN
  · simp only [dnsStepFactor, dnsStepLoss, if_neg hbase]
    exact dnsMainStepFactor_eq hmN

theorem dns_falling_baseline_eq_product
    {n q : Nat} (hqN : q <= 2 ^ n) :
    dnsFallingBaseline n q =
      ∏ m ∈ Finset.range q,
        (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 := by
  have hN : (0 : Real) < ((2 ^ n : Nat) : Real) := by positivity
  have hdesc : ((((2 ^ n).descFactorial q : Nat) : Real)) =
      ∏ m ∈ Finset.range q,
        (((2 ^ n : Nat) : Real) - (m : Real)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro m hm
    rw [Nat.cast_sub]
    exact le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hm) hqN)
  have hprod :
      (∏ m ∈ Finset.range q,
        (1 - (m : Real) / (((2 ^ n : Nat) : Real)))) =
      ((((2 ^ n).descFactorial q : Nat) : Real)) /
        (((2 ^ n : Nat) : Real) ^ q) := by
    conv_lhs =>
      arg 2
      ext m
      rw [show 1 - (m : Real) / (((2 ^ n : Nat) : Real)) =
          ((((2 ^ n : Nat) : Real) - (m : Real)) /
            (((2 ^ n : Nat) : Real))) from by field_simp [hN.ne']]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
      ← hdesc]
  unfold dnsFallingBaseline
  rw [Finset.prod_pow, hprod]

theorem dnsExactProduct_eq_normalized
    {n q : Nat} (hqN : q <= 2 ^ n) :
    dnsExactProduct n q =
      dnsFallingBaseline n q * dnsExactLossProduct n q := by
  calc
    dnsExactProduct n q =
        ∏ m ∈ Finset.range q,
          ((1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 *
            (1 - dnsStepLoss n m)) := by
      unfold dnsExactProduct
      apply Finset.prod_congr rfl
      intro m hm
      exact dnsStepFactor_eq
        (lt_of_lt_of_le (Finset.mem_range.mp hm) hqN)
    _ = (∏ m ∈ Finset.range q,
          (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2) *
        (∏ m ∈ Finset.range q, (1 - dnsStepLoss n m)) := by
      rw [Finset.prod_mul_distrib]
    _ = dnsFallingBaseline n q * dnsExactLossProduct n q := by
      rw [← dns_falling_baseline_eq_product hqN]
      rfl

theorem dnsStepLoss_nonneg (n m : Nat) : 0 <= dnsStepLoss n m := by
  by_cases hbase : m < 2 * n
  · simp only [dnsStepLoss, if_pos hbase]
    unfold dnsBaseStepLoss
    positivity
  · simp only [dnsStepLoss, if_neg hbase]
    unfold dnsMainStepLoss
    positivity

theorem dns_base_product_le_activeOneLabel
    {n q : Nat} (gamma : Fin q -> XorSpace n)
    (A : Finset (Fin q)) (p : Fin q) (hp : p ∉ A)
    (hrange : 2 * q <= 2 ^ n) :
    (∏ m ∈ Finset.range (A.card + 1), dnsBaseStepFactor n m) <=
      (activeOneLabel gamma A p).prob := by
  induction A using Finset.induction_on with
  | empty =>
      simp [dnsBaseStepFactor, activeOneLabel_empty_prob]
  | @insert j A hj ih =>
      have hpA : p ∉ A := fun h => hp (Finset.mem_insert_of_mem h)
      have hjp : j ≠ p := fun h => hp (by simpa [h])
      have hpInsert : p ∉ insert j A := by simpa [hjp.symm] using hp
      have hcard : A.card + 1 <= q := by
        have hle := Finset.card_le_univ (insert p A)
        rw [Finset.card_insert_of_notMem hpA, Fintype.card_fin] at hle
        exact hle
      have hfactor : 0 <= dnsBaseStepFactor n (A.card + 1) := by
        unfold dnsBaseStepFactor
        have hN : (0 : Real) < ((2 ^ n : Nat) : Real) := by positivity
        rw [sub_nonneg, div_le_one hN]
        have hnat : 2 * (A.card + 1) <= 2 ^ n :=
          (Nat.mul_le_mul_left 2 hcard).trans hrange
        have hcast : (2 * (A.card + 1) : Real) <= (2 ^ n : Nat) := by
          exact_mod_cast hnat
        push_cast at hcast ⊢
        nlinarith
      have hstep := activeOneLabel_prob_insert_lower gamma A p j hj
      rw [Finset.card_insert_of_notMem hj, Nat.add_assoc,
        Finset.prod_range_succ]
      calc
        (∏ x ∈ Finset.range (A.card + 1), dnsBaseStepFactor n x) *
              dnsBaseStepFactor n (A.card + 1) <=
            (activeOneLabel gamma A p).prob *
              dnsBaseStepFactor n (A.card + 1) :=
          mul_le_mul_of_nonneg_right (ih hpA) hfactor
        _ <= (activeOneLabel gamma (insert j A) p).prob := by
          simpa [dnsBaseStepFactor] using hstep

theorem dns_base_product_le_masterProb
    {n q : Nat} (gamma : Fin q -> XorSpace n) (p : Fin q)
    (hrange : 2 * q <= 2 ^ n) :
    (∏ m ∈ Finset.range q, dnsBaseStepFactor n m) <= masterProb gamma := by
  have h := dns_base_product_le_activeOneLabel gamma
    (Finset.univ.erase p) p (Finset.notMem_erase p Finset.univ) hrange
  have hcard : (Finset.univ.erase p).card + 1 = q := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    have hq : 0 < q := Nat.pos_of_ne_zero (fun h => by simpa [h] using p.isLt)
    omega
  rw [hcard, activeOneLabel_full_prob_eq_compatibleLabel,
    compatibleLabel_prob_eq_masterProb] at h
  exact h

theorem dnsMainStepFactor_nonneg
    {n m : Nat} (hrange : 17 * (m + 1) <= 2 ^ n) :
    0 <= dnsMainStepFactor n m := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let t : Real := (8 / 15 : Real) ^ (2 * n)
  have hN : 0 < N := by dsimp [N]; positivity
  have hrangeR : 17 * ((m : Real) + 1) <= N := by
    dsimp [N]
    exact_mod_cast hrange
  have ht : t <= 1 / N := by
    dsimp [t, N]
    exact recursive_terminal_le n
  have ht0 : 0 <= t := by dsimp [t]; positivity
  have hNt : N * t <= 1 := by
    calc
      N * t <= N * (1 / N) := mul_le_mul_of_nonneg_left ht hN.le
      _ = 1 := by field_simp [hN.ne']
  have hcoef : 2 * N * t + 9 <= 11 := by nlinarith
  have hm0 : (0 : Real) <= m := by positivity
  have hgap : 16 * (m : Real) + 17 <= N - m := by nlinarith
  have hsquare : 11 * (m : Real) <= (N - m) ^ 2 := by
    nlinarith [sq_nonneg (N - m)]
  have hmul : (m : Real) * (2 * N * t + 9) <= 11 * m :=
    by simpa [mul_comm] using mul_le_mul_of_nonneg_left hcoef hm0
  have hnum : 0 <= (N - m) ^ 2 - (m : Real) * (2 * N * t + 9) := by
    linarith
  have hid : dnsMainStepFactor n m =
      ((N - m) ^ 2 - (m : Real) * (2 * N * t + 9)) / N ^ 2 := by
    unfold dnsMainStepFactor
    dsimp [N, t]
    field_simp [hN.ne']
  rw [hid]
  exact div_nonneg hnum (sq_nonneg N)

theorem dnsStepLoss_le_one
    {n m : Nat} (hrange : 17 * (m + 1) <= 2 ^ n) :
    dnsStepLoss n m <= 1 := by
  have hmN : m < 2 ^ n := by omega
  have hmNR : (m : Real) < ((2 ^ n : Nat) : Real) := by exact_mod_cast hmN
  have hden : 0 < (((2 ^ n : Nat) : Real) - (m : Real)) := by linarith
  by_cases hbase : m < 2 * n
  · simp only [dnsStepLoss, if_pos hbase]
    unfold dnsBaseStepLoss
    rw [div_le_one (sq_pos_of_pos hden)]
    have h2Nat : 2 * m <= 2 ^ n := by omega
    have h2R : 2 * (m : Real) <= ((2 ^ n : Nat) : Real) := by
      exact_mod_cast h2Nat
    have hmle : (m : Real) <= ((2 ^ n : Nat) : Real) - m := by linarith
    nlinarith
  · simp only [dnsStepLoss, if_neg hbase]
    have hfactor := dnsMainStepFactor_nonneg hrange
    rw [dnsMainStepFactor_eq hmN] at hfactor
    have hbasePos : 0 <
        (1 - (m : Real) / (((2 ^ n : Nat) : Real))) ^ 2 := by
      have hN : (0 : Real) < ((2 ^ n : Nat) : Real) := by positivity
      have : 0 < 1 - (m : Real) / (((2 ^ n : Nat) : Real)) := by
        rw [sub_pos, div_lt_one hN]
        exact hmNR
      positivity
    have := nonneg_of_mul_nonneg_right hfactor hbasePos
    linarith

/-- Strongest pointwise DNS statement proved in this file: the literal
finite product of all formalized insertion/deletion factors. -/
theorem dnsExactProduct_le_masterProb
    {n q : Nat} (gamma : Fin q -> XorSpace n)
    (hn : 7 <= n) (hrange : 17 * q <= 2 ^ n) :
    dnsExactProduct n q <= masterProb gamma := by
  induction q with
  | zero =>
      have hinj (a : Fin 0 -> XorSpace n) : Function.Injective a := by
        intro i
        exact Fin.elim0 i
      have hshift (a : Fin 0 -> XorSpace n) :
          Function.Injective (fun i => a i + gamma i) := by
        intro i
        exact Fin.elim0 i
      simp [dnsExactProduct, masterProb, RandomSystems.SoP.compatible_count,
        hinj, hshift]
  | succ m ih =>
      by_cases hbase : m < 2 * n
      · let p : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
        have hrangeBase : 2 * (m + 1) <= 2 ^ n := by
          have : 2 * (m + 1) <= 17 * (m + 1) := by omega
          exact this.trans hrange
        have hprod : dnsExactProduct n (m + 1) =
            ∏ k ∈ Finset.range (m + 1), dnsBaseStepFactor n k := by
          unfold dnsExactProduct
          apply Finset.prod_congr rfl
          intro k hk
          rw [dnsStepFactor, if_pos]
          have hk' := Finset.mem_range.mp hk
          omega
        rw [hprod]
        exact dns_base_product_le_masterProb gamma p hrangeBase
      · have hmMain : 2 * n <= m := Nat.le_of_not_gt hbase
        have hm : 0 < m := by omega
        obtain ⟨p, hpmax⟩ := maxMultiplicity_attained gamma (Nat.succ_pos m)
        let smaller := dropCoordinate gamma p
        have hrangeSmaller : 17 * m <= 2 ^ n := by omega
        have hih : dnsExactProduct n m <= masterProb smaller :=
          ih smaller hrangeSmaller
        have hfactor : 0 <= dnsMainStepFactor n m :=
          dnsMainStepFactor_nonneg hrange
        have hmul := mul_le_mul_of_nonneg_right hih hfactor
        have hstep : masterProb smaller * dnsMainStepFactor n m <=
            masterProb gamma := by
          simpa [smaller, dnsMainStepFactor] using
            masterProb_addCoordinate_main_lower_exact gamma p hm hpmax hrangeSmaller
        have hprod : dnsExactProduct n (m + 1) =
            dnsExactProduct n m * dnsMainStepFactor n m := by
          unfold dnsExactProduct
          rw [Finset.prod_range_succ]
          simp [dnsStepFactor, hbase]
        rw [hprod]
        exact hmul.trans hstep

theorem dnsExactLossProduct_lower
    {n q : Nat} (hrange : 17 * q <= 2 ^ n) :
    1 - dnsExactError n q <= dnsExactLossProduct n q := by
  have hweier := RandomSystems.CR18.Counting.chain_product_lower_bound
    (q := q) (dnsStepLoss n)
    (fun m _hm => dnsStepLoss_nonneg n m)
    (fun m hm => dnsStepLoss_le_one (by
      have : 17 * (m + 1) <= 17 * q := Nat.mul_le_mul_left 17 hm
      exact this.trans hrange))
  simpa [dnsExactError, dnsExactLossProduct] using hweier

/-- Additive form of the exact product theorem.  Its error is still the
literal DNS step-loss sum; no polynomial-envelope constants have been used. -/
theorem dnsFallingBaseline_mul_one_sub_error_le_masterProb
    {n q : Nat} (gamma : Fin q -> XorSpace n)
    (hn : 7 <= n) (hrange : 17 * q <= 2 ^ n) :
    dnsFallingBaseline n q * (1 - dnsExactError n q) <= masterProb gamma := by
  have hqN : q <= 2 ^ n := by omega
  have hprod := dnsExactProduct_le_masterProb gamma hn hrange
  have hnorm := dnsExactProduct_eq_normalized hqN
  have hloss := dnsExactLossProduct_lower hrange
  have hbaseline : 0 <= dnsFallingBaseline n q := by
    unfold dnsFallingBaseline
    positivity
  calc
    dnsFallingBaseline n q * (1 - dnsExactError n q) <=
        dnsFallingBaseline n q * dnsExactLossProduct n q :=
      mul_le_mul_of_nonneg_left hloss hbaseline
    _ = dnsExactProduct n q := hnorm.symm
    _ <= masterProb gamma := hprod

/-- The constrained, axiom-free DNS compatible-fiber theorem on the
published XOR carrier.  This is Lemma 8 with the stronger exact formal error
`dnsExactError`, before any replacement by a quadratic/cubic envelope. -/
theorem dns_exact_counting_bound
    {n q : Nat} (gamma : Fin q -> XorSpace n)
    (hn : 7 <= n) (hrange : 17 * q <= 2 ^ n) :
    (1 - dnsExactError n q) *
        ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) <=
      (RandomSystems.SoP.compatible_count (XorSpace n) gamma : Real) *
        (((2 ^ n) ^ q : Nat) : Real) := by
  have h := dnsFallingBaseline_mul_one_sub_error_le_masterProb gamma hn hrange
  have hNq : (0 : Real) < (((2 ^ n) ^ q : Nat) : Real) := by positivity
  unfold dnsFallingBaseline masterProb at h
  rw [card_xorSpace] at h
  push_cast at h ⊢
  field_simp [hNq.ne'] at h
  nlinarith

/-! ### A closed envelope

The exact finite sum above is the primary bound.  For a compact corollary we
also bound it by a polynomial.  Even with deliberately simple denominator
arithmetic, the constants obtained from the formal recursion are `10` and
`5`, already stronger than DNS's published `19` and `8`. -/

theorem div_square_le_sixteen_ninth
    (N k a : Real) (hN : 0 < N) (hk0 : 0 <= k)
    (hk : 4 * k <= N) (ha : 0 <= a) :
    a / (N - k) ^ 2 <= (16 / 9 : Real) * a / N ^ 2 := by
  have hden : 0 < N - k := by nlinarith
  have hlin : 3 * N <= 4 * (N - k) := by nlinarith
  have hsquare : 9 * N ^ 2 <= 16 * (N - k) ^ 2 := by
    nlinarith [sq_nonneg N, sq_nonneg (N - k)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare ha
  field_simp [hN.ne', hden.ne']
  nlinarith

theorem dnsStepLoss_le_envelope
    {n q k : Nat} (hkq : k < q) (hrange : 17 * q <= 2 ^ n) :
    dnsStepLoss n k <=
      (176 / 9 : Real) * (k : Real) / (((2 ^ n : Nat) : Real) ^ 2) +
        if k < 2 * n then
          (16 / 9 : Real) * (k : Real) ^ 2 /
            (((2 ^ n : Nat) : Real) ^ 2)
        else 0 := by
  let N : Real := ((2 ^ n : Nat) : Real)
  have hN : 0 < N := by dsimp [N]; positivity
  have hk4Nat : 4 * k <= 2 ^ n := by
    have : 4 * k < 17 * q := by omega
    omega
  have hk4 : 4 * (k : Real) <= N := by
    dsimp [N]
    exact_mod_cast hk4Nat
  have hk0 : (0 : Real) <= k := by positivity
  have hbaseDen := div_square_le_sixteen_ninth N (k : Real)
    ((k : Real) ^ 2) hN hk0 hk4 (sq_nonneg _)
  have hlinearDen := div_square_le_sixteen_ninth N (k : Real)
    (k : Real) hN hk0 hk4 hk0
  by_cases hbase : k < 2 * n
  · rw [dnsStepLoss, if_pos hbase, if_pos hbase]
    unfold dnsBaseStepLoss
    dsimp [N] at hbaseDen ⊢
    exact hbaseDen.trans (le_add_of_nonneg_left (by positivity))
  · rw [dnsStepLoss, if_neg hbase, if_neg hbase, add_zero]
    unfold dnsMainStepLoss
    have ht := recursive_terminal_le n
    have hNt : N * (8 / 15 : Real) ^ (2 * n) <= 1 := by
      calc
        N * (8 / 15 : Real) ^ (2 * n) <= N * (1 / N) := by
          exact mul_le_mul_of_nonneg_left (by simpa [N] using ht) hN.le
        _ = 1 := by field_simp [hN.ne']
    have hcoef :
        9 + 2 * N * (8 / 15 : Real) ^ (2 * n) <= 11 := by nlinarith
    have hmul :
        (k : Real) * (9 + 2 * N * (8 / 15 : Real) ^ (2 * n)) <=
          11 * (k : Real) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcoef hk0
    have hdenPos : 0 < (N - (k : Real)) ^ 2 := by
      have : (k : Real) < N := by nlinarith
      exact sq_pos_of_pos (sub_pos.mpr this)
    calc
      (k : Real) *
            (9 + 2 * N * (8 / 15 : Real) ^ (2 * n)) /
          (N - (k : Real)) ^ 2 <=
        (11 * (k : Real)) / (N - (k : Real)) ^ 2 :=
          div_le_div_of_nonneg_right hmul hdenPos.le
      _ <= 11 * ((16 / 9 : Real) * (k : Real) / N ^ 2) := by
        calc
          (11 * (k : Real)) / (N - (k : Real)) ^ 2 =
              11 * ((k : Real) / (N - (k : Real)) ^ 2) := by ring
          _ <= 11 * ((16 / 9 : Real) * (k : Real) / N ^ 2) := by
            gcongr
      _ = (176 / 9 : Real) * (k : Real) / N ^ 2 := by ring

theorem dnsExactError_le_closed
    {n q : Nat} (hrange : 17 * q <= 2 ^ n) :
    dnsExactError n q <=
      (10 * (q : Real) ^ 2 + 5 * (n : Real) ^ 3) /
        (((2 ^ n : Nat) : Real) ^ 2) := by
  let N : Real := ((2 ^ n : Nat) : Real)
  have hN : 0 < N := by dsimp [N]; positivity
  have hsum : dnsExactError n q <=
      ∑ k ∈ Finset.range q,
        ((176 / 9 : Real) * (k : Real) / N ^ 2 +
          if k < 2 * n then
            (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2
          else 0) := by
    unfold dnsExactError
    apply Finset.sum_le_sum
    intro k hk
    simpa [N] using dnsStepLoss_le_envelope
      (Finset.mem_range.mp hk) hrange
  have hsumId :
      (∑ k ∈ Finset.range q, (k : Real)) =
        (q : Real) * ((q : Real) - 1) / 2 := by
    simpa using RandomSystems.CR18.Counting.sum_div_range 1 q (by norm_num)
  have hsumIdLe :
      (∑ k ∈ Finset.range q, (k : Real)) <= (q : Real) ^ 2 / 2 := by
    rw [hsumId]
    have hq0 : (0 : Real) <= q := by positivity
    nlinarith
  have hmain :
      (∑ k ∈ Finset.range q,
        (176 / 9 : Real) * (k : Real) / N ^ 2) <=
          10 * (q : Real) ^ 2 / N ^ 2 := by
    have hcoef : 0 <= (176 / 9 : Real) / N ^ 2 := by positivity
    calc
      (∑ k ∈ Finset.range q,
          (176 / 9 : Real) * (k : Real) / N ^ 2) =
          ((176 / 9 : Real) / N ^ 2) *
            ∑ k ∈ Finset.range q, (k : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ <= ((176 / 9 : Real) / N ^ 2) * ((q : Real) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hsumIdLe hcoef
      _ <= 10 * (q : Real) ^ 2 / N ^ 2 := by
        field_simp [hN.ne']
        nlinarith [sq_nonneg (q : Real)]
  let s : Finset Nat :=
    (Finset.range q).filter (fun k => k < 2 * n)
  have hbaseFilter :
      (∑ k ∈ Finset.range q,
        if k < 2 * n then
          (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2
        else 0) =
      ∑ k ∈ s, (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2 := by
    rw [Finset.sum_filter]
  have hsSubset : s ⊆ Finset.range (2 * n) := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  have hbaseSubset :
      (∑ k ∈ s, (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2) <=
        ∑ k ∈ Finset.range (2 * n),
          (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsSubset
      (fun _k _hk _hnot => by positivity)
  have hsq := RandomSystems.CR18.Counting.three_sum_sq_le_cube (2 * n)
  have hsq' :
      (∑ k ∈ Finset.range (2 * n), (k : Real) ^ 2) <=
        ((2 * n : Nat) : Real) ^ 3 / 3 := by
    nlinarith
  have hbaseRange :
      (∑ k ∈ Finset.range (2 * n),
        (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2) <=
          5 * (n : Real) ^ 3 / N ^ 2 := by
    have hcoef : 0 <= (16 / 9 : Real) / N ^ 2 := by positivity
    calc
      (∑ k ∈ Finset.range (2 * n),
          (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2) =
          ((16 / 9 : Real) / N ^ 2) *
            ∑ k ∈ Finset.range (2 * n), (k : Real) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ <= ((16 / 9 : Real) / N ^ 2) *
          (((2 * n : Nat) : Real) ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hsq' hcoef
      _ <= 5 * (n : Real) ^ 3 / N ^ 2 := by
        push_cast
        field_simp [hN.ne']
        have hn3 : 0 <= (n : Real) ^ 3 := pow_nonneg (by positivity) 3
        nlinarith
  have hbase :
      (∑ k ∈ Finset.range q,
        if k < 2 * n then
          (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2
        else 0) <= 5 * (n : Real) ^ 3 / N ^ 2 := by
    rw [hbaseFilter]
    exact hbaseSubset.trans hbaseRange
  rw [Finset.sum_add_distrib] at hsum
  calc
    dnsExactError n q <=
        (∑ k ∈ Finset.range q,
          (176 / 9 : Real) * (k : Real) / N ^ 2) +
        ∑ k ∈ Finset.range q,
          if k < 2 * n then
            (16 / 9 : Real) * (k : Real) ^ 2 / N ^ 2
          else 0 := hsum
    _ <= 10 * (q : Real) ^ 2 / N ^ 2 +
        5 * (n : Real) ^ 3 / N ^ 2 := add_le_add hmain hbase
    _ = (10 * (q : Real) ^ 2 + 5 * (n : Real) ^ 3) /
        (((2 ^ n : Nat) : Real) ^ 2) := by dsimp [N]; ring

/-- Closed-form corollary of the exact fiber theorem.  The constants `10,5`
come from the formal proof above and improve DNS's published `19,8`. -/
theorem dns_closed_counting_bound
    {n q : Nat} (gamma : Fin q -> XorSpace n)
    (hn : 7 <= n) (hrange : 17 * q <= 2 ^ n) :
    (1 - (10 * (q : Real) ^ 2 + 5 * (n : Real) ^ 3) /
          (((2 ^ n : Nat) : Real) ^ 2)) *
        ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) <=
      (RandomSystems.SoP.compatible_count (XorSpace n) gamma : Real) *
        (((2 ^ n) ^ q : Nat) : Real) := by
  have hexact := dns_exact_counting_bound gamma hn hrange
  have herr := dnsExactError_le_closed hrange
  have hdesc : 0 <=
      ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) := by
    positivity
  calc
    (1 - (10 * (q : Real) ^ 2 + 5 * (n : Real) ^ 3) /
            (((2 ^ n : Nat) : Real) ^ 2)) *
          ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) <=
        (1 - dnsExactError n q) *
          ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) := by
      gcongr
    _ <= (RandomSystems.SoP.compatible_count (XorSpace n) gamma : Real) *
        (((2 ^ n) ^ q : Nat) : Real) := hexact

/-- Literal published Lemma 8, retained as a compatibility corollary.  The
proof does not use these looser constants internally. -/
theorem dns_published_counting_bound
    {n q : Nat} (gamma : Fin q -> XorSpace n)
    (hn : 7 <= n) (hrange : 17 * q <= 2 ^ n) :
    (1 - (19 * (q : Real) ^ 2 + 8 * (n : Real) ^ 3) /
          (((2 ^ n : Nat) : Real) ^ 2)) *
        ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) <=
      (RandomSystems.SoP.compatible_count (XorSpace n) gamma : Real) *
        (((2 ^ n) ^ q : Nat) : Real) := by
  have hclosed := dns_closed_counting_bound gamma hn hrange
  have hN2 : 0 < (((2 ^ n : Nat) : Real) ^ 2) := by positivity
  have hdesc : 0 <=
      ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) := by
    positivity
  have herr :
      (10 * (q : Real) ^ 2 + 5 * (n : Real) ^ 3) /
          (((2 ^ n : Nat) : Real) ^ 2) <=
        (19 * (q : Real) ^ 2 + 8 * (n : Real) ^ 3) /
          (((2 ^ n : Nat) : Real) ^ 2) := by
    apply (div_le_div_iff_of_pos_right hN2).2
    have hq2 : 0 <= (q : Real) ^ 2 := sq_nonneg _
    have hn3 : 0 <= (n : Real) ^ 3 := pow_nonneg (by positivity) 3
    nlinarith
  calc
    (1 - (19 * (q : Real) ^ 2 + 8 * (n : Real) ^ 3) /
            (((2 ^ n : Nat) : Real) ^ 2)) *
          ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) <=
        (1 - (10 * (q : Real) ^ 2 + 5 * (n : Real) ^ 3) /
            (((2 ^ n : Nat) : Real) ^ 2)) *
          ((((2 ^ n).descFactorial q * (2 ^ n).descFactorial q : Nat) : Real)) := by
      gcongr
    _ <= (RandomSystems.SoP.compatible_count (XorSpace n) gamma : Real) *
        (((2 ^ n) ^ q : Nat) : Real) := hclosed


end Labels

end RandomSystems.SoP.DNS
