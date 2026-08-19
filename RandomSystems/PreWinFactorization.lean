/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CondEquiv

/-!
# CR18 eq. (4.38) — pre-winning cumulative behavior factors as a product of pre-winning kernels

This file proves CR18 Definition 4.19 / eq. (4.38) at the **factored** level: the game-side
pre-winning *cumulative* mass `massYAfalse Ŝ` (the not-yet-won region of the cumulative behavior
`bᶜ`, CondEquiv.lean) equals the product over rounds `j ≤ i` of the pre-winning *behavior* kernels
`gamePrewinBehavior Ŝ` (Def 4.15, GameEquivalence.lean):

> `massYAfalse Ŝ i yⁱ xⁱ = ∏ⱼ (gamePrewinBehavior Ŝ j (yⱼ, (xʲ, yʲ⁻¹))).get _`.

The entire content is **reuse** of the chain-rule product lemma
`PFunPDS.cumulativeBehavior_eq_behavior_prod` (CR18 Eq. (3.2), PDS.lean), because `massYAfalse Ŝ`
is exactly `cumulativeBehavior Ŝ` evaluated at the augmented output sequence `(yⱼ, false)`. No new
probability machinery is introduced, and **no `DecidableEq`/`Fintype`** appears — augmenting the
output type with the `false` MBO bit is a pure `Vector.map`, and the chain rule is invoked verbatim.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open PFunPDS (inputPrefix outputPrefix behavior cumulativeBehavior)

universe u v

variable {X : Type u} {Y : Type v}

/-- **Step B (helper).** `outputPrefix` commutes with `Vector.map`: the length-`j` prefix of a
mapped sequence is the mapped prefix. Pure reindexing of `Vector.ofFn`. -/
theorem outputPrefix_map {n : ℕ} {α β : Type*} (f : α → β) (ys : Vector α n) (j : Fin n) :
    PFunPDS.outputPrefix (ys.map f) j = (PFunPDS.outputPrefix ys j).map f := by
  simp only [PFunPDS.outputPrefix, Vector.map_ofFn]
  congr 1
  funext k
  simp [Vector.get_map]

/-- **CR18 eq. (4.38), factored form.** The game-side pre-winning cumulative mass factors into the
product of the pre-winning behavior kernels. Proved purely by reuse of the chain rule
`cumulativeBehavior_eq_behavior_prod` (Eq. (3.2)), since `massYAfalse Ŝ` is `cumulativeBehavior Ŝ`
read at the `(yⱼ, false)`-augmented output sequence. No `DecidableEq`, no `Fintype`. -/
theorem massYAfalse_eq_prewin_prod (Shat : PFunPDS X (Y × Bool))
    (hS : Shat.isProbDist) {i : ℕ}
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1))
    (hdef : ∀ j : Fin (i + 1),
      (gamePrewinBehavior Shat j.1
        (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).Dom) :
    CondEquiv.massYAfalse Shat i ys xs =
      ∏ j : Fin (i + 1),
        (gamePrewinBehavior Shat j.1
          (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).get (hdef j) := by
  classical
  -- The `(yⱼ, false)`-augmented output sequence.
  set f : Y → Y × Bool := fun y => (y, false) with hf
  set Ys : Vector (Y × Bool) (i + 1) := ys.map f with hYs
  -- `Ys.toList.get k = (ys.toList.get k, false)`; align the two `Fin` index types.
  have hYstoList : Ys.toList = ys.toList.map f := by
    simp [hYs, Vector.toList_map]
  -- **Step C.** Each augmented behavior factor equals the corresponding pre-winning factor.
  have hStepC : ∀ j : Fin (i + 1),
      behavior Shat j.1 (Ys.get j, (inputPrefix xs j, outputPrefix Ys j))
        = gamePrewinBehavior Shat j.1
            (ys.get j, (inputPrefix xs j, outputPrefix ys j)) := by
    intro j
    have hget : Ys.get j = (ys.get j, false) := by
      simp [hYs, Vector.get_eq_getElem, Vector.getElem_map, hf]
    have hpref : outputPrefix Ys j = (outputPrefix ys j).map f := by
      rw [hYs, outputPrefix_map]
    rw [hget, hpref]
    -- unfold the game-side pre-winning behavior to a `behavior Shat` application
    show behavior Shat j.1 ((ys.get j, false), (inputPrefix xs j, (outputPrefix ys j).map f))
        = gamePrewinBehavior Shat j.1
            (ys.get j, (inputPrefix xs j, outputPrefix ys j))
    rfl
  -- definedness on the augmented side, transported from `hdef` via Step C.
  have hdef' : ∀ j : Fin (i + 1),
      (behavior Shat j.1 (Ys.get j, (inputPrefix xs j, outputPrefix Ys j))).Dom := by
    intro j
    rw [hStepC j]; exact hdef j
  -- **Step A.** `massYAfalse Ŝ i ys xs = cumulativeBehavior Ŝ i (Ys, xs)`.
  have hStepA : CondEquiv.massYAfalse Shat i ys xs
      = cumulativeBehavior Shat i (Ys, xs) := by
    unfold CondEquiv.massYAfalse cumulativeBehavior
    simp only
    apply Dist.mass_congr
    intro s
    -- Predicate equivalence per realization, indices aligned via `length_map`.
    have hlen : Ys.toList.length = ys.toList.length := by
      rw [hYstoList, List.length_map]
    constructor
    · intro h k
      -- `k : Fin Ys.toList.length`; transport to `Fin ys.toList.length`.
      have hk : k.1 < ys.toList.length := by rw [← hlen]; exact k.2
      obtain ⟨hd, hy, hb⟩ := h ⟨k.1, hk⟩
      refine ⟨hd, ?_⟩
      have hget : Ys.toList.get k = (ys.toList.get ⟨k.1, hk⟩, false) := by
        simp only [List.get_eq_getElem, hYstoList, List.getElem_map, hf]
      rw [hget, Prod.ext_iff]
      exact ⟨hy, hb⟩
    · intro h k
      have hk : k.1 < Ys.toList.length := by rw [hlen]; exact k.2
      obtain ⟨hd, heq⟩ := h ⟨k.1, hk⟩
      have hget : Ys.toList.get ⟨k.1, hk⟩ = (ys.toList.get k, false) := by
        simp only [List.get_eq_getElem, hYstoList, List.getElem_map, hf]
      rw [hget] at heq
      refine ⟨hd, ?_, ?_⟩
      · rw [heq]
      · rw [heq]
  -- **Step D.** Assemble: rewrite via Step A, apply the chain rule, factor term-by-term.
  rw [hStepA, PFunPDS.cumulativeBehavior_eq_behavior_prod Shat hS Ys xs hdef']
  apply Finset.prod_congr rfl
  intro j _
  -- equal `Part`s ⇒ equal `.get`s (Dom proof-irrelevant).
  simp only [hStepC j]

/-- **CR18 Lemma 4.16 cancellation step.** Game-equivalent games (`G ≡ᵍ H`, i.e. equal pre-winning
behavior, Def 4.16) induce equal pre-winning *cumulative* mass. Immediate from the factorization
`massYAfalse_eq_prewin_prod`: both sides are the product of pre-winning behavior kernels, and `≡ᵍ`
is exactly equality of those kernels. No `DecidableEq`, no `Fintype`. -/
theorem massYAfalse_congr_gameEquiv_of_dom {G H : PFunPDS X (Y × Bool)}
    (hG : G.isProbDist) (hH : H.isProbDist) (hGH : G ≡ᵍ H)
    {i : ℕ} (ys : Vector Y (i + 1)) (xs : Vector X (i + 1))
    (hdef : ∀ j : Fin (i + 1),
      (gamePrewinBehavior G j.1
        (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).Dom) :
    CondEquiv.massYAfalse G i ys xs = CondEquiv.massYAfalse H i ys xs := by
  -- `≡ᵍ` is `GameEquiv`, defeq to equality of pre-winning behavior.
  have hGH' : gamePrewinBehavior G = gamePrewinBehavior H := hGH
  -- Transport the definedness hypothesis to `H` along `hGH'`.
  have hdefH : ∀ j : Fin (i + 1),
      (gamePrewinBehavior H j.1
        (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).Dom := by
    intro j; rw [← hGH']; exact hdef j
  rw [massYAfalse_eq_prewin_prod G hG ys xs hdef,
      massYAfalse_eq_prewin_prod H hH ys xs hdefH]
  apply Finset.prod_congr rfl
  intro j _
  simp only [hGH']

/-- **CR18 footnote 16/29 — the degenerate case.** If the pre-winning behavior is *undefined* at some
round `j` (the conditioning prefix has probability 0), the pre-winning *cumulative* mass is `0`: the
full not-won event implies the prefix not-won event, whose mass is `0`. This is what lets game
equivalence be unconditional (footnote 29: conditionals are partial, equal "where both defined"). -/
theorem massYAfalse_eq_zero_of_undef {G : PFunPDS X (Y × Bool)}
    (hGnn : G.NonNeg) {i : ℕ}
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) (j : Fin (i + 1))
    (hundef : ¬ (gamePrewinBehavior G j.1
      (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).Dom) :
    CondEquiv.massYAfalse G i ys xs = 0 := by
  classical
  simp only [gamePrewinBehavior, prewinBehavior, PFunPDS.behavior, Dist.cond] at hundef
  rw [not_not] at hundef
  refine le_antisymm ?_ (hGnn.mass_nonneg _)
  rw [← hundef]
  unfold CondEquiv.massYAfalse
  rw [Dist.mass, Dist.mass]
  apply Finsupp.sum_le_sum
  intro s _
  by_cases hM : (∀ (k : Fin ys.toList.length),
      ∃ h : List.take (k.1 + 1) xs.toList ∈ PFunDDS.dom s,
        (PFunDDS.output s (List.take (k.1 + 1) xs.toList) h).1 = ys.toList.get k ∧
        (PFunDDS.output s (List.take (k.1 + 1) xs.toList) h).2 = false)
  · -- The not-won full event implies the prefix conditioning event.
    rw [if_pos hM, if_pos ?_]
    intro k
    have hkj : k.1 < j.1 := by
      have hk2 := k.2
      simpa [Vector.toList_map, List.length_map, Vector.length_toList] using hk2
    have hki : k.1 < ys.toList.length := by
      have hl : ys.toList.length = i + 1 := by simp
      have := j.2
      omega
    obtain ⟨h, h1, h2⟩ := hM ⟨k.1, hki⟩
    have hin : List.take (k.1 + 1) (PFunPDS.inputPrefix xs j).toList
        = List.take (k.1 + 1) xs.toList := by
      rw [PFunPDS.inputPrefix_toList, List.take_take]; congr 1; omega
    have hout : (Vector.map (fun y => (y, false)) (PFunPDS.outputPrefix ys j)).toList.get k
        = (ys.toList.get ⟨k.1, hki⟩, false) := by
      simp only [List.get_eq_getElem, Vector.toList_map, List.getElem_map,
        PFunPDS.outputPrefix_toList, List.getElem_take]
    refine ⟨by rw [hin]; exact h, ?_⟩
    have hcong : PFunDDS.output s (List.take (k.1 + 1) (PFunPDS.inputPrefix xs j).toList)
        (by rw [hin]; exact h)
        = PFunDDS.output s (List.take (k.1 + 1) xs.toList) h :=
      PFunDDS.output_congr s hin _ _
    exact hcong.trans ((Prod.ext_iff.mpr ⟨h1, h2⟩).trans hout.symm)
  · rw [if_neg hM]
    split
    · exact hGnn s
    · exact le_rfl

/-- **CR18 Lemma 4.16 cancellation (unconditional, footnote-29 faithful).** Game-equivalent games
induce equal pre-winning cumulative mass — `P^{WG}(A_q=0)`-style — with **no** definedness/totality
hypothesis. Where the pre-winning conditionals are defined, this is `massYAfalse_congr_gameEquiv_of_dom`;
where one is undefined (prob-0 conditioning), both cumulative masses are `0` (`massYAfalse_eq_zero_of_undef`),
and `≡ᵍ` makes the undefined-points coincide. This is exactly Maurer's partial-conditional treatment. -/
theorem massYAfalse_congr_gameEquiv {G H : PFunPDS X (Y × Bool)}
    (hG : G.isProbDist) (hH : H.isProbDist) (hGH : G ≡ᵍ H)
    {i : ℕ} (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    CondEquiv.massYAfalse G i ys xs = CondEquiv.massYAfalse H i ys xs := by
  have hGH' : gamePrewinBehavior G = gamePrewinBehavior H := hGH
  by_cases hdef : ∀ j : Fin (i + 1),
      (gamePrewinBehavior G j.1
        (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).Dom
  · exact massYAfalse_congr_gameEquiv_of_dom hG hH hGH ys xs hdef
  · push_neg at hdef
    obtain ⟨j, hj⟩ := hdef
    have hjH : ¬ (gamePrewinBehavior H j.1
        (ys.get j, (PFunPDS.inputPrefix xs j, PFunPDS.outputPrefix ys j))).Dom := by
      rw [← hGH']; exact hj
    rw [massYAfalse_eq_zero_of_undef hG.nonNeg ys xs j hj,
      massYAfalse_eq_zero_of_undef hH.nonNeg ys xs j hjH]

end RandomSystems.CR18
