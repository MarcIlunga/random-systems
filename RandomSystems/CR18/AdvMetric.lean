/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.CR18.Indist

/-!
# CR18: metric properties of the distinction advantage (symmetry, triangle)

The shared sup-over-distinguishers advantage `AdvWith` relative to a CR18
§4.5.2 distinction structure (`Def47.DistinctionStructure`: objects `O`,
deterministic distinguishers `D`, decision function `κ : D → O → Bool`), with
systems embedded into object distributions through an arbitrary map `iota`,
plus two generic "metric" facts about it:

* `advWith_symm` (GAP-5, §3.3 of the HCTR2 sketch): **Δ-symmetry**.  The
  per-distinguisher `performance` is SIGNED, so `AdvWith S T = AdvWith T S` is
  NOT free: it needs the distinguisher class to be closed under pointwise
  complementation of the decision bit (`ComplementClosed`) AND equal object
  masses (for SUB-distributions, complementing `κ` gives
  `perf(S,T,d') = perf(T,S,d) + w_D·(w_T − w_S)`; the equal-mass hypothesis is
  always dischargeable for weight-1 systems).

* `advWith_triangle` (GAP-6, §3.2 of the HCTR2 sketch): **triangle
  inequality** for `AdvWith`, by pointwise additivity of the signed
  `performance` plus `csSup` subadditivity over the weight-1 distinguisher
  class (each image is bounded above by the mass of the right-hand system; the
  empty-class case degenerates to `Real.sSup_empty`).

## Dedupe (DONE at integration, 2026-06-11)

The module was drafted against local mirrors (`AdvMetric.DStruct` etc.); at
integration the mirrors were DELETED and everything is stated against the
library's `Def47.DistinctionStructure` (`RandomSystems/CR18/Game.lean`),
whose `ProbDistinguisher`/`performance` are definitionally what the proofs
unfold by `rfl`.  `AdvWith` (generic in the system carrier `σ`) is THE shared
advantage notion — `RandomSystems/CR18/Monotonicity.lean` consumes it for the
converter-monotonicity theorem.

**Connecting lemmas to the keystone** (`RandomSystems/CR18/Indist.lean`):

* `advWith_eq_keystone` — at the concrete CR18 §4.10.2 structure
  (`Lem416.distinctionStructure`, `iota = id`), `AdvWith` IS the `sSup` over
  `isProbDist` distinguishers appearing in `Thm417.delta_le_gamma` /
  `Thm417.fundamental` (the weight-1 classes coincide, by
  `Dist.weight_eq_finsupp_sum`).
* `advWith_le_gamma` — CR18 Theorem 4.17 re-expressed through `AdvWith`:
  `AdvWith (Lem416.distinctionStructure X Y q) id Shat⁻ T ≤ Γ(Shat)`.
-/

-- PORTED from hctr2-verification HCTR2/Proofs/CR18/Sketch.lean:4390-4566 — UPSTREAM-CANDIDATE landed 2026-06-11

noncomputable section

open scoped NNReal

namespace RandomSystems.CR18

open Def47

/-! ### The shared advantage notion -/

/-- THE advantage relative to a distinction structure (HCTR2 sketch §1.3): the
sup of the SIGNED `Def47.DistinctionStructure.performance` over the weight-1
(probability) distinguisher class, with systems embedded into object
distributions through `iota`.  Generic in the system carrier `σ` (instantiate
`σ := PDS X Y`, `iota := id` for the concrete CR18 §4.10.2 structure — see
`advWith_eq_keystone`).  NOTE `performance` is SIGNED; symmetry is NOT free —
see `advWith_symm`. -/
def AdvWith {σ : Type*} (ds : DistinctionStructure)
    (iota : σ → Dist ds.O) (S T : σ) : ℝ :=
  sSup ((fun D => ds.performance (iota S, iota T) D) ''
    {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1})

/-- The deterministic distinguisher class is closed under POINTWISE
complementation of the decision bit — what makes the SIGNED `performance` sup
symmetric (HCTR2 sketch's `ComplementClosed`). -/
def Def47.DistinctionStructure.ComplementClosed (ds : DistinctionStructure) : Prop :=
  ∀ d : ds.D, ∃ d' : ds.D, ∀ o : ds.O, ds.κ d' o = !(ds.κ d o)

/-! ### The two ported theorems (GAP-5, GAP-6) -/

/-- GAP-5 (HCTR2 sketch §3.3)  Δ-SYMMETRY: `performance` is SIGNED, so
`AdvWith S T = AdvWith T S` needs complement-closure AND equal object masses
(R4 repair, found attempting the proof: for SUB-distributions, complementing κ
gives `perf(S,T,d') = perf(T,S,d) + w_D·(w_T − w_S)`; always dischargeable for
weight-1 systems). -/
theorem advWith_symm {σ : Type*} (ds : DistinctionStructure)
    (iota : σ → Dist ds.O) (hcc : ds.ComplementClosed) (S T : σ)
    (hw : ((iota S).sum fun _ w => w) = ((iota T).sum fun _ w => w)) :
    AdvWith ds iota S T = AdvWith ds iota T S := by
  classical
  -- extract the complement map d ↦ d' with κ d' = !κ d (pointwise)
  have hcc' : ∀ d : ds.D, ∃ d' : ds.D, ∀ o : ds.O, ds.κ d' o = !(ds.κ d o) := hcc
  choose cmpl hcmpl using hcc'
  -- `performance` unfolded as a difference of correlation double-sums (definitional).
  have hperf : ∀ (V₀ V₁ : Dist ds.O) (E : ds.ProbDistinguisher),
      ds.performance (V₀, V₁) E
        = (E.sum fun d dw => V₁.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)
          - (E.sum fun d dw => V₀.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0) := fun _ _ _ => rfl
  -- one-sided image inclusion, generic in the ordered pair (uses equal masses):
  -- every perf(B,A) value of a weight-1 D is the perf(A,B) value of the
  -- complement-pushforward of D, still weight-1.
  have key : ∀ A B : σ, ((iota A).sum fun _ w => w) = ((iota B).sum fun _ w => w) →
      ((fun D => ds.performance (iota B, iota A) D) ''
          {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1})
        ⊆ ((fun D => ds.performance (iota A, iota B) D) ''
          {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1}) := by
    intro A B hAB x hx
    obtain ⟨D, hD, rfl⟩ := hx
    -- D's weight coerced to ℝ
    have hD1 : (D.sum fun _ w => (w : ℝ)) = 1 := by
      have h1 : ((D.sum fun _ w => w : NNReal) : ℝ) = 1 := by rw [hD]; norm_num
      simpa [Finsupp.sum, NNReal.coe_sum] using h1
    -- equal masses coerced to ℝ
    have hwR : ((iota A).sum fun _ w => (w : ℝ)) = ((iota B).sum fun _ w => (w : ℝ)) := by
      have h1 : (((iota A).sum fun _ w => w : NNReal) : ℝ)
          = (((iota B).sum fun _ w => w : NNReal) : ℝ) := by rw [hAB]
      simpa [Finsupp.sum, NNReal.coe_sum] using h1
    refine ⟨Finsupp.mapDomain cmpl D, ?_, ?_⟩
    · -- the pushforward preserves the weight
      show ((Finsupp.mapDomain cmpl D).sum fun _ w => w) = 1
      rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
      exact hD
    · -- correlation of the pushforward = mass − original correlation
      have hcorr : ∀ V : Dist ds.O,
          ((Finsupp.mapDomain cmpl D).sum fun d dw => V.sum fun o ow =>
              (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)
            = (V.sum fun _ w => (w : ℝ))
              - (D.sum fun d dw => V.sum fun o ow =>
                  (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0) := by
        intro V
        -- pull the sum back along the pushforward
        have hpush : ((Finsupp.mapDomain cmpl D).sum fun d dw => V.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)
              = D.sum fun d dw => V.sum fun o ow =>
                  (dw : ℝ) * (ow : ℝ) * if ds.κ (cmpl d) o then 1 else 0 := by
          refine Finsupp.sum_mapDomain_index (fun b => ?_) (fun b m₁ m₂ => ?_)
          · simp
          · simp only [NNReal.coe_add, add_mul]
            exact Finsupp.sum_add
        -- pointwise complementation flips the decision term
        have hflip : ∀ (d : ds.D) (dw : NNReal),
            (V.sum fun o ow => (dw : ℝ) * (ow : ℝ) * if ds.κ (cmpl d) o then 1 else 0)
              = (dw : ℝ) * (V.sum fun _ w => (w : ℝ))
                - (V.sum fun o ow => (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0) := by
          intro d dw
          rw [Finsupp.mul_sum, ← Finsupp.sum_sub]
          refine Finsupp.sum_congr fun o _ => ?_
          simp only [hcmpl]
          cases hb : ds.κ d o <;> simp
        calc ((Finsupp.mapDomain cmpl D).sum fun d dw => V.sum fun o ow =>
                (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)
            = D.sum fun d dw => V.sum fun o ow =>
                (dw : ℝ) * (ow : ℝ) * if ds.κ (cmpl d) o then 1 else 0 := hpush
          _ = D.sum fun d dw => ((dw : ℝ) * (V.sum fun _ w => (w : ℝ))
                - (V.sum fun o ow => (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)) :=
              Finsupp.sum_congr fun d _ => hflip d (D d)
          _ = (D.sum fun d dw => (dw : ℝ) * (V.sum fun _ w => (w : ℝ)))
                - (D.sum fun d dw => V.sum fun o ow =>
                    (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0) := Finsupp.sum_sub
          _ = (V.sum fun _ w => (w : ℝ))
                - (D.sum fun d dw => V.sum fun o ow =>
                    (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0) := by
              rw [← Finsupp.sum_mul, hD1, one_mul]
      show ds.performance (iota A, iota B) (Finsupp.mapDomain cmpl D)
          = ds.performance (iota B, iota A) D
      rw [hperf, hperf, hcorr (iota A), hcorr (iota B), hwR]
      ring
  -- the two weight-1 images coincide as SETS ⇒ equal suprema
  have himg : ((fun D => ds.performance (iota S, iota T) D) ''
        {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1})
      = ((fun D => ds.performance (iota T, iota S) D) ''
        {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1}) :=
    Set.Subset.antisymm (key T S hw.symm) (key S T hw)
  unfold AdvWith
  rw [himg]

/-- GAP-6 (HCTR2 sketch §3.2)  triangle inequality for `AdvWith` (pointwise
additivity of the signed `performance` + `csSup` subadditivity over the
weight-1 class; nonempty — the stop environment — and bounded — performance of
weight-1 pairs ∈ [−1,1]). -/
theorem advWith_triangle {σ : Type*} (ds : DistinctionStructure)
    (iota : σ → Dist ds.O) (S T U : σ) :
    AdvWith ds iota S U ≤ AdvWith ds iota S T + AdvWith ds iota T U := by
  classical
  -- `performance` unfolded as a difference of correlation double-sums (definitional).
  have hperf : ∀ (V₀ V₁ : Dist ds.O) (E : ds.ProbDistinguisher),
      ds.performance (V₀, V₁) E
        = (E.sum fun d dw => V₁.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)
          - (E.sum fun d dw => V₀.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0) := fun _ _ _ => rfl
  -- pointwise telescoping: perf(S,U) = perf(S,T) + perf(T,U) for EVERY distinguisher
  have hsplit : ∀ D : ds.ProbDistinguisher,
      ds.performance (iota S, iota U) D
        = ds.performance (iota S, iota T) D + ds.performance (iota T, iota U) D := by
    intro D
    simp only [hperf]
    ring
  -- uniform upper bound over the weight-1 class: perf(A,B) D ≤ |iota B|
  have hbound : ∀ (A B : σ) (D : ds.ProbDistinguisher), (D.sum fun _ w => w) = 1 →
      ds.performance (iota A, iota B) D ≤ ((iota B).sum fun _ w => (w : ℝ)) := by
    intro A B D hD
    have hD1 : (∑ d ∈ D.support, (D d : ℝ)) = 1 := by
      have h1 : ((D.sum fun _ w => w : NNReal) : ℝ) = 1 := by rw [hD]; norm_num
      simpa [Finsupp.sum, NNReal.coe_sum] using h1
    have hnnA : (0 : ℝ) ≤ D.sum fun d dw => (iota A).sum fun o ow =>
        (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0 := by
      simp only [Finsupp.sum]
      refine Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun o _ => ?_
      have hite : (0 : ℝ) ≤ if ds.κ d o then (1 : ℝ) else 0 := by split <;> norm_num
      have hnn : (0 : ℝ) ≤ (D d : ℝ) * ((iota A) o : ℝ) := by positivity
      exact mul_nonneg hnn hite
    have hub : (D.sum fun d dw => (iota B).sum fun o ow =>
        (dw : ℝ) * (ow : ℝ) * if ds.κ d o then 1 else 0)
          ≤ (iota B).sum fun _ w => (w : ℝ) := by
      simp only [Finsupp.sum]
      calc (∑ d ∈ D.support, ∑ o ∈ (iota B).support,
              (D d : ℝ) * ((iota B) o : ℝ) * if ds.κ d o then 1 else 0)
          ≤ ∑ d ∈ D.support, ∑ o ∈ (iota B).support, (D d : ℝ) * ((iota B) o : ℝ) := by
            refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun o _ => ?_
            have hite : (if ds.κ d o then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
            have hnn : (0 : ℝ) ≤ (D d : ℝ) * ((iota B) o : ℝ) := by positivity
            calc (D d : ℝ) * ((iota B) o : ℝ) * (if ds.κ d o then (1 : ℝ) else 0)
                ≤ (D d : ℝ) * ((iota B) o : ℝ) * 1 := mul_le_mul_of_nonneg_left hite hnn
              _ = (D d : ℝ) * ((iota B) o : ℝ) := mul_one _
        _ = (∑ d ∈ D.support, (D d : ℝ)) * ∑ o ∈ (iota B).support, ((iota B) o : ℝ) :=
            (Finset.sum_mul_sum _ _ _ _).symm
        _ = ∑ o ∈ (iota B).support, ((iota B) o : ℝ) := by rw [hD1, one_mul]
    rw [hperf]
    linarith [hnnA, hub]
  -- each image is bounded above (by the mass of the right-hand system)
  have hBdd : ∀ A B : σ,
      BddAbove ((fun D => ds.performance (iota A, iota B) D) ''
        {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1}) := by
    intro A B
    refine ⟨((iota B).sum fun _ w => (w : ℝ)), ?_⟩
    rintro x ⟨D, hD, rfl⟩
    exact hbound A B D hD
  unfold AdvWith
  by_cases hne : ({D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1}).Nonempty
  · -- nonempty class: csSup subadditivity through the pointwise telescoping
    refine csSup_le (hne.image _) ?_
    rintro x ⟨D, hD, rfl⟩
    have h1 : ds.performance (iota S, iota T) D
        ≤ sSup ((fun D => ds.performance (iota S, iota T) D) ''
            {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1}) :=
      le_csSup (hBdd S T) ⟨D, hD, rfl⟩
    have h2 : ds.performance (iota T, iota U) D
        ≤ sSup ((fun D => ds.performance (iota T, iota U) D) ''
            {D : ds.ProbDistinguisher | (D.sum fun _ w => w) = 1}) :=
      le_csSup (hBdd T U) ⟨D, hD, rfl⟩
    show ds.performance (iota S, iota U) D ≤ _
    rw [hsplit D]
    exact add_le_add h1 h2
  · -- empty class: all three suprema are `Real.sSup_empty = 0`
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp [Real.sSup_empty]

/-! ### Connecting lemmas to the keystone (`Indist.lean`) -/

section KeystoneBridge

universe u v

open Def45 Def416 Def417 Def419 Lem416

variable {X : Type u} {Y : Type v}
  [Inhabited Y] [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- CONNECTING LEMMA (dedupe obligation): the shared `AdvWith` at the concrete
CR18 §4.10.2 distinction structure (`Lem416.distinctionStructure`, `iota = id`)
IS the keystone's Δ — the `sSup` over `isProbDist` distinguishers appearing in
`Thm417.delta_le_gamma` / `Thm417.fundamental`.  The weight-1 classes coincide
by `Dist.weight_eq_finsupp_sum` (the concrete distinguisher type is a
`Fintype`). -/
theorem advWith_eq_keystone (q : ℕ) (S T : PDS X Y) :
    AdvWith (Lem416.distinctionStructure X Y q)
        (id : PDS X Y → Dist (Lem416.distinctionStructure X Y q).O) S T
      = sSup ((fun D : (Lem416.distinctionStructure X Y q).ProbDistinguisher =>
          (Lem416.distinctionStructure X Y q).performance (S, T) D) ''
    {D | D.isProbDist}) := by
  unfold AdvWith
  have hset : {D : (Lem416.distinctionStructure X Y q).ProbDistinguisher |
        (D.sum fun _ w => w) = 1}
      = {D : (Lem416.distinctionStructure X Y q).ProbDistinguisher | D.isProbDist} := by
    ext D
    simp only [Set.mem_setOf_eq, Dist.isProbDist, Dist.weight_eq_finsupp_sum]
  rw [hset]
  rfl

/-- CR18 Theorem 4.17 re-expressed through the shared `AdvWith`
(`Thm417.delta_le_gamma` transported along `advWith_eq_keystone`):

  `Δ(Shat⁻, T) = AdvWith (Lem416.distinctionStructure X Y q) id Shat⁻ T ≤ Γ(Shat)`. -/
theorem advWith_le_gamma [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
    [Inhabited X] (q : ℕ)
    (Shat : PDG X Y) (T : PDS X Y)
    (hCondEquiv : Shat |≡ T)
    (That : PDG X Y)
    (hGameEquiv : Shat ≡_g That)
    (hStrip : PDG.strip That = T)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hThat : That.sum (fun _ p => p) = 1) :
    AdvWith (Lem416.distinctionStructure X Y q)
        (id : PDS X Y → Dist (Lem416.distinctionStructure X Y q).O)
        (PDG.strip Shat) T
      ≤ (Def417.maxWinProb (Lem416.gameStructure X Y q) Shat : Real) := by
  rw [advWith_eq_keystone]
  exact Thm417.delta_le_gamma q Shat T hCondEquiv That hGameEquiv hStrip hShat hThat

end KeystoneBridge

end RandomSystems.CR18

end
