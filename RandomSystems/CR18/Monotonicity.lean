/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.AdvMetric

/-!
# CR18 Cross-Structure Converter Monotonicity

Cross-structure converter monotonicity for distinction advantages
(CR18 §1.2/§3.1): `Δ_U(αS, αT) ≤ Δ_X(S, T)` whenever the converter `α`
admits a mass-preserving, performance-preserving simulation of every
`U`-side distinguisher by an `X`-side one (`ConverterCompat`).  The
converter may CHANGE the interface — a same-interface statement is
useless for reductions that cross interfaces.

The `Nonempty dsU.D` hypothesis is a genuine repair (machine-checked
disproof without it, 2026-06-10): with `dsU.D` empty the `U`-side
weight-1 distinguisher class is empty and its `sSup` is junk `0`, while
the `X`-side supremum can be negative.

## Dedupe (DONE at integration, 2026-06-11)

The draft carried local `DStruct`/`AdvWith` mirrors; at integration they
were DELETED and the statement uses the library's
`Def47.DistinctionStructure` (`RandomSystems/CR18/Game.lean`) and the
SHARED advantage `RandomSystems.CR18.AdvWith`
(`RandomSystems/CR18/AdvMetric.lean`, connected to the keystone Δ by
`advWith_eq_keystone`).  Only the converter-specific pieces remain local:

* `applyPDS` — `Dist.fTransform` of `DDC.apply` (Dist-level lift of the
  deterministic converter application).
* `ConverterCompat` — the mass- and performance-preserving simulation
  predicate.
-/
-- PORTED from hctr2-verification HCTR2/Proofs/CR18/Sketch.lean:3255-3326 — UPSTREAM-CANDIDATE landed 2026-06-11

open scoped Classical

namespace RandomSystems.CR18.Monotonicity

open RandomSystems.CR18 Def47

/-- §1.2  Converter application = `Dist.fTransform` of the REAL `DDC.apply`
(Dist-level lift of the deterministic converter application). -/
noncomputable def applyPDS {U V X Y : Type} (α : DDC U V X Y)
    (S : PDS X Y) : PDS U V :=
  Dist.fTransform (fun s => α.apply s) S

/-- The reduction `D ↦ D ∘ α` maps every `dsU`-distinguisher to a
MASS-PRESERVING `dsX`-distinguisher with IDENTICAL performance on converted
systems — the cross-structure compatibility behind converter monotonicity.

(DISPROOF REPAIR 2026-06-10: the mass clause is LOAD-BEARING — `AdvWith`
sups over the weight-1 class and performance is linear in distinguisher
mass, so without it a bloated `D'` lets the `U`-side sup exceed the
`X`-side sup and the monotonicity statement is false.) -/
def ConverterCompat {U V X Y : Type} (dsU dsX : DistinctionStructure)
    (iotaU : PDS U V → Dist dsU.O) (iotaX : PDS X Y → Dist dsX.O)
    (α : DDC U V X Y) : Prop :=
  ∀ D : dsU.ProbDistinguisher, ∃ D' : dsX.ProbDistinguisher,
    (D'.sum fun _ w => w) = (D.sum fun _ w => w) ∧
    ∀ S T : PDS X Y,
      dsU.performance (iotaU (applyPDS α S), iotaU (applyPDS α T)) D
        = dsX.performance (iotaX S, iotaX T) D'

/-- (§1.2,§3.1)  CROSS-STRUCTURE converter monotonicity
`Δ_U(αS, αT) ≤ Δ_X(S, T)` under `ConverterCompat` — the converter may
CHANGE the interface (a same-interface statement is useless for
interface-crossing reductions).  ABSENT in CR18.

The `Nonempty dsU.D` hypothesis is a genuine repair: with `dsU.D` empty
the `U`-side weight-1 class is empty and its `sSup` is junk `0`, while the
`X`-side sup can be negative. -/
theorem converter_monotone {U V X Y : Type}
    (dsU dsX : DistinctionStructure)
    (iotaU : PDS U V → Dist dsU.O) (iotaX : PDS X Y → Dist dsX.O)
    (α : DDC U V X Y)
    (hα : ConverterCompat dsU dsX iotaU iotaX α) (hne : Nonempty dsU.D)
    (S T : PDS X Y) :
    AdvWith dsU iotaU (applyPDS α S) (applyPDS α T) ≤ AdvWith dsX iotaX S T := by
  classical
  -- X-side uniform bound on the weight-1 class.
  have hperf : ∀ (V₀ V₁ : Dist dsX.O) (E : dsX.ProbDistinguisher),
      dsX.performance (V₀, V₁) E
        = (E.sum fun d dw => V₁.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if dsX.κ d o then 1 else 0)
          - (E.sum fun d dw => V₀.sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if dsX.κ d o then 1 else 0) := fun _ _ _ => rfl
  have hbound : ∀ D' : dsX.ProbDistinguisher, (D'.sum fun _ w => w) = 1 →
      dsX.performance (iotaX S, iotaX T) D' ≤ ((iotaX T).sum fun _ w => (w : ℝ)) := by
    intro D' hD
    have hD1 : (∑ d ∈ D'.support, (D' d : ℝ)) = 1 := by
      have h1 : ((D'.sum fun _ w => w : NNReal) : ℝ) = 1 := by rw [hD]; norm_num
      simpa [Finsupp.sum, NNReal.coe_sum] using h1
    have hnnS : (0 : ℝ) ≤ D'.sum fun d dw => (iotaX S).sum fun o ow =>
        (dw : ℝ) * (ow : ℝ) * if dsX.κ d o then 1 else 0 := by
      simp only [Finsupp.sum]
      refine Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun o _ => ?_
      have hite : (0 : ℝ) ≤ if dsX.κ d o then (1 : ℝ) else 0 := by split <;> norm_num
      have hnn : (0 : ℝ) ≤ (D' d : ℝ) * ((iotaX S) o : ℝ) := by positivity
      exact mul_nonneg hnn hite
    have hub : (D'.sum fun d dw => (iotaX T).sum fun o ow =>
        (dw : ℝ) * (ow : ℝ) * if dsX.κ d o then 1 else 0)
          ≤ (iotaX T).sum fun _ w => (w : ℝ) := by
      simp only [Finsupp.sum]
      calc (∑ d ∈ D'.support, ∑ o ∈ (iotaX T).support,
              (D' d : ℝ) * ((iotaX T) o : ℝ) * if dsX.κ d o then 1 else 0)
          ≤ ∑ d ∈ D'.support, ∑ o ∈ (iotaX T).support, (D' d : ℝ) * ((iotaX T) o : ℝ) := by
            refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun o _ => ?_
            have hite : (if dsX.κ d o then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
            have hnn : (0 : ℝ) ≤ (D' d : ℝ) * ((iotaX T) o : ℝ) := by positivity
            calc (D' d : ℝ) * ((iotaX T) o : ℝ) * (if dsX.κ d o then (1 : ℝ) else 0)
                ≤ (D' d : ℝ) * ((iotaX T) o : ℝ) * 1 := mul_le_mul_of_nonneg_left hite hnn
              _ = (D' d : ℝ) * ((iotaX T) o : ℝ) := mul_one _
        _ = (∑ d ∈ D'.support, (D' d : ℝ)) * ∑ o ∈ (iotaX T).support, ((iotaX T) o : ℝ) :=
            (Finset.sum_mul_sum _ _ _ _).symm
        _ = ∑ o ∈ (iotaX T).support, ((iotaX T) o : ℝ) := by rw [hD1, one_mul]
    rw [hperf]
    linarith [hnnS, hub]
  have hBdd : BddAbove ((fun D' => dsX.performance (iotaX S, iotaX T) D') ''
      {D' : dsX.ProbDistinguisher | (D'.sum fun _ w => w) = 1}) := by
    refine ⟨((iotaX T).sum fun _ w => (w : ℝ)), ?_⟩
    rintro x ⟨D', hD, rfl⟩
    exact hbound D' hD
  -- Mass-preserving simulation: the U-side image is CONTAINED in the X-side image.
  have hsub : ((fun D => dsU.performance
        (iotaU (applyPDS α S), iotaU (applyPDS α T)) D) ''
        {D : dsU.ProbDistinguisher | (D.sum fun _ w => w) = 1})
      ⊆ ((fun D' => dsX.performance (iotaX S, iotaX T) D') ''
        {D' : dsX.ProbDistinguisher | (D'.sum fun _ w => w) = 1}) := by
    rintro x ⟨D, hD, rfl⟩
    obtain ⟨D', hw', hperfEq⟩ := hα D
    exact ⟨D', by rw [Set.mem_setOf_eq, hw']; exact hD, (hperfEq S T).symm⟩
  -- The U-side class is nonempty (point mass on any `d : dsU.D`).
  have hUne : ({D : dsU.ProbDistinguisher | (D.sum fun _ w => w) = 1}).Nonempty := by
    obtain ⟨d⟩ := hne
    exact ⟨Finsupp.single d 1, by
      simp [Finsupp.sum_single_index]⟩
  unfold AdvWith
  exact csSup_le_csSup hBdd (hUne.image _) hsub

end RandomSystems.CR18.Monotonicity
