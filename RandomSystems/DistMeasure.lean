/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DistExpect
import RandomSystems.DistLift
import RandomSystems.StatDist
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# One-way transport of `Dist` into mathlib's measure theory (`DESIGN.md` §12)

The bridge from the library's signed, unnormalized `Dist A = A →₀ ℝ` on a
`Fintype` carrier into mathlib's probability stack, at all three distribution
layers:

* `Dist.isProbDist → PMF`  (`Dist.toPMF`), with the integral bridge
  `integral_toPMF_eq_expect` and the event-mass correspondence
  `toPMF_toMeasure_apply`;
* `Dist.NonNeg → Measure`  (`Dist.toMeasure`), a finite measure by instance,
  with the set-mass correspondence `toMeasure_apply_massSet`;
* signed `→ SignedMeasure` (`Dist.toSignedMeasure`), with the explicit Jordan
  decomposition into the two truncated transports
  (`Dist.jordanDecomposition`, `toSignedMeasure_toJordanDecomposition`) and
  the characterization of `statDist` as the total mass of the Jordan positive
  part (`statDist_eq_toReal_posPart_univ`).

Everything mathlib already knows about probability is *imported* through this
bridge rather than reproved; `mass_ge_le_variance_div_sq` (Chebyshev) is the
worked demonstration.

## Instance discipline (`DESIGN.md` §12 point 3)

Measure-theoretic instances are introduced at the proof site
(`letI : MeasurableSpace A := ⊤`), never in a library-facing signature: every
statement expressible in `Dist`/ℝ vocabulary — here, Chebyshev — has only
`[Fintype A]` in its binders.  The transport *machinery* itself
(`toMeasure`, `toSignedMeasure`, the correspondence and Jordan lemmas)
necessarily carries `[MeasurableSpace A]` (+ `[MeasurableSingletonClass A]`):
its conclusions are measure-theory objects, so no `Dist`/ℝ spelling exists.
Any `Fintype` carrier enters the bridge by taking the `⊤` σ-algebra at the use
site; `@DiscreteMeasurableSpace α ⊤` is an instance and supplies
`MeasurableSingletonClass`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RandomSystems

namespace Dist

variable {A : Type*} [Fintype A]

/-! ## Bottom layer: `isProbDist → PMF` -/

/-- Transport of a probability `Dist` on a `Fintype` carrier into mathlib's
`PMF`.  Needs no measurable-space structure: a `PMF` is a bare
`ℝ≥0∞`-valued mass function summing to one. -/
def toPMF (X : Dist A) (hX : X.isProbDist) : _root_.PMF A :=
  ⟨fun a => ENNReal.ofReal (X a), by
    have hsum : ∑ a, ENNReal.ofReal (X a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hX.1 a), ← weight_eq_sum,
        hX.2, ENNReal.ofReal_one]
    simpa [hsum] using hasSum_fintype fun a => ENNReal.ofReal (X a)⟩

/-- Pointwise value of the transported `PMF`. -/
@[simp]
theorem toPMF_apply (X : Dist A) (hX : X.isProbDist) (a : A) :
    toPMF X hX a = ENNReal.ofReal (X a) := rfl

/-- The round trip through `ℝ≥0∞` is lossless on an honest probability
distribution. -/
theorem toPMF_apply_toReal (X : Dist A) (hX : X.isProbDist) (a : A) :
    (toPMF X hX a).toReal = X a :=
  ENNReal.toReal_ofReal (hX.1 a)

section MeasurableSpace

variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-! ## The integral bridge -/

/-- **The integral bridge**: the library expectation `Dist.expect` is the
Bochner integral against the transported measure.  This is the identity that
lets mathlib's integral-vocabulary theorems land on `Dist` statements. -/
theorem integral_toPMF_eq_expect (X : Dist A) (hX : X.isProbDist) (f : A → ℝ) :
    ∫ a, f a ∂(toPMF X hX).toMeasure = X.expect f := by
  rw [PMF.integral_eq_sum, expect_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [toPMF_apply, ENNReal.toReal_ofReal (hX.1 a), smul_eq_mul]

/-- Event-mass correspondence at the bottom layer: the transported measure of
an event is `ENNReal.ofReal` of its `Dist.mass`. -/
theorem toPMF_toMeasure_apply (X : Dist A) (hX : X.isProbDist) (P : A → Prop) :
    (toPMF X hX).toMeasure {a | P a} = ENNReal.ofReal (X.mass P) := by
  classical
  rw [show {a | P a} = ↑(Finset.univ.filter P) by ext a; simp,
    PMF.toMeasure_apply_finset, mass_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => by split <;> simp [hX.1 a])]
  simp [Finset.sum_filter, apply_ite ENNReal.ofReal]

/-! ## Middle layer: arbitrary `Dist` → finite `Measure`

`ENNReal.ofReal` truncates negative mass, so on `NonNeg` distributions nothing
is lost, and on signed ones the transport is exactly the positive part — which
the signed layer below exploits. -/

/-- Transport of an arbitrary `Dist` into a measure: the weighted sum of Dirac
atoms with truncated (`ENNReal.ofReal`) weights.  Faithful on `NonNeg`
distributions (`toMeasure_apply_massSet`); the positive part on signed
ones. -/
def toMeasure (X : Dist A) : Measure A :=
  Measure.sum fun a => ENNReal.ofReal (X a) • Measure.dirac a

/-- Value of the transported measure on a measurable set, as a finite sum of
truncated atom weights. -/
theorem toMeasure_apply (X : Dist A) {s : Set A} (hs : MeasurableSet s) :
    toMeasure X s = ∑ a, s.indicator (fun a => ENNReal.ofReal (X a)) a := by
  rw [toMeasure, Measure.sum_apply _ hs, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases ha : a ∈ s <;> simp [ha]

/-- Finiteness of the transported measure is structural — a finite sum of
finite atoms, no `NonNeg` needed (truncation already happened).  Registered as
an instance so `IsFiniteMeasure` side conditions downstream are discharged by
typeclass search. -/
instance instIsFiniteMeasureToMeasure (X : Dist A) :
    IsFiniteMeasure (toMeasure X) := by
  constructor
  rw [toMeasure_apply X MeasurableSet.univ]
  exact ENNReal.sum_lt_top.mpr fun a _ => by simp [ENNReal.ofReal_lt_top]

/-- Set-mass correspondence at the middle layer: for `NonNeg` `X`,
`X.toMeasure s = ENNReal.ofReal (X.massSet s)`. -/
theorem toMeasure_apply_massSet {X : Dist A} (hX : X.NonNeg) {s : Set A}
    (hs : MeasurableSet s) :
    toMeasure X s = ENNReal.ofReal (X.massSet s) := by
  classical
  rw [toMeasure_apply X hs, massSet, mass_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => by split <;> simp [hX a])]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases ha : a ∈ s <;> simp [ha]

/-- The transported measure of the whole space is the total weight (for
`NonNeg` `X`). -/
theorem toMeasure_univ {X : Dist A} (hX : X.NonNeg) :
    toMeasure X Set.univ = ENNReal.ofReal X.weight := by
  rw [toMeasure_apply_massSet hX MeasurableSet.univ]
  congr 1
  rw [massSet, weight_eq_sum, mass_eq_sum]
  simp

/-- Coherence of the layers: on a probability `Dist` the bottom-layer
(`toPMF`) and middle-layer (`toMeasure`) transports are the same measure. -/
theorem toPMF_toMeasure_eq_toMeasure (X : Dist A) (hX : X.isProbDist) :
    (toPMF X hX).toMeasure = toMeasure X := by
  classical
  refine Measure.ext fun s hs => ?_
  have h := toPMF_toMeasure_apply X hX (· ∈ s)
  rw [Set.setOf_mem_eq] at h
  rw [h, toMeasure_apply_massSet hX.1 hs, massSet]

/-! ## Top layer: signed `Dist` → `SignedMeasure`, and the Jordan
decomposition -/

/-- Transport of a signed `Dist`: positive part minus negative part, each a
finite measure via `toMeasure`.  (`toMeasure X` only sees `max (X a) 0`;
`toMeasure (-X)` only sees `max (-(X a)) 0`.) -/
def toSignedMeasure (X : Dist A) : SignedMeasure A :=
  (toMeasure X).toSignedMeasure - (toMeasure (-X)).toSignedMeasure

/-- The signed transport is faithful with *no* layer hypothesis: on any
measurable set it reads off the signed mass `X.massSet s`. -/
theorem toSignedMeasure_apply (X : Dist A) {s : Set A}
    (hs : MeasurableSet s) :
    toSignedMeasure X s = X.massSet s := by
  classical
  rw [toSignedMeasure, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs,
    measureReal_def, measureReal_def,
    toMeasure_apply X hs, toMeasure_apply (-X) hs,
    ENNReal.toReal_sum (fun a _ => by
      by_cases ha : a ∈ s <;> simp [ha]),
    ENNReal.toReal_sum (fun a _ => by
      by_cases ha : a ∈ s <;> simp [ha]),
    ← Finset.sum_sub_distrib, massSet, mass_eq_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ s
  · simp only [Set.indicator_apply, ha, if_true, Finsupp.neg_apply,
      ENNReal.toReal_ofReal', max_zero_sub_max_neg_zero_eq_self]
  · simp [ha]

/-- The explicit Jordan decomposition of the signed transport: the truncated
transports of the two signs, mutually singular on `{a | X a ≤ 0}`. -/
def jordanDecomposition (X : Dist A) : JordanDecomposition A where
  posPart := toMeasure X
  negPart := toMeasure (-X)
  mutuallySingular := by
    refine ⟨{a | X a ≤ 0}, MeasurableSet.of_discrete, ?_, ?_⟩
    · rw [toMeasure_apply X MeasurableSet.of_discrete]
      exact Finset.sum_eq_zero fun a _ => by
        by_cases ha : X a ≤ 0 <;> simp [ha, ENNReal.ofReal_eq_zero]
    · rw [toMeasure_apply (-X) MeasurableSet.of_discrete]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases ha : X a ≤ 0
      · simp [ha]
      · simp [ha, ENNReal.ofReal_eq_zero,
          neg_nonpos.mpr (le_of_lt (not_le.mp ha))]

/-- mathlib's `toJordanDecomposition` recovers exactly the two truncated
transports: `Dist.jordanDecomposition` *is* the Jordan decomposition of
`Dist.toSignedMeasure`. -/
theorem toSignedMeasure_toJordanDecomposition (X : Dist A) :
    (toSignedMeasure X).toJordanDecomposition = jordanDecomposition X := by
  have h : toSignedMeasure X = (jordanDecomposition X).toSignedMeasure := rfl
  rw [h, JordanDecomposition.toJordanDecomposition_toSignedMeasure]

/-! ## Chebyshev, transported -/

/-- Instance-carrying core of `mass_ge_le_variance_div_sq`; the public
statement introduces the σ-algebra at the proof site instead. -/
private theorem mass_ge_le_variance_div_sq_aux (X : Dist A)
    (hX : X.isProbDist) (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ |f a - X.expect f|) ≤ X.variance f / c ^ 2 := by
  classical
  set μ := (toPMF X hX).toMeasure with hμ
  have hmem : MemLp f 2 μ := .of_discrete
  have key := meas_ge_le_variance_div_sq (μ := μ) hmem hc
  have hint : μ[f] = X.expect f := integral_toPMF_eq_expect X hX f
  have hvar : Var[f; μ] = X.variance f := by
    rw [ProbabilityTheory.variance_eq_integral
      Measurable.of_discrete.aemeasurable, hint]
    simpa [variance] using
      integral_toPMF_eq_expect X hX fun a => (f a - X.expect f) ^ 2
  have h0 : 0 ≤ X.variance f / c ^ 2 :=
    div_nonneg (hvar ▸ ProbabilityTheory.variance_nonneg f μ) (sq_nonneg c)
  refine (ENNReal.ofReal_le_ofReal_iff h0).mp ?_
  rw [← toPMF_toMeasure_apply X hX]
  calc (toPMF X hX).toMeasure {a | c ≤ |f a - X.expect f|}
      ≤ ENNReal.ofReal (Var[f; μ] / c ^ 2) := by simpa only [hint] using key
    _ = ENNReal.ofReal (X.variance f / c ^ 2) := by rw [hvar]

end MeasurableSpace

/-- **Chebyshev's inequality** for a finite probability `Dist`:
`X{a | c ≤ |f a - 𝔼_X f|} ≤ Var_X f / c²`.  `isProbDist` layer.

Transported from `ProbabilityTheory.meas_ge_le_variance_div_sq` through
`Dist.toPMF`; the measurable-space instance (`⊤`) is introduced at the proof
site per `DESIGN.md` §12, so the binders stay in `Dist`/ℝ vocabulary.  The
worked demonstration that the bridge carries mathlib theorems. -/
theorem mass_ge_le_variance_div_sq {X : Dist A} (hX : X.isProbDist)
    (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ |f a - X.expect f|) ≤ X.variance f / c ^ 2 :=
  letI : MeasurableSpace A := ⊤
  mass_ge_le_variance_div_sq_aux X hX f hc

end Dist

/-! ## `statDist` as a Jordan positive part -/

section Jordan

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- **`statDist` is a Jordan positive part**: the statistical distance
`δ(X, Y)` is the total mass of the positive part of the Jordan decomposition
of the transported signed measure of `X - Y`.  This identifies the library's
one-sided excess `∑_a max(X(a) - Y(a), 0)` with mathlib's canonical
decomposition of a signed measure; no layer hypothesis is needed on either
side. -/
theorem statDist_eq_toReal_posPart_univ (X Y : Dist A) :
    statDist X Y
      = ((Dist.toSignedMeasure (X - Y)).toJordanDecomposition.posPart
          Set.univ).toReal := by
  rw [Dist.toSignedMeasure_toJordanDecomposition]
  show statDist X Y = ((Dist.toMeasure (X - Y)) Set.univ).toReal
  rw [Dist.toMeasure_apply _ MeasurableSet.univ, statDist_eq_sum_univ,
    ENNReal.toReal_sum (fun a _ => by simp)]
  exact Finset.sum_congr rfl fun a _ => by
    simp [ENNReal.toReal_ofReal', Finsupp.sub_apply]

end Jordan

/-! ## The `Dist`-level split and the measure-level split are the same

`RandomSystems.DistLift` performs the Jordan decomposition without leaving the
`Dist` carrier, as mathlib's lattice-ordered-group `posPart`/`negPart` on
`A →₀ ℝ`: `X⁺ - X⁻ = X` with `X⁺`, `X⁻` both `Dist.NonNeg`.  The lemmas below
prove that this is the *same* decomposition the measure side computes — the
truncating transport `toMeasure` cannot tell `X` from `X⁺`, so
`Dist.jordanDecomposition` is literally the pair of transported `Dist`-level
parts.  `statDist_eq_toReal_posPart_univ` above is the `X - Y` instance of
`Dist.toReal_toJordanDecomposition_posPart_univ` below, read through
`Dist.statDist_eq_weight_posPart`. -/

namespace Dist

section JordanLift

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
/-- `toMeasure` truncates, so it cannot distinguish a signed `Dist` from its
`Dist`-level positive part. -/
theorem toMeasure_posPart (X : Dist A) : toMeasure X⁺ = toMeasure X := by
  unfold toMeasure
  congr 1
  funext a
  rw [posPart_apply]
  rcases le_total (X a) 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr h]
  · rw [max_eq_left h]

omit [Fintype A] [MeasurableSingletonClass A] in
/-- The negative part transports to the truncated transport of `-X`, which is
what `Dist.jordanDecomposition` uses as its negative part. -/
theorem toMeasure_negPart (X : Dist A) : toMeasure X⁻ = toMeasure (-X) := by
  unfold toMeasure
  congr 1
  funext a
  rw [negPart_apply, Finsupp.neg_apply]
  rcases le_total (-X a) 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr h]
  · rw [max_eq_left h]

/-- **The two splits agree, positive side**: mathlib's Jordan positive part of
the transported signed measure is the transport of the `Dist`-level positive
part `X⁺`. -/
theorem toJordanDecomposition_posPart (X : Dist A) :
    (toSignedMeasure X).toJordanDecomposition.posPart = toMeasure X⁺ := by
  rw [toSignedMeasure_toJordanDecomposition, toMeasure_posPart]
  rfl

/-- **The two splits agree, negative side**: mathlib's Jordan negative part of
the transported signed measure is the transport of the `Dist`-level negative
part `X⁻`. -/
theorem toJordanDecomposition_negPart (X : Dist A) :
    (toSignedMeasure X).toJordanDecomposition.negPart = toMeasure X⁻ := by
  rw [toSignedMeasure_toJordanDecomposition, toMeasure_negPart]
  rfl

/-- Total mass of the Jordan positive part is the `Dist`-level weight `|X⁺|`.
This is `statDist_eq_toReal_posPart_univ` with the `X - Y` specialization
removed: that statement is this one at `X := X - Y`, composed with
`Dist.statDist_eq_weight_posPart`. -/
theorem toReal_toJordanDecomposition_posPart_univ (X : Dist A) :
    ((toSignedMeasure X).toJordanDecomposition.posPart Set.univ).toReal
      = (X⁺).weight := by
  rw [toJordanDecomposition_posPart, toMeasure_univ (nonNeg_posPart X),
    ENNReal.toReal_ofReal (nonNeg_posPart X).weight_nonneg]

end JordanLift

end Dist

end RandomSystems
