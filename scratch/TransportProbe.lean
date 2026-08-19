/-
TransportProbe.lean — EXPERIMENT, not library code.

Measures the cost of a one-way transport from the library's signed,
unnormalized `Dist A := A →₀ ℝ` into mathlib's measure-theory stack on a
`Fintype` carrier:

  P1  isProbDist  → PMF
  P2  expectation ∑ a, X a * f a  =  ∫ f d(toPMF X).toMeasure
  P3  transport of Chebyshev (ProbabilityTheory.meas_ge_le_variance_div_sq)
  P4  NonNeg      → Measure (finite)
  P5  signed      → SignedMeasure; statDist as Jordan positive part
  P6  layer counterexamples/witnesses

Not referenced by any lean_lib target.  Check with
  lake env lean scratch/TransportProbe.lean
-/
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Analysis.Convex.Jensen
import RandomSystems.Dist
import RandomSystems.StatDist

noncomputable section

open RandomSystems RandomSystems.Dist MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace TransportProbe

variable {A : Type*} [Fintype A]

/-! ## P1: bottom layer — `isProbDist` → `PMF` -/

/-- Transport of a probability `Dist` on a `Fintype` into mathlib's `PMF`. -/
def toPMF (X : RandomSystems.Dist A) (hX : X.isProbDist) : PMF A :=
  ⟨fun a => ENNReal.ofReal (X a), by
    have hsum : ∑ a, ENNReal.ofReal (X a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hX.1 a), ← Dist.weight_eq_sum,
        hX.2, ENNReal.ofReal_one]
    simpa [hsum] using hasSum_fintype fun a => ENNReal.ofReal (X a)⟩

@[simp]
theorem toPMF_apply (X : RandomSystems.Dist A) (hX : X.isProbDist) (a : A) :
    toPMF X hX a = ENNReal.ofReal (X a) := rfl

/-- Pointwise characterisation: the round trip through `ℝ≥0∞` is lossless on
an honest probability distribution. -/
theorem toPMF_toReal (X : RandomSystems.Dist A) (hX : X.isProbDist) (a : A) :
    ((toPMF X hX) a).toReal = X a :=
  ENNReal.toReal_ofReal (hX.1 a)

/-! ## P2: the integral bridge (the crux) -/

/-- The library's expectation (no first-class `expect` exists in
`RandomSystems`; this spelling `∑ a, X a * f a` is the one used inline
throughout, e.g. `StatDist.hTechnique_expectation`). -/
def expect (X : RandomSystems.Dist A) (f : A → ℝ) : ℝ := ∑ a, X a * f a

variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- P2: the library expectation IS the Bochner integral against the
transported measure. -/
theorem integral_toPMF (X : RandomSystems.Dist A) (hX : X.isProbDist) (f : A → ℝ) :
    ∫ a, f a ∂(toPMF X hX).toMeasure = expect X f := by
  rw [PMF.integral_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [toPMF_apply, ENNReal.toReal_ofReal (hX.1 a), smul_eq_mul]

/-- Event mass transports: measure of a set = `ENNReal.ofReal` of `Dist.mass`. -/
theorem toPMF_toMeasure_apply (X : RandomSystems.Dist A) (hX : X.isProbDist) (P : A → Prop) :
    (toPMF X hX).toMeasure {a | P a} = ENNReal.ofReal (X.mass P) := by
  classical
  rw [show {a | P a} = ↑(Finset.univ.filter P) by ext a; simp,
    PMF.toMeasure_apply_finset, mass_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => by split <;> simp [hX.1 a])]
  simp [Finset.sum_filter, apply_ite ENNReal.ofReal]

/-! ## P3: transporting a real theorem — Chebyshev -/

/-- Dist-side variance, in the library's sum vocabulary. -/
def distVar (X : RandomSystems.Dist A) (f : A → ℝ) : ℝ :=
  expect X fun a => (f a - expect X f) ^ 2

/-- P3: Chebyshev's inequality for the library's `Dist`, transported from
`ProbabilityTheory.meas_ge_le_variance_div_sq`.

Side conditions demanded by mathlib and how each was discharged:
* `IsFiniteMeasure μ`  — instance search (`PMF.toMeasure.isProbabilityMeasure`
  → `IsFiniteMeasure`), zero lines.
* `MemLp f 2 μ`        — `MemLp.of_discrete`, one term.
* `AEMeasurable`       — `Measurable.of_discrete.aemeasurable`, one term
  (needed for `variance_eq_integral`).
* integrability of the square — never surfaced; swallowed by the above. -/
theorem dist_chebyshev (X : RandomSystems.Dist A) (hX : X.isProbDist) (f : A → ℝ)
    {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ |f a - expect X f|) ≤ distVar X f / c ^ 2 := by
  classical
  set μ := (toPMF X hX).toMeasure with hμ
  have hmem : MemLp f 2 μ := .of_discrete
  have key := meas_ge_le_variance_div_sq (μ := μ) hmem hc
  have hint : μ[f] = expect X f := integral_toPMF X hX f
  have hvar : Var[f; μ] = distVar X f := by
    rw [variance_eq_integral Measurable.of_discrete.aemeasurable, hint]
    simpa [distVar] using integral_toPMF X hX fun a => (f a - expect X f) ^ 2
  have h0 : 0 ≤ distVar X f / c ^ 2 :=
    div_nonneg (hvar ▸ variance_nonneg f μ) (sq_nonneg c)
  refine (ENNReal.ofReal_le_ofReal_iff h0).mp ?_
  rw [← toPMF_toMeasure_apply X hX]
  calc (toPMF X hX).toMeasure {a | c ≤ |f a - expect X f|}
      ≤ ENNReal.ofReal (Var[f; μ] / c ^ 2) := by simpa only [hint] using key
    _ = ENNReal.ofReal (distVar X f / c ^ 2) := by rw [hvar]

/-! ## P4: middle layer — `NonNeg`, arbitrary weight → finite `Measure` -/

/-- Transport of an arbitrary `Dist` into a measure.  `ENNReal.ofReal`
truncates negative mass, so on `NonNeg` distributions nothing is lost and on
signed ones this is exactly the positive part — which P5 exploits. -/
def toMeas (X : RandomSystems.Dist A) : Measure A :=
  Measure.sum fun a => ENNReal.ofReal (X a) • Measure.dirac a

theorem toMeas_apply (X : RandomSystems.Dist A) {s : Set A}
    (hs : MeasurableSet s) :
    toMeas X s = ∑ a, s.indicator (fun a => ENNReal.ofReal (X a)) a := by
  rw [toMeas, Measure.sum_apply _ hs, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases ha : a ∈ s <;> simp [ha]

/-- Finiteness is structural: a finite sum of finite atoms.  (No `NonNeg`
needed — truncation already happened.)  This is an `instance`, so
`IsFiniteMeasure` side conditions downstream are discharged by typeclass
search, i.e. "automatically" in the sense of the experiment's question. -/
instance (X : RandomSystems.Dist A) : IsFiniteMeasure (toMeas X) := by
  constructor
  rw [toMeas_apply X MeasurableSet.univ]
  exact ENNReal.sum_lt_top.mpr fun a _ => by simp [ENNReal.ofReal_lt_top]

/-- Set mass corresponds: `μ(s) = ofReal (X.massSet s)` for `NonNeg` `X`. -/
theorem toMeas_apply_massSet {X : RandomSystems.Dist A} (hX : X.NonNeg)
    {s : Set A} (hs : MeasurableSet s) :
    toMeas X s = ENNReal.ofReal (X.massSet s) := by
  classical
  rw [toMeas_apply X hs, massSet, mass_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => by split <;> simp [hX a])]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases ha : a ∈ s <;> simp [ha]

/-- Total weight corresponds to the measure of the whole space. -/
theorem toMeas_univ {X : RandomSystems.Dist A} (hX : X.NonNeg) :
    toMeas X Set.univ = ENNReal.ofReal X.weight := by
  rw [toMeas_apply_massSet hX MeasurableSet.univ]
  congr 1
  rw [massSet, Dist.weight_eq_sum, mass_eq_sum]
  simp

/-- Coherence of the layers: on a probability `Dist` the P4 transport and the
P1/P2 transport are the same measure. -/
theorem toPMF_toMeasure_eq_toMeas (X : RandomSystems.Dist A)
    (hX : X.isProbDist) :
    (toPMF X hX).toMeasure = toMeas X := by
  classical
  refine Measure.ext fun s hs => ?_
  have h := toPMF_toMeasure_apply X hX (· ∈ s)
  rw [Set.setOf_mem_eq] at h
  rw [h, toMeas_apply_massSet hX.1 hs, massSet]

/-! ## P5: top layer — signed `Dist` → `SignedMeasure`, and the Jordan
conjecture -/

/-- Transport of a signed `Dist`: positive part minus negative part, each a
finite measure via P4.  (`toMeas X` only sees `max (X a) 0`; `toMeas (-X)`
only sees `max (-(X a)) 0`.) -/
def toSigned (X : RandomSystems.Dist A) : SignedMeasure A :=
  (toMeas X).toSignedMeasure - (toMeas (-X)).toSignedMeasure

/-- The transport is faithful: on any measurable set the signed measure reads
off the signed mass. -/
theorem toSigned_apply (X : RandomSystems.Dist A) {s : Set A}
    (hs : MeasurableSet s) :
    toSigned X s = X.massSet s := by
  classical
  rw [toSigned, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs,
    measureReal_def, measureReal_def,
    toMeas_apply X hs, toMeas_apply (-X) hs,
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

/-- The candidate Jordan decomposition of `toSigned X`: truncations of the two
signs, mutually singular on `{a | X a ≤ 0}`. -/
def jordanOf (X : RandomSystems.Dist A) : JordanDecomposition A where
  posPart := toMeas X
  negPart := toMeas (-X)
  mutuallySingular := by
    refine ⟨{a | X a ≤ 0}, MeasurableSet.of_discrete, ?_, ?_⟩
    · rw [toMeas_apply X MeasurableSet.of_discrete]
      exact Finset.sum_eq_zero fun a _ => by
        by_cases ha : X a ≤ 0 <;> simp [ha, ENNReal.ofReal_eq_zero]
    · rw [toMeas_apply (-X) MeasurableSet.of_discrete]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases ha : X a ≤ 0
      · simp [ha]
      · simp [ha, ENNReal.ofReal_eq_zero,
          neg_nonpos.mpr (le_of_lt (not_le.mp ha))]

/-- `toSigned X` really has `jordanOf X` as its Jordan decomposition: mathlib's
`toJordanDecomposition` recovers exactly the two truncated transports. -/
theorem toSigned_toJordanDecomposition (X : RandomSystems.Dist A) :
    (toSigned X).toJordanDecomposition = jordanOf X := by
  have h : toSigned X = (jordanOf X).toSignedMeasure := rfl
  rw [h, JordanDecomposition.toJordanDecomposition_toSignedMeasure]

/-- **The conjecture, proven**: `statDist X Y` is the total mass of the
positive part of the Jordan decomposition of the transported signed measure
`X - Y`. -/
theorem statDist_eq_jordan_posPart (X Y : RandomSystems.Dist A) :
    ((toSigned (X - Y)).toJordanDecomposition.posPart Set.univ).toReal
      = statDist X Y := by
  rw [toSigned_toJordanDecomposition]
  show ((toMeas (X - Y)) Set.univ).toReal = statDist X Y
  rw [toMeas_apply _ MeasurableSet.univ, statDist_eq_sum_univ,
    ENNReal.toReal_sum (fun a _ => by simp)]
  exact Finset.sum_congr rfl fun a _ => by
    simp [ENNReal.toReal_ofReal', Finsupp.sub_apply]

end TransportProbe

/-! ## P6: the layer question — weakest layer at which each fact is TRUE

Fresh namespace scope: no `MeasurableSpace` section variables leak in, so
these binders are the honest ones.  TOP = signed & arbitrary weight,
MIDDLE = `NonNeg` & arbitrary weight, BOTTOM = `isProbDist`. -/

namespace TransportProbe

section P6

variable {A : Type*} [Fintype A]

/-! ### (1) linearity of expectation in `f` — TOP -/

theorem expect_add_right (X : RandomSystems.Dist A) (f g : A → ℝ) :
    expect X (f + g) = expect X f + expect X g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_smul_right (X : RandomSystems.Dist A) (r : ℝ) (f : A → ℝ) :
    expect X (fun a => r * f a) = r * expect X f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

/-! ### (2) linearity of expectation in the DISTRIBUTION — TOP.
Note this one is *unstatable* after transport: `PMF` has no addition and no
scalar action, and `Measure` only a conical (`ℝ≥0∞`) one.  The signed
unnormalized carrier is exactly what makes it a bilinear pairing. -/

theorem expect_add_left (X Y : RandomSystems.Dist A) (f : A → ℝ) :
    expect (X + Y) f = expect X f + expect Y f := by
  simp [expect, add_mul, Finset.sum_add_distrib]

theorem expect_smul_left (r : ℝ) (X : RandomSystems.Dist A) (f : A → ℝ) :
    expect (r • X) f = r * expect X f := by
  simp [expect, Finset.mul_sum, mul_assoc]

/-! ### (3) monotonicity of expectation — MIDDLE -/

theorem expect_mono {X : RandomSystems.Dist A} (hX : X.NonNeg) {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : expect X f ≤ expect X g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hX a)

/-- (3) fails on the signed top layer: one point of mass `-1`. -/
theorem expect_mono_fails_signed :
    ∃ (X : RandomSystems.Dist Unit) (f g : Unit → ℝ),
      (∀ a, f a ≤ g a) ∧ ¬ expect X f ≤ expect X g := by
  refine ⟨ofFiniteMassFunction fun _ => -1, 0, 1, fun _ => zero_le_one, ?_⟩
  norm_num [expect]

/-! ### (4) Markov's inequality — MIDDLE (weight plays no role) -/

theorem dist_markov {X : RandomSystems.Dist A} (hX : X.NonNeg) {f : A → ℝ}
    (hf : ∀ a, 0 ≤ f a) {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ f a) ≤ expect X f / c := by
  classical
  rw [le_div_iff₀ hc, mass_eq_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : c ≤ f a
  · simpa [ha] using mul_le_mul_of_nonneg_left ha (hX a)
  · simpa [ha] using mul_nonneg (hX a) (hf a)

/-- (4) fails on the signed top layer: off-event negative mass at a positive
value of `f` pulls the expectation below the event mass. -/
theorem dist_markov_fails_signed :
    ∃ (X : RandomSystems.Dist Bool) (f : Bool → ℝ),
      (∀ a, 0 ≤ f a) ∧ ¬ X.mass (fun a => 1 ≤ f a) ≤ expect X f / 1 := by
  classical
  refine ⟨ofFiniteMassFunction fun b => if b then 1 else -1,
    fun b => if b then 1 else 1 / 2, fun b => by cases b <;> norm_num, ?_⟩
  rw [mass_eq_sum]
  norm_num [expect, Fintype.sum_bool]

/-! ### (5) discrete Cauchy–Schwarz — MIDDLE (any weight: it is positive
semidefiniteness of the pairing, not normalization) -/

theorem dist_cauchy_schwarz {X : RandomSystems.Dist A} (hX : X.NonNeg)
    (u v : A → ℝ) :
    (expect X fun a => u a * v a) ^ 2
      ≤ (expect X fun a => u a ^ 2) * expect X fun a => v a ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (X a) * u a) fun a => Real.sqrt (X a) * v a
  have h1 : ∀ a, Real.sqrt (X a) * u a * (Real.sqrt (X a) * v a)
      = X a * (u a * v a) := fun a => by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hX a)]
  have h2 : ∀ (w : A → ℝ) (a : A), (Real.sqrt (X a) * w a) ^ 2
      = X a * w a ^ 2 := fun w a => by
    rw [mul_pow, Real.sq_sqrt (hX a)]
  simpa only [expect, h1, h2 u, h2 v] using h

/-- (5) fails on the signed top layer: `X = (1, -1)` on `Bool` makes the
pairing indefinite — `⟨u,v⟩² = 4` against `⟨u,u⟩⟨v,v⟩ = 0`. -/
theorem dist_cauchy_schwarz_fails_signed :
    ∃ (X : RandomSystems.Dist Bool) (u v : Bool → ℝ),
      ¬ ((expect X fun a => u a * v a) ^ 2
          ≤ (expect X fun a => u a ^ 2) * expect X fun a => v a ^ 2) := by
  refine ⟨ofFiniteMassFunction fun b => if b then 1 else -1,
    fun _ => 1, fun b => if b then 1 else -1, ?_⟩
  norm_num [expect, Fintype.sum_bool]

/-! ### (6) Jensen for a concave function — BOTTOM (weight = 1 is load-bearing) -/

theorem dist_jensen_concave {X : RandomSystems.Dist A} (hX : X.isProbDist)
    {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) (f : A → ℝ) :
    expect X (fun a => φ (f a)) ≤ φ (expect X f) := by
  have h := hφ.le_map_sum (t := Finset.univ) (w := fun a => X a) (p := f)
    (fun a _ => hX.1 a)
    (by rw [← Dist.weight_eq_sum]; exact hX.2)
    (fun a _ => trivial)
  simpa [expect, smul_eq_mul] using h

/-- (6) fails at MIDDLE even with `NonNeg`: weight `1/2` on one point, with
the constant concave `φ = -1`.  `E[φ∘f] = -1/2 > -1 = φ(E[f])`. -/
theorem dist_jensen_fails_subprob :
    ∃ (X : RandomSystems.Dist Unit) (φ : ℝ → ℝ) (f : Unit → ℝ),
      X.NonNeg ∧ ConcaveOn ℝ Set.univ φ ∧
      ¬ expect X (fun a => φ (f a)) ≤ φ (expect X f) := by
  refine ⟨ofFiniteMassFunction fun _ => 1 / 2, fun _ => -1, fun _ => 0,
    fun _ => by norm_num, concaveOn_const _ convex_univ, ?_⟩
  norm_num [expect]

/-! ### (7) non-negativity of variance — MIDDLE in the `E[(f-c)²]` form,
BOTTOM in the `E[f²] - E[f]²` form -/

theorem expect_sq_dev_nonneg {X : RandomSystems.Dist A} (hX : X.NonNeg)
    (f : A → ℝ) (c : ℝ) :
    0 ≤ expect X fun a => (f a - c) ^ 2 :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hX a) (sq_nonneg _)

/-- (7) the subtracted form is NOT a MIDDLE-layer fact: at weight 2 it goes
negative.  (At weight 1 the two forms agree, so it is a BOTTOM-layer fact.) -/
theorem variance_sub_form_fails_at_weight_two :
    ∃ (X : RandomSystems.Dist Unit) (f : Unit → ℝ), X.NonNeg ∧
      (expect X fun a => f a ^ 2) - (expect X f) ^ 2 < 0 := by
  refine ⟨ofFiniteMassFunction fun _ => 2, fun _ => 1,
    fun _ => by norm_num, ?_⟩
  norm_num [expect]

/-! ### (8) triangle inequality for `statDist` — TOP.
Already in the library with NO hypotheses (`RandomSystems/StatDist.lean`,
`statDist_triangle`); the receipt: -/

example (X Y Z : RandomSystems.Dist A) :
    statDist X Z ≤ statDist X Y + statDist Y Z :=
  statDist_triangle X Y Z

end P6

/-! ### Entry cost of the measurable-space instances

Any `Fintype` carrier can enter the bridge by TAKING the `⊤` σ-algebra at the
use site: `@DiscreteMeasurableSpace α ⊤` is an instance, and
`DiscreteMeasurableSpace.toMeasurableSingletonClass` (priority 100) supplies
`MeasurableSingletonClass`.  Receipt: -/

example {A : Type*} [Fintype A] (X : RandomSystems.Dist A)
    (hX : X.isProbDist) (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ |f a - expect X f|) ≤ distVar X f / c ^ 2 :=
  letI : MeasurableSpace A := ⊤
  dist_chebyshev X hX f hc

end TransportProbe
