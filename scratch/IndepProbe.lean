/-
IndepProbe.lean — EXPERIMENT, not library code.

Measures whether the `Dist → mathlib` transport (established cheap for
integrability/measurability-shaped side conditions in
`scratch/TransportProbe.lean`) also carries theorems whose side conditions
are INDEPENDENCE-shaped:

  Q1a  Dist.IndepRV  → ProbabilityTheory.IndepFun   (Fintype codomains)
  Q1b  Dist.iIndepRV → ProbabilityTheory.iIndepFun  (Fintype codomains)
  Q1c  the same for arbitrary (e.g. ℝ-valued) codomains via range factoring
  Q2a  IndepFun.variance_add, pulled back to a Dist-side statement
  Q2b  Hoeffding/Chernoff via sub-Gaussian machinery: the ±1-sum
       concentration statement of Lanzenberger ch. 3, Dist-side

Not referenced by any lean_lib target.  Check with
  lake env lean scratch/IndepProbe.lean

Part 0 replicates the P1/P2 bridge from TransportProbe verbatim (scratch
files cannot import each other — no oleans); its cost is ALREADY measured
there and is not part of this experiment's friction count.
-/
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import RandomSystems.Dist
import RandomSystems.StatDist

noncomputable section

open RandomSystems RandomSystems.Dist MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace IndepProbe

variable {Ω : Type*} [Fintype Ω]

/-! ## Part 0: the bridge, replicated from `scratch/TransportProbe.lean`
(already-measured cost; NOT counted as friction of this probe) -/

/-- Transport of a probability `Dist` on a `Fintype` into mathlib's `PMF`. -/
def toPMF (X : RandomSystems.Dist Ω) (hX : X.isProbDist) : PMF Ω :=
  ⟨fun a => ENNReal.ofReal (X a), by
    have hsum : ∑ a, ENNReal.ofReal (X a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hX.1 a), ← Dist.weight_eq_sum,
        hX.2, ENNReal.ofReal_one]
    simpa [hsum] using hasSum_fintype fun a => ENNReal.ofReal (X a)⟩

@[simp]
theorem toPMF_apply (X : RandomSystems.Dist Ω) (hX : X.isProbDist) (a : Ω) :
    toPMF X hX a = ENNReal.ofReal (X a) := rfl

/-- Library-side expectation (the inline spelling used throughout RS). -/
def expect (X : RandomSystems.Dist Ω) (f : Ω → ℝ) : ℝ := ∑ a, X a * f a

/-- Library-side variance in the sum vocabulary. -/
def distVar (X : RandomSystems.Dist Ω) (f : Ω → ℝ) : ℝ :=
  expect X fun a => (f a - expect X f) ^ 2

/-- Expectation of a finite sum of random variables (pure `Finset` algebra). -/
theorem expect_sum {ι : Type*} (X : RandomSystems.Dist Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) :
    expect X (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expect X (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Expectation of a negated random variable. -/
theorem expect_neg (X : RandomSystems.Dist Ω) (f : Ω → ℝ) :
    expect X (fun ω => -f ω) = -expect X f := by
  simp [expect]

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The library expectation IS the Bochner integral against the transported
measure. -/
theorem integral_toPMF (X : RandomSystems.Dist Ω) (hX : X.isProbDist) (f : Ω → ℝ) :
    ∫ a, f a ∂(toPMF X hX).toMeasure = expect X f := by
  rw [PMF.integral_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [toPMF_apply, ENNReal.toReal_ofReal (hX.1 a), smul_eq_mul]

/-- Event mass transports: measure of a set = `ENNReal.ofReal` of `Dist.mass`. -/
theorem toPMF_toMeasure_apply (X : RandomSystems.Dist Ω) (hX : X.isProbDist) (P : Ω → Prop) :
    (toPMF X hX).toMeasure {a | P a} = ENNReal.ofReal (X.mass P) := by
  classical
  rw [show {a | P a} = ↑(Finset.univ.filter P) by ext a; simp,
    PMF.toMeasure_apply_finset, mass_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => by split <;> simp [hX.1 a])]
  simp [Finset.sum_filter, apply_ite ENNReal.ofReal]

/-- `measureReal` version of the event-mass bridge (new here, but bookkeeping
of the SAME kind as TransportProbe's P2: one `toReal_ofReal`). -/
theorem measureReal_toPMF (X : RandomSystems.Dist Ω) (hX : X.isProbDist) (P : Ω → Prop) :
    (toPMF X hX).toMeasure.real {a | P a} = X.mass P := by
  rw [measureReal_def, toPMF_toMeasure_apply,
    ENNReal.toReal_ofReal (hX.1.mass_nonneg P)]

/-! ## Q1a: `Dist.IndepRV → IndepFun`, Fintype codomains.

Route: mathlib characterizes `IndepFun` as an equation between measures
(`indepFun_iff_map_prod_eq_prod_map_map`); on a countable discrete carrier
two measures are equal iff they agree on singletons
(`Measure.ext_of_singleton`), and singleton events are EXACTLY what
`Dist.IndepRV` factors.  So the σ-algebra-wise obligation collapses to the
library's own pointwise statement. -/

theorem indepRV_toPMF {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : ProbDist Ω) (X : Ω → A) (Y : Ω → B) (h : Dist.IndepRV p X Y) :
    IndepFun X Y (toPMF p.val p.property).toMeasure := by
  set μ := (toPMF p.val p.property).toMeasure with hμ
  rw [indepFun_iff_map_prod_eq_prod_map_map
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  refine Measure.ext_of_singleton fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    show ({(a, b)} : Set (A × B)) = {a} ×ˢ {b} from
      (Set.singleton_prod_singleton).symm,
    Measure.prod_prod,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    show (fun ω => (X ω, Y ω)) ⁻¹' ({a} ×ˢ {b}) = {ω | X ω = a ∧ Y ω = b} by
      ext ω; simp,
    show X ⁻¹' {a} = {ω | X ω = a} by ext ω; simp,
    show Y ⁻¹' {b} = {ω | Y ω = b} by ext ω; simp,
    toPMF_toMeasure_apply, toPMF_toMeasure_apply, toPMF_toMeasure_apply,
    h a b, ENNReal.ofReal_mul (p.property.1.mass_nonneg _)]

/-! ## Q1b: `Dist.iIndepRV → iIndepFun`, Fintype codomains.

Same route through `iIndepFun_iff_map_fun_eq_pi_map`.  Note the asymmetry
this kills: `Dist.iIndepRV` only states FULL-tuple factorization, while
mathlib's `iIndepFun` demands factorization over every SUBSET of the index
set; the marginalization argument that closes that gap lives inside
mathlib's iff and is not re-proved here. -/

theorem iIndepRV_toPMF {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSingletonClass (A i)]
    (p : ProbDist Ω) (X : ∀ i, Ω → A i) (h : Dist.iIndepRV p X) :
    iIndepFun X (toPMF p.val p.property).toMeasure := by
  set μ := (toPMF p.val p.property).toMeasure with hμ
  haveI : MeasurableSingletonClass (∀ i, A i) :=
    ⟨fun a => by
      rw [show ({a} : Set (∀ i, A i)) = Set.pi Set.univ (fun i => {a i}) from
        (Set.univ_pi_singleton a).symm]
      exact MeasurableSet.univ_pi fun i => measurableSet_singleton _⟩
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => Measurable.of_discrete.aemeasurable]
  refine Measure.ext_of_singleton fun a => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    show ({a} : Set (∀ i, A i)) = Set.pi Set.univ (fun i => {a i}) from
      (Set.univ_pi_singleton a).symm,
    Measure.pi_pi,
    show (fun ω i => X i ω) ⁻¹' Set.pi Set.univ (fun i => {a i})
        = {ω | ∀ i, X i ω = a i} by ext ω; simp [Set.mem_pi],
    toPMF_toMeasure_apply, h a,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => p.property.1.mass_nonneg _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    show X i ⁻¹' {a i} = {ω | X i ω = a i} by ext ω; simp,
    toPMF_toMeasure_apply]

/-! ## Q1c: arbitrary codomains (e.g. ℝ with Borel) via range factoring.

`Measure.ext_of_singleton` is unavailable for codomain ℝ (not countable),
but any RV out of a `Fintype` sample space has finite range: corestrict onto
`Set.range X` carrying the `⊤` σ-algebra, transport with Q1a/Q1b there, and
push forward along the (automatically measurable) inclusion with
`IndepFun.comp` / `iIndepFun.comp`. -/

/-- Corestriction of a random variable onto its range. -/
def rangeFactor {A : Type*} (X : Ω → A) (ω : Ω) : Set.range X :=
  ⟨X ω, Set.mem_range_self ω⟩

theorem indepRV_toPMF' {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (p : ProbDist Ω) (X : Ω → A) (Y : Ω → B) (h : Dist.IndepRV p X Y) :
    IndepFun X Y (toPMF p.val p.property).toMeasure := by
  classical
  letI : MeasurableSpace (Set.range X) := ⊤
  letI : MeasurableSpace (Set.range Y) := ⊤
  haveI : Fintype (Set.range X) := (Set.finite_range X).fintype
  haveI : Fintype (Set.range Y) := (Set.finite_range Y).fintype
  have hF : Dist.IndepRV p (rangeFactor X) (rangeFactor Y) := by
    intro a b
    have e1 : p.val.mass (fun ω => rangeFactor X ω = a ∧ rangeFactor Y ω = b)
        = p.val.mass (fun ω => X ω = ↑a ∧ Y ω = ↑b) :=
      mass_congr _ fun ω => by simp [rangeFactor, Subtype.ext_iff]
    have e2 : p.val.mass (fun ω => rangeFactor X ω = a)
        = p.val.mass (fun ω => X ω = ↑a) :=
      mass_congr _ fun ω => by simp [rangeFactor, Subtype.ext_iff]
    have e3 : p.val.mass (fun ω => rangeFactor Y ω = b)
        = p.val.mass (fun ω => Y ω = ↑b) :=
      mass_congr _ fun ω => by simp [rangeFactor, Subtype.ext_iff]
    rw [e1, e2, e3]
    exact h ↑a ↑b
  exact (indepRV_toPMF p (rangeFactor X) (rangeFactor Y) hF).comp
    (Measurable.of_discrete (f := (Subtype.val : Set.range X → A)))
    (Measurable.of_discrete (f := (Subtype.val : Set.range Y → B)))

theorem iIndepRV_toPMF' {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)]
    (p : ProbDist Ω) (X : ∀ i, Ω → A i) (h : Dist.iIndepRV p X) :
    iIndepFun X (toPMF p.val p.property).toMeasure := by
  classical
  letI : ∀ i, MeasurableSpace (Set.range (X i)) := fun _ => ⊤
  haveI : ∀ i, Fintype (Set.range (X i)) := fun i => (Set.finite_range (X i)).fintype
  have hF : Dist.iIndepRV p (fun i => rangeFactor (X i)) := by
    intro a
    have e0 : p.val.mass (fun ω => ∀ i, rangeFactor (X i) ω = a i)
        = p.val.mass (fun ω => ∀ i, X i ω = ↑(a i)) :=
      mass_congr _ fun ω => by simp [rangeFactor, Subtype.ext_iff]
    rw [e0, h fun i => ↑(a i)]
    exact Finset.prod_congr rfl fun i _ =>
      (mass_congr _ fun ω => by simp [rangeFactor, Subtype.ext_iff]).symm
  exact (iIndepRV_toPMF p (fun i => rangeFactor (X i)) hF).comp
    (fun i => (Subtype.val : Set.range (X i) → A i))
    (fun i => Measurable.of_discrete)

/-! ## Q2a: variance of a sum under independence, Dist-side -/

/-- `Var[f; transported μ] = distVar` — same bridging shape as
TransportProbe's P3 (`variance_eq_integral` + the integral bridge). -/
theorem variance_toPMF (p : ProbDist Ω) (f : Ω → ℝ) :
    Var[f; (toPMF p.val p.property).toMeasure] = distVar p.val f := by
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable,
    integral_toPMF p.val p.property f]
  simpa [distVar] using
    integral_toPMF p.val p.property fun a => (f a - expect p.val f) ^ 2

/-- **Q2a headline**: variance is additive over independent random variables,
stated purely on the library side (`Dist.IndepRV`, `distVar`).  Transported
from `ProbabilityTheory.IndepFun.variance_add`; both `MemLp` side conditions
are `.of_discrete`. -/
theorem dist_variance_add (p : ProbDist Ω) (f g : Ω → ℝ)
    (h : Dist.IndepRV p f g) :
    distVar p.val (fun ω => f ω + g ω) = distVar p.val f + distVar p.val g := by
  have hv := IndepFun.variance_add (μ := (toPMF p.val p.property).toMeasure)
    MemLp.of_discrete MemLp.of_discrete (indepRV_toPMF' p f g h)
  rw [variance_toPMF, variance_toPMF, variance_toPMF] at hv
  exact hv

/-! ## Q2b workhorses: transported one-sided Hoeffding tails.

`measure_sum_ge_le_of_iIndepFun` (mathlib's Hoeffding inequality for
sub-Gaussian sums) + `hasSubgaussianMGF_of_mem_Icc` (Hoeffding's lemma),
entered through Q1c and the integral bridge. -/

/-- Upper tail: independent coordinates each bounded in `[a, b]`,
mean-centered.  The sub-Gaussian parameter `((b-a)/2)²` per coordinate is
mathlib's Hoeffding-lemma constant. -/
theorem measureReal_tail_of_iIndepRV {m : ℕ} (p : ProbDist Ω)
    (X : Fin m → Ω → ℝ) {a b : ℝ} (hb : ∀ i ω, X i ω ∈ Set.Icc a b)
    (hind : Dist.iIndepRV p X) {ε : ℝ} (hε : 0 ≤ ε) :
    (toPMF p.val p.property).toMeasure.real
        {ω | ε ≤ ∑ i, (X i ω - expect p.val (X i))}
      ≤ Real.exp (-ε ^ 2 / (2 * m * (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  set μ := (toPMF p.val p.property).toMeasure with hμ
  set c : ℝ≥0 := (‖b - a‖₊ / 2) ^ 2 with hc
  have hYind : iIndepFun (fun i ω => X i ω - expect p.val (X i)) μ := by
    have h0 := (iIndepRV_toPMF' p X hind).comp
      (fun i x => x - expect p.val (X i))
      (fun i => measurable_id.sub_const _)
    simpa [Function.comp] using h0
  have hSG : ∀ i, HasSubgaussianMGF (fun ω => X i ω - expect p.val (X i)) c μ := by
    intro i
    have h0 := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X i) (a := a) (b := b)
      Measurable.of_discrete.aemeasurable (ae_of_all _ fun ω => hb i ω)
    rwa [integral_toPMF p.val p.property (X i)] at h0
  have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind
    (s := Finset.univ) (fun i _ => hSG i) hε
  refine key.trans_eq ?_
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast [nsmul_eq_mul]
  ring

/-- Lower tail, by negating the coordinates.  The Dist-side independence of
the negated family is one `mass_congr` per event. -/
theorem measureReal_tail_lower_of_iIndepRV {m : ℕ} (p : ProbDist Ω)
    (X : Fin m → Ω → ℝ) {a b : ℝ} (hb : ∀ i ω, X i ω ∈ Set.Icc a b)
    (hind : Dist.iIndepRV p X) {ε : ℝ} (hε : 0 ≤ ε) :
    (toPMF p.val p.property).toMeasure.real
        {ω | ε ≤ ∑ i, (expect p.val (X i) - X i ω)}
      ≤ Real.exp (-ε ^ 2 / (2 * m * (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  have hind' : Dist.iIndepRV p (fun i ω => -X i ω) := by
    intro v
    have e0 : p.val.mass (fun ω => ∀ i, -X i ω = v i)
        = p.val.mass (fun ω => ∀ i, X i ω = -v i) :=
      mass_congr _ fun ω => by simp [neg_eq_iff_eq_neg]
    rw [e0, hind fun i => -v i]
    exact Finset.prod_congr rfl fun i _ =>
      (mass_congr _ fun ω => by simp [neg_eq_iff_eq_neg]).symm
  have hb' : ∀ i ω, -X i ω ∈ Set.Icc (-b) (-a) := fun i ω =>
    ⟨neg_le_neg (hb i ω).2, neg_le_neg (hb i ω).1⟩
  have key := measureReal_tail_of_iIndepRV p (fun i ω => -X i ω) hb' hind' hε
  have hev : {ω | ε ≤ ∑ i, (-X i ω - expect p.val (fun ω => -X i ω))}
      = {ω | ε ≤ ∑ i, (expect p.val (X i) - X i ω)} := by
    ext ω
    have : ∀ i, -X i ω - expect p.val (fun ω => -X i ω)
        = expect p.val (X i) - X i ω := fun i => by
      rw [expect_neg]; ring
    simp only [Set.mem_setOf_eq]
    rw [Finset.sum_congr rfl fun i _ => this i]
  have hnorm : ‖-a - -b‖₊ = ‖b - a‖₊ := by
    rw [show -a - -b = b - a by ring]
  rw [hev, hnorm] at key
  exact key

end IndepProbe

/-! ## Q2b headlines — fresh namespace scope: the statements carry NO
measure-theoretic binders (`[Fintype Ω]` and the library's own vocabulary
only; the σ-algebra is taken as `⊤` at the proof site, per DESIGN.md §12
consequence 3). -/

namespace IndepProbe

section Headline

variable {Ω : Type*} [Fintype Ω]

/-- **Q2b headline, two-sided**: for a sum `S` of `m` independent `±1`
variables, `Pr[λm ≤ |S − E[S]|] ≤ 2·exp(−λ²m/2)` — the Lanzenberger ch. 3
shape, stated purely on the library side. -/
theorem dist_hoeffding_pm_one {m : ℕ} (p : ProbDist Ω)
    (X : Fin m → Ω → ℝ) (hb : ∀ i ω, X i ω = 1 ∨ X i ω = -1)
    (hind : Dist.iIndepRV p X) {lam : ℝ} (hlam : 0 ≤ lam) :
    p.val.mass (fun ω =>
        lam * m ≤ |(∑ i, X i ω) - expect p.val (fun ω => ∑ i, X i ω)|)
      ≤ 2 * Real.exp (-(lam ^ 2 * m) / 2) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  have hIcc : ∀ i ω, X i ω ∈ Set.Icc (-1 : ℝ) 1 := fun i ω => by
    rcases hb i ω with h | h <;> simp [h]
  have hε : (0:ℝ) ≤ lam * m := mul_nonneg hlam (Nat.cast_nonneg m)
  have hup := measureReal_tail_of_iIndepRV p X hIcc hind hε
  have hlo := measureReal_tail_lower_of_iIndepRV p X hIcc hind hε
  have hc : (((‖(1:ℝ) - -1‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 := by norm_num
  have hexp : -(lam * (m:ℝ)) ^ 2 / (2 * (m:ℝ) * 1) = -(lam ^ 2 * (m:ℝ)) / 2 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      field_simp
  rw [hc, hexp] at hup hlo
  have hidU : ∀ ω, (∑ i, X i ω) - expect p.val (fun ω => ∑ i, X i ω)
      = ∑ i, (X i ω - expect p.val (X i)) := fun ω => by
    rw [expect_sum p.val Finset.univ X]
    exact (Finset.sum_sub_distrib _ _).symm
  rw [← measureReal_toPMF p.val p.property]
  have hsub : {ω | lam * (m:ℝ) ≤ |(∑ i, X i ω) - expect p.val (fun ω => ∑ i, X i ω)|}
      ⊆ {ω | lam * (m:ℝ) ≤ ∑ i, (X i ω - expect p.val (X i))}
        ∪ {ω | lam * (m:ℝ) ≤ ∑ i, (expect p.val (X i) - X i ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h | h
    · left
      show lam * (m:ℝ) ≤ ∑ i, (X i ω - expect p.val (X i))
      rw [← hidU ω]
      exact h
    · right
      show lam * (m:ℝ) ≤ ∑ i, (expect p.val (X i) - X i ω)
      have h2 : lam * (m:ℝ)
          ≤ -((∑ i, X i ω) - expect p.val (fun ω => ∑ i, X i ω)) := h
      rw [hidU ω, ← Finset.sum_neg_distrib] at h2
      simpa [neg_sub] using h2
  calc (toPMF p.val p.property).toMeasure.real
        {a | lam * (m:ℝ) ≤ |(∑ i, X i a) - expect p.val (fun ω => ∑ i, X i ω)|}
      ≤ (toPMF p.val p.property).toMeasure.real
          ({ω | lam * (m:ℝ) ≤ ∑ i, (X i ω - expect p.val (X i))}
            ∪ {ω | lam * (m:ℝ) ≤ ∑ i, (expect p.val (X i) - X i ω)}) :=
        measureReal_mono hsub
    _ ≤ (toPMF p.val p.property).toMeasure.real
          {ω | lam * (m:ℝ) ≤ ∑ i, (X i ω - expect p.val (X i))}
        + (toPMF p.val p.property).toMeasure.real
          {ω | lam * (m:ℝ) ≤ ∑ i, (expect p.val (X i) - X i ω)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(lam ^ 2 * (m:ℝ)) / 2) + Real.exp (-(lam ^ 2 * (m:ℝ)) / 2) :=
        add_le_add hup hlo
    _ = 2 * Real.exp (-(lam ^ 2 * (m:ℝ)) / 2) := by ring

/-- **Q2b headline, one-sided**: for a sum `S` of `m` independent
`[0,1]`-valued variables, `Pr[S ≤ E[S] − αm] ≤ exp(−2α²m)` — the one-sided
Lanzenberger ch. 3 shape with its constant (the `exp(−2α²m)` constant is the
`[0,1]` Hoeffding constant; for `±1` variables the honest constant is
`exp(−α²m/2)`, see `dist_hoeffding_pm_one`). -/
theorem dist_hoeffding_le_01 {m : ℕ} (p : ProbDist Ω)
    (X : Fin m → Ω → ℝ) (hb : ∀ i ω, X i ω ∈ Set.Icc (0:ℝ) 1)
    (hind : Dist.iIndepRV p X) {α : ℝ} (hα : 0 ≤ α) :
    p.val.mass (fun ω =>
        (∑ i, X i ω) ≤ expect p.val (fun ω => ∑ i, X i ω) - α * m)
      ≤ Real.exp (-2 * α ^ 2 * m) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  have hε : (0:ℝ) ≤ α * m := mul_nonneg hα (Nat.cast_nonneg m)
  have hlo := measureReal_tail_lower_of_iIndepRV p X hb hind hε
  have hc : (((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by norm_num
  have hexp : -(α * (m:ℝ)) ^ 2 / (2 * (m:ℝ) * (1 / 4)) = -2 * α ^ 2 * (m:ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      field_simp
      ring
  rw [hc, hexp] at hlo
  rw [← measureReal_toPMF p.val p.property]
  refine le_trans (measureReal_mono ?_) hlo
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hidL : expect p.val (fun ω => ∑ i, X i ω) - ∑ i, X i ω
      = ∑ i, (expect p.val (X i) - X i ω) := by
    rw [expect_sum p.val Finset.univ X]
    exact (Finset.sum_sub_distrib _ _).symm
  rw [← hidL]
  linarith

end Headline

/-! ## Q3: Kullback–Leibler divergence.

mathlib's `klDiv` sits on `Measure` behind two side conditions of a NEW kind
for this probe: absolute continuity `μ ≪ ν` and integrability of the
log-likelihood ratio, with the value computed through `Measure.rnDeriv`.
Measured here: on the discrete carrier, (i) the transported measure IS a
`withDensity` of the transported base — one singleton-ext computation — which
makes `≪` a one-liner and pins `rnDeriv` a.e. by `rnDeriv_withDensity`;
(ii) integrability is `.of_finite`; (iii) the value collapses to the finite
discrete formula. -/

section Q3

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Dist-side KL divergence: the discrete formula
`∑ a, X a · log (X a / Y a)` (`0·log(0/y) = 0` handled by `0 * _ = 0`). -/
def distKL (X Y : RandomSystems.Dist Ω) : ℝ :=
  ∑ a, X a * Real.log (X a / Y a)

/-- Singleton mass of the transported measure. -/
theorem toPMF_toMeasure_singleton (X : RandomSystems.Dist Ω) (hX : X.isProbDist)
    (a : Ω) : (toPMF X hX).toMeasure {a} = ENNReal.ofReal (X a) := by
  classical
  rw [show ({a} : Set Ω) = {x | x = a} by ext x; simp,
    toPMF_toMeasure_apply, mass_eq_sum]
  simp

/-- The crux of Q3: under pointwise absolute continuity the transported `X`
is a density against the transported `Y` — with density the pointwise ratio.
One `ext_of_singleton`, one `lintegral_singleton`, one `ofReal_mul`. -/
theorem toPMF_toMeasure_eq_withDensity (X Y : RandomSystems.Dist Ω)
    (hX : X.isProbDist) (hY : Y.isProbDist) (hac : ∀ a, Y a = 0 → X a = 0) :
    (toPMF X hX).toMeasure
      = (toPMF Y hY).toMeasure.withDensity
          (fun a => ENNReal.ofReal (X a / Y a)) := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
    toPMF_toMeasure_singleton, toPMF_toMeasure_singleton]
  by_cases h0 : Y a = 0
  · simp [h0, hac a h0]
  · rw [← ENNReal.ofReal_mul (div_nonneg (hX.1 a) (hY.1 a)),
      div_mul_cancel₀ _ h0]

/-- **Q3 headline**: mathlib's `klDiv` of the transported measures IS the
discrete KL formula (as `ENNReal.ofReal`), given pointwise absolute
continuity `Y a = 0 → X a = 0`. -/
theorem klDiv_toPMF (X Y : RandomSystems.Dist Ω) (hX : X.isProbDist)
    (hY : Y.isProbDist) (hac : ∀ a, Y a = 0 → X a = 0) :
    InformationTheory.klDiv (toPMF X hX).toMeasure (toPMF Y hY).toMeasure
      = ENNReal.ofReal (distKL X Y) := by
  classical
  set μ := (toPMF X hX).toMeasure with hμ
  set ν := (toPMF Y hY).toMeasure with hν
  have hdens : μ = ν.withDensity (fun a => ENNReal.ofReal (X a / Y a)) :=
    toPMF_toMeasure_eq_withDensity X Y hX hY hac
  have hAC : μ ≪ ν := hdens ▸ withDensity_absolutelyContinuous ν _
  have hint : Integrable (llr μ ν) μ := .of_finite
  have hrn : μ.rnDeriv ν =ᵐ[μ] fun a => ENNReal.ofReal (X a / Y a) := by
    have h1 : μ.rnDeriv ν =ᵐ[ν] fun a => ENNReal.ofReal (X a / Y a) := by
      conv_lhs => rw [hdens]
      exact Measure.rnDeriv_withDensity ν Measurable.of_discrete
    exact h1.filter_mono hAC.ae_le
  have hllr : llr μ ν =ᵐ[μ] fun a => Real.log (X a / Y a) := by
    filter_upwards [hrn] with a ha
    show Real.log (μ.rnDeriv ν a).toReal = _
    rw [ha, ENNReal.toReal_ofReal (div_nonneg (hX.1 a) (hY.1 a))]
  rw [InformationTheory.klDiv_of_ac_of_integrable hAC hint,
    integral_congr_ae hllr, integral_toPMF X hX]
  simp [distKL, expect, probReal_univ]

end Q3

end IndepProbe
