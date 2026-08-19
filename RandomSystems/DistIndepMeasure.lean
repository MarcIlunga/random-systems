/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DistCond
import RandomSystems.DistMeasure
import Mathlib.Probability.Independence.Basic

/-!
# Independence across the transport into mathlib (`DESIGN.md` §12)

`RandomSystems.DistCond` proves the independence *calculus* natively, because
its statements must hold on the tree's main carriers, which are deliberately
**not** `Fintype` (see `Dist.mass_prod_and`).  This module is the other half:
the one-way transport of `Dist.IndepRV` into mathlib's
`ProbabilityTheory.IndepFun`, and the theorems that are only worth importing
through it.

The headline is additivity of variance for a *pairwise* independent family
(`Dist.variance_sum_of_pairwiseIndepRV`), imported from
`ProbabilityTheory.IndepFun.variance_sum`.  Pairwise independence is the
honest hypothesis there — mutual independence is not needed — and it is
exactly what a `k`-wise independent family supplies
(`Dist.kIndepRV_two_iff_pairwiseIndepRV`).

Everything here carries `[Fintype Ω]`, inherited from `Dist.toPMF`; the
measurable-space instances are introduced at the proof site, so the public
statements stay in `Dist`/ℝ vocabulary (`DESIGN.md` §12 point 3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RandomSystems

namespace Dist

section Transport

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Corestriction of a random variable onto its (finite) range, the device that
lets the transport reach codomains with no `MeasurableSingletonClass` — ℝ in
particular. -/
private def rangeFactor {A : Type*} (X : Ω → A) (ω : Ω) : Set.range X :=
  ⟨X ω, Set.mem_range_self ω⟩

/-- Transport of `Dist.IndepRV` into mathlib's `IndepFun`, discrete codomains.

On a countable discrete carrier two measures agree iff they agree on
singletons (`Measure.ext_of_singleton`), and singleton events are exactly what
`Dist.IndepRV` factors, so the σ-algebra-wise obligation collapses to the
library's own pointwise statement. -/
private theorem indepFun_toPMF_of_indepRV_discrete {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B))
    (h : IndepRV p X Y) :
    IndepFun X Y (toPMF p.val p.property).toMeasure := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  refine Measure.ext_of_singleton fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    show ({(a, b)} : Set (A × B)) = {a} ×ˢ {b} from (Set.singleton_prod_singleton).symm,
    Measure.prod_prod,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    show (fun ω => (X ω, Y ω)) ⁻¹' ({a} ×ˢ {b}) = {ω | X ω = a ∧ Y ω = b} by
      ext ω; simp,
    show X ⁻¹' {a} = {ω | X ω = a} by ext ω; simp,
    show Y ⁻¹' {b} = {ω | Y ω = b} by ext ω; simp,
    toPMF_toMeasure_apply, toPMF_toMeasure_apply, toPMF_toMeasure_apply,
    h a b, ENNReal.ofReal_mul (p.property.1.mass_nonneg _)]

/-- **Transport of independence**: two random variables independent in the
library sense are independent in mathlib's sense against the transported
measure, for arbitrary codomains.  A random variable out of a `Fintype` sample
space has finite range, so the discrete case applies after corestriction and is
pushed forward along the (automatically measurable) inclusion. -/
theorem indepFun_toPMF_of_indepRV {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B))
    (h : IndepRV p X Y) :
    IndepFun X Y (toPMF p.val p.property).toMeasure := by
  classical
  letI : MeasurableSpace (Set.range X) := ⊤
  letI : MeasurableSpace (Set.range Y) := ⊤
  haveI : Fintype (Set.range X) := (Set.finite_range X).fintype
  haveI : Fintype (Set.range Y) := (Set.finite_range Y).fintype
  have hF : IndepRV p (rangeFactor X) (rangeFactor Y) := by
    intro a b
    rw [mass_congr _ (Q := fun ω => X ω = ↑a ∧ Y ω = ↑b)
        (fun ω => by simp [rangeFactor, Subtype.ext_iff]),
      mass_congr _ (P := fun ω => rangeFactor X ω = a) (Q := fun ω => X ω = ↑a)
        (fun ω => by simp [rangeFactor, Subtype.ext_iff]),
      mass_congr _ (P := fun ω => rangeFactor Y ω = b) (Q := fun ω => Y ω = ↑b)
        (fun ω => by simp [rangeFactor, Subtype.ext_iff])]
    exact h ↑a ↑b
  exact (indepFun_toPMF_of_indepRV_discrete p (rangeFactor X) (rangeFactor Y) hF).comp
    (Measurable.of_discrete (f := (Subtype.val : Set.range X → A)))
    (Measurable.of_discrete (f := (Subtype.val : Set.range Y → B)))

/-- The library variance is mathlib's variance against the transported
measure — the bridge that carries variance theorems onto `Dist` statements. -/
theorem variance_toPMF_eq_variance (D : Dist Ω) (hD : D.isProbDist) (f : Ω → ℝ) :
    Var[f; (toPMF D hD).toMeasure] = D.variance f := by
  rw [ProbabilityTheory.variance_eq_integral Measurable.of_discrete.aemeasurable,
    integral_toPMF_eq_expect D hD f]
  simpa [variance] using
    integral_toPMF_eq_expect D hD fun a => (f a - D.expect f) ^ 2

/-- Instance-carrying core of `Dist.variance_sum_of_pairwise`. -/
private theorem variance_sum_of_pairwise_aux {ι : Type*} (p : ProbDist Ω)
    (f : ι → Ω → ℝ) (s : Finset ι)
    (h : Set.Pairwise (↑s : Set ι) fun i j => IndepRV p (f i) (f j)) :
    p.val.variance (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, p.val.variance (f i) := by
  have key := ProbabilityTheory.IndepFun.variance_sum
    (μ := (toPMF p.val p.property).toMeasure) (X := f) (s := s)
    (fun i _ => MemLp.of_discrete)
    (fun i hi j hj hij => indepFun_toPMF_of_indepRV p (f i) (f j) (h hi hj hij))
  rw [← variance_toPMF_eq_variance p.val p.property]
  rw [show (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i from
    funext fun ω => (Finset.sum_apply ω s f).symm]
  rw [key]
  exact Finset.sum_congr rfl fun i _ => variance_toPMF_eq_variance p.val p.property (f i)

end Transport

/-- **Variance is additive over a pairwise independent family**
(mathlib: `ProbabilityTheory.IndepFun.variance_sum`).  Pairwise independence —
not mutual independence — is the honest hypothesis; this is the statement the
tree could not make before `Dist.PairwiseIndepRV` existed.

Transported through `Dist.toPMF`; the measurable-space instance (`⊤`) is
introduced at the proof site, so the binders stay in `Dist`/ℝ vocabulary. -/
theorem variance_sum_of_pairwise {Ω ι : Type*} [Fintype Ω] (p : ProbDist Ω)
    (f : ι → Ω → ℝ) (s : Finset ι)
    (h : Set.Pairwise (↑s : Set ι) fun i j => IndepRV p (f i) (f j)) :
    p.val.variance (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, p.val.variance (f i) :=
  letI : MeasurableSpace Ω := ⊤
  variance_sum_of_pairwise_aux p f s h

/-- `Dist.variance_sum_of_pairwise` phrased for a `Dist.PairwiseIndepRV`
family: the variance of any finite sub-sum is the sum of the variances. -/
theorem variance_sum_of_pairwiseIndepRV {Ω ι : Type*} [Fintype Ω] (p : ProbDist Ω)
    (f : ι → RV (Ω := Ω) (A := ℝ)) (s : Finset ι)
    (h : PairwiseIndepRV (A := fun _ => ℝ) p f) :
    p.val.variance (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, p.val.variance (f i) :=
  variance_sum_of_pairwise p f s (h.set_pairwise _)

/-- Variance of a sum of two independent random variables
(mathlib: `ProbabilityTheory.IndepFun.variance_add`), the two-variable case of
`Dist.variance_sum_of_pairwise`. -/
theorem variance_add_of_indepRV {Ω : Type*} [Fintype Ω] (p : ProbDist Ω)
    (f g : RV (Ω := Ω) (A := ℝ)) (h : IndepRV p f g) :
    p.val.variance (fun ω => f ω + g ω)
      = p.val.variance f + p.val.variance g := by
  letI : MeasurableSpace Ω := ⊤
  have key := ProbabilityTheory.IndepFun.variance_fun_add
    (μ := (toPMF p.val p.property).toMeasure) MemLp.of_discrete MemLp.of_discrete
    (indepFun_toPMF_of_indepRV p f g h)
  rw [variance_toPMF_eq_variance, variance_toPMF_eq_variance,
    variance_toPMF_eq_variance] at key
  exact key

end Dist

end RandomSystems
