/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Advantage

/-!
# XOR of Permutations: LM20 Coupling Scaffold

This file is a theorem-first scaffold for the XoP research line.

The north-star theorem is a random-systems security statement:

`Adv(XoPReal, IdealRF) <= bound`.

The current file deliberately does not start from local rank or random-relief
estimates.  Instead, it exposes the proof obligations forced by the top-level
theorem:

1. an LM20 / transcript-distance wrapper;
2. a normalized density-ratio statement `R = Z / E[Z]`;
3. an `L1` transcript-density bound;
4. a pair-Mayer/Penrose expansion before atomization;
5. finite-field rank/codimension estimates;
6. a tilted visible-defect bound under the induced cluster measure.

## Approach Catalogue

The maintained routes to explore are:

* H-coefficient/table-density bounds for fixed input transcripts.
* Hoeffding/ANOVA decomposition in `L1`.
* Pair-Mayer/Penrose cluster expansion before colored-bond atomization.
* Finite-field rank/codimension counting for hidden and visible constraints.
* Dependency-graph/Janson-style tilted visible-defect domination.
* LM20 maximal-coupling wrapper after the transcript bound is proved.
* Creative route: defect-witness transport coupling, where a coupling fails only
  when a minimal visible-defect certificate appears; certificate density is then
  bounded by a rank-sensitive tree expansion.

Forbidden shortcuts, recorded from the research review:

* Do not apply KP directly to raw colored bonds with per-edge activity `1/N`.
* Do not factor tilted visible-defect terms across overlapping supports.
* Do not claim weight-`>1` representatives improve the bound unless the output
  marginal condition is proved.
* Do not treat the LM20 wrapper as the source of the analytic estimate.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP

variable {X Y : Type*} {q : Nat}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- A theorem-facing XoP security instance.

`X` is the query alphabet, `Y` is the output alphabet, and `q` is the fixed query
budget.  The real and ideal systems are intentionally stored as `PDS`s so the
statement plugs directly into the LM20 formalization. -/
structure SecurityInstance (X Y : Type*) (q : Nat)
    [Fintype (DDS X Y q)] where
  /-- Real XoP transcript system, represented as a PDS over DDSs. -/
  real : PDS X Y q
  /-- Ideal random-function transcript system, represented as a PDS over DDSs. -/
  ideal : PDS X Y q
  /-- Claimed transcript/security bound. -/
  bound : NNReal

attribute [nolint docBlame] SecurityInstance

/-- Fixed-input transcript total-variation obligation.

This is the analytic theorem that H-coefficient, ANOVA, and cluster-expansion
work must eventually discharge. -/
def FixedInputTranscriptBound (M : SecurityInstance X Y q) : Prop :=
  ∀ inputs : Fin q → X,
    statDist (M.real.transcriptDist inputs) (M.ideal.transcriptDist inputs) ≤ M.bound

/-- Admissible non-repeating fixed-input query sequences. -/
def InjectiveInputs (inputs : Fin q → X) : Prop :=
  Function.Injective inputs

instance injectiveInputsDecidable : DecidablePred (InjectiveInputs (X := X) (q := q)) :=
  fun _ => Classical.propDecidable _

/-- Injective-input transcript total-variation obligation.

The concrete XoP counting model is currently proved on non-repeating query
sequences.  This obligation is the theorem-facing version of that path.  It
does not replace `FixedInputTranscriptBound`; a repeated-query reduction is
still needed to recover the unrestricted fixed-input statement. -/
def InjectiveInputTranscriptBound (M : SecurityInstance X Y q) : Prop :=
  ∀ inputs : Fin q → X,
    InjectiveInputs inputs →
      statDist (M.real.transcriptDist inputs) (M.ideal.transcriptDist inputs) ≤ M.bound

/-- Adaptive transcript total-variation obligation.

This is the paper-level form, ranging over deterministic discrete environments.
It is stronger than `FixedInputTranscriptBound` unless a separate adaptive bridge
for bounds, not just equivalence, has been proved. -/
def AdaptiveTranscriptBound (M : SecurityInstance X Y q) : Prop :=
  ∀ e : DDE X Y q,
    statDist (M.real.adaptiveTranscriptDist e) (M.ideal.adaptiveTranscriptDist e) ≤ M.bound

/-! ## Named Analytic Proof Obligations -/

/-- The normalized density-ratio obligation.

For XoP, this is intended to become the concrete statement
`R(y) = Z(y) / E_I[Z]` with `E_I[Z] = (N)_q^2 / N^q`, where `Z(y)` counts hidden
states/permutation-pair assignments compatible with transcript `y`. -/
def NormalizedDensityObligation (M : SecurityInstance X Y q) : Prop :=
  ∀ inputs : Fin q → X,
    (M.real.transcriptDist inputs).weight = (M.ideal.transcriptDist inputs).weight

/-- A one-sided density-ratio error certificate for two finite transcript
distributions.

The intended concrete XoP instantiation is:

* `reference = ideal transcript law`;
* `real = XoP transcript law`;
* `density t = Z(t) / E_I[Z]`;
* the final inequality is the `L1`/positive-part estimate obtained from the
  ANOVA or cluster expansion.

This uses LM20's one-sided statistical distance convention
`δ(P,Q)=sum_t (P t - Q t)_+`, so the positive error is exactly the quantity
needed for a transcript-distance bound. -/
def DensityRatioPositiveErrorBound
    {A : Type*} [Fintype A]
  (real reference : Dist A) (density : A → NNReal) (ε : NNReal) : Prop :=
  (∀ a : A, real a = density a * reference a) ∧
  (∑ a : A, max (density a * reference a - reference a) 0) ≤ ε

/-- Density-ratio positive error implies a statistical-distance bound.

This is the formal density-to-TV bridge used by the XoP scaffold.  The hard
research work is to prove the second conjunct of
`DensityRatioPositiveErrorBound` for the concrete XoP density. -/
theorem statDist_le_of_densityRatioPositiveError
    {A : Type*} [Fintype A]
    (real reference : Dist A) (density : A → NNReal) (ε : NNReal)
    (h : DensityRatioPositiveErrorBound real reference density ε) :
    statDist real reference ≤ ε := by
  rcases h with ⟨hreal, hbound⟩
  -- the signed carrier indexes `statDist` by `(X - Y).support`, not `univ`;
  -- `statDist_eq_sum_univ` is the migrated unfolding lemma for `Fintype` carriers
  rw [statDist_eq_sum_univ]
  calc
    (∑ a : A, max (real a - reference a) 0)
        = ∑ a : A, max (density a * reference a - reference a) 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hreal a]
    _ ≤ ε := hbound

/-- Fixed-input density-ratio proof obligation.

This is a more concrete version of the transcript-distance goal: for every
fixed query sequence, exhibit a normalized density of the real transcript law
with respect to the ideal transcript law, and bound its positive error. -/
def FixedInputDensityRatioBound (M : SecurityInstance X Y q) : Prop :=
  ∀ inputs : Fin q → X,
    ∃ density : Transcript X Y q → NNReal,
      DensityRatioPositiveErrorBound
        (M.real.transcriptDist inputs)
        (M.ideal.transcriptDist inputs)
        density
        M.bound

/-- A fixed-input density-ratio certificate gives the fixed-input transcript
bound required by the LM20 wrapper. -/
theorem fixed_transcript_bound_of_densityRatio
    (M : SecurityInstance X Y q)
    (h : FixedInputDensityRatioBound M) :
    FixedInputTranscriptBound M := by
  intro inputs
  rcases h inputs with ⟨density, hdensity⟩
  exact statDist_le_of_densityRatioPositiveError
    (M.real.transcriptDist inputs)
    (M.ideal.transcriptDist inputs)
    density
    M.bound
    hdensity

/-- A normalized counting representation for a real transcript law relative to a
reference transcript law.

For concrete XoP, `count` is intended to be `Z(t)`, the number/mass of hidden
permutation-pair assignments compatible with transcript `t`, and `expected` is
intended to be `E_I[Z] = (N)_q^2 / N^q`.  The induced density is `Z/E_I[Z]`.
-/
structure NormalizedCountingModel
    {A : Type*} [Fintype A]
    (real reference : Dist A) (ε : NNReal) where
  /-- Compatible hidden-state count or mass. -/
  count : A → NNReal
  /-- Reference expectation of `count`. -/
  expected : NNReal
  /-- The normalizer is nonzero. -/
  expected_ne_zero : expected ≠ 0
  /-- Real transcript mass is the normalized count times reference mass. -/
  real_eq_count_density :
    ∀ a : A, real a = (count a / expected) * reference a
  /-- The analytic `L1`/positive-part estimate for the normalized count. -/
  positive_error_le :
    (∑ a : A, max ((count a / expected) * reference a - reference a) 0) ≤ ε

/-- The density induced by a normalized counting model. -/
def NormalizedCountingModel.density
    {A : Type*} [Fintype A]
    {real reference : Dist A} {ε : NNReal}
    (C : NormalizedCountingModel real reference ε) : A → NNReal :=
  fun a => C.count a / C.expected

/-- A normalized counting model gives a density-ratio positive-error
certificate. -/
theorem densityRatioPositiveError_of_normalizedCounting
    {A : Type*} [Fintype A]
    {real reference : Dist A} {ε : NNReal}
    (C : NormalizedCountingModel real reference ε) :
    DensityRatioPositiveErrorBound real reference C.density ε := by
  constructor
  · intro a
    exact C.real_eq_count_density a
  · exact C.positive_error_le

/-- Fixed-input normalized-counting proof obligation.

This is the intended first concrete XoP target: for every fixed query sequence,
construct `Z`, prove the corrected normalizer, prove
`real = (Z/E_I[Z]) * ideal`, and prove the positive-error estimate. -/
def FixedInputCountingDensityBound (M : SecurityInstance X Y q) : Prop :=
  ∀ inputs : Fin q → X,
    ∃ C : NormalizedCountingModel
        (M.real.transcriptDist inputs)
        (M.ideal.transcriptDist inputs)
        M.bound,
      C.expected ≠ 0

/-- Normalized counting certificates imply density-ratio certificates. -/
theorem fixed_densityRatio_of_countingDensity
    (M : SecurityInstance X Y q)
    (h : FixedInputCountingDensityBound M) :
    FixedInputDensityRatioBound M := by
  intro inputs
  rcases h inputs with ⟨C, _⟩
  exact ⟨C.density, densityRatioPositiveError_of_normalizedCounting C⟩

/-- Normalized counting certificates imply the fixed-input transcript bound. -/
theorem fixed_transcript_bound_of_countingDensity
    (M : SecurityInstance X Y q)
    (h : FixedInputCountingDensityBound M) :
    FixedInputTranscriptBound M :=
  fixed_transcript_bound_of_densityRatio M
    (fixed_densityRatio_of_countingDensity M h)

/-- Pair-Mayer/Penrose expansion obligation.

This must expand `Z` using signed pair interactions before any colored-bond
atomization.  The earlier raw-colored-bond KP route is explicitly rejected. -/
def PairMayerPenroseObligation (_M : SecurityInstance X Y q) : Prop :=
  True

/-- Finite-field rank/codimension obligation.

This is the algebraic core: fixed connected constraint systems must contribute
at most their rank/codimension weight, with injectivity corrections accounted
for separately. -/
def RankCodimensionObligation (_M : SecurityInstance X Y q) : Prop :=
  True

/-- Tilted visible-defect obligation.

This must be proved under the cluster/density tilt induced by the expansion, not
by a false raw-product factorization over overlapping visible supports. -/
def TiltedVisibleDefectObligation (_M : SecurityInstance X Y q) : Prop :=
  True

/-- The hard analytic sufficiency theorem.

This is the point where the mathematical proof must eventually combine:
normalization, pair-Mayer/Penrose, rank/codimension, and tilted visible-defect
control into the fixed-input transcript bound.

The proposition is a named theorem target rather than an anonymous assumption so
future work has a stable top-down leaf to refine. -/
def AnalyticObligationsSuffice (M : SecurityInstance X Y q) : Prop :=
  NormalizedDensityObligation M →
  PairMayerPenroseObligation M →
  RankCodimensionObligation M →
  TiltedVisibleDefectObligation M →
  FixedInputTranscriptBound M

/-! ## LM20 / Advantage Wrappers -/

section SecurityWrappers

variable [Fintype X]

/-- Non-adaptive LM20 wrapper.

Once the fixed-input transcript TV bound is proved, the existing
`advantage_le_of_pointwise` theorem immediately gives the random-system security
bound. -/
theorem nonadaptive_security_from_fixed_transcript_bound
    (M : SecurityInstance X Y q)
    (h : FixedInputTranscriptBound M) :
    advantage M.real M.ideal ≤ M.bound :=
  advantage_le_of_pointwise M.real M.ideal M.bound h

/-- Restricted non-adaptive wrapper for non-repeating fixed inputs.

This is the honest endpoint for the current concrete model/counting bridge until
the repeated-query reduction is proved. -/
theorem nonadaptive_securityOn_injective_from_transcript_bound
    (M : SecurityInstance X Y q)
    (h : InjectiveInputTranscriptBound M) :
    advantageOn M.real M.ideal (InjectiveInputs (X := X) (q := q)) ≤ M.bound := by
  exact advantageOn_le_of_pointwise
    M.real M.ideal
    (InjectiveInputs (X := X) (q := q))
    M.bound
    h

section Adaptive

variable [Fintype Y] [DecidableEq Y]

/-- Adaptive LM20 wrapper.

This is the paper-level wrapper when the proof supplies an adaptive transcript
bound directly.  A later task may derive this from fixed-input bounds via a
stronger LM20 theorem, but equivalence alone is not enough for inequalities. -/
theorem adaptive_security_from_adaptive_transcript_bound
    (M : SecurityInstance X Y q)
    (h : AdaptiveTranscriptBound M) :
    advantageAdaptive M.real M.ideal ≤ M.bound :=
  advantageAdaptive_le_of_pointwise M.real M.ideal M.bound h

end Adaptive

/-- Fully proved non-adaptive theorem from the named analytic obligations.

This is the maintained theorem-composition spine.  Future work should replace
the four obligation hypotheses with concrete XoP proofs, but this theorem's
combine step is already closed. -/
theorem xop_nonadaptive_security_from_analytic_obligations
    (M : SecurityInstance X Y q)
    (hSuffices : AnalyticObligationsSuffice M)
    (hNorm : NormalizedDensityObligation M)
    (hMayer : PairMayerPenroseObligation M)
    (hRank : RankCodimensionObligation M)
    (hTilt : TiltedVisibleDefectObligation M) :
    advantage M.real M.ideal ≤ M.bound :=
  nonadaptive_security_from_fixed_transcript_bound M
    (hSuffices hNorm hMayer hRank hTilt)

/-- Main non-adaptive XoP theorem target.

This theorem is intentionally top-down: the final security theorem is proved by
combining named proof obligations.  The hard mathematical leaves remain explicit
arguments rather than hidden local assumptions.
-/
theorem xop_nonadaptive_security_research_target
    (M : SecurityInstance X Y q)
    (hSuffices : AnalyticObligationsSuffice M)
    (hNorm : NormalizedDensityObligation M)
    (hMayer : PairMayerPenroseObligation M)
    (hRank : RankCodimensionObligation M)
    (hTilt : TiltedVisibleDefectObligation M) :
    advantage M.real M.ideal ≤ M.bound :=
  xop_nonadaptive_security_from_analytic_obligations
    M hSuffices hNorm hMayer hRank hTilt

section Adaptive

variable [Fintype Y] [DecidableEq Y]

/-- Fully proved adaptive theorem from an adaptive transcript bound.

This is currently the honest adaptive theorem surface.  Deriving
`AdaptiveTranscriptBound` from fixed-input density estimates is a separate
research obligation. -/
theorem xop_adaptive_security_from_adaptive_transcript_bound
    (M : SecurityInstance X Y q)
    (hAdaptive : AdaptiveTranscriptBound M) :
    advantageAdaptive M.real M.ideal ≤ M.bound :=
  adaptive_security_from_adaptive_transcript_bound M hAdaptive

/-- Main adaptive XoP theorem target.

This keeps the paper-level adaptive theorem visible.  The missing obligation is
not merely the fixed-input density proof; it also includes the adaptive
bound-transfer step, or a direct adaptive transcript analysis. -/
theorem xop_adaptive_security_research_target
    (M : SecurityInstance X Y q)
    (hAdaptive : AdaptiveTranscriptBound M) :
    advantageAdaptive M.real M.ideal ≤ M.bound :=
  adaptive_security_from_adaptive_transcript_bound M hAdaptive

end Adaptive

end SecurityWrappers

end XoP
end Applications
end RandomSystems
