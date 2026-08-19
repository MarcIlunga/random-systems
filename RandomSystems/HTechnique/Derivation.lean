/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18Names
import RandomSystems.DistExpect
import RandomSystems.AdaptiveLawBridge
import RandomSystems.BoundedEnvironment
import RandomSystems.CR18Tactics
import RandomSystems.FunctionEvaluator
import RandomSystems.QueryCompression
import RandomSystems.Counting
import RandomSystems.HTechnique.HashThenPRF
import RandomSystems.HTechnique.SecurityDefs
import RandomSystems.FilterDomNormalization

/-!
# The H-technique, derived (high-level tooling, no applications)

Self-contained derivation of the H-coefficient technique on the law-level
random-systems surface, following the chain of `DESIGN.md` §9 (thesis
references: Lanzenberger, Defs 2.9–2.19, Lemma 2.18/App. A.1, Def 2.26,
Thm 2.31).

Notation used in the docstrings below (Unicode, so it renders in-editor):

* `S, T` — law-level systems (`ProbPDS`); in factorization lemmas `R` = real, `I` = ideal;
* `tr(S,E)` — the length-`q` transcript distribution of `S` against a
  deterministic environment `E` (`deterministicTranscriptDist`);
* `tr(S,xs)` — its non-adaptive special case for the fixed query tuple `xs`
  (`fixedQueryTranscriptDist`); at the transcript `t = (xs, ys)` this is the
  *system factor* `σ_S(xs,ys) = S{s : ∀ i, s(xs₁…xsᵢ) = ysᵢ}`;
* `δ(·,·)` — statistical distance (`statDist`);
  `Pr_P[B]` — mass of the event `B` under `P` (`probBad`);
* `Adv_q(S,T) = sup_E δ(tr(S,E), tr(T,E))` — the thesis Def 2.26 advantage,
  over deterministic `q`-query-total environments
  (`adaptiveTranscriptAdvantage`; deterministic is WLOG).

The derivation layers:

* **Layer A (objects)** — the existing core objects above; nothing re-defined.
* **Layer B (adversary factorization)** — for deterministic `E`,
  `tr(S,E)(t) = 𝟙[E consistent with t] · σ_S(t)` (thesis App. A.1; CR18
  Lemma 3.2), so pointwise hypotheses gated by a good-transcript predicate
  transfer from fixed-query to arbitrary environments.
* **Layer C** — the distribution-level H-lemmas from `RandomSystems.StatDist`
  (`hTechnique_ratio`, `hTechnique_eq_on_good`, `hTechnique_expectation`),
  reused verbatim.
* **Layer D** — the adaptive H-technique: ratio, equality-on-good,
  expectation-method, and perfect forms; plus the (★) identity
  `δ(tr(S,E), tr(T,E)) = Σ_t (σ_S(t) − σ_T(t))·η_E(t)` with named
  `sysFactor`/`envFactor`.
* **Layer D′ (generalized H-lemma)** — the Chen–Steinberger partition form
  `δ ≤ Σ_i ε_i·Pr[cell = i]`, derived from the expectation form; good/bad is
  the two-cell special case (`hTechnique_ratio_via_partition`).
* **Layer E (extended transcripts)** — extension-as-data: any `tr⁺(S,E)` on
  transcripts × `Z` with `fst_* tr⁺(S,E) = tr(S,E)` can only increase `δ`
  (thesis Lemma 2.7, data processing), so the H-technique runs on the
  extended space.
* **Layer E′ (σ⁺ fixed-query refinement)** — the canonical extension from a
  revealed-information map `aug : DDS → Z`, with `tr⁺(S,aug,E)(t,z) =
  σ⁺_S(t,z)·η_E(t)`; its H-technique hypotheses reduce to fixed-query form.
* **Layer E″ (representative extensions)** — reveals as functions of the
  **sample and the transcript**, `aug : Ω → Transcript → Z`, for a law
  presented by a representative `(Ω, p, F)`; subsumes E′ (Ω := DDS, F := id)
  and expresses sample-level reveals (hash keys) and transcript-dependent
  ones (HCTR2's internal wire values); randomized reveals via coin-enlarged
  representatives.
* **Layer F (fundamental theorem, lower bound)** — thesis Thm 2.31 `≤`:
  `Adv_q(S,T) ≤ δ_law(S′,T′)` for every `q`-equivalent representative pair
  (hence `Adv ≤ Δ_q`), and the Thm 2.32 coupling reading
  `Adv_q(S,T) ≤ Pr_J[s ≠ s′]`.  The attainment direction (successor
  induction, Lemma 2.33) is recorded in `DESIGN.md` §9, not formalized.
* **Layer A′ (environment duality)** — the chooser chart: `q`-query-total
  environments are (for `q`-round purposes exactly) chooser families; the
  environment supremum equals the chooser supremum.
* **Layer G (stress tests)** — the adaptive PRF/PRP switching lemma
  `Adv[q](urf, urp) ≤ q(q−1)/2N` via the perfect form (**no bad event**:
  with `urp` as ideal, collision transcripts have zero ideal mass); the
  PRP/PRF direction via `Adv`-symmetry of total systems (the H-technique
  itself is not symmetric); hash-then-PRF restated and composed with the
  fixed-query switching bound.

The residual adaptivity is isolated in exactly one hypothesis: the
bad-transcript mass `Pr_{tr(T,E)}[Bad]` is bounded *uniformly over
environments*; everything else is checked non-adaptively.
-/

noncomputable section

open scoped BigOperators NNReal RandomSystems.CR18

namespace RandomSystems.CR18
namespace HTechniqueDerivation

open RandomSystems (statDist probBad Dist)
open PFunDDS (DDS DDE)
open PFunPDS.Prob (deterministicTranscriptDist fixedQueryTranscriptDist
  transcriptDist transcriptDist_ofDDE transcriptDist_weight_eq_one_of_total
  adaptiveTranscriptAdvantage adaptiveTranscriptAdvantage_le_of_pointwise
  adaptiveTranscriptAdvantage_nonneg
  deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
  boundedAdaptiveTranscriptAdvantage
  boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage
  boundedAdaptiveTranscriptAdvantage_image_bddAbove)
open PFunPDE (transcriptLaw deterministicTranscriptLaw
  deterministicTranscriptLawDist deterministicTranscriptLawDist_apply
  transcriptSystemFactor transcriptEnvironmentFactor
  transcriptSystemEvent transcriptEnvironmentEvent transcriptJointEvent_unique
  transcriptLaw_eq_systemFactor_mul_environmentFactor)
open PFunPDE.Prob (ofDDE ofDDE_KQueryTotal)

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- The tautological system representative: the law's own carrier with the
identity random variable (the V1↔V2 bridge, inlined). -/
abbrev idSysRV : PFunPDS.RV (DDS X Y) X Y := fun s => s

/-- The tautological environment representative (identity RV over `DDE`). -/
abbrev idEnvRV : PFunPDE.RV (DDE X Y) X Y := fun e => e

/-- A deterministic environment as a one-point environment RV. -/
abbrev constEnvRV (E : DDE X Y) : PFunPDE.RV PUnit.{1} X Y := fun _ => E

/-! ### Notation

Scoped notation (active on `open RandomSystems.CR18.HTechniqueDerivation`),
matching the docstring mathematics:

    δ(P, Q)              statistical distance        (`statDist`)
    δˡ(P, Q)             law distance                (`lawStatDist`, any carrier)
    Pr[B ∣ P]            mass of event B under P     (`probBad`)
    tr[q](S, E)          transcript distribution     (`deterministicTranscriptDist`)
    tr(S, xs)            fixed-query special case    (`fixedQueryTranscriptDist`)
    tr⁺[q](S, aug, E)    extended transcript dist    (`extendedDeterministicTranscriptDist`)
    tr⁺(S, aug, xs)      extended fixed-query        (`extFixedQueryTranscriptDist`)
    σ(S) t, η(E) t       system/environment factor   (`sysFactor`, `envFactor`)
    σ⁺(S, aug) tz        extended system factor      (`extSysFactor`)
    Adv[q](S, T)         adaptive advantage          (`adaptiveTranscriptAdvantage`)
    Δ[q](S, T)           inf over representatives    (`lawDelta`)
    trˡ[q](S, E)         transcript law, E : DDE     (`deterministicTranscriptLaw`)
    trᵖ[q](S, E)         transcript law, E : ProbPDE (`Prob.transcriptLaw`)
    idSysRV, idEnvRV     tautological representative RVs (identity)
    constEnvRV E         deterministic E as a one-point environment RV
    Advᶜ[q](S, T)        chooser-family advantage    (`boundedAdaptiveTranscriptAdvantage`)
    E ⊨ t                E consistent with t         (`EnvConsistent`)
    s ⊩ t                s realizes t                (`SysConsistent`)
    π₁⋆ P                pushforward along fst       (`Dist.fTransform Prod.fst`)
-/

@[inherit_doc statDist]
scoped notation:max "δ(" P ", " Q ")" => statDist P Q

@[inherit_doc probBad]
scoped notation:max "Pr[" B:51 " ∣ " P:51 "]" => probBad P B

@[inherit_doc deterministicTranscriptDist]
scoped notation:max "tr[" q "](" S ", " E ")" =>
  deterministicTranscriptDist (q := q) S E

@[inherit_doc fixedQueryTranscriptDist]
scoped notation:max "tr(" S ", " xs ")" =>
  fixedQueryTranscriptDist S xs

@[inherit_doc adaptiveTranscriptAdvantage]
scoped notation:max "Adv[" q "](" S ", " T ")" =>
  adaptiveTranscriptAdvantage (q := q) S T

@[inherit_doc deterministicTranscriptLaw]
scoped notation:max "trˡ[" q "](" S ", " E ")" =>
  deterministicTranscriptLaw S E q

@[inherit_doc PFunPDS.Prob.transcriptLaw]
scoped notation:max "trᵖ[" q "](" S ", " E ")" =>
  PFunPDS.Prob.transcriptLaw S E q

@[inherit_doc boundedAdaptiveTranscriptAdvantage]
scoped notation:max "Advᶜ[" q "](" S ", " T ")" =>
  boundedAdaptiveTranscriptAdvantage (q := q) S T

/-- Pushforward along the first projection. -/
scoped prefix:max "π₁⋆" => Dist.fTransform Prod.fst

/-- `s` realizes the transcript `t`: the system-side rectangle event
`∀ i, s(xs₁…xsᵢ) = ysᵢ` (CR18 Lemma 3.2, system conjunct). -/
abbrev SysConsistent (t : TranscriptPrefix X Y q) (s : DDS X Y) : Prop := transcriptSystemEvent
    idSysRV t.1 t.2 s

@[inherit_doc SysConsistent]
scoped notation:50 s:51 " ⊩ " t:51 => SysConsistent t s

/-! ## Layer B — adversary factorization, good-transcript form

The unpredicated version is `transcriptLaw_ratio_of_fixedQuery_ratio_law`
(`AdaptiveLawBridge`).  The bad-event refinement below is the same
factorization argument: at a fixed transcript `t`, the transcript mass under
*any* environment is `σ_S(t) · η_E(t)` with the environment factor `η_E`
common to both systems, so a ratio hypothesis *at the same `t`* — in
particular one gated by `t ∉ Bad` — transfers verbatim.  This is the formal content of "the adversary factors out":
pointwise hypotheses are non-adaptively checkable. -/

/-- **Thesis App. A.1 / CR18 Lemma 3.2, good-transcript form.**

    (∀ xs, ∀ t ∉ Bad :  (1 − ε)·tr(I,xs)(t) ≤ tr(R,xs)(t))
        ⟹   ∀ t ∉ Bad :  (1 − ε)·tr(I,E)(t) ≤ tr(R,E)(t)

for *every* law-level environment `E` (`ProbPDE`): a fixed-query
(non-adaptive) pointwise ratio on good transcripts transfers to arbitrary
environments, at every good transcript. -/
theorem transcriptLaw_ratio_of_fixedQuery_ratio_of_good
    (R I : ProbPDS X Y)
    (E : ProbPDE X Y)
    (Bad : TranscriptPrefix X Y q → Prop)
    (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q), ¬ Bad t →
      (1 - eps) * trˡ[q](I, fixedQueryDDE (Y := Y) xs) t ≤ trˡ[q](R, fixedQueryDDE (Y := Y) xs) t)
    (t : TranscriptPrefix X Y q) (h_good : ¬ Bad t) :
    (1 - eps) * trᵖ[q](I, E) t ≤ trᵖ[q](R, E) t := by
  -- Write the transcript as `t = (xs, ys)` (input vector, output vector).
  rcases t with ⟨xv, yv⟩
  -- `xs` := the input vector of `t`, viewed as a query tuple — the
  -- fixed-query environment replaying exactly the inputs of `t`
  -- (thesis A.1: "let e′ query the inputs of t").
  let xs : Fin q → X := functionOfVector xv
  -- Core step — the ratio holds for the SYSTEM FACTORS:
  --   (1 − ε) · σ_I(xs, ys) ≤ σ_R(xs, ys),
  -- because at the transcript `t` itself the fixed-query masses ARE the
  -- system factors: tr(S, xs)(t) = σ_S(xs, ys)  (thesis A.1 observation).
  have h_sys :
      (1 - eps) * transcriptSystemFactor I idSysRV xv yv ≤ transcriptSystemFactor R idSysRV
          xv yv := by
    -- tr(I, xs)(xs, ys) = σ_I(xs, ys): the fixed-query transcript mass at its
    -- own query tuple is exactly the system-side event mass
    -- I{s : ∀ i ≤ q, s(x₁…xᵢ) = yᵢ}.
    have hI :
        trˡ[q](I, fixedQueryDDE (Y := Y) xs) (xv, yv) = transcriptSystemFactor I idSysRV
            xv yv := by
      simpa [deterministicTranscriptLaw, fixedQueryEnvironment, xs] using
        transcriptLaw_fixedQueryEnvironment_of_eq I idSysRV xs yv
    -- The same identity for the real system: tr(R, xs)(xs, ys) = σ_R(xs, ys).
    have hR :
        trˡ[q](R, fixedQueryDDE (Y := Y) xs) (xv, yv) = transcriptSystemFactor R idSysRV
            xv yv := by
      simpa [deterministicTranscriptLaw, fixedQueryEnvironment, xs] using
        transcriptLaw_fixedQueryEnvironment_of_eq R idSysRV xs yv
    -- Instantiate the fixed-query hypothesis AT THE SAME transcript `t`
    -- (this is where `t ∉ Bad` is consumed), then rewrite both sides into
    -- system-factor form:  (1 − ε)·σ_I ≤ σ_R.
    have h := h_fixed xs (xv, yv) h_good
    rw [hI, hR] at h
    exact h
  -- Unfold the law-level transcript mass to the RV-form transcript law
  -- (identity system RV and identity environment RV over the laws' carriers).
  change (1 - eps) * transcriptLaw I E idSysRV idEnvRV
          q (xv, yv) ≤
      transcriptLaw R E idSysRV idEnvRV
        q (xv, yv)
  -- CR18 Lemma 3.2 (factorization):  tr(S,E)(t) = σ_S(xs,ys) · η_E(xs,ys),
  -- with the environment factor η_E common to both sides.
  cr18_transcript
  -- Multiply the system-factor inequality by the common η_E ≥ 0:
  calc (1 - eps) * (transcriptSystemFactor I idSysRV
            xv yv *
          transcriptEnvironmentFactor E idEnvRV
            xv yv)
      -- associativity:  (1 − ε)·(σ_I·η_E) = ((1 − ε)·σ_I)·η_E
      = ((1 - eps) * transcriptSystemFactor I idSysRV
            xv yv) *
          transcriptEnvironmentFactor E idEnvRV
            xv yv := by rw [← mul_assoc]
    -- monotonicity in the left factor (η_E ≥ 0):
    --   ((1 − ε)·σ_I)·η_E ≤ σ_R·η_E   from h_sys
    _ ≤ transcriptSystemFactor R idSysRV
          xv yv *
        transcriptEnvironmentFactor E idEnvRV
          xv yv := by
        gcongr
        exact E.2.nonNeg.mass_nonneg _

section WithFiniteTranscripts

variable [FiniteTranscriptSpace X Y q]

/-- Deterministic-environment form of the good-transcript transfer, on the
`Dist` carriers:

    (∀ xs, ∀ t ∉ Bad :  (1 − ε)·tr(I,xs)(t) ≤ tr(R,xs)(t))
        ⟹   ∀ t ∉ Bad :  (1 − ε)·tr(I,E)(t) ≤ tr(R,E)(t)

for every deterministic `q`-query-total `E`. -/
theorem deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
    (R I : ProbPDS X Y)
    (E : QQueryEnvironment X Y q)
    (Bad : TranscriptPrefix X Y q → Prop)
    (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q), ¬ Bad t →
      (1 - eps) * (tr(I, xs)) t ≤ (tr(R, xs)) t)
    (t : TranscriptPrefix X Y q) (h_good : ¬ Bad t) :
    (1 - eps) * (tr[q](I, E.1)) t ≤ (tr[q](R, E.1)) t := by
  -- Apply Layer B with the degenerate law-level environment δ_E := `ofDDE E`
  -- (a deterministic environment is the point mass on itself).
  have h := transcriptLaw_ratio_of_fixedQuery_ratio_of_good R I
    (ofDDE E.1) Bad eps
    (by
      -- The `Dist`-carrier fixed-query hypothesis is definitionally the
      -- law-function one:  (tr(S, xs)) t
      --                      = tr(S, fixedQueryDDE xs)(t).
      intro xs t' ht'
      have hfix := h_fixed xs t' ht'
      simpa [fixedQueryTranscriptDist, deterministicTranscriptDist] using hfix)
    t h_good
  -- Convert back:  tr(S, δ_E) = tr(S, E)  as `Dist`s (`transcriptDist_ofDDE`),
  -- then evaluate the transcript law at `t`.
  have hI := transcriptDist_ofDDE (q := q) I E.1
  have hR := transcriptDist_ofDDE (q := q) R E.1
  rw [← hI, ← hR]
  -- `transcriptDist_ofDDE` is a global `@[simp]` lemma, so a plain `simp` here
  -- would immediately undo the two rewrites above.  Unfold to the transcript
  -- law by the named evaluation lemma instead.
  exact h

/-- Pointwise-at-`t` form of the transfer: a fixed-query ratio *at a single
transcript* `t` transfers to every deterministic environment at `t`
(the "singleton-shrink" instance of the good-transcript transfer; this is
what lets the ratio defect depend on the transcript). -/
theorem deterministicTranscriptDist_ratio_of_fixedQuery_ratio_at
    (R I : ProbPDS X Y) (E : QQueryEnvironment X Y q)
    (t : TranscriptPrefix X Y q) (eps : NNReal)
    (h_fixed : ∀ xs : Fin q → X,
      (1 - eps) * (tr(I, xs)) t ≤ (tr(R, xs)) t) :
    (1 - eps) * tr[q](I, E.1) t ≤ tr[q](R, E.1) t := by
  refine deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
    R I E (fun t' => t' ≠ t) eps ?_ t (by simp)
  intro xs t' ht'
  push Not at ht'
  rw [ht']
  exact h_fixed xs

/-- **Weight side condition.**  For a `q`-step total system `S` and a
`q`-query-total deterministic environment `E`:

    |tr(S,E)| = 1

— transcripts of total systems are honest probability distributions.  This is
the standing side condition of every H-technique statement, discharged once. -/
@[grind =]
theorem deterministicTranscriptDist_weight_eq_one
    (S : ProbPDS X Y) (E : QQueryEnvironment X Y q)
    (hS : S.KStepTotal q) :
    (tr[q](S, E.1)).weight = 1 := by
  -- tr(S,E) = tr(S, δ_E) as `Dist`s; then |tr(S, δ_E)| = 1 by the law-level
  -- weight theorem, from `S` q-step total and `δ_E` q-query total.
  rw [← transcriptDist_ofDDE]
  exact transcriptDist_weight_eq_one_of_total (q := q) S
    (ofDDE E.1) hS (ofDDE_KQueryTotal E.1 E.2)

/-- Transcript distributions of law-level probability systems are pointwise
non-negative. -/
theorem deterministicTranscriptDist_nonNeg
    (S : ProbPDS X Y) (E : DDE X Y) :
    (tr[q](S, E)).NonNeg :=
  RandomSystems.HTechnique.ProbPDS.deterministicTranscriptDist_nonNeg S E

/-- Paired weight side condition:  |tr(S,E)| = |tr(T,E)|  for total S, T. -/
theorem deterministicTranscriptDist_weight_eq
    (S T : ProbPDS X Y) (E : QQueryEnvironment X Y q)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q) :
    (tr[q](S, E.1)).weight = (tr[q](T, E.1)).weight := by
  grind only [= deterministicTranscriptDist_weight_eq_one]

/-- Weight bound side condition:  |tr(T,E)| ≤ 1  for total T. -/
theorem deterministicTranscriptDist_weight_le_one
    (T : ProbPDS X Y) (E : QQueryEnvironment X Y q) (hT : T.KStepTotal q) :
    (tr[q](T, E.1)).weight ≤ 1 := by
  grind only [= deterministicTranscriptDist_weight_eq_one]

/-! ## Layer D — the adaptive H-technique

Each theorem below is the composition

    (fixed-query hypothesis)
      ─Layer B→  (pointwise hypothesis, for each E)
      ─Layer C→  δ(tr(S,E), tr(T,E)) ≤ bound
      ─sup over E→  Adv_q(S,T) ≤ bound

with the bad-transcript mass bounded uniformly over environments as the sole
adaptive residue. -/

/-- **H-technique, ratio form (adaptive).**

    (∀ xs, ∀ t ∉ Bad :  (1 − ε)·tr(T,xs)(t) ≤ tr(S,xs)(t))
      ∧  (∀ E :  Pr_{tr(T,E)}[Bad] ≤ δ_b)
        ⟹   Adv_q(S,T) ≤ δ_b + ε
$γ$
 -/
theorem adv_le_of_fixedQuery_ratio_of_good
    (S T : ProbPDS X Y)
    (Bad : TranscriptPrefix X Y q → Prop)
    (eps δb : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_ratio : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q), ¬ Bad t →
      (1 - eps) * (tr(T, xs)) t ≤ (tr(S, xs)) t)
    (h_bad : ∀ E : QQueryEnvironment X Y q, Pr[Bad ∣ tr[q](T, E.1)] ≤ δb) :
    Adv[q](S, T) ≤ ((δb + eps : NNReal) : ℝ) := by
  -- Supremum lift:  Adv_q(S,T) ≤ δ_b + ε  reduces to
  --   δ(tr(S,E), tr(T,E)) ≤ δ_b + ε  for every q-query-total deterministic E.
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T (δb + eps)
  intro E
  -- Layer C (`hTechnique_ratio`) at the transcript distributions of E:
  --   δ(tr(S,E), tr(T,E)) ≤ Pr_{tr(T,E)}[Bad] + ε.
  have h := hTechnique_ratio
      (tr[q](S, E.1))
      (tr[q](T, E.1))
      Bad eps
      (deterministicTranscriptDist_nonNeg S E.1)
      (deterministicTranscriptDist_nonNeg T E.1)
      (deterministicTranscriptDist_weight_eq S T E hS hT)
      (deterministicTranscriptDist_weight_le_one T E hT)
      -- ∀ t ∉ Bad:  (1 − ε)·tr(T,E)(t) ≤ tr(S,E)(t) — the fixed-query
      -- hypothesis pushed through the Layer-B factorization transfer.
      (fun t h_good =>
        deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
          S T E Bad eps h_ratio t h_good)
  -- Uniform bad bound:  Pr_{tr(T,E)}[Bad] + ε ≤ δ_b + ε.
  grw [h_bad E] at h
  push_cast
  exact h

/-- **H-technique, equality-on-good form (adaptive).**

    (∀ xs, ∀ t ∉ Bad :  tr(S,xs)(t) = tr(T,xs)(t))
      ∧  (∀ E :  Pr_{tr(T,E)}[Bad] ≤ δ_b)
        ⟹   Adv_q(S,T) ≤ δ_b

Derived by running the ratio transfer twice with `ε = 0`: each direction
gives one inequality, together pointwise equality on good. -/
theorem adv_le_of_fixedQuery_eq_on_good
    (S T : ProbPDS X Y)
    (Bad : TranscriptPrefix X Y q → Prop)
    (δb : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_eq : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q), ¬ Bad t →
      (tr(S, xs)) t = (tr(T, xs)) t)
    (h_bad : ∀ E : QQueryEnvironment X Y q, Pr[Bad ∣ tr[q](T, E.1)] ≤ δb) :
    Adv[q](S, T) ≤ (δb : ℝ) := by
  -- Supremum lift: bound each  δ(tr(S,E), tr(T,E)) ≤ δ_b.
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T δb
  intro E
  -- Direction 1:  tr(T,E)(t) ≤ tr(S,E)(t)  on good t.  Layer-B transfer at
  -- ε = 0 (so 1 − ε = 1) with hypothesis  σ_T ≤ σ_S  (h_eq right-to-left).
  have h_le₁ : ∀ t, ¬ Bad t → (tr[q](T, E.1)) t ≤ (tr[q](S, E.1)) t := by
    intro t h_good
    have h := deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
      S T E Bad 0
      (fun xs t' ht' => by simpa using (h_eq xs t' ht').ge) t h_good
    simpa using h
  -- Direction 2:  tr(S,E)(t) ≤ tr(T,E)(t)  on good t (roles swapped,
  -- h_eq left-to-right).
  have h_le₂ : ∀ t, ¬ Bad t → (tr[q](S, E.1)) t ≤ (tr[q](T, E.1)) t := by
    intro t h_good
    have h := deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
      T S E Bad 0
      (fun xs t' ht' => by simpa using (h_eq xs t' ht').le) t h_good
    simpa using h
  -- Layer C (`hTechnique_eq_on_good`): equal masses off Bad give
  --   δ(tr(S,E), tr(T,E)) ≤ Pr_{tr(T,E)}[Bad];
  -- pointwise equality on good = antisymmetry of the two directions.
  have h := hTechnique_eq_on_good
      (tr[q](S, E.1))
      (tr[q](T, E.1))
      Bad
      (deterministicTranscriptDist_nonNeg S E.1)
      (deterministicTranscriptDist_nonNeg T E.1)
      (deterministicTranscriptDist_weight_eq S T E hS hT)
      (fun t h_good => le_antisymm (h_le₂ t h_good) (h_le₁ t h_good))
  -- Uniform bad bound:  Pr_{tr(T,E)}[Bad] ≤ δ_b.
  exact le_trans h (h_bad E)

/-- **H-technique, expectation-method form (adaptive).**  The pointwise error
may depend on the transcript:

    (∀ xs, ∀ t ∉ Bad :  (1 − ε(t))·tr(T,xs)(t) ≤ tr(S,xs)(t))
      ∧  (∀ E :  Pr_{tr(T,E)}[Bad] ≤ δ_b)
      ∧  (∀ E :  𝔼_{t ~ tr(T,E)}[ε(t)·𝟙(t ∉ Bad)] ≤ c)
        ⟹   Adv_q(S,T) ≤ δ_b + c -/
theorem adv_le_of_fixedQuery_expectation
    (S T : ProbPDS X Y)
    (Bad : TranscriptPrefix X Y q → Prop) [DecidablePred Bad]
    (eps : TranscriptPrefix X Y q → NNReal)
    (δb c : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_ratio : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q), ¬ Bad t →
      (1 - eps t) * (tr(T, xs)) t ≤ (tr(S, xs)) t)
    (h_bad : ∀ E : QQueryEnvironment X Y q, Pr[Bad ∣ tr[q](T, E.1)] ≤ δb)
    (h_exp : ∀ E : QQueryEnvironment X Y q, ((tr[q](T, E.1)).sum
        fun t w => if ¬ Bad t then w * eps t else 0) ≤ c) :
    Adv[q](S, T) ≤ ((δb + c : NNReal) : ℝ) := by
  classical
  -- Supremum lift: bound each  δ(tr(S,E), tr(T,E)) ≤ δ_b + c.
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T (δb + c)
  intro E
  -- Pointwise transfer with transcript-DEPENDENT ε(t): for each good t run
  -- the Layer-B transfer at the constant ε := ε(t), with the good set shrunk
  -- to the singleton {t} (predicate  Bad ∨ (· ≠ t)), so the constant-ε
  -- hypothesis is only demanded at t itself.
  have h_pointwise : ∀ t, ¬ Bad t → (1 - eps t) * (tr[q](T, E.1)) t ≤ (tr[q](S, E.1)) t := by
    intro t h_good
    refine deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
      S T E (fun t' => Bad t' ∨ t' ≠ t) (eps t) ?_ t (by simp [h_good])
    -- The only good transcript of the shrunken predicate is t' = t, where
    -- the demanded ratio is exactly  h_ratio  at ε(t).
    intro xs t' ht'
    push Not at ht'
    rw [ht'.2]
    exact h_ratio xs t (ht'.2 ▸ ht'.1)
  -- Layer C (`hTechnique_expectation`):
  --   δ(tr(S,E), tr(T,E)) ≤ Pr_{tr(T,E)}[Bad] + E_{tr(T,E)}[ε·1_good].
  have h := hTechnique_expectation
      (tr[q](S, E.1))
      (tr[q](T, E.1))
      Bad eps
      (deterministicTranscriptDist_nonNeg S E.1)
      (deterministicTranscriptDist_nonNeg T E.1)
      (deterministicTranscriptDist_weight_eq S T E hS hT)
      h_pointwise
  -- Bound both summands uniformly:  Pr[Bad] ≤ δ_b  and  E[ε·1_good] ≤ c.
  grw [h_bad E, h_exp E] at h
  push_cast
  exact h

/-- **H-technique, perfect form** (`Bad = ∅`):

    (∀ xs, ∀ t :  (1 − ε)·tr(T,xs)(t) ≤ tr(S,xs)(t))
        ⟹   Adv_q(S,T) ≤ ε

The thesis-style `oneSided_hTechnique_law_experiment_of_fixedQuery_ratio` is
this statement one environment at a time. -/
theorem adv_le_of_fixedQuery_ratio
    (S T : ProbPDS X Y)
    (eps : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_ratio : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      (1 - eps) * (tr(T, xs)) t ≤ (tr(S, xs)) t) :
    Adv[q](S, T) ≤ (eps : ℝ) := by
  -- Instantiate the ratio form at Bad := ∅ and δ_b := 0.
  have h := adv_le_of_fixedQuery_ratio_of_good S T (fun _ => False) eps 0 hS hT
    (fun xs t _ => h_ratio xs t)
    (by
      -- Pr_{tr(T,E)}[∅] = Σ_t 0 = 0  for every environment E.
      intro E
      simp [probBad, Dist.mass_eq_sum])
  -- 0 + ε = ε.
  simpa using h


/-! ### The (★) identity — transcript distance with the adversary factored

For a deterministic environment, statistical distance of transcript
distributions is a *sum of system-factor gaps weighted by the 0/1 environment
factor*:

    δ(tr(S,E), tr(T,E)) = Σ_t (σ_S(t) − σ_T(t)) · η_E(t)

with σ_S(t) expressed through the public fixed-query facade at the
transcript's own inputs.  This is the quantitative form of "the adversary
factors out": the summands are non-adaptive, and `E` only selects (via the
indicator `η_E`) which fixed-query gaps are counted. -/

/-- The 0/1 environment factor of a deterministic environment at a
transcript: `η_E(t) = 𝟙[∀ i < q, E((t.ys.take i).map some) = some (t.xs i)]`. -/
noncomputable def envFactor (E : DDE X Y)
    (t : TranscriptPrefix X Y q) : ℝ :=
  transcriptEnvironmentFactor Dist.unitProbDist.{0}
    (constEnvRV E) t.1 t.2

@[inherit_doc envFactor]
scoped notation:max "η(" E ")" => envFactor E

/-- The environment factor is a probability mass, hence non-negative. -/
theorem envFactor_nonneg (E : DDE X Y) (t : TranscriptPrefix X Y q) :
    0 ≤ envFactor (q := q) E t :=
  Dist.unitProbDist.2.nonNeg.mass_nonneg _

/-- The system factor of a law at a transcript:
`σ_S(t) = S{s : ∀ i, s(xs₁…xsᵢ) = ysᵢ}`. -/
noncomputable def sysFactor (S : ProbPDS X Y)
    (t : TranscriptPrefix X Y q) : ℝ :=
  transcriptSystemFactor S idSysRV t.1 t.2

@[inherit_doc sysFactor]
scoped notation:max "σ(" S ")" => sysFactor S

/-- The system factor is a probability mass, hence non-negative. -/
theorem sysFactor_nonneg (S : ProbPDS X Y) (t : TranscriptPrefix X Y q) :
    0 ≤ sysFactor (q := q) S t :=
  S.2.nonNeg.mass_nonneg _

/-- CR18 Lemma 3.2 in named-factor form:  tr(S,E)(t) = σ_S(t) · η_E(t). -/
@[grind =]
theorem deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor
    (S : ProbPDS X Y) (E : DDE X Y)
    (t : TranscriptPrefix X Y q) :
    (tr[q](S, E)) t = σ(S) t * η(E) t := by
  -- Unfold to the RV-form transcript law and apply the factorization.
  simp only [deterministicTranscriptDist, deterministicTranscriptLawDist_apply,
    deterministicTranscriptLaw]
  exact transcriptLaw_eq_systemFactor_mul_environmentFactor _ _ _ _ t

/-- The system factor is the fixed-query transcript mass at the transcript's
own inputs:  σ_S(t) = tr(S, xs(t))(t)  with  xs(t) := t's input tuple. -/
@[grind =]
theorem sysFactor_eq_fixedQueryTranscriptDist_self
    (S : ProbPDS X Y) (t : TranscriptPrefix X Y q) :
    σ(S) t = (tr(S, functionOfVector t.1)) t := by
  rcases t with ⟨xv, yv⟩
  -- The fixed-query mass at its own query tuple is exactly the system-side
  -- event mass (thesis A.1 observation), as in Layer B.
  simp only [fixedQueryTranscriptDist, deterministicTranscriptDist,
    deterministicTranscriptLawDist_apply]
  symm
  simpa [deterministicTranscriptLaw, fixedQueryEnvironment, sysFactor] using
    transcriptLaw_fixedQueryEnvironment_of_eq S idSysRV
      (functionOfVector xv) yv

/-- **The (★) identity.**

    δ(tr(S,E), tr(T,E))
      = Σ_t ( tr(S, xs(t))(t) − tr(T, xs(t))(t) ) · η_E(t)

— the transcript distance is a sum of non-adaptive fixed-query gaps, filtered
by the deterministic environment's 0/1 consistency indicator. -/
theorem statDist_deterministicTranscriptDist_eq_sum_fixedQuery_gap
    (S T : ProbPDS X Y) (E : DDE X Y) :
    δ(tr[q](S, E), tr[q](T, E)) = ∑ t : TranscriptPrefix X Y q,
        max ((tr(S, functionOfVector t.1)) t -
          (tr(T, functionOfVector t.1)) t) 0 * η(E) t := by
  -- δ(P,Q) = Σ_t max (P t − Q t) 0; factor each summand and pull η_E out of
  -- the positive part:  max (σ_S·η − σ_T·η) 0 = max (σ_S − σ_T) 0 · η.
  rw [statDist_eq_sum_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor S E t,
    deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor T E t,
    ← sub_mul, max_mul_of_nonneg _ _ (envFactor_nonneg E t), zero_mul,
    sysFactor_eq_fixedQueryTranscriptDist_self S t,
    sysFactor_eq_fixedQueryTranscriptDist_self T t]

/-! ### Layer D′ — the generalized H-lemma (partition form, Chen–Steinberger)

Good/bad is not fundamental: partition the transcript space into cells
`cell : A → ι` with a per-cell ratio defect `ε_i`, and

    δ(real, ideal) ≤ Σ_i ε_i · Pr_ideal[cell = i].

This is derived from the expectation form (`hTechnique_expectation` with
`Bad := ∅` and `ε(t) := ε_{cell t}`), and the good/bad ratio lemma is the
two-cell special case (`Bad ↦ ε₀ = 1`, `good ↦ ε₁ = ε`). -/

/-- **Generalized H-lemma (partition form).**

    (∀ t :  (1 − ε_{cell t})·ideal t ≤ real t)
        ⟹   δ(real, ideal) ≤ Σ_i ε_i · Pr[cell = i ∣ ideal]. -/
theorem hTechnique_partition {A : Type*} [Fintype A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (real ideal : Dist A) (cell : A → ι) (eps : ι → NNReal)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ratio : ∀ a, (1 - eps (cell a)) * ideal a ≤ real a) :
    statDist real ideal ≤
      ∑ i, eps i * Pr[(fun a => cell a = i) ∣ ideal] := by
  classical
  -- Expectation form at Bad := ∅, ε(a) := ε_{cell a}.
  have h := hTechnique_expectation real ideal (fun _ => False)
    (fun a => eps (cell a)) h_real_nonneg h_ideal_nonneg h_weight
    (fun a _ => h_ratio a)
  refine le_trans h (le_of_eq ?_)
  -- Pr[∅] = 0, and the ideal expectation of ε_{cell ·} regroups by cell:
  --   Σ_a ideal(a)·ε_{cell a} = Σ_i ε_i·Pr[cell = i].
  rw [show probBad ideal (fun _ => False) = 0 by
    simp [probBad, Dist.mass_eq_sum], zero_add]
  cr18_mass_expand
  simp only [not_false_iff, if_true, Finset.mul_sum]
  cr18_sum_swap a
  -- Σ_i ε_i·𝟙[cell a = i]·w = ε_{cell a}·w
  cr18_ite_collapse

/-- **Good/bad is the two-cell special case** of the partition lemma:
`Bad` is the cell with defect `1`, `good` the cell with defect `ε`;
`1·Pr[Bad] + ε·Pr[good] ≤ Pr[Bad] + ε` recovers `hTechnique_ratio`. -/
theorem hTechnique_ratio_via_partition {A : Type*} [Fintype A]
    (real ideal : Dist A) (B : A → Prop) [DecidablePred B] (eps : NNReal)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_le_one : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ Pr[B ∣ ideal] + eps := by
  classical
  have h := hTechnique_partition real ideal
    (fun a => if B a then (0 : Fin 2) else 1)
    (fun i => if i = 0 then 1 else eps)
    h_real_nonneg h_ideal_nonneg h_weight
    (by
      intro a
      by_cases hB : B a
      · simpa [hB] using h_real_nonneg a
      · simpa [hB] using h_ratio a hB)
  refine le_trans h ?_
  rw [Fin.sum_univ_two]
  simp only [reduceIte, NNReal.coe_one, one_mul]
  have h0 : Pr[(fun a => (if B a then (0 : Fin 2) else 1) = 0) ∣ ideal] =
      Pr[B ∣ ideal] := by
    apply Dist.mass_congr
    intro a
    by_cases hB : B a <;> simp [hB]
  have h1 : eps * Pr[(fun a => (if B a then (0 : Fin 2) else 1) = 1) ∣ ideal] ≤
      eps := by
    have hm : Pr[(fun a => (if B a then (0 : Fin 2) else 1) = 1) ∣ ideal] ≤ 1 :=
      le_trans (Dist.mass_le_weight h_ideal_nonneg _) h_le_one
    bound
  rw [h0]
  exact add_le_add le_rfl h1

/-- **H-technique, partition form (adaptive).**

    (∀ xs, ∀ t :  (1 − ε_{cell t})·tr(T,xs)(t) ≤ tr(S,xs)(t))
      ∧  (∀ E :  Σ_i ε_i·Pr[cell = i ∣ tr(T,E)] ≤ c)
        ⟹   Adv_q(S,T) ≤ c

— the per-cell ratios are non-adaptive, and the sole adaptive residue is a
uniform bound on the ideal cell-mass average. -/
theorem adv_le_of_fixedQuery_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : ProbPDS X Y)
    (cell : TranscriptPrefix X Y q → ι) (eps : ι → NNReal) (c : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_ratio : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      (1 - eps (cell t)) * (tr(T, xs)) t ≤ (tr(S, xs)) t)
    (h_cell : ∀ E : QQueryEnvironment X Y q,
      (∑ i, eps i * Pr[(fun t => cell t = i) ∣ tr[q](T, E.1)]) ≤ c) :
    Adv[q](S, T) ≤ (c : ℝ) := by
  classical
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T c
  intro E
  -- Pointwise transfer with cell-dependent ε (singleton-shrink, as in the
  -- expectation form).
  have h_pointwise : ∀ t, (1 - eps (cell t)) * tr[q](T, E.1) t ≤
      tr[q](S, E.1) t := fun t =>
    deterministicTranscriptDist_ratio_of_fixedQuery_ratio_at S T E t
      (eps (cell t)) (fun xs => h_ratio xs t)
  have h := hTechnique_partition
    (tr[q](S, E.1)) (tr[q](T, E.1)) cell eps
    (deterministicTranscriptDist_nonNeg S E.1)
    (deterministicTranscriptDist_nonNeg T E.1)
    (deterministicTranscriptDist_weight_eq S T E hS hT)
    h_pointwise
  exact le_trans h (h_cell E)

end WithFiniteTranscripts

/-! ## Layer E — extended transcripts (extension-as-data)

An *extension* of a transcript distribution is any distribution `tr⁺(S,E)`
on transcripts × `Z` with `fst_* tr⁺(S,E) = tr(S,E)` — "reveal auxiliary
information `Z` (a key, a hash function, …) after the interaction".  By data
processing (thesis Lemma 2.7), extensions can only increase statistical
distance, so the H-technique may be run on the extended space, where
good-transcript ratios are typically exactly computable.  The extension is
supplied per environment as data, together with its projection laws; how it
is constructed (pushforward of the sampled system along
`s ↦ (tr(s,E), aug(s))`, joint sampling, …) is the application's business. -/

section ExtendedTranscripts

variable {Z : Type*} [Fintype Z]
variable [FiniteTranscriptSpace X Y q] [DiscreteTranscriptSpace X Y q]

/-- **Data processing for extensions** (thesis Lemma 2.7):

    fst_* P′ = P  ∧  fst_* Q′ = Q   ⟹   δ(P,Q) ≤ δ(P′,Q′) -/
theorem statDist_le_of_extension {A : Type*} [Fintype A] [DecidableEq A]
    (P Q : Dist A) (P' Q' : Dist (A × Z))
    (hP : π₁⋆ P' = P)
    (hQ : π₁⋆ Q' = Q) :
    δ(P, Q) ≤ δ(P', Q') := by
  -- Substitute  P = fst_* P',  Q = fst_* Q'  and apply data processing
  --   δ(f_* X, f_* Y) ≤ δ(X, Y)   with  f := fst.
  rw [← hP, ← hQ]
  exact statDist_fTransform_le P' Q' Prod.fst

/-- **H-technique, extended-transcript ratio form (adaptive).**  Writing
`tr⁺_S(E)`, `tr⁺_T(E)` for the per-environment extensions:

    (∀ E :  fst_* tr⁺_S(E) = tr(S,E)  ∧  fst_* tr⁺_T(E) = tr(T,E))
      ∧  (∀ E, ∀ (t,z) ∉ Bad :  (1 − ε)·tr⁺_T(E)(t,z) ≤ tr⁺_S(E)(t,z))
      ∧  (∀ E :  Pr_{tr⁺_T(E)}[Bad] ≤ δ_b)
        ⟹   Adv_q(S,T) ≤ δ_b + ε -/
theorem adv_le_of_extended_ratio_of_good
    (S T : ProbPDS X Y)
    (extS extT : QQueryEnvironment X Y q → Dist (TranscriptPrefix X Y q × Z))
    (Bad : TranscriptPrefix X Y q × Z → Prop)
    (eps δb : NNReal)
    (h_nnS : ∀ E, (extS E).NonNeg)
    (h_nnT : ∀ E, (extT E).NonNeg)
    (h_projS : ∀ E, π₁⋆ (extS E) = tr[q](S, E.1))
    (h_projT : ∀ E, π₁⋆ (extT E) = tr[q](T, E.1))
    (h_weight : ∀ E, (extS E).weight = (extT E).weight)
    (h_le_one : ∀ E, (extT E).weight ≤ 1)
    (h_ratio : ∀ E (tz : TranscriptPrefix X Y q × Z), ¬ Bad tz →
      (1 - eps) * (extT E) tz ≤ (extS E) tz)
    (h_bad : ∀ E, Pr[Bad ∣ extT E] ≤ δb) :
    Adv[q](S, T) ≤ ((δb + eps : NNReal) : ℝ) := by
  -- Supremum lift: bound each  δ(tr(S,E), tr(T,E)) ≤ δ_b + ε.
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T (δb + eps)
  intro E
  -- H-technique ON THE EXTENDED SPACE (Layer C at tr⁺):
  --   δ(tr⁺_S(E), tr⁺_T(E)) ≤ Pr_{tr⁺_T(E)}[Bad] + ε.
  have h_ext := hTechnique_ratio (extS E) (extT E) Bad eps
      (h_nnS E) (h_nnT E)
      (h_weight E) (h_le_one E) (h_ratio E)
  -- Data processing:  δ(tr(S,E), tr(T,E)) ≤ δ(tr⁺_S(E), tr⁺_T(E)).
  have h_proj := statDist_le_of_extension
    (tr[q](S, E.1))
    (tr[q](T, E.1))
    (extS E) (extT E) (h_projS E) (h_projT E)
  -- Chain:  δ(tr) ≤ δ(tr⁺) ≤ Pr[Bad] + ε ≤ δ_b + ε.
  grw [h_ext, h_bad E] at h_proj
  exact h_proj

/-- **H-technique, extended equality-on-good form (adaptive).**

    (∀ E, ∀ (t,z) ∉ Bad :  tr⁺_S(E)(t,z) = tr⁺_T(E)(t,z))
      ∧  (∀ E :  Pr_{tr⁺_T(E)}[Bad] ≤ δ_b)
        ⟹   Adv_q(S,T) ≤ δ_b

(projection hypotheses as in the ratio form). -/
theorem adv_le_of_extended_eq_on_good
    (S T : ProbPDS X Y)
    (extS extT : QQueryEnvironment X Y q → Dist (TranscriptPrefix X Y q × Z))
    (Bad : TranscriptPrefix X Y q × Z → Prop)
    (δb : NNReal)
    (h_nnS : ∀ E, (extS E).NonNeg)
    (h_nnT : ∀ E, (extT E).NonNeg)
    (h_projS : ∀ E, π₁⋆ (extS E) = tr[q](S, E.1))
    (h_projT : ∀ E, π₁⋆ (extT E) = tr[q](T, E.1))
    (h_weight : ∀ E, (extS E).weight = (extT E).weight)
    (h_eq : ∀ E (tz : TranscriptPrefix X Y q × Z), ¬ Bad tz → (extS E) tz = (extT E) tz)
    (h_bad : ∀ E, Pr[Bad ∣ extT E] ≤ δb) :
    Adv[q](S, T) ≤ (δb : ℝ) := by
  -- Supremum lift: bound each  δ(tr(S,E), tr(T,E)) ≤ δ_b.
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T δb
  intro E
  -- Equality-on-good on the extended space:
  --   δ(tr⁺_S(E), tr⁺_T(E)) ≤ Pr_{tr⁺_T(E)}[Bad].
  have h_ext := hTechnique_eq_on_good (extS E) (extT E) Bad
      (h_nnS E) (h_nnT E)
      (h_weight E) (h_eq E)
  -- Data processing:  δ(tr(S,E), tr(T,E)) ≤ δ(tr⁺_S(E), tr⁺_T(E)).
  have h_proj := statDist_le_of_extension
    (tr[q](S, E.1))
    (tr[q](T, E.1))
    (extS E) (extT E) (h_projS E) (h_projT E)
  -- Chain:  δ(tr) ≤ δ(tr⁺) ≤ Pr[Bad] ≤ δ_b.
  grw [h_ext, h_bad E] at h_proj
  exact h_proj

end ExtendedTranscripts

/-! ## Layer E′ — the σ⁺ fixed-query refinement of extended transcripts

Layer E takes extensions as opaque per-environment data.  This layer builds
the *canonical* extension from a revealed-information map `aug : DDS → Z`
("reveal the sampled key/function after the interaction") and shows its
hypotheses reduce to **fixed-query** (non-adaptive) conditions, exactly as in
Layer B:

    tr⁺(S,aug,E)(t,z) = σ⁺_S(t,z) · η_E(t),
    σ⁺_S(t,z) = S{s : sysEvent(t,s) ∧ aug s = z} = tr⁺(S,aug,xs(t))(t,z).

The construction is event-mass based (no pushforward through a partial
transcript map), so it works for arbitrary laws; totality only enters through
the usual weight side conditions. -/

section ExtendedFixedQuery

set_option linter.unusedSectionVars false

variable {Z : Type u} [Fintype Z] [DecidableEq Z]
variable [DecidableEq X]
variable [FiniteTranscriptSpace X Y q] [DiscreteTranscriptSpace X Y q]

/-- The **extended system factor**:
`σ⁺_S(t,z) = S{s : sysEvent(t,s) ∧ aug s = z}` — the system-side event of the
transcript, refined by the revealed value of `aug`. -/
noncomputable def extSysFactor (S : ProbPDS X Y)
    (aug : DDS X Y → Z)
    (tz : TranscriptPrefix X Y q × Z) : ℝ :=
  S.val.mass (fun s =>
    transcriptSystemEvent idSysRV
      tz.1.1 tz.1.2 s ∧ aug s = tz.2)

@[inherit_doc extSysFactor]
scoped notation:max "σ⁺(" S ", " aug ")" => extSysFactor S aug

/-- The extended system factor is a probability mass, hence non-negative. -/
theorem extSysFactor_nonneg (S : ProbPDS X Y) (aug : DDS X Y → Z)
    (tz : TranscriptPrefix X Y q × Z) :
    0 ≤ extSysFactor (q := q) S aug tz :=
  S.2.nonNeg.mass_nonneg _

/-- Revealing `aug` partitions the system factor:
`Σ_z σ⁺_S(t,z) = σ_S(t)`. -/
theorem sum_extSysFactor (S : ProbPDS X Y)
    (aug : DDS X Y → Z) (t : TranscriptPrefix X Y q) :
    (∑ z : Z, σ⁺(S, aug) (t, z)) = σ(S) t := by
  classical
  unfold extSysFactor sysFactor transcriptSystemFactor
  -- Σ_z Σ_{s ∈ supp} 𝟙[Ev s ∧ aug s = z]·w  =  Σ_{s ∈ supp} Σ_z …  =  Σ_s 𝟙[Ev s]·w
  cr18_mass_expand
  cr18_sum_swap s
  by_cases hEv : transcriptSystemEvent idSysRV t.1 t.2 s
  · -- only the fiber z = aug s contributes:  Σ_z 𝟙[aug s = z]·w = w
    simp [hEv, Finset.sum_ite_eq]
  · simp [hEv]

/-- The canonical **extended deterministic transcript distribution**:

    tr⁺(S,aug,E)(t,z) := σ⁺_S(t,z) · η_E(t). -/
noncomputable def extendedDeterministicTranscriptDist (S : ProbPDS X Y)
    (aug : DDS X Y → Z) (E : DDE X Y) :
    Dist (TranscriptPrefix X Y q × Z) :=
  Dist.ofFiniteMassFunction
    (fun tz => σ⁺(S, aug) tz * η(E) tz.1)

@[inherit_doc extendedDeterministicTranscriptDist]
scoped notation:max "tr⁺[" q "](" S ", " aug ", " E ")" =>
  extendedDeterministicTranscriptDist (q := q) S aug E

@[simp, grind =]
theorem extendedDeterministicTranscriptDist_apply (S : ProbPDS X Y)
    (aug : DDS X Y → Z) (E : DDE X Y)
    (tz : TranscriptPrefix X Y q × Z) :
    tr⁺[q](S, aug, E) tz = σ⁺(S, aug) tz * η(E) tz.1 := by
  simp [extendedDeterministicTranscriptDist]

/-- The canonical extension is pointwise non-negative. -/
theorem extendedDeterministicTranscriptDist_nonNeg (S : ProbPDS X Y)
    (aug : DDS X Y → Z) (E : DDE X Y) :
    (tr⁺[q](S, aug, E)).NonNeg := fun tz => by
  rw [extendedDeterministicTranscriptDist_apply]
  exact mul_nonneg (extSysFactor_nonneg S aug tz) (envFactor_nonneg E tz.1)

/-- **Projection law**:  fst_* tr⁺(S,aug,E) = tr(S,E).  Revealing `aug` and
then forgetting it changes nothing. -/
theorem fTransform_fst_extendedDeterministicTranscriptDist
    (S : ProbPDS X Y) (aug : DDS X Y → Z) (E : DDE X Y) :
    Dist.fTransform Prod.fst
        (tr⁺[q](S, aug, E)) =
      tr[q](S, E) := by
  classical
  ext t
  -- (fst_* tr⁺) t = Σ_{(t',z) : t' = t} tr⁺(t',z) = Σ_z σ⁺(t,z)·η(t)
  --              = (Σ_z σ⁺(t,z))·η(t) = σ(t)·η(t) = tr(S,E)(t).
  rw [Dist.fTransform_apply_eq_sum, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [extendedDeterministicTranscriptDist_apply]
  rw [show (∑ t' : TranscriptPrefix X Y q, ∑ z : Z,
        if t' = t then σ⁺(S, aug) (t', z) * η(E) t' else 0) =
      ∑ z : Z, σ⁺(S, aug) (t, z) * η(E) t from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp]
  rw [← Finset.sum_mul, sum_extSysFactor,
    ← deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor]

/-- The extension preserves total mass:  |tr⁺(S,aug,E)| = |tr(S,E)|. -/
theorem extendedDeterministicTranscriptDist_weight (S : ProbPDS X Y)
    (aug : DDS X Y → Z) (E : DDE X Y) :
    (tr⁺[q](S, aug, E)).weight = (tr[q](S, E)).weight := by
  rw [← fTransform_fst_extendedDeterministicTranscriptDist S aug E, Dist.weight_fTransform]

/-- The extended **fixed-query** transcript distribution (the σ⁺ facade). -/
noncomputable def extFixedQueryTranscriptDist (S : ProbPDS X Y)
    (aug : DDS X Y → Z) (xs : Fin q → X) :
    Dist (TranscriptPrefix X Y q × Z) :=
  extendedDeterministicTranscriptDist S aug (fixedQueryDDE (Y := Y) xs)

@[inherit_doc extFixedQueryTranscriptDist]
scoped notation:max "tr⁺(" S ", " aug ", " xs ")" =>
  extFixedQueryTranscriptDist S aug xs

/-- The fixed-query environment factor is the input-match indicator:
`η_{xs}(t) = 𝟙[t.inputs = xs]`. -/
@[grind =]
theorem envFactor_fixedQueryDDE (xs : Fin q → X)
    (t : TranscriptPrefix X Y q) :
    η(fixedQueryDDE (Y := Y) xs) t = if t.1 = vectorOfFunction xs then 1 else 0 := by
  classical
  unfold envFactor transcriptEnvironmentFactor
  by_cases hc : t.1 = vectorOfFunction xs
  · rw [if_pos hc]
    -- the event is sure:  mass(⊤) = |unit| = 1
    have hmass : (Dist.unitProbDist.{0}).val.mass
        (transcriptEnvironmentEvent
          (constEnvRV (fixedQueryDDE (Y := Y) xs))
          t.1 t.2) =
        (Dist.unitProbDist.{0}).val.mass (fun _ => True) := by
      apply Dist.mass_congr
      intro ω
      cases ω
      simp only [iff_true]
      exact (transcriptEnvironmentEvent_fixedQueryEnvironment_iff
        xs t.1 t.2).mpr hc
    rw [hmass]
    simpa [Dist.mass, Dist.weight] using
      (Dist.unitProbDist.{0}).2.weight_eq
  · rw [if_neg hc]
    -- the event is impossible:  mass(⊥) = 0
    have hmass : (Dist.unitProbDist.{0}).val.mass
        (transcriptEnvironmentEvent
          (constEnvRV (fixedQueryDDE (Y := Y) xs))
          t.1 t.2) =
        (Dist.unitProbDist.{0}).val.mass (fun _ => False) := by
      apply Dist.mass_congr
      intro ω
      cases ω
      simp only [iff_false]
      intro h
      exact hc ((transcriptEnvironmentEvent_fixedQueryEnvironment_iff
        xs t.1 t.2).mp h)
    rw [hmass]
    simp [Dist.mass]

/-- The σ⁺ analogue of the thesis A.1 identity: the extended fixed-query mass
at the transcript's own inputs is exactly the extended system factor,

    tr⁺(S, aug, xs(t))(t,z) = σ⁺_S(t,z). -/
@[grind =]
theorem extFixedQueryTranscriptDist_self (S : ProbPDS X Y)
    (aug : DDS X Y → Z)
    (tz : TranscriptPrefix X Y q × Z) :
    tr⁺(S, aug, (functionOfVector tz.1.1)) tz = σ⁺(S, aug) tz := by
  grind [extFixedQueryTranscriptDist, vectorOfFunction_functionOfVector]

/-- **Layer-B transfer, σ⁺ form.**  An extended fixed-query ratio on good
extended transcripts transfers to every deterministic environment:

    (∀ xs, ∀ (t,z) ∉ Bad :  (1 − ε)·tr⁺(I,augI,xs)(t,z) ≤ tr⁺(R,augR,xs)(t,z))
        ⟹   ∀ (t,z) ∉ Bad :  (1 − ε)·tr⁺(I,augI,E)(t,z) ≤ tr⁺(R,augR,E)(t,z). -/
theorem extended_ratio_of_extFixedQuery_ratio_of_good
    (R I : ProbPDS X Y)
    (augR augI : DDS X Y → Z)
    (E : DDE X Y)
    (Bad : TranscriptPrefix X Y q × Z → Prop)
    (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (tz : TranscriptPrefix X Y q × Z), ¬ Bad tz →
      (1 - eps) * tr⁺(I, augI, xs) tz ≤ tr⁺(R, augR, xs) tz)
    (tz : TranscriptPrefix X Y q × Z) (h_good : ¬ Bad tz) :
    (1 - eps) * tr⁺[q](I, augI, E) tz ≤ tr⁺[q](R, augR, E) tz := by
  -- The σ⁺-ratio at tz, from the hypothesis at tz's own inputs
  -- (thesis-A.1 identity, extended form):
  have hσ := h_fixed (functionOfVector tz.1.1) tz h_good
  rw [extFixedQueryTranscriptDist_self, extFixedQueryTranscriptDist_self] at hσ
  -- Multiply by the common environment factor η_E(tz.1):
  rw [extendedDeterministicTranscriptDist_apply,
    extendedDeterministicTranscriptDist_apply, ← mul_assoc]
  gcongr
  exact envFactor_nonneg _ _

/-- **H-technique, σ⁺ fixed-query ratio form (adaptive).**  The full
Patarin/Chen–Steinberger route on the law-level surface:

    (∀ xs, ∀ (t,z) ∉ Bad :  (1 − ε)·tr⁺(T,augT,xs)(t,z) ≤ tr⁺(S,augS,xs)(t,z))
      ∧  (∀ E :  Pr_{tr⁺(T,augT,E)}[Bad] ≤ δ_b)
        ⟹   Adv_q(S,T) ≤ δ_b + ε

— the ratio hypothesis is non-adaptive AND may consult the revealed value. -/
theorem adv_le_of_extFixedQuery_ratio_of_good
    (S T : ProbPDS X Y)
    (augS augT : DDS X Y → Z)
    (Bad : TranscriptPrefix X Y q × Z → Prop)
    (eps δb : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_ratio : ∀ (xs : Fin q → X) (tz : TranscriptPrefix X Y q × Z), ¬ Bad tz →
      (1 - eps) * tr⁺(T, augT, xs) tz ≤ tr⁺(S, augS, xs) tz)
    (h_bad : ∀ E : QQueryEnvironment X Y q, Pr[Bad ∣ tr⁺[q](T, augT, E.1)] ≤ δb) :
    Adv[q](S, T) ≤ ((δb + eps : NNReal) : ℝ) := by
  -- Instantiate the extension-as-data theorem with the canonical extension.
  refine adv_le_of_extended_ratio_of_good S T
    (fun E => tr⁺[q](S, augS, E.1))
    (fun E => tr⁺[q](T, augT, E.1))
    Bad eps δb
    (fun E => extendedDeterministicTranscriptDist_nonNeg S augS E.1)
    (fun E => extendedDeterministicTranscriptDist_nonNeg T augT E.1)
    (fun E => fTransform_fst_extendedDeterministicTranscriptDist S augS E.1)
    (fun E => fTransform_fst_extendedDeterministicTranscriptDist T augT E.1)
    (fun E => ?_) (fun E => ?_)
    (fun E tz h_good =>
      extended_ratio_of_extFixedQuery_ratio_of_good S T augS augT E.1
        Bad eps h_ratio tz h_good)
    h_bad
  · -- |tr⁺(S,augS,E)| = |tr(S,E)| = 1 = |tr(T,E)| = |tr⁺(T,augT,E)|
    rw [extendedDeterministicTranscriptDist_weight, extendedDeterministicTranscriptDist_weight,
      deterministicTranscriptDist_weight_eq_one S E hS,
      deterministicTranscriptDist_weight_eq_one T E hT]
  · -- |tr⁺(T,augT,E)| = 1 ≤ 1
    rw [extendedDeterministicTranscriptDist_weight,
      deterministicTranscriptDist_weight_eq_one T E hT]

end ExtendedFixedQuery

/-! ## Layer E″ — representative extensions: `aug` of sample AND transcript

Generalizes Layer E′ from system-level reveals (`aug : DDS → Z`) to
**representative-level, transcript-dependent** reveals
`aug : Ω → Transcript → Z`, for a law presented by a representative
`(Ω, p, F)` — the V1 view.  Two forcing examples:

* the hash key of hash-then-PRF is a function of the sample `(h, ρ)` but
  not of the induced oracle, so reveals must live at the sample level;
* HCTR2's extended transcripts reveal the internal block-cipher pairs
  *used in answering the queries* — irreducibly a function of the sample
  AND the transcript.

Randomized reveals (HCTR2's ideal world samples dummy internals conditioned
on the transcript) are absorbed by **enlarging the representative with
coins**: `(Ω × C, p ⊗ uniform, F ∘ fst)` presents the same law, and `aug`
reads the coins.  Layer E′ is the special case `Ω := DDS`, `F := id`,
transcript-independent `aug`. -/

section RepresentativeExtensions

set_option linter.unusedSectionVars false

variable {Ω Ω' : Type*} {Z : Type*} [Fintype Z] [DecidableEq Z]
variable [DecidableEq X]
variable [FiniteTranscriptSpace X Y q] [DiscreteTranscriptSpace X Y q]

/-- The **representative extended system factor**:
`σ⁺(t,z) = p{ω : F ω ⊩ t ∧ aug ω t = z}`. -/
noncomputable def extSysFactorRep (p : Dist.ProbDist Ω) (F : PFunPDS.RV Ω X Y)
    (aug : Ω → TranscriptPrefix X Y q → Z)
    (tz : TranscriptPrefix X Y q × Z) : ℝ :=
  p.val.mass (fun ω =>
    transcriptSystemEvent F tz.1.1 tz.1.2 ω ∧ aug ω tz.1 = tz.2)

/-- Revealing `aug` partitions the representative system factor. -/
theorem sum_extSysFactorRep (p : Dist.ProbDist Ω) (F : PFunPDS.RV Ω X Y)
    (aug : Ω → TranscriptPrefix X Y q → Z) (t : TranscriptPrefix X Y q) :
    (∑ z : Z, extSysFactorRep p F aug (t, z)) =
      transcriptSystemFactor p F t.1 t.2 := by
  classical
  unfold extSysFactorRep transcriptSystemFactor
  cr18_mass_expand
  cr18_sum_swap ω
  by_cases hEv : transcriptSystemEvent F t.1 t.2 ω
  · simp [hEv, Finset.sum_ite_eq]
  · simp [hEv]

/-- The representative extended transcript distribution:
`tr⁺(t,z) = σ⁺(t,z)·η_E(t)`. -/
noncomputable def extendedTranscriptDistRep (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (E : DDE X Y) : Dist (TranscriptPrefix X Y q × Z) :=
  Dist.ofFiniteMassFunction
    (fun tz => extSysFactorRep p F aug tz * η(E) tz.1)

@[simp, grind =]
theorem extendedTranscriptDistRep_apply (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (E : DDE X Y) (tz : TranscriptPrefix X Y q × Z) :
    extendedTranscriptDistRep (q := q) p F aug E tz =
      extSysFactorRep p F aug tz * η(E) tz.1 := by
  simp [extendedTranscriptDistRep]

/-- Named-factor factorization for laws presented by a representative:
`tr(PMF p F, E)(t) = σ_{p,F}(t)·η_E(t)`. -/
@[grind =]
theorem deterministicTranscriptDist_pmf_apply (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (E : DDE X Y) (t : TranscriptPrefix X Y q) :
    tr[q]((Dist.PMF p F : ProbPDS X Y), E) t =
      transcriptSystemFactor p F t.1 t.2 * η(E) t := by
  simp only [deterministicTranscriptDist, deterministicTranscriptLawDist_apply]
  rw [PFunPDE.deterministicTranscriptLaw_pmf]
  exact transcriptLaw_eq_systemFactor_mul_environmentFactor _ _ _ _ t

/-- The representative extended system factor is non-negative. -/
theorem extSysFactorRep_nonneg (p : Dist.ProbDist Ω) (F : PFunPDS.RV Ω X Y)
    (aug : Ω → TranscriptPrefix X Y q → Z)
    (tz : TranscriptPrefix X Y q × Z) :
    0 ≤ extSysFactorRep p F aug tz :=
  p.2.nonNeg.mass_nonneg _

/-- The representative extension is pointwise non-negative. -/
theorem extendedTranscriptDistRep_nonNeg (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (E : DDE X Y) :
    (extendedTranscriptDistRep (q := q) p F aug E).NonNeg := fun tz => by
  rw [extendedTranscriptDistRep_apply]
  exact mul_nonneg (extSysFactorRep_nonneg p F aug tz) (envFactor_nonneg E tz.1)

/-- **Projection law**: forgetting the reveal recovers the transcripts,
`fst⋆ tr⁺(p,F,aug,E) = tr(PMF p F, E)`. -/
theorem fTransform_fst_extendedTranscriptDistRep (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (E : DDE X Y) :
    π₁⋆ (extendedTranscriptDistRep (q := q) p F aug E) =
      tr[q]((Dist.PMF p F : ProbPDS X Y), E) := by
  classical
  ext t
  rw [Dist.fTransform_apply_eq_sum, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [extendedTranscriptDistRep_apply]
  rw [show (∑ t' : TranscriptPrefix X Y q, ∑ z : Z,
        if t' = t then extSysFactorRep p F aug (t', z) * η(E) t' else 0) =
      ∑ z : Z, extSysFactorRep p F aug (t, z) * η(E) t from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp]
  rw [← Finset.sum_mul, sum_extSysFactorRep,
    ← deterministicTranscriptDist_pmf_apply]

/-- The representative extension preserves total mass. -/
theorem extendedTranscriptDistRep_weight (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (E : DDE X Y) :
    (extendedTranscriptDistRep (q := q) p F aug E).weight =
      (tr[q]((Dist.PMF p F : ProbPDS X Y), E)).weight := by
  rw [← fTransform_fst_extendedTranscriptDistRep p F aug E,
    Dist.weight_fTransform]

/-- The representative extended **fixed-query** distribution (the σ⁺ facade). -/
noncomputable def extFixedQueryTranscriptDistRep (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (xs : Fin q → X) : Dist (TranscriptPrefix X Y q × Z) :=
  extendedTranscriptDistRep (q := q) p F aug (fixedQueryDDE (Y := Y) xs)

/-- The extended thesis-A.1 identity, representative form: at the
transcript's own inputs the extended fixed-query mass is the extended
system factor. -/
theorem extFixedQueryTranscriptDistRep_self (p : Dist.ProbDist Ω)
    (F : PFunPDS.RV Ω X Y) (aug : Ω → TranscriptPrefix X Y q → Z)
    (tz : TranscriptPrefix X Y q × Z) :
    extFixedQueryTranscriptDistRep p F aug (functionOfVector tz.1.1) tz =
      extSysFactorRep p F aug tz := by
  grind [extFixedQueryTranscriptDistRep, vectorOfFunction_functionOfVector]

/-- **Layer-B transfer, representative σ⁺ form**: an extended fixed-query
ratio on good extended transcripts transfers to every deterministic
environment. -/
theorem extended_ratio_of_extFixedQueryRep_ratio_of_good
    (pR : Dist.ProbDist Ω) (FR : PFunPDS.RV Ω X Y)
    (pI : Dist.ProbDist Ω') (FI : PFunPDS.RV Ω' X Y)
    (augR : Ω → TranscriptPrefix X Y q → Z)
    (augI : Ω' → TranscriptPrefix X Y q → Z)
    (E : DDE X Y) (Bad : TranscriptPrefix X Y q × Z → Prop) (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (tz : TranscriptPrefix X Y q × Z),
      ¬ Bad tz →
      (1 - eps) * extFixedQueryTranscriptDistRep pI FI augI xs tz ≤
        extFixedQueryTranscriptDistRep pR FR augR xs tz)
    (tz : TranscriptPrefix X Y q × Z) (h_good : ¬ Bad tz) :
    (1 - eps) * extendedTranscriptDistRep (q := q) pI FI augI E tz ≤
      extendedTranscriptDistRep (q := q) pR FR augR E tz := by
  have hσ := h_fixed (functionOfVector tz.1.1) tz h_good
  rw [extFixedQueryTranscriptDistRep_self, extFixedQueryTranscriptDistRep_self]
    at hσ
  rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply,
    ← mul_assoc]
  gcongr
  exact envFactor_nonneg _ _

/-- **H-technique, representative σ⁺ ratio form (adaptive).** -/
theorem adv_le_of_extFixedQueryRep_ratio_of_good
    (pR : Dist.ProbDist Ω) (FR : PFunPDS.RV Ω X Y)
    (pI : Dist.ProbDist Ω') (FI : PFunPDS.RV Ω' X Y)
    (augR : Ω → TranscriptPrefix X Y q → Z)
    (augI : Ω' → TranscriptPrefix X Y q → Z)
    (Bad : TranscriptPrefix X Y q × Z → Prop) (eps δb : NNReal)
    (hR : PFunPDS.Prob.KStepTotal (Dist.PMF pR FR) q)
    (hI : PFunPDS.Prob.KStepTotal (Dist.PMF pI FI) q)
    (h_ratio : ∀ (xs : Fin q → X) (tz : TranscriptPrefix X Y q × Z),
      ¬ Bad tz →
      (1 - eps) * extFixedQueryTranscriptDistRep pI FI augI xs tz ≤
        extFixedQueryTranscriptDistRep pR FR augR xs tz)
    (h_bad : ∀ E : QQueryEnvironment X Y q,
      Pr[Bad ∣ extendedTranscriptDistRep (q := q) pI FI augI E.1] ≤ δb) :
    Adv[q]((Dist.PMF pR FR : ProbPDS X Y), (Dist.PMF pI FI : ProbPDS X Y)) ≤
      ((δb + eps : NNReal) : ℝ) := by
  refine adv_le_of_extended_ratio_of_good _ _
    (fun E => extendedTranscriptDistRep (q := q) pR FR augR E.1)
    (fun E => extendedTranscriptDistRep (q := q) pI FI augI E.1)
    Bad eps δb
    (fun E => extendedTranscriptDistRep_nonNeg pR FR augR E.1)
    (fun E => extendedTranscriptDistRep_nonNeg pI FI augI E.1)
    (fun E => fTransform_fst_extendedTranscriptDistRep pR FR augR E.1)
    (fun E => fTransform_fst_extendedTranscriptDistRep pI FI augI E.1)
    (fun E => ?_) (fun E => ?_)
    (fun E tz h_good =>
      extended_ratio_of_extFixedQueryRep_ratio_of_good pR FR pI FI augR augI
        E.1 Bad eps h_ratio tz h_good)
    h_bad
  · rw [extendedTranscriptDistRep_weight, extendedTranscriptDistRep_weight,
      deterministicTranscriptDist_weight_eq_one _ E hR,
      deterministicTranscriptDist_weight_eq_one _ E hI]
  · rw [extendedTranscriptDistRep_weight,
      deterministicTranscriptDist_weight_eq_one _ E hI]

/-- **H-technique, representative σ⁺ equality-on-good form (adaptive)** —
the HCTR2-shaped endpoint: equal extended fixed-query masses on good
extended transcripts, plus a uniform bad bound on the ideal extension. -/
theorem adv_le_of_extFixedQueryRep_eq_on_good
    (pR : Dist.ProbDist Ω) (FR : PFunPDS.RV Ω X Y)
    (pI : Dist.ProbDist Ω') (FI : PFunPDS.RV Ω' X Y)
    (augR : Ω → TranscriptPrefix X Y q → Z)
    (augI : Ω' → TranscriptPrefix X Y q → Z)
    (Bad : TranscriptPrefix X Y q × Z → Prop) (δb : NNReal)
    (hR : PFunPDS.Prob.KStepTotal (Dist.PMF pR FR) q)
    (hI : PFunPDS.Prob.KStepTotal (Dist.PMF pI FI) q)
    (h_eq : ∀ (xs : Fin q → X) (tz : TranscriptPrefix X Y q × Z), ¬ Bad tz →
      extFixedQueryTranscriptDistRep pR FR augR xs tz =
        extFixedQueryTranscriptDistRep pI FI augI xs tz)
    (h_bad : ∀ E : QQueryEnvironment X Y q,
      Pr[Bad ∣ extendedTranscriptDistRep (q := q) pI FI augI E.1] ≤ δb) :
    Adv[q]((Dist.PMF pR FR : ProbPDS X Y), (Dist.PMF pI FI : ProbPDS X Y)) ≤
      (δb : ℝ) := by
  refine adv_le_of_extended_eq_on_good _ _
    (fun E => extendedTranscriptDistRep (q := q) pR FR augR E.1)
    (fun E => extendedTranscriptDistRep (q := q) pI FI augI E.1)
    Bad δb
    (fun E => extendedTranscriptDistRep_nonNeg pR FR augR E.1)
    (fun E => extendedTranscriptDistRep_nonNeg pI FI augI E.1)
    (fun E => fTransform_fst_extendedTranscriptDistRep pR FR augR E.1)
    (fun E => fTransform_fst_extendedTranscriptDistRep pI FI augI E.1)
    (fun E => ?_)
    (fun E tz h_good => ?_)
    h_bad
  · rw [extendedTranscriptDistRep_weight, extendedTranscriptDistRep_weight,
      deterministicTranscriptDist_weight_eq_one _ E hR,
      deterministicTranscriptDist_weight_eq_one _ E hI]
  · -- pointwise equality: equal σ⁺ (from the fixed-query equality at the
    -- transcript's own inputs) times the common η_E
    rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply,
      ← extFixedQueryTranscriptDistRep_self pR FR augR tz,
      ← extFixedQueryTranscriptDistRep_self pI FI augI tz,
      h_eq (functionOfVector tz.1.1) tz h_good]

end RepresentativeExtensions

/-! ## Layer F — the fundamental theorem, lower-bound direction
(thesis Thm 2.31, `Adv ≤ Δ`, plus the coupling reading of Thm 2.32)

The thesis defines `Δ(S,T) = inf δ(S′,T′)` over representatives `S′ ∈ [S]`,
`T′ ∈ [T]` of the transcript-equivalence classes, and proves `Δ = Adv`.
This layer proves the *lower-bound* half at the law level, in full:

    Adv_q(S,T) ≤ δ_law(S′,T′)   for every q-equivalent S′, T′       (Thm 2.31, ≤)
    Adv_q(S,T) ≤ Pr_J[s ≠ s′]   for every coupling J of the laws    (Thm 2.32, ≤)

The carrier of laws (`DDS X Y`) is infinite, so the `Fintype`-based
`statDist` does not apply; `lawStatDist` below is the support-based
one-sided distance `Σ_a (P a − Q a)` (agreeing with `statDist` on finite
carriers).  The key step is the transcript data-processing inequality
`δ(tr(S,E), tr(T,E)) ≤ δ_law(S,T)`, proved via the factorization
`tr(S,E)(t) = σ_S(t)·η_E(t)` and the fact that each sampled system realizes
at most one `E`-consistent transcript (`transcriptJointEvent_unique`).

The *attainment* half (existence of representatives achieving the sup — the
thesis successor induction with product couplings, Lemma 2.33) is not
formalized here; see `DESIGN.md` §9 for the recorded plan. -/

section FundamentalLowerBound

set_option linter.unusedSectionVars false

variable [DecidableEq X]

/-- Support-based one-sided statistical distance on an arbitrary carrier:
`δ_law(P,Q) = Σ_a (P a − Q a)` (truncated subtraction; the sum is finite
because it ranges over `P`'s support). -/
noncomputable def lawStatDist {A : Type*} (P Q : Dist A) : ℝ :=
  P.sum fun a w => max (w - Q a) 0

@[inherit_doc lawStatDist]
scoped notation:max "δˡ(" P ", " Q ")" => lawStatDist P Q

/-- On a finite carrier, `lawStatDist` is the usual `statDist` (for a
non-negative second law: off `P`'s support the positive part vanishes only
because `Q` is non-negative there). -/
@[grind =]
theorem lawStatDist_eq_statDist {A : Type*} [Fintype A] (P : Dist A)
    {Q : Dist A} (hQ : Q.NonNeg) :
    δˡ(P, Q) = δ(P, Q) := by
  unfold lawStatDist
  rw [Finsupp.sum, statDist_eq_sum_univ]
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
  rw [Finsupp.notMem_support_iff.mp ha]
  exact max_eq_right (sub_nonpos.mpr (hQ a))

/-- Mass is monotone under event implication (for a non-negative law). -/
theorem mass_mono {A : Type*} {D : Dist A} (hD : D.NonNeg) {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : D.mass P ≤ D.mass Q :=
  Dist.mass_mono hD h

/-- Splitting a mass along a second event:
`D(P) = D(P ∧ B) + D(P ∧ ¬B)`. -/
theorem mass_eq_mass_and_add_mass_and_not {A : Type*} (D : Dist A)
    (P B : A → Prop) :
    D.mass P = D.mass (fun a => P a ∧ B a) + D.mass (fun a => P a ∧ ¬ B a) := by
  classical
  cr18_mass_expand
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hP : P a <;> by_cases hB : B a <;> simp [hP, hB]

/-- Event-mass differences are bounded by the pointwise gaps on the event:
`P(Ev) − Q(Ev) ≤ Σ_{a ∈ Ev} (P a − Q a)`. -/
theorem mass_tsub_mass_le_sum_gap {A : Type*} (P : Dist A) {Q : Dist A}
    (hQnn : Q.NonNeg) (Ev : A → Prop)
    [DecidablePred Ev] :
    P.mass Ev - Q.mass Ev ≤
      P.sum fun a w => if Ev a then max (w - Q a) 0 else 0 := by
  classical
  -- Work over the common index set `P.support ∪ Q.support`.
  have hP : P.mass Ev = ∑ a ∈ P.support ∪ Q.support, if Ev a then P a else 0 := by
    unfold Dist.mass
    rw [Finsupp.sum_of_support_subset _
      (Finset.subset_union_left : P.support ⊆ P.support ∪ Q.support) _
      (fun a _ => by simp)]
    exact Finset.sum_congr rfl fun a _ => by congr
  have hQ : Q.mass Ev = ∑ a ∈ P.support ∪ Q.support, if Ev a then Q a else 0 := by
    unfold Dist.mass
    rw [Finsupp.sum_of_support_subset _
      (Finset.subset_union_right : Q.support ⊆ P.support ∪ Q.support) _
      (fun a _ => by simp)]
    exact Finset.sum_congr rfl fun a _ => by congr
  have hD : (P.sum fun a w => if Ev a then max (w - Q a) 0 else 0) =
      ∑ a ∈ P.support ∪ Q.support, if Ev a then max (P a - Q a) 0 else 0 := by
    rw [Finsupp.sum_of_support_subset _ Finset.subset_union_left _
      (fun a _ => by
        by_cases h : Ev a
        · simp only [if_pos h]
          simpa using max_eq_right (sub_nonpos.mpr (hQnn a))
        · simp [h])]
  rw [hP, hQ, hD, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hEv : Ev a
  · simp only [if_pos hEv]
    exact le_max_left _ _
  · simp [hEv]

/-- Deterministic-environment consistency of a transcript, in checkable form:
`E` asks exactly the transcript's queries along its outputs. -/
def EnvConsistent (E : DDE X Y)
    (t : TranscriptPrefix X Y q) : Prop :=
  ∀ i : Fin q, E ((t.2.toList.take i.1).map some) = some (t.1.get i)

@[inherit_doc EnvConsistent]
scoped notation:50 E:51 " ⊨ " t:51 => EnvConsistent E t

instance (E : DDE X Y) (t : TranscriptPrefix X Y q) :
    Decidable (E ⊨ t) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- `EnvConsistent` is the (constant-`ω`) environment rectangle event. -/
theorem envConsistent_iff_transcriptEnvironmentEvent
    (E : DDE X Y) (t : TranscriptPrefix X Y q)
    (ω : PUnit.{1}) :
    E ⊨ t ↔ transcriptEnvironmentEvent
        (constEnvRV E) t.1 t.2 ω := by
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i.1 i.2

/-- The deterministic environment factor is the consistency indicator:
`η_E(t) = 𝟙[E ⊨ t]`. -/
@[grind =]
theorem envFactor_eq_indicator (E : DDE X Y)
    (t : TranscriptPrefix X Y q) :
    η(E) t = if E ⊨ t then 1 else 0 := by
  classical
  unfold envFactor transcriptEnvironmentFactor
  by_cases hc : E ⊨ t
  · rw [if_pos hc]
    have hmass : (Dist.unitProbDist.{0}).val.mass
        (transcriptEnvironmentEvent
          (constEnvRV E) t.1 t.2) =
        (Dist.unitProbDist.{0}).val.mass (fun _ => True) := by
      apply Dist.mass_congr
      intro ω
      simp only [iff_true]
      exact (envConsistent_iff_transcriptEnvironmentEvent E t ω).mp hc
    rw [hmass]
    simpa [Dist.mass, Dist.weight] using
      (Dist.unitProbDist.{0}).2.weight_eq
  · rw [if_neg hc]
    have hmass : (Dist.unitProbDist.{0}).val.mass
        (transcriptEnvironmentEvent
          (constEnvRV E) t.1 t.2) =
        (Dist.unitProbDist.{0}).val.mass (fun _ => False) := by
      apply Dist.mass_congr
      intro ω
      simp only [iff_false]
      intro h
      exact hc ((envConsistent_iff_transcriptEnvironmentEvent E t ω).mpr h)
    rw [hmass]
    simp [Dist.mass]

/-- One sampled system realizes at most one `E`-consistent transcript
(CR18 transcript uniqueness, law-level reading). -/
theorem eq_of_envConsistent_of_systemEvent
    (E : DDE X Y) (t u : TranscriptPrefix X Y q)
    (s : DDS X Y)
    (hct : E ⊨ t) (hcu : E ⊨ u)
    (hst : s ⊩ t) (hsu : s ⊩ u) : t = u := by
  refine transcriptJointEvent_unique idSysRV (constEnvRV E)
    t u (s, PUnit.unit) ⟨hst, ?_⟩ ⟨hsu, ?_⟩
  · exact (envConsistent_iff_transcriptEnvironmentEvent E t _).mp hct
  · exact (envConsistent_iff_transcriptEnvironmentEvent E u _).mp hcu

section WithFiniteTranscriptsF

variable [FiniteTranscriptSpace X Y q]

/-- **Transcript data processing** (thesis Lemma 2.7 at the law level):
observing a `q`-round interaction cannot distinguish better than the laws
themselves,

    δ(tr(S,E), tr(T,E)) ≤ δ_law(S,T)

for every deterministic environment `E`. -/
theorem statDist_deterministicTranscriptDist_le_lawStatDist
    (S T : ProbPDS X Y) (E : DDE X Y) :
    δ(tr[q](S, E), tr[q](T, E)) ≤ δˡ(S.val, T.val) := by
  classical
  -- Step 1: factor each transcript mass and keep the consistency filter:
  --   Σ_t (tr(S,E)(t) − tr(T,E)(t)) = Σ_t 𝟙[Cons t]·(σ_S(t) − σ_T(t)).
  rw [statDist_eq_sum_univ]
  have hpt : ∀ t : TranscriptPrefix X Y q, (tr[q](S, E)) t -
        (tr[q](T, E)) t =
      if E ⊨ t then σ(S) t - σ(T) t else 0 := by
    intro t
    rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor S E t,
      deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor T E t,
      envFactor_eq_indicator]
    by_cases hc : E ⊨ t <;> simp [hc]
  -- Step 2: bound each consistent gap by the pointwise law gaps on the
  -- system event (event-mass difference ≤ sum of gaps):
  --   σ_S(t) − σ_T(t) ≤ Σ_s 𝟙[sysEvent t s]·(S s − T s).
  have hmid : (∑ t : TranscriptPrefix X Y q, max ((tr[q](S, E)) t -
        (tr[q](T, E)) t) 0) ≤
      ∑ t : TranscriptPrefix X Y q, if E ⊨ t then
          (S.val.sum fun s w =>
            if transcriptSystemEvent
                idSysRV t.1 t.2 s
            then max (w - T.val s) 0 else 0)
        else 0 := by
    refine Finset.sum_le_sum fun t _ => ?_
    rw [hpt t]
    by_cases hc : E ⊨ t
    · simp only [if_pos hc]
      refine max_le ?_ (Finset.sum_nonneg fun s _ => ?_)
      · simpa [hc] using
          mass_tsub_mass_le_sum_gap S.val T.2.nonNeg
            (transcriptSystemEvent
              idSysRV t.1 t.2)
      · by_cases h : transcriptSystemEvent idSysRV t.1 t.2 s
        · simp [h, le_max_right]
        · simp [h]
    · simp [hc]
  refine le_trans hmid ?_
  -- Step 3: swap the sums; each sampled system realizes at most one
  -- consistent transcript (uniqueness), so it contributes at most one copy
  -- of its law gap:
  --   Σ_t 𝟙[Cons t] Σ_s 𝟙[Ev_t s]·gap(s) = Σ_s gap(s)·#{consistent t of s}
  --                                       ≤ Σ_s gap(s) = δ_law(S,T).
  have hpush : ∀ t : TranscriptPrefix X Y q, (if E ⊨ t then
        (S.val.sum fun s w =>
          if transcriptSystemEvent
              idSysRV t.1 t.2 s
          then max (w - T.val s) 0 else 0)
      else 0) =
      ∑ s ∈ S.val.support, if E ⊨ t ∧
            transcriptSystemEvent
              idSysRV t.1 t.2 s
        then max (S.val s - T.val s) 0 else 0 := by
    intro t
    by_cases hc : E ⊨ t <;> simp [hc, Finsupp.sum]
  have huniq : ∀ s ∈ S.val.support, (∑ t : TranscriptPrefix X Y q, if E ⊨ t ∧
            transcriptSystemEvent
              idSysRV t.1 t.2 s
        then max (S.val s - T.val s) 0 else 0) ≤ max (S.val s - T.val s) 0 := by
    intro s _
    by_cases hex : ∃ t : TranscriptPrefix X Y q, E ⊨ t ∧
        transcriptSystemEvent
          idSysRV t.1 t.2 s
    · obtain ⟨t₀, hc₀, hs₀⟩ := hex
      rw [Finset.sum_eq_single t₀
        (fun t _ hne => by
          by_cases h : E ⊨ t ∧
              transcriptSystemEvent
                idSysRV t.1 t.2 s
          · exact absurd
              (eq_of_envConsistent_of_systemEvent E t t₀ s h.1 hc₀ h.2 hs₀) hne
          · simp [h])
        (fun h => absurd (Finset.mem_univ _) h)]
      split
      · exact le_refl _
      · exact le_max_right _ _
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun t _ => ?_))
        (le_max_right _ _)
      exact if_neg fun h => hex ⟨t, h⟩
  calc (∑ t : TranscriptPrefix X Y q, if E ⊨ t then
        (S.val.sum fun s w =>
          if transcriptSystemEvent
              idSysRV t.1 t.2 s
          then max (w - T.val s) 0 else 0)
      else 0)
      = ∑ s ∈ S.val.support, ∑ t : TranscriptPrefix X Y q, if E ⊨ t ∧
              transcriptSystemEvent
                idSysRV t.1 t.2 s
          then max (S.val s - T.val s) 0 else 0 := by
        simp only [hpush]
        exact Finset.sum_comm
    _ ≤ ∑ s ∈ S.val.support, max (S.val s - T.val s) 0 :=
        Finset.sum_le_sum huniq
    _ = δˡ(S.val, T.val) := rfl

/-- **Thm 2.31, lower bound (pointwise representative form).**  The adaptive
transcript advantage of `S,T` is a lower bound on the law distance of *every*
`q`-transcript-equivalent pair of representatives:

    (∀ E : tr(S′,E) = tr(S,E))  ∧  (∀ E : tr(T′,E) = tr(T,E))
        ⟹   Adv_q(S,T) ≤ δ_law(S′,T′). -/
theorem adaptiveTranscriptAdvantage_le_lawStatDist_of_equiv
    (S T S' T' : ProbPDS X Y)
    (hS' : ∀ E : QQueryEnvironment X Y q, tr[q](S', E.1) = tr[q](S, E.1))
    (hT' : ∀ E : QQueryEnvironment X Y q, tr[q](T', E.1) = tr[q](T, E.1)) :
    Adv[q](S, T) ≤ (δˡ(S'.val, T'.val) : ℝ) := by
  have hnn : 0 ≤ δˡ(S'.val, T'.val) :=
    Finset.sum_nonneg fun a _ => le_max_right _ _
  have h := adaptiveTranscriptAdvantage_le_of_pointwise (q := q) S T
    ⟨δˡ(S'.val, T'.val), hnn⟩ ?_
  · simpa using h
  intro E
  rw [← hS' E, ← hT' E]
  simpa using statDist_deterministicTranscriptDist_le_lawStatDist S' T' E.1

/-- Special case `S′ := S`, `T′ := T`:  Adv_q(S,T) ≤ δ_law(S,T). -/
theorem adaptiveTranscriptAdvantage_le_lawStatDist (S T : ProbPDS X Y) :
    Adv[q](S, T) ≤ (δˡ(S.val, T.val) : ℝ) :=
  adaptiveTranscriptAdvantage_le_lawStatDist_of_equiv S T S T
    (fun _ => rfl) (fun _ => rfl)

/-- The thesis `Δ_q`: infimum of law distances over `q`-transcript-equivalent
representative pairs (Def 2.28, `q`-bounded, law level). -/
noncomputable def lawDelta (S T : ProbPDS X Y) : ℝ := sInf ((fun p : ProbPDS X Y × ProbPDS X Y =>
      (δˡ(p.1.val, p.2.val) : ℝ)) ''
    {p | (∀ E : QQueryEnvironment X Y q, tr[q](p.1, E.1) = tr[q](S, E.1)) ∧
      (∀ E : QQueryEnvironment X Y q, tr[q](p.2, E.1) = tr[q](T, E.1))})

@[inherit_doc lawDelta]
scoped notation:max "Δ[" q "](" S ", " T ")" => lawDelta (q := q) S T

/-- **Thm 2.31, lower bound:**  Adv_q(S,T) ≤ Δ_q(S,T).  (The attainment
direction — existence of representatives with `δ_law = Adv`, by the thesis
successor induction with product couplings, Lemma 2.33 — is not formalized;
the plan is recorded in `DESIGN.md` §9.) -/
theorem adaptiveTranscriptAdvantage_le_lawDelta (S T : ProbPDS X Y) :
    Adv[q](S, T) ≤ Δ[q](S, T) := by
  refine le_csInf ⟨(δˡ(S.val, T.val) : ℝ), ⟨(S, T), ⟨fun _ => rfl, fun _ => rfl⟩, rfl⟩⟩ ?_
  rintro b ⟨⟨S', T'⟩, ⟨hS', hT'⟩, rfl⟩
  exact adaptiveTranscriptAdvantage_le_lawStatDist_of_equiv S T S' T' hS' hT'

end WithFiniteTranscriptsF

/-! ### The coupling reading (thesis Thm 2.32, upper-bound direction)

A coupling of the two laws bounds the law distance — hence the advantage —
by the probability that the coupled systems differ.  Marginals are stated by
event masses, so no finiteness or decidable equality of the carrier is
needed. -/

/-- `δ_law(P,Q) ≤ Pr_J[a ≠ b]` for any joint `J` with the correct marginals. -/
theorem lawStatDist_le_mass_ne {A : Type*}
    (P Q : Dist A) {J : Dist (A × A)} (hJnn : J.NonNeg)
    (h_fst : ∀ a, P a = J.mass fun p => p.1 = a)
    (h_snd : ∀ a, Q a = J.mass fun p => p.2 = a) :
    δˡ(P, Q) ≤ J.mass fun p => p.1 ≠ p.2 := by
  classical
  -- Pointwise:  P a − Q a ≤ J{fst = a} − J{fst = a ∧ snd = a}
  --                       = J{fst = a ∧ snd ≠ a}.
  have hpt : ∀ a, max (P a - Q a) 0 ≤ J.mass fun p => p.1 = a ∧ p.2 ≠ a := by
    intro a
    have hsplit := mass_eq_mass_and_add_mass_and_not J
      (fun p => p.1 = a) (fun p => p.2 = a)
    have hle : J.mass (fun p => p.1 = a ∧ p.2 = a) ≤ Q a := by
      rw [h_snd a]
      exact mass_mono hJnn fun p hp => hp.2
    refine max_le ?_ (hJnn.mass_nonneg _)
    calc P a - Q a
        ≤ J.mass (fun p => p.1 = a) -
            J.mass (fun p => p.1 = a ∧ p.2 = a) := by
          rw [h_fst a]
          exact sub_le_sub_left hle _
      _ = J.mass fun p => p.1 = a ∧ p.2 ≠ a := by
          rw [hsplit, add_sub_cancel_left]
  -- Sum over P's support; the disagreement events are disjoint across `a`
  -- (a pair `p` matches only `a = p.1`).
  unfold lawStatDist
  simp only [Finsupp.sum]
  have hexp : ∀ a, (J.mass fun p => p.1 = a ∧ p.2 ≠ a) =
      ∑ p ∈ J.support, if p.1 = a ∧ p.2 ≠ a then J p else 0 := by
    intro a
    unfold Dist.mass
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr
  calc (∑ a ∈ P.support, max (P a - Q a) 0)
      ≤ ∑ a ∈ P.support, J.mass fun p => p.1 = a ∧ p.2 ≠ a := Finset.sum_le_sum fun a _ => hpt a
    _ = ∑ p ∈ J.support, ∑ a ∈ P.support, if p.1 = a ∧ p.2 ≠ a then J p else 0 := by
        simp only [hexp]
        exact Finset.sum_comm
    _ ≤ ∑ p ∈ J.support, if p.1 ≠ p.2 then J p else 0 := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hne : p.1 ≠ p.2
        · -- only a = p.1 can contribute
          calc (∑ a ∈ P.support, if p.1 = a ∧ p.2 ≠ a then J p else 0)
              ≤ ∑ a ∈ P.support, if p.1 = a then J p else 0 := Finset.sum_le_sum fun a _ => by
                  by_cases h : p.1 = a ∧ p.2 ≠ a
                  · rw [if_pos h, if_pos h.1]
                  · rw [if_neg h]
                    by_cases h1 : p.1 = a
                    · simp [h1, hJnn p]
                    · simp [h1]
            _ ≤ if p.1 ≠ p.2 then J p else 0 := by
                rw [Finset.sum_ite_eq]
                split
                · simp [hne]
                · simp [hne, hJnn p]
        · -- p.1 = p.2: no `a` matches (the `p.2 ≠ a` conjunct fails at a = p.1)
          have hp : p.1 = p.2 := not_not.mp hne
          refine le_trans (le_of_eq (Finset.sum_eq_zero fun a _ => ?_)) ?_
          · exact if_neg fun h => h.2 (hp ▸ h.1)
          · by_cases h : p.1 ≠ p.2
            · simp [h, hJnn p]
            · simp [h]
    _ = J.mass fun p => p.1 ≠ p.2 := by
        unfold Dist.mass
        rw [Finsupp.sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        congr

/-- `lawStatDist_le_mass_ne` through pushforwards: a joint law over two seed
spaces with the correct marginals bounds the law distance of the two
pushforwards by the mass of the disagreement event.  This is the Δ-face of
the coupling method whose equality face is `Dist.fTransform_eq_of_coupling`;
the `Machine.lawOf` corollary lives in `RandomSystems/Jost/LawCoupling.lean`. -/
theorem lawStatDist_fTransform_le_mass_ne {Ω₁ Ω₂ B : Type*}
    (f₁ : Ω₁ → B) (f₂ : Ω₂ → B) {μ₁ : Dist Ω₁} {μ₂ : Dist Ω₂}
    {γ : Dist (Ω₁ × Ω₂)} (hγnn : γ.NonNeg)
    (h_fst : Dist.fTransform Prod.fst γ = μ₁)
    (h_snd : Dist.fTransform Prod.snd γ = μ₂) :
    δˡ(Dist.fTransform f₁ μ₁, Dist.fTransform f₂ μ₂) ≤
      γ.mass fun p => f₁ p.1 ≠ f₂ p.2 := by
  classical
  set J : Dist (B × B) := Dist.fTransform (fun p => (f₁ p.1, f₂ p.2)) γ with hJ
  have hJnn : J.NonNeg := hγnn.fTransform _
  have h_fst' : ∀ b, Dist.fTransform f₁ μ₁ b = J.mass fun p => p.1 = b := by
    intro b
    rw [← h_fst, Dist.fTransform_comp, Dist.fTransform_apply_eq_mass, hJ,
      Dist.mass_fTransform]
    exact Dist.mass_congr γ fun a => Iff.rfl
  have h_snd' : ∀ b, Dist.fTransform f₂ μ₂ b = J.mass fun p => p.2 = b := by
    intro b
    rw [← h_snd, Dist.fTransform_comp, Dist.fTransform_apply_eq_mass, hJ,
      Dist.mass_fTransform]
    exact Dist.mass_congr γ fun a => Iff.rfl
  refine (lawStatDist_le_mass_ne _ _ hJnn h_fst' h_snd').trans (le_of_eq ?_)
  rw [hJ, Dist.mass_fTransform]

section WithFiniteTranscriptsG

variable [FiniteTranscriptSpace X Y q]

/-- **Thm 2.32, upper-bound direction (law level).**  Any coupling of the two
laws bounds the adaptive transcript advantage by its disagreement
probability:

    Adv_q(S,T) ≤ Pr_J[s ≠ s′]. -/
theorem adaptiveTranscriptAdvantage_le_mass_ne
    (S T : ProbPDS X Y)
    {J : Dist (DDS X Y × DDS X Y)} (hJnn : J.NonNeg)
    (h_fst : ∀ s, S.val s = J.mass fun p => p.1 = s)
    (h_snd : ∀ s, T.val s = J.mass fun p => p.2 = s) :
    Adv[q](S, T) ≤ (J.mass (fun p => p.1 ≠ p.2) : ℝ) :=
  le_trans (adaptiveTranscriptAdvantage_le_lawStatDist S T)
    (lawStatDist_le_mass_ne S.val T.val hJnn h_fst h_snd)

end WithFiniteTranscriptsG

end FundamentalLowerBound

/-! ## Filtered (restricted-adversary) advantage

The paper's H-coefficient restricts the adversary class — it forbids
"pointless" queries (§3.4), whose responses are already determined.  This is
NOT WLOG when the two worlds are not both permutations (a pointless inverse
query distinguishes a permutation from a memoryless random function with
advantage `≈ 1`), so the ±rnd-comparison bounds are genuinely *restricted*
advantages.  We model the restriction by a transcript filter `Filt` and take
the supremum only over environments that never leave the `Filt` region. -/

section FilteredAdvantage

variable [FiniteTranscriptSpace X Y q] [DecidableEq X]

/-- An environment *respects* the filter `Filt` when every transcript it can
realize (is consistent with) satisfies `Filt` — i.e. the adversary stays in
the compatible/allowed region (paper §3.4). -/
def EnvRespects (Filt : TranscriptPrefix X Y q → Prop)
    (E : QQueryEnvironment X Y q) : Prop :=
  ∀ t, EnvConsistent E.1 t → Filt t

/-- Lift a predicate on visible input histories to transcript prefixes.  The
input projection is the first vector component, converted to the list on
which a `PFunDDS` domain predicate is defined. -/
def liftHist (P : List X → Prop) : TranscriptPrefix X Y q → Prop :=
  fun t => P t.1.toList

/-- An exact-query distinguisher respects a visible-history predicate when
every transcript consistent with its environment has an admitted input
history. -/
def DistinguisherRespects (P : List X → Prop) (d : PFunDDS.DDD X Y) : Prop :=
  ∀ t : TranscriptPrefix X Y q,
    EnvConsistent (PFunDDS.ddToDDE d) t → liftHist P t

omit [DecidableEq X] in
/-- History-dependent respecting padding produces a `P`-respecting exact-query
distinguisher. -/
theorem distinguisherRespects_padRespecting
    (P : List X → Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : PFunDDS.DDD X Y) :
    DistinguisherRespects (q := q) P
      (PFunDDS.padRespecting P q hExt h0 d) := by
  intro t hconsistent
  unfold liftHist
  have hstate : ∀ n : ℕ, n ≤ q →
      (PFunDDS.padRespectingState P q hExt h0 d
        ((t.2.toList.take n).map some)).1.1 = t.1.toList.take n := by
    intro n hn
    induction n with
    | zero => simp [PFunDDS.padRespectingState]
    | succ n ih =>
        have hnlt : n < q := by omega
        have hny : n < t.2.toList.length := by simpa using hnlt
        have hnx : n < t.1.toList.length := by simpa using hnlt
        have htakeY := list_take_succ_eq_take_append_get
          (l := t.2.toList) ⟨n, hny⟩
        have htakeX := list_take_succ_eq_take_append_get
          (l := t.1.toList) ⟨n, hnx⟩
        rw [htakeY, List.map_append]
        simp only [List.map_singleton]
        rw [PFunDDS.padRespectingState_append_of_lt P q hExt h0 d _ _ (by
          simp; exact hnlt)]
        have hquery := hconsistent ⟨n, hnlt⟩
        rw [PFunDDS.ddToDDE_padRespecting_of_lt P q hExt h0 d (by
          simp; exact hnlt)] at hquery
        have hnext := Option.some.inj hquery
        simp only
        calc
          _ = (PFunDDS.padRespectingState P q hExt h0 d
                ((t.2.toList.take n).map some)).1.1 ++
              [t.1.get ⟨n, hnlt⟩] := by
                congr 1
                simpa using hnext
          _ = t.1.toList.take n ++ [t.1.get ⟨n, hnlt⟩] := by
                rw [ih (by omega)]
          _ = _ := htakeX.symm
  have hfull := hstate q (le_refl q)
  have hp := (PFunDDS.padRespectingState P q hExt h0 d
    ((t.2.toList.take q).map some)).1.2
  rw [hfull] at hp
  have ht : t.1.toList.take q = t.1.toList :=
    List.take_of_length_le (by simp)
  rw [ht] at hp
  exact hp

/-- Finite-query normalization for a general domain filter.  Besides exact
query count, the normalized point distinguishers must respect the filtered
history predicate, and their base-system advantage must dominate the original
filtered advantage.

The respect clause is the load-bearing completion obligation for a general
prefix-closed predicate: prefix closure alone does not say that every admitted
short history has an admitted length-`q` continuation. -/
def DeltaFilterDomFiniteQueryNormalization
    (P : List X → Prop) (hP : PrefixClosed P) (q : ℕ)
    (S T : PFunPDS X Y) : Prop :=
  ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
    ∃ D' : Dist (PFunDDS.DDD X Y),
      D'.isProbDist ∧
      (∀ d ∈ D'.support,
        QueriesExactly (PFunDDS.ddToDDE d) q ∧
          DistinguisherRespects (q := q) P d) ∧
      advantage D (PFunPDS.filterDom P hP S) (PFunPDS.filterDom P hP T) ≤
        advantage D' S T

omit [DecidableEq X] in
/-- Finite-query normalization for an extensible, bounded domain predicate.
Suppression first converts filtered interaction into base-system interaction;
respecting padding then completes the already-stopped run to exactly `q`
queries without changing its verdict. -/
theorem deltaFilterDomFiniteQueryNormalization_of_extensible
    (P : List X → Prop) (hP : PrefixClosed P) (q : ℕ)
    (S T : PFunPDS X Y)
    (hExt : QExtensible P q) (hBound : QBounded P q) (h0 : P [])
    (hS : CondEquiv.TotalOnNonempty S)
    (hT : CondEquiv.TotalOnNonempty T) :
    DeltaFilterDomFiniteQueryNormalization P hP q S T := by
  intro D hD
  let normalize : PFunDDS.DDD X Y → PFunDDS.DDD X Y :=
    PFunDDS.padRespecting P q hExt h0 ∘ PFunDDS.suppressViolating P
  refine ⟨Dist.fTransform normalize D,
    Dist.fTransform_isProbDist normalize hD, ?_, ?_⟩
  · intro d hd
    obtain ⟨d₀, _hd₀, hd₀⟩ := mem_support_fTransform _ _ hd
    subst d
    change
      QueriesExactly (PFunDDS.ddToDDE
        (PFunDDS.padRespecting P q hExt h0 (PFunDDS.suppressViolating P d₀))) q ∧
      DistinguisherRespects (q := q) P
        (PFunDDS.padRespecting P q hExt h0 (PFunDDS.suppressViolating P d₀))
    exact ⟨PFunDDS.queriesExactly_ddToDDE_padRespecting
        P q hExt h0 (PFunDDS.suppressViolating P d₀),
      distinguisherRespects_padRespecting
        P q hExt h0 (PFunDDS.suppressViolating P d₀)⟩
  · calc
      advantage D (PFunPDS.filterDom P hP S) (PFunPDS.filterDom P hP T) =
          advantage (Dist.fTransform (PFunDDS.suppressViolating P) D) S T :=
        advantage_suppressViolating_eq_filterDom P hP D S T hS hT
      _ ≤ advantage (Dist.fTransform normalize D) S T := by
        rw [show normalize =
            PFunDDS.padRespecting P q hExt h0 ∘ PFunDDS.suppressViolating P from rfl]
        exact advantage_suppressViolating_le_padRespecting
          P q hExt hBound h0 D S T hS hT

/-- The `Filt`-restricted adaptive transcript advantage: the supremum of the
per-environment transcript distance over environments respecting `Filt`. -/
noncomputable def filteredAdaptiveTranscriptAdvantage
    (Filt : TranscriptPrefix X Y q → Prop) (S T : ProbPDS X Y) : ℝ :=
  sSup ((fun E : QQueryEnvironment X Y q =>
      (statDist (tr[q](S, E.1)) (tr[q](T, E.1)) : ℝ)) ''
    {E | EnvRespects Filt E})

omit [DecidableEq X] in
/-- Uniform pointwise bound over respecting environments bounds the restricted
advantage. -/
theorem filteredAdaptiveTranscriptAdvantage_le_of_pointwise
    (Filt : TranscriptPrefix X Y q → Prop) (S T : ProbPDS X Y) (c : ℝ)
    (hc : 0 ≤ c)
    (h : ∀ E : QQueryEnvironment X Y q, EnvRespects Filt E →
      (statDist (tr[q](S, E.1)) (tr[q](T, E.1)) : ℝ) ≤ c) :
    filteredAdaptiveTranscriptAdvantage Filt S T ≤ c := by
  unfold filteredAdaptiveTranscriptAdvantage
  refine Real.sSup_le ?_ hc
  rintro x ⟨E, hE, rfl⟩
  exact h E hE

omit [DecidableEq X] in
/-- **Common transcript-factorization normalization.**  Suppose every
environment `E` has an allowed normalized environment `normalize E`, and the
two original transcript laws are pushforwards along the same reconstruction
map of the two normalized transcript laws.  Then restricting the environment
supremum to `Filt` loses no advantage.

This is the transcript instantiation of
`lawFamilyAdvantage_eq_restricted_of_common_fTransform`.  It is independent of
how the factorization was obtained: self-answering pointless queries is one
producer, but no query semantics or H-technique data occurs here. -/
theorem adaptiveTranscriptAdvantage_eq_filtered_of_common_fTransform
    (Filt : TranscriptPrefix X Y q → Prop) (S T : ProbPDS X Y)
    (normalize : QQueryEnvironment X Y q → QQueryEnvironment X Y q)
    (hAllowed : ∀ E, EnvRespects Filt (normalize E))
    (reconstruct : QQueryEnvironment X Y q →
      TranscriptPrefix X Y q → TranscriptPrefix X Y q)
    (hS : ∀ E,
      tr[q](S, E.1) = Dist.fTransform (reconstruct E) (tr[q](S, (normalize E).1)))
    (hT : ∀ E,
      tr[q](T, E.1) = Dist.fTransform (reconstruct E) (tr[q](T, (normalize E).1))) :
    adaptiveTranscriptAdvantage (q := q) S T =
      filteredAdaptiveTranscriptAdvantage (q := q) Filt S T := by
  let P : QQueryEnvironment X Y q → Dist (TranscriptPrefix X Y q) :=
    fun E => tr[q](S, E.1)
  let Q : QQueryEnvironment X Y q → Dist (TranscriptPrefix X Y q) :=
    fun E => tr[q](T, E.1)
  have hstat : ∀ E : QQueryEnvironment X Y q,
      (statDist (P E) (Q E) : ℝ) = δ (P E) (Q E) := by
    intro E
    exact statDist_eq_δ_of_nonneg _ _ (deterministicTranscriptDist_nonNeg T E.1)
  have hfull : adaptiveTranscriptAdvantage (q := q) S T =
      lawFamilyAdvantage P Q := by
    unfold adaptiveTranscriptAdvantage lawFamilyAdvantage
    rw [show (fun E : QQueryEnvironment X Y q =>
        (statDist (tr[q](S, E.1)) (tr[q](T, E.1)) : ℝ)) =
        (fun E => δ (P E) (Q E)) from by funext E; exact hstat E]
  have hrestricted : filteredAdaptiveTranscriptAdvantage (q := q) Filt S T =
      restrictedLawFamilyAdvantage (fun E => EnvRespects Filt E) P Q := by
    unfold filteredAdaptiveTranscriptAdvantage restrictedLawFamilyAdvantage
    rw [show (fun E : QQueryEnvironment X Y q =>
        (statDist (tr[q](S, E.1)) (tr[q](T, E.1)) : ℝ)) =
        (fun E => δ (P E) (Q E)) from by funext E; exact hstat E]
  have hbounded : BddAbove
      ((fun E : QQueryEnvironment X Y q => δ (P E) (Q E)) '' Set.univ) := by
    obtain ⟨c, hc⟩ :=
      PFunPDS.Prob.adaptiveTranscriptAdvantage_image_bddAbove (q := q) S T
    exact ⟨c, by
      rintro x ⟨E, -, rfl⟩
      calc
        δ (P E) (Q E) = (statDist (P E) (Q E) : ℝ) := (hstat E).symm
        _ ≤ c := by simpa [P, Q] using hc ⟨E, Set.mem_univ _, rfl⟩⟩
  rw [hfull, hrestricted]
  exact lawFamilyAdvantage_eq_restricted_of_common_fTransform
    (fun E : QQueryEnvironment X Y q => EnvRespects Filt E) P Q
    (fun E => deterministicTranscriptDist_nonNeg T E.1)
    hbounded normalize hAllowed reconstruct hS hT

/-- Respecting environments have zero transcript mass outside the filter. -/
theorem deterministicTranscriptDist_eq_zero_of_not_filt
    (Filt : TranscriptPrefix X Y q → Prop) (T : ProbPDS X Y)
    (E : QQueryEnvironment X Y q) (hE : EnvRespects Filt E)
    (t : TranscriptPrefix X Y q) (ht : ¬ Filt t) :
    tr[q](T, E.1) t = 0 := by
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    envFactor_eq_indicator]
  by_cases hc : E.1 ⊨ t
  · exact absurd (hE t hc) ht
  · rw [if_neg hc, mul_zero]

/-- On a respecting environment, a domain filter is invisible to the
length-`q` deterministic transcript law of the base system. -/
theorem deterministicTranscriptDist_filterDom_eq
    (P : List X → Prop) (hP : PrefixClosed P) (S : ProbPDS X Y)
    (E : QQueryEnvironment X Y q) (hE : EnvRespects (liftHist P) E) :
    tr[q](
      (⟨PFunPDS.filterDom P hP S.val,
        (PFunPDS.isProbDist_filterDom_iff P hP S.property.nonNeg).mpr S.property⟩ : ProbPDS X Y),
      E.1) = tr[q](S, E.1) := by
  ext t
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor]
  by_cases hc : E.1 ⊨ t
  · have hsys :
        σ((⟨PFunPDS.filterDom P hP S.val,
            (PFunPDS.isProbDist_filterDom_iff P hP S.property.nonNeg).mpr S.property⟩ : ProbPDS X Y)) t =
          σ(S) t := by
      unfold sysFactor PFunPDE.transcriptSystemFactor PFunPDS.filterDom
      rw [Dist.mass_fTransform]
      apply Dist.mass_congr
      intro s
      constructor
      · intro hs i hi
        exact (PFunDDS.filterDom_apply_eq_some_iff P hP s
          (hP (List.take_prefix _ _) (hE t hc))).mp (hs i hi)
      · intro hs i hi
        exact (PFunDDS.filterDom_apply_eq_some_iff P hP s
          (hP (List.take_prefix _ _) (hE t hc))).mpr (hs i hi)
    rw [hsys]
  · rw [envFactor_eq_indicator E.1 t, if_neg hc, mul_zero, mul_zero]

/-- **Filtered H-technique, ratio form.**  Same as
`adv_le_of_fixedQuery_ratio_of_good`, but the good-transcript ratio need only
hold on `Filt` transcripts and the bad bound only over `Filt`-respecting
environments; the conclusion bounds the restricted advantage. -/
theorem adv_le_of_fixedQuery_ratio_of_good_filtered
    (Filt : TranscriptPrefix X Y q → Prop)
    (S T : ProbPDS X Y) (Bad : TranscriptPrefix X Y q → Prop)
    (eps δb : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_ratio : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      Filt t → ¬ Bad t →
      (1 - eps) * (tr(T, xs)) t ≤ (tr(S, xs)) t)
    (h_bad : ∀ E : QQueryEnvironment X Y q, EnvRespects Filt E →
      Pr[Bad ∣ tr[q](T, E.1)] ≤ δb) :
    filteredAdaptiveTranscriptAdvantage Filt S T ≤ ((δb + eps : NNReal) : ℝ) := by
  refine filteredAdaptiveTranscriptAdvantage_le_of_pointwise Filt S T _
    (by positivity) ?_
  intro E hE
  -- pointwise ratio on ¬Bad: split on whether the transcript is in the filter
  have h_pointwise : ∀ t, ¬ Bad t →
      (1 - eps) * tr[q](T, E.1) t ≤ tr[q](S, E.1) t := by
    intro t hnb
    by_cases hf : Filt t
    · -- in-filter: Layer B transfer with the enlarged bad set `Bad ∨ ¬Filt`
      refine deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
        S T E (fun t' => Bad t' ∨ ¬ Filt t') eps ?_ t ?_
      · intro xs t' ht'
        rw [not_or, not_not] at ht'
        exact h_ratio xs t' ht'.2 ht'.1
      · rw [not_or, not_not]; exact ⟨hnb, hf⟩
    · -- out-of-filter: the ideal transcript vanishes
      rw [deterministicTranscriptDist_eq_zero_of_not_filt Filt T E hE t hf,
        mul_zero]
      exact deterministicTranscriptDist_nonNeg S E.1 t
  have h :=
    RandomSystems.hTechnique_ratio (tr[q](S, E.1)) (tr[q](T, E.1)) Bad eps
      (deterministicTranscriptDist_nonNeg S E.1)
      (deterministicTranscriptDist_nonNeg T E.1)
      (by rw [deterministicTranscriptDist_weight_eq_one S E hS,
        deterministicTranscriptDist_weight_eq_one T E hT])
      (by rw [deterministicTranscriptDist_weight_eq_one T E hT])
      h_pointwise
  calc (statDist (tr[q](S, E.1)) (tr[q](T, E.1)) : ℝ)
      ≤ Pr[Bad ∣ tr[q](T, E.1)] + (eps : ℝ) := h
    _ ≤ ((δb + eps : NNReal) : ℝ) := by
        push_cast
        exact add_le_add (h_bad E hE) le_rfl

omit [DecidableEq X] in
/-- A respecting environment's per-transcript distance is `≤` the filtered
advantage (the `sup` includes it; the family is bounded by `1 =` the
`KStepTotal` transcript weight).  Generic in the filter. -/
theorem statDist_le_filteredAdv
    (Filt : TranscriptPrefix X Y q → Prop)
    (S T' : ProbPDS X Y) (hS : S.KStepTotal q)
    (E : QQueryEnvironment X Y q) (hE : EnvRespects Filt E) :
    (statDist (tr[q](S, E.1)) (tr[q](T', E.1)) : ℝ) ≤
      filteredAdaptiveTranscriptAdvantage Filt S T' := by
  refine le_csSup ⟨1, ?_⟩ ⟨E, hE, rfl⟩
  rintro x ⟨E', _, rfl⟩
  refine le_trans (statDist_le_weight
    (deterministicTranscriptDist_nonNeg S E'.1)
    (deterministicTranscriptDist_nonNeg T' E'.1)) ?_
  exact_mod_cast deterministicTranscriptDist_weight_le_one S E' hS

omit [DecidableEq X] [FiniteTranscriptSpace X Y q] in
/-- Every exact-`q` environment respects the length-`≤q` history predicate. -/
theorem envRespects_liftHist_length_le (E : QQueryEnvironment X Y q) :
    EnvRespects (liftHist (q := q) (fun l : List X => l.length ≤ q)) E := by
  intro t _
  simp [liftHist, List.Vector.toList_length]

omit [DecidableEq X] in
/-- The count-filter restriction on environments is vacuous at transcript
length `q`; its filtered advantage is the ordinary adaptive transcript
advantage. -/
theorem filteredAdaptiveTranscriptAdvantage_liftHist_length_le_eq
    (S T : ProbPDS X Y) (hS : S.KStepTotal q) :
    filteredAdaptiveTranscriptAdvantage (q := q)
        (liftHist (q := q) (fun l : List X => l.length ≤ q)) S T =
      adaptiveTranscriptAdvantage (q := q) S T := by
  apply le_antisymm
  · refine filteredAdaptiveTranscriptAdvantage_le_of_pointwise _ S T _
      (adaptiveTranscriptAdvantage_nonneg (q := q) S T) ?_
    intro E _
    exact deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
      (q := q) S T E
  · unfold adaptiveTranscriptAdvantage
    apply Real.sSup_le
    · rintro _ ⟨E, _, rfl⟩
      exact statDist_le_filteredAdv (q := q)
        (liftHist (q := q) (fun l : List X => l.length ≤ q))
        S T hS E (envRespects_liftHist_length_le E)
    · exact Real.sSup_nonneg (by
        rintro _ ⟨E, _, rfl⟩
        exact statDist_nonneg _ _)

omit [DecidableEq X] in
/-- A probability distribution of exact-`q`, `P`-respecting distinguishers is
bounded by the transcript advantage over `liftHist P`-respecting
environments. -/
theorem advantage_le_filteredAdaptiveTranscriptAdvantage_of_queriesExactly
    (P : List X → Prop) (S T : ProbPDS X Y)
    (D : Dist (PFunDDS.DDD X Y)) (hD : D.isProbDist)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) q)
    (hRespect : ∀ d ∈ D.support, DistinguisherRespects (q := q) P d)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q) :
    advantage D S.val T.val ≤
      filteredAdaptiveTranscriptAdvantage (q := q) (liftHist (q := q) P) S T := by
  apply advantage_le_of_single_le D S.val T.val _ hD
  intro d hd
  let E : QQueryEnvironment X Y q :=
    ⟨PFunDDS.ddToDDE d,
      PFunPDE.DDEKQueryTotal_of_queriesExactly (PFunDDS.ddToDDE d) (hQ d hd)⟩
  have hE : EnvRespects (liftHist (q := q) P) E := hRespect d hd
  exact le_trans
    (advantage_single_le_deterministicTranscriptDist_statDist_of_queriesExactly
      (q := q) S T d (hQ d hd) hS hT)
    (by simpa [E] using
      statDist_le_filteredAdv (q := q) (liftHist (q := q) P) S T hS E hE)

omit [DecidableEq X] in
/-- **Filter-to-restricted-transcript bridge.**  A normalized distinguisher
of the `filterDom P` systems contributes only through `P`-respecting visible
histories, hence its advantage is bounded by the supremum over respecting
base-system environments. -/
theorem maxAdvantage_filterDom_le_filteredAdaptiveTranscriptAdvantage
    (P : List X → Prop) (hP : PrefixClosed P) (S T : ProbPDS X Y)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (hNorm : DeltaFilterDomFiniteQueryNormalization P hP q S.val T.val) :
    (Δ(PFunPDS.filterDom P hP S.val, PFunPDS.filterDom P hP T.val) : ℝ) ≤
      filteredAdaptiveTranscriptAdvantage (q := q) (liftHist (q := q) P) S T := by
  have hnonneg :
      0 ≤ filteredAdaptiveTranscriptAdvantage (q := q) (liftHist (q := q) P) S T := by
    obtain ⟨D, hD, hQR, _⟩ :=
      hNorm (rejectDistinguisher X Y) (rejectDistinguisher_isProbDist X Y)
    have hDne : D ≠ 0 := by
      intro hzero
      subst D
      simp [Dist.isProbDist, Dist.weight] at hD
    obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr hDne
    let E : QQueryEnvironment X Y q :=
      ⟨PFunDDS.ddToDDE d,
        PFunPDE.DDEKQueryTotal_of_queriesExactly
          (PFunDDS.ddToDDE d) (hQR d hd).1⟩
    exact le_trans (statDist_nonneg _ _)
      (statDist_le_filteredAdv (q := q) (liftHist (q := q) P) S T hS E (hQR d hd).2)
  unfold maxAdvantage
  apply Real.sSup_le
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨D', hD', hQR, hle⟩ := hNorm D hD
    exact hle.trans
      (advantage_le_filteredAdaptiveTranscriptAdvantage_of_queriesExactly
        (q := q) P S T D' hD' (fun d hd => (hQR d hd).1)
          (fun d hd => (hQR d hd).2) hS hT)
  · exact hnonneg

omit [DecidableEq X] in
/-- **Filter monotonicity**: strengthening the filter shrinks the respecting
environment class, hence the restricted advantage.  Reuses the weaker-filter
bound (e.g. a non-pointlessness birthday bound) at a stronger filter. -/
theorem filteredAdv_mono
    (Filt Filt' : TranscriptPrefix X Y q → Prop)
    (himp : ∀ t, Filt' t → Filt t)
    (S T' : ProbPDS X Y) (hS : S.KStepTotal q) :
    filteredAdaptiveTranscriptAdvantage Filt' S T' ≤
      filteredAdaptiveTranscriptAdvantage Filt S T' := by
  refine Real.sSup_le ?_ (Real.sSup_nonneg ?_)
  · rintro x ⟨E, hE, rfl⟩
    exact statDist_le_filteredAdv Filt S T' hS E (fun t hc => himp t (hE t hc))
  · rintro x ⟨E', _, rfl⟩; exact statDist_nonneg _ _

omit [DecidableEq X] in
/-- **Filtered triangle inequality** (from `statDist_triangle` +
`filteredAdaptiveTranscriptAdvantage_le_of_pointwise` + `statDist_le_filteredAdv`).
Generic in the filter. -/
theorem filteredAdv_triangle
    (Filt : TranscriptPrefix X Y q → Prop)
    (S T' U : ProbPDS X Y) (hS : S.KStepTotal q) (hT' : T'.KStepTotal q) :
    filteredAdaptiveTranscriptAdvantage Filt S U ≤
      filteredAdaptiveTranscriptAdvantage Filt S T'
        + filteredAdaptiveTranscriptAdvantage Filt T' U := by
  refine filteredAdaptiveTranscriptAdvantage_le_of_pointwise Filt S U _
    (add_nonneg (Real.sSup_nonneg ?_) (Real.sSup_nonneg ?_)) (fun E hE => ?_)
  · rintro x ⟨E', _, rfl⟩; exact statDist_nonneg _ _
  · rintro x ⟨E', _, rfl⟩; exact statDist_nonneg _ _
  · exact le_trans (by exact_mod_cast statDist_triangle _ _ _)
      (add_le_add (statDist_le_filteredAdv Filt S T' hS E hE)
        (statDist_le_filteredAdv Filt T' U hT' E hE))

omit [DecidableEq X] in
/-- **Filtered symmetry** (`statDist_symm_of_eq_weight`; the `KStepTotal`
transcript weights are both `1`).  Generic in the filter. -/
theorem filteredAdv_symm
    (Filt : TranscriptPrefix X Y q → Prop)
    (S T' : ProbPDS X Y) (hS : S.KStepTotal q) (hT' : T'.KStepTotal q) :
    filteredAdaptiveTranscriptAdvantage Filt S T' =
      filteredAdaptiveTranscriptAdvantage Filt T' S := by
  unfold filteredAdaptiveTranscriptAdvantage
  congr 1
  ext x
  constructor
  · rintro ⟨E, hE, rfl⟩
    refine ⟨E, hE, ?_⟩
    show (↑(statDist (tr[q](T', E.1)) (tr[q](S, E.1))) : ℝ)
      = ↑(statDist (tr[q](S, E.1)) (tr[q](T', E.1)))
    exact_mod_cast statDist_symm_of_eq_weight _ _ (by
      rw [deterministicTranscriptDist_weight_eq_one _ E hT',
        deterministicTranscriptDist_weight_eq_one _ E hS])
  · rintro ⟨E, hE, rfl⟩
    refine ⟨E, hE, ?_⟩
    show (↑(statDist (tr[q](S, E.1)) (tr[q](T', E.1))) : ℝ)
      = ↑(statDist (tr[q](T', E.1)) (tr[q](S, E.1)))
    exact_mod_cast statDist_symm_of_eq_weight _ _ (by
      rw [deterministicTranscriptDist_weight_eq_one _ E hS,
        deterministicTranscriptDist_weight_eq_one _ E hT'])

/-! ### Filtered extended / representative endpoints

The `±rnd`-comparison lemmas (PRP-RND, HCTR2 main lemma) that need BOTH the
extended-transcript good ratio (to make world X exactly computable) AND the
pointless-query filter (world X is a permutation, so a pointless query
distinguishes it trivially) — the filter enters only on the bad-bound side
(pointless environments force a collision, so their `Pr[Bad] = 1`), while the
extended good ratio holds unconditionally on `¬Bad`. -/

section FilteredExtended

variable {Ω Ω' Z : Type*} [Fintype Z] [DecidableEq Z]
variable [DiscreteTranscriptSpace X Y q]

omit [DecidableEq X] [DecidableEq Z] in
/-- **Filtered extended-transcript H-technique (ratio form).**  As
`adv_le_of_extended_ratio_of_good`, but the supremum is taken only over
`Filt`-respecting environments and the bad bound is required only there —
concluding the `Filt`-restricted advantage. -/
theorem adv_le_of_extended_ratio_of_good_filtered
    (Filt : TranscriptPrefix X Y q → Prop)
    (S T : ProbPDS X Y)
    (extS extT : QQueryEnvironment X Y q → Dist (TranscriptPrefix X Y q × Z))
    (Bad : TranscriptPrefix X Y q × Z → Prop) (eps δb : NNReal)
    (h_nnS : ∀ E, (extS E).NonNeg)
    (h_nnT : ∀ E, (extT E).NonNeg)
    (h_projS : ∀ E, π₁⋆ (extS E) = tr[q](S, E.1))
    (h_projT : ∀ E, π₁⋆ (extT E) = tr[q](T, E.1))
    (h_weight : ∀ E, (extS E).weight = (extT E).weight)
    (h_le_one : ∀ E, (extT E).weight ≤ 1)
    (h_ratio : ∀ E (tz : TranscriptPrefix X Y q × Z), ¬ Bad tz →
      (1 - eps) * (extT E) tz ≤ (extS E) tz)
    (h_bad : ∀ E, EnvRespects Filt E → Pr[Bad ∣ extT E] ≤ δb) :
    filteredAdaptiveTranscriptAdvantage Filt S T ≤ ((δb + eps : NNReal) : ℝ) := by
  refine filteredAdaptiveTranscriptAdvantage_le_of_pointwise Filt S T _
    (by positivity) (fun E hE => ?_)
  have h_ext := hTechnique_ratio (extS E) (extT E) Bad eps
    (h_nnS E) (h_nnT E)
    (h_weight E) (h_le_one E) (h_ratio E)
  have h_proj := statDist_le_of_extension (tr[q](S, E.1)) (tr[q](T, E.1))
    (extS E) (extT E) (h_projS E) (h_projT E)
  grw [h_ext, h_bad E hE] at h_proj
  exact h_proj

/-- **Filtered representative σ⁺ endpoint (ratio form)** — the HCTR2 main-lemma
endpoint: extended fixed-query σ⁺ ratio on good extended transcripts, a bad
bound over `Filt`-respecting environments on the ideal extension, concluding
the `Filt`-restricted advantage. -/
theorem adv_le_of_extFixedQueryRep_ratio_of_good_filtered
    (Filt : TranscriptPrefix X Y q → Prop)
    (pR : Dist.ProbDist Ω) (FR : PFunPDS.RV Ω X Y)
    (pI : Dist.ProbDist Ω') (FI : PFunPDS.RV Ω' X Y)
    (augR : Ω → TranscriptPrefix X Y q → Z)
    (augI : Ω' → TranscriptPrefix X Y q → Z)
    (Bad : TranscriptPrefix X Y q × Z → Prop) (eps δb : NNReal)
    (hR : PFunPDS.Prob.KStepTotal (Dist.PMF pR FR) q)
    (hI : PFunPDS.Prob.KStepTotal (Dist.PMF pI FI) q)
    (h_ratio : ∀ (xs : Fin q → X) (tz : TranscriptPrefix X Y q × Z),
      ¬ Bad tz →
      (1 - eps) * extFixedQueryTranscriptDistRep pI FI augI xs tz ≤
        extFixedQueryTranscriptDistRep pR FR augR xs tz)
    (h_bad : ∀ E : QQueryEnvironment X Y q, EnvRespects Filt E →
      Pr[Bad ∣ extendedTranscriptDistRep (q := q) pI FI augI E.1] ≤ δb) :
    filteredAdaptiveTranscriptAdvantage Filt
        (Dist.PMF pR FR : ProbPDS X Y) (Dist.PMF pI FI : ProbPDS X Y) ≤
      ((δb + eps : NNReal) : ℝ) := by
  refine adv_le_of_extended_ratio_of_good_filtered Filt _ _
    (fun E => extendedTranscriptDistRep (q := q) pR FR augR E.1)
    (fun E => extendedTranscriptDistRep (q := q) pI FI augI E.1)
    Bad eps δb
    (fun E => extendedTranscriptDistRep_nonNeg pR FR augR E.1)
    (fun E => extendedTranscriptDistRep_nonNeg pI FI augI E.1)
    (fun E => fTransform_fst_extendedTranscriptDistRep pR FR augR E.1)
    (fun E => fTransform_fst_extendedTranscriptDistRep pI FI augI E.1)
    (fun E => ?_) (fun E => ?_)
    (fun E tz h_good =>
      extended_ratio_of_extFixedQueryRep_ratio_of_good pR FR pI FI augR augI
        E.1 Bad eps h_ratio tz h_good)
    h_bad
  · rw [extendedTranscriptDistRep_weight, extendedTranscriptDistRep_weight,
      deterministicTranscriptDist_weight_eq_one _ E hR,
      deterministicTranscriptDist_weight_eq_one _ E hI]
  · rw [extendedTranscriptDistRep_weight,
      deterministicTranscriptDist_weight_eq_one _ E hI]

end FilteredExtended

end FilteredAdvantage

/-! #### Deterministic-environment replay: consistent transcripts ↔ response vectors

A `q`-query-total deterministic environment reads only the *responses*, so the
queries of an `E`-consistent transcript are a function of its response vector,
and consistent transcripts biject with response vectors (`envReplay`).  Two
consequences drive the remaining kernel:

* **response surgery** — modify one response and re-run: the queries up to and
  including the modified step are unchanged, and the result is again
  `E`-consistent.  This turns the *possibilistic* `EnvRespects` filter into
  per-transcript facts: a respecting environment can never produce a transcript
  in which a later query shares its `(tweak, plaintext)` (resp. ciphertext)
  with an earlier constraint, because the completion answering with the
  matching partner would be a consistent `lpNPV`/injectivity violation
  (`hctr_plain_share_false` / `hctr_cipher_share_false`);
* the **transcript ↔ ω pullback** for the response-pin engine (`§ResponsePin`).
-/

section EnvReplay

/-- The query a `q`-total deterministic environment asks at step `i`, given the
response vector `ys` (it reads only the first `i` responses). -/
noncomputable def envReplayQuery (E : QQueryEnvironment X Y q)
    (ys : List.Vector Y q) (i : Fin q) : X :=
  (E.1 ((ys.toList.take i.1).map some)).get (by
    obtain ⟨x, hx⟩ := E.2 (ys.toList.take i.1)
      (by rw [List.length_take, List.Vector.toList_length]
          exact lt_of_le_of_lt (min_le_left _ _) i.isLt)
    rw [hx]
    rfl)

/-- Defining property of `envReplayQuery`. -/
theorem envReplayQuery_spec (E : QQueryEnvironment X Y q)
    (ys : List.Vector Y q) (i : Fin q) :
    E.1 ((ys.toList.take i.1).map some) = some (envReplayQuery E ys i) :=
  (Option.some_get _).symm

/-- Replay a response vector through the environment: the unique `E`-consistent
transcript with responses `ys`. -/
noncomputable def envReplay (E : QQueryEnvironment X Y q) (ys : List.Vector Y q) :
    TranscriptPrefix X Y q :=
  (List.Vector.ofFn (envReplayQuery E ys), ys)

theorem envReplay_consistent (E : QQueryEnvironment X Y q) (ys : List.Vector Y q) :
    E.1 ⊨ envReplay E ys := by
  intro i
  show E.1 ((ys.toList.take i.1).map some) = some ((List.Vector.ofFn _).get i)
  rw [List.Vector.get_ofFn]
  exact envReplayQuery_spec E ys i

/-- On a consistent transcript, the queries are the replayed ones. -/
theorem consistent_queries_eq (E : QQueryEnvironment X Y q)
    {t : TranscriptPrefix X Y q} (hcon : E.1 ⊨ t) (i : Fin q) :
    t.1.get i = envReplayQuery E t.2 i :=
  Option.some_inj.mp ((hcon i).symm.trans (envReplayQuery_spec E t.2 i))

/-- Replayed queries depend only on the strictly earlier responses. -/
theorem envReplayQuery_congr (E : QQueryEnvironment X Y q)
    {ys ys' : List.Vector Y q} (i : Fin q)
    (h : ys.toList.take i.1 = ys'.toList.take i.1) :
    envReplayQuery E ys i = envReplayQuery E ys' i := by
  have h1 := envReplayQuery_spec E ys i
  rw [h] at h1
  exact Option.some_inj.mp (h1.symm.trans (envReplayQuery_spec E ys' i))

/-- Setting a response at index `s` leaves the earlier response prefix (any
`take n` with `n ≤ s`) unchanged. -/
theorem toList_take_set_of_le (ys : List.Vector Y q) (s : Fin q) (c : Y)
    {n : ℕ} (hn : n ≤ s.1) :
    ((ys.set s c).toList.take n) = ys.toList.take n := by
  have hset : (ys.set s c).toList = ys.toList.set s.1 c :=
    List.Vector.toList_set ys s c
  rw [hset]
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    have hk : k < n := by
      simp only [List.length_take] at h1
      omega
    have hsk : (s : ℕ) ≠ k := by omega
    rw [List.getElem_take, List.getElem_take]
    exact List.getElem_set_ne hsk _

/-- **Response surgery**: replaying with one response modified at index `s`
keeps all queries up to and including step `s` unchanged. -/
theorem envReplay_set_query_eq (E : QQueryEnvironment X Y q)
    (ys : List.Vector Y q) (s : Fin q) (c : Y) {i : Fin q} (hi : i ≤ s) :
    envReplayQuery E (ys.set s c) i = envReplayQuery E ys i :=
  envReplayQuery_congr E i (toList_take_set_of_le ys s c hi)

end EnvReplay

/-! #### Running a memoryless oracle against the environment

`runResponses E f` is the response vector produced by the deterministic
interaction of `E` with the *memoryless* oracle `f : X → Y`; `envRun E f` is
the resulting transcript.  `envRun_eq_iff` characterizes its fibers: the
transcript distribution of the ideal world is the pushforward of the uniform
`ω` along `envRun` (`hctr_omega_slice_le`), which is what lets the
response-pin argument work at the `ω` level, where adaptivity is resolved. -/

section EnvRun

/-- The first `n` responses of the run, with their length. -/
noncomputable def runListAux (E : QQueryEnvironment X Y q) (f : X → Y) :
    (n : ℕ) → n ≤ q → {l : List Y // l.length = n}
  | 0, _ => ⟨[], rfl⟩
  | n + 1, h =>
    let prev := runListAux E f n (Nat.le_of_succ_le h)
    ⟨prev.1 ++ [f ((E.1 (prev.1.map some)).get (by
        obtain ⟨x, hx⟩ := E.2 prev.1 (by rw [prev.2]; omega)
        rw [hx]
        rfl))],
      by rw [List.length_append, List.length_singleton, prev.2]⟩

/-- Earlier run prefixes are literal prefixes. -/
theorem runListAux_take (E : QQueryEnvironment X Y q) (f : X → Y) :
    ∀ (m : ℕ) (hm : m ≤ q) (n : ℕ) (hnm : n ≤ m),
      (runListAux E f m hm).1.take n = (runListAux E f n (hnm.trans hm)).1 := by
  intro m
  induction m with
  | zero =>
    intro hm n hnm
    interval_cases n
    rfl
  | succ m ih =>
    intro hm n hnm
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm' : n ≤ m := by omega
      show ((runListAux E f m _).1 ++ [_]).take n = _
      rw [List.take_append_of_le_length (by rw [(runListAux E f m _).2]; omega)]
      exact ih (Nat.le_of_succ_le hm) n hnm'
    · have hn : n = m + 1 := by omega
      subst hn
      rw [List.take_of_length_le (by rw [(runListAux E f (m + 1) hm).2])]

/-- The response vector of the full run. -/
noncomputable def runResponses (E : QQueryEnvironment X Y q) (f : X → Y) :
    List.Vector Y q :=
  ⟨(runListAux E f q le_rfl).1, (runListAux E f q le_rfl).2⟩

/-- Element access into the run: response `i` is `f` of the query computed
from the length-`i` run prefix. -/
theorem runListAux_getElem (E : QQueryEnvironment X Y q) (f : X → Y) :
    ∀ (m : ℕ) (hm : m ≤ q) (i : ℕ) (hi : i < m)
      (hi' : i < (runListAux E f m hm).1.length),
      (runListAux E f m hm).1[i] =
        f ((E.1 (((runListAux E f i (le_trans hi.le hm)).1).map some)).get (by
          obtain ⟨x, hx⟩ := E.2 (runListAux E f i (le_trans hi.le hm)).1
            (by rw [(runListAux E f i (le_trans hi.le hm)).2]; omega)
          rw [hx]
          rfl)) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro hm i hi hi'
    rcases Nat.lt_or_ge i m with hlt | hge
    · show ((runListAux E f m _).1 ++ [_])[i]'_ = _
      rw [List.getElem_append_left (by rw [(runListAux E f m _).2]; exact hlt)]
      exact ih (Nat.le_of_succ_le hm) i hlt _
    · have hi0 : i = m := by omega
      subst hi0
      show ((runListAux E f i _).1 ++ [_])[i]'_ = _
      rw [List.getElem_append_right (by rw [(runListAux E f i _).2])]
      simp [(runListAux E f i _).2]

/-- **Run spec**: each response is `f` applied to the replayed query. -/
theorem runResponses_get (E : QQueryEnvironment X Y q) (f : X → Y) (i : Fin q) :
    (runResponses E f).get i = f (envReplayQuery E (runResponses E f) i) := by
  have htake : (runResponses E f).toList.take i.1
      = (runListAux E f i.1 (le_of_lt i.isLt)).1 :=
    runListAux_take E f q le_rfl i.1 (le_of_lt i.isLt)
  have hq : envReplayQuery E (runResponses E f) i
      = (E.1 (((runListAux E f i.1 (le_of_lt i.isLt)).1).map some)).get (by
          obtain ⟨x, hx⟩ := E.2 (runListAux E f i.1 (le_of_lt i.isLt)).1
            (by rw [(runListAux E f i.1 (le_of_lt i.isLt)).2]; exact i.isLt)
          rw [hx]
          rfl) := by
    apply Option.some_inj.mp
    rw [← envReplayQuery_spec E (runResponses E f) i, htake, Option.some_get]
  rw [hq]
  show (runResponses E f).toList[i.1]'(by
      rw [List.Vector.toList_length]; exact i.isLt) = _
  exact runListAux_getElem E f q le_rfl i.1 i.isLt _

/-- The transcript of the run. -/
noncomputable def envRun (E : QQueryEnvironment X Y q) (f : X → Y) :
    TranscriptPrefix X Y q :=
  envReplay E (runResponses E f)

theorem envRun_consistent (E : QQueryEnvironment X Y q) (f : X → Y) :
    E.1 ⊨ envRun E f :=
  envReplay_consistent E _

/-- **Fiber characterization of the run**: the run hits exactly the
`E`-consistent transcripts whose responses are `f` of their queries. -/
theorem envRun_eq_iff (E : QQueryEnvironment X Y q) (f : X → Y)
    (t : TranscriptPrefix X Y q) :
    envRun E f = t ↔ (E.1 ⊨ t ∧ ∀ i, f (t.1.get i) = t.2.get i) := by
  constructor
  · rintro rfl
    refine ⟨envRun_consistent E f, fun i => ?_⟩
    have h1 : (envRun E f).1.get i = envReplayQuery E (runResponses E f) i :=
      List.Vector.get_ofFn _ _
    rw [h1]
    exact (runResponses_get E f i).symm
  · rintro ⟨hcon, hf⟩
    have key : ∀ n : ℕ, ∀ i : Fin q, i.1 = n →
        (runResponses E f).get i = t.2.get i := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hin
        have htake : (runResponses E f).toList.take i.1 = t.2.toList.take i.1 := by
          apply List.ext_getElem
          · simp
          · intro k h1 h2
            have hk : k < i.1 := by
              simp only [List.length_take] at h1
              omega
            have hkq : k < q := lt_trans hk i.isLt
            rw [List.getElem_take, List.getElem_take]
            exact ih k (by omega) ⟨k, hkq⟩ rfl
        have hq : envReplayQuery E (runResponses E f) i = t.1.get i := by
          rw [envReplayQuery_congr E i htake, ← consistent_queries_eq E hcon i]
        rw [runResponses_get E f i, hq]
        exact hf i
    have h2 : runResponses E f = t.2 := by
      apply List.Vector.ext
      intro i
      exact key i.1 i rfl
    show envReplay E (runResponses E f) = t
    rw [h2]
    obtain ⟨t1, t2⟩ := t
    refine Prod.ext ?_ rfl
    apply List.Vector.ext
    intro i
    show (List.Vector.ofFn _).get i = t1.get i
    rw [List.Vector.get_ofFn]
    exact (consistent_queries_eq E hcon i).symm

end EnvRun

section EnvRunCongr

/-- **Run-prefix stability**: if `f'` agrees with `f` away from the run's
`s`-th query and the run's queries are pairwise distinct, then the `f'`-run
agrees with the `f`-run on all queries through step `s` and all responses
before step `s`. -/
theorem envRun_prefix_congr (E : QQueryEnvironment X Y q) (f f' : X → Y)
    (s : Fin q) (hinj : Function.Injective (envRun E f).1.get)
    (hagree : ∀ x, x ≠ (envRun E f).1.get s → f x = f' x) :
    (∀ k : Fin q, k ≤ s → (envRun E f').1.get k = (envRun E f).1.get k) ∧
      (∀ k : Fin q, k < s → (envRun E f').2.get k = (envRun E f).2.get k) := by
  have hq : ∀ (i : Fin q), (envRun E f).1.get i
      = envReplayQuery E (runResponses E f) i := fun i => List.Vector.get_ofFn _ _
  have hq' : ∀ (i : Fin q), (envRun E f').1.get i
      = envReplayQuery E (runResponses E f') i := fun i => List.Vector.get_ofFn _ _
  -- responses strictly below s agree, by strong induction
  have key : ∀ n : ℕ, ∀ k : Fin q, k.1 = n → k < s →
      (runResponses E f').get k = (runResponses E f).get k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hkn hks
      have htake : (runResponses E f').toList.take k.1
          = (runResponses E f).toList.take k.1 := by
        apply List.ext_getElem
        · simp
        · intro m h1 h2
          have hm : m < k.1 := by
            simp only [List.length_take] at h1
            omega
          have hmq : m < q := lt_trans hm k.isLt
          rw [List.getElem_take, List.getElem_take]
          exact ih m (by omega) ⟨m, hmq⟩ rfl (lt_trans (by exact hm) hks)
      have hquery : envReplayQuery E (runResponses E f') k
          = envReplayQuery E (runResponses E f) k :=
        envReplayQuery_congr E k htake
      rw [runResponses_get E f' k, runResponses_get E f k, hquery]
      refine (hagree _ (fun hx => ?_)).symm
      rw [← hq k] at hx
      exact absurd (hinj hx) (ne_of_lt hks)
  have hresp : ∀ k : Fin q, k < s →
      (envRun E f').2.get k = (envRun E f).2.get k :=
    fun k hk => key k.1 k rfl hk
  refine ⟨fun k hk => ?_, hresp⟩
  rw [hq k, hq' k]
  refine envReplayQuery_congr E k ?_
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    have hm : m < k.1 := by
      simp only [List.length_take] at h1
      omega
    have hmq : m < q := lt_trans hm k.isLt
    rw [List.getElem_take, List.getElem_take]
    exact key m ⟨m, hmq⟩ rfl (lt_of_lt_of_le (by exact hm) hk)

end EnvRunCongr

section EnvRunDist

/-- The system factor of a sampled function evaluator at a transcript is the
base mass of the evaluation-consistency event (the generic form of the
per-application `sysFactor` computations). -/
theorem sysFactor_functionEvaluator {Ω : Type*}
    (base : Dist.ProbDist Ω) (fn : Ω → X → Y) (t : TranscriptPrefix X Y q) :
    σ(PFunPDS.Prob.functionEvaluator base fn) t
      = base.val.mass (fun ω => ∀ i, fn ω (t.1.get i) = t.2.get i) := by
  unfold sysFactor PFunPDE.transcriptSystemFactor PFunPDS.Prob.functionEvaluator
  rw [Dist.PMF, Dist.mass_fTransform]
  exact Dist.mass_congr _
    (fun ω => transcriptSystemEvent_functionEvaluatorRV_iff fn t.1 t.2 ω)

/-- **Pushforward identity for memoryless sampled systems**: the transcript
distribution of a sampled function evaluator against a deterministic
`q`-query-total environment is the pushforward of the base distribution along
the run map `ω ↦ envRun E (fn ω)`.  This resolves adaptivity at the sample
level: `tr(S, E) = (envRun E ∘ fn)⋆ base`. -/
theorem deterministicTranscriptDist_functionEvaluator_eq_fTransform
    [FiniteTranscriptSpace X Y q] {Ω : Type*}
    (base : Dist.ProbDist Ω) (fn : Ω → X → Y) (E : QQueryEnvironment X Y q) :
    tr[q](PFunPDS.Prob.functionEvaluator base fn, E.1)
      = Dist.fTransform (fun ω => envRun E (fn ω)) base.val := by
  classical
  ext t
  rw [Dist.fTransform_apply_eq_mass,
    deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    sysFactor_functionEvaluator]
  by_cases hcon : E.1 ⊨ t
  · rw [envFactor_eq_indicator, if_pos hcon, mul_one]
    exact Dist.mass_congr _ (fun ω => by
      rw [envRun_eq_iff]
      exact ⟨fun h => ⟨hcon, h⟩, fun h => h.2⟩)
  · rw [envFactor_eq_indicator, if_neg hcon, mul_zero]
    rw [show (fun ω : Ω => envRun E (fn ω) = t) = fun _ => False from
      funext fun ω => eq_false fun h =>
        hcon ((envRun_eq_iff E (fn ω) t).mp h).1]
    simp [Dist.mass]

end EnvRunDist

/-! ## Self-answering filter converters (pointless-query WLOG, generic layer)

A *self-answering filter* wraps the environment side of an interaction:
queries whose answer is already determined by the history (`ptl`) are
answered by the converter itself with the determined value (`det`); all
other queries are forwarded to the real oracle.  Once the inner environment
halts, fresh padding queries (`pad`) keep the attached environment
`q`-query-total.

The point (the "pointless queries are forbidden" WLOG): for oracles that
*do* answer determined queries with the determined value (`hdet`), the inner
environment's transcript is a deterministic reconstruction
(`reconstructTranscript`) of the attached environment's responses,
simultaneously in both worlds (`reconstruct`), while the attached
environment only ever realizes stepwise-fresh transcripts
(`attachEnv_respects`).  The resulting two common pushforward identities are
exposed as a law-factorization contract.  The carrier-independent normalization
theorem in `RandomSystem.lean` then proves equality of unrestricted and
restricted advantages.  No H-technique hypothesis or partition enters this
layer.

The recursion scheme is structural: `advance` runs the environment through
self-answered queries until it emits a real query or the history fills up
(well-founded on `q − h.length`); `consume` feeds it the real-answer supply
(structural on the supply).  There is no fuel and no absorbing terminal
state; the extension lemmas are `consume_append_some`/`consume_append_none`
via the absorption property of `advance` (`advance_spec`). -/

section SelfAnswer

/-! ### Transcript pair-prefixes (generic bookkeeping) -/

/-- The first `m` query/answer pairs of a transcript, as a list. -/
def TranscriptPrefix.pairs (t : TranscriptPrefix X Y q) (m : ℕ) :
    List (X × Y) :=
  (List.range m).filterMap (fun k =>
    if h : k < q then some (t.1.get ⟨k, h⟩, t.2.get ⟨k, h⟩) else none)

/-- Membership in the pair-prefix: exactly the pairs at indices `< m`. -/
theorem TranscriptPrefix.mem_pairs_iff
    (t : TranscriptPrefix X Y q) (m : ℕ) (c : X × Y) :
    c ∈ TranscriptPrefix.pairs t m ↔
      ∃ k : Fin q, k.val < m ∧ c = (t.1.get k, t.2.get k) := by
  unfold TranscriptPrefix.pairs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hc⟩
    rw [List.mem_range] at ha
    by_cases hq : a < q
    · rw [dif_pos hq, Option.some_inj] at hc
      exact ⟨⟨a, hq⟩, ha, hc.symm⟩
    · rw [dif_neg hq] at hc
      simp at hc
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, List.mem_range.mpr hk, by rw [dif_pos k.isLt]⟩

theorem TranscriptPrefix.pairs_zero (t : TranscriptPrefix X Y q) :
    TranscriptPrefix.pairs t 0 = [] := by
  simp [TranscriptPrefix.pairs]

theorem TranscriptPrefix.pairs_succ
    (t : TranscriptPrefix X Y q) {n : ℕ} (hn : n < q) :
    TranscriptPrefix.pairs t (n + 1)
      = TranscriptPrefix.pairs t n ++ [(t.1.get ⟨n, hn⟩, t.2.get ⟨n, hn⟩)] := by
  unfold TranscriptPrefix.pairs
  rw [List.range_succ, List.filterMap_append]
  congr 1
  simp [hn]

theorem TranscriptPrefix.pairs_length
    (t : TranscriptPrefix X Y q) {n : ℕ} (hn : n ≤ q) :
    (TranscriptPrefix.pairs t n).length = n := by
  induction n with
  | zero => rw [TranscriptPrefix.pairs_zero]; rfl
  | succ n ih =>
    rw [TranscriptPrefix.pairs_succ t (by omega), List.length_append,
      ih (by omega)]
    rfl

theorem TranscriptPrefix.pairs_getD
    (t : TranscriptPrefix X Y q) (d : X × Y)
    {n k : ℕ} (hn : n ≤ q) (hk : k < n) :
    (TranscriptPrefix.pairs t n).getD k d
      = (t.1.get ⟨k, lt_of_lt_of_le hk hn⟩, t.2.get ⟨k, lt_of_lt_of_le hk hn⟩) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hnq : n < q := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    rw [TranscriptPrefix.pairs_succ t hnq]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · rw [List.getD_append _ _ _ _
        (by rw [TranscriptPrefix.pairs_length t (le_of_lt hnq)]; omega)]
      exact ih (le_of_lt hnq) hkn
    · have hk' : k = n := by omega
      subst hk'
      rw [List.getD_append_right _ _ _ _
          (by rw [TranscriptPrefix.pairs_length t (le_of_lt hnq)]),
        TranscriptPrefix.pairs_length t (le_of_lt hnq)]
      simp

/-- Junk-free `getElem` form of `pairs_getD`. -/
theorem TranscriptPrefix.pairs_getElem
    (t : TranscriptPrefix X Y q) {n k : ℕ} (hn : n ≤ q) (hk : k < n)
    (hk' : k < (TranscriptPrefix.pairs t n).length) :
    (TranscriptPrefix.pairs t n)[k]
      = (t.1.get ⟨k, lt_of_lt_of_le hk hn⟩, t.2.get ⟨k, lt_of_lt_of_le hk hn⟩) := by
  have h := TranscriptPrefix.pairs_getD t ((TranscriptPrefix.pairs t n)[k]'hk') hn hk
  rwa [List.getD_eq_getElem _ _ hk'] at h

theorem TranscriptPrefix.pairs_map_snd
    (t : TranscriptPrefix X Y q) {n : ℕ} (hn : n ≤ q) :
    (TranscriptPrefix.pairs t n).map Prod.snd = t.2.toList.take n := by
  induction n with
  | zero => rw [TranscriptPrefix.pairs_zero]; simp
  | succ n ih =>
    have hnq : n < q := hn
    rw [TranscriptPrefix.pairs_succ t hnq, List.map_append, ih (le_of_lt hnq),
      List.take_add_one,
      List.getElem?_eq_getElem (by rw [List.Vector.toList_length]; exact hnq)]
    rfl

/-! ### The converter and its recursion scheme -/

/-- A **self-answering filter converter** for the environment side: queries
whose answer is determined by the history (`ptl`) are answered by the
converter itself (`det`); the rest are forwarded.  `pad` supplies fresh
queries once the inner environment halts (`q`-totality of the attached
environment). -/
structure SelfAnswerFilter (X : Type u) (Y : Type v) (q : ℕ) where
  /-- The query is *pointless* against the history: its answer is determined. -/
  ptl : List (X × Y) → X → Prop
  /-- The determined answer of a pointless query. -/
  det : List (X × Y) → X → Y
  /-- A fresh padding query for the given history. -/
  pad : List (X × Y) → X
  /-- Padding queries are never pointless (the freshness supply). -/
  pad_ok : ∀ h : List (X × Y), h.length < q → ¬ ptl h (pad h)
  /-- Pointlessness is monotone in the history (membership suffices). -/
  ptl_mono : ∀ ⦃l l' : List (X × Y)⦄ ⦃x : X⦄,
    (∀ p ∈ l, p ∈ l') → ptl l x → ptl l' x

namespace SelfAnswerFilter

open Classical in
/-- Run `E` from history `h` through self-answered queries until it emits a
non-determined query (`some x`, not yet appended to the history) or the
history reaches `q` (or `E` halts) — `none`.  Well-founded on
`q − h.length`; no fuel, no absorbing terminal state. -/
noncomputable def advance (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (h : List (X × Y)) : List (X × Y) × Option X :=
  if _hlen : h.length < q then
    match E (h.map fun p => some p.2) with
    | none => (h, none)
    | some x =>
      if sa.ptl h x then sa.advance E (h ++ [(x, sa.det h x)])
      else (h, some x)
  else (h, none)
termination_by q - h.length
decreasing_by simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- Feed the real-answer supply to the advancing run: each supplied answer
resolves one forwarded query.  Structural on the supply. -/
noncomputable def consume (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (h : List (X × Y)) : List Y → List (X × Y) × Option X
  | [] => sa.advance E h
  | y :: ys =>
    match sa.advance E h with
    | (h', some x) => sa.consume E (h' ++ [(x, y)]) ys
    | (h', none) => (h', none)

@[simp] theorem consume_nil (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (h : List (X × Y)) : sa.consume E h [] = sa.advance E h := rfl

theorem consume_cons (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (h : List (X × Y)) (y : Y) (ys : List Y) :
    sa.consume E h (y :: ys) =
      match sa.advance E h with
      | (h', some x) => sa.consume E (h' ++ [(x, y)]) ys
      | (h', none) => (h', none) := rfl

/-- **`advance` master spec**: the result extends the input history, is
*absorbing* (re-running `advance` from the result history reproduces the
result), and a forwarded query is non-pointless against the result history. -/
theorem advance_spec (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    ∀ (h h' : List (X × Y)) (r : Option X), sa.advance E h = (h', r) →
      h <+: h' ∧ sa.advance E h' = (h', r) ∧
        ∀ x, r = some x → ¬ sa.ptl h' x := by
  suffices H : ∀ (fuel : ℕ) (h : List (X × Y)), q - h.length ≤ fuel →
      ∀ (h' : List (X × Y)) (r : Option X), sa.advance E h = (h', r) →
        h <+: h' ∧ sa.advance E h' = (h', r) ∧
          ∀ x, r = some x → ¬ sa.ptl h' x from
    fun h h' r => H (q - h.length) h le_rfl h' r
  intro fuel
  induction fuel with
  | zero =>
    intro h hf h' r hadv
    have hnl : ¬ h.length < q := by omega
    rw [advance, dif_neg hnl] at hadv
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
    exact ⟨List.prefix_rfl, by rw [advance, dif_neg hnl], fun x hx => by simp at hx⟩
  | succ fuel ih =>
    intro h hf h' r hadv
    by_cases hlen : h.length < q
    · rw [advance, dif_pos hlen] at hadv
      rcases hE : E (h.map fun p => some p.2) with _ | x <;>
        rw [hE] at hadv <;> dsimp only at hadv
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
        refine ⟨List.prefix_rfl, ?_, fun x hx => by simp at hx⟩
        rw [advance, dif_pos hlen, hE]
      · by_cases hptl : sa.ptl h x
        · rw [if_pos hptl] at hadv
          obtain ⟨hpre, hab, hnp⟩ := ih (h ++ [(x, sa.det h x)])
            (by simp only [List.length_append, List.length_cons,
              List.length_nil]; omega) h' r hadv
          exact ⟨(List.prefix_append _ _).trans hpre, hab, hnp⟩
        · rw [if_neg hptl] at hadv
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
          refine ⟨List.prefix_rfl, ?_, ?_⟩
          · rw [advance, dif_pos hlen, hE]
            dsimp only
            rw [if_neg hptl]
          · rintro x' hx'
            obtain rfl : x = x' := by simpa using hx'
            exact hptl
    · rw [advance, dif_neg hlen] at hadv
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
      exact ⟨List.prefix_rfl, by rw [advance, dif_neg hlen],
        fun x hx => by simp at hx⟩

/-- A run ending with a pending forwarded query has that verdict re-derivable
from its final history. -/
theorem consume_some_advance (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    ∀ (ys : List Y) (h h' : List (X × Y)) (x : X),
      sa.consume E h ys = (h', some x) → sa.advance E h' = (h', some x) := by
  intro ys
  induction ys with
  | nil =>
    intro h h' x hc
    rw [consume_nil] at hc
    exact (advance_spec sa E h h' _ hc).2.1
  | cons y ys ih =>
    intro h h' x hc
    rw [consume_cons] at hc
    rcases hadv : sa.advance E h with ⟨h₁, _ | x₁⟩ <;>
      rw [hadv] at hc <;> dsimp only at hc
    · exact absurd hc (by simp)
    · exact ih _ h' x hc

/-- **Supply extension, live side**: a run ending with a pending forwarded
query continues from its final history. -/
theorem consume_append_some (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    ∀ (ys : List Y) (h h' : List (X × Y)) (x : X) (zs : List Y),
      sa.consume E h ys = (h', some x) →
      sa.consume E h (ys ++ zs) = sa.consume E h' zs := by
  intro ys
  induction ys with
  | nil =>
    intro h h' x zs hc
    rw [consume_nil] at hc
    have hab := (advance_spec sa E h h' _ hc).2.1
    cases zs with
    | nil => rw [List.nil_append, consume_nil, consume_nil, hc, hab]
    | cons z zs' => rw [List.nil_append, consume_cons, consume_cons, hc, hab]
  | cons y ys ih =>
    intro h h' x zs hc
    rw [consume_cons] at hc
    rw [List.cons_append, consume_cons]
    rcases hadv : sa.advance E h with ⟨h₁, _ | x₁⟩ <;>
      rw [hadv] at hc <;> dsimp only at hc ⊢
    · exact absurd hc (by simp)
    · exact ih _ h' x zs hc

/-- **Supply extension, halted side**: a run whose environment finished (or
filled the history) ignores additional answers. -/
theorem consume_append_none (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    ∀ (ys : List Y) (h h' : List (X × Y)) (zs : List Y),
      sa.consume E h ys = (h', none) →
      sa.consume E h (ys ++ zs) = (h', none) := by
  intro ys
  induction ys with
  | nil =>
    intro h h' zs hc
    rw [consume_nil] at hc
    cases zs with
    | nil => rw [List.nil_append, consume_nil, hc]
    | cons z zs' => rw [List.nil_append, consume_cons, hc]
  | cons y ys ih =>
    intro h h' zs hc
    rw [consume_cons] at hc
    rw [List.cons_append, consume_cons]
    rcases hadv : sa.advance E h with ⟨h₁, _ | x₁⟩ <;>
      rw [hadv] at hc <;> dsimp only at hc ⊢
    · exact hc
    · exact ih _ h' zs hc

/-- One-step supply extension: consuming one more answer resolves the pending
query and advances. -/
theorem consume_concat_some {sa : SelfAnswerFilter X Y q} {E : DDE X Y}
    {h h' : List (X × Y)} {x : X} {ys : List Y}
    (hc : sa.consume E h ys = (h', some x)) (y : Y) :
    sa.consume E h (ys ++ [y]) = sa.advance E (h' ++ [(x, y)]) := by
  rw [consume_append_some sa E ys h h' x [y] hc, consume_cons,
    consume_some_advance sa E ys h h' x hc]
  rfl

/-! ### The attached environment -/

/-- The attached environment's own past query/response pairs (in reverse
supply order): structural recursion on the reversed response list. -/
noncomputable def attachPairsRev (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    List Y → List (X × Y)
  | [] => []
  | y :: ys =>
    sa.attachPairsRev E ys ++
      [(((sa.consume E [] ys.reverse).2).getD (sa.pad (sa.attachPairsRev E ys)), y)]

/-- The attached environment's own past query/response pairs, recomputed from
the response list alone (chronological order). -/
noncomputable def attachPairs (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (rs : List Y) : List (X × Y) :=
  sa.attachPairsRev E rs.reverse

/-- The query the attached environment asks after seeing responses `rs`: the
pending forwarded query of the replayed run if the inner environment still
has one, otherwise a fresh pad. -/
noncomputable def attachQuery (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (rs : List Y) : X :=
  ((sa.consume E [] rs).2).getD (sa.pad (sa.attachPairs E rs))

@[simp] theorem attachPairs_nil (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    sa.attachPairs E [] = [] := rfl

theorem attachPairs_concat (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (rs : List Y) (y : Y) :
    sa.attachPairs E (rs ++ [y])
      = sa.attachPairs E rs ++ [(sa.attachQuery E rs, y)] := by
  simp only [attachPairs, attachQuery, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, attachPairsRev,
    List.reverse_reverse]

@[simp] theorem attachPairs_length (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (rs : List Y) : (sa.attachPairs E rs).length = rs.length := by
  suffices H : ∀ l : List Y, (sa.attachPairsRev E l).length = l.length by
    rw [attachPairs, H, List.length_reverse]
  intro l
  induction l with
  | nil => rfl
  | cons y ys ih => simp [attachPairsRev, ih]

theorem attachPairs_getElem (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (rs : List Y) {k : ℕ} (hk : k < rs.length)
    (hk' : k < (sa.attachPairs E rs).length) :
    (sa.attachPairs E rs)[k] = (sa.attachQuery E (rs.take k), rs[k]) := by
  induction rs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton rs y ih =>
    simp only [attachPairs_concat]
    rcases Nat.lt_or_ge k rs.length with h | h
    · rw [List.getElem_append_left (by rw [attachPairs_length]; exact h),
        ih h (by rw [attachPairs_length]; exact h),
        List.take_append_of_le_length (le_of_lt h),
        List.getElem_append_left h]
    · have hk0 : k = rs.length := by
        rw [List.length_append, List.length_singleton] at hk
        omega
      subst hk0
      rw [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_concat_length, List.getElem_concat_length]
      · rfl
      · exact (attachPairs_length sa E rs).symm

/-- The attached environment: always answers with `attachQuery` on the
realized (all-`some`) history. -/
noncomputable def attachEnv (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    QQueryEnvironment X Y q :=
  ⟨fun oys => some (sa.attachQuery E (oys.filterMap id)),
    fun ys _ => ⟨sa.attachQuery E ((ys.map some).filterMap id), rfl⟩⟩

/-- On realized histories, the attached environment asks exactly
`attachQuery` of the response prefix. -/
theorem attachEnv_replayQuery (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (ys : List.Vector Y q) (i : Fin q) :
    envReplayQuery (sa.attachEnv E) ys i
      = sa.attachQuery E (ys.toList.take i.1) := by
  apply Option.some_inj.mp
  rw [← envReplayQuery_spec (sa.attachEnv E) ys i]
  show some (sa.attachQuery E (((ys.toList.take i.1).map some).filterMap id)) = _
  rw [List.filterMap_map]
  simp [List.filterMap_some]

/-- **Forwarded-query spec** (arbitrary supply): a pending forwarded query is
non-pointless against the final history, which contains every attached pair
of the supply consumed so far. -/
theorem consume_some_spec (sa : SelfAnswerFilter X Y q) (E : DDE X Y) :
    ∀ (rs : List Y) (h' : List (X × Y)) (x : X),
      sa.consume E [] rs = (h', some x) →
      ¬ sa.ptl h' x ∧
        ∀ (k : ℕ) (hk : k < rs.length),
          (sa.attachQuery E (rs.take k), rs[k]) ∈ h' := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro h' x hc
    rw [consume_nil] at hc
    exact ⟨(advance_spec sa E [] h' _ hc).2.2 x rfl,
      fun k hk => absurd hk (by simp)⟩
  | append_singleton rs y ih =>
    intro h' x hc
    rcases hc₁ : sa.consume E [] rs with ⟨h₁, _ | x₁⟩
    · rw [consume_append_none sa E rs [] h₁ [y] hc₁] at hc
      exact absurd hc (by simp)
    · rw [consume_concat_some hc₁ y] at hc
      obtain ⟨hnp, hmem⟩ := ih h₁ x₁ hc₁
      obtain ⟨hpre, -, hnp'⟩ := advance_spec sa E (h₁ ++ [(x₁, y)]) h' _ hc
      have hq₁ : sa.attachQuery E rs = x₁ := by
        rw [attachQuery, hc₁]
        rfl
      refine ⟨hnp' x rfl, fun k hk => ?_⟩
      rcases Nat.lt_or_ge k rs.length with hkl | hkl
      · rw [List.take_append_of_le_length (le_of_lt hkl),
          List.getElem_append_left hkl]
        exact hpre.subset (List.mem_append_left _ (hmem k hkl))
      · have hk0 : k = rs.length := by
          rw [List.length_append, List.length_singleton] at hk
          omega
        subst hk0
        rw [List.take_append_of_le_length le_rfl, List.take_length,
          List.getElem_concat_length, hq₁]
        · exact hpre.subset (List.mem_append_right _ (by simp))
        · rfl

/-- **The attached environment respects the filter**: every consistent
transcript of `attachEnv` is stepwise-fresh — no query is pointless against
its own pair-prefix (so any filter implied by stepwise freshness holds). -/
theorem attachEnv_respects (sa : SelfAnswerFilter X Y q) (E : DDE X Y)
    (Filt : TranscriptPrefix X Y q → Prop)
    (hFilt : ∀ t : TranscriptPrefix X Y q,
      (∀ m : Fin q, ¬ sa.ptl (TranscriptPrefix.pairs t m.1) (t.1.get m)) →
        Filt t) :
    EnvRespects Filt (sa.attachEnv E) := by
  intro t' hcon
  refine hFilt t' (fun m => ?_)
  have hrslen : t'.2.toList.length = q := List.Vector.toList_length t'.2
  have htklen : (t'.2.toList.take m.1).length = m.1 := by
    rw [List.length_take, hrslen]
    omega
  have hq0 : t'.1.get m = sa.attachQuery E (t'.2.toList.take m.1) := by
    rw [consistent_queries_eq (sa.attachEnv E) hcon m, attachEnv_replayQuery]
  have hqk : ∀ k : Fin q, t'.1.get k = sa.attachQuery E (t'.2.toList.take k.1) := by
    intro k
    rw [consistent_queries_eq (sa.attachEnv E) hcon k, attachEnv_replayQuery]
  -- the transcript's pair-prefix is the recomputable attached pair list
  have hpairs_eq : sa.attachPairs E (t'.2.toList.take m.1)
      = TranscriptPrefix.pairs t' m.1 := by
    refine List.ext_getElem ?_ ?_
    · rw [attachPairs_length, htklen,
        TranscriptPrefix.pairs_length t' (le_of_lt m.isLt)]
    · intro k hk1 hk2
      have hkm : k < m.1 := by
        rw [attachPairs_length, htklen] at hk1
        exact hk1
      rw [attachPairs_getElem sa E _ (by rw [htklen]; exact hkm),
        TranscriptPrefix.pairs_getElem t' (le_of_lt m.isLt) hkm,
        List.take_take, min_eq_left (le_of_lt hkm),
        ← hqk ⟨k, lt_trans hkm m.isLt⟩, List.getElem_take]
      rfl
  rw [hq0, ← hpairs_eq]
  cases hout : (sa.consume E [] (t'.2.toList.take m.1)).2 with
  | some x =>
    have hx : sa.attachQuery E (t'.2.toList.take m.1) = x := by
      rw [attachQuery, hout]
      rfl
    obtain ⟨hnp, hmem⟩ := consume_some_spec sa E (t'.2.toList.take m.1)
      (sa.consume E [] (t'.2.toList.take m.1)).1 x
      (by rw [← hout])
    rw [hx]
    intro hptl
    refine hnp (sa.ptl_mono ?_ hptl)
    intro p hp
    rw [List.mem_iff_getElem] at hp
    obtain ⟨k, hk, hkp⟩ := hp
    have hkm : k < (t'.2.toList.take m.1).length := by
      rwa [attachPairs_length] at hk
    rw [← hkp, attachPairs_getElem sa E _ hkm]
    exact hmem k hkm
  | none =>
    have hx : sa.attachQuery E (t'.2.toList.take m.1)
        = sa.pad (sa.attachPairs E (t'.2.toList.take m.1)) := by
      rw [attachQuery, hout]
      rfl
    rw [hx]
    exact sa.pad_ok _ (by rw [attachPairs_length, htklen]; exact m.isLt)

/-! ### Simulation correctness against determined-answer oracles -/

/-- **`advance` along the true run**: starting from a true pair-prefix of
`envRun E f`, `advance` self-answers pointless true queries (correctly, by
`hdet`) and stops at the first non-pointless true query, or fills the
history. -/
theorem advance_run_spec (sa : SelfAnswerFilter X Y q)
    (E : QQueryEnvironment X Y q) (f : X → Y)
    (hdet : ∀ (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = f p.1) → sa.ptl h x → f x = sa.det h x) :
    ∀ n, n ≤ q → ∃ m, n ≤ m ∧
      ((∃ hm : m < q,
          ¬ sa.ptl (TranscriptPrefix.pairs (envRun E f) m)
            ((envRun E f).1.get ⟨m, hm⟩) ∧
          sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) n)
            = (TranscriptPrefix.pairs (envRun E f) m,
                some ((envRun E f).1.get ⟨m, hm⟩))) ∨
        (m = q ∧ sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) n)
            = (TranscriptPrefix.pairs (envRun E f) q, none))) := by
  have hrun := (envRun_eq_iff E f (envRun E f)).mp rfl
  have hstop : sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) q)
      = (TranscriptPrefix.pairs (envRun E f) q, none) := by
    rw [advance,
      dif_neg (by rw [TranscriptPrefix.pairs_length _ le_rfl]; omega)]
  suffices H : ∀ (fuel n : ℕ), q - n ≤ fuel → n ≤ q → ∃ m, n ≤ m ∧
      ((∃ hm : m < q,
          ¬ sa.ptl (TranscriptPrefix.pairs (envRun E f) m)
            ((envRun E f).1.get ⟨m, hm⟩) ∧
          sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) n)
            = (TranscriptPrefix.pairs (envRun E f) m,
                some ((envRun E f).1.get ⟨m, hm⟩))) ∨
        (m = q ∧ sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) n)
            = (TranscriptPrefix.pairs (envRun E f) q, none))) from
    fun n hn => H (q - n) n le_rfl hn
  intro fuel
  induction fuel with
  | zero =>
    intro n hf hn
    obtain rfl : n = q := by omega
    exact ⟨n, le_rfl, Or.inr ⟨rfl, hstop⟩⟩
  | succ fuel ih =>
    intro n hf hn
    rcases eq_or_lt_of_le hn with rfl | hn'
    · exact ⟨n, le_rfl, Or.inr ⟨rfl, hstop⟩⟩
    · have hEq : E.1 ((TranscriptPrefix.pairs (envRun E f) n).map
          fun p => some p.2) = some ((envRun E f).1.get ⟨n, hn'⟩) := by
        have h1 := hrun.1 ⟨n, hn'⟩
        rw [← h1, ← TranscriptPrefix.pairs_map_snd (envRun E f) (le_of_lt hn'),
          List.map_map]
        rfl
      have hlen : (TranscriptPrefix.pairs (envRun E f) n).length < q := by
        rw [TranscriptPrefix.pairs_length _ (le_of_lt hn')]
        omega
      by_cases hptl : sa.ptl (TranscriptPrefix.pairs (envRun E f) n)
          ((envRun E f).1.get ⟨n, hn'⟩)
      · -- pointless: self-answer with the determined = true value, recurse
        have hpairs_f : ∀ p ∈ TranscriptPrefix.pairs (envRun E f) n,
            p.2 = f p.1 := by
          intro p hp
          obtain ⟨k, -, rfl⟩ :=
            (TranscriptPrefix.mem_pairs_iff (envRun E f) n p).mp hp
          exact (hrun.2 k).symm
        have hdet' : sa.det (TranscriptPrefix.pairs (envRun E f) n)
            ((envRun E f).1.get ⟨n, hn'⟩) = (envRun E f).2.get ⟨n, hn'⟩ := by
          rw [← hdet _ _ hpairs_f hptl]
          exact hrun.2 ⟨n, hn'⟩
        have hstep : sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) n)
            = sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) (n + 1)) := by
          rw [advance, dif_pos hlen, hEq]
          dsimp only
          rw [if_pos hptl, hdet', ← TranscriptPrefix.pairs_succ (envRun E f) hn']
        rw [hstep]
        obtain ⟨m, hm, hspec⟩ := ih (n + 1) (by omega) (by omega)
        exact ⟨m, by omega, hspec⟩
      · -- non-pointless: stop and forward
        refine ⟨n, le_rfl, Or.inl ⟨hn', hptl, ?_⟩⟩
        rw [advance, dif_pos hlen, hEq]
        dsimp only
        rw [if_neg hptl]

/-- **`consume` along the true run**: replaying any correctly-answered supply
(each answer is `f` of the pending attached query) lands on a true
pair-prefix, with at least one true step per consumed answer. -/
theorem consume_run_spec (sa : SelfAnswerFilter X Y q)
    (E : QQueryEnvironment X Y q) (f : X → Y)
    (hdet : ∀ (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = f p.1) → sa.ptl h x → f x = sa.det h x)
    (rs : List Y)
    (hrs : ∀ (k : ℕ) (hk : k < rs.length),
      rs[k] = f (sa.attachQuery E.1 (rs.take k))) :
    (∃ (n : ℕ) (hn : n < q), rs.length ≤ n ∧
        sa.consume E.1 [] rs
          = (TranscriptPrefix.pairs (envRun E f) n,
              some ((envRun E f).1.get ⟨n, hn⟩))) ∨
      sa.consume E.1 [] rs = (TranscriptPrefix.pairs (envRun E f) q, none) := by
  induction rs using List.reverseRecOn with
  | nil =>
    obtain ⟨m, -, hspec⟩ := advance_run_spec sa E f hdet 0 (Nat.zero_le q)
    rw [TranscriptPrefix.pairs_zero] at hspec
    rcases hspec with ⟨hm, -, hadv⟩ | ⟨-, hadv⟩
    · exact Or.inl ⟨m, hm, Nat.zero_le m, by rw [consume_nil, hadv]⟩
    · exact Or.inr (by rw [consume_nil, hadv])
  | append_singleton rs y ih =>
    have hrs' : ∀ (k : ℕ) (hk : k < rs.length),
        rs[k] = f (sa.attachQuery E.1 (rs.take k)) := by
      intro k hk
      have h := hrs k (by rw [List.length_append, List.length_singleton]; omega)
      rwa [List.getElem_append_left hk,
        List.take_append_of_le_length (le_of_lt hk)] at h
    rcases ih hrs' with ⟨n, hn, hlen, hcons⟩ | hcons
    · -- pending forwarded query: the supplied answer is the true response
      have hxq : sa.attachQuery E.1 rs = (envRun E f).1.get ⟨n, hn⟩ := by
        rw [attachQuery, hcons]
        rfl
      have hrun := (envRun_eq_iff E f (envRun E f)).mp rfl
      have hy : y = (envRun E f).2.get ⟨n, hn⟩ := by
        have h := hrs rs.length
          (by rw [List.length_append, List.length_singleton]; omega)
        rw [List.getElem_concat_length, List.take_append_of_le_length le_rfl,
          List.take_length, hxq] at h
        · rw [h]
          exact hrun.2 ⟨n, hn⟩
        · rfl
      have hsnoc : sa.consume E.1 [] (rs ++ [y])
          = sa.advance E.1 (TranscriptPrefix.pairs (envRun E f) (n + 1)) := by
        rw [consume_concat_some hcons y, hy,
          ← TranscriptPrefix.pairs_succ (envRun E f) hn]
      obtain ⟨m, hm1, hspec⟩ := advance_run_spec sa E f hdet (n + 1) (by omega)
      rw [hsnoc]
      rcases hspec with ⟨hm, -, hadv⟩ | ⟨-, hadv⟩
      · refine Or.inl ⟨m, hm, ?_, hadv⟩
        rw [List.length_append, List.length_singleton]
        omega
      · exact Or.inr hadv
    · exact Or.inr (consume_append_none sa E.1 rs [] _ [y] hcons)

/-- Reconstruction map `Φ`: from the attached environment's responses,
rebuild the inner environment's transcript by replaying the run to
completion (`d` is an unreachable junk default). -/
noncomputable def reconstructTranscript (sa : SelfAnswerFilter X Y q)
    (E : DDE X Y) (d : X × Y) (rs : List Y) : TranscriptPrefix X Y q :=
  (List.Vector.ofFn (fun i : Fin q => ((sa.consume E [] rs).1.getD i.1 d).1),
   List.Vector.ofFn (fun i : Fin q => ((sa.consume E [] rs).1.getD i.1 d).2))

/-- **Φ-correctness**: against an oracle whose answers make determined
queries truly determined, the inner environment's true transcript is the
reconstruction of the attached environment's responses. -/
theorem reconstruct (sa : SelfAnswerFilter X Y q)
    (E : QQueryEnvironment X Y q) (f : X → Y) (d : X × Y)
    (hdet : ∀ (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = f p.1) → sa.ptl h x → f x = sa.det h x) :
    sa.reconstructTranscript E.1 d (envRun (sa.attachEnv E.1) f).2.toList
      = envRun E f := by
  set rs : List Y := (envRun (sa.attachEnv E.1) f).2.toList with hrs_def
  have hrslen : rs.length = q := List.Vector.toList_length _
  have hrs : ∀ (k : ℕ) (hk : k < rs.length),
      rs[k] = f (sa.attachQuery E.1 (rs.take k)) := by
    intro k hk
    have hkq : k < q := hrslen ▸ hk
    have h := runResponses_get (sa.attachEnv E.1) f ⟨k, hkq⟩
    rw [attachEnv_replayQuery] at h
    exact h
  rcases consume_run_spec sa E f hdet rs hrs with ⟨n, hn, hlen, -⟩ | hcons
  · omega
  · unfold reconstructTranscript
    rw [hcons]
    refine Prod.ext ?_ ?_ <;>
      · apply List.Vector.ext
        intro i
        rw [List.Vector.get_ofFn,
          TranscriptPrefix.pairs_getD (envRun E f) d le_rfl i.isLt]

/-! ### Law factorization and its DPI endpoint -/

/-- The law-level contract produced by any sound self-answering
normalization.  It says that the original transcript law is reconstructed as
a deterministic pushforward of the attached environment's transcript law.

This property deliberately does not prescribe how the system is represented.
Static function evaluators below are one producer; a stateful system may use
the same endpoint after separately proving that erased queries have no hidden
state effect. -/
def FactorsTranscriptLawAt [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q) (S : PFunPDS.Prob X Y)
    (E : QQueryEnvironment X Y q) (d : X × Y) : Prop :=
  PFunPDS.Prob.deterministicTranscriptDist (q := q) S E.1 =
    Dist.fTransform
      (fun tp => sa.reconstructTranscript E.1 d tp.2.toList)
      (PFunPDS.Prob.deterministicTranscriptDist
        (q := q) S (sa.attachEnv E.1).1)

/-- Uniform version of `FactorsTranscriptLawAt` for one fixed
self-answering filter and junk default. -/
def FactorsTranscriptLaw [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q) (S : PFunPDS.Prob X Y) (d : X × Y) : Prop :=
  ∀ E : QQueryEnvironment X Y q, sa.FactorsTranscriptLawAt S E d

/-- **Self-answering normalization, environment-indexed form.**  The
self-answering filter and its junk default may depend on the original
environment.  This flexibility is necessary when the padding supply is chosen
from an environment's first query, as in HCTR2.

For each environment, `attachEnv` supplies the normalized index,
`attachEnv_respects` proves that it is allowed, and the two
`FactorsTranscriptLawAt` hypotheses supply the common pushforwards. -/
theorem adaptiveTranscriptAdvantage_eq_filtered_of_factorFamily
    [FiniteTranscriptSpace X Y q]
    (sa : QQueryEnvironment X Y q → SelfAnswerFilter X Y q)
    (Filt : TranscriptPrefix X Y q → Prop)
    (hFilt : ∀ E (t : TranscriptPrefix X Y q),
      (∀ m : Fin q,
        ¬ (sa E).ptl (TranscriptPrefix.pairs t m.1) (t.1.get m)) →
        Filt t)
    (S T : PFunPDS.Prob X Y)
    (d : QQueryEnvironment X Y q → X × Y)
    (hS : ∀ E, (sa E).FactorsTranscriptLawAt S E (d E))
    (hT : ∀ E, (sa E).FactorsTranscriptLawAt T E (d E)) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T =
      filteredAdaptiveTranscriptAdvantage (q := q) Filt S T :=
  adaptiveTranscriptAdvantage_eq_filtered_of_common_fTransform Filt S T
    (fun E => (sa E).attachEnv E.1)
    (fun E => (sa E).attachEnv_respects E.1 Filt (hFilt E))
    (fun E tp => (sa E).reconstructTranscript E.1 (d E) tp.2.toList)
    hS hT

/-- Fixed-filter specialization of
`adaptiveTranscriptAdvantage_eq_filtered_of_factorFamily`. -/
theorem adaptiveTranscriptAdvantage_eq_filtered_of_factors
    [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q)
    (Filt : TranscriptPrefix X Y q → Prop)
    (hFilt : ∀ t : TranscriptPrefix X Y q,
      (∀ m : Fin q, ¬ sa.ptl (TranscriptPrefix.pairs t m.1) (t.1.get m)) →
        Filt t)
    (S T : PFunPDS.Prob X Y) (d : X × Y)
    (hS : sa.FactorsTranscriptLaw S d)
    (hT : sa.FactorsTranscriptLaw T d) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T =
      filteredAdaptiveTranscriptAdvantage (q := q) Filt S T :=
  adaptiveTranscriptAdvantage_eq_filtered_of_factorFamily
    (fun _ => sa) Filt (fun _ => hFilt) S T (fun _ => d) hS hT

/-- A mixture of static functions satisfies the law-factorization contract
when every sampled function gives the history-determined answer.  This is the
function-oracle specialization; the generic contract above also permits
stateful systems whose no-state-effect property is proved by another route. -/
theorem factorsTranscriptLawAt_functionEvaluator
    [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q) {Ω : Type*}
    (base : Dist.ProbDist Ω) (F : Ω → X → Y)
    (hdet : ∀ (ω : Ω) (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F ω p.1) → sa.ptl h x → F ω x = sa.det h x)
    (E : QQueryEnvironment X Y q) (d : X × Y) :
    sa.FactorsTranscriptLawAt
      (PFunPDS.Prob.functionEvaluator base F) E d := by
  unfold FactorsTranscriptLawAt
  rw [deterministicTranscriptDist_functionEvaluator_eq_fTransform,
    deterministicTranscriptDist_functionEvaluator_eq_fTransform,
    Dist.fTransform_comp]
  congr 1
  funext ω
  show envRun E (F ω) =
    sa.reconstructTranscript E.1 d
      (envRun (sa.attachEnv E.1) (F ω)).2.toList
  exact (sa.reconstruct E (F ω) d (hdet ω)).symm

/-- Uniform fixed-filter form of
`factorsTranscriptLawAt_functionEvaluator`. -/
theorem factorsTranscriptLaw_functionEvaluator
    [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q) {Ω : Type*}
    (base : Dist.ProbDist Ω) (F : Ω → X → Y)
    (hdet : ∀ (ω : Ω) (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F ω p.1) → sa.ptl h x → F ω x = sa.det h x)
    (d : X × Y) :
    sa.FactorsTranscriptLaw (PFunPDS.Prob.functionEvaluator base F) d :=
  fun E => sa.factorsTranscriptLawAt_functionEvaluator base F hdet E d

/-- **Consistent function-oracle corollary, environment-indexed form.**  The
self-answering filter, padding choice, and junk default may depend on the
environment; the sampled endpoint functions do not. -/
theorem adaptiveTranscriptAdvantage_eq_filtered_of_selfAnswerFamily
    [FiniteTranscriptSpace X Y q]
    (sa : QQueryEnvironment X Y q → SelfAnswerFilter X Y q)
    (Filt : TranscriptPrefix X Y q → Prop)
    (hFilt : ∀ E (t : TranscriptPrefix X Y q),
      (∀ m : Fin q,
        ¬ (sa E).ptl (TranscriptPrefix.pairs t m.1) (t.1.get m)) →
        Filt t)
    {Ω₁ Ω₂ : Type*}
    (b₁ : Dist.ProbDist Ω₁) (b₂ : Dist.ProbDist Ω₂)
    (F₁ : Ω₁ → X → Y) (F₂ : Ω₂ → X → Y)
    (hdet₁ : ∀ (E : QQueryEnvironment X Y q) (ω : Ω₁)
      (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F₁ ω p.1) →
        (sa E).ptl h x → F₁ ω x = (sa E).det h x)
    (hdet₂ : ∀ (E : QQueryEnvironment X Y q) (ω : Ω₂)
      (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F₂ ω p.1) →
        (sa E).ptl h x → F₂ ω x = (sa E).det h x)
    (d : QQueryEnvironment X Y q → X × Y) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (PFunPDS.Prob.functionEvaluator b₁ F₁)
        (PFunPDS.Prob.functionEvaluator b₂ F₂) =
      filteredAdaptiveTranscriptAdvantage (q := q) Filt
        (PFunPDS.Prob.functionEvaluator b₁ F₁)
        (PFunPDS.Prob.functionEvaluator b₂ F₂) :=
  adaptiveTranscriptAdvantage_eq_filtered_of_factorFamily sa Filt hFilt _ _ d
    (fun E => (sa E).factorsTranscriptLawAt_functionEvaluator
      b₁ F₁ (hdet₁ E) E (d E))
    (fun E => (sa E).factorsTranscriptLawAt_functionEvaluator
      b₂ F₂ (hdet₂ E) E (d E))

/-- **Consistent function-oracle corollary, fixed-filter form.**  Two sampled
static function oracles lose no transcript advantage when
history-determined queries are self-answered.  Repeated queries to PRFs/random
functions and coherent forward/inverse queries to permutations are the
principal instances. -/
theorem adaptiveTranscriptAdvantage_eq_filtered_of_selfAnswer
    [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q) (Filt : TranscriptPrefix X Y q → Prop)
    (hFilt : ∀ t : TranscriptPrefix X Y q,
      (∀ m : Fin q, ¬ sa.ptl (TranscriptPrefix.pairs t m.1) (t.1.get m)) →
        Filt t)
    {Ω₁ Ω₂ : Type*}
    (b₁ : Dist.ProbDist Ω₁) (b₂ : Dist.ProbDist Ω₂)
    (F₁ : Ω₁ → X → Y) (F₂ : Ω₂ → X → Y)
    (hdet₁ : ∀ (ω : Ω₁) (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F₁ ω p.1) → sa.ptl h x → F₁ ω x = sa.det h x)
    (hdet₂ : ∀ (ω : Ω₂) (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F₂ ω p.1) → sa.ptl h x → F₂ ω x = sa.det h x)
    (d : X × Y) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (PFunPDS.Prob.functionEvaluator b₁ F₁)
        (PFunPDS.Prob.functionEvaluator b₂ F₂) =
      filteredAdaptiveTranscriptAdvantage (q := q) Filt
        (PFunPDS.Prob.functionEvaluator b₁ F₁)
        (PFunPDS.Prob.functionEvaluator b₂ F₂) :=
  adaptiveTranscriptAdvantage_eq_filtered_of_selfAnswerFamily
    (fun _ => sa) Filt (fun _ => hFilt) b₁ b₂ F₁ F₂
    (fun _ => hdet₁) (fun _ => hdet₂) (fun _ => d)

/-- **Compatibility endpoint.**  The former specialized per-environment DPI
theorem is now a one-line consequence of inclusion in the unrestricted
supremum followed by the function-oracle normalization equality. -/
theorem statDist_le_filteredAdv_of_selfAnswer
    [FiniteTranscriptSpace X Y q]
    (sa : SelfAnswerFilter X Y q) (Filt : TranscriptPrefix X Y q → Prop)
    (hFilt : ∀ t : TranscriptPrefix X Y q,
      (∀ m : Fin q, ¬ sa.ptl (TranscriptPrefix.pairs t m.1) (t.1.get m)) →
        Filt t)
    {Ω₁ Ω₂ : Type*}
    (b₁ : Dist.ProbDist Ω₁) (b₂ : Dist.ProbDist Ω₂)
    (F₁ : Ω₁ → X → Y) (F₂ : Ω₂ → X → Y)
    (hdet₁ : ∀ (ω : Ω₁) (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F₁ ω p.1) → sa.ptl h x → F₁ ω x = sa.det h x)
    (hdet₂ : ∀ (ω : Ω₂) (h : List (X × Y)) (x : X),
      (∀ p ∈ h, p.2 = F₂ ω p.1) → sa.ptl h x → F₂ ω x = sa.det h x)
    (E : QQueryEnvironment X Y q) (d : X × Y) :
    (statDist (tr[q](PFunPDS.Prob.functionEvaluator b₁ F₁, E.1))
        (tr[q](PFunPDS.Prob.functionEvaluator b₂ F₂, E.1)) : ℝ) ≤
      filteredAdaptiveTranscriptAdvantage (q := q) Filt
        (PFunPDS.Prob.functionEvaluator b₁ F₁)
        (PFunPDS.Prob.functionEvaluator b₂ F₂) := by
  classical
  haveI : DiscreteTranscriptSpace X Y q := Classical.decEq _
  calc
    (statDist (tr[q](PFunPDS.Prob.functionEvaluator b₁ F₁, E.1))
        (tr[q](PFunPDS.Prob.functionEvaluator b₂ F₂, E.1)) : ℝ)
        ≤ PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
            (PFunPDS.Prob.functionEvaluator b₁ F₁)
            (PFunPDS.Prob.functionEvaluator b₂ F₂) :=
      PFunPDS.Prob.deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
        _ _ E
    _ = filteredAdaptiveTranscriptAdvantage (q := q) Filt
          (PFunPDS.Prob.functionEvaluator b₁ F₁)
          (PFunPDS.Prob.functionEvaluator b₂ F₂) :=
      adaptiveTranscriptAdvantage_eq_filtered_of_selfAnswer
        sa Filt hFilt b₁ b₂ F₁ F₂ hdet₁ hdet₂ d

end SelfAnswerFilter

end SelfAnswer

/-! ## Layer A′ — environment duality (the chooser chart)

Thesis Def 2.11 presents an environment as the *dual* of a system: positive
data saying which query to make after each output history.  On the CR18
carrier (`DDE X Y = List (Option Y) → Option X`) that data is the chooser
family

    chooser E : (i : Fin q) → (Y^i → X)      -- "after outputs ys, ask chooser E i ys"

This section makes the duality a theorem: the chooser is a **complete
invariant** of a `q`-query-total environment for `q`-round interaction —
environments with equal choosers induce equal transcript distributions, and
the adaptive advantage is *exactly* the supremum over chooser families
(upgrading the one-directional `boundedAdaptiveTranscriptAdvantage`
comparison to an equality). -/

section EnvironmentDuality

/-- The **chooser** of a `q`-query-total environment: the next query after
each concrete output history.

    chooser E i ys = the x with E (ys.map some) = some x -/
def chooser (E : QQueryEnvironment X Y q)
    (i : Fin q) (ys : Fin i.1 → Y) : X :=
  (E.1 ((List.ofFn ys).map some)).get
    (Option.isSome_iff_exists.mpr
      -- totality: |ofFn ys| = i < q, so E answers `some _`.
      (E.2 (List.ofFn ys) (by simp [i.2])))

/-- Defining property of the chooser:  E (ys.map some) = some (chooser E i ys). -/
theorem apply_map_some_eq_chooser (E : QQueryEnvironment X Y q)
    (i : Fin q) (ys : Fin i.1 → Y) :
    E.1 ((List.ofFn ys).map some) = some (chooser E i ys) := by
  simp [chooser]

/-- Embed a chooser family as a `q`-query-total environment (via the shared
`boundedDDE` bridge). -/
def ofChooser (c : (i : Fin q) → (Fin i.1 → Y) → X) :
    QQueryEnvironment X Y q :=
  ⟨boundedDDE c, fun ys hlen =>
    ⟨c ⟨ys.length, hlen⟩ (fun j => ys.get j), boundedDDE_apply_map_some_of_lt c ys hlen⟩⟩

/-- Round-trip: extracting the chooser of an embedded chooser family recovers
the family —  chooser (ofChooser c) = c. -/
theorem chooser_ofChooser (c : (i : Fin q) → (Fin i.1 → Y) → X) :
    chooser (ofChooser c) = c := by
  funext i ys
  -- (boundedDDE c) ((ofFn ys).map some) = some (c i (get-form of ys)),
  -- and the get-form of `ofFn ys` is `ys` again.
  have h := boundedDDE_apply_map_some_of_length_eq c (List.ofFn ys) i (by simp)
  simp only [chooser, ofChooser, h, Option.get_some]
  congr 1
  funext j
  simp

/-- Agreement: the canonical embedded environment `ofChooser (chooser E)`
agrees with `E` on every concrete history of length `< q` — the only
histories a `q`-round interaction ever consults. -/
theorem ofChooser_chooser_agree (E : QQueryEnvironment X Y q)
    (ys : List Y) (hlen : ys.length < q) :
    (ofChooser (chooser E)).1 (ys.map some) = E.1 (ys.map some) := by
  show boundedDDE (chooser E) (ys.map some) = E.1 (ys.map some)
  rw [boundedDDE_apply_map_some_of_lt _ _ hlen]
  -- some (chooser E ⟨|ys|,_⟩ (ys.get ·)) = E (ys.map some):
  -- unfold the chooser at the history `ofFn (ys.get ·) = ys`.
  rw [← apply_map_some_eq_chooser E ⟨ys.length, hlen⟩ (fun j => ys.get j)]
  simp

/-- **Environments agreeing on concrete histories of length `< q` have equal
length-`q` transcript laws.**  The transcript joint event only consults the
environment at histories `(ys.take i).map some` with `i < q`. -/
theorem deterministicTranscriptLaw_congr_of_agree
    (S : ProbPDS X Y) {E E' : DDE X Y}
    (h : ∀ ys : List Y, ys.length < q → E (ys.map some) = E' (ys.map some))
    (t : TranscriptPrefix X Y q) :
    trˡ[q](S, E) t = trˡ[q](S, E') t := by
  rcases t with ⟨xv, yv⟩
  -- Both sides are masses of the joint rectangle event; the system conjunct
  -- is identical, and the environment conjunct rewrites along `h` since it
  -- only mentions E at `(yv.take i).map some` with `i < q`.
  unfold deterministicTranscriptLaw transcriptLaw
  apply Dist.mass_congr
  intro ω
  dsimp only
  constructor
  · rintro ⟨hsys, henv⟩
    refine ⟨hsys, fun i hi => ?_⟩
    have hlen : (List.take i yv.toList).length < q := by
      rw [List.length_take, List.Vector.toList_length]
      omega
    have hev := henv i hi
    rw [show E' ((List.take i yv.toList).map some) =
        E ((List.take i yv.toList).map some) from (h _ hlen).symm]
    exact hev
  · rintro ⟨hsys, henv⟩
    refine ⟨hsys, fun i hi => ?_⟩
    have hlen : (List.take i yv.toList).length < q := by
      rw [List.length_take, List.Vector.toList_length]
      omega
    have hev := henv i hi
    rw [show E ((List.take i yv.toList).map some) =
        E' ((List.take i yv.toList).map some) from h _ hlen]
    exact hev

section WithFiniteTranscriptsDual

variable [FiniteTranscriptSpace X Y q]

/-- `Dist`-carrier form of the agreement transfer. -/
theorem deterministicTranscriptDist_congr_of_agree
    (S : ProbPDS X Y) {E E' : DDE X Y}
    (h : ∀ ys : List Y, ys.length < q → E (ys.map some) = E' (ys.map some)) :
    tr[q](S, E) = tr[q](S, E') := by
  ext t
  simpa [deterministicTranscriptDist] using
    deterministicTranscriptLaw_congr_of_agree S h t

/-- **Transport: the chooser is a complete invariant.**

    tr(S, ofChooser (chooser E)) = tr(S, E) -/
theorem deterministicTranscriptDist_ofChooser_chooser
    (S : ProbPDS X Y) (E : QQueryEnvironment X Y q) :
    tr[q](S, (ofChooser (chooser E)).1) = tr[q](S, E.1) :=
  deterministicTranscriptDist_congr_of_agree S
    (fun ys hlen => ofChooser_chooser_agree E ys hlen)

/-- **Duality-as-theorem for the advantage.**  The full `q`-query-total
environment supremum EQUALS the chooser-family supremum:

    Adv_q(S,T) = sup over choosers c of δ(tr(S, boundedDDE c), tr(T, boundedDDE c))

(upgrades `boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage`
to an equality: every environment's transcript distance is realized by its
chooser). -/
theorem adaptiveTranscriptAdvantage_eq_boundedAdaptiveTranscriptAdvantage
    (S T : ProbPDS X Y) :
    Adv[q](S, T) = Advᶜ[q](S, T) := by
  refine le_antisymm ?_
    (boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage
      (q := q) S T)
  -- ≤ : each environment E's transcript distance equals the one of its
  -- chooser (transport), hence appears in the chooser image.
  unfold adaptiveTranscriptAdvantage
    boundedAdaptiveTranscriptAdvantage
  refine sSup_image_univ_le_sSup_image_univ_of_forall_exists _ _
    (boundedAdaptiveTranscriptAdvantage_image_bddAbove (q := q) S T)
    (fun c => statDist_nonneg _ _) ?_
  intro E
  refine ⟨chooser E, ?_⟩
  have hS := deterministicTranscriptDist_ofChooser_chooser S E
  have hT := deterministicTranscriptDist_ofChooser_chooser T E
  simp only [ofChooser] at hS hT
  rw [← hS, ← hT]

end WithFiniteTranscriptsDual

end EnvironmentDuality


/-! ## Layer G — stress tests: the switching lemma and hash-then-PRF

Three applications exercising the derivation end-to-end, consuming only
existing counting facts (`Counting.switching_ratio_le`, `card_perm_fiber`),
the generic function-evaluator law machinery, and query compression.

The H-technique **asymmetry** on display: with `urp` as the *ideal* system,
collision transcripts have zero ideal mass, so the perfect (no-bad) endpoint
`adv_le_of_fixedQuery_ratio` applies and the switching lemma needs **no bad
event**.  With `urf` as ideal, the direct route would need
`Bad = output collisions` plus an adaptive birthday bound — instead, that
direction follows from `Adv`-symmetry of total systems. -/

section StressTests

set_option linter.unusedSectionVars false

open PFunPDS (uniformP)
open PFunPDS.Prob (urf urp fixedQueryTranscriptDist_urf
  fixedQueryTranscriptDist_functionEvaluator urf_KStepTotal)
open RandomSystems.CR18.Counting

/-- Pointwise ratios survive event masses:
`(∀ a, c·P a ≤ Q a)  ⟹  c·P(Ev) ≤ Q(Ev)`. -/
theorem mass_ratio_of_pointwise {A : Type*} (P Q : Dist A) (c : ℝ)
    (h : ∀ a, c * P a ≤ Q a) (Ev : A → Prop) :
    c * P.mass Ev ≤ Q.mass Ev := by
  classical
  cr18_mass_expand
  rw [Finset.mul_sum]
  calc (∑ a ∈ P.support, c * if Ev a then P a else 0)
      = ∑ a ∈ P.support ∪ Q.support, c * (if Ev a then P a else 0) :=
        Finset.sum_subset Finset.subset_union_left
          (fun a _ ha => by simp [Finsupp.notMem_support_iff.mp ha])
    _ ≤ ∑ a ∈ P.support ∪ Q.support, (if Ev a then Q a else 0) := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases hEv : Ev a <;> simp [hEv, h a]
    _ = ∑ a ∈ Q.support, (if Ev a then Q a else 0) :=
        (Finset.sum_subset Finset.subset_union_right
          (fun a _ ha => by simp [Finsupp.notMem_support_iff.mp ha])).symm

/-- Pointwise ratios survive pushforwards along **any** map:
`(∀ a, c·P a ≤ Q a)  ⟹  ∀ b, c·(g⋆P) b ≤ (g⋆Q) b`. -/
theorem fTransform_ratio_of_pointwise {A B : Type*} (g : A → B)
    (P Q : Dist A) (c : ℝ) (h : ∀ a, c * P a ≤ Q a) (b : B) :
    c * (Dist.fTransform g P) b ≤ (Dist.fTransform g Q) b := by
  classical
  rw [Dist.fTransform_apply_eq_mass, Dist.fTransform_apply_eq_mass]
  exact mass_ratio_of_pointwise P Q c h _

/-- Zero mass from pointwise vanishing. -/
theorem mass_eq_zero_of_forall {A : Type*} (D : Dist A) {P : A → Prop}
    (h : ∀ a, P a → D a = 0) : D.mass P = 0 := by
  classical
  cr18_mass_expand
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hP : P a
  · simp [hP, h a hP]
  · simp [hP]

/-- The whole weight is the sure event's mass. -/
theorem mass_true_eq_weight {A : Type*} (D : Dist A) :
    D.mass (fun _ => True) = D.weight := by
  cr18_mass_expand
  simp

/-- Weight splits into an event's mass and its complement's. -/
theorem probBad_add_mass_not {A : Type*} (D : Dist A) (B : A → Prop) :
    Pr[B ∣ D] + D.mass (fun a => ¬ B a) = D.weight := by
  classical
  have h := mass_eq_mass_and_add_mass_and_not D (fun _ => True) B
  simp only [true_and] at h
  rw [← mass_true_eq_weight, h]
  rfl

/-- Pointwise vanishing from zero mass (for a non-negative law). -/
theorem eq_zero_of_mass_eq_zero {A : Type*} {D : Dist A} (hD : D.NonNeg)
    {B : A → Prop}
    (h : D.mass B = 0) {a : A} (ha : B a) : D a = 0 := by
  classical
  by_contra hne
  refine absurd h (ne_of_gt ?_)
  calc (0 : ℝ) < D a := lt_of_le_of_ne (hD a) (Ne.symm hne)
    _ = (if B a then D a else 0) := by rw [if_pos ha]
    _ ≤ D.mass B := by
        unfold Dist.mass Finsupp.sum
        by_cases hs : a ∈ D.support
        · exact Finset.single_le_sum (f := fun a => if B a then D a else 0)
            (fun i _ => by by_cases h' : B i <;> simp [h', hD i]) hs
        · rw [Finsupp.notMem_support_iff.mp hs] at hne; exact absurd rfl hne

/-- **The ratio trick**: if the ideal `Q` never hits `Bad`, both are
probability distributions, and `(1−δ)·Q ≤ P` off `Bad`, then
`P.mass Bad ≤ δ`.  (Encapsulates the switching-lemma bad-mass bound.) -/
theorem probBad_le_of_ratio {A : Type*} [Fintype A] {P Q : Dist A}
    (hPnn : P.NonNeg) (hQnn : Q.NonNeg)
    (B : A → Prop) (δb : NNReal)
    (hPw : P.weight = 1) (hQw : Q.weight = 1) (hQbad : Q.mass B = 0)
    (hr : ∀ a, ¬ B a → (1 - δb) * Q a ≤ P a) :
    P.mass B ≤ δb := by
  classical
  have hfull : ∀ a, (1 - (δb : ℝ)) * Q a ≤ P a := by
    intro a
    by_cases hb : B a
    · rw [eq_zero_of_mass_eq_zero hQnn hQbad hb, mul_zero]; exact hPnn a
    · exact hr a hb
  have h1 : (1 - δb) * Q.mass (fun a => ¬ B a) ≤ P.mass (fun a => ¬ B a) :=
    mass_ratio_of_pointwise Q P (1 - δb) hfull (fun a => ¬ B a)
  have hQg : Q.mass (fun a => ¬ B a) = 1 := by
    have h := probBad_add_mass_not Q B
    unfold probBad at h; rw [hQbad, zero_add, hQw] at h; exact h
  rw [hQg, mul_one] at h1
  have hPg : P.mass B + P.mass (fun a => ¬ B a) = 1 := by
    have h := probBad_add_mass_not P B
    unfold probBad at h; rw [hPw] at h; exact h
  have hstep : P.mass B + (1 - (δb : ℝ)) ≤ 1 := by
    calc P.mass B + (1 - (δb : ℝ))
        ≤ P.mass B + P.mass (fun a => ¬ B a) := by gcongr
      _ = 1 := hPg
  linarith

/-! ### Reusable uniform-mass and event atoms (promoted from HCTR2) -/

/-- **Reusable reveal-marginal atom (fst)**: a two-source-uniform event
equivalent to a predicate `Q` on the FIRST coordinate is bounded by `Q`'s
marginal mass.  Collapses every "isolate `h̄`" collision bound to one
`prop`-application: `uniform_prod_fst_marginal_le (fun r => <shape>_eq_iff …)
(Hf.prop_k …)`. -/
theorem uniform_prod_fst_marginal_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] {P : A × B → Prop} {Q : A → Prop}
    (hPQ : ∀ p, P p ↔ Q p.1) {b : ℝ} (hQ : (Dist.uniform A).mass Q ≤ b) :
    (Dist.uniform (A × B)).mass P ≤ b := by
  rw [Dist.mass_congr _ hPQ, ← Dist.prod_uniform,
    Dist.mass_prod_fst (Dist.uniform A) (Dist.uniform B) Q,
    show (Dist.uniform B).weight = 1 from Dist.uniform_isProbDist.weight_eq, mul_one]
  exact hQ

/-- **Reusable reveal-marginal atom (snd)**: the `L`-coordinate analogue of
`uniform_prod_fst_marginal_le`. -/
theorem uniform_prod_snd_marginal_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] {P : A × B → Prop} {Q : B → Prop}
    (hPQ : ∀ p, P p ↔ Q p.2) {b : ℝ} (hQ : (Dist.uniform B).mass Q ≤ b) :
    (Dist.uniform (A × B)).mass P ≤ b := by
  rw [Dist.mass_congr _ hPQ, ← Dist.prod_uniform,
    Dist.mass_prod_snd (Dist.uniform A) (Dist.uniform B) Q,
    show (Dist.uniform A).weight = 1 from Dist.uniform_isProbDist.weight_eq, one_mul]
  exact hQ

/-- **Functional-in-second-coordinate mass** `≤ 1/|B|`: if an event on a
uniform product pins the second coordinate uniquely given the first (at most
one `b` per `a`), its uniform mass is `≤ 1/|B|`.  Robust S1 shape ("the second
coordinate isolates a uniform value"): built from `evalPred_uniform_le` with
the fiber-count bound `|{P}| ≤ |A|` (the first projection is injective on
`{P}`). -/
theorem uniform_prod_snd_functional {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (P : A × B → Prop) [DecidablePred P]
    (hP : ∀ a b b', P (a, b) → P (a, b') → b = b') :
    (Dist.uniform (A × B)).mass P ≤ (Fintype.card B : NNReal)⁻¹ := by
  have hmass : (Dist.uniform (A × B)).mass P = (Dist.uniform (A × B)).evalPred P := by
    rw [Dist.evalPred, Dist.mass_eq_sum, Finset.sum_filter]
  rw [hmass, ← one_div]
  refine Dist.evalPred_uniform_le P Fintype.card_pos ?_
  have hfib : (Finset.univ.filter P).card ≤ Fintype.card A := by
    rw [← Finset.card_univ (α := A)]
    refine Finset.card_le_card_of_injOn (fun p => p.1) (fun _ _ => Finset.mem_univ _) ?_
    rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' hpp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp hp'
    simp only at hpp
    subst hpp
    rw [hP a b b' hp hp']
  calc Fintype.card B * (Finset.univ.filter P).card
      ≤ Fintype.card B * Fintype.card A := Nat.mul_le_mul_left _ hfib
    _ = Fintype.card (A × B) := by rw [Fintype.card_prod, Nat.mul_comm]

/-- **Reusable single-coordinate functional atom (Pi)** — the `ResponseBad`
engine, generalizing `uniform_prod_snd_functional` to a uniform dependent
product: if an event pins one coordinate `i₀` uniquely given all the others (at
most one value of `f i₀` per fixing of the rest), its mass is `≤ 1/|X i₀|`.  The
"fresh URF response block is uniform given the prior transcript ⟹ 1/N" step of
the paper's response-functional collision cases. -/
theorem uniform_pi_functional {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (i₀ : ι) (P : (∀ i, X i) → Prop) [DecidablePred P]
    (hP : ∀ f g : ∀ i, X i, (∀ i, i ≠ i₀ → f i = g i) → P f → P g → f i₀ = g i₀) :
    (Dist.uniform (∀ i, X i)).mass P ≤ (Fintype.card (X i₀) : NNReal)⁻¹ := by
  have hmass : (Dist.uniform (∀ i, X i)).mass P = (Dist.uniform (∀ i, X i)).evalPred P := by
    rw [Dist.evalPred, Dist.mass_eq_sum, Finset.sum_filter]
  rw [hmass, ← one_div]
  refine Dist.evalPred_uniform_le P Fintype.card_pos ?_
  have hcard : Fintype.card (∀ i, X i)
      = Fintype.card (X i₀) * Fintype.card (∀ i : {j // j ≠ i₀}, X i) := by
    rw [Fintype.card_congr (Equiv.piSplitAt i₀ X), Fintype.card_prod]
  rw [hcard]
  refine Nat.mul_le_mul_left _ ?_
  refine Finset.card_le_card_of_injOn (fun f => (fun i : {j // j ≠ i₀} => f i.1))
    (fun _ _ => Finset.mem_univ _) ?_
  intro f hf g hg hfg
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf hg
  funext i
  by_cases hi : i = i₀
  · subst hi; exact hP f g (fun j hj => congrFun hfg ⟨j, hj⟩) hf hg
  · exact congrFun hfg ⟨i, hi⟩

/-- Uniform event mass transports along an equivalence of carriers. -/
theorem uniform_mass_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) (P : α → Prop) :
    (Dist.uniform α).mass P = (Dist.uniform β).mass (fun b => P (e.symm b)) := by
  classical
  rw [Dist.uniform_mass_eq_card_filter, Dist.uniform_mass_eq_card_filter]
  have hc : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hfilter : (Finset.univ.filter P).card
      = (Finset.univ.filter (fun b => P (e.symm b))).card := by
    refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rwa [Equiv.symm_apply_apply]
    · intro a _ a' _ h
      exact e.injective h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨e.symm b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      · exact e.apply_symm_apply b
  rw [hfilter, hc]

/-- **Self-locating pinned coordinate** (the adaptive `ResponseBad` engine):
`loc` names a coordinate *insensitively* (updating the named coordinate does
not change which coordinate is named — for us: the later query and block index
are computed from the run prefix, which never reads the designated response
block), and the event pins the named coordinate given all the others.  Then
the event's uniform mass is `≤ 1/|A|`.  Proof: `ω ↦ update ω (loc ω) a₀` is
injective from the event into the anchored slice `{ω₀ ∣ ω₀ (loc ω₀) = a₀}`,
and the slice times `A` tiles the whole space. -/
theorem uniform_pi_selfloc_le {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : (ι → A) → Prop) [DecidablePred P] (loc : (ι → A) → ι) (a₀ : A)
    (hloc : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω)
    (hpin : ∀ ω ω', loc ω = loc ω' → (∀ i, i ≠ loc ω → ω i = ω' i) →
      P ω → P ω' → ω (loc ω) = ω' (loc ω)) :
    (Dist.uniform (ι → A)).mass P ≤ (Fintype.card A : NNReal)⁻¹ := by
  classical
  -- shared cancellation: equal updates with self-located indices agree
  have cancel : ∀ (ω ω' : ι → A) (a a' : A),
      Function.update ω (loc ω) a = Function.update ω' (loc ω') a' →
      loc ω = loc ω' ∧ (∀ i, i ≠ loc ω → ω i = ω' i) ∧ a = a' := by
    intro ω ω' a a' heq
    have hli : loc ω = loc ω' := by
      calc loc ω = loc (Function.update ω (loc ω) a) := (hloc ω a).symm
        _ = loc (Function.update ω' (loc ω') a') := by rw [heq]
        _ = loc ω' := hloc ω' a'
    refine ⟨hli, fun i hi => ?_, ?_⟩
    · have h1 := congrFun heq i
      rw [Function.update_of_ne hi] at h1
      rw [h1, Function.update_of_ne (hli ▸ hi)]
    · have h1 := congrFun heq (loc ω)
      rw [Function.update_self] at h1
      rw [h1, hli, Function.update_self]
  have hmass : (Dist.uniform (ι → A)).mass P = (Dist.uniform (ι → A)).evalPred P := by
    rw [Dist.evalPred, Dist.mass_eq_sum, Finset.sum_filter]
  rw [hmass, ← one_div]
  refine Dist.evalPred_uniform_le P Fintype.card_pos ?_
  set S : Finset (ι → A) := Finset.univ.filter (fun ω₀ => ω₀ (loc ω₀) = a₀) with hS
  have hmemS : ∀ ω : ι → A, Function.update ω (loc ω) a₀ ∈ S := by
    intro ω
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hloc, Function.update_self]
  -- the anchored slice tiles the space: #Ω = #S · #A
  have hsplit : Fintype.card (ι → A) = S.card * Fintype.card A := by
    rw [← Finset.card_univ (α := ι → A), ← Finset.card_univ (α := A),
      ← Finset.card_product]
    refine (Finset.card_bij (fun w _ => Function.update w.1 (loc w.1) w.2)
      (fun _ _ => Finset.mem_univ _) ?_ ?_).symm
    · rintro ⟨ω₀, a⟩ hw ⟨ω₀', a'⟩ hw' heq
      have heq' : Function.update ω₀ (loc ω₀) a
          = Function.update ω₀' (loc ω₀') a' := heq
      obtain ⟨hli, hoff, ha⟩ := cancel ω₀ ω₀' a a' heq'
      have hw0 : ω₀ (loc ω₀) = a₀ := by
        have := (Finset.mem_product.mp hw).1
        simpa [hS] using this
      have hw0' : ω₀' (loc ω₀') = a₀ := by
        have := (Finset.mem_product.mp hw').1
        simpa [hS] using this
      have hω : ω₀ = ω₀' := by
        funext i
        by_cases hi : i = loc ω₀
        · subst hi; rw [hw0, hli, hw0']
        · exact hoff i hi
      simp [hω, ha]
    · intro ω _
      refine ⟨(Function.update ω (loc ω) a₀, ω (loc ω)),
        Finset.mem_product.mpr ⟨hmemS ω, Finset.mem_univ _⟩, ?_⟩
      show Function.update (Function.update ω (loc ω) a₀)
          (loc (Function.update ω (loc ω) a₀)) (ω (loc ω)) = ω
      rw [hloc, Function.update_idem, Function.update_eq_self]
  -- the event injects into the slice
  have hinj : (Finset.univ.filter P).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun ω => Function.update ω (loc ω) a₀)
      (fun ω _ => Finset.mem_coe.mpr (hmemS ω)) ?_
    intro ω hω ω' hω' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      at hω hω'
    have heq' : Function.update ω (loc ω) a₀
        = Function.update ω' (loc ω') a₀ := heq
    obtain ⟨hli, hoff, -⟩ := cancel ω ω' a₀ a₀ heq'
    have hat := hpin ω ω' hli hoff hω hω'
    funext i
    by_cases hi : i = loc ω
    · subst hi; exact hat
    · exact hoff i hi
  calc Fintype.card A * (Finset.univ.filter P).card
      ≤ Fintype.card A * S.card := Nat.mul_le_mul_left _ hinj
    _ = S.card * Fintype.card A := Nat.mul_comm _ _
    _ = Fintype.card (ι → A) := hsplit.symm

/-- `2·(n choose 2) = n·(n−1)`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega

/-- `2·(n choose 2) = n·(n−1)` over `ℤ` (subtraction-free caller form). -/
theorem two_mul_choose_two_int (n : ℕ) : (2 : ℤ) * n.choose 2 = n * ((n : ℤ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hz : ((2 * n.choose 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by
      exact_mod_cast two_mul_choose_two n
    push_cast [Nat.cast_sub hn] at hz
    linarith

/-- UPSTREAM-CANDIDATE: the strict upper triangle of a ranked square has
`C(n,2)` cells — the counting side of every sorted-pair union bound.  Proof:
the swap bijection pairs `<` with `>`, the diagonal has `n` cells (rank
injective), and `2·C(n,2) = n² − n`. -/
theorem card_filter_rank_lt {α : Type*} [Fintype α] [DecidableEq α]
    (rank : α → ℕ) (hinj : Function.Injective rank) :
    (Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2)).card
      = (Fintype.card α).choose 2 := by
  classical
  have hswap : (Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2)).card
      = (Finset.univ.filter (fun p : α × α => rank p.2 < rank p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simpa using hp, rfl⟩
  have hdiag : (Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2)).card
      = Fintype.card α := by
    rw [show (Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2))
        = Finset.univ.filter (fun p : α × α => p.1 = p.2) from
      Finset.filter_congr (fun p _ => by
        constructor
        · exact fun h => hinj h
        · exact fun h => congrArg rank h)]
    refine (Finset.card_bij (fun (a : α) _ => (a, a)) ?_ ?_ ?_).symm
    · intro a _
      simp
    · intro a _ b _ h
      exact congrArg Prod.fst h
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨p.1, Finset.mem_univ _, Prod.ext rfl hp⟩
  have htotal : (Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2)).card
      + (Finset.univ.filter (fun p : α × α => rank p.2 < rank p.1)).card
      + (Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2)).card
      = Fintype.card α * Fintype.card α := by
    rw [← Fintype.card_prod, ← Finset.card_univ]
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
        intro p hp1 hp2
        have h1 := (Finset.mem_filter.mp hp1).2
        have h2 := (Finset.mem_filter.mp hp2).2
        omega)),
      ← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
        intro p hp1 hp2
        have h2 := (Finset.mem_filter.mp hp2).2
        rcases Finset.mem_union.mp hp1 with h | h <;>
          · have h1 := (Finset.mem_filter.mp h).2
            omega))]
    have hcover : ((Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2) ∪
        Finset.univ.filter (fun p : α × α => rank p.2 < rank p.1)) ∪
        Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2)) = Finset.univ := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      omega
    rw [hcover]
  have h2 := two_mul_choose_two (Fintype.card α)
  have h3 : Fintype.card α * (Fintype.card α - 1)
      = Fintype.card α * Fintype.card α - Fintype.card α := Nat.mul_pred _ _
  omega

/-- UPSTREAM-CANDIDATE: a sum of a composite `g ∘ f` collapses to a
fiber-count-weighted sum over the (finite) codomain — the assembly step of
every classifier-based union bound. -/
theorem sum_comp_card_smul {α β M : Type*} [DecidableEq β] [Fintype β]
    [AddCommMonoid M] (s : Finset α) (f : α → β) (g : β → M) :
    ∑ a ∈ s, g (f a) = ∑ b : β, (s.filter (fun a => f a = b)).card • g b := by
  rw [← Finset.sum_fiberwise' s f g]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_const (g b)

/-- UPSTREAM-CANDIDATE: counting a filter through an injective
parametrization — if every element satisfying `P` is in the range of `φ`,
the count of `P` is the count of `P ∘ φ`. -/
theorem card_filter_comp {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq δ]
    (φ : γ → δ) (hφ : Function.Injective φ) (P : δ → Prop) [DecidablePred P]
    (hP : ∀ d, P d → ∃ c, φ c = d) :
    (Finset.univ.filter P).card
      = (Finset.univ.filter (fun c => P (φ c))).card := by
  rw [show Finset.univ.filter P
      = (Finset.univ.filter (fun c => P (φ c))).image φ from ?_,
    Finset.card_image_of_injective _ hφ]
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hd
    obtain ⟨c, rfl⟩ := hP d hd
    exact ⟨c, hd, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact hc

/-- UPSTREAM-CANDIDATE: a filter by independent component predicates on a
product counts as the product of the component counts. -/
theorem card_filter_prod {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter (fun x : α × β => P x.1 ∧ Q x.2)).card
      = (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [show Finset.univ.filter (fun x : α × β => P x.1 ∧ Q x.2)
      = (Finset.univ.filter P) ×ˢ (Finset.univ.filter Q) from ?_,
    Finset.card_product]
  ext x
  simp [Finset.mem_product]

/-- The strict upper triangle of `Fin n × Fin n` has `C(n, 2)` cells
(`card_filter_rank_lt` at `rank = Fin.val`). -/
theorem card_filter_fin_lt (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = n.choose 2 := by
  rw [Finset.filter_congr (fun p _ => Fin.lt_def (a := p.1) (b := p.2)),
    card_filter_rank_lt (fun x : Fin n => x.val) (fun _ _ h => Fin.ext h),
    Fintype.card_fin]

/-- Only the head index of `Fin n` has `val = 0`: count `1`. -/
theorem card_filter_fin_val_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val = 0)).card = 1 := by
  rw [show Finset.univ.filter (fun j : Fin n => j.val = 0) = {⟨0, hn⟩} from ?_,
    Finset.card_singleton]
  ext j
  simp [Fin.ext_iff]

/-- The tail indices of `Fin n` (`val ≠ 0`) count `n − 1`. -/
theorem card_filter_fin_val_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter (fun j : Fin n => ¬ j.val = 0)).card = n - 1 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun j : Fin n => j.val = 0)
  rw [card_filter_fin_val_eq_zero hn] at hsplit
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-! ### Gated head/tail sums over a fixed cap

Evaluation lemmas for sums over a fixed cap `Fin K` gated by a per-instance
validity bound `· < m`, with head (`= 0`) / tail (`≠ 0`) split values — the
shape of one instance's entry family (block `0` = `MM`/`UU`, blocks `≥ 1` =
XCTR cells) embedded in the fixed cap of a sorted-pair union bound.  Generic
in the summand values; the per-application charge tables instantiate. -/

/-- Count of the gated tail indices: `#{j : Fin K ∣ j ≠ 0 ∧ j < m} = m − 1`. -/
theorem card_filter_fin_pos_lt {K m : ℕ} (hmK : m ≤ K) :
    (Finset.univ.filter (fun j : Fin K => j.val ≠ 0 ∧ j.val < m)).card
      = m - 1 := by
  rw [show Finset.univ.filter (fun j : Fin K => j.val ≠ 0 ∧ j.val < m)
      = (Finset.Ico 1 m).attachFin (fun k hk =>
          lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hmK) from ?_,
    Finset.card_attachFin, Nat.card_Ico]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
    Finset.mem_Ico]
  omega

/-- **Gated head/tail sum**: `Σ_{j < m} (head/tail value) = X + (m−1)•Y`. -/
theorem sum_fin_gate {K m : ℕ} {M : Type*} [AddCommMonoid M]
    (hm : 1 ≤ m) (hmK : m ≤ K) (X Y : M) :
    ∑ j : Fin K, (if j.val < m then (if j.val = 0 then X else Y) else 0)
      = X + (m - 1) • Y := by
  classical
  have hsplit : ∀ j : Fin K,
      (if j.val < m then (if j.val = 0 then X else Y) else 0)
        = (if j.val = 0 ∧ j.val < m then X else 0)
          + (if j.val ≠ 0 ∧ j.val < m then Y else 0) := by
    intro j
    by_cases h0 : j.val = 0 <;> by_cases hlt : j.val < m <;> simp [h0, hlt]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    card_filter_fin_pos_lt hmK]
  congr 2
  rw [show Finset.univ.filter (fun j : Fin K => j.val = 0 ∧ j.val < m)
      = {(⟨0, lt_of_lt_of_le hm hmK⟩ : Fin K)} from ?_, Finset.card_singleton,
    one_smul]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Fin.ext_iff]
  omega

/-- **Gated product head/tail sum** (the cross-instance pair family):
`Σ_{i<m₁, j<m₂}` of the four-way head/tail split value. -/
theorem sum_fin_gate_prod {K m₁ m₂ : ℕ} {M : Type*} [AddCommMonoid M]
    (h₁ : 1 ≤ m₁) (hK₁ : m₁ ≤ K) (h₂ : 1 ≤ m₂) (hK₂ : m₂ ≤ K) (P Q R S : M) :
    ∑ p : Fin K × Fin K, (if p.1.val < m₁ ∧ p.2.val < m₂ then
        (if p.1.val = 0 then (if p.2.val = 0 then P else Q)
         else (if p.2.val = 0 then R else S)) else 0)
      = (P + (m₂ - 1) • Q) + (m₁ - 1) • (R + (m₂ - 1) • S) := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner : ∀ i : Fin K,
      (∑ j : Fin K, if i.val < m₁ ∧ j.val < m₂ then
          (if i.val = 0 then (if j.val = 0 then P else Q)
           else (if j.val = 0 then R else S)) else 0)
        = if i.val < m₁ then
            (if i.val = 0 then P + (m₂ - 1) • Q else R + (m₂ - 1) • S) else 0 := by
    intro i
    by_cases hi : i.val < m₁
    · by_cases hi0 : i.val = 0
      · rw [if_pos hi, if_pos hi0, ← sum_fin_gate h₂ hK₂ P Q]
        exact Finset.sum_congr rfl (fun j _ => by
          simp [hi0, show 0 < m₁ from h₁])
      · rw [if_pos hi, if_neg hi0, ← sum_fin_gate h₂ hK₂ R S]
        exact Finset.sum_congr rfl (fun j _ => by simp [hi, hi0])
    · rw [if_neg hi]
      exact Finset.sum_eq_zero (fun j _ => by simp [hi])
  rw [Finset.sum_congr rfl (fun i _ => hinner i), ← sum_fin_gate h₁ hK₁
    (P + (m₂ - 1) • Q) (R + (m₂ - 1) • S)]

/-- **Gated sorted head/tail sum** (the same-instance pair family):
`Σ_{i<j, j<m} (head/tail-of-i value) = (m−1)•X + C(m−1,2)•Y`. -/
theorem sum_fin_gate_sorted {K m : ℕ} {M : Type*} [AddCommMonoid M]
    (hmK : m ≤ K) (X Y : M) :
    ∑ p : Fin K × Fin K,
        (if p.1.val < p.2.val ∧ p.2.val < m then
          (if p.1.val = 0 then X else Y) else 0)
      = (m - 1) • X + (m - 1).choose 2 • Y := by
  classical
  have hsplit : ∀ p : Fin K × Fin K,
      (if p.1.val < p.2.val ∧ p.2.val < m then
          (if p.1.val = 0 then X else Y) else 0)
        = (if p.1.val = 0 ∧ (p.2.val ≠ 0 ∧ p.2.val < m) then X else 0)
          + (if p.1.val ≠ 0 ∧ p.1.val < p.2.val ∧ p.2.val < m then Y else 0) := by
    intro p
    split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl (fun p _ => hsplit p), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const]
  congr 2
  · -- head fiber: `p.1 = 0`, `0 < p.2 < m` — count `m − 1`
    rw [card_filter_prod (fun i : Fin K => i.val = 0)
      (fun j : Fin K => j.val ≠ 0 ∧ j.val < m), card_filter_fin_pos_lt hmK]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [card_filter_fin_val_eq_zero (lt_of_lt_of_le hm hmK), one_mul]
  · -- tail–tail fiber: `1 ≤ p.1 < p.2 < m` — count `C(m−1, 2)`
    rw [show Finset.univ.filter (fun p : Fin K × Fin K =>
          p.1.val ≠ 0 ∧ p.1.val < p.2.val ∧ p.2.val < m)
        = Finset.map ⟨fun p : Fin (m - 1) × Fin (m - 1) =>
            ((⟨p.1.val + 1, by omega⟩ : Fin K), (⟨p.2.val + 1, by omega⟩ : Fin K)),
            by
              intro p p' h
              simp only [Prod.ext_iff, Fin.ext_iff] at h ⊢
              omega⟩
          (Finset.univ.filter (fun p : Fin (m - 1) × Fin (m - 1) => p.1 < p.2))
        from ?_, Finset.card_map, card_filter_fin_lt]
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, Prod.ext_iff, Fin.ext_iff, Fin.lt_def]
    constructor
    · rintro ⟨h0, hij, hm'⟩
      exact ⟨(⟨p.1.val - 1, by omega⟩, ⟨p.2.val - 1, by omega⟩),
        by dsimp only; omega, by dsimp only; omega⟩
    · rintro ⟨p', hp', h1, h2⟩
      omega

/-- **Sorted-pair block split over a `Bool ⊕ (instance × slot)` cap**: for any
rank placing the two constants below every entry, constants ordered
`false < true`, and entries ordered lexicographically, the sorted-pair sum
decomposes into the constant pair, the const–entry block, the cross-instance
block, and the same-instance sorted block.  The counting side of a
classifier-based sorted-pair union bound with per-instance charge tables
(the constant-charge route instead goes through `sum_comp_card_smul`). -/
theorem sum_sorted_capSplit {q K : ℕ} {M' : Type*} [AddCommMonoid M']
    (rank : (Bool ⊕ Fin q × Fin K) → ℕ)
    (h01 : rank (Sum.inl false) < rank (Sum.inl true))
    (hli : ∀ b (x : Fin q × Fin K), rank (Sum.inl b) < rank (Sum.inr x))
    (hil : ∀ (x : Fin q × Fin K) b, ¬ rank (Sum.inr x) < rank (Sum.inl b))
    (hrr : ∀ (r : Fin q) (i : Fin K) (s : Fin q) (j : Fin K),
      rank (Sum.inr (r, i)) < rank (Sum.inr (s, j))
        ↔ r < s ∨ (r = s ∧ i.val < j.val))
    (g : (Bool ⊕ Fin q × Fin K) × (Bool ⊕ Fin q × Fin K) → M') :
    (∑ p ∈ Finset.univ.filter
        (fun p : (Bool ⊕ Fin q × Fin K) × (Bool ⊕ Fin q × Fin K) =>
          rank p.1 < rank p.2), g p)
      = g (Sum.inl false, Sum.inl true)
        + (∑ s : Fin q, ∑ j : Fin K,
            (g (Sum.inl false, Sum.inr (s, j)) + g (Sum.inl true, Sum.inr (s, j))))
        + ((∑ rs ∈ Finset.univ.filter (fun rs : Fin q × Fin q => rs.1 < rs.2),
              ∑ i : Fin K, ∑ j : Fin K, g (Sum.inr (rs.1, i), Sum.inr (rs.2, j)))
          + ∑ s : Fin q, ∑ i : Fin K, ∑ j : Fin K,
              (if i.val < j.val then g (Sum.inr (s, i), Sum.inr (s, j)) else 0)) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_sum_type]
  congr 1
  · -- outer `inl` block: the constant rows
    rw [Fintype.sum_bool]
    have ht : (∑ y : Bool ⊕ Fin q × Fin K,
        if rank (Sum.inl true) < rank y then g (Sum.inl true, y) else 0)
        = ∑ x : Fin q × Fin K, g (Sum.inl true, Sum.inr x) := by
      rw [Fintype.sum_sum_type]
      rw [show (∑ b : Bool, if rank (Sum.inl true) < rank (Sum.inl b)
          then g (Sum.inl true, Sum.inl b) else 0) = 0 from by
        rw [Fintype.sum_bool, if_neg (lt_irrefl _), if_neg (lt_asymm h01),
          add_zero]]
      rw [zero_add]
      exact Finset.sum_congr rfl (fun x _ => if_pos (hli true x))
    have hf : (∑ y : Bool ⊕ Fin q × Fin K,
        if rank (Sum.inl false) < rank y then g (Sum.inl false, y) else 0)
        = g (Sum.inl false, Sum.inl true)
          + ∑ x : Fin q × Fin K, g (Sum.inl false, Sum.inr x) := by
      rw [Fintype.sum_sum_type]
      congr 1
      · rw [Fintype.sum_bool, if_pos h01, if_neg (lt_irrefl _), add_zero]
      · exact Finset.sum_congr rfl (fun x _ => if_pos (hli false x))
    rw [ht, hf]
    have hmerge : (∑ s : Fin q, ∑ j : Fin K,
        (g (Sum.inl false, Sum.inr (s, j)) + g (Sum.inl true, Sum.inr (s, j))))
        = (∑ x : Fin q × Fin K, g (Sum.inl false, Sum.inr x))
          + ∑ x : Fin q × Fin K, g (Sum.inl true, Sum.inr x) := by
      rw [show (∑ x : Fin q × Fin K, g (Sum.inl false, Sum.inr x))
          = ∑ s : Fin q, ∑ j : Fin K, g (Sum.inl false, Sum.inr (s, j)) from
        Fintype.sum_prod_type _,
        show (∑ x : Fin q × Fin K, g (Sum.inl true, Sum.inr x))
          = ∑ s : Fin q, ∑ j : Fin K, g (Sum.inl true, Sum.inr (s, j)) from
        Fintype.sum_prod_type _,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.sum_add_distrib])
    rw [hmerge]
    abel
  · -- outer `inr` block: `(inr, inl)` never sorted; `(inr, inr)` splits by lex
    have hrow : ∀ x : Fin q × Fin K,
        (∑ y : Bool ⊕ Fin q × Fin K,
          if rank (Sum.inr x) < rank y then g (Sum.inr x, y) else 0)
        = (∑ s : Fin q, (if x.1 < s then
              ∑ j : Fin K, g (Sum.inr x, Sum.inr (s, j)) else 0))
          + ∑ j : Fin K,
              (if x.2.val < j.val then g (Sum.inr x, Sum.inr (x.1, j)) else 0) := by
      intro x
      obtain ⟨r, i⟩ := x
      rw [Fintype.sum_sum_type]
      rw [show (∑ b : Bool, if rank (Sum.inr (r, i)) < rank (Sum.inl b)
          then g (Sum.inr (r, i), Sum.inl b) else 0) = 0 from by
        rw [Fintype.sum_bool, if_neg (hil _ _), if_neg (hil _ _), add_zero]]
      rw [zero_add, Fintype.sum_prod_type]
      have hpt : ∀ (s : Fin q) (j : Fin K),
          (if rank (Sum.inr (r, i)) < rank (Sum.inr (s, j))
            then g (Sum.inr (r, i), Sum.inr (s, j)) else 0)
          = (if r < s then g (Sum.inr (r, i), Sum.inr (s, j)) else 0)
            + (if r = s ∧ i.val < j.val then
                g (Sum.inr (r, i), Sum.inr (s, j)) else 0) := by
        intro s j
        simp only [hrr r i s j]
        by_cases h1 : r < s
        · rw [if_pos (Or.inl h1), if_pos h1,
            if_neg (fun h2 => absurd h2.1 (ne_of_lt h1)), add_zero]
        · by_cases h2 : r = s ∧ i.val < j.val
          · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
          · rw [if_neg (fun h => h.elim h1 h2), if_neg h1, if_neg h2, add_zero]
      rw [Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl
        (fun j _ => hpt s j))]
      rw [show (∑ s : Fin q, ∑ j : Fin K,
          ((if r < s then g (Sum.inr (r, i), Sum.inr (s, j)) else 0)
            + (if r = s ∧ i.val < j.val then
                g (Sum.inr (r, i), Sum.inr (s, j)) else 0)))
        = (∑ s : Fin q, ∑ j : Fin K,
            (if r < s then g (Sum.inr (r, i), Sum.inr (s, j)) else 0))
          + ∑ s : Fin q, ∑ j : Fin K,
              (if r = s ∧ i.val < j.val then
                g (Sum.inr (r, i), Sum.inr (s, j)) else 0) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.sum_add_distrib])]
      congr 1
      · -- cross rows: pull the `r < s` guard out of the `j`-sum
        refine Finset.sum_congr rfl (fun s _ => ?_)
        by_cases hrs : r < s
        · rw [if_pos hrs]
          exact Finset.sum_congr rfl (fun j _ => if_pos hrs)
        · rw [if_neg hrs]
          exact Finset.sum_eq_zero (fun j _ => if_neg hrs)
      · -- same-instance rows: collapse the `s`-sum at `s = r`
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (∑ s : Fin q, if r = s ∧ i.val < j.val then
            g (Sum.inr (r, i), Sum.inr (s, j)) else 0)
          = ∑ s : Fin q, if i.val < j.val then
              (if r = s then g (Sum.inr (r, i), Sum.inr (s, j)) else 0) else 0
          from Finset.sum_congr rfl (fun s _ => by
            by_cases h1 : r = s <;> by_cases h2 : i.val < j.val <;>
              simp [h1, h2])]
        by_cases h2 : i.val < j.val
        · simp only [if_pos h2]
          rw [Finset.sum_ite_eq Finset.univ r
            (fun s => g (Sum.inr (r, i), Sum.inr (s, j))),
            if_pos (Finset.mem_univ r)]
        · simp only [if_neg h2, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl (fun x _ => hrow x), Finset.sum_add_distrib]
    congr 1
    · -- cross block: regroup `(r, i)` sums into the sorted `(r, s)` Finset
      rw [Fintype.sum_prod_type]
      rw [show (∑ r : Fin q, ∑ i : Fin K, ∑ s : Fin q,
          (if (r, i).1 < s then
            ∑ j : Fin K, g (Sum.inr (r, i), Sum.inr (s, j)) else 0))
        = ∑ r : Fin q, ∑ s : Fin q, (if r < s then
            ∑ i : Fin K, ∑ j : Fin K,
              g (Sum.inr (r, i), Sum.inr (s, j)) else 0) from ?_]
      · rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
      · refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        by_cases hrs : r < s
        · simp only [if_pos hrs]
        · simp only [if_neg hrs, Finset.sum_const_zero]
    · -- same block: flatten the pair sum
      rw [Fintype.sum_prod_type]

/-- UPSTREAM-CANDIDATE (CR18-native union bound): the `mass` of a witnessed
event is at most the sum of per-witness masses over an explicit witness
`Finset` — the witness may be constrained to `s`, and only `s`'s masses are
summed.  Stated at the `Finsupp` `mass` level — **no** `Fintype` carrier,
**no** `DecidablePred` — so it applies on huge transcript spaces with zero
instance-defeq cost (unlike `probBad_iUnion_le`/`evalPred`, whose carrier
`Fintype`/filter decidability blow up `whnf`). -/
theorem mass_witness_sum_le {A ι : Type*} {D : Dist A} (hDnn : D.NonNeg)
    (s : Finset ι)
    (B : A → Prop) (P : ι → A → Prop) (hB : ∀ a, B a → ∃ i ∈ s, P i a) :
    D.mass B ≤ ∑ i ∈ s, D.mass (P i) := by
  classical
  refine le_trans (mass_mono hDnn hB) ?_
  simp only [Dist.mass, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases h : ∃ i ∈ s, P i a
  · obtain ⟨i₀, hi₀s, hi₀⟩ := h
    rw [if_pos ⟨i₀, hi₀s, hi₀⟩]
    calc D a = if P i₀ a then D a else 0 := (if_pos hi₀).symm
      _ ≤ ∑ i ∈ s, if P i a then D a else 0 :=
        Finset.single_le_sum (f := fun i => if P i a then D a else 0)
          (fun i _ => by by_cases h' : P i a <;> simp [h', hDnn a]) hi₀s
  · rw [if_neg h]
    exact Finset.sum_nonneg fun i _ => by
      by_cases h' : P i a <;> simp [h', hDnn a]

/-- The all-witnesses (`s = univ`) instance of `mass_witness_sum_le`. -/
theorem mass_witness_iUnion_le {A ι : Type*} [Fintype ι] {D : Dist A}
    (hDnn : D.NonNeg)
    (B : A → Prop) (P : ι → A → Prop) (hB : ∀ a, B a → ∃ p, P p a) :
    D.mass B ≤ ∑ p, D.mass (P p) :=
  mass_witness_sum_le hDnn Finset.univ B P
    (fun a ha => let ⟨p, hp⟩ := hB a ha; ⟨p, Finset.mem_univ p, hp⟩)

/-- UPSTREAM-CANDIDATE: sorted-pair union bound over a fixed ranked cap — a
within-family collision event is bounded by the sum of per-**sorted**-pair
bounds (`rank p.1 < rank p.2`; the witness pair is sorted via the injective
rank, using the symmetry of the collision event). -/
theorem mass_sorted_pair_le {A κ V : Type*} [Fintype κ] {D : Dist A}
    (hDnn : D.NonNeg)
    (rank : κ → ℕ) (hinj : Function.Injective rank)
    (valid : A → κ → Prop) (f : A → κ → V) (bound : κ × κ → ℝ)
    (hcell : ∀ p : κ × κ, rank p.1 < rank p.2 →
      D.mass (fun a => valid a p.1 ∧ valid a p.2 ∧ f a p.1 = f a p.2) ≤ bound p) :
    D.mass (fun a => ∃ i j : κ, i ≠ j ∧ valid a i ∧ valid a j ∧ f a i = f a j)
      ≤ ∑ p ∈ Finset.univ.filter (fun p : κ × κ => rank p.1 < rank p.2),
          bound p := by
  classical
  refine le_trans (mass_witness_sum_le hDnn
      (Finset.univ.filter (fun p : κ × κ => rank p.1 < rank p.2)) _
      (fun p a => valid a p.1 ∧ valid a p.2 ∧ f a p.1 = f a p.2) ?_)
    (Finset.sum_le_sum fun p hp => hcell p (Finset.mem_filter.mp hp).2)
  rintro a ⟨i, j, hne, hvi, hvj, hf⟩
  rcases lt_or_gt_of_ne (fun h => hne (hinj h)) with h | h
  · exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hvi, hvj, hf⟩
  · exact ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hvj, hvi, hf.symm⟩

/-- Embedded-index front end of `mass_sorted_pair_le`: the collision family
lives on an `a`-dependent index type embedded (injectively, value- and
validity-preservingly) in the fixed ranked cap `κ`. -/
theorem mass_sorted_pair_le_of_embed {A κ V : Type*} [Fintype κ] {D : Dist A}
    (hDnn : D.NonNeg)
    (rank : κ → ℕ) (hinj : Function.Injective rank)
    {ι : A → Type*} (e : ∀ a, ι a → κ) (hem : ∀ a, Function.Injective (e a))
    (g : ∀ a, ι a → V) (valid : A → κ → Prop) (f : A → κ → V)
    (hval : ∀ a i, valid a (e a i)) (hf : ∀ a i, f a (e a i) = g a i)
    (bound : κ × κ → ℝ)
    (hcell : ∀ p : κ × κ, rank p.1 < rank p.2 →
      D.mass (fun a => valid a p.1 ∧ valid a p.2 ∧ f a p.1 = f a p.2) ≤ bound p) :
    D.mass (fun a => ∃ i j : ι a, i ≠ j ∧ g a i = g a j)
      ≤ ∑ p ∈ Finset.univ.filter (fun p : κ × κ => rank p.1 < rank p.2),
          bound p := by
  refine le_trans (mass_mono hDnn ?_)
    (mass_sorted_pair_le hDnn rank hinj valid f bound hcell)
  rintro a ⟨i, j, hne, hg⟩
  exact ⟨e a i, e a j, fun h => hne (hem a h), hval a i, hval a j,
    by rw [hf, hf, hg]⟩

/-- UPSTREAM-CANDIDATE: two-event union bound at the `mass` level (no `Fintype`
carrier, no decidability). -/
theorem mass_or_le {A : Type*} {D : Dist A} (hDnn : D.NonNeg) (P Q : A → Prop) :
    D.mass (fun a => P a ∨ Q a) ≤ D.mass P + D.mass Q :=
  Dist.mass_or_le hDnn P Q

/-- UPSTREAM-CANDIDATE: a symmetric pair event's mass is orientation-invariant —
each unordered shape lemma bounds both ordered orientations of the per-pair sum. -/
theorem mass_pairSwap_eq {A ι β : Type*} (D : Dist A) (V : A → ι → Prop)
    (f : A → ι → β) (a b : ι) :
    D.mass (fun x => a ≠ b ∧ V x a ∧ V x b ∧ f x a = f x b)
      = D.mass (fun x => b ≠ a ∧ V x b ∧ V x a ∧ f x b = f x a) :=
  Dist.mass_congr _ (fun _ =>
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3, h2, h4.symm⟩,
     fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3, h2, h4.symm⟩⟩)

section WithFiniteTranscriptsG2

variable [FiniteTranscriptSpace X Y q]

/-- `Adv` is symmetric on total systems (per-environment `statDist` symmetry
under equal weights). -/
theorem adaptiveTranscriptAdvantage_symm
    (S T : ProbPDS X Y) (hS : S.KStepTotal q) (hT : T.KStepTotal q) :
    Adv[q](S, T) = Adv[q](T, S) := by
  unfold adaptiveTranscriptAdvantage
  congr 1
  have : (fun E : QQueryEnvironment X Y q =>
      (δ(tr[q](S, E.1), tr[q](T, E.1)) : ℝ)) =
      fun E => (δ(tr[q](T, E.1), tr[q](S, E.1)) : ℝ) := by
    funext E
    rw [statDist_symm_of_eq_weight _ _
      (deterministicTranscriptDist_weight_eq S T E hS hT)]
  rw [this]

/-- The adaptive advantage of total systems is at most `1`. -/
theorem adaptiveTranscriptAdvantage_le_one
    (S T : ProbPDS X Y) (hS : S.KStepTotal q) (_hT : T.KStepTotal q) :
    Adv[q](S, T) ≤ 1 := by
  apply adaptiveTranscriptAdvantage_le_of_pointwise S T 1
  intro E
  rw [NNReal.coe_one]
  calc δ(tr[q](S, E.1), tr[q](T, E.1)) ≤ (tr[q](S, E.1)).weight :=
        statDist_le_weight (deterministicTranscriptDist_nonNeg S E.1)
          (deterministicTranscriptDist_nonNeg T E.1)
    _ = 1 := deterministicTranscriptDist_weight_eq_one S E hS

end WithFiniteTranscriptsG2

/-! ### The URP bridges (nextgen `ProbPDS.urp` is a function-evaluator law) -/

/-- `urp` **is** the function-evaluator law of a uniformly sampled
permutation — its definition is the pushforward `σ ↦ functionEvaluator σ`. -/
theorem urp_eq_functionEvaluator {X : Type u} [Fintype X] [DecidableEq X] :
    urp (X := X) =
      PFunPDS.Prob.functionEvaluator
        ⟨Dist.uniform (Equiv.Perm X),
          by
            haveI : Nonempty (Equiv.Perm X) := ⟨Equiv.refl X⟩
            exact Dist.uniform_isProbDist⟩
        (fun σ => σ.toFun) := by
  refine Subtype.ext ?_
  show PFunPDS.URP X = _
  unfold PFunPDS.URP PFunPDS.ofPermDist PFunPDS.Prob.functionEvaluator
    Dist.PMF functionEvaluatorRV
  dsimp only
  congr 1
  first
    | exact Subsingleton.elim _ _
    | · congr 1
        exact Subsingleton.elim _ _

/-- `urp` is total for every query budget (via the generic function-evaluator
totality). -/
theorem urp_KStepTotal {X : Type u} [Fintype X] [DecidableEq X] (k : ℕ) :
    (urp (X := X)).KStepTotal k := by
  rw [urp_eq_functionEvaluator]
  exact functionEvaluatorProb_KStepTotal _ _ k



/-! ### Product-mass and general-tuple evaluation helpers -/

/-- Product mass with the first coordinate pinned:
`(P ⊗ Q){p : C(p) ∧ p.1 = a} = P(a) · Q(C(a,·))`. -/
theorem mass_prod_fst_eq {A B : Type*} [Fintype A] [Fintype B]
    (P : Dist A) (Q : Dist B) (a : A) (C : A → B → Prop) :
    (Dist.prod P Q).mass (fun p => C p.1 p.2 ∧ p.1 = a) =
      P a * Q.mass (C a) := by
  classical
  rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  have h1 : ∀ a' : A, (∑ b : B,
      if C a' b ∧ a' = a then Dist.prod P Q (a', b) else 0) =
      if a' = a then P a * Q.mass (C a) else 0 := by
    intro a'
    by_cases ha : a' = a
    · subst ha
      rw [if_pos rfl, Dist.mass_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : C a' b
      · simp [hb, Dist.prod_apply]
      · simp [hb]
    · rw [if_neg ha]
      exact Finset.sum_eq_zero fun b _ => if_neg (fun h => ha h.2)
  refine Eq.trans (Finset.sum_congr rfl fun a' _ =>
    Eq.trans (Finset.sum_congr rfl fun b _ => by congr) (h1 a')) (by simp)

/-- Product mass of a second-coordinate event:
`(P ⊗ Q){p : p.2 = b} = |P| · Q(b)`. -/
theorem mass_prod_snd_eq {A B : Type*} [Fintype A] [Fintype B]
    (P : Dist A) (Q : Dist B) (b : B) :
    (Dist.prod P Q).mass (fun p => p.2 = b) = P.weight * Q b := by
  classical
  rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  have h1 : ∀ a : A, (∑ b' : B,
      if b' = b then Dist.prod P Q (a, b') else 0) = P a * Q b := by
    intro a
    rw [Finset.sum_ite_eq' Finset.univ b]
    simp [Dist.prod_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a _ =>
    Eq.trans (Finset.sum_congr rfl fun b' _ => by congr) (h1 a)) ?_
  rw [← Finset.sum_mul, Dist.weight_eq_sum]

/-- Product mass of a second-coordinate event (predicate form). -/
theorem mass_prod_snd_pred {A B : Type*} [Fintype A] [Fintype B]
    (P : Dist A) (Q : Dist B) (C : B → Prop) :
    (Dist.prod P Q).mass (fun p => C p.2) = P.weight * Q.mass C := by
  classical
  rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  have h1 : ∀ a : A, (∑ b : B,
      if C (a, b).2 then Dist.prod P Q (a, b) else 0) = P a * Q.mass C := by
    intro a
    rw [Dist.mass_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : C b
    · simp [hb, Dist.prod_apply]
    · simp [hb]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => h1 a) ?_
  rw [← Finset.sum_mul, Dist.weight_eq_sum]

/-- Event masses of tuple constraints are evaluation-pushforward values. -/
theorem mass_eval_eq_apply {X' Y' : Type*} (D : Dist (X' → Y'))
    (u : Fin q → X') (v : Fin q → Y') :
    D.mass (fun f => ∀ i, f (u i) = v i) =
      (Dist.fTransform (fun f : X' → Y' => fun i => f (u i)) D) v := by
  rw [Dist.fTransform_apply_eq_mass]
  exact Dist.mass_congr _ (fun f => by
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congr_fun h i)

/-! ### Product-factored mass bounds (Fubini corollaries)

Shared collapse skeleton: when a joint distribution factors as
`D (a, b) = (mass of b) * (mass of a)`, its event mass is bounded by any
uniform per-fiber bound — sum the outer coordinate against the
(sub-)probability weight of its factor, bound each fiber by `bnd`.  Both
HCTR2 collapse bridges (`revealCollapse_le`, `hctr_omega_slice_le`) are
instances, with the roles of the two coordinates exchanged. -/

/-- Fiber bound over the **second** coordinate: if `D (a, b) = u b * f a`
with `∑ f ≤ 1`, and every mass-carrying `a`-slice has `u`-mass at most
`bnd`, then `D.mass P ≤ bnd`. -/
theorem mass_le_of_fiber_snd {A B : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (f : A → ℝ) (u : Dist B)
    (hD : ∀ a b, D (a, b) = u b * f a) (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf : ∑ a, f a ≤ 1)
    (P : A × B → Prop) (bnd : ℝ) (hbnd : 0 ≤ bnd)
    (h : ∀ a, f a ≠ 0 → u.mass (fun b => P (a, b)) ≤ bnd) :
    D.mass P ≤ bnd := by
  classical
  rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  have hinner : ∀ a, (∑ b, if P (a, b) then D (a, b) else 0)
      = u.mass (fun b => P (a, b)) * f a := by
    intro a
    rw [Dist.mass_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hp : P (a, b) <;> simp [hp, hD a b]
  calc (∑ a, ∑ b, if P (a, b) then D (a, b) else 0)
      ≤ ∑ a, bnd * f a := Finset.sum_le_sum fun a _ => by
        rw [hinner a]
        rcases eq_or_ne (f a) 0 with h0 | h0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_right (h a h0) (hf_nonneg a)
    _ = bnd * ∑ a, f a := by
        rw [Finset.mul_sum]
    _ ≤ bnd * 1 := mul_le_mul_of_nonneg_left hf hbnd
    _ = bnd := mul_one _

/-- Fiber bound over the **first** coordinate (the transpose of
`mass_le_of_fiber_snd`): if `D (a, b) = g b * w a` with `∑ g ≤ 1`, and every
mass-carrying `b`-slice has `w`-mass at most `bnd`, then `D.mass P ≤ bnd`. -/
theorem mass_le_of_fiber_fst {A B : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (w : Dist A) (g : B → ℝ)
    (hD : ∀ a b, D (a, b) = g b * w a) (hg_nonneg : ∀ b, 0 ≤ g b)
    (hg : ∑ b, g b ≤ 1)
    (P : A × B → Prop) (bnd : ℝ) (hbnd : 0 ≤ bnd)
    (h : ∀ b, g b ≠ 0 → w.mass (fun a => P (a, b)) ≤ bnd) :
    D.mass P ≤ bnd := by
  classical
  rw [Dist.mass_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  have hinner : ∀ b, (∑ a, if P (a, b) then D (a, b) else 0)
      = g b * w.mass (fun a => P (a, b)) := by
    intro b
    rw [Dist.mass_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : P (a, b) <;> simp [hp, hD a b]
  calc (∑ b, ∑ a, if P (a, b) then D (a, b) else 0)
      ≤ ∑ b, g b * bnd := Finset.sum_le_sum fun b _ => by
        rw [hinner b]
        rcases eq_or_ne (g b) 0 with h0 | h0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (h b h0) (hg_nonneg b)
    _ = (∑ b, g b) * bnd := by
        rw [Finset.sum_mul]
    _ ≤ 1 * bnd := mul_le_mul_of_nonneg_right hg hbnd
    _ = bnd := one_mul _

/-- **Independent-reveal factorization**: for a product sampler `p₁ ⊗ p₂`
whose sampled system reads only the second coordinate while the reveal is
the first, the extended transcript distribution factors as
`reveal-marginal × transcript-distribution`.  The HCTR2 ideal world
(dummy `(h̄, L)` × URF coins) is the motivating instance. -/
theorem extendedTranscriptDistRep_indep {Ω₁ Ω₂ : Type*}
    [Fintype Ω₁] [DecidableEq Ω₁] [Fintype Ω₂] [DecidableEq X]
    [FiniteTranscriptSpace X Y q] [DiscreteTranscriptSpace X Y q]
    (p₁ : Dist.ProbDist Ω₁) (p₂ : Dist.ProbDist Ω₂) (fn : Ω₂ → X → Y)
    (E : DDE X Y) (t : TranscriptPrefix X Y q) (z : Ω₁) :
    extendedTranscriptDistRep (q := q) (Dist.prodProbDist p₁ p₂)
        (functionEvaluatorRV (fun p => fn p.2)) (fun p _ => p.1) E (t, z)
      = p₁.val z * (tr[q](PFunPDS.Prob.functionEvaluator p₂ fn, E)) t := by
  classical
  have hfac : extSysFactorRep (q := q) (Dist.prodProbDist p₁ p₂)
      (functionEvaluatorRV (fun p : Ω₁ × Ω₂ => fn p.2)) (fun p _ => p.1)
      ((t, z) : TranscriptPrefix X Y q × Ω₁)
      = p₁.val z * p₂.val.mass (fun g => ∀ i, fn g (t.1.get i) = t.2.get i) := by
    refine Eq.trans (b := (Dist.prod p₁.val p₂.val).mass
        (fun p => (∀ i, fn p.2 (t.1.get i) = t.2.get i) ∧ p.1 = z)) ?_ ?_
    · exact Dist.mass_congr _ (fun p => and_congr_left'
        (transcriptSystemEvent_functionEvaluatorRV_iff _ t.1 t.2 p))
    · exact mass_prod_fst_eq p₁.val p₂.val z
        (fun _ g => ∀ i, fn g (t.1.get i) = t.2.get i)
  rw [extendedTranscriptDistRep_apply, hfac,
    deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    sysFactor_functionEvaluator, mul_assoc]

theorem compressedQueryIndex_surjective {X' : Type*} [Fintype X']
    (u : Fin q → X') : Function.Surjective (compressedQueryIndex u) := by
  letI : DecidableEq X' := Classical.decEq X'
  intro a
  obtain ⟨i, -, hxi⟩ := Finset.mem_image.mp
    ((Fintype.equivFin {x : X' // x ∈ queryImageSet u}).symm a).2
  exact ⟨i, by
    unfold compressedQueryIndex
    exact (congrArg (Fintype.equivFin {x : X' // x ∈ queryImageSet u})
      (Subtype.ext hxi)).trans (Equiv.apply_symm_apply _ a)⟩

theorem expandCompressedOutputs_injective {X' Y' : Type*} [Fintype X']
    (u : Fin q → X') :
    Function.Injective (expandCompressedOutputs (Y := Y') u) := by
  intro w w' h
  funext a
  obtain ⟨i, rfl⟩ := compressedQueryIndex_surjective u a
  exact congr_fun h i

theorem compressedQuery_compressedQueryIndex {X' : Type*} [Fintype X']
    (u : Fin q → X') (i : Fin q) :
    compressedQuery u (compressedQueryIndex u i) = u i :=
  congr_fun (expandCompressedOutputs_compressedQuery u) i

/-- Factorization through the compressed indices ⟺ pattern-consistency of
the outputs. -/
theorem exists_expand_eq_iff_consistent {X' Y' : Type*} [Fintype X']
    (u : Fin q → X') (v : Fin q → Y') :
    (∃ w, expandCompressedOutputs u w = v) ↔
      ∀ i j, u i = u j → v i = v j := by
  constructor
  · rintro ⟨w, rfl⟩ i j hij
    simp only [expandCompressedOutputs]
    congr 1
    unfold compressedQueryIndex
    exact congrArg _ (Subtype.ext hij)
  · intro hcons
    choose f hf using compressedQueryIndex_surjective u
    refine ⟨fun a => v (f a), ?_⟩
    funext i
    simp only [expandCompressedOutputs]
    have hu : u (f (compressedQueryIndex u i)) = u i := by
      rw [← compressedQuery_compressedQueryIndex u (f (compressedQueryIndex u i)),
        hf, compressedQuery_compressedQueryIndex]
    exact hcons _ _ hu

/-- **Pointwise law of a uniformly sampled function evaluated at an arbitrary
tuple**: the consistency indicator times `N^{-q′}` at the compressed arity.

    Pr_f[f∘u = v] = 𝟙[∀ i j, uᵢ = uⱼ → vᵢ = vⱼ] · N^{-|image u|}. -/
theorem uniformFunction_eval_apply {X' : Type*} {Y' : Type*}
    [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Nonempty Y']
    (u : Fin q → X') (v : Fin q → Y') :
    (Dist.fTransform (fun f : X' → Y' => fun i => f (u i))
      (Dist.uniform (X' → Y'))) v =
      if ∀ i j, u i = u j → v i = v j then
        ((Fintype.card Y' : ℝ) ^
          Fintype.card {x : X' // x ∈ queryImageSet u})⁻¹
      else 0 := by
  classical
  rw [fTransform_eval_repeated_eq_expand_compressedQuery u _,
    uniformFunction_eval_uniform (compressedQuery u) (compressedQuery_injective u)]
  by_cases hcons : ∀ i j, u i = u j → v i = v j
  · obtain ⟨w, rfl⟩ := (exists_expand_eq_iff_consistent u v).mpr hcons
    rw [Dist.fTransform_injective_apply _ _
      (expandCompressedOutputs_injective u) w, if_pos hcons, Dist.uniform_apply]
    simp [one_div]
  · rw [if_neg hcons, Dist.fTransform_apply_of_forall_ne _ _ _
      (fun w hw => hcons ((exists_expand_eq_iff_consistent u v).mp ⟨w, hw⟩))]

/-! ### Phase-1 reusable infrastructure (HCTR2 roadmap; generic)

Three lemmas shared by the PRP/PRF switching family and the HCTR2 proof:
the perm-consistency mass engine, its `N^{-k}` lower bound, and the
`Adv`-triangle inequality. -/

/-- `N^{-k} ≤ ∏_{i<k} 1/(N−i) = 1/(N)_k` in `NNReal`: a uniform permutation
consistent with `k` distinct constraints is at least as likely as `k`
independent uniform coincidences. -/
theorem pow_inv_le_descFactorial_inv {N k : ℕ} (h_le : k ≤ N) :
    ((N : NNReal) ^ k)⁻¹ ≤ ((N.descFactorial k : NNReal))⁻¹ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · omega
  · have hdposR : (0 : NNReal) < N.descFactorial k := by
      exact_mod_cast Nat.descFactorial_pos.mpr h_le
    have hle : (N.descFactorial k : NNReal) ≤ (N : NNReal) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow N k
    gcongr

/-- **The perm-consistency mass engine** (paper §3.4.1 good direction / §3.5).
For a uniformly sampled `π : Equiv.Perm X` and an injective assignment of
`k` inputs to `k` distinct outputs, the mass of "π realizes it" is
`(|X|−k)!/|X|! = 1/(|X|)_k`, hence `≥ |X|^{−k}`. -/
theorem uniform_perm_consistent_mass_ge {X : Type u} [Fintype X] [DecidableEq X]
    {k : ℕ} (xs : Fin k → X) (hx : Function.Injective xs)
    (ys : Fin k → X) (hy : Function.Injective ys) (h_le : k ≤ Fintype.card X) :
    ((Fintype.card X : ℝ) ^ k)⁻¹ ≤
      (Dist.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (xs i) = ys i) := by
  classical
  -- mass = (#consistent perms)/|Perm X| = (N−k)!/N! = 1/(N)_k
  have hmass : (Dist.uniform (Equiv.Perm X)).mass
      (fun π => ∀ i, π (xs i) = ys i) =
      ((Fintype.card X - k).factorial : ℝ) /
        ((Fintype.card X).factorial : ℝ) := by
    rw [Dist.uniform_mass_eq_card_filter, card_perm_fiber xs hx ys hy h_le,
      show (Fintype.card (Equiv.Perm X) : ℝ)
          = ((Fintype.card X).factorial : ℝ) from by
        exact_mod_cast Fintype.card_perm]
  rw [hmass]
  have h := le_trans (pow_inv_le_descFactorial_inv (N := Fintype.card X) h_le)
    (le_of_eq (RandomSystems.CR18.Counting.factorial_ratio_eq_descFactorial_inv
      h_le).symm)
  exact_mod_cast h

/-- **Perm-consistency for a partial-injection constraint family** (Phase 2
engine, repeats allowed).  If `(a i, b i)` is a partial injection (same input
⟹ same output, and injective), the mass of permutations realizing every
constraint is `≥ N^{−|image a|}`. -/
theorem uniform_perm_consistent_mass_ge_finset {X ι : Type u}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (a b : ι → X)
    (h_pf : ∀ i j, a i = a j → b i = b j)
    (h_inj : ∀ i j, b i = b j → a i = a j)
    (h_le : (Finset.univ.image a).card ≤ Fintype.card X) :
    ((Fintype.card X : ℝ) ^ (Finset.univ.image a).card)⁻¹ ≤
      (Dist.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (a i) = b i) := by
  classical
  set S := Finset.univ.image a with hS
  set k := Fintype.card ↥S with hk
  set e := Fintype.equivFin S with he
  let xs : Fin k → X := fun j => (e.symm j).1
  have hxs_inj : Function.Injective xs :=
    fun p q h => e.symm.injective (Subtype.ext h)
  have hmem : ∀ j : Fin k, (e.symm j).1 ∈ S := fun j => (e.symm j).2
  choose pre hpre using fun j : Fin k => Finset.mem_image.mp (hmem j)
  let ys : Fin k → X := fun j => b (pre j)
  have hys_inj : Function.Injective ys := by
    intro p q h
    have hab := h_inj _ _ h
    have : xs p = xs q := by
      simp only [xs]; rw [← (hpre p).2, ← (hpre q).2, hab]
    exact hxs_inj this
  have hiff : ∀ π : Equiv.Perm X,
      (∀ i, π (a i) = b i) ↔ (∀ j, π (xs j) = ys j) := by
    intro π
    constructor
    · intro h j; simp only [xs, ys]; rw [← (hpre j).2]; exact h (pre j)
    · intro h i
      have hai : a i ∈ S := Finset.mem_image_of_mem a (Finset.mem_univ i)
      have hx : xs (e ⟨a i, hai⟩) = a i := by simp [xs]
      have hh := h (e ⟨a i, hai⟩)
      rw [hx] at hh
      rw [hh]; simp only [ys]; apply h_pf; rw [(hpre _).2]; exact hx
  rw [Dist.mass_congr _ hiff, show (Finset.univ.image a).card = k from
    (Fintype.card_coe S).symm]
  exact uniform_perm_consistent_mass_ge xs hxs_inj ys hys_inj
    (by rw [hk, ← Fintype.card_coe S] at *; exact hk ▸ (Fintype.card_coe S ▸ h_le))

/-- Exact perm-consistency mass on distinct constraints: `(N−k)!/N!`. -/
theorem uniform_perm_consistent_mass_eq {X : Type u} [Fintype X] [DecidableEq X]
    {k : ℕ} (xs : Fin k → X) (hx : Function.Injective xs)
    (ys : Fin k → X) (hy : Function.Injective ys) (h_le : k ≤ Fintype.card X) :
    (Dist.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (xs i) = ys i) =
      ((Fintype.card X - k).factorial : ℝ) / ((Fintype.card X).factorial) := by
  rw [Dist.uniform_mass_eq_card_filter, card_perm_fiber xs hx ys hy h_le,
    show (Fintype.card (Equiv.Perm X) : ℝ)
        = ((Fintype.card X).factorial : ℝ) from by exact_mod_cast Fintype.card_perm]

/-- Exact perm-consistency mass, partial-injection (finset) form. -/
theorem uniform_perm_consistent_mass_eq_finset {X ι : Type u}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (a b : ι → X)
    (h_pf : ∀ i j, a i = a j → b i = b j)
    (h_inj : ∀ i j, b i = b j → a i = a j)
    (h_le : (Finset.univ.image a).card ≤ Fintype.card X) :
    (Dist.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (a i) = b i) =
      ((Fintype.card X - (Finset.univ.image a).card).factorial : ℝ) /
        ((Fintype.card X).factorial) := by
  classical
  set S := Finset.univ.image a with hS
  set k := Fintype.card ↥S with hk
  set e := Fintype.equivFin S with he
  let xs : Fin k → X := fun j => (e.symm j).1
  have hxs_inj : Function.Injective xs :=
    fun p q h => e.symm.injective (Subtype.ext h)
  have hmem : ∀ j : Fin k, (e.symm j).1 ∈ S := fun j => (e.symm j).2
  choose pre hpre using fun j : Fin k => Finset.mem_image.mp (hmem j)
  let ys : Fin k → X := fun j => b (pre j)
  have hys_inj : Function.Injective ys := by
    intro p q h
    have hab := h_inj _ _ h
    have : xs p = xs q := by
      simp only [xs]; rw [← (hpre p).2, ← (hpre q).2, hab]
    exact hxs_inj this
  have hiff : ∀ π : Equiv.Perm X,
      (∀ i, π (a i) = b i) ↔ (∀ j, π (xs j) = ys j) := by
    intro π
    constructor
    · intro h j; simp only [xs, ys]; rw [← (hpre j).2]; exact h (pre j)
    · intro h i
      have hai : a i ∈ S := Finset.mem_image_of_mem a (Finset.mem_univ i)
      have hx : xs (e ⟨a i, hai⟩) = a i := by simp [xs]
      have hh := h (e ⟨a i, hai⟩)
      rw [hx] at hh
      rw [hh]; simp only [ys]; apply h_pf; rw [(hpre _).2]; exact hx
  rw [Dist.mass_congr _ hiff,
    show (Finset.univ.image a).card = k from (Fintype.card_coe S).symm]
  exact uniform_perm_consistent_mass_eq xs hxs_inj ys hys_inj
    (by rw [hk, ← Fintype.card_coe S] at *; exact hk ▸ (Fintype.card_coe S ▸ h_le))

/-- **Factoring cardinality bound** (Phase 2 counting): if `φ` factors through
`ψ` (`ψ i = ψ j → φ i = φ j`), then `|image φ| ≤ |image ψ|`. -/
theorem card_image_le_of_factors {ι A B : Type*}
    [Fintype ι] [DecidableEq A] [DecidableEq B] (φ : ι → A) (ψ : ι → B)
    (h : ∀ i j, ψ i = ψ j → φ i = φ j) :
    (Finset.univ.image φ).card ≤ (Finset.univ.image ψ).card := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.univ_eq_empty]
  · have hsub : Finset.univ.image φ ⊆ (Finset.univ.image ψ).image
        (fun b => φ (if hb : ∃ i, ψ i = b then hb.choose else Classical.arbitrary ι)) := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      refine Finset.mem_image.mpr
        ⟨ψ i, Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩
      have hex : ∃ k, ψ k = ψ i := ⟨i, rfl⟩
      simp only [hex, dif_pos]
      exact h hex.choose i hex.choose_spec
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **`Adv`-triangle** for total systems (Phase 1.3; used to compose the
HCTR2 main lemma with PRP-RND):
`Adv[q](S,U) ≤ Adv[q](S,T) + Adv[q](T,U)`. -/
theorem adaptiveTranscriptAdvantage_triangle [FiniteTranscriptSpace X Y q]
    (S T U : ProbPDS X Y) :
    Adv[q](S, U) ≤ Adv[q](S, T) + Adv[q](T, U) := by
  unfold adaptiveTranscriptAdvantage
  refine sSup_image_univ_le_of_forall _ ?_ ?_
  · have := adaptiveTranscriptAdvantage_nonneg (q := q) S T
    have := adaptiveTranscriptAdvantage_nonneg (q := q) T U
    unfold adaptiveTranscriptAdvantage at *
    positivity
  · intro E
    calc (statDist (tr[q](S, E.1)) (tr[q](U, E.1)) : ℝ)
        ≤ (statDist (tr[q](S, E.1)) (tr[q](T, E.1)) : ℝ) +
          (statDist (tr[q](T, E.1)) (tr[q](U, E.1)) : ℝ) := by
          exact_mod_cast statDist_triangle _ _ _
      _ ≤ Adv[q](S, T) + Adv[q](T, U) :=
          add_le_add
            (deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
              S T E)
            (deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
              T U E)

/-- **Tweak-product factorization** (Phase 2a; general, reused by PRP-RND and
HCTR2).  For a uniform function space `T → A`, the mass of a per-index
constraint `P i` evaluated at coordinate `idx i` factors over coordinates:

    Pr_{f}[∀ i, P i (f (idx i))] = ∏_τ Pr_{a}[∀ i, idx i = τ → P i a].

(Coordinates `τ` not among the `idx i` contribute mass `1`.) -/
theorem uniform_pi_eval_mass {T A : Type*}
    [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A] [Nonempty A]
    {k : ℕ} (idx : Fin k → T) (P : Fin k → A → Prop) [∀ i, DecidablePred (P i)] :
    (Dist.uniform (T → A)).mass (fun f => ∀ i, P i (f (idx i)))
      = ∏ τ : T, (Dist.uniform A).mass (fun a => ∀ i, idx i = τ → P i a) := by
  classical
  simp_rw [Dist.uniform_mass_eq_card_filter]
  rw [show (Finset.univ.filter (fun f : T → A => ∀ i, P i (f (idx i))))
      = Fintype.piFinset
          (fun τ => Finset.univ.filter (fun a => ∀ i, idx i = τ → P i a)) from by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    exact ⟨fun h τ i hi => hi ▸ h i, fun h i => h (idx i) i rfl⟩,
    Fintype.card_piFinset,
    show (Fintype.card (T → A) : ℝ) = ∏ _τ : T, (Fintype.card A : ℝ) from by
      rw [Fintype.card_fun]; push_cast; rw [Finset.prod_const, Finset.card_univ],
    Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **Dependent tweak-product factorization** (faithful length migration): the
per-index codomain `A i` may vary (e.g. a permutation of `Msgℓ` per length),
so the constraint is transported via `h ▸ a`.  Generalizes
`uniform_pi_eval_mass` to a length-indexed family. -/
theorem uniform_dpi_eval_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)]
    {k : ℕ} (idx : Fin k → ι) (P : ∀ (i : Fin k), A (idx i) → Prop)
    [∀ i, DecidablePred (P i)] :
    (Dist.uniform (∀ i, A i)).mass (fun f => ∀ i, P i (f (idx i))) =
      ∏ τ : ι, (Dist.uniform (A τ)).mass
        (fun a => ∀ i (h : idx i = τ), P i (h ▸ a)) := by
  classical
  simp_rw [Dist.uniform_mass_eq_card_filter]
  rw [show (Finset.univ.filter (fun f : ∀ i, A i => ∀ i, P i (f (idx i))))
      = Fintype.piFinset (fun τ => Finset.univ.filter
          (fun a : A τ => ∀ i (h : idx i = τ), P i (h ▸ a))) from by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    exact ⟨fun hf τ a h => h ▸ hf _, fun hf i => hf (idx i) i rfl⟩,
    Fintype.card_piFinset,
    show (Fintype.card (∀ i, A i) : ℝ)
        = ∏ _τ : ι, (Fintype.card (A _τ) : ℝ) from by
      rw [Fintype.card_pi]; push_cast; rfl,
    Nat.cast_prod, ← Finset.prod_div_distrib]

/-! ### The switching lemma (adaptive, both directions) -/

section Switching

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The birthday defect `q(q−1)/(2N)` (as in `Counting.switching_ratio_le`). -/
noncomputable def bday (q N : ℕ) : NNReal :=
  ((q * (q - 1) : ℕ) : NNReal) / ((2 * N : ℕ) : NNReal)

theorem bday_mono {q' q N : ℕ} (h : q' ≤ q) : bday q' N ≤ bday q N := by
  unfold bday
  gcongr

/-- **Pointwise counting core**: at an injective query tuple, the uniform
permutation's output-tuple mass is within `1 − bday` of the uniform
function's,

    (1 − q'(q'−1)/2N) · Pr_σ[σ∘xs = v] ≤ Pr_f[f∘xs = v].

`v` non-injective: the permutation mass vanishes.  `v` injective: the masses
are `(N−q')!/N!` (`card_perm_fiber`) and `1/N^{q'}`
(`uniformFunction_eval_uniform`), and `Counting.switching_ratio_le` closes. -/
theorem perm_eval_ratio {q' : ℕ} (xs : Fin q' → X)
    (h_inj : Function.Injective xs)
    (h_eps : bday q' (Fintype.card X) ≤ 1) (v : Fin q' → X) :
    (1 - bday q' (Fintype.card X)) *
        (Dist.fTransform (fun σ : Equiv.Perm X => fun i => σ.toFun (xs i))
          (Dist.uniform (Equiv.Perm X))) v ≤
      (Dist.fTransform (fun f : X → X => fun i => f (xs i))
          (Dist.uniform (X → X))) v := by
  classical
  have hq'N : q' ≤ Fintype.card X := by
    simpa using Fintype.card_le_of_injective xs h_inj
  by_cases hv : Function.Injective v
  · -- both masses are explicit counting facts
    rw [uniformFunction_eval_uniform xs h_inj, Dist.fTransform_uniform_apply,
      Dist.uniform_apply]
    have hperm : (Finset.univ.filter
        (fun σ : Equiv.Perm X => (fun i => σ.toFun (xs i)) = v)).card =
        (Fintype.card X - q').factorial := by
      rw [show (Finset.univ.filter
          (fun σ : Equiv.Perm X => (fun i => σ.toFun (xs i)) = v)) =
          (Finset.univ.filter (fun σ : Equiv.Perm X => ∀ i, σ (xs i) = v i)) from
        Finset.filter_congr fun σ _ => by simp [funext_iff]]
      exact card_perm_fiber xs h_inj v hv hq'N
    rw [hperm]
    have hcards : (Fintype.card (Equiv.Perm X) : ℝ) =
        ((Fintype.card X).factorial : ℝ) := by
      exact_mod_cast Fintype.card_perm
    have hcardf : (Fintype.card (Fin q' → X) : ℝ) =
        ((Fintype.card X : ℝ)) ^ q' := by
      simp
    rw [hcards, hcardf,
      show (1 : ℝ) - (bday q' (Fintype.card X) : ℝ)
          = (((1 - bday q' (Fintype.card X) : NNReal)) : ℝ) from by
        rw [NNReal.coe_sub h_eps, NNReal.coe_one]]
    unfold bday at h_eps ⊢
    exact_mod_cast switching_ratio_le hq'N Fintype.card_pos h_eps
  · -- non-injective outputs are impossible for a permutation
    have hzero : (Dist.fTransform
        (fun σ : Equiv.Perm X => fun i => σ.toFun (xs i))
        (Dist.uniform (Equiv.Perm X))) v = 0 := by
      rw [Dist.fTransform_uniform_apply]
      rw [Finset.filter_eq_empty_iff.mpr fun σ _ => ?_, Finset.card_empty]
      · simp
      · intro hσv
        exact hv (hσv ▸ (σ.injective.comp h_inj))
    rw [hzero, mul_zero]
    exact (Dist.uniform_nonNeg.fTransform _) v

variable {q : ℕ} [FiniteTranscriptSpace X X q]

/-- **The fixed-query ratio behind the switching lemma**: at every query
tuple `xs` (repeats allowed) and every transcript,

    (1 − q(q−1)/2N) · tr(urp, xs)(t) ≤ tr(urf, xs)(t).

Both laws are pushforwards of sampled evaluations; compression reduces to the
injective compressed tuple, where `perm_eval_ratio` counts. -/
theorem urp_urf_fixedQuery_ratio
    (h_eps : bday q (Fintype.card X) ≤ 1) (xs : Fin q → X)
    (t : TranscriptPrefix X X q) :
    (1 - bday q (Fintype.card X)) * (tr(urp (X := X), xs)) t ≤
      (tr(urf (X := X) (Y := X), xs)) t := by
  classical
  -- both fixed-query laws are pushforwards of sampled evaluations
  rw [urp_eq_functionEvaluator, fixedQueryTranscriptDist_functionEvaluator,
    fixedQueryTranscriptDist_urf]
  unfold fixedInputLiftDist
  refine fTransform_ratio_of_pointwise _ _ _ _ (fun v => ?_) t
  -- compress repeated queries to the injective compressed tuple
  rw [PFunPDS.uniformP_val,
    fTransform_sampled_eval_repeated_eq_expand_compressedQuery xs _ _,
    fTransform_sampled_eval_repeated_eq_expand_compressedQuery xs _ _]
  refine fTransform_ratio_of_pointwise _ _ _ _ (fun w => ?_) v
  -- the counting core at the compressed tuple, with the birthday defect
  -- monotone in the (smaller) compressed arity
  have hq' := compressedQuery_card_le xs
  calc (1 - bday q (Fintype.card X)) *
        (Dist.fTransform _ (Dist.uniform (Equiv.Perm X))) w
      ≤ (1 - bday (Fintype.card {x : X // x ∈ queryImageSet xs})
            (Fintype.card X)) *
        (Dist.fTransform _ (Dist.uniform (Equiv.Perm X))) w := by
        gcongr
        · exact (Dist.uniform_nonNeg.fTransform _) w
        · exact_mod_cast bday_mono hq'
    _ ≤ _ := perm_eval_ratio (compressedQuery xs)
        (compressedQuery_injective xs)
        (le_trans (bday_mono hq') h_eps) w

/-- **The PRF/PRP switching lemma** (adaptive, via the H-technique's perfect
form — **no bad event**):

    Adv[q](urf, urp) ≤ q(q−1)/(2N).

With `urp` as the *ideal* system, collision transcripts have zero ideal mass,
so the pointwise fixed-query ratio holds everywhere and
`adv_le_of_fixedQuery_ratio` applies directly. -/
theorem urf_urp_switching :
    Adv[q](urf (X := X) (Y := X), urp (X := X)) ≤
      (bday q (Fintype.card X) : ℝ) := by
  by_cases h_eps : bday q (Fintype.card X) ≤ 1
  · -- the H-technique route, perfect form
    exact adv_le_of_fixedQuery_ratio _ _ _
      (urf_KStepTotal q) (urp_KStepTotal q)
      (urp_urf_fixedQuery_ratio h_eps)
  · -- bday > 1: the advantage of total systems is at most 1
    calc Adv[q](urf (X := X) (Y := X), urp (X := X))
        ≤ 1 := adaptiveTranscriptAdvantage_le_one _ _
          (urf_KStepTotal q) (urp_KStepTotal q)
      _ ≤ (bday q (Fintype.card X) : ℝ) := by
          exact_mod_cast (not_le.mp h_eps).le


/-! #### The PRP/PRF direction, worked out directly with bad transcripts

The H-technique route with `urf` as *ideal*, where the asymmetry bites:
collision transcripts have positive ideal mass, so a bad event is genuinely
needed.  The pieces:

* `Collision` — an output collision at distinct inputs;
* `σ(urp)` **vanishes** on collisions (permutations are injective);
* the good-transcript ratio `tr(urf, xs)(t) ≤ tr(urp, xs)(t)` with **ε = 0**
  — on collision-free transcripts the URP mass `1/(N)_{q′}` dominates the
  URF mass `1/N^{q′}` (`Nat.descFactorial_le_pow`);
* the **adaptive birthday bound** `Pr[Collision ∣ tr(urf, E)] ≤ q(q−1)/2N`
  for *every* environment, with no freshness recursion: since
  `Pr[Collision ∣ tr(urp, E)] = 0` and the pointwise switching ratio sums
  over good transcripts (`mass_ratio_of_pointwise`),
  `Pr_urf[good] ≥ (1−ε)·Pr_urp[good] = 1−ε`. -/

/-- An output collision at distinct inputs. -/
def Collision {q : ℕ} (t : TranscriptPrefix X X q) : Prop :=
  ∃ i j : Fin q, t.1.get i ≠ t.1.get j ∧ t.2.get i = t.2.get j

/-- Permutations never collide: the URP system factor vanishes on collision
transcripts. -/
theorem sysFactor_urp_eq_zero_of_collision {q : ℕ}
    (t : TranscriptPrefix X X q) (hc : Collision t) :
    σ(urp (X := X)) t = 0 := by
  classical
  obtain ⟨i, j, hxx, hyy⟩ := hc
  show (PFunPDS.URP X).mass _ = 0
  unfold PFunPDS.URP PFunPDS.ofPermDist
  rw [Dist.mass_fTransform]
  have himp : ∀ σ : Equiv.Perm X,
      ¬ transcriptSystemEvent idSysRV t.1 t.2
        (PFunDDS.functionEvaluator σ.toFun) := by
    intro σ hev
    have hev' : transcriptSystemEvent
        (functionEvaluatorRV (fun σ : Equiv.Perm X => σ.toFun)) t.1 t.2 σ := hev
    have h' := (transcriptSystemEvent_functionEvaluatorRV_iff
      (fun σ : Equiv.Perm X => σ.toFun) t.1 t.2 σ).mp hev'
    exact hxx (σ.injective (show σ.toFun (t.1.get i) = σ.toFun (t.1.get j) by
      rw [h' i, h' j, hyy]))
  refine Eq.trans (Dist.mass_congr _ (fun σ => ?_))
    (mass_eq_zero_of_forall _ (fun _ (h : False) => h.elim))
  simp only [iff_false]
  exact himp σ

variable {q : ℕ} [FiniteTranscriptSpace X X q]

/-- Collision transcripts have zero URP transcript mass, under every
environment. -/
theorem probBad_urp_collision_eq_zero (E : QQueryEnvironment X X q) :
    Pr[Collision ∣ tr[q](urp (X := X), E.1)] = 0 := by
  refine mass_eq_zero_of_forall _ (fun t hc => ?_)
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    sysFactor_urp_eq_zero_of_collision t hc, zero_mul]

/-- **The adaptive birthday bound**, from the switching ratio — no freshness
recursion:  Pr_urf[good] ≥ (1−ε)·Pr_urp[good] = 1−ε, so
Pr_urf[Collision] ≤ ε. -/
theorem probBad_urf_collision_le
    (h_eps : bday q (Fintype.card X) ≤ 1) (E : QQueryEnvironment X X q) :
    Pr[Collision ∣ tr[q](urf (X := X) (Y := X), E.1)] ≤
      bday q (Fintype.card X) := by
  -- pointwise per-environment switching ratio (Layer B transfer)
  have hpt : ∀ t, (1 - bday q (Fintype.card X)) *
      tr[q](urp (X := X), E.1) t ≤
      tr[q](urf (X := X) (Y := X), E.1) t := fun t =>
    deterministicTranscriptDist_ratio_of_fixedQuery_ratio_at _ _ E t _
      (fun xs => urp_urf_fixedQuery_ratio h_eps xs t)
  -- sum it over the good transcripts
  have hgood := mass_ratio_of_pointwise _ _ _ hpt (fun t => ¬ Collision t)
  -- the URP good mass is everything
  have hurp := probBad_add_mass_not (tr[q](urp (X := X), E.1)) Collision
  rw [probBad_urp_collision_eq_zero E, zero_add,
    deterministicTranscriptDist_weight_eq_one _ E (urp_KStepTotal q)] at hurp
  rw [hurp, mul_one] at hgood
  -- so the URF bad mass is at most ε
  have hurf := probBad_add_mass_not
    (tr[q](urf (X := X) (Y := X), E.1)) Collision
  rw [deterministicTranscriptDist_weight_eq_one _ E (urf_KStepTotal q)] at hurf
  rw [eq_tsub_of_add_eq hurf]
  calc 1 - (tr[q](urf (X := X) (Y := X), E.1)).mass (fun t => ¬ Collision t)
      ≤ 1 - (1 - bday q (Fintype.card X)) := tsub_le_tsub_left hgood 1
    _ = bday q (Fintype.card X) := tsub_tsub_cancel_of_le h_eps

/-- **Pointwise counting core, good direction**: at injective queries and
injective outputs, the URF mass `1/N^{q′}` is at most the URP mass
`1/(N)_{q′}`. -/
theorem fun_eval_le_perm_eval {q' : ℕ} (xs' : Fin q' → X)
    (hxs : Function.Injective xs') (w : Fin q' → X)
    (hw : Function.Injective w) :
    (Dist.fTransform (fun f : X → X => fun i => f (xs' i))
      (Dist.uniform (X → X))) w ≤
      (Dist.fTransform (fun σ : Equiv.Perm X => fun i => σ.toFun (xs' i))
        (Dist.uniform (Equiv.Perm X))) w := by
  classical
  have hq'N : q' ≤ Fintype.card X := by
    simpa using Fintype.card_le_of_injective xs' hxs
  rw [uniformFunction_eval_uniform xs' hxs, Dist.uniform_apply,
    Dist.fTransform_uniform_apply]
  have hperm : (Finset.univ.filter
      (fun σ : Equiv.Perm X => (fun i => σ.toFun (xs' i)) = w)).card =
      (Fintype.card X - q').factorial := by
    rw [show (Finset.univ.filter
        (fun σ : Equiv.Perm X => (fun i => σ.toFun (xs' i)) = w)) =
        (Finset.univ.filter (fun σ : Equiv.Perm X => ∀ i, σ (xs' i) = w i)) from
      Finset.filter_congr fun σ _ => by simp [funext_iff]]
    exact card_perm_fiber xs' hxs w hw hq'N
  rw [hperm]
  have hcards : (Fintype.card (Equiv.Perm X) : ℝ) =
      ((Fintype.card X).factorial : ℝ) := by
    exact_mod_cast Fintype.card_perm
  have hcardf : (Fintype.card (Fin q' → X) : ℝ) =
      ((Fintype.card X : ℝ)) ^ q' := by simp
  rw [hcards, hcardf,
    show ((Fintype.card X - q').factorial : ℝ) / ((Fintype.card X).factorial : ℝ)
        = (((Fintype.card X).descFactorial q' : ℝ))⁻¹ from by
      have h := congrArg NNReal.toReal
        (factorial_ratio_eq_descFactorial_inv (N := Fintype.card X) hq'N)
      rw [NNReal.coe_div, NNReal.coe_inv, NNReal.coe_natCast,
        NNReal.coe_natCast, NNReal.coe_natCast] at h
      exact h,
    one_div]
  gcongr
  · exact_mod_cast Nat.descFactorial_pos.mpr hq'N
  · exact_mod_cast Nat.descFactorial_le_pow (Fintype.card X) q'

/-- Goodness makes compressed outputs injective: if the expanded outputs are
collision-free at distinct inputs, the compressed output tuple is injective. -/
theorem injective_of_expand_of_good (xs : Fin q → X) (yv : List.Vector X q)
    (w : Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) → X)
    (hw : expandCompressedOutputs xs w = functionOfVector yv)
    (h_good : ¬ Collision ((vectorOfFunction xs : List.Vector X q), yv)) :
    Function.Injective w := by
  intro a b hab
  by_contra hne
  obtain ⟨i, rfl⟩ := compressedQueryIndex_surjective xs a
  obtain ⟨j, rfl⟩ := compressedQueryIndex_surjective xs b
  refine h_good ⟨i, j, fun hxeq => hne ?_, ?_⟩
  · -- equal inputs force equal compressed indices
    unfold compressedQueryIndex
    exact congrArg _ (Subtype.ext (by
      simpa [vectorOfFunction_eq_ofFn] using hxeq))
  · -- equal compressed outputs copy back to the transcript outputs
    have hi := congr_fun hw i
    have hj := congr_fun hw j
    simp only [expandCompressedOutputs] at hi hj
    rw [show yv.get i = functionOfVector yv i from rfl,
      show yv.get j = functionOfVector yv j from rfl, ← hi, ← hj, hab]

/-- **The good-transcript ratio, ε = 0**: on collision-free transcripts the
URF fixed-query mass is dominated by the URP one. -/
theorem urf_le_urp_fixedQuery_of_good (xs : Fin q → X)
    (t : TranscriptPrefix X X q) (h_good : ¬ Collision t) :
    (tr(urf (X := X) (Y := X), xs)) t ≤ (tr(urp (X := X), xs)) t := by
  classical
  obtain ⟨xv, yv⟩ := t
  rw [urp_eq_functionEvaluator, fixedQueryTranscriptDist_functionEvaluator,
    fixedQueryTranscriptDist_urf, PFunPDS.uniformP_val]
  by_cases hxv : xv = vectorOfFunction xs
  · subst hxv
    -- reduce to the sampled output-vector laws at v := outputs
    rw [show ((vectorOfFunction xs : List.Vector X q), yv) =
        fixedInputTranscriptPrefix xs (functionOfVector yv) from by
      unfold fixedInputTranscriptPrefix
      rw [vectorOfFunction_functionOfVector]]
    rw [fixedInputLiftDist_apply_fixed, fixedInputLiftDist_apply_fixed]
    -- compress to the injective compressed tuple
    rw [fTransform_eval_repeated_eq_expand_compressedQuery xs _,
      fTransform_sampled_eval_repeated_eq_expand_compressedQuery xs _ _]
    by_cases hrange : ∃ w, expandCompressedOutputs xs w = functionOfVector yv
    · obtain ⟨w, hw⟩ := hrange
      rw [← hw,
        Dist.fTransform_injective_apply _ _
          (expandCompressedOutputs_injective xs) w,
        Dist.fTransform_injective_apply _ _
          (expandCompressedOutputs_injective xs) w]
      -- goodness makes the compressed outputs injective
      have hwinj : Function.Injective w :=
        injective_of_expand_of_good xs yv w hw h_good
      exact fun_eval_le_perm_eval (compressedQuery xs)
        (compressedQuery_injective xs) w hwinj
    · push Not at hrange
      rw [Dist.fTransform_apply_of_forall_ne _ _ _ hrange,
        Dist.fTransform_apply_of_forall_ne _ _ _ hrange]
  · rw [fixedInputLiftDist_apply_of_input_ne _ _ _ _ hxv,
      fixedInputLiftDist_apply_of_input_ne _ _ _ _ hxv]

/-- **The PRP/PRF direction, direct H-technique with bad transcripts**:

    Adv[q](urp, urf) ≤ Pr[Collision] + 0 ≤ q(q−1)/(2N)

via `adv_le_of_fixedQuery_ratio_of_good` at `Bad := Collision`, `ε = 0` —
the equality-strength good ratio plus the adaptive birthday bound.
(It also follows in one line from `adaptiveTranscriptAdvantage_symm` and
`urf_urp_switching`; the point here is the direct route.) -/
theorem urp_urf_switching :
    Adv[q](urp (X := X), urf (X := X) (Y := X)) ≤
      (bday q (Fintype.card X) : ℝ) := by
  by_cases h_eps : bday q (Fintype.card X) ≤ 1
  · have h := adv_le_of_fixedQuery_ratio_of_good
      (urp (X := X)) (urf (X := X) (Y := X)) Collision 0
      (bday q (Fintype.card X))
      (urp_KStepTotal q) (urf_KStepTotal q)
      (fun xs t h_good => by
        simpa using urf_le_urp_fixedQuery_of_good xs t h_good)
      (fun E => probBad_urf_collision_le h_eps E)
    simpa using h
  · calc Adv[q](urp (X := X), urf (X := X) (Y := X))
        ≤ 1 := adaptiveTranscriptAdvantage_le_one _ _
          (urp_KStepTotal q) (urf_KStepTotal q)
      _ ≤ (bday q (Fintype.card X) : ℝ) := by
          exact_mod_cast (not_le.mp h_eps).le

/-! ### SecurityDefs corollaries — the switching lemma on the frozen
endpoint surface -/

/-- The URP is a good PRF:  advPRF(urp) ≤ q(q−1)/2N. -/
theorem advPRF_urp_le :
    RandomSystems.HTechnique.SecurityDefs.advPRF (q := q) (urp (X := X)) ≤
      (bday q (Fintype.card X) : ℝ) := by
  show Adv[q](urp (X := X), urf (X := X) (Y := X)) ≤ _
  exact urp_urf_switching

/-- The URF is a good PRP:  advPRP(urf) ≤ q(q−1)/2N. -/
theorem advPRP_urf_le :
    RandomSystems.HTechnique.SecurityDefs.advPRP (q := q)
      (urf (X := X) (Y := X)) ≤ (bday q (Fintype.card X) : ℝ) := by
  show Adv[q](urf (X := X) (Y := X), urp (X := X)) ≤ _
  exact urf_urp_switching

end Switching


/-! ### Hash-then-PRF, and composition with the switching bound -/

/-- The fixed-query environment is `q`-query-total on the `DDE` carrier. -/
theorem fixedQueryDDE_KQueryTotal {X Y : Type*} {q : ℕ} (xs : Fin q → X) :
    PFunPDE.DDEKQueryTotal (fixedQueryDDE (Y := Y) xs) q := by
  intro ys hlen
  exact ⟨xs ⟨ys.length, hlen⟩, by
    simp [fixedQueryDDE, hlen]⟩

section WithFiniteTranscriptsG5

variable {q : ℕ} [FiniteTranscriptSpace X Y q]

/-- Fixed-query transcripts of total systems are probability distributions. -/
theorem fixedQueryTranscriptDist_weight_eq_one
    (S : ProbPDS X Y) (hS : S.KStepTotal q) (xs : Fin q → X) :
    (tr(S, xs)).weight = 1 :=
  deterministicTranscriptDist_weight_eq_one S
    ⟨fixedQueryDDE (Y := Y) xs, fixedQueryDDE_KQueryTotal xs⟩ hS

end WithFiniteTranscriptsG5

section SwitchingFixedQuery

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
variable {q : ℕ} [FiniteTranscriptSpace X X q]

/-- The **fixed-query** switching bound, from the same ratio via the
one-sided distribution-level H-lemma. -/
theorem urf_urp_fixedQuery_switching (xs : Fin q → X) :
    δ(tr(urf (X := X) (Y := X), xs), tr(urp (X := X), xs)) ≤
      bday q (Fintype.card X) := by
  by_cases h_eps : bday q (Fintype.card X) ≤ 1
  · refine oneSided_hTechnique _ _ _
      (HTechniqueDerivation.deterministicTranscriptDist_nonNeg (urp (X := X)) _)
      ?_ ?_ (urp_urf_fixedQuery_ratio h_eps xs)
    · rw [fixedQueryTranscriptDist_weight_eq_one _ (urf_KStepTotal q),
        fixedQueryTranscriptDist_weight_eq_one _ (urp_KStepTotal q)]
    · rw [fixedQueryTranscriptDist_weight_eq_one _ (urp_KStepTotal q)]
  · calc δ(tr(urf (X := X) (Y := X), xs), tr(urp (X := X), xs))
        ≤ (tr(urf (X := X) (Y := X), xs)).weight := statDist_le_weight
          (HTechniqueDerivation.deterministicTranscriptDist_nonNeg (urf (X := X) (Y := X)) _)
          (HTechniqueDerivation.deterministicTranscriptDist_nonNeg (urp (X := X)) _)
      _ = 1 := fixedQueryTranscriptDist_weight_eq_one _ (urf_KStepTotal q) xs
      _ ≤ bday q (Fintype.card X) := (not_le.mp h_eps).le

end SwitchingFixedQuery

section HashThenPRFApp

open RandomSystems.HTechnique.HashThenPRF

-- match the instance regime of `HashThenPRF.lean`, so its statements unify
attribute [local instance] Classical.propDecidable

variable {K Y H : Type*} {q : ℕ}
variable [Fintype K] [Nonempty K] [Fintype H]
variable [Fintype Y] [Nonempty Y]
variable [FiniteTranscriptSpace Y Y q]

/-- **Hash-then-PRF** (existing surface theorem, restated in derivation
notation): at distinct messages, the fixed-query transcripts of
`hash-then-PRF` and a URF are within `C(q,2)·ε` — the ε-universal hash's
collision slack. -/
theorem hashThenPRF_fixedQuery
    (Hf : EpsUniversalHash K Y H) (ms : Fin q → Y)
    (h_inj : Function.Injective ms) :
    δ(tr(hashThenPRFProbPDS (Y := Y) Hf, ms), tr(urf (X := Y) (Y := Y), ms)) ≤
      choose2 q * Hf.eps :=
  hashThenPRF_security Hf ms h_inj

/-- **Hash-then-PRF vs a URP**: compose the hash-then-PRF bound with the
fixed-query switching bound by the triangle inequality,

    δ(tr(HtP, ms), tr(urp, ms)) ≤ C(q,2)·ε + q(q−1)/(2N). -/
theorem hashThenPRF_vs_urp
    (Hf : EpsUniversalHash K Y H) (ms : Fin q → Y)
    (h_inj : Function.Injective ms) :
    δ(tr(hashThenPRFProbPDS (Y := Y) Hf, ms), tr(urp (X := Y), ms)) ≤
      choose2 q * Hf.eps + bday q (Fintype.card Y) := by
  calc δ(tr(hashThenPRFProbPDS (Y := Y) Hf, ms), tr(urp (X := Y), ms))
      ≤ δ(tr(hashThenPRFProbPDS (Y := Y) Hf, ms),
            tr(urf (X := Y) (Y := Y), ms)) +
        δ(tr(urf (X := Y) (Y := Y), ms), tr(urp (X := Y), ms)) :=
        statDist_triangle _ _ _
    _ ≤ choose2 q * Hf.eps + bday q (Fintype.card Y) :=
        add_le_add (hashThenPRF_fixedQuery Hf ms h_inj)
          (urf_urp_fixedQuery_switching ms)


/-! ### Adaptive hash-then-PRF

The existing surface theorem (`hashThenPRF_security`) is fixed-query at
injective tuples.  The adaptive statement below follows the switching-lemma
pattern: `Bad := Collision` (transcript-measurable), a good-transcript ratio
with defect `C(q,2)·ε` — obtained by marginalizing the paper's extended
`(y⃗, h)` masses over good keys — and the adaptive collision bound already
proved for the URF.  The extra birthday term (vs the extended fixed-query
bound's bare `C(q,2)·ε`) is the price of not extending the transcripts. -/

/-- Key-marginal lower bound for the real output law at an injective tuple:

    (1 − C(q,2)·ε) · 1/N^q ≤ realOutputDist(w)

— sum the extended law over good keys, where it agrees with the ideal
product law (`realExtDist_apply_uniform_of_good`). -/
theorem realOutputDist_apply_ge (Hf : EpsUniversalHash K Y H) {q' : ℕ}
    (ms : Fin q' → Y) (h_inj : Function.Injective ms) (w : Fin q' → Y) :
    (1 - choose2 q' * Hf.eps) * Dist.uniform (Fin q' → Y) w ≤
      realOutputDist Hf ms w := by
  classical
  -- fst-marginal:  realOutputDist(w) = Σ_h realExtDist(w, h)
  have hmarg : realOutputDist Hf ms w = ∑ h : K, realExtDist Hf ms (w, h) := by
    unfold realOutputDist realExtDist
    rw [show (fun p : K × (H → Y) =>
          fun i : Fin q' => hashThenPRF Hf p.1 p.2 (ms i)) =
        Prod.fst ∘ (fun p : K × (H → Y) =>
          ((fun i : Fin q' => hashThenPRF Hf p.1 p.2 (ms i)), p.1)) from rfl,
      ← Dist.fTransform_comp]
    rw [Dist.fTransform_apply_eq_sum, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [Finset.sum_ite_eq']
  -- the good-key mass dominates 1 − C(q,2)·ε
  have hgood : (1 - choose2 q' * Hf.eps) ≤
      (Dist.uniform K).mass (fun h => ¬ hashCollision Hf h ms) := by
    have hsplit := probBad_add_mass_not (Dist.uniform K)
      (fun h => hashCollision Hf h ms)
    rw [show (Dist.uniform K).weight = 1
      from Dist.uniform_isProbDist.weight_eq] at hsplit
    rw [show (Dist.uniform K).mass (fun h => ¬ hashCollision Hf h ms) =
        1 - Pr[(fun h => hashCollision Hf h ms) ∣ Dist.uniform K] from
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)]
    exact sub_le_sub_left (hashCollision_prob_le Hf ms h_inj) 1
  calc (1 - choose2 q' * Hf.eps) * Dist.uniform (Fin q' → Y) w
      ≤ (Dist.uniform K).mass (fun h => ¬ hashCollision Hf h ms) *
          Dist.uniform (Fin q' → Y) w := by
        gcongr
        exact Dist.uniform_nonNeg w
    _ = ∑ h : K, (if ¬ hashCollision Hf h ms then
          Dist.uniform K h * Dist.uniform (Fin q' → Y) w else 0) := by
        rw [Dist.mass_eq_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun h _ => ?_
        by_cases hg : hashCollision Hf h ms <;> simp [hg]
    _ ≤ ∑ h : K, realExtDist Hf ms (w, h) := by
        refine Finset.sum_le_sum fun h _ => ?_
        by_cases hg : hashCollision Hf h ms
        · simp only [hg, not_true_eq_false, if_false]
          exact ((Dist.uniform_nonNeg.prod
            Dist.uniform_nonNeg).fTransform _) (w, h)
        · rw [if_pos hg]
          exact le_of_eq
            (realExtDist_apply_uniform_of_good Hf ms w h hg).symm
    _ = realOutputDist Hf ms w := hmarg.symm

/-- **Good-transcript ratio for hash-then-PRF** (arbitrary query tuple):

    (1 − C(q,2)·ε) · tr(urf, xs)(t) ≤ tr(hashThenPRF, xs)(t)   for t ∉ Collision. -/
theorem urf_le_hashThenPRF_fixedQuery_of_good
    (Hf : EpsUniversalHash K Y H) (xs : Fin q → Y)
    (t : TranscriptPrefix Y Y q) (h_good : ¬ Collision t) :
    (1 - choose2 q * Hf.eps) * (tr(urf (X := Y) (Y := Y), xs)) t ≤
      (tr(hashThenPRFProbPDS (Y := Y) Hf, xs)) t := by
  classical
  obtain ⟨xv, yv⟩ := t
  unfold hashThenPRFProbPDS
  rw [fixedQueryTranscriptDist_functionEvaluator, fixedQueryTranscriptDist_urf,
    PFunPDS.uniformP_val]
  by_cases hxv : xv = vectorOfFunction xs
  · subst hxv
    rw [show ((vectorOfFunction xs : List.Vector Y q), yv) =
        fixedInputTranscriptPrefix xs (functionOfVector yv) from by
      unfold fixedInputTranscriptPrefix
      rw [vectorOfFunction_functionOfVector]]
    rw [fixedInputLiftDist_apply_fixed, fixedInputLiftDist_apply_fixed]
    rw [fTransform_eval_repeated_eq_expand_compressedQuery xs _,
      fTransform_sampled_eval_repeated_eq_expand_compressedQuery xs _ _]
    by_cases hrange : ∃ w, expandCompressedOutputs xs w = functionOfVector yv
    · obtain ⟨w, hw⟩ := hrange
      rw [← hw,
        Dist.fTransform_injective_apply _ _
          (expandCompressedOutputs_injective xs) w,
        Dist.fTransform_injective_apply _ _
          (expandCompressedOutputs_injective xs) w,
        uniformFunction_eval_uniform (compressedQuery xs)
          (compressedQuery_injective xs)]
      show (1 - choose2 q * Hf.eps) * Dist.uniform _ w ≤
        realOutputDist Hf (compressedQuery xs) w
      calc (1 - choose2 q * Hf.eps) * Dist.uniform _ w
          ≤ (1 - choose2 (Fintype.card {x : Y // x ∈ queryImageSet xs}) *
              Hf.eps) * Dist.uniform _ w := by
            gcongr
            · exact Dist.uniform_nonNeg w
            · exact_mod_cast Nat.choose_le_choose 2 (compressedQuery_card_le xs)
        _ ≤ realOutputDist Hf (compressedQuery xs) w :=
            realOutputDist_apply_ge Hf _ (compressedQuery_injective xs) w
    · push Not at hrange
      rw [Dist.fTransform_apply_of_forall_ne _ _ _ hrange,
        Dist.fTransform_apply_of_forall_ne _ _ _ hrange]
      simp
  · rw [fixedInputLiftDist_apply_of_input_ne _ _ _ _ hxv,
      fixedInputLiftDist_apply_of_input_ne _ _ _ _ hxv]
    simp

/-- **Adaptive hash-then-PRF**:

    Adv[q](hashThenPRF, urf) ≤ q(q−1)/(2N) + C(q,2)·ε

with `Bad := Collision`; the birthday term is the price of running the
H-technique on unextended transcripts. -/
theorem hashThenPRF_adaptive (Hf : EpsUniversalHash K Y H) :
    Adv[q](hashThenPRFProbPDS (Y := Y) Hf, urf (X := Y) (Y := Y)) ≤
      ((bday q (Fintype.card Y) + choose2 q * Hf.eps : NNReal) : ℝ) := by
  have hR : (hashThenPRFProbPDS (Y := Y) Hf).KStepTotal q := by
    unfold hashThenPRFProbPDS
    exact functionEvaluatorProb_KStepTotal _ _ q
  by_cases h_eps : bday q (Fintype.card Y) ≤ 1
  · exact adv_le_of_fixedQuery_ratio_of_good _ _ Collision
      (choose2 q * Hf.eps) (bday q (Fintype.card Y)) hR (urf_KStepTotal q)
      (fun xs t h_good => urf_le_hashThenPRF_fixedQuery_of_good Hf xs t h_good)
      (fun E => probBad_urf_collision_le h_eps E)
  · calc Adv[q](hashThenPRFProbPDS (Y := Y) Hf, urf (X := Y) (Y := Y))
        ≤ 1 := adaptiveTranscriptAdvantage_le_one _ _ hR (urf_KStepTotal q)
      _ ≤ (bday q (Fintype.card Y) : ℝ) := by
          exact_mod_cast (not_le.mp h_eps).le
      _ ≤ _ := by exact_mod_cast le_self_add

/-- The adaptive bound on the frozen endpoint surface. -/
theorem advPRF_hashThenPRF_le (Hf : EpsUniversalHash K Y H) :
    RandomSystems.HTechnique.SecurityDefs.advPRF (q := q)
      (hashThenPRFProbPDS (Y := Y) Hf) ≤
      ((bday q (Fintype.card Y) + choose2 q * Hf.eps : NNReal) : ℝ) := by
  show Adv[q](hashThenPRFProbPDS (Y := Y) Hf, urf (X := Y) (Y := Y)) ≤ _
  exact hashThenPRF_adaptive Hf


/-! ### The tight adaptive bound via Layer E″ (reveal the key)

Representatives: real `Ω = K × (H → Y)` sampling `(h, ρ)`; ideal
`Ω′ = K × (Y → Y)` sampling an independent **dummy key** alongside the URF.
`aug := fst` reveals the key.  `Bad (t,h)` = two distinct transcript inputs
colliding under `h`.  Equality-on-good is exact, so the endpoint yields the
bare `C(q,2)·ε` — no birthday term. -/

/-- Real representative: uniform key × uniform function (the sampler inside
`hashThenPRFProbPDS`). -/
noncomputable abbrev htpP : Dist.ProbDist (K × (H → Y)) :=
  Dist.prodProbDist
    (⟨Dist.uniform K, Dist.uniform_isProbDist⟩ : Dist.ProbDist K)
    (⟨Dist.uniform (H → Y), Dist.uniform_isProbDist⟩ : Dist.ProbDist (H → Y))

/-- Real sampled system. -/
noncomputable abbrev htpF (Hf : EpsUniversalHash K Y H) :
    PFunPDS.RV (K × (H → Y)) Y Y :=
  functionEvaluatorRV (fun p => hashThenPRF Hf p.1 p.2)

/-- Ideal representative: uniform **dummy key** × uniform function. -/
noncomputable abbrev idealP : Dist.ProbDist (K × (Y → Y)) :=
  Dist.prodProbDist
    (⟨Dist.uniform K, Dist.uniform_isProbDist⟩ : Dist.ProbDist K)
    (⟨Dist.uniform (Y → Y), Dist.uniform_isProbDist⟩ : Dist.ProbDist (Y → Y))

/-- Ideal sampled system (ignores the dummy key). -/
noncomputable abbrev idealF : PFunPDS.RV (K × (Y → Y)) Y Y :=
  functionEvaluatorRV (fun p => p.2)

/-- The reveal: the (dummy) key. -/
abbrev keyAug {Ω' : Type*} : (K × Ω') → TranscriptPrefix Y Y q → K :=
  fun p _ => p.1

/-- Bad extended transcripts: two distinct transcript inputs collide under
the revealed key. -/
def HashBad (Hf : EpsUniversalHash K Y H)
    (tz : TranscriptPrefix Y Y q × K) : Prop :=
  ∃ i j : Fin q, tz.1.1.get i ≠ tz.1.1.get j ∧
    Hf.hash tz.2 (tz.1.1.get i) = Hf.hash tz.2 (tz.1.1.get j)

/-- σ⁺ of the real representative, closed form. -/
theorem extSysFactorRep_htp_apply (Hf : EpsUniversalHash K Y H)
    (xv yv : List.Vector Y q) (h : K) :
    extSysFactorRep (htpP (K := K) (Y := Y) (H := H)) (htpF Hf) keyAug ((xv, yv), h) =
      Dist.uniform K h *
        (Dist.uniform (H → Y)).mass
          (fun ρ => ∀ i : Fin q, ρ (Hf.hash h (xv.get i)) = yv.get i) := by
  unfold extSysFactorRep
  rw [show (fun ω : K × (H → Y) =>
      transcriptSystemEvent (htpF Hf) ((xv, yv), h).1.1 ((xv, yv), h).1.2 ω ∧
        keyAug ω ((xv, yv), h).1 = ((xv, yv), h).2) =
    (fun ω : K × (H → Y) =>
      (∀ i : Fin q, ω.2 (Hf.hash ω.1 (xv.get i)) = yv.get i) ∧ ω.1 = h) from
    funext fun ω => propext (Iff.intro
      (fun ⟨hev, hk⟩ =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv ω).mp hev, hk⟩)
      (fun ⟨hev, hk⟩ =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv ω).mpr hev, hk⟩))]
  exact mass_prod_fst_eq _ _ h
    (fun (h' : K) (ρ : H → Y) => ∀ i : Fin q, ρ (Hf.hash h' (xv.get i)) = yv.get i)

/-- σ⁺ of the ideal representative, closed form. -/
theorem extSysFactorRep_ideal_apply (xv yv : List.Vector Y q) (h : K) :
    extSysFactorRep (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug ((xv, yv), h) =
      Dist.uniform K h *
        (Dist.uniform (Y → Y)).mass
          (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) := by
  unfold extSysFactorRep
  rw [show (fun ω : K × (Y → Y) =>
      transcriptSystemEvent (idealF (K := K)) ((xv, yv), h).1.1
          ((xv, yv), h).1.2 ω ∧
        keyAug ω ((xv, yv), h).1 = ((xv, yv), h).2) =
    (fun ω : K × (Y → Y) =>
      (∀ i : Fin q, ω.2 (xv.get i) = yv.get i) ∧ ω.1 = h) from
    funext fun ω => propext (Iff.intro
      (fun ⟨hev, hk⟩ =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv ω).mp hev, hk⟩)
      (fun ⟨hev, hk⟩ =>
        ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv ω).mpr hev, hk⟩))]
  exact mass_prod_fst_eq _ _ h
    (fun (_ : K) (g : Y → Y) => ∀ i : Fin q, g (xv.get i) = yv.get i)

/-- The ideal system factor: the dummy key sums out. -/
theorem sysFactor_ideal_eq (xv yv : List.Vector Y q) :
    transcriptSystemFactor (idealP (K := K) (Y := Y)) (idealF (K := K)) xv yv =
      (Dist.uniform (Y → Y)).mass
        (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) := by
  unfold transcriptSystemFactor
  rw [show (transcriptSystemEvent (idealF (K := K)) xv yv) =
    (fun ω : K × (Y → Y) => (∀ i : Fin q, ω.2 (xv.get i) = yv.get i)) from
    funext fun ω => propext
      (transcriptSystemEvent_functionEvaluatorRV_iff _ xv yv ω)]
  exact (mass_prod_snd_pred (Dist.uniform K) (Dist.uniform (Y → Y))
      (fun g : Y → Y => ∀ i : Fin q, g (xv.get i) = yv.get i)).trans
    (by rw [show (Dist.uniform K).weight = 1 from Dist.uniform_isProbDist.weight_eq,
      one_mul])

/-- **Equality on good extended transcripts.** -/
theorem htp_extFixedQuery_eq_on_good (Hf : EpsUniversalHash K Y H)
    (xs : Fin q → Y) (tz : TranscriptPrefix Y Y q × K)
    (h_good : ¬ HashBad Hf tz) :
    extFixedQueryTranscriptDistRep (htpP (K := K) (Y := Y) (H := H)) (htpF Hf) keyAug xs tz =
      extFixedQueryTranscriptDistRep (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug xs tz := by
  classical
  obtain ⟨⟨xv, yv⟩, h⟩ := tz
  unfold extFixedQueryTranscriptDistRep
  rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply]
  congr 1
  rw [extSysFactorRep_htp_apply, extSysFactorRep_ideal_apply]
  congr 1
  have hpat : ∀ i j : Fin q,
      Hf.hash h (xv.get i) = Hf.hash h (xv.get j) ↔ xv.get i = xv.get j := by
    intro i j
    constructor
    · intro hh
      by_contra hne
      exact h_good ⟨i, j, hne, hh⟩
    · intro hx
      rw [hx]
  have hcond : (∀ i j : Fin q, Hf.hash h (xv.get i) = Hf.hash h (xv.get j) →
      yv.get i = yv.get j) ↔
      (∀ i j : Fin q, xv.get i = xv.get j → yv.get i = yv.get j) := by
    constructor <;> intro hc i j hij
    · exact hc i j (by rw [hij])
    · exact hc i j ((hpat i j).mp hij)
  have hcard : Fintype.card
      {x : H // x ∈ queryImageSet (fun i => Hf.hash h (xv.get i))} =
      Fintype.card {x : Y // x ∈ queryImageSet (fun i => xv.get i)} := by
    rw [Fintype.card_coe, Fintype.card_coe]
    unfold queryImageSet
    rw [show ((Finset.univ : Finset (Fin q)).image
        fun i => Hf.hash h (xv.get i)) =
        ((Finset.univ : Finset (Fin q)).image fun i => xv.get i).image
          (Hf.hash h) from by rw [Finset.image_image]; rfl]
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact (hpat i j).mp hab
  calc (Dist.uniform (H → Y)).mass
        (fun ρ => ∀ i : Fin q, ρ (Hf.hash h (xv.get i)) = yv.get i)
      = (Dist.fTransform (fun f : H → Y => fun i => f (Hf.hash h (xv.get i)))
          (Dist.uniform (H → Y))) (fun i => yv.get i) :=
        mass_eval_eq_apply _ _ _
    _ = (if ∀ i j : Fin q, Hf.hash h (xv.get i) = Hf.hash h (xv.get j) →
          yv.get i = yv.get j then
          ((Fintype.card Y : ℝ) ^ Fintype.card
            {x : H // x ∈ queryImageSet (fun i => Hf.hash h (xv.get i))})⁻¹
        else 0) := uniformFunction_eval_apply _ _
    _ = (if ∀ i j : Fin q, xv.get i = xv.get j → yv.get i = yv.get j then
          ((Fintype.card Y : ℝ) ^ Fintype.card
            {x : Y // x ∈ queryImageSet (fun i => xv.get i)})⁻¹
        else 0) := by
        simp only [hcond]
        rw [hcard]
    _ = (Dist.fTransform (fun f : Y → Y => fun i => f (xv.get i))
          (Dist.uniform (Y → Y))) (fun i => yv.get i) :=
        (uniformFunction_eval_apply _ _).symm
    _ = (Dist.uniform (Y → Y)).mass
          (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) :=
        (mass_eval_eq_apply _ _ _).symm

/-- Per-transcript key bound via the compressed injective tuple. -/
theorem uniformK_hashBadAt_le (Hf : EpsUniversalHash K Y H)
    (xv : List.Vector Y q) :
    (Dist.uniform K).mass (fun h => ∃ i j : Fin q,
        xv.get i ≠ xv.get j ∧
        Hf.hash h (xv.get i) = Hf.hash h (xv.get j)) ≤
      choose2 q * Hf.eps := by
  classical
  set u : Fin q → Y := fun i => xv.get i with hu
  have hbridge : ∀ h : K, (∃ i j : Fin q, xv.get i ≠ xv.get j ∧
      Hf.hash h (xv.get i) = Hf.hash h (xv.get j)) ↔
      hashCollision Hf h (compressedQuery u) := by
    intro h
    constructor
    · rintro ⟨i, j, hne, hcol⟩
      refine ⟨compressedQueryIndex u i, compressedQueryIndex u j, ?_, ?_⟩
      · intro hab
        have h2 := congrArg (compressedQuery u) hab
        rw [compressedQuery_compressedQueryIndex,
          compressedQuery_compressedQueryIndex] at h2
        exact hne h2
      · have h2 : Hf.hash h (u i) = Hf.hash h (u j) := hcol
        rw [← compressedQuery_compressedQueryIndex u i,
          ← compressedQuery_compressedQueryIndex u j] at h2
        exact h2
    · rintro ⟨a, b, hab, hcol⟩
      obtain ⟨i, rfl⟩ := compressedQueryIndex_surjective u a
      obtain ⟨j, rfl⟩ := compressedQueryIndex_surjective u b
      refine ⟨i, j, ?_, ?_⟩
      · intro hx
        refine hab ?_
        unfold compressedQueryIndex
        exact congrArg _ (Subtype.ext (show u i = u j from hx))
      · have h2 : Hf.hash h (compressedQuery u (compressedQueryIndex u i)) =
            Hf.hash h (compressedQuery u (compressedQueryIndex u j)) := hcol
        rw [compressedQuery_compressedQueryIndex,
          compressedQuery_compressedQueryIndex] at h2
        exact h2
  rw [Dist.mass_congr _ hbridge]
  refine le_trans (hashCollision_prob_le Hf (compressedQuery u)
    (compressedQuery_injective u)) ?_
  gcongr
  exact_mod_cast Nat.choose_le_choose 2 (compressedQuery_card_le u)

/-- **The adaptive bad bound on the ideal extension**: the dummy key is
independent of the transcript, so the bad mass is an average of
per-transcript key bounds — no freshness recursion. -/
theorem htp_extRep_probBad_le (Hf : EpsUniversalHash K Y H)
    (E : QQueryEnvironment Y Y q) :
    Pr[HashBad Hf ∣ extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y))
        (idealF (K := K)) keyAug E.1] ≤ choose2 q * Hf.eps := by
  classical
  have hI : PFunPDS.Prob.KStepTotal
      (Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K))) q :=
    functionEvaluatorProb_KStepTotal (idealP (K := K) (Y := Y))
      (fun p => p.2) q
  have hmass : Pr[HashBad Hf ∣ extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y))
      (idealF (K := K)) keyAug E.1] =
      ∑ t : TranscriptPrefix Y Y q, ∑ h : K,
        if HashBad Hf (t, h) then
          extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug
            E.1 (t, h) else 0 := by
    rw [show Pr[HashBad Hf ∣ extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y))
        (idealF (K := K)) keyAug E.1] =
      (extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug
        E.1).mass (HashBad Hf) from rfl]
    rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  rw [hmass]
  have hinner : ∀ t : TranscriptPrefix Y Y q,
      (∑ h : K, if HashBad Hf (t, h) then
        extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug
          E.1 (t, h) else 0) ≤
      (choose2 q * Hf.eps) *
        tr[q]((Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K)) : ProbPDS Y Y), E.1) t := by
    intro t
    obtain ⟨xv, yv⟩ := t
    calc (∑ h : K, if HashBad Hf ((xv, yv), h) then
          extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug
            E.1 ((xv, yv), h) else 0)
        = (∑ h : K, if HashBad Hf ((xv, yv), h) then Dist.uniform K h else 0) *
            ((Dist.uniform (Y → Y)).mass
              (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) *
              η(E.1) (xv, yv)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [extendedTranscriptDistRep_apply, extSysFactorRep_ideal_apply]
          by_cases hb : HashBad Hf ((xv, yv), h)
          · rw [if_pos hb, if_pos hb]
            ring
          · rw [if_neg hb, if_neg hb, zero_mul]
      _ ≤ (choose2 q * Hf.eps) *
            ((Dist.uniform (Y → Y)).mass
              (fun g => ∀ i : Fin q, g (xv.get i) = yv.get i) *
              η(E.1) (xv, yv)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg
            (Dist.uniform_nonNeg.mass_nonneg _) (envFactor_nonneg _ _))
          calc (∑ h : K, if HashBad Hf ((xv, yv), h) then
                Dist.uniform K h else 0)
              = (Dist.uniform K).mass (fun h => HashBad Hf ((xv, yv), h)) :=
                (Dist.mass_eq_sum _ _).symm
            _ ≤ choose2 q * Hf.eps := by
                refine le_trans (le_of_eq (Dist.mass_congr _ (fun h =>
                  Iff.intro (fun hb => hb) (fun hb => hb)))) ?_
                exact uniformK_hashBadAt_le Hf xv
      _ = (choose2 q * Hf.eps) *
            tr[q]((Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K)) : ProbPDS Y Y), E.1)
              (xv, yv) := by
          rw [deterministicTranscriptDist_pmf_apply, sysFactor_ideal_eq]
  calc (∑ t : TranscriptPrefix Y Y q, ∑ h : K,
      if HashBad Hf (t, h) then
        extendedTranscriptDistRep (q := q) (idealP (K := K) (Y := Y)) (idealF (K := K)) keyAug
          E.1 (t, h) else 0)
      ≤ ∑ t : TranscriptPrefix Y Y q, (choose2 q * Hf.eps) *
          tr[q]((Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K)) : ProbPDS Y Y), E.1) t :=
        Finset.sum_le_sum fun t _ => hinner t
    _ = (choose2 q * Hf.eps) *
        (tr[q]((Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K)) : ProbPDS Y Y),
          E.1)).weight := by
        rw [← Finset.mul_sum, Dist.weight_eq_sum]
    _ ≤ choose2 q * Hf.eps := by
        rw [deterministicTranscriptDist_weight_eq_one _ E hI, mul_one]

/-- The dummy-key representative presents the URF law. -/
theorem pmf_dummyKey_eq_urf :
    (Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K)) : ProbPDS Y Y) =
      urf (X := Y) (Y := Y) := by
  refine Subtype.ext ?_
  show Dist.fTransform (idealF (K := K)) (idealP (K := K) (Y := Y)).val =
    Dist.fTransform PFunPDS.urfRV (PFunPDS.uniformP (X := Y) (Y := Y)).val
  rw [show (idealF (K := K) (Y := Y)) =
      PFunPDS.urfRV ∘ Prod.snd from rfl, ← Dist.fTransform_comp]
  congr 1
  refine Finsupp.ext fun g => ?_
  rw [Dist.fTransform_apply_eq_mass]
  refine ((mass_prod_snd_pred (Dist.uniform K) (Dist.uniform (Y → Y))
      (fun g' : Y → Y => g' = g)).trans ?_)
  rw [show (Dist.uniform K).weight = 1 from Dist.uniform_isProbDist.weight_eq, one_mul,
    PFunPDS.uniformP_val, Dist.mass_eq_sum]
  refine (Finset.sum_eq_single g (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ g) h)).trans (if_pos rfl)

/-- **Adaptive hash-then-PRF, tight**:

    Adv[q](hashThenPRF, urf) ≤ C(q,2)·ε

— the Layer E″ endpoint with the key revealed; no birthday term. -/
theorem hashThenPRF_adaptive_tight (Hf : EpsUniversalHash K Y H) :
    Adv[q](hashThenPRFProbPDS (Y := Y) Hf, urf (X := Y) (Y := Y)) ≤
      ((choose2 q * Hf.eps : NNReal) : ℝ) := by
  have hR : PFunPDS.Prob.KStepTotal
      (Dist.PMF (htpP (K := K) (Y := Y) (H := H)) (htpF Hf)) q :=
    functionEvaluatorProb_KStepTotal (htpP (K := K) (Y := Y) (H := H))
      (fun p => hashThenPRF Hf p.1 p.2) q
  have hI : PFunPDS.Prob.KStepTotal
      (Dist.PMF (idealP (K := K) (Y := Y)) (idealF (K := K))) q :=
    functionEvaluatorProb_KStepTotal (idealP (K := K) (Y := Y))
      (fun p => p.2) q
  rw [← pmf_dummyKey_eq_urf (K := K)]
  exact adv_le_of_extFixedQueryRep_eq_on_good (htpP (K := K) (Y := Y) (H := H)) (htpF Hf) (idealP (K := K) (Y := Y))
    (idealF (K := K)) keyAug keyAug (HashBad Hf) (choose2 q * Hf.eps)
    hR hI (htp_extFixedQuery_eq_on_good Hf) (htp_extRep_probBad_le Hf)

/-- The tight adaptive bound on the frozen endpoint surface. -/
theorem advPRF_hashThenPRF_le_tight (Hf : EpsUniversalHash K Y H) :
    RandomSystems.HTechnique.SecurityDefs.advPRF (q := q)
      (hashThenPRFProbPDS (Y := Y) Hf) ≤
      ((choose2 q * Hf.eps : NNReal) : ℝ) := by
  show Adv[q](hashThenPRFProbPDS (Y := Y) Hf, urf (X := Y) (Y := Y)) ≤ _
  exact hashThenPRF_adaptive_tight Hf

end HashThenPRFApp

end StressTests

/-! ## Generic mass / counting toolbox (upstreamed from `HCTR2.lean`, 2026-07-11)

Uniform pin/self-locating engines, the `expectW` weighted-mass functional, conditional
fiber bounds, indicator algebra, and small `Fin` counting helpers — all HCTR2-free. -/

section MassToolbox

/-- Uniform point mass `Pr[a = c] = 1/|A|` (the S1 leaf). -/
theorem uniform_pt_mass {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (c : A) : (Dist.uniform A).mass (fun a => a = c) = (Fintype.card A : ℝ)⁻¹ := by
  rw [Dist.mass_eq_sum]
  refine (Finset.sum_eq_single c (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  rw [if_pos rfl, Dist.uniform_apply, one_div]

/-- Tail-block embedding `Fin (L−1) → Fin L` (`j ↦ j + 1`) — the index type of the
`j ≥ 1` cells. -/
def finTail {L : ℕ} (j : Fin (L - 1)) : Fin L :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

@[simp] theorem finTail_val {L : ℕ} (j : Fin (L - 1)) :
    (finTail j).val = j.val + 1 := rfl

theorem finTail_injective {L : ℕ} : Function.Injective (finTail (L := L)) :=
  fun x y h => Fin.ext (by
    have h' := congrArg Fin.val h
    simp only [finTail_val] at h'
    omega)

/-- The `<`-subtype of ordered index pairs has `C(n, 2)` elements — the index type of the
cross-query cells. -/
theorem card_subtype_fin_lt (n : ℕ) :
    Fintype.card {x : Fin n × Fin n // x.1 < x.2} = n.choose 2 := by
  rw [Fintype.card_subtype, card_filter_fin_lt]

/-- Fraction comparison for the budget endgame: `C/N ≤ num/(2N)` given `2C ≤ num` (also
valid at `N = 0`, where both sides vanish). -/
theorem cast_mul_inv_le_div (C num N : ℕ) (h : 2 * C ≤ num) :
    (C : NNReal) * ((N : NNReal))⁻¹ ≤ (num : NNReal) / (2 * (N : NNReal)) := by
  rw [← div_eq_mul_inv, ← mul_div_mul_left (C : NNReal) (N : NNReal) two_ne_zero]
  gcongr
  exact_mod_cast h

/-- **Middle-coordinate functional mass** (UPSTREAM-CANDIDATE): if an event on
a uniform triple pins the middle coordinate given the outer two, its mass is
`≤ 1/|B|` — the triple analogue of `uniform_prod_snd_functional` (the
"`SjvB = ⋯` solves for `L`" shape).  (Oracle: `uniform_triple_middle_functional`.) -/
theorem uniform_triple_middle_functional {A B C : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C] (P : A × B × C → Prop)
    (hP : ∀ a b b' c, P (a, b, c) → P (a, b', c) → b = b') :
    (Dist.uniform (A × B × C)).mass P ≤ (Fintype.card B : ℝ)⁻¹ := by
  classical
  rw [uniform_mass_equiv ((Equiv.prodAssoc A C B).trans
    (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm C B))).symm P]
  refine uniform_prod_snd_functional _ (fun ac b b' h1 h2 => ?_)
  obtain ⟨a, c⟩ := ac
  exact hP a b b' c h1 h2

/-- **Self-locating pinned coordinate, dependent codomain, slice-restricted**
(UPSTREAM-CANDIDATE; PHASE P1a.E1): as `uniform_pi_selfloc_dep_le`, but the
mass is taken on `P ∧ S` for a slice event `S` that is a *cylinder in the
located direction* (`hS`), and the bound is the conditional
`(1/c) · mass S`.  Proof: the same anchor injection `Ψ = update-to-anchor`,
now targeting `anchored ∩ S` (`hS` keeps `Ψ` and its `Fin c`-tiling inside `S`),
so the `c`-fold embedding lands in `filter S` rather than the whole space,
giving `c · card(filter (P ∧ S)) ≤ card(filter S)`.  (Oracle: `uniform_pi_selfloc_slice_le`.) -/
theorem uniform_pi_selfloc_slice_le {ι : Type*} {X : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)]
    (P S : (∀ i, X i) → Prop) [DecidablePred P] [DecidablePred S]
    (loc : (∀ i, X i) → ι)
    (a₀ : ∀ i, X i) (c : ℕ) (hc0 : 0 < c)
    (hcard : ∀ ω, P ω → S ω → c ≤ Fintype.card (X (loc ω)))
    (hloc : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω)
    (hS : ∀ ω v, S (Function.update ω (loc ω) v) ↔ S ω)
    (hpin : ∀ ω ω', loc ω = loc ω' → (∀ i, i ≠ loc ω → ω i = ω' i) →
      P ω → P ω' → S ω → S ω' → ω (loc ω) = ω' (loc ω)) :
    (Dist.uniform (∀ i, X i)).mass (fun ω => P ω ∧ S ω)
      ≤ ((c : ℕ) : NNReal)⁻¹ * (Dist.uniform (∀ i, X i)).mass S := by
  classical
  -- cancellation: equal updates at self-located indices agree off-index
  have cancel : ∀ (ω ω' : ∀ i, X i) (a : X (loc ω)) (a' : X (loc ω')),
      Function.update ω (loc ω) a = Function.update ω' (loc ω') a' →
      loc ω = loc ω' ∧ (∀ i, i ≠ loc ω → ω i = ω' i) := by
    intro ω ω' a a' heq
    have hli : loc ω = loc ω' := by
      calc loc ω = loc (Function.update ω (loc ω) a) := (hloc ω a).symm
        _ = loc (Function.update ω' (loc ω') a') := by rw [heq]
        _ = loc ω' := hloc ω' a'
    refine ⟨hli, fun i hi => ?_⟩
    have h1 := congrFun heq i
    rw [Function.update_of_ne hi] at h1
    rw [h1, Function.update_of_ne (hli ▸ hi)]
  set anchor : (∀ i, X i) → (∀ i, X i) :=
    fun ω => Function.update ω (loc ω) (a₀ (loc ω)) with hanchor
  set Sset : Finset (∀ i, X i) :=
    (Finset.univ.filter (fun ω => P ω ∧ S ω)).image anchor with hSset
  -- the event injects into the anchored slice
  have hinjP : Set.InjOn anchor (Finset.univ.filter (fun ω => P ω ∧ S ω)) := by
    intro ω hω ω' hω' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      at hω hω'
    obtain ⟨hli, hoff⟩ := cancel ω ω' _ _ heq
    have hat := hpin ω ω' hli hoff hω.1 hω'.1 hω.2 hω'.2
    funext i
    by_cases hi : i = loc ω
    · subst hi; exact hat
    · exact hoff i hi
  have hcardS : (Finset.univ.filter (fun ω => P ω ∧ S ω)).card = Sset.card :=
    (Finset.card_image_of_injOn hinjP).symm
  -- anchored points are anchored and have large located coordinates
  have hanch : ∀ ω₀ ∈ Sset, ω₀ (loc ω₀) = a₀ (loc ω₀)
      ∧ c ≤ Fintype.card (X (loc ω₀)) := by
    intro ω₀ h₀
    obtain ⟨ω, hωP, rfl⟩ := Finset.mem_image.mp h₀
    have hl : loc (anchor ω) = loc ω := hloc ω _
    have hmem := (Finset.mem_filter.mp hωP).2
    constructor
    · rw [hl]; exact Function.update_self ..
    · rw [hl]; exact hcard ω hmem.1 hmem.2
  -- anchored points are inside `S`
  have hanchS : ∀ ω₀ ∈ Sset, S ω₀ := by
    intro ω₀ h₀
    obtain ⟨ω, hωP, rfl⟩ := Finset.mem_image.mp h₀
    exact (hS ω (a₀ (loc ω))).mpr (Finset.mem_filter.mp hωP).2.2
  -- choose per-coordinate embeddings of `Fin c` where they exist
  have hembex : ∀ i : ι, ∃ f : Fin c → X i,
      c ≤ Fintype.card (X i) → Function.Injective f := by
    intro i
    by_cases h : c ≤ Fintype.card (X i)
    · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
        (α := Fin c) (β := X i) (by simpa using h)
      exact ⟨e, fun _ => e.injective⟩
    · exact ⟨fun _ => Classical.arbitrary (X i), fun hcon => absurd hcon h⟩
  choose emb hembInj using hembex
  -- `Sset × Fin c` injects into `filter S`: update the located coordinate
  have hkey : c * Sset.card ≤ (Finset.univ.filter S).card := by
    have hprod : (Sset ×ˢ (Finset.univ : Finset (Fin c))).card = c * Sset.card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
    rw [← hprod]
    refine Finset.card_le_card_of_injOn
      (fun p => Function.update p.1 (loc p.1) (emb (loc p.1) p.2))
      (fun p hp => ?_) ?_
    · have hmem : p.1 ∈ Sset := (Finset.mem_product.mp hp).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (hS p.1 (emb (loc p.1) p.2)).mpr (hanchS p.1 hmem)
    · rintro ⟨ω₀, k⟩ hw ⟨ω₀', k'⟩ hw' heq
      have heq' : Function.update ω₀ (loc ω₀) (emb (loc ω₀) k)
          = Function.update ω₀' (loc ω₀') (emb (loc ω₀') k') := heq
      have hmem : ω₀ ∈ Sset := (Finset.mem_product.mp (Finset.mem_coe.mp hw)).1
      have hmem' : ω₀' ∈ Sset := (Finset.mem_product.mp (Finset.mem_coe.mp hw')).1
      obtain ⟨hw0, hcard0⟩ := hanch ω₀ hmem
      obtain ⟨hw0', -⟩ := hanch ω₀' hmem'
      obtain ⟨hli, hoff⟩ := cancel ω₀ ω₀' _ _ heq'
      have hωeq : ω₀ = ω₀' := by
        funext i
        by_cases hi : i = loc ω₀
        · subst hi; rw [hw0, hli, hw0']
        · exact hoff i hi
      subst hωeq
      have hval : emb (loc ω₀) k = emb (loc ω₀) k' := by
        have h1 := congrFun heq' (loc ω₀)
        rwa [Function.update_self, Function.update_self] at h1
      have hk : k = k' := hembInj (loc ω₀) hcard0 hval
      rw [hk]
  have hkeyfinal : c * (Finset.univ.filter (fun ω => P ω ∧ S ω)).card
      ≤ (Finset.univ.filter S).card := by rw [hcardS]; exact hkey
  -- turn the counting bound into the conditional mass bound
  rw [Dist.uniform_mass_eq_card_filter, Dist.uniform_mass_eq_card_filter]
  set N : ℝ := (Fintype.card (∀ i, X i) : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
  push_cast
  rw [show ((c : ℕ) : ℝ)⁻¹
        * (((Finset.univ.filter S).card : ℝ) / N)
      = ((Finset.univ.filter S).card : ℝ) / ((c : ℝ) * N) by
        rw [← mul_div_assoc, inv_mul_eq_div, div_div]]
  rw [div_le_div_iff₀ hNpos (mul_pos hcpos hNpos)]
  have : ((Finset.univ.filter (fun ω => P ω ∧ S ω)).card : ℝ) * ((c : ℝ) * N)
      = (((c * (Finset.univ.filter (fun ω => P ω ∧ S ω)).card : ℕ)) : ℝ) * N := by
    push_cast; ring
  rw [this]
  gcongr

/-- **Fused-coordinate self-locating pin over a product, slice-restricted**
(UPSTREAM-CANDIDATE; PHASE P1b4b V1): the slice twin of
`uniform_pi_prod_selfloc_fused_le` — the same fused pin, but the mass is taken on
`P ∧ S` for a slice event `S` that is a *cylinder in the fused pair's
coordinates* (`hS`: `S` invariant under updating both the located `ω`-coordinate
and the `j₀`-th `w`-coordinate), and the bound is the conditional
`(1/|V|) · mass S`.  Proof (route (a), the anchor-injection route mirrored at the
fused level): the same composite update `upd`/anchor injection as the base lemma,
now targeting `anchored ∩ S`; `hS` keeps `upd` and its `V`-tiling inside `S`, so
the `|V|`-fold embedding lands in `filter S` rather than the whole space, giving
`|V| · card(filter (P ∧ S)) ≤ card(filter S)`.  (Oracle: `uniform_pi_prod_selfloc_fused_slice_le`.) -/
theorem uniform_pi_prod_selfloc_fused_slice_le {ι κ V : Type*} {X : ι → Type*}
    {W : κ → Type*} {R : ι → Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [∀ i, Nonempty (X i)]
    [∀ j, Fintype (W j)] [∀ j, DecidableEq (W j)] [∀ j, Nonempty (W j)]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (P S : ((∀ i, X i) × (∀ j, W j)) → Prop) [DecidablePred P] [DecidablePred S]
    (loc : (∀ i, X i) → ι) (j₀ : κ)
    (e : ∀ i, X i × W j₀ ≃ V × R i) (v₀ : V)
    (hloc : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω)
    (hS : ∀ (p : (∀ i, X i) × (∀ j, W j)) (a : X (loc p.1)) (b : W j₀),
      S (Function.update p.1 (loc p.1) a, Function.update p.2 j₀ b) ↔ S p)
    (hpin : ∀ ω w ω' w', loc ω = loc ω' →
      (∀ i, i ≠ loc ω → ω i = ω' i) → (∀ j, j ≠ j₀ → w j = w' j) →
      P (ω, w) → P (ω', w') → S (ω, w) → S (ω', w') →
      (e (loc ω) (ω (loc ω), w j₀)).1 = (e (loc ω') (ω' (loc ω'), w' j₀)).1) :
    (Dist.uniform ((∀ i, X i) × (∀ j, W j))).mass (fun p => P p ∧ S p)
      ≤ (Fintype.card V : ℝ)⁻¹
        * (Dist.uniform ((∀ i, X i) × (∀ j, W j))).mass S := by
  classical
  -- the composite update: set the fused pair from a prescribed V-part,
  -- keeping the remainder
  set upd : ((∀ i, X i) × (∀ j, W j)) → V → ((∀ i, X i) × (∀ j, W j)) :=
    fun p v =>
      (Function.update p.1 (loc p.1)
        ((e (loc p.1)).symm (v, (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).2)).1,
       Function.update p.2 j₀
        ((e (loc p.1)).symm (v, (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).2)).2)
    with hupd
  have hlocupd : ∀ p v, loc (upd p v).1 = loc p.1 := fun p v => hloc p.1 _
  have hcoords : ∀ p v, ((upd p v).1 (loc p.1), (upd p v).2 j₀)
      = (e (loc p.1)).symm (v, (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).2) := by
    intro p v
    exact Prod.ext (Function.update_self ..) (Function.update_self ..)
  have hfusedupd : ∀ p v, e (loc p.1) ((upd p v).1 (loc p.1), (upd p v).2 j₀)
      = (v, (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).2) := by
    intro p v
    rw [hcoords p v, Equiv.apply_symm_apply]
  have hvpupd : ∀ p v, (e (loc (upd p v).1)
      ((upd p v).1 (loc (upd p v).1), (upd p v).2 j₀)).1 = v := by
    intro p v
    rw [hlocupd p v, hfusedupd p v]
  have hoffupd1 : ∀ p v i, i ≠ loc p.1 → (upd p v).1 i = p.1 i := by
    intro p v i hi
    exact Function.update_of_ne hi _ _
  have hoffupd2 : ∀ p v j, j ≠ j₀ → (upd p v).2 j = p.2 j := by
    intro p v j hj
    exact Function.update_of_ne hj _ _
  have cancel : ∀ p p' v v', upd p v = upd p' v' →
      loc p.1 = loc p'.1 ∧ (∀ i, i ≠ loc p.1 → p.1 i = p'.1 i) ∧
        (∀ j, j ≠ j₀ → p.2 j = p'.2 j) ∧ v = v' := by
    intro p p' v v' heq
    have hli : loc p.1 = loc p'.1 := by
      calc loc p.1 = loc (upd p v).1 := (hlocupd p v).symm
        _ = loc (upd p' v').1 := by rw [heq]
        _ = loc p'.1 := hlocupd p' v'
    refine ⟨hli, fun i hi => ?_, fun j hj => ?_, ?_⟩
    · have h1 : (upd p v).1 i = (upd p' v').1 i := by rw [heq]
      rwa [hoffupd1 p v i hi, hoffupd1 p' v' i (hli ▸ hi)] at h1
    · have h1 : (upd p v).2 j = (upd p' v').2 j := by rw [heq]
      rwa [hoffupd2 p v j hj, hoffupd2 p' v' j hj] at h1
    · have h1 := hvpupd p v
      rw [heq, hvpupd p' v'] at h1
      exact h1.symm
  have hfusedeq : ∀ p p' v v', upd p v = upd p' v' → loc p.1 = loc p'.1 →
      (v, (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).2)
        = ((v', (e (loc p.1) (p'.1 (loc p.1), p'.2 j₀)).2) : V × R (loc p.1)) := by
    intro p p' v v' heq hli
    have h1 := hfusedupd p v
    have h2 := hfusedupd p' v'
    rw [← hli] at h2
    rw [← heq] at h2
    exact h1.symm.trans h2
  -- full recovery of a point from off-coordinates + fused pair (common index)
  have hfull : ∀ p p' : ((∀ i, X i) × (∀ j, W j)), loc p.1 = loc p'.1 →
      (∀ i, i ≠ loc p.1 → p.1 i = p'.1 i) → (∀ j, j ≠ j₀ → p.2 j = p'.2 j) →
      e (loc p.1) (p.1 (loc p.1), p.2 j₀) = e (loc p.1) (p'.1 (loc p.1), p'.2 j₀) →
      p = p' := by
    intro p p' hli hoff1 hoff2 hfused
    have hpair : (p.1 (loc p.1), p.2 j₀) = (p'.1 (loc p.1), p'.2 j₀) :=
      (e (loc p.1)).injective hfused
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · by_cases hi : i = loc p.1
      · subst hi
        exact congrArg Prod.fst hpair
      · exact hoff1 i hi
    · by_cases hj : j = j₀
      · subst hj
        exact congrArg Prod.snd hpair
      · exact hoff2 j hj
  -- the anchoring update to V-part `v₀`
  set anchor : ((∀ i, X i) × (∀ j, W j)) → ((∀ i, X i) × (∀ j, W j)) :=
    fun p => upd p v₀ with hanchor
  set Sset : Finset ((∀ i, X i) × (∀ j, W j)) :=
    (Finset.univ.filter (fun p => P p ∧ S p)).image anchor with hSset
  -- the event injects into the anchored slice
  have hinjP : Set.InjOn anchor (Finset.univ.filter (fun p => P p ∧ S p)) := by
    intro p hp p' hp' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      at hp hp'
    have heq' : upd p v₀ = upd p' v₀ := heq
    obtain ⟨hli, hoff1, hoff2, -⟩ := cancel p p' v₀ v₀ heq'
    have hsnd : (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).2
        = (e (loc p.1) (p'.1 (loc p.1), p'.2 j₀)).2 := by
      have h := congrArg Prod.snd (hfusedeq p p' v₀ v₀ heq' hli)
      exact h
    have hfst : (e (loc p.1) (p.1 (loc p.1), p.2 j₀)).1
        = (e (loc p.1) (p'.1 (loc p.1), p'.2 j₀)).1 := by
      have hv := hpin p.1 p.2 p'.1 p'.2 hli hoff1 hoff2 hp.1 hp'.1 hp.2 hp'.2
      rwa [← hli] at hv
    exact hfull p p' hli hoff1 hoff2 (Prod.ext hfst hsnd)
  have hcardS : (Finset.univ.filter (fun p => P p ∧ S p)).card = Sset.card :=
    (Finset.card_image_of_injOn hinjP).symm
  -- anchored points have V-part `v₀`
  have hanchored : ∀ p₁ ∈ Sset, (e (loc p₁.1) (p₁.1 (loc p₁.1), p₁.2 j₀)).1 = v₀ := by
    intro p₁ h₁
    obtain ⟨p₂, -, rfl⟩ := Finset.mem_image.mp h₁
    exact hvpupd p₂ v₀
  -- anchored points are inside `S`
  have hanchS : ∀ p₁ ∈ Sset, S p₁ := by
    intro p₁ h₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp h₁
    exact (hS p₂ _ _).mpr (Finset.mem_filter.mp hp₂).2.2
  -- `Sset × V` injects into `filter S` via the composite update
  have hkey : Fintype.card V * Sset.card ≤ (Finset.univ.filter S).card := by
    have hprod : (Sset ×ˢ (Finset.univ : Finset V)).card = Fintype.card V * Sset.card := by
      rw [Finset.card_product, Finset.card_univ, Nat.mul_comm]
    rw [← hprod]
    refine Finset.card_le_card_of_injOn (fun pv => upd pv.1 pv.2)
      (fun pv hpv => ?_) ?_
    · have hmem : pv.1 ∈ Sset := (Finset.mem_product.mp hpv).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (hS pv.1 _ _).mpr (hanchS pv.1 hmem)
    · rintro ⟨p₀, v⟩ hw ⟨p₀', v'⟩ hw' heq
      have heq' : upd p₀ v = upd p₀' v' := heq
      have hmem : p₀ ∈ Sset := (Finset.mem_product.mp (Finset.mem_coe.mp hw)).1
      have hmem' : p₀' ∈ Sset := (Finset.mem_product.mp (Finset.mem_coe.mp hw')).1
      obtain ⟨hli, hoff1, hoff2, hveq⟩ := cancel p₀ p₀' v v' heq'
      have hsnd : (e (loc p₀.1) (p₀.1 (loc p₀.1), p₀.2 j₀)).2
          = (e (loc p₀.1) (p₀'.1 (loc p₀.1), p₀'.2 j₀)).2 := by
        have h := congrArg Prod.snd (hfusedeq p₀ p₀' v v' heq' hli)
        exact h
      have hva' := hanchored p₀' hmem'
      rw [← hli] at hva'
      have hfst : (e (loc p₀.1) (p₀.1 (loc p₀.1), p₀.2 j₀)).1
          = (e (loc p₀.1) (p₀'.1 (loc p₀.1), p₀'.2 j₀)).1 := by
        rw [hanchored p₀ hmem, hva']
      have hp := hfull p₀ p₀' hli hoff1 hoff2 (Prod.ext hfst hsnd)
      rw [hp, hveq]
  have hkeyfinal : Fintype.card V * (Finset.univ.filter (fun p => P p ∧ S p)).card
      ≤ (Finset.univ.filter S).card := by rw [hcardS]; exact hkey
  -- turn the counting bound into the conditional mass bound
  rw [Dist.uniform_mass_eq_card_filter, Dist.uniform_mass_eq_card_filter]
  set N : ℝ := (Fintype.card ((∀ i, X i) × (∀ j, W j)) : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hcpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [show (Fintype.card V : ℝ)⁻¹
        * (((Finset.univ.filter S).card : ℝ) / N)
      = ((Finset.univ.filter S).card : ℝ) / ((Fintype.card V : ℝ) * N) by
        rw [← mul_div_assoc, inv_mul_eq_div, div_div]]
  rw [div_le_div_iff₀ hNpos (mul_pos hcpos hNpos)]
  have : ((Finset.univ.filter (fun p => P p ∧ S p)).card : ℝ)
        * ((Fintype.card V : ℝ) * N)
      = (((Fintype.card V * (Finset.univ.filter (fun p => P p ∧ S p)).card : ℕ)) : ℝ) * N := by
    push_cast; ring
  rw [this]
  gcongr

/-- **Weighted mass** (the expectation of a nonnegative weight `w` under `D`).

Thin wrapper over `Dist.expect` (`RandomSystems/DistExpect.lean`), the
library-level expectation this operator predated; kept for the `NNReal`-weighted
call sites of the HCTR2 development (`DESIGN.md` §12 point 4 — one owner, callers
repointed).  New code should use `Dist.expect` directly.  (Oracle: `expectW`.) -/
noncomputable def expectW {A : Type*} [Fintype A] (D : Dist A) (w : A → NNReal) :
    ℝ :=
  Dist.expect D fun a => (w a : ℝ)

/-- `expectW` of a nonnegative law is nonnegative. -/
theorem expectW_nonneg {A : Type*} [Fintype A] {D : Dist A} (hDnn : D.NonNeg)
    (w : A → NNReal) : 0 ≤ expectW D w :=
  Dist.expect_nonneg hDnn fun a => (w a).coe_nonneg

/-- **Support bound**: a uniform bound on the weight over the support of `D`
lifts to `expectW D w ≤ c · D.weight`.  (Oracle: `expectW_le_of_support_bound`.) -/
theorem expectW_le_of_support_bound {A : Type*} [Fintype A] {D : Dist A}
    (hDnn : D.NonNeg)
    (w : A → NNReal) (c : NNReal) (h : ∀ a, D a ≠ 0 → w a ≤ c) :
    expectW D w ≤ c * D.weight :=
  Dist.expect_le_mul_weight hDnn fun a ha =>
    NNReal.coe_le_coe.mpr (h a (Finsupp.mem_support_iff.mp ha))

/-- **Sum-swap**: a `Finset`-indexed family of `expectW`s collects into a single
`expectW` of the summed weight (`Dist.expect_finset_sum` under the hood).
(Oracle: `expectW_sum_swap`.) -/
theorem expectW_sum_swap {A ι : Type*} [Fintype A] (D : Dist A) (s : Finset ι)
    (w : ι → A → NNReal) :
    (∑ p ∈ s, expectW D (w p)) = expectW D (fun a => ∑ p ∈ s, w p a) := by
  simp only [expectW, Dist.expect_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [NNReal.coe_sum, Finset.mul_sum]

/-- **Additivity** (PHASE P1b4a): `expectW` is additive in the weight — the split
D-cells (`MM`–`MM` cross: a `senc` reveal leg plus an `sdec` pin leg) sum their
two `expectW`s into one at the merged per-pair weight.  (Oracle: `expectW_add`.) -/
theorem expectW_add {A : Type*} [Fintype A] (D : Dist A) (w w' : A → NNReal) :
    expectW D w + expectW D w' = expectW D (fun a => w a + w' a) := by
  simp only [expectW, Dist.expect_eq_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [NNReal.coe_add, mul_add]

/-- **Constant-weight indicator collapse** (PHASE P1b4a): `expectW` of a constant
scalar over a predicate is that scalar times the predicate's mass — the pin-route
cells (`(1/N)·mass(valid)`) land in `expectW` form through this.  (Oracle: `expectW_indicator_const`.) -/
theorem expectW_indicator_const {A : Type*} [Fintype A] (D : Dist A) (P : A → Prop)
    [DecidablePred P] (c : NNReal) :
    expectW D (fun a => if P a then c else 0) = c * D.mass P := by
  rw [show expectW D (fun a => if P a then c else 0)
      = Dist.expect D fun a => ((if P a then c else 0 : NNReal) : ℝ) from rfl,
    show (fun a => ((if P a then c else 0 : NNReal) : ℝ))
      = fun a => if P a then (c : ℝ) else 0 from
        funext fun a => by split <;> simp,
    Dist.expect_indicator_const]

/-- **Weighted conditional fiber bound** (PHASE P1b3.C1, the `_wexp` engine
extension): `mass_le_of_fiber_snd_cond` with a *per-`a`* bound function `bnd`.
On a factored product `D (a, b) = u b · f a`, if `P` lies inside the `a`-cylinder
`V` (`hVP`) and every `V`-fiber with mass has `u`-mass `≤ bnd a` (`h`), then
`D.mass P ≤ expectW D (fun ab => if V ab.1 then bnd ab.1 else 0)` — the sharp
green cells feed a *`t`-dependent* scalar `bnd t = bitMsgDeg …/N`, so the const
`bnd` of the `_cond` engine no longer suffices.  (Oracle: `mass_le_of_fiber_snd_cond_wexp`.) -/
theorem mass_le_of_fiber_snd_cond_wexp {A B : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (f : A → ℝ) (u : Dist B)
    (hD : ∀ a b, D (a, b) = u b * f a) (hf_nonneg : ∀ a, 0 ≤ f a)
    (hu : u.weight = 1)
    (P : A × B → Prop) (V : A → Prop) [DecidablePred V] (bnd : A → NNReal)
    (hVP : ∀ a b, P (a, b) → V a)
    (h : ∀ a, f a ≠ 0 → V a → u.mass (fun b => P (a, b)) ≤ bnd a) :
    D.mass P ≤ expectW D (fun ab => if V ab.1 then bnd ab.1 else 0) := by
  classical
  rw [Dist.mass_eq_sum, Fintype.sum_prod_type]
  have hinner : ∀ a, (∑ b, if P (a, b) then D (a, b) else 0)
      = u.mass (fun b => P (a, b)) * f a := by
    intro a
    rw [Dist.mass_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hp : P (a, b) <;> simp [hp, hD a b]
  have hE : expectW D (fun ab => if V ab.1 then bnd ab.1 else 0)
      = ∑ a, ((if V a then bnd a else 0 : NNReal) : ℝ) * f a := by
    rw [expectW, Dist.expect_eq_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (∑ b, D (a, b) * ((if V a then bnd a else 0 : NNReal) : ℝ))
      = ((if V a then bnd a else 0 : NNReal) : ℝ) * f a
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp_rw [hD a]
    rw [← Finset.sum_mul, ← Dist.weight_eq_sum, hu, one_mul]
  rw [hE]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hinner a]
  by_cases hv : V a
  · rw [if_pos hv]
    rcases eq_or_ne (f a) 0 with h0 | h0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (h a h0 hv) (hf_nonneg a)
  · have hz : u.mass (fun b => P (a, b)) = 0 := by
      rw [Dist.mass_eq_sum, Finset.sum_eq_zero]
      exact fun b _ => if_neg (fun hp => hv (hVP a b hp))
    rw [if_neg hv, hz, zero_mul, NNReal.coe_zero, zero_mul]

/-- **Conditional fiber bound over the first coordinate** (PHASE P1b4a engine):
the `_cond` twin of `mass_le_of_fiber_fst`.  On a factored product
`D (a, b) = g b · w a` (`g` a probability law over the fibered coordinate `b`),
a per-fiber conditional bound `w.mass (P(·, b)) ≤ c · w.mass S` for a
first-coordinate slice `S` lifts to `D.mass P ≤ c · D.mass (S∘fst)` — the slice
rides through as the conditioning weight (the `Σ_b g b = 1` closes the tally).  (Oracle: `mass_le_of_fiber_fst_cond`.) -/
theorem mass_le_of_fiber_fst_cond {A B : Type*} [Fintype A] [Fintype B]
    (D : Dist (A × B)) (w : Dist A) (g : B → ℝ)
    (hD : ∀ a b, D (a, b) = g b * w a) (hg_nonneg : ∀ b, 0 ≤ g b)
    (hg : ∑ b, g b = 1)
    (S : A → Prop) (P : A × B → Prop) (c : NNReal)
    (h : ∀ b, g b ≠ 0 → w.mass (fun a => P (a, b)) ≤ c * w.mass S) :
    D.mass P ≤ c * D.mass (fun ab => S ab.1) := by
  classical
  have hSmass : D.mass (fun ab => S ab.1) = w.mass S := by
    rw [Dist.mass_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
    have hb : ∀ b, (∑ a, if S a then D (a, b) else 0) = g b * w.mass S := by
      intro b
      rw [Dist.mass_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by by_cases hs : S a <;> simp [hs, hD a b]
    simp_rw [hb]
    rw [← Finset.sum_mul, hg, one_mul]
  rw [hSmass, Dist.mass_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  have hbound : ∀ b, (∑ a, if P (a, b) then D (a, b) else 0) ≤ g b * (c * w.mass S) := by
    intro b
    rw [show (∑ a, if P (a, b) then D (a, b) else 0)
        = g b * w.mass (fun a => P (a, b)) from by
      rw [Dist.mass_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by by_cases hp : P (a, b) <;> simp [hp, hD a b]]
    rcases eq_or_ne (g b) 0 with h0 | h0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (h b h0) (hg_nonneg b)
  refine le_trans (Finset.sum_le_sum (fun b _ => hbound b)) (le_of_eq ?_)
  rw [← Finset.sum_mul, hg, one_mul]

/-- **First-coordinate functional mass on a uniform triple** (UPSTREAM-CANDIDATE): if an
event pins the first coordinate given the outer two, its mass is `≤ 1/|A|` — companion of
`uniform_triple_middle_functional` (the "`h̄` hits a transcript-determined value" shape).
(Oracle: `uniform_triple_fst_functional`.) -/
theorem uniform_triple_fst_functional {A B C : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C] (P : A × B × C → Prop)
    (hP : ∀ a a' b c, P (a, b, c) → P (a', b, c) → a = a') :
    (Dist.uniform (A × B × C)).mass P ≤ (Fintype.card A : NNReal)⁻¹ := by
  classical
  rw [uniform_mass_equiv
    (⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2),
      fun _ => rfl, fun _ => rfl⟩ :
      A × B × C ≃ B × A × C) P]
  exact uniform_triple_middle_functional _
    (fun b a a' c h1 h2 => hP a a' b c h1 h2)

/-- **Fubini slice bound over the first coordinate of a uniform product**
(UPSTREAM-CANDIDATE): a slice bound uniform in the second coordinate bounds the joint mass
— the "`prop1` against a reveal-determined target" engine.  (Oracle:
`uniform_prod_fst_slice_le`.) -/
theorem uniform_prod_fst_slice_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (P : A × B → Prop) (b : ℝ)
    (h : ∀ y : B, (Dist.uniform A).mass (fun a => P (a, y)) ≤ b) :
    (Dist.uniform (A × B)).mass P ≤ b := by
  classical
  have hb : 0 ≤ b :=
    le_trans (Dist.uniform_nonNeg.mass_nonneg _) (h (Classical.arbitrary B))
  refine mass_le_of_fiber_fst (Dist.uniform (A × B)) (Dist.uniform A)
    (fun _ : B => ((Fintype.card B : ℝ))⁻¹) (fun a y => ?_)
    (fun _ => by positivity) ?_ P b hb
    (fun y _ => h y)
  · rw [Dist.uniform_apply, Dist.uniform_apply, Fintype.card_prod, Nat.cast_mul,
      one_div, one_div, mul_inv, mul_comm]
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- Merge two same-guard indicators (mmCross's `senc`+`sdec` legs).  (Oracle:
`ite_add_ite_zero`.) -/
theorem ite_add_ite_zero {P : Prop} [Decidable P] (a b : NNReal) :
    (if P then a else 0) + (if P then b else 0) = if P then a + b else 0 := by
  split_ifs <;> simp

/-- **Disjoint-kind charge collapse**: two `w`-charged legs on the complementary slices
of a partition of the pair's validity sum to a SINGLE `w`.  (Oracle:
`ite_add_ite_of_disjoint`.) -/
theorem ite_add_ite_of_disjoint {A B : Prop} [Decidable A] [Decidable B]
    (w : NNReal) (hdisj : ¬(A ∧ B)) :
    (if A then w else 0) + (if B then w else 0) = if A ∨ B then w else 0 := by
  by_cases hA : A
  · by_cases hB : B
    · exact absurd ⟨hA, hB⟩ hdisj
    · simp [hA, hB]
  · by_cases hB : B <;> simp [hA, hB]

/-- **Kind-partition indicator collapse**: the merged indicator over the complementary
slices `A ∧ K` / `A ∧ ¬K` is the single indicator over `A`.  (Oracle: `ite_kind_or`.) -/
theorem ite_kind_or {A K : Prop} [Decidable A] [Decidable K] (w : NNReal) :
    (if (A ∧ K) ∨ (A ∧ ¬ K) then w else 0) = if A then w else 0 := by
  by_cases hA : A <;> by_cases hK : K <;> simp [hA, hK]

end MassToolbox

end HTechniqueDerivation
end RandomSystems.CR18
