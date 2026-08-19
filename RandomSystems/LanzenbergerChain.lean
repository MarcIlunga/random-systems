/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystemCoupling
import RandomSystems.GameWinnability
import RandomSystems.MultiSystemCoupling

/-!
# The Lanzenberger chain, named
(Lanzenberger, *Theory of Random Systems and Games*, Ch. 2 — the numbered
derivation, one Lean declaration per thesis item)

Every numbered step of the thesis's Chapter 2 derivation exists in the tree;
this file is the *name table* plus the four statements that previously had no
declaration in the thesis's own shape.  Statements were checked against the
scanned original (`papers/thesis (1).pdf`, printed pages 11–23 and 87–88), not
against secondary notes.

## Definitions (already named; no wrapper needed)

| Thesis            | Lean declaration |
| ----------------- | ---------------- |
| Def 2.1 distribution (finite support, arbitrary weight) | `RandomSystems.Dist`, `Dist.weight`; normalization is the *separate* predicate `Dist.isProbDist` / subtype `Dist.ProbDist` |
| Def 2.2 marginal | `Dist.marginal`, `Dist.marginalAt` |
| Def 2.4 statistical distance (one-sided) | `RandomSystems.CR18.δ` (indexed by `μ.support`), `RandomSystems.statDist` (indexed by `(μ − ν).support`); agreement on a non-negative second law: `delta_eq_statDist` below |
| Def 2.6 f-transformation | `Dist.fTransform` |
| Def 2.9 DDS | `PFunDDS.DDS` (partial function on `List X`, prefix-closed domain, empty history excluded) |
| Def 2.11 DDE | `PFunDDS.DDE` — **model note**: the thesis environment is a partial `e : Y* →. X` plus a compatibility side condition; the repository uses CR18's `⊥`-totalized `List (Option Y) → Option X`, interacting with `s⊥` (`PFunDDS.fullyDefined`).  Compatibility is thereby absorbed, and domains become *observable*, which is why no common-domain hypothesis appears in `Equivalent` (see Lemma 2.18 note below). |
| Def 2.12 transcript `tr(s,e)` | `PFunDDS.transcript` (function form), `PFunDDS.Transcript` (prefix characterization, `PFunDDS.transcript_mem_iff`) |
| Def 2.14 PDS | `RandomSystems.CR18.PFunPDS` = `Dist (DDS X Y)` — arbitrary nonnegative weight, exactly Def 2.1's generality.  The thesis's "one shared domain" clause is the separate predicate `PFunPDS.HasFixedDomain` (pair form `PFunPDS.HaveCommonDomainAndBounded`), imposed only where the thesis needs it (Theorem 2.31/2.32); its standing finiteness assumption is the `[Fintype X]` + depth-bound hypotheses there. |
| Def 2.15 PDE | `RandomSystems.CR18.PFunPDE`, `ProbPDE` |
| Ex. 2.16 `V_α`, `V₀ ≡ V_{1/2}` at `δ = 1` | `Example216.lean`: `Example216.V`, `equivalent_V`, `delta_V0_Vhalf`; the single-query carrier of Fig. 2.1 is `Example216.singleQuery` |
| Def 2.17 equivalence `S ≡ T` | `RandomSystems.CR18.Equivalent` (via `transcriptDist`, deterministic environments — Def 2.17's own quantifier) |
| Notation 2.19 random system = equivalence class | `RandomSystems.CR18.RandomSystem` (`RandomSystemQuotient.lean`) |
| Def 2.26 optimal advantage `Adv` | `RandomSystems.CR18.Adv`; its remark (= classical verdict advantage) is `adv_eq_maxAdvantage_swap` |
| Def 2.28 class distance `Δ` | `RandomSystems.CR18.Δ` |
| Notation 2.34 successors `s↑x`, `e↑y`, `S↑x↓y` | `PFunDDS.DDS.successor`, `PFunDDS.DDE.successor`, `RandomSystems.CR18.successorTransform`; the sub-normalization remark (`|S↑x↓y|` = answer probability) is `weight_successorTransform` |

## Theorems (already named; no wrapper needed)

| Thesis | Lean declaration |
| ------ | ---------------- |
| Lemma 2.5 partition additivity | `RandomSystems.CR18.δ_sum_of_disjoint_support` |
| Lemma 2.7 data processing | `RandomSystems.CR18.δ_fTransform_le` |
| Lemma 2.8 coupling lemma (attainment half) | `RandomSystems.CR18.optimal_coupling_exists_finsupp`, normalized `optimal_probability_coupling_exists` |
| Lemma 2.18 (hard direction) | `RandomSystems.CR18.transcript_equivalent_of_nonadaptive_transcript_equivalent`; thesis iff shape below |
| Lemma 2.33 arbitrary-weight joint induction lemma | `RandomSystems.CR18.exists_finite_class_joint_witness_of_common_side_weights` |
| Thm 2.31 (easy direction) | `RandomSystems.CR18.optimal_advantage_le_class_distance` |
| Thm 2.31 (hard direction + attainment) | `BoundedAttainment.lean`: `exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded`, `class_distance_eq_optimal_advantage_of_finite_common_domain_and_bounded`; thesis conjunction shape below |
| Thm 2.32 coupling theorem | `RandomSystemCoupling.lean`: `exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded`; thesis shape below |
| CR18 §3.6 behavior ↔ transcript law | `RandomSystems.CR18.behavior_equivalent_iff_transcript_equivalent` (`RandomSystem.lean`) |

## The game half (§2.3.3 Random Games, §2.4.3 Game Winnability)

Statements checked against the scanned original, printed pages 16–17 and
23–26.  The repository's game carrier is CR18's MBO form (`PFunPDS X (Y ×
Bool)`), **not** the thesis's MC-pair `(s, A)`; the bridge and the two model
discrepancies are documented in `GameWinnability.lean`'s header.

| Thesis | Lean declaration |
| ------ | ---------------- |
| Def 2.20 MC + DDG | carriers `PFunDDS.IsMBO`, `PFunDDS.DDS.IsGame`, `PFunDDS.DDG` (`PDS.lean`, CR18 Def 3.22) — **model note**: the thesis MC is an input-history predicate `A : X* → {0,1}` *paired* with an `(X,Y)`-DDS; the repository carries the bit in the output alphabet.  A thesis pair is `PFunDDS.gameOfDDS` at an input-only condition (`GameOf.lean`, whose Def 2.20 reconciliation note predates this file); footnote 7's monotonicity is `PFunDDS.MonotoneCond` / `PFunDDS.DDS.IsGame`, **not needed** for §2.4.3. |
| Def 2.21 game transcript `tr(s^A, e)` | `RandomSystems.CR18.gameTranscriptView`, `gameTranscriptDist` — the bit-stripped transcript plus the single `wonFlag`; the environment is `PFunDDS.Winner X Y = DDE X Y` through `PFunDDS.winnerView` (Remark 2.23: the MC is not observed during the interaction). |
| Def 2.22 PDG + equivalence | PDG carrier `PFunPDS.PDG` (`PDS.lean`); the equivalence is `RandomSystems.CR18.GameEquivalent`.  **Discrepancy note**: CR18's `≡ᵍ` (`GameEquivalence.lean`, Def 4.16 pre-winning behavior) is *not* thesis Def 2.22 — it conditions on the not-yet-won region rather than comparing `(t, A(t'))` laws. |
| Remark 2.23 | quantitative half: `RandomSystems.CR18.gameEquivalent_of_equivalent` (full-transcript equivalence refines game equivalence); uselessness of observing the MC *for winning*: `winningTranscript_winnerView_blindize_iff`. |
| Remark 2.24 | prose (random game = equivalence class); adjoining an MC to a system is `RandomSystems.CR18.gameOf` (`GameOf.lean`). |
| Def 2.25 supremum winning probability `ν` | `RandomSystems.CR18.supWinProb`; agreement with CR18's Γ (Def 4.17, `WinProb.lean`): `maxWinProb_eq_supWinProb`. |
| Def 2.35 winnable DDG | `RandomSystems.CR18.PFunDDS.Winnable` |
| Def 2.36 infimum winnability `ω` | `RandomSystems.CR18.infWinnability` |
| Thm 2.37 Winnability Theorem | `RandomSystems.CR18.winnability_theorem_of_fixed_domain_and_bounded` (`GameWinnability.lean`, proved via the thesis's own alternative proof on top of Thm 2.31); thesis conjunction shape `theorem_2_37_winnability_theorem` below. |

**Def 2.27/2.28/Thm 2.29/Lemma 2.30 (closed 2026-07-27, with two source
errata):** the carrier-level layer (joint distributions, `supAgreement`, the
`n`-ary maximal coupling, Lemma 2.30's matrix bound, and the corrected
distribution-level Theorem 2.29 step) lives in `MultiSystemCoupling.lean`;
this file keeps Def 2.27 (`multiSystemDistance`, **with the thesis's
`inf`-over-representatives corrected to a `sup`** — see its docstring),
Def 2.28's asserted identity
(`definition_2_28_pair_distance_eq_class_distance`), and Theorem 2.29's
lower bound (`theorem_2_29_lower_bound`, `theorem_2_29_lower_bound_min_form`)
and upper bound (`theorem_2_29_upper_bound`, **in the corrected
`max`-over-pairs form**; the printed `min` form is refuted kernel-checked at
the distribution level, `printed_min_form_counterexample` in
`MultiSystemCoupling.lean`).

## What this file adds

* `delta_eq_statDist` — Def 2.4's two repository renderings agree (previously
  only an inline step inside `optimal_coupling_exists_finsupp`);
* `fixed_transcript_event_eq_fixed_query_event` — Appendix A.1's proof device
  for Lemma 2.18, under a thesis-pointing name;
* `lemma_2_18_nonadaptive_environments_suffice` — Lemma 2.18 in the thesis's
  own **iff** shape (the tree named only the nontrivial direction);
* `transcriptDistMixture` + `definition_2_17_probabilistic_environments_agree`
  — Def 2.17's parenthetical ("deterministic environments give the same
  equivalence notion as probabilistic ones"), previously noted only in
  `Equivalent`'s docstring;
* `theorem_2_31_distance_eq_advantage_attained` — Theorem 2.31 as the thesis
  states it: `Δ = Adv` *and* representatives attaining `δ = Δ`, one statement;
* `theorem_2_32_coupling_theorem` — Theorem 2.32 under a thesis-pointing name;
* `theorem_2_37_winnability_theorem` — Theorem 2.37 in the thesis's own
  conjunction shape: `ν = ω` *and* a representative attaining
  `Pr(winnable) = ω`;
* `multiSystemDistance` — Def 2.27 with its `inf`/`sup` erratum corrected
  (see the section header below), plus Theorem 2.29:
  `multiSystemDistance_pair_le` and `theorem_2_29_lower_bound` /
  `theorem_2_29_lower_bound_min_form` (lower half),
  `definition_2_28_pair_distance_eq_class_distance` (Def 2.28's asserted
  identity with the repository's `Δ`), and `theorem_2_29_upper_bound` (upper
  half, corrected `max` form) — on top of `MultiSystemCoupling.lean`'s
  Lemma 2.30, `n`-ary maximal coupling, and
  `theorem_2_29_distribution_upper_bound`;
* `printedMultiSystemDistance` — Def 2.28's second display rendered
  **verbatim**, kept solely so that `Example216.lean` can prove the two
  printed displays disagree (Def 2.15/2.16/2.17 and the erratum live there).

The unrestricted (unbounded / varying-domain) strengthening of 2.31/2.32 is
**false** in this model — `papers/notes/RS_SOURCE_CONTRACT.md` records the
boundary and counterexample; the hypotheses here are the thesis's own standing
finiteness assumptions (Def 2.9 "finite", Def 2.14 "we always assume S is
finite"), made explicit.
-/

namespace RandomSystems.CR18.Lanzenberger

open RandomSystems (Dist statDist)
open RandomSystems.CR18

universe u v

variable {X : Type u} {Y : Type v}

/-- Thesis Definition 2.4's two repository renderings agree: the Finsupp-native
one-sided distance `δ` *is* `statDist`.  Both sides are
`∑ₐ max(0, X(a) − Y(a))` — the thesis's asymmetric distance, sound at unequal
weights.  Previously this identity lived only as an inline step inside
`optimal_coupling_exists_finsupp`; naming it makes the Def 2.4 invariant
kernel-checked once and for all.

`hν` is the signed carrier's cost, and it is the *whole* content of the gap:
`δ` sums over `μ.support`, `statDist` over `(μ − ν).support`, and the cells
`δ` omits carry `max (−ν a) 0`, which vanishes exactly when `ν ≥ 0`.
`Dist.NonNeg` is therefore not a convenience — at `ν = −1` off `μ`'s support
the two renderings genuinely differ — and nothing here uses normalization, so
`isProbDist` would be strictly more than the identity needs.  The `Fintype`
carrier of the old statement is no longer needed either: `statDist` is now
support-indexed, so the agreement holds at full generality. -/
theorem delta_eq_statDist {A : Type*} (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) : δ μ ν = statDist μ ν :=
  (statDist_eq_δ_of_nonneg μ ν hν).symm

/-- Thesis Appendix A.1 (proof of Lemma 2.18), the load-bearing identity: for a
transcript value `t̂` consistent with the environment's replies, the system-side
event `{s : tr(s,e) = t̂}` is the **fixed-query** event
`{s : ∀ i, s⊥(x̂¹..x̂ⁱ) = ŷᵢ}` — independent of how the environment chose the
queries.  This is why non-adaptive environments extract the same masses as
adaptive ones.  Alias of `transcript_eq_iff_of_consistent`, named for the
thesis step it implements. -/
theorem fixed_transcript_event_eq_fixed_query_event
    {environment : PFunDDS.DDE X Y} {prefixLength : ℕ}
    {transcriptValue : List (X × Option Y)}
    (environmentConsistent : ∀ k (hk : k < transcriptValue.length),
      environment (PFunDDS.transcriptOutputs (transcriptValue.take k))
        = some (transcriptValue[k].1))
    (lengthConsistent : transcriptValue.length = prefixLength ∨
      (transcriptValue.length < prefixLength ∧
        environment (PFunDDS.transcriptOutputs transcriptValue) = none))
    (system : PFunDDS.DDS X Y) :
    PFunDDS.transcript system environment prefixLength = transcriptValue ↔
      ∀ k (hk : k < transcriptValue.length),
        (PFunDDS.fullyDefined system).1
          (PFunDDS.transcriptInputs (transcriptValue.take (k + 1)))
          = Part.some (transcriptValue[k].2) :=
  transcript_eq_iff_of_consistent environmentConsistent lengthConsistent system

/-- Thesis Lemma 2.18, in the thesis's own **iff** shape: `S ≡ T` if and only
if the transcript distributions agree under all **non-adaptive** deterministic
environments.  The forward direction is the restriction of Def 2.17's
quantifier; the backward direction is
`transcript_equivalent_of_nonadaptive_transcript_equivalent` (proof =
Appendix A.1's fixed-query extraction, `playQueries`).

The thesis states the lemma for two PDS *with the same domain*; here no
common-domain hypothesis appears because the `⊥`-totalized model (Def 2.11
note in the header) makes domains observable through the `none`-answers, so
transcript agreement itself enforces domain agreement. -/
theorem lemma_2_18_nonadaptive_environments_suffice (S T : PFunPDS X Y) :
    Equivalent S T ↔
      ∀ environment : PFunDDS.DDE X Y, NonAdaptive environment →
        ∀ prefixLength : ℕ,
          transcriptDist S environment prefixLength
            = transcriptDist T environment prefixLength := by
  constructor
  · intro equivalent environment _ prefixLength
    exact equivalent environment prefixLength
  · exact transcript_equivalent_of_nonadaptive_transcript_equivalent

/-- Thesis Theorem 2.31, as the thesis states it: for random systems with a
common domain, `Δ(S,T) = Adv(S,T)`, **and** there exist representatives
`S' ∈ [S]`, `T' ∈ [T]` with `δ(S',T') = Δ(S,T)` — the infimum is attained.
The hypotheses (`Fintype X`, one common DDS domain, uniform answered-depth
bound) are the thesis's standing finiteness assumptions from Def 2.9/2.14 made
explicit; the unrestricted strengthening is false
(`papers/notes/RS_SOURCE_CONTRACT.md`).  Packaging of
`class_distance_eq_optimal_advantage_of_finite_common_domain_and_bounded` and
`exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded`. -/
theorem theorem_2_31_distance_eq_advantage_attained
    [Fintype X] {S T : PFunPDS X Y} {D : Set (List X)} {q : ℕ}
    (hS : S.NonNeg) (hT : T.NonNeg)
    (finiteCommonDomain : PFunPDS.HaveCommonDomainAndBounded S T D q) :
    Δ S T = Adv S T ∧
      ∃ S' T' : PFunPDS X Y,
        S'.NonNeg ∧ T'.NonNeg ∧ Equivalent S' S ∧ Equivalent T' T ∧
          (δ S' T' : ℝ) = Δ S T := by
  have distance_eq_advantage :=
    class_distance_eq_optimal_advantage_of_finite_common_domain_and_bounded
      hS hT finiteCommonDomain
  obtain ⟨S', T', hS', hT', equivalentLeft, equivalentRight, -, -, delta_eq⟩ :=
    exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded
      hS hT finiteCommonDomain
  exact ⟨distance_eq_advantage, S', T', hS', hT', equivalentLeft, equivalentRight,
    by rw [delta_eq, distance_eq_advantage]⟩

/-- The transcript law under a **probabilistic** environment (Def 2.15 PDE):
the environment-weighted mixture of the deterministic transcript laws.  This
is the `tr(S, E)` a probabilistic environment induces — affine in the
environment by construction. -/
noncomputable def transcriptDistMixture (S : PFunPDS X Y) (E : PFunPDE X Y)
    (n : ℕ) : Dist (List (X × Option Y)) :=
  E.sum fun environment weight => weight • transcriptDist S environment n

/-- Thesis Definition 2.17's parenthetical, previously only a docstring note
on `Equivalent`: *"considering only deterministic environments results in the
same equivalence notion that is obtained when considering probabilistic
environments."*  Forward: the mixture law is affine in the environment, so
termwise equality transfers.  Backward: a deterministic environment is the
Dirac PDE. -/
theorem definition_2_17_probabilistic_environments_agree (S T : PFunPDS X Y) :
    Equivalent S T ↔
      ∀ (E : PFunPDE X Y) (n : ℕ),
        transcriptDistMixture S E n = transcriptDistMixture T E n := by
  constructor
  · intro hequiv E n
    exact Finsupp.sum_congr fun environment _ => by rw [hequiv environment n]
  · intro hmix environment n
    have hdirac := hmix (Finsupp.single environment 1) n
    unfold transcriptDistMixture at hdirac
    rwa [Finsupp.sum_single_index (by rw [zero_smul]),
      Finsupp.sum_single_index (by rw [zero_smul]), one_smul, one_smul]
      at hdirac

/-- Thesis Theorem 2.32 (**Coupling Theorem for Random Systems**): for two
random systems there are representatives `S' ∈ [S]`, `T' ∈ [T]` and a joint
probability distribution with those marginals whose disagreement probability
is exactly `Adv(S,T)` — the advantage as the probability of a *static* failure
event, decided before any interaction.  Same standing finiteness assumptions
as Theorem 2.31.  Alias of the `RandomSystemCoupling.lean` endpoint, named for
the thesis step. -/
theorem theorem_2_32_coupling_theorem
    [Fintype X] (S T : PFunPDS.Prob X Y) {D : Set (List X)} {q : ℕ}
    (finiteCommonDomain :
      PFunPDS.HaveCommonDomainAndBounded S.val T.val D q) :
    ∃ S' T' : PFunPDS X Y,
      ∃ joint : Dist.ProbDist (PFunDDS.DDS X Y × PFunDDS.DDS X Y),
        Equivalent S' S.val ∧
        Equivalent T' T.val ∧
        Dist.fTransform Prod.fst joint.val = S' ∧
        Dist.fTransform Prod.snd joint.val = T' ∧
        (joint.val.mass (fun pair => pair.1 ≠ pair.2) : ℝ) =
          Adv S.val T.val :=
  exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded
    S T finiteCommonDomain

/-- Thesis Theorem 2.37 (**Winnability Theorem**), in the thesis's own
conjunction shape: for a random game, `ν(S^A) = ω(S^A)` — the supremum
winning probability (Def 2.25) equals the infimum winnability (Def 2.36) —
**and** some representative attains `Pr(winnable) = ω(S^A)`.  This is the
precise sense in which a game with maximal winning probability `δ` is
unwinnable with probability `1 − δ` over the randomness of the game itself,
independent of any strategy.

The attained representative is `Equivalent` (full-transcript equivalence) —
strictly stronger membership than the Def 2.22 class that `ω` quantifies over
(`gameEquivalent_of_equivalent`).  Hypotheses are the thesis's standing
finiteness assumptions (Def 2.9/2.14), the same as Theorem 2.31's; the MC
monotonicity of Def 2.20 is **not needed** (see `GameWinnability.lean`).
Wrapper over `winnability_theorem_of_fixed_domain_and_bounded`, which was
proved by the thesis's own alternative proof (printed p. 26) on top of
Theorem 2.31's attainment.

`hG` is a *restored* hypothesis, not a new one: Def 2.36 takes `ω(S^A)` as an
infimum over the representatives `S^A ∈ 𝐒^A`, and those representatives are
PDS — probability distributions over deterministic systems (Def 2.14), so
non-negativity is part of what membership in the class means.  The `NNReal`
carrier supplied it structurally; the signed `ℝ` carrier has to state it.
`Dist.NonNeg` is the whole requirement — neither `ν` nor `ω` is normalized,
so `isProbDist` would be strictly stronger than Thm 2.37 needs.  The attained
representative is non-negative as well, which the statement now records. -/
theorem theorem_2_37_winnability_theorem
    [Fintype X] {G : PFunPDS X (Y × Bool)} {D : Set (List X)} {q : ℕ}
    (hG : G.NonNeg)
    (finiteDomain : PFunPDS.HasFixedDomain G D) (bounded : QBounded D q) :
    supWinProb G = infWinnability G ∧
      ∃ G' : PFunPDS X (Y × Bool), G'.NonNeg ∧ Equivalent G' G ∧
        G'.mass PFunDDS.Winnable = infWinnability G := by
  obtain ⟨hνω, G', hG'nn, hequiv, hmass⟩ :=
    winnability_theorem_of_fixed_domain_and_bounded hG finiteDomain bounded
  exact ⟨hνω, G', hG'nn, hequiv, by rw [hmass, hνω]⟩

/-! ## Thesis Definition 2.27 — the multi-system distance `Δ(𝒮)`

Statements checked against the scanned original, printed pp. 18–19 (PDF
leaves 28–29).  The carrier-level layer — joint distributions of a tuple of
laws (`IsJointOf`), the agreement event (`agreementMass`), the inner supremum
(`supAgreement`), the pair selector (`selectPair`), the `n`-ary maximal
coupling, and thesis Lemma 2.30 — lives in `MultiSystemCoupling.lean`; this
section renders Def 2.27, Def 2.28's asserted identity, and Theorem 2.29.

**Source erratum (Def 2.27/2.28, sign of the representative quantifier).**
Def 2.27 prints `Δ(𝒮) := 1 − inf_{(S₁,…,Sₙ) ∈ 𝐒₁×⋯×𝐒ₙ} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`
and Def 2.28 prints `Δ(S,T) := inf_{S∈𝐒,T∈𝐓} δ(S,T) = 1 − inf_{(S,T)∈𝐒×𝐓}
sup_ℰ Pr^ℰ(S = T)`.  The inner `inf` over representatives must be a `sup`:
by the classical coupling lemma `sup_ℰ Pr^ℰ(S = T) = 1 − δ(S,T)` for each
representative pair, so the printed second display of Def 2.28 equals
`sup_{(S,T)} δ(S,T)`, not the asserted first display `inf_{(S,T)} δ(S,T)` —
the thesis's own remark below Def 2.28 (V₀/V_{1/2}: equivalent PDS at
`δ = 1`, "taking the infimum seems to be necessary") separates the two, and
the published version (LanMau20, Definition 12) prints only the first
display.  `multiSystemDistance` below is Def 2.27 with the corrected `sup`;
the identification with the repository's `Δ` at a pair
(`definition_2_28_pair_distance_eq_class_distance`) is exactly Def 2.28's
asserted identity and *fails* for the verbatim `inf` rendering.

**This erratum is kernel-checked, not argued.**  The verbatim printed second
display is `printedMultiSystemDistance` below, and
`Example216.definition_2_28_printed_displays_disagree` exhibits the concrete
class pair `𝐒 = 𝐓 = [V]` of thesis Example 2.16 — built from the thesis's own
`V₀` and `V_{1/2}`, whose equivalence and `δ = 1` are themselves proved there —
at which the first display is `0` and the second is `1`.  The corrected reading
agrees at the same pair (`Example216.corrected_display_agrees_at_V`). -/

/-- Thesis Definition 2.27 (with the erratum corrected; see the section
header): the multi-system distance
`Δ(𝒮) = 1 − sup_{representatives} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)` — the thesis
prints `inf` over the representative tuples, which contradicts Def 2.28's
first display and its own V₀/V_{1/2} remark.  As with the repository's `Δ`
and `Adv`, the thesis's standing same-domain and probability assumptions are
left to the theorems that need them rather than baked into the carrier. -/
noncomputable def multiSystemDistance {n : ℕ}
    (S : Fin n → PFunPDS X Y) : ℝ :=
  1 - sSup {a : ℝ | ∃ laws : Fin n → PFunPDS X Y,
    (∀ i, Equivalent (laws i) (S i)) ∧ a = supAgreement laws}

/-- Thesis Definition 2.28's **second printed display**, rendered verbatim:
`1 − inf_{representatives} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`, i.e. `multiSystemDistance`
with the printed `inf` over representative tuples kept instead of corrected to
a `sup`.

This declaration exists only so that the erratum recorded in the section
header above is a *theorem* rather than an argument: Def 2.28 asserts that this
quantity equals its first display `inf_{S∈𝐒,T∈𝐓} δ(S,T)` (the repository's
`Δ`), and `Example216.definition_2_28_printed_displays_disagree` exhibits a
concrete class pair at which the two take the values `1` and `0`.  Nothing
else in the tree may depend on it. -/
noncomputable def printedMultiSystemDistance {n : ℕ}
    (S : Fin n → PFunPDS X Y) : ℝ :=
  1 - sInf {a : ℝ | ∃ laws : Fin n → PFunPDS X Y,
    (∀ i, Equivalent (laws i) (S i)) ∧ a = supAgreement laws}

/-- Def 2.27's outer supremum set is bounded above by the weight of any one
class (all representatives of one class share its weight), so the real
`sSup` is well-behaved.

`hw` is the signed carrier's cost, at its weakest layer.  Note it is *not*
`(S 0).NonNeg`: the representatives `laws` are only known to be `Equivalent`
to `S`, and equivalence transports weight but not non-negativity, so a
pointwise hypothesis on `S` would buy nothing anyway.  What actually saves
the bound is that a *joint* is non-negative by `IsJointOf` (Def 2.27's `ℰ` is
a distribution): every agreement mass in the inner set is then below the
joint's weight, hence below `(laws 0).weight = (S 0).weight`.  When no joint
exists the inner supremum is the empty `sSup = 0`, and `hw` is exactly what
bounds *that* — which is why the hypothesis is on the weight and nothing
stronger. -/
theorem bddAbove_supAgreement_set {n : ℕ} [NeZero n]
    (S : Fin n → PFunPDS X Y) (hw : 0 ≤ (S 0).weight) :
    BddAbove {a : ℝ | ∃ laws : Fin n → PFunPDS X Y,
      (∀ i, Equivalent (laws i) (S i)) ∧ a = supAgreement laws} := by
  refine ⟨((S 0).weight : ℝ), ?_⟩
  rintro a ⟨laws, hlaws, rfl⟩
  refine Real.sSup_le ?_ hw
  rintro b ⟨joint, hjoint, rfl⟩
  exact (Dist.mass_le_weight hjoint.nonNeg _).trans_eq
    ((weight_eq_of_isJointOf hjoint 0).trans
      (weight_eq_of_equivalent (hlaws 0)))

/-- **The trivial inequality of thesis Theorem 2.29** (per pair, which
implies the thesis's `min_{i≠j}` form; no distinctness of `i` and `j` is
needed): every pair's multi-system distance is a lower bound for the
tuple's.  Every representative tuple projects to a representative pair, and
every tuple joint projects to a pair joint with at least the tuple's
agreement.  The pair `(Sᵢ, Sⱼ)` is spelled `selectPair i j S`;
`selectPair_zero` and `selectPair_one` rewrite it to the thesis's
`{Sᵢ, Sⱼ}`.

`hw` is `bddAbove_supAgreement_set`'s hypothesis at the projected pair, whose
zeroth entry is `Sᵢ`: without an upper bound on the pair's supremum set the
real `sSup` collapses to its junk value and the comparison is meaningless. -/
theorem multiSystemDistance_pair_le {n : ℕ} (S : Fin n → PFunPDS X Y)
    (i j : Fin n) (hw : 0 ≤ (S i).weight) :
    multiSystemDistance (selectPair i j S) ≤ multiSystemDistance S := by
  classical
  have hrefl : ∀ L : PFunPDS X Y, Equivalent L L := fun _ _ _ => rfl
  have hwpair : 0 ≤ ((selectPair i j S) 0).weight := hw
  unfold multiSystemDistance
  refine sub_le_sub_left ?_ 1
  have hnonneg : 0 ≤ sSup {a : ℝ | ∃ pairLaws : Fin 2 → PFunPDS X Y,
      (∀ k, Equivalent (pairLaws k) (selectPair i j S k)) ∧
        a = supAgreement pairLaws} :=
    (supAgreement_nonneg (selectPair i j S)).trans
      (le_csSup (bddAbove_supAgreement_set (selectPair i j S) hwpair)
        ⟨selectPair i j S, fun _ => hrefl _, rfl⟩)
  refine Real.sSup_le ?_ hnonneg
  rintro a ⟨laws, hlaws, rfl⟩
  have hequiv : ∀ k, Equivalent (selectPair i j laws k)
      (selectPair i j S k) := by
    intro k
    fin_cases k
    · exact hlaws i
    · exact hlaws j
  exact (supAgreement_le_of_pair_marginals (selectPair i j laws) i j rfl
    rfl).trans (le_csSup (bddAbove_supAgreement_set (selectPair i j S) hwpair)
      ⟨selectPair i j laws, hequiv, rfl⟩)

/-- On the signed carrier a representative tuple need not be non-negative, and
then Def 2.27's inner set is **empty**: `IsJointOf` demands a non-negative
joint (Def 2.27's `ℰ` is a distribution), and the coordinate marginals of a
non-negative joint are non-negative.  The real `sSup` of the empty set is `0`,
so a signed tuple contributes exactly `0` to Def 2.27's outer supremum.

This is why `multiSystemDistance` keeps the thesis's unrestricted quantifier
over representatives even though `Δ` had to restrict its own to non-negative
ones: on the sup side the signed tuples are already inert, so restricting
would change nothing but the statement's fidelity to Def 2.27. -/
theorem supAgreement_eq_zero_of_not_nonNeg {A : Type*} {n : ℕ}
    {laws : Fin n → Dist A} (hsigned : ¬ ∀ i, (laws i).NonNeg) :
    supAgreement laws = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hsigned
  have hempty : {b : ℝ | ∃ joint, IsJointOf joint laws ∧
      b = agreementMass joint} = ∅ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    rintro joint ⟨hjoint, -⟩
    exact hi (IsJointOf.nonNeg_law hjoint i)
  unfold supAgreement
  rw [hempty, Real.sSup_empty]

/-- **Thesis Definition 2.28's asserted identity**: at a pair of probability
classes, Def 2.27's coupling presentation *is* the repository's class
distance `Δ` (Def 2.28's first display, `inf` of `δ` over representatives).
Proof: for every representative pair the inner supremum is exactly
`1 − δ` (`supAgreement_pair_eq_weight_sub_delta`, the classical coupling
lemma via the `n`-ary maximal coupling), so the corrected outer `sup`
complements `Δ`'s `inf`.  No common-domain or finiteness hypotheses are
needed — contrary to what routing through Theorems 2.31/2.32 would impose —
because the identity never mentions `Adv`.

The `isProbDist` hypotheses are the thesis's own ("`𝐒`, `𝐓` are classes of
PDS"), and on the signed carrier they are needed at *both* their conjuncts:
`Dist.NonNeg` because the coupling bridge
(`supAgreement_pair_eq_weight_sub_delta`) is false for signed laws, and
`weight = 1` because the identity's `1 −` normalizes the agreement mass.  So
here — unlike everywhere else in this file — `NonNeg` alone would not do. -/
theorem definition_2_28_pair_distance_eq_class_distance
    {S T : PFunPDS X Y} (hS : S.isProbDist) (hT : T.isProbDist)
    (P : Fin 2 → PFunPDS X Y) (h0 : P 0 = S) (h1 : P 1 = T) :
    multiSystemDistance P = Δ S T := by
  classical
  have hrefl : ∀ L : PFunPDS X Y, Equivalent L L := fun _ _ _ => rfl
  have hSw : S.weight = 1 := hS.2
  have hTw : T.weight = 1 := hT.2
  have hwP : 0 ≤ (P 0).weight := by rw [h0, hSw]; exact zero_le_one
  have hDbdd : BddBelow {a : ℝ | ∃ S' T' : PFunPDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' S ∧ Equivalent T' T ∧ a = (δ S' T' : ℝ)} := by
    refine ⟨0, ?_⟩
    rintro a ⟨S', T', -, -, -, -, rfl⟩
    exact δ_nonneg S' T'
  have hDne : {a : ℝ | ∃ S' T' : PFunPDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' S ∧ Equivalent T' T ∧ a = (δ S' T' : ℝ)}.Nonempty :=
    ⟨(δ S T : ℝ), S, T, hS.1, hT.1, hrefl S, hrefl T, rfl⟩
  -- each *non-negative* representative tuple's inner supremum is `1 − δ` of
  -- its entries; a signed tuple has no joint at all and contributes `0`
  have hsup : ∀ laws : Fin 2 → PFunPDS X Y,
      (∀ k, Equivalent (laws k) (P k)) → (∀ k, (laws k).NonNeg) →
      supAgreement laws = 1 - (δ (laws 0) (laws 1) : ℝ) := by
    intro laws hlaws hnn
    have hw0 : (laws 0).weight = 1 := by
      rw [weight_eq_of_equivalent (hlaws 0), h0, hSw]
    have hw1 : (laws 1).weight = 1 := by
      rw [weight_eq_of_equivalent (hlaws 1), h1, hTw]
    rw [supAgreement_pair_eq_weight_sub_delta laws hnn (by rw [hw1, hw0]), hw0]
  -- `Δ` is below each non-negative representative `δ`, and at most one
  have hΔ_le_delta : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      Equivalent S' S → Equivalent T' T → Δ S T ≤ (δ S' T' : ℝ) := by
    intro S' T' hS'nn hT'nn hS' hT'
    exact csInf_le hDbdd ⟨S', T', hS'nn, hT'nn, hS', hT', rfl⟩
  have hΔle1 : Δ S T ≤ 1 := by
    refine (hΔ_le_delta S T hS.1 hT.1 (hrefl S) (hrefl T)).trans ?_
    have h := δ_le_weight hS.1 hT.1
    rw [hSw] at h
    exact h
  have hkey : sSup {a : ℝ | ∃ laws : Fin 2 → PFunPDS X Y,
      (∀ i, Equivalent (laws i) (P i)) ∧ a = supAgreement laws}
      = 1 - Δ S T := by
    refine le_antisymm (Real.sSup_le ?_ (by linarith)) ?_
    · rintro a ⟨laws, hlaws, rfl⟩
      by_cases hnn : ∀ k, (laws k).NonNeg
      · rw [hsup laws hlaws hnn]
        have hle := hΔ_le_delta (laws 0) (laws 1) (hnn 0) (hnn 1)
          (by rw [← h0]; exact hlaws 0) (by rw [← h1]; exact hlaws 1)
        linarith
      · rw [supAgreement_eq_zero_of_not_nonNeg hnn]
        linarith
    · -- for every representative `δ`, `1 − δ` is an achieved supremum value
      have hstep : 1 - sSup {a : ℝ | ∃ laws : Fin 2 → PFunPDS X Y,
          (∀ i, Equivalent (laws i) (P i)) ∧ a = supAgreement laws}
          ≤ Δ S T := by
        refine le_csInf hDne ?_
        rintro d ⟨S', T', hS'nn, hT'nn, hS', hT', rfl⟩
        set laws : Fin 2 → PFunPDS X Y :=
          fun k => if k = 0 then S' else T' with hlawsdef
        have hlawsP : ∀ k, Equivalent (laws k) (P k) := by
          intro k
          fin_cases k
          · show Equivalent (laws 0) (P 0)
            rw [h0]
            exact hS'
          · show Equivalent (laws 1) (P 1)
            rw [h1]
            exact hT'
        have hlawsnn : ∀ k, (laws k).NonNeg := by
          intro k
          fin_cases k
          · show (laws 0).NonNeg
            exact hS'nn
          · show (laws 1).NonNeg
            exact hT'nn
        have hle : supAgreement laws
            ≤ sSup {a : ℝ | ∃ laws : Fin 2 → PFunPDS X Y,
              (∀ i, Equivalent (laws i) (P i)) ∧ a = supAgreement laws} :=
          le_csSup (bddAbove_supAgreement_set P hwP) ⟨laws, hlawsP, rfl⟩
        rw [hsup laws hlawsP hlawsnn] at hle
        have hentries : (δ (laws 0) (laws 1) : ℝ) = (δ S' T' : ℝ) := rfl
        linarith
      linarith
  unfold multiSystemDistance
  rw [hkey]
  ring

/-- **Thesis Theorem 2.29, the lower bound**, in the repository's `Δ`: each
pairwise class distance is a lower bound for the multi-system distance —
per pair, which implies the thesis's `min_{i≠j}` display
(`theorem_2_29_lower_bound_min_form`).  Composition of
`multiSystemDistance_pair_le` with Def 2.28's identity. -/
theorem theorem_2_29_lower_bound {n : ℕ} {S : Fin n → PFunPDS X Y}
    (hprob : ∀ i, (S i).isProbDist) (i j : Fin n) :
    Δ (S i) (S j) ≤ multiSystemDistance S := by
  have hpair := multiSystemDistance_pair_le S i j
    (by rw [(hprob i).2]; exact zero_le_one)
  rwa [definition_2_28_pair_distance_eq_class_distance (hprob i) (hprob j)
    (selectPair i j S) rfl rfl] at hpair

/-- Thesis Theorem 2.29's lower bound in the thesis's own
`min_{i,j∈[n], i≠j}` display, as an `inf'` over the off-diagonal pairs. -/
theorem theorem_2_29_lower_bound_min_form {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → PFunPDS X Y} (hprob : ∀ i, (S i).isProbDist) :
    ({p : Fin n × Fin n | p.1 ≠ p.2} : Finset (Fin n × Fin n)).inf'
        ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩
        (fun p => Δ (S p.1) (S p.2))
      ≤ multiSystemDistance S := by
  classical
  have hmem : ((⟨0, by omega⟩, ⟨1, by omega⟩) : Fin n × Fin n) ∈
      ({p : Fin n × Fin n | p.1 ≠ p.2} : Finset (Fin n × Fin n)) := by
    simp
  exact (Finset.inf'_le _ hmem).trans (theorem_2_29_lower_bound hprob _ _)

/-- **Thesis Theorem 2.29, the upper bound — in the corrected
`max`-over-pairs form** (attained: some pair `i ≠ j` realizes it): for a
representative tuple of probability laws, with `ℓ` the number of distinct
deterministic systems in their supports,

`Δ(𝒮) ≤ (min(n,ℓ) − 1) · δ(lawsᵢ, lawsⱼ)` for some `i ≠ j`,

hence `Δ(𝒮) ≤ (min(n,ℓ) − 1) · max_{i≠j} δ(lawsᵢ, lawsⱼ)`.  Two departures
from the printed statement, both forced (see `MultiSystemCoupling.lean`'s
header): the printed `min_{i≠j} Δ(Sᵢ,Sⱼ)` on the right is an erratum for a
`max` — Lemma 2.30 controls the *largest* pairwise distance, and the `min`
form is refuted kernel-checked (`printed_min_form_counterexample`); and the
right-hand side carries the chosen representatives' `δ`, quantified over all
representative tuples, because transferring to the pairwise `inf` `Δ(Sᵢ,Sⱼ)`
under a `max` would need one tuple attaining all pairwise infima
simultaneously, which the thesis does not provide (its transfer step is
sound only for the `min` form it misstates).  The thesis's `ℓ` counts the
union over *all* representatives; the per-tuple count here is smaller, so
this bound is at least as strong at every tuple. -/
theorem theorem_2_29_upper_bound {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → PFunPDS X Y} (laws : Fin n → PFunPDS X Y)
    (hlaws : ∀ i, Equivalent (laws i) (S i))
    (hprob : ∀ i, (laws i).isProbDist) :
    ∃ i j : Fin n, i ≠ j ∧
      multiSystemDistance S
        ≤ (((min n (supportUnion laws).card : ℕ) : ℝ) - 1)
            * (δ (laws i) (laws j) : ℝ) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hw : ∀ k, (laws k).weight = 1 := fun k => (hprob k).2
  have hnn : ∀ k, (laws k).NonNeg := fun k => (hprob k).1
  obtain ⟨i, j, hij, hbound⟩ :=
    theorem_2_29_distribution_upper_bound hn laws hprob
  refine ⟨i, j, hij, ?_⟩
  -- the multi-system distance is below this tuple's `1 − supAgreement`
  have hmsd : multiSystemDistance S ≤ 1 - supAgreement laws := by
    unfold multiSystemDistance
    -- the classes `S` are only known through their probability
    -- representatives `laws`, which is exactly what bounds `(S 0).weight`
    have hwS : 0 ≤ (S 0).weight := by
      rw [← weight_eq_of_equivalent (hlaws 0), hw 0]
      exact zero_le_one
    have hle := le_csSup (bddAbove_supAgreement_set S hwS) ⟨laws, hlaws, rfl⟩
    linarith
  -- the pair term is the chosen representatives' `δ`
  have hpairδ : 1 - supAgreement (selectPair i j laws)
      = (δ (laws i) (laws j) : ℝ) := by
    have hnn' : ∀ k, ((selectPair i j laws) k).NonNeg := by
      intro k
      fin_cases k
      · exact hnn i
      · exact hnn j
    have hsup := supAgreement_pair_eq_weight_sub_delta (selectPair i j laws)
      hnn' (by simp only [selectPair_zero, selectPair_one, hw i, hw j])
    simp only [selectPair_zero, selectPair_one, hw i] at hsup
    rw [hsup]
    ring
  rw [hpairδ] at hbound
  exact hmsd.trans hbound

end RandomSystems.CR18.Lanzenberger
