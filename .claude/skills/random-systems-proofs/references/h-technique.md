# The H-technique

## Contents

- It is one lemma, not thirty
- Choosing the analysis
- The obligation nodes per variant
- Routine inputs
- Traps
- Worked exemplars in the tree

---

**The bad thing is a bad transcript.** The most-used family in the library, and the only one
with a complete labelled-spine surface today.

## It is one lemma, not thirty

Five analyses, all specialisations of one general statement:

```
hTechnique_partition   (∀a, (1 − ε_{cell a})·ideal a ≤ real a)  ⟹  δ ≤ Σᵢ εᵢ·Pr[cell = i]
  ├── hTechnique_expectation      cell := the point itself  (pointwise defect ε(a))
  ├── hTechnique_ratio            two cells: bad ↦ 1, good ↦ ε
  │     └── hTechnique_eq_on_good   … with ε = 0 on good
  └── oneSided_hTechnique         one cell: the ratio holds everywhere
```

So the analysis choice is **one question**: how fine a partition, at what defect per cell.

The fifteen user-facing entry points are the product of three orthogonal axes:

```
adv_le_of_ ⟨transcript model⟩ _ ⟨analysis⟩ [_filtered[_of_filter]]

  transcript model : fixedQuery | extended | extFixedQuery | extFixedQueryRep
  analysis         : eq_on_good | ratio_of_good | ratio | expectation | partition
  query filter     : —          | filtered      | filtered_of_filter
```

`extended` is the **extended H-technique** — the transcript carries terminal side
information. It is a transcript *model*, orthogonal to the analysis, so it composes with all
five analyses rather than being a sixth analysis.

**Do not guess a name.** `selectHTechnique : TranscriptModel → Analysis → QueryFilter →
Option Name` returns `none` for combinations the library genuinely lacks — 15 of 60 exist.
Run `#h_grammar` for the matrix. Namespace:
`RandomSystems.CR18.HTechniqueDerivation.adv_le_of_*`, with two in
`RandomSystems.HTechnique.IdealCompression`.

## Choosing the analysis

The library's own selection rule (`ccprover/CCProver/RS/Teaching/OrdinaryH.lean:8-14`):

| use | when |
|---|---|
| **perfect** (`ratio`) | one uniform pointwise ratio holds on **every** transcript |
| **eq_on_good** | the two fixed-query laws **coincide** off an explicit bad event — *try this first* |
| **ratio_of_good** | only a one-sided likelihood ratio is available off the bad event |
| **expectation** | the defect genuinely varies **transcript by transcript** |
| **partition** | the defect genuinely varies **by cell** |

**Take the most special variant that applies.** It has the fewest obligations. Reaching for
`partition` when `eq_on_good` holds manufactures two extra creative goals.

## The obligation nodes per variant

These are your stage-2 DAG nodes. Name your holes exactly these; the names are the shared
vocabulary across the sketch, the plan, and the Lean.

| analysis | endpoint suffix | `[CREATIVE]` nodes |
|---|---|---|
| perfect | `_ratio` | `pointwise_ratio` |
| equality on good | `_eq_on_good` | `good_transcript_equality`, `ideal_bad_probability` |
| ratio on good | `_ratio_of_good` | `good_transcript_ratio`, `ideal_bad_probability` |
| expectation | `_expectation` | `pointwise_defect_ratio`, `ideal_bad_probability`, `ideal_good_defect_expectation` |
| partition | `_partition` | `cell_defect_ratio`, `weighted_cell_bound` |
| extended | `adv_le_of_extended_ratio_of_good` | `extended_good_ratio`, `extended_ideal_bad_probability` (+ 2 routine projection goals) |
| representative | `adv_le_of_extFixedQueryRep_ratio_of_good` | `representative_good_ratio`, `representative_ideal_bad_probability` |

The skeleton, statement-first:

```lean
theorem my_prf_bound … :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T ≤ (δ : ℝ) := by
  refine RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good
    S T Bad δ (by htechnique_total) (by htechnique_total)
    ?good_transcript_equality ?ideal_bad_probability
  case good_transcript_equality => sorry   -- real and ideal agree off Bad
  case ideal_bad_probability    => sorry   -- ideal-world mass of Bad, uniformly over environments
```

Compile the skeleton before filling either hole. **Nothing checks that the goal count is
right** — compare against your stage-2 DAG by eye. If they disagree, the endpoint is not the
one you planned.

> Prior art, **not available here:** `ccprover` has tactic spines (`rs_h_eq_on_good`, …) that
> apply the endpoint *and* assert the residual goal count, plus typed worked examples in
> `CCProver/RS/Teaching/OrdinaryH.lean`. `ccprover` depends on `random-systems`, not the
> reverse, so none of it resolves here. Read it for the label vocabulary; do not plan against
> it.

## Routine inputs

| obligation | discharged by |
|---|---|
| `hS hT : PFunPDS.Prob.KStepTotal _ q` | `cr18_total`, `htechnique_total` |
| `FiniteTranscriptSpace X Y q`, `DiscreteTranscriptSpace X Y q` | `inferInstance` (`abbrev`s for `Fintype`/`DecidableEq` on the transcript prefix, `RandomSystems/CR18Names.lean:37,48`) |
| `hWeight`, `hLeOne` (extended) | `cr18_prob` and friends |
| repeated queries in the query vector | `htechnique_compress`; the underlying fact is `compressedQuery_bound` |
| `advPRF/advPRP/Adv ≤ ε` shell → pointwise | `htechnique_adv_le` |

**Query compression is mathematically a normalisation — but the tactic only applies on the
canonical shapes.** Preprocess an arbitrary query vector to its canonical injective vector of
distinct entries *before* any counting.

Do not read "normalisation" as "free". `htechnique_compress` is a `simp only` over a fixed
rewrite set; off those shapes it does nothing and the normalisation becomes hand work.
Measured: closing an H-technique leaf for CBC-MAC cost ~60 lines, of which the substantive
part was exactly this step done by hand — re-indexing `Fin q` query positions to the
distinct-message subtype, **plus** an inconsistent-answer-vector branch that exists only
because the H-technique quantifies over transcripts *neither system can produce* and which
therefore has no counterpart in the paper.

Budget for it. If your answer vector is `Fin q → X` and the ideal object is indexed by
distinct queries, the re-indexing is yours to write.

## Traps

**Never reverse the ratio.** The endpoint fixes the ideal law on the left and the real law
on the right:

```
(1 - ε) * idealDist t  ≤  realDist t
```

Reversed, it type-checks against nothing and costs an hour.

**`ideal_bad_probability` is universally quantified over environments**, not stated at one
query vector:

```lean
∀ E : QQueryEnvironment X Y q, probBad (…deterministicTranscriptDist T E.val) Bad ≤ δ
```

Bound it uniformly. A per-schedule bound does not discharge it.

**The extended model's two projection goals are routine, not creative.** They say the
extended distribution pushes forward to the plain transcript distribution. If one is hard,
the extension was built wrong.

**Do not close `ideal_bad_probability` by hand.** It is a counting goal — route it through
the union bound (`probBad_iUnion_le`) and see `counting.md`.

## Worked exemplars in the tree

| file | what it demonstrates |
|---|---|
| `RandomSystems/HTechnique/HashThenPRF.lean` | `eq_on_good` — the two worlds coincide exactly off collision |
| `RandomSystems/HTechnique/TweakablePRP.lean` | the ratio trick on `Pr[bad]` itself |
| `RandomSystems/HTechnique/StrongPRP.lean` | strong-PRP totality specialisations |
| `RandomSystems/HTechnique/HCTR2Paper.lean` | paper-parity endpoint over `GF(2^128)` |
| `RandomSystems/HTechnique/IdealCompression.lean` | the `extFixedQueryRep` + filtered variants |
| `RandomSystems/HTechnique/SoP/` | sum-of-permutations, the heaviest counting |
