# Proof Gaps & Issues — Random Systems Formalization

## Status: 3 sorry, 0 custom axioms

Full targeted XoP build succeeds (`RandomSystems.Applications.XoPMayer` and
`RandomSystems.Applications.XoPRank`, 3359 Lake jobs). Only standard Lean axioms
(propext, Classical.choice, Quot.sound) appear in `#print axioms`.

Sorry breakdown:
- 2 original core theory (Theorem 1 inductive step, Amplification general k)
- 0 XoP research-target scaffold obligations — **ALL XoP SORRIES REMOVED**
- 0 condition-based proof technique — **ALL PROVED**
- 1 adaptive cascade application scaffold
- 0 CBC-MAC application (delegates to condition-based framework)

---

## XoP Research Target Scaffold

**File:** `RandomSystems/Applications/XoP.lean`
**Related files:**
- `RandomSystems/Applications/XoPCounting.lean`
- `RandomSystems/Applications/XoPCombinatorics.lean`
- `RandomSystems/Applications/XoPModel.lean`
- `RandomSystems/Applications/XoPAnalytic.lean`
- `RandomSystems/Applications/XoPANOVA.lean`
- `RandomSystems/Applications/XoPMayer.lean`
- `RandomSystems/Applications/XoPRank.lean`
**Theorems:**
- `xop_nonadaptive_security_research_target`
- `xop_adaptive_security_research_target`

**Purpose:** Keep the XoP work theorem-first.  The north-star statements are
`Adv(real, ideal) ≤ bound` and `Adv_adapt(real, ideal) ≤ bound`; lower
mathematical facts are exposed as named obligations rather than hidden in a
local estimate.

**Manager-loop policy:** This is a long-running formalization task, not a
one-shot scaffold.  The loop is not complete until the XoP theorem is fully
proved in Lean with no remaining XoP `sorry`s, no hidden analytic assumptions,
and no unresolved obligations in the chain from the top-level security theorem
down through normalization, density, counting, pair-Mayer/Penrose,
rank/codimension, and visible-defect bounds.  Treat every serious run as a
minimum five-hour push unless the full theorem closes earlier or a precise
mathematical obstruction must be escalated.  Do not report "done" for scaffold,
interface, or planning progress: the accepted endpoint is the full theorem path,
come rain or shine, or a mechanically documented proof of why the stated theorem
must be restated.

**Execution stance for the current campaign:** Push from the top-level theorem
downward, close named obligations in dependency order, and keep dispatching
work until the theorem path is mechanically checked.  A pass may pause only with
the next Lean target, current blocker, verification result, and tracker update
recorded here.

**Reuse-first implementation policy:** For every obligation below, the
implementer must first look for reusable results in Mathlib, the
`random-systems` project, and nearby FV repositories before proving anything
from scratch.  Treat reproving standard combinatorics, algebra, probability, or
finite-sum facts as a last resort.  New proofs should be limited to genuinely
XoP-specific glue, missing bridge lemmas, or theorem-shape adapters.

**Current task tree, top to bottom:**
1. Prove the fixed-input transcript-distance theorem
   `FixedInputTranscriptBound`.
2. Create the concrete counting slice in `XoPCounting.lean`: define the
   theorem-facing normalizer/counting objects that instantiate
   `NormalizedCountingModel`.
3. Prove the normalized density identity `R = Z / E_I[Z]`, with
   `E_I[Z] = (N)_q^2 / N^q` in the concrete XoP model.
4. Establish the density-to-distance bridge
   `TV(real, ideal) = 1/2 E_I |R - 1|`.
5. Build the pair-Mayer/Penrose expansion before any colored-bond atomization.
6. Prove finite-field rank/codimension bounds for fixed connected constraint
   systems.
7. Prove the tilted visible-defect bound under the induced cluster measure; do
   not use raw-product factorization over overlapping supports.
8. Sum the cluster/rank estimates into the analytic sufficiency theorem
   `AnalyticObligationsSuffice`.
9. Wrap the transcript bound with `advantage_le_of_pointwise` or
   `advantageAdaptive_le_of_pointwise`.

**Known-invalid shortcuts:** raw colored-bond KP with per-edge activity `1/N`,
unproved tilted domination by independent defect factors, and weight-`>1`
representatives that do not preserve transcript marginals.

**Status:** Scaffold only, but without XoP `sorry`s.  The research-target
theorems are now conditional theorem spines whose open leaves are explicit
arguments: normalized density, analytic sufficiency, and adaptive transcript
transfer.  The mathematical obligations remain tracked here rather than hidden
as local Lean proof holes.

**Already proved in the scaffold:**
- `statDist_le_of_densityRatioPositiveError`: a normalized density-ratio
  positive-error certificate implies a transcript statistical-distance bound.
- `InjectiveInputs`, `InjectiveInputTranscriptBound`, and
  `nonadaptive_securityOn_injective_from_transcript_bound`: an honest
  restricted `advantageOn` endpoint for the current injective-input XoP path.
- `fixed_transcript_bound_of_densityRatio`: fixed-input density-ratio
  certificates imply `FixedInputTranscriptBound`.
- `densityRatioPositiveError_of_normalizedCounting`,
  `fixed_densityRatio_of_countingDensity`, and
  `fixed_transcript_bound_of_countingDensity`: normalized counting models
  `Z/E[Z]` imply the density-ratio and transcript-distance obligations.
- `xop_nonadaptive_security_from_analytic_obligations`: the non-adaptive
  theorem-composition spine from analytic obligations to `Adv ≤ bound`.
- `xop_adaptive_security_from_adaptive_transcript_bound`: the adaptive wrapper
  from an adaptive transcript bound to `Adv_adapt ≤ bound`.

**Already proved in the counting slice:**
- `Counting.realizesNormalizedCountingModel_of_density_and_positiveError`: a
  reusable constructor that turns a concrete density identity plus analytic
  positive-error estimate into `RealizesNormalizedCountingModel`.
- `Counting.fixed_countingDensity_of_concreteCounting`: concrete compatible
  counts plus a falling-factorial-style normalizer induce the generic
  `FixedInputCountingDensityBound`.
- `Counting.fixed_transcript_bound_of_concreteCounting`: concrete counts feed
  through the normalized-counting and density-ratio wrappers to produce
  `FixedInputTranscriptBound`.

**Already proved in the combinatorics slice:**
- `Combinatorics.CompatibleHiddenState`: a hidden tuple `a` is compatible with
  a visible output tuple `y` when both `a` and `a + y` are injective.
- `Combinatorics.compatibleCountNat` and
  `Combinatorics.compatibleCountNNReal`: raw compatible hidden-state counts.
- `Combinatorics.compatibleHiddenState_zero` and
  `Combinatorics.compatibleHiddenState_one`: zero- and one-query compatibility
  are trivial.
- `Combinatorics.injectiveTupleCount_descFactorial`: the injective hidden-tuple
  count is Mathlib's falling factorial `(N)_q`, via
  `Fintype.card_embedding_eq`.
- `Combinatorics.compatiblePairEquivInjectiveProduct` and
  `Combinatorics.compatiblePair_card`: compatible `(y, a)` pairs are equivalent
  to two injective tuples `(a, b)`, so their total count is `(N)_q^2`.
- `Combinatorics.compatibleHiddenState_add_const`,
  `Combinatorics.compatibleFiberAddConstEquiv`,
  `Combinatorics.compatibleCountNat_add_const`, and
  `Combinatorics.compatibleCountNNReal_add_const`: global visible translation
  preserves compatibility and compatible counts.  This closes the counting
  side of the singleton-marginal leaf without adding a separate
  falling-factorial fiber-count branch.
- `Combinatorics.sum_compatibleCountNat_eq_descFactorial_sq` and
  `Combinatorics.sum_compatibleCountNNReal_eq_descFactorial_sq`: the raw sum
  over visible outputs satisfies `∑_y Z(y) = (N)_q^2`.
- `Combinatorics.idealCompatibleExpectation_eq_descFactorial_sq_div_pow`: the
  uniform visible-output average satisfies `E_y[Z(y)] = (N)_q^2 / N^q`.
- `Combinatorics.compatibleExpectationNormalizer` and
  `Combinatorics.compatibleCountWithExpectationNormalizer`: the corrected
  theorem-facing normalizer package is available under the explicit domain
  assumption `q ≤ N`.
- `Combinatorics.compatibleCount`: a raw `CompatibleCount` package whose `Z`
  reads the output component of the transcript.

**Already proved in the model slice:**
- `Model.xopDDS`: deterministic XoP system induced by two permutations.
- `Model.xopRealPDS`: real XoP PDS as the pushforward of the uniform pair of
  permutations.
- `Model.xopIdealPDS`: ideal PDS using the existing stateless uniform random
  function `Instances.URFfun`.
- `Model.xopReal_isProbPDS` and `Model.xopIdeal_isProbPDS`: both concrete
  systems are probability systems.
- `Model.compatibleHiddenState_xopDDS`: for injective fixed inputs, the
  `π₁` hidden tuple is compatible with the visible XoP output tuple.
- `Model.xopIdeal_output_uniform`: on injective fixed inputs, the ideal
  `URFfun` output vector is uniform, reusing
  `Instances.eval_nonces_uniform`.
- `Model.xopIdeal_transcriptDist_eq_uniform_outputs`: the ideal fixed-input
  transcript law factors through uniform output vectors and the fixed-input
  transcript embedding.
- `Model.xopIdeal_transcriptDist_transcriptEmbed_apply`: ideal embedded
  fixed-input transcript probabilities are uniform.
- `Model.transcriptDist_eq_output_pushforward`: any fixed-input transcript law
  factors through its output-vector law.
- `Model.xopReal_outputDist_eq_pair_pushforward`: the real output-vector law is
  reduced to the uniform permutation-pair pushforward.
- `Model.outputMap_xopDDS`, `Model.output_eq_iff_hiddenTuple`,
  `Model.outputFiber`, `Model.permFiber`, `Model.compatibleFiber`,
  `Model.namedPermFiber_card`, and `Model.compatibleFiber_card_named`: the real
  output-fiber count has been reduced to named finite fibers and the reusable
  `card_perm_fiber` lemma.
- `Model.outputFiberEquivCompatibleSigma`: real output fibers are equivalent to
  a compatible hidden tuple plus two permutation-extension fibers.
- `Model.real_xop_output_fiber_count`: the real output-fiber cardinality is
  exactly `Z(y) * ((N - q)!)^2` for injective fixed inputs.
- `Model.real_xop_outputDist_apply`: the real fixed-input output-vector
  probability at `y` is the exact output-fiber count divided by the number of
  permutation pairs, using `Dist.fTransform_uniform_apply`.  This is still an
  injective-input theorem; a repeated-query reduction or injective-input
  theorem endpoint is required before it can close the theorem-facing
  `FixedInputTranscriptBound`.
- `Model.real_xop_transcriptDist_transcriptEmbed_apply`: the real fixed-input
  transcript probability at an embedded transcript is the corresponding output
  probability, again on injective inputs.
- `Model.real_xop_outputDist_apply_descFactorial` and
  `Model.real_xop_transcriptDist_transcriptEmbed_apply_descFactorial`: the real
  output/transcript probabilities are normalized by `(N)_q^2`.
- `Model.real_eq_density_mul_ideal_transcriptEmbed_descPow`: the embedded
  transcript density identity is proved with the corrected normalizer
  `(N)_q^2/N^q`, on injective inputs.
- `Model.fTransform_transcriptEmbed_eq_zero_of_not_image`: off-image
  transcripts have zero mass under any output-vector law pushed through
  `transcriptEmbed`.
- `Model.real_eq_density_mul_ideal_transcript`: the full fixed-input transcript
  density identity `real = (Z/E_I[Z]) * ideal` is proved for injective input
  sequences, including off-image transcripts.
- `Model.realizes_xop_compatibleCount_of_positiveError`: the concrete corrected
  compatible-count package realizes the generic normalized-counting model once
  the analytic positive-error bound is supplied.
- `Model.positiveError_transcriptEmbed_pushforward_eq_visible`,
  `Model.positiveError_idealTranscript_eq_visible`, and
  `Model.positiveError_xop_compatibleCount_eq_visible`: transcript-level
  positive-error sums reduce to visible-output sums, disposing of off-image
  transcripts explicitly.
- `Model.realizes_xop_compatibleCount_of_visible_positiveError`: a visible-tuple
  analytic positive-error estimate is enough to instantiate the concrete
  normalized-counting model on the injective-input path.
- `Model.xop_advantageOn_injective_of_visible_positiveError`: the current
  theorem-composition spine is closed up to the visible-output positive-error
  estimate; proving that estimate for all injective inputs gives the restricted
  non-adaptive XoP advantage bound.
- `Model.visiblePositiveError_xop_compatibleCount_eq_count` and
  `Model.xop_advantageOn_injective_of_pure_visible_positiveError`: the remaining
  restricted theorem is now reduced to a pure visible-tuple positive-error
  estimate, independent of the fixed input sequence.
- `Model.idealEmbeddedExpectation_eq_descFactorial_sq_div_pow`: the embedded
  output-vector form of `E_I[Z]` equals `(N)_q^2 / N^q`.
- `Model.xopIdeal_compatibleExpectation_eq_descFactorial_sq_div_pow`: the full
  fixed-input ideal transcript expectation of `Z` equals `(N)_q^2 / N^q` for
  injective inputs.
- `Dist.fTransform_sum_mul`: generic reusable pushforward-expectation bridge.
- `Analytic.pureVisiblePositiveError`, the pure visible positive-error
  expression left by the model bridge.
- `Analytic.xop_advantageOn_injective_of_pureVisiblePositiveError`: general
  wrapper from a bound on `pureVisiblePositiveError q` to the concrete
  injective-input restricted XoP `advantageOn` theorem.
- `Analytic.pureVisiblePositiveError_zero` and
  `Analytic.pureVisiblePositiveError_one`: the zero-query and one-query
  visible analytic base cases are fully proved.
- `Analytic.compatibleFinTwoDiffEquiv`: for two queries, compatible hidden
  states are equivalent to a first hidden value plus a nonzero difference that
  avoids the visible collision constraint.
- `Analytic.compatibleCountNat_two_eq_of_eq`,
  `Analytic.compatibleCountNat_two_eq_of_ne`, and their `NNReal` versions:
  the exact compatible counts are proved for repeated and distinct visible
  two-query outputs.
- `Analytic.pureVisiblePositiveError_two_summand_eq_of_eq`,
  `Analytic.pureVisiblePositiveError_two_summand_eq_of_ne`, and
  `Analytic.pureVisiblePositiveError_two`: the exact two-query pure visible
  positive-error expression is proved:
  `pureVisiblePositiveError 2 = 1 / (N * (N - 1))` under `2 ≤ N`.
- `Analytic.pureVisiblePositiveError_two_le_quadratic`: the exact q=2
  expression is packaged as the theorem-facing bound
  `pureVisiblePositiveError 2 ≤ 2^2 / N^2`.
- `Analytic.xop_advantageOn_injective_two_le_quadratic`: the q=2 pure-visible
  bound has been routed through the concrete model bridge to an injective-input
  restricted `advantageOn` theorem.
- `ANOVA.coordinates`, `ANOVA.restrictTuple`, `ANOVA.uniformAverage`,
  `ANOVA.conditionalAverage`, `ANOVA.visibleDensityRatioReal`, and
  `ANOVA.visibleDensityErrorReal`: the first finite-product ANOVA scaffold
  definitions are in place over `ℝ`, separating signed decomposition work from
  the `NNReal` counting/probability bridge.
- `ANOVA.project`, `ANOVA.anovaComponent`, `ANOVA.visibleL1`, and
  `ANOVA.xopError`: the explicit projection/component/L1 API for XOP-DAG-10 is
  now in Lean.  The projection base API is now proved: `project_apply`,
  `restrictTuple_coordinates_eq_iff`, `project_eq_of_restrictTuple_eq`,
  `project_of_restrict`, `project_idempotent(_apply)`, `project_empty`,
  `project_full`, `project_const`, `project_add`, `project_sub`,
  `restrictTupleOfSubset`, `subsetFiberFiberEquiv`,
  `sum_project_fiber_of_subset`, `conditionalAverage_project_of_subset`, and
  `project_project_of_subset`.
- `ANOVA.anovaComponent_empty(_apply)` and `ANOVA.anovaComponent_singleton`:
  the zero- and one-coordinate Möbius components have been computed explicitly,
  giving the first checked leaves of the finite Hoeffding decomposition.
- `ANOVA.anovaComponent_reconstruction_apply` and
  `ANOVA.anovaComponent_reconstruction`: the finite Boolean-lattice Möbius
  reconstruction is proved in Lean.  For every real-valued visible function
  `f`, summing all components over `(coordinates q).powerset` reconstructs
  `f` pointwise.
- `ANOVA.xopError_anova_reconstruction(_apply)`: the reconstruction theorem is
  specialized to the current real-valued XoP visible density error.
- `ANOVA.visibleL1_sum_le`, `ANOVA.visibleL1_anova_sum_bound`, and
  `ANOVA.visibleL1_xopError_anova_sum_bound`: the finite `L¹` triangle bridge
  is proved.  Thus component `visibleL1` estimates now formally imply a global
  signed-real `visibleL1` estimate for `xopError`.
- `ANOVA.abs_project_le_project_abs`,
  `ANOVA.visibleL1_project_le`,
  `ANOVA.visibleL1_const_mul`, and
  `ANOVA.visibleL1_anovaComponent_le_card_powerset_mul_visibleL1`: the generic
  finite-product conditional-expectation infrastructure now proves that
  projections are `L¹` contractions and that one ANOVA component is bounded by
  a powerset-size triangle factor times the underlying function's `L¹` norm.
  This is only a crude theorem-spine reduction; it does not replace the
  source-specific XoP activity estimate.
- `ANOVA.uniformAverage_project`: finite conditional projections preserve the
  global uniform average.
- `ANOVA.uniformAverage_anovaComponent_eq_zero_of_nonempty`: every nonempty
  ANOVA component has zero global uniform mean.
- `ANOVA.projectionIrrelevance`: product-space projection irrelevance is now
  proved.  If a real-valued visible function depends only on coordinates `U`,
  then conditioning on an additional coordinate `x ∉ U` does not change its
  projection.  The proof reuses `Fintype.sum_equiv`, `Fintype.card_congr`,
  `Fintype.sum_prod_type`, and a concrete fiber equivalence splitting a
  `T`-fiber as `G ×` an `(insert x T)`-fiber.
- `ANOVA.anovaComponent_eq_zero_of_insert_project_eq` and
  `ANOVA.anovaComponent_eq_zero_of_restrict_invariant_of_not_subset`: the
  Boolean-lattice off-support cancellation is proved generically.  If an ANOVA
  support `S` contains a coordinate outside a function's support `U`, then the
  `S` component is exactly zero.
- `ANOVA.visibleNormalizerNNReal_ne_zero` and
  `ANOVA.visibleDensityRatioReal_eq`: the corrected visible normalizer is named
  and its nonzero side condition is exposed under `q ≤ Fintype.card G`.
- `ANOVA.pureVisiblePositiveError_toReal_le_visibleL1_xopError`: the existing
  `NNReal` pure visible positive-error expression is bounded, after coercion
  to `ℝ`, by the signed-real `visibleL1` norm of `xopError`.  This closes the
  generic signed-real to positive-error inequality; remaining work is to package
  it into the exact `NNReal ≤ ε` shape used by the advantage theorem.
- `ANOVA.pureVisiblePositiveError_le_of_visibleL1_xopError_le` and
  `ANOVA.pureVisiblePositiveError_le_of_anova_l1_sum_le`: the bridge is now
  packaged in the exact downstream `NNReal ≤ ε` shape.  A real-valued component
  L1 estimate over all ANOVA components now implies the existing
  `Analytic.pureVisiblePositiveError q ≤ ε` obligation.
- `ANOVA.XoPComponentL1Bound` and
  `ANOVA.pureVisiblePositiveError_le_of_componentL1Bound`: the ANOVA file now
  names the exact component-level analytic obligation that pair-Mayer/rank
  estimates must prove.
- `ANOVA.xop_advantageOn_injective_of_componentL1Bound`: the named component
  L1 obligation now implies the concrete injective-input `advantageOn ≤ ε`
  theorem through the existing model and analytic bridges.
- `ANOVA.ComponentActivityBound`,
  `ANOVA.componentL1Bound_of_activity_sum`, and
  `ANOVA.xop_advantageOn_injective_of_activity_sum`: pair-Mayer/rank work now
  has a precise plug-in interface.  It suffices to prove a per-component
  activity bound depending on `S.card` and then sum those activities.
- `Mayer.PairEdge`, `Mayer.pairBad`, `Mayer.pairGood`, and
  `Mayer.pairMayerFactor`: the pair-level XoP Mayer objects are now named
  before any colored-bond atomization.
- `Mayer.pairBadHidden`, `Mayer.pairBadShifted`, and
  `Mayer.pairMayerFactor_atomized`: the pair-level factor can now be atomized as
  hidden-collision plus shifted-collision minus their overlap, but only after
  the pair-level Mayer expansion boundary.
- `Mayer.pairGood_coordinates_iff_compatibleHiddenState`: full-coordinate
  pair noncollision is proved equivalent to the existing compatible hidden-state
  predicate.
- `Mayer.pairMayer_product_eq_indicator` and
  `Mayer.pairMayer_product_expand`: the finite pair product is proved to be the
  all-pairs-good indicator and expanded as a finite powerset Mayer sum.
- `Mayer.pairFamilyTerm`, `Mayer.pairPartition_eq_sum_pairFamilyTerm`,
  `Mayer.normalizedPairFamilyTerm`, and
  `Mayer.xopError_eq_normalized_pairFamily_sum_sub_one`: the raw pair-Mayer
  partition is now also exposed as an explicit all-edge-family expansion of the
  visible density error.
- `Mayer.anovaComponent_xopError_eq_normalized_pairFamily_sum_sub_one`: each
  ANOVA component can now be rewritten to act on the all-edge-family Mayer
  expansion, which is the algebraic boundary before connected resummation.
- `Mayer.pairMayerFactor_eq_of_eq_on_edge` and
  `Mayer.pairFamilyTerm_eq_of_eq_on_edgeVertices`/
  `Mayer.normalizedPairFamilyTerm_eq_of_eq_on_edgeVertices`: edge-family terms
  are proved to depend only on the visible coordinates touched by their edges,
  a support lemma needed for off-support ANOVA vanishing.
- `Mayer.restrictInvariant_normalizedPairFamilyTerm` and
  `Mayer.anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'`: the
  off-support vanishing lemma is now instantiated for every normalized pair-edge
  family term using the proved product-space projection irrelevance theorem.
- `ANOVA.project_eq_self_of_restrict_invariant` and
  `ANOVA.project_eq_self_of_restrict_invariant_of_subset` plus
  `Mayer.project_edgeVertices_normalizedPairFamilyTerm`/
  `Mayer.project_superset_normalizedPairFamilyTerm`: invariant functions are
  fixed by projection to their support or any support superset; normalized
  edge-family terms are fixed by projection to `edgeVertices` and its supersets.
- `ANOVA.project_finset_sum` and `ANOVA.anovaComponent_finset_sum`: projections
  and ANOVA components are now linear over finite sums, enabling termwise
  estimates for the all-edge-family Mayer expansion.
- `ANOVA.anovaComponent_const_of_nonempty`,
  `ANOVA.anovaComponent_sub_const_of_nonempty`, and
  `Mayer.anovaComponent_xopError_eq_normalized_pairFamily_sum_of_nonempty`: for
  nonempty supports, the constant `-1` part of `R - 1` vanishes from the ANOVA
  component, leaving only the normalized pair-family Mayer sum.
- `Mayer.anovaComponent_xopError_eq_sum_edgeFamily_components_of_nonempty`: for
  nonempty supports, the XoP component is now a finite sum of individual
  normalized edge-family ANOVA components.
- `Mayer.EdgeFamilyComponentActivityBound` and
  `Mayer.nonempty_componentActivity_of_edgeFamilyActivity`: a termwise
  edge-family `L1` estimate now implies the component activity bound for each
  nonempty support.
- `Mayer.CoveringEdgeFamilyComponentActivityBound` and
  `Mayer.edgeFamilyActivity_of_coveringEdgeFamilyActivity`: edge-family
  activity estimates may now be restricted to families satisfying
  `S ⊆ edgeVertices Γ`, since all non-covering families have zero component.
- `Mayer.pairPartition_coordinates_eq_compatibleCountNNReal` and
  `Mayer.visibleDensityRatioReal_eq_pairPartition`: the pair-Mayer partition is
  proved to be the same numerator used by the existing visible density ratio.
- `Mayer.edgeVertices`, `Mayer.edgeLinked`, `Mayer.PairConnected`,
  `Mayer.PairCluster`, and `Mayer.rawClusterContribution`: connected pair
  clusters and a raw normalized product contribution candidate are now named.
- `Mayer.edgeVertices_card_ge_two_of_mem`,
  `Mayer.pairCluster_edges_nonempty_of_support_nonempty`, and
  `Mayer.pairCluster_support_card_ge_two_of_nonempty`: basic support-cardinality
  facts for pair clusters are proved.  In particular, a nonempty pair-cluster
  support has at least two vertices.
- `Mayer.edgeLinked_symm`: the pair-family adjacency relation is symmetric,
  preparing the later bridge to Mathlib `SimpleGraph` connectivity/tree
  lemmas.
- `Mayer.PairClusterExpansion`, `Mayer.PairClusterActivityBound`, and
  `Mayer.componentActivityBound_of_pairClusterActivity`: the remaining
  Penrose/tree-graph stage has an explicit contribution-family parameter and a
  proved handoff into `ANOVA.ComponentActivityBound`.  This avoids incorrectly
  assuming that raw connected products are already the final cumulant/Penrose
  contributions.
- `Mayer.xop_advantageOn_injective_of_pairClusterActivity`: the connected
  pair-cluster route now has a theorem-level endpoint into the concrete
  injective-input XoP advantage bound.
- `Mayer.PairClusterChargeBound`,
  `Mayer.componentL1Bound_of_pairClusterExpansion_charge`, and
  `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_charge`: the
  pair-cluster endpoint now also accepts support-indexed per-cluster charges.
  This is the non-vacuous handoff that rank/codimension estimates should feed
  before the final tree-graph summability step collapses charges to a closed
  cardinality-only activity.
- `Mayer.PairClusterChargeLayer`, `Mayer.pairClusterCharge_sum_by_card`,
  `Mayer.PairTree`, `Mayer.PairTreeChargeLayer`,
  `Mayer.pairTreeCharge_sum_by_card`, and the corresponding layer/tree
  endpoints: the Penrose summability branch is now represented in the theorem
  DAG without raw connected-graph enumeration.  The implementation reuses
  Mathlib's `Finset.sum_powerset`/`powersetCard` decomposition and
  `SimpleGraph.IsTree`; the remaining new mathematics is exactly the Penrose
  tree-charge inequality and the closed-form tree-layer estimate.
- `Mayer.pairTreeChargeLayer_le_choose_mul` and
  `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_localActivity`:
  a local per-support tree estimate now feeds the theorem through the standard
  binomial support count `choose`.  This reuses Mathlib's
  `Finset.card_powersetCard`, so the remaining summability proof only has to
  provide the local activity and the scalar binomial sum.
- `Mayer.pairTree_natCard_edgeSet_add_one` and
  `Mayer.pairTree_natCard_edgeSet_add_one_eq_card`: the Mathlib tree edge-count
  theorem is now specialized to `PairTree`, using
  `SimpleGraph.isTree_iff_connected_and_card`.  This is the local fact the
  Penrose activity estimate should use for any `k - 1` tree-edge exponent.
- `Mayer.pairClusterGraph`, `Mayer.pairClusterGraph_connected`,
  `Mayer.PairTreeSubcluster`, and `Mayer.exists_pairCluster_spanningTree`: a
  nonempty pair cluster now has a Mathlib spanning tree contained in its
  cluster graph, using `SimpleGraph.Connected.exists_isTree_le`.  This is the
  formal selector-existence bridge needed before proving Penrose tree-fiber
  domination; the empty-support case remains a separate harmless/support
  convention leaf.
- `Mayer.sum_range_choose_mul_pow_eq_add_pow`: the scalar binomial identity
  `∑_k binom(n,k) a^k = (1+a)^n` is proved for `ℝ`, reusing Mathlib's
  powerset expansion and `sum_powerset_apply_card`.  This is the support-size
  summability simplifier for geometric local activities.
- `Rank.AtomColor`, `Rank.Atom`, `Rank.atomHolds`, `Rank.hiddenAtom`,
  `Rank.shiftedAtom`, and `Rank.pairBad_iff_exists_atomHolds`: XOP-DAG-12 now
  has typed colored-atom inputs after the pair-Mayer boundary.  The file also
  defines `Rank.atomVertices` and proves atom vertices stay inside the parent
  pair support.
- `Rank.edgeDifferenceLinearForm`, `Rank.atomLinearForm`, `Rank.atomRhs`, and
  `Rank.atomHolds_iff_linearForm_eq`: every hidden/shifted atom is now expressed
  as an affine linear equation over a finite-field carrier.  This records the
  necessary strengthening from arbitrary finite additive groups to vector spaces
  over a field for rank/codimension arguments.
- `Rank.hiddenConstraintMap`, `Rank.visibleRhsMap`, and
  `Rank.all_atomHolds_iff_hiddenConstraintMap_eq_visibleRhsMap`: finite atom row
  families are packaged as one vector linear equation.
- `Rank.visibleObstructionMap` and
  `Rank.exists_hidden_solution_iff_visibleObstruction_eq_zero`: fixed-visible
  hidden feasibility is now characterized by vanishing in the quotient by the
  hidden row-space.  This is the Lean bridge for the future visible-defect rank.
- `Rank.hiddenRank`, `Rank.visibleObstructionRank`, `Rank.jointConstraintMap`,
  and `Rank.jointRank`: the rank quantities for XOP-DAG-12 are now named in
  Lean using `Module.finrank`.
- `Rank.atomFamilyHolds_iff_jointConstraintMap_eq_zero` and
  `Rank.atomFamily_joint_card_eq_pow`: the fixed-bond codimension parent
  theorem is now proved for selected atom families.  It reuses Mathlib's
  `Module.card_eq_pow_finrank`, `LinearMap.finrank_range_add_finrank_ker`,
  `Module.finrank_prod`, and the existing finite-function-space finrank
  simplification; the new work is only the XoP-specific bridge from
  atom-family satisfaction to the joint kernel event.
- `Rank.jointRank_le_two_mul_q`,
  `Rank.atomFamily_joint_card_density_eq_pow_div_pow`, and
  `Rank.atomFamily_joint_card_density_eq_inv_pow`: the fixed atom-family
  codimension count is now normalized to the exact uniform joint probability
  mass `|K|^{-jointRank}`.
- `Rank.atomLinearForm_mem_hidden_dualMap_range`,
  `Rank.finrank_span_atomLinearForms_le_hiddenRank`,
  `Rank.atomLinked`,
  `Rank.edgeDifference_mem_span_atomLinearForms_of_reachable`,
  `Rank.starEdgeDifference_linearIndependent`, and
  `Rank.hiddenRank_atomFamilyRow_ge_card_sub_one_of_root_reaches`: the
  connected hidden-rank lower bound is proved in the root-reachability form
  needed by the tree/cluster route.  The row-rank bridge reuses Mathlib's
  `LinearMap.finrank_range_dualMap_eq_finrank_range`; the new work is the
  XoP-specific path telescoping and star-edge independence.
- `Rank.HasVisibleObstruction`,
  `Rank.visibleObstructionRank_pos_of_hasVisibleObstruction`, and
  `Rank.jointRank_atomFamilyRow_ge_card_of_root_reaches_and_visibleObstruction`:
  the algebraic visible-defect and combined-codimension leaves are proved.
  What remains is the Penrose/cluster semantic bridge showing that every
  surviving nonconstant cluster yields `HasVisibleObstruction`; the rank algebra
  no longer carries that gap.
- `Rank.hiddenAtomLinked`, `Rank.hiddenAtomReachable_eq_of_atomFamilyHolds`, and
  `Rank.hasVisibleObstruction_of_shiftedAtom_hiddenReachable`: the first
  concrete mixed-cycle bridge is proved.  A shifted atom whose endpoints are
  already connected by hidden atoms forces a nonzero visible obstruction.
- `Rank.hasVisibleObstruction_of_leftKernel_rhs_ne`: a general left-kernel
  visible-defect certificate is proved.  This is the theorem shape a colored
  cycle/Penrose survival argument should target: hidden rows cancel, but their
  visible RHS combination is nonzero for some visible tuple.
- `Rank.atomFamily_joint_card_density_le_inv_pow_of_jointRank_ge` and
  `Rank.atomFamily_joint_card_density_le_inv_pow_card_of_root_reaches_and_visibleObstruction`:
  the exact joint-count formula is now available in the inequality form needed
  by cluster estimates, giving `|K|^{-|V|}` from connectedness plus visible
  obstruction.
- `Rank.pairFamilyFullAtoms`,
  `Rank.atomVertices_pairFamilyFullAtoms`,
  `Rank.reachable_edgeLinked_to_atomLinked_pairFamilyFullAtoms`,
  `Rank.hasVisibleObstruction_pairFamilyFullAtoms_of_nonempty`, and
  `Rank.pairFamilyFullAtoms_density_le_inv_pow_edgeVertices_of_connected_nonempty`:
  connected nonempty pair-edge families now have a concrete post-Penrose
  full-atomization bridge into the rank/codimension API, with touched vertices
  preserved and normalized mass bounded by `|K|^{-|edgeVertices Γ|}`.
- `Rank.pairFamilyFullAtomsJointDensity`,
  `Rank.fullAtomizedPairClusterCharge`,
  `Rank.PairClusterFullAtomizedDensityChargeBound`, and
  `Rank.pairClusterChargeBound_of_fullAtomizedDensityChargeBound`: exact
  full-atomized density charges now feed the generic
  `Mayer.PairClusterChargeBound` interface with simple charge `|K|^{-|S|}`.
- `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge`:
  the current connected-cluster/rank route now has an end-to-end injective-input
  advantage endpoint.  The only remaining hypotheses on that endpoint are the
  genuine Penrose cluster expansion, exact domination of each cluster
  contribution by its full-atomized density, and total summability of the simple
  full-atomized charges.
- `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_layers`,
  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree`,
  and
  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_layers`:
  the same rank endpoint now accepts support-size layer summability and an
  explicit Penrose tree-charge handoff.  This records the correct next target:
  prove tree domination and sum tree layers, not raw connected pair clusters.
- `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_localActivity`:
  the rank/codimension route now reaches the scalar binomial-sum endpoint:
  Penrose tree domination plus a local support-size tree activity estimate plus
  `∑_k binom(q,k) activity(k) ≤ ε`.
- `Rank.fullAtomizedPairClusterCharge_htree_of_treeFiberBound`: once a
  spanning-tree selector is chosen, per-tree fiber charge bounds imply the
  `htree` hypothesis consumed by the tree-local-activity endpoint.  This uses
  Mathlib's finite-sum fiberwise decomposition instead of enumerating raw
  connected graphs.
- `ANOVA.uniformAverage_visibleDensityRatioReal_eq_one`,
  `ANOVA.uniformAverage_xopError_eq_zero`, and
  `ANOVA.visibleL1_anovaComponent_empty_xopError`: the empty ANOVA component of
  `xopError` is now proved to vanish under the theorem-facing domain condition
  `q ≤ |G|`.  The proof reuses the existing compatible-count expectation
  theorem rather than reproving any finite counting identity.
- `Mayer.componentL1Bound_of_pairClusterExpansion_charge_nonempty`,
  `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_charge_nonempty`,
  `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty`,
  and
  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_nonempty`:
  the tree route now has a checked nonempty-support endpoint with an explicit
  empty-component-zero premise.  This is the theorem path to use while
  resolving the `PairTree ∅` obstruction.
- `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_of_domain`
  and
  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_tree_nonempty_of_domain`:
  the nonempty tree route now discharges the empty-component premise directly
  from `q ≤ |G|`.
- `Mayer.pairClusterSpanningTree`,
  `Mayer.pairClusterSpanningTree_subcluster`,
  `Rank.fullAtomizedPairClusterCharge_htree_nonempty_of_treeFiberBound`, and
  `Rank.fullAtomizedPairClusterCharge_htree_nonempty_of_spanningTreeFiberBound`:
  the Penrose route now has a concrete nonempty spanning-tree selector and a
  selected-tree fiber handoff.  The remaining tree estimate should target the
  selected-tree fiber bound directly.
- `Rank.selectedSpanningTreeFiberCharge`,
  `Rank.fullAtomizedPairClusterCharge_selectedSpanningTreeFiber_le`,
  `Rank.fullAtomizedPairClusterCharge_htree_nonempty_selectedSpanningTreeFiberCharge`,
  `Mayer.nonemptySupportActivity_sum_by_card`,
  `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_of_domain`,
  `Mayer.xop_advantageOn_injective_of_pairClusterExpansion_treeCharge_nonempty_localActivity_cardSum_of_domain`,
  `Mayer.PairClusterPenroseTreeActivityBound`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity`,
  `Mayer.pairCluster_sum_eq_zero_of_nonempty_card_lt_two`,
	  `Mayer.PairClusterPenroseActivityBoundGeTwo`,
	  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_Ico`,
	  `Mayer.PairClusterExpansionGeTwo`,
	  `Mayer.PairClusterPenroseActivityBoundGeTwoOnly`,
	  `Mayer.pairClusterPenroseActivityBoundGeTwoOnly_of_full`,
	  `Mayer.pairClusterPenroseActivityBoundGeTwoOnly_of_selectedContributionFiberBound`,
	  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseActivityGeTwoOnly_Ico`,
	  `Mayer.sum_range_if_ge_two_eq_Ico`,
	  `Mayer.sum_Ico_choose_mul_le_of_activity_le`,
	  `Mayer.sum_Ico_choose_mul_pow_le_add_pow`,
  `Mayer.sum_range_if_lt_two_choose_mul_pow`,
  `Mayer.sum_Ico_choose_mul_pow_add_low_eq_add_pow`,
  `Mayer.sum_Ico_choose_mul_pow_eq_add_pow_sub_low`,
  `Mayer.choose_mul_pow_le_mul_pow`,
  `Mayer.sum_Ico_choose_mul_pow_le_sum_Ico_mul_pow`,
  `Mayer.sum_Ico_choose_mul_pow_le_geom_tail`,
  `Mayer.sum_Ico_choose_mul_pow_le_two_mul_sq`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_Ico_of_activity_le`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_pow_small_q_toNNReal`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_card_scaled`,
  `Mayer.xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_card_scaled_quadratic`,
  `Mayer.componentL1Bound_of_edgeFamilyActivity_nonempty`,
  `Mayer.componentL1Bound_of_coveringEdgeFamilyActivity`, and
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity`,
  `Mayer.componentL1Bound_of_coveringEdgeFamilyActivity_ge_two`, and
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two`,
  `Mayer.geTwoSupportActivity_sum_by_card`, and
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum`,
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum_of_singletonDensity`,
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity_ge_two_cardSum_uniformSingleton`,
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small`,
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamilyActivity_pow_small_q`,
  `Mayer.CoveringEdgeFamilyComponentActivityBoundGeTwo`,
  `Mayer.coveringEdgeFamilyActivityGeTwo_of_termwise_bound`,
  `Mayer.nonempty_componentActivity_of_coveringEdgeFamilyActivityGeTwo`,
  `Mayer.componentL1Bound_of_coveringEdgeFamilyActivityGeTwo`,
  `Mayer.xop_advantageOn_injective_of_coveringEdgeFamily_geTwo_termwiseBudget_pow_small_q`,
  `Mayer.componentFactorizedNormalizedPairFamilyTerm`,
  `Mayer.pairFamilyComponentLocalSum`,
  `Mayer.componentFactorizedNormalizedPairFamilyTerm_eq_localSums`,
  `Mayer.pairFamilyComponentLocalProduct_eq_of_eq_on_componentVertices`,
  `Mayer.pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices`,
  `Mayer.restrictInvariant_pairFamilyComponentLocalSum`,
  `Mayer.project_pairFamilyComponentVertices_localSum`,
  `Mayer.abs_pairMayerFactor_le_one`,
  `Mayer.abs_pairFamilyComponentLocalProduct_le_one`,
  `Mayer.abs_pairFamilyComponentLocalSum_le_card`,
  `Mayer.abs_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard`,
  `Mayer.visibleL1_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard`,
  `Mayer.normalizedPairFamilyTerm_eq_componentFactorized`,
  `Mayer.visibleL1_anovaComponent_componentFactorized_le`,
  `Mayer.restrictInvariant_componentFactorizedNormalizedPairFamilyTerm`,
  `Mayer.project_edgeVertices_componentFactorizedNormalizedPairFamilyTerm`,
  `Mayer.coveringEdgeFamilyActivityGeTwo_of_factorized_termwise_bound`,
  `Mayer.xop_advantageOn_injective_of_factorizedCoveringEdgeFamily_geTwo_termwiseBudget_pow_small_q`,
  `Mayer.xop_advantageOn_injective_of_factorizedL1Budget_geTwo_pow_small_q`,
  `Mayer.pairFamilySupportGraph`,
  `Mayer.pairFamilySupportGraph_preconnected_iff_pairConnected`, and
  `Mayer.pairFamilySupportGraph_connected_iff_pairConnected_and_nonempty`,
  `Mayer.pairFamilyComponentVertices`,
  `Mayer.pairFamilyComponentEdgeFamily`, and
  `Mayer.edgeVertices_pairFamilyComponentEdgeFamily`,
  `Mayer.pairFamilyComponentVertices_component_eq_of_mem`,
  `Mayer.pairFamilyComponentVertices_pairwiseDisjoint`,
  `Mayer.pairFamilyComponentVertices_biUnion_eq_edgeVertices`,
  `Mayer.sum_card_pairFamilyComponentVertices`,
  `Mayer.edgeLinked_pairFamilyComponentEdgeFamily_of_edgeLinked`,
  `Mayer.componentVertices_mem_of_edgeLinked`,
  `Mayer.edgeLinked_reflTransGen_componentEdgeFamily_of_supportGraph`,
  `Mayer.pairFamilyComponentEdgeFamily_pairConnected`,
  `Mayer.pairFamilyComponentCluster`,
  `Mayer.pairFamilyComponentEdgeFamily_subset`,
  `Mayer.mem_pairFamilyComponentEdgeFamily_self_left`,
  `Mayer.pairFamilyComponentEdgeFamily_component_eq_of_mem`, and
  `Mayer.pairFamilyComponentEdgeFamily_biUnion_eq`,
  `Mayer.pairFamilyComponentEdgeFamily_pairwiseDisjoint`,
  `Mayer.sum_card_pairFamilyComponentEdgeFamily`,
  `Mayer.prod_pairFamilyComponentEdgeFamily`, and
  `Mayer.prod_pairMayerFactor_pairFamilyComponentEdgeFamily`,
  `Mayer.pairMayerFactor_eq_of_eq_on_hidden_edge`,
  `Mayer.extendOn`,
  `Mayer.extendOn_eq`,
	  `Mayer.pairFamilyComponentLocalProduct`,
	  `Mayer.pairFamilyComponentLocalProduct_restrictTuple`,
	  `Mayer.pairFamilyTerm_eq_sum_component_products`, and
  `Mayer.pairFamilyTerm_eq_sum_component_localProducts`,
	  `Mayer.normalizedPairFamilyTerm_eq_sum_component_products_div`,
	  `Mayer.normalizedPairFamilyTerm_eq_sum_component_localProducts_div`,
	  `Rank.componentLocalAtomizedRankBudget`,
	  `Rank.visibleL1_pairFamilyComponentLocalSum_le_componentLocalAtomizedRankBudget`,
	  `Rank.xop_advantageOn_injective_of_componentLocalAtomizedRankBudget_geTwo_pow_small_q`,
	  `ANOVA.anovaComponent_singleton_xopError_eq_zero_of_project_density_eq_one`,
  `ANOVA.visibleL1_anovaComponent_singleton_xopError_of_project_density_eq_one`,
  `ANOVA.addConstTuple`,
	  `ANOVA.project_singleton_eq_uniformAverage_of_addConst_invariant`,
	  `ANOVA.visibleDensityRatioReal_addConst`,
	  `ANOVA.project_singleton_visibleDensityRatioReal_eq_one`,
	  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_localActivity`,
	  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_cardSum`,
	  `Rank.PairClusterAtomizedContributionCertificateGeTwo`, and
	  `Rank.xop_advantageOn_injective_of_atomizedCumulantCertificateGeTwo_card_scaled_quadratic`:
  the rank/Penrose path now has an exact selected-tree fiber charge and two
  endpoint forms for the remaining estimate: filtered nonempty-support
  activity and support-cardinality-indexed scalar activity.  The main
  pair-Mayer route also has a separate named Penrose activity obligation so the
  proof does not accidentally sum raw positive connected clusters.  The scalar
  support-size sum can now be rewritten as the interval tail `Ico 2 (q+1)`,
  with supports of size zero and one discharged before the scalar estimate.
  A scalar comparison endpoint lets a later closed-form activity bound feed the
  theorem without reworking the Penrose construction, and a conservative
  nonnegative binomial-tail bound by `(1+a)^q` is available.  The sharper
  additive identity `tail + (1 + q a) = (1+a)^q` is also proved, preserving
  the cancellation of the `k=0,1` terms needed for birthday-scale estimates;
  a subtractive form is available for paper-style analytic statements.  The
  first geometric comparison lemmas reuse Mathlib's `Nat.choose_le_pow` and
  `geom_sum_Ico_le_of_lt_one`; the theorem-facing query-count endpoint now
  closes the scalar side of XOP-DAG-14 from a Penrose activity bound
  `localActivity k ≤ a^k`, a small-ratio assumption `q * a ≤ 1/2`, and the
  final numeric comparison `2 * (q * a)^2 ≤ ε`.  A direct `NNReal` endpoint is
  also available with bound `Real.toNNReal (2 * (q * a)^2)`, so future Penrose
  workers do not need to repeat coercion bookkeeping.  The expected
  field-size-scaled specialization is now exposed in the conventional
  `Real.toNNReal (2 * C^2 * q^2 / |G|^2)` form.  Separately, the already-proved
  all-edge-family expansion and off-support vanishing now have a concrete
  bridge: a covering-only edge-family activity bound over nonempty supports
  implies the component `L¹` bound and the injective-input advantage endpoint.
  A stronger ge-two bridge is also checked: after a singleton-component
  vanishing leaf is supplied, the covering activity summability starts at
	  support size two and can be expressed directly as the usual
	  `∑_{k≥2} binom(q,k) activity(k)` cardinality-indexed tail.  The theorem-facing
	  version now accepts the natural one-coordinate density marginal
  `project {i} visibleDensityRatioReal = 1` and derives singleton vanishing
  through the ANOVA bridge.  That marginal is now proved from the global visible
  translation symmetry of compatible counts, and the final theorem-facing
  ge-two covering endpoint no longer needs a separate singleton premise.
  The covering-edge route also now has direct scalar endpoints: a future proof
  of `CoveringEdgeFamilyComponentActivityBound activity` or the sharper
  ge-two interface `CoveringEdgeFamilyComponentActivityBoundGeTwo activity`
  plus `activity k ≤ a^k` feeds the birthday-scale bound through the same
  binomial-tail algebra as the Penrose cluster endpoint.  The termwise-budget
  bridge is checked in both forms; the ge-two version discharges empty and
  singleton supports internally using the already-proved singleton marginal.
  After component/fiber factorization, the route now has a named factorized
  term and endpoints that accept budgets for either
  `visibleL1 (anovaComponent S componentFactorizedTerm)` or, after the generic
  ANOVA `L¹` triangle/projection contraction, for
  `visibleL1 componentFactorizedTerm` itself.  This leaves the actual
  numerical activity estimate on the connected-component product expression as
  the current analytic leaf.  The component-local hidden sums are also named,
  and each local sum is proved to depend only on the visible vertices in its
  connected component.  This prepares the next product-space step: factor or
  bound the visible average over disjoint component supports without assuming
  disconnected products vanish.  A crude pointwise/`L¹` bound by raw hidden
  assignment cardinalities is checked as a baseline, using only the fact that
  each pair-Mayer factor is `0` or `-1`; it is explicitly too weak for the
  birthday-scale theorem.
  The first graph-theoretic leaf for the genuine connected expansion is also
  checked: every pair-edge family has a support graph on `edgeVertices Γ`, and
  its Mathlib `Preconnected` predicate is equivalent to the existing
  `PairConnected Γ`; full `Connected` additionally requires a nonempty touched
  vertex set, matching Mathlib's convention and avoiding a false empty-family
  equivalence.  A finite support set and filtered edge family are now attached
  to each connected component, and the filtered edge family has exactly that
  finite support.  Component edge families are proved connected, packaged as
  `PairCluster`s, and shown to form a finite `biUnion` partition of the
  original edge family.  Component vertex sets are also proved pairwise
  disjoint and their `biUnion` is exactly `edgeVertices Γ`, so later
  factorization arguments can use disjoint visible/hidden supports rather than
	  only disjoint edge sets.  The corresponding vertex- and edge-cardinality
	  decompositions are proved with Mathlib's `Finset.card_biUnion`.  Mathlib's
  `Finset.prod_biUnion` is then reused to
  factor products over a raw pair-edge family into products over its connected
  component edge families, including the concrete pair-Mayer factor product.
  A local hidden-coordinate product for each component is also named, and it is
  proved to agree with the full hidden tuple product after restricting the
  hidden tuple to the component support.
  The fixed raw and normalized edge-family terms are now rewritten as
  hidden-state sums of connected-component products, and also in a local form
  where each component product receives only the hidden tuple restricted to its
  own support.  This stops exactly at the next missing theorem-forced leaf:
	  product-space/fiber factorization of the hidden-state sum over the disjoint
	  component supports and then the genuine Ursell/Penrose connected contribution
	  identity.
	  This is the graph-theoretic bridge toward decomposing an arbitrary edge
	  family into connected pair clusters; it still does not assert the missing
	  Ursell/Penrose connected contribution identity.
	  The preferred concrete cumulant endpoint is now the ge-two-only Penrose
	  interface: it only asks for `PairClusterExpansionGeTwo` on supports with
	  cardinality at least two, internally discharges empty/singleton ANOVA
	  components from the established XoP marginals, and feeds the same
	  `Ico 2 (q+1)` scalar summability premise directly to the injective-input
	  advantage theorem.  This is the target interface for the next concrete
	  Penrose/cumulant construction.
- `Rank.selectedSpanningTreeFiberCharge_eq_zero_of_card_lt_two`,
  `Mayer.nonemptySupportActivity_sum_by_card_ge_two`, and
  `Rank.xop_advantageOn_injective_of_pairClusterExpansion_fullAtomizedDensityCharge_selectedSpanningTreeFiber_cardSum_ge_two`:
  support sizes zero and one are now discharged before the scalar activity
  estimate, using the existing pair-cluster support-cardinality theorem.  The
  remaining scalar sum starts at `k = 2`.
- `Rank.fullAtomizedPairClusterCharge_nonneg`,
  `Rank.selectedSpanningTreeFiberCharge_nonneg`,
  `Rank.selectedSpanningTreeFiberCharge_sum_nonneg`,
  `Rank.selectedSpanningTreeFiberCharge_eq_card_mul`,
  `Rank.SelectedSpanningTreeFiberLocalActivityBound`, and
  `Rank.xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity`:
  the remaining Penrose local-activity estimate is now named as the current
  hard leaf, with basic nonnegativity facts available for monotone comparisons.
  The cardinality expansion makes the raw selected-fiber counting obstruction
  explicit.
- `Rank.xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity_pow_small`
  and
  `Rank.xop_advantageOn_injective_of_selectedSpanningTreeFiberLocalActivity_pow_small_q`:
  the selected-fiber rank route now has the same scalar binomial-tail endpoint
  as the pair-cluster Penrose route.  Once the hard local activity obligation is
  bounded by `a^k`, the proof can close through the existing quadratic
  summability algebra without redoing finite-sum estimates.

**Important caution on selected-tree fibers:** `Rank.selectedSpanningTreeFiberCharge`
is an exact positive fiber charge for the currently exposed full-atomized
per-cluster charge.  It is a useful theorem-facing interface, but by itself it
does not prove Penrose cancellation; naively bounding it by counting every raw
cluster in the fiber may reintroduce the combinatorial explosion.  The accepted
proof must still establish a genuine pair-Mayer/Penrose contribution family and
show that its tree charge or selected-fiber activity is dominated after the
Mayer cancellations have been applied.  This is now witnessed formally by
`Rank.selectedSpanningTreeFiberCharge_eq_card_mul`.

**Contrarian acceptance note on scalar Penrose endpoints:** the scalar lemmas
`sum_Ico_choose_mul_pow_le_geom_tail`,
`sum_Ico_choose_mul_pow_le_two_mul_sq`, and the downstream
`xop_advantageOn_injective_of_pairClusterPenroseTreeActivity_*` endpoints are
accepted only as conditional scalar infrastructure.  They do **not** prove the
Penrose/tree-graph estimate.  The hard open leaf remains: construct a concrete
Penrose/cumulant contribution family, prove its `PairClusterExpansion`, prove
its power activity estimate `localActivity k ≤ (C/|G|)^k`, and bridge the
rank/full-atomized charge path to that actual contribution family without raw
positive selected-fiber counting.

**Closed theorem-forced ANOVA leaf:** the ge-two covering bridge exposed the
singleton vanishing obligation
`∀ i, visibleL1 (anovaComponent {i} xopError) = 0`.  `XoPANOVA.lean` now proves
the ANOVA algebra reducing singleton vanishing to the one-coordinate density
marginal `project {i} visibleDensityRatioReal = 1`, then proves that marginal
from the global visible-translation symmetry of compatible counts and the
already-proved global mean
`uniformAverage visibleDensityRatioReal = 1`.  The finite-fiber proof reuses
`uniformAverage_project`, `Fintype.sum_equiv`, and the local compatible-count
translation equivalence rather than introducing a new fixed-coordinate
falling-factorial count.

**Reuse check:** Mathlib supplies the graph side used so far
(`SimpleGraph.Connected.exists_isTree_le`, tree cardinality facts, finite-sum
reindexing), but no ready-made Penrose tree-graph inequality or Cayley
enumeration theorem for these `PairTree` objects was found in the local Mathlib
checkout.  The remaining Penrose inequality is genuinely project-specific.

**Resolved tree-route convention issue:** Mathlib's `SimpleGraph.IsTree`
requires a nonempty vertex type, so `Mayer.PairTree ∅` is empty while
`Mayer.PairCluster ∅` contains the empty edge family.  Therefore the
full-atomized charge `|K|^0 = 1` cannot be dominated by a sum over
`PairTree ∅`.  The accepted route is now the first option: the empty ANOVA
component of `xopError` is zero under `q ≤ |G|`, and the tree-charge theorem is
routed only over nonempty supports.  Do not use the older all-support
full-atomized tree endpoint as the main Penrose theorem unless an explicit
empty forest/tree convention is added later.
until this empty-support convention is resolved.

**Important open normalization point:** `XoPCombinatorics.compatibleCount` uses a
trivial normalizer only to package the raw `Z` function.  The proof-relevant
normalizer remains the corrected value `E_I[Z] = (N)_q^2 / N^q`; proving and
wiring that normalizer is the next concrete obligation.

**Current proof gaps from latest checkpoint:**
- `Model.outputFiberEquivCompatibleSigma`: prove the dependent equivalence
  between permutation pairs producing a fixed output vector and a compatible
  hidden tuple plus two permutation fibers.  The current obstruction is Lean
  bookkeeping in the inverse/right-inverse proof, not a mathematical gap:
  proof-irrelevance/dependent equality for the embedded compatibility witness
  must be handled cleanly.
- `Model.real_xop_output_fiber_count`: derive the concrete real output-fiber
  cardinality
  `# { (π₁,π₂) | outputMap inputs (xopDDS π₁ π₂) = ys }
    = Z(ys) * ((N - q)!)^2`
  for injective fixed inputs, reusing `card_perm_fiber`.
- Real output law: convert the output-fiber cardinality into a probability
  formula for `xopReal_outputDist_eq_pair_pushforward`, preferably via existing
  uniform-pushforward/fiber lemmas before adding new ones.
- Transcript lift: push the real output law through `transcriptEmbed` using the
  already-proved injectivity/factorization lemmas.
- Real/reference density identity: prove
  `real(t) = (Z(t) / E_I[Z]) * ideal(t)` for every fixed-input embedded
  transcript, with `E_I[Z] = (N)_q^2 / N^q`.
- Correct normalizer wiring: instantiate the concrete
  `RealizesNormalizedCountingModel`/`NormalizedCountingModel` path using
  `compatibleCountWithExpectationNormalizer`, eliminating the placeholder
  normalizer from theorem applications.
- Analytic estimate: after the density identity is wired, prove the concrete
  positive-error bound, or isolate the exact pair-Mayer/Penrose, rank, and
  tilted-defect obligations needed to prove it.
- Endpoint assumptions: settle whether the first final theorem is fixed-input
  non-adaptive, full non-adaptive, adaptive, or a documented reduction between
  them; keep `Function.Injective inputs`, `q ≤ N`, and any nonempty/domain
  assumptions explicit.
- Import hygiene: decide whether `card_perm_fiber` should stay imported from
  `PRPPRFSwitchingGeneral` or move to a shared permutation-fiber module to
  avoid pulling unrelated application warnings into XoP model builds.

**Contrarian acceptance notes:**
- The current endpoint is honestly restricted: it proves an `advantageOn`
  wrapper for injective/non-repeating fixed inputs only.  It does not imply
  unrestricted `advantage`, and it does not imply adaptive security.
- The restricted endpoint must always be advertised with non-vacuity/domain
  assumptions such as `q ≤ Fintype.card G`; otherwise the injective-input class
  may be empty.
- The concrete normalized-counting constructor still takes the analytic
  positive-error estimate as a hypothesis.  It packages the bridge; it does not
  prove the `q²/N²` bound.
- Downstream analytic work must be stated over visible output tuples or must
  explicitly dispose of off-image transcripts; do not reason over arbitrary
  transcripts as if all of them are embedded fixed-input transcripts.
- The corrected normalizer is semantically proved in the ideal-expectation
  lemmas, but every final package must use that theorem, not merely a chosen
  nonzero denominator.

**Active dependency DAG for the q²/N² target:**

The manager loop must keep work flowing in this order unless a proof attempt
exposes a real mathematical obstruction.  A local lemma is accepted only when it
discharges one of these nodes or creates a documented bridge required by one of
them.

| ID | Node | Status | Immediate dependencies / closure condition |
|---|---|---|---|
| XOP-DAG-00 | Final theorem `Adv_XoP(q) ≤ C q²/N²` | Open | Needs XOP-DAG-01 and final domain assumptions. |
| XOP-DAG-01 | LM/random-system advantage wrapper | Mostly proved | Needs fixed-input/adaptive endpoint decision and XOP-DAG-01A/XOP-DAG-02. |
| XOP-DAG-01A | Repeated-query reduction or injective-input endpoint | Partially addressed; q=2 restricted endpoint proved | `nonadaptive_securityOn_injective_from_transcript_bound` gives the restricted endpoint, and `Analytic.xop_advantageOn_injective_two_le_quadratic` demonstrates the full bridge for q=2. Still open: prove repeats reduce to distinct inputs if the final theorem uses unrestricted `advantage`. |
| XOP-DAG-02 | Fixed-input transcript TV bound | Closed on injective-input restricted path modulo XOP-DAG-09 | `Model.xop_advantageOn_injective_of_visible_positiveError` reduces the restricted theorem to visible positive-error estimates. |
| XOP-DAG-03 | Density identity `real = (Z/E_I[Z]) * ideal` | Proved for injective inputs | `Model.real_eq_density_mul_ideal_transcript`; next package into `NormalizedCountingModel`/analytic obligations. |
| XOP-DAG-04 | Real fixed-input transcript law | Proved for injective inputs | `Model.real_xop_transcriptDist_transcriptEmbed_apply_descFactorial` plus off-image zero through `fTransform_transcriptEmbed_eq_zero_of_not_image`. |
| XOP-DAG-05 | Real output probability formula | Proved for injective inputs, needs downstream algebraic normalization | `Model.real_xop_outputDist_apply`; next use it to prove XOP-DAG-04/XOP-DAG-03 for injective inputs. |
| XOP-DAG-06 | Real output-fiber count | Proved for injective inputs | `Model.outputFiberEquivCompatibleSigma` and `Model.real_xop_output_fiber_count`; verified by `lake env lean RandomSystems/Applications/XoPModel.lean`. |
| XOP-DAG-07 | Ideal fixed-input transcript law | Proved | Reuses `Instances.eval_nonces_uniform`; keep injective-input assumptions explicit. |
| XOP-DAG-08 | Correct normalizer `E_I[Z] = (N)_q²/N^q` | Wired on injective-input path modulo analytic positive-error bound | `compatibleCountWithExpectationNormalizer` plus `Model.realizes_xop_compatibleCount_of_positiveError`. |
| XOP-DAG-08A | Transcript positive-error sum reduces to visible-output sum | Proved | `Model.positiveError_xop_compatibleCount_eq_visible`; analytic work can now target visible tuples. |
| XOP-DAG-09 | Analytic estimate `E_I |Z/E_I[Z] - 1| ≤ C q²/N²` | Research open; q=0, q=1, exact q=2, and q=2 quadratic-bound leaf proved | Pure visible-tuple expression is defined in `Analytic.pureVisiblePositiveError`; next concrete leaf is the general `q` proof via XOP-DAG-10 through XOP-DAG-14. |
| XOP-DAG-10 | ANOVA/Hoeffding decomposition of `R - 1` | In progress; generic reconstruction/L1/centering/tower/off-support/positive-error/advantage bridge proved | `XoPANOVA.lean` now proves projection endpoint laws (`project_empty`, `project_full`), fiber-constant projection (`project_of_restrict`), idempotence, constants, add/sub linearity, projection mean preservation, the tower law `project S (project T f) = project S f` under `S ⊆ T`, product-space projection irrelevance for coordinates outside a function support, exact off-support ANOVA vanishing, explicit empty/singleton components, finite subset-Möbius reconstruction `∑ S ⊆ coordinates, anovaComponent S f = f`, specialization to `xopError`, nonempty-component zero global mean, named nonzero normalizer condition, finite `visibleL1` triangle bridge, `(pureVisiblePositiveError q : ℝ) ≤ visibleL1 xopError`, the downstream `NNReal ≤ ε` packaging theorem from component L1 estimates, the named component obligation `XoPComponentL1Bound`, the theorem `xop_advantageOn_injective_of_componentL1Bound`, singleton-component vanishing from the one-coordinate density marginal, and the singleton density marginal itself via compatible-count translation symmetry. Remaining leaves: actual XoP component estimates for supports of size at least two and any stronger source-specific orthogonality statements needed by the estimates. |
| XOP-DAG-10A | Component activity plug-in interface | Proved | `ComponentActivityBound` plus `componentL1Bound_of_activity_sum` and `xop_advantageOn_injective_of_activity_sum` connect per-component estimates to concrete injective-input security. |
| XOP-DAG-11 | Pair-Mayer/Penrose expansion before atomization | In progress | Pair-level objects, finite product indicator identity, powerset Mayer expansion, equality to the existing compatible-count density numerator, all-edge-family expansion of `xopError`, covering-only edge-family bridge to advantage, connected cluster types, the explicit contribution-family cluster-activity-to-ANOVA bridge, the support-indexed per-cluster charge endpoint, the scalar covering-edge endpoint, and the support-graph equivalence for pair connectedness are proved in `XoPMayer.lean`. Remaining: prove the genuine connected contribution expansion and Penrose/tree-graph activity/charge bound, or prove a covering-edge activity estimate strong enough to feed the covering bridge. |
| XOP-DAG-12 | Rank/codimension bounds for atomized constraints | In progress | `XoPRank.lean` defines typed hidden/shifted atoms, proves `pairBad` iff existence of an atom on the same pair edge, expresses atoms as affine linear equations over fields, packages row families as linear maps, proves the quotient-obstruction feasibility criterion, names hidden rank, visible obstruction rank, joint constraint map, and joint rank, proves the exact rank identity `visibleObstructionRank + hiddenRank = jointRank`, proves finite-field hidden and joint codimension counts, bridges selected atom families to row systems, proves the connected hidden-rank lower bound in root-reachability form, proves the algebraic visible-obstruction and combined-codimension leaves, proves a concrete hidden-path-plus-shifted-edge mixed-cycle witness, proves the general left-kernel RHS visible-defect certificate, proves the `|K|^{-|V|}` probability-form codimension bound, proves a concrete full-atomization bridge for connected nonempty pair-edge families, connects exact full-atomized density charges to the generic pair-cluster charge interface, composes these into an end-to-end injective-input advantage endpoint conditional on expansion, density domination, and charge summability, and exposes the selected-spanning-tree local-activity endpoint directly in scalar `a^k`/query-count form. Remaining: prove the genuine Penrose contribution expansion, exact density domination for that contribution family, and the selected-tree local activity estimate, then injectivity corrections. |
| XOP-DAG-13 | Tilted visible-defect bound | Open | Must handle overlapping supports via dependency/cluster method, not false factorization. |
| XOP-DAG-14 | Cluster summability to `C q²/N²` | Partially proved on scalar side | `XoPMayer.lean` now proves the binomial/geometric tail, query-count endpoint, direct `NNReal` endpoint, and field-size-scaled quadratic endpoint from `localActivity k ≤ (C/|G|)^k` and `q*C/|G| ≤ 1/2`. Remaining: prove the genuine Penrose activity bound supplying the contribution family and constant `C`. |
| XOP-DAG-15 | Contrarian review and no-vacuity audit | Open | Required after each major artifact and before final completion. |

**Contrarian note for XOP-DAG-10 reconstruction leaf (accepted with narrowed
scope):** the proved `ANOVA.anovaComponent_reconstruction(_apply)` theorem is a
generic Boolean-lattice identity for arbitrary real-valued visible functions.
It does **not** yet prove the XoP Hoeffding theorem needed for the L1 analytic
bound.  The accepted status is only: "generic Möbius reconstruction leaf
proved."  Still required before XOP-DAG-10 can close:
- specialize reconstruction to `xopError`/`visibleDensityErrorReal` under the
  valid nonzero-normalizer hypotheses such as `q ≤ Fintype.card G`;
- prove any stronger orthogonality statement needed downstream; the projection
  nesting/tower law is now proved generically;
- bridge signed `ℝ` component `visibleL1` estimates to the `NNReal`
  positive-error sum consumed by the concrete XoP model theorem.

Update: the generic reconstruction theorem has now been specialized to
`xopError`; the corrected normalizer is named with a nonzero lemma under
`q ≤ Fintype.card G`; global centering of nonempty components is proved; the
projection tower law is proved as `ANOVA.project_project_of_subset`; and
off-support ANOVA vanishing is proved from the product-space fiber equivalence
`ANOVA.projectionIrrelevance`.  The remaining contrarian objections are now the
actual XoP component activity estimates and any additional source-specific
orthogonality they require.

**Tower-law proof plan (completed):** proved
`conditionalAverage S (project T f) zS = conditionalAverage S f zS` under
`S ⊆ T` by partitioning an `S`-fiber into `T`-fibers.  Reuse
`conditionalAverage_fiber_card_mul`, `Finset.sum_fiberwise`,
`Finset.sum_subtype`, and `Fintype.sum_equiv`.  The useful helper is
`restrictTupleOfSubset hST zT`, allowing each `T`-fiber to be checked as either
empty or equivalent to the corresponding full fiber inside the `S`-fiber.

**Current dispatch plan:**
- Manager local work: XOP-DAG-03 through XOP-DAG-08A are closed on the
  injective-input path.  The active theorem chain is XOP-DAG-09 through
  XOP-DAG-14, beginning in `XoPRank.lean` because rank/codimension is the next
  blocker for the analytic estimate.
- Worker A / local proof target: prove the rank identity, or the exact weaker
  identity actually needed downstream, relating `jointRank`, `hiddenRank`, and
  `visibleObstructionRank`.
- Worker B / local proof target: prove finite-field fiber cardinality for
  hidden solutions: every feasible row system has exactly `|K|^(q -
  hiddenRank)` hidden assignments, and infeasible systems have zero.
- Worker C / local proof target: connect atomized Mayer products to row-family
  constraint systems, reusing the post-pair atomization boundary and never
  running raw colored-bond KP.
- Worker D / local proof target: prove graph/rank lower bounds for connected
  covering families, then feed them into the fixed-bond codimension estimate.
- Worker E / local proof target: start the Penrose/tree-graph activity bound
  using the covering-only interface in `XoPMayer.lean`.
- Deferred until the above rank/Penrose chain is in place: tilted
  visible-defect and final summability into the `C q² / N²` positive-error
  estimate.
- Contrarian review remains mandatory after each major artifact; accepted
  progress must survive no-vacuity, hidden-assumption, source-faithfulness, and
  downstream-usability checks.

### XoP Remaining Obligations Progress List

This list is the manager-loop progress list for the long-running XoP task.  Do
not mark the task finished until every item below is complete and the XoP
theorem path has no `sorry`, hidden analytic assumption, or unresolved
obligation.

Five-hour theorem push contract:

- [ ] Run the next serious pass as a minimum five-hour manager loop unless the
      full theorem closes earlier or a precise mathematical obstruction is
      proved and logged.
- [ ] During that pass, keep the active target theorem-first: start from
      `xop_nonadaptive_security_from_analytic_obligations` /
      `Model.xop_advantageOn_injective_of_pureVisiblePositiveError`, then close
      the current leaf obligations rather than drifting into unrelated lemmas.
- [ ] Do not accept "partial scaffold" as completion.  A paused pass must record
      the next theorem, the current Lean blocker, changed files, and verification
      commands.
- [ ] Dispatch implementation and contrarian-review work in parallel where file
      ownership is disjoint; every accepted artifact must survive targeted Lean
      checks and tracker synchronization.

Top theorem and wrappers:

- [x] Replace `xop_nonadaptive_security_research_target` with a checked
      conditional theorem spine over explicit named obligations.
- [x] Replace `xop_adaptive_security_research_target` with a checked
      conditional theorem spine over `AdaptiveTranscriptBound`.
- [ ] Instantiate the non-adaptive theorem spine with concrete XoP proofs of
      the remaining named obligations.
- [ ] Instantiate the adaptive theorem spine, or prove a paper-faithful
      reduction showing the non-adaptive theorem is the intended endpoint for
      the selected XoP setting.
- [ ] Decide and document the final public theorem name and statement:
      non-adaptive transcript theorem, adaptive random-system theorem, or both.
- [ ] Prove any required bridge from fixed-input transcript bounds to adaptive
      bounds; do not rely on equivalence-only Lemma 5 for inequalities unless a
      valid bound-transfer theorem is proved.
- [x] Add an honest restricted `advantageOn` wrapper for injective fixed-input
      sequences.
- [ ] Prove a repeated-query reduction from arbitrary fixed inputs to injective
      fixed inputs, or restate the first final theorem using the existing
      admissible-input supremum over injective inputs.

Concrete XoP model:

- [x] Define the concrete XoP real PDS from two independent permutations.
- [x] Define the ideal random-function PDS with the same query/output alphabet.
- [x] Prove both real and ideal PDSs are probability distributions when the
      theorem requires probability systems.
- [ ] Prove the fixed-input transcript distributions used by the XoP theorem are
      the intended transcript laws of the concrete PDS definitions.
- [ ] Resolve the injective-input limitation: either prove repeated inputs add
      no distinguishing power for the stateless real/ideal systems, or keep the
      theorem endpoint explicitly restricted to injective/admissible inputs.
- [x] Prove the ideal fixed-input transcript law for injective inputs by reusing
      `Instances.eval_nonces_uniform`.
- [x] Prove the first model-to-count bridge: for injective fixed inputs, the
      real XoP transcript induces a compatible hidden state.
- [x] Define the real output-fiber types and prove the reusable permutation
      fiber cardinality helper from `card_perm_fiber`.
- [x] Prove `Model.outputFiberEquivCompatibleSigma`, the dependent equivalence
      from real output fibers to compatible hidden tuples and two permutation
      fibers.
- [x] Prove `Model.real_xop_output_fiber_count`, the concrete count of
      permutation pairs producing a fixed output vector.
- [x] Prove the real fixed-input output-vector distribution formula from the
      output-fiber count.
- [x] Lift the real output-vector distribution formula to embedded fixed-input
      transcript distributions through `transcriptEmbed`.
- [x] Prove off-support fixed-input transcripts have zero real and ideal mass,
      or otherwise package the density identity over the image of
      `transcriptEmbed`.
- [x] Prove the full XoP transcript law depends on the output tuple through the
      compatible hidden-state count `Z`.

Counting and normalization:

- [x] Add a corrected concrete count package with normalizer
      `E_I[Z] = (N)_q^2 / N^q` under the explicit assumption `q ≤ N`.
- [x] Replace remaining theorem instantiations that still use the
      placeholder/trivial normalizer with the corrected package.
- [x] Formalize the falling factorial `(N)_q` or reuse the correct Mathlib
      combinatorial object.
- [x] Prove the injective-tuple count `# {a : Fin q → G | Injective a} = (N)_q`.
- [x] Prove the raw compatible-pair total
      `∑_y Z(y) = (N)_q^2`.
- [x] Prove the visible-output uniform expectation identity
      `E_y[Z(y)] = (N)_q^2 / N^q`.
- [x] Prove the embedded-output version of the ideal expectation identity.
- [x] Prove the ideal expectation identity
      `E_I[Z] = (N)_q^2 / N^q` for the actual fixed-input reference transcript
      distribution.
- [ ] Prove the real/reference density identity
      `real(t) = (Z(t) / E_I[Z]) * ideal(t)` for every fixed input transcript.
- [x] Prove the full-transcript real/reference density identity with corrected
      normalizer `(N)_q^2/N^q` under injective fixed inputs.
- [x] Instantiate `RealizesNormalizedCountingModel` for the concrete XoP model
      under injective inputs and the corrected expectation normalizer.
- [x] Prove the constructor that instantiates the concrete corrected
      compatible-count package from the density identity plus the analytic
      positive-error estimate.
- [x] Prove that the transcript-level positive-error sum for the ideal
      transcript law equals the corresponding visible-output sum under
      `Dist.uniform (Fin q → G)`.
- [x] Prove the transcript-to-visible positive-error reduction for the corrected
      XoP compatible-count density.
- [x] Prove that a visible-output positive-error estimate instantiates the
      corrected concrete normalized-counting model for injective inputs.
- [x] Prove the normalizer is nonzero under the theorem's domain assumptions.
- [x] Surface the first required domain assumption, `q ≤ N`, for the corrected
      normalizer package.
- [ ] Surface and prove any remaining required domain assumptions, such as the
      exact nonzero falling-factorial condition.

Density and total variation:

- [x] Prove the generic bridge
      `DensityRatioPositiveErrorBound → statDist real reference ≤ ε`.
- [x] Prove fixed-input density-ratio certificates imply
      `FixedInputTranscriptBound`.
- [x] Prove normalized counting models imply density-ratio certificates.
- [ ] Prove the concrete positive-error estimate for XoP:
      `sum_t ((Z(t)/E_I[Z]) * ideal(t) - ideal(t)) ≤ bound`.
- [x] Prove the restricted theorem-composition spine from visible-output
      positive-error estimates to `advantageOn` over injective inputs.
- [x] Remove the fixed-input sequence from the remaining visible positive-error
      estimate, reducing the restricted theorem to a pure visible-tuple bound.
- [x] Prove the pure visible analytic base cases q=0 and q=1.
- [x] Prove the first nontrivial pure visible analytic case q=2, preferably
      exactly before weakening to a `C/N^2` bound.
- [x] Package the q=2 exact expression as a theorem-facing
      `pureVisiblePositiveError 2 ≤ C * 2^2 / N^2` bound with an explicit
      constant and domain assumptions.
- [x] Route the q=2 theorem-facing analytic bound through the model bridge to a
      concrete restricted `advantageOn` XoP theorem.
- [ ] Decide the final bound expression to formalize first, starting with the
      strongest honest theorem supported by the analytic obligations.

ANOVA / Hoeffding route:

- [ ] Define the product reference law over fixed-input transcripts.
- [ ] Define the normalized density `R = Z / E_I[Z]`.
- [x] Define the real-valued pure visible density ratio and density error used
      by the signed ANOVA decomposition.
- [x] Define finite coordinate restrictions and conditional averages over
      visible tuple fibers.
- [x] Define the Hoeffding/ANOVA projections `h_S` under the correct reference
      law.
- [x] Prove the visible ANOVA decomposition `R - 1 = sum_S h_S` for the finite
      product visible-output space.
- [x] Prove global centering of each nonempty visible component.
- [x] Prove product-space projection irrelevance and the generic off-support
      ANOVA vanishing lemma for functions with a finite coordinate support.
- [x] Instantiate off-support ANOVA vanishing for normalized pair-edge family
      terms via `edgeVertices`.
- [ ] Prove any further conditional-centering/orthogonality property required
      by the final component estimates.
- [x] Prove the injective-input visible positive-error/advantage bound from
      ANOVA component `L1` estimates.
- [ ] Prove or reject the dream lemma
      `||h_S||_1 ≤ (C/N)^|S|` with precise assumptions.

Pair-Mayer/Penrose route:

- [x] Define pair interactions before colored-bond atomization.
- [x] Prove the pair-Mayer expansion identity for the concrete `Z`.
- [x] Add the sanctioned post-pair atomization identity for hidden, shifted, and
      overlap atoms.
- [x] Define connected pair clusters and their weights.
- [x] Prove edge-family support dependence and exact off-support ANOVA
      vanishing, so only edge families whose touched vertices cover the ANOVA
      support can contribute.
- [x] Add a covering-only edge-family activity interface and prove it implies
      the previous all-edge-family activity interface.
- [x] Add a per-pair-cluster charge interface and prove expansion plus total
      charge summability implies the concrete injective-input advantage bound.
- [x] Add support-size layer reindexing for cluster charges, reusing Mathlib's
      `Finset.sum_powerset` instead of reproving powerset combinatorics.
- [x] Add the Mathlib-backed `SimpleGraph.IsTree` tree-charge handoff and prove
      tree-charge summability implies the concrete injective-input advantage
      bound.
- [x] Add the local-activity/binomial-count endpoint using Mathlib
      `card_powersetCard`.
- [x] Specialize Mathlib's tree edge-count theorem to `PairTree`.
- [x] Prove the scalar binomial-sum identity needed for geometric local
      activities.
- [x] Build the cluster graph and prove nonempty pair clusters admit a spanning
      tree subcluster via Mathlib's spanning-tree theorem.
- [ ] Prove the Penrose/tree-graph inequality needed to sum connected clusters.
  - [x] Define an arbitrary spanning-tree selector for nonempty pair clusters.
  - [x] Resolve the empty-support convention by proving the empty ANOVA
        component vanishes and excluding empty support from tree domination.
  - [x] Add checked nonempty-support charge/tree endpoints with an explicit
        empty-component-zero premise.
  - [x] Prove the generic tree-fiber domination wrapper from a selector and
        per-tree fiber estimates to the `htree` hypothesis.
  - [x] Specialize the generic tree-fiber wrapper to the selected spanning tree
        of each nonempty pair cluster.
  - [x] Define the exact selected-tree fiber charge and route it to a
        support-cardinality-indexed local-activity endpoint.
  - [x] Add the theorem-facing `PairClusterPenroseTreeActivityBound` endpoint
        separating genuine Penrose activity from raw selected full-atomized
        charge.
  - [x] Add selected-tree fiber wrappers for the actual contribution family:
        `Mayer.pairClusterPenroseTreeActivityBound_of_selectedContributionFiberBound`
        and
        `Mayer.pairClusterPenroseActivityBoundGeTwo_of_selectedContributionFiberBound`.
        These are the accepted bridge for future Penrose work: prove fiber
        estimates for `visibleL1 (contribution S C)`, not for the raw
        full-atomized positive charge.
  - [x] Add the direct scalar theorem-spine endpoint
        `Mayer.xop_advantageOn_injective_of_selectedContributionFiberBound_pow_small_q`.
        The remaining theorem leaves are now exactly: provide
        `PairClusterExpansion contribution`, selected contribution-fiber bounds,
        local activity bounds, and the scalar smallness hypotheses.
  - [x] Add the scalar rewrite from the `if k < 2` support-size sum to an
        `Ico 2 (q+1)` tail.
	  - [x] Add the corrected `Ico` endpoint for Penrose activity bounded only on
	        supports of size at least two, using the no-singleton-cluster lemma.
	  - [x] Add the ge-two-only expansion/activity endpoint:
	        `Mayer.PairClusterExpansionGeTwo`,
	        `Mayer.PairClusterPenroseActivityBoundGeTwoOnly`,
	        `Mayer.pairClusterPenroseActivityBoundGeTwoOnly_of_selectedContributionFiberBound`,
	        and
	        `Mayer.xop_advantageOn_injective_of_pairClusterPenroseActivityGeTwoOnly_Ico`.
	        This is the preferred interface for the concrete cumulant certificate:
	        it avoids irrelevant empty and singleton expansion obligations and
	        proves the final component `L¹` bound directly from the already-proved
	        empty/singleton ANOVA cancellations plus the `k ≥ 2` cluster estimate.
	        Verification: `lake build RandomSystems.Applications.XoPMayer
	        RandomSystems.Applications.XoPRank` passed; only unrelated pre-existing
	        PRP/PRF warnings remain.
  - [x] Add scalar activity monotonicity and an endpoint that accepts a
        closed-form tail bound after comparing local activity termwise.
  - [x] Add the conservative nonnegative binomial-tail bound
        `∑_{k≥2} binom(q,k) a^k ≤ (1+a)^q`.
  - [x] Prove the sharper additive binomial-tail identity
        `∑_{k≥2} binom(q,k) a^k + (1+qa) = (1+a)^q`.
  - [x] Add the equivalent subtractive tail identity
        `∑_{k≥2} binom(q,k) a^k = (1+a)^q - (1+qa)`.
  - [x] Prove the termwise geometric comparison
        `binom(q,k) a^k ≤ (qa)^k` for `a ≥ 0`, reusing Mathlib.
  - [x] Sum the termwise comparison over the `k ≥ 2` support-size tail.
  - [x] Exclude support sizes zero and one from the selected-tree scalar sum.
  - [x] Name the selected-tree local-activity obligation and prove basic charge
        nonnegativity facts needed by monotone estimates.
  - [x] Prove the selected-tree fiber cardinality expansion that exposes why
        raw positive fiber counting is not a valid Penrose bound.
  - [x] Prove the exact total selected-tree fiber identity:
        `Rank.selectedSpanningTreeFiberCharge_sum_eq_pairClusterCharge_sum` and
        `Rank.selectedSpanningTreeFiberCharge_sum_eq_pairCluster_card_mul`.
        These show that the exact selected full-atomized fibers still sum to
        the raw positive cluster count, with an explicit
        `Fintype.card (PairCluster S)` factor.  This mechanically confirms the
        tracker warning: the theorem cannot close by proving a uniform
        `C^|S|/|K|^|S|` estimate for this raw charge alone; the remaining
        activity estimate must be for a genuine Penrose/cumulant contribution
        family or another charge where the pair-Mayer cancellations have already
        been used.
  - [x] Decompose an arbitrary pair-edge family into Mathlib connected
        components: component vertex/edge sets are disjoint, their `biUnion`s
        recover `edgeVertices Γ` and `Γ`, component edge families package as
        `PairCluster`s, and raw pair-Mayer products/terms rewrite to products
        over connected components.
  - [x] Prove the finite-product fiber factorization for the hidden-state sum
        over the disjoint component supports exposed by
        `pairFamilyTerm_eq_sum_component_localProducts`.  This is now
        `pairFamilyTerm_eq_complementCard_mul_component_sums`, using
        `sum_restrictTuple_eq_card_compl_mul_sum`,
        `pairFamilyComponentAssignmentsEquivSupport`, and
        `Fintype.prod_sum` rather than reproving finite-product algebra.
  - [x] Add the normalized component-factorization statement
        `Mayer.normalizedPairFamilyTerm_eq_complementCard_mul_component_sums_div`
        for use by covering-edge activity estimates.
  - [ ] Prove the mathematical per-tree fiber estimate for the genuine Penrose
        contribution/charge family, not for the exact raw selected
        full-atomized fiber charge.
  - [ ] Construct the concrete Penrose/cumulant contribution family whose
        selected-tree fibers satisfy the new contribution-fiber wrappers.
      - [x] Add the theorem-forced atomized cumulant certificate interface
            `Rank.PairClusterAtomizedContributionCertificate`.  This does not
            assert a concrete Penrose construction; it records the exact object
            the construction must supply: a genuine `PairClusterContribution`,
            `PairClusterExpansion`, and a finite signed evaluation into
            atom-family hidden-fiber counts.
	      - [x] Prove the certificate-to-fiber-bound adapters:
	            `Rank.atomizedContributionRankBudget`,
	            `Rank.visibleL1_contribution_le_sum_atomized_jointRankBudget`,
	            `Rank.selectedContributionFiberBound_of_atomizedCertificate`, and
	            `Rank.xop_advantageOn_injective_of_atomizedCumulantCertificate_card_scaled_quadratic`.
	            These reduce the final quadratic endpoint to concrete certificate
	            construction, joint-rank budgets for certificate terms, selected
	            tree-fiber budget summability, and local activity bounds.
	            Verification: `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF warnings remain.
	      - [x] Add the ge-two-only atomized cumulant certificate interface and
	            endpoint:
	            `Rank.PairClusterAtomizedContributionCertificateGeTwo`,
	            `Rank.atomizedContributionRankBudgetGeTwo`,
	            `Rank.visibleL1_contribution_le_sum_atomized_jointRankBudget_geTwo`,
	            `Rank.selectedContributionFiberBound_of_atomizedCertificateGeTwo`,
	            and
	            `Rank.xop_advantageOn_injective_of_atomizedCumulantCertificateGeTwo_card_scaled_quadratic`.
	            This is now the preferred theorem-facing certificate target: the
	            concrete Penrose/Ursell construction only needs to prove
	            `PairClusterExpansionGeTwo`, not the irrelevant empty/singleton
	            expansion equations.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
      - [x] Add the corrected support-indexed Penrose/Ursell theorem spine:
            `Mayer.SupportIndexedContribution`,
            `Mayer.SupportIndexedExpansionGeTwo`,
            `Mayer.SupportIndexedActivityBoundGeTwo`,
            `Mayer.SupportPartitionClusters`,
            `Mayer.SupportPartitionTrees`,
            `Mayer.supportPartitionClusters_block_nonempty`,
            `Mayer.supportPartitionClusters_sum_block_card`,
            `Mayer.supportPartitionTrees_sum_block_card`,
            `Mayer.pairFamilyComponentFinpartition`,
            `Mayer.pairFamilyComponentClusterOfPart`,
            `Mayer.pairFamilyComponentSupportPartitionIndex`,
            `Mayer.supportPartitionClusterProductContribution`,
            `Mayer.xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_Ico`,
            `Mayer.xop_advantageOn_injective_of_supportIndexedExpansionGeTwo_card_scaled_quadratic`,
            and
            `Mayer.xop_advantageOn_injective_of_supportPartitionClusters_card_scaled_quadratic`.
            This repairs the source-faithfulness issue in the single-cluster
            interface: the true cumulant/Penrose contribution may now be
            indexed by a partition of the ANOVA support and per-block connected
            data, so disconnected edge-family products are not silently thrown
            away.
      - [x] Add the support-indexed atomized certificate endpoint:
            `Rank.SupportIndexedAtomizedContributionCertificateGeTwo`,
            `Rank.supportIndexedAtomizedContributionRankBudgetGeTwo`,
            `Rank.visibleL1_supportIndexedContribution_le_sum_atomized_jointRankBudget_geTwo`,
            `Rank.supportIndexedActivityBound_of_atomizedCertificateGeTwo`, and
            `Rank.xop_advantageOn_injective_of_supportIndexedAtomizedCertificateGeTwo_card_scaled_quadratic`.
            The concrete support-partition specialization is also named as
            `Rank.SupportPartitionClustersAtomizedContributionCertificateGeTwo`
            `Rank.supportPartitionClustersAtomizedCertificateGeTwo_of_globalAtomizedEval`
            `Rank.xop_advantageOn_injective_of_supportPartitionClusters_globalAtomizedEval_card_scaled_quadratic`
            and
            `Rank.xop_advantageOn_injective_of_supportPartitionClustersAtomizedCertificateGeTwo_card_scaled_quadratic`.
            This is now the preferred certificate target for the concrete
            Penrose/Ursell construction; the old pair-cluster certificate
            remains useful as a special-case adapter but is not sufficient for
            the full density expansion.  Verification:
            `lake build RandomSystems.Applications.XoPMayer
            RandomSystems.Applications.XoPRank` passed; only unrelated
            pre-existing PRP/PRF warnings remain.
      - [x] Add the support-inclusion atom bridge needed by any concrete
            support-partition global evaluation:
            `Rank.pairEdge_mono`, `Rank.atom_mono`,
            `Rank.atomHolds_atom_mono`, `Rank.atomFamily_mono`, and
            `Rank.atomFamilyHolds_atomFamily_mono_iff`.
            These let block-local atom families be lifted into the ambient
            ANOVA support before forming one global hidden-fiber count.
      - [x] Add the block-union atom bridge:
            `Rank.supportPartitionAtomFamily` and
            `Rank.atomFamilyHolds_supportPartitionAtomFamily_iff`.
            This packages all lifted block atom families into one ambient
            support-level atom family, which is the shape required by the
            global `heval` certificate.
      - [x] Add the forced vertex-support facts for the support-partition atom
            bridge:
            `Rank.atomVertices_atomFamily_mono` and
            `Rank.atomVertices_supportPartitionAtomFamily`.  These are the
            next rank-budget leaves generated by the global `heval` path:
            lifted block atoms preserve their original endpoint set, and the
            global support atom family has endpoint set equal to the union of
            the block endpoint sets.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the block-cover support consequences
            `Rank.atomVertices_supportPartitionAtomFamily_eq_of_blocks` and
            `Rank.card_atomVertices_supportPartitionAtomFamily_eq_of_blocks`.
            These are forced by the rank-budget path for
            `SupportPartitionClusters`: once each block-local Penrose term
            touches exactly its block, the single global atom family touches
            exactly the ambient ANOVA support.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add visible-obstruction monotonicity under support lifting and
            support partitions:
            `Rank.hasVisibleObstruction_atomFamily_mono` and
            `Rank.hasVisibleObstruction_supportPartitionAtomFamily_of_block`.
            These show that any block-local obstruction survives in the global
            atom family by restricting a hypothetical global hidden solution
            back to the block.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the first block-diagonal rank-sum leaves:
            `Rank.atom_mono_injective`,
            `Rank.supportPartitionAtomFamily_lift_eq_block_eq`,
            `Rank.supportPartitionAtomFamilySigmaEquiv`,
            `Rank.card_supportPartitionAtomFamily`, and
            `Rank.atomFamilyRow_supportPartitionAtomFamilySigmaEquiv`.
            These prove that the row index of a global
            `supportPartitionAtomFamily` is exactly the sigma-type of
            block-local rows, with disjointness justified by
            `Finpartition.eq_of_mem_parts`.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the theorem-facing conditional rank-budget adapter
            `Rank.jointRank_supportPartitionAtomFamily_ge_card_of_blocks_of_rank_sum`.
            It reduces the global `S.card ≤ jointRank` budget to the missing
            block-diagonal rank-sum inequality plus already-proved per-block
            connected visible-obstruction bounds.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the sigma-row rank reindexing layer:
            `Rank.supportPartitionSigmaAtomRow`,
            `Rank.hiddenConstraintMap_supportPartitionSigmaAtomRow_apply`,
            `Rank.visibleRhsMap_supportPartitionSigmaAtomRow_apply`,
            `Rank.jointConstraintMap_supportPartitionSigmaAtomRow_apply`,
            `Rank.jointRank_supportPartitionAtomFamily_eq_sigma`,
            `Rank.jointRank_supportPartitionAtomFamily_ge_sum_of_sigma_rank_sum`,
            `Rank.supportPartitionCurriedJointConstraintMap`, and
            `Rank.supportPartitionCurriedJointConstraintMap_apply`.
            The hard block-diagonal rank-sum leaf is now isolated to proving
            that the curried sigma joint map has product range equal to the
            block-local joint ranges.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the product-range rank adapters:
            `Rank.range_supportPartitionCurriedJointConstraintMap_le_pi_block_ranges`,
            `Rank.finrank_pi_block_joint_ranges`,
            `Rank.jointRank_supportPartitionSigmaAtomRow_eq_curried`,
            `Rank.jointRank_supportPartitionSigmaAtomRow_ge_sum_of_pi_le_range`,
            and
            `Rank.jointRank_supportPartitionAtomFamily_ge_sum_of_pi_le_range`.
            One inclusion, global range into the product of block ranges, is
            proved.  The reverse inclusion is also now proved by assembling
            block-local hidden/visible witnesses into one global assignment
            with `Rank.supportPartitionAssemble` and
            `Rank.supportPartitionAssemble_eq_of_mem`.  The completed
            block-diagonal layer includes
            `Rank.pi_block_ranges_le_range_supportPartitionCurriedJointConstraintMap`,
            `Rank.range_supportPartitionCurriedJointConstraintMap_eq_pi_block_ranges`,
            `Rank.jointRank_supportPartitionSigmaAtomRow_ge_sum`,
            `Rank.jointRank_supportPartitionAtomFamily_ge_sum`, and
            `Rank.jointRank_supportPartitionAtomFamily_ge_card_of_blocks`.
            Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the downstream support-partition rank-budget adapters:
            `Rank.jointRank_ge_card_of_supportPartitionClusterBlockAtoms`
            and
            `Rank.xop_advantageOn_injective_of_supportPartitionClusters_globalAtomizedEval_cardBudget_quadratic`.
            This discharges the `hvr` side of the concrete
            support-partition atomized endpoint using canonical budget
            `rankBudget S i t = S.card`, provided each term's atom family is
            the lifted block union and each block supplies touch/connectivity
            plus visible obstruction.  The remaining hypotheses are now the
            concrete global atomized evaluation, the support-indexed expansion
            resummation, and the scalar activity bound for the `S.card`
            budget expression.  Verification:
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
      - [x] Add the source-faithful conditional expansion adapter:
            `Mayer.supportPartitionClusterProductContribution_pairFamilyComponentSupportPartitionIndex`
            and
            `Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_supportPartition_resummation`.
            This connects the existing all-edge-family Mayer expansion plus
            component factorization to the corrected
            `SupportIndexedExpansionGeTwo` interface, while leaving the real
            Penrose/Ursell regrouping as the named hypothesis `hresum`.
            Verification:
            `lake env lean RandomSystems/Applications/XoPMayer.lean` and
            `lake env lean RandomSystems/Applications/XoPRank.lean` passed.
	        Current precise blocker: existing code decomposes each fixed
        pair-edge family into connected components and proves the hidden-state
        product/fiber factorization, but it does not yet define the Möbius /
        cumulant / Penrose assignment that turns the edge-family/component
        factorization into a `SupportIndexedExpansionGeTwo` contribution.  The
        raw connected product
        contribution is now connected by
        `Mayer.rawClusterContribution_eq_normalizedPairFamilyTerm`, but it is
        explicitly not an acceptable substitute because it lacks connected
        cumulant cancellation.
        Stronger model-gap note: for the density expansion `R - 1`, a
        disconnected edge family can contribute products across several
        connected components.  The support-indexed endpoint is now the valid
        Penrose theorem path; the covering-edge-family endpoint remains the
        conservative fallback, but it is too weak unless the rank/Penrose layer
        supplies a sharper non-raw budget.
      - [x] Add the support-retyped block-full-atomization bridge forced by the
            concrete support-partition rank budget:
            `Mayer.pairClusterSupportEdge`,
            `Mayer.pairClusterSupportEdges`,
            `Mayer.pairClusterSupportEdge_injective`,
            `Mayer.card_pairClusterSupportEdges`,
            `Mayer.edgeVertices_pairClusterSupportEdges`,
            `Mayer.pairClusterSupportEdges_pairConnected`,
            `Mayer.pairClusterSupportEdges_nonempty_of_support_nonempty`,
            `Rank.atomVertices_supportPartitionCluster_supportFullAtoms`,
            `Rank.supportPartitionCluster_supportFullAtoms_connected`,
            `Rank.hasVisibleObstruction_supportPartitionCluster_supportFullAtoms`,
            and
            `Rank.xop_advantageOn_injective_of_supportPartitionClusters_globalSupportFullAtomizedEval_cardBudget_quadratic`.
            This closes the automatic `hblocks`/`hconn`/`hvis` side when a
            future Penrose/Ursell term's block atom family is the full
            hidden/shifted atomization of the block cluster retyped over the
            block support.  The remaining concrete leaves are now exactly:
            a real support-indexed expansion/resummation for a concrete
            Ursell/Penrose block contribution, a global support-full-atomized
            hidden-fiber evaluation for that contribution family, and the
            scalar activity estimate for the resulting `S.card` budget.
            Verification: `lake build RandomSystems.Applications.XoPMayer
            RandomSystems.Applications.XoPRank` passed; only unrelated
            pre-existing PRP/PRF warnings remain.
      - [x] Add the composed theorem-facing endpoint
            `Rank.xop_advantageOn_injective_of_componentFactorized_resummation_globalSupportFullAtomizedEval_cardBudget_quadratic`.
            This removes a layer of expansion plumbing from the current parent
            theorem: it consumes the source-faithful `hresum` premise directly
            via
            `Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_supportPartition_resummation`,
            then feeds the support-full-atomized rank endpoint.  Remaining
            leaves are therefore the real Penrose/Ursell resummation, the
            global support-full-atomized evaluation, and the scalar budget.
      - [x] Generalize the support-partition contribution interface to allow
            partition-level Ursell/Penrose coefficients:
            `Mayer.supportPartitionWeightedClusterProductContribution`,
            `Mayer.supportPartitionWeightedClusterProductContribution_one`,
            `Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_weightedSupportPartition_resummation`,
            `Rank.xop_advantageOn_injective_of_supportPartitionContribution_globalSupportFullAtomizedEval_cardBudget_quadratic`,
            and
            `Rank.xop_advantageOn_injective_of_componentFactorized_weightedResummation_globalSupportFullAtomizedEval_cardBudget_quadratic`.
            This addresses the contrarian-review risk that the true
            Möbius/Ursell coefficient may depend on the whole support
            partition rather than factor blockwise.  The accepted theorem path
            can now use either a general support-indexed contribution or the
            weighted product shape; it is no longer forced to hide a
            partition-level coefficient inside block-local contributions.
            Contrarian review accepted this as conditional DAG plumbing and
            confirmed that the previous partition-level coefficient objection
            is resolved; it remains conditional on proving the actual `hresum`,
            `heval`, and `hbudget` leaves without raw colored-bond domination.
      - [x] Name the concrete partition-lattice coefficient target:
            `Mayer.supportPartitionUrsellWeight`,
            `Mayer.abs_supportPartitionUrsellWeight`,
            `Mayer.abs_supportPartitionUrsellWeight_le_factorial_card`, and
            `Rank.xop_advantageOn_injective_of_componentFactorized_ursellResummation_globalSupportFullAtomizedEval_cardBudget_quadratic`.
            The hard resummation leaf can now be stated with the standard
            Ursell coefficient `(-1)^(m-1)(m-1)!` rather than an arbitrary
            partition weight, while the absolute-value lemma is available for
            the future coefficient-budget estimate.
	      - [x] Name the resummation obligations as first-class Props and add
	            theorem wrappers:
	            `Mayer.SupportPartitionWeightedResummationGeTwo`,
	            `Mayer.SupportPartitionUrsellResummationGeTwo`,
	            `Mayer.supportIndexedExpansionGeTwo_of_weightedResummationGeTwo`,
	            `Mayer.supportIndexedExpansionGeTwo_of_ursellResummationGeTwo`, and
	            `Rank.xop_advantageOn_injective_of_ursellResummationGeTwo_globalSupportFullAtomizedEval_cardBudget_quadratic`.
	            This makes the next hard leaf stable and theorem-facing: prove
	            `SupportPartitionUrsellResummationGeTwo` for the concrete
	            contribution family, then prove its global evaluation and budget.
	      - [x] Reduce the concrete Ursell `hresum` leaf to selector-fiber
	            identities:
	            `Mayer.SupportPartitionUrsellCoveringFiberResummationGeTwo`,
	            `Mayer.supportPartitionWeightedResummationGeTwo_of_coveringFiber_resummation`,
	            `Mayer.supportPartitionUrsellResummationGeTwo_of_coveringFiber_resummation`,
	            `Mayer.supportPartitionUrsellResummationGeTwo_of_exists_coveringFiber_resummation`,
	            and
	            `Rank.xop_advantageOn_injective_of_ursellCoveringFiberResummation_globalSupportFullAtomizedEval_cardBudget_quadratic`.
	            This proved the finite off-support cleanup and `Finset.sum_fiberwise`
	            reindexing once and leaves the genuine Penrose/Ursell work as the
	            exact child obligation: construct a source-faithful selector from
	            covering edge families to support-partition clusters and prove the
	            fiber identity for that selector.  It avoids choosing a premature
	            concrete selector while `S ⊆ edgeVertices Γ` still permits extra
	            touched vertices outside the ANOVA support.  The selector is now
	            dependent on the active hypotheses `S.Nonempty` and `2 ≤ S.card`,
	            avoiding the invalid total-selector demand on singleton supports
	            where `SupportPartitionClusters S` may be empty.
	      - [x] Add the Ursell coefficient/evaluation budget adapter:
	            `Rank.xop_advantageOn_injective_of_ursellResummationGeTwo_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic`
	            and
	            `Rank.xop_advantageOn_injective_of_existsUrsellCoveringFiber_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic`.
	            The weighted endpoint can now reuse an unweighted global
	            support-full-atomized evaluation by absorbing
	            `supportPartitionUrsellWeight` into the scalar coefficients and
	            paying the existing factorial bound
	            `Mayer.abs_supportPartitionUrsellWeight_le_factorial_card`.
	            The current composed parent leaves are now precisely:
	            selector existence plus fiber identity, unweighted global atomized
	            evaluation, and the factorial-paid scalar activity bound.
	      - [x] Add the source-faithful ambient selector layer forced by the
	            off-support-vertex issue:
	            `Mayer.SupportPartitionAmbientBlock`,
	            `Mayer.SupportPartitionAmbientClusters`,
	            `Mayer.SupportPartitionAmbientCoveringSelector`,
	            `Mayer.SupportPartitionAmbientFiberResummationGeTwo`, and
	            `Mayer.SupportPartitionAmbientToUrsellContractionGeTwo`, with the
	            adapter
	            `Mayer.supportPartitionUrsellResummationGeTwo_of_ambientFiber_contraction`.
	            A
	            covering family can have connected components that touch `S`
	            through vertices outside `S`; the ambient layer records those
	            components instead of inventing a cluster whose exact support is
	            only the intersection with `S`.  The selector branch is therefore
	            split into source-faithful ambient selection plus an explicit
	            Ursell/Penrose contraction from ambient indices to
	            `SupportPartitionClusters S`.
	            The rank-side composed endpoint
	            `Rank.xop_advantageOn_injective_of_ambientFiberContraction_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic`
	            now consumes this ambient branch directly together with the
	            unweighted global evaluation and factorial activity budget.
	      - [x] Close the source-faithful ambient selector/fiber branch:
	            `Mayer.completePairEdgeFamily`,
	            `Mayer.edgeVertices_completePairEdgeFamily`,
	            `Mayer.completePairEdgeFamily_pairConnected`, and
	            `Mayer.exists_pairCluster_of_two_le_card` provide the total
	            fallback needed by selectors without weakening the covering
	            theorem.  The covering branch is now the restricted component
	            partition
	            `(pairFamilyComponentFinpartition Γ).restrict hcover`, via
	            `Mayer.exists_component_part_of_mem_restrict`,
	            `Mayer.restrictedComponentAmbientPart`,
	            `Mayer.supportPartitionAmbientComponentSelector`, and
	            `Mayer.supportPartitionAmbientComponentSelector_spec`.
	            This proves `Mayer.supportPartitionAmbientCoveringSelector`.
	            The canonical selector
	            `Mayer.supportPartitionAmbientCoveringSelect` and contribution
	            `Mayer.supportPartitionCanonicalAmbientFiberContribution` then
	            close
	            `Mayer.supportPartitionCanonicalAmbientFiberResummationGeTwo`
	            by exact fiber definition.  The rank endpoint
	            `Rank.xop_advantageOn_injective_of_canonicalAmbientContraction_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic`
	            removes the abstract `hfiber` premise.  Ambient indices now
	            have reusable finite/decidable instances:
	            `Mayer.supportPartitionAmbientBlockFintype`,
	            `Mayer.supportPartitionAmbientBlockDecidableEq`,
	            `Mayer.supportPartitionAmbientClustersFintype`,
	            `Mayer.supportPartitionAmbientClustersDecidableEq`, and the
	            family instances needed by the existing contraction wrappers.
	            The remaining resummation child is now named exactly as
	            `Mayer.SupportPartitionCanonicalAmbientToUrsellContractionGeTwo`
	            for the intended block contribution.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Split the canonical ambient contraction into finite reindexing
	            and genuine cancellation.  The new theorem
	            `Mayer.sum_supportPartitionCanonicalAmbientFiberContribution_eq_covering`
	            proves that summing canonical ambient fibers over ambient
	            indices is exactly the covering edge-family sum.  The bridge
	            `Mayer.supportPartitionCanonicalAmbientToUrsellContractionGeTwo_of_coveringUrsell`
	            reduces the canonical ambient contraction to the remaining
	            covering-to-Ursell identity, now named
	            `Mayer.SupportPartitionCoveringUrsellContractionGeTwo`.
	            The rank endpoint
	            `Rank.xop_advantageOn_injective_of_coveringUrsell_unweightedGlobalSupportFullAtomizedEval_factorialBudget_quadratic`
	            now exposes that identity directly.  Contrarian/source-faithful
	            note: `Mayer.SupportPartitionCoveringUrsellContractionGeTwo` is
	            an interface Prop parameterized by `blockContribution`, not a
	            theorem to prove for arbitrary contributions.  A generic theorem
	            would be false by taking `blockContribution := 0`.  The strongest
	            path therefore remains the specialized normalized rank-certified
	            obligation
	            `Rank.RankCertifiedNormalizedUrsellCoveringFiberResummation`,
	            where the weight is `Rank.supportPartitionNormalizedUrsellWeight`
	            and blocks are
	            `Rank.rankCertifiedSignedPairMayerBlockContribution`.
	            Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Replace the direct normalized selector-fiber premise on the
	            strongest path by a source-faithful weighted ambient contraction:
	            `Mayer.SupportPartitionAmbientToWeightedContractionGeTwo`,
	            `Mayer.SupportPartitionCanonicalAmbientToWeightedContractionGeTwo`,
	            and
	            `Mayer.supportPartitionWeightedResummationGeTwo_of_ambientFiber_weightedContraction`
	            generalize the ambient bridge from bare Ursell weights to
	            arbitrary support-partition weights.  On the rank side,
	            `Rank.RankCertifiedNormalizedUrsellCanonicalAmbientContraction`
	            is now the live normalized/certified resummation leaf, and
	            `Rank.rankCertifiedNormalizedUrsell_weightedResummation_of_canonicalAmbientContraction`
	            supplies the weighted resummation premise.  The strongest
	            query-regime endpoint is now
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_canonicalAmbient_queryPairSlack_partitionEdgeSummability_quadratic`.
	            Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Expose the normalized/rank-certified hard leaf as a covering
	            contraction after canonical ambient reindexing:
	            `Mayer.SupportPartitionCoveringWeightedContractionGeTwo` names the
	            matched weighted covering-family identity, and
	            `Mayer.supportPartitionCanonicalAmbientToWeightedContractionGeTwo_of_coveringWeighted`
	            proves the finite reindexing bridge to canonical ambient fibers.
	            On the rank side,
	            `Rank.RankCertifiedNormalizedUrsellCoveringContraction` is the
	            specialized source-level leaf for
	            `Rank.supportPartitionNormalizedUrsellWeight` and
	            `Rank.rankCertifiedSignedPairMayerBlockContribution`; the bridge
	            `Rank.rankCertifiedNormalizedUrsell_canonicalAmbientContraction_of_coveringContraction`
	            feeds the canonical ambient endpoint, and the new endpoint
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringContraction_queryPairSlack_partitionEdgeSummability_quadratic`
	            exposes this leaf directly.  Verification:
	            `lake build RandomSystems.Applications.XoPMayer` and
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [ ] Prove the specialized covering contraction
	            `Rank.RankCertifiedNormalizedUrsellCoveringContraction`.
	            This is now the next theorem-DAG leaf.  It must identify, for
	            each nonempty `S` with `2 ≤ S.card`, the covering-family sum
	            `∑ Γ, anovaComponent S
	              (Mayer.componentFactorizedNormalizedPairFamilyTerm Γ)`
	            with the support-partition product using
	            `Rank.supportPartitionNormalizedUrsellWeight` and
	            `Rank.rankCertifiedSignedPairMayerBlockContribution`.  Reuse
	            existing local facts first:
	            `Mayer.componentFactorizedNormalizedPairFamilyTerm_eq_localSums`,
	            `Mayer.normalizedPairFamilyTerm_eq_componentFactorized`,
	            `Mayer.supportPartitionWeightedClusterProductContribution`,
	            `Rank.anovaComponent_signedPairMayerBlockContribution_eq_rankCertified`,
	            and the already-proved rank-certified block evaluation/budget
	            lemmas.  Do not attempt the false generic theorem for arbitrary
	            `blockContribution`.
	      - [x] Split the specialized covering contraction into local support
	            obligations:
	            `Rank.RankCertifiedNormalizedUrsellCoveringSupportContraction`
	            and
	            `Rank.RankCertifiedNormalizedUrsellCoveringSupportPointwise`
	            name the fixed-support and pointwise fixed-support forms, while
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportContraction_of_pointwise`
	            and
	            `Rank.rankCertifiedNormalizedUrsell_coveringContraction_of_supportContractions`
	            reassemble them into the global covering contraction.
	            The next mathematical split is now explicit in
	            `Rank.rankCertifiedNormalizedUrsell_coveringContraction_of_pair_and_ge_three`:
	            the base pair interaction `S.card = 2` and the genuine
	            higher-order support case `3 ≤ S.card`.
	      - [ ] Prove the base pair-support contraction
	            `∀ S ∈ coordinates q powerset, S.card = 2 →
	              Rank.RankCertifiedNormalizedUrsellCoveringSupportContraction K S`.
	            This should reuse the existing exact two-query/pair facts where
	            possible and the bridge
	            `Rank.anovaComponent_signedPairMayerBlockContribution_eq_rankCertified`.
	            Current obstruction: the existing selected-fiber bridge
	            `Rank.RankCertifiedNormalizedUrsellSelectedFiberIdentity` is
	            centered on the left, because the fiber sums are sums of
	            `anovaComponent S (...)`, but the current rank-certified
	            support contribution on the right is uncentered.  Read-only
	            review found that off-support families already vanish by
	            `Mayer.anovaComponent_normalizedPairFamilyTerm_eq_zero_of_not_subset'`
	            together with
	            `Mayer.normalizedPairFamilyTerm_eq_componentFactorized`; the
	            remaining mismatch is not off-support cleanup but centering.
	            The next base-branch step must replace the direct uncentered
	            fiber target by a centered identity, e.g. against
	            `anovaComponent S` applied to the weighted rank-certified
	            support contribution, or introduce a centered pair-support
	            contribution before invoking the fixed-support bridge.
	            This correction is now represented in Lean:
	            `Mayer.supportPartitionCoveringSupportContraction_of_selected_fibers`
	            gives generic fixed-support fiber reindexing for any indexed
	            target contribution, and
	            `Rank.rankCertifiedNormalizedUrsellSupportContribution`,
	            `Rank.RankCertifiedNormalizedUrsellCoveringSupportCenteredContraction`,
	            `Rank.RankCertifiedNormalizedUrsellCenteredSelectedFiberIdentity`,
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportCenteredContraction_of_centeredSelectedFiberIdentity`,
	            and
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportContraction_of_centeredSelectedFiberIdentity`
	            name the corrected centered branch and expose the exact extra
	            obligation required to recover the old uncentered contraction.
	            The corrected branch has also been connected back to the
	            theorem-facing support-indexed endpoint:
	            `Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedSupportPartition_resummation`
	            and
	            `Mayer.supportIndexedExpansionGeTwo_of_componentFactorized_centeredWeightedCoveringContraction`
	            adapt centered support-partition resummations to
	            `SupportIndexedExpansionGeTwo`, while
	            `Rank.RankCertifiedNormalizedUrsellCenteredCoveringContraction`,
	            `Rank.rankCertifiedNormalizedUrsell_centeredCoveringContraction_of_supportContractions`,
	            `Rank.rankCertifiedNormalizedUrsell_supportIndexedExpansion_of_centeredCoveringContraction`,
	            and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_activity_quadratic`
	            provide the corrected quadratic endpoint.  Its remaining
	            analytic premise is now an activity bound on the centered
	            indexed contributions, so any cost from ANOVA projection is
	            explicit rather than hidden.
	            `Rank.rankCertifiedNormalizedUrsell_centeredActivityBound_of_rawActivity`
	            then bridges that activity premise back to raw uncentered
	            support-contribution activity by paying the standard
	            `S.powerset.card` ANOVA projection factor.  This keeps existing
	            rank/atomization budget machinery reusable while making the
	            centering loss explicit in the local-activity scalar branch.
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_rawActivity_quadratic`
	            composes the centered contraction, raw activity, centering
	            scalar, and quadratic summability into a single theorem-facing
	            endpoint.
	            `Rank.rankCertifiedNormalizedUrsell_rawActivityBound_of_indexCardBudget`
	            adds the next scalar bridge: per-index
	            `visibleL1 ≤ rankCertifiedNormalizedUrsellIndexCardBudget`
	            plus a summed index-card budget gives raw uncentered support
	            activity.
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_indexCardBudget_quadratic`
	            composes this bridge into the corrected centered quadratic
	            endpoint.
	            `Rank.rankCertifiedNormalizedUrsellSupportContribution_visibleL1_le_indexCardBudget`
	            now proves the single-index estimate
	            `visibleL1 (rankCertifiedNormalizedUrsellSupportContribution K S idx)
	            ≤ rankCertifiedNormalizedUrsellIndexCardBudget K S idx` by
	            reusing the existing block-local rank-certified atomized
	            evaluation machinery and the joint-rank fiber budget; no
	            disconnected helper lemma was introduced.
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_indexBudget_quadratic`
	            discharges that local premise in the theorem-facing centered
	            endpoint.  The centered branch has also been lifted through the
	            existing scalar chain:
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_factorialThreePowEdgeBudget_quadratic`,
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_partitionEdgeSummability_quadratic`,
	            and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_queryPairSlack_partitionEdgeSummability_quadratic`.
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centeredCoveringContraction_queryPairSlack_partitionEdgeSummability_centeredActivity_quadratic`
	            absorbs the ANOVA-centering cost into a per-cardinality `2^k`
	            local-activity premise using `Finset.card_powerset`.  The next
	            theorem-facing wrapper,
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_queryPairSlack_partitionEdgeSummability_centeredActivity_quadratic`,
	            splits the centered covering contraction into its base pair
	            support branch and its genuine `3 ≤ |S|` Penrose/Ursell branch.
	            This avoids routing the corrected centered endpoint through the
	            old uncentered covering-fiber theorem.
	            `Rank.rankCertifiedSupportPartitionEdgeActivity`,
	            `Rank.rankCertifiedSupportPartitionEdgeActivity_nonneg`, and
	            `Rank.rankCertifiedSupportPartitionEdgeActivity_bound` replace
	            the abstract support-partition edge-summability witness by the
	            exact finite cardinality-indexed edge activity.  The scalar
	            endpoint
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_pair_and_ge_three_exactEdgeActivity_growth_quadratic`
	            now asks directly for the pure growth inequality
	            `2^k * k! * edgeActivity(k) * 4 ≤ C^k`.
	            The current strongest named endpoint is
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_named_obligations_quadratic`.
	            Its remaining named leaves are
	            `Rank.RankCertifiedNormalizedUrsellCenteredPairSupportContractions`,
	            `Rank.RankCertifiedNormalizedUrsellCenteredHigherSupportContractions`,
	            and
	            `Rank.RankCertifiedSupportPartitionEdgeActivityGrowth`.
	            The base pair branch has been pushed one level lower:
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportCentered_lhs_eq_xopError`
	            proves that the filtered centered covering-family sum is
	            exactly `anovaComponent S xopError`, and
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportCenteredContraction_of_xopError_anova`
	            turns a direct `xopError` ANOVA identity into the centered
	            fixed-support contraction.
	            `Rank.RankCertifiedNormalizedUrsellCenteredPairSupportAnovaIdentities`
	            is now the lower base-pair leaf, and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_centered_anovaPair_named_obligations_quadratic`
	            is the strongest endpoint using that lower pair leaf.
	            The higher branch now has the source-faithful ambient leaf
	            named as
	            `Rank.RankCertifiedNormalizedUrsellCenteredCanonicalAmbientHigherContraction`.
	            A direct wrapper from this ambient leaf to
	            `RankCertifiedNormalizedUrsellCenteredHigherSupportContractions`
	            was attempted but removed because the naive function-level
	            bridge forced expensive normalization and timed out; reintroduce
	            it later with a lighter theorem statement or a helper lemma in
	            `XoPMayer` that packages the canonical ambient fiber sum without
	            unfolding large indexed contributions.
	            The next
	            connected proof leaves are now exactly the premises of that
	            strongest centered endpoint: prove the centered covering
	            contraction, prove support-partition/Penrose edge summability,
	            and prove the final scalar local-activity tail bound for the
	            chosen `partitionActivity`.
	            Verification: targeted
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings appeared.
	      - [ ] Prove the higher-order support contraction
	            `∀ S ∈ coordinates q powerset, 3 ≤ S.card →
	              Rank.RankCertifiedNormalizedUrsellCoveringSupportContraction K S`.
	            This is the genuine Penrose/tree-graph contraction leaf; it must
	            keep the pair-Mayer expansion intact before any atomization and
	            must not use raw colored-bond KP.
	            Read-only exploration found no existing local Penrose/tree-graph
	            lemma that closes this branch.  The first real missing theorem is
	            a selected-fiber identity for a source-faithful support selector:
	            each fiber of covering edge families over one
	            `Mayer.SupportPartitionClusters S` index must equal the
	            corresponding normalized Ursell-weighted product of
	            rank-certified signed pair-Mayer blocks.
	            Follow-up review sharpened this: for `3 ≤ S.card`, the selector
	            should be source-faithful and ambient-component based, using
	            `Mayer.SupportPartitionAmbientClusters S` and
	            `Mayer.supportPartitionAmbientCoveringSelect`, rather than a
	            direct selector into `Mayer.SupportPartitionClusters S`.  A
	            covering edge family can have components with vertices in
	            `edgeVertices Γ \ S`; collapsing those directly to a support
	            partition erases exactly the ambient support needed for the
	            Mayer/Ursell cancellation.  The next higher-branch API should
	            therefore expose an ambient selected-fiber identity and a
	            separate ambient-to-weighted contraction, instead of forcing
	            `Rank.RankCertifiedNormalizedUrsellSelectedFiberIdentity`.
	      - [x] Add pair-support structural utilities forced by the base branch:
	            `Mayer.exists_pairEdge_edgeVertices_singleton_eq_of_card_eq_two`
	            uses Mathlib's `Finset.card_eq_two` to choose the unique
	            two-point pair edge, and
	            `Mayer.pairConnected_singleton` proves singleton edge-family
	            connectedness.  The two-point transport utilities
	            `Mayer.cardTwoSupportEquivFin2` and
	            `Mayer.cardTwoRestrictTuple` use Mathlib's
	            `Fintype.equivFinOfCardEq`/`Fintype.card_coe` to reindex an
	            arbitrary two-point support as `Fin 2`, and
	            `Mayer.singletonPairCluster`/
	            `Mayer.singletonPairClusterOfCardEqTwo` package singleton
	            edge families as exact clusters.  These feed the base
	            pair-support contraction without reconstructing basic finite-set
	            facts locally.
	            `Mayer.supportPartitionClusters_parts_card_eq_one_of_support_card_eq_two`
	            proves that a support-partition cluster on a two-point support
	            has exactly one block, because every block carries a pair
	            cluster and therefore has cardinality at least two.
	            `Mayer.supportPartitionClusters_block_eq_support_of_card_eq_two`,
	            `Mayer.supportPartitionClusters_parts_univ_eq_singleton_of_card_eq_two`,
	            and `Mayer.supportPartitionClustersUniqueBlockOfCardEqTwo`
	            strengthen that base-case structure: the unique block is the
	            whole support, and products over blocks collapse to that block.
	            `Mayer.supportPartitionClusterProductContribution_cardTwo`
	            packages the corresponding support-partition product collapse.
	            `Mayer.pairEdge_eq_of_support_card_eq_two` proves that a
	            two-point support has only one oriented pair edge, and
	            `Mayer.exists_pairClusterSupportEdges_eq_singleton_of_support_card_eq_two`
	            turns any pair cluster on such a support into a singleton
	            support-retyped edge family.
	            `Rank.supportPartitionNormalizedUrsellWeight_cardTwo`
	            simplifies the normalized Ursell coefficient in this base case
	            to the complement-normalizer factor.
	            `Rank.supportPartitionWeightedRankCertifiedContribution_cardTwo`
	            and its `..._uniqueBlock` variant combine the two-point
	            normalized coefficient with the unique-block product collapse.
	      - [x] Add the theorem-forced certified singleton atom-choice facts
	            needed by the base pair-support branch:
	            `Rank.pairAtomChoiceFamilyAtoms_singleton`,
	            `Rank.not_hasVisibleObstruction_pairAtomChoiceAtoms_hidden`,
	            `Rank.not_hasVisibleObstruction_pairAtomChoiceAtoms_shifted`,
	            `Rank.rankCertifiedPairAtomChoiceFamily_singleton_choice_eq_both`,
	            `Rank.rankCertifiedPairAtomChoiceFamilyCoeff_singleton`, and
	            `Rank.rankCertifiedPairAtomChoiceFamilyAtoms_singleton`.  These
	            show that a certified one-edge block cannot be hidden-only or
	            shifted-only; its only surviving certified term is the `both`
	            term with coefficient `1` and full hidden+shifted atom family.
	            `Rank.rankCertifiedPairAtomChoiceFamilySingletonBoth`,
	            `Rank.rankCertifiedPairAtomChoiceFamily_singleton_eq`, and
	            `Rank.rankCertifiedPairAtomChoiceFamily_singleton_subsingleton`
	            package the unique certified singleton term, while
	            `Rank.rankCertifiedSignedPairMayerBlockContribution_of_supportEdges_singleton`
	            evaluates any certified block whose support-retyped edge set is
	            a singleton as the full hidden+shifted atom fiber for that edge.
	            `Rank.exists_rankCertifiedSignedPairMayerBlockContribution_cardTwo_fullAtomFiber`
	            and
	            `Rank.exists_supportPartitionWeightedRankCertifiedContribution_cardTwo_fullAtomFiber`
	            combine the two-point support structure, singleton certified
	            term, normalized Ursell coefficient, and block evaluator into
	            a support-side full-edge-atom-fiber normal form.
	            The follow-up forced by this normal form is now proved:
	            `Rank.pairEdgeFullAtomsCardTwoFiberEquiv`,
	            `Rank.card_pairEdgeFullAtoms_cardTwo_eq_of_visible_eq`,
	            `Rank.card_pairEdgeFullAtoms_cardTwo_eq_zero_of_visible_ne`,
	            and `Rank.card_pairEdgeFullAtoms_cardTwo` identify the local
	            full hidden+shifted atom fiber as `|K|` on the visible collision
	            event and `0` off that event.  This concrete base-case
	            evaluation is also the evidence for the centering mismatch
	            above: the uncentered RHS is a positive collision indicator,
	            whereas a nonempty ANOVA component has zero uniform average.
	            `Rank.exists_supportPartitionWeightedRankCertifiedContribution_cardTwo_collisionIndicator`
	            lifts this fiber normal form to the complete two-point
	            support-partition weighted rank-certified contribution.
	            Verification: targeted
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings appeared.
	      - [x] Add the fixed-support selected-fiber bridge:
	            `Mayer.supportPartitionCoveringWeightedSupportContraction_of_selected_fibers`
	            proves the finite `Finset.sum_fiberwise` reindexing for one
	            fixed support and arbitrary matched weight/block contribution.
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportContraction_of_selected_fibers`
	            specializes it to
	            `Rank.supportPartitionNormalizedUrsellWeight` and
	            `Rank.rankCertifiedSignedPairMayerBlockContribution`.
	            `Rank.RankCertifiedNormalizedUrsellSelectedFiberIdentity`
	            names the exact remaining fiberwise equality for a chosen
	            support selector, and
	            `Rank.rankCertifiedNormalizedUrsell_coveringSupportContraction_of_selectedFiberIdentity`
	            reconnects that hard leaf to the fixed-support contraction.
	            Verification: full `lake build` and targeted
	            `lake build RandomSystems.Applications.XoPRank` passed after the
	            bridge.
	      - [x] Add the full-atomization semantic leaves required by the future
	            global evaluation proof:
            `Rank.atomFamilyHolds_pairEdgeFullAtoms_iff` and
            `Rank.atomFamilyHolds_pairFamilyFullAtoms_iff`.
            These identify a full hidden/shifted atom family with the
            conjunction of the hidden and shifted collision equations over all
            selected pair edges, reusing the existing pair-edge atomization
            boundary instead of introducing a colored-bond expansion upstream
            of pair-Mayer cancellation.
	      - [x] Add the global support-partition semantic bridge
	            `Rank.atomFamilyHolds_supportPartition_supportFullAtoms_iff`.
	            This combines the existing block-union atom bridge with the new
	            full-atomization semantics, so the future `heval` proof can reason
	            directly about all support-retyped block edges rather than unpacking
	            `supportPartitionAtomFamily` by hand.
	      - [x] Add the support-partition assignment product bridge needed by the
	            unweighted global evaluation leaf:
	            `Rank.supportPartitionAssembleWithOutside`,
	            `Rank.supportPartitionAssembleWithOutside_eq_of_mem`,
	            `Rank.supportPartitionAssembleWithOutside_eq_of_not_mem`, and
	            `Rank.supportPartitionAssignmentEquiv`, plus the cardinality
	            corollary `Rank.card_supportPartitionAssignmentProduct`.  This gives the reusable
	            finite equivalence between a global hidden tuple and
	            outside-support coordinates plus one tuple on each partition block.
	            The next `heval` step can use it to turn products of block-local
	            hidden sums into a single support-partition hidden-fiber count with
	            an explicit power-of-`|K|` factor.
	      - [x] Prove the algebraic product-of-block-sums part of the unweighted
	            evaluation leaf:
	            `Mayer.supportPartitionClusterProductContribution_eq_sum_pi_blockValues`
	            and
	            `Mayer.supportPartitionClusterProductContribution_eq_sum_pi_blockCoeff_mul_values`.
	            This reuses Mathlib's `Fintype.prod_sum` to expand the product of
	            block contributions into a sum over dependent choices of one block
	            term per support-partition part, then separates scalar block
	            coefficients from block fiber-count factors.  The remaining
	            evaluation work is now the count assembly step from products of
	            block-local hidden fiber counts to one global support-partition
	            hidden-fiber count.
	      - [x] Prove the hidden-fiber count assembly step for the unweighted
	            global evaluation leaf:
	            `Rank.atomFamilyHolds_congr_on_atomVertices`,
	            `Rank.atomFamilyHolds_congr_on_support`,
	            `Rank.supportSubtypeLift`,
	            `Rank.AtomFamilyHoldsOn`,
	            `Rank.atomFamilyHolds_iff_atomFamilyHoldsOn_of_eq_on_support`,
	            `Rank.atomFamilyHolds_supportPartitionAssembleWithOutside_iff`,
	            `Rank.supportPartitionAtomFamilyHiddenFiberEquiv`,
	            `Rank.supportPartitionBlockHiddenFiberEquiv`,
	            `Rank.card_supportPartition_blockHiddenFiber`,
	            `Rank.card_supportPartitionAtomFamily_hiddenFiber_eq_outside_mul_prod_blocks`,
	            and
	            `Rank.prod_blockHiddenFiber_card_eq_global_div_outside_real`.
	            This closes the contrarian overcounting objection: block products
	            are over assignments `B.1 → K`, not fresh full assignments
	            `Fin q → K`, and the single free outside-support factor appears
	            explicitly in the coefficient arithmetic.
	      - [x] Lift block-local atomized evaluations to the theorem-facing
	            global `heval` shape:
	            `Rank.supportPartitionClusterProductContribution_eq_sum_pi_blockLocalAtomized`
	            and
	            `Rank.xop_advantageOn_injective_of_ursellResummationGeTwo_blockLocalAtomizedEval_factorialBudget_quadratic`.
	            The new endpoint consumes block-local hidden-fiber evaluations,
	            the required support-retyped full-atomization identity for each
	            block term, and a scalar budget with coefficient
	            `∏ blockCoeff / |outside(S)|`.  It no longer requires a primitive
	            global atomized evaluation assumption.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [ ] Construct the concrete block contribution family and prove its
	            block-local atomized evaluation:
	            for each `PairCluster S`, define the Penrose/Ursell block term
	            type, coefficient, and full support atom family so that
	            `blockContribution S C y` expands as a finite signed sum of
	            local hidden fibers
	            `{aS : S → K // AtomFamilyHoldsOn y (pairFamilyFullAtoms
	            (pairClusterSupportEdges C)) aS}`.
	            Status: the full-atomized candidate contribution is now defined
	            and its block-local evaluation is proved:
	            `Rank.supportFullAtomizedBlockContribution`,
	            `Rank.supportFullAtomizedBlockContribution_blockLocalEval`, and
	            `Rank.xop_advantageOn_injective_of_ursellResummationGeTwo_supportFullAtomizedBlockContribution_factorialBudget_quadratic`.
	            The remaining part of this item is no longer the local
	            evaluation, but the mathematical question whether the true
	            Penrose/Ursell resummation should target this full-atomized
	            candidate or a signed correction of it.  This is logged below as
	            the concrete resummation leaf.
	      - [x] Reject the full-atomized candidate as the exact resummation
	            target and replace it by the signed/certified block-local route.
	            Independent reviewers found the same obstruction: for a one-edge
	            two-point support, the pair-Mayer source term is
	            `-hidden - shifted + both`, while
	            `Rank.supportFullAtomizedBlockContribution` keeps only the
	            positive `both` fiber; the one-block Ursell coefficient cannot
	            repair this mismatch, and it also omits the normalization in
	            `componentFactorizedNormalizedPairFamilyTerm`.
	      - [x] Add the source-faithful signed local block contribution and its
	            atom-choice evaluation:
	            `Rank.sum_atomFamilyHoldsOn_indicator_eq_card`,
	            `Rank.signedPairMayerBlockContribution`, and
	            `Rank.signedPairMayerBlockContribution_blockLocalEval`.
	            This proves the local pair-Mayer product is expanded only after
	            the signed pair-level cancellation
	            `-hidden - shifted + both` has been formed.
	      - [x] Prove the first low-rank ANOVA cancellation leaf for hidden-only
	            atom-choice terms:
	            `Rank.PairAtomChoiceFamilyAllHidden`,
	            `Rank.atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_iff`,
	            `Rank.card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allHidden_eq`,
	            and
	            `Rank.anovaComponent_hiddenOnly_atomChoiceFiber_eq_zero_of_nonempty`.
	            This formalizes one concrete way uncertified raw terms disappear
	            before the rank/codimension endpoint sees them.
	      - [x] Prove the shifted-only low-rank ANOVA cancellation leaf:
	            `Rank.PairAtomChoiceFamilyAllShifted`,
	            `Rank.shiftedLocalAssignmentEquiv`,
	            `Rank.atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_iff`,
	            `Rank.pairBadShifted_shiftedLocalAssignmentEquiv`,
	            `Rank.card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_allShifted_eq`,
	            and
	            `Rank.anovaComponent_shiftedOnly_atomChoiceFiber_eq_zero_of_nonempty`.
	            This closes the symmetric singleton-color obstruction: shifted-only
	            raw terms have no visible obstruction, but their local hidden-fiber
	            cardinality is independent of the visible transcript after
	            translation by `y - y'`, so any nonempty ANOVA component kills them.
	            Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Prove that `both` atom-choice terms are already certified:
	            `Rank.hiddenAtomLinked_pairAtomChoiceFamilyAtoms_self_of_both`
	            and `Rank.hasVisibleObstruction_of_pairAtomChoiceFamily_both`.
	            A `both` edge contains its own hidden atom and shifted atom, so it
	            provides a one-edge visible-obstruction witness without waiting for
	            higher-order centering.
	      - [x] Add the general no-visible-obstruction constant-fiber
	            cancellation interface:
	            `Rank.atomFamily_solution_card_eq_of_forall_feasible`,
	            `Rank.atomFamily_solution_card_eq_of_not_hasVisibleObstruction`,
	            `Rank.atomFamilyLocalHiddenFiberEquiv`,
	            `Rank.card_atomFamily_hiddenFiber_eq_outside_mul_local`,
	            `Rank.card_atomFamilyHoldsOn_eq_of_not_hasVisibleObstruction`,
	            `Rank.anovaComponent_atomChoiceFiber_eq_zero_of_not_hasVisibleObstruction`,
	            `Rank.card_atomFamilyHoldsOn_pairAtomChoiceFamilyAtoms_eq_of_not_hasVisibleObstruction`,
	            and
	            `Rank.anovaComponent_atomChoiceFiber_eq_zero_of_not_hasVisibleObstruction'`.
	            This replaces incomplete graph slogans such as "single shifted
	            edge plus hidden path" with the correct linear-algebraic dichotomy:
	            if a local atom-choice term has no visible obstruction, every
	            visible RHS is feasible and all hidden fibers have the same kernel
	            cardinality, so nonempty ANOVA kills the term.  If it has a
	            visible obstruction, it belongs in the certified rank endpoint.
	            Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Add the rank-certified atom-choice interface:
	            `Rank.RankCertifiedPairAtomChoiceFamily`,
	            `Rank.rankCertifiedPairAtomChoiceFamilyEquivSubtype`,
	            `Rank.rankCertifiedPairAtomChoiceFamilySubtypeFintype`,
	            `Rank.rankCertifiedPairAtomChoiceFamilyCoeff`,
	            `Rank.rankCertifiedPairAtomChoiceFamilyAtoms`,
	            `Rank.sum_rankCertifiedPairAtomChoiceFamily_eq_subtype`,
	            `Rank.rankCertifiedPairAtomChoiceFamily_hasVisibleObstruction`,
	            `Rank.jointRank_rankCertifiedPairAtomChoiceFamily_ge_card_of_pairConnected`,
	            `Rank.atomVertices_rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges`,
	            and
	            `Rank.rankCertifiedPairAtomChoiceFamilyAtoms_pairClusterSupportEdges_connected`.
	            This is the theorem-facing type the genuine centered/Ursell
	            construction should emit instead of all raw pair-atom choices.
	      - [x] Prove the certified-centering replacement for a single signed
	            block:
	            `ANOVA.project_const_mul`,
	            `ANOVA.anovaComponent_fintype_sum`,
	            `ANOVA.anovaComponent_const_mul`,
	            `Rank.anovaComponent_rawPairAtomChoiceFamily_sum_eq_rankCertified_sum`,
	            and
	            `Rank.anovaComponent_signedPairMayerBlockContribution_eq_rankCertified`.
	            This is the first source-faithful bridge from raw signed
	            pair-Mayer atomization to the certified rank endpoint: after a
	            nonempty ANOVA projection, every raw atom-choice term without
	            visible obstruction vanishes by the constant-fiber lemma, and
	            the remaining obstructed terms reindex exactly as
	            `RankCertifiedPairAtomChoiceFamily`.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Add the corrected weighted/certified theorem-facing endpoint:
	            `Rank.xop_advantageOn_injective_of_weightedResummation_blockLocalSignedAtomizedEval_cardBudget_quadratic`.
	            Unlike the rejected full-atomized branch, this endpoint accepts a
	            weighted support-partition resummation and requires rank
	            certificates only for the block terms that actually survive the
	            ANOVA/Ursell construction.
	      - [x] Name the source-normalized Ursell coefficient:
	            `Rank.supportPartitionNormalizedUrsellWeight`, and add
	            `Rank.xop_advantageOn_injective_of_normalizedUrsell_blockLocalSignedAtomizedEval_cardBudget_quadratic`.
	            This fixes the earlier normalization mismatch by including the
	            outside-support hidden-assignment factor and
	            `visibleNormalizerNNReal` directly in the partition weight.
	      - [ ] Prove the centered/certified signed block contribution leaf:
	            construct the actual Penrose/Ursell block contribution whose
	            terms satisfy the block-local vertex, connectivity, and
	            `HasVisibleObstruction` premises consumed by
	            `xop_advantageOn_injective_of_normalizedUrsell_blockLocalSignedAtomizedEval_cardBudget_quadratic`.
	            Raw `PairAtomChoice` terms are not enough: hidden-only choices
	            have no visible obstruction, and shifted-only terms do not by
	            themselves give the `S.card` joint-rank budget.  The missing
	            theorem must express the ANOVA/Ursell cancellation or centering
	            that removes/repackages these low-rank terms before the rank
	            budget is applied.
	            Status update: the theorem-facing certified block wrapper is
	            now implemented and checked:
	            `Rank.rankCertifiedSignedPairMayerBlockContribution`,
	            `Rank.rankCertifiedSignedPairMayerBlockContribution_blockLocalEval`,
	            and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_cardBudget_quadratic`.
	            This closes only the structural endpoint plumbing.  It does
	            not prove source-faithful cancellation: the required remaining
	            premise is exactly
	            `Mayer.SupportPartitionWeightedResummationGeTwo
	            (Rank.supportPartitionNormalizedUrsellWeight K)
	            (Rank.rankCertifiedSignedPairMayerBlockContribution K)`.
	            Reviewer verdict: this direct certified resummation is not
	            justified by filtering raw `PairAtomChoice` terms; it must be
	            proved from `Rank.signedPairMayerBlockContribution` and the
	            ANOVA/Ursell centering that kills or repackages every
	            non-certified raw atom-choice contribution.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Add the weighted covering-fiber child obligation for the
	            certified normalized-Ursell resummation:
	            `Mayer.SupportPartitionWeightedCoveringFiberResummationGeTwo`,
	            `Mayer.supportPartitionWeightedResummationGeTwo_of_exists_coveringFiber_resummation`,
	            and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_cardBudget_quadratic`.
	            This turns the hard certified resummation premise into a
	            selector-fiber theorem: construct a concrete selector from
	            covering pair-edge families to support-partition indices, and
	            prove each fiber equals the normalized weighted certified block
	            contribution.  The no-obstruction ANOVA kill above is the local
	            tool for removing terms that do not enter
	            `RankCertifiedPairAtomChoiceFamily`; obstructed terms are routed
	            to the rank endpoint.  Verification: full `lake build` passed
	            with XoPMayer and XoPRank rebuilt; only unrelated existing
	            warnings remain.
	      - [ ] Prove the corresponding factorial-paid scalar activity budget
	            for the block-local endpoint, including the outside-support
	            denominator and the `supportPartitionUrsellWeight` factorial
	            factor.
	            Status update for the certified normalized-Ursell route:
	            `Rank.abs_rankCertifiedPairAtomChoiceFamilyCoeff`,
	            `Rank.rankCertifiedBlockChoiceAssignments`,
	            `Rank.rankCertifiedBlockChoiceAssignmentsFintype`,
	            `Rank.rankCertifiedBlockChoiceAssignmentsCard`,
	            `Rank.rankCertifiedNormalizedUrsellIndexCardBudget`, and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_indexCardBudget_quadratic`
	            are now checked.  This removes the signed coefficient product
	            from the scalar budget.  The remaining budget leaf is the
	            product-count estimate
	            `∑_idx Rank.rankCertifiedNormalizedUrsellIndexCardBudget K S idx
	            ≤ localActivity S.card`, then the usual support-size activity
	            bound `localActivity k ≤ (C/N)^k`.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	            Status: the `Unit` block-term sum for the full-atomized
	            candidate has been simplified to the real combinatorial burden:
	            `Rank.xop_advantageOn_injective_of_ursellResummationGeTwo_supportFullAtomizedBlockContribution_indexCardBudget_quadratic`
	            now requires a budget with
	            `Fintype.card (Mayer.SupportPartitionClusters S)` times the
	            outside-denominator weight, rather than an opaque dependent sum
	            over unit terms.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	            Certified-route progress: the certificate-count and normalizer
	            algebra have now been reduced to a pure scalar
	            support-partition estimate.  New checked lemmas/endpoints:
	            `Rank.card_pairAtomChoiceFamily`,
	            `Rank.card_rankCertifiedPairAtomChoiceFamily_le_three_pow`,
	            `Rank.rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_edges`,
	            `Rank.prod_three_pow_pairClusterSupportEdges_card`,
	            `Rank.rankCertifiedBlockChoiceAssignmentsCard_le_three_pow_sum_supportEdges`,
	            `Rank.rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_edges`,
	            `Rank.rankCertifiedNormalizedUrsellIndexCardBudget_le_three_pow_sum_supportEdges`,
	            `Rank.rankCertifiedNormalizedUrsellIndexCardBudget_le_factorial_three_pow_edges`,
	            `Rank.rankCertifiedNormalizedUrsell_sum_indexCardBudget_le_of_factorial_three_pow_edges`,
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_threePowEdgeBudget_quadratic`,
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_threePowSumEdgeBudget_quadratic`, and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_factorialThreePowEdgeBudget_quadratic`.
	            The current budget leaf is no longer about signed coefficients,
	            certified subtypes, or outside-support cancellation.  It is the
	            mathematical Penrose/tree estimate:
	            for every ge-two support `S`, bound
	            `∑ idx, 3^(∑ block edge-counts) * S.card! *
	            ((|K|^q / visibleNormalizerNNReal) / |K|^S.card)` by
	            `localActivity S.card`, then show
	            `localActivity k ≤ (C/|K|)^k`.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	            Scalar split progress: `ANOVA.visibleNormalizerSlackReal`,
	            `ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq`,
	            `ANOVA.visibleNormalizerSlackReal_le_of_pow_le_const_mul_descFactorial_sq`,
	            `Rank.rankCertifiedNormalizedUrsell_hscalar_of_partitionEdgeSummability`,
	            and
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_partitionEdgeSummability_quadratic`
	            now isolate two independent remaining scalar leaves:
	            (1) a query-regime bound on
	            `visibleNormalizerSlackReal K q`, and
	            (2) a genuine Penrose/tree summability bound for
	            `∑ idx, 3^(∑ block edge-counts)`.  Naive positive cluster
	            counting is explicitly insufficient here because it leaves the
	            `2^(k.choose 2)` graph-count explosion and cannot feed
	            `localActivity k ≤ (C/|K|)^k`.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	            Normalizer leaf progress: the query-regime branch is now
	            checked.  New theorem-forced lemmas in `XoPANOVA.lean`:
	            `ANOVA.query_le_of_queryPair_le_card`,
	            `ANOVA.prod_one_sub_ge_one_sub_sum`,
	            `ANOVA.descFactorial_div_pow_ge_one_sub_sum`,
	            `ANOVA.sum_range_div_card_le_half_of_queryPair_le_card`,
	            `ANOVA.pow_le_two_mul_descFactorial_of_queryPair_le_card`,
	            `ANOVA.visibleNormalizerSlackReal_le_four_of_pow_le_two_descFactorial`,
	            and
	            `ANOVA.visibleNormalizerSlackReal_le_four_of_queryPair_le_card`.
	            The rank endpoint
	            `Rank.xop_advantageOn_injective_of_rankCertifiedNormalizedUrsell_coveringFiber_queryPairSlack_partitionEdgeSummability_quadratic`
	            now consumes the concrete side condition
	            `q * (q - 1) ≤ Fintype.card K` and removes the abstract
	            normalizer-slack premise.  Verification:
	            `lake build RandomSystems.Applications.XoPRank` passed; only
	            unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Resolve the concrete full-atomized Ursell resummation leaf by
	            rejection:
	            `Mayer.SupportPartitionUrsellResummationGeTwo
	            Rank.supportFullAtomizedBlockContribution` is not the
	            source-faithful target.  It has been replaced by the
	            normalized weighted signed/certified endpoint above; no further
	            work should try to prove this false full-atomized resummation
	            identity.
		  - [ ] Prove selected-tree fiber bounds for that concrete contribution family,
		        then feed them through
	        `pairClusterPenroseActivityBoundGeTwo_of_selectedContributionFiberBound`.
- [ ] Show that atomization into colored constraints is performed only after the
      pair-level cancellation is established.
- [ ] Prove that raw colored-bond KP is not used in the accepted proof path.
- [x] Add the valid all-edge-family budget bridge
      `Mayer.coveringEdgeFamilyActivity_of_termwise_bound` and the direct
      theorem-spine endpoint
      `Mayer.xop_advantageOn_injective_of_coveringEdgeFamily_termwiseBudget_pow_small_q`.
  - [x] Add the sharper ge-two covering budget bridge
        `Mayer.coveringEdgeFamilyActivityGeTwo_of_termwise_bound`, the direct
        component bridge
        `Mayer.componentL1Bound_of_coveringEdgeFamilyActivityGeTwo`, and the
        scalar theorem-spine endpoint
        `Mayer.xop_advantageOn_injective_of_coveringEdgeFamily_geTwo_termwiseBudget_pow_small_q`.
        Verification: `lake build RandomSystems.Applications.XoPMayer
        RandomSystems.Applications.XoPRank` passed; warnings are unrelated
        pre-existing PRP/PRF lints.
  - [x] Add the component-factorized theorem-spine endpoint
        `Mayer.xop_advantageOn_injective_of_factorizedCoveringEdgeFamily_geTwo_termwiseBudget_pow_small_q`
        using
        `Mayer.componentFactorizedNormalizedPairFamilyTerm` and
        `Mayer.normalizedPairFamilyTerm_eq_componentFactorized`.
  - [x] Prove the generic ANOVA/projection `L¹` reduction and its factorized
        Mayer specialization:
        `ANOVA.visibleL1_anovaComponent_le_card_powerset_mul_visibleL1`,
        `Mayer.visibleL1_anovaComponent_componentFactorized_le`, and
        `Mayer.xop_advantageOn_injective_of_factorizedL1Budget_geTwo_pow_small_q`.
        Verification: `lake build RandomSystems.Applications.XoPANOVA
        RandomSystems.Applications.XoPMayer RandomSystems.Applications.XoPRank`
        passed; warnings are unrelated pre-existing PRP/PRF lints.
  - [x] Name component-local hidden sums and prove their support API:
        `Mayer.pairFamilyComponentLocalSum`,
        `Mayer.componentFactorizedNormalizedPairFamilyTerm_eq_localSums`,
        `Mayer.pairFamilyComponentLocalProduct_eq_of_eq_on_componentVertices`,
        `Mayer.pairFamilyComponentLocalSum_eq_of_eq_on_componentVertices`,
        `Mayer.restrictInvariant_pairFamilyComponentLocalSum`, and
        `Mayer.project_pairFamilyComponentVertices_localSum`.
        Verification: `lake build RandomSystems.Applications.XoPANOVA
        RandomSystems.Applications.XoPMayer RandomSystems.Applications.XoPRank`
        passed; warnings are unrelated pre-existing PRP/PRF lints.
  - [x] Prove the crude baseline bounds
        `Mayer.abs_pairMayerFactor_le_one`,
        `Mayer.abs_pairFamilyComponentLocalProduct_le_one`,
        `Mayer.abs_pairFamilyComponentLocalSum_le_card`,
        `Mayer.abs_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard`,
        and
        `Mayer.visibleL1_componentFactorizedNormalizedPairFamilyTerm_le_crudeCard`.
        Verification: `lake build RandomSystems.Applications.XoPANOVA
        RandomSystems.Applications.XoPMayer RandomSystems.Applications.XoPRank`
        passed; only unrelated pre-existing PRP/PRF warnings remain.
  - [x] Prove the product-space averaging lemma for component-local sums over
        pairwise disjoint component supports:
        `visibleL1 (fun y => ∏ C, pairFamilyComponentLocalSum Γ C y) =
         ∏ C, visibleL1 (pairFamilyComponentLocalSum Γ C)`.
        Proved as exact equalities, not an unsupported independence assertion:
        `Mayer.visibleL1_eq_visibleL1On_of_restrictInvariant`,
        `Mayer.uniformAverage_pi_prod`,
        `Mayer.uniformAverage_equiv`,
        `Mayer.pairFamilyComponentLocalSum_extendOn_support_eq_component`,
        `Mayer.visibleL1On_edgeVertices_prod_pairFamilyComponentLocalSum`,
        `Mayer.restrictInvariant_prod_pairFamilyComponentLocalSum`,
        `Mayer.visibleL1_prod_pairFamilyComponentLocalSum_eq_prod_visibleL1`,
        and
        `Mayer.visibleL1_componentFactorizedNormalizedPairFamilyTerm_eq_const_mul_prod_localL1`.
        Verification: `lake build RandomSystems.Applications.XoPMayer`
        passed; only unrelated pre-existing PRP/PRF warnings remain.
  - [ ] Prove a numerical local-component budget for
        `visibleL1 (pairFamilyComponentLocalSum Γ C)` and lift it through
        `Mayer.visibleL1_componentFactorizedNormalizedPairFamilyTerm_eq_const_mul_prod_localL1`
        to a term budget for
        `visibleL1 (componentFactorizedNormalizedPairFamilyTerm Γ)`.
        The theorem-spine adapter is now proved as
        `Mayer.xop_advantageOn_injective_of_componentLocalL1Budget_geTwo_pow_small_q`;
        the remaining proof obligation is the actual rank/codimension estimate
        for each connected component-local hidden sum, plus the covering-family
        summability estimate for the resulting term budget.
        Verification: `lake build RandomSystems.Applications.XoPMayer`
        passed; only unrelated pre-existing PRP/PRF warnings remain.
        Baseline-only local component bound also proved:
        `Mayer.visibleL1_pairFamilyComponentLocalSum_le_card`.  This is not an
        accepted final estimate; it records the crude hidden-assignment
        boundary that the rank/codimension or Penrose layer must improve.
      - [x] Prove the exact component-edge fiber identity
            `Mayer.pairFamilyTerm_componentEdgeFamily_eq_complementCard_mul_localSum`.
            This connects a component-local sum back to the full pair-family
            term for that component's edge family without reproving finite
            product/fiber algebra.
	      - [x] Prove the rank-budget component-local `L¹` bridge
	            `Rank.visibleL1_pairFamilyComponentLocalSum_le_invComplement_mul_sum_atomChoiceFamily_jointRankBudget`.
	            This reduces a numerical local-component budget to joint-rank lower
	            bounds for the atom-choice families generated by the component edge
	            family, plus the explicit complement-assignment scaling factor.
	            Verification: `lake build` and
	            `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF/Cascade/CTR lints remain.
	      - [x] Name the component-local atomized rank budget and connect it to the
	            theorem spine:
	            `Rank.componentLocalAtomizedRankBudget`,
	            `Rank.visibleL1_pairFamilyComponentLocalSum_le_componentLocalAtomizedRankBudget`,
	            and
	            `Rank.xop_advantageOn_injective_of_componentLocalAtomizedRankBudget_geTwo_pow_small_q`.
	            The remaining covering-route leaves are now explicit in Lean:
	            joint-rank lower bounds for each component atom-choice family,
	            a product-to-term-budget comparison, and the covering-family
	            summability estimate.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Prove the atom-choice support/connectivity bridge for connected
	            component edge families:
	            `Rank.atomVertices_pairAtomChoiceAtoms`,
	            `Rank.atomVertices_pairAtomChoiceFamilyAtoms`,
	            `Rank.atomLinked_pairAtomChoiceFamilyAtoms_of_edgeLinked`,
	            `Rank.pairAtomChoiceFamily_root_reaches_of_pairConnected`,
	            `Rank.hiddenRank_pairAtomChoiceFamily_ge_card_sub_one_of_pairConnected`,
	            and
	            `Rank.hiddenRank_pairFamilyComponentAtomChoice_ge_card_sub_one`.
	            This discharges the hidden-rank half of the component atom-choice
	            estimate by reusing the already-proved root-reachability theorem.
	            The visible-obstruction/mixed-cycle condition is still the required
	            extra hypothesis for a full `|K|^{-|V|}` joint-rank budget.
	            Verification: `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF warnings remain.
		      - [x] Prove the combined joint-rank wrapper for component atom choices:
		            `Rank.jointRank_pairAtomChoiceFamily_ge_card_of_pairConnected_and_visibleObstruction`
		            and
		            `Rank.jointRank_pairFamilyComponentAtomChoice_ge_card_of_visibleObstruction`.
	            This composes the component connectivity bridge with the existing
	            rank identity and visible-obstruction theorem, so the component
	            budget can use a single premise:
		            `HasVisibleObstruction (atomFamilyRow atoms)`.
		            Verification: `lake build RandomSystems.Applications.XoPRank
		            RandomSystems.Applications.XoPMayer` passed; only unrelated
		            pre-existing PRP/PRF warnings remain.
	      - [x] Add the visible-obstruction-budget endpoint
	            `Rank.xop_advantageOn_injective_of_componentLocalVisibleObstructionBudget_geTwo_pow_small_q`.
	            This fixes the component rank budget to
	            `|pairFamilyComponentVertices Γ C|` and derives the required
	            joint-rank bound from
	            `Rank.jointRank_pairFamilyComponentAtomChoice_ge_card_of_visibleObstruction`.
	            The remaining component-covering route now has three explicit
	            leaves: prove visible obstruction for the surviving atom choices,
	            prove the product-to-term-budget comparison, and prove the
	            covering-family summability estimate.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Name the exact component visible-obstruction term budget and
	            connect it to the theorem spine:
	            `Rank.componentVisibleObstructionTermBudget` and
	            `Rank.xop_advantageOn_injective_of_componentVisibleObstructionTermBudget_geTwo_pow_small_q`.
	            This removes the abstract `termBudget` parameter from the
	            component-covering rank route.  The remaining analytic leaf is the
	            concrete covering-family summability estimate over
	            `componentVisibleObstructionTermBudget`, plus the source-specific
	            visible-obstruction survival condition.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Prove the nonnegativity API for the concrete component budgets:
	            `Rank.componentLocalAtomizedRankBudget_nonneg` and
	            `Rank.componentVisibleObstructionTermBudget_nonneg`.
	            These are needed for monotone analytic estimates in the remaining
	            concrete covering-family summability proof.  Verification:
	            `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF warnings remain.
	      - [x] Prove the constant-rank component-budget simplifications
	            `Rank.componentLocalAtomizedRankBudget_const_rank` and
	            `Rank.card_component_pairAtomChoiceFamily`.
	            For a fixed component rank budget `v`, the atom-choice sum is now
	            exposed as `3^|E_C|` times one inverse-power term.  This is the
	            first algebraic simplification needed by the concrete covering
	            summability estimate.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Prove the complement-function cardinality and local cancellation
	            lemmas:
	            `Rank.card_complement_function_space` and
	            `Rank.componentLocalAtomizedRankBudget_visibleObstruction_eq_three_pow`.
	            The visible-obstruction component-local budget now collapses
	            exactly to `3^|E_C|`; the finite-field factors cancel inside each
	            connected component.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Expand the concrete component visible-obstruction term budget as a
	            product of explicit component factors:
	            `Rank.componentVisibleObstructionTermBudget_eq_explicit`.
	            The expression now exposes the remaining combinatorial terms
	            `3^|E_C|`, complement assignment factors, and
	            `|K|^(2q-|V_C|)/|K|^q` factors that the final summability proof must
	            dominate.  Verification: `lake build
	            RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	            passed; only unrelated pre-existing PRP/PRF warnings remain.
	      - [x] Collapse the product over connected components:
	            `Rank.componentVisibleObstructionTermBudget_eq_complementNormalizer_mul_three_pow_card`.
	            Using the exact product decomposition and
	            `Mayer.sum_card_pairFamilyComponentEdgeFamily`, the concrete
	            budget is now `|complement assignments / normalizer| * 3^|Γ|`.
	            Verification: `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF warnings remain.
	      - [x] Rewrite the concrete component visible-obstruction term budget in
	            graph-family weight form:
	            `Rank.componentVisibleObstructionTermBudget_eq_normalizerSlack_mul_three_pow_div_card_pow`.
	            The remaining summability target is now the exact scalar weight
	            `(|K|^q / visibleNormalizer) * (3^|Γ| / |K|^|edgeVertices Γ|)`.
	            This exposes the normalizer slack separately from the graph-family
	            covering estimate.  Verification:
	            `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF warnings remain.
	      - [x] Add the theorem-spine graph-weight endpoint
	            `Rank.xop_advantageOn_injective_of_componentVisibleObstructionGraphWeight_geTwo_pow_small_q`.
	            This replaces the remaining abstract `componentVisibleObstructionTermBudget`
	            summability premise with the exact scalar graph-family weight
	            exposed by the preceding equality.  Verification:
	            `lake build RandomSystems.Applications.XoPRank
	            RandomSystems.Applications.XoPMayer` passed; only unrelated
	            pre-existing PRP/PRF warnings remain.
	      Remaining covering-route summability leaf: prove a numerical budget for
      `visibleL1 (componentFactorizedNormalizedPairFamilyTerm Γ)` and show that
      `∑_{Γ covering S} |S.powerset| * termBudget Γ ≤ activity |S|`.  This is
      intentionally a crude triangle route; if it is too weak, the proof must
      switch to the genuine cumulant/Penrose contribution family already logged
      above rather than pretending disconnected products vanish.

Rank/codimension route:

- [x] Create `XoPRank.lean` and import it from `RandomSystems.lean`.
- [x] Define typed hidden and shifted atoms after the pair-level Mayer boundary.
- [x] Prove `pairBad` is equivalent to existence of a hidden or shifted atom on
      the same pair edge.
- [x] Define atom touched vertices and prove they remain inside the parent pair
      support.
- [x] Define the finite-field linear forms for hidden and shifted atom
      constraints.
- [x] Package finite atom families as hidden constraint maps and visible RHS
      maps.
- [x] Define the quotient visible-obstruction map and prove hidden feasibility
      iff the obstruction vanishes.
- [x] Define hidden rank, visible defect/obstruction rank, joint constraint map,
      and joint rank.
- [x] Prove the rank identity relating joint rank to hidden rank plus visible
      obstruction rank, or log and prove the precise weaker identity needed
      downstream.
- [x] Prove the linear-map fiber equivalence between a nonempty affine fiber
      `{a | hiddenConstraintMap row a = visibleRhsMap row y}` and the kernel of
      `hiddenConstraintMap row`.
- [x] Prove finite-field fiber cardinality: feasible hidden systems have
      `|K|^(q - hiddenRank)` hidden solutions, infeasible systems have zero.
- [x] Prove the theorem-forced feasible/infeasible wrapper for selected atom
      families:
      `Rank.atomFamily_solution_card_le_pow_hiddenRank` and
      `Rank.atomFamily_solution_card_real_le_pow_hiddenRank`.
- [x] Connect atomized Mayer products to row-family constraint systems so that
      every selected hidden/shifted atom family has a corresponding linear map
      and visible obstruction event.
- [x] Prove one-edge inclusion-exclusion atomization of the pair-Mayer factor
      after the pair-level Mayer boundary:
      `Rank.pairMayerFactor_eq_atom_inclusion_exclusion`.
- [x] Expand pair-edge-family Mayer products into sums over `PairAtomChoice`
      families:
      `Rank.pairMayerProduct_eq_sum_pairAtomChoiceFamilies` and
      `Rank.pairMayerProduct_eq_sum_pairAtomChoiceFamilyAtoms`.
- [x] Connect atom-choice family expansion to hidden-solution fiber
      cardinalities:
      `Rank.pairFamilyTerm_eq_sum_atomChoiceFamily_counts`.
- [x] Prove the fixed atom-family joint codimension count:
      selected atom families have joint solution count
      `|K|^(2q - jointRank)`.
- [x] Convert the fixed-bond codimension count into the normalized probability
      form needed by the cluster estimate, e.g. an `N^{-jointRank}` bound.
- [x] Prove the finite Fubini/averaging bridge from selected hidden fibers to
      joint hidden-visible solution counts:
      `Rank.sum_atomFamily_solution_card_eq_joint_card`,
      `Rank.uniformAverage_atomFamily_solution_card_eq_joint_card_div`,
      `Rank.atomFamily_joint_card_le_pow_two_mul_sub_of_jointRank_ge`, and
      `Rank.uniformAverage_atomFamily_solution_card_le_pow_div_pow_of_jointRank_ge`.
- [x] Prove the atom-choice `L¹` budget interface for pair-family terms:
      `Rank.visibleL1_pairFamilyTerm_le_sum_atomChoiceFamily_jointRankBudget`
      and
      `Rank.visibleL1_normalizedPairFamilyTerm_le_invNormalizer_mul_sum_atomChoiceFamily_jointRankBudget`.
      Verification: `lake build RandomSystems.Applications.XoPRank
      RandomSystems.Applications.XoPMayer` passed; only unrelated pre-existing
      PRP/PRF warnings remain.
- [x] Prove connected tree constraints have hidden rank at least `v - 1`.
  Component atom-choice specialization is now proved as
  `Rank.hiddenRank_pairFamilyComponentAtomChoice_ge_card_sub_one`; the remaining
  rank leaf is the visible-obstruction certificate for the surviving atom choices.
- [x] Prove the single-atom base case of the hidden-rank lower bound:
      `hiddenRank(singleAtomRow A) = |atomVertices {A}| - 1 = 1`.
- [x] Prove surviving nonconstant clusters have visible defect rank at least
      `1`, or state the exact replacement lemma if this form is false.
      Replacement proved: `HasVisibleObstruction row` implies
      `1 ≤ visibleObstructionRank row`.
- [x] Prove the combined codimension lower bound needed by the accepted cluster
      estimate.
  Component atom-choice specialization is now proved conditional on
  `HasVisibleObstruction`; the remaining source-specific work is proving that
  the Penrose-surviving atom-choice terms satisfy that predicate.
- [ ] Bridge the Penrose/cluster notion of a surviving nonconstant atomized
      contribution to `HasVisibleObstruction`.
	  - [x] Prove the concrete mixed-cycle witness:
	        a shifted atom closing a hidden-atom path implies
	        `HasVisibleObstruction`.
	  - [x] Prove the general left-kernel/RHS certificate:
	        hidden row combination cancels while visible RHS does not.
	  - [x] Add the atom-choice-family witness bridge:
	        `Rank.shiftedAtom_mem_pairAtomChoiceFamilyAtoms_of_choice`,
	        `Rank.hiddenAtom_mem_pairAtomChoiceFamilyAtoms_of_choice`, and
	        `Rank.hasVisibleObstruction_of_pairAtomChoiceFamily_shifted_hiddenReachable`.
	        This connects the existing mixed-cycle theorem to the concrete
	        atom-choice families generated after pair-Mayer atomization.  The
	        remaining Penrose/survival leaf must still prove that each surviving
	        nonconstant atomized contribution actually supplies the shifted edge
	        and hidden reachability hypotheses.  Verification: `lake build
	        RandomSystems.Applications.XoPRank RandomSystems.Applications.XoPMayer`
	        passed; only unrelated pre-existing PRP/PRF warnings remain.
	  - [ ] Prove that every surviving nonconstant atomized Penrose contribution
	        contains a formal mixed-cycle witness or another proved
	        `HasVisibleObstruction` certificate.
  - [x] Prove the full-atomization bridge for connected nonempty pair-edge
        families, preserving edge vertices and giving the `|K|^{-|V|}`
        normalized codimension bound.
  - [x] Connect exact full-atomized density charges to the generic pair-cluster
        charge interface with simple charge `|K|^{-|S|}`.
  - [ ] Relate the actual Penrose/cumulant contribution family to full
        atomization, or replace full atomization by the sharper atom-choice
        family generated by the Penrose expansion.
  - [x] Compose expansion + full-atomized density domination + charge summability
        into a concrete injective-input advantage theorem.
  - [x] Add layer/tree variants of the full-atomized endpoint, so the remaining
        summability theorem can be proved by support size and Penrose tree
        charges.
  - [x] Add the scalar local-activity endpoint:
        `∑_k binom(q,k) activity(k) ≤ ε` is now enough after tree domination.
  - [x] Add the final selected-contribution theorem-spine endpoint:
        `Mayer.xop_advantageOn_injective_of_selectedContributionFiberBound_card_scaled_quadratic`.
        This states the expected quadratic security bound directly from the
        remaining genuine Penrose obligations: concrete contribution expansion,
        selected-tree fiber domination, and
        `localActivity k ≤ (C / |G|)^k`.
        Verification: `lake build RandomSystems.Applications.XoPMayer
        RandomSystems.Applications.XoPRank` passed; only unrelated pre-existing
        PRP/PRF warnings remain.
  - [ ] Prove the exact density domination hypothesis for the actual Penrose
        contribution family.
  - [ ] Prove total summability of
        the Penrose local tree activity, or a sharper valid charge generated by
        the Penrose expansion.  Do not try to sum raw connected pair clusters.
    - [x] Add reusable support-tree counting lemmas for the genuine Penrose
          branch:
          `Mayer.pairTree_card_le_two_pow_choose` and
          `Mayer.pairTree_sum_le_two_pow_choose_mul`.
          These do not supply cancellation; they are the finite tree-count
          adapter needed after a genuine per-tree charge/fiber estimate is
          proved.  Verification:
          `lake build RandomSystems.Applications.XoPMayer
          RandomSystems.Applications.XoPRank` passed; only unrelated
          pre-existing PRP/PRF warnings remain.
    - [x] Add the ge-two atomized-certificate endpoint with a uniform per-tree
          fiber budget:
          `Rank.xop_advantageOn_injective_of_atomizedCumulantCertificateGeTwo_uniformTreeCharge_card_scaled_quadratic`.
          This reduces the summability leaf to a per-selected-tree atomized
          fiber estimate plus the scalar inequality
          `2^(k choose 2) * perTreeActivity k ≤ localActivity k`.
          Verification:
          `lake build RandomSystems.Applications.XoPMayer
          RandomSystems.Applications.XoPRank` passed; only unrelated
          pre-existing PRP/PRF warnings remain.
- [ ] Account for injectivity corrections and show they do not break the final
      bound.

Tilted visible-defect route:

- [ ] Define the tilted cluster/density measure precisely.
- [ ] Prove visible-defect bounds under the tilted measure, not under the raw
      product law.
- [ ] Replace any false independence or factorization argument over overlapping
      supports with a dependency-graph, Janson-style, or cluster-derived proof.
- [ ] Prove the tilted defect estimate needed by
      `TiltedVisibleDefectObligation`.

Summability and final analytic theorem:

- [ ] Prove the subset/cluster summability bound from the per-cluster estimates.
- [ ] Prove `PairMayerPenroseObligation` from the concrete expansion.
- [ ] Prove `RankCodimensionObligation` from the concrete rank lemmas.
- [ ] Prove `TiltedVisibleDefectObligation` from the tilted defect estimate.
- [ ] Prove `AnalyticObligationsSuffice` without assumptions.
- [ ] Instantiate `xop_nonadaptive_security_from_analytic_obligations` with the
      concrete obligations.
- [ ] Instantiate the adaptive theorem or document/prove why the selected XoP
      theorem is non-adaptive.

Lean hygiene and acceptance gates:

- [x] Import all accepted XoP files from `RandomSystems.lean`.
- [x] Keep `PROOF_GAPS.md` as the canonical tracker; do not create a competing
      XoP tracker.
- [ ] Before implementing each obligation, search Mathlib and local FV projects
      for reusable lemmas/APIs and cite the reused declarations in code comments
      or tracker notes when they shape the proof.
- [ ] Avoid reproving standard facts unless no reusable result exists or the
      bridge proof would be longer/more fragile than the local proof.
- [ ] Decide whether to keep the direct XoP import of
      `Applications.PRPPRFSwitchingGeneral` for `card_perm_fiber` or extract the
      permutation-fiber lemma into a shared module.
- [x] Run targeted `lake env lean` checks after each proof slice.
- [x] Run the root import check `lake env lean RandomSystems.lean` after import
      changes.
- [x] Verify there are no XoP `sorry` warnings.
- [ ] Run a final build once the mathematical obligations are closed.
- [ ] Run a contrarian review of the final theorem path for vacuity, hidden
      assumptions, source mismatch, and invalid LM20 weight reasoning.
- [ ] Only mark the XoP task complete after the contrarian review clears and the
      full theorem path is mechanically checked.

---

## Sorry 1: Theorem 1 Inductive Step

**File:** `RandomSystems/FundamentalTheorem.lean:132`
**Theorem:** `exists_equiv_achieving_advantage_ind` (succ case)
**Severity:** HIGH — blocks full Theorem 1 (Δ = Adv)

**What's proved:**
- Base case (q=0): DDS is subsingleton, transcript function is injective, statDist preserved
- IH correctly formulated: for each (x,y), optimal S'_xy ≡ S^{↑x↓y}, T'_xy ≡ T^{↑x↓y}
- Both directions of Theorem 1 proved assuming this sorry

**What's needed for the inductive step (paper pp. 17-18):**
1. **Advantage decomposition via successor**:
   `advantage S T = sup_x ∑_y advantage(S.successor x y, T.successor x y)`
   This itself requires showing non-adaptive advantage equals adaptive advantage
   (our `PDS.equiv` definition sidesteps this, but advantage is over transcript
   distributions, so the decomposition via `Fin.cons` is needed).

2. **PDS reconstruction from successor families**: Given optimal successor distributions
   S'_xy for each (x,y), reconstruct a (q+1)-query PDS S' via `DDS.reconstruct`.
   Infrastructure exists (`DDS.reconstruct`, `DDS.decompose` equivalence) but the
   distribution-level reconstruction (building `Dist (DDS X Y (q+1))` from
   first-query marginal + successor distributions) is not formalized.

3. **Lemma 6 of the paper** (joint distribution from marginals): Given marginals
   X₁,...,Xₙ that sum to the same total weight, construct a joint distribution
   whose marginals match. Not formalized.

**Difficulty:** Hard. This is the core mathematical content of the paper.
Each sub-piece is ~100-200 lines of Lean. Total estimated: 400-600 lines.

**Source of difficulty:** Formalization, not paper bugs. The paper proof is correct
but relies on measure-theoretic constructions (conditional distributions, product
measures) that must be built from Finsupp primitives.

---

## Sorry 2: Amplification Theorem (General k)

**File:** `RandomSystems/Amplification.lean:57`
**Theorem:** `amplification_theorem`
**Severity:** MEDIUM — k=1 case and Corollary 1 are proved

**Statement:** For a (k,n)-combiner with black-box reduction:
  `Adv(C(Ss), I_out) ≤ binom(n, k-1) · ε^k`

**What's proved:**
- k=1 case (`amplification_theorem_k1`): ✅ fully proved via hybrid argument
- (1,2)-combiner bound (`threshold_combiner_bound_1_2`): ✅ fully proved

**What's needed:**
- Combinatorial counting: enumerate subsets of size k-1
- For each subset J of "bad" (non-ideal) components with |J| = k-1:
  the remaining n-(k-1) components include at least k ideal ones,
  so the threshold combiner gives C(Ss_J) ≡ I_out
- Combine via union bound / inclusion-exclusion

**Difficulty:** Medium. The combinatorics is standard but requires Mathlib's
`Finset.powerset` and `Nat.choose` machinery.

**Source of difficulty:** Formalization (combinatorial bookkeeping in Lean).
The paper proof is correct.

---

## Sorry 3: URF/URP Transcript Distribution Equality (q=1)

**File:** `RandomSystems/Applications/PRPPRFSwitching.lean:72`
**Theorem:** `urf_urp_transcriptDist_eq`
**Severity:** LOW — only blocks the q=1 PRF/PRP switching result

**Statement:** For q=1, URF and URP produce the same transcript distributions:
  `URF.transcriptDist inputs = URP.transcriptDist inputs`

**What's proved:**
- `urf_urp_cond_equiv`: ✅ proved (delegates to transcriptDist equality)
- `urf_collision_bound`: ✅ proved (condition never fails for q=1)
- `prf_prp_switching_q1`: ✅ proved (delegates to transcriptDist equality)

**What's needed:**
- Show that for any input x, both distributions assign weight 1/|X| to each
  output y. This requires computing fiber cardinalities:
  - URF: `|{f : X→X | f(x)=y}| = |X|^(|X|-1)`, so weight = `|X|^(|X|-1) / |X|^|X| = 1/|X|`
  - URP: `|{π ∈ Sym(X) | π(x)=y}| = (|X|-1)!`, so weight = `(|X|-1)! / |X|! = 1/|X|`
- Mathlib has `Fintype.card_filter_piFinset_const_eq_of_mem` for the URF side
  and `Fintype.card_perm` for |Sym(X)| = |X|!, but the permutation fiber
  counting requires orbit-stabilizer or direct combinatorial argument.

**Difficulty:** Medium. Standard combinatorics but requires connecting DDS
definitions to Mathlib's `piFinset` and `Equiv.Perm` machinery.

**Source of difficulty:** Bridging between our custom DDS type and Mathlib's
function/permutation types. The mathematical fact is elementary.

---

## Proved Results (Previously Sorry)

### ✅ Condition-Based Proof Technique (Maurer 2002)

**File:** `RandomSystems/ConditionBased.lean`

- `advantage_le_condition_failure`: **PROVED** — Two-sided bound
  `S ≡_A T → Adv(S,T) ≤ ν(S,A) + ν(T,A)`. Key technique: pushforward
  regrouping lemma `fTransform_filter_sum` that relates filtered fTransform
  sums to filtered sums over the original domain.

- `advantage_le_single_failure`: **PROVED** — One-sided bound
  `Adv(S,T) ≤ ν(S,A)`. Uses same pushforward regrouping directly without
  needing the equal-weight hypothesis (the one-directional statDist already
  gives the single-sided bound).

### ✅ PRF/PRP Switching Application (q=1)

**File:** `RandomSystems/Applications/PRPPRFSwitching.lean`

- `urf_collision_bound`: **PROVED** — For q=1, the failure probability is 0
  because the "all outputs distinct" condition holds trivially (one element
  is always injective). The birthday bound `1·0/(2|X|) = 0` matches.

- `urf_urp_cond_equiv`: **PROVED** (modulo `urf_urp_transcriptDist_eq`) —
  Conditional equivalence follows from full transcript distribution equality.

- `prf_prp_switching_q1`: **PROVED** (modulo `urf_urp_transcriptDist_eq`) —
  If transcript distributions are equal, advantage = 0 by `statDist_self`.

---

## Non-Sorry Issues

### Issue 1: Adaptive Lemma 5 is formalized

**File:** `RandomSystems/Equiv.lean`

The paper's Lemma 5 states: "Non-adaptive environments suffice for checking
equivalence." This is a non-trivial statement: if two PDS agree on all
*non-adaptive* environments, they agree on all *adaptive* environments.

The formalization now separates non-adaptive equivalence
`PDS.equivNonadaptive` from adaptive equivalence `PDS.equivAdaptive`, and proves
the actual bridge as `PDS.equivAdaptive_iff_nonadaptive`.

**Impact:** Resolved for equivalence. Non-adaptive transcript equality now
implies adaptive transcript equality for all deterministic environments.

**Status:** Proved in `RandomSystems/Equiv.lean`.

### Issue 2: PDS Allows Sub-distributions

**File:** `RandomSystems/PDS.lean:46-48`

PDS wraps `Dist (DDS X Y q)` without requiring weight = 1. The `isProbPDS`
predicate exists but is not enforced.

**Impact:** None. This is intentional — sub-distributions arise in the
inductive proof of Theorem 1 (conditioning on first query produces
sub-distributions). All theorems are correct without the weight=1 assumption.

### Issue 3: Construction Has No "Uses Components" Requirement

**File:** `RandomSystems/Construction.lean:39-51`

The `Construction` structure only requires `respects_equiv`. A construction
could ignore all its components (constant function). The `black_box_reduction`
hypothesis in amplification theorems enforces meaningful component usage.

**Impact:** Low. This is standard in game-based security: the reduction
hypothesis captures what we need. Adding a structural requirement would be
non-trivial and not match the paper.

### Issue 4: Instance Management Complexity

Theorems that do induction on `q` (the query count) must use `DDS.instFintype`
explicitly rather than section variables `[Fintype (DDS X Y q)]`, because
induction changes `q` and the derived instance for `q+1` differs from the
section's assumed instance.

**Current fix:** `exists_equiv_achieving_advantage` uses `@PDS X Y q DDS.instFintype`
explicitly. The `MainTheorem` section derives instances automatically. Bridging
between them uses `Subsingleton.elim` on Fintype instances.

**Impact:** Adds complexity to theorem statements but is mathematically sound.

### Issue 5: URP Only Defined for q=1

**File:** `RandomSystems/Instances/URP.lean`

The Uniform Random Permutation is only formalized for single-query systems
(q=1). Multi-query URP requires handling the consistency constraint: a
permutation must respond consistently to repeated inputs.

**Impact:** Limits PRF/PRP switching to q=1 case. Multi-query requires
extending URP to handle the "lazy sampling" pattern where the permutation
is built incrementally.

---

## Paper vs Formalization Gaps

| Paper Concept | Formalized? | Notes |
|---|---|---|
| Def 1-4 (Dist, marginal, statDist, fTransform) | ✅ | |
| Lemma 1 (joint from marginals) | ❌ | Not needed yet; would help Theorem 1 step |
| Lemma 2 (partition of statDist) | ✅ | `statDist_partition` |
| Lemma 3 (data processing inequality) | ✅ | Both ≤ and = (injective) versions |
| Lemma 4 (coupling bound + optimal coupling) | ✅ | |
| Def 5-7 (DDS, DDE, transcript) | ✅ | |
| Def 8-10 (PDS, equiv) | ✅ | Equiv defined via non-adaptive only |
| Lemma 5 (non-adaptive suffices) | ✅ | `PDS.equivAdaptive_iff_nonadaptive` |
| Notation 2 (successor) | ✅ | Both DDS and PDS levels |
| Def 11-12 (advantage, delta) | ✅ | |
| Lemma 6 (joint from marginals, systems) | ❌ | Needed for Theorem 1 step |
| **Theorem 1** (Δ = Adv) | ⚠️ | 1 sorry in inductive step |
| **Theorem 2** (system coupling) | ✅ | Uses Theorem 1 |
| Def 13-15 (construction, combiner) | ✅ | |
| Hybrid argument bound | ✅ | `construction_advantage_bound` |
| **Theorem 3** (amplification, general k) | ⚠️ | 1 sorry; k=1 proved |
| Corollary 1 ((1,2)-combiner) | ✅ | |
| Condition-based proof technique (Mau02) | ✅ | **ALL PROVED** |
| PRF/PRP switching (Mau02 Sec 4.1) | ⚠️ | 1 sorry (fiber counting); q=1 structure proved |
| CBC-MAC security (Mau02 Sec 4.2) | ✅ | Delegates to ConditionBased |

---

## No Paper Bugs Found

The papers (Lanzenberger-Maurer TCC 2020, Maurer EUROCRYPT 2002) appear
mathematically correct. All difficulties encountered stem from formalization
challenges:
- Building distribution-level operations from Finsupp primitives
- Lean instance management during induction on type-level parameters
- Combinatorial bookkeeping for the amplification bound
- Bridging DDS types with Mathlib's function/permutation infrastructure
- URP only defined for single-query case

The paper proofs are sketches (especially Theorem 1 pp. 17-18 and
Theorem 3) but the mathematical content is sound.
