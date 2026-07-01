# H-technique component roadmap

This file tracks the migration from the bottom of the stack up to the SoP
proof.  Each layer is audited before moving upward: the goal is to keep public
statements on high-level CR18 objects while leaving low-level sample-space and
representative machinery in bridge or compatibility modules only.

## Layer 0: Distribution and density

Status: audited.

Owner modules:

- `RandomSystems.Dist`: finite distributions, probability laws, event mass,
  pushforward, product laws, sampled random-variable laws, and uniform laws.
- `RandomSystems.StatDist`: statistical distance, bad-event probability, and
  the distribution-only H-technique inequalities.
- `NextGen.Migration.HTechnique.Density`: source-name facade for the
  distribution-only H-technique API.  It should not introduce new probability
  concepts.

Core objects:

- `RandomSystems.Dist A := A ->0 NNReal`
- `RandomSystems.Dist.weight`
- `RandomSystems.Dist.isProbDist`
- `RandomSystems.Dist.ProbDist`
- `RandomSystems.Dist.supportProbDist`
- `RandomSystems.Dist.mass`
- `RandomSystems.Dist.evalPred`
- `RandomSystems.probBad`
- `RandomSystems.statDist`

Core constructors and transport:

- `RandomSystems.Dist.uniform`
- `RandomSystems.Dist.unitProbDist`
- `RandomSystems.Dist.prod`
- `RandomSystems.Dist.prodProbDist`
- `RandomSystems.Dist.fTransform`
- `RandomSystems.Dist.PMF`
- `RandomSystems.Dist.iidPow`
- `RandomSystems.Dist.clonePow`

Core rewrite and bound facts used above this layer:

- `RandomSystems.Dist.mass_congr`
- `RandomSystems.Dist.mass_fTransform`
- `RandomSystems.Dist.fTransform_apply_eq_mass`
- `RandomSystems.Dist.fTransform_comp`
- `RandomSystems.Dist.weight_fTransform`
- `RandomSystems.Dist.fTransform_isProbDist`
- `RandomSystems.Dist.supportProbDist_mass_preimage`
- `RandomSystems.Dist.uniform_mass_eq_card_filter`
- `RandomSystems.Dist.uniform_apply`
- `RandomSystems.Dist.weight_uniform`
- `RandomSystems.Dist.uniform_isProbDist`
- `RandomSystems.Dist.evalPred_iUnion_le`
- `RandomSystems.Dist.evalPred_uniform`
- `RandomSystems.Dist.evalPred_uniform_le`
- `RandomSystems.Dist.evalPred_fTransform_uniform_le`
- `RandomSystems.statDist_fTransform_le`

Core H-technique facts:

- `RandomSystems.hTechnique_ratio`
- `RandomSystems.hTechnique_expectation`
- `RandomSystems.hTechnique_eq_on_good`
- `RandomSystems.oneSided_hTechnique`
- `RandomSystems.oneSided_hTechnique_fTransform`
- `RandomSystems.oneSided_hTechnique_proper`
- `RandomSystems.hTechnique_ratio_massFunction`
- `RandomSystems.oneSided_hTechnique_massFunction`

How the SoP proof uses this layer:

- `SoP.VisibleLaw` builds exact visible-output distributions using
  `Dist.uniform`, `Dist.ofFiniteMassFunction`, and distribution weights.
- `SoP.TranscriptPrefix` lifts visible-output laws into fixed-input transcript
  prefixes by a deterministic pushforward and applies
  `Density.oneSided_hTechnique_fTransform`.
- `SoP.SystemLaw` identifies CR18 system factors with visible-output masses
  using `Dist.mass`, `Dist.mass_congr`, `Dist.fTransform_apply_eq_mass`, and
  uniform-function evaluation facts.
- `SoP.Compression` moves repeated-query transcript laws through common
  pushforwards using `Dist.fTransform_comp`, `statDist_fTransform_le`, and the
  monotone pushforward bound
  `Dist.mul_fTransform_le_fTransform_of_forall_mul_le`.

Audit result:

- The distribution layer is not duplicated in the migrated H-technique public
  surface.  Distribution math lives in `RandomSystems.Dist` and
  `RandomSystems.StatDist`.
- `Density` is acceptable as a source-name facade: its declarations forward to
  owner-module facts and keep the H-technique names grouped for downstream
  migration.  It must stay distribution-only and must not mention SoP, PDS,
  PDE, transcript representatives, or adaptive environments.
- Raw `Dist.PMF` and `Dist.RV` are allowed in bridge/support modules where the
  theorem is explicitly about constructing a law from a sample space.  Public
  model sites should use higher-level constructors such as
  `RandomSystems.CR18.PFunPDS.Prob.functionEvaluator`.

Next layer:

- Layer 1 is the CR18 transcript-law surface: `PFunPDE.TranscriptPrefix`,
  `PFunPDE.TranscriptLaw`, `PFunPDS.Prob`, `PFunPDE.Prob`, and the
  representative-free transcript distribution API.

