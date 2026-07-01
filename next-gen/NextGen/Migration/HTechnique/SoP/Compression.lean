/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.SoP.SystemLaw
import NextGen.Migration.HTechnique.TacticsBase
import NextGen.AdaptiveLawBridge
import NextGen.QueryCompression

/-!
# SoP query compression

This module ports the repeated-query compression layer from the external
`/h-technique` SoP application to the `NextGen` migration surface.

Source status:

* source-theorem bridge: specialize the generic CR18 repeated-query compression
  infrastructure to the SoP application;
* source-theorem bridge: identify the concrete real/ideal SoP transcript laws as
  deterministic expansions of their compressed fixed-query laws;
* source-theorem bridge: keep the concrete SoP compression names as thin
  wrappers over the shared `RandomSystems.CR18` query-compression API.

Representative compatibility endpoints live in `SoP.CompressionLegacy`.

The later repeated-query SoP theorem should identify the concrete CR18
transcript laws for `xs` as common pushforwards of the injective fixed-query
laws for `compressedInput xs`.
-/

noncomputable section

namespace NextGen
namespace Migration
namespace HTechnique
namespace SoP

attribute [local instance] Classical.decEq

variable {G : Type*} {q : Nat}

/-- **Source-theorem object.** The set of distinct query values appearing in
`xs`. -/
abbrev imageSet [Fintype G] (xs : Fin q → G) : Finset G :=
  RandomSystems.CR18.queryImageSet xs

/-- **Source-theorem bridge.** A canonical injective enumeration of the distinct
query values in `xs`. -/
abbrev compressedInput [Fintype G] (xs : Fin q → G) :
    Fin (Fintype.card {x : G // x ∈ imageSet xs}) → G :=
  RandomSystems.CR18.compressedQuery xs

/-- **Source-theorem bridge.** For each original query index, the corresponding
compressed-query index. -/
abbrev compressedIndex [Fintype G] (xs : Fin q → G) :
    Fin q → Fin (Fintype.card {x : G // x ∈ imageSet xs}) :=
  RandomSystems.CR18.compressedQueryIndex xs

/-- **Source-theorem bridge.** Expand compressed output vectors by copying
outputs back to repeated query positions. -/
abbrev expandCompressed [Fintype G] (xs : Fin q → G) :
    (Fin (Fintype.card {x : G // x ∈ imageSet xs}) → G) → (Fin q → G) :=
  RandomSystems.CR18.expandCompressedOutputs xs

/-- **Support lemma forced by formalization.** The compressed input vector is
injective by construction. -/
theorem compressedInput_injective [Fintype G] (xs : Fin q → G) :
    Function.Injective (compressedInput xs) := by
  exact RandomSystems.CR18.compressedQuery_injective xs

/-- **Source-theorem bridge.** Expanding the compressed input vector recovers
the original query vector. -/
theorem expandCompressed_compressedInput [Fintype G] (xs : Fin q → G) :
    expandCompressed xs (compressedInput xs) = xs := by
  exact RandomSystems.CR18.expandCompressedOutputs_compressedQuery xs

/-- **Source-theorem bridge.** Evaluating any function on the original repeated
query vector is the same as evaluating it on the compressed query vector and
expanding outputs back to the original query positions. -/
theorem expandCompressed_eval_compressedInput [Fintype G] (xs : Fin q → G)
    (f : G → G) :
    expandCompressed xs (fun j => f (compressedInput xs j)) =
      fun i => f (xs i) := by
  exact RandomSystems.CR18.expandCompressedOutputs_eval_compressedQuery xs f

/-- **Source-theorem bridge.** Distribution-level form of
`expandCompressed_eval_compressedInput`: evaluating a sampled function on the
original repeated query vector is the common pushforward of evaluating it on the
compressed injective query vector and expanding outputs. -/
theorem fTransform_eval_repeated_eq_expand_compressed [Fintype G]
    (xs : Fin q → G) (D : RandomSystems.Dist (G → G)) :
    RandomSystems.Dist.fTransform (fun f : G → G => fun i : Fin q => f (xs i)) D =
      RandomSystems.Dist.fTransform (expandCompressed xs)
        (RandomSystems.Dist.fTransform
          (fun f : G → G =>
            fun j : Fin (Fintype.card {x : G // x ∈ imageSet xs}) =>
              f (compressedInput xs j)) D) := by
  exact RandomSystems.CR18.fTransform_eval_repeated_eq_expand_compressedQuery xs D

/-- **Source-theorem bridge.** Compression never increases the query count. -/
theorem compressed_card_le [Fintype G] (xs : Fin q → G) :
    Fintype.card {x : G // x ∈ imageSet xs} ≤ q := by
  exact RandomSystems.CR18.compressedQuery_card_le xs

/-- **Source-theorem bridge.** The paper's cubic query bound is monotone under
compression. -/
theorem compressed_bound [Fintype G] (xs : Fin q → G)
    {N : Nat} (h_bound : q ^ 3 ≤ N ^ 2) :
    (Fintype.card {x : G // x ∈ imageSet xs}) ^ 3 ≤ N ^ 2 := by
  exact RandomSystems.CR18.compressedQuery_bound xs h_bound

/-- **Source-theorem bridge.** Expand a transcript prefix for the compressed
fixed-query experiment back to the original repeated-query transcript-prefix
carrier.  The input component is reset to the original query vector `xs`; the
output component is expanded by copying compressed outputs to repeated query
positions. -/
abbrev expandTranscriptPrefix [Fintype G] (xs : Fin q → G) :
    TranscriptPrefix G G (Fintype.card {x : G // x ∈ imageSet xs}) →
      TranscriptPrefix G G q :=
  RandomSystems.CR18.expandCompressedTranscriptPrefix xs

/-- **Source-theorem bridge.** Lifting an expanded visible-output law to the
original fixed-input transcript-prefix carrier is the same as first lifting the
compressed law and then expanding transcript prefixes. -/
theorem liftVisibleDist_expandCompressed [Fintype G]
    (xs : Fin q → G)
    (D : RandomSystems.Dist
      (Fin (Fintype.card {x : G // x ∈ imageSet xs}) → G)) :
    liftVisibleDist xs (RandomSystems.Dist.fTransform (expandCompressed xs) D) =
      RandomSystems.Dist.fTransform (expandTranscriptPrefix xs)
        (liftVisibleDist (compressedInput xs) D) := by
  simpa [liftVisibleDist, expandTranscriptPrefix, expandCompressed, compressedInput] using
    RandomSystems.CR18.fixedInputLiftDist_expandCompressedOutputs (X := G) (Y := G)
      (q := q) xs D

/-- **Source-theorem bridge.** Exact repeated-query compression for the concrete
normalized SoP real system. -/
theorem transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_compress
    [AddGroup G] [Fintype G] [DecidableEq G] (xs : Fin q → G) :
    TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q) =
      RandomSystems.Dist.fTransform (expandTranscriptPrefix xs)
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
            (normalizedSoPRV (G := G)) (fixedQueryEnvironment (compressedInput xs))
            (Fintype.card {x : G // x ∈ imageSet xs}))) := by
  simpa [TranscriptLawBridge.dist, expandTranscriptPrefix, compressedInput] using
    RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress
      (X := G) (Y := G) (q := q) (pΩ := normalizedSoPProbDist (G := G))
      (F := normalizedSoPFunction (G := G)) xs

/-- **Source-theorem bridge.** Exact repeated-query compression for the concrete
ideal random-function system. -/
theorem transcriptLaw_fixedQueryEnvironment_urfRV_compress
    [Fintype G] [DecidableEq G] [Nonempty G] (xs : Fin q → G) :
    TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q) =
      RandomSystems.Dist.fTransform (expandTranscriptPrefix xs)
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment (compressedInput xs))
            (Fintype.card {x : G // x ∈ imageSet xs}))) := by
  simpa [TranscriptLawBridge.dist, expandTranscriptPrefix, compressedInput] using
    RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress
      (X := G) (Y := G) (q := q)
      (pΩ := RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
      (F := fun f : G → G => f) xs

/-- **Source-theorem bridge.** Repeated-query SoP H-technique step.  An
arbitrary fixed query vector is first compressed to its distinct query values;
the injective fixed-query SoP theorem applies there, and deterministic
expansion back to the original repeated transcript prefix cannot increase
statistical distance. -/
theorem repeatedQuerySoP_oneSided_hTechnique
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (eps : NNReal)
    (h_lower :
      ∀ y : Fin (Fintype.card {x : G // x ∈ imageSet xs}) → G,
        (1 - eps) *
            idealVisibleMass (G := G)
              (q := Fintype.card {x : G // x ∈ imageSet xs}) y ≤
          realVisibleMass (G := G)
            (q := Fintype.card {x : G // x ∈ imageSet xs}) y) :
    RandomSystems.statDist
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
            (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q))
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q)) ≤ eps := by
  rw [transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_compress,
    transcriptLaw_fixedQueryEnvironment_urfRV_compress]
  refine le_trans (RandomSystems.statDist_fTransform_le _ _ (expandTranscriptPrefix xs)) ?_
  have hq : Fintype.card {x : G // x ∈ imageSet xs} ≤ Fintype.card G := by
    simpa [Fintype.card_fin] using
      Fintype.card_le_of_injective (compressedInput xs) (compressedInput_injective xs)
  exact fixedQuerySoP_oneSided_hTechnique (G := G)
    (q := Fintype.card {x : G // x ∈ imageSet xs})
    (compressedInput xs) eps (compressedInput_injective xs) hq h_lower

/-- **Source theorem bridge.** Pointwise repeated-query SoP transcript-law ratio
with the paper's concrete error term.  The proof compresses repeated queries to
their distinct query values, applies the fixed-query pointwise ratio there, and
transports the lower bound through the common deterministic transcript
expansion. -/
theorem repeatedQuerySoP_transcriptLaw_lower_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (t : TranscriptPrefix G G q) :
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q t ≤
      RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q t := by
  let m := Fintype.card {x : G // x ∈ imageSet xs}
  let epsq : NNReal := (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2
  let epsm : NNReal := (m : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2
  have h_eps_le : epsm ≤ epsq := by
    dsimp [epsm, epsq, m]
    gcongr
    exact_mod_cast compressed_card_le (G := G) (q := q) xs
  have h_coeff : 1 - epsq ≤ 1 - epsm := by
    exact tsub_le_tsub_left h_eps_le 1
  have hideal_t := congrArg (fun D : RandomSystems.Dist (TranscriptPrefix G G q) => D t)
      (transcriptLaw_fixedQueryEnvironment_urfRV_compress (G := G) (q := q) xs)
  have hreal_t := congrArg (fun D : RandomSystems.Dist (TranscriptPrefix G G q) => D t)
      (transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_compress (G := G) (q := q) xs)
  simp only [htechnique_dist_simp] at hideal_t hreal_t
  rw [hideal_t, hreal_t]
  change (1 - epsq) *
      RandomSystems.Dist.fTransform (expandTranscriptPrefix xs)
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment (compressedInput xs)) m)) t ≤
    RandomSystems.Dist.fTransform (expandTranscriptPrefix xs)
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
            (normalizedSoPRV (G := G)) (fixedQueryEnvironment (compressedInput xs)) m)) t
  apply RandomSystems.Dist.mul_fTransform_le_fTransform_of_forall_mul_le
  intro s
  calc (1 - epsq) *
        TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment (compressedInput xs)) m) s
      ≤ (1 - epsm) *
        TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment (compressedInput xs)) m) s := by
          gcongr
    _ ≤ TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment (compressedInput xs)) m) s := by
          simpa [epsm, m] using
            fixedQuerySoP_transcriptLaw_lower_bound (G := G) (q := m)
              (compressedInput xs) (compressedInput_injective xs)
              (compressed_bound (G := G) (q := q) xs h_bound) s

/-- **Source theorem bridge.** Law-level deterministic fixed-query SoP
transcript-law ratio.  This is the fixed-query ratio above, transported from
the concrete function/permutation representatives to the direct `ProbPDS`
transcript-law surface. -/
theorem repeatedQuerySoP_deterministicTranscriptLaw_lower_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (t : TranscriptPrefix G G q) :
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
      RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw
          (ProbPDS.urf (X := G) (Y := G)) (fixedQueryDDE (Y := G) xs) q t ≤
      RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw
          (normalizedSoPProbPDS (G := G)) (fixedQueryDDE (Y := G) xs) q t := by
  rw [show ProbPDS.urf (X := G) (Y := G) =
      RandomSystems.Dist.PMF
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
        (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) by
        rfl]
  rw [show normalizedSoPProbPDS (G := G) =
      RandomSystems.Dist.PMF
        (normalizedSoPProbDist (G := G))
        (normalizedSoPRV (G := G)) by
        rfl]
  rw [RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw_pmf
      (p := RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
      (S := RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)),
    RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw_pmf
      (p := normalizedSoPProbDist (G := G))
      (S := normalizedSoPRV (G := G))]
  change
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
          RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G))
          (fixedQueryEnvironment xs) q t ≤
      RandomSystems.CR18.PFunPDE.transcriptLaw
        (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
        (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q t
  exact repeatedQuerySoP_transcriptLaw_lower_bound (G := G) (q := q) xs h_bound t

/-- **Source theorem bridge.** Law-level repeated-query SoP H-technique theorem
for an arbitrary law-level CR18 environment.  The public inputs are the
law-level environment and its support-totality premise; representative adapters
are confined to the generic bridge. -/
theorem repeatedQuerySoP_probPDE_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (E : ProbPDE G G)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (hEtotal : E.KQueryTotal q) :
    RandomSystems.statDist
        (ProbPDS.transcriptDist (q := q) (normalizedSoPProbPDS (G := G)) E)
        (ProbPDS.transcriptDist (q := q) (ProbPDS.urf (X := G) (Y := G)) E) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  have hRtotal : (normalizedSoPProbPDS (G := G)).KStepTotal q := by
    exact normalizedSoPProbPDS_KStepTotal (G := G) q
  have hItotal : (ProbPDS.urf (X := G) (Y := G)).KStepTotal q := by
    exact RandomSystems.CR18.PFunPDS.Prob.urf_KStepTotal q
  exact RandomSystems.CR18.oneSided_hTechnique_law_experiment_of_fixedQuery_ratio
    (R := normalizedSoPProbPDS (G := G))
    (I := ProbPDS.urf (X := G) (Y := G))
    (E := E)
    ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)
    hRtotal hItotal hEtotal
    (fun xs t =>
      repeatedQuerySoP_deterministicTranscriptLaw_lower_bound
        (G := G) (q := q) xs h_bound t)

end SoP
end HTechnique
end Migration
end NextGen
