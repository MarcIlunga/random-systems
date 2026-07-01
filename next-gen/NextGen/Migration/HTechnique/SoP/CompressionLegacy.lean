/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.SoP.Compression
import NextGen.Migration.HTechnique.AdaptiveBridge

/-!
# SoP query-compression legacy compatibility

This module keeps representative-level SoP compression endpoints build-checked
while the public migration surface moves to law-level `ProbPDS`/`ProbPDE`
statements.  New public endpoints should import `SoP.Compression`, not this
file.

Migration note: this module is compatibility-only.
-/

noncomputable section

open scoped NNReal

namespace NextGen
namespace Migration
namespace HTechnique
namespace SoP

attribute [local instance] Classical.decEq

variable {G : Type*} {q : Nat}

/-- **Compatibility bridge.** The normalized SoP real system packaged as the
CR18 representative used by legacy representative transcript-law endpoints. -/
noncomputable def normalizedSoPRepresentative
    [AddGroup G] [Fintype G] [DecidableEq G] :
    PDSRepresentative G G where
  Ω := Equiv.Perm G × Equiv.Perm G
  prob := normalizedSoPProbDist (G := G)
  rv := normalizedSoPRV (G := G)

/-- **Compatibility bridge.** The ideal uniform-random-function system packaged
as the CR18 representative used by legacy representative transcript-law
endpoints. -/
noncomputable abbrev urfRepresentative [Fintype G] [DecidableEq G] [Nonempty G] :
    PDSRepresentative G G :=
  PDSRepresentative.urf (X := G) (Y := G)

/-- **Source theorem bridge.** Pointwise SoP transcript-law ratio for an
arbitrary representative CR18 environment.  This is the legacy representative
wrapper around the law-level fixed-query compression ratio in `SoP.Compression`.
-/
theorem repeatedQuerySoP_transcriptLaw_lower_bound_experiment
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (E : PDERepresentative G G)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (t : TranscriptPrefix G G q) :
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        PDSRepresentative.transcriptLaw (urfRepresentative (G := G)) E q t ≤
      PDSRepresentative.transcriptLaw (normalizedSoPRepresentative (G := G)) E q t := by
  apply transcriptLaw_ratio_of_fixedQuery_ratio
    (R := normalizedSoPRepresentative (G := G))
    (I := urfRepresentative (G := G))
  intro xs t
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

/-- **Source theorem bridge.** Repeated-query SoP H-technique theorem for an
arbitrary representative CR18 environment.  This legacy endpoint is retained
for migration comparison; public callers should use `repeatedQuerySoP_probPDE_bound`.
-/
theorem repeatedQuerySoP_experiment_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (E : PDERepresentative G G)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (hEtotal : E.KQueryTotal q) :
    RandomSystems.statDist
        (PDSRepresentative.transcriptDist (q := q) (normalizedSoPRepresentative (G := G)) E)
        (PDSRepresentative.transcriptDist (q := q) (urfRepresentative (G := G)) E) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  exact NextGen.Migration.HTechnique.oneSided_hTechnique_experiment_of_fixedQuery_ratio
    (R := normalizedSoPRepresentative (G := G))
    (I := urfRepresentative (G := G))
    (E := E)
    ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)
    (RandomSystems.CR18.functionEvaluatorRV_KStepTotal
      (normalizedSoPFunction (G := G)) q)
    (by
      change RandomSystems.CR18.PFunPDS.RV.KStepTotal
        (RandomSystems.CR18.functionEvaluatorRV (fun f : G → G => f)) q
      exact RandomSystems.CR18.functionEvaluatorRV_KStepTotal (fun f : G → G => f) q)
    hEtotal
    (fun xs t => by
      change
        (1 - ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)) *
            RandomSystems.CR18.PFunPDE.transcriptLaw
              (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
              RandomSystems.Dist.unitProbDist.{0}
              (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G))
              (fixedQueryEnvironment xs) q t ≤
          RandomSystems.CR18.PFunPDE.transcriptLaw
            (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
            (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q t
      exact repeatedQuerySoP_transcriptLaw_lower_bound (G := G) (q := q) xs h_bound t)

/-- **Source theorem bridge.** Repeated-query SoP H-technique theorem with the
paper's concrete error term `q^3 / |G|^2`, packaged for the legacy
representative fixed-query environment. -/
theorem repeatedQuerySoP_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    RandomSystems.statDist
        (PDSRepresentative.transcriptDist (q := q)
          (normalizedSoPRepresentative (G := G))
          (fixedQueryRepresentative (Y := G) xs))
        (PDSRepresentative.transcriptDist (q := q)
          (urfRepresentative (G := G))
          (fixedQueryRepresentative (Y := G) xs)) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  change RandomSystems.statDist
      (TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q))
      (TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q)) ≤
    (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2
  let m := Fintype.card {x : G // x ∈ imageSet xs}
  have h_core :
      RandomSystems.statDist
          (TranscriptLawBridge.dist
            (RandomSystems.CR18.PFunPDE.transcriptLaw
              (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
              (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q))
          (TranscriptLawBridge.dist
            (RandomSystems.CR18.PFunPDE.transcriptLaw
              (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
              (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q)) ≤
        (m : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
    exact repeatedQuerySoP_oneSided_hTechnique (G := G) (q := q) xs
      ((m : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)
      (fun y =>
        realVisibleMass_lower_bound (G := G) (q := m)
          (compressed_bound (G := G) (q := q) xs h_bound) y)
  have h_m_le :
      (m : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 ≤
        (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
    gcongr
    exact_mod_cast compressed_card_le (G := G) (q := q) xs
  exact le_trans h_core h_m_le

end SoP
end HTechnique
end Migration
end NextGen
