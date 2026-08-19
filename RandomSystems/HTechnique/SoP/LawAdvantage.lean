/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.SecurityDefs
import RandomSystems.HTechnique.SoP.Compression
import RandomSystems.HTechnique.Tactics

/-!
# SoP law-level transcript advantage

This module contains the public SoP application endpoints on the CR18/thesis
transcript-law surface.  Representative adapters are used only inside bridge
proofs; representative and old bounded adaptive advantage endpoints live in
`SoP.AdaptiveAdvantage`.
-/

noncomputable section

open scoped NNReal
open scoped RandomSystems.CR18

namespace RandomSystems
namespace HTechnique
namespace SoP

variable {G : Type*} {q : Nat}

/-- **Source theorem boundary.** Law-level pointwise SoP transcript bound for a
deterministic CR18 environment.  A deterministic environment is treated as the
degenerate law-level PDE concentrated on that environment, so this wrapper
delegates to the arbitrary law-level SoP theorem. -/
theorem repeatedQuerySoP_law_experiment_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (E : QQueryEnvironment G G q)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    RandomSystems.statDist
      (ProbPDS.deterministicTranscriptDist (q := q)
        (normalizedSoPProbPDS (G := G)) E.1)
      (ProbPDS.deterministicTranscriptDist (q := q)
        (ProbPDS.urf (X := G) (Y := G)) E.1) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  letI : Nonempty G := ⟨0⟩
  have h :=
    repeatedQuerySoP_probPDE_bound
      (G := G) (q := q)
      (E := ProbPDE.ofDDE E.1)
      h_bound
      (ProbPDE.ofDDE_KQueryTotal E.1 (by simpa [DDEKQueryTotal] using E.2))
  simpa only [ProbPDS.transcriptDist_ofDDE] using h

/-- **Source theorem boundary.** Law-level fixed-query SoP transcript bound.
This is the deterministic-environment specialization of the arbitrary
law-level SoP theorem, where the environment asks exactly the supplied query
vector. -/
theorem repeatedQuerySoP_fixedQuery_law_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (xs : Fin q → G) (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist
          (normalizedSoPProbPDS (G := G)) xs)
        (ProbPDS.fixedQueryTranscriptDist
          (ProbPDS.urf (X := G) (Y := G)) xs) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  letI : Nonempty G := ⟨0⟩
  have h :=
    repeatedQuerySoP_probPDE_bound
      (G := G) (q := q)
      (E := ProbPDE.ofDDE (fixedQueryDDE (Y := G) xs))
      h_bound
      (ProbPDE.ofDDE_KQueryTotal
        (fixedQueryDDE (Y := G) xs)
        (by
          intro ys hlen
          exact ⟨xs ⟨ys.length, hlen⟩, by simp [fixedQueryDDE, hlen]⟩))
  simpa only [ProbPDS.fixedQueryTranscriptDist, ProbPDS.transcriptDist_ofDDE] using h

/-- **Source theorem boundary.** Law-level arbitrary-PDE SoP transcript bound.
Public callers provide only a law-level environment and its meaningful
q-query-totality premise; the proof delegates to the law-level arbitrary-PDE
SoP theorem in `SoP.Compression`. -/
theorem repeatedQuerySoP_probPDE_law_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (E : ProbPDE G G)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (hEtotal : E.KQueryTotal q) :
    RandomSystems.statDist
        (ProbPDS.transcriptDist (q := q) (normalizedSoPProbPDS (G := G)) E)
        (ProbPDS.transcriptDist (q := q) (ProbPDS.urf (X := G) (Y := G)) E) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  letI : Nonempty G := ⟨0⟩
  exact repeatedQuerySoP_probPDE_bound (G := G) (q := q) E h_bound hEtotal

/-- **Source-theorem bridge.** The migrated paper-facing adaptive PRF advantage
for normalized SoP, in the thesis transcript-law sense of `Adv`: compare the
SoP PDS law with the ideal URF law. -/
noncomputable def advPRF
    [AddGroup G] [Fintype G] [DecidableEq G] : ℝ := by
  letI : Nonempty G := ⟨0⟩
  exact
    SecurityDefs.advPRF
      (q := q)
      (normalizedSoPProbPDS (G := G))

/-- **Source theorem boundary.** The raw CR18 filtered distinguishing advantage
for normalized SoP is bounded by the migrated thesis-style transcript-law PRF
advantage.

The normalization premise required by the generic CR18 bridge is discharged for
the concrete SoP/URF pair: both systems are laws of total function evaluators,
so Maurer's `[q]` finite-query padding applies directly. -/
theorem filteredDelta_le_advPRF
    [AddGroup G] [Fintype G] [DecidableEq G] :
    (Δ(⌈q⌉ (normalizedSoPProbPDS (G := G)).val,
        ⌈q⌉ (ProbPDS.urf (X := G) (Y := G)).val) : ℝ) ≤
      advPRF (G := G) (q := q) := by
  letI : Nonempty G := ⟨0⟩
  have hRtotal : (normalizedSoPProbPDS (G := G)).KStepTotal q := by
    htechnique_total
  have hItotal : (ProbPDS.urf (X := G) (Y := G)).KStepTotal q := by
    htechnique_total
  have hRtotNonempty : RandomSystems.CR18.CondEquiv.TotalOnNonempty
      (normalizedSoPProbPDS (G := G)).val := by
    htechnique_total
  have hItotNonempty : RandomSystems.CR18.CondEquiv.TotalOnNonempty
      (ProbPDS.urf (X := G) (Y := G)).val := by
    htechnique_total
  have hNorm : RandomSystems.CR18.DeltaFilteredFiniteQueryNormalization q
      (normalizedSoPProbPDS (G := G)).val
      (ProbPDS.urf (X := G) (Y := G)).val :=
    RandomSystems.CR18.deltaFilteredFiniteQueryNormalization_of_totalOnNonempty
      (0 : G) q
      (normalizedSoPProbPDS (G := G)).val
      (ProbPDS.urf (X := G) (Y := G)).val
      hRtotNonempty hItotNonempty
  exact SecurityDefs.filteredDelta_le_Adv
    (q := q)
    (normalizedSoPProbPDS (G := G))
    (ProbPDS.urf (X := G) (Y := G))
    hRtotal hItotal hNorm

/-- **Source theorem boundary.** Migrated SoP adaptive PRF advantage bound,
matching the source endpoint `sop_advPRF_le` but on the CR18/thesis
transcript-law advantage surface. -/
theorem advPRF_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    advPRF (G := G) (q := q) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  letI : Nonempty G := ⟨0⟩
  refine
    SecurityDefs.advPRF_le_of_pointwise
      (q := q)
      (normalizedSoPProbPDS (G := G))
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)
      ?pointwise
  intro E
  exact repeatedQuerySoP_law_experiment_bound (G := G) (q := q) E h_bound

/-- **Source theorem boundary.** Raw CR18 filtered distinguishing bound for
normalized SoP, obtained by composing the filtered-`Delta`/`Adv` bridge with the
migrated SoP transcript-law PRF bound. -/
theorem filteredDelta_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    (Δ(⌈q⌉ (normalizedSoPProbPDS (G := G)).val,
        ⌈q⌉ (ProbPDS.urf (X := G) (Y := G)).val) : ℝ) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  exact le_trans
    (filteredDelta_le_advPRF (G := G) (q := q))
    (advPRF_bound (G := G) (q := q) h_bound)

end SoP
end HTechnique
end RandomSystems
