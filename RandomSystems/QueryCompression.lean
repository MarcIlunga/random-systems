/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.FunctionEvaluator

/-!
# Repeated-query compression for CR18 fixed-query laws

This module contains the application-independent compression step used by
H-technique proofs: an arbitrary fixed query vector is replaced by the canonical
injective vector of the distinct queries it contains, and compressed output
vectors are deterministically expanded back to the original repeated-query
positions.

The construction is exact.  It uses the image of the actual query tuple and a
subtype enumeration of that image, so it introduces no default query and no
over-approximated event.
-/

noncomputable section

namespace RandomSystems
namespace CR18

attribute [local instance] Classical.decEq

variable {X Y : Type*} {q : Nat}

/-- **Support lemma forced by formalization; candidate for upstream.** The set
of distinct query values appearing in `xs`. -/
def queryImageSet [Fintype X] (xs : Fin q → X) : Finset X :=
  Finset.univ.image xs

/-- **Support lemma forced by formalization; candidate for upstream.** A
canonical injective enumeration of the distinct query values in `xs`. -/
def compressedQuery [Fintype X] (xs : Fin q → X) :
    Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) → X :=
  fun j => ((Fintype.equivFin {x : X // x ∈ queryImageSet xs}).symm j).1

/-- **Support lemma forced by formalization; candidate for upstream.** For each
original query index, the corresponding compressed-query index. -/
def compressedQueryIndex [Fintype X] (xs : Fin q → X) :
    Fin q → Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) :=
  fun i => (Fintype.equivFin {x : X // x ∈ queryImageSet xs}) ⟨xs i, by simp [queryImageSet]⟩

/-- **Support lemma forced by formalization; candidate for upstream.** Expand
compressed output vectors by copying outputs back to repeated query positions. -/
def expandCompressedOutputs [Fintype X] (xs : Fin q → X) :
    (Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) → Y) → (Fin q → Y) :=
  fun ys i => ys (compressedQueryIndex xs i)

/-- **Support lemma forced by formalization; candidate for upstream.** The
compressed query vector is injective by construction. -/
theorem compressedQuery_injective [Fintype X] (xs : Fin q → X) :
    Function.Injective (compressedQuery xs) := by
  exact fun _ _ h =>
    (Fintype.equivFin {x : X // x ∈ queryImageSet xs}).symm.injective (Subtype.ext h)

/-- **Support lemma forced by formalization; candidate for upstream.** Expanding
the compressed query vector recovers the original query vector. -/
theorem expandCompressedOutputs_compressedQuery [Fintype X] (xs : Fin q → X) :
    expandCompressedOutputs xs (compressedQuery xs) = xs := by
  funext i
  simp [expandCompressedOutputs, compressedQuery, compressedQueryIndex]

/-- **Support lemma forced by formalization; candidate for upstream.**
Evaluating any function on the original repeated query vector is the same as
evaluating it on the compressed query vector and expanding outputs. -/
theorem expandCompressedOutputs_eval_compressedQuery [Fintype X] (xs : Fin q → X)
    (f : X → Y) :
    expandCompressedOutputs xs (fun j => f (compressedQuery xs j)) =
      fun i => f (xs i) := by
  exact congrArg (fun g => fun i => f (g i)) (expandCompressedOutputs_compressedQuery xs)

/-- **Support lemma forced by formalization; candidate for upstream.**
Distribution-level repeated-query compression for evaluating sampled functions. -/
theorem fTransform_eval_repeated_eq_expand_compressedQuery [Fintype X]
    (xs : Fin q → X) (D : RandomSystems.Dist (X → Y)) :
    RandomSystems.Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) D =
      RandomSystems.Dist.fTransform (expandCompressedOutputs xs)
        (RandomSystems.Dist.fTransform
          (fun f : X → Y =>
            fun j : Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) =>
              f (compressedQuery xs j)) D) := by
  rw [RandomSystems.Dist.fTransform_comp]
  congr 1
  funext f
  exact (expandCompressedOutputs_eval_compressedQuery xs f).symm

/-- **Support lemma forced by formalization; candidate for upstream.**
Sample-space form of repeated-query compression. -/
theorem fTransform_sampled_eval_repeated_eq_expand_compressedQuery
    {Ω : Type*} [Fintype X]
    (xs : Fin q → X) (F : Ω → X → Y) (D : RandomSystems.Dist Ω) :
    RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i)) D =
      RandomSystems.Dist.fTransform (expandCompressedOutputs xs)
        (RandomSystems.Dist.fTransform
          (fun ω : Ω =>
            fun j : Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) =>
              F ω (compressedQuery xs j)) D) := by
  simpa [RandomSystems.Dist.fTransform_comp, Function.comp] using
    fTransform_eval_repeated_eq_expand_compressedQuery (X := X) (Y := Y) xs
      (RandomSystems.Dist.fTransform F D)

/-- **Support lemma forced by formalization; candidate for upstream.**
Compression never increases the query count. -/
theorem compressedQuery_card_le [Fintype X] (xs : Fin q → X) :
    Fintype.card {x : X // x ∈ queryImageSet xs} ≤ q := by
  rw [Fintype.card_coe]
  simpa [queryImageSet] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin q))) (f := xs))

/-- **Support lemma forced by formalization; candidate for upstream.** A query
bound is monotone under compression. -/
theorem compressedQuery_bound [Fintype X] (xs : Fin q → X)
    {N : Nat} (h_bound : q ^ 3 ≤ N ^ 2) :
    (Fintype.card {x : X // x ∈ queryImageSet xs}) ^ 3 ≤ N ^ 2 := by
  exact le_trans (Nat.pow_le_pow_left (compressedQuery_card_le xs) 3) h_bound

/-- **Support lemma forced by formalization; candidate for upstream.** Expand a
compressed fixed-query transcript prefix back to the original repeated-query
transcript-prefix carrier. -/
def expandCompressedTranscriptPrefix [Fintype X] (xs : Fin q → X) :
    CR18TranscriptPrefix X Y (Fintype.card {x : X // x ∈ queryImageSet xs}) →
      CR18TranscriptPrefix X Y q :=
  fun t =>
    (vectorOfFunction xs,
      vectorOfFunction (expandCompressedOutputs xs (functionOfVector t.2)))

/-- **Support lemma forced by formalization; candidate for upstream.** Lifting
an expanded output law to the original fixed-input transcript-prefix carrier is
the same as first lifting the compressed law and then expanding transcript
prefixes. -/
theorem fixedInputLiftDist_expandCompressedOutputs [Fintype X]
    (xs : Fin q → X)
    (D : RandomSystems.Dist
      (Fin (Fintype.card {x : X // x ∈ queryImageSet xs}) → Y)) :
    fixedInputLiftDist xs (RandomSystems.Dist.fTransform (expandCompressedOutputs xs) D) =
      RandomSystems.Dist.fTransform (expandCompressedTranscriptPrefix xs)
        (fixedInputLiftDist (compressedQuery xs) D) := by
  simpa [expandCompressedTranscriptPrefix, fixedInputTranscriptPrefix] using
    fixedInputLiftDist_fTransform (X := X) (Y := Y) (q := q)
      (X' := X) (Y' := Y)
      (q' := Fintype.card {x : X // x ∈ queryImageSet xs})
      xs (compressedQuery xs) (expandCompressedOutputs xs) D

/-- **Support lemma forced by formalization; candidate for upstream.** Exact
repeated-query compression for any function-evaluator CR18 system. -/
theorem transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress
    {Ω : Type*} [Fintype X] [Fintype Y]
    (pΩ : RandomSystems.Dist.ProbDist Ω) (F : Ω → X → Y) (xs : Fin q → X) :
    PFunPDE.transcriptLawDist
        (PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
          (functionEvaluatorRV F) (fixedQueryEnvironment xs) q) =
      RandomSystems.Dist.fTransform (expandCompressedTranscriptPrefix xs)
        (PFunPDE.transcriptLawDist
          (PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
            (functionEvaluatorRV F) (fixedQueryEnvironment (compressedQuery xs))
            (Fintype.card {x : X // x ∈ queryImageSet xs}))) := by
  rw [transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist]
  rw [transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist]
  rw [fTransform_sampled_eval_repeated_eq_expand_compressedQuery]
  rw [fixedInputLiftDist_expandCompressedOutputs]

end CR18
end RandomSystems
