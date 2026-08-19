/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.XoPCounting
import RandomSystems.CompatibleCount
import Mathlib.Data.Fintype.CardEmbedding

/-!
# XoP Combinatorics

This file exposes the elementary hidden-state count used by the concrete XoP
counting scaffold.  For a visible output tuple `y`, a hidden tuple `a` is
compatible when both `a` and `a + y` are injective.

The definitional core and its counting facts live in the dependency-light
shared module `RandomSystems.CompatibleCount` and are `export`ed here under
the historical `XoP.Combinatorics` names (so `simp`/`unfold`/term references
in downstream proofs keep working on the same constants).  This file adds the
XoP-specific `Transcript` wrappers and `CompatibleCount` normalizer
certificates.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Combinatorics

export RandomSystems.CompatibleCount (
  InjectiveTuple
  injectiveTupleCount
  injectiveTupleCount_descFactorial
  InjectiveTupleSubtype
  injectiveTupleSubtype_card
  shifted
  CompatibleHiddenState
  CompatiblePair
  compatiblePairEquivInjectiveProduct
  compatiblePairEquivSigma
  compatiblePair_card
  compatibleCountNat
  compatibleCountNat_eq_card_filter
  compatibleFiber_card
  compatibleHiddenState_add_const
  compatibleFiberAddConstEquiv
  compatibleCountNat_add_const
  sum_compatibleCountNat_eq_compatiblePair_card
  sum_compatibleCountNat_eq_injectiveTupleCount_sq
  sum_compatibleCountNat_eq_descFactorial_sq
  compatibleCountNNReal
  compatibleCountNNReal_eq_coe_nat
  compatibleCountNNReal_add_const
  sum_compatibleCountNNReal_eq_descFactorial_sq
  visibleTupleCount_eq_pow
  idealCompatibleExpectation_eq_descFactorial_sq_div_pow
  compatibleCountNat_le_injectiveTupleCount
  compatibleCountNat_le_descFactorial
  compatibleHiddenState_zero
  compatibleHiddenState_one)

variable {G : Type*} {q : Nat}

/--
Correct theorem-facing normalizer for the visible-output compatible count:
`(N)_q^2 / N^q`.  The explicit `q ≤ N` assumption is the reusable condition
that makes `(N)_q` nonzero.
-/
def compatibleExpectationNormalizer [AddGroup G] [Fintype G] (hq : q ≤ Fintype.card G) :
    Counting.FallingFactorialNormalizer G q where
  value := (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
      NNReal) / ((Fintype.card G ^ q : Nat) : NNReal)
  value_ne_zero := by
    have hdesc_pos : 0 < (Fintype.card G).descFactorial q := Nat.descFactorial_pos.mpr hq
    have hnum_pos :
        0 < (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) :=
      Nat.cast_pos.mpr (Nat.mul_pos hdesc_pos hdesc_pos)
    have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
    have hden_pos : 0 < ((Fintype.card G ^ q : Nat) : NNReal) :=
      Nat.cast_pos.mpr (pow_pos hcard_pos q)
    exact ne_of_gt (div_pos hnum_pos hden_pos)

/-- The output component of a transcript, viewed as the visible XoP tuple. -/
def transcriptOutputs (t : Transcript G G q) : Fin q → G :=
  fun i => (t i).2

/-- Transcript-level natural count, depending only on the output component. -/
def compatibleTranscriptCountNat [AddGroup G] [Fintype G] (t : Transcript G G q) : Nat :=
  compatibleCountNat (transcriptOutputs t)

/-- Transcript-level NNReal count, depending only on the output component. -/
def compatibleTranscriptCountNNReal [AddGroup G] [Fintype G] (t : Transcript G G q) : NNReal :=
  compatibleCountNNReal (transcriptOutputs t)

/-- The transcript-level natural count reads the output component of the transcript. -/
@[simp]
theorem compatibleTranscriptCountNat_eq_outputs [AddGroup G] [Fintype G] (t : Transcript G G q) :
    compatibleTranscriptCountNat t =
      compatibleCountNat (transcriptOutputs t) := by
  rfl

/-- The transcript-level NNReal count reads the output component of the transcript. -/
@[simp]
theorem compatibleTranscriptCountNNReal_eq_outputs [AddGroup G] [Fintype G] (t : Transcript G G q) :
    compatibleTranscriptCountNNReal t =
      compatibleCountNNReal (transcriptOutputs t) := by
  rfl

/-- The trivial normalizer used to package the raw compatible-count function. -/
def compatibleCountNormalizer [Fintype G] : Counting.FallingFactorialNormalizer G q where
  value := 1
  value_ne_zero := one_ne_zero

/--
The concrete `CompatibleCount` object whose `Z` reads the output component of a
transcript and returns the compatible hidden-state count for that output tuple.
-/
def compatibleCount [AddGroup G] [Fintype G] : Counting.CompatibleCount G G q where
  Z := compatibleTranscriptCountNNReal
  normalizer := compatibleCountNormalizer

/--
The theorem-facing compatible count using the corrected normalizer
`(N)_q^2 / N^q` under the explicit nonzero-domain assumption `q ≤ N`.
-/
def compatibleCountWithExpectationNormalizer [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) : Counting.CompatibleCount G G q where
  Z := compatibleTranscriptCountNNReal
  normalizer := compatibleExpectationNormalizer hq

/-- The packaged compatible count is exactly the output-tuple hidden-state count. -/
@[simp]
theorem compatibleCount_Z [AddGroup G] [Fintype G] (t : Transcript G G q) :
    compatibleCount.Z t = compatibleCountNNReal (transcriptOutputs t) := by
  rfl

/-- The corrected packaged compatible count has the same `Z` function. -/
@[simp]
theorem compatibleCountWithExpectationNormalizer_Z [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) (t : Transcript G G q) :
    (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).Z t =
      compatibleCountNNReal (transcriptOutputs t) := by
  rfl

/-- The corrected packaged compatible count exposes the expected normalizer. -/
@[simp]
theorem compatibleCountWithExpectationNormalizer_normalizer [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).normalizer.value =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        NNReal) / ((Fintype.card G ^ q : Nat) : NNReal) := by
  rfl

end Combinatorics
end XoP
end Applications
end RandomSystems
