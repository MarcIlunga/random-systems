/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Applications.XoP

/-!
# Concrete XoP Counting Scaffold

This file isolates the next theorem-first counting slice for XoP.  It names the
finite output alphabet size, the concrete-counting normalizer, and the
compatible transcript count `Z`, then closes the wrapper from per-input
normalized counting models to the existing fixed-input transcript bound.
-/

noncomputable section

open scoped NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Counting

variable {X Y : Type*} {q : Nat}

/-- The finite output alphabet size used in the concrete XoP counting formulas. -/
def outputAlphabetSize (Y : Type*) [Fintype Y] : Nat :=
  Fintype.card Y

/-- The local notation `N = |Y|` for XoP counting statements. -/
abbrev N (Y : Type*) [Fintype Y] : Nat :=
  outputAlphabetSize Y

/--
The falling-factorial-style normalizer for concrete XoP counting.

The intended later instantiation is the `NNReal` interpretation of a formula
such as `(N)_q^2 / N^q`.  It remains abstract here so this slice can state and
reuse the normalized-counting wrapper before committing to the arithmetic proof.
-/
structure FallingFactorialNormalizer (Y : Type*) (q : Nat) [Fintype Y] where
  /-- Abstract normalizing mass for compatible hidden states. -/
  value : NNReal
  /-- The normalizer must be nonzero to induce a density. -/
  value_ne_zero : value ≠ 0

attribute [nolint docBlame] FallingFactorialNormalizer

/--
Concrete XoP-compatible counts for a fixed transcript alphabet.

`Z` is the compatible-count function: for each visible transcript, it records
the hidden permutation-pair count or mass that will later be proved compatible
with the XoP real transcript law.
-/
structure CompatibleCount (X Y : Type*) (q : Nat)
    [Fintype (Transcript X Y q)] [Fintype Y] where
  /-- Compatible hidden-state count for each transcript. -/
  Z : Transcript X Y q → NNReal
  /-- Abstract falling-factorial-style normalizer for `Z`. -/
  normalizer : FallingFactorialNormalizer Y q

attribute [nolint docBlame] CompatibleCount

/-- The density induced by a concrete compatible count. -/
def CompatibleCount.density
    [Fintype (Transcript X Y q)] [Fintype Y]
    (C : CompatibleCount X Y q) :
    Transcript X Y q → NNReal :=
  fun transcript => C.Z transcript / C.normalizer.value

/--
Named obligation: a concrete compatible count realizes the generic normalized
counting model for one fixed input sequence.

Future work can fill this obligation by proving the `Z` formula, the corrected
normalizer, the real/reference density identity, and the positive-error
estimate. -/
structure RealizesNormalizedCountingModel
    [Fintype (Transcript X Y q)] [Fintype Y]
    {real reference : Dist (Transcript X Y q)} {ε : NNReal}
    (C : CompatibleCount X Y q) where
  /-- The generic normalized counting model induced by this concrete count. -/
  model : NormalizedCountingModel real reference ε
  /-- The model's count is the concrete compatible-count function `Z`. -/
  count_eq : model.count = C.Z
  /-- The model's expected count is the concrete falling-factorial normalizer. -/
  expected_eq : model.expected = C.normalizer.value

/-- Build the concrete realization package from the density identity and the
analytic positive-error estimate. -/
theorem realizesNormalizedCountingModel_of_density_and_positiveError
    [Fintype (Transcript X Y q)] [Fintype Y]
    {real reference : Dist (Transcript X Y q)} {ε : NNReal}
    (C : CompatibleCount X Y q)
    (hreal : ∀ t, real t = C.density t * reference t)
    (hpos : (∑ t : Transcript X Y q, (C.density t * reference t - reference t)) ≤ ε) :
    Nonempty
      (RealizesNormalizedCountingModel
        (real := real) (reference := reference) (ε := ε) C) := by
  refine ⟨?_⟩
  refine {
    model := ?_,
    count_eq := ?_,
    expected_eq := ?_
  }
  · refine {
      count := C.Z,
      expected := C.normalizer.value,
      expected_ne_zero := C.normalizer.value_ne_zero,
      real_eq_count_density := ?_,
      positive_error_le := ?_
    }
    · intro t
      exact hreal t
    · exact hpos
  · rfl
  · rfl

/--
Concrete XoP counting obligation for every fixed input.

For each fixed input sequence, it asks for a compatible count `Z` and an
abstract falling-factorial normalizer that realize the generic
`NormalizedCountingModel` already used by the XoP scaffold.
-/
def FixedInputConcreteCountingModels
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)]
    [Fintype Y]
    (M : SecurityInstance X Y q) : Prop :=
  ∀ inputs : Fin q → X,
    ∃ C : CompatibleCount X Y q,
      Nonempty
        (RealizesNormalizedCountingModel
          (real := M.real.transcriptDist inputs)
          (reference := M.ideal.transcriptDist inputs)
          (ε := M.bound)
          C)

/--
Concrete compatible counts induce the generic fixed-input counting-density
obligation.
-/
theorem fixed_countingDensity_of_concreteCounting
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)]
    [Fintype Y]
    (M : SecurityInstance X Y q)
    (h : FixedInputConcreteCountingModels M) :
    FixedInputCountingDensityBound M := by
  intro inputs
  rcases h inputs with ⟨C, ⟨hC⟩⟩
  exact ⟨hC.model, NormalizedCountingModel.expected_ne_zero hC.model⟩

/--
If every fixed input has a concrete XoP normalized counting model, then the
existing XoP density wrapper yields the fixed-input transcript bound.
-/
theorem fixed_transcript_bound_of_concreteCounting
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)]
    [Fintype Y]
    (M : SecurityInstance X Y q)
    (h : FixedInputConcreteCountingModels M) :
    FixedInputTranscriptBound M :=
  fixed_transcript_bound_of_countingDensity M
    (fixed_countingDensity_of_concreteCounting M h)

end Counting
end XoP
end Applications
end RandomSystems
