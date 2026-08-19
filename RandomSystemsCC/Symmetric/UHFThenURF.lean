/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.UHFThenURFModel
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage

/-!
# UHF then URF constructs a long-input URF

This file defines the bounded source and target oracle resources and freezes
both the generic epsilon-universal and polynomial-hash construction
statements.  The polynomial message encoding is length-separated at the
object level; no padding convention is deferred to the proof.
-/

namespace RandomSystemsCC.Symmetric.UHFThenURF

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystems.HTechnique.HashThenPRF
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto BigOperators ENNReal

universe u

section Generic

variable {K M X T : Type u}
variable [Fintype K] [DecidableEq K] [Nonempty K]
variable [Fintype M] [DecidableEq M] [Nonempty M]
variable [Fintype X] [DecidableEq X] [Nonempty X]
variable [Fintype T] [DecidableEq T] [Nonempty T]

/-- Number of short-oracle evaluations in a source history, including the
current query. -/
private def sourceEvalCount
    (history : List (Query (signatures K M X T)
      (sourceBoundary K M X T))) : Nat :=
  (history.filter fun query =>
    match query with
    | ⟨(), .eval _⟩ => true
    | _ => false).length

/-- The deterministic bundled source at a fixed hash key and short function. -/
def sourceDDS (Q : Nat) (sample : K × (X → T)) :
    DependentDDS (signatures K M X T) (sourceBoundary K M X T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨(), .key⟩ => .key sample.1
    | ⟨(), .eval point⟩ =>
        .value <| if sourceEvalCount history ≤ Q
          then some (sample.2 point)
          else none

/-- The normalized bundled key/short-URF law. -/
noncomputable def sourceLaw (Q : Nat) :
    DependentPDS.Prob (signatures K M X T) (sourceBoundary K M X T) :=
  ⟨Dist.fTransform (sourceDDS Q) (Dist.uniform (K × (X → T))),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named source resource: a uniform hash key and `Q`-bounded short URF. -/
noncomputable def uhfShortUrfResource
    (Hf : EpsUniversalHash K M X) (Q : Nat) :
    Phi Unit (signatures K M X T) :=
  let _hash := Hf.hash
  ⟨sourceBoundary K M X T, DependentRandomSystem.ofProb (sourceLaw Q)⟩

/-- The deterministic `Q`-bounded long oracle at a fixed function. -/
def targetDDS (Q : Nat) (oracle : M → T) :
    DependentDDS (signatures K M X T) (targetBoundary K M X T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨(), message⟩ =>
        if history.length ≤ Q then some (oracle message) else none

/-- The normalized bounded long-URF law. -/
noncomputable def targetLaw (Q : Nat) :
    DependentPDS.Prob (signatures K M X T) (targetBoundary K M X T) :=
  ⟨Dist.fTransform (targetDDS (K := K) (X := X) Q)
      (Dist.uniform (M → T)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named target resource: the `Q`-query random function `M → T`. -/
noncomputable def boundedLongUrfResource (Q : Nat) :
    Phi Unit (signatures K M X T) :=
  ⟨targetBoundary K M X T, DependentRandomSystem.ofProb (targetLaw Q)⟩

/-- The named protocol embedding of the hash-then-oracle primitive. -/
noncomputable def hashThenOracle (Hf : EpsUniversalHash K M X) :
    Protocol Unit (signatures K M X T) :=
  hashThenOraclePrimitive (T := T) Hf

/-! ## Generic final construction statement -/

/-- **An epsilon-universal hash followed by a short URF constructs a bounded
long-input URF**, with the tight adaptive collision term. -/
theorem uhf_then_urf_constructs_long_urf
    (Hf : EpsUniversalHash K M X) (Q : Nat) :
    ⟪uhfShortUrfResource (T := T) Hf Q⟫
      —[hashThenOracle (T := T) Hf;
        (Nat.choose Q 2 : ℝ≥0∞) * (Hf.eps : ℝ≥0∞)]→
    ⟪boundedLongUrfResource (K := K) (X := X) (T := T) Q⟫ := by
  sorry

end Generic

/-! ## Polynomial-hash objects and final statement -/

/-- Field vectors of length at most `ell`, with the length retained in the
type. -/
abbrev BoundedMessage (F : Type u) (ell : Nat) :=
  Σ n : Fin (ell + 1), Fin n.val → F

instance (F : Type u) (ell : Nat) : Nonempty (BoundedMessage F ell) :=
  ⟨⟨⟨0, Nat.zero_lt_succ ell⟩, fun index => Fin.elim0 index⟩⟩

/-- Length-separated polynomial hashing.  The terminal coefficient `1` at
degree `n` distinguishes different message lengths; message coefficients
occupy only degrees strictly below `n`. -/
def polynomialHash {F : Type u} [Field F] {ell : Nat}
    (key : F) (message : BoundedMessage F ell) : F :=
  key ^ message.1.val +
    ∑ i : Fin message.1.val, message.2 i * key ^ i.val

section Polynomial

variable {F T : Type u}
variable [Fintype F] [DecidableEq F] [Nonempty F] [Field F]
variable [Fintype T] [DecidableEq T] [Nonempty T]

/-- **Length-separated polynomial hashing is `ell / |F|`-universal.**  The
epsilon is fixed by the downstream statement
`polynomial_hash_then_urf_constructs_long_urf`, which asserts the bound
`C(Q,2) * (ell / |F|)`; it is not free to choose. -/
noncomputable def polynomialHashUniversal (ell : Nat) :
    EpsUniversalHash F (BoundedMessage F ell) F where
  hash := polynomialHash
  eps := (ell : NNReal) / (Fintype.card F : NNReal)
  universal := by sorry

/-- The polynomial-hash source uses a uniform field key and a short URF
`F → T`. -/
noncomputable def polynomialHashShortUrfResource (Q ell : Nat) :
    Phi Unit (signatures F (BoundedMessage F ell) F T) :=
  ⟨sourceBoundary F (BoundedMessage F ell) F T,
    DependentRandomSystem.ofProb (sourceLaw (K := F)
      (M := BoundedMessage F ell) (X := F) (T := T) Q)⟩

/-- The polynomial-hash-then-URF converter. -/
noncomputable def polynomialHashThenOraclePrimitive (ell : Nat) :
    Primitive Unit (signatures F (BoundedMessage F ell) F T) () :=
  hashThenOracleOf (T := T) (polynomialHash (F := F) (ell := ell))

/-- The named protocol embedding of polynomial hash-then-URF. -/
noncomputable def polynomialHashThenOracle (ell : Nat) :
    Protocol Unit (signatures F (BoundedMessage F ell) F T) :=
  polynomialHashThenOraclePrimitive (F := F) (T := T) ell

/-- **Length-separated polynomial hashing followed by a short URF constructs
a bounded long-input URF** over any finite field. -/
theorem polynomial_hash_then_urf_constructs_long_urf (Q ell : Nat) :
    ⟪polynomialHashShortUrfResource (F := F) (T := T) Q ell⟫
      —[polynomialHashThenOracle (F := F) (T := T) ell;
        (Nat.choose Q 2 : ℝ≥0∞) *
          ((ell : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))]→
    ⟪boundedLongUrfResource (K := F) (M := BoundedMessage F ell)
      (X := F) (T := T) Q⟫ := by
  sorry

end Polynomial

end RandomSystemsCC.Symmetric.UHFThenURF
