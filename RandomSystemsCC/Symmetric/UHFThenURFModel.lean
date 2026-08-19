/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystems.HTechnique.HashThenPRF
import RandomSystemsCC.TypedFinite

/-!
# Typed model for hash-then-URF

The source port multiplexes a uniform hash key and a short-input random
function.  The target port is a long-input random function.  This file
bundles the genuine two-query `m ↦ ρ(H k m)` converter.
-/

namespace RandomSystemsCC.Symmetric.UHFThenURF

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystems.HTechnique.HashThenPRF
open RandomSystemsCC.TypedFinite

universe u

/-- Source operations: read the sampled hash key or evaluate the short URF. -/
inductive SourceIn (K X : Type u) : Type u
  | key
  | eval (point : X)
  deriving DecidableEq

/-- Replies from the bundled key/short-URF source. -/
inductive SourceOut (K T : Type u) : Type u
  | key (value : K)
  | value (result : Option T)

/-- Source and target oracle codes. -/
inductive Code
  | short
  | long
  deriving DecidableEq

/-- Signatures for the bundled short oracle and long oracle. -/
abbrev signatures (K M X T : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .short => SourceIn K X
    | .long => M
  output
    | .short => SourceOut K T
    | .long => Option T

instance (K M X T : Type u) : DecidableEq (signatures K M X T).Code := by
  change DecidableEq Code
  infer_instance

def sourceBoundary (K M X T : Type u) :
    Boundary (signatures K M X T) Unit :=
  fun _ => .short

def targetBoundary (K M X T : Type u) :
    Boundary (signatures K M X T) Unit :=
  fun _ => .long

section

variable {K M X T : Type u}

/-- The two-query hash-then-oracle state machine. -/
def hashThenOracleStep (hash : K → M → X) (fallbackKey : K) :
    M → List (SourceOut K T) → SourceIn K X ⊕ Option T
  | _, [] => .inl .key
  | message, [.key key] => .inl (.eval (hash key message))
  | message, [.value _] => .inl (.eval (hash fallbackKey message))
  | _, _ :: .value result :: _ => .inr result
  | _, _ => .inr none

/-- The genuine two-query converter for an arbitrary keyed hash function. -/
noncomputable def hashThenOracleOf [Nonempty K] (hash : K → M → X) :
    Primitive Unit (signatures K M X T) () :=
  let fallbackKey : K := Classical.choice inferInstance
  Primitive.ofHistory .short .long
    (PFunConverter.ProtocolFn.ofStep
      (hashThenOracleStep hash fallbackKey) (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep
      (hashThenOracleStep hash fallbackKey) (fun _ => 2)
      (by
        intro request answers
        cases answers with
        | nil => simp [hashThenOracleStep]
        | cons answer tail =>
            cases tail with
            | nil =>
                cases answer <;> simp [hashThenOracleStep]
            | cons answer' tail' =>
                cases answer' <;> simp [hashThenOracleStep])
      ⟨2, by intro; rfl⟩)

/-- Hash-then-oracle specialized to an epsilon-universal hash object. -/
noncomputable def hashThenOraclePrimitive
    [Fintype K] [Nonempty K] (Hf : EpsUniversalHash K M X) :
    Primitive Unit (signatures K M X T) () :=
  hashThenOracleOf Hf.hash

end

end RandomSystemsCC.Symmetric.UHFThenURF
