/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.UHFURFMACModel
import RandomSystemsCC.Symmetric.UHFThenURF
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage
import RandomSystemsCC.TypedConstruct

/-!
# UHF/URF MAC construction statements

The source, intermediate long-oracle resource, and authenticated target share
one typed carrier.  The final protocol is the serial product of the bounded
URF-MAC protocol and the hash-then-oracle protocol.  Proofs are deferred until
the statement surface is complete.
-/

namespace RandomSystemsCC.Symmetric.UHFURFMAC

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystems.HTechnique.HashThenPRF
open RandomSystemsCC.Symmetric
open RandomSystemsCC.Symmetric.UHFThenURF (BoundedMessage polynomialHash)
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto ENNReal

universe u

section Generic

variable {K M X T : Type u}
variable [Fintype K] [DecidableEq K] [Nonempty K]
variable [Fintype M] [DecidableEq M] [Nonempty M]
variable [Fintype X] [DecidableEq X] [Nonempty X]
variable [Fintype T] [DecidableEq T] [Nonempty T]

/-! ## Source and intermediate objects -/

private def sourcePayloads (q : Nat)
    (history : List (Query (signatures K M X T)
      (sourceBoundary K M X T))) : List (M × T) :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .sendPayload payload⟩ => some payload
    | _ => none).take q

private def sourceReplacement?
    (history : List (Query (signatures K M X T)
      (sourceBoundary K M X T))) : Option (M × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .replacePayload payload⟩ => some payload
        | _ => none) none

/-- Insecure channel bundled with a fixed hash key and short function. -/
def sourceDDS (q : Nat) (sample : K × (X → T)) :
    DependentDDS (signatures K M X T) (sourceBoundary K M X T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .key⟩ => .key sample.1
    | ⟨.alice, .eval point⟩ => .tag (sample.2 point)
    | ⟨.alice, .sendPayload _⟩ => .ack
    | ⟨.bob, .key⟩ => .key sample.1
    | ⟨.bob, .eval point⟩ => .tag (sample.2 point)
    | ⟨.bob, .receivePayload⟩ =>
        .payload ((sourceReplacement? history).orElse fun _ =>
          (sourcePayloads q history).getLast?)
    | ⟨.eve, .readPayload index⟩ =>
        .payload ((sourcePayloads q history)[index]?)
    | ⟨.eve, .replacePayload _⟩ => .ack

noncomputable def sourceLaw (q : Nat) :
    DependentPDS.Prob (signatures K M X T) (sourceBoundary K M X T) :=
  ⟨Dist.fTransform (sourceDDS q) (Dist.uniform (K × (X → T))),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named UHF/short-URF MAC source resource. -/
noncomputable def uhfMacAssumedResource
    (Hf : EpsUniversalHash K M X) (q : Nat) :
    Phi Interface (signatures K M X T) :=
  let _hash := Hf.hash
  ⟨sourceBoundary K M X T, DependentRandomSystem.ofProb (sourceLaw q)⟩

private def longPayloads (q : Nat)
    (history : List (Query (signatures K M X T)
      (longBoundary K M X T))) : List (M × T) :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .sendPayload payload⟩ => some payload
    | _ => none).take q

private def longReplacement?
    (history : List (Query (signatures K M X T)
      (longBoundary K M X T))) : Option (M × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .replacePayload payload⟩ => some payload
        | _ => none) none

/-- The common intermediate resource: insecure channel plus long URF. -/
def longDDS (q : Nat) (oracle : M → T) :
    DependentDDS (signatures K M X T) (longBoundary K M X T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .eval message⟩ => .tag (oracle message)
    | ⟨.alice, .sendPayload _⟩ => .ack
    | ⟨.bob, .eval message⟩ => .tag (oracle message)
    | ⟨.bob, .receivePayload⟩ =>
        .payload ((longReplacement? history).orElse fun _ =>
          (longPayloads q history).getLast?)
    | ⟨.eve, .readPayload index⟩ =>
        .payload ((longPayloads q history)[index]?)
    | ⟨.eve, .replacePayload _⟩ => .ack

noncomputable def longLaw (q : Nat) :
    DependentPDS.Prob (signatures K M X T) (longBoundary K M X T) :=
  ⟨Dist.fTransform (longDDS q) (Dist.uniform (M → T)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named long-URF MAC intermediate resource. -/
noncomputable def boundedLongMacResource (q : Nat) :
    Phi Interface (signatures K M X T) :=
  ⟨longBoundary K M X T, DependentRandomSystem.ofProb (longLaw q)⟩

/-! ## Authenticated target -/

private def idealMessages (q : Nat)
    (history : List (Query (signatures K M X T)
      (idealBoundary K M X T))) : List M :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .send message⟩ => some message
    | _ => none).take q

private def idealReplacement?
    (history : List (Query (signatures K M X T)
      (idealBoundary K M X T))) : Option (M × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .tryReplacement payload⟩ => some payload
        | _ => none) none

def idealDDS (q : Nat) (simulatorOracle : M → T) :
    DependentDDS (signatures K M X T) (idealBoundary K M X T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ =>
        let messages := idealMessages q history
        match idealReplacement? history with
        | none => messages.getLast?
        | some payload =>
            if payload ∈ messages.map (fun message =>
                (message, simulatorOracle message))
            then some payload.1
            else none
    | ⟨.eve, .readTagged index⟩ =>
        .tagged ((idealMessages q history)[index]? |>.map fun message =>
          (message, simulatorOracle message))
    | ⟨.eve, .tryReplacement _⟩ => .ack

noncomputable def idealLaw (q : Nat) :
    DependentPDS.Prob (signatures K M X T) (idealBoundary K M X T) :=
  ⟨Dist.fTransform (idealDDS q) (Dist.uniform (M → T)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

noncomputable def qAuthenticatedResource (q : Nat) :
    Phi Interface (signatures K M X T) :=
  ⟨idealBoundary K M X T, DependentRandomSystem.ofProb (idealLaw q)⟩

/-! ## Protocols, filters, and simulators -/

noncomputable def hashThenOracleProtocol (hash : K → M → X) :
    Protocol Interface (signatures K M X T) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive (hashAlice hash)) *
    Pi.mulSingle .bob (Gamma.ofPrimitive (hashBob hash))

noncomputable def boundedUrfMacProtocol :
    Protocol Interface (signatures K M X T) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive sign) *
    Pi.mulSingle .bob (Gamma.ofPrimitive verify)

/-- Serial UHF/URF/MAC protocol, with the hash layer acting first. -/
noncomputable def uhfUrfMacProtocol (Hf : EpsUniversalHash K M X) :
    Protocol Interface (signatures K M X T) :=
  boundedUrfMacProtocol * hashThenOracleProtocol Hf.hash

noncomputable def bottom :
    Protocol Interface (signatures K M X T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive blockIdealEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive blockRealEve)

noncomputable def simulatorProtocol :
    Protocol Interface (signatures K M X T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive simulator)

noncomputable def uhfUrfMacSimulators :
    Submonoid (Protocol Interface (signatures K M X T)) :=
  supportedOn ({.eve} : Set Interface) (fun _ => ⊤)

/-! ## The two layers, and the composite derived from them

The chain this file models is two construction steps sharing the intermediate
resource `boundedLongMacResource`:

```text
[short URF, key, InsecCh] --hashThenOracle--> [long URF, InsecCh]  ε₁
[long URF, InsecCh]       --sign/verify----->  AuthChan            ε₂
```

so the composite must be the *serial product* of the two protocols at the sum
of the two errors.  `uhfUrfMacProtocol` is already defined as exactly that
product, and the stated error is already exactly that sum — so the composite
is **derived** below rather than restated, and the remaining obligations are
the two layers alone.

This is the load-bearing check on the model: `securelyConstructs_trans_of_supported`
(CC composition, MauRen11 Definition 7's serial composability) only applies if
the two layers really do share the intermediate resource, the simulator class,
and the availability filter, and if the protocol labels multiply in the right
order.  They do, and nothing had to be adjusted to make them. -/

/-- **Layer 1 — the hash.**  An `ε`-almost-universal hash turns the short-input
URF into a long-input one; the cost is the chance that two of the at most
`q + 1` distinct queries collide under the hash key. -/
theorem uhf_hash_layer_securely_constructs
    (Hf : EpsUniversalHash K M X) (q : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (uhfUrfMacSimulators (K := K) (M := M) (X := X) (T := T))
      (hashThenOracleProtocol (T := T) Hf.hash)
      (bottom (K := K) (M := M) (X := X) (T := T))
      ((Nat.choose (q + 1) 2 : ℝ≥0∞) * (Hf.eps : ℝ≥0∞))
      (uhfMacAssumedResource (T := T) Hf q)
      (boundedLongMacResource (K := K) (M := M) (X := X) (T := T) q) := by
  sorry

/-- **Layer 2 — the MAC.**  A long-input URF used as a MAC over an insecure
channel constructs the authenticated channel; the cost is one guessed tag. -/
theorem urf_mac_layer_securely_constructs (q : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (uhfUrfMacSimulators (K := K) (M := M) (X := X) (T := T))
      (boundedUrfMacProtocol (K := K) (M := M) (X := X) (T := T))
      (bottom (K := K) (M := M) (X := X) (T := T))
      (1 / (Fintype.card T : ℝ≥0∞))
      (boundedLongMacResource (K := K) (M := M) (X := X) (T := T) q)
      (qAuthenticatedResource (K := K) (X := X) (T := T) q) := by
  sorry

/-- **UHF then URF constructs a bounded MAC/authenticated channel.**

Derived — not assumed — from the two layers by CC composition.  The admitted
simulator class is already the tuples supported at Eve, which is precisely the
side condition `securelyConstructs_trans_of_supported` needs, so the
composition goes through with `le_rfl`. -/
theorem uhf_urf_mac_securely_constructs
    (Hf : EpsUniversalHash K M X) (q : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (uhfUrfMacSimulators (K := K) (M := M) (X := X) (T := T))
      (uhfUrfMacProtocol (T := T) Hf)
      (bottom (K := K) (M := M) (X := X) (T := T))
      ((Nat.choose (q + 1) 2 : ℝ≥0∞) * (Hf.eps : ℝ≥0∞) +
        1 / (Fintype.card T : ℝ≥0∞))
      (uhfMacAssumedResource (T := T) Hf q)
      (qAuthenticatedResource (K := K) (X := X) (T := T) q) :=
  securelyConstructs_trans_of_supported le_rfl
    (uhf_hash_layer_securely_constructs (T := T) Hf q)
    (urf_mac_layer_securely_constructs (K := K) (M := M) (X := X) (T := T) q)

end Generic

section Polynomial

variable {F T : Type u}
variable [Fintype F] [DecidableEq F] [Nonempty F] [Field F]
variable [Fintype T] [DecidableEq T] [Nonempty T]

noncomputable def polynomialUhfMacAssumedResource (q ell : Nat) :
    Phi Interface (signatures F (BoundedMessage F ell) F T) :=
  ⟨sourceBoundary F (BoundedMessage F ell) F T,
    DependentRandomSystem.ofProb
      (sourceLaw (K := F) (M := BoundedMessage F ell)
        (X := F) (T := T) q)⟩

noncomputable def polynomialHashProtocol (ell : Nat) :
    Protocol Interface (signatures F (BoundedMessage F ell) F T) :=
  hashThenOracleProtocol (T := T)
    (polynomialHash (F := F) (ell := ell))

noncomputable def polynomialUhfUrfMacProtocol (ell : Nat) :
    Protocol Interface (signatures F (BoundedMessage F ell) F T) :=
  boundedUrfMacProtocol *
    polynomialHashProtocol (F := F) (T := T) ell

/-- **The polynomial-UHF/URF MAC constructs a bounded authenticated channel**
over any finite field, without a universality hypothesis. -/
theorem polynomial_uhf_urf_mac_securely_constructs (q ell : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (uhfUrfMacSimulators (K := F) (M := BoundedMessage F ell)
        (X := F) (T := T))
      (polynomialUhfUrfMacProtocol (F := F) (T := T) ell)
      (bottom (K := F) (M := BoundedMessage F ell) (X := F) (T := T))
      ((Nat.choose (q + 1) 2 : ℝ≥0∞) *
          ((ell : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) +
        1 / (Fintype.card T : ℝ≥0∞))
      (polynomialUhfMacAssumedResource (F := F) (T := T) q ell)
      (qAuthenticatedResource (K := F) (M := BoundedMessage F ell)
        (X := F) (T := T) q) := by
  sorry

end Polynomial

end RandomSystemsCC.Symmetric.UHFURFMAC
