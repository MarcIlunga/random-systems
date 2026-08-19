/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.BoundedURFMACModel
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage

/-!
# A bounded URF MAC constructs authentication

The source and target histories enforce at most `q` honest signing deliveries
and one replacement attempt.  The sampled function is a URF directly; this
exercise has no computational PRF layer.
-/

namespace RandomSystemsCC.Symmetric.BoundedURFMAC

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto ENNReal

universe u

section

variable {M T : Type u}
variable [Fintype M] [DecidableEq M] [Nonempty M]
variable [Fintype T] [DecidableEq T] [Nonempty T]

/-! ## Objects -/

/-- The first `q` payloads submitted by Alice. -/
private def realPayloads (q : Nat)
    (history : List (Query (signatures M T) (realBoundary M T))) :
    List (M × T) :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .sendPayload payload⟩ => some payload
    | _ => none).take q

/-- Eve's first candidate replacement. -/
private def realReplacement?
    (history : List (Query (signatures M T) (realBoundary M T))) :
    Option (M × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .replacePayload payload⟩ => some payload
        | _ => none) none

/-- The bounded insecure-channel-plus-URF source at a fixed function. -/
def realDDS (q : Nat) (oracle : M → T) :
    DependentDDS (signatures M T) (realBoundary M T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .eval message⟩ => .tag (oracle message)
    | ⟨.alice, .sendPayload _⟩ => .ack
    | ⟨.bob, .receivePayload⟩ =>
        .payload ((realReplacement? history).orElse fun _ =>
          (realPayloads q history).getLast?)
    | ⟨.bob, .eval message⟩ => .tag (oracle message)
    | ⟨.eve, .readPayload index⟩ =>
        .payload ((realPayloads q history)[index]?)
    | ⟨.eve, .replacePayload _⟩ => .ack

/-- The normalized source law, sampling one uniform function `M → T`. -/
noncomputable def realLaw (q : Nat) :
    DependentPDS.Prob (signatures M T) (realBoundary M T) :=
  ⟨Dist.fTransform (realDDS q) (Dist.uniform (M → T)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The named `q`-signing insecure-channel-plus-URF source. -/
noncomputable def boundedUrfMacAssumedResource (q : Nat) :
    Phi Interface (signatures M T) :=
  ⟨realBoundary M T, DependentRandomSystem.ofProb (realLaw q)⟩

/-- The first `q` messages submitted to the ideal authenticated channel. -/
private def idealMessages (q : Nat)
    (history : List (Query (signatures M T) (idealBoundary M T))) :
    List M :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .send message⟩ => some message
    | _ => none).take q

/-- Eve's first ideal candidate replacement. -/
private def idealReplacement?
    (history : List (Query (signatures M T) (idealBoundary M T))) :
    Option (M × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .tryReplacement payload⟩ => some payload
        | _ => none) none

/-- The bounded ideal authenticated channel at a fixed simulator URF.
Replays of an observed payload are delivered; fresh payloads are rejected. -/
def idealDDS (q : Nat) (simulatorOracle : M → T) :
    DependentDDS (signatures M T) (idealBoundary M T) :=
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

/-- The normalized target law, sampling the simulator transcript URF. -/
noncomputable def idealLaw (q : Nat) :
    DependentPDS.Prob (signatures M T) (idealBoundary M T) :=
  ⟨Dist.fTransform (idealDDS q) (Dist.uniform (M → T)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The named `q`-delivery authenticated target. -/
noncomputable def qAuthenticatedResource (q : Nat) :
    Phi Interface (signatures M T) :=
  ⟨idealBoundary M T, DependentRandomSystem.ofProb (idealLaw q)⟩

/-- Alice signs and Bob verifies against the same bundled URF. -/
noncomputable def boundedUrfMacProtocol :
    Protocol Interface (signatures M T) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive sign) *
    Pi.mulSingle .bob (Gamma.ofPrimitive verify)

/-- Availability blocks both Eve codes. -/
noncomputable def bottom :
    Protocol Interface (signatures M T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive blockIdealEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive blockRealEve)

noncomputable def simulatorProtocol :
    Protocol Interface (signatures M T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive simulator)

noncomputable def boundedUrfMacSimulators :
    Submonoid (Protocol Interface (signatures M T)) :=
  supportedOn ({.eve} : Set Interface) (fun _ => ⊤)

/-! ## Final construction statement -/

/-- **A bounded URF MAC constructs a bounded authenticated channel.**  The
resource enforces `q` honest signing deliveries and one fresh attempt; the
error is one inverse tag-space cardinality. -/
theorem bounded_urf_mac_securely_constructs (q : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (boundedUrfMacSimulators (M := M) (T := T))
      (boundedUrfMacProtocol (M := M) (T := T))
      (bottom (M := M) (T := T))
      (1 / (Fintype.card T : ℝ≥0∞))
      (boundedUrfMacAssumedResource (M := M) (T := T) q)
      (qAuthenticatedResource (M := M) (T := T) q) := by
  sorry

end

end RandomSystemsCC.Symmetric.BoundedURFMAC
