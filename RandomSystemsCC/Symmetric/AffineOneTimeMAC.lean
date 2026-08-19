/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.AffineOneTimeMACModel
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage

/-!
# The affine one-time MAC channel construction

The source is a one-message insecure channel bundled with a uniform affine
key `(a,b)`.  The target is a one-message authenticated channel.  This file
contains only the named objects and final statement required by `DESIGN.md`
§11.4; its construction proof remains deferred until statement gate G0.
-/

namespace RandomSystemsCC.Symmetric.AffineOneTimeMAC

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto ENNReal

universe u

section

variable {F : Type u}
variable [Fintype F] [DecidableEq F] [Field F]

/-! ## Objects -/

/-- Alice's first submitted real-world message/tag payload. -/
private def realOriginalPayload?
    (history : List (Query (signatures F) (realBoundary F))) :
    Option (F × F) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.alice, .sendPayload payload⟩ => some payload
        | _ => none) none

/-- Eve's first real-world replacement attempt. -/
private def realReplacement?
    (history : List (Query (signatures F) (realBoundary F))) :
    Option (F × F) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .replacePayload payload⟩ => some payload
        | _ => none) none

/-- The deterministic assumed resource at a fixed affine key. -/
def realDDS (key : F × F) :
    DependentDDS (signatures F) (realBoundary F) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .key⟩ => .key key
    | ⟨.alice, .sendPayload _⟩ => .ack
    | ⟨.bob, .key⟩ => .key key
    | ⟨.bob, .receivePayload⟩ =>
        .payload ((realReplacement? history).orElse fun _ =>
          realOriginalPayload? history)
    | ⟨.eve, .readPayload⟩ => .payload (realOriginalPayload? history)
    | ⟨.eve, .replacePayload _⟩ => .ack

/-- The normalized source law, sampling `(a,b)` uniformly. -/
noncomputable def realLaw :
    DependentPDS.Prob (signatures F) (realBoundary F) :=
  ⟨Dist.fTransform realDDS (Dist.uniform (F × F)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The named insecure-channel-plus-affine-key assumed resource. -/
noncomputable def affineMacAssumedResource :
    Phi Interface (signatures F) :=
  ⟨realBoundary F, DependentRandomSystem.ofProb realLaw⟩

/-- Alice's first message at the ideal authenticated channel. -/
private def idealMessage?
    (history : List (Query (signatures F) (idealBoundary F))) : Option F :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.alice, .send message⟩ => some message
        | _ => none) none

/-- Eve's first candidate replacement at the ideal authenticated channel. -/
private def idealReplacement?
    (history : List (Query (signatures F) (idealBoundary F))) :
    Option (F × F) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .tryReplacement payload⟩ => some payload
        | _ => none) none

/-- The deterministic ideal resource at a fixed simulated original tag.
Exact replay delivers Alice's message; every modified payload is rejected. -/
def idealDDS (simulatedTag : F) :
    DependentDDS (signatures F) (idealBoundary F) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ =>
        match idealMessage? history with
        | none => none
        | some message =>
            match idealReplacement? history with
            | none => some message
            | some payload =>
                if payload = (message, simulatedTag) then some message else none
    | ⟨.eve, .readTagged⟩ =>
        .tagged ((idealMessage? history).map fun message =>
          (message, simulatedTag))
    | ⟨.eve, .tryReplacement _⟩ => .ack

/-- The normalized ideal law, sampling the simulated original tag uniformly. -/
noncomputable def idealLaw :
    DependentPDS.Prob (signatures F) (idealBoundary F) :=
  ⟨Dist.fTransform idealDDS (Dist.uniform F),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The named one-message authenticated channel. -/
noncomputable def oneTimeAuthenticatedResource :
    Phi Interface (signatures F) :=
  ⟨idealBoundary F, DependentRandomSystem.ofProb idealLaw⟩

/-- Alice signs and Bob verifies; Eve remains unattached. -/
noncomputable def affineMacProtocol :
    Protocol Interface (signatures F) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive sign) *
    Pi.mulSingle .bob (Gamma.ofPrimitive verify)

/-- The availability filter blocks either Eve code. -/
noncomputable def bottom :
    Protocol Interface (signatures F) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive blockIdealEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive blockRealEve)

/-- The concrete Eve-side affine-MAC simulator tuple. -/
noncomputable def simulatorProtocol :
    Protocol Interface (signatures F) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive simulator)

/-- Exactly Eve-supported converter tuples are admitted as simulators. -/
noncomputable def affineMacSimulators :
    Submonoid (Protocol Interface (signatures F)) :=
  supportedOn ({.eve} : Set Interface) (fun _ => ⊤)

/-! ## Final construction statement -/

/-- **The affine one-time MAC constructs an authenticated channel** over every
finite field, with one fresh-forgery error `1 / |F|`. -/
theorem affine_one_time_mac_securely_constructs :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (affineMacSimulators (F := F)) (affineMacProtocol (F := F))
      (bottom (F := F)) (1 / (Fintype.card F : ℝ≥0∞))
      (affineMacAssumedResource (F := F))
      (oneTimeAuthenticatedResource (F := F)) := by
  sorry

end

end RandomSystemsCC.Symmetric.AffineOneTimeMAC
