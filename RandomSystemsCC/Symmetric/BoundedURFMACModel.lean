/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystemsCC.Symmetric.ChannelModel

/-!
# Typed model for a bounded URF MAC

The source multiplexes an insecure payload channel with a uniformly sampled
function.  Its history enforces the signing budget and the single final
replacement attempt.  This file bundles the honest and simulator converters;
the resource laws and construction statement are in `BoundedURFMAC`.
-/

namespace RandomSystemsCC.Symmetric.BoundedURFMAC

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite

universe u

/-- Alice evaluates the sampled function or submits a signed payload. -/
inductive AliceIn (M T : Type u) : Type u
  | eval (message : M)
  | sendPayload (payload : M × T)
  deriving DecidableEq

/-- Alice receives a function value or channel acknowledgement. -/
inductive AliceOut (T : Type u) : Type u
  | tag (value : T)
  | ack

/-- Bob retrieves the candidate payload or evaluates its message. -/
inductive BobIn (M T : Type u) : Type u
  | receivePayload
  | eval (message : M)
  deriving DecidableEq

/-- Bob receives a payload or function value. -/
inductive BobOut (M T : Type u) : Type u
  | payload (value : Option (M × T))
  | tag (value : T)

/-- Eve observes any of the bounded signed payloads and makes one replacement
attempt. -/
inductive EveRealIn (M T : Type u) : Type u
  | readPayload (index : Nat)
  | replacePayload (payload : M × T)
  deriving DecidableEq

/-- Replies at the real Eve interface. -/
inductive EveRealOut (M T : Type u) : Type u
  | payload (value : Option (M × T))
  | ack

/-- The simulator reads the ideal tagged transcript and submits the single
candidate replacement. -/
inductive EveIdealIn (M T : Type u) : Type u
  | readTagged (index : Nat)
  | tryReplacement (payload : M × T)
  deriving DecidableEq

/-- Replies at the ideal Eve interface. -/
inductive EveIdealOut (M T : Type u) : Type u
  | tagged (value : Option (M × T))
  | ack

/-- Bounded-URF-MAC source, authenticated target, and blocked codes. -/
inductive Code
  | realAlice
  | realBob
  | realEve
  | idealAlice
  | idealBob
  | idealEve
  | blockedEve
  deriving DecidableEq

/-- Signatures for abstract message and tag spaces. -/
abbrev signatures (M T : Type u) :
    SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .realAlice => AliceIn M T
    | .realBob => BobIn M T
    | .realEve => EveRealIn M T
    | .idealAlice => SenderIn M
    | .idealBob => ReceiverIn M
    | .idealEve => EveIdealIn M T
    | .blockedEve => BlockedIn M
  output
    | .realAlice => AliceOut T
    | .realBob => BobOut M T
    | .realEve => EveRealOut M T
    | .idealAlice => Ack M
    | .idealBob => Option M
    | .idealEve => EveIdealOut M T
    | .blockedEve => BlockedOut M

instance (M T : Type u) : DecidableEq (signatures M T).Code := by
  change DecidableEq Code
  infer_instance

def realBoundary (M T : Type u) :
    Boundary (signatures M T) Interface
  | .alice => .realAlice
  | .bob => .realBob
  | .eve => .realEve

def idealBoundary (M T : Type u) :
    Boundary (signatures M T) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .idealEve

def availableBoundary (M T : Type u) :
    Boundary (signatures M T) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .blockedEve

section

variable {M T : Type u}
variable [DecidableEq M] [DecidableEq T]

/-- Signing evaluates the URF and submits the resulting payload. -/
def signStep (fallbackTag : T) :
    SenderIn M → List (AliceOut T) → AliceIn M T ⊕ Ack M
  | .send message, [] => .inl (.eval message)
  | .send message, [.tag tag] => .inl (.sendPayload (message, tag))
  | .send message, [.ack] => .inl (.sendPayload (message, fallbackTag))
  | .send _, _ => .inr .ack

/-- Verification retrieves the candidate, evaluates its message, and checks
the supplied tag. -/
def verifyStep (fallbackMessage : M) :
    ReceiverIn M → List (BobOut M T) → BobIn M T ⊕ Option M
  | .receive, [] => .inl .receivePayload
  | .receive, [.payload (some (message, _))] => .inl (.eval message)
  | .receive, [.payload none] => .inl (.eval fallbackMessage)
  | .receive, [.tag _] => .inl (.eval fallbackMessage)
  | .receive, payloadAnswer :: tagAnswer :: _ =>
      .inr <| match payloadAnswer, tagAnswer with
        | .payload (some (message, tag)), .tag expected =>
            if tag = expected then some message else none
        | _, _ => none

/-- Alice's genuine two-query URF signing primitive. -/
noncomputable def sign [Nonempty T] :
    Primitive Interface (signatures M T) .alice :=
  let fallbackTag : T := Classical.choice inferInstance
  Primitive.ofHistory .realAlice .idealAlice
    (PFunConverter.ProtocolFn.ofStep (signStep fallbackTag) (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep (signStep fallbackTag) (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [signStep]
        | cons answer tail =>
            cases tail with
            | nil =>
                cases answer <;> simp [signStep]
            | cons answer' tail' => simp [signStep])
      ⟨2, by intro; rfl⟩)

/-- Bob's genuine two-query URF verification primitive. -/
noncomputable def verify [Nonempty M] :
    Primitive Interface (signatures M T) .bob :=
  let fallbackMessage : M := Classical.choice inferInstance
  Primitive.ofHistory .realBob .idealBob
    (PFunConverter.ProtocolFn.ofStep (verifyStep fallbackMessage) (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep (verifyStep fallbackMessage) (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [verifyStep]
        | cons answer tail =>
            cases tail with
            | nil =>
                cases answer with
                | payload value =>
                    cases value <;> simp [verifyStep]
                | tag value => simp [verifyStep]
            | cons answer' tail' => simp [verifyStep])
      ⟨2, by intro; rfl⟩)

/-- Eve's transcript/replacement simulator. -/
def simulator :
    Primitive Interface (signatures M T) .eve :=
  Primitive.ofFunctions .idealEve .realEve
    (fun
      | .readPayload index => .readTagged index
      | .replacePayload payload => .tryReplacement payload)
    (fun
      | .tagged payload => .payload payload
      | .ack => .ack)

def blockRealEve :
    Primitive Interface (signatures M T) .eve :=
  Primitive.ofFunctions .realEve .blockedEve
    (fun | .query => .readPayload 0)
    (fun _ => .blocked)

def blockIdealEve :
    Primitive Interface (signatures M T) .eve :=
  Primitive.ofFunctions .idealEve .blockedEve
    (fun | .query => .readTagged 0)
    (fun _ => .blocked)

end

end RandomSystemsCC.Symmetric.BoundedURFMAC
