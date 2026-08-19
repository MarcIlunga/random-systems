/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystemsCC.Symmetric.ChannelModel

/-!
# Typed model for the affine one-time MAC

This file fixes the staged signatures and bundles the signing, verification,
simulation, and availability converters.  The resources and final CC
construction statement live in `RandomSystemsCC.Symmetric.AffineOneTimeMAC`.
-/

namespace RandomSystemsCC.Symmetric.AffineOneTimeMAC

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite

universe u

/-- Alice obtains the affine key or submits a message/tag payload. -/
inductive AliceIn (F : Type u) : Type u
  | key
  | sendPayload (payload : F × F)
  deriving DecidableEq

/-- Alice receives either the affine key or an insecure-channel
acknowledgement. -/
inductive AliceOut (F : Type u) : Type u
  | key (value : F × F)
  | ack

/-- Bob obtains the affine key or retrieves the insecure-channel payload. -/
inductive BobIn (F : Type u) : Type u
  | key
  | receivePayload
  deriving DecidableEq

/-- Bob receives either the affine key or the current payload. -/
inductive BobOut (F : Type u) : Type u
  | key (value : F × F)
  | payload (value : Option (F × F))

/-- Eve can observe Alice's payload and make one replacement attempt. -/
inductive EveRealIn (F : Type u) : Type u
  | readPayload
  | replacePayload (payload : F × F)
  deriving DecidableEq

/-- Replies at the real Eve interface. -/
inductive EveRealOut (F : Type u) : Type u
  | payload (value : Option (F × F))
  | ack

/-- The simulator observes the ideal tagged original and submits the
candidate replacement to the ideal authenticated channel. -/
inductive EveIdealIn (F : Type u) : Type u
  | readTagged
  | tryReplacement (payload : F × F)
  deriving DecidableEq

/-- Replies at the ideal Eve interface. -/
inductive EveIdealOut (F : Type u) : Type u
  | tagged (value : Option (F × F))
  | ack

/-- Affine-MAC source, authenticated target, and availability codes. -/
inductive Code
  | realAlice
  | realBob
  | realEve
  | idealAlice
  | idealBob
  | idealEve
  | blockedEve
  deriving DecidableEq

/-- The affine one-time MAC signature universe over an abstract field. -/
abbrev signatures (F : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .realAlice => AliceIn F
    | .realBob => BobIn F
    | .realEve => EveRealIn F
    | .idealAlice => SenderIn F
    | .idealBob => ReceiverIn F
    | .idealEve => EveIdealIn F
    | .blockedEve => BlockedIn F
  output
    | .realAlice => AliceOut F
    | .realBob => BobOut F
    | .realEve => EveRealOut F
    | .idealAlice => Ack F
    | .idealBob => Option F
    | .idealEve => EveIdealOut F
    | .blockedEve => BlockedOut F

instance (F : Type u) : DecidableEq (signatures F).Code := by
  change DecidableEq Code
  infer_instance

/-- The insecure-channel-plus-key source boundary. -/
def realBoundary (F : Type u) : Boundary (signatures F) Interface
  | .alice => .realAlice
  | .bob => .realBob
  | .eve => .realEve

/-- The one-time authenticated-channel target boundary. -/
def idealBoundary (F : Type u) : Boundary (signatures F) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .idealEve

/-- The boundary after availability blocks Eve. -/
def availableBoundary (F : Type u) : Boundary (signatures F) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .blockedEve

section

variable {F : Type u} [Field F] [DecidableEq F]

/-- Signing reads the affine key and submits `(m, a*m+b)`. -/
def signStep : SenderIn F → List (AliceOut F) → AliceIn F ⊕ Ack F
  | .send _, [] => .inl .key
  | .send message, [.key (a, b)] =>
      .inl (.sendPayload (message, a * message + b))
  | .send message, [.ack] => .inl (.sendPayload (message, 0))
  | .send _, _ => .inr .ack

/-- Verification reads the affine key and payload, accepting exactly a valid
tag. -/
def verifyStep : ReceiverIn F → List (BobOut F) → BobIn F ⊕ Option F
  | .receive, [] => .inl .key
  | .receive, [_] => .inl .receivePayload
  | .receive, keyAnswer :: payloadAnswer :: _ =>
      .inr <| match keyAnswer, payloadAnswer with
        | .key (a, b), .payload (some (message, tag)) =>
            if tag = a * message + b then some message else none
        | _, _ => none

/-- Alice's genuine two-query affine signing primitive. -/
noncomputable def sign :
    Primitive Interface (signatures F) .alice :=
  Primitive.ofHistory .realAlice .idealAlice
    (PFunConverter.ProtocolFn.ofStep signStep (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep signStep (fun _ => 2)
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

/-- Bob's genuine two-query affine verification primitive. -/
noncomputable def verify :
    Primitive Interface (signatures F) .bob :=
  Primitive.ofHistory .realBob .idealBob
    (PFunConverter.ProtocolFn.ofStep verifyStep (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep verifyStep (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [verifyStep]
        | cons answer tail =>
            cases tail with
            | nil => simp [verifyStep]
            | cons answer' tail' => simp [verifyStep])
      ⟨2, by intro; rfl⟩)

/-- Eve's simulator translates observations and the single replacement
attempt to the ideal authenticated interface. -/
def simulator :
    Primitive Interface (signatures F) .eve :=
  Primitive.ofFunctions .idealEve .realEve
    (fun
      | .readPayload => .readTagged
      | .replacePayload payload => .tryReplacement payload)
    (fun
      | .tagged payload => .payload payload
      | .ack => .ack)

/-- Availability blocks the real Eve port. -/
def blockRealEve :
    Primitive Interface (signatures F) .eve :=
  Primitive.ofFunctions .realEve .blockedEve
    (fun | .query => .readPayload)
    (fun _ => .blocked)

/-- Availability blocks the ideal Eve port. -/
def blockIdealEve :
    Primitive Interface (signatures F) .eve :=
  Primitive.ofFunctions .idealEve .blockedEve
    (fun | .query => .readTagged)
    (fun _ => .blocked)

end

end RandomSystemsCC.Symmetric.AffineOneTimeMAC
