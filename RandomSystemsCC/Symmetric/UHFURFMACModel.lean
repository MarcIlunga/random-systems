/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystems.HTechnique.HashThenPRF
import RandomSystemsCC.Symmetric.ChannelModel

/-!
# Staged typed model for UHF/URF MAC

One carrier contains three boundaries:

1. an insecure channel bundled with a uniform hash key and short URF;
2. the same channel bundled with the induced long oracle;
3. the bounded authenticated channel.

The file bundles the hash, signing, verification, simulator, and availability
converters.  Resource laws and final statements live in `UHFURFMAC`.
-/

namespace RandomSystemsCC.Symmetric.UHFURFMAC

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystems.HTechnique.HashThenPRF
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite

universe u

inductive SourceAliceIn (K M X T : Type u) : Type u
  | key
  | eval (point : X)
  | sendPayload (payload : M × T)
  deriving DecidableEq

inductive SourceAliceOut (K T : Type u) : Type u
  | key (value : K)
  | tag (value : T)
  | ack

inductive SourceBobIn (K M X T : Type u) : Type u
  | key
  | eval (point : X)
  | receivePayload
  deriving DecidableEq

inductive SourceBobOut (K M T : Type u) : Type u
  | key (value : K)
  | tag (value : T)
  | payload (value : Option (M × T))

inductive LongAliceIn (M T : Type u) : Type u
  | eval (message : M)
  | sendPayload (payload : M × T)
  deriving DecidableEq

inductive LongAliceOut (T : Type u) : Type u
  | tag (value : T)
  | ack

inductive LongBobIn (M T : Type u) : Type u
  | eval (message : M)
  | receivePayload
  deriving DecidableEq

inductive LongBobOut (M T : Type u) : Type u
  | tag (value : T)
  | payload (value : Option (M × T))

inductive EveRealIn (M T : Type u) : Type u
  | readPayload (index : Nat)
  | replacePayload (payload : M × T)
  deriving DecidableEq

inductive EveRealOut (M T : Type u) : Type u
  | payload (value : Option (M × T))
  | ack

inductive EveIdealIn (M T : Type u) : Type u
  | readTagged (index : Nat)
  | tryReplacement (payload : M × T)
  deriving DecidableEq

inductive EveIdealOut (M T : Type u) : Type u
  | tagged (value : Option (M × T))
  | ack

inductive Code
  | sourceAlice
  | sourceBob
  | realEve
  | longAlice
  | longBob
  | idealAlice
  | idealBob
  | idealEve
  | blockedEve
  deriving DecidableEq

abbrev signatures (K M X T : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .sourceAlice => SourceAliceIn K M X T
    | .sourceBob => SourceBobIn K M X T
    | .realEve => EveRealIn M T
    | .longAlice => LongAliceIn M T
    | .longBob => LongBobIn M T
    | .idealAlice => SenderIn M
    | .idealBob => ReceiverIn M
    | .idealEve => EveIdealIn M T
    | .blockedEve => BlockedIn M
  output
    | .sourceAlice => SourceAliceOut K T
    | .sourceBob => SourceBobOut K M T
    | .realEve => EveRealOut M T
    | .longAlice => LongAliceOut T
    | .longBob => LongBobOut M T
    | .idealAlice => Ack M
    | .idealBob => Option M
    | .idealEve => EveIdealOut M T
    | .blockedEve => BlockedOut M

instance (K M X T : Type u) : DecidableEq (signatures K M X T).Code := by
  change DecidableEq Code
  infer_instance

def sourceBoundary (K M X T : Type u) :
    Boundary (signatures K M X T) Interface
  | .alice => .sourceAlice
  | .bob => .sourceBob
  | .eve => .realEve

def longBoundary (K M X T : Type u) :
    Boundary (signatures K M X T) Interface
  | .alice => .longAlice
  | .bob => .longBob
  | .eve => .realEve

def idealBoundary (K M X T : Type u) :
    Boundary (signatures K M X T) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .idealEve

def availableBoundary (K M X T : Type u) :
    Boundary (signatures K M X T) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .blockedEve

section

variable {K M X T : Type u}
variable [DecidableEq M] [DecidableEq T] [Nonempty K]

def hashAliceStep (hash : K → M → X) (fallbackKey : K) :
    LongAliceIn M T → List (SourceAliceOut K T) →
      SourceAliceIn K M X T ⊕ LongAliceOut T
  | .eval _, [] => .inl .key
  | .eval message, [.key key] => .inl (.eval (hash key message))
  | .eval message, [_] => .inl (.eval (hash fallbackKey message))
  | .eval _, _ :: .tag value :: _ => .inr (.tag value)
  | .eval _, _ => .inr .ack
  | .sendPayload payload, [] => .inl (.sendPayload payload)
  | .sendPayload _, _ => .inr .ack

def hashBobStep (hash : K → M → X) (fallbackKey : K) :
    LongBobIn M T → List (SourceBobOut K M T) →
      SourceBobIn K M X T ⊕ LongBobOut M T
  | .eval _, [] => .inl .key
  | .eval message, [.key key] => .inl (.eval (hash key message))
  | .eval message, [_] => .inl (.eval (hash fallbackKey message))
  | .eval _, _ :: .tag value :: _ => .inr (.tag value)
  | .eval _, _ => .inr (.payload none)
  | .receivePayload, [] => .inl .receivePayload
  | .receivePayload, [.payload payload] => .inr (.payload payload)
  | .receivePayload, _ => .inr (.payload none)

def hashAliceCount : LongAliceIn M T → Nat
  | .eval _ => 2
  | .sendPayload _ => 1

def hashBobCount : LongBobIn M T → Nat
  | .eval _ => 2
  | .receivePayload => 1

noncomputable def hashAlice (hash : K → M → X) :
    Primitive Interface (signatures K M X T) .alice :=
  let fallbackKey : K := Classical.choice inferInstance
  Primitive.ofHistory .sourceAlice .longAlice
    (PFunConverter.ProtocolFn.ofStep
      (hashAliceStep hash fallbackKey)
      hashAliceCount)
    (PFunConverter.ProtocolFn.isDDC_ofStep
      (hashAliceStep hash fallbackKey)
      hashAliceCount
      (by
        intro request answers
        cases request <;> cases answers with
        | nil => simp [hashAliceStep, hashAliceCount]
        | cons answer tail =>
            cases tail with
            | nil =>
                cases answer <;> simp [hashAliceStep, hashAliceCount]
            | cons answer' tail' =>
                cases answer' <;> simp [hashAliceStep, hashAliceCount])
      ⟨2, by intro request; cases request <;> simp [hashAliceCount]⟩)

noncomputable def hashBob (hash : K → M → X) :
    Primitive Interface (signatures K M X T) .bob :=
  let fallbackKey : K := Classical.choice inferInstance
  Primitive.ofHistory .sourceBob .longBob
    (PFunConverter.ProtocolFn.ofStep
      (hashBobStep hash fallbackKey)
      hashBobCount)
    (PFunConverter.ProtocolFn.isDDC_ofStep
      (hashBobStep hash fallbackKey)
      hashBobCount
      (by
        intro request answers
        cases request <;> cases answers with
        | nil => simp [hashBobStep, hashBobCount]
        | cons answer tail =>
            cases tail with
            | nil =>
                cases answer <;> simp [hashBobStep, hashBobCount]
            | cons answer' tail' =>
                cases answer' <;> simp [hashBobStep, hashBobCount])
      ⟨2, by intro request; cases request <;> simp [hashBobCount]⟩)

def signStep (fallbackTag : T) :
    SenderIn M → List (LongAliceOut T) → LongAliceIn M T ⊕ Ack M
  | .send message, [] => .inl (.eval message)
  | .send message, [.tag tag] => .inl (.sendPayload (message, tag))
  | .send message, [.ack] => .inl (.sendPayload (message, fallbackTag))
  | .send _, _ => .inr .ack

def verifyStep (fallbackMessage : M) :
    ReceiverIn M → List (LongBobOut M T) → LongBobIn M T ⊕ Option M
  | .receive, [] => .inl .receivePayload
  | .receive, [.payload (some (message, _))] => .inl (.eval message)
  | .receive, [.payload none] => .inl (.eval fallbackMessage)
  | .receive, [.tag _] => .inl (.eval fallbackMessage)
  | .receive, payloadAnswer :: tagAnswer :: _ =>
      .inr <| match payloadAnswer, tagAnswer with
        | .payload (some (message, tag)), .tag expected =>
            if tag = expected then some message else none
        | _, _ => none

noncomputable def sign [Nonempty T] :
    Primitive Interface (signatures K M X T) .alice :=
  let fallbackTag : T := Classical.choice inferInstance
  Primitive.ofHistory .longAlice .idealAlice
    (PFunConverter.ProtocolFn.ofStep (signStep fallbackTag) (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep (signStep fallbackTag) (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [signStep]
        | cons answer tail =>
            cases tail with
            | nil => cases answer <;> simp [signStep]
            | cons answer' tail' => simp [signStep])
      ⟨2, by intro; rfl⟩)

noncomputable def verify [Nonempty M] :
    Primitive Interface (signatures K M X T) .bob :=
  let fallbackMessage : M := Classical.choice inferInstance
  Primitive.ofHistory .longBob .idealBob
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
                | payload value => cases value <;> simp [verifyStep]
                | tag value => simp [verifyStep]
            | cons answer' tail' => simp [verifyStep])
      ⟨2, by intro; rfl⟩)

def simulator :
    Primitive Interface (signatures K M X T) .eve :=
  Primitive.ofFunctions .idealEve .realEve
    (fun
      | .readPayload index => .readTagged index
      | .replacePayload payload => .tryReplacement payload)
    (fun
      | .tagged payload => .payload payload
      | .ack => .ack)

def blockRealEve :
    Primitive Interface (signatures K M X T) .eve :=
  Primitive.ofFunctions .realEve .blockedEve
    (fun | .query => .readPayload 0)
    (fun _ => .blocked)

def blockIdealEve :
    Primitive Interface (signatures K M X T) .eve :=
  Primitive.ofFunctions .idealEve .blockedEve
    (fun | .query => .readTagged 0)
    (fun _ => .blocked)

end

end RandomSystemsCC.Symmetric.UHFURFMAC
