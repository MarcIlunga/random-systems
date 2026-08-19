/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystemsCC.Symmetric.ChannelModel

/-!
# Typed model for indexed OTP with a fresh-pad resource

The source combines an indexed authenticated channel with a shared
URF-style pad table.  Alice and Bob query the same table entry at a channel
index; distinct indices carry independent uniform pads under the source law.
Resource laws and the final CC statement live in
`RandomSystemsCC.Symmetric.FreshOTP`.
-/

namespace RandomSystemsCC.Symmetric.FreshOTP

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite

universe u

/-- Alice reads the shared pad at an index or submits the indexed ciphertext. -/
inductive AliceIn (X G : Type u) : Type u
  | pad (index : X)
  | sendCipher (index : X) (ciphertext : G)
  deriving DecidableEq

/-- Alice receives a shared pad or an authenticated-channel acknowledgement. -/
inductive AliceOut (G : Type u) : Type u
  | pad (value : G)
  | ack

/-- Bob reads the same indexed pad or retrieves the indexed ciphertext. -/
inductive BobIn (X : Type u) : Type u
  | pad (index : X)
  | receiveCipher (index : X)
  deriving DecidableEq

/-- Bob receives a shared pad or the indexed authenticated ciphertext. -/
inductive BobOut (G : Type u) : Type u
  | pad (value : G)
  | cipher (value : Option G)

/-- Eve reads the authenticated ciphertext at an index. -/
inductive EveRealIn (X : Type u) : Type u
  | readCipher (index : X)
  deriving DecidableEq

/-- Alice's external indexed secure-channel operation. -/
inductive IndexedSenderIn (X G : Type u) : Type u
  | send (index : X) (message : G)
  deriving DecidableEq

/-- Bob's external indexed secure-channel operation. -/
inductive IndexedReceiverIn (X : Type u) : Type u
  | receive (index : X)
  deriving DecidableEq

/-- Eve requests the ideal simulated ciphertext at an index. -/
inductive EveIdealIn (X : Type u) : Type u
  | sampleCipher (index : X)
  deriving DecidableEq

/-- Source, target, and availability-blocking signature codes. -/
inductive Code
  | realAlice
  | realBob
  | realEve
  | idealAlice
  | idealBob
  | idealEve
  | blockedEve
  deriving DecidableEq

/-- Signature universe for indexed fresh-pad OTP. -/
abbrev signatures (X G : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .realAlice => AliceIn X G
    | .realBob => BobIn X
    | .realEve => EveRealIn X
    | .idealAlice => IndexedSenderIn X G
    | .idealBob => IndexedReceiverIn X
    | .idealEve => EveIdealIn X
    | .blockedEve => BlockedIn G
  output
    | .realAlice => AliceOut G
    | .realBob => BobOut G
    | .realEve => Option G
    | .idealAlice => Ack G
    | .idealBob => Option G
    | .idealEve => Option G
    | .blockedEve => BlockedOut G

instance (X G : Type u) : DecidableEq (signatures X G).Code := by
  change DecidableEq Code
  infer_instance

/-- Authenticated indexed channel plus shared-pad source boundary. -/
def realBoundary (X G : Type u) : Boundary (signatures X G) Interface
  | .alice => .realAlice
  | .bob => .realBob
  | .eve => .realEve

/-- Indexed secure-channel target boundary. -/
def idealBoundary (X G : Type u) : Boundary (signatures X G) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .idealEve

/-- Common honest boundary after either Eve port is blocked. -/
def availableBoundary (X G : Type u) : Boundary (signatures X G) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .blockedEve

section

variable {X G : Type u}
variable [AddCommGroup G]

/-- Encryption reads the pad at the message index, then submits the indexed
ciphertext. -/
def encryptStep :
    IndexedSenderIn X G → List (AliceOut G) → AliceIn X G ⊕ Ack G
  | .send index _, [] => .inl (.pad index)
  | .send index message, [.pad key] =>
      .inl (.sendCipher index (message + key))
  | .send index message, [.ack] =>
      .inl (.sendCipher index message)
  | .send _ _, _ => .inr .ack

/-- Decryption reads the pad at the requested index, then retrieves and
decrypts the indexed ciphertext. -/
def decryptStep :
    IndexedReceiverIn X → List (BobOut G) → BobIn X ⊕ Option G
  | .receive index, [] => .inl (.pad index)
  | .receive index, [_] => .inl (.receiveCipher index)
  | .receive _, padAnswer :: cipherAnswer :: _ =>
      .inr <| match padAnswer, cipherAnswer with
        | .pad key, .cipher (some ciphertext) => some (ciphertext - key)
        | _, _ => none

/-- Alice's genuine two-query indexed OTP encryption primitive. -/
noncomputable def encrypt :
    Primitive Interface (signatures X G) .alice :=
  Primitive.ofHistory .realAlice .idealAlice
    (PFunConverter.ProtocolFn.ofStep encryptStep (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep encryptStep (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [encryptStep]
        | cons answer tail =>
            cases tail with
            | nil => cases answer <;> simp [encryptStep]
            | cons answer' tail' => simp [encryptStep])
      ⟨2, by intro; rfl⟩)

/-- Bob's genuine two-query indexed OTP decryption primitive. -/
noncomputable def decrypt :
    Primitive Interface (signatures X G) .bob :=
  Primitive.ofHistory .realBob .idealBob
    (PFunConverter.ProtocolFn.ofStep decryptStep (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep decryptStep (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [decryptStep]
        | cons answer tail =>
            cases tail with
            | nil => simp [decryptStep]
            | cons answer' tail' => simp [decryptStep])
      ⟨2, by intro; rfl⟩)

/-- Eve's simulator routes a real indexed ciphertext read to the corresponding
ideal simulated-ciphertext query. -/
def simulator :
    Primitive Interface (signatures X G) .eve :=
  Primitive.ofFunctions .idealEve .realEve
    (fun | .readCipher index => .sampleCipher index)
    id

/-- Availability blocks the real Eve port. -/
noncomputable def blockRealEve [Nonempty X] :
    Primitive Interface (signatures X G) .eve :=
  let defaultIndex : X := Classical.choice inferInstance
  Primitive.ofFunctions .realEve .blockedEve
    (fun | .query => .readCipher defaultIndex)
    (fun _ => .blocked)

/-- Availability blocks the ideal Eve port. -/
noncomputable def blockIdealEve [Nonempty X] :
    Primitive Interface (signatures X G) .eve :=
  let defaultIndex : X := Classical.choice inferInstance
  Primitive.ofFunctions .idealEve .blockedEve
    (fun | .query => .sampleCipher defaultIndex)
    (fun _ => .blocked)

end

end RandomSystemsCC.Symmetric.FreshOTP
