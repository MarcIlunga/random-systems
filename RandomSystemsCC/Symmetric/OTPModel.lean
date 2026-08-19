/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystemsCC.Symmetric.ChannelModel

/-!
# Typed model for the additive one-time pad

This is the formalization-only half of the OTP construction, following the
split used by `RandomSystemsCC.CBCModel`.  It fixes the staged signatures and
bundles the genuine two-query encryption/decryption converters with their DDC
certificates.  The real and ideal resources and the final CC statement live in
`RandomSystemsCC.Symmetric.OTP`.
-/

namespace RandomSystemsCC.Symmetric.OTP

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite

universe u

/-- Alice's assumed-resource operations: obtain the shared key or submit the
authenticated ciphertext. -/
inductive AliceIn (G : Type u)
  | key
  | sendCipher (ciphertext : G)
  deriving DecidableEq

/-- Alice receives either the shared key or the authenticated channel's
acknowledgement. -/
inductive AliceOut (G : Type u) : Type u
  | key (value : G)
  | ack

/-- Bob's assumed-resource operations: obtain the same key or receive the
authenticated ciphertext. -/
inductive BobIn (G : Type u) : Type u
  | key
  | receiveCipher
  deriving DecidableEq

/-- Bob receives either the shared key or the unique delivered ciphertext. -/
inductive BobOut (G : Type u) : Type u
  | key (value : G)
  | cipher (value : Option G)

/-- Eve reads the ciphertext carried by the authenticated channel. -/
inductive EveRealIn (G : Type u) : Type u
  | readCipher
  deriving DecidableEq

/-- The ideal Eve port supplies the message-independent view used by the
simulator. -/
inductive EveIdealIn (G : Type u) : Type u
  | sampleCipher
  deriving DecidableEq

/-- OTP source, secure-channel target, and availability-blocking codes. -/
inductive Code
  | realAlice
  | realBob
  | realEve
  | idealAlice
  | idealBob
  | idealEve
  | blockedEve
  deriving DecidableEq

/-- The OTP signature universe over an abstract message/key group. -/
abbrev signatures (G : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .realAlice => AliceIn G
    | .realBob => BobIn G
    | .realEve => EveRealIn G
    | .idealAlice => SenderIn G
    | .idealBob => ReceiverIn G
    | .idealEve => EveIdealIn G
    | .blockedEve => BlockedIn G
  output
    | .realAlice => AliceOut G
    | .realBob => BobOut G
    | .realEve => Option G
    | .idealAlice => Ack G
    | .idealBob => Option G
    | .idealEve => Option G
    | .blockedEve => BlockedOut G

instance (G : Type u) : DecidableEq (signatures G).Code := by
  change DecidableEq Code
  infer_instance

/-- The assumed authenticated-channel-plus-key boundary. -/
def realBoundary (G : Type u) : Boundary (signatures G) Interface
  | .alice => .realAlice
  | .bob => .realBob
  | .eve => .realEve

/-- The ideal secure-channel boundary. -/
def idealBoundary (G : Type u) : Boundary (signatures G) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .idealEve

/-- The boundary used by both worlds after availability blocks Eve. -/
def availableBoundary (G : Type u) : Boundary (signatures G) Interface
  | .alice => .idealAlice
  | .bob => .idealBob
  | .eve => .blockedEve

section

variable {G : Type u} [AddCommGroup G]

/-- Encryption performs two inner calls: read the key, then send the
ciphertext. -/
def encryptStep : SenderIn G → List (AliceOut G) → AliceIn G ⊕ Ack G
  | .send _, [] => .inl .key
  | .send message, [.key key] => .inl (.sendCipher (message + key))
  | .send message, [.ack] => .inl (.sendCipher message)
  | .send _, _ => .inr .ack

/-- Decryption performs two inner calls: read the key, then receive the
ciphertext. -/
def decryptStep : ReceiverIn G → List (BobOut G) → BobIn G ⊕ Option G
  | .receive, [] => .inl .key
  | .receive, [_] => .inl .receiveCipher
  | .receive, keyAnswer :: cipherAnswer :: _ =>
      .inr <| match keyAnswer, cipherAnswer with
        | .key key, .cipher (some ciphertext) => some (ciphertext - key)
        | _, _ => none

/-- Alice's genuine two-query OTP encryption primitive. -/
noncomputable def encrypt :
    Primitive Interface (signatures G) .alice :=
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
            | nil =>
                cases answer <;> simp [encryptStep]
            | cons answer' tail' => simp [encryptStep])
      ⟨2, by intro; rfl⟩)

/-- Bob's genuine two-query OTP decryption primitive. -/
noncomputable def decrypt :
    Primitive Interface (signatures G) .bob :=
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

/-- Eve's deterministic simulator routes the real ciphertext observation to
the ideal message-independent sample. -/
def simulator :
    Primitive Interface (signatures G) .eve :=
  Primitive.ofFunctions .idealEve .realEve
    (fun | .readCipher => .sampleCipher)
    id

/-- Availability blocks the real Eve port. -/
def blockRealEve :
    Primitive Interface (signatures G) .eve :=
  Primitive.ofFunctions .realEve .blockedEve
    (fun | .query => .readCipher)
    (fun _ => .blocked)

/-- Availability blocks the ideal Eve port. -/
def blockIdealEve :
    Primitive Interface (signatures G) .eve :=
  Primitive.ofFunctions .idealEve .blockedEve
    (fun | .query => .sampleCipher)
    (fun _ => .blocked)

end

end RandomSystemsCC.Symmetric.OTP
