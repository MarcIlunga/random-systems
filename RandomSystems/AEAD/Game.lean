/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.GameOf

namespace RandomSystems.AEAD

open RandomSystems.CR18

structure EncryptQuery (Nonce AD Plaintext : Type*) where
  nonce : Nonce
  associatedData : AD
  plaintext : Plaintext

structure DecryptQuery (Nonce AD Ciphertext Tag : Type*) where
  nonce : Nonce
  associatedData : AD
  ciphertext : Ciphertext
  tag : Tag

structure EncryptResponse (Ciphertext Tag : Type*) where
  ciphertext : Ciphertext
  tag : Tag

structure DecryptResponse (Plaintext : Type*) where
  verified : Bool
  plaintext : Plaintext

abbrev Query (Nonce AD Plaintext Ciphertext Tag : Type*) :=
  EncryptQuery Nonce AD Plaintext ⊕ DecryptQuery Nonce AD Ciphertext Tag

abbrev Response (Plaintext Ciphertext Tag : Type*) :=
  EncryptResponse Ciphertext Tag ⊕ DecryptResponse Plaintext

variable {Nonce AD Plaintext Ciphertext Tag : Type*}
  [DecidableEq Nonce] [DecidableEq AD] [DecidableEq Ciphertext] [DecidableEq Tag]

def encryptionNonce : Query Nonce AD Plaintext Ciphertext Tag ×
    Response Plaintext Ciphertext Tag → Option Nonce
  | (Sum.inl query, Sum.inl _) => some query.nonce
  | _ => none

def encryptionRecord : Query Nonce AD Plaintext Ciphertext Tag ×
    Response Plaintext Ciphertext Tag → Option (Nonce × AD × Ciphertext × Tag)
  | (Sum.inl query, Sum.inl response) =>
      some (query.nonce, query.associatedData, response.ciphertext, response.tag)
  | _ => none

def nonceRespecting (transcript : List
    (Query Nonce AD Plaintext Ciphertext Tag × Response Plaintext Ciphertext Tag)) : Bool :=
  decide (List.Nodup (transcript.filterMap encryptionNonce))

def forgeryAt (transcript : List
    (Query Nonce AD Plaintext Ciphertext Tag × Response Plaintext Ciphertext Tag)) : Bool :=
  match transcript.getLast? with
  | some (Sum.inr query, Sum.inr response) =>
      nonceRespecting transcript && response.verified &&
        !(transcript.dropLast.filterMap encryptionRecord).contains
          (query.nonce, query.associatedData, query.ciphertext, query.tag)
  | _ => false

def win (transcript : List
    (Query Nonce AD Plaintext Ciphertext Tag × Response Plaintext Ciphertext Tag)) : Bool :=
  transcript.inits.any forgeryAt

noncomputable def game
    (S : PFunPDS (Query Nonce AD Plaintext Ciphertext Tag)
      (Response Plaintext Ciphertext Tag)) :
    PFunPDS (Query Nonce AD Plaintext Ciphertext Tag)
      (Response Plaintext Ciphertext Tag × Bool) :=
  RandomSystems.CR18.gameOf S win

end RandomSystems.AEAD
