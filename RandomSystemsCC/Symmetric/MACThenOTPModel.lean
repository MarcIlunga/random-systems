/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystemsCC.Symmetric.ChannelModel

/-!
# Shared staged model for MAC followed by OTP

The carrier has an insecure-channel source, an authenticated-channel
intermediate boundary that preserves the OTP-pad capability, and a secure
target.  The pad capability is an **index-addressed table**: `.otpKey index`
reads one named entry (`none` past the table), the channel delivers every
ciphertext **with its position**, and `.nextIndex` names the slot the next
submission will occupy.  Sender and receiver therefore address the same pad
through the position of the ciphertext in flight — there is no per-interface
call counting anywhere in the model.  MAC and OTP converters are bundled
here; resource laws and final composition statements live in `MACThenOTP`.
-/

namespace RandomSystemsCC.Symmetric.MACThenOTP

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite

universe u

inductive SourceAliceIn (S G T : Type u) : Type u
  | macKey
  | nextIndex
  | otpKey (index : Nat)
  | sendPayload (payload : G × T)
  deriving DecidableEq

inductive SourceAliceOut (S G : Type u) : Type u
  | macKey (value : S)
  | index (value : Nat)
  | otpKey (value : Option G)
  | ack

inductive SourceBobIn (S G T : Type u) : Type u
  | macKey
  | otpKey (index : Nat)
  | receivePayload
  deriving DecidableEq

inductive SourceBobOut (S G T : Type u) : Type u
  | macKey (value : S)
  | otpKey (value : Option G)
  | payload (value : Option (Nat × G × T))

inductive AuthAliceIn (G : Type u) : Type u
  | nextIndex
  | otpKey (index : Nat)
  | sendCipher (ciphertext : G)
  deriving DecidableEq

inductive AuthAliceOut (G : Type u) : Type u
  | index (value : Nat)
  | otpKey (value : Option G)
  | ack

inductive AuthBobIn (G : Type u) : Type u
  | otpKey (index : Nat)
  | receiveCipher
  deriving DecidableEq

inductive AuthBobOut (G : Type u) : Type u
  | otpKey (value : Option G)
  | ciphertext (value : Option (Nat × G))

inductive EveRealIn (G T : Type u) : Type u
  | readPayload (index : Nat)
  | replacePayload (payload : G × T)
  deriving DecidableEq

inductive EveRealOut (G T : Type u) : Type u
  | payload (value : Option (G × T))
  | ack

inductive EveAuthIn (G T : Type u) : Type u
  | readTagged (index : Nat)
  | tryReplacement (payload : G × T)
  deriving DecidableEq

inductive EveAuthOut (G T : Type u) : Type u
  | tagged (value : Option (G × T))
  | ack

inductive EveSecureIn (G T : Type u) : Type u
  | readSimulated (index : Nat)
  | tryReplacement (payload : G × T)
  deriving DecidableEq

inductive EveSecureOut (G T : Type u) : Type u
  | simulated (value : Option (G × T))
  | ack

inductive Code
  | sourceAlice
  | sourceBob
  | realEve
  | authAlice
  | authBob
  | authEve
  | secureAlice
  | secureBob
  | secureEve
  | blockedEve
  deriving DecidableEq

abbrev signatures (S G T : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .sourceAlice => SourceAliceIn S G T
    | .sourceBob => SourceBobIn S G T
    | .realEve => EveRealIn G T
    | .authAlice => AuthAliceIn G
    | .authBob => AuthBobIn G
    | .authEve => EveAuthIn G T
    | .secureAlice => SenderIn G
    | .secureBob => ReceiverIn G
    | .secureEve => EveSecureIn G T
    | .blockedEve => BlockedIn G
  output
    | .sourceAlice => SourceAliceOut S G
    | .sourceBob => SourceBobOut S G T
    | .realEve => EveRealOut G T
    | .authAlice => AuthAliceOut G
    | .authBob => AuthBobOut G
    | .authEve => EveAuthOut G T
    | .secureAlice => Ack G
    | .secureBob => Option G
    | .secureEve => EveSecureOut G T
    | .blockedEve => BlockedOut G

instance (S G T : Type u) : DecidableEq (signatures S G T).Code := by
  change DecidableEq Code
  infer_instance

def sourceBoundary (S G T : Type u) :
    Boundary (signatures S G T) Interface
  | .alice => .sourceAlice
  | .bob => .sourceBob
  | .eve => .realEve

def authBoundary (S G T : Type u) :
    Boundary (signatures S G T) Interface
  | .alice => .authAlice
  | .bob => .authBob
  | .eve => .authEve

def secureBoundary (S G T : Type u) :
    Boundary (signatures S G T) Interface
  | .alice => .secureAlice
  | .bob => .secureBob
  | .eve => .secureEve

def availableBoundary (S G T : Type u) :
    Boundary (signatures S G T) Interface
  | .alice => .secureAlice
  | .bob => .secureBob
  | .eve => .blockedEve

section

variable {S G T : Type u}
variable [DecidableEq T] [Nonempty S] [Nonempty G] [AddCommGroup G]

def macAliceStep (tag : S → G → T) (fallbackSecret : S) :
    AuthAliceIn G → List (SourceAliceOut S G) →
      SourceAliceIn S G T ⊕ AuthAliceOut G
  | .nextIndex, [] => .inl .nextIndex
  | .nextIndex, [.index position] => .inr (.index position)
  | .nextIndex, _ => .inr (.index 0)
  | .otpKey index, [] => .inl (.otpKey index)
  | .otpKey _, [.otpKey pad] => .inr (.otpKey pad)
  | .otpKey _, _ => .inr (.otpKey none)
  | .sendCipher _, [] => .inl .macKey
  | .sendCipher ciphertext, [.macKey secret] =>
      .inl (.sendPayload (ciphertext, tag secret ciphertext))
  | .sendCipher ciphertext, [_] =>
      .inl (.sendPayload (ciphertext, tag fallbackSecret ciphertext))
  | .sendCipher _, _ => .inr .ack

def macBobStep (tag : S → G → T) :
    AuthBobIn G → List (SourceBobOut S G T) →
      SourceBobIn S G T ⊕ AuthBobOut G
  | .otpKey index, [] => .inl (.otpKey index)
  | .otpKey _, [.otpKey pad] => .inr (.otpKey pad)
  | .otpKey _, _ => .inr (.otpKey none)
  | .receiveCipher, [] => .inl .receivePayload
  | .receiveCipher, [_] => .inl .macKey
  | .receiveCipher, payloadAnswer :: secretAnswer :: _ =>
      .inr <| match payloadAnswer, secretAnswer with
        | .payload (some (position, ciphertext, supplied)), .macKey secret =>
            if supplied = tag secret ciphertext
            then .ciphertext (some (position, ciphertext))
            else .ciphertext none
        | _, _ => .ciphertext none

def macAliceCount : AuthAliceIn G → Nat
  | .nextIndex => 1
  | .otpKey _ => 1
  | .sendCipher _ => 2

def macBobCount : AuthBobIn G → Nat
  | .otpKey _ => 1
  | .receiveCipher => 2

noncomputable def macAlice (tag : S → G → T) :
    Primitive Interface (signatures S G T) .alice :=
  let fallbackSecret : S := Classical.choice inferInstance
  Primitive.ofHistory .sourceAlice .authAlice
    (PFunConverter.ProtocolFn.ofStep
      (macAliceStep tag fallbackSecret) macAliceCount)
    (PFunConverter.ProtocolFn.isDDC_ofStep
      (macAliceStep tag fallbackSecret) macAliceCount
      (by
        intro request answers
        cases request <;> cases answers with
        | nil => simp [macAliceStep, macAliceCount]
        | cons answer tail =>
            cases tail with
            | nil => cases answer <;> simp [macAliceStep, macAliceCount]
            | cons answer' tail' =>
                simp [macAliceStep, macAliceCount])
      ⟨2, by intro request; cases request <;> simp [macAliceCount]⟩)

noncomputable def macBob (tag : S → G → T) :
    Primitive Interface (signatures S G T) .bob :=
  Primitive.ofHistory .sourceBob .authBob
    (PFunConverter.ProtocolFn.ofStep
      (macBobStep tag) macBobCount)
    (PFunConverter.ProtocolFn.isDDC_ofStep
      (macBobStep tag) macBobCount
      (by
        intro request answers
        cases request <;> cases answers with
        | nil => simp [macBobStep, macBobCount]
        | cons answer tail =>
            cases tail with
            | nil => cases answer <;> simp [macBobStep, macBobCount]
            | cons answer' tail' =>
                simp [macBobStep, macBobCount])
      ⟨2, by intro request; cases request <;> simp [macBobCount]⟩)

/-- Encryption asks the channel which slot its submission will occupy, reads
the pad **at that index**, and submits the padded ciphertext.  The
unpadded fallbacks are unreachable under the honest resources: they answer
a slot at or past the channel capacity, whose submission the channel
drops. -/
def encryptStep :
    SenderIn G → List (AuthAliceOut G) → AuthAliceIn G ⊕ Ack G
  | .send _, [] => .inl .nextIndex
  | .send _, [.index position] => .inl (.otpKey position)
  | .send _, [_] => .inl (.otpKey 0)
  | .send message, [_, .otpKey (some pad)] =>
      .inl (.sendCipher (message + pad))
  | .send message, [_, _] => .inl (.sendCipher message)
  | .send _, _ => .inr .ack

/-- Decryption receives the ciphertext **together with its position**, then
reads the pad at exactly that index — the pad address travels with the
ciphertext, so sender and receiver cannot disagree about it. -/
def decryptStep :
    ReceiverIn G → List (AuthBobOut G) → AuthBobIn G ⊕ Option G
  | .receive, [] => .inl .receiveCipher
  | .receive, [.ciphertext (some (position, _))] => .inl (.otpKey position)
  | .receive, [_] => .inl (.otpKey 0)
  | .receive, cipherAnswer :: padAnswer :: _ =>
      .inr <| match cipherAnswer, padAnswer with
        | .ciphertext (some (_, ciphertext)), .otpKey (some pad) =>
            some (ciphertext - pad)
        | _, _ => none

noncomputable def encrypt :
    Primitive Interface (signatures S G T) .alice :=
  Primitive.ofHistory .authAlice .secureAlice
    (PFunConverter.ProtocolFn.ofStep encryptStep (fun _ => 3))
    (PFunConverter.ProtocolFn.isDDC_ofStep encryptStep (fun _ => 3)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [encryptStep]
        | cons answer tail =>
            cases tail with
            | nil => cases answer <;> simp [encryptStep]
            | cons answer' tail' =>
                cases tail' with
                | nil =>
                    cases answer' with
                    | otpKey value => cases value <;> simp [encryptStep]
                    | index value => simp [encryptStep]
                    | ack => simp [encryptStep]
                | cons answer'' tail'' => simp [encryptStep])
      ⟨3, by intro; rfl⟩)

noncomputable def decrypt :
    Primitive Interface (signatures S G T) .bob :=
  Primitive.ofHistory .authBob .secureBob
    (PFunConverter.ProtocolFn.ofStep decryptStep (fun _ => 2))
    (PFunConverter.ProtocolFn.isDDC_ofStep decryptStep (fun _ => 2)
      (by
        intro request answers
        cases request
        cases answers with
        | nil => simp [decryptStep]
        | cons answer tail =>
            cases tail with
            | nil =>
                cases answer with
                | otpKey value => simp [decryptStep]
                | ciphertext value =>
                    cases value with
                    | none => simp [decryptStep]
                    | some indexed =>
                        cases indexed
                        simp [decryptStep]
            | cons answer' tail' => simp [decryptStep])
      ⟨2, by intro; rfl⟩)

def macSimulator :
    Primitive Interface (signatures S G T) .eve :=
  Primitive.ofFunctions .authEve .realEve
    (fun
      | .readPayload index => .readTagged index
      | .replacePayload payload => .tryReplacement payload)
    (fun
      | .tagged payload => .payload payload
      | .ack => .ack)

def otpSimulator :
    Primitive Interface (signatures S G T) .eve :=
  Primitive.ofFunctions .secureEve .authEve
    (fun
      | .readTagged index => .readSimulated index
      | .tryReplacement payload => .tryReplacement payload)
    (fun
      | .simulated payload => .tagged payload
      | .ack => .ack)

def blockRealEve :
    Primitive Interface (signatures S G T) .eve :=
  Primitive.ofFunctions .realEve .blockedEve
    (fun | .query => .readPayload 0)
    (fun _ => .blocked)

def blockAuthEve :
    Primitive Interface (signatures S G T) .eve :=
  Primitive.ofFunctions .authEve .blockedEve
    (fun | .query => .readTagged 0)
    (fun _ => .blocked)

def blockSecureEve :
    Primitive Interface (signatures S G T) .eve :=
  Primitive.ofFunctions .secureEve .blockedEve
    (fun | .query => .readSimulated 0)
    (fun _ => .blocked)

end

end RandomSystemsCC.Symmetric.MACThenOTP
