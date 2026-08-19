/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Frost.Group
import RandomSystemsCC.TypedFinite

/-!
# The concrete FROST model: interfaces and signatures

The typed signature universe of the FROST development.  One interface per
party (`Fin n`, matching LiuMau20 and the frozen CC.MPC contract); the
sub-channels of each stage are multiplexed inside that stage's query and
answer *sum types*, so the assumed `[NET, BC, RO, COIN]` bundle, the
intermediate key resource, and the final threshold-signature resource are
single monolithic resources with structured codes — no parallel
composition is used anywhere (`MPC_TSS_PLAN.md`, frozen contract).

Three codes:

* `.assumed` — party view of the DKG-stage bundle: private coins (the
  Komlo–Goldberg sharing polynomial and PoK nonce), an authenticated
  broadcast for Feldman commitment vectors with their proofs of
  knowledge, private authenticated share channels, the random oracle,
  and the signing-stage channels passed through untouched (stage 1 must
  construct the full stage-2 bundle).
* `.keys` — party view of the intermediate ideal: the **uniform-key**
  threshold-key resource (`getShare`/`getGroupKey`/`pkShare`) together
  with the signing-stage channels.  Uniform-key first, per the frozen
  design: the Pedersen/GJKR key bias is to appear as a machine-checked
  impossibility for this ideal before a bias-absorbing repair is
  introduced.
* `.tss` — party view of the final ideal, the **gated real signer**: a
  party approves `(sid, msg, quorum)`; the resource runs the genuine
  signing algebra internally for approving parties (their nonces are its
  own coins), accepts the remaining parties' contributions through the
  session channels, and releases the aggregate signature.  Its guarantee
  is the *gate*; validity is public algebra, so its game bound is the
  standard unforgeability statement — the single computational leaf.

Modeling boundaries, fixed here once:

* The random oracle has an abstract finite input space `RoIn`; the
  structured points the protocol hashes are injected by encoder
  parameters (`encBind`, `encChal`, `encPok`), and RFC 9591 domain
  separation becomes explicit injectivity/disjointness hypotheses where
  proofs need them.  The byte-level pipeline stays in
  `Applications.Frost.Rfc9591`.
* Party identifiers enter the algebra through a parameter
  `pid : Fin n → F` (the RFC's nonzero scalar identifiers); its
  injectivity and nonvanishing are hypotheses of the reconstruction
  lemmas, not baked into the types.
* Sessions are drawn from a finite `SId`; messages from a finite `Msg`.
  Finiteness is what the finite-support law layer (`Dist`) requires.
* No coordinator: RFC 9591's coordinator role is absorbed into the
  broadcast channel (any party can read posted commitments and shares).
* Identifiable abort (RFC 9591 §5.4) is out of scope.
* **A broadcast channel (and authenticated per-pair channels) are assumed**,
  bundled into `.assumed`; **constructing broadcast is out of scope**, at
  the same assumption level as RFC 9591 / Komlo–Goldberg / BCKMTZ22.  So
  LiuMau20's `Q³` regime is not needed and the security statement tolerates
  a dishonest majority (`frost_threshold_unforgeability`).
-/

namespace RandomSystemsCC.Frost

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource

/-! ## Stage queries and answers -/

/-- Party queries of the assumed `[NET, BC, RO, COIN]` bundle.  The first
six arms are the DKG-stage channels; the remaining arms are the
signing-stage channels the DKG protocol passes through. -/
inductive AssumedIn (F V SId RoIn : Type) (n τ : ℕ) where
  /-- Read my private DKG coins: sharing polynomial and PoK nonce. -/
  | dkgCoins
  /-- Broadcast my Feldman commitment vector with its Schnorr proof of
  knowledge `(R, μ)` (Komlo–Goldberg round 1). -/
  | bcPost (commitment : Fin τ → V) (pok : V × F)
  /-- Read the commitment vector broadcast by `dealer`. -/
  | bcRead (dealer : Fin n)
  /-- Send a private share to `recipient` (Komlo–Goldberg round 2). -/
  | shareSend (recipient : Fin n) (share : F)
  /-- Receive the private share sent to me by `dealer`. -/
  | shareRecv (dealer : Fin n)
  /-- Query the random oracle. -/
  | ro (input : RoIn)
  /-- Read my private signing nonces for session `sid`. -/
  | nonceCoins (sid : SId)
  /-- Post my round-one signing commitment pair `(D, E)` for `sid`. -/
  | sigCommitPost (sid : SId) (commitment : V × V)
  /-- Read `signer`'s round-one commitment pair for `sid`. -/
  | sigCommitRead (sid : SId) (signer : Fin n)
  /-- Post my round-two signature share for `sid`. -/
  | sigSharePost (sid : SId) (share : F)
  /-- Read `signer`'s round-two signature share for `sid`. -/
  | sigShareRead (sid : SId) (signer : Fin n)
  deriving DecidableEq

/-- Answers of the assumed bundle. -/
inductive AssumedOut (F V : Type) (τ : ℕ) where
  /-- My DKG coins. -/
  | dkgCoins (poly : Fin τ → F) (pokNonce : F)
  /-- A write was recorded. -/
  | ack
  /-- A broadcast read: `none` if the dealer has not posted. -/
  | bc (posted : Option ((Fin τ → V) × (V × F)))
  /-- A share read: `none` if the dealer has not sent to me. -/
  | share (received : Option F)
  /-- A random-oracle answer. -/
  | ro (answer : F)
  /-- My signing nonces for the requested session. -/
  | nonceCoins (hidingNonce bindingNonce : F)
  /-- A commitment read for a signing session. -/
  | sigCommit (posted : Option (V × V))
  /-- A signature-share read for a signing session. -/
  | sigShare (posted : Option F)
  deriving DecidableEq

/-- Party queries of the intermediate key resource (uniform-key ideal,
bundled with the signing-stage channels). -/
inductive KeysIn (F V SId RoIn : Type) (n : ℕ) where
  /-- Read my secret key share. -/
  | getShare
  /-- Read the group public key. -/
  | getGroupKey
  /-- Read `holder`'s public key share. -/
  | pkShare (holder : Fin n)
  /-- Query the random oracle. -/
  | ro (input : RoIn)
  /-- Read my private signing nonces for session `sid`. -/
  | nonceCoins (sid : SId)
  /-- Post my round-one signing commitment pair for `sid`. -/
  | sigCommitPost (sid : SId) (commitment : V × V)
  /-- Read `signer`'s round-one commitment pair for `sid`. -/
  | sigCommitRead (sid : SId) (signer : Fin n)
  /-- Post my round-two signature share for `sid`. -/
  | sigSharePost (sid : SId) (share : F)
  /-- Read `signer`'s round-two signature share for `sid`. -/
  | sigShareRead (sid : SId) (signer : Fin n)
  deriving DecidableEq

/-- Answers of the intermediate key resource. -/
inductive KeysOut (F V : Type) where
  /-- A scalar answer (key share). -/
  | scalar (value : F)
  /-- A group-element answer (group key, public key share). -/
  | point (value : V)
  /-- A write was recorded. -/
  | ack
  /-- A random-oracle answer. -/
  | ro (answer : F)
  /-- My signing nonces for the requested session. -/
  | nonceCoins (hidingNonce bindingNonce : F)
  /-- A commitment read for a signing session. -/
  | sigCommit (posted : Option (V × V))
  /-- A signature-share read for a signing session. -/
  | sigShare (posted : Option F)
  deriving DecidableEq

/-- Party queries of the final ideal: the gated real signer. -/
inductive TssIn (F V Msg SId : Type) (n : ℕ) where
  /-- Approve signing `message` in session `sid` with the given quorum;
  the resource signs on behalf of approving parties. -/
  | approve (sid : SId) (message : Msg) (quorum : Fin n → Bool)
  /-- Read the aggregate signature of a completed session. -/
  | readSig (sid : SId)
  /-- Read the group public key. -/
  | getGroupKey
  /-- Read `holder`'s public key share. -/
  | pkShare (holder : Fin n)
  /-- Contribute a round-one commitment pair to `sid` without approving
  (the non-approving parties' participation channel). -/
  | sigCommitPost (sid : SId) (commitment : V × V)
  /-- Read `signer`'s round-one commitment pair for `sid` (session
  transcripts are public, as in the real protocol). -/
  | sigCommitRead (sid : SId) (signer : Fin n)
  /-- Contribute a round-two signature share to `sid` without approving. -/
  | sigSharePost (sid : SId) (share : F)
  /-- Read `signer`'s round-two signature share for `sid`. -/
  | sigShareRead (sid : SId) (signer : Fin n)
  deriving DecidableEq

/-- Answers of the gated real signer. -/
inductive TssOut (F V : Type) where
  /-- A write was recorded. -/
  | ack
  /-- The aggregate signature `(R, z)`, or `none` if the session is not
  complete. -/
  | sig (result : Option (V × F))
  /-- A group-element answer. -/
  | point (value : V)
  /-- A commitment read. -/
  | sigCommit (posted : Option (V × V))
  /-- A signature-share read. -/
  | sigShare (posted : Option F)
  deriving DecidableEq

/-! ## The signature universe and stage boundaries -/

/-- The three stage codes. -/
inductive Code where
  | assumed
  | keys
  | tss
  deriving DecidableEq

/-- The FROST signature universe over scalar field `F`, group `V`,
message space `Msg`, session space `SId`, oracle inputs `RoIn`, `n`
parties, and quorum size `τ`. -/
abbrev signatures (F V Msg SId RoIn : Type) (n τ : ℕ) :
    SignatureUniverse where
  Code := Code
  input
    | .assumed => AssumedIn F V SId RoIn n τ
    | .keys => KeysIn F V SId RoIn n
    | .tss => TssIn F V Msg SId n
  output
    | .assumed => AssumedOut F V τ
    | .keys => KeysOut F V
    | .tss => TssOut F V

instance (F V Msg SId RoIn : Type) (n τ : ℕ) :
    DecidableEq (signatures F V Msg SId RoIn n τ).Code := by
  change DecidableEq Code
  infer_instance

variable (F V Msg SId RoIn : Type) (n τ : ℕ)

/-- Every party interface advertises the assumed bundle. -/
def assumedBoundary : Boundary (signatures F V Msg SId RoIn n τ) (Fin n) :=
  fun _ => .assumed

/-- Every party interface advertises the intermediate key resource. -/
def keysBoundary : Boundary (signatures F V Msg SId RoIn n τ) (Fin n) :=
  fun _ => .keys

/-- Every party interface advertises the gated real signer. -/
def tssBoundary : Boundary (signatures F V Msg SId RoIn n τ) (Fin n) :=
  fun _ => .tss

end RandomSystemsCC.Frost
