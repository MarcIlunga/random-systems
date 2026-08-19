/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.MACThenOTPModel
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage
import RandomSystemsCC.TypedConstruct

/-!
# Authentication followed by OTP constructs a secure channel

The source samples the MAC secret and `q` independent OTP pads.  The
intermediate authenticated resource preserves those pads; the secure target
simulates independent ciphertext/tag views.  The pads form an
index-addressed table and every delivered ciphertext carries its position,
so sender and receiver always address the pad of the ciphertext in flight.
Generic composition and the assumption-free affine and polynomial/URF
endpoints are stated below.
-/

namespace RandomSystemsCC.Symmetric.MACThenOTP

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto BigOperators ENNReal

universe u

section Generic

variable {S G T : Type u}
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype G] [DecidableEq G] [Nonempty G] [AddCommGroup G]
variable [Fintype T] [DecidableEq T] [Nonempty T]

/-! ## Shared resource state

Every positional quantity below is derived from one source of truth — the
list of submitted payloads/ciphertexts/messages.  The pad table itself is
read purely by index (`(List.ofFn pads)[index]?`, `none` past the table);
its answers never consult the history. -/

private def sourcePayloads (q : Nat)
    (history : List (Query (signatures S G T) (sourceBoundary S G T))) :
    List (G × T) :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .sendPayload payload⟩ => some payload
    | _ => none).take q

private def sourceReplacement?
    (history : List (Query (signatures S G T) (sourceBoundary S G T))) :
    Option (G × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .replacePayload payload⟩ => some payload
        | _ => none) none

/-- Insecure channel with MAC secret and an index-addressed OTP-pad table.
`.nextIndex` names the slot the next payload will occupy, and
`.receivePayload` delivers the payload in flight together with its
position. -/
def sourceDDS (q : Nat) (sample : S × (Fin q → G)) :
    DependentDDS (signatures S G T) (sourceBoundary S G T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .macKey⟩ => .macKey sample.1
    | ⟨.alice, .nextIndex⟩ => .index (sourcePayloads q history).length
    | ⟨.alice, .otpKey index⟩ => .otpKey (List.ofFn sample.2)[index]?
    | ⟨.alice, .sendPayload _⟩ => .ack
    | ⟨.bob, .macKey⟩ => .macKey sample.1
    | ⟨.bob, .otpKey index⟩ => .otpKey (List.ofFn sample.2)[index]?
    | ⟨.bob, .receivePayload⟩ =>
        let payloads := sourcePayloads q history
        .payload <| match sourceReplacement? history with
          | some payload => some (payloads.length - 1, payload)
          | none =>
              payloads.getLast?.map fun payload =>
                (payloads.length - 1, payload)
    | ⟨.eve, .readPayload index⟩ =>
        .payload ((sourcePayloads q history)[index]?)
    | ⟨.eve, .replacePayload _⟩ => .ack

noncomputable def sourceLaw
    (macSecretLaw : Dist.ProbDist S) (q : Nat) :
    DependentPDS.Prob (signatures S G T) (sourceBoundary S G T) :=
  let joint := Dist.prodProbDist macSecretLaw
    (⟨Dist.uniform (Fin q → G), Dist.uniform_isProbDist⟩ :
      Dist.ProbDist (Fin q → G))
  ⟨Dist.fTransform (sourceDDS q) joint.val,
    Dist.fTransform_isProbDist _ joint.property⟩

/-- Named insecure-channel-with-keys source. -/
noncomputable def insecureWithKeysResource
    (macSecretLaw : Dist.ProbDist S) (q : Nat) :
    Phi Interface (signatures S G T) :=
  ⟨sourceBoundary S G T,
    DependentRandomSystem.ofProb (sourceLaw macSecretLaw q)⟩

private def authCiphertexts (q : Nat)
    (history : List (Query (signatures S G T) (authBoundary S G T))) :
    List G :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .sendCipher ciphertext⟩ => some ciphertext
    | _ => none).take q

private def authReplacement?
    (history : List (Query (signatures S G T) (authBoundary S G T))) :
    Option (G × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .tryReplacement payload⟩ => some payload
        | _ => none) none

/-- Authenticated ciphertext channel preserving the index-addressed OTP-pad
table.  Every delivered ciphertext carries its position, so the pad a
receiver reads is the pad of the ciphertext in flight, not a function of
its own call pattern.  The sampled function supplies only Eve's simulated
MAC transcript. -/
def authDDS (q : Nat)
    (sample : (Fin q → G) × (G → T)) :
    DependentDDS (signatures S G T) (authBoundary S G T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .nextIndex⟩ => .index (authCiphertexts q history).length
    | ⟨.alice, .otpKey index⟩ => .otpKey (List.ofFn sample.1)[index]?
    | ⟨.alice, .sendCipher _⟩ => .ack
    | ⟨.bob, .otpKey index⟩ => .otpKey (List.ofFn sample.1)[index]?
    | ⟨.bob, .receiveCipher⟩ =>
        let ciphertexts := authCiphertexts q history
        .ciphertext <|
          match authReplacement? history, ciphertexts.getLast? with
          | none, latest =>
              latest.map fun ciphertext =>
                (ciphertexts.length - 1, ciphertext)
          | some payload, some latest =>
              if payload = (latest, sample.2 latest)
              then some (ciphertexts.length - 1, latest)
              else none
          | some _, none => none
    | ⟨.eve, .readTagged index⟩ =>
        .tagged ((authCiphertexts q history)[index]? |>.map fun ciphertext =>
          (ciphertext, sample.2 ciphertext))
    | ⟨.eve, .tryReplacement _⟩ => .ack

noncomputable def authLaw (q : Nat) :
    DependentPDS.Prob (signatures S G T) (authBoundary S G T) :=
  ⟨Dist.fTransform (authDDS (S := S) q)
      (Dist.uniform ((Fin q → G) × (G → T))),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named authenticated channel with the OTP-pad capability preserved. -/
noncomputable def authenticatedWithOtpKeyResource (q : Nat) :
    Phi Interface (signatures S G T) :=
  ⟨authBoundary S G T, DependentRandomSystem.ofProb (authLaw q)⟩

private def secureMessages (q : Nat)
    (history : List (Query (signatures S G T) (secureBoundary S G T))) :
    List G :=
  (history.filterMap fun query =>
    match query with
    | ⟨.alice, .send message⟩ => some message
    | _ => none).take q

private def secureReplacement?
    (history : List (Query (signatures S G T) (secureBoundary S G T))) :
    Option (G × T) :=
  history.foldl (fun current query =>
    match current with
    | some _ => current
    | none =>
        match query with
        | ⟨.eve, .tryReplacement payload⟩ => some payload
        | _ => none) none

/-- Secure channel with an independent simulated ciphertext/tag transcript,
indexed by message position. -/
def secureDDS (q : Nat)
    (sample : (Fin q → G) × (G → T)) :
    DependentDDS (signatures S G T) (secureBoundary S G T) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ =>
        let messages := secureMessages q history
        match secureReplacement? history, messages.getLast? with
        | none, latest => latest
        | some payload, some latest =>
            match (List.ofFn sample.1)[messages.length - 1]? with
            | some ciphertext =>
                if payload = (ciphertext, sample.2 ciphertext)
                then some latest
                else none
            | none => none
        | some _, none => none
    | ⟨.eve, .readSimulated index⟩ =>
        .simulated ((secureMessages q history)[index]?.bind fun _ =>
          (List.ofFn sample.1)[index]?.map fun ciphertext =>
            (ciphertext, sample.2 ciphertext))
    | ⟨.eve, .tryReplacement _⟩ => .ack

noncomputable def secureLaw (q : Nat) :
    DependentPDS.Prob (signatures S G T) (secureBoundary S G T) :=
  ⟨Dist.fTransform (secureDDS (S := S) q)
      (Dist.uniform ((Fin q → G) × (G → T))),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named `q`-message secure-channel target. -/
noncomputable def secureChannelResource (q : Nat) :
    Phi Interface (signatures S G T) :=
  ⟨secureBoundary S G T, DependentRandomSystem.ofProb (secureLaw q)⟩

/-! ## Protocols, availability, and simulator class -/

noncomputable def macProtocol (tag : S → G → T) :
    Protocol Interface (signatures S G T) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive (macAlice tag)) *
    Pi.mulSingle .bob (Gamma.ofPrimitive (macBob tag))

noncomputable def otpProtocol :
    Protocol Interface (signatures S G T) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive encrypt) *
    Pi.mulSingle .bob (Gamma.ofPrimitive decrypt)

noncomputable def macThenOtpProtocol (tag : S → G → T) :
    Protocol Interface (signatures S G T) :=
  otpProtocol * macProtocol tag

noncomputable def bottom :
    Protocol Interface (signatures S G T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive blockSecureEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive blockAuthEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive blockRealEve)

noncomputable def macSimulatorProtocol :
    Protocol Interface (signatures S G T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive macSimulator)

noncomputable def otpSimulatorProtocol :
    Protocol Interface (signatures S G T) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive otpSimulator)

noncomputable def macThenOtpSimulators :
    Submonoid (Protocol Interface (signatures S G T)) :=
  supportedOn ({.eve} : Set Interface) (fun _ => ⊤)

/-! ## The pad address travels with the ciphertext

The previous model selected pads by per-interface call counters that
nothing tied to each other or to the position of the ciphertext in flight,
and three kernel-checked counterexamples showed sender and receiver
desynchronizing under mismatched query rates, refuting
`otp_stage_securely_constructs` for every `q`.  Those counterexamples did
their job and are gone together with the model they refuted.  The repaired
channel names positions instead; the twins below replay the exact attack
patterns of the deleted counterexamples and watch them come out
synchronized.  All are computed by the kernel (`rfl`). -/

section PadSynchronization

private abbrev PadG := ZMod 4

private abbrev PadQuery :=
  Query (signatures Bool PadG Bool) (authBoundary Bool PadG Bool)

private def aliceSend (ciphertext : PadG) : PadQuery :=
  ⟨.alice, .sendCipher ciphertext⟩
private def bobKeyAt (index : Nat) : PadQuery := ⟨.bob, .otpKey index⟩
private def bobCipher : PadQuery := ⟨.bob, .receiveCipher⟩

private def distinctPads : (Fin 2 → PadG) × (PadG → Bool) :=
  (![1, 2], fun _ => false)

/-- After Alice has sent twice, Bob's `.receiveCipher` hands him the second
ciphertext **with its position `1`** — the pad address is part of the
delivery, not a receiver-side counter. -/
example :
    (authDDS (S := Bool) 2 distinctPads).output
        [aliceSend 0, aliceSend 3, bobCipher]
        (by simp) (by simp [authDDS, DependentDDS.historyEvaluator]) =
      AuthBobOut.ciphertext (some (1, 3)) :=
  rfl

/-- ...and `.otpKey 1` — the address the delivery names — returns the pad
the second ciphertext was made with, however often either side has queried
before. -/
example :
    (authDDS (S := Bool) 2 distinctPads).output
        [aliceSend 0, aliceSend 3, bobKeyAt 1]
        (by simp) (by simp [authDDS, DependentDDS.historyEvaluator]) =
      AuthBobOut.otpKey (some 2) :=
  rfl

/-- The `q = 1` twin of the deleted third counterexample: Bob's *second*
receive re-delivers position `0` — there is no receiver-side counter left
to advance past the single stored ciphertext. -/
example :
    (authDDS (S := Bool) 1 (![3], fun _ => false)).output
        [aliceSend 2, bobCipher, bobKeyAt 0, bobCipher]
        (by simp) (by simp [authDDS, DependentDDS.historyEvaluator]) =
      AuthBobOut.ciphertext (some (0, 2)) :=
  rfl

end PadSynchronization

/-! ## The OTP stage on the pad-carrying carrier

This estate has no protocol-side `Par`: `Par (Phi I U)` exists for
`HasSumCode` universes (`RandomSystemsCC.TypedParallel`), but
`CC.SecurelyConstructs.par` additionally needs `Par` on the converter
tuples and `SMulParClass`, which are deliberately absent (STATUS §11.5) —
the parallel action is not non-expanding, so a protocol-side `par` would
assert something false.  The MAC secret and the OTP pads are therefore
carried by a *single* DDS with both capabilities rather than composed as
`authChannel ∥ padStore`, and composition is serial via
`CC.SecurelyConstructs.trans`.  The pad table is nevertheless kept
separable: `.otpKey` answers depend only on the sample, never on the
history, so a later `∥`-restatement is a refactor, not a redesign.

The price of the missing `Par` is exactly this lemma: the perfect OTP
construction has to be re-established on the pad-carrying resource rather
than imported from `Symmetric.OTP.otp_securely_constructs`, whose carrier
is `signatures G` without the pads.  This is the one genuine mathematical
obligation of the composition; everything below it is converter algebra. -/

/-- **The OTP stage is perfect over the pad-carrying authenticated
channel** — admitted.  The statement is the repaired one: the pad is
addressed by the position of the ciphertext in flight (`.receiveCipher`
delivers the position, `.nextIndex` names it ahead), so the
per-interface-counter desynchronization that refuted the previous model is
no longer expressible; the `PadSynchronization` twins above replay the old
attack patterns against the kernel.

What remains is the `q`-message analogue of the proven
`Symmetric.OTP.otp_securely_constructs`, by the same pipeline: normalize
both attachment chains to single-DDS laws, then close the security clause
as a distribution equality by transporting the uniform sample along the
history-indexed bijection `(pads, tags) ↦ (ciphertexts, tags)` — messages
read off the transcript, `Dist.fTransform_bijection_uniform` finishing as
in `OTP.security_flatten_observableBehaviorEq` — and the availability
clause as an equality of deterministic answers.  A large but routine
instance of that pipeline, hence the honest admission at error `0`. -/
theorem otp_stage_securely_constructs (q : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (macThenOtpSimulators (S := S) (G := G) (T := T))
      (otpProtocol (S := S) (G := G) (T := T))
      (bottom (S := S) (G := G) (T := T)) 0
      (authenticatedWithOtpKeyResource (S := S) (G := G) (T := T) q)
      (secureChannelResource (S := S) (G := G) (T := T) q) := by
  sorry

/-- The honest protocol commutes with every admitted simulator: simulators are
supported at Eve, the honest converters at Eve's complement.  This is the
carrier-level fact `TypedFinite.commute_honest_of_supported`, at this model's
admitted class; the controlled sentence "We obtain the commutation of the
honest protocol with every admitted simulator" lowers to the same theorem. -/
theorem commute_honest_simulators
    (protocol : Protocol Interface (signatures S G T))
    (simulator : Protocol Interface (signatures S G T))
    (member : simulator ∈ macThenOtpSimulators (S := S) (G := G) (T := T)) :
    Commute
      (protocol ⇂ ({.eve} : Set Interface)ᶜ)
      simulator := by
  rs_commute using le_rfl, member

/-! ## Generic composition statement -/

/-- **Authentication followed by OTP constructs a secure channel.**  Proven
by serial composition (`CC.SecurelyConstructs.trans` discharged by
`commute_honest_simulators`); the hypotheses it inherits are the MAC-stage
construction receipt supplied by the caller and the admitted OTP stage
lemma `otp_stage_securely_constructs`, which contributes zero additional
error. -/
theorem mac_then_otp_securely_constructs
    (tag : S → G → T) (macSecretLaw : Dist.ProbDist S)
    (q : Nat) (εmac : ℝ≥0∞)
    (hmac :
      CC.SecurelyConstructs ({.eve} : Set Interface)
        (macThenOtpSimulators (S := S) (G := G) (T := T))
        (macProtocol tag) (bottom (S := S) (G := G) (T := T)) εmac
        (insecureWithKeysResource (G := G) (T := T) macSecretLaw q)
        (authenticatedWithOtpKeyResource (S := S) (G := G) (T := T) q)) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (macThenOtpSimulators (S := S) (G := G) (T := T))
      (macThenOtpProtocol tag) (bottom (S := S) (G := G) (T := T)) εmac
      (insecureWithKeysResource (G := G) (T := T) macSecretLaw q)
      (secureChannelResource (S := S) (G := G) (T := T) q) := by
  have composed :=
    CC.SecurelyConstructs.trans hmac (otp_stage_securely_constructs q)
      (fun simulator member =>
        commute_honest_simulators _ simulator member)
  simpa [macThenOtpProtocol] using composed

end Generic

/-! ## Assumption-free affine endpoint -/

section Affine

variable {F : Type u}
variable [Fintype F] [DecidableEq F] [Nonempty F] [Field F]

def affineTag (secret : F × F) (message : F) : F :=
  secret.1 * message + secret.2

noncomputable def affineSecretLaw : Dist.ProbDist (F × F) :=
  ⟨Dist.uniform (F × F), Dist.uniform_isProbDist⟩

/-- Affine MAC stage preserving the OTP-pad capability. -/
theorem affine_mac_with_otp_key_securely_constructs :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (macThenOtpSimulators (S := F × F) (G := F) (T := F))
      (macProtocol (affineTag (F := F)))
      (bottom (S := F × F) (G := F) (T := F))
      (1 / (Fintype.card F : ℝ≥0∞))
      (insecureWithKeysResource (G := F) (T := F)
        (affineSecretLaw (F := F)) 1)
      (authenticatedWithOtpKeyResource (S := F × F) (G := F) (T := F) 1) := by
  sorry

/-- **Affine one-time authentication followed by OTP constructs a one-message
secure channel.**  Derived from `mac_then_otp_securely_constructs`;
conditional on the two admissions it inherits — the affine MAC-stage
receipt above and the OTP stage lemma. -/
theorem affine_mac_then_otp_securely_constructs :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (macThenOtpSimulators (S := F × F) (G := F) (T := F))
      (macThenOtpProtocol (affineTag (F := F)))
      (bottom (S := F × F) (G := F) (T := F))
      (1 / (Fintype.card F : ℝ≥0∞))
      (insecureWithKeysResource (G := F) (T := F)
        (affineSecretLaw (F := F)) 1)
      (secureChannelResource (S := F × F) (G := F) (T := F) 1) :=
  mac_then_otp_securely_constructs (affineTag (F := F))
    (affineSecretLaw (F := F)) 1 _
    (affine_mac_with_otp_key_securely_constructs (F := F))

end Affine

/-! ## Assumption-free polynomial-UHF/URF endpoint -/

section Polynomial

variable {F T : Type u}
variable [Fintype F] [DecidableEq F] [Nonempty F] [Field F]
variable [Fintype T] [DecidableEq T] [Nonempty T]

/-- Fixed-length, length-separated polynomial hash used by the end-to-end
construction. -/
def fixedPolynomialHash {ell : Nat}
    (key : F) (message : Fin ell → F) : F :=
  key ^ ell + ∑ i : Fin ell, message i * key ^ i.val

/-- A polynomial hash key paired with the true short-input URF. -/
abbrev PolynomialSecret (F T : Type u) := F × (F → T)

def polynomialUrfTag {ell : Nat}
    (secret : PolynomialSecret F T) (message : Fin ell → F) : T :=
  secret.2 (fixedPolynomialHash secret.1 message)

noncomputable def polynomialSecretLaw :
    Dist.ProbDist (PolynomialSecret F T) :=
  ⟨Dist.uniform (PolynomialSecret F T), Dist.uniform_isProbDist⟩

/-- Polynomial-UHF/URF MAC stage preserving the independent OTP pads. -/
theorem polynomial_urf_mac_with_otp_key_securely_constructs
    (q ell : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (macThenOtpSimulators (S := PolynomialSecret F T)
        (G := Fin ell → F) (T := T))
      (macProtocol (polynomialUrfTag (F := F) (T := T) (ell := ell)))
      (bottom (S := PolynomialSecret F T) (G := Fin ell → F) (T := T))
      ((Nat.choose (q + 1) 2 : ℝ≥0∞) *
          ((ell : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) +
        1 / (Fintype.card T : ℝ≥0∞))
      (insecureWithKeysResource (G := Fin ell → F) (T := T)
        (polynomialSecretLaw (F := F) (T := T)) q)
      (authenticatedWithOtpKeyResource (S := PolynomialSecret F T)
        (G := Fin ell → F) (T := T) q) := by
  sorry

/-- **Polynomial-UHF/URF authentication followed by independent OTP pads
constructs a `q`-message secure channel.**  Derived from
`mac_then_otp_securely_constructs`; conditional on the two admissions it
inherits — the polynomial/URF MAC-stage receipt above and the OTP stage
lemma. -/
theorem polynomial_urf_mac_then_otp_securely_constructs
    (q ell : Nat) :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (macThenOtpSimulators (S := PolynomialSecret F T)
        (G := Fin ell → F) (T := T))
      (macThenOtpProtocol
        (polynomialUrfTag (F := F) (T := T) (ell := ell)))
      (bottom (S := PolynomialSecret F T) (G := Fin ell → F) (T := T))
      ((Nat.choose (q + 1) 2 : ℝ≥0∞) *
          ((ell : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) +
        1 / (Fintype.card T : ℝ≥0∞))
      (insecureWithKeysResource (G := Fin ell → F) (T := T)
        (polynomialSecretLaw (F := F) (T := T)) q)
      (secureChannelResource (S := PolynomialSecret F T)
        (G := Fin ell → F) (T := T) q) :=
  mac_then_otp_securely_constructs
    (polynomialUrfTag (F := F) (T := T) (ell := ell))
    (polynomialSecretLaw (F := F) (T := T)) q _
    (polynomial_urf_mac_with_otp_key_securely_constructs (F := F) (T := T)
      q ell)

end Polynomial

end RandomSystemsCC.Symmetric.MACThenOTP
