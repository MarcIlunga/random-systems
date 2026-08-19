/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.OTPModel
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage
import RandomSystemsCC.AdversaryStructure

/-!
# The additive one-time-pad channel construction

This file contains the random-systems objects and the final constructive-
cryptography statement for CR18 §2.4.  In the real world, an authenticated
channel is bundled with a uniformly sampled shared key.  In the ideal world,
the secure channel gives Eve only a message-independent ciphertext sample.

Following the statement-first program in `DESIGN.md` §11, the final proof is
intentionally deferred until all six construction surfaces have been fixed.
-/

namespace RandomSystemsCC.Symmetric.OTP

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto ENNReal

universe u

section

variable {G : Type u}
variable [Fintype G] [DecidableEq G] [AddCommGroup G]

/-! ## Objects -/

/-- Count selected events in a global resource history. -/
private def countWith {α : Type*} (weight : α → Nat) : List α → Nat
  | [] => 0
  | head :: tail => weight head + countWith weight tail

private theorem countWith_append {α : Type*} (weight : α → Nat)
    (left right : List α) :
    countWith weight (left ++ right) =
      countWith weight left + countWith weight right := by
  induction left with
  | nil => simp only [List.nil_append, countWith, Nat.zero_add]
  | cons head tail ih =>
      simp only [List.cons_append, countWith, ih, Nat.add_assoc]

/-- `countWith` sums a weight over the history, so it sees only *which* queries
were asked, not when.  This is what makes the one-message budget a restriction
on multiplicity rather than on scheduling. -/
private theorem countWith_perm {α : Type*} (weight : α → Nat)
    {left right : List α} (perm : left.Perm right) :
    countWith weight left = countWith weight right := by
  induction perm with
  | nil => rfl
  | cons head _ ih => simp only [countWith, ih]
  | swap first second tail => simp only [countWith]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem countWith_le_append {α : Type*} (weight : α → Nat)
    (left right : List α) :
    countWith weight left ≤ countWith weight (left ++ right) := by
  rw [countWith_append]
  omega

/-- Alice's authenticated-channel submission consumes the real resource's
one-message budget.  Key reads and Bob/Eve observations do not. -/
private def realSubmissionWeight
    (query : Query (signatures G) (realBoundary G)) : Nat :=
  match query with
  | ⟨.alice, .sendCipher _⟩ => 1
  | _ => 0

/-- Alice's send consumes the ideal resource's one-message budget.  Bob/Eve
observations do not. -/
private def idealSubmissionWeight
    (query : Query (signatures G) (idealBoundary G)) : Nat :=
  match query with
  | ⟨.alice, .send _⟩ => 1
  | _ => 0

/-- The unique submitted ciphertext on an admitted real-world `[1]` history. -/
private def realCiphertext?
    (history : List (Query (signatures G) (realBoundary G))) : Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .sendCipher ciphertext⟩ => some ciphertext
    | _ => current) none

/-- The unique submitted message on an admitted ideal-world `[1]` history. -/
private def idealMessage?
    (history : List (Query (signatures G) (idealBoundary G))) : Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .send message⟩ => some message
    | _ => current) none

/-- The deterministic assumed resource at a fixed shared OTP key.  Alice and
Bob receive the same key; the authenticated channel exposes the submitted
ciphertext to Bob and Eve.  Its domain is `[1]` at Alice's submission port:
the history containing a second submission is undefined. -/
def realDDS (key : G) :
    DependentDDS (signatures G) (realBoundary G) where
  domain := {history |
    history ≠ [] ∧ countWith realSubmissionWeight history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact (countWith_le_append realSubmissionWeight left suffix).trans
      rightMember.2
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .key⟩ => .key key
    | ⟨.alice, .sendCipher _⟩ => .ack
    | ⟨.bob, .key⟩ => .key key
    | ⟨.bob, .receiveCipher⟩ => .cipher (realCiphertext? history)
    | ⟨.eve, .readCipher⟩ => realCiphertext? history

/-- The normalized real-world law, sampling the shared OTP key uniformly. -/
noncomputable def realLaw :
    DependentPDS.Prob (signatures G) (realBoundary G) :=
  ⟨Dist.fTransform realDDS (Dist.uniform G),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The named authenticated-channel-plus-key resource assumed by OTP. -/
noncomputable def otpAssumedResource :
    Phi Interface (signatures G) :=
  ⟨realBoundary G, DependentRandomSystem.ofProb realLaw⟩

/-- A deterministic presentation of the secure channel at a fixed simulated
ciphertext.  Bob receives Alice's unique message and Eve receives the
message-independent simulated ciphertext.  Its domain is `[1]` at Alice's
send port: the history containing a second send is undefined. -/
def idealDDS (simulatedCiphertext : G) :
    DependentDDS (signatures G) (idealBoundary G) where
  domain := {history |
    history ≠ [] ∧ countWith idealSubmissionWeight history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact (countWith_le_append idealSubmissionWeight left suffix).trans
      rightMember.2
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ => idealMessage? history
    | ⟨.eve, .sampleCipher⟩ =>
        (idealMessage? history).map fun _ => simulatedCiphertext

/-- The normalized ideal-world law.  Its sole Eve-side ciphertext is sampled
uniformly and independently of Alice's message. -/
noncomputable def idealLaw :
    DependentPDS.Prob (signatures G) (idealBoundary G) :=
  ⟨Dist.fTransform idealDDS (Dist.uniform G),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The named one-message secure channel constructed by OTP. -/
noncomputable def secureChannelResource :
    Phi Interface (signatures G) :=
  ⟨idealBoundary G, DependentRandomSystem.ofProb idealLaw⟩

/-- Alice encrypts and Bob decrypts; Eve is left unattached. -/
noncomputable def otpProtocol :
    Protocol Interface (signatures G) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive encrypt) *
    Pi.mulSingle .bob (Gamma.ofPrimitive decrypt)

/-- The availability filter first runs the ideal-to-real simulator when its
source code is present and then blocks the real Eve port.  On a real resource
the simulator is a source mismatch, so the same protocol is just the real
blocker.  Both worlds therefore reach `availableBoundary`, and availability
can be derived from the simulated-security equality by CC action algebra. -/
noncomputable def bottom :
    Protocol Interface (signatures G) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive blockRealEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive simulator)

/-- The concrete Eve-side simulator tuple. -/
noncomputable def simulatorProtocol :
    Protocol Interface (signatures G) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive simulator)

/-- Exactly the converter tuples supported at Eve are admitted as
simulators. -/
noncomputable def otpSimulators :
    Submonoid (Protocol Interface (signatures G)) :=
  supportedOn ({.eve} : Set Interface) (fun _ => ⊤)

private theorem simulatorProtocol_mem_otpSimulators :
    simulatorProtocol (G := G) ∈ otpSimulators (G := G) := by
  refine AbstractCrypto.mem_supportedOn.mpr ⟨?_, ?_⟩
  · intro interface _
    exact Submonoid.mem_top _
  · intro interface outside
    unfold simulatorProtocol
    rw [Pi.mulSingle_eq_of_ne]
    exact outside

private theorem otpProtocol_smul (resource : Phi Interface (signatures G)) :
    otpProtocol (G := G) • resource =
      encrypt.act (decrypt.act resource) := by
  simp [otpProtocol, mul_smul, primitive_mul_single_smul]

private theorem bottom_smul (resource : Phi Interface (signatures G)) :
    bottom (G := G) • resource =
      blockRealEve.act (simulator.act resource) := by
  simp [bottom, mul_smul, primitive_mul_single_smul]

private theorem simulatorProtocol_smul
    (resource : Phi Interface (signatures G)) :
    simulatorProtocol (G := G) • resource = simulator.act resource := by
  simp [simulatorProtocol, primitive_mul_single_smul]

private theorem otpProtocol_smul_eq_realLaw_attachments :
    otpProtocol (G := G) • otpAssumedResource (G := G) =
      ⟨replaceBoundary
          (replaceBoundary (realBoundary G) .bob .idealBob)
          .alice .idealAlice,
        DependentRandomSystem.ofProb
          (((realLaw (G := G)).attach .bob decrypt.converter rfl).attach
            .alice encrypt.converter rfl)⟩ := by
  rw [otpProtocol_smul]
  unfold otpAssumedResource
  rw [Primitive.act_of_matches decrypt (realBoundary G) rfl]
  change encrypt.act
    ⟨replaceBoundary (realBoundary G) .bob .idealBob,
      DependentRandomSystem.ofProb
        ((realLaw (G := G)).attach .bob decrypt.converter rfl)⟩ = _
  rw [Primitive.act_of_matches encrypt
    (replaceBoundary (realBoundary G) .bob .idealBob) rfl]
  rfl

private theorem simulatorProtocol_smul_eq_idealLaw_attachment :
    simulatorProtocol (G := G) • secureChannelResource (G := G) =
      ⟨replaceBoundary (idealBoundary G) .eve .realEve,
        DependentRandomSystem.ofProb
          ((idealLaw (G := G)).attach .eve simulator.converter rfl)⟩ := by
  rw [simulatorProtocol_smul]
  unfold secureChannelResource
  rw [Primitive.act_of_matches simulator (idealBoundary G) rfl]
  rfl

private theorem security_boundaries_agree :
    replaceBoundary
        (replaceBoundary (realBoundary G) .bob .idealBob)
        .alice .idealAlice =
      replaceBoundary (idealBoundary G) .eve .realEve := by
  funext interface
  cases interface <;> rfl

private theorem strict_equivalent_of_equivalent
    {Input Output : Type*}
    (left right : PFunPDS Input Output)
    (leftProbability : left.isProbDist)
    (rightProbability : right.isProbDist)
    (equivalent : Equivalent left right) :
    StrictContext.Equivalent left right := by
  intro test
  apply edist_eq_zero.mp
  apply bot_unique
  have bound :=
    RandomSystemsCC.StrictContextAdvantage.edist_acceptMass_le_maxAdvantage
      test left right leftProbability rightProbability
  have maxZero : maxAdvantage left right = 0 := by
    rw [← adv_eq_maxAdvantage_swap rightProbability.nonNeg
      leftProbability.nonNeg]
    exact adv_eq_zero_of_equivalent
      (fun environment queries => (equivalent environment queries).symm)
  rw [maxZero] at bound
  simpa using bound

private def securityBoundary (G : Type u) :
    Boundary (signatures G) Interface :=
  replaceBoundary (idealBoundary G) .eve .realEve

private def postDecryptBoundary (G : Type u) :
    Boundary (signatures G) Interface :=
  replaceBoundary (realBoundary G) .bob .idealBob

private def honestSecurityBoundary (G : Type u) :
    Boundary (signatures G) Interface :=
  replaceBoundary (postDecryptBoundary G) .alice .idealAlice

/-- Global query map induced by the one-query Eve simulator.  This is kept
construction-local until the corresponding generic `ofFunctions` framing
receipt is promoted to `TypedFraming`. -/
private def simulatorQueryMap :
    Query (signatures G) (securityBoundary G) →
      Query (signatures G) (idealBoundary G)
  | ⟨.alice, input⟩ => ⟨.alice, input⟩
  | ⟨.bob, input⟩ => ⟨.bob, input⟩
  | ⟨.eve, .readCipher⟩ => ⟨.eve, .sampleCipher⟩

/-- Global answer map induced by the one-query Eve simulator. -/
private def simulatorAnswerMap :
    FlatAnswer (signatures G) (idealBoundary G) →
      FlatAnswer (signatures G) (securityBoundary G)
  | ⟨.alice, output⟩ => ⟨.alice, output⟩
  | ⟨.bob, output⟩ => ⟨.bob, output⟩
  | ⟨.eve, output⟩ => ⟨.eve, output⟩

private def securitySubmissionWeight
    (query : Query (signatures G) (securityBoundary G)) : Nat :=
  match query with
  | ⟨.alice, .send _⟩ => 1
  | _ => 0

private def securityMessage?
    (history : List (Query (signatures G) (securityBoundary G))) : Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .send message⟩ => some message
    | _ => current) none

private theorem securityMessage?_append_of_count_eq_zero
    (left right : List (Query (signatures G) (securityBoundary G)))
    (zero : countWith securitySubmissionWeight right = 0) :
    securityMessage? (left ++ right) = securityMessage? left := by
  unfold securityMessage?
  rw [List.foldl_append]
  generalize
    List.foldl
      (fun current query =>
        match query with
        | ⟨.alice, .send message⟩ => some message
        | _ => current)
      none left = current
  induction right generalizing current with
  | nil => rfl
  | cons query right induction =>
      rcases query with ⟨interface, input⟩
      cases interface <;> cases input <;>
        simp only [countWith, securitySubmissionWeight] at zero ⊢
      · omega
      all_goals exact induction (by omega) _

private theorem countWith_pos_of_securityMessage?_eq_some
    (history : List (Query (signatures G) (securityBoundary G)))
    {message : G} (someMessage : securityMessage? history = some message) :
    0 < countWith securitySubmissionWeight history := by
  by_contra notPositive
  have zero : countWith securitySubmissionWeight history = 0 := by omega
  have noneMessage :=
    securityMessage?_append_of_count_eq_zero (G := G) [] history zero
  change securityMessage? history = securityMessage? [] at noneMessage
  change securityMessage? history = none at noneMessage
  rw [someMessage] at noneMessage
  simp at noneMessage

private theorem securityMessage?_eq_of_prefix_of_count_le_one
    {left right : List (Query (signatures G) (securityBoundary G))}
    (isPrefix : left <+: right)
    (rightBound : countWith securitySubmissionWeight right ≤ 1)
    {message : G} (leftMessage : securityMessage? left = some message) :
    securityMessage? right = some message := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  have leftPositive :=
    countWith_pos_of_securityMessage?_eq_some left leftMessage
  have suffixZero : countWith securitySubmissionWeight suffix = 0 := by
    rw [countWith_append] at rightBound
    omega
  rw [securityMessage?_append_of_count_eq_zero left suffix suffixZero,
    leftMessage]

private def postDecryptSubmissionWeight
    (query : Query (signatures G) (postDecryptBoundary G)) : Nat :=
  match query with
  | ⟨.alice, .sendCipher _⟩ => 1
  | _ => 0

private def postDecryptCiphertext?
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .sendCipher ciphertext⟩ => some ciphertext
    | _ => current) none

private def postDecryptDDS (key : G) :
    DependentDDS (signatures G) (postDecryptBoundary G) where
  domain := {history |
    history ≠ [] ∧ countWith postDecryptSubmissionWeight history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact
      (countWith_le_append postDecryptSubmissionWeight left suffix).trans
        rightMember.2
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .key⟩ => .key key
    | ⟨.alice, .sendCipher _⟩ => .ack
    | ⟨.bob, .receive⟩ =>
        (postDecryptCiphertext? history).map fun ciphertext =>
          ciphertext - key
    | ⟨.eve, .readCipher⟩ => postDecryptCiphertext? history

/-- A harmless value used only on malformed cross-interface answer traces.
Such traces cannot be produced by a flattened dependent resource; the
resource-aware framing receipt below therefore never observes this branch. -/
private def postDecryptFallback
    (query : Query (signatures G) (postDecryptBoundary G)) :
    FlatAnswer (signatures G) (postDecryptBoundary G) :=
  match query with
  | ⟨.alice, _⟩ => ⟨.alice, .ack⟩
  | ⟨.bob, _⟩ => ⟨.bob, none⟩
  | ⟨.eve, _⟩ => ⟨.eve, none⟩

/-- Decode a Bob answer for the lifted decryption step.  The non-Bob cases
are unreachable under tag-faithful application and exist only to make the
global step total. -/
private def decryptInnerAnswer :
    FlatAnswer (signatures G) (realBoundary G) → BobOut G
  | ⟨.bob, answer⟩ => answer
  | _ => .cipher none

/-- The all-interface step induced by installing the local decryption step at
Bob.  Other interfaces make one pass-through resource call. -/
private def decryptGlobalStep
    (query : Query (signatures G) (postDecryptBoundary G))
    (answers : List (FlatAnswer (signatures G) (realBoundary G))) :
    Query (signatures G) (realBoundary G) ⊕
      FlatAnswer (signatures G) (postDecryptBoundary G) :=
  match query, answers with
  | ⟨.alice, .key⟩, [] => .inl ⟨.alice, .key⟩
  | ⟨.alice, .key⟩, ⟨.alice, answer⟩ :: _ =>
      .inr ⟨.alice, answer⟩
  | ⟨.alice, .key⟩, _ => .inr ⟨.alice, .ack⟩
  | ⟨.alice, .sendCipher ciphertext⟩, [] =>
      .inl ⟨.alice, .sendCipher ciphertext⟩
  | ⟨.alice, .sendCipher _⟩, ⟨.alice, answer⟩ :: _ =>
      .inr ⟨.alice, answer⟩
  | ⟨.alice, .sendCipher _⟩, _ => .inr ⟨.alice, .ack⟩
  | ⟨.bob, .receive⟩, [] => .inl ⟨.bob, .key⟩
  | ⟨.bob, .receive⟩, [_] => .inl ⟨.bob, .receiveCipher⟩
  | ⟨.bob, .receive⟩,
      ⟨.bob, .key key⟩ :: ⟨.bob, .cipher (some ciphertext)⟩ :: _ =>
      .inr ⟨.bob, some (ciphertext - key)⟩
  | ⟨.bob, .receive⟩, _ :: _ :: _ => .inr ⟨.bob, none⟩
  | ⟨.eve, .readCipher⟩, [] => .inl ⟨.eve, .readCipher⟩
  | ⟨.eve, .readCipher⟩, ⟨.eve, answer⟩ :: _ =>
      .inr ⟨.eve, answer⟩
  | ⟨.eve, .readCipher⟩, _ => .inr ⟨.eve, none⟩

/-- The lifted step uses two resource answers at Bob and one elsewhere. -/
private def decryptGlobalCount
    (query : Query (signatures G) (postDecryptBoundary G)) : Nat :=
  match query with
  | ⟨.bob, _⟩ => 2
  | _ => 1

set_option maxHeartbeats 800000 in
private theorem decryptGlobalStep_issues_iff
    (query : Query (signatures G) (postDecryptBoundary G))
    (answers : List (FlatAnswer (signatures G) (realBoundary G))) :
    (∃ inner, decryptGlobalStep query answers = Sum.inl inner) ↔
      answers.length < decryptGlobalCount query := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | alice =>
      cases input <;>
        cases answers with
        | nil => simp [decryptGlobalStep, decryptGlobalCount]
        | cons first rest =>
            rcases first with ⟨firstInterface, firstAnswer⟩
            cases firstInterface <;> cases firstAnswer <;>
              simp [decryptGlobalStep, decryptGlobalCount]
  | bob =>
      cases input
      cases answers with
      | nil => simp [decryptGlobalStep, decryptGlobalCount]
      | cons first rest =>
          cases rest with
          | nil => simp [decryptGlobalStep, decryptGlobalCount]
          | cons second tail =>
              rcases first with ⟨firstInterface, firstAnswer⟩
              rcases second with ⟨secondInterface, secondAnswer⟩
              cases firstInterface <;> cases secondInterface <;>
                cases firstAnswer <;> cases secondAnswer <;>
                  simp [decryptGlobalStep, decryptGlobalCount]
              all_goals
                rename_i tail keyValue cipherValue
                cases cipherValue <;>
                  simp [decryptGlobalStep, decryptGlobalCount]
  | eve =>
      cases input
      cases answers with
      | nil => simp [decryptGlobalStep, decryptGlobalCount]
      | cons first rest =>
          rcases first with ⟨firstInterface, firstAnswer⟩
          cases firstInterface <;> cases firstAnswer <;>
            simp [decryptGlobalStep, decryptGlobalCount]

/-- Step presentation used only to normalize application; it is not exposed
as an additional construction object. -/
private noncomputable def decryptGlobalProtocol :
    PFunConverter.ProtocolFn
      (Query (signatures G) (postDecryptBoundary G))
      (FlatAnswer (signatures G) (postDecryptBoundary G))
      (Query (signatures G) (realBoundary G))
      (FlatAnswer (signatures G) (realBoundary G)) :=
  PFunConverter.ProtocolFn.ofStep decryptGlobalStep decryptGlobalCount

/-- Hidden real-resource queries generated by one post-decryption query. -/
private def decryptQueryPath
    (query : Query (signatures G) (postDecryptBoundary G)) :
    List (Query (signatures G) (realBoundary G)) :=
  match query with
  | ⟨.alice, .key⟩ => [⟨.alice, .key⟩]
  | ⟨.alice, .sendCipher ciphertext⟩ =>
      [⟨.alice, .sendCipher ciphertext⟩]
  | ⟨.bob, .receive⟩ => [⟨.bob, .key⟩, ⟨.bob, .receiveCipher⟩]
  | ⟨.eve, .readCipher⟩ => [⟨.eve, .readCipher⟩]

/-- Complete hidden real-resource history generated by an outside history. -/
private def decryptQueryHistory
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    List (Query (signatures G) (realBoundary G)) :=
  history.flatMap decryptQueryPath

private theorem decryptQueryPath_ne_nil
    (query : Query (signatures G) (postDecryptBoundary G)) :
    decryptQueryPath query ≠ [] := by
  unfold decryptQueryPath
  split <;> simp

private theorem decryptQueryHistory_ne_nil_iff
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    decryptQueryHistory history ≠ [] ↔ history ≠ [] := by
  induction history with
  | nil => simp [decryptQueryHistory]
  | cons query history induction =>
      simp only [decryptQueryHistory, List.flatMap_cons]
      constructor
      · simp
      · intro _
        simpa using
          List.append_ne_nil_of_left_ne_nil
            (decryptQueryPath_ne_nil query)
            (List.flatMap decryptQueryPath history)

private theorem realSubmissionWeight_decryptQueryPath
    (query : Query (signatures G) (postDecryptBoundary G)) :
    countWith realSubmissionWeight (decryptQueryPath query) =
      postDecryptSubmissionWeight query := by
  rcases query with ⟨interface, input⟩
  cases interface <;> cases input <;>
    simp [decryptQueryPath, realSubmissionWeight,
      postDecryptSubmissionWeight, countWith,
      TypedFraming.Internal.passQuery,
      TypedFraming.Internal.globalQuery, realBoundary,
      postDecryptBoundary, replaceBoundary]

private theorem countWith_decryptQueryHistory
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    countWith realSubmissionWeight (decryptQueryHistory history) =
      countWith postDecryptSubmissionWeight history := by
  induction history with
  | nil => rfl
  | cons query history induction =>
      rw [show decryptQueryHistory (query :: history) =
        decryptQueryPath query ++ decryptQueryHistory history by rfl]
      rw [countWith_append, realSubmissionWeight_decryptQueryPath,
        induction, countWith]

private theorem decryptQueryHistory_mem_iff
    (key : G)
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    decryptQueryHistory history ∈ (realDDS key).domain ↔
      history ∈ (postDecryptDDS key).domain := by
  change
    (decryptQueryHistory history ≠ [] ∧
      countWith realSubmissionWeight (decryptQueryHistory history) ≤ 1) ↔
    (history ≠ [] ∧
      countWith postDecryptSubmissionWeight history ≤ 1)
  rw [decryptQueryHistory_ne_nil_iff, countWith_decryptQueryHistory]

private theorem ciphertextFold_decryptQueryHistory
    (initial : Option G)
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    List.foldl
        (fun current query =>
          match query with
          | ⟨.alice, .sendCipher ciphertext⟩ => some ciphertext
          | _ => current)
        initial (decryptQueryHistory history) =
      List.foldl
        (fun current query =>
          match query with
          | ⟨.alice, .sendCipher ciphertext⟩ => some ciphertext
          | _ => current)
        initial history := by
  induction history generalizing initial with
  | nil => simp [decryptQueryHistory]
  | cons query history induction =>
      rcases query with ⟨interface, input⟩
      cases interface <;> cases input <;>
        simp [decryptQueryHistory, decryptQueryPath, List.foldl_append,
          TypedFraming.Internal.passQuery,
          TypedFraming.Internal.globalQuery, realBoundary,
          postDecryptBoundary, replaceBoundary]
      all_goals apply induction

private theorem realCiphertext?_decryptQueryHistory
    (history : List (Query (signatures G) (postDecryptBoundary G))) :
    realCiphertext? (decryptQueryHistory history) =
      postDecryptCiphertext? history := by
  exact ciphertextFold_decryptQueryHistory none history

/-- The fixed three-step unrolling of one lifted Bob/pass-through round.
The right side is already the advertised post-decryption resource answer. -/
private theorem decrypt_driveG_eq
    (key : G)
    (prior : List (Query (signatures G) (postDecryptBoundary G)))
    (query : Query (signatures G) (postDecryptBoundary G)) :
    CausalApply.driveG (decryptGlobalStep query)
        (realDDS key).flatten.1 3 (decryptQueryHistory prior) [] =
      ((postDecryptDDS key).flatten.1 (prior ++ [query])).map
        (fun answer =>
          (answer, decryptQueryHistory (prior ++ [query]))) := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | alice =>
      cases input with
      | key =>
          let outerQuery :
              Query (signatures G) (postDecryptBoundary G) :=
            ⟨.alice, .key⟩
          let innerQuery :
              Query (signatures G) (realBoundary G) :=
            ⟨.alice, .key⟩
          have pathEquation :
              decryptQueryHistory prior ++ [innerQuery] =
                decryptQueryHistory (prior ++ [outerQuery]) := by
            simp [outerQuery, innerQuery, decryptQueryHistory,
              decryptQueryPath]
          by_cases admitted :
              prior ++ [outerQuery] ∈
                (postDecryptDDS key).domain
          · have realAdmitted :
                decryptQueryHistory (prior ++ [outerQuery]) ∈
                  (realDDS key).domain :=
              (decryptQueryHistory_mem_iff key _).mpr admitted
            have realPathAdmitted :
                decryptQueryHistory prior ++ [innerQuery] ∈
                  (realDDS key).domain :=
              pathEquation.symm ▸ realAdmitted
            have realRaw :
                (realDDS key).flatten.1
                    (decryptQueryHistory prior ++ [innerQuery]) =
                  Part.some
                    (⟨.alice, .key key⟩ :
                      FlatAnswer (signatures G) (realBoundary G)) := by
              have rawMember :
                  ((realDDS key).flatten.1
                    (decryptQueryHistory prior ++ [innerQuery])).Dom :=
                realPathAdmitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, realDDS, innerQuery]
              rw [List.getLast_append_singleton]
            have postRaw :
                (postDecryptDDS key).flatten.1
                    (prior ++ [outerQuery]) =
                  Part.some
                    (⟨.alice, .key key⟩ :
                      FlatAnswer (signatures G)
                        (postDecryptBoundary G)) := by
              have rawMember :
                  ((postDecryptDDS key).flatten.1
                    (prior ++ [outerQuery])).Dom :=
                admitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, postDecryptDDS, outerQuery]
              rw [List.getLast_append_singleton]
            rw [CausalApply.driveG]
            rw [show
              decryptGlobalStep outerQuery [] =
                Sum.inl innerQuery by rfl]
            simp only
            rw [realRaw, postRaw]
            simp [CausalApply.driveG, decryptGlobalStep,
              outerQuery, innerQuery, realDDS, postDecryptDDS,
              pathEquation]
          · have transformedRejected :
                ¬ (decryptQueryHistory (prior ++ [outerQuery]) ∈
                  (realDDS key).domain) := fun member =>
              admitted ((decryptQueryHistory_mem_iff key _).mp member)
            have realRejected :
                ¬ ((realDDS key).flatten.1
                    (decryptQueryHistory prior ++ [innerQuery])).Dom :=
              fun member => transformedRejected (pathEquation ▸ member)
            have postRejected :
                ¬ ((postDecryptDDS key).flatten.1
                    (prior ++ [outerQuery])).Dom :=
              admitted
            rw [CausalApply.driveG]
            rw [show
              decryptGlobalStep outerQuery [] =
                Sum.inl innerQuery by rfl]
            simp only
            rw [Part.eq_none_iff'.mpr realRejected,
              Part.eq_none_iff'.mpr postRejected]
            simp
      | sendCipher ciphertext =>
          let outerQuery :
              Query (signatures G) (postDecryptBoundary G) :=
            ⟨.alice, .sendCipher ciphertext⟩
          let innerQuery :
              Query (signatures G) (realBoundary G) :=
            ⟨.alice, .sendCipher ciphertext⟩
          have pathEquation :
              decryptQueryHistory prior ++ [innerQuery] =
                decryptQueryHistory (prior ++ [outerQuery]) := by
            simp [outerQuery, innerQuery, decryptQueryHistory,
              decryptQueryPath]
          by_cases admitted :
              prior ++ [outerQuery] ∈
                (postDecryptDDS key).domain
          · have realAdmitted :
                decryptQueryHistory (prior ++ [outerQuery]) ∈
                  (realDDS key).domain :=
              (decryptQueryHistory_mem_iff key _).mpr admitted
            have realPathAdmitted :
                decryptQueryHistory prior ++ [innerQuery] ∈
                  (realDDS key).domain :=
              pathEquation.symm ▸ realAdmitted
            have realRaw :
                (realDDS key).flatten.1
                    (decryptQueryHistory prior ++ [innerQuery]) =
                  Part.some
                    (⟨.alice, .ack⟩ :
                      FlatAnswer (signatures G) (realBoundary G)) := by
              have rawMember :
                  ((realDDS key).flatten.1
                    (decryptQueryHistory prior ++ [innerQuery])).Dom :=
                realPathAdmitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, realDDS, innerQuery]
              rw [List.getLast_append_singleton]
            have postRaw :
                (postDecryptDDS key).flatten.1
                    (prior ++ [outerQuery]) =
                  Part.some
                    (⟨.alice, .ack⟩ :
                      FlatAnswer (signatures G)
                        (postDecryptBoundary G)) := by
              have rawMember :
                  ((postDecryptDDS key).flatten.1
                    (prior ++ [outerQuery])).Dom :=
                admitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, postDecryptDDS, outerQuery]
              rw [List.getLast_append_singleton]
            rw [CausalApply.driveG]
            rw [show
              decryptGlobalStep outerQuery [] =
                Sum.inl innerQuery by rfl]
            simp only
            rw [realRaw, postRaw]
            simp [CausalApply.driveG, decryptGlobalStep,
              outerQuery, innerQuery, realDDS, postDecryptDDS,
              pathEquation]
          · have transformedRejected :
                ¬ (decryptQueryHistory (prior ++ [outerQuery]) ∈
                  (realDDS key).domain) := fun member =>
              admitted ((decryptQueryHistory_mem_iff key _).mp member)
            have realRejected :
                ¬ ((realDDS key).flatten.1
                    (decryptQueryHistory prior ++ [innerQuery])).Dom :=
              fun member => transformedRejected (pathEquation ▸ member)
            have postRejected :
                ¬ ((postDecryptDDS key).flatten.1
                    (prior ++ [outerQuery])).Dom :=
              admitted
            rw [CausalApply.driveG]
            rw [show
              decryptGlobalStep outerQuery [] =
                Sum.inl innerQuery by rfl]
            simp only
            rw [Part.eq_none_iff'.mpr realRejected,
              Part.eq_none_iff'.mpr postRejected]
            simp
  | bob =>
      cases input
      let outerQuery :
          Query (signatures G) (postDecryptBoundary G) :=
        ⟨.bob, .receive⟩
      let keyQuery :
          Query (signatures G) (realBoundary G) :=
        ⟨.bob, .key⟩
      let ciphertextQuery :
          Query (signatures G) (realBoundary G) :=
        ⟨.bob, .receiveCipher⟩
      have pathEquation :
          decryptQueryHistory prior ++ [keyQuery] ++ [ciphertextQuery] =
            decryptQueryHistory (prior ++ [outerQuery]) := by
        simp [outerQuery, keyQuery, ciphertextQuery,
          decryptQueryHistory, decryptQueryPath]
      by_cases admitted :
          prior ++ [outerQuery] ∈ (postDecryptDDS key).domain
      · have transformedAdmitted :
            decryptQueryHistory (prior ++ [outerQuery]) ∈
              (realDDS key).domain :=
          (decryptQueryHistory_mem_iff key _).mpr admitted
        have fullAdmitted :
            decryptQueryHistory prior ++ [keyQuery] ++ [ciphertextQuery] ∈
              (realDDS key).domain :=
          pathEquation.symm ▸ transformedAdmitted
        have firstAdmitted :
            decryptQueryHistory prior ++ [keyQuery] ∈
              (realDDS key).domain :=
          (realDDS key).prefix_closed (by simp) (by simp) fullAdmitted
        have firstRaw :
            (realDDS key).flatten.1
                (decryptQueryHistory prior ++ [keyQuery]) =
              Part.some
                (⟨.bob, .key key⟩ :
                  FlatAnswer (signatures G) (realBoundary G)) := by
          have rawMember :
              ((realDDS key).flatten.1
                (decryptQueryHistory prior ++ [keyQuery])).Dom :=
            firstAdmitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, realDDS, keyQuery]
          rw [List.getLast_append_singleton]
        have ciphertextEquation :
            realCiphertext?
                (decryptQueryHistory prior ++ [keyQuery] ++
                  [ciphertextQuery]) =
              postDecryptCiphertext? (prior ++ [outerQuery]) := by
          rw [pathEquation]
          exact realCiphertext?_decryptQueryHistory _
        have fullRaw :
            (realDDS key).flatten.1
                (decryptQueryHistory prior ++ [keyQuery] ++
                  [ciphertextQuery]) =
              Part.some
                (⟨.bob,
                    .cipher
                      (postDecryptCiphertext? (prior ++ [outerQuery]))⟩ :
                  FlatAnswer (signatures G) (realBoundary G)) := by
          have rawMember :
              ((realDDS key).flatten.1
                (decryptQueryHistory prior ++ [keyQuery] ++
                  [ciphertextQuery])).Dom :=
            fullAdmitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, realDDS, ciphertextQuery]
          rw [List.getLast_append_singleton, ciphertextEquation]
        have postRaw :
            (postDecryptDDS key).flatten.1
                (prior ++ [outerQuery]) =
              Part.some
                (⟨.bob,
                    (postDecryptCiphertext? (prior ++ [outerQuery])).map
                      fun ciphertext => ciphertext - key⟩ :
                  FlatAnswer (signatures G)
                    (postDecryptBoundary G)) := by
          have rawMember :
              ((postDecryptDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
            admitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, postDecryptDDS, outerQuery]
          rw [List.getLast_append_singleton]
        rw [CausalApply.driveG]
        rw [show decryptGlobalStep outerQuery [] =
          Sum.inl keyQuery by rfl]
        simp only
        rw [firstRaw]
        simp only [Part.bind_some, List.nil_append]
        rw [CausalApply.driveG]
        rw [show
          decryptGlobalStep outerQuery
              [(⟨.bob, .key key⟩ :
                FlatAnswer (signatures G) (realBoundary G))] =
            Sum.inl ciphertextQuery by rfl]
        simp only
        rw [fullRaw, postRaw]
        cases ciphertext :
            postDecryptCiphertext? (prior ++ [outerQuery]) <;>
          simp [CausalApply.driveG, decryptGlobalStep,
            outerQuery, keyQuery, ciphertextQuery,
            pathEquation, ciphertext]
      · have firstRejected :
            ¬ ((realDDS key).flatten.1
                (decryptQueryHistory prior ++ [keyQuery])).Dom := by
          intro firstMember
          apply admitted
          apply (decryptQueryHistory_mem_iff key _).mp
          have fullMember :
              decryptQueryHistory prior ++ [keyQuery] ++
                  [ciphertextQuery] ∈
                (realDDS key).domain := by
            change
              (_ ≠ [] ∧ countWith realSubmissionWeight _ ≤ 1)
                at firstMember
            change
              (_ ≠ [] ∧ countWith realSubmissionWeight _ ≤ 1)
            refine ⟨by simp, ?_⟩
            rw [countWith_append]
            simpa [ciphertextQuery, countWith,
              realSubmissionWeight] using firstMember.2
          exact pathEquation ▸ fullMember
        have postRejected :
            ¬ ((postDecryptDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
          admitted
        rw [CausalApply.driveG]
        rw [show decryptGlobalStep outerQuery [] =
          Sum.inl keyQuery by rfl]
        simp only
        rw [Part.eq_none_iff'.mpr firstRejected,
          Part.eq_none_iff'.mpr postRejected]
        simp
  | eve =>
      cases input
      let outerQuery :
          Query (signatures G) (postDecryptBoundary G) :=
        ⟨.eve, .readCipher⟩
      let innerQuery :
          Query (signatures G) (realBoundary G) :=
        ⟨.eve, .readCipher⟩
      have pathEquation :
          decryptQueryHistory prior ++ [innerQuery] =
            decryptQueryHistory (prior ++ [outerQuery]) := by
        simp [outerQuery, innerQuery, decryptQueryHistory,
          decryptQueryPath]
      by_cases admitted :
          prior ++ [outerQuery] ∈ (postDecryptDDS key).domain
      · have transformedAdmitted :
            decryptQueryHistory (prior ++ [outerQuery]) ∈
              (realDDS key).domain :=
          (decryptQueryHistory_mem_iff key _).mpr admitted
        have realAdmitted :
            decryptQueryHistory prior ++ [innerQuery] ∈
              (realDDS key).domain :=
          pathEquation.symm ▸ transformedAdmitted
        have ciphertextEquation :
            realCiphertext?
                (decryptQueryHistory prior ++ [innerQuery]) =
              postDecryptCiphertext? (prior ++ [outerQuery]) := by
          rw [pathEquation]
          exact realCiphertext?_decryptQueryHistory _
        have realRaw :
            (realDDS key).flatten.1
                (decryptQueryHistory prior ++ [innerQuery]) =
              Part.some
                (⟨.eve,
                    postDecryptCiphertext? (prior ++ [outerQuery])⟩ :
                  FlatAnswer (signatures G) (realBoundary G)) := by
          have rawMember :
              ((realDDS key).flatten.1
                (decryptQueryHistory prior ++ [innerQuery])).Dom :=
            realAdmitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, realDDS, innerQuery]
          rw [List.getLast_append_singleton, ciphertextEquation]
        have postRaw :
            (postDecryptDDS key).flatten.1
                (prior ++ [outerQuery]) =
              Part.some
                (⟨.eve,
                    postDecryptCiphertext? (prior ++ [outerQuery])⟩ :
                  FlatAnswer (signatures G)
                    (postDecryptBoundary G)) := by
          have rawMember :
              ((postDecryptDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
            admitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, postDecryptDDS, outerQuery]
          rw [List.getLast_append_singleton]
        rw [CausalApply.driveG]
        rw [show decryptGlobalStep outerQuery [] =
          Sum.inl innerQuery by rfl]
        simp only
        rw [realRaw, postRaw]
        simp [CausalApply.driveG, decryptGlobalStep,
          outerQuery, innerQuery, realDDS, postDecryptDDS,
          pathEquation, realCiphertext?_decryptQueryHistory]
      · have transformedRejected :
            ¬ (decryptQueryHistory (prior ++ [outerQuery]) ∈
              (realDDS key).domain) := fun member =>
          admitted ((decryptQueryHistory_mem_iff key _).mp member)
        have realRejected :
            ¬ ((realDDS key).flatten.1
                (decryptQueryHistory prior ++ [innerQuery])).Dom :=
          fun member => transformedRejected (pathEquation ▸ member)
        have postRejected :
            ¬ ((postDecryptDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
          admitted
        rw [CausalApply.driveG]
        rw [show decryptGlobalStep outerQuery [] =
          Sum.inl innerQuery by rfl]
        simp only
        rw [Part.eq_none_iff'.mpr realRejected,
          Part.eq_none_iff'.mpr postRejected]
        simp

/-- The fixed-fuel whole-history receipt.  It relates the hidden real-resource
history to the visible post-decryption history and otherwise has exactly the
identity simple-converter behavior. -/
private theorem decrypt_driveOuter_eq (key : G) :
    ∀ (prior :
        List (Query (signatures G) (postDecryptBoundary G)))
      (queries :
        List (Query (signatures G) (postDecryptBoundary G))),
      CausalApply.driveOuter decryptGlobalStep
          (realDDS key).flatten.1 3
          (decryptQueryHistory prior) queries =
        (CausalApply.driveOuter
            (PFunConverter.DDC.simpleStep id id)
            (postDecryptDDS key).flatten.1 2 prior queries).map
          (fun result =>
            (result.1, decryptQueryHistory result.2)) := by
  intro prior queries
  induction queries generalizing prior with
  | nil =>
      simp [CausalApply.driveOuter]
  | cons query rest induction =>
      simp only [CausalApply.driveOuter]
      rw [decrypt_driveG_eq]
      rw [show (2 : Nat) = 0 + 1 + 1 by rfl,
        PFunConverter.DDC.driveG_simpleStep]
      simp only [id_eq, Part.map_bind, Part.bind_map, Part.map_map,
        Function.comp_def]
      rw [induction]
      simp only [Part.map_map, Function.comp_def]

/-- The small RS receipt consumed by the typed attachment proof: after
decryption, the flattened resource is exactly the advertised intermediate
DDS. -/
private theorem decrypt_applyG_eq (key : G) :
    CausalApply.applyG decryptGlobalStep (realDDS key).flatten.1 =
      (postDecryptDDS key).flatten := by
  apply Subtype.ext
  funext queries
  apply Part.ext
  intro answer
  rw [show
      (CausalApply.applyG decryptGlobalStep
        (realDDS key).flatten.1).1 =
          CausalApply.applyRaw decryptGlobalStep
            (realDDS key).flatten.1 from rfl,
    CausalApply.mem_applyRaw]
  constructor
  · rintro ⟨fuel, appliedMember⟩
    rw [CausalApply.mem_applyRawAt_iff] at appliedMember
    obtain ⟨result, outerMember, lastAnswer⟩ := appliedMember
    have count_le :
        ∀ query :
            Query (signatures G) (postDecryptBoundary G),
          decryptGlobalCount query ≤ 2 := by
      rintro ⟨interface, input⟩
      cases interface <;> cases input <;>
        simp [decryptGlobalCount]
    have normalizedOuter :=
      CausalApply.driveOuter_mem_at_uniform_count_succ
        decryptGlobalStep decryptGlobalCount
        decryptGlobalStep_issues_iff 2 count_le
        (realDDS key).flatten.1 outerMember
    have normalizedOuter' :
        result ∈
          CausalApply.driveOuter decryptGlobalStep
            (realDDS key).flatten.1 3
            (decryptQueryHistory []) queries := by
      simpa [decryptQueryHistory] using normalizedOuter
    rw [decrypt_driveOuter_eq key [] queries] at normalizedOuter'
    rw [Part.mem_map_iff] at normalizedOuter'
    obtain ⟨simpleResult, simpleMember, resultEquation⟩ :=
      normalizedOuter'
    subst result
    have queriesNonempty : queries ≠ [] := by
      intro queriesEmpty
      subst queries
      have resultLength :=
        CausalApply.driveOuter_length
          (PFunConverter.DDC.simpleStep id id)
          (postDecryptDDS key).flatten.1 2 [] []
          simpleMember
      have resultEmpty : simpleResult.1 = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using resultLength)
      rw [resultEmpty] at lastAnswer
      simp at lastAnswer
    obtain ⟨_, lastOutput⟩ :=
      PFunConverter.DDC.driveOuter_simpleStep_mem_imp
        (id :
          Query (signatures G) (postDecryptBoundary G) →
            Query (signatures G) (postDecryptBoundary G))
        (id :
          FlatAnswer (signatures G) (postDecryptBoundary G) →
            FlatAnswer (signatures G) (postDecryptBoundary G))
        (postDecryptDDS key).flatten queries [] simpleMember
    obtain ⟨domainMember, lastOutput⟩ :=
      lastOutput queriesNonempty
    have domainMember' :
        queries ∈ PFunDDS.dom (postDecryptDDS key).flatten := by
      simpa using domainMember
    have lastOutput' :
        simpleResult.1.getLast? =
          some
            (PFunDDS.output (postDecryptDDS key).flatten
              queries domainMember') := by
      simpa using lastOutput
    rw [lastAnswer] at lastOutput'
    have answerEquation :
        answer =
          PFunDDS.output (postDecryptDDS key).flatten
            queries domainMember' :=
      Option.some.inj lastOutput'
    rw [answerEquation]
    exact Part.get_mem _
  · intro answerMember
    have domainMember :
        queries ∈ PFunDDS.dom (postDecryptDDS key).flatten := by
      rw [PFunDDS.dom_def, PFun.mem_dom]
      exact ⟨answer, answerMember⟩
    have queriesNonempty : queries ≠ [] := by
      intro queriesEmpty
      subst queries
      exact PFunDDS.empty_not_mem (postDecryptDDS key).flatten
        domainMember
    obtain ⟨answers, simpleMember, lastOutput⟩ :=
      PFunConverter.DDC.driveOuter_simpleStep_of_dom
        (id :
          Query (signatures G) (postDecryptBoundary G) →
            Query (signatures G) (postDecryptBoundary G))
        (id :
          FlatAnswer (signatures G) (postDecryptBoundary G) →
            FlatAnswer (signatures G) (postDecryptBoundary G))
        (postDecryptDDS key).flatten queries []
        (Or.inl (by simpa using domainMember))
    have simpleMember' :
        (answers, queries) ∈
          CausalApply.driveOuter
            (PFunConverter.DDC.simpleStep id id)
            (postDecryptDDS key).flatten.1 2 [] queries := by
      simpa using simpleMember
    have outputEquation :
        PFunDDS.output (postDecryptDDS key).flatten
            queries domainMember =
          answer :=
      Part.mem_unique (Part.get_mem _) answerMember
    have lastAnswer : answers.getLast? = some answer := by
      rw [lastOutput (by simpa using domainMember) queriesNonempty]
      simpa using congrArg some outputEquation
    have transformedMember :
        (answers, decryptQueryHistory queries) ∈
          CausalApply.driveOuter decryptGlobalStep
            (realDDS key).flatten.1 3
            (decryptQueryHistory []) queries := by
      rw [decrypt_driveOuter_eq key [] queries, Part.mem_map_iff]
      exact ⟨(answers, queries), simpleMember', rfl⟩
    refine ⟨3, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    exact ⟨(answers, decryptQueryHistory queries),
      by simpa [decryptQueryHistory] using transformedMember,
      lastAnswer⟩

/-- Construction-local U07 instance.  The equality is deliberately only
after application to the tag-faithful flattened resource; it is one
instantiation of the promoted framed-`ofStep` coherence receipt. -/
private theorem decrypt_framed_apply_eq_global (key : G) :
    PFunConverter.apply
        (TypedFraming.framedConverter (.bob : Interface) (realBoundary G)
          decrypt.converter rfl).val
        (realDDS key).flatten =
      PFunConverter.apply decryptGlobalProtocol (realDDS key).flatten := by
  unfold decryptGlobalProtocol
  exact TypedFraming.apply_framed_ofStep_eq_apply_ofStep
    (.bob : Interface) (realBoundary G) decrypt.converter rfl
    decryptStep (fun _ => 2) rfl
    decryptGlobalStep decryptGlobalCount decryptGlobalStep_issues_iff
    (by
      rintro ⟨queryInterface, input⟩ same
      change queryInterface = Interface.bob at same
      subst queryInterface
      cases input
      intro localAnswers
      rcases localAnswers with _ | ⟨keyAnswer, _ | ⟨cipherAnswer, rest⟩⟩
      · rfl
      · cases keyAnswer <;> rfl
      · cases keyAnswer <;> cases cipherAnswer <;>
          first
            | rfl
            | (rename_i cipher; cases cipher <;> rfl))
    (by
      rintro ⟨queryInterface, input⟩ same
      change queryInterface = Interface.bob at same
      subst queryInterface
      cases input
      rfl)
    (by
      rintro ⟨queryInterface, input⟩ different
      cases queryInterface with
      | alice => cases input <;> rfl
      | bob => exact absurd rfl different
      | eve => cases input; rfl)
    (by
      rintro ⟨queryInterface, input⟩ different ⟨answerInterface, output⟩
        sameTag
      change answerInterface = queryInterface at sameTag
      subst answerInterface
      cases queryInterface with
      | alice => cases input <;> rfl
      | bob => exact absurd rfl different
      | eve => cases input; rfl)
    (by
      rintro ⟨queryInterface, input⟩ different
      cases queryInterface with
      | alice => rfl
      | bob => exact absurd rfl different
      | eve => rfl)
    (realDDS key).flatten (realDDS key).flatten_tag_faithful

private theorem decrypt_attach_eq (key : G) :
    (realDDS key).attach .bob decrypt.converter rfl =
      postDecryptDDS key := by
  apply DependentDDS.flatten_injective
  rw [DependentDDS.flatten_attach_eq_apply_framed]
  rw [decrypt_framed_apply_eq_global]
  unfold decryptGlobalProtocol
  rw [PFunConverter.ProtocolFn.apply_ofStep_eq_applyG
    decryptGlobalStep decryptGlobalCount decryptGlobalStep_issues_iff]
  exact decrypt_applyG_eq key

private def honestSubmissionWeight
    (query : Query (signatures G) (honestSecurityBoundary G)) : Nat :=
  match query with
  | ⟨.alice, .send _⟩ => 1
  | _ => 0

private def honestMessage?
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .send message⟩ => some message
    | _ => current) none

private def honestSecurityDDS (key : G) :
    DependentDDS (signatures G) (honestSecurityBoundary G) where
  domain := {history |
    history ≠ [] ∧ countWith honestSubmissionWeight history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact
      (countWith_le_append honestSubmissionWeight left suffix).trans
        rightMember.2
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ => honestMessage? history
    | ⟨.eve, .readCipher⟩ =>
        (honestMessage? history).map fun message => message + key

/-- The all-interface step induced by installing the local encryption step at
Alice.  Other interfaces make one pass-through resource call. -/
private def encryptGlobalStep
    (query : Query (signatures G) (honestSecurityBoundary G))
    (answers : List (FlatAnswer (signatures G) (postDecryptBoundary G))) :
    Query (signatures G) (postDecryptBoundary G) ⊕
      FlatAnswer (signatures G) (honestSecurityBoundary G) :=
  match query, answers with
  | ⟨.alice, .send _⟩, [] => .inl ⟨.alice, .key⟩
  | ⟨.alice, .send message⟩, [⟨.alice, .key key⟩] =>
      .inl ⟨.alice, .sendCipher (message + key)⟩
  | ⟨.alice, .send message⟩, [⟨.alice, .ack⟩] =>
      .inl ⟨.alice, .sendCipher message⟩
  | ⟨.alice, .send _⟩, [_] => .inl ⟨.alice, .key⟩
  | ⟨.alice, .send _⟩, _ :: _ :: _ => .inr ⟨.alice, .ack⟩
  | ⟨.bob, .receive⟩, [] => .inl ⟨.bob, .receive⟩
  | ⟨.bob, .receive⟩, ⟨.bob, answer⟩ :: _ => .inr ⟨.bob, answer⟩
  | ⟨.bob, .receive⟩, _ :: _ => .inr ⟨.bob, none⟩
  | ⟨.eve, .readCipher⟩, [] => .inl ⟨.eve, .readCipher⟩
  | ⟨.eve, .readCipher⟩, ⟨.eve, answer⟩ :: _ => .inr ⟨.eve, answer⟩
  | ⟨.eve, .readCipher⟩, _ :: _ => .inr ⟨.eve, none⟩

/-- The lifted step uses two resource answers at Alice and one elsewhere. -/
private def encryptGlobalCount
    (query : Query (signatures G) (honestSecurityBoundary G)) : Nat :=
  match query with
  | ⟨.alice, _⟩ => 2
  | _ => 1

private theorem encryptGlobalStep_issues_iff
    (query : Query (signatures G) (honestSecurityBoundary G))
    (answers : List (FlatAnswer (signatures G) (postDecryptBoundary G))) :
    (∃ inner, encryptGlobalStep query answers = Sum.inl inner) ↔
      answers.length < encryptGlobalCount query := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | alice =>
      cases input
      cases answers with
      | nil => simp [encryptGlobalStep, encryptGlobalCount]
      | cons first rest =>
          cases rest with
          | nil =>
              rcases first with ⟨firstInterface, firstAnswer⟩
              cases firstInterface <;> cases firstAnswer <;>
                simp [encryptGlobalStep, encryptGlobalCount]
          | cons second tail =>
              simp [encryptGlobalStep, encryptGlobalCount]
  | bob =>
      cases input
      cases answers with
      | nil => simp [encryptGlobalStep, encryptGlobalCount]
      | cons first rest =>
          rcases first with ⟨firstInterface, firstAnswer⟩
          cases firstInterface <;>
            simp [encryptGlobalStep, encryptGlobalCount]
  | eve =>
      cases input
      cases answers with
      | nil => simp [encryptGlobalStep, encryptGlobalCount]
      | cons first rest =>
          rcases first with ⟨firstInterface, firstAnswer⟩
          cases firstInterface <;>
            simp [encryptGlobalStep, encryptGlobalCount]

/-- Step presentation used only to normalize application; it is not exposed
as an additional construction object. -/
private noncomputable def encryptGlobalProtocol :
    PFunConverter.ProtocolFn
      (Query (signatures G) (honestSecurityBoundary G))
      (FlatAnswer (signatures G) (honestSecurityBoundary G))
      (Query (signatures G) (postDecryptBoundary G))
      (FlatAnswer (signatures G) (postDecryptBoundary G)) :=
  PFunConverter.ProtocolFn.ofStep encryptGlobalStep encryptGlobalCount

/-- Hidden post-decryption queries generated by one honest-boundary query. -/
private def encryptQueryPath (key : G)
    (query : Query (signatures G) (honestSecurityBoundary G)) :
    List (Query (signatures G) (postDecryptBoundary G)) :=
  match query with
  | ⟨.alice, .send message⟩ =>
      [⟨.alice, .key⟩, ⟨.alice, .sendCipher (message + key)⟩]
  | ⟨.bob, .receive⟩ => [⟨.bob, .receive⟩]
  | ⟨.eve, .readCipher⟩ => [⟨.eve, .readCipher⟩]

/-- Complete hidden post-decryption history generated by an outside
history. -/
private def encryptQueryHistory (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    List (Query (signatures G) (postDecryptBoundary G)) :=
  history.flatMap (encryptQueryPath key)

private theorem encryptQueryPath_ne_nil (key : G)
    (query : Query (signatures G) (honestSecurityBoundary G)) :
    encryptQueryPath key query ≠ [] := by
  unfold encryptQueryPath
  split <;> simp

private theorem encryptQueryHistory_ne_nil_iff (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    encryptQueryHistory key history ≠ [] ↔ history ≠ [] := by
  induction history with
  | nil => simp [encryptQueryHistory]
  | cons query history induction =>
      simp only [encryptQueryHistory, List.flatMap_cons]
      constructor
      · simp
      · intro _
        simpa using
          List.append_ne_nil_of_left_ne_nil
            (encryptQueryPath_ne_nil key query)
            (List.flatMap (encryptQueryPath key) history)

private theorem postDecryptSubmissionWeight_encryptQueryPath (key : G)
    (query : Query (signatures G) (honestSecurityBoundary G)) :
    countWith postDecryptSubmissionWeight (encryptQueryPath key query) =
      honestSubmissionWeight query := by
  rcases query with ⟨interface, input⟩
  cases interface <;> cases input <;>
    simp [encryptQueryPath, postDecryptSubmissionWeight,
      honestSubmissionWeight, countWith]

private theorem countWith_encryptQueryHistory (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    countWith postDecryptSubmissionWeight (encryptQueryHistory key history) =
      countWith honestSubmissionWeight history := by
  induction history with
  | nil => rfl
  | cons query history induction =>
      rw [show encryptQueryHistory key (query :: history) =
        encryptQueryPath key query ++ encryptQueryHistory key history by rfl]
      rw [countWith_append, postDecryptSubmissionWeight_encryptQueryPath,
        induction, countWith]

private theorem encryptQueryHistory_mem_iff (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    encryptQueryHistory key history ∈ (postDecryptDDS key).domain ↔
      history ∈ (honestSecurityDDS key).domain := by
  change
    (encryptQueryHistory key history ≠ [] ∧
      countWith postDecryptSubmissionWeight
        (encryptQueryHistory key history) ≤ 1) ↔
    (history ≠ [] ∧ countWith honestSubmissionWeight history ≤ 1)
  rw [encryptQueryHistory_ne_nil_iff, countWith_encryptQueryHistory]

private theorem ciphertextFold_encryptQueryHistory (key : G)
    (initial : Option G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    List.foldl
        (fun current query =>
          match query with
          | ⟨.alice, .sendCipher ciphertext⟩ => some ciphertext
          | _ => current)
        (initial.map fun message => message + key)
        (encryptQueryHistory key history) =
      (List.foldl
        (fun current query =>
          match query with
          | ⟨.alice, .send message⟩ => some message
          | _ => current)
        initial history).map fun message => message + key := by
  induction history generalizing initial with
  | nil => simp [encryptQueryHistory]
  | cons query history induction =>
      rcases query with ⟨interface, input⟩
      cases interface <;> cases input <;>
        simp only [encryptQueryHistory, List.flatMap_cons, List.foldl_append,
          List.foldl_cons] <;>
        simp only [encryptQueryPath, List.foldl_cons, List.foldl_nil]
      · rename_i message
        simpa using induction (some message)
      all_goals exact induction initial

private theorem postDecryptCiphertext?_encryptQueryHistory (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    postDecryptCiphertext? (encryptQueryHistory key history) =
      (honestMessage? history).map fun message => message + key := by
  simpa using ciphertextFold_encryptQueryHistory key none history

/-- The fixed three-step unrolling of one lifted Alice/pass-through round.
The right side is already the advertised honest-boundary resource answer. -/
private theorem encrypt_driveG_eq
    (key : G)
    (prior : List (Query (signatures G) (honestSecurityBoundary G)))
    (query : Query (signatures G) (honestSecurityBoundary G)) :
    CausalApply.driveG (encryptGlobalStep query)
        (postDecryptDDS key).flatten.1 3 (encryptQueryHistory key prior) [] =
      ((honestSecurityDDS key).flatten.1 (prior ++ [query])).map
        (fun answer =>
          (answer, encryptQueryHistory key (prior ++ [query]))) := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | alice =>
      cases input with
      | send message =>
          let outerQuery :
              Query (signatures G) (honestSecurityBoundary G) :=
            ⟨.alice, .send message⟩
          let keyQuery :
              Query (signatures G) (postDecryptBoundary G) :=
            ⟨.alice, .key⟩
          let cipherQuery :
              Query (signatures G) (postDecryptBoundary G) :=
            ⟨.alice, .sendCipher (message + key)⟩
          have pathEquation :
              encryptQueryHistory key prior ++ [keyQuery] ++
                  [cipherQuery] =
                encryptQueryHistory key (prior ++ [outerQuery]) := by
            simp [outerQuery, keyQuery, cipherQuery,
              encryptQueryHistory, encryptQueryPath]
          by_cases admitted :
              prior ++ [outerQuery] ∈ (honestSecurityDDS key).domain
          · have transformedAdmitted :
                encryptQueryHistory key (prior ++ [outerQuery]) ∈
                  (postDecryptDDS key).domain :=
              (encryptQueryHistory_mem_iff key _).mpr admitted
            have fullAdmitted :
                encryptQueryHistory key prior ++ [keyQuery] ++
                    [cipherQuery] ∈
                  (postDecryptDDS key).domain :=
              pathEquation.symm ▸ transformedAdmitted
            have firstAdmitted :
                encryptQueryHistory key prior ++ [keyQuery] ∈
                  (postDecryptDDS key).domain :=
              (postDecryptDDS key).prefix_closed (by simp) (by simp)
                fullAdmitted
            have firstRaw :
                (postDecryptDDS key).flatten.1
                    (encryptQueryHistory key prior ++ [keyQuery]) =
                  Part.some
                    (⟨.alice, .key key⟩ :
                      FlatAnswer (signatures G) (postDecryptBoundary G)) := by
              have rawMember :
                  ((postDecryptDDS key).flatten.1
                    (encryptQueryHistory key prior ++ [keyQuery])).Dom :=
                firstAdmitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, postDecryptDDS, keyQuery]
              rw [List.getLast_append_singleton]
            have fullRaw :
                (postDecryptDDS key).flatten.1
                    (encryptQueryHistory key prior ++ [keyQuery] ++
                      [cipherQuery]) =
                  Part.some
                    (⟨.alice, .ack⟩ :
                      FlatAnswer (signatures G) (postDecryptBoundary G)) := by
              have rawMember :
                  ((postDecryptDDS key).flatten.1
                    (encryptQueryHistory key prior ++ [keyQuery] ++
                      [cipherQuery])).Dom :=
                fullAdmitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, postDecryptDDS, cipherQuery]
              rw [List.getLast_append_singleton]
            have postRaw :
                (honestSecurityDDS key).flatten.1
                    (prior ++ [outerQuery]) =
                  Part.some
                    (⟨.alice, .ack⟩ :
                      FlatAnswer (signatures G)
                        (honestSecurityBoundary G)) := by
              have rawMember :
                  ((honestSecurityDDS key).flatten.1
                    (prior ++ [outerQuery])).Dom :=
                admitted
              rw [← Part.some_get rawMember]
              congr 1
              dsimp only [DependentDDS.flatten, honestSecurityDDS,
                outerQuery]
              rw [List.getLast_append_singleton]
            rw [CausalApply.driveG]
            rw [show encryptGlobalStep outerQuery [] =
              Sum.inl keyQuery by rfl]
            simp only
            rw [firstRaw]
            simp only [Part.bind_some, List.nil_append]
            rw [CausalApply.driveG]
            rw [show
              encryptGlobalStep outerQuery
                  [(⟨.alice, .key key⟩ :
                    FlatAnswer (signatures G) (postDecryptBoundary G))] =
                Sum.inl cipherQuery by rfl]
            simp only
            rw [fullRaw, postRaw]
            simp [CausalApply.driveG, encryptGlobalStep,
              outerQuery, keyQuery, cipherQuery, pathEquation]
          · have postRejected :
                ¬ ((honestSecurityDDS key).flatten.1
                    (prior ++ [outerQuery])).Dom :=
              admitted
            have fullRejected :
                ¬ ((postDecryptDDS key).flatten.1
                    (encryptQueryHistory key prior ++ [keyQuery] ++
                      [cipherQuery])).Dom := by
              intro member
              apply admitted
              apply (encryptQueryHistory_mem_iff key _).mp
              exact pathEquation ▸ member
            by_cases firstMember :
                encryptQueryHistory key prior ++ [keyQuery] ∈
                  (postDecryptDDS key).domain
            · have firstRaw :
                  (postDecryptDDS key).flatten.1
                      (encryptQueryHistory key prior ++ [keyQuery]) =
                    Part.some
                      (⟨.alice, .key key⟩ :
                        FlatAnswer (signatures G)
                          (postDecryptBoundary G)) := by
                have rawMember :
                    ((postDecryptDDS key).flatten.1
                      (encryptQueryHistory key prior ++ [keyQuery])).Dom :=
                  firstMember
                rw [← Part.some_get rawMember]
                congr 1
                dsimp only [DependentDDS.flatten, postDecryptDDS, keyQuery]
                rw [List.getLast_append_singleton]
              rw [CausalApply.driveG]
              rw [show encryptGlobalStep outerQuery [] =
                Sum.inl keyQuery by rfl]
              simp only
              rw [firstRaw]
              simp only [Part.bind_some, List.nil_append]
              rw [CausalApply.driveG]
              rw [show
                encryptGlobalStep outerQuery
                    [(⟨.alice, .key key⟩ :
                      FlatAnswer (signatures G) (postDecryptBoundary G))] =
                  Sum.inl cipherQuery by rfl]
              simp only
              rw [Part.eq_none_iff'.mpr fullRejected,
                Part.eq_none_iff'.mpr postRejected]
              simp
            · have firstRejected :
                  ¬ ((postDecryptDDS key).flatten.1
                      (encryptQueryHistory key prior ++ [keyQuery])).Dom :=
                firstMember
              rw [CausalApply.driveG]
              rw [show encryptGlobalStep outerQuery [] =
                Sum.inl keyQuery by rfl]
              simp only
              rw [Part.eq_none_iff'.mpr firstRejected,
                Part.eq_none_iff'.mpr postRejected]
              simp
  | bob =>
      cases input
      let outerQuery :
          Query (signatures G) (honestSecurityBoundary G) :=
        ⟨.bob, .receive⟩
      let innerQuery :
          Query (signatures G) (postDecryptBoundary G) :=
        ⟨.bob, .receive⟩
      have pathEquation :
          encryptQueryHistory key prior ++ [innerQuery] =
            encryptQueryHistory key (prior ++ [outerQuery]) := by
        simp [outerQuery, innerQuery, encryptQueryHistory,
          encryptQueryPath]
      by_cases admitted :
          prior ++ [outerQuery] ∈ (honestSecurityDDS key).domain
      · have transformedAdmitted :
            encryptQueryHistory key (prior ++ [outerQuery]) ∈
              (postDecryptDDS key).domain :=
          (encryptQueryHistory_mem_iff key _).mpr admitted
        have realAdmitted :
            encryptQueryHistory key prior ++ [innerQuery] ∈
              (postDecryptDDS key).domain :=
          pathEquation.symm ▸ transformedAdmitted
        have ciphertextEquation :
            postDecryptCiphertext?
                (encryptQueryHistory key prior ++ [innerQuery]) =
              (honestMessage? (prior ++ [outerQuery])).map
                fun message => message + key := by
          rw [pathEquation]
          exact postDecryptCiphertext?_encryptQueryHistory key _
        have realRaw :
            (postDecryptDDS key).flatten.1
                (encryptQueryHistory key prior ++ [innerQuery]) =
              Part.some
                (⟨.bob,
                    ((honestMessage? (prior ++ [outerQuery])).map
                        (fun message => message + key)).map
                      fun ciphertext => ciphertext - key⟩ :
                  FlatAnswer (signatures G) (postDecryptBoundary G)) := by
          have rawMember :
              ((postDecryptDDS key).flatten.1
                (encryptQueryHistory key prior ++ [innerQuery])).Dom :=
            realAdmitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, postDecryptDDS, innerQuery]
          rw [List.getLast_append_singleton, ciphertextEquation]
        have postRaw :
            (honestSecurityDDS key).flatten.1
                (prior ++ [outerQuery]) =
              Part.some
                (⟨.bob, honestMessage? (prior ++ [outerQuery])⟩ :
                  FlatAnswer (signatures G)
                    (honestSecurityBoundary G)) := by
          have rawMember :
              ((honestSecurityDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
            admitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, honestSecurityDDS, outerQuery]
          rw [List.getLast_append_singleton]
        rw [CausalApply.driveG]
        rw [show encryptGlobalStep outerQuery [] =
          Sum.inl innerQuery by rfl]
        simp only
        rw [realRaw, postRaw]
        simp [CausalApply.driveG, encryptGlobalStep,
          outerQuery, innerQuery, pathEquation, Option.map_map,
          Function.comp_def]
      · have transformedRejected :
            ¬ (encryptQueryHistory key (prior ++ [outerQuery]) ∈
              (postDecryptDDS key).domain) := fun member =>
          admitted ((encryptQueryHistory_mem_iff key _).mp member)
        have realRejected :
            ¬ ((postDecryptDDS key).flatten.1
                (encryptQueryHistory key prior ++ [innerQuery])).Dom :=
          fun member => transformedRejected (pathEquation ▸ member)
        have postRejected :
            ¬ ((honestSecurityDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
          admitted
        rw [CausalApply.driveG]
        rw [show encryptGlobalStep outerQuery [] =
          Sum.inl innerQuery by rfl]
        simp only
        rw [Part.eq_none_iff'.mpr realRejected,
          Part.eq_none_iff'.mpr postRejected]
        simp
  | eve =>
      cases input
      let outerQuery :
          Query (signatures G) (honestSecurityBoundary G) :=
        ⟨.eve, .readCipher⟩
      let innerQuery :
          Query (signatures G) (postDecryptBoundary G) :=
        ⟨.eve, .readCipher⟩
      have pathEquation :
          encryptQueryHistory key prior ++ [innerQuery] =
            encryptQueryHistory key (prior ++ [outerQuery]) := by
        simp [outerQuery, innerQuery, encryptQueryHistory,
          encryptQueryPath]
      by_cases admitted :
          prior ++ [outerQuery] ∈ (honestSecurityDDS key).domain
      · have transformedAdmitted :
            encryptQueryHistory key (prior ++ [outerQuery]) ∈
              (postDecryptDDS key).domain :=
          (encryptQueryHistory_mem_iff key _).mpr admitted
        have realAdmitted :
            encryptQueryHistory key prior ++ [innerQuery] ∈
              (postDecryptDDS key).domain :=
          pathEquation.symm ▸ transformedAdmitted
        have ciphertextEquation :
            postDecryptCiphertext?
                (encryptQueryHistory key prior ++ [innerQuery]) =
              (honestMessage? (prior ++ [outerQuery])).map
                fun message => message + key := by
          rw [pathEquation]
          exact postDecryptCiphertext?_encryptQueryHistory key _
        have realRaw :
            (postDecryptDDS key).flatten.1
                (encryptQueryHistory key prior ++ [innerQuery]) =
              Part.some
                (⟨.eve,
                    (honestMessage? (prior ++ [outerQuery])).map
                      fun message => message + key⟩ :
                  FlatAnswer (signatures G) (postDecryptBoundary G)) := by
          have rawMember :
              ((postDecryptDDS key).flatten.1
                (encryptQueryHistory key prior ++ [innerQuery])).Dom :=
            realAdmitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, postDecryptDDS, innerQuery]
          rw [List.getLast_append_singleton, ciphertextEquation]
        have postRaw :
            (honestSecurityDDS key).flatten.1
                (prior ++ [outerQuery]) =
              Part.some
                (⟨.eve,
                    (honestMessage? (prior ++ [outerQuery])).map
                      fun message => message + key⟩ :
                  FlatAnswer (signatures G)
                    (honestSecurityBoundary G)) := by
          have rawMember :
              ((honestSecurityDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
            admitted
          rw [← Part.some_get rawMember]
          congr 1
          dsimp only [DependentDDS.flatten, honestSecurityDDS, outerQuery]
          rw [List.getLast_append_singleton]
        rw [CausalApply.driveG]
        rw [show encryptGlobalStep outerQuery [] =
          Sum.inl innerQuery by rfl]
        simp only
        rw [realRaw, postRaw]
        simp [CausalApply.driveG, encryptGlobalStep,
          outerQuery, innerQuery, pathEquation]
      · have transformedRejected :
            ¬ (encryptQueryHistory key (prior ++ [outerQuery]) ∈
              (postDecryptDDS key).domain) := fun member =>
          admitted ((encryptQueryHistory_mem_iff key _).mp member)
        have realRejected :
            ¬ ((postDecryptDDS key).flatten.1
                (encryptQueryHistory key prior ++ [innerQuery])).Dom :=
          fun member => transformedRejected (pathEquation ▸ member)
        have postRejected :
            ¬ ((honestSecurityDDS key).flatten.1
                (prior ++ [outerQuery])).Dom :=
          admitted
        rw [CausalApply.driveG]
        rw [show encryptGlobalStep outerQuery [] =
          Sum.inl innerQuery by rfl]
        simp only
        rw [Part.eq_none_iff'.mpr realRejected,
          Part.eq_none_iff'.mpr postRejected]
        simp

/-- The fixed-fuel whole-history receipt for the Alice frame. -/
private theorem encrypt_driveOuter_eq (key : G) :
    ∀ (prior :
        List (Query (signatures G) (honestSecurityBoundary G)))
      (queries :
        List (Query (signatures G) (honestSecurityBoundary G))),
      CausalApply.driveOuter encryptGlobalStep
          (postDecryptDDS key).flatten.1 3
          (encryptQueryHistory key prior) queries =
        (CausalApply.driveOuter
            (PFunConverter.DDC.simpleStep id id)
            (honestSecurityDDS key).flatten.1 2 prior queries).map
          (fun result =>
            (result.1, encryptQueryHistory key result.2)) := by
  intro prior queries
  induction queries generalizing prior with
  | nil =>
      simp [CausalApply.driveOuter]
  | cons query rest induction =>
      simp only [CausalApply.driveOuter]
      rw [encrypt_driveG_eq]
      rw [show (2 : Nat) = 0 + 1 + 1 by rfl,
        PFunConverter.DDC.driveG_simpleStep]
      simp only [id_eq, Part.map_bind, Part.bind_map, Part.map_map,
        Function.comp_def]
      rw [induction]
      simp only [Part.map_map, Function.comp_def]

/-- The small RS receipt consumed by the typed attachment proof: after
encryption, the flattened intermediate resource is exactly the honest
security DDS. -/
private theorem encrypt_applyG_eq (key : G) :
    CausalApply.applyG encryptGlobalStep (postDecryptDDS key).flatten.1 =
      (honestSecurityDDS key).flatten := by
  apply Subtype.ext
  funext queries
  apply Part.ext
  intro answer
  rw [show
      (CausalApply.applyG encryptGlobalStep
        (postDecryptDDS key).flatten.1).1 =
          CausalApply.applyRaw encryptGlobalStep
            (postDecryptDDS key).flatten.1 from rfl,
    CausalApply.mem_applyRaw]
  constructor
  · rintro ⟨fuel, appliedMember⟩
    rw [CausalApply.mem_applyRawAt_iff] at appliedMember
    obtain ⟨result, outerMember, lastAnswer⟩ := appliedMember
    have count_le :
        ∀ query :
            Query (signatures G) (honestSecurityBoundary G),
          encryptGlobalCount query ≤ 2 := by
      rintro ⟨interface, input⟩
      cases interface <;> cases input <;>
        simp [encryptGlobalCount]
    have normalizedOuter :=
      CausalApply.driveOuter_mem_at_uniform_count_succ
        encryptGlobalStep encryptGlobalCount
        encryptGlobalStep_issues_iff 2 count_le
        (postDecryptDDS key).flatten.1 outerMember
    have normalizedOuter' :
        result ∈
          CausalApply.driveOuter encryptGlobalStep
            (postDecryptDDS key).flatten.1 3
            (encryptQueryHistory key []) queries := by
      simpa [encryptQueryHistory] using normalizedOuter
    rw [encrypt_driveOuter_eq key [] queries] at normalizedOuter'
    rw [Part.mem_map_iff] at normalizedOuter'
    obtain ⟨simpleResult, simpleMember, resultEquation⟩ :=
      normalizedOuter'
    subst result
    have queriesNonempty : queries ≠ [] := by
      intro queriesEmpty
      subst queries
      have resultLength :=
        CausalApply.driveOuter_length
          (PFunConverter.DDC.simpleStep id id)
          (honestSecurityDDS key).flatten.1 2 [] []
          simpleMember
      have resultEmpty : simpleResult.1 = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using resultLength)
      rw [resultEmpty] at lastAnswer
      simp at lastAnswer
    obtain ⟨_, lastOutput⟩ :=
      PFunConverter.DDC.driveOuter_simpleStep_mem_imp
        (id :
          Query (signatures G) (honestSecurityBoundary G) →
            Query (signatures G) (honestSecurityBoundary G))
        (id :
          FlatAnswer (signatures G) (honestSecurityBoundary G) →
            FlatAnswer (signatures G) (honestSecurityBoundary G))
        (honestSecurityDDS key).flatten queries [] simpleMember
    obtain ⟨domainMember, lastOutput⟩ :=
      lastOutput queriesNonempty
    have domainMember' :
        queries ∈ PFunDDS.dom (honestSecurityDDS key).flatten := by
      simpa using domainMember
    have lastOutput' :
        simpleResult.1.getLast? =
          some
            (PFunDDS.output (honestSecurityDDS key).flatten
              queries domainMember') := by
      simpa using lastOutput
    rw [lastAnswer] at lastOutput'
    have answerEquation :
        answer =
          PFunDDS.output (honestSecurityDDS key).flatten
            queries domainMember' :=
      Option.some.inj lastOutput'
    rw [answerEquation]
    exact Part.get_mem _
  · intro answerMember
    have domainMember :
        queries ∈ PFunDDS.dom (honestSecurityDDS key).flatten := by
      rw [PFunDDS.dom_def, PFun.mem_dom]
      exact ⟨answer, answerMember⟩
    have queriesNonempty : queries ≠ [] := by
      intro queriesEmpty
      subst queries
      exact PFunDDS.empty_not_mem (honestSecurityDDS key).flatten
        domainMember
    obtain ⟨answers, simpleMember, lastOutput⟩ :=
      PFunConverter.DDC.driveOuter_simpleStep_of_dom
        (id :
          Query (signatures G) (honestSecurityBoundary G) →
            Query (signatures G) (honestSecurityBoundary G))
        (id :
          FlatAnswer (signatures G) (honestSecurityBoundary G) →
            FlatAnswer (signatures G) (honestSecurityBoundary G))
        (honestSecurityDDS key).flatten queries []
        (Or.inl (by simpa using domainMember))
    have simpleMember' :
        (answers, queries) ∈
          CausalApply.driveOuter
            (PFunConverter.DDC.simpleStep id id)
            (honestSecurityDDS key).flatten.1 2 [] queries := by
      simpa using simpleMember
    have outputEquation :
        PFunDDS.output (honestSecurityDDS key).flatten
            queries domainMember =
          answer :=
      Part.mem_unique (Part.get_mem _) answerMember
    have lastAnswer : answers.getLast? = some answer := by
      rw [lastOutput (by simpa using domainMember) queriesNonempty]
      simpa using congrArg some outputEquation
    have transformedMember :
        (answers, encryptQueryHistory key queries) ∈
          CausalApply.driveOuter encryptGlobalStep
            (postDecryptDDS key).flatten.1 3
            (encryptQueryHistory key []) queries := by
      rw [encrypt_driveOuter_eq key [] queries, Part.mem_map_iff]
      exact ⟨(answers, queries), simpleMember', rfl⟩
    refine ⟨3, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    exact ⟨(answers, encryptQueryHistory key queries),
      by simpa [encryptQueryHistory] using transformedMember,
      lastAnswer⟩

/-- Construction-local U07 instance for the Alice frame. -/
private theorem encrypt_framed_apply_eq_global (key : G) :
    PFunConverter.apply
        (TypedFraming.framedConverter (.alice : Interface)
          (postDecryptBoundary G) encrypt.converter rfl).val
        (postDecryptDDS key).flatten =
      PFunConverter.apply encryptGlobalProtocol
        (postDecryptDDS key).flatten := by
  unfold encryptGlobalProtocol
  exact TypedFraming.apply_framed_ofStep_eq_apply_ofStep
    (.alice : Interface) (postDecryptBoundary G) encrypt.converter rfl
    encryptStep (fun _ => 2) rfl
    encryptGlobalStep encryptGlobalCount encryptGlobalStep_issues_iff
    (by
      rintro ⟨queryInterface, input⟩ same
      change queryInterface = Interface.alice at same
      subst queryInterface
      cases input
      intro localAnswers
      rcases localAnswers with _ | ⟨keyAnswer, _ | ⟨cipherAnswer, rest⟩⟩
      · rfl
      · cases keyAnswer <;> rfl
      · cases keyAnswer <;> cases cipherAnswer <;> rfl)
    (by
      rintro ⟨queryInterface, input⟩ same
      change queryInterface = Interface.alice at same
      subst queryInterface
      cases input
      rfl)
    (by
      rintro ⟨queryInterface, input⟩ different
      cases queryInterface with
      | alice => exact absurd rfl different
      | bob => cases input; rfl
      | eve => cases input; rfl)
    (by
      rintro ⟨queryInterface, input⟩ different ⟨answerInterface, output⟩
        sameTag
      change answerInterface = queryInterface at sameTag
      subst answerInterface
      cases queryInterface with
      | alice => exact absurd rfl different
      | bob => cases input; rfl
      | eve => cases input; rfl)
    (by
      rintro ⟨queryInterface, input⟩ different
      cases queryInterface with
      | alice => exact absurd rfl different
      | bob => rfl
      | eve => rfl)
    (postDecryptDDS key).flatten (postDecryptDDS key).flatten_tag_faithful

private theorem encrypt_attach_eq (key : G) :
    (postDecryptDDS key).attach .alice encrypt.converter rfl =
      honestSecurityDDS key := by
  apply DependentDDS.flatten_injective
  rw [DependentDDS.flatten_attach_eq_apply_framed]
  rw [encrypt_framed_apply_eq_global]
  unfold encryptGlobalProtocol
  rw [PFunConverter.ProtocolFn.apply_ofStep_eq_applyG
    encryptGlobalStep encryptGlobalCount encryptGlobalStep_issues_iff]
  exact encrypt_applyG_eq key

private theorem idealSubmissionWeight_simulatorQueryMap
    (query : Query (signatures G) (securityBoundary G)) :
    idealSubmissionWeight (simulatorQueryMap query) =
      securitySubmissionWeight query := by
  rcases query with ⟨interface, input⟩
  cases interface <;> cases input <;> rfl

private theorem countWith_simulatorQueryMap
    (history : List (Query (signatures G) (securityBoundary G))) :
    countWith idealSubmissionWeight (history.map simulatorQueryMap) =
      countWith securitySubmissionWeight history := by
  induction history with
  | nil => rfl
  | cons query history induction =>
      simp only [List.map_cons, countWith, induction,
        idealSubmissionWeight_simulatorQueryMap]

private theorem idealMessage?_simulatorQueryMap
    (history : List (Query (signatures G) (securityBoundary G))) :
    idealMessage? (history.map simulatorQueryMap) =
      securityMessage? history := by
  unfold idealMessage? securityMessage?
  have loop (current : Option G) :
      List.foldl
          (fun current query =>
            match query with
            | ⟨.alice, .send message⟩ => some message
            | _ => current)
          current (history.map simulatorQueryMap) =
        List.foldl
          (fun current query =>
            match query with
            | ⟨.alice, .send message⟩ => some message
            | _ => current)
          current history := by
    induction history generalizing current with
    | nil => rfl
    | cons query history induction =>
        rcases query with ⟨interface, input⟩
        cases interface <;> cases input <;>
          simp only [List.map_cons, List.foldl_cons, simulatorQueryMap] <;>
          exact induction _
  exact loop none

private def realSecurityDDS (key : G) :
    DependentDDS (signatures G) (securityBoundary G) where
  domain := {history |
    history ≠ [] ∧ countWith securitySubmissionWeight history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact (countWith_le_append securitySubmissionWeight left suffix).trans
      rightMember.2
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ => securityMessage? history
    | ⟨.eve, .readCipher⟩ =>
        (securityMessage? history).map fun message => message + key

private def simulatedSecurityDDS (ciphertext : G) :
    DependentDDS (signatures G) (securityBoundary G) where
  domain := {history |
    history ≠ [] ∧ countWith securitySubmissionWeight history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact (countWith_le_append securitySubmissionWeight left suffix).trans
      rightMember.2
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .send _⟩ => .ack
    | ⟨.bob, .receive⟩ => securityMessage? history
    | ⟨.eve, .readCipher⟩ =>
        (securityMessage? history).map fun _ => ciphertext

/-- Identity-shaped recoding between the honest post-protocol boundary and
the simulator-side security boundary.  The two boundaries carry
definitionally equal codes at every interface; only the boundary functions
differ as terms. -/
private def honestToSecurityQuery :
    Query (signatures G) (honestSecurityBoundary G) →
      Query (signatures G) (securityBoundary G)
  | ⟨.alice, input⟩ => ⟨.alice, input⟩
  | ⟨.bob, input⟩ => ⟨.bob, input⟩
  | ⟨.eve, input⟩ => ⟨.eve, input⟩

private theorem encodeQuery_honestToSecurityQuery
    (query : Query (signatures G) (honestSecurityBoundary G)) :
    encodeQuery (honestToSecurityQuery query) = encodeQuery query := by
  rcases query with ⟨interface, input⟩
  cases interface <;> rfl

private theorem encode_map_honestToSecurityQuery
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    (history.map honestToSecurityQuery).map encodeQuery =
      history.map encodeQuery := by
  induction history with
  | nil => rfl
  | cons query history induction =>
      simp only [List.map_cons, induction,
        encodeQuery_honestToSecurityQuery]

private theorem securitySubmissionWeight_honestToSecurityQuery
    (query : Query (signatures G) (honestSecurityBoundary G)) :
    securitySubmissionWeight (honestToSecurityQuery query) =
      honestSubmissionWeight query := by
  rcases query with ⟨interface, input⟩
  cases interface <;> cases input <;> rfl

private theorem countWith_honestToSecurityQuery
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    countWith securitySubmissionWeight
        (history.map honestToSecurityQuery) =
      countWith honestSubmissionWeight history := by
  induction history with
  | nil => rfl
  | cons query history induction =>
      simp only [List.map_cons, countWith, induction,
        securitySubmissionWeight_honestToSecurityQuery]

private theorem securityMessage?_map_honestToSecurityQuery
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    securityMessage? (history.map honestToSecurityQuery) =
      honestMessage? history := by
  unfold securityMessage? honestMessage?
  have loop (current : Option G) :
      List.foldl
          (fun current query =>
            match query with
            | ⟨.alice, .send message⟩ => some message
            | _ => current)
          current (history.map honestToSecurityQuery) =
        List.foldl
          (fun current query =>
            match query with
            | ⟨.alice, .send message⟩ => some message
            | _ => current)
          current history := by
    induction history generalizing current with
    | nil => rfl
    | cons query history induction =>
        rcases query with ⟨interface, input⟩
        cases interface <;> cases input <;>
          simp only [List.map_cons, List.foldl_cons,
            honestToSecurityQuery] <;>
          exact induction _
  exact loop none

private theorem mem_map_honestToSecurityQuery_iff (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    history.map honestToSecurityQuery ∈ (realSecurityDDS key).domain ↔
      history ∈ (honestSecurityDDS key).domain := by
  change
    (history.map honestToSecurityQuery ≠ [] ∧
      countWith securitySubmissionWeight
        (history.map honestToSecurityQuery) ≤ 1) ↔
    (history ≠ [] ∧ countWith honestSubmissionWeight history ≤ 1)
  rw [countWith_honestToSecurityQuery]
  simp

/-- The behavioral core of the boundary transport: the honest DDS and the
security-boundary DDS have identical ambient-encoded behavior along the
identity-shaped recoding. -/
private theorem honest_security_flatten_encode_eq (key : G)
    (history : List (Query (signatures G) (honestSecurityBoundary G))) :
    ((honestSecurityDDS key).flatten.1 history).map encodeAnswer =
      ((realSecurityDDS key).flatten.1
        (history.map honestToSecurityQuery)).map encodeAnswer := by
  apply Part.ext'
  · exact (mem_map_honestToSecurityQuery_iff key history).symm
  · intro leftMember rightMember
    have historyNonempty : history ≠ [] :=
      DependentDDS.history_ne_nil (honestSecurityDDS key) leftMember
    have lastMap :
        (history.map honestToSecurityQuery).getLast
            (by simpa using historyNonempty) =
          honestToSecurityQuery (history.getLast historyNonempty) :=
      List.getLast_map _
    generalize lastEquation :
      history.getLast historyNonempty = lastQuery
    rcases lastQuery with ⟨interface, input⟩
    cases interface <;> cases input <;>
      simp [DependentDDS.flatten, honestSecurityDDS, realSecurityDDS,
        securityMessage?_map_honestToSecurityQuery, encodeAnswer]
    all_goals rw [lastMap, lastEquation]
    all_goals exact ⟨rfl, HEq.rfl⟩

/-- The honest post-protocol resource is, in the boundary-independent
ambient chart, exactly the security-boundary real resource. -/
private theorem honest_security_embed_eq (key : G) :
    (honestSecurityDDS key).embed = (realSecurityDDS key).embed := by
  apply Subtype.ext
  funext ambient
  by_cases conforms :
      HistoryConforms (honestSecurityBoundary G) ambient
  · obtain ⟨typed, rfl⟩ :
        ∃ typed :
          List (Query (signatures G) (honestSecurityBoundary G)),
          typed.map encodeQuery = ambient :=
      ⟨decodeHistory _ ambient conforms,
        encode_history_decode _ ambient conforms⟩
    calc
      (honestSecurityDDS key).embed.1 (typed.map encodeQuery)
          = ((honestSecurityDDS key).flatten.1 typed).map encodeAnswer :=
            DependentDDS.embed_apply_encoded _ typed
      _ = ((realSecurityDDS key).flatten.1
            (typed.map honestToSecurityQuery)).map encodeAnswer :=
          honest_security_flatten_encode_eq key typed
      _ = (realSecurityDDS key).embed.1
            ((typed.map honestToSecurityQuery).map encodeQuery) :=
          (DependentDDS.embed_apply_encoded _ _).symm
      _ = (realSecurityDDS key).embed.1 (typed.map encodeQuery) := by
          rw [encode_map_honestToSecurityQuery]
  · have conformsSecurity :
        ¬ HistoryConforms (securityBoundary G) ambient := by
      intro securityConforms
      apply conforms
      intro query member
      have componentConforms := securityConforms query member
      rcases query with ⟨interface, payload⟩
      cases interface <;> exact componentConforms
    apply Part.ext'
    · constructor
      · rintro ⟨historyConforms, _⟩
        exact absurd historyConforms conforms
      · rintro ⟨historyConforms, _⟩
        exact absurd historyConforms conformsSecurity
    · rintro ⟨historyConforms, _⟩ _
      exact absurd historyConforms conforms

private noncomputable def securityObservedMessage?
    (history : List (Query (signatures G) (securityBoundary G))) : Option G :=
  securityMessage?
    (PFunDDS.keptPrefix (realSecurityDDS (0 : G)).flatten history)

private noncomputable def securityReindex
    (history : List (Query (signatures G) (securityBoundary G))) (key : G) : G :=
  match securityObservedMessage? history with
  | none => key
  | some message => message + key

private theorem securityReindex_bijective
    (history : List (Query (signatures G) (securityBoundary G))) :
    Function.Bijective (securityReindex history) := by
  unfold securityReindex
  generalize securityObservedMessage? history = observed
  cases observed with
  | none => exact Function.bijective_id
  | some message =>
    exact ⟨fun _ _ equal => add_left_cancel equal,
      fun ciphertext => ⟨-message + ciphertext, by simp⟩⟩

private theorem securityObservedMessage?_eq_of_prefix
    {left right : List (Query (signatures G) (securityBoundary G))}
    (isPrefix : left <+: right)
    {message : G}
    (leftMessage :
      securityMessage?
        (PFunDDS.keptPrefix
          (realSecurityDDS (0 : G)).flatten left) = some message) :
    securityObservedMessage? right = some message := by
  unfold securityObservedMessage?
  apply securityMessage?_eq_of_prefix_of_count_le_one
    (PFunDDS.keptPrefix_mono (realSecurityDDS (0 : G)).flatten isPrefix) _ leftMessage
  rcases PFunDDS.keptPrefix_mem_or
      (realSecurityDDS (0 : G)).flatten right with member | empty
  · exact member.2
  · simp [empty, countWith]

private theorem security_completion_apply_eq
    (full historyPrefix :
      List (Query (signatures G) (securityBoundary G)))
    (isPrefix : historyPrefix <+: full) (key : G) :
    (PFunDDS.fullyDefined (realSecurityDDS key).flatten).1 historyPrefix =
      (PFunDDS.fullyDefined
        (simulatedSecurityDDS
          (securityReindex full key)).flatten).1 historyPrefix := by
  classical
  apply Part.ext'
  · rfl
  · intro leftMember rightMember
    change
      PFunDDS.output
          (PFunDDS.fullyDefined (realSecurityDDS key).flatten)
          historyPrefix leftMember =
        PFunDDS.output
          (PFunDDS.fullyDefined
            (simulatedSecurityDDS
              (securityReindex full key)).flatten)
          historyPrefix rightMember
    rw [PFunDDS.output_fullyDefined, PFunDDS.output_fullyDefined]
    have keptEqual :
        PFunDDS.keptPrefix (realSecurityDDS key).flatten
            historyPrefix.dropLast =
          PFunDDS.keptPrefix
            (simulatedSecurityDDS
              (securityReindex full key)).flatten
            historyPrefix.dropLast := by
      rfl
    rw [keptEqual]
    have lastEqual :
        historyPrefix.getLast leftMember =
          historyPrefix.getLast rightMember := rfl
    rw [lastEqual]
    let candidate :=
      PFunDDS.keptPrefix
          (simulatedSecurityDDS
            (securityReindex full key)).flatten
          historyPrefix.dropLast ++
        [historyPrefix.getLast rightMember]
    change
      (if accepted : candidate ∈ PFunDDS.dom (realSecurityDDS key).flatten then
        some
          (PFunDDS.output (realSecurityDDS key).flatten
            candidate accepted)
      else none) =
      (if accepted :
          candidate ∈ PFunDDS.dom
            (simulatedSecurityDDS (securityReindex full key)).flatten then
        some
          (PFunDDS.output
            (simulatedSecurityDDS (securityReindex full key)).flatten
            candidate accepted)
      else none)
    by_cases accepted :
        candidate ∈ PFunDDS.dom (realSecurityDDS key).flatten
    · have simulatedAccepted :
          candidate ∈ PFunDDS.dom
            (simulatedSecurityDDS (securityReindex full key)).flatten :=
        accepted
      rw [dif_pos accepted, dif_pos simulatedAccepted]
      congr 1
      simp [PFunDDS.output, DependentDDS.flatten, realSecurityDDS,
        simulatedSecurityDDS]
      generalize lastEquation :
        candidate.getLast (by simp [candidate]) = lastQuery
      rcases lastQuery with ⟨interface, input⟩
      cases interface <;> cases input <;>
        simp
      generalize messageEquation :
        securityMessage? candidate = currentMessage
      cases currentMessage with
      | none => rfl
      | some message =>
          have keptPrefixZero :
              PFunDDS.keptPrefix
                  (realSecurityDDS (0 : G)).flatten historyPrefix =
                candidate := by
            rw [← List.dropLast_append_getLast
              (show historyPrefix ≠ [] from rightMember)]
            unfold PFunDDS.keptPrefix candidate
            rw [List.foldl_append]
            simp only [List.foldl_cons, List.foldl_nil]
            rw [if_pos]
            · rfl
            · exact accepted
          have observedMessage :
              securityObservedMessage? full = some message :=
            securityObservedMessage?_eq_of_prefix isPrefix
              (by rw [keptPrefixZero, messageEquation])
          simp [securityReindex, observedMessage]
    · have simulatedRejected :
          candidate ∉ PFunDDS.dom
            (simulatedSecurityDDS (securityReindex full key)).flatten :=
        accepted
      rw [dif_neg accepted, dif_neg simulatedRejected]

private theorem security_observable_atom_iff
    (transcript : List
      (Query (signatures G) (securityBoundary G) ×
        Option (FlatAnswer (signatures G) (securityBoundary G))))
    (key : G) :
    (∀ index (indexLess : index < transcript.length),
        (PFunDDS.fullyDefined (realSecurityDDS key).flatten).1
            (PFunDDS.transcriptInputs (transcript.take (index + 1))) =
          Part.some transcript[index].2) ↔
      ∀ index (indexLess : index < transcript.length),
        (PFunDDS.fullyDefined
            (simulatedSecurityDDS
              (securityReindex
                (PFunDDS.transcriptInputs transcript) key)).flatten).1
            (PFunDDS.transcriptInputs (transcript.take (index + 1))) =
          Part.some transcript[index].2 := by
  have inputPrefix (index : Nat) :
      PFunDDS.transcriptInputs (transcript.take (index + 1)) <+:
        PFunDDS.transcriptInputs transcript := by
    unfold PFunDDS.transcriptInputs
    exact List.IsPrefix.map Prod.fst (List.take_prefix (index + 1) transcript)
  constructor
  · intro realAtom index indexLess
    rw [← security_completion_apply_eq
      (PFunDDS.transcriptInputs transcript)
      (PFunDDS.transcriptInputs (transcript.take (index + 1)))
      (inputPrefix index) key]
    exact realAtom index indexLess
  · intro simulatedAtom index indexLess
    rw [security_completion_apply_eq
      (PFunDDS.transcriptInputs transcript)
      (PFunDDS.transcriptInputs (transcript.take (index + 1)))
      (inputPrefix index) key]
    exact simulatedAtom index indexLess

private noncomputable def realSecurityLaw :
    DependentPDS.Prob (signatures G) (securityBoundary G) :=
  ⟨Dist.fTransform realSecurityDDS (Dist.uniform G),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

private noncomputable def simulatedSecurityLaw :
    DependentPDS.Prob (signatures G) (securityBoundary G) :=
  ⟨Dist.fTransform simulatedSecurityDDS (Dist.uniform G),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The honest post-protocol law, presented at the honest boundary. -/
private noncomputable def honestSecurityLaw :
    DependentPDS.Prob (signatures G) (honestSecurityBoundary G) :=
  ⟨Dist.fTransform honestSecurityDDS (Dist.uniform G),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- E01.2b.3c: applying Bob's decryption and then Alice's encryption to the
real law is exactly the honest security law. -/
private theorem realLaw_attach_chain_eq :
    ((realLaw (G := G)).attach .bob decrypt.converter rfl).attach
        .alice encrypt.converter rfl =
      honestSecurityLaw (G := G) := by
  apply Subtype.ext
  unfold DependentPDS.Prob.attach DependentPDS.attach realLaw
    honestSecurityLaw
  change
    Dist.fTransform
        (fun deterministic =>
          deterministic.attach .alice encrypt.converter rfl)
        (Dist.fTransform
          (fun deterministic =>
            deterministic.attach .bob decrypt.converter rfl)
          (Dist.fTransform realDDS (Dist.uniform G))) =
      Dist.fTransform honestSecurityDDS (Dist.uniform G)
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  apply congrArg (fun function =>
    Dist.fTransform function (Dist.uniform G))
  funext key
  change
    ((realDDS key).attach .bob decrypt.converter rfl).attach
        .alice encrypt.converter rfl = honestSecurityDDS key
  rw [decrypt_attach_eq]
  exact encrypt_attach_eq key

/-- E01.2b.3d, transport half: across `security_boundaries_agree` the honest
law is the security-boundary real law. -/
private theorem honest_security_law_heq :
    HEq (honestSecurityLaw (G := G)) (realSecurityLaw (G := G)) := by
  apply DependentPDS.Prob.heq_of_boundary_eq_of_val_heq
    security_boundaries_agree
  apply DependentPDS.heq_of_boundary_eq_of_embed_eq
    security_boundaries_agree
  show
    DependentPDS.embed
        (Dist.fTransform honestSecurityDDS (Dist.uniform G)) =
      DependentPDS.embed
        (Dist.fTransform realSecurityDDS (Dist.uniform G))
  unfold DependentPDS.embed
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg (fun function =>
    Dist.fTransform function (Dist.uniform G))
    (funext fun key => honest_security_embed_eq key)

private theorem security_flatten_observableBehaviorEq :
    ObservableBehaviorEq
      (DependentPDS.flatten (realSecurityLaw (G := G)).val)
      (DependentPDS.flatten (simulatedSecurityLaw (G := G)).val) := by
  funext transcript
  unfold observableBehavior DependentPDS.flatten realSecurityLaw
    simulatedSecurityLaw
  rw [Dist.mass_fTransform, Dist.mass_fTransform,
    Dist.mass_fTransform, Dist.mass_fTransform]
  let simulatedAtom : G → Prop := fun ciphertext =>
    ∀ index (indexLess : index < transcript.length),
      (PFunDDS.fullyDefined
          (simulatedSecurityDDS ciphertext).flatten).1
          (PFunDDS.transcriptInputs (transcript.take (index + 1))) =
        Part.some transcript[index].2
  calc
    (Dist.uniform G).mass
        (fun key =>
          ∀ index (indexLess : index < transcript.length),
            (PFunDDS.fullyDefined (realSecurityDDS key).flatten).1
                (PFunDDS.transcriptInputs
                  (transcript.take (index + 1))) =
              Part.some transcript[index].2) =
      (Dist.uniform G).mass
        (fun key =>
          simulatedAtom
            (securityReindex
              (PFunDDS.transcriptInputs transcript) key)) := by
        apply Dist.mass_congr
        intro key
        simpa [simulatedAtom] using
          (security_observable_atom_iff transcript key)
    _ =
        (Dist.fTransform
          (securityReindex (PFunDDS.transcriptInputs transcript))
          (Dist.uniform G)).mass simulatedAtom := by
      rw [Dist.mass_fTransform]
    _ = (Dist.uniform G).mass simulatedAtom := by
      rw [Dist.fTransform_bijection_uniform _
        (securityReindex_bijective
          (PFunDDS.transcriptInputs transcript))]
    _ = _ := rfl

private theorem realSecurityLaw_eq_simulatedSecurityLaw :
    DependentRandomSystem.ofProb (realSecurityLaw (G := G)) =
      DependentRandomSystem.ofProb (simulatedSecurityLaw (G := G)) := by
  let realFlattened := (realSecurityLaw (G := G)).flatten
  let simulatedFlattened := (simulatedSecurityLaw (G := G)).flatten
  have transcriptEquivalent :
      Equivalent realFlattened.val simulatedFlattened.val := by
    apply (behavior_equivalent_iff_transcript_equivalent
      realFlattened simulatedFlattened).mp
    exact security_flatten_observableBehaviorEq (G := G)
  apply DependentRandomSystem.ofProb_eq_of_flatten_equivalent
  exact strict_equivalent_of_equivalent
    realFlattened.val simulatedFlattened.val
    realFlattened.property simulatedFlattened.property transcriptEquivalent

private theorem simulator_attach_eq (ciphertext : G) :
    (idealDDS ciphertext).attach .eve simulator.converter rfl =
      simulatedSecurityDDS ciphertext := by
  apply DependentDDS.flatten_injective
  have receipt :=
    DependentDDS.flatten_attach_ofFunctions
      (Interface.eve) (idealBoundary G)
      ((fun input => match input with
        | EveRealIn.readCipher => EveIdealIn.sampleCipher) :
        (signatures G).input Code.realEve →
          (signatures G).input Code.idealEve)
      id rfl (simulatorQueryMap (G := G)) (simulatorAnswerMap (G := G))
      (by
        rintro ⟨queryInterface, input⟩ same
        change queryInterface = Interface.eve at same
        subst queryInterface
        cases input
        rfl)
      (by
        rintro ⟨queryInterface, input⟩ different
        cases queryInterface with
        | alice => rfl
        | bob => rfl
        | eve => exact absurd rfl different)
      (by
        rintro ⟨answerInterface, output⟩ same
        change answerInterface = Interface.eve at same
        subst answerInterface
        rfl)
      (by
        rintro ⟨answerInterface, output⟩ different
        cases answerInterface with
        | alice => rfl
        | bob => rfl
        | eve => exact absurd rfl different)
      (idealDDS ciphertext)
  refine receipt.trans ?_
  show
    PFunConverter.apply
        (PFunConverter.simpleFn (simulatorQueryMap (G := G))
          (simulatorAnswerMap (G := G)))
        (idealDDS ciphertext).flatten =
      (simulatedSecurityDDS ciphertext).flatten
  rw [PFunConverter.ProtocolFn.apply_simpleFn_eq_simple_apply]
  apply Subtype.ext
  funext history
  rw [PFunConverter.DDC.simple_apply]
  apply Part.ext'
  · simp [DependentDDS.flatten, idealDDS, simulatedSecurityDDS,
      countWith_simulatorQueryMap]
  · intro leftMember rightMember
    have historyNonempty : history ≠ [] :=
      DependentDDS.history_ne_nil
        (simulatedSecurityDDS ciphertext) rightMember
    have lastMap :
        (history.map simulatorQueryMap).getLast
            (by simpa using historyNonempty) =
          simulatorQueryMap (history.getLast historyNonempty) :=
      List.getLast_map _
    generalize lastEquation :
      history.getLast historyNonempty = lastQuery
    rcases lastQuery with ⟨interface, input⟩
    cases interface <;> cases input <;>
      simp [DependentDDS.flatten, idealDDS, simulatedSecurityDDS,
        idealMessage?_simulatorQueryMap, simulatorAnswerMap]
    all_goals rw [lastMap, lastEquation]
    all_goals rfl

private theorem idealLaw_attach_simulator_eq :
    (idealLaw (G := G)).attach .eve simulator.converter rfl =
      simulatedSecurityLaw (G := G) := by
  apply Subtype.ext
  unfold DependentPDS.Prob.attach DependentPDS.attach idealLaw
    simulatedSecurityLaw
  change
    Dist.fTransform
        (fun deterministic =>
          deterministic.attach .eve simulator.converter rfl)
        (Dist.fTransform idealDDS (Dist.uniform G)) =
      Dist.fTransform simulatedSecurityDDS (Dist.uniform G)
  rw [Dist.fTransform_comp]
  apply congrArg (fun function =>
    Dist.fTransform function (Dist.uniform G))
  funext ciphertext
  exact simulator_attach_eq ciphertext

private theorem availability_eq_of_security_eq
    (security :
      otpProtocol (G := G) • otpAssumedResource (G := G) =
        simulatorProtocol (G := G) • secureChannelResource (G := G)) :
    otpProtocol (G := G) •
        (bottom (G := G) • otpAssumedResource (G := G)) =
      bottom (G := G) • secureChannelResource (G := G) := by
  have simulatorMismatch :
      simulator.act (otpAssumedResource (G := G)) =
        otpAssumedResource (G := G) := by
    unfold otpAssumedResource
    apply Primitive.act_of_not_matches
    change ¬Code.realEve = Code.idealEve
    decide
  simp only [bottom, otpProtocol, mul_smul,
    primitive_mul_single_smul]
  rw [simulatorMismatch]
  rw [decrypt.act_comm (by decide : Interface.bob ≠ Interface.eve)
    blockRealEve]
  rw [encrypt.act_comm (by decide : Interface.alice ≠ Interface.eve)
    blockRealEve]
  simpa only [otpProtocol, simulatorProtocol, mul_smul,
    primitive_mul_single_smul] using congrArg blockRealEve.act security

/-! ## Final construction statements

The primary statement is the LiuMau20 §2.4 Definition 1 specification family
`otp_constructs_for_adversary_structure`; MauRen11's fixed-`Z` Definition 3
judgment `otp_securely_constructs` is derived from it and kept verbatim as the
receipt that the specification form loses nothing. -/

/-- The simulator leaf of the construction: the honest encryption/decryption
protocol over the assumed resource is *equal* to Eve's simulator over the
secure channel.  Everything probabilistic in the OTP argument lives here; both
final statements are converter algebra over this one equation. -/
private theorem otp_simulator_leaf :
    otpProtocol (G := G) • otpAssumedResource (G := G) =
      simulatorProtocol (G := G) • secureChannelResource (G := G) := by
  rw [otpProtocol_smul_eq_realLaw_attachments,
    simulatorProtocol_smul_eq_idealLaw_attachment]
  rw [Resource.mk.injEq]
  refine ⟨security_boundaries_agree (G := G), ?_⟩
  have honestLaw :
      HEq
        (((realLaw (G := G)).attach .bob decrypt.converter rfl).attach
          .alice encrypt.converter rfl)
        (realSecurityLaw (G := G)) :=
    (heq_of_eq (realLaw_attach_chain_eq (G := G))).trans
      (honest_security_law_heq (G := G))
  have honestSystem :
      HEq
        (DependentRandomSystem.ofProb
          (((realLaw (G := G)).attach .bob decrypt.converter rfl).attach
            .alice encrypt.converter rfl))
        (DependentRandomSystem.ofProb
          (realSecurityLaw (G := G))) :=
    DependentRandomSystem.of_prob_heq_of_boundary_eq
      (security_boundaries_agree (G := G)) honestLaw
  have idealSystem :
      DependentRandomSystem.ofProb
          ((idealLaw (G := G)).attach .eve simulator.converter rfl) =
        DependentRandomSystem.ofProb
          (simulatedSecurityLaw (G := G)) :=
    congrArg DependentRandomSystem.ofProb
      (idealLaw_attach_simulator_eq (G := G))
  have normalizedTail :
      DependentRandomSystem.ofProb (realSecurityLaw (G := G)) =
        DependentRandomSystem.ofProb
          ((idealLaw (G := G)).attach .eve simulator.converter rfl) :=
    (realSecurityLaw_eq_simulatedSecurityLaw (G := G)).trans
      idealSystem.symm
  exact honestSystem.trans (heq_of_eq normalizedTail)

/-- The OTP protocol leaves Eve's interface alone — one of the two
interface-disjointness side conditions MauRen11 Definition 3 leaves
implicit. -/
private theorem otpProtocol_eve : otpProtocol (G := G) .eve = 1 := by
  simp [otpProtocol]

/-- The availability filter acts only at Eve's interface — the other
interface-disjointness side condition. -/
private theorem bottom_eq_one_of_ne (interface : Interface)
    (outside : interface ≠ .eve) : bottom (G := G) interface = 1 := by
  simp [bottom, Pi.mulSingle_eq_of_ne outside]

/-- The admitted simulator class of this construction *is* LiuMau20's joint
dishonest converter class at `{Eve}`: `supportedOn {Eve} ⊤` is exactly the
class generated by the interface converter monoids over the (finite) dishonest
set.  This is what makes the two final statements interchangeable rather than
merely comparable. -/
private theorem otpSimulators_eq_zSub :
    otpSimulators (G := G) =
      zSub (M := Protocol Interface (signatures G)) tupleGamma
        ({.eve} : Set Interface) :=
  (zSub_tupleGamma_eq_supportedOn (Set.finite_singleton _)).symm

/-- **Additive OTP constructs a secure channel, as a specification family**
(CR18 §2.4 in the form of LiuMau20 §2.4 Definition 1 and §2.5).

The protocol tuple is the honest converter at *every* interface — Alice
encrypts, Bob decrypts, and an honest Eve runs the availability filter — and
one construction is asserted per dishonest set `Z` of the adversary structure
`{∅, {Eve}}` this construction tolerates.  Both the assumed and the ideal
specification are `∗Z`-relaxed, so **no simulator is named in the statement**:
at `Z = {Eve}` the relaxation supplies it, and at `Z = ∅` it collapses and the
availability filter survives on the ideal side, which is MauRen11 Definition
3's availability target `⊥ᶻ S`.

This is *exact* set containment, with no metric anywhere in the statement —
strictly more than the `edist … ≤ 0` that the fixed-`Z` judgment below can
say, because the carrier's `edist` is a pseudo-emetric and its zero ball is
not a singleton. -/
theorem otp_constructs_for_adversary_structure :
    ConstructsForAdversaryStructure (singleDishonest Interface.eve)
      (otpProtocol (G := G) * bottom (G := G))
      (fun Z => zStar (M := Protocol Interface (signatures G)) tupleGamma Z
        ({otpAssumedResource (G := G)} : Set (Phi Interface (signatures G))))
      (fun Z => zStar (M := Protocol Interface (signatures G)) tupleGamma Z
        ({patternAttach Zᶜ (bottom (G := G)) • secureChannelResource (G := G)} :
          Set (Phi Interface (signatures G)))) := by
  refine constructsForAdversaryStructure_of_exact_leaves
    (otpProtocol_eve (G := G)) (bottom_eq_one_of_ne (G := G)) ?_ ?_
  · rw [mul_smul]
    exact availability_eq_of_security_eq (otp_simulator_leaf (G := G))
  · refine ⟨simulatorProtocol (G := G), ?_, otp_simulator_leaf (G := G)⟩
    rw [← otpSimulators_eq_zSub (G := G)]
    exact simulatorProtocol_mem_otpSimulators (G := G)

/-- **Additive OTP constructs a secure channel** (CR18 §2.4, MauRen11 §5.1
Definition 3): the honest encryption/decryption protocol constructs the named
secure channel from the named authenticated-channel-plus-key resource with
zero error, with an Eve-supported simulator.

Kept verbatim, but now *derived* from the specification-family statement
above, through the `0`-radius relaxation: this is the receipt that moving to
the general form loses none of the fixed-`Z` content. -/
theorem otp_securely_constructs :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (otpSimulators (G := G)) (otpProtocol (G := G)) (bottom (G := G)) 0
      (otpAssumedResource (G := G)) (secureChannelResource (G := G)) := by
  rw [otpSimulators_eq_zSub (G := G)]
  exact securelyConstructs_of_constructsForAdversaryStructure
    (otpProtocol_eve (G := G)) (bottom_eq_one_of_ne (G := G))
    (constructsForAdversaryStructure_eball_of_exact 0
      (otp_constructs_for_adversary_structure (G := G)))

/-! ### Scheduling receipts

The one-message budget above is a restriction on *multiplicity*, not on
*order*: `countWith` sums a weight over the history and so is invariant under
permutation.  Both worlds are therefore schedule-agnostic, and by
`DependentDDS.rushing_not_excluded` a distinguisher may drive Eve *before* the
honest parties on the same multiset of queries.  Nothing in this endpoint's
statement is weakened by a scheduling assumption we forgot to make. -/

theorem realDDS_scheduleAgnostic (key : G) :
    DependentDDS.ScheduleAgnostic (realDDS (G := G) key) :=
  DependentDDS.scheduleAgnostic_of_perm_invariant
    (fun history => countWith realSubmissionWeight history ≤ 1) rfl
    (fun perm => by simp only [countWith_perm _ perm])

theorem idealDDS_scheduleAgnostic (simulatedCiphertext : G) :
    DependentDDS.ScheduleAgnostic (idealDDS (G := G) simulatedCiphertext) :=
  DependentDDS.scheduleAgnostic_of_perm_invariant
    (fun history => countWith idealSubmissionWeight history ≤ 1) rfl
    (fun perm => by simp only [countWith_perm _ perm])

private theorem postDecryptDDS_scheduleAgnostic (key : G) :
    DependentDDS.ScheduleAgnostic (postDecryptDDS (G := G) key) :=
  DependentDDS.scheduleAgnostic_of_perm_invariant
    (fun history => countWith postDecryptSubmissionWeight history ≤ 1) rfl
    (fun perm => by simp only [countWith_perm _ perm])

/-- The rushing capability, spelled out on the assumed resource: whatever the
honest parties do, Eve may have acted first. -/
theorem realDDS_rushing (key : G)
    (honest adversarial : List (Query (signatures G) (realBoundary G)))
    (member : (honest ++ adversarial) ∈ (realDDS (G := G) key).domain) :
    (adversarial ++ honest) ∈ (realDDS (G := G) key).domain :=
  DependentDDS.rushing_not_excluded (realDDS_scheduleAgnostic key) _ _ member

end

end RandomSystemsCC.Symmetric.OTP
