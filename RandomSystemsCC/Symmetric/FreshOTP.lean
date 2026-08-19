/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.FreshOTPModel
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.StrictContextAdvantage

/-!
# Indexed OTP from a shared fresh-pad resource

The source exposes an authenticated indexed channel together with a shared
uniform function `X → G`.  Distinct indices therefore receive independent
uniform pads, while repeated pad reads at one index remain consistent.  The
public endpoint is the zero-error CC construction of an indexed secure
channel.
-/

namespace RandomSystemsCC.Symmetric.FreshOTP

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Symmetric
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto ENNReal

universe u

section

variable {X G : Type u}
variable [Fintype X] [DecidableEq X] [Nonempty X]
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

/-- Count real Alice submissions at one channel index. -/
private def realSubmissionWeight (index : X)
    (query : Query (signatures X G) (realBoundary X G)) : Nat :=
  match query with
  | ⟨.alice, .sendCipher submittedIndex _⟩ =>
      if submittedIndex = index then 1 else 0
  | _ => 0

/-- Count ideal Alice submissions at one channel index. -/
private def idealSubmissionWeight (index : X)
    (query : Query (signatures X G) (idealBoundary X G)) : Nat :=
  match query with
  | ⟨.alice, .send submittedIndex _⟩ =>
      if submittedIndex = index then 1 else 0
  | _ => 0

/-- The submitted real ciphertext at an index, if any. -/
private def realCiphertext? (index : X)
    (history : List (Query (signatures X G) (realBoundary X G))) :
    Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .sendCipher submittedIndex ciphertext⟩ =>
        if submittedIndex = index then some ciphertext else current
    | _ => current) none

/-- The submitted ideal message at an index, if any. -/
private def idealMessage? (index : X)
    (history : List (Query (signatures X G) (idealBoundary X G))) :
    Option G :=
  history.foldl (fun current query =>
    match query with
    | ⟨.alice, .send submittedIndex message⟩ =>
        if submittedIndex = index then some message else current
    | _ => current) none

/-- Authenticated indexed channel plus a fixed shared pad table.  At most one
Alice submission is admitted per index. -/
def realDDS (pads : X → G) :
    DependentDDS (signatures X G) (realBoundary X G) where
  domain := {history |
    history ≠ [] ∧
      ∀ index, countWith (realSubmissionWeight index) history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, fun index => ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact
      (countWith_le_append (realSubmissionWeight index) left suffix).trans
        (rightMember.2 index)
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .pad index⟩ => .pad (pads index)
    | ⟨.alice, .sendCipher _ _⟩ => .ack
    | ⟨.bob, .pad index⟩ => .pad (pads index)
    | ⟨.bob, .receiveCipher index⟩ =>
        .cipher (realCiphertext? index history)
    | ⟨.eve, .readCipher index⟩ => realCiphertext? index history

/-- The normalized source law samples one uniform shared function `X → G`.
Consequently, distinct fresh indices have independent uniform pads. -/
noncomputable def realLaw :
    DependentPDS.Prob (signatures X G) (realBoundary X G) :=
  ⟨Dist.fTransform realDDS (Dist.uniform (X → G)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named authenticated indexed channel with its shared fresh-pad resource. -/
noncomputable def freshPadAssumedResource :
    Phi Interface (signatures X G) :=
  ⟨realBoundary X G, DependentRandomSystem.ofProb realLaw⟩

/-- Indexed secure channel with a fixed table of simulated ciphertexts.  At
most one Alice submission is admitted per index. -/
def idealDDS (simulatedCiphertexts : X → G) :
    DependentDDS (signatures X G) (idealBoundary X G) where
  domain := {history |
    history ≠ [] ∧
      ∀ index, countWith (idealSubmissionWeight index) history ≤ 1}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, fun index => ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    exact
      (countWith_le_append (idealSubmissionWeight index) left suffix).trans
        (rightMember.2 index)
  output := fun history nonempty _ =>
    match history.getLast nonempty with
    | ⟨.alice, .send _ _⟩ => .ack
    | ⟨.bob, .receive index⟩ => idealMessage? index history
    | ⟨.eve, .sampleCipher index⟩ =>
        (idealMessage? index history).map fun _ =>
          simulatedCiphertexts index

/-- The normalized ideal law samples an independent uniform simulated-
ciphertext table. -/
noncomputable def idealLaw :
    DependentPDS.Prob (signatures X G) (idealBoundary X G) :=
  ⟨Dist.fTransform idealDDS (Dist.uniform (X → G)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Named indexed secure-channel target. -/
noncomputable def indexedSecureChannelResource :
    Phi Interface (signatures X G) :=
  ⟨idealBoundary X G, DependentRandomSystem.ofProb idealLaw⟩

/-- Alice encrypts and Bob decrypts at the supplied channel index. -/
noncomputable def freshOtpProtocol :
    Protocol Interface (signatures X G) :=
  Pi.mulSingle .alice (Gamma.ofPrimitive encrypt) *
    Pi.mulSingle .bob (Gamma.ofPrimitive decrypt)

/-- Availability blocks either Eve port and exposes the same honest indexed
channel boundary in both worlds. -/
noncomputable def bottom :
    Protocol Interface (signatures X G) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive blockIdealEve) *
    Pi.mulSingle .eve (Gamma.ofPrimitive blockRealEve)

/-- The concrete indexed Eve-side simulator tuple. -/
noncomputable def simulatorProtocol :
    Protocol Interface (signatures X G) :=
  Pi.mulSingle .eve (Gamma.ofPrimitive simulator)

/-- Exactly Eve-supported converter tuples are admitted as simulators. -/
noncomputable def freshOtpSimulators :
    Submonoid (Protocol Interface (signatures X G)) :=
  supportedOn ({.eve} : Set Interface) (fun _ => ⊤)

/-! ## Final construction statement -/

/-- **Indexed OTP with a shared fresh-pad resource constructs an indexed
secure channel.**  A fresh index uses a fresh uniform pad; repeated pad access
at that index is consistent, and the channel admits one Alice submission at
each index. -/
theorem fresh_otp_securely_constructs :
    CC.SecurelyConstructs ({.eve} : Set Interface)
      (freshOtpSimulators (X := X) (G := G))
      (freshOtpProtocol (X := X) (G := G))
      (bottom (X := X) (G := G)) 0
      (freshPadAssumedResource (X := X) (G := G))
      (indexedSecureChannelResource (X := X) (G := G)) := by
  sorry

/-! ### Scheduling receipts

The per-index one-message budget restricts *multiplicity*, not *order*:
`countWith` is permutation-invariant, and the budget is a `∀ index` conjunction
of such counts.  Both worlds are schedule-agnostic, so
`DependentDDS.rushing_not_excluded` applies and a rushing Eve is admitted. -/

theorem realDDS_scheduleAgnostic (pads : X → G) :
    DependentDDS.ScheduleAgnostic (realDDS pads) :=
  DependentDDS.scheduleAgnostic_of_perm_invariant
    (fun history => ∀ index, countWith (realSubmissionWeight index) history ≤ 1)
    rfl (fun perm => by simp only [countWith_perm _ perm])

theorem idealDDS_scheduleAgnostic (simulatedCiphertexts : X → G) :
    DependentDDS.ScheduleAgnostic
      (idealDDS simulatedCiphertexts) :=
  DependentDDS.scheduleAgnostic_of_perm_invariant
    (fun history => ∀ index, countWith (idealSubmissionWeight index) history ≤ 1)
    rfl (fun perm => by simp only [countWith_perm _ perm])

end

end RandomSystemsCC.Symmetric.FreshOTP
