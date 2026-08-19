/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Advantage

/-!
# Condition-Based Proofs

Formalization of the condition-based proof technique from Maurer (EUROCRYPT 2002),
"Indistinguishability of Random Systems."

## Overview

The key proof technique in the random systems framework is:
1. Define a monotone condition A (an "event") on transcripts
2. Show that S and T are equivalent conditioned on A (i.e., their
   transcript distributions agree on transcripts satisfying A)
3. Bound the probability that A fails

Then: Adv(S, T) ≤ Pr[¬A | S] (the probability that the condition fails).

## Main Definitions

* `MonotoneCondition` — a predicate on transcripts that is monotone
  (if it holds for a prefix, it holds for the full transcript)
* `PDS.condAdvantage` — the conditional advantage given a condition

## Main Results

* `advantage_le_condition_failure` — the core lemma: if S ≡ T conditioned
  on A, then Adv(S, T) ≤ Pr[¬A]

## References

* Maurer, U. (2002). "Indistinguishability of Random Systems." EUROCRYPT 2002.
  Section 3: "Bounding the Distinguishing Advantage"
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- A condition on transcripts: a decidable predicate on input-output sequences.

In Maurer's framework, this corresponds to a "monotone condition" or "event"
that can be checked during the execution of a random system.

Example: "no internal collision" in CBC-MAC, or "all outputs are distinct"
for the PRF/PRP switching lemma. -/
structure TranscriptCondition (X Y : Type*) (q : ℕ) where
  /-- The predicate on transcripts. -/
  holds : (Fin q → X × Y) → Prop
  /-- The predicate is decidable. -/
  dec : DecidablePred holds

attribute [instance] TranscriptCondition.dec

/-- The probability that a condition fails under a PDS with given inputs.

  Pr[¬A | S, inputs] := ∑_{s : ¬A(transcript(s, inputs))} S.dist(s)

This is the total mass of DDS whose transcripts violate the condition. -/
def conditionFailureProb
    (S : PDS X Y q) (A : TranscriptCondition X Y q) (inputs : Fin q → X) : NNReal :=
  ∑ s ∈ (Finset.univ : Finset (DDS X Y q)).filter
    (fun s => ¬A.holds (DDS.transcript s inputs)),
    S.dist s

/-- The probability that a condition fails under a PDS interacting with an adaptive environment. -/
def conditionFailureProbAdaptive
    (S : PDS X Y q) (A : TranscriptCondition X Y q) (e : DDE X Y q) : NNReal :=
  ∑ s ∈ (Finset.univ : Finset (DDS X Y q)).filter (fun s => ¬A.holds (interact s e)),
    S.dist s

/-- The maximum failure probability over all input sequences.

  ν(S, A) := sup_inputs Pr[¬A | S, inputs] -/
def maxConditionFailure
    (S : PDS X Y q) (A : TranscriptCondition X Y q) : NNReal :=
  Finset.sup Finset.univ (fun inputs => conditionFailureProb S A inputs)

/-- The maximum failure probability over all adaptive environments. -/
def maxConditionFailureAdaptive
    (S : PDS X Y q) (A : TranscriptCondition X Y q) : NNReal :=
  Finset.sup Finset.univ (fun e => conditionFailureProbAdaptive S A e)

/-- Two PDS are equivalent conditioned on A if their transcript distributions
agree on all transcripts satisfying A.

  S ≡_A T ↔ ∀ inputs, ∀ t with A(t), tr(S,inputs)(t) = tr(T,inputs)(t)

This is the key condition for the condition-based proof technique. -/
def PDS.condEquiv (S T : PDS X Y q) (A : TranscriptCondition X Y q) : Prop :=
  ∀ (inputs : Fin q → X) (t : Transcript X Y q),
    A.holds t → S.transcriptDist inputs t = T.transcriptDist inputs t

/-- Adaptive conditional equivalence: agreement on all "good" transcripts for all environments. -/
def PDS.condEquivAdaptive (S T : PDS X Y q) (A : TranscriptCondition X Y q) : Prop :=
  ∀ (e : DDE X Y q) (t : Transcript X Y q),
    A.holds t → S.adaptiveTranscriptDist e t = T.adaptiveTranscriptDist e t

/-- The sum of `fTransform f X` over a filtered finset equals
the sum of `X` over the preimage of that filter.

  ∑_{b : P(b)} (f(X))(b) = ∑_{a : P(f(a))} X(a)

This is the pushforward regrouping lemma. -/
lemma fTransform_filter_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (X : Dist A) (P : B → Prop) [DecidablePred P] :
    ∑ b ∈ (Finset.univ : Finset B).filter P, (Dist.fTransform f X) b =
    ∑ a ∈ (Finset.univ : Finset A).filter (P ∘ f), X a := by
  -- fTransform f X = mapDomain f X
  -- mapDomain f X is defined as X.sum (fun a => single (f a))
  -- (mapDomain f X) b = ∑_{a ∈ support} if f a = b then X a else 0
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  -- Goal: ∑ b ∈ filter P, ∑ a ∈ support, if f a = b then X a else 0
  --     = ∑ a ∈ filter (P∘f), X a
  -- Swap the sums
  rw [Finset.sum_comm]
  -- Goal: ∑ a ∈ support, ∑ b ∈ filter P, if f a = b then X a else 0
  --     = ∑ a ∈ filter (P∘f), X a
  -- Inner sum: ∑ b ∈ filter P, if f a = b then X a else 0
  --   = if P (f a) then X a else 0  (exactly one b = f a in filter P, if P holds)
  have h_inner : ∀ a ∈ X.support,
      ∑ b ∈ Finset.univ.filter P, (if f a = b then X a else 0) =
      if P (f a) then X a else 0 := by
    intro a _
    simp_rw [eq_comm (a := f a)]
    rw [Finset.sum_ite_eq' (Finset.univ.filter P) (f a) (fun _ => X a)]
    simp [Finset.mem_filter]
  rw [Finset.sum_congr rfl h_inner]
  -- Goal: ∑ a ∈ support, if P (f a) then X a else 0 = ∑ a ∈ filter (P∘f), X a
  -- LHS: sum over support with conditional = sum over support ∩ {P∘f}
  rw [← Finset.sum_filter]
  -- Goal: ∑ a ∈ support.filter (P∘f), X a = ∑ a ∈ univ.filter (P∘f), X a
  apply Finset.sum_subset
  · exact Finset.filter_subset_filter _ (Finset.subset_univ _)
  · intro a ha1 ha2
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finset.mem_univ, true_and,
      Function.comp] at ha1 ha2
    -- ha2 : ¬(X a ≠ 0 ∧ P (f a)), ha1 : P (f a)
    by_contra h
    exact ha2 ⟨h, ha1⟩

/-! ### Bridge lemmas: statDist ↔ conditionFailure

These lemmas connect the condition-based framework (condEquiv + failure bound)
with direct statistical distance computations (like PRPPRFSwitchingGeneral).

The key insight is that `condEquiv` zeroes out the "good" transcript terms in
the statistical distance sum, leaving only the "bad" transcript mass. -/

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- Condition failure probability equals the transcript mass on the bad set.

  Pr[¬A | S, inputs] = ∑_{t : ¬A(t)} transcriptDist(S, inputs)(t) -/
theorem conditionFailureProb_eq_transcriptDist_filter
    (S : PDS X Y q) (A : TranscriptCondition X Y q) (inputs : Fin q → X) :
    conditionFailureProb S A inputs =
    ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
      S.transcriptDist inputs t := by
  simp only [conditionFailureProb, PDS.transcriptDist]
  rw [fTransform_filter_sum (fun s => DDS.transcript s inputs) S.dist
    (fun t => ¬A.holds t)]
  rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- Adaptive condition failure probability equals transcript mass on the bad set. -/
theorem conditionFailureProbAdaptive_eq_transcriptDist_filter
    (S : PDS X Y q) (A : TranscriptCondition X Y q) (e : DDE X Y q) :
    conditionFailureProbAdaptive S A e =
    ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
      S.adaptiveTranscriptDist e t := by
  simp only [conditionFailureProbAdaptive, PDS.adaptiveTranscriptDist]
  rw [fTransform_filter_sum (fun s => interact s e) S.dist (fun t => ¬A.holds t)]
  rfl

/-! ### Shared good/bad split lemma

When `f t = g t` on good transcripts, the sum `∑ (f - g)` reduces to
the bad part only. This pattern appears 5+ times below. -/

/-- If `f t = g t` for all `t` satisfying `P`, then `∑ t, (f t - g t)`
equals the sum restricted to `¬ P`. -/
theorem sum_tsub_eq_sum_filter_not {T : Type*} [Fintype T]
    (f g : T → NNReal) (P : T → Prop) [DecidablePred P]
    (h : ∀ t, P t → f t = g t) :
    ∑ t : T, (f t - g t) =
      ∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬ P t), (f t - g t) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]
  have h_zero :
      ∑ t ∈ (Finset.univ : Finset T).filter P, (f t - g t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h t ht, tsub_self]
  rw [h_zero, zero_add]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- Pointwise bound: condEquiv implies statDist ≤ sum of failure probs.

  S ≡_A T → δ(tr(S,e), tr(T,e)) ≤ fail(S,A,e) + fail(T,A,e) -/
theorem statDist_le_conditionFailure
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquiv T A) (inputs : Fin q → X) :
    statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤
    conditionFailureProb S A inputs + conditionFailureProb T A inputs := by
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
      (S.transcriptDist inputs t - T.transcriptDist inputs t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_cond inputs t ht, tsub_self]
  rw [h_zero, zero_add]
  calc ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        (S.transcriptDist inputs t - T.transcriptDist inputs t)
      ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        S.transcriptDist inputs t := by
        apply Finset.sum_le_sum; intro t _; exact tsub_le_self
    _ ≤ conditionFailureProb S A inputs + conditionFailureProb T A inputs := by
        apply le_add_right
        rw [← conditionFailureProb_eq_transcriptDist_filter]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- One-sided bound: condEquiv implies statDist ≤ S's failure prob.

  S ≡_A T → δ(tr(S,e), tr(T,e)) ≤ fail(S,A,e) -/
theorem statDist_le_conditionFailure_single
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquiv T A) (inputs : Fin q → X) :
    statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤
    conditionFailureProb S A inputs := by
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
      (S.transcriptDist inputs t - T.transcriptDist inputs t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_cond inputs t ht, tsub_self]
  rw [h_zero, zero_add]
  calc ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        (S.transcriptDist inputs t - T.transcriptDist inputs t)
      ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        S.transcriptDist inputs t := by
        apply Finset.sum_le_sum; intro t _; exact tsub_le_self
    _ ≤ conditionFailureProb S A inputs := by
        rw [← conditionFailureProb_eq_transcriptDist_filter]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- Adaptive one-sided bound: condEquivAdaptive implies statDist ≤ S's adaptive failure prob. -/
theorem statDist_le_conditionFailureAdaptive_single
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquivAdaptive T A) (e : DDE X Y q) :
    statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) ≤
    conditionFailureProbAdaptive S A e := by
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
      (S.adaptiveTranscriptDist e t - T.adaptiveTranscriptDist e t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_cond e t ht, tsub_self]
  rw [h_zero, zero_add]
  calc ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        (S.adaptiveTranscriptDist e t - T.adaptiveTranscriptDist e t)
      ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        S.adaptiveTranscriptDist e t := by
        apply Finset.sum_le_sum; intro t _; exact tsub_le_self
    _ ≤ conditionFailureProbAdaptive S A e := by
        rw [← conditionFailureProbAdaptive_eq_transcriptDist_filter (S := S) (A := A) (e := e)]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- One-sided adaptive bound for a **fixed** environment.

This is the environment-specialized form of `statDist_le_conditionFailureAdaptive_single` and is
useful when proving conditional equivalence only for one particular environment (rather than for
all environments). -/
theorem statDist_le_conditionFailureAdaptive_single_for_env
    (S T : PDS X Y q) (A : TranscriptCondition X Y q) (e : DDE X Y q)
    (h_eq : ∀ t : Transcript X Y q, A.holds t →
      S.adaptiveTranscriptDist e t = T.adaptiveTranscriptDist e t) :
    statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) ≤
    conditionFailureProbAdaptive S A e := by
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
      (S.adaptiveTranscriptDist e t - T.adaptiveTranscriptDist e t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_eq t ht, tsub_self]
  rw [h_zero, zero_add]
  calc ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        (S.adaptiveTranscriptDist e t - T.adaptiveTranscriptDist e t)
      ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        S.adaptiveTranscriptDist e t := by
        apply Finset.sum_le_sum; intro t _; exact tsub_le_self
    _ ≤ conditionFailureProbAdaptive S A e := by
        rw [← conditionFailureProbAdaptive_eq_transcriptDist_filter (S := S) (A := A) (e := e)]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- Adaptive two-sided bound: condEquivAdaptive implies statDist ≤ sum of adaptive failure probs. -/
theorem statDist_le_conditionFailureAdaptive
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquivAdaptive T A) (e : DDE X Y q) :
    statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) ≤
    conditionFailureProbAdaptive S A e + conditionFailureProbAdaptive T A e := by
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
      (S.adaptiveTranscriptDist e t - T.adaptiveTranscriptDist e t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_cond e t ht, tsub_self]
  rw [h_zero, zero_add]
  calc ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        (S.adaptiveTranscriptDist e t - T.adaptiveTranscriptDist e t)
      ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        S.adaptiveTranscriptDist e t := by
        apply Finset.sum_le_sum; intro t _; exact tsub_le_self
    _ ≤ conditionFailureProbAdaptive S A e + conditionFailureProbAdaptive T A e := by
        apply le_add_right
        rw [← conditionFailureProbAdaptive_eq_transcriptDist_filter (S := S) (A := A) (e := e)]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- When T=0 on bad transcripts and S≤T on good transcripts,
statDist = conditionFailureProb S A inputs.

This is the workhorse for switching-style proofs that use the
"dominated on good, zero on bad" pattern. -/
theorem statDist_eq_conditionFailure_when_dominated
    (S T : PDS X Y q) (A : TranscriptCondition X Y q) (inputs : Fin q → X)
    (h_zero : ∀ t, ¬A.holds t → T.transcriptDist inputs t = 0)
    (h_le : ∀ t, A.holds t → S.transcriptDist inputs t ≤ T.transcriptDist inputs t) :
    statDist (S.transcriptDist inputs) (T.transcriptDist inputs) =
    conditionFailureProb S A inputs := by
  set bad := (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t)
  have h_sd := statDist_eq_mass_on_zero_support
    (S.transcriptDist inputs) (T.transcriptDist inputs) bad
    (fun t ht => h_zero t (Finset.mem_filter.mp ht).2)
    (fun t ht => by
      have h_good : A.holds t := by
        by_contra h_neg; exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_neg⟩)
      exact h_le t h_good)
  rw [h_sd, conditionFailureProb_eq_transcriptDist_filter]

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- **Core lemma**: If S ≡_A T (equivalent conditioned on A), then
the distinguishing advantage is bounded by the failure probability of A.

  S ≡_A T → Adv(S, T) ≤ ν(S, A) + ν(T, A)

Paper (Maurer 2002, Lemma 1): "If S and T are equivalent conditioned on A,
then the distinguishing advantage is at most the probability that A fails."

The bound uses both S and T failure probabilities because statistical distance
is the max of both directions. -/
theorem advantage_le_condition_failure
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquiv T A) :
    advantage S T ≤ maxConditionFailure S A + maxConditionFailure T A := by
  simp only [advantage, maxConditionFailure]
  apply Finset.sup_le
  intro inputs _
  calc statDist (S.transcriptDist inputs) (T.transcriptDist inputs)
      ≤ conditionFailureProb S A inputs + conditionFailureProb T A inputs :=
        statDist_le_conditionFailure S T A h_cond inputs
    _ ≤ _ := add_le_add (Finset.le_sup (Finset.mem_univ inputs))
                         (Finset.le_sup (Finset.mem_univ inputs))

omit [DecidableEq X] in
/-- Adaptive advantage bound from an adaptive conditional equivalence + failure bounds. -/
theorem advantageAdaptive_le_condition_failure
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquivAdaptive T A) :
    advantageAdaptive S T ≤
      maxConditionFailureAdaptive S A + maxConditionFailureAdaptive T A := by
  simp only [advantageAdaptive, maxConditionFailureAdaptive]
  apply Finset.sup_le
  intro e _
  calc statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e)
      ≤ conditionFailureProbAdaptive S A e + conditionFailureProbAdaptive T A e :=
        statDist_le_conditionFailureAdaptive S T A h_cond e
    _ ≤ _ := add_le_add (Finset.le_sup (Finset.mem_univ e))
                         (Finset.le_sup (Finset.mem_univ e))

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- Simplified version when S and T have equal weight and we only need
one-sided failure probability.

  S ≡_A T ∧ |S| = |T| → Adv(S, T) ≤ ν(S, A)

This is the most commonly used form. -/
theorem advantage_le_single_failure
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h_cond : S.condEquiv T A)
    (_h_weight : S.dist.weight = T.dist.weight) :
    advantage S T ≤ maxConditionFailure S A := by
  simp only [advantage, maxConditionFailure]
  apply Finset.sup_le
  intro inputs _
  exact le_trans (statDist_le_conditionFailure_single S T A h_cond inputs)
    (Finset.le_sup (Finset.mem_univ inputs))

/-! ## Ratio-Bounded Conditional Equivalence

Generalization of `condEquiv` (which requires exact equality on good transcripts)
to allow a multiplicative ratio bound. This is the NNReal analog of the
H-coefficient method's ratio form:

  `Pr_X[t] ≤ c · Pr_Y[t]` for good transcripts t

This bridges the gap between Maurer's condition-based proofs (c = 1) and
Patarin's H-technique (general c ≥ 1). -/

/-- Ratio-bounded conditional equivalence: on good transcripts,
S's transcript mass is at most c times T's mass.

When c = 1, this reduces to `condEquiv` (pointwise ≤ in one direction). -/
def PDS.ratioCondEquiv (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (c : NNReal) : Prop :=
  ∀ (inputs : Fin q → X) (t : Transcript X Y q),
    A.holds t → S.transcriptDist inputs t ≤ c * T.transcriptDist inputs t

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- condEquiv implies ratioCondEquiv with c = 1 in both directions. -/
theorem PDS.condEquiv_implies_ratioCondEquiv_one
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (h : S.condEquiv T A) :
    S.ratioCondEquiv T A 1 := by
  intro inputs t ht
  rw [one_mul, h inputs t ht]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- **Ratio-form statDist bound**: If S ≤ c·T on good transcripts,
then statDist ≤ (c - 1) · weight(T) + fail(S).

This is the NNReal analog of `probPred_le_mul_probPred_add_bad`. -/
theorem statDist_le_ratio_plus_failure
    (S T : PDS X Y q) (A : TranscriptCondition X Y q) (c : NNReal)
    (h_ratio : S.ratioCondEquiv T A c) (inputs : Fin q → X) :
    statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤
    (c - 1) * (∑ t : Transcript X Y q, T.transcriptDist inputs t)
    + conditionFailureProb S A inputs := by
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  -- On good transcripts: S(t) - T(t) ≤ c·T(t) - T(t) ≤ (c-1)·T(t)
  have h_good : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
      (S.transcriptDist inputs t - T.transcriptDist inputs t) ≤
      (c - 1) * ∑ t : Transcript X Y q, T.transcriptDist inputs t := by
    calc ∑ t ∈ Finset.univ.filter (fun t => A.holds t),
          (S.transcriptDist inputs t - T.transcriptDist inputs t)
        ≤ ∑ t ∈ Finset.univ.filter (fun t => A.holds t),
          (c - 1) * T.transcriptDist inputs t := by
          apply Finset.sum_le_sum
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          -- S(t) ≤ c·T(t), so S(t) - T(t) ≤ c·T(t) - T(t) = (c-1)·T(t)
          calc S.transcriptDist inputs t - T.transcriptDist inputs t
              ≤ c * T.transcriptDist inputs t - T.transcriptDist inputs t :=
                tsub_le_tsub_right (h_ratio inputs t ht) _
            _ = c * T.transcriptDist inputs t - 1 * T.transcriptDist inputs t := by
                rw [one_mul]
            _ = (c - 1) * T.transcriptDist inputs t := by
                rw [← tsub_mul]
      _ ≤ (c - 1) * ∑ t : Transcript X Y q, T.transcriptDist inputs t := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun _ _ _ => zero_le _)
  -- On bad transcripts: S(t) - T(t) ≤ S(t) ≤ condFailure
  have h_bad : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
      (S.transcriptDist inputs t - T.transcriptDist inputs t) ≤
      conditionFailureProb S A inputs := by
    calc ∑ t ∈ Finset.univ.filter (fun t => ¬A.holds t),
          (S.transcriptDist inputs t - T.transcriptDist inputs t)
        ≤ ∑ t ∈ Finset.univ.filter (fun t => ¬A.holds t),
          S.transcriptDist inputs t := by
          apply Finset.sum_le_sum; intro t _; exact tsub_le_self
      _ ≤ conditionFailureProb S A inputs := by
          rw [← conditionFailureProb_eq_transcriptDist_filter]
  exact add_le_add h_good h_bad

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- **Advantage bound via ratio**: If S ≤ c·T on good transcripts and
T has total weight w, then Adv(S,T) ≤ (c-1)·w + maxFailure(S,A).

For probability distributions (weight = 1), the (c-1) term captures
the multiplicative closeness between the two systems. -/
theorem advantage_le_ratio_plus_maxFailure [Fintype X]
    (S T : PDS X Y q) (A : TranscriptCondition X Y q) (c : NNReal)
    (h_ratio : S.ratioCondEquiv T A c)
    (w : NNReal) (h_weight : ∀ inputs : Fin q → X,
      ∑ t : Transcript X Y q, T.transcriptDist inputs t ≤ w) :
    advantage S T ≤ (c - 1) * w + maxConditionFailure S A := by
  simp only [advantage, maxConditionFailure]
  apply Finset.sup_le
  intro inputs _
  calc statDist (S.transcriptDist inputs) (T.transcriptDist inputs)
      ≤ (c - 1) * (∑ t : Transcript X Y q, T.transcriptDist inputs t)
        + conditionFailureProb S A inputs :=
        statDist_le_ratio_plus_failure S T A c h_ratio inputs
    _ ≤ (c - 1) * w + Finset.sup Finset.univ
        (fun inputs => conditionFailureProb S A inputs) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (h_weight inputs) (zero_le _))
          (Finset.le_sup (f := fun i => conditionFailureProb S A i)
            (Finset.mem_univ inputs))

/-! ## DDS-Level Conditions

For constructions like CBC-MAC, the relevant condition (e.g., "no internal
collision") depends on the internal DDS state, not just the observed transcript.
A `DDSCondition` generalizes `TranscriptCondition` by allowing the predicate
to depend on the DDS itself and the input sequence, rather than only the
transcript.

The condition-based bound still holds: Adv(S,T) ≤ Pr[¬A | S] where the
failure probability sums over DDS failing the condition. The proof is
simpler because we skip the pushforward regrouping step entirely. -/

/-- A condition on DDS and inputs: a decidable predicate that determines
whether a particular DDS "behaves well" on given inputs.

Example: for CBC-MAC, the condition checks whether all internal P-inputs
(chaining values) are distinct — something that depends on the DDS (the
permutation P) and the messages, not on the transcript. -/
structure DDSCondition (X Y : Type*) (q : ℕ) where
  /-- The predicate on a DDS and input sequence. -/
  holds : DDS X Y q → (Fin q → X) → Prop
  /-- The predicate is decidable. -/
  dec : ∀ s inputs, Decidable (holds s inputs)

instance (A : DDSCondition X Y q) (s : DDS X Y q) (inputs : Fin q → X) :
    Decidable (A.holds s inputs) := A.dec s inputs

/-- The probability that a DDS condition fails under a PDS with given inputs.

  Pr[¬A | S, inputs] := ∑_{s : ¬A(s, inputs)} S.dist(s) -/
def ddsConditionFailureProb
    (S : PDS X Y q) (A : DDSCondition X Y q) (inputs : Fin q → X) : NNReal :=
  ∑ s ∈ (Finset.univ : Finset (DDS X Y q)).filter
    (fun s => ¬A.holds s inputs),
    S.dist s

/-- The maximum DDS-condition failure probability over all input sequences. -/
def maxDDSConditionFailure
    (S : PDS X Y q) (A : DDSCondition X Y q) : NNReal :=
  Finset.sup Finset.univ (fun inputs => ddsConditionFailureProb S A inputs)

/-- Lift a `DDSCondition` to a `TranscriptCondition` for specific inputs.

A transcript is "good" iff ALL DDS that produce it satisfy the DDS condition.
This is the strongest transcript-level condition compatible with the DDS condition. -/
def DDSCondition.toTranscriptCondition
    (A : DDSCondition X Y q) (inputs : Fin q → X) :
    TranscriptCondition X Y q where
  holds := fun t => ∀ s : DDS X Y q, DDS.transcript s inputs = t → A.holds s inputs
  dec := fun _ => inferInstance

/-- Two PDS are equivalent conditioned on a DDS condition if their transcript
distributions agree for all transcripts where every producing DDS satisfies
the condition.

  S ≡_A T ↔ ∀ inputs, ∀ t, (∀ s with tr(s,inputs)=t, A(s,inputs)) →
              tr(S)(t) = tr(T)(t) -/
def PDS.ddsCondEquiv (S T : PDS X Y q) (A : DDSCondition X Y q) : Prop :=
  ∀ (inputs : Fin q → X) (t : Transcript X Y q),
    (∀ s : DDS X Y q, DDS.transcript s inputs = t → A.holds s inputs) →
    S.transcriptDist inputs t = T.transcriptDist inputs t

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype (Transcript X Y q)] in
/-- The DDS-level failure probability bounds the transcript-level failure
probability from below.

  ddsFailure ≤ transcriptFailure

because `{s | ¬A(s)} ⊆ {s | bad tr(s)}`. -/
theorem dds_failure_le_transcript_failure
    (S : PDS X Y q) (A : DDSCondition X Y q) (inputs : Fin q → X) :
    ddsConditionFailureProb S A inputs ≤
    conditionFailureProb S (A.toTranscriptCondition inputs) inputs := by
  simp only [ddsConditionFailureProb, conditionFailureProb,
    DDSCondition.toTranscriptCondition]
  apply Finset.sum_le_sum_of_subset
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact fun h_all => hs (h_all s rfl)

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- **Advantage bound via DDS conditions.**

If S and T agree on all transcripts that can only be produced by "good" DDS,
then the advantage is bounded by the transcript-level failure probability
of the lifted condition.

  S ≡_A T → Adv(S, T) ≤ sup_inputs condFailure(S, A_tr(inputs), inputs) -/
theorem advantage_le_dds_failure
    (S T : PDS X Y q) (A : DDSCondition X Y q)
    (h_cond : S.ddsCondEquiv T A)
    (_h_weight : S.dist.weight = T.dist.weight) :
    advantage S T ≤
    Finset.sup Finset.univ (fun inputs : Fin q → X =>
      conditionFailureProb S (A.toTranscriptCondition inputs) inputs) := by
  simp only [advantage]
  apply Finset.sup_le
  intro inputs _
  -- For this specific inputs, S ≡ T conditioned on A.toTranscriptCondition inputs
  have h_cond_tr : ∀ t : Transcript X Y q,
      (A.toTranscriptCondition inputs).holds t →
      S.transcriptDist inputs t = T.transcriptDist inputs t := by
    intro t ht; exact h_cond inputs t ht
  -- Standard one-sided bound argument
  have h_le_fail : statDist (S.transcriptDist inputs) (T.transcriptDist inputs)
      ≤ conditionFailureProb S (A.toTranscriptCondition inputs) inputs := by
    simp only [statDist]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t => (A.toTranscriptCondition inputs).holds t)]
    have h_zero : ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter
        (fun t => (A.toTranscriptCondition inputs).holds t),
        (S.transcriptDist inputs t - T.transcriptDist inputs t) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [h_cond_tr t ht, tsub_self]
    rw [h_zero, zero_add]
    calc ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter
          (fun t => ¬(A.toTranscriptCondition inputs).holds t),
          (S.transcriptDist inputs t - T.transcriptDist inputs t)
        ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter
          (fun t => ¬(A.toTranscriptCondition inputs).holds t),
          S.transcriptDist inputs t := by
          apply Finset.sum_le_sum; intro t _; exact tsub_le_self
      _ ≤ conditionFailureProb S (A.toTranscriptCondition inputs) inputs := by
          rw [← conditionFailureProb_eq_transcriptDist_filter]
  set f := fun i : Fin q → X => conditionFailureProb S (A.toTranscriptCondition i) i
  exact le_trans h_le_fail (Finset.le_sup (f := f) (Finset.mem_univ inputs))

/-- Convert a `TranscriptCondition` to a `DDSCondition`.

A transcript condition can be viewed as a DDS condition that depends on
the DDS only through its transcript. -/
def TranscriptCondition.toDDSCondition (A : TranscriptCondition X Y q) :
    DDSCondition X Y q where
  holds := fun s inputs => A.holds (DDS.transcript s inputs)
  dec := fun s inputs => A.dec (DDS.transcript s inputs)

end RandomSystems
