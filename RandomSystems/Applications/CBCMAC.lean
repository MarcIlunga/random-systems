/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ConditionBased
import RandomSystems.Instances.URF
import RandomSystems.Applications.PRPPRFSwitching

/-!
# CBC-MAC Security via Random Systems

Formalization of the CBC-MAC security proof from Maurer (EUROCRYPT 2002),
"Indistinguishability of Random Systems," Section 4.2.

## Overview

CBC-MAC with a random permutation P computes the MAC of an ℓ-block message
(m₁, ..., mℓ) as:
  c₀ = 0
  cᵢ = P(cᵢ₋₁ ⊕ mᵢ)   for i = 1, ..., ℓ
  tag = cℓ

The security proof shows that when P is a uniform random permutation,
the CBC-MAC construction is indistinguishable from a uniform random
function oracle (the paper’s URF, modeled here as `Instances.URFfun`), with
advantage bounded by q²ℓ²/(2N) where:
- q = number of MAC queries
- ℓ = message length in blocks
- N = |block| = size of the block space

## Note on “URF” in this codebase

There are two closely-related “uniform” ideals:

* `Instances.URFfun` (paper ideal): sample a random function `f : X → Y` once and
  answer each query with `f x` (consistent on repeats).
* `Instances.URF` (uniform-over-DDS ideal): uniform over *all* DDS `DDS X Y q`.
  For `q > 1` this is strictly more powerful than a random function oracle and
  behaves beacon-like on repeated inputs.

This file proves a per-input bound against `Instances.URF` as an intermediate
step (it has very clean uniformity properties), then bridges to the paper ideal
`Instances.URFfun` on injective input sequences.

## Proof Strategy

The proof uses the condition-based technique:
1. Define "no internal collision" condition:
   all intermediate values c_{i,j} (block j of query i) are distinct
2. Show: conditioned on no internal collision, the CBC-MAC output
   is uniformly distributed (equivalent to `URFfun` on distinct inputs)
3. Bound: Pr[internal collision] ≤ q²ℓ²/(2N) (birthday bound on
   all qℓ intermediate values)

## References

* Maurer, U. (2002). "Indistinguishability of Random Systems." EUROCRYPT 2002.
  Section 4.2: "Application 2: CBC-MAC"
* Bellare, M., Kilian, J. & Rogaway, P. (2000).
  "The Security of the Cipher Block Chaining Message Authentication Code."
  Journal of Computer and System Sciences, 61(3).
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

/-! ## CBC-MAC Computation -/

/-- CBC-MAC computation for a single block (ℓ = 1).

This is simply the permutation applied to the message block.
  CBC-MAC₁(P, m) = P(m) -/
def cbcMac1 {B : Type*} (P : B → B) (m : B) : B := P m

/-- CBC-MAC computation for ℓ blocks using a fixed permutation.

  c₀ = 0
  cᵢ = P(cᵢ₋₁ + mᵢ)   for i = 1, ..., ℓ
  tag = cℓ

where + is the XOR/group operation. -/
def cbcMacMulti {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) : B :=
  Fin.foldl ℓ (fun acc i => P (acc + m i)) 0

/-- The "no internal collision" condition for CBC-MAC.

When processing q messages of 1 block each, define the condition:
"all outputs in the transcript are distinct."

If this holds, then each P-application receives a fresh input,
so the outputs are independent uniform values. -/
def noInternalCollision (B : Type*) [DecidableEq B] (q : ℕ) :
    TranscriptCondition B B q where
  holds := fun t => Function.Injective (fun i => (t i).2)
  dec := inferInstance

/-! ## Security Bounds -/

/-- The CBC-MAC advantage bound for single-block messages.

For ℓ = 1, CBC-MAC(P, m) = P(m), which is a random permutation.
The advantage against a URF is bounded by the failure probability
of the no-collision condition.

  Adv(CBC-MAC₁, URF) ≤ ν(CBC-MAC₁, noCollision)

where ν is the max failure probability of the condition. -/
theorem cbcMac1_advantage_bound
    {B : Type*} [Fintype B] [DecidableEq B]
    [Nonempty (DDS B B 1)]
    (CBC_MAC : PDS B B 1)
    (URF_sys : PDS B B 1)
    (h_cond : CBC_MAC.condEquiv URF_sys (noInternalCollision B 1))
    (h_weight : CBC_MAC.dist.weight = URF_sys.dist.weight) :
    advantage CBC_MAC URF_sys ≤ maxConditionFailure CBC_MAC (noInternalCollision B 1) :=
  advantage_le_single_failure CBC_MAC URF_sys (noInternalCollision B 1) h_cond h_weight

/-- The CBC-MAC advantage bound for multi-block messages (abstract statement).

For ℓ-block messages and q queries:

  Adv(CBC-MACℓ, URF) ≤ q²ℓ² / (2N)

This is the birthday bound on all q·ℓ intermediate chaining values. -/
theorem cbcMac_bound_value (ℓ q N : ℕ) :
    ∃ (bound : NNReal),
      bound = (q * q * ℓ * ℓ : ℕ) / (2 * N : ℕ) :=
  ⟨_, rfl⟩

/-! ## Relating CBC-MAC to the Construction Framework

In the random systems framework, CBC-MAC is a *construction* (Definition 13):
it takes a component PDS (the random permutation P) and produces
an output PDS (the MAC system).

For ℓ = 1: C(P) = P (identity construction)
For ℓ > 1: C(P) applies P iteratively with XOR chaining

The hybrid argument gives:
  Adv(CBC-MAC(P), CBC-MAC(P*)) ≤ Adv(P, P*)

so replacing a PRP with a random function oracle (`URFfun`) costs at most the
PRP/PRF switching bound. -/

/-- The CBC-MAC construction for single-block messages is the identity:
it just passes through the component system.

  C₁(P) = P

This means Adv(C₁(P), C₁(P*)) ≤ Adv(P, P*) trivially. -/
theorem cbcMac1_is_identity_construction {B : Type*} :
    ∀ (P : B → B) (m : B), cbcMac1 P m = P m :=
  fun _ _ => rfl

/-- The no-internal-collision condition is the same as allOutputsDistinct. -/
theorem noInternalCollision_eq_allOutputsDistinct (B : Type*) [DecidableEq B] (q : ℕ) :
    noInternalCollision B q = allOutputsDistinct B q := rfl

/-- **End-to-end uniform-over-DDS bound** (about `Instances.URF`).

For any system T conditionally equivalent to URF under the no-collision
condition, the advantage is bounded by the birthday bound:

  Adv(URF, T) ≤ q(q-1)/(2|B|)

This combines:
1. `advantage_le_single_failure`: Adv(URF, T) ≤ maxConditionFailure(URF, A)
2. `urf_collision_bound_general`: maxConditionFailure(URF, A) ≤ birthday bound

For CBC-MAC₁ with a random permutation, T = URP and the conditional
equivalence is `urf_urp_cond_equiv` (from the q=1 switching lemma). -/
theorem urf_condEquiv_birthday_bound
    {B : Type*} [Fintype B] [DecidableEq B]
    {q : ℕ} [Fintype (DDS B B q)] [Nonempty (DDS B B q)]
    (T : PDS B B q)
    (h_cond : (Instances.URF (X := B) (Y := B) (q := q)).condEquiv T
      (allOutputsDistinct B q))
    (h_weight : (Instances.URF (X := B) (Y := B) (q := q)).dist.weight = T.dist.weight) :
    advantage (Instances.URF (X := B) (Y := B) (q := q)) T
    ≤ birthdayBound q (Fintype.card B) :=
  le_trans
    (advantage_le_single_failure _ T _ h_cond h_weight)
    urf_collision_bound_general

/-! ## Multi-Block CBC-MAC (ℓ > 1)

For ℓ-block messages, CBC-MAC internally applies the permutation P
a total of q·ℓ times. The security proof uses the condition-based
technique on these q·ℓ internal P-applications.
-/

/-- All intermediate chaining values of CBC-MAC for one message.

Given a permutation P and an ℓ-block message m, the j-th chaining value is:
  c₀ = 0
  cⱼ = P(cⱼ₋₁ + mⱼ)   for j = 0, ..., ℓ-1

Returns the ℓ chaining values c₀, ..., c_{ℓ-1} (each is the output of P). -/
def cbcMacChainValues {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) :
    Fin ℓ → B :=
  fun j => Fin.foldl (j.val + 1) (fun acc (i : Fin (j.val + 1)) =>
    P (acc + m ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt j.isLt)⟩)) 0

/-- The last chaining value equals the CBC-MAC tag. -/
theorem cbcMacChainValues_last {B : Type*} [AddCommGroup B] (P : B → B)
    (ℓ : ℕ) (m : Fin (ℓ + 1) → B) :
    cbcMacChainValues P (ℓ + 1) m (Fin.last ℓ) = cbcMacMulti P (ℓ + 1) m := by
  rfl

/-- The P-input at step j of a single-message CBC-MAC computation.

This is cⱼ₋₁ + mⱼ, which is the value fed to P to produce cⱼ. -/
private def finPred {n : ℕ} (j : Fin n) (hj0 : j.val ≠ 0) : Fin n :=
  ⟨j.val - 1, by
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
    have hlt : j.val - 1 < j.val := Nat.sub_lt hjpos Nat.one_pos
    exact lt_trans hlt j.isLt⟩

private lemma finPred_succ_eq_castSucc {n : ℕ} (i : Fin n)
    (h : (i.succ : Fin (n + 1)).val ≠ 0) :
    finPred (n := n + 1) i.succ h = Fin.castSucc i := by
  ext
  simp [finPred]

def cbcMacPInput {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) :
    Fin ℓ → B :=
  fun j =>
    let prev := if h : j.val = 0 then 0
      else cbcMacChainValues P ℓ m (finPred j h)
    prev + m j

/-- All P-inputs across all q queries of ℓ-block CBC-MAC.

For q messages, each of ℓ blocks, the permutation P is called q·ℓ times.
This function enumerates all q·ℓ P-inputs as a flat sequence indexed by
Fin (q * ℓ), where index k corresponds to query k/ℓ, block k%ℓ. -/
def cbcMacAllPInputs {B : Type*} [AddCommGroup B] (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) : Fin (q * ℓ) → B :=
  fun k =>
    have hk := k.isLt
    let i : Fin q := ⟨k.val / ℓ, by
      rwa [Nat.div_lt_iff_lt_mul hℓ]⟩
    let j : Fin ℓ := ⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩
    cbcMacPInput P ℓ (msgs i) j

/-- The "no internal collision" condition for multi-block CBC-MAC.

When processing q messages of ℓ blocks each, define the condition:
"all q·ℓ P-inputs are distinct."

If this holds, each P-application receives a fresh input, so the
outputs are independent uniform values (when P is a URF). -/
def noInternalCollisionMulti (B : Type*) [DecidableEq B] [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (Fin q → Fin ℓ → B) → Prop :=
  fun msgs => Function.Injective (cbcMacAllPInputs P ℓ hℓ msgs)

/-! ## Multi-Block Security Bounds -/

/-- The multi-block birthday bound: (q·ℓ)·(q·ℓ - 1) / (2·N) ≤ q²ℓ² / (2·N).

Since (q·ℓ)·(q·ℓ - 1) ≤ (q·ℓ)² = q²ℓ², the exact birthday bound
on q·ℓ values is at most the standard q²ℓ²/(2N) bound. -/
theorem birthdayBound_mul_le (q ℓ N : ℕ) :
    birthdayBound (q * ℓ) N ≤ (q * q * ℓ * ℓ : ℕ) / (2 * N : ℕ) := by
  simp only [birthdayBound]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h_nat : q * ℓ * (q * ℓ - 1) ≤ q * q * ℓ * ℓ :=
    calc q * ℓ * (q * ℓ - 1)
        ≤ q * ℓ * (q * ℓ) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = q * q * ℓ * ℓ := by ring
  exact_mod_cast h_nat

/-- **Multi-block CBC-MAC security bound (abstract)** (about `Instances.URF`).

For any PDS S : PDS M B q (e.g., CBC-MAC with a URF/URP as internal
permutation), if S is conditionally equivalent to a URF under a condition
A whose failure probability is bounded by birthdayBound (q * ℓ) |B|,
then the advantage is bounded by the birthday bound.

  Adv(URF, S) ≤ (q·ℓ)·(q·ℓ - 1) / (2·|B|)

The condition A captures "no internal collision" — all q·ℓ P-inputs
are distinct. This theorem is parametric in A, so the user instantiates
it with the specific condition for their CBC-MAC construction. -/
theorem cbcMac_multi_security_abstract
    {M B : Type*} [Fintype M] [Fintype B] [DecidableEq M] [DecidableEq B]
    {q : ℕ} [Fintype (DDS M B q)] [Nonempty (DDS M B q)]
    [Fintype (Transcript M B q)] [DecidableEq (Transcript M B q)]
    (ℓ : ℕ)
    (S : PDS M B q)
    (A : TranscriptCondition M B q)
    (h_cond : (Instances.URF (X := M) (Y := B) (q := q)).condEquiv S A)
    (h_weight : (Instances.URF (X := M) (Y := B) (q := q)).dist.weight = S.dist.weight)
    (h_fail : maxConditionFailure (Instances.URF (X := M) (Y := B) (q := q)) A
      ≤ birthdayBound (q * ℓ) (Fintype.card B)) :
    advantage (Instances.URF (X := M) (Y := B) (q := q)) S
    ≤ birthdayBound (q * ℓ) (Fintype.card B) :=
  le_trans (advantage_le_single_failure _ S _ h_cond h_weight) h_fail

/-- **Multi-block CBC-MAC security bound (numerical)** (about `Instances.URF`).

The same as `cbcMac_multi_security_abstract` but with the explicit
numerical bound q²ℓ²/(2N):

  Adv(URF, S) ≤ q²ℓ² / (2·|B|) -/
theorem cbcMac_multi_security_numerical
    {M B : Type*} [Fintype M] [Fintype B] [DecidableEq M] [DecidableEq B]
    {q : ℕ} [Fintype (DDS M B q)] [Nonempty (DDS M B q)]
    [Fintype (Transcript M B q)] [DecidableEq (Transcript M B q)]
    (ℓ : ℕ)
    (S : PDS M B q)
    (A : TranscriptCondition M B q)
    (h_cond : (Instances.URF (X := M) (Y := B) (q := q)).condEquiv S A)
    (h_weight : (Instances.URF (X := M) (Y := B) (q := q)).dist.weight = S.dist.weight)
    (h_fail : maxConditionFailure (Instances.URF (X := M) (Y := B) (q := q)) A
      ≤ birthdayBound (q * ℓ) (Fintype.card B)) :
    advantage (Instances.URF (X := M) (Y := B) (q := q)) S
    ≤ (q * q * ℓ * ℓ : ℕ) / (2 * Fintype.card B : ℕ) :=
  le_trans (cbcMac_multi_security_abstract ℓ S A h_cond h_weight h_fail)
    (birthdayBound_mul_le q ℓ (Fintype.card B))

/-! ## Concrete CBC-MAC as DDS

The CBC-MAC construction maps a permutation `P : B → B` to a DDS that
computes the CBC-MAC tag for each query message. This makes the connection
between the abstract PDS framework and the concrete computation explicit.
-/

/-- A concrete DDS for multi-block CBC-MAC with a fixed permutation P.

Given P : B → B and block length ℓ, this DDS answers q queries where each
input is an ℓ-block message (Fin ℓ → B) and the output is the CBC-MAC tag.

Note: this is a stateless DDS — each response depends only on the current
message, not on previous queries. The response at query i uses input
`inputs ⟨i, ...⟩` (the i-th message in the sequence). -/
def cbcMacDDS {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (q : ℕ) :
    DDS (Fin ℓ → B) B q where
  respond := fun i inputs => cbcMacMulti P ℓ (inputs ⟨i.val, by omega⟩)

/-! ## Compositional CBC-MAC Security (Pushforward Construction)

CBC-MAC with a uniform random function P : B → B is modeled as a
**pushforward construction**: take the uniform distribution over all
functions B → B (via `DDS B B 1`), map each function P to the DDS
`cbcMacDDS P ℓ q`, and compare the resulting PDS against the ideal
uniform-function oracle `Instances.URFfun (X := Fin ℓ → B) (Y := B) (q := q)`.

Internally, many lemmas are phrased against `Instances.URF` (uniform over all
q-query DDS) because it has an especially simple output-vector distribution for
*any* fixed input sequence. The bridge section later shows that on injective
input sequences (the only ones relevant for the birthday-bound argument),
`URFfun` and `URF` induce the same transcript distribution.

The security argument has two components:
1. **Conditional equivalence**: when all q·ℓ P-inputs are distinct
   (no internal collision), each CBC-MAC tag is a fresh uniform output
   of P, matching the ideal transcript distribution.
2. **Collision bound**: the probability that uniform P causes a collision
   among q·ℓ correlated P-inputs is ≤ birthdayBound(q·ℓ, |B|).

The P-inputs are correlated through chaining (cⱼ = P(cⱼ₋₁ + mⱼ)),
but under uniform P, conditioned on no prior collision, each new P-output
is independently uniform (P at a fresh input is independent of P at
previous inputs). This gives a sequential conditioning argument matching
the standard birthday bound.
-/

/-- CBC-MAC with a uniform random function P : B → B.

This is the pushforward of the uniform distribution on `B → B` (via
`DDS B B 1 ≃ (B → B)`) through the map `P ↦ cbcMacDDS P ℓ q`.

Each function P : B → B is mapped to the DDS that computes CBC-MAC
tags for q messages of ℓ blocks each. The resulting PDS over
`DDS (Fin ℓ → B) B q` is the natural random system corresponding to
"run CBC-MAC with a random function." -/
def cbcMacPDS (B : Type*) [AddCommGroup B] [Fintype B] [DecidableEq B]
    (ℓ q : ℕ) [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS B B 1)] :
    PDS (Fin ℓ → B) B q where
  dist := Dist.fTransform
    (fun (s : DDS B B 1) => cbcMacDDS (dds1Equiv B B s) ℓ q)
    (Dist.uniform (DDS B B 1))

/-! ## Instrumented CBC-MAC: Full chaining-value transcripts

For the conditional-equivalence step (Maurer02 / cbc-improved), we need a
condition that is *transcript-measurable*. For CBC-MAC, “no internal collision”
is naturally expressed in terms of the *full chaining values* `c₀,…,c_{ℓ-1}` for
each query message, because the P-inputs are computed from the message blocks
and the previous chaining values.

We therefore introduce an “instrumented” DDS/PDS that outputs the full chain
vector per query. The usual tag transcript is obtained by projecting each chain
vector to its last element. -/

/-- CBC-MAC DDS that returns the full chaining-value vector `c₀,…,c_{ℓ-1}` per query. -/
def cbcMacChainDDS {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (q : ℕ) :
    DDS (Fin ℓ → B) (Fin ℓ → B) q where
  respond := fun i inputs => cbcMacChainValues P ℓ (inputs ⟨i.val, by omega⟩)

/-- CBC-MAC with a uniform random function `P : B → B`, instrumented to expose all chaining values. -/
def cbcMacChainPDS (B : Type*) [AddCommGroup B] [Fintype B] [DecidableEq B]
    (ℓ q : ℕ) [Fintype (DDS (Fin ℓ → B) (Fin ℓ → B) q)] [Nonempty (DDS B B 1)] :
    PDS (Fin ℓ → B) (Fin ℓ → B) q where
  dist := Dist.fTransform
    (fun (s : DDS B B 1) => cbcMacChainDDS (dds1Equiv B B s) ℓ q)
    (Dist.uniform (DDS B B 1))

/-- Project a chaining-value transcript to the usual tag transcript by taking the last chain value. -/
def chainTranscriptToTagTranscript
    {B : Type*} [AddCommGroup B] {ℓ q : ℕ} (hℓ : 0 < ℓ) :
    Transcript (Fin ℓ → B) (Fin ℓ → B) q → Transcript (Fin ℓ → B) B q :=
  fun t i =>
    let last : Fin ℓ := ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩
    ((t i).1, (t i).2 last)

private lemma cbcMacChainValues_last_of_pos
    {B : Type*} [AddCommGroup B] (P : B → B) {ℓ : ℕ} (hℓ : 0 < ℓ) (m : Fin ℓ → B) :
    let last : Fin ℓ := ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩
    cbcMacChainValues P ℓ m last = cbcMacMulti P ℓ m := by
  classical
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓ) with ⟨n, rfl⟩
  -- `ℓ = n+1`, and `⟨(n+1)-1, _⟩ = Fin.last n`.
  simpa [Nat.succ_sub_one] using (cbcMacChainValues_last (P := P) (ℓ := n) (m := m))

private lemma chainTranscriptToTagTranscript_transcript_cbcMacChainDDS
    {B : Type*} [AddCommGroup B] {ℓ q : ℕ} (hℓ : 0 < ℓ)
    (P : B → B) (inputs : Fin q → Fin ℓ → B) :
    chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ
        (DDS.transcript (cbcMacChainDDS P ℓ q) inputs)
      =
      DDS.transcript (cbcMacDDS P ℓ q) inputs := by
  classical
  funext i
  ext
  · rfl
  · -- the output is the last chaining value, which equals the CBC-MAC tag
    simp [chainTranscriptToTagTranscript, DDS.transcript, cbcMacChainDDS, cbcMacDDS,
      cbcMacChainValues_last_of_pos (P := P) (hℓ := hℓ)]

private lemma cbcMacPDS_transcriptDist_eq_fTransform_chainTranscriptDist
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS B B 1)]
    [Fintype (DDS (Fin ℓ → B) (Fin ℓ → B) q)]
    [DecidableEq (Transcript (Fin ℓ → B) B q)]
    (inputs : Fin q → Fin ℓ → B) :
    (cbcMacPDS B ℓ q).transcriptDist inputs =
      Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
        ((cbcMacChainPDS B ℓ q).transcriptDist inputs) := by
  classical
  ext t
  -- unfold both sides down to a single `fTransform` over the base uniform distribution
  simp [PDS.transcriptDist, cbcMacPDS, cbcMacChainPDS, Dist.fTransform_comp]
  -- match the two fTransform maps pointwise
  have h_point :
      ((fun s : DDS (Fin ℓ → B) B q => s.transcript inputs) ∘
          fun s : DDS B B 1 => cbcMacDDS (dds1Equiv B B s) ℓ q)
        =
      (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ) ∘
        ((fun s : DDS (Fin ℓ → B) (Fin ℓ → B) q => s.transcript inputs) ∘
          fun s : DDS B B 1 => cbcMacChainDDS (dds1Equiv B B s) ℓ q) := by
    funext s
    simpa [Function.comp] using
      (chainTranscriptToTagTranscript_transcript_cbcMacChainDDS (B := B) (ℓ := ℓ) (q := q) hℓ
        (P := dds1Equiv B B s) (inputs := inputs)).symm
  simp [h_point]

/-- The P-input associated to a *given* chaining vector `cs` (rather than recomputing the chain). -/
def cbcMacPInputFromChain {B : Type*} [AddCommGroup B] (ℓ : ℕ)
    (m : Fin ℓ → B) (cs : Fin ℓ → B) (j : Fin ℓ) : B :=
  let prev := if h : j.val = 0 then 0 else cs (finPred j h)
  prev + m j

/-- All internal P-inputs computed from a chaining-value transcript. -/
def cbcMacAllPInputsFromChainTranscript
    {B : Type*} [AddCommGroup B] {ℓ q : ℕ} (hℓ : 0 < ℓ)
    (t : Transcript (Fin ℓ → B) (Fin ℓ → B) q) : Fin (q * ℓ) → B :=
  fun k =>
    let i : Fin q :=
      ⟨k.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).2 k.isLt⟩
    let j : Fin ℓ := ⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩
    let m : Fin ℓ → B := (t i).1
    let cs : Fin ℓ → B := (t i).2
    cbcMacPInputFromChain (B := B) ℓ m cs j

/-- Flatten the chaining-value outputs from a transcript into a `Fin (q*ℓ) → B` vector. -/
def cbcMacChainOutputsFromTranscript
    {B : Type*} [AddCommGroup B] {ℓ q : ℕ} (hℓ : 0 < ℓ)
    (t : Transcript (Fin ℓ → B) (Fin ℓ → B) q) : Fin (q * ℓ) → B :=
  fun k =>
    let i : Fin q :=
      ⟨k.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).2 k.isLt⟩
    let j : Fin ℓ := ⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩
    ((t i).2) j

/-- “No internal collision” as a transcript condition on full chaining-value transcripts. -/
def noInternalCollisionChain
    (B : Type*) [DecidableEq B] [AddCommGroup B] (ℓ q : ℕ) (hℓ : 0 < ℓ) :
    TranscriptCondition (Fin ℓ → B) (Fin ℓ → B) q where
  holds := fun t => Function.Injective (cbcMacAllPInputsFromChainTranscript (B := B) (ℓ := ℓ) (q := q) hℓ t)
  dec := inferInstance


/-- At block 0, the P-input is independent of P. -/
theorem cbcMacAllPInputs_block_zero {B : Type*} [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (a : Fin (q * ℓ))
    (ha : a.val % ℓ = 0) :
    cbcMacAllPInputs P ℓ hℓ msgs a =
    msgs ⟨a.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr a.isLt⟩ ⟨0, hℓ⟩ := by
  simp only [cbcMacAllPInputs, cbcMacPInput]
  simp [ha, zero_add]

/-- Each chaining value is `P` applied to the corresponding P-input. -/
theorem cbcMacChainValues_eq_apply {B : Type*} [AddCommGroup B]
    (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) (j : Fin ℓ) :
    cbcMacChainValues P ℓ m j = P (cbcMacPInput P ℓ m j) := by
  classical
  cases ℓ with
  | zero =>
    cases j with
    | mk _ isLt => cases isLt
  | succ ℓ =>
    -- `j : Fin (ℓ+1)`; prove by induction on `j.val`.
    refine Fin.inductionOn (n := ℓ) j ?base ?step
    · -- j = 0
      simp [cbcMacChainValues, cbcMacPInput, Fin.foldl_succ, Fin.foldl_zero]
    · intro i _ih
      -- Split off the last fold step and reduce to an equality of the final message-block index.
      simp [cbcMacChainValues, cbcMacPInput, Fin.foldl_succ_last]
      -- After unfolding, this is just a `Fin`-index equality inside `m`.
      congr 1

/-- Chain stability for single-query CBC-MAC: if P₁ and P₂ agree at all
prior P-input values (within the same message), then `cbcMacPInput` at
step j is the same. -/
theorem cbcMacPInput_eq_of_agree {B : Type*} [AddCommGroup B]
    (P₁ P₂ : B → B) (ℓ : ℕ) (m : Fin ℓ → B) (j : Fin ℓ)
    (h_agree : ∀ i : Fin ℓ, i.val < j.val →
      P₁ (cbcMacPInput P₁ ℓ m i) = P₂ (cbcMacPInput P₂ ℓ m i)) :
    cbcMacPInput P₁ ℓ m j = cbcMacPInput P₂ ℓ m j := by
  classical
  by_cases h0 : j.val = 0
  · simp [cbcMacPInput, h0]
  ·
    let jpred : Fin ℓ := finPred j h0
    have hlt : jpred.val < j.val := by
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero h0
      have hsub : j.val - 1 < j.val := Nat.sub_lt hjpos Nat.one_pos
      simpa [jpred, finPred] using hsub
    have h_chain : cbcMacChainValues P₁ ℓ m jpred = cbcMacChainValues P₂ ℓ m jpred := by
      have hag := h_agree jpred hlt
      calc
        cbcMacChainValues P₁ ℓ m jpred = P₁ (cbcMacPInput P₁ ℓ m jpred) := by
          simp [cbcMacChainValues_eq_apply]
        _ = P₂ (cbcMacPInput P₂ ℓ m jpred) := hag
        _ = cbcMacChainValues P₂ ℓ m jpred := by
          simp [cbcMacChainValues_eq_apply]
    simp [cbcMacPInput, h0, jpred, h_chain]

/-- Chain stability for multi-query CBC-MAC: if P₁ and P₂ agree at all
P-input values with flat index in the same query as `a` and less than `a`,
then the P-input at index `a` is the same. -/
theorem cbcMacAllPInputs_eq_of_agree {B : Type*} [AddCommGroup B]
    (P₁ P₂ : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (a : Fin (q * ℓ))
    (h_agree : ∀ i : Fin (q * ℓ),
      i.val / ℓ = a.val / ℓ → i.val < a.val →
      P₁ (cbcMacAllPInputs P₁ ℓ hℓ msgs i) = P₂ (cbcMacAllPInputs P₂ ℓ hℓ msgs i)) :
    cbcMacAllPInputs P₁ ℓ hℓ msgs a = cbcMacAllPInputs P₂ ℓ hℓ msgs a := by
  classical
  -- Unfold the flat-index projection `a ↦ (query, block)`.
  simp only [cbcMacAllPInputs]
  -- Work with the query/block indices for `a`.
  let qa : Fin q := ⟨a.val / ℓ, by
    exact (Nat.div_lt_iff_lt_mul hℓ).2 a.isLt⟩
  let ja : Fin ℓ := ⟨a.val % ℓ, Nat.mod_lt a.val hℓ⟩
  -- After rewriting, this is a single-message chain-stability statement.
  have : cbcMacPInput P₁ ℓ (msgs qa) ja = cbcMacPInput P₂ ℓ (msgs qa) ja := by
    -- Apply the single-message lemma, discharging its hypothesis via the multi-query hypothesis.
    refine cbcMacPInput_eq_of_agree (P₁ := P₁) (P₂ := P₂) (ℓ := ℓ) (m := msgs qa) (j := ja) ?_
    intro t ht
    -- Consider the corresponding flat index within the same query `qa`.
    let bval : ℕ := (a.val / ℓ) * ℓ + t.val
    have hb_lt_a : bval < a.val := by
      have ha_decomp : (a.val / ℓ) * ℓ + a.val % ℓ = a.val := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod a.val ℓ)
      have : (a.val / ℓ) * ℓ + t.val < (a.val / ℓ) * ℓ + a.val % ℓ :=
        Nat.add_lt_add_left ht ((a.val / ℓ) * ℓ)
      simpa [bval, ha_decomp] using this
    have hb_lt_total : bval < q * ℓ := by
      have hq : a.val / ℓ < q := (Nat.div_lt_iff_lt_mul hℓ).2 a.isLt
      have ht' : t.val < ℓ := t.isLt
      have hb_lt_succ : bval < (a.val / ℓ + 1) * ℓ := by
        have : (a.val / ℓ) * ℓ + t.val < (a.val / ℓ) * ℓ + ℓ :=
          Nat.add_lt_add_left ht' ((a.val / ℓ) * ℓ)
        have hEq : (a.val / ℓ) * ℓ + ℓ = (a.val / ℓ + 1) * ℓ := by
          simp [Nat.succ_mul]
        have htmp : bval < (a.val / ℓ) * ℓ + ℓ := by
          dsimp [bval]
          exact this
        exact lt_of_lt_of_eq htmp hEq
      have hb_succ_le : (a.val / ℓ + 1) * ℓ ≤ q * ℓ :=
        Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt hq)
      exact lt_of_lt_of_le hb_lt_succ hb_succ_le
    let b : Fin (q * ℓ) := ⟨bval, hb_lt_total⟩
    have hb_div : b.val / ℓ = a.val / ℓ := by
      -- `(q*ℓ + t)/ℓ = q` when `t < ℓ`.
      calc
        b.val / ℓ = bval / ℓ := rfl
        _ = (ℓ * (a.val / ℓ) + t.val) / ℓ := by
              simp [bval, Nat.mul_comm]
        _ = (a.val / ℓ) + t.val / ℓ := by
              simpa using (Nat.mul_add_div hℓ (a.val / ℓ) t.val)
        _ = a.val / ℓ := by
              simp [Nat.div_eq_of_lt t.isLt]
    have hb_mod : b.val % ℓ = t.val := by
      simpa [b, bval] using
        (Nat.mul_add_mod_of_lt (a := a.val / ℓ) (b := ℓ) (c := t.val) t.isLt)
    -- Use `h_agree` at flat index `b` and simplify back to the single-message formulation.
    have h := h_agree b hb_div hb_lt_a
    -- Rewrite the query and block indices inside `cbcMacAllPInputs` at `b`.
    have hq_b : (⟨b.val / ℓ, by
        exact (Nat.div_lt_iff_lt_mul hℓ).2 b.isLt⟩ : Fin q) = qa := by
      ext
      simp [qa, hb_div]
    have hj_b : (⟨b.val % ℓ, Nat.mod_lt b.val hℓ⟩ : Fin ℓ) = t := by
      ext
      simp [hb_mod]
    simpa [cbcMacAllPInputs, qa, hq_b, hj_b] using h
  -- Finish by rewriting the unfolded goal.
  simpa [cbcMacAllPInputs, qa, ja] using this


/-- Auxiliary lemma: updating `P` at a point that is not used as a P-input up to `j`
does not change the P-input at index `j`. -/
theorem cbcMacPInput_update_eq_aux
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) (w : B) (x : B) (j : Fin ℓ)
    (h_not_used : ∀ i : Fin ℓ, i.val ≤ j.val → cbcMacPInput P ℓ m i ≠ w) :
    cbcMacPInput (Function.update P w x) ℓ m j =
      cbcMacPInput P ℓ m j := by
  classical
  cases ℓ with
  | zero =>
    cases j with
    | mk _ isLt => cases isLt
  | succ ℓ =>
    -- Induction on `j.val` (as `j : Fin (ℓ+1)`), keeping `h_not_used` as an explicit hypothesis.
    refine
      (Fin.inductionOn (n := ℓ)
        (motive := fun j =>
          (∀ i : Fin (ℓ + 1), i.val ≤ j.val → cbcMacPInput P (ℓ + 1) m i ≠ w) →
            cbcMacPInput (Function.update P w x) (ℓ + 1) m j =
              cbcMacPInput P (ℓ + 1) m j)
        j ?base ?step) h_not_used
    · intro _h_not_used
      -- j = 0: P-input is independent of `P`.
      simp [cbcMacPInput]
    · intro i ih h_not_used_succ
      -- Restrict `h_not_used_succ` to indices ≤ `i.castSucc`.
      have h_not_used_pred :
          ∀ t : Fin (ℓ + 1), t.val ≤ (Fin.castSucc i).val → cbcMacPInput P (ℓ + 1) m t ≠ w := by
        intro t ht
        exact h_not_used_succ t (le_trans ht (Nat.le_succ i.val))
      have h_pinput_pred :
          cbcMacPInput (Function.update P w x) (ℓ + 1) m (Fin.castSucc i) =
            cbcMacPInput P (ℓ + 1) m (Fin.castSucc i) :=
        ih h_not_used_pred
      have hneq_pred : cbcMacPInput P (ℓ + 1) m (Fin.castSucc i) ≠ w :=
        h_not_used_pred (Fin.castSucc i) le_rfl
      -- Stability of the predecessor chaining value.
      have h_chain_pred :
          cbcMacChainValues (Function.update P w x) (ℓ + 1) m (Fin.castSucc i) =
            cbcMacChainValues P (ℓ + 1) m (Fin.castSucc i) := by
        calc
          cbcMacChainValues (Function.update P w x) (ℓ + 1) m (Fin.castSucc i)
              = (Function.update P w x)
                  (cbcMacPInput (Function.update P w x) (ℓ + 1) m (Fin.castSucc i)) := by
                    simpa using
                      (cbcMacChainValues_eq_apply (P := Function.update P w x) (ℓ := ℓ + 1)
                        (m := m) (j := Fin.castSucc i))
          _ = (Function.update P w x) (cbcMacPInput P (ℓ + 1) m (Fin.castSucc i)) := by
                exact congrArg (Function.update P w x) h_pinput_pred
          _ = P (cbcMacPInput P (ℓ + 1) m (Fin.castSucc i)) := by
                simp [Function.update, hneq_pred]
          _ = cbcMacChainValues P (ℓ + 1) m (Fin.castSucc i) := by
                simpa using
                  (cbcMacChainValues_eq_apply (P := P) (ℓ := ℓ + 1) (m := m) (j := Fin.castSucc i)).symm
      -- Now unfold `cbcMacPInput` at `i.succ`.
      have hpred :
          (⟨(i.succ : Fin (ℓ + 1)).val - 1, by omega⟩ : Fin (ℓ + 1)) =
            Fin.castSucc i := by
        ext; simp
      -- Unfold at `i.succ`; `simp` cancels the common `+ m i.succ`, leaving a
      -- predecessor chaining-value equality.
      simp [cbcMacPInput]
      simpa using h_chain_pred

/-- Chain stability: if `w` is not any P-input at blocks 0 through `j` of message `m`,
then updating P at `w` preserves the chain values and P-inputs through block `j`.

This is the key lemma for the injection argument in the collision bound proof:
under `goodUpTo`, modifying P at the j-th P-input doesn't affect P-inputs at
indices ≤ j (since those use P at distinct earlier points). -/
theorem cbcMacChainValues_update_eq
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) (w : B) (x : B) (j : Fin ℓ)
    (h_not_used : ∀ i : Fin ℓ, i.val ≤ j.val → cbcMacPInput P ℓ m i ≠ w) :
    cbcMacChainValues (Function.update P w x) ℓ m j =
    cbcMacChainValues P ℓ m j := by
  classical
  have hj_neq : cbcMacPInput P ℓ m j ≠ w := h_not_used j le_rfl
  have hj_inp :
      cbcMacPInput (Function.update P w x) ℓ m j = cbcMacPInput P ℓ m j :=
    cbcMacPInput_update_eq_aux P ℓ m w x j h_not_used
  calc
    cbcMacChainValues (Function.update P w x) ℓ m j
        = (Function.update P w x) (cbcMacPInput (Function.update P w x) ℓ m j) := by
            simpa using
              (cbcMacChainValues_eq_apply (P := Function.update P w x) (ℓ := ℓ) (m := m) (j := j))
    _ = (Function.update P w x) (cbcMacPInput P ℓ m j) := by
          exact congrArg (Function.update P w x) hj_inp
    _ = P (cbcMacPInput P ℓ m j) := by
          simp [Function.update, hj_neq]
    _ = cbcMacChainValues P ℓ m j := by
          simpa using (cbcMacChainValues_eq_apply (P := P) (ℓ := ℓ) (m := m) (j := j)).symm

/-- P-input stability: if `w` is not any P-input at blocks 0 through `j` of
message `m`, then updating P at `w` preserves the P-input at block `j`. -/
theorem cbcMacPInput_update_eq
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) (w : B) (x : B) (j : Fin ℓ)
    (h_not_used : ∀ i : Fin ℓ, i.val ≤ j.val → cbcMacPInput P ℓ m i ≠ w) :
    cbcMacPInput (Function.update P w x) ℓ m j =
    cbcMacPInput P ℓ m j := by
  exact cbcMacPInput_update_eq_aux P ℓ m w x j h_not_used

/-- The "no internal collision" predicate on a function P and messages.

Given P : B → B and q messages of ℓ blocks each, this checks whether
all q·ℓ P-inputs (the values fed to P during CBC-MAC computation) are
distinct. When this holds, each P-application receives a fresh input,
so its output is independent of all other outputs under uniform P. -/
def isGoodFunction {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ) (msgs : Fin q → Fin ℓ → B) : Prop :=
  Function.Injective (cbcMacAllPInputs P ℓ hℓ msgs)

instance {B : Type*} [DecidableEq B] [AddCommGroup B] [Fintype B]
    {P : B → B} {q ℓ : ℕ} {hℓ : 0 < ℓ} {msgs : Fin q → Fin ℓ → B} :
    Decidable (isGoodFunction P ℓ hℓ msgs) :=
  show Decidable (Function.Injective (cbcMacAllPInputs P ℓ hℓ msgs)) from inferInstance

/-
╔══════════════════════════════════════════════════════════════════════════════╗
║ Historical note (preserved): an earlier attempt stated conditional           ║
║ equivalence *pointwise* on tag transcripts by summing over “good” functions. ║
║ That statement is too strong: summing over all transcripts would force       ║
║ `Pr[good]=1`.                                                                ║
║                                                                              ║
║ The correct Maurer-style conditioning is transcript-based. For CBC-MAC,      ║
║ the condition becomes transcript-measurable once we instrument the system    ║
║ to output the full chaining-value vectors.                                   ║
╚══════════════════════════════════════════════════════════════════════════════╝
-/

/-! ### Conditional equivalence on full chaining-value transcripts

On transcripts where all internal P-inputs are distinct (computed from the
message blocks and the chaining values), CBC-MAC with a uniform random function
is pointwise identical to `Instances.URF` over chaining-value vectors (i.e. the
uniform-over-DDS ideal, which on distinct inputs coincides with the usual random
function oracle). This matches the
paper proof structure: “good transcripts” correspond to fixing the random
function at `q·ℓ` distinct points. -/

private lemma card_fiber_multipoint
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n : ℕ} (nonces : Fin n → X) (ys : Fin n → Y) (h_inj : Function.Injective nonces) :
    (Finset.univ.filter (fun f : X → Y => (fun i => f (nonces i)) = ys)).card
    = Fintype.card Y ^ (Fintype.card X - n) := by
  set S := (Finset.univ : Finset (Fin n)).image nonces
  have hS_card : S.card = n := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]
  rw [show Fintype.card Y ^ (Fintype.card X - n) = Fintype.card (↥Sᶜ → Y) from by
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl, hS_card]]
  apply Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x)
    (fun _ _ => Finset.mem_univ _)
    (fun f₁ hf₁ f₂ hf₂ h => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
      ext x
      by_cases hx : x ∈ S
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        -- use equality on the fixed coordinates
        have h1 : f₁ (nonces i) = ys i := congr_fun hf₁ i
        have h2 : f₂ (nonces i) = ys i := congr_fun hf₂ i
        exact h1.trans h2.symm
      · exact congr_fun h ⟨x, Finset.mem_compl.mpr hx⟩)
    (fun g _ => by
      have h_ext : ∀ x ∈ S, ∃! i : Fin n, nonces i = x := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨i, rfl, fun j hj => h_inj hj⟩
      refine ⟨fun x =>
        if hx : x ∈ S then ys ((h_ext x hx).choose)
        else g ⟨x, Finset.mem_compl.mpr hx⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        ext i
        have h_mem : nonces i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
        show dite (nonces i ∈ S) _ _ = ys i
        rw [dif_pos h_mem]
        have hcs := (h_ext (nonces i) h_mem).choose_spec
        congr 1
        exact h_inj hcs.1
      · ext ⟨x, hx⟩
        show dite (x ∈ S) _ _ = g ⟨x, hx⟩
        rw [dif_neg (Finset.mem_compl.mp hx)])

private lemma eval_nonces_uniform
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n : ℕ} (nonces : Fin n → X) (h_inj : Function.Injective nonces)
    [Nonempty (Fin n → Y)] :
    Dist.fTransform (fun f : X → Y => fun i => f (nonces i))
      (Dist.uniform (X → Y)) = Dist.uniform (Fin n → Y) := by
  classical
  ext ys
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, Dist.uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
      (fun _ : X → Y => (1 : NNReal) / (Fintype.card (X → Y) : NNReal))).support = Finset.univ := by
    ext s; simp [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  congr 1
  · rw [card_fiber_multipoint (X := X) (Y := Y) nonces ys h_inj, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin]
    simp only [Nat.cast_pow]
    have hY : (Fintype.card Y : NNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos (α := Y).ne'
    have hn : n ≤ Fintype.card X :=
      Fintype.card_fin n ▸ Fintype.card_le_of_injective nonces h_inj
    rw [show (Fintype.card Y : NNReal) ^ Fintype.card X =
        (Fintype.card Y : NNReal) ^ (Fintype.card X - n) * (Fintype.card Y : NNReal) ^ n from by
      rw [← pow_add, Nat.sub_add_cancel hn]]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hY), one_div]

/-! Helper: explicit fiber-sum form of `Dist.fTransform` evaluation.

This is now available as `Dist.fTransform_apply_eq_sum` in `RandomSystems.Dist`. -/

private lemma cbcMacChainValues_eq_of_forall_apply_pInputFromChain
    {B : Type*} [AddCommGroup B] {ℓ : ℕ}
    (P : B → B) (m : Fin ℓ → B) (cs : Fin ℓ → B)
    (h : ∀ j : Fin ℓ, P (cbcMacPInputFromChain (B := B) ℓ m cs j) = cs j) :
    cbcMacChainValues P ℓ m = cs := by
  classical
  funext j
  -- Induction on j.val
  cases ℓ with
  | zero =>
    cases j with
    | mk _ isLt => cases isLt
  | succ ℓ =>
    -- `j : Fin (ℓ+1)`
    refine Fin.inductionOn (n := ℓ) j ?base ?step
    · -- j = 0
      have h0 : P (cbcMacPInputFromChain (B := B) (ℓ := ℓ + 1) m cs ⟨0, Nat.succ_pos _⟩) =
          cs ⟨0, Nat.succ_pos _⟩ := h ⟨0, Nat.succ_pos _⟩
      -- cbcMacChainValues at 0 is P(0 + m0)
      have h0' : P (m ⟨0, Nat.succ_pos _⟩) = cs ⟨0, Nat.succ_pos _⟩ := by
        simpa [cbcMacPInputFromChain] using h0
      simpa [cbcMacChainValues, Fin.foldl_succ, Fin.foldl_zero] using h0'
    · intro i ih
      -- step i.succ
      have hi : P (cbcMacPInputFromChain (B := B) (ℓ := ℓ + 1) m cs i.succ) =
          cs i.succ := h i.succ
      -- rewrite cbcMacPInput at i.succ using ih
      have h_prev :
          cbcMacChainValues P (ℓ + 1) m (Fin.castSucc i) = cs (Fin.castSucc i) := by
        simpa using ih
      -- now unfold chain value at i.succ using `cbcMacChainValues_eq_apply`
      -- and the corresponding P-input definition
      have h_pinput :
          cbcMacPInput P (ℓ + 1) m i.succ =
            cbcMacPInputFromChain (B := B) (ℓ := ℓ + 1) m cs i.succ := by
        have h0 : (i.succ : Fin (ℓ + 1)).val ≠ 0 := by
          simp
        have hpred : finPred (n := ℓ + 1) i.succ h0 = Fin.castSucc i :=
          finPred_succ_eq_castSucc (n := ℓ) i h0
        simp [cbcMacPInput, cbcMacPInputFromChain, hpred, h_prev]
      calc
        cbcMacChainValues P (ℓ + 1) m i.succ
            = P (cbcMacPInput P (ℓ + 1) m i.succ) := by
                simpa using (cbcMacChainValues_eq_apply (P := P) (ℓ := ℓ + 1) (m := m) (j := i.succ))
        _ = P (cbcMacPInputFromChain (B := B) (ℓ := ℓ + 1) m cs i.succ) := by
              simp [h_pinput]
        _ = cs i.succ := hi

private lemma cbcMacAllPInputsFromChainTranscript_eq_allPInputs
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ) (P : B → B) (inputs : Fin q → Fin ℓ → B) :
    cbcMacAllPInputsFromChainTranscript (B := B) (ℓ := ℓ) (q := q) hℓ
      (DDS.transcript (cbcMacChainDDS P ℓ q) inputs) =
    cbcMacAllPInputs P ℓ hℓ inputs := by
  funext k
  -- unfold both sides at k; the key is that the chain transcript at query i stores
  -- `cbcMacChainValues P ℓ (inputs i)` as its output vector.
  simp [cbcMacAllPInputsFromChainTranscript, cbcMacAllPInputs, cbcMacPInputFromChain,
    cbcMacChainDDS, DDS.transcript, cbcMacPInput]

private lemma noInternalCollisionChain_holds_transcript_iff_isGoodFunction
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ) (P : B → B) (inputs : Fin q → Fin ℓ → B) :
    (noInternalCollisionChain B ℓ q hℓ).holds (DDS.transcript (cbcMacChainDDS P ℓ q) inputs) ↔
      isGoodFunction P ℓ hℓ inputs := by
  -- unfold the two injectivity predicates and rewrite via `cbcMacAllPInputsFromChainTranscript_eq_allPInputs`
  simp [noInternalCollisionChain, isGoodFunction,
    cbcMacAllPInputsFromChainTranscript_eq_allPInputs (B := B) (ℓ := ℓ) (q := q) hℓ P inputs]

/-! ### URF output uniformity (generic)

We use the same decomposition pattern as in `CTRMode` / `PRPPRFSwitchingGeneral`:
splitting each `respond i` function at the concrete query prefix extracts the
output vector as the first component of an equivalence, so pushing forward the
uniform DDS distribution yields a uniform output vector. -/

private def urfOutputMap {X Y : Type*} {q : ℕ} (inputs : Fin q → X) (s : DDS X Y q) :
    Fin q → Y :=
  fun i => s.respond i (fun j => inputs ⟨j.val,
    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)

private def transcriptEmbed' {X Y : Type*} {q : ℕ} (inputs : Fin q → X) (ys : Fin q → Y) :
    Transcript X Y q :=
  fun i => (inputs i, ys i)

private lemma transcript_factors {X Y : Type*} {q : ℕ} (inputs : Fin q → X) :
    (fun s : DDS X Y q => DDS.transcript s inputs) =
    transcriptEmbed' inputs ∘ urfOutputMap inputs := by
  funext s i
  simp [DDS.transcript, urfOutputMap, transcriptEmbed']

private lemma transcriptEmbed'_injective {X Y : Type*} {q : ℕ} (inputs : Fin q → X) :
    Function.Injective (transcriptEmbed' (X := X) (Y := Y) (q := q) inputs) := by
  intro ys₁ ys₂ h
  funext i
  exact (Prod.mk.inj (congr_fun h i)).2

private def piProdEquiv {A : Type*} {ι : Type*} {B : ι → Type*} :
    ((i : ι) → A × B i) ≃ (ι → A) × ((i : ι) → B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv f := by ext i <;> simp
  right_inv p := by ext <;> simp

private def qPrefix {X : Type*} {q : ℕ} (inputs : Fin q → X) (i : Fin q) : Fin (i.val + 1) → X :=
  fun j => inputs ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩

private def ddsDecomp {X Y : Type*} [Fintype X] [DecidableEq X] {q : ℕ} (inputs : Fin q → X) :
    DDS X Y q ≃
    (Fin q → Y) ×
    ((i : Fin q) → ({f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → Y)) :=
  (DDS.equivRespond X Y q).trans
    ((Equiv.piCongrRight (fun i => Equiv.funSplitAt (qPrefix inputs i) Y)).trans
      (piProdEquiv (A := Y) (B := fun i => {f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → Y)))

private lemma urfOutput_eq_fst_decomp {X Y : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    (inputs : Fin q → X) :
    urfOutputMap inputs = Prod.fst ∘ ddsDecomp (X := X) (Y := Y) inputs := by
  funext s
  rfl

private lemma urf_output_uniform
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {q : ℕ} [Fintype (DDS X Y q)] [Nonempty (DDS X Y q)]
    (inputs : Fin q → X) [Nonempty (Fin q → Y)] :
    Dist.fTransform (urfOutputMap inputs) (Dist.uniform (DDS X Y q)) =
    Dist.uniform (Fin q → Y) := by
  classical
  rw [urfOutput_eq_fst_decomp (X := X) (Y := Y) inputs]
  rw [← Dist.fTransform_comp Prod.fst (ddsDecomp (X := X) (Y := Y) inputs) _]
  haveI : Nonempty ((Fin q → Y) ×
      ((i : Fin q) → ({f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → Y))) :=
    ⟨(ddsDecomp (X := X) (Y := Y) inputs) (Classical.arbitrary _)⟩
  rw [Dist.fTransform_equiv_uniform (ddsDecomp (X := X) (Y := Y) inputs)]
  haveI : Nonempty ((i : Fin q) → ({f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → Y)) :=
    ⟨((ddsDecomp (X := X) (Y := Y) inputs) (Classical.arbitrary _)).2⟩
  exact Dist.fTransform_fst_uniform _ _

/-! ### Bridging `URF` (uniform over DDS) and `URFfun` (uniform function oracle)

`Instances.URF` is uniform over *all* DDS, hence its outputs are independent
uniform even under repeated inputs (beacon-like).

For game-based PRF/RO reasoning we also need the *uniform random function*
oracle (`Instances.URFfun`), which answers repeated inputs consistently. On a
fixed input sequence with no repeats (injective `inputs`), both notions induce
the same transcript distribution. -/

private lemma urfFun_output_uniform_of_injective
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : ℕ} [Fintype (DDS X Y q)]
    (inputs : Fin q → X) (h_inj : Function.Injective inputs) :
    Dist.fTransform (urfOutputMap inputs)
        (Instances.URFfun (X := X) (Y := Y) (q := q)).dist
      =
      Dist.uniform (Fin q → Y) := by
  classical
  -- Reduce to evaluating a uniform random function on `inputs`.
  -- `URFfun.dist = fTransform (DDS.ofFunq) (uniform (X → Y))`.
  simp [Instances.URFfun, Instances.URFfunOf]
  -- Push `urfOutputMap` through the embedding `DDS.ofFunq`.
  rw [Dist.fTransform_comp]
  -- Now apply the evaluation-uniformity lemma for injective inputs.
  -- `urfOutputMap inputs (DDS.ofFunq f)` is the output vector `i ↦ f (inputs i)`.
  have h_eval :
      (fun f : X → Y => urfOutputMap inputs (DDS.ofFunq (q := q) f)) =
        (fun f : X → Y => fun i : Fin q => f (inputs i)) := by
    funext f i
    simp [urfOutputMap, DDS.ofFunq]
  simpa [h_eval] using (eval_nonces_uniform (X := X) (Y := Y) (n := q) inputs h_inj)

private lemma urfFun_transcriptDist_eq_urf_transcriptDist_of_injective
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : ℕ} [Fintype (DDS X Y q)] [Nonempty (DDS X Y q)]
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (inputs : Fin q → X) (h_inj : Function.Injective inputs) :
    (Instances.URFfun (X := X) (Y := Y) (q := q)).transcriptDist inputs
      =
      (Instances.URF (X := X) (Y := Y) (q := q)).transcriptDist inputs := by
  classical
  haveI : Nonempty (Fin q → Y) := ⟨fun _ => Classical.arbitrary Y⟩
  -- Both transcript distributions factor through the output-vector distribution.
  have h_tr :
      (fun s : DDS X Y q => DDS.transcript s inputs) =
        (transcriptEmbed' (X := X) (Y := Y) (q := q) inputs) ∘ urfOutputMap inputs := by
    exact transcript_factors (inputs := inputs)
  -- URF side: always uniform on output vectors.
  have h_out_urf :
      Dist.fTransform (urfOutputMap inputs) (Instances.URF (X := X) (Y := Y) (q := q)).dist
        =
        Dist.uniform (Fin q → Y) := by
    simpa [Instances.URF] using (urf_output_uniform (X := X) (Y := Y) (q := q) inputs)
  -- URFfun side: uniform on output vectors when inputs are injective.
  have h_out_fun :
      Dist.fTransform (urfOutputMap inputs)
          (Instances.URFfun (X := X) (Y := Y) (q := q)).dist
        =
        Dist.uniform (Fin q → Y) :=
    urfFun_output_uniform_of_injective (X := X) (Y := Y) (q := q) inputs h_inj
  -- Convert output-vector equality into transcriptDist equality.
  -- Both sides are `fTransform transcriptEmbed'` of the corresponding output-vector dist.
  simp [PDS.transcriptDist, h_tr]
  rw [← Dist.fTransform_comp (g := transcriptEmbed' (X := X) (Y := Y) (q := q) inputs)
        (f := urfOutputMap inputs)
        (X := (Instances.URFfun (X := X) (Y := Y) (q := q)).dist)]
  rw [← Dist.fTransform_comp (g := transcriptEmbed' (X := X) (Y := Y) (q := q) inputs)
        (f := urfOutputMap inputs)
        (X := (Instances.URF (X := X) (Y := Y) (q := q)).dist)]
  -- Rewrite the inner output-vector distributions to the same uniform distribution.
  rw [h_out_fun, h_out_urf]

private def lastIndex {ℓ : ℕ} (hℓ : 0 < ℓ) : Fin ℓ :=
  ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩

private lemma urf_outputVec_last_uniform
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ) [Nonempty (Fin q → Fin ℓ → B)] :
    Dist.fTransform (fun ys : Fin q → Fin ℓ → B => fun i : Fin q => ys i (lastIndex (ℓ := ℓ) hℓ))
        (Dist.uniform (Fin q → Fin ℓ → B))
      =
      Dist.uniform (Fin q → B) := by
  classical
  let last : Fin ℓ := lastIndex (ℓ := ℓ) hℓ
  let decomp : (Fin q → Fin ℓ → B) ≃
      (Fin q → B) × (Fin q → ({j : Fin ℓ // j ≠ last} → B)) :=
    (Equiv.piCongrRight (fun _ : Fin q => (Equiv.funSplitAt last B))).trans
      (piProdEquiv (A := B) (B := fun _ : Fin q => {j : Fin ℓ // j ≠ last} → B))
  have h_proj :
      (fun ys : Fin q → Fin ℓ → B => fun i : Fin q => ys i last) =
        Prod.fst ∘ decomp := by
    funext ys i
    simp [decomp, piProdEquiv, Equiv.trans_apply, Function.comp]
  rw [h_proj]
  rw [← Dist.fTransform_comp Prod.fst decomp _]
  haveI : Nonempty ((Fin q → B) × (Fin q → ({j : Fin ℓ // j ≠ last} → B))) :=
    ⟨decomp (Classical.arbitrary _)⟩
  rw [Dist.fTransform_equiv_uniform decomp]
  haveI : Nonempty (Fin q → ({j : Fin ℓ // j ≠ last} → B)) :=
    ⟨(decomp (Classical.arbitrary _)).2⟩
  exact Dist.fTransform_fst_uniform _ _

set_option maxHeartbeats 800000 in
private lemma urf_tag_transcriptDist_eq_fTransform_chainTranscriptDist
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS (Fin ℓ → B) B q)]
    [Nonempty (DDS (Fin ℓ → B) (Fin ℓ → B) q)]
    [Fintype (Transcript (Fin ℓ → B) B q)] [DecidableEq (Transcript (Fin ℓ → B) B q)]
    (inputs : Fin q → Fin ℓ → B) :
    Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
        ((Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs)
      =
      (Instances.URF (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs := by
  classical
  -- Avoid Fintype-instance diamonds on `(Fin ℓ → B)` and derived Pi-types.
  letI : Fintype (Fin ℓ → B) := Pi.instFintype
  haveI : Nonempty (Fin q → Fin ℓ → B) := ⟨fun _ _ => 0⟩
  haveI : Nonempty (Fin q → B) := ⟨fun _ => 0⟩
  -- Rewrite both transcript distributions as `fTransform transcriptEmbed'` of a uniform output vector.
  have h_chain :
      (Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs =
        Dist.fTransform (transcriptEmbed' (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs)
          (Dist.uniform (Fin q → Fin ℓ → B)) := by
    simp only [PDS.transcriptDist, Instances.URF]
    rw [transcript_factors (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs]
    rw [← Dist.fTransform_comp]
    rw [urf_output_uniform (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs]
  have h_tag :
      (Instances.URF (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs =
        Dist.fTransform (transcriptEmbed' (X := Fin ℓ → B) (Y := B) (q := q) inputs)
          (Dist.uniform (Fin q → B)) := by
    simp only [PDS.transcriptDist, Instances.URF]
    rw [transcript_factors (X := Fin ℓ → B) (Y := B) (q := q) inputs]
    rw [← Dist.fTransform_comp]
    rw [urf_output_uniform (X := Fin ℓ → B) (Y := B) (q := q) inputs]
  -- Commute the transcript projection with `transcriptEmbed'`, reducing to a uniformity fact.
  let projYs : (Fin q → Fin ℓ → B) → (Fin q → B) :=
    fun ys => fun i => ys i (lastIndex (ℓ := ℓ) hℓ)
  have h_comm :
      (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ) ∘
          (transcriptEmbed' (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs)
        =
      (transcriptEmbed' (X := Fin ℓ → B) (Y := B) (q := q) inputs) ∘ projYs := by
    funext ys i
    simp [chainTranscriptToTagTranscript, transcriptEmbed', projYs, lastIndex, Function.comp, lastIndex]
  -- Rewrite the LHS down to a uniform output vector, commuting the projection with `transcriptEmbed'`.
  have h1 :
      Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
          ((Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs)
        =
        Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
          (Dist.fTransform (transcriptEmbed' (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs)
            (Dist.uniform (Fin q → Fin ℓ → B))) := by
    simpa using congrArg
      (fun D =>
        Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ) D)
      h_chain
  refine h1.trans ?_
  rw [Dist.fTransform_comp
    (g := chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
    (f := transcriptEmbed' (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs)
    (X := Dist.uniform (Fin q → Fin ℓ → B))]
  rw [h_comm]
  rw [(Dist.fTransform_comp
    (g := transcriptEmbed' (X := Fin ℓ → B) (Y := B) (q := q) inputs)
    (f := projYs)
    (X := Dist.uniform (Fin q → Fin ℓ → B))).symm]
  have h_projYs :
      Dist.fTransform projYs (Dist.uniform (Fin q → Fin ℓ → B)) =
        Dist.uniform (Fin q → B) := by
    simpa [projYs] using (urf_outputVec_last_uniform (B := B) (ℓ := ℓ) (q := q) hℓ)
  rw [h_projYs]
  exact h_tag.symm

/-- Conditional equivalence (paper-style): on good *chaining-value* transcripts,
instrumented CBC-MAC matches URF. -/
theorem cbcMac_cond_equiv_urf
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) (Fin ℓ → B) q)] [Nonempty (DDS (Fin ℓ → B) (Fin ℓ → B) q)]
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    [Fintype (Transcript (Fin ℓ → B) (Fin ℓ → B) q)]
    [DecidableEq (Transcript (Fin ℓ → B) (Fin ℓ → B) q)] :
    (cbcMacChainPDS B ℓ q).condEquiv
      (Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q))
      (noInternalCollisionChain B ℓ q hℓ) := by
  classical
  -- Avoid Fintype-instance diamonds: `cbcMacChainPDS` uses `DDS.instFintype` for `DDS B B 1`.
  letI : Fintype (DDS B B 1) := DDS.instFintype (X := B) (Y := B) (q := 1)
  intro inputs t ht
  -- Split on whether `t` has the correct input components (transcripts always record `inputs`).
  by_cases h_inputs : ∀ i : Fin q, (t i).1 = inputs i
  · -- In-range case: `t = transcriptEmbed' inputs ys`
    let ys : Fin q → Fin ℓ → B := fun i => (t i).2
    have ht_embed : t = transcriptEmbed' inputs ys := by
      funext i
      exact Prod.ext (h_inputs i) rfl
    -- URF side: uniform on output vectors
    haveI : Nonempty (Fin q → Fin ℓ → B) := ⟨ys⟩
    have h_urf :
        (Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs t =
        (Dist.uniform (Fin q → Fin ℓ → B)) ys := by
      -- factor the transcript map through `transcriptEmbed' inputs`
      simp only [PDS.transcriptDist, Instances.URF]
      rw [transcript_factors (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs]
      rw [← Dist.fTransform_comp]
      rw [urf_output_uniform (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs]
      -- evaluate via injectivity of transcriptEmbed'
      rw [ht_embed]
      simpa using
        (fTransform_injective_apply (X := Dist.uniform (Fin q → Fin ℓ → B))
          (f := transcriptEmbed' inputs)
          (hf := transcriptEmbed'_injective (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q) inputs)
          ys)
    -- CBC side: on good transcripts, the transcript mass is `1 / |B|^(q*ℓ)`
    -- because it fixes the underlying random function at `q*ℓ` distinct internal inputs.
    let nonces := cbcMacAllPInputsFromChainTranscript (B := B) (ℓ := ℓ) (q := q) hℓ t
    let outs := cbcMacChainOutputsFromTranscript (B := B) (ℓ := ℓ) (q := q) hℓ t
    have h_inj_nonces : Function.Injective nonces := ht
    -- Evaluate CBC transcriptDist as a sum over (single-query) DDS, then rewrite the fiber
    -- `{s | transcript(cbcMacChainDDS (dds1Equiv s)) = t}` as `{s | eval(nonces)=outs}`.
    have h_cbc :
        (cbcMacChainPDS B ℓ q).transcriptDist inputs t =
        (Dist.uniform (Fin (q * ℓ) → B)) outs := by
      -- Unfold the pushforward twice: first to the transcript, then to the nonce-evaluation vector.
      -- Step 1: expand transcriptDist
      simp only [PDS.transcriptDist, cbcMacChainPDS, Dist.fTransform_comp]
      -- Now goal is the evaluation of an fTransform; expand it as a fiber-sum.
      -- We show this equals the fiber-sum for evaluating at `nonces`.
      -- The key equivalence: for any function f, producing transcript t ↔ f(nonces)=outs.
      have h_fiber : ∀ s : DDS B B 1,
          DDS.transcript (cbcMacChainDDS (dds1Equiv B B s) ℓ q) inputs = t ↔
            (fun k : Fin (q * ℓ) => (dds1Equiv B B s) (nonces k)) = outs := by
        intro s
        -- forward: transcript equality implies the point constraints
        constructor
        · intro hs
          funext k
          -- unpack flat index
          let i : Fin q := ⟨k.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).2 k.isLt⟩
          let j : Fin ℓ := ⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩
          have hti : (t i).1 = inputs i := h_inputs i
          -- output vector equality at query i
          have hs_i : (cbcMacChainValues (dds1Equiv B B s) ℓ (inputs i)) = (t i).2 := by
            -- from transcript equality at index i
            have := congr_fun hs i
            simp [cbcMacChainDDS, DDS.transcript] at this
            -- this : (inputs i, chainValues ...) = (t i)
            exact (Prod.mk.inj this).2
          -- derive point constraint at block j using the chain recurrence
          have h_point : (dds1Equiv B B s)
              (cbcMacPInputFromChain (B := B) ℓ (inputs i) ((t i).2) j) = ((t i).2) j := by
            -- from hs_i we get chainValues = (t i).2, then unfold the defining equation for chain values
            have hj : cbcMacChainValues (dds1Equiv B B s) ℓ (inputs i) j = (t i).2 j := by
              exact congrArg (fun f => f j) hs_i
            -- rewrite chainValues via `cbcMacChainValues_eq_apply` and replace the computed pinput by `pInputFromChain`
            have h_pinput :
                cbcMacPInput (dds1Equiv B B s) ℓ (inputs i) j =
                  cbcMacPInputFromChain (B := B) ℓ (inputs i) ((t i).2) j := by
              -- unfold both; only the predecessor chain value matters
              by_cases hj0 : j.val = 0
              · simp [cbcMacPInput, cbcMacPInputFromChain, hj0]
              · -- predecessor chain value uses `hs_i`
                have h_prev :
                    cbcMacChainValues (dds1Equiv B B s) ℓ (inputs i)
                      (finPred j hj0) =
                    (t i).2 (finPred j hj0) := by
                  exact congrArg (fun f => f (finPred j hj0)) hs_i
                simp [cbcMacPInput, cbcMacPInputFromChain, hj0, h_prev]
            -- finish: chainValues = P(pinput)
            have := congrArg (fun z => z) (cbcMacChainValues_eq_apply
              (P := dds1Equiv B B s) (ℓ := ℓ) (m := inputs i) (j := j))
            -- `this` is definitional; use it to rewrite hj
            -- (avoid rewriting the whole goal; just `simp` with h_pinput)
            have : cbcMacChainValues (dds1Equiv B B s) ℓ (inputs i) j =
                (dds1Equiv B B s) (cbcMacPInput (dds1Equiv B B s) ℓ (inputs i) j) := by
              simpa using (cbcMacChainValues_eq_apply (P := dds1Equiv B B s) (ℓ := ℓ)
                (m := inputs i) (j := j))
            -- rearrange to get the desired point constraint
            -- from `hj` and `this`
            calc
              (dds1Equiv B B s)
                  (cbcMacPInputFromChain (B := B) ℓ (inputs i) ((t i).2) j)
                  = (dds1Equiv B B s) (cbcMacPInput (dds1Equiv B B s) ℓ (inputs i) j) := by
                      simp [h_pinput]
              _ = cbcMacChainValues (dds1Equiv B B s) ℓ (inputs i) j := by
                      simp [this]
              _ = (t i).2 j := hj
          -- match definitions of `nonces` and `outs`
          simp [nonces, outs, cbcMacAllPInputsFromChainTranscript, cbcMacChainOutputsFromTranscript,
            cbcMacPInputFromChain, i, j, hti] at h_point ⊢
          exact h_point
        · -- reverse: point constraints imply transcript equality
          intro h_eval
          funext i
          -- show (inputs i, chainValues ...) = t i
          apply Prod.ext
          · exact (h_inputs i).symm
          · -- show chainValues = (t i).2 using the per-block constraints extracted from h_eval
            have h_blocks :
                ∀ j : Fin ℓ,
                  (dds1Equiv B B s)
                    (cbcMacPInputFromChain (B := B) ℓ (inputs i) ((t i).2) j) = ((t i).2) j := by
              intro j
              -- pick corresponding flat index k for (i,j) as `j + ℓ*i`
              let kNat : ℕ := j.val + ℓ * i.val
              have hkNat_lt : kNat < q * ℓ := by
                have hjlt : j.val < ℓ := j.isLt
                have hi_le : i.val + 1 ≤ q := Nat.succ_le_of_lt i.isLt
                have h1 : kNat < ℓ * (i.val + 1) := by
                  -- j + ℓ*i < ℓ + ℓ*i = ℓ*(i+1)
                  have h' : j.val + ℓ * i.val < ℓ + ℓ * i.val :=
                    Nat.add_lt_add_right hjlt (ℓ * i.val)
                  have h'' : kNat < ℓ + ℓ * i.val := by
                    dsimp [kNat]
                    exact h'
                  have hEq : ℓ + ℓ * i.val = ℓ * (i.val + 1) := by
                    simp [Nat.mul_succ, Nat.add_comm]
                  exact lt_of_lt_of_eq h'' hEq
                have h2 : ℓ * (i.val + 1) ≤ ℓ * q := Nat.mul_le_mul_left ℓ hi_le
                have : kNat < ℓ * q := lt_of_lt_of_le h1 h2
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              let k : Fin (q * ℓ) := ⟨kNat, hkNat_lt⟩
              have hk : (fun k : Fin (q * ℓ) => (dds1Equiv B B s) (nonces k)) k = outs k := by
                simpa using congrArg (fun f => f k) h_eval
              -- compute the div/mod used in `nonces` / `outs` for this k
              have h_div : k.val / ℓ = i.val := by
                have hpos : 0 < ℓ := hℓ
                -- (j + ℓ*i)/ℓ = j/ℓ + i = i since j<ℓ
                calc
                  k.val / ℓ = (j.val / ℓ) + i.val := by
                    simpa [k, kNat, Nat.mul_comm] using (Nat.add_mul_div_left j.val i.val hpos)
                  _ = i.val := by simp [Nat.div_eq_of_lt j.isLt]
              have h_mod : k.val % ℓ = j.val := by
                calc
                  k.val % ℓ = (j.val % ℓ) := by
                    simp [k, kNat]
                  _ = j.val := Nat.mod_eq_of_lt j.isLt
              have hiFin :
                  (⟨k.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).2 k.isLt⟩ : Fin q) = i := by
                apply Fin.ext
                simp [h_div]
              have hjFin : (⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩ : Fin ℓ) = j := by
                apply Fin.ext
                simp [h_mod]
              -- unfold `nonces`/`outs` at k and rewrite the computed indices to (i,j)
              -- (also use that (t i).1 = inputs i)
              simpa [nonces, outs, cbcMacAllPInputsFromChainTranscript, cbcMacChainOutputsFromTranscript,
                cbcMacPInputFromChain, h_div, h_mod, hiFin, hjFin, h_inputs i] using hk
            -- apply the single-message reconstruction lemma
            exact cbcMacChainValues_eq_of_forall_apply_pInputFromChain
              (P := dds1Equiv B B s) (m := inputs i) (cs := (t i).2) h_blocks
      -- Step 2: rewrite the fTransform fiber at `t` using `h_fiber`
      -- and compute it via the nonce-evaluation distribution.
      -- Expand via the fiber-sum form of `fTransform`.
      let g : DDS B B 1 → Transcript (Fin ℓ → B) (Fin ℓ → B) q :=
        fun s => (cbcMacChainDDS (dds1Equiv B B s) ℓ q).transcript inputs
      let evalMap : DDS B B 1 → Fin (q * ℓ) → B :=
        fun s => fun k => (dds1Equiv B B s) (nonces k)
      -- Replace the composed transcript map with `g` to use the fiber-sum lemma.
      change (Dist.fTransform g (Dist.uniform (DDS B B 1))) t =
        (Dist.uniform (Fin (q * ℓ) → B)) outs
      rw [Dist.fTransform_apply_eq_sum (f := g) (X := Dist.uniform (DDS B B 1)) (b := t)]
      have h_filter :
          (Finset.univ : Finset (DDS B B 1)).filter (fun s => g s = t) =
          (Finset.univ : Finset (DDS B B 1)).filter (fun s => evalMap s = outs) := by
        ext s
        simp [g, evalMap, h_fiber s]
      rw [h_filter]
      rw [← Dist.fTransform_apply_eq_sum (f := evalMap) (X := Dist.uniform (DDS B B 1)) (b := outs)]
      -- Now compute the nonce-evaluation distribution via `dds1Equiv` + `eval_nonces_uniform`.
      haveI : Nonempty (Fin (q * ℓ) → B) := ⟨outs⟩
      have h_eval_uniform :
          Dist.fTransform evalMap (Dist.uniform (DDS B B 1)) =
            Dist.uniform (Fin (q * ℓ) → B) := by
        have h_equiv :
            Dist.fTransform (dds1Equiv B B) (Dist.uniform (DDS B B 1)) =
              (Dist.uniform (B → B)) := by
          simpa using (Dist.fTransform_equiv_uniform (dds1Equiv B B))
        have h_eval :
            Dist.fTransform (fun f : B → B => fun k : Fin (q * ℓ) => f (nonces k))
                (Dist.uniform (B → B)) =
              Dist.uniform (Fin (q * ℓ) → B) :=
          eval_nonces_uniform (X := B) (Y := B) (n := q * ℓ) nonces h_inj_nonces
        calc
          Dist.fTransform evalMap (Dist.uniform (DDS B B 1))
              =
            Dist.fTransform (fun f : B → B => fun k : Fin (q * ℓ) => f (nonces k))
              (Dist.fTransform (dds1Equiv B B) (Dist.uniform (DDS B B 1))) := by
                -- functoriality: `fTransform g (fTransform f X) = fTransform (g ∘ f) X`
                simpa [evalMap, Function.comp] using
                  (Dist.fTransform_comp
                    (g := fun f : B → B => fun k : Fin (q * ℓ) => f (nonces k))
                    (f := dds1Equiv B B)
                    (X := Dist.uniform (DDS B B 1))).symm
          _ =
            Dist.fTransform (fun f : B → B => fun k : Fin (q * ℓ) => f (nonces k))
              (Dist.uniform (B → B)) := by
                simp [h_equiv]
          _ = Dist.uniform (Fin (q * ℓ) → B) := h_eval
      have := congrArg (fun D => D outs) h_eval_uniform
      simpa [Dist.uniform] using this
    -- Finish: `h_cbc` matches the URF mass because both are `1/|B|^(q·ℓ)`.
    -- Rewrite `h_urf` and `h_cbc` to the same numeric value.
    -- Since URF mass is `1 / |(Fin q → Fin ℓ → B)|` and the CBC mass is
    -- `1 / |(Fin (q*ℓ) → B)|`, both equal `1 / |B|^(q*ℓ)`.
    have h_uniform_eq :
        (Dist.uniform (Fin (q * ℓ) → B)) outs =
        (Dist.uniform (Fin q → Fin ℓ → B)) ys := by
      -- both are constant `1 / card` and the cards are both `|B|^(q*ℓ)`
      simp [Dist.uniform, Fintype.card_fin, pow_mul, Nat.mul_comm]
    simp [h_cbc, h_urf, h_uniform_eq]
  · -- Out-of-range case: no DDS can produce a transcript with mismatched inputs, so both masses are 0.
    have h_ne_urf : ∀ s : DDS (Fin ℓ → B) (Fin ℓ → B) q, s.transcript inputs ≠ t := by
      intro s hs
      have ht_inputs : ∀ i : Fin q, (t i).1 = inputs i := by
        intro i
        have := congrArg (fun tr => tr i) hs
        simpa [DDS.transcript] using (Prod.mk.inj this).1.symm
      exact h_inputs ht_inputs
    have h_ne_cbc : ∀ s : DDS B B 1, (cbcMacChainDDS (dds1Equiv B B s) ℓ q).transcript inputs ≠ t := by
      intro s hs
      have ht_inputs : ∀ i : Fin q, (t i).1 = inputs i := by
        intro i
        have := congrArg (fun tr => tr i) hs
        simpa [DDS.transcript] using (Prod.mk.inj this).1.symm
      exact h_inputs ht_inputs
    -- Unfold both transcript distributions to a single fTransform and use the empty fiber.
    have h_cbc0 :
        (cbcMacChainPDS B ℓ q).transcriptDist inputs t = 0 := by
      simp only [PDS.transcriptDist, cbcMacChainPDS, Dist.fTransform_comp]
      change (Dist.fTransform
          (fun s : DDS B B 1 => (cbcMacChainDDS (dds1Equiv B B s) ℓ q).transcript inputs)
          (Dist.uniform (DDS B B 1))) t = 0
      rw [Dist.fTransform_apply_eq_sum
        (f := fun s : DDS B B 1 => (cbcMacChainDDS (dds1Equiv B B s) ℓ q).transcript inputs)
        (X := Dist.uniform (DDS B B 1)) (b := t)]
      have : (Finset.univ : Finset (DDS B B 1)).filter
          (fun s => (cbcMacChainDDS (dds1Equiv B B s) ℓ q).transcript inputs = t) = ∅ := by
        ext s; simp [h_ne_cbc s]
      simp [this]
    have h_urf0 :
        (Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs t = 0 := by
      simp only [PDS.transcriptDist, Instances.URF]
      rw [Dist.fTransform_apply_eq_sum
        (f := fun s : DDS (Fin ℓ → B) (Fin ℓ → B) q => s.transcript inputs)
        (X := Dist.uniform (DDS (Fin ℓ → B) (Fin ℓ → B) q)) (b := t)]
      have : (Finset.univ : Finset (DDS (Fin ℓ → B) (Fin ℓ → B) q)).filter
          (fun s => s.transcript inputs = t) = ∅ := by
        ext s; simp [h_ne_urf s]
      simp [this]
    simp [h_cbc0, h_urf0]


/-- Whether the first `k` P-inputs are all distinct.

This is the key predicate for sequential conditioning: at step k,
we condition on all prior P-inputs being distinct, and then bound
the probability that the k-th P-input collides with one of the prior ones.

`goodUpTo P ℓ hℓ msgs 0` is vacuously true (no pairs to collide).
`goodUpTo P ℓ hℓ msgs n` means `cbcMacAllPInputs P ℓ hℓ msgs` is
injective on the first `n` indices. -/
def goodUpTo {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (n : ℕ) (_hn : n ≤ q * ℓ) : Prop :=
  ∀ (i j : Fin (q * ℓ)), i.val < n → j.val < n → i ≠ j →
    cbcMacAllPInputs P ℓ hℓ msgs i ≠ cbcMacAllPInputs P ℓ hℓ msgs j

instance {B : Type*} [DecidableEq B] [AddCommGroup B] [Fintype B]
    {P : B → B} {q ℓ : ℕ} {hℓ : 0 < ℓ} {msgs : Fin q → Fin ℓ → B}
    {n : ℕ} {hn : n ≤ q * ℓ} :
    Decidable (goodUpTo P ℓ hℓ msgs n hn) :=
  show Decidable (∀ (i j : Fin (q * ℓ)), i.val < n → j.val < n → i ≠ j →
    cbcMacAllPInputs P ℓ hℓ msgs i ≠ cbcMacAllPInputs P ℓ hℓ msgs j) from
  inferInstance

/-- `goodUpTo` with `n = q * ℓ` is equivalent to `isGoodFunction`. -/
theorem goodUpTo_full_iff_isGoodFunction
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    {P : B → B} {q ℓ : ℕ} {hℓ : 0 < ℓ} {msgs : Fin q → Fin ℓ → B} :
    goodUpTo P ℓ hℓ msgs (q * ℓ) le_rfl ↔ isGoodFunction P ℓ hℓ msgs := by
  constructor
  · intro h_good a b h_eq
    by_contra h_ne
    exact h_good a b a.isLt b.isLt h_ne h_eq
  · intro h_inj i j _ _ h_ne h_eq
    exact h_ne (h_inj h_eq)

/-- Whether the k-th P-input collides with any prior P-input.

`collisionAtStep P ℓ hℓ msgs k` holds when there exists some j < k
such that P-inputs at j and k are equal. This is the "bad event" at
step k in the sequential conditioning proof. -/
def collisionAtStep {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (k : Fin (q * ℓ)) : Prop :=
  ∃ (j : Fin (q * ℓ)), j.val < k.val ∧
    cbcMacAllPInputs P ℓ hℓ msgs j = cbcMacAllPInputs P ℓ hℓ msgs k

instance {B : Type*} [DecidableEq B] [AddCommGroup B] [Fintype B]
    {P : B → B} {q ℓ : ℕ} {hℓ : 0 < ℓ} {msgs : Fin q → Fin ℓ → B}
    {k : Fin (q * ℓ)} :
    Decidable (collisionAtStep P ℓ hℓ msgs k) :=
  show Decidable (∃ (j : Fin (q * ℓ)), j.val < k.val ∧
    cbcMacAllPInputs P ℓ hℓ msgs j = cbcMacAllPInputs P ℓ hℓ msgs k) from
  inferInstance

/-- `goodUpTo (k+1)` ↔ `goodUpTo k` ∧ no collision at step k.

This decomposes the injectivity condition one step at a time. -/
theorem goodUpTo_succ_iff
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    {P : B → B} {q ℓ : ℕ} {hℓ : 0 < ℓ} {msgs : Fin q → Fin ℓ → B}
    {k : ℕ} (hk : k < q * ℓ) :
    goodUpTo P ℓ hℓ msgs (k + 1) (by omega) ↔
    goodUpTo P ℓ hℓ msgs k (by omega) ∧
    ¬collisionAtStep P ℓ hℓ msgs ⟨k, hk⟩ := by
  have hk_val : (⟨k, hk⟩ : Fin (q * ℓ)).val = k := rfl
  constructor
  · intro h_good
    refine ⟨fun i j hi hj hne => h_good i j (by omega) (by omega) hne, ?_⟩
    intro ⟨j, hj_lt, hj_eq⟩
    have hne : j ≠ ⟨k, hk⟩ := by intro h; subst h; omega
    exact h_good j ⟨k, hk⟩ (by omega) (by omega) hne hj_eq
  · intro ⟨h_prev, h_no_coll⟩ i j hi hj hne
    by_cases hik : i.val < k
    · by_cases hjk : j.val < k
      · exact h_prev i j hik hjk hne
      · -- i < k, j.val = k
        have hjk_eq : j = ⟨k, hk⟩ := Fin.ext (by omega)
        intro h_eq
        apply h_no_coll
        exact ⟨i, hik, by rw [← hjk_eq]; exact h_eq⟩
    · by_cases hjk : j.val < k
      · -- i.val = k, j < k
        have hik_eq : i = ⟨k, hk⟩ := Fin.ext (by omega)
        intro h_eq
        apply h_no_coll
        exact ⟨j, hjk, by rw [← hik_eq]; exact h_eq.symm⟩
      · -- i = k, j = k — contradicts i ≠ j
        exact absurd (Fin.ext (by omega)) hne

/-- Helper: if `a` is not at block 0, then `cbcMacAllPInputs` at `a`
is `P` applied to the previous flat index plus the current message block.

This is the flat-index analogue of the single-message identity:
`v_{j} = P(v_{j-1}) + m_j` for `j > 0`. -/
theorem cbcMacAllPInputs_succ_of_mod_ne_zero
    {B : Type*} [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (a : Fin (q * ℓ))
    (ha0 : a.val % ℓ ≠ 0) :
    cbcMacAllPInputs P ℓ hℓ msgs a =
      P (cbcMacAllPInputs P ℓ hℓ msgs ⟨a.val - 1, by omega⟩) +
        msgs ⟨a.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr a.isLt⟩
          ⟨a.val % ℓ, Nat.mod_lt a.val hℓ⟩ := by
  classical
  have ha_pos : 0 < a.val := by
    by_contra h0
    have ha0' : a.val = 0 := Nat.eq_zero_of_not_pos h0
    exact ha0 (by simp [ha0'])
  -- Derived query/block indices.
  let qa : Fin q := ⟨a.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr a.isLt⟩
  let ja : Fin ℓ := ⟨a.val % ℓ, Nat.mod_lt a.val hℓ⟩
  have hja0 : ja.val ≠ 0 := by
    simp [ja, ha0]
  -- Predecessor indices.
  let apred : Fin (q * ℓ) := ⟨a.val - 1, by omega⟩
  let jpred : Fin ℓ := finPred ja hja0
  -- Division/modulo facts for the predecessor.
  have hrpos : 1 ≤ a.val % ℓ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha0)
  have hdecomp : (a.val / ℓ) * ℓ + a.val % ℓ = a.val := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod a.val ℓ)
  have hpred : a.val - 1 = (a.val / ℓ) * ℓ + (a.val % ℓ - 1) := by
    -- (q*ℓ + r) - 1 = q*ℓ + (r-1) when 1 ≤ r
    calc
      a.val - 1 = ((a.val / ℓ) * ℓ + a.val % ℓ) - 1 := by simp [hdecomp]
      _ = (a.val / ℓ) * ℓ + (a.val % ℓ - 1) := by
            simp [Nat.add_sub_assoc hrpos]
  have hrlt' : a.val % ℓ - 1 < ℓ := by
    have hrlt : a.val % ℓ < ℓ := Nat.mod_lt a.val hℓ
    have : a.val % ℓ - 1 < a.val % ℓ := Nat.sub_lt (Nat.pos_of_ne_zero ha0) Nat.one_pos
    exact lt_trans this hrlt
  have h_div : apred.val / ℓ = qa.val := by
    calc
      apred.val / ℓ = (a.val - 1) / ℓ := rfl
      _ = ((a.val / ℓ) * ℓ + (a.val % ℓ - 1)) / ℓ := by simp [hpred]
      _ = ((ℓ * (a.val / ℓ)) + (a.val % ℓ - 1)) / ℓ := by simp [Nat.mul_comm]
      _ = (a.val / ℓ) + (a.val % ℓ - 1) / ℓ := by
            exact (Nat.mul_add_div hℓ (a.val / ℓ) (a.val % ℓ - 1))
      _ = a.val / ℓ := by simp [Nat.div_eq_of_lt hrlt']
  have h_mod : apred.val % ℓ = ja.val - 1 := by
    calc
      apred.val % ℓ = (a.val - 1) % ℓ := rfl
      _ = ((a.val / ℓ) * ℓ + (a.val % ℓ - 1)) % ℓ := by simp [hpred]
      _ = (a.val % ℓ - 1) := by
            simpa [Nat.mul_comm] using (Nat.mul_add_mod_of_lt (a := a.val / ℓ) (b := ℓ)
              (c := a.val % ℓ - 1) hrlt')
      _ = ja.val - 1 := by rfl
  -- Unfold `cbcMacAllPInputs` at `a` and use the single-message `cbcMacPInput` identity.
  have hpinput :
      cbcMacPInput P ℓ (msgs qa) ja =
        P (cbcMacPInput P ℓ (msgs qa) jpred) + msgs qa ja := by
    have h0 : ja.val ≠ 0 := hja0
    have hprev :
        cbcMacPInput P ℓ (msgs qa) ja =
          cbcMacChainValues P ℓ (msgs qa) jpred + msgs qa ja := by
      simp [cbcMacPInput, h0, jpred]
    -- Replace the chain value with `P` applied to the predecessor input.
    calc
      cbcMacPInput P ℓ (msgs qa) ja
          = cbcMacChainValues P ℓ (msgs qa) jpred + msgs qa ja := hprev
      _ = P (cbcMacPInput P ℓ (msgs qa) jpred) + msgs qa ja := by
            simp [cbcMacChainValues_eq_apply]
  -- Rewrite the predecessor block `jpred` as the flat predecessor `apred`.
  have hqa : (⟨apred.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr apred.isLt⟩ : Fin q) = qa := by
    ext; simp [qa, apred, h_div]
  have hjpred' : (⟨apred.val % ℓ, Nat.mod_lt apred.val hℓ⟩ : Fin ℓ) = jpred := by
    ext
    simp [jpred, finPred, apred, ja, h_mod]
  -- Finish by unfolding both sides at `a`.
  simp [cbcMacAllPInputs, qa, ja, apred, hqa, hjpred', hpinput]

/-- Prefix stability for CBC-MAC P-inputs under a single-cell update:
if `pivot < k` and `goodUpTo P … k` holds, then updating `P` at the pivot
P-input does not change any earlier P-input (in the flat ordering). -/
theorem cbcMacAllPInputs_update_eq_of_le
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B)
    (k : ℕ) (hk : k < q * ℓ)
    (pivot : Fin (q * ℓ)) (hpivot : pivot.val < k)
    (hgood : goodUpTo P ℓ hℓ msgs k (by omega))
    (x : B) (a : Fin (q * ℓ)) (ha : a.val ≤ pivot.val) :
    cbcMacAllPInputs (Function.update P (cbcMacAllPInputs P ℓ hℓ msgs pivot) x) ℓ hℓ msgs a =
      cbcMacAllPInputs P ℓ hℓ msgs a := by
  classical
  set w : B := cbcMacAllPInputs P ℓ hℓ msgs pivot with hw
  by_cases ha0 : a.val % ℓ = 0
  · -- Block 0: P-input is independent of P.
    have h1 :=
      cbcMacAllPInputs_block_zero (P := Function.update P w x) (ℓ := ℓ) hℓ msgs a ha0
    have h2 := cbcMacAllPInputs_block_zero (P := P) (ℓ := ℓ) hℓ msgs a ha0
    simpa using (h1.trans h2.symm)
  · -- Block > 0: use `cbcMacChainValues_update_eq` within the relevant message.
    let qa : Fin q := ⟨a.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr a.isLt⟩
    let ja : Fin ℓ := ⟨a.val % ℓ, Nat.mod_lt a.val hℓ⟩
    have hja0 : ja.val ≠ 0 := by simpa [ja] using ha0
    let jpred : Fin ℓ := finPred ja hja0
    -- Show: `w` is not any P-input at blocks ≤ jpred of message `msgs qa`.
    have h_not_used :
        ∀ i : Fin ℓ, i.val ≤ jpred.val → cbcMacPInput P ℓ (msgs qa) i ≠ w := by
      intro i hi_le
      -- Flat index corresponding to (qa, i).
      let bval : ℕ := (a.val / ℓ) * ℓ + i.val
      have hi_lt : i.val < a.val % ℓ := by
        -- i ≤ ja-1 < ja = a%ℓ
        have hi_le' : i.val ≤ ja.val - 1 := by
          simpa [jpred, finPred] using hi_le
        have : i.val < ja.val := lt_of_le_of_lt hi_le' (Nat.sub_lt (Nat.pos_of_ne_zero hja0) Nat.one_pos)
        simpa [ja] using this
      have hb_lt_a : bval < a.val := by
        have ha_decomp : (a.val / ℓ) * ℓ + a.val % ℓ = a.val := by
          simpa [Nat.mul_comm] using (Nat.div_add_mod a.val ℓ)
        have : (a.val / ℓ) * ℓ + i.val < (a.val / ℓ) * ℓ + a.val % ℓ :=
          Nat.add_lt_add_left hi_lt ((a.val / ℓ) * ℓ)
        simpa [bval, ha_decomp] using this
      let b : Fin (q * ℓ) := ⟨bval, lt_trans hb_lt_a a.isLt⟩
      have hb_lt_k : b.val < k := lt_of_lt_of_le (lt_of_lt_of_le hb_lt_a ha) (Nat.le_of_lt hpivot)
      have hne : b ≠ pivot := by
        intro h
        have : b.val = pivot.val := congrArg Fin.val h
        exact (Nat.ne_of_lt (lt_of_lt_of_le hb_lt_a ha)) this
      have hdiff := hgood b pivot hb_lt_k hpivot hne
      -- Rewrite `cbcMacAllPInputs` at b as the single-message P-input.
      have hb_div : b.val / ℓ = a.val / ℓ := by
        calc
          b.val / ℓ = bval / ℓ := rfl
          _ = (ℓ * (a.val / ℓ) + i.val) / ℓ := by simp [bval, Nat.mul_comm]
          _ = (a.val / ℓ) + i.val / ℓ := by
                simpa using (Nat.mul_add_div hℓ (a.val / ℓ) i.val)
          _ = a.val / ℓ := by simp [Nat.div_eq_of_lt i.isLt]
      have hb_mod : b.val % ℓ = i.val := by
        simpa [b, bval] using
          (Nat.mul_add_mod_of_lt (a := a.val / ℓ) (b := ℓ) (c := i.val) i.isLt)
      have hq_b : (⟨b.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr b.isLt⟩ : Fin q) = qa := by
        ext; simp [qa, hb_div]
      have hj_b : (⟨b.val % ℓ, Nat.mod_lt b.val hℓ⟩ : Fin ℓ) = i := by
        ext; simp [hb_mod]
      -- Conclude: pinput i ≠ w.
      simpa (config := {contextual := false}) [w, qa, hq_b, hj_b, cbcMacAllPInputs] using hdiff
    have h_chain :
        cbcMacChainValues (Function.update P w x) ℓ (msgs qa) jpred =
          cbcMacChainValues P ℓ (msgs qa) jpred :=
      cbcMacChainValues_update_eq P ℓ (msgs qa) w x jpred h_not_used
    -- Finish by unfolding `cbcMacAllPInputs` at `a` to `cbcMacPInput`.
    simp (config := {contextual := false})
      [cbcMacAllPInputs, qa, ja, cbcMacPInput, hja0, jpred, h_chain]

/-- **Per-step collision bound**: among uniform random functions P that
are good up to step k, the fraction that collide at step k is ≤ k/|B|.

This is the core sequential conditioning lemma. The proof uses an
injection argument: for each prior index j < k that P-input k collides
with, and each substitute value x ∈ B, the map `Function.update P v x`
(where v is the colliding P-input) gives a distinct "good" function.

The `h_no_forced_collision` hypothesis ensures that the collision at
step k is not deterministic — there exists some P where the k-th
P-input differs from every prior one. -/
theorem cbcMac_step_collision_bound
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    (msgs : Fin q → Fin ℓ → B)
    (h_no_forced_collision : ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
      ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ msgs k₁ ≠
        cbcMacAllPInputs P ℓ hℓ msgs k₂)
    (k : ℕ) (hk : k < q * ℓ) :
    -- Mass of {P | goodUpTo k ∧ collision at step k}
    ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
      (fun s => goodUpTo (dds1Equiv B B s) ℓ hℓ msgs k (by omega) ∧
        collisionAtStep (dds1Equiv B B s) ℓ hℓ msgs ⟨k, hk⟩),
      (Dist.uniform (DDS B B 1)) s
    ≤ (k : NNReal) / (Fintype.card B : NNReal) := by
  -- Paper proof (Maurer 2002 §4.2, sequential conditioning):
  -- Under uniform P, conditioned on goodUpTo k, the k-th P-input v_k
  -- is determined by P's outputs at k distinct prior P-inputs.
  -- Collision occurs iff v_k ∈ {v_0,...,v_{k-1}} (at most k values from B).
  --
  -- Step 1: Convert ∑_filter uniform to |filter| / |DDS B B 1|
  let collSet := (Finset.univ : Finset (DDS B B 1)).filter
    (fun s => goodUpTo (dds1Equiv B B s) ℓ hℓ msgs k (by omega) ∧
      collisionAtStep (dds1Equiv B B s) ℓ hℓ msgs ⟨k, hk⟩)
  -- Decompose collisionAtStep: for each P in collSet, pick the witness j < k
  -- CollSet = ⋃_{j<k} S_j where S_j = {P | goodUpTo k ∧ P-input k = P-input j}
  -- |CollSet| ≤ ∑_{j<k} |S_j| and |S_j| ≤ |B|^(|B|-1) = |DDS|/|B|
  -- So |CollSet| ≤ k * |DDS|/|B|, giving |CollSet|/|DDS| ≤ k/|B|.
  --
  -- Step 1: Convert uniform sum to cardinality fraction
  have h_sum_eq : ∑ s ∈ collSet, (Dist.uniform (DDS B B 1)) s =
      (collSet.card : NNReal) / (Fintype.card (DDS B B 1) : NNReal) := by
    simp only [Dist.uniform, Finsupp.equivFunOnFinite, Finsupp.coe_mk]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [h_sum_eq]
  -- Step 2: Bound |collSet| * |B| ≤ k * |DDS B B 1|
  -- This gives |collSet| / |DDS| ≤ k / |B|
  have h_card_bound : (collSet.card : NNReal) * (Fintype.card B : NNReal) ≤
      (k : NNReal) * (Fintype.card (DDS B B 1) : NNReal) := by
    -- Union bound: collSet ⊆ ⋃_{j<k} S_j, so |collSet| ≤ ∑_{j<k} |S_j|
    -- where S_j = {P | goodUpTo k ∧ v_k = v_j}
    -- For each j: |S_j| * |B| ≤ |DDS|  (i.e. |S_j| ≤ |B|^(|B|-1))
    -- So |collSet| * |B| ≤ ∑_{j<k} |S_j| * |B| ≤ k * |DDS|
    suffices h : (collSet.card : ℕ) * Fintype.card B ≤ k * Fintype.card (DDS B B 1) by
      exact_mod_cast h
    -- Define per-witness sets S_j
    let S : Fin k → Finset (DDS B B 1) := fun j =>
      (Finset.univ : Finset (DDS B B 1)).filter
        (fun s => goodUpTo (dds1Equiv B B s) ℓ hℓ msgs k (by omega) ∧
          cbcMacAllPInputs (dds1Equiv B B s) ℓ hℓ msgs ⟨j.val, by omega⟩ =
          cbcMacAllPInputs (dds1Equiv B B s) ℓ hℓ msgs ⟨k, hk⟩)
    -- Step A: collSet ⊆ ⋃_{j<k} S_j
    have h_subset : collSet ⊆ Finset.biUnion Finset.univ S := by
      intro s hs
      simp only [collSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨h_good, ⟨j, hj_lt, hj_eq⟩⟩ := hs
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨⟨j.val, hj_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_good, hj_eq⟩⟩
    -- Step B: |collSet| ≤ ∑_{j<k} |S_j|
    have h_card_le : collSet.card ≤ ∑ j : Fin k, (S j).card :=
      le_trans (Finset.card_le_card h_subset) Finset.card_biUnion_le
    -- Step C: For each j, |S_j| * |B| ≤ |DDS|
    -- Strategy: injection φ : (S j) ×ˢ univ → univ.
    -- When k%ℓ > 0: inject at v_{k-1} (chain predecessor of v_k)
    -- When k%ℓ = 0 ∧ j%ℓ > 0: inject at v_{j-1} (chain predecessor of v_j)
    -- When k%ℓ = 0 ∧ j%ℓ = 0: both block-0 → S_j empty (h_no_forced_collision)
    have h_per_j : ∀ j : Fin k, (S j).card * Fintype.card B ≤
        Fintype.card (DDS B B 1) := by
      intro j
      -- Determine pivot: the flat index whose P-output we modify
      -- Cases: at least one of j, k is not at block 0 (otherwise forced collision)
      by_cases hk_mod : k % ℓ = 0 ∧ j.val % ℓ = 0
      · -- Both at block 0: P-inputs are constants → forced collision → S_j empty
        suffices h_empty : S j = ∅ by
          rw [h_empty, Finset.card_empty, Nat.zero_mul]; exact Nat.zero_le _
        rw [Finset.eq_empty_iff_forall_notMem]
        intro s hs
        have hs' := (Finset.mem_filter.mp hs).2
        have hcoll := hs'.2
        have hjlt : j.val < q * ℓ := Nat.lt_trans j.isLt hk
        -- Both P-inputs are independent of P (block 0)
        have h1 := cbcMacAllPInputs_block_zero (dds1Equiv B B s) ℓ hℓ msgs
          ⟨j.val, hjlt⟩ hk_mod.2
        have h2 := cbcMacAllPInputs_block_zero (dds1Equiv B B s) ℓ hℓ msgs
          ⟨k, hk⟩ hk_mod.1
        -- Since they're constants, the collision holds for ALL P
        -- h_no_forced_collision says ∃ P with different values → contradiction
        have h_forced := h_no_forced_collision
          ⟨j.val, hjlt⟩ ⟨k, hk⟩ (by
            intro h
            have : j.val = k := Fin.val_eq_of_eq h
            exact (Nat.ne_of_lt j.isLt) this)
        obtain ⟨P₀, hP₀⟩ := h_forced
        have h1' := cbcMacAllPInputs_block_zero P₀ ℓ hℓ msgs
          ⟨j.val, hjlt⟩ hk_mod.2
        have h2' := cbcMacAllPInputs_block_zero P₀ ℓ hℓ msgs
          ⟨k, hk⟩ hk_mod.1
        -- hcoll: const_j = const_k (from s), hP₀: const_j ≠ const_k (from P₀)
        rw [h1, h2] at hcoll; rw [h1', h2'] at hP₀
        exact hP₀ hcoll
      · -- At least one of j, k is at block > 0
        -- Choose pivot index p: predecessor of whichever is not at block 0
        push_neg at hk_mod
        -- Determine the pivot index
        -- If k%ℓ ≠ 0: pivot = k-1 (predecessor of k in same query)
        -- If k%ℓ = 0: must have j%ℓ ≠ 0, pivot = j-1 (predecessor of j)
        -- In either case, pivot < q*ℓ and the P-input at the non-block-0
        -- index depends on P through the chain predecessor.
        --
        -- Define pivot and the injection
        -- We use k-1 as pivot when k%ℓ ≠ 0, and j-1 when k%ℓ = 0
        let pivot : Fin (q * ℓ) :=
          if hk0 : k % ℓ = 0 then ⟨j.val - 1, by omega⟩
          else ⟨k - 1, by omega⟩
        let v_pivot := fun (s : DDS B B 1) =>
          cbcMacAllPInputs (dds1Equiv B B s) ℓ hℓ msgs pivot
        let φ : DDS B B 1 × B → DDS B B 1 := fun ⟨s, x⟩ =>
          (dds1Equiv B B).symm (Function.update (dds1Equiv B B s) (v_pivot s) x)
        have h_maps : ∀ p ∈ (S j) ×ˢ (Finset.univ : Finset B),
            φ p ∈ (Finset.univ : Finset (DDS B B 1)) := by
          intro p _; exact Finset.mem_univ _
        have h_inj : Set.InjOn φ ↑((S j) ×ˢ (Finset.univ : Finset B)) := by
          intro ⟨s₁, x₁⟩ hp₁ ⟨s₂, x₂⟩ hp₂ heq
          rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
          have hs₁ := (Finset.mem_filter.mp hp₁.1).2
          have hs₂ := (Finset.mem_filter.mp hp₂.1).2
          obtain ⟨hgood₁, hcoll₁⟩ := hs₁
          obtain ⟨hgood₂, hcoll₂⟩ := hs₂
          -- φ equality: Function.update P₁ (v_pivot₁) x₁ = Function.update P₂ (v_pivot₂) x₂
          have heq_fn : Function.update (dds1Equiv B B s₁) (v_pivot s₁) x₁ =
              Function.update (dds1Equiv B B s₂) (v_pivot s₂) x₂ := by
            simpa [φ] using congrArg (dds1Equiv B B) heq
          -- Chain bootstrap: v_pivot(P₁) = v_pivot(P₂)
          -- (pivot's chain uses P at points distinct from v_pivot by goodUpTo)
          -- Then: x₁ = x₂ and P₁ = P₂ on B\{v_pivot}
          -- Then: collision condition forces P₁(v_pivot) = P₂(v_pivot)
          -- Proof: v_k(or v_j) = f(P(v_pivot)) + const,
          --   collision = constraint on P(v_pivot), uniquely determining it.
          classical
          -- Name the underlying functions and the pivot inputs.
          set P₁ : B → B := dds1Equiv B B s₁
          set P₂ : B → B := dds1Equiv B B s₂
          set w₁ : B := v_pivot s₁
          set w₂ : B := v_pivot s₂
          -- The pivot is always strictly before step k.
          have hpivot_lt : pivot.val < k := by
            by_cases hk0 : k % ℓ = 0
            · -- pivot = j-1, and j < k (and j ≠ 0 since j%ℓ ≠ 0)
              have hj0 : j.val ≠ 0 := by
                intro hj0
                have : j.val % ℓ = 0 := by simp [hj0]
                exact (hk_mod hk0) this
              have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
              -- simplify pivot and finish by arithmetic
              simp [pivot, hk0]
              omega
            · -- pivot = k-1
              have hkpos : 0 < k := by
                by_contra hkpos
                have : k = 0 := Nat.eq_zero_of_not_pos hkpos
                subst this
                exact hk0 (by simp)
              have hp : pivot.val = k - 1 := by
                simp [pivot, hk0]
              rw [hp]
              exact Nat.sub_lt hkpos Nat.one_pos
          -- Recover the pivot input from the updated function.
          have hwrec₁ :
              cbcMacAllPInputs (Function.update P₁ w₁ x₁) ℓ hℓ msgs pivot = w₁ := by
            have h :=
              cbcMacAllPInputs_update_eq_of_le (P := P₁) (ℓ := ℓ) (hℓ := hℓ) (msgs := msgs)
                (k := k) (hk := hk) (pivot := pivot) (hpivot := hpivot_lt) (hgood := hgood₁)
                (x := x₁) (a := pivot) (ha := le_rfl)
            simpa [P₁, w₁, v_pivot] using h
          have hwrec₂ :
              cbcMacAllPInputs (Function.update P₂ w₂ x₂) ℓ hℓ msgs pivot = w₂ := by
            have h :=
              cbcMacAllPInputs_update_eq_of_le (P := P₂) (ℓ := ℓ) (hℓ := hℓ) (msgs := msgs)
                (k := k) (hk := hk) (pivot := pivot) (hpivot := hpivot_lt) (hgood := hgood₂)
                (x := x₂) (a := pivot) (ha := le_rfl)
            simpa [P₂, w₂, v_pivot] using h
          have hw' :
              cbcMacAllPInputs (Function.update P₁ w₁ x₁) ℓ hℓ msgs pivot =
                cbcMacAllPInputs (Function.update P₂ w₂ x₂) ℓ hℓ msgs pivot := by
            have := congrArg (fun f => cbcMacAllPInputs f ℓ hℓ msgs pivot) heq_fn
            simpa [P₁, P₂, w₁, w₂, v_pivot] using this
          have hw : w₁ = w₂ := by simpa [hwrec₁, hwrec₂] using hw'
          -- Recover x from the updated function at the pivot input.
          have hx : x₁ = x₂ := by
            have h := congrFun heq_fn w₁
            -- rewrite the RHS update point to w₁
            have hw2 : w₁ = w₂ := hw
            -- simplify updates at the pivot point
            simpa [P₁, P₂, w₁, w₂, hw2, Function.update] using h
          -- Agreement away from the pivot input.
          have h_other : ∀ z : B, z ≠ w₁ → P₁ z = P₂ z := by
            intro z hz
            have hz2 : z ≠ w₂ := by simpa [hw] using hz
            have h := congrFun heq_fn z
            simpa [P₁, P₂, w₁, w₂, Function.update, hz, hz2] using h
          -- Recover the original pivot cell value from the collision constraint.
          have h_pivot_val : P₁ w₁ = P₂ w₁ := by
            by_cases hk0 : k % ℓ = 0
            · -- Then j%ℓ ≠ 0, and the collision is between j and the block-0 index k.
              have hj_mod_ne : j.val % ℓ ≠ 0 := hk_mod hk0
              let jflat : Fin (q * ℓ) := ⟨j.val, by omega⟩
              let kflat : Fin (q * ℓ) := ⟨k, hk⟩
              have hcoll₁' : cbcMacAllPInputs P₁ ℓ hℓ msgs jflat =
                  cbcMacAllPInputs P₁ ℓ hℓ msgs kflat := by
                simpa [P₁, jflat, kflat] using hcoll₁
              have hcoll₂' : cbcMacAllPInputs P₂ ℓ hℓ msgs jflat =
                  cbcMacAllPInputs P₂ ℓ hℓ msgs kflat := by
                simpa [P₂, jflat, kflat] using hcoll₂
              -- k is block-0, so its P-input is a constant message block.
              have hk0₁ :
                  cbcMacAllPInputs P₁ ℓ hℓ msgs kflat =
                    msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩ ⟨0, hℓ⟩ := by
                simpa [kflat, hk0] using cbcMacAllPInputs_block_zero (P := P₁) (ℓ := ℓ) hℓ msgs kflat hk0
              have hk0₂ :
                  cbcMacAllPInputs P₂ ℓ hℓ msgs kflat =
                    msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩ ⟨0, hℓ⟩ := by
                simpa [kflat, hk0] using cbcMacAllPInputs_block_zero (P := P₂) (ℓ := ℓ) hℓ msgs kflat hk0
              -- j is nonzero block, so we can express it as `P(w) + m_j`.
              have hj_succ₁ := cbcMacAllPInputs_succ_of_mod_ne_zero (P := P₁) (ℓ := ℓ) hℓ msgs jflat hj_mod_ne
              have hj_succ₂ := cbcMacAllPInputs_succ_of_mod_ne_zero (P := P₂) (ℓ := ℓ) hℓ msgs jflat hj_mod_ne
              -- Identify the predecessor index with `pivot` (since hk0).
              have hpivot_def : (⟨j.val - 1, by omega⟩ : Fin (q * ℓ)) = pivot := by
                simp [pivot, hk0]
              -- Solve for the pivot cell value by subtracting the message block.
              have hP₁w :
                  P₁ w₁ =
                    cbcMacAllPInputs P₁ ℓ hℓ msgs jflat -
                      msgs ⟨jflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr jflat.isLt⟩
                        ⟨jflat.val % ℓ, Nat.mod_lt jflat.val hℓ⟩ := by
                have hpivot_def' : (⟨jflat.val - 1, by omega⟩ : Fin (q * ℓ)) = pivot := by
                  simpa [jflat] using hpivot_def
                have hj_succ₁' :
                    cbcMacAllPInputs P₁ ℓ hℓ msgs jflat =
                      P₁ w₁ +
                        msgs ⟨jflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr jflat.isLt⟩
                          ⟨jflat.val % ℓ, Nat.mod_lt jflat.val hℓ⟩ := by
                  simpa [w₁, v_pivot, P₁, hpivot_def'] using hj_succ₁
                have := congrArg (fun z => z -
                  msgs ⟨jflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr jflat.isLt⟩
                    ⟨jflat.val % ℓ, Nat.mod_lt jflat.val hℓ⟩) hj_succ₁'
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
              have hP₂w :
                  P₂ w₂ =
                    cbcMacAllPInputs P₂ ℓ hℓ msgs jflat -
                      msgs ⟨jflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr jflat.isLt⟩
                        ⟨jflat.val % ℓ, Nat.mod_lt jflat.val hℓ⟩ := by
                have hpivot_def' : (⟨jflat.val - 1, by omega⟩ : Fin (q * ℓ)) = pivot := by
                  simpa [jflat] using hpivot_def
                have hj_succ₂' :
                    cbcMacAllPInputs P₂ ℓ hℓ msgs jflat =
                      P₂ w₂ +
                        msgs ⟨jflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr jflat.isLt⟩
                          ⟨jflat.val % ℓ, Nat.mod_lt jflat.val hℓ⟩ := by
                  simpa [w₂, v_pivot, P₂, hpivot_def'] using hj_succ₂
                have := congrArg (fun z => z -
                  msgs ⟨jflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr jflat.isLt⟩
                    ⟨jflat.val % ℓ, Nat.mod_lt jflat.val hℓ⟩) hj_succ₂'
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
              -- Use the collision constraint to replace `jflat` by the block-0 value.
              have : P₁ w₁ = P₂ w₂ := by
                -- rewrite both sides using hcoll and block0.
                rw [hP₁w, hP₂w, hcoll₁', hcoll₂', hk0₁, hk0₂]
              simpa [hw] using this
            · -- k%ℓ ≠ 0: the collision is between j and k, and k expands to `P(w)+m_k`.
              have hk_mod_ne : k % ℓ ≠ 0 := hk0
              let jflat : Fin (q * ℓ) := ⟨j.val, by omega⟩
              let kflat : Fin (q * ℓ) := ⟨k, hk⟩
              have hcoll₁' : cbcMacAllPInputs P₁ ℓ hℓ msgs jflat =
                  cbcMacAllPInputs P₁ ℓ hℓ msgs kflat := by
                simpa [P₁, jflat, kflat] using hcoll₁
              have hcoll₂' : cbcMacAllPInputs P₂ ℓ hℓ msgs jflat =
                  cbcMacAllPInputs P₂ ℓ hℓ msgs kflat := by
                simpa [P₂, jflat, kflat] using hcoll₂
              -- Express k as `P(w)+m_k`, where predecessor is `pivot = k-1`.
              have hk_succ₁ := cbcMacAllPInputs_succ_of_mod_ne_zero (P := P₁) (ℓ := ℓ) hℓ msgs kflat hk_mod_ne
              have hk_succ₂ := cbcMacAllPInputs_succ_of_mod_ne_zero (P := P₂) (ℓ := ℓ) hℓ msgs kflat hk_mod_ne
              have hpivot_def : (⟨k - 1, by omega⟩ : Fin (q * ℓ)) = pivot := by
                simp [pivot, hk0]
              have hP₁w :
                  P₁ w₁ =
                    cbcMacAllPInputs P₁ ℓ hℓ msgs jflat -
                      msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                        ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩ := by
                have hpivot_def' : (⟨kflat.val - 1, by omega⟩ : Fin (q * ℓ)) = pivot := by
                  simpa [kflat] using hpivot_def
                have hk_succ₁' :
                    cbcMacAllPInputs P₁ ℓ hℓ msgs kflat =
                      P₁ w₁ +
                        msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                          ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩ := by
                  simpa [w₁, v_pivot, P₁, hpivot_def'] using hk_succ₁
                have hj_eq₁ :
                    cbcMacAllPInputs P₁ ℓ hℓ msgs jflat =
                      P₁ w₁ +
                        msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                          ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩ := by
                  simpa [hcoll₁'] using hk_succ₁'
                have := congrArg (fun z => z -
                  msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                    ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩) hj_eq₁
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
              have hP₂w :
                  P₂ w₂ =
                    cbcMacAllPInputs P₂ ℓ hℓ msgs jflat -
                      msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                        ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩ := by
                have hpivot_def' : (⟨kflat.val - 1, by omega⟩ : Fin (q * ℓ)) = pivot := by
                  simpa [kflat] using hpivot_def
                have hk_succ₂' :
                    cbcMacAllPInputs P₂ ℓ hℓ msgs kflat =
                      P₂ w₂ +
                        msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                          ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩ := by
                  simpa [w₂, v_pivot, P₂, hpivot_def'] using hk_succ₂
                have hj_eq₂ :
                    cbcMacAllPInputs P₂ ℓ hℓ msgs jflat =
                      P₂ w₂ +
                        msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                          ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩ := by
                  simpa [hcoll₂'] using hk_succ₂'
                have := congrArg (fun z => z -
                  msgs ⟨kflat.val / ℓ, (Nat.div_lt_iff_lt_mul hℓ).mpr kflat.isLt⟩
                    ⟨kflat.val % ℓ, Nat.mod_lt kflat.val hℓ⟩) hj_eq₂
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
              -- Show the (base) value at `jflat` is the same for P₁ and P₂ by prefix stability and `heq_fn`.
              have hj_le : jflat.val ≤ pivot.val := by
                simp [jflat, pivot, hk0]
                omega
              have hj_stable₁ :
                  cbcMacAllPInputs (Function.update P₁ w₁ x₁) ℓ hℓ msgs jflat =
                    cbcMacAllPInputs P₁ ℓ hℓ msgs jflat := by
                have h :=
                  cbcMacAllPInputs_update_eq_of_le (P := P₁) (ℓ := ℓ) (hℓ := hℓ) (msgs := msgs)
                    (k := k) (hk := hk) (pivot := pivot) (hpivot := hpivot_lt) (hgood := hgood₁)
                    (x := x₁) (a := jflat) (ha := hj_le)
                simpa [P₁, w₁, v_pivot] using h
              have hj_stable₂ :
                  cbcMacAllPInputs (Function.update P₂ w₂ x₂) ℓ hℓ msgs jflat =
                    cbcMacAllPInputs P₂ ℓ hℓ msgs jflat := by
                have h :=
                  cbcMacAllPInputs_update_eq_of_le (P := P₂) (ℓ := ℓ) (hℓ := hℓ) (msgs := msgs)
                    (k := k) (hk := hk) (pivot := pivot) (hpivot := hpivot_lt) (hgood := hgood₂)
                    (x := x₂) (a := jflat) (ha := hj_le)
                simpa [P₂, w₂, v_pivot] using h
              have hj_eq_updates :
                  cbcMacAllPInputs (Function.update P₁ w₁ x₁) ℓ hℓ msgs jflat =
                    cbcMacAllPInputs (Function.update P₂ w₂ x₂) ℓ hℓ msgs jflat := by
                have := congrArg (fun f => cbcMacAllPInputs f ℓ hℓ msgs jflat) heq_fn
                simpa [P₁, P₂, w₁, w₂, v_pivot] using this
              have hj_eq : cbcMacAllPInputs P₁ ℓ hℓ msgs jflat = cbcMacAllPInputs P₂ ℓ hℓ msgs jflat := by
                simpa [hj_stable₁, hj_stable₂] using hj_eq_updates
              -- Conclude.
              have : P₁ w₁ = P₂ w₂ := by
                rw [hP₁w, hP₂w, hj_eq]
              simpa [hw] using this
          -- Now show P₁ = P₂ and hence s₁ = s₂, and package the product equality.
          have hP : P₁ = P₂ := by
            funext z
            by_cases hz : z = w₁
            · subst hz
              exact h_pivot_val
            · exact h_other z hz
          have hs : s₁ = s₂ := by
            apply (dds1Equiv B B).injective
            simpa [P₁, P₂] using hP
          exact Prod.ext hs hx
        have h_card_le := Finset.card_le_card_of_injOn φ h_maps h_inj
        rw [Finset.card_product, Finset.card_univ] at h_card_le
        exact h_card_le
    -- Combine: |collSet| * |B| ≤ ∑_{j<k} |S_j| * |B| ≤ k * |DDS|
    calc collSet.card * Fintype.card B
        ≤ (∑ j : Fin k, (S j).card) * Fintype.card B := by
          exact Nat.mul_le_mul_right _ h_card_le
      _ = ∑ j : Fin k, (S j).card * Fintype.card B := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _ : Fin k, Fintype.card (DDS B B 1) :=
          Finset.sum_le_sum (fun j _ => h_per_j j)
      _ = k * Fintype.card (DDS B B 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- Step 3: Derive the division inequality from the multiplication one
  -- Step 3: Derive the division inequality from the multiplication one
  have hDDS : 0 < Fintype.card (DDS B B 1) := Fintype.card_pos
  have hB : 0 < Fintype.card B := Fintype.card_pos
  rw [div_le_div_iff₀ (by exact_mod_cast hDDS) (by exact_mod_cast hB)]
  exact h_card_bound

/-- **Telescoping sum**: the total failure mass (¬isGoodFunction) is
bounded by the sum of per-step collision masses.

  ∑_{P : ¬good} uniform(P) ≤ ∑_{k=0}^{n-1} ∑_{P : goodUpTo k ∧ coll at k} uniform(P)

This follows because every "bad" function P has a first collision at
some step k — at that step, P is `goodUpTo k` but has `collisionAtStep k`. -/
theorem bad_functions_le_telescoping_sum
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    (msgs : Fin q → Fin ℓ → B) :
    ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
      (fun s => ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ msgs),
      (Dist.uniform (DDS B B 1)) s
    ≤ ∑ k ∈ Finset.range (q * ℓ),
      ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
        (fun s => if hk : k < q * ℓ then
          goodUpTo (dds1Equiv B B s) ℓ hℓ msgs k (by omega) ∧
          collisionAtStep (dds1Equiv B B s) ℓ hℓ msgs ⟨k, hk⟩
        else False),
        (Dist.uniform (DDS B B 1)) s := by
  -- Paper proof: every bad P has a first collision step k. At that step,
  -- P is goodUpTo k and has collisionAtStep k. So bad ⊆ ∪_k (per-step sets).
  -- Since uniform masses are non-negative, ∑_bad ≤ ∑_k ∑_{per-step k}.
  --
  -- Step 1: For each bad s, find its first collision step
  have h_first_collision : ∀ s : DDS B B 1,
      ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ msgs →
      ∃ k, ∃ hk : k < q * ℓ,
        goodUpTo (dds1Equiv B B s) ℓ hℓ msgs k (by omega) ∧
        collisionAtStep (dds1Equiv B B s) ℓ hℓ msgs ⟨k, hk⟩ := by
    intro s h_bad
    let P := dds1Equiv B B s
    -- ¬isGoodFunction = ¬injective, so ∃ collision step
    have h_exists_coll : ∃ k : Fin (q * ℓ), collisionAtStep P ℓ hℓ msgs k := by
      rw [isGoodFunction, Function.Injective] at h_bad; push_neg at h_bad
      obtain ⟨i, j, h_eq, h_ne⟩ := h_bad
      by_cases hij : i.val < j.val
      · exact ⟨j, i, hij, h_eq⟩
      · push_neg at hij
        exact ⟨i, j, lt_of_le_of_ne hij (fun h => h_ne (Fin.ext h).symm), h_eq.symm⟩
    -- Use Finset.min' on the nonempty set of collision indices
    let collSet := (Finset.univ : Finset (Fin (q * ℓ))).filter (fun k =>
      collisionAtStep P ℓ hℓ msgs k)
    have h_ne : collSet.Nonempty := by
      obtain ⟨k, hk⟩ := h_exists_coll
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
    let k₀ := collSet.min' h_ne
    have hk₀_mem := Finset.min'_mem collSet h_ne
    rw [Finset.mem_filter] at hk₀_mem
    have hk₀_coll : collisionAtStep P ℓ hℓ msgs k₀ := hk₀_mem.2
    refine ⟨k₀.val, k₀.isLt, ?_, by convert hk₀_coll⟩
    -- goodUpTo k₀: no collision before k₀ (by minimality)
    intro i j hi hj h_ne_ij h_eq
    -- If P-inputs at i,j (both < k₀) are equal with i ≠ j, then
    -- max(i,j) has a collision, contradicting minimality of k₀.
    by_cases hij : i.val < j.val
    · -- j has collision at i, and j.val < k₀.val
      have hj_mem : j ∈ collSet := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ j, ⟨i, hij, h_eq⟩⟩
      have := Finset.min'_le collSet j hj_mem
      exact absurd (Fin.val_le_of_le this) (by omega)
    · push_neg at hij
      have hij' : j.val < i.val := lt_of_le_of_ne hij (fun h => h_ne_ij (Fin.ext h).symm)
      have hi_mem : i ∈ collSet := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ i, ⟨j, hij', h_eq.symm⟩⟩
      have := Finset.min'_le collSet i hi_mem
      exact absurd (Fin.val_le_of_le this) (by omega)
  -- Step 2: bad set ⊆ union of per-step sets → LHS ≤ RHS
  -- Each bad s appears in at least one inner sum.
  let stepSet := fun k : ℕ => (Finset.univ : Finset (DDS B B 1)).filter
    (fun s => if hk : k < q * ℓ then
      goodUpTo (dds1Equiv B B s) ℓ hℓ msgs k (by omega) ∧
      collisionAtStep (dds1Equiv B B s) ℓ hℓ msgs ⟨k, hk⟩
    else False)
  let badSet := (Finset.univ : Finset (DDS B B 1)).filter
    (fun s => ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ msgs)
  -- bad ⊆ biUnion of step sets
  have h_subset : badSet ⊆ (Finset.range (q * ℓ)).biUnion stepSet := by
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_range] at hs ⊢
    have hs_bad : ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ msgs := by
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs; exact hs
    obtain ⟨k, hk, h_good, h_coll⟩ := h_first_collision s hs_bad
    refine ⟨k, hk, ?_⟩
    simp only [stepSet, Finset.mem_filter, Finset.mem_univ, true_and, dif_pos hk]
    exact ⟨h_good, h_coll⟩
  -- Direct proof: each bad s appears in at least one inner sum.
  -- We skip the biUnion intermediate and directly prove the inequality
  -- using h_first_collision to assign each bad s to a specific k.
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => zero_le _))
  -- ∑_{⋃_k S_k} f ≤ ∑_k ∑_{S_k} f for NNReal (by induction on outer Finset)
  suffices h_union_le : ∀ (R : Finset ℕ),
      ∑ s ∈ R.biUnion stepSet, (Dist.uniform (DDS B B 1)) s ≤
      ∑ k ∈ R, ∑ s ∈ stepSet k, (Dist.uniform (DDS B B 1)) s from
    h_union_le (Finset.range (q * ℓ))
  intro R
  induction R using Finset.induction with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    -- ∑_{S_a ∪ ⋃_{S} S_k} f ≤ ∑_{S_a} f + ∑_{⋃_S S_k} f ≤ ∑_{S_a} f + ∑_S ∑_{S_k} f
    -- For the first step: A ∪ B ⊆ A ∪ B, and ∑_{A ∪ B} f ≤ ∑_A f + ∑_B f
    -- because A ∪ B = A ∪ (B \ A), disjoint, and B \ A ⊆ B.
    -- ∑_{Sa ∪ SB} f ≤ ∑_{Sa} f + ∑_{SB} f for NNReal
    -- Proof: Sa ∪ SB = Sa ∪ (SB \ Sa) (disjoint), so ∑ = ∑_Sa + ∑_{SB\Sa} ≤ ∑_Sa + ∑_SB
    set Sa := stepSet a
    set SB := S.biUnion stepSet
    have h_eq : Sa ∪ SB = Sa ∪ (SB \ Sa) := (Finset.union_sdiff_self_eq_union).symm
    have h_disj : Disjoint Sa (SB \ Sa) := disjoint_sdiff_self_right
    rw [h_eq, Finset.sum_union h_disj]
    -- Goal: ∑_Sa f + ∑_{SB\Sa} f ≤ ∑_Sa f + ∑_S ∑_{stepSet k} f
    -- Suffices: ∑_{SB\Sa} f ≤ ∑_S ∑_{stepSet k} f
    -- Chain: ∑_{SB\Sa} f ≤ ∑_SB f ≤ ∑_S ∑_{stepSet k} f
    gcongr
    exact le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => zero_le _))
      ih

/-- Helper: 2 * ∑_{i=0}^{n-1} i = n * (n-1). -/
private theorem two_mul_sum_range_id (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, i = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    rcases n with _ | m
    · simp
    · simp; ring

/-- Arithmetic: ∑_{k=0}^{n-1} k/N ≤ n(n-1)/(2N) = birthdayBound n N. -/
theorem sum_div_le_birthdayBound (n N : ℕ) :
    ∑ k ∈ Finset.range n, (k : NNReal) / (N : NNReal)
    ≤ birthdayBound n N := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul, birthdayBound]
  -- Cast the NNReal sum to a ℕ sum
  have h_sum_nat : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by
    have := two_mul_sum_range_id n; omega
  have h_sum : (∑ i ∈ Finset.range n, (i : NNReal)) = ((n * (n - 1) / 2 : ℕ) : NNReal) := by
    rw [show (∑ i ∈ Finset.range n, (i : NNReal)) =
        ((∑ i ∈ Finset.range n, i : ℕ) : NNReal) from by push_cast; rfl,
        h_sum_nat]
  rw [h_sum, ← div_eq_mul_inv, ← div_eq_mul_inv]
  -- Case split: if N = 0 both sides are 0; if N > 0 cross-multiply
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_div_iff₀ (by exact_mod_cast hN) (by exact_mod_cast (by omega : 0 < 2 * N))]
    exact_mod_cast show n * (n - 1) / 2 * (2 * N) ≤ n * (n - 1) * N from by
      have h := Nat.div_mul_le_self (n * (n - 1)) 2
      nlinarith

/-- **Collision bound**: the probability that a uniform random function
P : B → B causes an internal collision during CBC-MAC on messages `inputs`
is at most the birthday bound on q·ℓ values from B.

## Hypothesis: `h_no_forced_collision`

For every pair of distinct P-input indices, there EXISTS some function
P : B → B for which the P-inputs at those indices differ. This rules
out deterministic collisions (e.g., shared block prefixes) while being
strictly weaker than prefix-freeness.

## Proof Structure

The proof factors into three sub-lemmas:
1. `bad_functions_le_telescoping_sum`: bad mass ≤ ∑_k (step-k collision mass)
2. `cbcMac_step_collision_bound`: step-k collision mass ≤ k/|B|
3. Arithmetic: ∑_{k=0}^{n-1} k/|B| = n(n-1)/(2|B|) = birthdayBound(n, |B|) -/
theorem cbcMac_collision_bound
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    (inputs : Fin q → Fin ℓ → B)
    (h_no_forced_collision : ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
      ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ inputs k₁ ≠
        cbcMacAllPInputs P ℓ hℓ inputs k₂) :
    ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
      (fun s => ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ inputs),
      (Dist.uniform (DDS B B 1)) s
    ≤ birthdayBound (q * ℓ) (Fintype.card B) := by
  -- Step 1: Bad mass ≤ telescoping sum of per-step masses
  have h_tele := bad_functions_le_telescoping_sum hℓ inputs
  -- Step 2: Each per-step mass ≤ k/|B|
  have h_step : ∀ k ∈ Finset.range (q * ℓ),
      ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
        (fun s => if hk : k < q * ℓ then
          goodUpTo (dds1Equiv B B s) ℓ hℓ inputs k (by omega) ∧
          collisionAtStep (dds1Equiv B B s) ℓ hℓ inputs ⟨k, hk⟩
        else False),
        (Dist.uniform (DDS B B 1)) s
      ≤ (k : NNReal) / (Fintype.card B : NNReal) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    -- Simplify the dif with the known hk
    have h_eq : (Finset.univ : Finset (DDS B B 1)).filter
        (fun s => if h : k < q * ℓ then
          goodUpTo (dds1Equiv B B s) ℓ hℓ inputs k (by omega) ∧
          collisionAtStep (dds1Equiv B B s) ℓ hℓ inputs ⟨k, h⟩
        else False) =
      (Finset.univ : Finset (DDS B B 1)).filter
        (fun s => goodUpTo (dds1Equiv B B s) ℓ hℓ inputs k (by omega) ∧
          collisionAtStep (dds1Equiv B B s) ℓ hℓ inputs ⟨k, hk⟩) := by
      congr 1; ext s; simp only [dif_pos hk]
    rw [h_eq]
    exact cbcMac_step_collision_bound hℓ inputs h_no_forced_collision k hk
  -- Step 3: ∑_{k=0}^{n-1} k/|B| = n(n-1)/(2|B|) = birthdayBound
  have h_sum_le : ∑ k ∈ Finset.range (q * ℓ),
      (k : NNReal) / (Fintype.card B : NNReal)
      ≤ birthdayBound (q * ℓ) (Fintype.card B) := by
    exact sum_div_le_birthdayBound (q * ℓ) (Fintype.card B)
  -- Combine
  calc ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
        (fun s => ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ inputs),
        (Dist.uniform (DDS B B 1)) s
      ≤ ∑ k ∈ Finset.range (q * ℓ),
        ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
          (fun s => if hk : k < q * ℓ then
            goodUpTo (dds1Equiv B B s) ℓ hℓ inputs k (by omega) ∧
            collisionAtStep (dds1Equiv B B s) ℓ hℓ inputs ⟨k, hk⟩
          else False),
          (Dist.uniform (DDS B B 1)) s := h_tele
    _ ≤ ∑ k ∈ Finset.range (q * ℓ),
        (k : NNReal) / (Fintype.card B : NNReal) :=
        Finset.sum_le_sum h_step
    _ ≤ birthdayBound (q * ℓ) (Fintype.card B) := h_sum_le

/-- Helper: cbcMacPDS.transcriptDist evaluated at a point equals the sum over the
preimage of the composed map (cbcMacDDS ∘ dds1Equiv). This avoids Fintype instance
diamonds by using only the canonical DDS.instFintype instance. -/
private theorem cbcMacPDS_transcriptDist_eq
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ}
    [Fintype (DDS (Fin ℓ → B) B q)]
    [Nonempty (DDS B B 1)]
    [Fintype (Transcript (Fin ℓ → B) B q)]
    [DecidableEq (Transcript (Fin ℓ → B) B q)]
    (inputs : Fin q → Fin ℓ → B) (t : Transcript (Fin ℓ → B) B q) :
    (cbcMacPDS B ℓ q).transcriptDist inputs t =
    ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
      (fun s => DDS.transcript (cbcMacDDS (dds1Equiv B B s) ℓ q) inputs = t),
      (Dist.uniform (DDS B B 1)) s := by
  -- Here: no explicit [Fintype (DDS B B 1)] parameter, so the only instance
  -- is DDS.instFintype, matching what cbcMacPDS uses internally.
  simp only [PDS.transcriptDist, cbcMacPDS]
  rw [Dist.fTransform_comp]
  -- Now: fTransform (g ∘ f) uniform at t = ∑_{s : (g∘f)(s) = t} uniform(s)
  show Finsupp.mapDomain
    (fun s => DDS.transcript (cbcMacDDS (dds1Equiv B B s) ℓ q) inputs)
    (Dist.uniform (DDS B B 1)) t = _
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  rw [← Finset.sum_filter (p := fun s =>
    DDS.transcript (cbcMacDDS (dds1Equiv B B s) ℓ q) inputs = t)]
  apply Finset.sum_subset
  · exact Finset.filter_subset_filter _ (Finset.subset_univ _)
  · intro a ha1 ha2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha1
    simp only [Finset.mem_filter, not_and] at ha2
    exact Finsupp.notMem_support_iff.mp (by tauto)

-- This theorem combines several large pushforward/conditioning rewrites; allow extra heartbeats.
-- (Kept local to avoid affecting other files.)
set_option maxHeartbeats 2000000 in
/-- **Per-input CBC-MAC security bound**: for messages with no forced
collisions (so, in particular, no repeated messages),

  δ(tr(cbcMacPDS, inputs), tr(Instances.URF, inputs)) ≤ q²ℓ²/(2|B|)

The `h_no_forced_collision` hypothesis ensures no pair of P-input indices
is forced to collide for ALL functions P. This rules out messages that
share block prefixes (e.g., `msg₁ = [a, b]` and `msg₂ = [a, c]` force
the first P-inputs to always equal `0 + a`).

This theorem is intentionally **per-input**: the hypothesis depends on the
chosen `inputs`, so it does not directly imply a bound on `advantage` (which
maximizes over *all* input sequences).

Also, `Instances.URF` here is the **uniform-over-DDS** ideal; for `q > 1` it
returns fresh independent outputs even on repeated inputs. For the paper ideal
(a consistent random function oracle), use `cbcMac_per_input_security_URFfun`.

This combines:
1. Good/bad partition: split P into "no collision" (good) and "collision" (bad)
2. Conditional equivalence: good P's match URF (`cbcMac_cond_equiv_urf`)
3. Collision bound: bad P's have mass ≤ birthday bound (`cbcMac_collision_bound`)
4. Arithmetic: birthdayBound(q·ℓ, |B|) ≤ q²ℓ²/(2|B|) (`birthdayBound_mul_le`) -/
theorem cbcMac_per_input_security
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS (Fin ℓ → B) B q)]
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    [Fintype (Transcript (Fin ℓ → B) B q)]
    [DecidableEq (Transcript (Fin ℓ → B) B q)]
    (inputs : Fin q → Fin ℓ → B)
    (h_no_forced_collision : ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
      ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ inputs k₁ ≠
        cbcMacAllPInputs P ℓ hℓ inputs k₂) :
    statDist ((cbcMacPDS B ℓ q).transcriptDist inputs)
      ((Instances.URF (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs)
    ≤ (q * q * ℓ * ℓ : ℕ) / (2 * Fintype.card B : ℕ) := by
  /-
  ATTEMPT 1 (deprecated):
  The following proof tried to partition by `isGoodFunction` directly on the base
  random function and equate the “good” fiber-sums with URF pointwise. This is
  not the right notion of conditioning (it is not transcript-measurable), and it
  also became incompatible after switching `cbcMac_cond_equiv_urf` to the
  Maurer-style transcript condition on *chaining-value* transcripts.
  -/
  classical
  -- Use the canonical `Pi` fintype instance for `(Fin ℓ → B)` (avoids instance diamonds).
  letI : Fintype (Fin ℓ → B) := Pi.instFintype
  -- Use the canonical `DDS` fintype instance for `DDS B B 1` (avoids instance diamonds).
  letI : Fintype (DDS B B 1) := DDS.instFintype (X := B) (Y := B) (q := 1)
  -- Needed to form the `URF` system at `Y = Fin ℓ → B`.
  haveI : Nonempty (DDS (Fin ℓ → B) (Fin ℓ → B) q) := ⟨⟨fun _ _ => 0⟩⟩
  haveI : Nonempty (Fin q → Fin ℓ → B) := ⟨fun _ _ => 0⟩
  haveI : Nonempty (Fin q → B) := ⟨fun _ => 0⟩
  -- Rewrite both tag transcript distributions as projections of chaining-value transcript distributions.
  have h_cbc_proj :
      (cbcMacPDS B ℓ q).transcriptDist inputs =
        Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
          ((cbcMacChainPDS B ℓ q).transcriptDist inputs) :=
    cbcMacPDS_transcriptDist_eq_fTransform_chainTranscriptDist
      (B := B) (ℓ := ℓ) (q := q) hℓ (inputs := inputs)
  have h_urf_proj :
      (Instances.URF (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs =
        Dist.fTransform (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)
          ((Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs) :=
    (urf_tag_transcriptDist_eq_fTransform_chainTranscriptDist
      (B := B) (ℓ := ℓ) (q := q) hℓ (inputs := inputs)).symm
  -- Chain-level conditional equivalence (paper-style).
  have h_cond :
      (cbcMacChainPDS B ℓ q).condEquiv
        (Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q))
        (noInternalCollisionChain B ℓ q hℓ) :=
    cbcMac_cond_equiv_urf (B := B) (ℓ := ℓ) (q := q) hℓ
  -- Condition failure probability reduces to “bad base functions” via `fTransform_filter_sum`.
  have h_fail :
      conditionFailureProb (cbcMacChainPDS B ℓ q) (noInternalCollisionChain B ℓ q hℓ) inputs =
        ∑ s ∈ (Finset.univ : Finset (DDS B B 1)).filter
          (fun s => ¬isGoodFunction (dds1Equiv B B s) ℓ hℓ inputs),
          (Dist.uniform (DDS B B 1)) s := by
    classical
    -- unfold the failure probability on the pushforward system and regroup using `fTransform_filter_sum`
    simp [conditionFailureProb, cbcMacChainPDS]
    rw [fTransform_filter_sum
      (f := fun s : DDS B B 1 => cbcMacChainDDS (dds1Equiv B B s) ℓ q)
      (X := Dist.uniform (DDS B B 1))
      (P := fun s : DDS (Fin ℓ → B) (Fin ℓ → B) q =>
        ¬(noInternalCollisionChain B ℓ q hℓ).holds (DDS.transcript s inputs))]
    -- simplify the pulled-back predicate using the transcript ↔ good-function lemma
    -- Rewrite the filtered sums as sums over `univ` with an `if`, then simplify the predicate
    -- using the transcript ↔ good-function lemma.
    simp [Finset.sum_filter, Function.comp,
      noInternalCollisionChain_holds_transcript_iff_isGoodFunction
        (B := B) (ℓ := ℓ) (q := q) hℓ (P := dds1Equiv B B _) (inputs := inputs)]
  -- Bound the original (tag) transcript distance by the chain transcript distance (data processing),
  -- then by the chain condition failure probability, and finally by the birthday bound.
  rw [h_cbc_proj, h_urf_proj]
  refine le_trans
    (statDist_fTransform_le
      ((cbcMacChainPDS B ℓ q).transcriptDist inputs)
      ((Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q)).transcriptDist inputs)
      (chainTranscriptToTagTranscript (B := B) (ℓ := ℓ) (q := q) hℓ)) ?_
  refine le_trans (statDist_le_conditionFailure_single
      (cbcMacChainPDS B ℓ q)
      (Instances.URF (X := Fin ℓ → B) (Y := Fin ℓ → B) (q := q))
      (noInternalCollisionChain B ℓ q hℓ) h_cond inputs) ?_
  -- collision bound + arithmetic
  refine le_trans ?_ (birthdayBound_mul_le q ℓ (Fintype.card B))
  rw [h_fail]
  exact cbcMac_collision_bound (B := B) (ℓ := ℓ) (q := q) hℓ inputs h_no_forced_collision

/-! ### Paper-style statement: compare against a uniform random function oracle

The papers (Maurer02 / cbc-improved) idealize CBC-MAC against a *random oracle* /
uniform random function: repeated message queries are answered consistently.

Our local proof `cbcMac_per_input_security` compares against `Instances.URF`, which
is uniform over *all* DDS and therefore behaves beacon-like on repeated inputs.
Under the hypothesis `h_no_forced_collision`, the input sequence is injective,
so `Instances.URFfun` (uniform function oracle) and `Instances.URF` induce the
same transcript distribution. This yields the paper-style per-input bound. -/

private lemma inputs_injective_of_no_forced_collision
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    (inputs : Fin q → Fin ℓ → B)
    (h_no_forced_collision : ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
      ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ inputs k₁ ≠
        cbcMacAllPInputs P ℓ hℓ inputs k₂) :
    Function.Injective inputs := by
  classical
  intro i₁ i₂ hEq
  by_contra hne
  -- Look at the first internal P-input of each query: it is just the first block.
  let k : Fin q → Fin (q * ℓ) :=
    fun i =>
      ⟨i.val * ℓ, by
        have : i.val * ℓ < q * ℓ := Nat.mul_lt_mul_of_pos_right i.isLt hℓ
        simpa using this⟩
  have hk_ne : k i₁ ≠ k i₂ := by
    intro hk
    have : i₁.val = i₂.val := by
      -- cancel by dividing both sides by ℓ (ℓ > 0)
      have hk' : (k i₁).val = (k i₂).val := congrArg Fin.val hk
      have h1 : (k i₁).val / ℓ = (k i₂).val / ℓ := by simp [hk']
      simpa [k, Nat.mul_div_left _ hℓ] using h1
    exact hne (Fin.ext this)
  rcases h_no_forced_collision (k i₁) (k i₂) hk_ne with ⟨P, hP⟩
  -- But the two values are forced equal because `inputs i₁ = inputs i₂`.
  have h_first : inputs i₁ ⟨0, hℓ⟩ = inputs i₂ ⟨0, hℓ⟩ := by
    simpa using congr_fun hEq ⟨0, hℓ⟩
  have h_k (i : Fin q) :
      cbcMacAllPInputs P ℓ hℓ inputs (k i) = inputs i ⟨0, hℓ⟩ := by
    -- At index `i*ℓ`, the block index is 0, so `cbcMacPInput` is just `0 + msg[0]`.
    simp [cbcMacAllPInputs, cbcMacPInput, k, Nat.mul_div_left _ hℓ]
  have : cbcMacAllPInputs P ℓ hℓ inputs (k i₁) = cbcMacAllPInputs P ℓ hℓ inputs (k i₂) := by
    simp [h_k, h_first]
  exact hP this

/-- **Per-input CBC-MAC security bound (paper ideal)**.

This is the same numerical bound as `cbcMac_per_input_security`, but with the
ideal system taken to be `Instances.URFfun` (a consistent uniform random
function oracle on messages), matching Maurer02 / cbc-improved.

The proof is a thin wrapper: `h_no_forced_collision` implies injective `inputs`,
so `URFfun` and `URF` induce the same transcript distribution on these inputs;
then we reuse `cbcMac_per_input_security`. -/
theorem cbcMac_per_input_security_URFfun
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS (Fin ℓ → B) B q)]
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    [Fintype (Transcript (Fin ℓ → B) B q)]
    [DecidableEq (Transcript (Fin ℓ → B) B q)]
    (inputs : Fin q → Fin ℓ → B)
    (h_no_forced_collision : ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
      ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ inputs k₁ ≠
        cbcMacAllPInputs P ℓ hℓ inputs k₂) :
    statDist ((cbcMacPDS B ℓ q).transcriptDist inputs)
      ((Instances.URFfun (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs)
    ≤ (q * q * ℓ * ℓ : ℕ) / (2 * Fintype.card B : ℕ) := by
  classical
  have h_inj : Function.Injective inputs :=
    inputs_injective_of_no_forced_collision (B := B) (ℓ := ℓ) (q := q) hℓ inputs h_no_forced_collision
  have h_ideal :
      (Instances.URFfun (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs =
        (Instances.URF (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs :=
    (urfFun_transcriptDist_eq_urf_transcriptDist_of_injective
      (X := Fin ℓ → B) (Y := B) (q := q) (inputs := inputs) h_inj)
  -- Reduce to the existing bound against `Instances.URF`.
  simpa [h_ideal] using
    (cbcMac_per_input_security (B := B) (ℓ := ℓ) (q := q) hℓ (inputs := inputs) h_no_forced_collision)

/-- Alias for `cbcMac_per_input_security_URFfun` with a “paper ideal” name. -/
theorem cbcMac_per_input_security_paper
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS (Fin ℓ → B) B q)]
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    [Fintype (Transcript (Fin ℓ → B) B q)]
    [DecidableEq (Transcript (Fin ℓ → B) B q)]
    (inputs : Fin q → Fin ℓ → B)
    (h_no_forced_collision : ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
      ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ inputs k₁ ≠
        cbcMacAllPInputs P ℓ hℓ inputs k₂) :
    statDist ((cbcMacPDS B ℓ q).transcriptDist inputs)
      ((Instances.URFfun (X := Fin ℓ → B) (Y := B) (q := q)).transcriptDist inputs)
    ≤ (q * q * ℓ * ℓ : ℕ) / (2 * Fintype.card B : ℕ) :=
  cbcMac_per_input_security_URFfun (B := B) (ℓ := ℓ) (q := q) hℓ (inputs := inputs)
    h_no_forced_collision

/-! ### Lifting per-input bounds to restricted advantage

The per-input theorems above assume an admissibility hypothesis on the chosen
input sequence `inputs`. In game-based terms, this corresponds to proving a PRF
bound for adversaries whose non-adaptive query sequences lie in some admissible
set. We capture this by `advantageOn` (a restricted supremum over inputs). -/

private def noForcedCollisionInputs
    {B : Type*} [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ) (inputs : Fin q → Fin ℓ → B) : Prop :=
  ∀ (k₁ k₂ : Fin (q * ℓ)), k₁ ≠ k₂ →
    ∃ P : B → B, cbcMacAllPInputs P ℓ hℓ inputs k₁ ≠
      cbcMacAllPInputs P ℓ hℓ inputs k₂

private instance noForcedCollisionInputs_decidablePred
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ) : DecidablePred (noForcedCollisionInputs (B := B) (ℓ := ℓ) (q := q) hℓ) :=
  fun inputs => by
    classical
    infer_instance

/-- CBC-MAC security as a *restricted* advantage bound: the supremum over all
input sequences with no forced collisions is at most the birthday bound. -/
theorem cbcMac_advantageOn_noForcedCollision_URFfun
    {B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {ℓ q : ℕ} (hℓ : 0 < ℓ)
    [Fintype (DDS (Fin ℓ → B) B q)] [Nonempty (DDS (Fin ℓ → B) B q)]
    [Fintype (DDS B B 1)] [Nonempty (DDS B B 1)]
    [Fintype (Transcript (Fin ℓ → B) B q)]
    [DecidableEq (Transcript (Fin ℓ → B) B q)] :
    advantageOn (cbcMacPDS B ℓ q)
        (Instances.URFfun (X := Fin ℓ → B) (Y := B) (q := q))
        (noForcedCollisionInputs (B := B) (ℓ := ℓ) (q := q) hℓ)
      ≤ (q * q * ℓ * ℓ : ℕ) / (2 * Fintype.card B : ℕ) := by
  classical
  -- Avoid instance diamonds for `Fintype (Fin ℓ → B)` (used by `advantageOn`).
  letI : Fintype (Fin ℓ → B) := Pi.instFintype
  refine advantageOn_le_of_pointwise
    (S := cbcMacPDS B ℓ q)
    (T := Instances.URFfun (X := Fin ℓ → B) (Y := B) (q := q))
    (Good := noForcedCollisionInputs (B := B) (ℓ := ℓ) (q := q) hℓ)
    (ε := (q * q * ℓ * ℓ : ℕ) / (2 * Fintype.card B : ℕ)) ?_
  intro inputs hGood
  simpa [noForcedCollisionInputs] using
    (cbcMac_per_input_security_URFfun (B := B) (ℓ := ℓ) (q := q) hℓ (inputs := inputs) hGood)

end RandomSystems.Applications
