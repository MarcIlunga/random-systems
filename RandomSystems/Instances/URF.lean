/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS
import RandomSystems.Instances.URFfunEval
import RandomSystems.StatDist

/-!
# Uniform Random Function (URF) / Uniform Random DDS

Paper Example 5 / Definition 15 (Maurer02 / Lanzenberger-Maurer20):
the *uniform random function* is uniform over all functions `X → Y`.

This file contains two related objects:

* `URF` — uniform over **all** `(X,Y)`-DDS of query bound `q`. For `q = 1`,
  this coincides with the uniform random function (`DDS X Y 1 ≃ (X → Y)`), but
  for `q > 1` it is *strictly more general* because a DDS may depend on the full
  query prefix (i.e., can be history-dependent / stateful).
* `URFfun` — uniform over functions `X → Y`, embedded as a stateless DDS via
  `DDS.ofFunq`. This matches the “random function / random oracle” notion used
  in the CBC-MAC papers.

## Main Definitions

* `URF` — uniform over all DDS (a “uniform random DDS”)
* `URFfun` — uniform over all functions `X → Y` (a consistent function oracle)
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Instances

variable {X Y : Type*} {q : ℕ} [Fintype X] [DecidableEq X] [Fintype Y]
variable [Fintype (DDS X Y q)]

/-- The Uniform Random Function: uniform distribution over all DDS.

This assigns mass `1 / |DDS X Y q|` to every deterministic system. -/
def URF [Nonempty (DDS X Y q)] : PDS X Y q where
  dist := Dist.uniform (DDS X Y q)

/-! ### Uniform random function (consistent oracle) as a PDS -/

/-- A random function oracle drawn from an arbitrary distribution on functions.

This samples `f : X → Y` according to `Df` and answers each query with `f x`
(consistently across repeated inputs). -/
def URFfunOf [DecidableEq Y] (Df : Dist (X → Y)) : PDS X Y q where
  dist := Dist.fTransform (fun f : X → Y => DDS.ofFunq (q := q) f) Df

/-- Uniform random function (URF): pick `f : X → Y` uniformly and answer each
query with `f` applied to the current input (consistently across repeated
queries). Formally this is the pushforward of `uniform (X → Y)` along
`DDS.ofFunq`. -/
def URFfun [DecidableEq Y] [Nonempty Y] : PDS X Y q where
  dist := (URFfunOf (X := X) (Y := Y) (q := q) (Dist.uniform (X → Y))).dist

omit [Fintype X] [DecidableEq X] [Fintype Y] in
/-- URF is a probability PDS (weight = 1) when the DDS type is nonempty. -/
theorem URF_isProbPDS [Nonempty (DDS X Y q)] :
    (URF (X := X) (Y := Y) (q := q)).isProbPDS := by
  unfold PDS.isProbPDS Dist.isProbDist URF
  exact Dist.weight_uniform

/-- Evaluating a single-query URF at any input produces the uniform
distribution on outputs.

`fTransform (firstQuery · x₀) (uniform DDS) = uniform Y`

Proof: fiber counting shows `|{s | firstQuery s x₀ = y}| = |Y|^(|X|-1)`,
and `|DDS X Y 1| = |Y|^|X|`, giving ratio `1/|Y|`. -/
theorem URF_eval_eq_uniform [DecidableEq Y] [Nonempty (DDS X Y 1)] [Nonempty Y] (x₀ : X) :
    Dist.fTransform (fun s : DDS X Y 1 => s.firstQuery Nat.zero_lt_one x₀)
      (Dist.uniform (DDS X Y 1)) = Dist.uniform Y := by
  ext y
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, Dist.uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
    (fun _ : DDS X Y 1 => (1 : NNReal) / (Fintype.card (DDS X Y 1) : NNReal))).support
    = Finset.univ := by
    ext s; simp_all [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul,
    mul_one_div]
  have h_fiber_card : (Finset.univ.filter
      (fun s : DDS X Y 1 => s.firstQuery Nat.zero_lt_one x₀ = y)).card =
      Fintype.card Y ^ (Fintype.card X - 1) := by
    rw [show (Finset.univ.filter
        (fun s : DDS X Y 1 => s.firstQuery Nat.zero_lt_one x₀ = y)).card =
        (Finset.univ.filter (fun f : X → Y => f x₀ = y)).card from by
      apply Finset.card_bij (fun s _ => dds1Equiv X Y s)
      · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢; exact hs
      · intro s₁ _ s₂ _ h; exact (dds1Equiv X Y).injective h
      · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        refine ⟨(dds1Equiv X Y).symm f, ?_, (dds1Equiv X Y).apply_symm_apply f⟩
        simp only [dds1Equiv]; exact hf]
    have h := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset Y) x₀
      (Finset.mem_univ y)
    rw [Fintype.piFinset_univ, Finset.card_univ] at h; exact h
  have h_total_card : Fintype.card (DDS X Y 1) = Fintype.card Y ^ Fintype.card X := by
    exact Fintype.card_congr (dds1Equiv X Y) ▸ Fintype.card_fun
  rw [h_fiber_card, h_total_card]
  haveI : Nonempty X := ⟨x₀⟩
  have h_pos : 0 < Fintype.card Y := Fintype.card_pos
  have h_card : Fintype.card Y ^ Fintype.card X =
      Fintype.card Y ^ (Fintype.card X - 1) * Fintype.card Y := by
    rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos]
  rw [h_card, Nat.cast_mul, div_mul_eq_div_div,
    div_self (show (↑(Fintype.card Y ^ (Fintype.card X - 1)) : NNReal) ≠ 0 from by
      exact_mod_cast pow_ne_zero _ h_pos.ne'), one_div]

end RandomSystems.Instances

namespace RandomSystems

/-- Transcript mass of a stateless `URFfunOf` world on a matching transcript:
the pushforward "evaluate at the query points" mass of the function
distribution. -/
theorem transcriptDist_URFfunOf_match
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (Df : Dist (X → Y))
    (xs : Fin q → X) (t : Transcript X Y q) (hmatch : transcriptInputsMatch xs t) :
    (Instances.URFfunOf (X := X) (Y := Y) (q := q) Df).transcriptDist xs t =
      Dist.fTransform (fun f : X → Y => fun i => f (xs i)) Df (transcriptOutputs t) := by
  classical
  unfold PDS.transcriptDist Instances.URFfunOf
  rw [Dist.fTransform_comp, Dist.fTransform_apply_eq_sum, Dist.fTransform_apply_eq_sum]
  apply Finset.sum_congr
  · ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hf
      funext i
      have hpoint := congr_fun hf i
      simpa [DDS.transcript, DDS.ofFunq, transcriptOutputs] using congrArg Prod.snd hpoint
    · intro hf
      funext i
      apply Prod.ext
      · simpa [DDS.transcript, DDS.ofFunq] using (hmatch i).symm
      · have hpoint := congr_fun hf i
        simpa [DDS.transcript, DDS.ofFunq, transcriptOutputs] using hpoint
  · intro f _
    rfl

/-- Transcript mass of a stateless `URFfunOf` world on a mismatched transcript
is zero. -/
theorem transcriptDist_URFfunOf_mismatch
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (Df : Dist (X → Y))
    (xs : Fin q → X) (t : Transcript X Y q) (hmatch : ¬ transcriptInputsMatch xs t) :
    (Instances.URFfunOf (X := X) (Y := Y) (q := q) Df).transcriptDist xs t = 0 := by
  classical
  unfold PDS.transcriptDist Instances.URFfunOf
  rw [Dist.fTransform_comp, Dist.fTransform_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  exfalso
  apply hmatch
  intro i
  have hpoint := congr_fun hf i
  simpa [DDS.transcript, DDS.ofFunq] using (congrArg Prod.fst hpoint).symm

/-- On a transcript recording distinct fixed queries, the uniform random
function assigns uniform mass `1 / |Y| ^ q`. -/
theorem transcriptDist_URFfun_uniform
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (xs : Fin q → X) (h_inj : Function.Injective xs)
    (t : Transcript X Y q) (hmatch : transcriptInputsMatch xs t) :
    (Instances.URFfun (X := X) (Y := Y) (q := q)).transcriptDist xs t =
      1 / (Fintype.card Y : NNReal) ^ q := by
  simp only [Instances.URFfun]
  rw [transcriptDist_URFfunOf_match (Dist.uniform (X → Y)) xs t hmatch,
    Instances.eval_nonces_uniform xs h_inj, Dist.uniform_apply, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]

/-- Every `ofStatelessOracleDist` world is a `URFfunOf` of the pushforward
function distribution. -/
theorem ofStatelessOracleDist_eq_URFfunOf
    {X Y A : Type*} {q : ℕ}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    [Fintype A] [Fintype (DDS X Y q)]
    (D : Dist A) (oracle : A → X → Y) :
    PDS.ofStatelessOracleDist (X := X) (Y := Y) (q := q) D oracle =
      Instances.URFfunOf (Dist.fTransform oracle D) := by
  unfold PDS.ofStatelessOracleDist Instances.URFfunOf
  congr 1
  rw [Dist.fTransform_comp]
  rfl

/-- For compatible transcripts, an adaptive `URFfunOf` transcript mass equals
the non-adaptive transcript mass on the query vector recorded by the transcript. -/
theorem adaptiveTranscriptDist_URFfunOf_eq_of_compatible
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (Df : Dist (X → Y)) (e : DDE X Y q) (t : Transcript X Y q)
    (hcompat : Transcript.compatibleWithEnv e t) :
    (Instances.URFfunOf (X := X) (Y := Y) (q := q) Df).adaptiveTranscriptDist e t =
      (Instances.URFfunOf (X := X) (Y := Y) (q := q) Df).transcriptDist
        (fun i => (t i).1) t := by
  classical
  unfold PDS.adaptiveTranscriptDist PDS.transcriptDist Instances.URFfunOf
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  rw [Dist.fTransform_apply_eq_sum, Dist.fTransform_apply_eq_sum]
  apply Finset.sum_congr
  · ext f
    simp [interact_ofFunq_eq_iff, hcompat]
  · intro f _
    rfl

/-- Incompatible transcripts have zero adaptive mass for any stateless
function-oracle distribution. -/
theorem adaptiveTranscriptDist_URFfunOf_eq_zero_of_incompatible
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (Df : Dist (X → Y)) (e : DDE X Y q) (t : Transcript X Y q)
    (hcompat : ¬ Transcript.compatibleWithEnv e t) :
    (Instances.URFfunOf (X := X) (Y := Y) (q := q) Df).adaptiveTranscriptDist e t = 0 := by
  classical
  unfold PDS.adaptiveTranscriptDist Instances.URFfunOf
  rw [Dist.fTransform_comp]
  rw [Dist.fTransform_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  exact (hcompat (compatibleWithEnv_of_interact_eq _ _ _ hf)).elim

/-- UPSTREAM-CANDIDATE: `URFfun` adaptive transcripts are the pushforward of the
uniform function distribution along deterministic interaction. -/
theorem urffun_aTD_eq_fTransform_uniform
    {X Y : Type*} {q : ℕ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)]
    (e : DDE X Y q) :
    (Instances.URFfun (X := X) (Y := Y) (q := q)).adaptiveTranscriptDist e =
      Dist.fTransform (fun f : X → Y => interact (DDS.ofFunq f) e)
        (Dist.uniform (X → Y)) := by
  unfold PDS.adaptiveTranscriptDist Instances.URFfun Instances.URFfunOf
  rw [Dist.fTransform_comp]
  rfl

/-- UPSTREAM-CANDIDATE: predicate mass bound for adaptive `URFfun` transcripts
from a function-fiber count. -/
theorem urffun_evalPred_le
    {X Y : Type*} {q : ℕ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)]
    (e : DDE X Y q) (P : Transcript X Y q → Prop) [DecidablePred P]
    {d : ℕ} (hd : 0 < d)
    (hcard : d * (Finset.univ.filter (fun f : X → Y =>
        P (interact (DDS.ofFunq f) e))).card ≤ Fintype.card (X → Y)) :
    ((Instances.URFfun (X := X) (Y := Y) (q := q)).adaptiveTranscriptDist e).evalPred P
      ≤ 1 / (d : NNReal) := by
  rw [urffun_aTD_eq_fTransform_uniform]
  exact Dist.evalPred_fTransform_uniform_le _ P hd hcard

/-- UPSTREAM-CANDIDATE: birthday-style union bound for adaptive `URFfun`
transcript bad events. -/
theorem probBad_urffun_birthday_le
    {X Y ι : Type*} {q : ℕ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype ι] [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)]
    (e : DDE X Y q) (B : Transcript X Y q → Prop)
    (P : ι → Transcript X Y q → Prop) [∀ p, DecidablePred (P p)]
    {d : ℕ} (hd : 0 < d)
    (hB : ∀ t, B t → ∃ p, P p t)
    (hpair : ∀ p : ι, d * (Finset.univ.filter (fun f : X → Y =>
        P p (interact (DDS.ofFunq f) e))).card ≤ Fintype.card (X → Y)) :
    probBad ((Instances.URFfun (X := X) (Y := Y) (q := q)).adaptiveTranscriptDist e) B
      ≤ (Fintype.card ι : NNReal) / (d : NNReal) := by
  refine le_trans (probBad_iUnion_le _ B P hB) ?_
  calc ∑ p : ι,
        ((Instances.URFfun (X := X) (Y := Y) (q := q)).adaptiveTranscriptDist e).evalPred (P p)
      ≤ ∑ _p : ι, (1 / (d : NNReal)) :=
        Finset.sum_le_sum (fun p _ => urffun_evalPred_le e (P p) hd (hpair p))
    _ = (Fintype.card ι : NNReal) / (d : NNReal) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

end RandomSystems
