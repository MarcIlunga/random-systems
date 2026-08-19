/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.Derivation

/-!
# Ideal-compression H-technique facade

This module supplies the scheme-independent infrastructure for direct
H-technique analyses of constructions that expose one shared ideal
compression function through two tagged interfaces:

* `prim` evaluates the compression function directly;
* `eval` evaluates a construction built from that same compression function.

The real and ideal worlds below have the same `prim` interface.  The real
`eval` interface is parameterized by the construction, while the ideal one is
an independent random function per user.  Application modules provide the
construction-specific trace, reveal, good event, and bad-mass argument.

`EnvRespects` is deliberately unchanged.  `TaggedBudgetRespects` is a reusable
transcript predicate consumed by the existing `EnvRespects` and filtered-
advantage APIs, so all existing filters remain source-compatible.
-/

noncomputable section

open scoped BigOperators NNReal RandomSystems.CR18

namespace RandomSystems
namespace HTechnique
namespace IdealCompression

open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation

universe uP uE uR uC uB uU uK uM uD uRole uZ uOmega

attribute [local instance] Classical.propDecidable

variable {C : Type uC} {B : Type uB} {User : Type uU} {Key : Type uK}
variable {Message : Type uM} {Digest : Type uD}
variable {Role : Type uRole} {Z : Type uZ} {Omega : Type uOmega}
variable {n : ℕ}

/-! ## Tagged query accounting -/

/-- A query to a joint primitive/construction resource. -/
inductive TaggedQuery (Prim : Type uP) (Eval : Type uE) where
  | prim (query : Prim)
  | eval (query : Eval)
deriving DecidableEq, Fintype

/-- A response from a joint primitive/construction resource. -/
inductive TaggedReply (Prim : Type uP) (Eval : Type uE) where
  | prim (reply : Prim)
  | eval (reply : Eval)
deriving DecidableEq, Fintype

/-- Number of direct primitive queries in a fixed tagged schedule. -/
def primCount {Prim : Type uP} {Eval : Type uE} {n : ℕ}
    (xs : List.Vector (TaggedQuery Prim Eval) n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i =>
    match xs.get i with
    | .prim _ => True
    | .eval _ => False).card

/-- Number of construction-evaluation queries in a fixed tagged schedule. -/
def evalCount {Prim : Type uP} {Eval : Type uE} {n : ℕ}
    (xs : List.Vector (TaggedQuery Prim Eval) n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i =>
    match xs.get i with
    | .prim _ => False
    | .eval _ => True).card

/-- The generic tag counters agree with their visible-list projections. -/
theorem taggedCounts_toList
    {Prim : Type uP} {Eval : Type uE} {n : ℕ}
    (queries : List.Vector (TaggedQuery Prim Eval) n) :
    primCount queries =
        (queries.toList.filterMap fun query =>
          match query with
          | .prim _ => some ()
          | .eval _ => none).length ∧
      evalCount queries =
        (queries.toList.filterMap fun query =>
          match query with
          | .prim _ => none
          | .eval _ => some ()).length := by
  classical
  induction n with
  | zero =>
      simp [primCount, evalCount]
  | succ n ih =>
      have primCount_cons
          (query : TaggedQuery Prim Eval)
          (tail : List.Vector (TaggedQuery Prim Eval) n) :
          primCount (query ::ᵥ tail) =
            (match query with | .prim _ => 1 | .eval _ => 0) +
              primCount tail := by
        unfold primCount
        simp only [Finset.card_filter]
        rw [Fin.sum_univ_succ]
        cases query <;> simp [List.Vector.get_cons_succ]
      have evalCount_cons
          (query : TaggedQuery Prim Eval)
          (tail : List.Vector (TaggedQuery Prim Eval) n) :
          evalCount (query ::ᵥ tail) =
            (match query with | .prim _ => 0 | .eval _ => 1) +
              evalCount tail := by
        unfold evalCount
        simp only [Finset.card_filter]
        rw [Fin.sum_univ_succ]
        cases query <;> simp [List.Vector.get_cons_succ]
      rw [← queries.cons_head_tail]
      cases queries.head <;>
        simp [primCount_cons, evalCount_cons,
          (ih queries.tail).1, (ih queries.tail).2] <;> omega

/-- Every tagged query is counted in exactly one of the two tag counters. -/
theorem primCount_add_evalCount
    {Prim : Type uP} {Eval : Type uE} {n : ℕ}
    (queries : List.Vector (TaggedQuery Prim Eval) n) :
    primCount queries + evalCount queries = n := by
  classical
  rw [(taggedCounts_toList queries).1, (taggedCounts_toList queries).2]
  have hcount : ∀ l : List (TaggedQuery Prim Eval),
      (l.filterMap fun query =>
          match query with | .prim _ => some () | .eval _ => none).length +
        (l.filterMap fun query =>
          match query with | .prim _ => none | .eval _ => some ()).length =
        l.length := by
    intro l
    induction l with
    | nil => simp
    | cons query l ih => cases query <;> simp <;> omega
  simpa using hcount queries.toList

/-- Primitive-tag counts are monotone under visible-list prefixes. -/
theorem primCount_le_of_toList_prefix
    {Prim : Type uP} {Eval : Type uE} {m n : ℕ}
    (xs : List.Vector (TaggedQuery Prim Eval) m)
    (ys : List.Vector (TaggedQuery Prim Eval) n)
    (h : xs.toList <+: ys.toList) :
    primCount xs ≤ primCount ys := by
  rw [(taggedCounts_toList xs).1, (taggedCounts_toList ys).1]
  exact (h.filterMap fun query =>
    match query with | .prim _ => some () | .eval _ => none).length_le

/-- Evaluation-tag counts are monotone under visible-list prefixes. -/
theorem evalCount_le_of_toList_prefix
    {Prim : Type uP} {Eval : Type uE} {m n : ℕ}
    (xs : List.Vector (TaggedQuery Prim Eval) m)
    (ys : List.Vector (TaggedQuery Prim Eval) n)
    (h : xs.toList <+: ys.toList) :
    evalCount xs ≤ evalCount ys := by
  rw [(taggedCounts_toList xs).2, (taggedCounts_toList ys).2]
  exact (h.filterMap fun query =>
    match query with | .prim _ => none | .eval _ => some ()).length_le

/--
Reusable tagged budget/cost filter.  Its transcript length is fixed by its
type to `p + q`; it separately bounds the number of `prim` and `eval` tags and
requires every visible `eval` request to have trace cost at most `lambda`.

The explicit `evalCost` argument keeps the facade honest: trace cost is
model-specific, while tag accounting is completely generic.
-/
def TaggedBudgetRespects {Prim : Type uP} {Eval : Type uE} {Reply : Type uR}
    (p q lambda : ℕ) (evalCost : Eval → ℕ)
    (t : TranscriptPrefix (TaggedQuery Prim Eval) Reply (p + q)) : Prop :=
  primCount t.1 ≤ p ∧ evalCount t.1 ≤ q ∧
    ∀ i e, t.1.get i = TaggedQuery.eval e → evalCost e ≤ lambda

theorem TaggedBudgetRespects.primCount_le
    {Prim : Type uP} {Eval : Type uE} {Reply : Type uR}
    {evalCost : Eval → ℕ} {p q lambda : ℕ}
    {t : TranscriptPrefix (TaggedQuery Prim Eval) Reply (p + q)}
    (h : TaggedBudgetRespects p q lambda evalCost t) :
    primCount t.1 ≤ p :=
  h.1

theorem TaggedBudgetRespects.evalCount_le
    {Prim : Type uP} {Eval : Type uE} {Reply : Type uR}
    {evalCost : Eval → ℕ} {p q lambda : ℕ}
    {t : TranscriptPrefix (TaggedQuery Prim Eval) Reply (p + q)}
    (h : TaggedBudgetRespects p q lambda evalCost t) :
    evalCount t.1 ≤ q :=
  h.2.1

theorem TaggedBudgetRespects.evalCost_le
    {Prim : Type uP} {Eval : Type uE} {Reply : Type uR}
    {evalCost : Eval → ℕ} {p q lambda : ℕ}
    {t : TranscriptPrefix (TaggedQuery Prim Eval) Reply (p + q)}
    (h : TaggedBudgetRespects p q lambda evalCost t)
    (i : Fin (p + q)) (e : Eval) (hi : t.1.get i = TaggedQuery.eval e) :
    evalCost e ≤ lambda :=
  h.2.2 i e hi

/-! ## Joint ideal-compression worlds -/

/-- A compression function with chaining state `C` and block type `B`. -/
abbrev CompressionFunction (C : Type uC) (B : Type uB) := C → B → C

/-- The tagged query alphabet of a joint ideal-compression resource. -/
abbrev Query (C : Type uC) (B : Type uB) (User : Type uU)
    (Message : Type uM) :=
  TaggedQuery (C × B) (User × Message)

/-- The tagged response alphabet of a joint ideal-compression resource. -/
abbrev Reply (C : Type uC) (Digest : Type uD) := TaggedReply C Digest

/-- Real-world coins: the public compression function and the users' keys. -/
abbrev RealCoins (C : Type uC) (B : Type uB) (User : Type uU)
    (Key : Type uK) :=
  CompressionFunction C B × (User → Key)

/-- Ideal-world coins: the same public compression-function and key types,
plus an independent ideal evaluation function for every user.  The ideal
function ignores the keys, but retaining them in the representative lets an
equality-on-good extension reveal identically distributed dummy keys. -/
abbrev IdealCoins (C : Type uC) (B : Type uB) (User : Type uU)
    (Key : Type uK) (Message : Type uM) (Digest : Type uD) :=
  CompressionFunction C B × ((User → Key) × (User → Message → Digest))

/-- Uniform ideal-compression coins. -/
noncomputable def compressionP [Fintype C] [Fintype B] [Nonempty C] :
    Dist.ProbDist (CompressionFunction C B) :=
  ⟨Dist.uniform (CompressionFunction C B), Dist.uniform_isProbDist⟩

/-- Real joint coins, with a uniform ideal compression function independent
of an arbitrary user-key law. -/
noncomputable def realP [Fintype C] [Fintype B] [Nonempty C]
    (keysP : Dist.ProbDist (User → Key)) :
    Dist.ProbDist (RealCoins C B User Key) :=
  Dist.prodProbDist compressionP keysP

/-- Ideal joint coins: a uniform ideal compression function independent of
the per-user ideal evaluation functions. -/
noncomputable def idealP [Fintype C] [Fintype B] [Nonempty C]
    [Fintype User] [Fintype Message] [Fintype Digest] [Nonempty Digest] :
    (keysP : Dist.ProbDist (User → Key)) →
    Dist.ProbDist (IdealCoins C B User Key Message Digest) :=
  fun keysP =>
  Dist.prodProbDist compressionP
    (Dist.prodProbDist keysP
      ⟨Dist.uniform (User → Message → Digest), Dist.uniform_isProbDist⟩)

/-- The real tagged function.  `eval` is the only construction-specific
ingredient; both interfaces use the same sampled compression function. -/
def realFunction
    (eval : CompressionFunction C B → Key → Message → Digest)
    (coins : RealCoins C B User Key) :
    Query C B User Message → Reply C Digest
  | .prim cb => .prim (coins.1 cb.1 cb.2)
  | .eval um => .eval (eval coins.1 (coins.2 um.1) um.2)

/-- The ideal tagged function.  Its `prim` side exposes the sampled ideal
compression function, while `eval` uses an independent random function for
each user. -/
def idealFunction (coins : IdealCoins C B User Key Message Digest) :
    Query C B User Message → Reply C Digest
  | .prim cb => .prim (coins.1 cb.1 cb.2)
  | .eval um => .eval (coins.2.2 um.1 um.2)

@[simp, grind =]
theorem realFunction_prim
    (eval : CompressionFunction C B → Key → Message → Digest)
    (coins : RealCoins C B User Key) (cb : C × B) :
    realFunction eval coins (.prim cb) = .prim (coins.1 cb.1 cb.2) :=
  rfl

@[simp, grind =]
theorem idealFunction_prim
    (coins : IdealCoins C B User Key Message Digest) (cb : C × B) :
    idealFunction coins (.prim cb) = .prim (coins.1 cb.1 cb.2) :=
  rfl

@[simp, grind =]
theorem realFunction_eval
    (eval : CompressionFunction C B → Key → Message → Digest)
    (coins : RealCoins C B User Key) (um : User × Message) :
    realFunction eval coins (.eval um) =
      .eval (eval coins.1 (coins.2 um.1) um.2) :=
  rfl

@[simp, grind =]
theorem idealFunction_eval
    (coins : IdealCoins C B User Key Message Digest) (um : User × Message) :
    idealFunction coins (.eval um) = .eval (coins.2.2 um.1 um.2) :=
  rfl

/-- Representative of the real shared-primitive world. -/
def realF (eval : CompressionFunction C B → Key → Message → Digest) :
    PFunPDS.RV (RealCoins C B User Key)
      (Query C B User Message) (Reply C Digest) :=
  functionEvaluatorRV (realFunction eval)

/-- Representative of the ideal shared-primitive world. -/
def idealF :
    PFunPDS.RV (IdealCoins C B User Key Message Digest)
      (Query C B User Message) (Reply C Digest) :=
  functionEvaluatorRV idealFunction

/-- Law-level real shared-primitive world. -/
noncomputable def real
    {C : Type uC} {B : Type uB} {User : Type uU} {Key : Type uK}
    {Message : Type uM} {Digest : Type uD}
    [Fintype C] [Fintype B] [Nonempty C]
    (keysP : Dist.ProbDist (User → Key))
    (eval : CompressionFunction C B → Key → Message → Digest) :
    ProbPDS (Query C B User Message) (Reply C Digest) :=
  PFunPDS.Prob.functionEvaluator
    (realP (C := C) (B := B) (User := User) (Key := Key) keysP)
    (realFunction eval)

/-- Law-level ideal shared-primitive world. -/
noncomputable def ideal
    {C : Type uC} {B : Type uB} {User : Type uU} {Key : Type uK}
    {Message : Type uM} {Digest : Type uD}
    [Fintype C] [Fintype B] [Nonempty C]
    [Fintype User] [Fintype Message] [Fintype Digest] [Nonempty Digest]
    (keysP : Dist.ProbDist (User → Key)) :
    ProbPDS (Query C B User Message) (Reply C Digest) :=
  PFunPDS.Prob.functionEvaluator
    (idealP (C := C) (B := B) (User := User)
      (Key := Key) (Message := Message) (Digest := Digest) keysP)
    idealFunction

theorem real_KStepTotal
    {C : Type uC} {B : Type uB} {User : Type uU} {Key : Type uK}
    {Message : Type uM} {Digest : Type uD}
    [Fintype C] [Fintype B] [Nonempty C]
    (keysP : Dist.ProbDist (User → Key))
    (eval : CompressionFunction C B → Key → Message → Digest) (n : ℕ) :
    (real keysP eval).KStepTotal n :=
  functionEvaluatorProb_KStepTotal _ _ n

theorem ideal_KStepTotal
    {C : Type uC} {B : Type uB} {User : Type uU} {Key : Type uK}
    {Message : Type uM} {Digest : Type uD}
    [Fintype C] [Fintype B] [Nonempty C]
    [Fintype User] [Fintype Message] [Fintype Digest] [Nonempty Digest]
    (keysP : Dist.ProbDist (User → Key)) (n : ℕ) :
    (ideal (C := C) (B := B) (User := User)
      (Key := Key) (Message := Message) (Digest := Digest) keysP).KStepTotal n :=
  functionEvaluatorProb_KStepTotal _ _ n

/-! ## Typed trace and reveal carriers -/

/-- One revealed call to the shared compression function, classified by a
construction-specific role. -/
structure TraceEntry (Role : Type uRole) (C : Type uC) (B : Type uB) where
  role : Role
  input : C × B
  output : C
deriving DecidableEq, Fintype

/-- A compression trace padded to the public per-evaluation bound `lambda`. -/
abbrev EvalTrace (Role : Type uRole) (C : Type uC) (B : Type uB)
    (lambda : ℕ) :=
  Fin lambda → Option (TraceEntry Role C B)

/-- Generic reveal carrier for the equality-on-good proof: reveal all user
keys and `evalSlots` ordered compression traces, each padded to `lambda`.
Unlike an unbounded `List`, this is a finite carrier suitable for the existing
representative-extension endpoint. -/
structure Reveal (User : Type uU) (Key : Type uK) (Role : Type uRole)
    (C : Type uC) (B : Type uB) (evalSlots lambda : ℕ) where
  keys : User → Key
  evalTraces : Fin evalSlots → EvalTrace Role C B lambda
deriving DecidableEq, Fintype

/-- A representative-level, transcript-dependent reveal of the carrier above. -/
abbrev RevealMap (Omega : Type uOmega) (User : Type uU) (Key : Type uK)
    (Role : Type uRole) (C : Type uC) (B : Type uB)
    (Message : Type uM) (Digest : Type uD)
    (n evalSlots lambda : ℕ) :=
  Omega → TranscriptPrefix (Query C B User Message) (Reply C Digest) n →
    Reveal User Key Role C B evalSlots lambda

/-- Thin typed facade over the existing representative extension. -/
noncomputable def extension
    [Fintype Z] [DecidableEq Z]
    [FiniteTranscriptSpace (Query C B User Message) (Reply C Digest) n]
    (p : Dist.ProbDist Omega)
    (F : PFunPDS.RV Omega (Query C B User Message) (Reply C Digest))
    (aug : Omega →
      TranscriptPrefix (Query C B User Message) (Reply C Digest) n → Z)
    (E : PFunDDS.DDE (Query C B User Message) (Reply C Digest)) :
    Dist (TranscriptPrefix (Query C B User Message) (Reply C Digest) n × Z) :=
  extendedTranscriptDistRep p F aug E

/-- Forgetting an ideal-compression reveal recovers the visible transcript
law.  This is exactly the existing representative-extension projection law. -/
theorem fTransform_fst_extension
    [Fintype Z] [DecidableEq Z]
    [FiniteTranscriptSpace (Query C B User Message) (Reply C Digest) n]
    [DiscreteTranscriptSpace (Query C B User Message) (Reply C Digest) n]
    (p : Dist.ProbDist Omega)
    (F : PFunPDS.RV Omega (Query C B User Message) (Reply C Digest))
    (aug : Omega →
      TranscriptPrefix (Query C B User Message) (Reply C Digest) n → Z)
    (E : PFunDDS.DDE (Query C B User Message) (Reply C Digest)) :
    Dist.fTransform Prod.fst (extension p F aug E) =
      PFunPDS.Prob.deterministicTranscriptDist
        (q := n)
        (Dist.PMF p F : ProbPDS (Query C B User Message) (Reply C Digest)) E := by
  exact fTransform_fst_extendedTranscriptDistRep p F aug E

/-! ## Filtered equality-on-good endpoint -/

/--
Filtered equality-on-good representative endpoint.  This is only the
`eps = 0` specialization of
`adv_le_of_extFixedQueryRep_ratio_of_good_filtered`; no fundamental theorem,
coupling, or extension argument is reproved here.
-/
theorem adv_le_of_extFixedQueryRep_eq_on_good_filtered
    {X : Type uP} {Y : Type uR} {Omega : Type uOmega} {Omega' : Type uE}
    {Z : Type uZ} {n : ℕ}
    [FiniteTranscriptSpace X Y n] [DecidableEq X]
    [Fintype Z] [DecidableEq Z] [DiscreteTranscriptSpace X Y n]
    (Filt : TranscriptPrefix X Y n → Prop)
    (pR : Dist.ProbDist Omega) (FR : PFunPDS.RV Omega X Y)
    (pI : Dist.ProbDist Omega') (FI : PFunPDS.RV Omega' X Y)
    (augR : Omega → TranscriptPrefix X Y n → Z)
    (augI : Omega' → TranscriptPrefix X Y n → Z)
    (Bad : TranscriptPrefix X Y n × Z → Prop) (deltaBad : NNReal)
    (hR : PFunPDS.Prob.KStepTotal (Dist.PMF pR FR) n)
    (hI : PFunPDS.Prob.KStepTotal (Dist.PMF pI FI) n)
    (h_eq : ∀ (xs : Fin n → X) (tz : TranscriptPrefix X Y n × Z),
      ¬ Bad tz →
      extFixedQueryTranscriptDistRep pR FR augR xs tz =
        extFixedQueryTranscriptDistRep pI FI augI xs tz)
    (h_bad : ∀ E : QQueryEnvironment X Y n, EnvRespects Filt E →
      probBad (extendedTranscriptDistRep (q := n) pI FI augI E.1) Bad ≤
        deltaBad) :
    filteredAdaptiveTranscriptAdvantage Filt
        (Dist.PMF pR FR : ProbPDS X Y) (Dist.PMF pI FI : ProbPDS X Y) ≤
      (deltaBad : ℝ) := by
  simpa using
    adv_le_of_extFixedQueryRep_ratio_of_good_filtered Filt pR FR pI FI
      augR augI Bad 0 deltaBad hR hI
      (fun xs tz hgood => by
        rw [h_eq xs tz hgood]
        simp)
      h_bad

/--
Filtered equality-on-good representative endpoint with a filter-conditional
mass premise.  Unlike `adv_le_of_extFixedQueryRep_eq_on_good_filtered`, the
extended fixed-query masses need agree only when the visible transcript
satisfies `Filt`.  A respecting environment gives zero mass to every other
visible transcript, so no equality hypothesis is needed there.

This is the equality specialization of the filtered ratio pattern from
`adv_le_of_fixedQuery_ratio_of_good_filtered`; it reuses the representative
projection and H-technique bounds and does not invoke a new fundamental or
coupling argument.
-/
theorem adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter
    {X : Type uP} {Y : Type uR} {Omega : Type uOmega} {Omega' : Type uE}
    {Z : Type uZ} {n : ℕ}
    [FiniteTranscriptSpace X Y n] [DecidableEq X]
    [Fintype Z] [DecidableEq Z] [DiscreteTranscriptSpace X Y n]
    (Filt : TranscriptPrefix X Y n → Prop)
    (pR : Dist.ProbDist Omega) (FR : PFunPDS.RV Omega X Y)
    (pI : Dist.ProbDist Omega') (FI : PFunPDS.RV Omega' X Y)
    (augR : Omega → TranscriptPrefix X Y n → Z)
    (augI : Omega' → TranscriptPrefix X Y n → Z)
    (Bad : TranscriptPrefix X Y n × Z → Prop) (deltaBad : NNReal)
    (hR : PFunPDS.Prob.KStepTotal (Dist.PMF pR FR) n)
    (hI : PFunPDS.Prob.KStepTotal (Dist.PMF pI FI) n)
    (h_eq : ∀ (xs : Fin n → X) (tz : TranscriptPrefix X Y n × Z),
      Filt tz.1 → ¬ Bad tz →
      extFixedQueryTranscriptDistRep pR FR augR xs tz =
        extFixedQueryTranscriptDistRep pI FI augI xs tz)
    (h_bad : ∀ E : QQueryEnvironment X Y n, EnvRespects Filt E →
      probBad (extendedTranscriptDistRep (q := n) pI FI augI E.1) Bad ≤
        deltaBad) :
    filteredAdaptiveTranscriptAdvantage Filt
        (Dist.PMF pR FR : ProbPDS X Y) (Dist.PMF pI FI : ProbPDS X Y) ≤
      (deltaBad : ℝ) := by
  refine filteredAdaptiveTranscriptAdvantage_le_of_pointwise Filt _ _ _
    (by positivity) ?_
  intro E hE
  have h_ext := RandomSystems.hTechnique_eq_on_good
    (extendedTranscriptDistRep (q := n) pR FR augR E.1)
    (extendedTranscriptDistRep (q := n) pI FI augI E.1) Bad
    (extendedTranscriptDistRep_nonNeg pR FR augR E.1)
    (extendedTranscriptDistRep_nonNeg pI FI augI E.1) (by
      rw [extendedTranscriptDistRep_weight, extendedTranscriptDistRep_weight,
        deterministicTranscriptDist_weight_eq_one _ E hR,
        deterministicTranscriptDist_weight_eq_one _ E hI]) (fun tz hgood => by
      by_cases hfilt : Filt tz.1
      · rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply,
          ← extFixedQueryTranscriptDistRep_self pR FR augR tz,
          ← extFixedQueryTranscriptDistRep_self pI FI augI tz,
          h_eq (functionOfVector tz.1.1) tz hfilt hgood]
      · have hnotConsistent : ¬ E.1 ⊨ tz.1 := fun hconsistent =>
          hfilt (hE tz.1 hconsistent)
        simp [extendedTranscriptDistRep_apply, envFactor_eq_indicator,
          hnotConsistent])
  have h_proj := statDist_le_of_extension
    (PFunPDS.Prob.deterministicTranscriptDist (q := n)
      (Dist.PMF pR FR : ProbPDS X Y) E.1)
    (PFunPDS.Prob.deterministicTranscriptDist (q := n)
      (Dist.PMF pI FI : ProbPDS X Y) E.1)
    (extendedTranscriptDistRep (q := n) pR FR augR E.1)
    (extendedTranscriptDistRep (q := n) pI FI augI E.1)
    (fTransform_fst_extendedTranscriptDistRep pR FR augR E.1)
    (fTransform_fst_extendedTranscriptDistRep pI FI augI E.1)
  exact_mod_cast h_proj.trans (h_ext.trans (h_bad E hE))

end IdealCompression
end HTechnique
end RandomSystems
