/-
Boneh–Shoup §6.4 (prefix-free PRFs for long messages): Cascade construction.

This file sets up the *variable-length* cascade object in the RandomSystems/PDS framework,
and the prefix-free restriction on non-adaptive environments.

What this corresponds to in the book:
- Base primitive (short-input PRF): `F' : K × X → K` (key space `K`, block space `X`).
- Long-input cascade: start from secret `k : K`, then update `t := F'(t, a_i)` for blocks `a_i`.
- Security notion: only against *prefix-free* adversaries (no query is a proper prefix of another).

Status:
- Definitions are complete.
- The core prefix-free security bound is proved:
  `advantageOn_URFfunCascadeIdeal_URFfun_prefixFree_le_birthday`.

This file is imported by `RandomSystems.lean`.
-/
import RandomSystems.Instances.URF
import RandomSystems.Instances.URFfunEval
import RandomSystems.Advantage
import RandomSystems.ConditionBased
import RandomSystems.Applications.PRPPRFSwitching
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Infix

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

namespace BonehShoup6_4

variable {K X : Type*}

/-! ### Message type (bounded, non-empty block lists) -/

/-- Messages are non-empty lists of blocks with length bounded by `ℓ`. -/
abbrev Msg (X : Type*) (ℓ : ℕ) : Type _ :=
  { m : List X // m ≠ [] ∧ m.length ≤ ℓ }

lemma Msg.ne_nil {X : Type*} {ℓ : ℕ} (m : Msg X ℓ) : (m.1 : List X) ≠ [] :=
  m.2.1

lemma Msg.length_le {X : Type*} {ℓ : ℕ} (m : Msg X ℓ) : m.1.length ≤ ℓ :=
  m.2.2

/-! ### Prefix-free restriction on environments -/

def ProperPrefix {X : Type*} (m m' : List X) : Prop :=
  m <+: m' ∧ m ≠ m'

/-- Prefix-free non-adaptive input sequences (Boneh–Shoup Definition 4.5 / §6.4):
no query is a *proper* prefix of another. Equal messages are allowed. -/
def PrefixFree (X : Type*) (ℓ q : ℕ) (inputs : Fin q → Msg X ℓ) : Prop :=
  ∀ i j : Fin q, i ≠ j → ¬ ProperPrefix (inputs i).1 (inputs j).1

instance {X : Type*} [DecidableEq X] {ℓ q : ℕ} :
    DecidablePred (PrefixFree X ℓ q) := by
  classical
  infer_instance

/-! ### Cascade evaluation and the induced PDS -/

/-- Evaluate the cascade defined by a transition function `h : K × X → K` and initial key `k0`
on a (block) message `m`. -/
def cascadeEval {K X : Type*} (h : K × X → K) (k0 : K) (m : List X) : K :=
  m.foldl (fun t a => h (t, a)) k0

/-- A non-uniform transition primitive: sample `h : K × X → K` from `Dh` and answer queries with `h`.

This is the Random Systems version of “a (possibly keyed) PRF on short inputs”. -/
def transitionPrimitive (K X : Type*)
    [Fintype K] [DecidableEq K]
    [Fintype X] [DecidableEq X]
    (q : ℕ) (Dh : Dist (K × X → K)) : PDS (K × X) K q :=
  Instances.URFfunOf (X := K × X) (Y := K) (q := q) Dh

/-- Cascade oracle induced by an arbitrary distribution `Dh` on transition functions. -/
def URFfunCascadeOf (K X : Type*)
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    (ℓ q : ℕ) [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)]
    (Dh : Dist (K × X → K)) : PDS (Msg X ℓ) K q where
  dist :=
    Dist.fTransform
      (fun p : K × (K × X → K) =>
        DDS.ofFunq (q := q) (fun msg => cascadeEval (K := K) (X := X) p.2 p.1 msg.1))
      (Dist.prod (Dist.uniform K) Dh)

/-- Idealized cascade oracle distribution:
sample a uniform initial key `k0 : K` and a uniform random transition `h : K × X → K`,
then answer each query message by `cascadeEval h k0 message`.

This is the RandomSystems version of the "cascade built from a truly random function"
hybrid used inside Boneh–Shoup’s proof of Theorem 6.4.
-/
def URFfunCascadeIdeal (K X : Type*)
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    (ℓ q : ℕ) [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] : PDS (Msg X ℓ) K q where
  dist := (URFfunCascadeOf (K := K) (X := X) (ℓ := ℓ) (q := q) (Dist.uniform (K × X → K))).dist

/-! ### Prefix-trace instrumentation (Maurer-style condition-based proof) -/

/-- The prefix-length index into a message's trace (the full message length). -/
def tagIndex {X : Type*} {ℓ : ℕ} (m : Msg X ℓ) : Fin (ℓ + 1) :=
  ⟨m.1.length, Nat.lt_succ_of_le (Msg.length_le m)⟩

/-- Package the non-empty prefix `m.take j` as a `Msg`, for `j ≠ 0`. -/
def takeMsg {X : Type*} {ℓ : ℕ} (m : Msg X ℓ) (j : Fin (ℓ + 1)) (hj : j.val ≠ 0) : Msg X ℓ :=
  ⟨m.1.take j.val, by
    constructor
    · intro hnil
      have := (List.take_eq_nil_iff (l := m.1) (k := j.val)).1 hnil
      rcases this with hj0 | hnil'
      · exact (hj hj0).elim
      · exact (Msg.ne_nil m) hnil'
    · -- `length (take j m) ≤ j ≤ ℓ`
      have hjle : j.val ≤ ℓ := Nat.le_of_lt_succ j.isLt
      exact le_trans (List.length_take_le j.val m.1) hjle⟩

/-- The full cascade trace of a message: for each prefix length `j`, return
`cascadeEval h k0 (m.take j)` (with `take 0` giving the root `k0`). -/
def cascadeTrace {K X : Type*} {ℓ : ℕ} (h : K × X → K) (k0 : K) (m : Msg X ℓ) :
    Fin (ℓ + 1) → K :=
  fun j => cascadeEval (K := K) (X := X) h k0 (m.1.take j.val)

/-- Ideal prefix-trace oracle induced by a uniform random function on `Msg X ℓ`. -/
def URFfunPrefixTraceIdeal (K X : Type*)
    [Fintype K] [DecidableEq K] [Nonempty K]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] :
    PDS (Msg X ℓ) (Fin (ℓ + 1) → K) q where
  dist :=
    Dist.fTransform
      (fun p : K × (Msg X ℓ → K) =>
        DDS.ofFunq (q := q) (fun msg =>
          fun j =>
            if hj : j.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) msg j hj)))
      (Dist.prod (Dist.uniform K) (Dist.uniform (Msg X ℓ → K)))

/-- Ideal prefix-trace oracle, additionally exposing the *tag* explicitly as the first component.

This packaging is convenient for **adaptive** environments: the environment can ignore the trace
and use only the tag, without needing to know the queried message length. -/
def URFfunPrefixTraceIdealTag (K X : Type*)
    [Fintype K] [DecidableEq K] [Nonempty K]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] :
    PDS (Msg X ℓ) (K × (Fin (ℓ + 1) → K)) q where
  dist :=
    Dist.fTransform
      (fun p : K × (Msg X ℓ → K) =>
        DDS.ofFunq (q := q) (fun msg =>
          let tr : Fin (ℓ + 1) → K :=
            fun j => if hj : j.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) msg j hj)
          (tr (tagIndex msg), tr)))
      (Dist.prod (Dist.uniform K) (Dist.uniform (Msg X ℓ → K)))

/-- Instrumented cascade oracle: output the entire prefix trace for each query. -/
def URFfunCascadeIdealTrace (K X : Type*)
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] :
    PDS (Msg X ℓ) (Fin (ℓ + 1) → K) q where
  dist :=
    (Dist.fTransform
      (fun p : K × (K × X → K) =>
        DDS.ofFunq (q := q) (fun msg => cascadeTrace (K := K) (X := X) (ℓ := ℓ) p.2 p.1 msg))
      (Dist.prod (Dist.uniform K) (Dist.uniform (K × X → K))))

/-- Instrumented cascade oracle, additionally exposing the tag explicitly as the first component. -/
def URFfunCascadeIdealTraceTag (K X : Type*)
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] :
    PDS (Msg X ℓ) (K × (Fin (ℓ + 1) → K)) q where
  dist :=
    Dist.fTransform
      (fun p : K × (K × X → K) =>
        DDS.ofFunq (q := q) (fun msg =>
          let tr := cascadeTrace (K := K) (X := X) (ℓ := ℓ) p.2 p.1 msg
          (tr (tagIndex msg), tr)))
      (Dist.prod (Dist.uniform K) (Dist.uniform (K × X → K)))

/-- Project a (tag, trace)-transcript to a tag-only transcript by dropping the trace component. -/
def traceTagTranscriptToTagTranscript {K X : Type*} {ℓ q : ℕ} :
    Transcript (Msg X ℓ) (K × (Fin (ℓ + 1) → K)) q → Transcript (Msg X ℓ) K q :=
  fun t i =>
    let msg := (t i).1
    (msg, (t i).2.1)

/-- Project a prefix-trace transcript to a tag-only transcript by selecting the component at
the full message length. -/
def traceTranscriptToTagTranscript {K X : Type*} {ℓ q : ℕ} :
    Transcript (Msg X ℓ) (Fin (ℓ + 1) → K) q → Transcript (Msg X ℓ) K q :=
  fun t i =>
    let msg := (t i).1
    (msg, (t i).2 (tagIndex msg))

/-- **Good trace** condition: prefix labels are consistent and collision-free.

Formally, for any two positions `(i,j)` and `(i',j')`, the corresponding prefixes
`(t i).1.take j` and `(t i').1.take j'` are equal iff the reported labels are equal. -/
def goodPrefixTrace (K X : Type*) {ℓ q : ℕ} [DecidableEq X] [DecidableEq K] :
    TranscriptCondition (Msg X ℓ) (Fin (ℓ + 1) → K) q where
  holds := fun t =>
    ∀ p p' : Fin q × Fin (ℓ + 1),
      (((t p.1).1).1.take p.2.val = (((t p'.1).1).1.take p'.2.val)) ↔
        ((t p.1).2 p.2 = (t p'.1).2 p'.2)
  dec := by
    classical
    infer_instance

/-! ### Generic helper: per-input condition-based bound -/

private theorem statDist_le_conditionFailure_single_for_inputs
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (S T : PDS X Y q) (A : TranscriptCondition X Y q)
    (inputs : Fin q → X)
    (h_eq : ∀ t : Transcript X Y q, A.holds t → S.transcriptDist inputs t = T.transcriptDist inputs t) :
    statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤ conditionFailureProb S A inputs := by
  -- This is `ConditionBased.statDist_le_conditionFailure_single` specialized to a fixed `inputs`.
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero :
      ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
          (S.transcriptDist inputs t - T.transcriptDist inputs t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_eq t ht, tsub_self]
  rw [h_zero, zero_add]
  calc
    ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
          (S.transcriptDist inputs t - T.transcriptDist inputs t)
        ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
          S.transcriptDist inputs t := by
          apply Finset.sum_le_sum
          intro t _; exact tsub_le_self
    _ ≤ conditionFailureProb S A inputs := by
          -- Rewrite failure prob as mass of bad transcripts.
          rw [← conditionFailureProb_eq_transcriptDist_filter (S := S) (A := A) (inputs := inputs)]

/-! ### Helper: explicit fiber form of `fTransform`

This is now available as `Dist.fTransform_apply_eq_sum` in `RandomSystems.Dist`. -/

/-! ### Helper: transcriptDist as a fiber sum, and mismatch implies 0 -/

-- Use the generic fiber-sum lemma `PDS.transcriptDist_apply_eq_sum` from `RandomSystems.PDS`.

private lemma transcriptDist_eq_zero_of_input_mismatch
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (S : PDS X Y q) (inputs : Fin q → X) (t : Transcript X Y q) (i : Fin q)
    (h : (t i).1 ≠ inputs i) :
    S.transcriptDist inputs t = 0 := by
  classical
  rw [PDS.transcriptDist_apply_eq_sum (S := S) (inputs := inputs) (t := t)]
  -- The fiber is empty: every transcript at `inputs` has input component `inputs i` at index `i`.
  have : (Finset.univ : Finset (DDS X Y q)).filter (fun s => DDS.transcript s inputs = t) = ∅ := by
    ext s
    constructor
    · intro hs
      have hs' : DDS.transcript s inputs = t := (Finset.mem_filter.mp hs).2
      have := congrArg (fun tr => (tr i).1) hs'
      have ht : inputs i = (t i).1 := by
        simpa [DDS.transcript] using this
      exact (h ht.symm).elim
    · intro hs
      simp at hs
  simp [this]

/-! ### Helper: pairwise collision count for uniform functions -/

private lemma fun_pair_collision_le
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (a₁ a₂ : A) (ha : a₁ ≠ a₂) :
    ((Finset.univ : Finset (A → B)).filter (fun f => f a₁ = f a₂)).card * Fintype.card B ≤
      Fintype.card (A → B) := by
  classical
  set C : Finset (A → B) := (Finset.univ : Finset (A → B)).filter (fun f => f a₁ = f a₂)
  -- Injection `C × B ↪ (A → B)` by updating coordinate `a₁`.
  let φ : (A → B) × B → (A → B) := fun p => Function.update p.1 a₁ p.2
  have h_maps : ∀ p ∈ C ×ˢ (Finset.univ : Finset B), φ p ∈ (Finset.univ : Finset (A → B)) := by
    intro _ _; exact Finset.mem_univ _
  have h_inj : Set.InjOn φ ↑(C ×ˢ (Finset.univ : Finset B)) := by
    intro ⟨f₁, b₁⟩ hp₁ ⟨f₂, b₂⟩ hp₂ hφ
    have hf₁ : f₁ a₁ = f₁ a₂ := by
      have : f₁ ∈ C := (Finset.mem_product.mp hp₁).1
      simpa [C] using (Finset.mem_filter.mp this).2
    have hf₂ : f₂ a₁ = f₂ a₂ := by
      have : f₂ ∈ C := (Finset.mem_product.mp hp₂).1
      simpa [C] using (Finset.mem_filter.mp this).2
    have hb : b₁ = b₂ := by
      have := congrArg (fun g : A → B => g a₁) hφ
      simpa [φ] using this
    have h_eq_other : ∀ a : A, a ≠ a₁ → f₁ a = f₂ a := by
      intro a ha'
      have := congrArg (fun g : A → B => g a) hφ
      simpa [φ, Function.update, ha'] using this
    have hf₁a₂ : f₁ a₂ = f₂ a₂ := h_eq_other a₂ (by exact ha.symm)
    have hf₁a₁ : f₁ a₁ = f₂ a₁ := by
      calc f₁ a₁ = f₁ a₂ := hf₁
      _ = f₂ a₂ := hf₁a₂
      _ = f₂ a₁ := hf₂.symm
    have hf : f₁ = f₂ := by
      funext a
      by_cases ha' : a = a₁
      · subst ha'; exact hf₁a₁
      · exact h_eq_other a ha'
    exact Prod.ext hf hb
  have h_card_le := Finset.card_le_card_of_injOn φ h_maps h_inj
  -- Rewrite the product cardinality.
  simpa [C, Finset.card_product, Finset.card_univ] using h_card_le

/-! ### What is actually true in this finitary RS model -/

/-
The following *tempting* claim is false in this finitary random-systems model:

  “Ideal cascade built from a uniform random transition `h : K×X→K` is exactly the same as
   a uniform random function `Msg X ℓ → K` on prefix-free inputs.”

Counterexample (smallest): take `K = X = Bool`, `ℓ = 2`, and query the prefix-free messages
`[false,false]` and `[true,false]`. In the cascade world the two tags collide with probability
`3/4`, while for a true random function the collision probability is `1/2`.

What *is* true (and matches the Boneh–Shoup “no additive term in |X|” intuition) is that the
statistical distance is bounded by the probability of an internal key collision, which is a
birthday term in `|K|`.
-/

theorem advantageOn_URFfunCascadeIdeal_URFfun_prefixFree_le_birthday
    {K X : Type*}
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)]
    [Fintype (Transcript (Msg X ℓ) K q)] [DecidableEq (Transcript (Msg X ℓ) K q)] :
    advantageOn (URFfunCascadeIdeal (K := K) (X := X) ℓ q)
      (Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q))
      (PrefixFree X ℓ q) ≤ birthdayBound (q * (ℓ + 1)) (Fintype.card K) := by
  classical
  -- Bound `statDist` pointwise on prefix-free input sequences, then take the supremum.
  refine advantageOn_le_of_pointwise
    (S := URFfunCascadeIdeal (K := K) (X := X) ℓ q)
    (T := Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q))
    (Good := PrefixFree X ℓ q)
    (ε := birthdayBound (q * (ℓ + 1)) (Fintype.card K)) ?_
  intro inputs _hPF

  -- Trace systems.
  let STrace : PDS (Msg X ℓ) (Fin (ℓ + 1) → K) q :=
    URFfunCascadeIdealTrace (K := K) (X := X) (ℓ := ℓ) (q := q)
  let TTrace : PDS (Msg X ℓ) (Fin (ℓ + 1) → K) q :=
    URFfunPrefixTraceIdeal (K := K) (X := X) (ℓ := ℓ) (q := q)

  -- Step 1: Data processing from trace transcripts to tag transcripts.
  have h_proj_S :
      (URFfunCascadeIdeal (K := K) (X := X) ℓ q).transcriptDist inputs =
        Dist.fTransform (traceTranscriptToTagTranscript (K := K) (X := X) (ℓ := ℓ) (q := q))
          (STrace.transcriptDist inputs) := by
    classical
    ext t
    -- Collapse both sides into a single pushforward from the same base distribution on `(k0,h)`,
    -- then use that projecting the trace transcript picks out the tag transcript.
    have hmaps :
        (fun p : K × (K × X → K) =>
            DDS.transcript
              (DDS.ofFunq (q := q)
                (fun msg : Msg X ℓ => cascadeEval (K := K) (X := X) p.2 p.1 msg.1))
              inputs)
          =
        (fun p : K × (K × X → K) =>
            traceTranscriptToTagTranscript (K := K) (X := X) (ℓ := ℓ) (q := q)
              (DDS.transcript
                (DDS.ofFunq (q := q)
                  (fun msg : Msg X ℓ => cascadeTrace (K := K) (X := X) (ℓ := ℓ) p.2 p.1 msg))
                inputs)) := by
      funext p
      funext i
      simp [DDS.transcript, DDS.ofFunq, traceTranscriptToTagTranscript, cascadeTrace, tagIndex,
        cascadeEval]
    have hmaps' :
        ((fun s : DDS (Msg X ℓ) K q => s.transcript inputs) ∘
              fun p : K × (K × X → K) =>
                DDS.ofFunq (q := q) (fun msg : Msg X ℓ => cascadeEval (K := K) (X := X) p.2 p.1 msg.1))
          =
        (traceTranscriptToTagTranscript (K := K) (X := X) (ℓ := ℓ) (q := q) ∘
              (fun s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q => s.transcript inputs) ∘
              fun p : K × (K × X → K) =>
                DDS.ofFunq (q := q) (fun msg : Msg X ℓ => cascadeTrace (K := K) (X := X) (ℓ := ℓ) p.2 p.1 msg)) := by
      funext p
      -- Expand the compositions and use `hmaps` pointwise.
      simpa [Function.comp] using congrArg (fun f => f p) hmaps
    -- Unfold transcript distributions and regroup pushforwards.
    simp [PDS.transcriptDist, URFfunCascadeIdeal, URFfunCascadeOf, STrace, URFfunCascadeIdealTrace,
      Dist.fTransform_comp, hmaps']

  have h_proj_T :
      (Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q)).transcriptDist inputs =
        Dist.fTransform (traceTranscriptToTagTranscript (K := K) (X := X) (ℓ := ℓ) (q := q))
          (TTrace.transcriptDist inputs) := by
    classical
    ext t
    -- Reduce both sides to pushforwards from a uniform distribution over `(k0,f)`, and use that
    -- tags only depend on `f` (since messages are non-empty, `tagIndex msg ≠ 0`).
    let A : (Msg X ℓ → K) → Transcript (Msg X ℓ) K q :=
      fun f => DDS.transcript (DDS.ofFunq (q := q) f) inputs
    have hmaps :
        (fun p : K × (Msg X ℓ → K) =>
            traceTranscriptToTagTranscript (K := K) (X := X) (ℓ := ℓ) (q := q)
              (DDS.transcript
                (DDS.ofFunq (q := q) (fun msg : Msg X ℓ =>
                  fun j =>
                    if h : j = 0 then
                      p.1
                    else
                      p.2 (takeMsg (ℓ := ℓ) msg j (by
                        intro hj0
                        apply h
                        apply Fin.ext
                        simpa using hj0))))
                inputs))
          =
        (fun p : K × (Msg X ℓ → K) => A p.2) := by
      funext p
      funext i
      have hlenpos : 0 < (inputs i).1.length :=
        List.length_pos_of_ne_nil (Msg.ne_nil (inputs i))
      have hj0 : (tagIndex (inputs i) : Fin (ℓ + 1)).val ≠ 0 := by
        simpa [tagIndex] using (Nat.ne_of_gt hlenpos)
      have hjne : (tagIndex (inputs i) : Fin (ℓ + 1)) ≠ 0 := by
        intro h
        apply hj0
        simpa using congrArg Fin.val h
      have ht :
          ∀ hj : (tagIndex (inputs i) : Fin (ℓ + 1)).val ≠ 0,
            takeMsg (ℓ := ℓ) (inputs i) (tagIndex (inputs i)) hj = inputs i := by
        intro hj
        apply Subtype.ext
        simp [takeMsg, tagIndex, List.take_length]
      simp [A, traceTranscriptToTagTranscript, DDS.transcript, DDS.ofFunq, hjne, ht]
    -- Unfold transcript distributions and align both sides on `uniform (K × (Msg X ℓ → K))`.
    simp [PDS.transcriptDist, Instances.URFfun, Instances.URFfunOf, TTrace, URFfunPrefixTraceIdeal,
      Dist.fTransform_comp]
    -- Convert `prod (uniform K) (uniform F)` to `uniform (K×F)` and marginalize out `k0`.
    rw [Dist.prod_uniform (A := K) (B := (Msg X ℓ → K))]
    have hunif :
        Dist.uniform (Msg X ℓ → K) =
          Dist.fTransform Prod.snd (Dist.uniform (K × (Msg X ℓ → K))) := by
      simpa using
        (Dist.fTransform_snd_uniform (A' := K) (B' := (Msg X ℓ → K))).symm
    rw [hunif]
    -- Functoriality of pushforwards.
    rw [Dist.fTransform_comp]
    -- Rewrite the RHS map using `hmaps`, then both sides are definitional equal.
    simpa [Function.comp, A] using
      (congrArg (fun f => (Dist.fTransform f (Dist.uniform (K × (Msg X ℓ → K)))) t) hmaps).symm

  have h_data :
      statDist ((URFfunCascadeIdeal (K := K) (X := X) ℓ q).transcriptDist inputs)
          ((Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q)).transcriptDist inputs)
        ≤ statDist (STrace.transcriptDist inputs) (TTrace.transcriptDist inputs) := by
    simpa [h_proj_S, h_proj_T] using
      (statDist_fTransform_le (STrace.transcriptDist inputs) (TTrace.transcriptDist inputs)
        (traceTranscriptToTagTranscript (K := K) (X := X) (ℓ := ℓ) (q := q)))

  -- Step 2: On good trace transcripts, the two trace systems agree.
  have h_trace_eq_on_good :
      ∀ t : Transcript (Msg X ℓ) (Fin (ℓ + 1) → K) q,
        (goodPrefixTrace (K := K) (X := X) (ℓ := ℓ) (q := q)).holds t →
          STrace.transcriptDist inputs t = TTrace.transcriptDist inputs t := by
    classical
    intro t ht_good
    -- If input components mismatch, both transcript masses are 0.
    by_cases h_inputs : ∀ i : Fin q, (t i).1 = inputs i
    · by_cases hq0 : q = 0
      · subst hq0
        -- No queries: `Fin 0` is empty, so every transcript is equal.
        have h_all :
            ∀ s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0, DDS.transcript s inputs = t := by
          intro s
          funext i
          exact Fin.elim0 i

        have hST :
            STrace.transcriptDist inputs t =
              ∑ s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0, STrace.dist s := by
          rw [PDS.transcriptDist_apply_eq_sum (S := STrace) (inputs := inputs) (t := t)]
          have :
              (Finset.univ : Finset (DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0)).filter
                  (fun s => DDS.transcript s inputs = t) =
                (Finset.univ : Finset (DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0)) := by
            ext s
            constructor
            · intro hs; exact (Finset.mem_filter.mp hs).1
            · intro hs; exact Finset.mem_filter.mpr ⟨hs, h_all s⟩
          simp [this]

        have hTT :
            TTrace.transcriptDist inputs t =
              ∑ s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0, TTrace.dist s := by
          rw [PDS.transcriptDist_apply_eq_sum (S := TTrace) (inputs := inputs) (t := t)]
          have :
              (Finset.univ : Finset (DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0)).filter
                  (fun s => DDS.transcript s inputs = t) =
                (Finset.univ : Finset (DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0)) := by
            ext s
            constructor
            · intro hs; exact (Finset.mem_filter.mp hs).1
            · intro hs; exact Finset.mem_filter.mpr ⟨hs, h_all s⟩
          simp [this]

        have hSTw : STrace.dist.weight = (1 : NNReal) := by
          dsimp [STrace, URFfunCascadeIdealTrace]
          rw [Dist.weight_fTransform]
          rw [Dist.weight_prod]
          simp [Dist.weight, Dist.uniform]
        have hTTw : TTrace.dist.weight = (1 : NNReal) := by
          dsimp [TTrace, URFfunPrefixTraceIdeal]
          rw [Dist.weight_fTransform]
          rw [Dist.weight_prod]
          simp [Dist.weight, Dist.uniform]
        have hSTsum : (∑ s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0, STrace.dist s) = 1 := by
          simpa [Dist.weight] using hSTw
        have hTTsum : (∑ s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) 0, TTrace.dist s) = 1 := by
          simpa [Dist.weight] using hTTw
        calc
          STrace.transcriptDist inputs t = ∑ s, STrace.dist s := hST
          _ = 1 := hSTsum
          _ = ∑ s, TTrace.dist s := hTTsum.symm
          _ = TTrace.transcriptDist inputs t := hTT.symm
      ·
        have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        let i0 : Fin q := ⟨0, hqpos⟩
        haveI : Nonempty (Msg X ℓ) := ⟨inputs i0⟩
        haveI : Nonempty X := ⟨(inputs i0).1.getLast (Msg.ne_nil (inputs i0))⟩

        -- Output matrix of the transcript.
        let ys : Fin q → Fin (ℓ + 1) → K := fun i => (t i).2

        -- Factor transcript distribution through output vectors.
        let outputVec :
            DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q → Fin q → Fin (ℓ + 1) → K :=
          fun s i => (DDS.transcript s inputs i).2
        let transcriptEmbed :
            (Fin q → Fin (ℓ + 1) → K) → Transcript (Msg X ℓ) (Fin (ℓ + 1) → K) q :=
          fun ys i => (inputs i, ys i)
        have ht_embed : t = transcriptEmbed ys := by
          funext i
          exact Prod.ext (h_inputs i) rfl
        have h_embed_inj : Function.Injective transcriptEmbed := by
          intro ys₁ ys₂ h
          funext i
          have := congrArg Prod.snd (congrArg (fun tr => tr i) h)
          simpa [transcriptEmbed] using this
        have h_factors :
            (fun s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q => DDS.transcript s inputs) =
              transcriptEmbed ∘ outputVec := by
          funext s
          funext i
          simp [outputVec, transcriptEmbed, DDS.transcript]

        have h_mass_S :
            STrace.transcriptDist inputs t =
              (Dist.fTransform outputVec STrace.dist) ys := by
          simp only [PDS.transcriptDist]
          rw [h_factors]
          rw [← Dist.fTransform_comp]
          rw [ht_embed]
          simpa using
            (fTransform_injective_apply (X := Dist.fTransform outputVec STrace.dist)
              (f := transcriptEmbed) (hf := h_embed_inj) ys)

        have h_mass_T :
            TTrace.transcriptDist inputs t =
              (Dist.fTransform outputVec TTrace.dist) ys := by
          simp only [PDS.transcriptDist]
          rw [h_factors]
          rw [← Dist.fTransform_comp]
          rw [ht_embed]
          simpa using
            (fTransform_injective_apply (X := Dist.fTransform outputVec TTrace.dist)
              (f := transcriptEmbed) (hf := h_embed_inj) ys)

        -- Prefix positions and the good-trace equivalence.
        let Pos : Type := Fin q × Fin (ℓ + 1)
        let pref : Pos → List X := fun p => (inputs p.1).1.take p.2.val
        let lab : Pos → K := fun p => ys p.1 p.2
        have h_pref_iff_lab : ∀ u v : Pos, pref u = pref v ↔ lab u = lab v := by
          intro u v
          simpa [goodPrefixTrace, pref, lab, ys, h_inputs] using (ht_good u v)

        let root : K := ys i0 0
        have h_root : ∀ i : Fin q, ys i 0 = root := by
          intro i
          have : pref (i, (0 : Fin (ℓ + 1))) = pref (i0, (0 : Fin (ℓ + 1))) := by
            simp [pref]
          exact (h_pref_iff_lab (i, 0) (i0, 0)).1 this

        -- Prefix-list finset and its induced label function `L`.
        let P : Finset (List X) := (Finset.univ : Finset Pos).image pref
        have h_rep : ∀ l : ↥P, ∃ p : Pos, pref p = l.1 := by
          intro l
          rcases Finset.mem_image.mp l.2 with ⟨p, _, hpref⟩
          exact ⟨p, hpref⟩
        let rep : ↥P → Pos := fun l => Classical.choose (h_rep l)
        have rep_spec : ∀ l : ↥P, pref (rep l) = l.1 := by
          intro l
          exact Classical.choose_spec (h_rep l)
        let L : ↥P → K := fun l => lab (rep l)

        have h_L_at : ∀ p : Pos,
            L ⟨pref p, Finset.mem_image_of_mem pref (Finset.mem_univ p)⟩ = lab p := by
          intro p
          let lp : ↥P := ⟨pref p, Finset.mem_image_of_mem pref (Finset.mem_univ p)⟩
          have hpref : pref (rep lp) = pref p := by
            simpa [lp] using rep_spec lp
          have hlab : lab (rep lp) = lab p := (h_pref_iff_lab (rep lp) p).1 hpref
          simpa [L, lp] using hlab

        have h_L_inj : Function.Injective L := by
          intro l₁ l₂ h
          apply Subtype.ext
          have hlab : lab (rep l₁) = lab (rep l₂) := by
            simpa [L] using h
          have hpref : pref (rep l₁) = pref (rep l₂) := (h_pref_iff_lab (rep l₁) (rep l₂)).2 hlab
          simpa [rep_spec l₁, rep_spec l₂] using hpref

        -- Non-root prefix messages (distinct) and their enumeration.
        let PosNR : Type := { p : Pos // p.2.val ≠ 0 }
        let prefMsg : PosNR → Msg X ℓ := fun p => takeMsg (ℓ := ℓ) (inputs p.1.1) p.1.2 p.2
        let S : Finset (Msg X ℓ) := (Finset.univ : Finset PosNR).image prefMsg
        let n : ℕ := Fintype.card (↥S)
        let eS : (↥S) ≃ Fin n := Fintype.equivFin (↥S)
        let decS : Fin n → ↥S := eS.symm
        let nonces : Fin n → Msg X ℓ := fun k => (decS k).1

        have h_inj_nonces : Function.Injective nonces := by
          intro a b hab
          have hdec : decS a = decS b := by
            apply Subtype.ext
            simpa [nonces] using hab
          have : a = b := by
            have := congrArg eS hdec
            simpa [decS] using this
          exact this

        have memP_of_nonce : ∀ m : ↥S, m.1.1 ∈ P := by
          intro m
          rcases Finset.mem_image.mp m.2 with ⟨p, _, hpref⟩
          have hm_list : pref p.1 = m.1.1 := by
            have := congrArg Subtype.val hpref
            simpa [prefMsg, pref, takeMsg] using this
          have : pref p.1 ∈ P := Finset.mem_image_of_mem pref (Finset.mem_univ p.1)
          simpa [hm_list] using this

        have memP_dropLast_of_nonce : ∀ m : ↥S, m.1.1.dropLast ∈ P := by
          intro m
          rcases Finset.mem_image.mp m.2 with ⟨p, _, hpref⟩
          have hm_list : pref p.1 = m.1.1 := by
            have := congrArg Subtype.val hpref
            simpa [prefMsg, pref, takeMsg] using this
          let l : List X := m.1.1
          have hl_len : l.length ≤ ℓ := by
            simpa [l] using Msg.length_le m.1
          have hl_lt : l.length - 1 < ℓ + 1 := by
            have : l.length - 1 ≤ ℓ := le_trans (Nat.sub_le _ _) hl_len
            exact Nat.lt_succ_of_le this
          let j' : Fin (ℓ + 1) := ⟨l.length - 1, hl_lt⟩
          have hj'_mem : pref (p.1.1, j') ∈ P :=
            Finset.mem_image_of_mem pref (Finset.mem_univ (p.1.1, j'))
          have hj'_eq : pref (p.1.1, j') = l.dropLast := by
            have hle : l.length - 1 ≤ p.1.2.val := by
              have : l.length ≤ p.1.2.val := by
                have : (pref p.1).length ≤ p.1.2.val := by
                  simp [pref]
                simpa [l, hm_list] using this
              exact le_trans (Nat.sub_le _ _) this
            have h_drop : l.dropLast = (inputs p.1.1).1.take (l.length - 1) := by
              calc
                l.dropLast = l.take (l.length - 1) := by
                  simp [List.dropLast_eq_take]
                _ = ((inputs p.1.1).1.take p.1.2.val).take (l.length - 1) := by
                  simp [l, hm_list, pref]
                _ = (inputs p.1.1).1.take (min (l.length - 1) p.1.2.val) := by
                  simp [List.take_take]
                _ = (inputs p.1.1).1.take (l.length - 1) := by
                  simp [Nat.min_eq_left hle]
            have h_drop' : (inputs p.1.1).1.take (l.length - 1) = l.dropLast := h_drop.symm
            simpa [pref, j', l] using h_drop'
          simpa [hj'_eq, l] using hj'_mem

        let nonceList : ↥S → ↥P := fun m => ⟨m.1.1, memP_of_nonce m⟩
        let parentList : ↥S → ↥P := fun m => ⟨m.1.1.dropLast, memP_dropLast_of_nonce m⟩
        let outs : Fin n → K := fun k => L (nonceList (decS k))
        let transNonces : Fin n → K × X := fun k =>
          let m := decS k
          (L (parentList m), m.1.1.getLast (Msg.ne_nil m.1))

        have h_inj_trans : Function.Injective transNonces := by
          intro a b hab
          have hfst : L (parentList (decS a)) = L (parentList (decS b)) := by
            simpa [transNonces] using congrArg Prod.fst hab
          have hsnd :
              (decS a).1.1.getLast (Msg.ne_nil (decS a).1) =
                (decS b).1.1.getLast (Msg.ne_nil (decS b).1) := by
            simpa [transNonces] using congrArg Prod.snd hab
          have h_par : parentList (decS a) = parentList (decS b) := h_L_inj hfst
          have h_drop : (decS a).1.1.dropLast = (decS b).1.1.dropLast := by
            simpa [parentList] using congrArg Subtype.val h_par
          have h_lists : (decS a).1.1 = (decS b).1.1 := by
            have ha :
                (decS a).1.1.dropLast ++ [(decS a).1.1.getLast (Msg.ne_nil (decS a).1)] =
                  (decS a).1.1 :=
              List.dropLast_append_getLast (l := (decS a).1.1) (Msg.ne_nil (decS a).1)
            have hb :
                (decS b).1.1.dropLast ++ [(decS b).1.1.getLast (Msg.ne_nil (decS b).1)] =
                  (decS b).1.1 :=
              List.dropLast_append_getLast (l := (decS b).1.1) (Msg.ne_nil (decS b).1)
            calc
              (decS a).1.1 =
                  (decS a).1.1.dropLast ++ [(decS a).1.1.getLast (Msg.ne_nil (decS a).1)] := by
                    simp [ha]
              _ = (decS b).1.1.dropLast ++ [(decS b).1.1.getLast (Msg.ne_nil (decS b).1)] := by
                    simp [h_drop, hsnd]
              _ = (decS b).1.1 := by
                    simp [hb]
          have h_msg : (decS a).1 = (decS b).1 := by
            apply Subtype.ext
            exact h_lists
          have h_dec : decS a = decS b := by
            apply Subtype.ext
            exact h_msg
          have := congrArg eS h_dec
          simpa [decS] using this

        -- Step 2 conclusion: the trace transcript masses coincide on good transcripts.
        have h_out :
            (Dist.fTransform outputVec STrace.dist) ys =
              (Dist.fTransform outputVec TTrace.dist) ys := by
          classical
          -- Base distributions.
          let baseT : Dist (K × (Msg X ℓ → K)) :=
            Dist.prod (Dist.uniform K) (Dist.uniform (Msg X ℓ → K))
          let baseS : Dist (K × (K × X → K)) :=
            Dist.prod (Dist.uniform K) (Dist.uniform (K × X → K))

          -- Output-matrix maps from base samples.
          let gT : K × (Msg X ℓ → K) → Fin q → Fin (ℓ + 1) → K :=
            fun p i j =>
              if hj : j.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) (inputs i) j hj)
          let gS : K × (K × X → K) → Fin q → Fin (ℓ + 1) → K :=
            fun p i j => cascadeTrace (K := K) (X := X) (ℓ := ℓ) p.2 p.1 (inputs i) j

          -- Evaluation maps on the underlying random functions.
          let evalPref : (Msg X ℓ → K) → Fin n → K := fun f k => f (nonces k)
          let evalTrans : (K × X → K) → Fin n → K := fun h k => h (transNonces k)

          have h_L_nil :
              ∀ hnil : ([] : List X) ∈ P, L ⟨[], hnil⟩ = root := by
            intro hnil
            -- Compare with the canonical root position `(i0,0)`.
            have h0 := h_L_at (i0, (0 : Fin (ℓ + 1)))
            have : L ⟨[], hnil⟩ =
                L ⟨pref (i0, (0 : Fin (ℓ + 1))),
                  Finset.mem_image_of_mem pref (Finset.mem_univ (i0, (0 : Fin (ℓ + 1))))⟩ := by
              apply congrArg L
              apply Subtype.ext
              simp [pref]
            simpa [root, lab, ys, pref] using this.trans h0

          -- `gT p = ys` iff the base sample fixes the root and agrees with `outs` on `nonces`.
          have h_gT_iff :
              ∀ p : K × (Msg X ℓ → K), gT p = ys ↔ p.1 = root ∧ evalPref p.2 = outs := by
            intro p
            constructor
            · intro hg
              have hk0 : p.1 = root := by
                have := congrArg (fun M => M i0 0) hg
                simpa [gT, root] using this
              have hf : evalPref p.2 = outs := by
                funext k
                -- use the representative position for the nonce prefix list
                let m : ↥S := decS k
                let lp : ↥P := nonceList m
                have hposnz : (rep lp).2.val ≠ 0 := by
                  intro h0
                  have : lp.1 = ([] : List X) := by
                    have hr : pref (rep lp) = lp.1 := rep_spec lp
                    have : pref (rep lp) = ([] : List X) := by
                      have : (rep lp).2 = 0 := by
                        apply Fin.ext
                        simpa using h0
                      simp [pref, this]
                    simpa [hr] using this
                  exact (Msg.ne_nil m.1) (by simpa [lp, nonces, decS] using this)
                have h_at := congrArg (fun M => M (rep lp).1 (rep lp).2) hg
                have hnonce : takeMsg (ℓ := ℓ) (inputs (rep lp).1) (rep lp).2 (by
                      intro h0; exact hposnz (by simpa using h0)) = nonces k := by
                  apply Subtype.ext
                  -- Keep `decS` opaque here so the RHS is literally `m`.
                  simp [nonces, lp, nonceList, pref, rep_spec lp, takeMsg, m]
                have : p.2 (nonces k) = outs k := by
                  -- unfold `gT` at a non-root index and rewrite with `hnonce`
                  have : p.2
                        (takeMsg (ℓ := ℓ) (inputs (rep lp).1) (rep lp).2 (by
                          intro h0; exact hposnz (by simpa using h0))) =
                        ys (rep lp).1 (rep lp).2 := by
                    have hrep0 : ¬(↑(rep lp).2 = 0) := by
                      intro h0
                      exact hposnz (by simpa using h0)
                    simpa [gT, hrep0] using h_at
                  have hout : ys (rep lp).1 (rep lp).2 = outs k := by
                    have houts : outs k = L lp := by
                      dsimp [outs, lp, m]
                    have hL : L lp = ys (rep lp).1 (rep lp).2 := by
                      simp [L, lab]
                    exact hL.symm.trans houts.symm
                  simpa [hnonce, hout] using this
                simpa [evalPref] using this
              exact ⟨hk0, hf⟩
            · rintro ⟨hk0, hf⟩
              funext i
              funext j
              by_cases hj0 : j.val = 0
              · have hrooti : ys i 0 = root := by
                  simpa [root] using h_root i
                have hj0' : j = 0 := by
                  apply Fin.ext
                  simpa using hj0
                subst hj0'
                simp [gT, hk0, hrooti, root]
              · have hj : j.val ≠ 0 := hj0
                let pos : PosNR := ⟨(i, j), hj⟩
                let mS : ↥S :=
                  ⟨prefMsg pos, Finset.mem_image_of_mem prefMsg (Finset.mem_univ pos)⟩
                let k : Fin n := eS mS
                have hk : nonces k = prefMsg pos := by
                  simp [nonces, decS, k, mS]
                have hf' : p.2 (prefMsg pos) = outs k := by
                  have := congrArg (fun v => v k) hf
                  simpa [evalPref, hk] using this
                have hnonce :
                    nonceList mS =
                      ⟨pref (i, j), Finset.mem_image_of_mem pref (Finset.mem_univ (i, j))⟩ := by
                  apply Subtype.ext
                  simp [nonceList, mS, prefMsg, pref, takeMsg, pos]
                have hout : outs k = ys i j := by
                  have := h_L_at (i, j)
                  -- Rewrite `outs k` to the label attached to the `(i,j)`-prefix list, then use `h_L_at`.
                  have hdec : decS k = mS := by
                    simp [decS, k, mS]
                  have : nonceList (decS k) =
                      ⟨pref (i, j), Finset.mem_image_of_mem pref (Finset.mem_univ (i, j))⟩ := by
                    simpa [hdec] using hnonce
                  -- `outs k = L (nonceList (decS k))`
                  -- and `L ⟨pref (i,j), _⟩ = ys i j` by `h_L_at`.
                  have hL : L ⟨pref (i, j), Finset.mem_image_of_mem pref (Finset.mem_univ (i, j))⟩ = ys i j := by
                    simpa [lab] using (h_L_at (i, j))
                  simpa [outs, this] using hL
                have htake :
                    takeMsg (ℓ := ℓ) (inputs i) j (by intro h0; exact hj (by simpa using h0)) =
                      takeMsg (ℓ := ℓ) (inputs i) j hj := by
                  apply Subtype.ext
                  rfl
                have : p.2 (takeMsg (ℓ := ℓ) (inputs i) j hj) = ys i j := by
                  calc
                    p.2 (takeMsg (ℓ := ℓ) (inputs i) j hj)
                        = p.2 (prefMsg pos) := by
                            simp [prefMsg, pos, htake]
                    _ = outs k := hf'
                    _ = ys i j := hout
                have hj' : j.val ≠ 0 := hj
                have htake' :
                    takeMsg (ℓ := ℓ) (inputs i) j hj' = takeMsg (ℓ := ℓ) (inputs i) j hj := by
                  apply Subtype.ext
                  rfl
                have : p.2 (takeMsg (ℓ := ℓ) (inputs i) j hj') = ys i j := by
                  simpa [htake'] using this
                -- unfold `gT` on a non-root index
                have hjNat : ¬(↑j = 0) := by
                  intro h0
                  exact hj0 (by simpa using h0)
                -- `hjNat` forces the else-branch of `gT`.
                simp [gT, hjNat, this]

          -- `gS p = ys` iff the base sample fixes the root and agrees with `outs` on `transNonces`.
          have h_gS_iff :
              ∀ p : K × (K × X → K), gS p = ys ↔ p.1 = root ∧ evalTrans p.2 = outs := by
            intro p
            constructor
            · intro hg
              have hk0 : p.1 = root := by
                have := congrArg (fun M => M i0 0) hg
                simpa [gS, cascadeTrace, cascadeEval, root] using this
              -- On `hg`, cascadeEval matches `L` on every prefix list in `P`.
              have h_evalP : ∀ lP : ↥P, cascadeEval (K := K) (X := X) p.2 p.1 lP.1 = L lP := by
                intro lP
                have := congrArg (fun M => M (rep lP).1 (rep lP).2) hg
                simpa [gS, cascadeTrace, pref, rep_spec lP, lab, L] using this
              have hh : evalTrans p.2 = outs := by
                funext k
                let m : ↥S := decS k
                -- cascade recurrence for the nonce list
                have hnil : (nonceList m).1 ≠ ([] : List X) := Msg.ne_nil m.1
                have hdl : (nonceList m).1.dropLast ++ [(nonceList m).1.getLast hnil] = (nonceList m).1 :=
                  List.dropLast_append_getLast (l := (nonceList m).1) hnil
                have hrec :
                    cascadeEval (K := K) (X := X) p.2 p.1 (nonceList m).1 =
                      p.2 (cascadeEval (K := K) (X := X) p.2 p.1 (parentList m).1,
                        (nonceList m).1.getLast (Msg.ne_nil m.1)) := by
                  calc
                    cascadeEval (K := K) (X := X) p.2 p.1 (nonceList m).1
                        = cascadeEval (K := K) (X := X) p.2 p.1 ((nonceList m).1.dropLast ++ [(nonceList m).1.getLast hnil]) := by
                            simp [hdl]
                    _ = p.2 (cascadeEval (K := K) (X := X) p.2 p.1 ((nonceList m).1.dropLast),
                          (nonceList m).1.getLast hnil) := by
                            simp [cascadeEval]
                    _ = p.2 (cascadeEval (K := K) (X := X) p.2 p.1 (parentList m).1,
                          (nonceList m).1.getLast (Msg.ne_nil m.1)) := by
                            simp [parentList, nonceList]
                have : p.2 (transNonces k) = outs k := by
                  -- rewrite with `h_evalP` and `hrec`
                  have hchild : cascadeEval (K := K) (X := X) p.2 p.1 (nonceList m).1 = outs k := by
                    simpa [outs, nonceList, nonces, decS] using congrArg (fun x => x) (h_evalP (nonceList m))
                  have hparent : cascadeEval (K := K) (X := X) p.2 p.1 (parentList m).1 = L (parentList m) := h_evalP (parentList m)
                  have : p.2 (L (parentList m), (nonceList m).1.getLast (Msg.ne_nil m.1)) = outs k := by
                    -- from the recurrence
                    simpa [hrec, hparent] using congrArg (fun z => z) hchild
                  simpa [evalTrans, transNonces, outs, nonceList, parentList] using this
                simpa [evalTrans] using this
              exact ⟨hk0, hh⟩
            · rintro ⟨hk0, hh⟩
              -- Strong induction on prefix length: cascadeEval matches `L` on every prefix list in `P`.
              have h_evalP :
                  ∀ lP : ↥P, cascadeEval (K := K) (X := X) p.2 root lP.1 = L lP := by
                classical
                intro lP
                refine Nat.strongRecOn (motive := fun m =>
                  ∀ lP : ↥P, lP.1.length = m →
                    cascadeEval (K := K) (X := X) p.2 root lP.1 = L lP) lP.1.length ?_ lP rfl
                intro m ih lP hm
                by_cases hnil : lP.1 = ([] : List X)
                ·
                  have hnilP : ([] : List X) ∈ P := by
                    simpa [hnil] using lP.2
                  have hL' : L ⟨[], hnilP⟩ = root := h_L_nil hnilP
                  have hlP : lP = ⟨[], hnilP⟩ := by
                    apply Subtype.ext
                    simp [hnil]
                  have hL : L lP = root := by simpa [hlP] using hL'
                  simpa [hnil, cascadeEval] using hL.symm
                · -- use the corresponding nonce constraint at this list
                  have hposnz : (rep lP).2.val ≠ 0 := by
                    intro h0
                    have : lP.1 = ([] : List X) := by
                      have hr : pref (rep lP) = lP.1 := rep_spec lP
                      have : pref (rep lP) = ([] : List X) := by
                        have : (rep lP).2 = 0 := by
                          apply Fin.ext
                          simpa using h0
                        simp [pref, this]
                      simpa [hr] using this
                    exact (hnil this).elim
                  let pos : PosNR := ⟨rep lP, hposnz⟩
                  let mS : ↥S :=
                    ⟨prefMsg pos, Finset.mem_image_of_mem prefMsg (Finset.mem_univ pos)⟩
                  let k : Fin n := eS mS
                  have hk : nonces k = prefMsg pos := by
                    simp [nonces, decS, k, mS]
                  have hnonce : nonceList mS = lP := by
                    apply Subtype.ext
                    simpa [nonceList, mS, prefMsg, takeMsg, pos, pref] using rep_spec lP
                  -- Parent prefix list.
                  let parentP : ↥P := parentList mS
                  have hlen_lt : parentP.1.length < m := by
                    have hm0 : 0 < m := by
                      have : 0 < lP.1.length := List.length_pos_of_ne_nil hnil
                      simpa [hm] using this
                    have hm_list : mS.1.1 = lP.1 := by
                      simpa [nonceList] using congrArg Subtype.val hnonce
                    have hlen : parentP.1.length = m - 1 := by
                      calc
                        parentP.1.length = (mS.1.1.dropLast).length := by
                          simp [parentP, parentList]
                        _ = mS.1.1.length - 1 := by
                          simp
                        _ = lP.1.length - 1 := by
                          simp [hm_list]
                        _ = m - 1 := by
                          simp [hm]
                    simpa [hlen] using (Nat.sub_lt hm0 zero_lt_one)
                  have hIH : cascadeEval (K := K) (X := X) p.2 root parentP.1 = L parentP := by
                    exact ih parentP.1.length hlen_lt parentP rfl
                  -- Edge constraint from `hh` at index `k`.
                  have h_edge : p.2 (transNonces k) = outs k := congrArg (fun v => v k) hh
                  -- cascadeEval recurrence
                  have hnil' : lP.1 ≠ ([] : List X) := hnil
                  have hdl : lP.1.dropLast ++ [lP.1.getLast hnil'] = lP.1 :=
                    List.dropLast_append_getLast (l := lP.1) hnil'
                  have hrec :
                      cascadeEval (K := K) (X := X) p.2 root lP.1 =
                        p.2 (cascadeEval (K := K) (X := X) p.2 root lP.1.dropLast, lP.1.getLast hnil') := by
                    calc
                      cascadeEval (K := K) (X := X) p.2 root lP.1
                          = cascadeEval (K := K) (X := X) p.2 root (lP.1.dropLast ++ [lP.1.getLast hnil']) := by
                              simp [hdl]
                      _ = p.2 (cascadeEval (K := K) (X := X) p.2 root lP.1.dropLast, lP.1.getLast hnil') := by
                              simp [cascadeEval]
                  have hout : outs k = L lP := by
                    simp [outs, decS, k, mS, hnonce]
                  have htrans :
                      transNonces k = (L parentP, lP.1.getLast hnil') := by
                    have hm_list : mS.1.1 = lP.1 := by
                      simpa [nonceList] using congrArg Subtype.val hnonce
                    have hlast :
                        mS.1.1.getLast (Msg.ne_nil mS.1) = lP.1.getLast hnil' :=
                      List.getLast_congr (Msg.ne_nil mS.1) hnil' hm_list
                    simp [transNonces, k, mS, parentP, decS, hlast]
                  -- Finish.
                  have : cascadeEval (K := K) (X := X) p.2 root lP.1 = L lP := by
                    -- rewrite `h_edge` into the recurrence form
                    have h_edge' : p.2 (L parentP, lP.1.getLast hnil') = L lP := by
                      simpa [hout, htrans] using h_edge
                    have hparent' : cascadeEval (K := K) (X := X) p.2 root lP.1.dropLast = L parentP := by
                      -- `lP.1.dropLast = parentP.1`
                      have hm_list : mS.1.1 = lP.1 := by
                        simpa [nonceList] using congrArg Subtype.val hnonce
                      simpa [parentP, parentList, hm_list] using hIH
                    simpa [hrec, hparent'] using h_edge'
                  exact this
              -- Now show `gS (p.1,p.2) = ys` pointwise.
              funext i
              funext j
              have hlP : pref (i, j) ∈ P := Finset.mem_image_of_mem pref (Finset.mem_univ (i, j))
              have := h_evalP ⟨pref (i, j), hlP⟩
              have hk0' : p.1 = root := hk0
              have hL : L ⟨pref (i, j), hlP⟩ = ys i j := by
                simpa [lab] using (h_L_at (i, j))
              have : cascadeEval (K := K) (X := X) p.2 root (pref (i, j)) = ys i j := this.trans hL
              simpa [gS, cascadeTrace, hk0', pref] using this

          -- Collapse `outputVec` pushforwards to the base distributions.
          have h_T_push :
              (Dist.fTransform outputVec TTrace.dist) ys =
                (Dist.fTransform gT baseT) ys := by
            let mkDDS : K × (Msg X ℓ → K) → DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q :=
              fun p =>
                DDS.ofFunq (q := q) (fun msg =>
                  fun j =>
                    if hj : j.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) msg j hj))
            have h_comp : outputVec ∘ mkDDS = gT := by
              funext p i j
              simp [outputVec, mkDDS, gT, DDS.transcript, DDS.ofFunq]
            calc
              (Dist.fTransform outputVec TTrace.dist) ys =
                  (Dist.fTransform (outputVec ∘ mkDDS) baseT) ys := by
                simp [TTrace, URFfunPrefixTraceIdeal, baseT, mkDDS, Dist.fTransform_comp]
              _ = (Dist.fTransform gT baseT) ys := by
                  simp [h_comp]

          have h_S_push :
              (Dist.fTransform outputVec STrace.dist) ys =
                (Dist.fTransform gS baseS) ys := by
            let mkDDS : K × (K × X → K) → DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q :=
              fun p =>
                DDS.ofFunq (q := q) (fun msg =>
                  cascadeTrace (K := K) (X := X) (ℓ := ℓ) p.2 p.1 msg)
            have h_comp : outputVec ∘ mkDDS = gS := by
              funext p i j
              simp [outputVec, mkDDS, gS, DDS.transcript, DDS.ofFunq]
            calc
              (Dist.fTransform outputVec STrace.dist) ys =
                  (Dist.fTransform (outputVec ∘ mkDDS) baseS) ys := by
                simp [STrace, URFfunCascadeIdealTrace, baseS, mkDDS, Dist.fTransform_comp]
              _ = (Dist.fTransform gS baseS) ys := by
                  simp [h_comp]

          -- Evaluate both sides at `ys` using fiber sums.
          have h_T_mass :
              (Dist.fTransform gT baseT) ys =
                (Dist.uniform K) root * (Dist.fTransform evalPref (Dist.uniform (Msg X ℓ → K))) outs := by
            have h_sum :=
              Dist.fTransform_apply_eq_sum
                (A := K × (Msg X ℓ → K)) (B := Fin q → Fin (ℓ + 1) → K)
                (f := gT) (X := baseT) ys
            rw [h_sum]
            have h_fiber :
                (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p => gT p = ys)
                  =
                ({root} : Finset K) ×ˢ
                  ((Finset.univ : Finset (Msg X ℓ → K)).filter (fun f => evalPref f = outs)) := by
              ext p
              rcases p with ⟨k0, f⟩
              constructor
              · intro hp
                have hp' : gT (k0, f) = ys := by
                  simpa [Finset.mem_filter] using (Finset.mem_filter.mp hp).2
                have hk : k0 = root ∧ evalPref f = outs := (h_gT_iff (k0, f)).1 hp'
                refine Finset.mem_product.2 ?_
                refine ⟨by simp [hk.1], ?_⟩
                refine Finset.mem_filter.2 ?_
                exact ⟨Finset.mem_univ _, hk.2⟩
              · intro hp
                rcases (Finset.mem_product.mp hp) with ⟨hk0, hf⟩
                have hk0' : k0 = root := by simpa using hk0
                have hf' : evalPref f = outs := by
                  simpa [Finset.mem_filter] using (Finset.mem_filter.mp hf).2
                refine Finset.mem_filter.2 ?_
                refine ⟨Finset.mem_univ _, ?_⟩
                exact (h_gT_iff (k0, f)).2 ⟨hk0', hf'⟩
            rw [h_fiber]
            rw [Finset.sum_product]
            simp [baseT, Dist.prod_apply]
            rw [← (Finset.mul_sum
              (s := (Finset.univ : Finset (Msg X ℓ → K)).filter (fun f => evalPref f = outs))
              (f := fun f => (Dist.uniform (Msg X ℓ → K)) f)
              (a := (Dist.uniform K) root))]
            have h_eval_sum :=
              Dist.fTransform_apply_eq_sum
                (A := Msg X ℓ → K) (B := Fin n → K)
                (f := evalPref) (X := Dist.uniform (Msg X ℓ → K)) outs
            -- Rewrite the remaining term using the fiber-sum characterization of `fTransform`.
            -- (`simpa` here triggers `mul_eq_mul_left_iff` and produces an unwanted disjunction.)
            rw [h_eval_sum]

          have h_S_mass :
              (Dist.fTransform gS baseS) ys =
                (Dist.uniform K) root * (Dist.fTransform evalTrans (Dist.uniform (K × X → K))) outs := by
            have h_sum :=
              Dist.fTransform_apply_eq_sum
                (A := K × (K × X → K)) (B := Fin q → Fin (ℓ + 1) → K)
                (f := gS) (X := baseS) ys
            rw [h_sum]
            have h_fiber :
                (Finset.univ : Finset (K × (K × X → K))).filter (fun p => gS p = ys)
                  =
                ({root} : Finset K) ×ˢ
                  ((Finset.univ : Finset (K × X → K)).filter (fun h => evalTrans h = outs)) := by
              ext p
              rcases p with ⟨k0, h⟩
              constructor
              · intro hp
                have hp' : gS (k0, h) = ys := by
                  simpa [Finset.mem_filter] using (Finset.mem_filter.mp hp).2
                have hk : k0 = root ∧ evalTrans h = outs := (h_gS_iff (k0, h)).1 hp'
                refine Finset.mem_product.2 ?_
                refine ⟨by simp [hk.1], ?_⟩
                refine Finset.mem_filter.2 ?_
                exact ⟨Finset.mem_univ _, hk.2⟩
              · intro hp
                rcases (Finset.mem_product.mp hp) with ⟨hk0, hh⟩
                have hk0' : k0 = root := by simpa using hk0
                have hh' : evalTrans h = outs := by
                  simpa [Finset.mem_filter] using (Finset.mem_filter.mp hh).2
                refine Finset.mem_filter.2 ?_
                refine ⟨Finset.mem_univ _, ?_⟩
                exact (h_gS_iff (k0, h)).2 ⟨hk0', hh'⟩
            rw [h_fiber]
            rw [Finset.sum_product]
            simp [baseS, Dist.prod_apply]
            rw [← (Finset.mul_sum
              (s := (Finset.univ : Finset (K × X → K)).filter (fun h => evalTrans h = outs))
              (f := fun h => (Dist.uniform (K × X → K)) h)
              (a := (Dist.uniform K) root))]
            have h_eval_sum :=
              Dist.fTransform_apply_eq_sum
                (A := K × X → K) (B := Fin n → K)
                (f := evalTrans) (X := Dist.uniform (K × X → K)) outs
            rw [h_eval_sum]

          -- Both evaluations are uniform on vectors (distinct points).
          have h_evalPref :
              Dist.fTransform evalPref (Dist.uniform (Msg X ℓ → K)) = Dist.uniform (Fin n → K) := by
            simpa [evalPref] using
              (RandomSystems.Instances.eval_nonces_uniform
                (X := Msg X ℓ) (Y := K) (n := n) nonces h_inj_nonces)
          have h_evalTrans :
              Dist.fTransform evalTrans (Dist.uniform (K × X → K)) = Dist.uniform (Fin n → K) := by
            simpa [evalTrans] using
              (RandomSystems.Instances.eval_nonces_uniform
                (X := K × X) (Y := K) (n := n) transNonces h_inj_trans)

          have hT' : (Dist.fTransform gT baseT) ys =
                (Dist.uniform K) root * (Dist.uniform (Fin n → K)) outs := by
            simpa [h_evalPref] using h_T_mass
          have hS' : (Dist.fTransform gS baseS) ys =
                (Dist.uniform K) root * (Dist.uniform (Fin n → K)) outs := by
            simpa [h_evalTrans] using h_S_mass

          calc
            (Dist.fTransform outputVec STrace.dist) ys = (Dist.fTransform gS baseS) ys := h_S_push
            _ = (Dist.uniform K) root * (Dist.uniform (Fin n → K)) outs := hS'
            _ = (Dist.fTransform gT baseT) ys := hT'.symm
            _ = (Dist.fTransform outputVec TTrace.dist) ys := h_T_push.symm

        -- Finish by rewriting transcript masses via `h_mass_S`/`h_mass_T`.
        simpa [h_mass_S, h_mass_T] using h_out
    ·
      rcases (not_forall.mp h_inputs) with ⟨i, hi⟩
      have hST :=
        transcriptDist_eq_zero_of_input_mismatch (S := STrace) (inputs := inputs) (t := t) i hi
      have hTT :=
        transcriptDist_eq_zero_of_input_mismatch (S := TTrace) (inputs := inputs) (t := t) i hi
      simp [hST, hTT]

  -- Step 3: Bound the trace-level statDist by the failure probability of the good condition.
  have h_weight :
      (STrace.transcriptDist inputs).weight = (TTrace.transcriptDist inputs).weight := by
    -- Both are probability distributions (weight 1), so weights match.
    have hSTdist : STrace.dist.weight = (1 : NNReal) := by
      dsimp [STrace, URFfunCascadeIdealTrace]
      -- Pushforward preserves weight; product of uniforms has weight 1.
      rw [Dist.weight_fTransform]
      rw [Dist.weight_prod]
      simp [Dist.weight, Dist.uniform]
    have hTTdist : TTrace.dist.weight = (1 : NNReal) := by
      dsimp [TTrace, URFfunPrefixTraceIdeal]
      rw [Dist.weight_fTransform]
      rw [Dist.weight_prod]
      simp [Dist.weight, Dist.uniform]
    have hST : (STrace.transcriptDist inputs).weight = (1 : NNReal) := by
      dsimp [PDS.transcriptDist]
      rw [Dist.weight_fTransform]
      exact hSTdist
    have hTT : (TTrace.transcriptDist inputs).weight = (1 : NNReal) := by
      dsimp [PDS.transcriptDist]
      rw [Dist.weight_fTransform]
      exact hTTdist
    simp [hST, hTT]

  have h_symm :
      statDist (STrace.transcriptDist inputs) (TTrace.transcriptDist inputs) =
        statDist (TTrace.transcriptDist inputs) (STrace.transcriptDist inputs) := by
    simpa using statDist_symm_of_eq_weight (STrace.transcriptDist inputs) (TTrace.transcriptDist inputs) h_weight

  have h_trace_sd_le :
      statDist (STrace.transcriptDist inputs) (TTrace.transcriptDist inputs) ≤
        conditionFailureProb TTrace (goodPrefixTrace (K := K) (X := X) (ℓ := ℓ) (q := q)) inputs := by
    -- Use symmetry + one-sided condition-based bound.
    rw [h_symm]
    exact statDist_le_conditionFailure_single_for_inputs
      (S := TTrace) (T := STrace) (A := goodPrefixTrace (K := K) (X := X) (ℓ := ℓ) (q := q))
      inputs (fun t ht => (h_trace_eq_on_good t ht).symm)

  -- Step 4: Birthday bound for the good-trace failure probability under the ideal trace system.
  have h_fail_le :
      conditionFailureProb TTrace (goodPrefixTrace (K := K) (X := X) (ℓ := ℓ) (q := q)) inputs ≤
        birthdayBound (q * (ℓ + 1)) (Fintype.card K) := by
    classical
    -- Unfold the condition failure probability for the ideal prefix-trace system and pull it back
    -- to the base sampling `(k0, f)` where `k0 : K` and `f : Msg X ℓ → K` are uniform.
    let A := goodPrefixTrace (K := K) (X := X) (ℓ := ℓ) (q := q)
    let base : Dist (K × (Msg X ℓ → K)) :=
      Dist.prod (Dist.uniform K) (Dist.uniform (Msg X ℓ → K))
    let mkDDS : K × (Msg X ℓ → K) → DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q :=
      fun p =>
        DDS.ofFunq (q := q) (fun msg =>
          fun j =>
            if hj : j.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) msg j hj))

    have h_fail_pullback :
        conditionFailureProb TTrace A inputs =
          ∑ p ∈ (Finset.univ : Finset (K × (Msg X ℓ → K))).filter
              (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs)),
            base p := by
      -- Unfold conditionFailureProb and regroup via `fTransform_filter_sum`.
      simp only [conditionFailureProb, TTrace, URFfunPrefixTraceIdeal]
      rw [fTransform_filter_sum
        (f := fun p : K × (Msg X ℓ → K) =>
          DDS.ofFunq (q := q) (fun msg =>
            fun j =>
              if hj : j.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) msg j hj)))
        (X := Dist.prod (Dist.uniform K) (Dist.uniform (Msg X ℓ → K)))
        (P := fun s : DDS (Msg X ℓ) (Fin (ℓ + 1) → K) q =>
          ¬A.holds (DDS.transcript s inputs))]
      simp [mkDDS, base]
      rfl

    -- Switch to the uniform distribution on the product type.
    have h_fail_uniform :
        conditionFailureProb TTrace A inputs =
          ∑ p ∈ (Finset.univ : Finset (K × (Msg X ℓ → K))).filter
              (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs)),
            (Dist.uniform (K × (Msg X ℓ → K))) p := by
      -- `prod (uniform K) (uniform F)` is uniform on the product.
      rw [h_fail_pullback]
      -- rewrite the base distribution
      simpa [base] using congrArg (fun D =>
        ∑ p ∈ (Finset.univ : Finset (K × (Msg X ℓ → K))).filter
              (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs)),
            D p) (Dist.prod_uniform (A := K) (B := (Msg X ℓ → K)))

    -- Now we count bad base samples by a union bound over all pairs of prefix-positions.
    -- Positions are `(query index, prefix length)`.
    let Pos := Fin q × Fin (ℓ + 1)
    let N : ℕ := Fintype.card Pos
    let enc : Pos → Fin N := (Fintype.equivFin Pos)
    let dec : Fin N → Pos := (Fintype.equivFin Pos).symm
    let pref : Pos → List X := fun p => (inputs p.1).1.take p.2.val
    let lab : (K × (Msg X ℓ → K)) → Pos → K := fun p pos =>
      if hj : pos.2.val = 0 then p.1 else p.2 (takeMsg (ℓ := ℓ) (inputs pos.1) pos.2 hj)

    have h_pref_imp_lab : ∀ (p : K × (Msg X ℓ → K)) (u v : Pos),
        pref u = pref v → lab p u = lab p v := by
      intro p u v hpref
      -- If `pref u = pref v`, then either both are the root (j=0) or both are non-root.
      by_cases hu0 : u.2.val = 0
      · -- Root: `pref u = []`, so `pref v = []`, hence `v.2.val = 0` (messages are nonempty).
        have hv0 : v.2.val = 0 := by
          have hnil : (inputs v.1).1.take v.2.val = ([] : List X) := by
            simpa [pref, hu0] using hpref.symm
          have h' :=
              (List.take_eq_nil_iff (l := (inputs v.1).1) (k := v.2.val)).1 hnil
          rcases h' with hv0 | hnil'
          · exact hv0
          · exact (Msg.ne_nil (inputs v.1) hnil').elim
        have hu0' : u.2 = 0 := by
          apply Fin.ext
          simpa using hu0
        have hv0' : v.2 = 0 := by
          apply Fin.ext
          simpa using hv0
        simp [lab, hu0', hv0']
      · by_cases hv0 : v.2.val = 0
        · -- Contradiction: `pref v = []` forces `u.2.val = 0` (or empty message), but `hu0` forbids it.
          exfalso
          have hnil : (inputs u.1).1.take u.2.val = ([] : List X) := by
            simpa [pref, hv0] using hpref
          have h' :=
              (List.take_eq_nil_iff (l := (inputs u.1).1) (k := u.2.val)).1 hnil
          rcases h' with hu0' | hnil'
          · exact hu0 (by simpa using hu0')
          · exact (Msg.ne_nil (inputs u.1) hnil').elim
        · -- Both non-root: equal prefixes imply equal `takeMsg`, hence equal `f` values.
          have htake :
              takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0 =
                takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0 := by
            apply Subtype.ext
            simpa [takeMsg, pref] using hpref
          have hu0' : u.2 ≠ 0 := by
            intro h
            apply hu0
            simp [h]
          have hv0' : v.2 ≠ 0 := by
            intro h
            apply hv0
            simp [h]
          simp [lab, hu0', hv0', htake]

    have h_bad_subset :
        (Finset.univ : Finset (K × (Msg X ℓ → K))).filter
            (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs))
          ⊆
          ((Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2)).biUnion
            (fun ij =>
              (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2))) := by
      intro p hp
      -- From ¬goodPrefixTrace we obtain a collision `lab` at distinct prefixes.
      have hbad : ¬A.holds (DDS.transcript (mkDDS p) inputs) := by
        simpa using (Finset.mem_filter.mp hp).2
      -- Expand the condition and pick a witness pair.
      have :
          ∃ (i : Fin q) (j : Fin (ℓ + 1)) (i' : Fin q) (j' : Fin (ℓ + 1)),
            ¬((pref (i, j) = pref (i', j')) ↔ (lab p (i, j) = lab p (i', j'))) := by
        -- Unfold `A.holds` on the explicit transcript `DDS.transcript (mkDDS p) inputs`.
        -- The input component is always `inputs`, so the condition reduces to `pref`/`lab`.
        simpa [A, goodPrefixTrace, mkDDS, pref, lab, DDS.transcript, DDS.ofFunq] using hbad
      rcases this with ⟨i, j, i', j', huv⟩
      let u : Pos := (i, j)
      let v : Pos := (i', j')
      have huv' : ¬((pref u = pref v) ↔ (lab p u = lab p v)) := by
        simpa [u, v] using huv
      -- Use the implication `pref → lab` to show we get `lab u = lab v` but `pref u ≠ pref v`.
      have huvcoll : lab p u = lab p v ∧ pref u ≠ pref v := by
        by_cases hpref : pref u = pref v
        · have hlab : lab p u = lab p v := h_pref_imp_lab p u v hpref
          have : (pref u = pref v) ↔ (lab p u = lab p v) := by
            exact ⟨fun _ => hlab, fun _ => hpref⟩
          exact (huv' this).elim
        · have hlab : lab p u = lab p v := by
            -- if both sides are false, the ↔ would be true, so `lab` must collide
            by_contra h
            have : (pref u = pref v) ↔ (lab p u = lab p v) := by
              exact ⟨fun h' => (hpref h').elim, fun h' => (h h').elim⟩
            exact (huv' this).elim
          exact ⟨hlab, hpref⟩
      rcases huvcoll with ⟨hlab, hpref⟩
      -- Map positions to indices in `Fin N` and order them.
      let a : Fin N := enc u
      let b : Fin N := enc v
      have hab_ne : a ≠ b := by
        intro h
        have : u = v := (Fintype.equivFin Pos).injective h
        exact hpref (by simp [this])
      -- Choose (min,max) so we land in the strict pair set.
      have hmem :
          ∃ ij : Fin N × Fin N,
            ij.1 < ij.2 ∧ pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2) := by
        by_cases hab : a < b
        · refine ⟨(a, b), hab, ?_, ?_⟩
          · simpa [a, b, enc, dec] using hpref
          · simpa [a, b, enc, dec] using hlab
        · have hba : b < a := lt_of_le_of_ne (Fin.not_lt.mp hab) (Ne.symm hab_ne)
          refine ⟨(b, a), hba, ?_, ?_⟩
          · simpa [a, b, enc, dec] using hpref.symm
          · simpa [a, b, enc, dec] using hlab.symm
      rcases hmem with ⟨ij, hijlt, hijpref, hijlab⟩
      -- Conclude membership in the biUnion.
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨ij, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hijlt⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hijpref, hijlab⟩⟩

    -- Under uniform, bad mass = |bad| / |all|.
    have h_sum_eq :
        (∑ p ∈ (Finset.univ : Finset (K × (Msg X ℓ → K))).filter
              (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs)),
            (Dist.uniform (K × (Msg X ℓ → K))) p)
          =
          (((Finset.univ : Finset (K × (Msg X ℓ → K))).filter
              (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs))).card : NNReal) /
            (Fintype.card (K × (Msg X ℓ → K)) : NNReal) := by
      simp only [Dist.uniform]
      simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

    -- Union bound on the bad set cardinality.
    have h_nat_ub :
          ((Finset.univ : Finset (K × (Msg X ℓ → K))).filter
                (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs))).card ≤
            ∑ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
              ((Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2))).card := by
        calc
          ((Finset.univ : Finset (K × (Msg X ℓ → K))).filter
                (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs))).card
              ≤
              (((Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2)).biUnion
                (fun ij =>
                  (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                    pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2)))).card :=
                Finset.card_le_card h_bad_subset
          _ ≤ _ := Finset.card_biUnion_le

    have h_union_bound :
          (((Finset.univ : Finset (K × (Msg X ℓ → K))).filter
                (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs))).card : NNReal) /
              (Fintype.card (K × (Msg X ℓ → K)) : NNReal)
            ≤
            ∑ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
              (((Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2))).card : NNReal) /
                (Fintype.card (K × (Msg X ℓ → K)) : NNReal) := by
        calc
          (((Finset.univ : Finset (K × (Msg X ℓ → K))).filter
                (fun p => ¬A.holds (DDS.transcript (mkDDS p) inputs))).card : NNReal) /
              (Fintype.card (K × (Msg X ℓ → K)) : NNReal)
            ≤
            ((∑ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
                  ((Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                    pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2))).card : NNReal)) /
              (Fintype.card (K × (Msg X ℓ → K)) : NNReal) := by
                apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
                exact_mod_cast h_nat_ub
          _ = _ := by
                simp_rw [div_eq_mul_inv]
                rw [← Finset.sum_mul]

    -- Each pairwise collision probability is at most `1/|K|`.
    have h_each_pair :
        ∀ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
          (((Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
            pref (dec ij.1) ≠ pref (dec ij.2) ∧ lab p (dec ij.1) = lab p (dec ij.2))).card : NNReal) /
              (Fintype.card (K × (Msg X ℓ → K)) : NNReal)
            ≤ (1 : NNReal) / (Fintype.card K : NNReal) := by
      intro ij hij
      rcases ij with ⟨a, b⟩
      -- Abbreviate the two positions.
      let u : Pos := dec a
      let v : Pos := dec b
      by_cases hpref : pref u = pref v
      · -- Then the collision event is empty.
        have h_empty :
            (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                pref (dec a) ≠ pref (dec b) ∧ lab p (dec a) = lab p (dec b)) = ∅ := by
          ext p
          simp [hpref, u, v]
        simp [h_empty]
      · -- Prefixes differ: split on whether `u`/`v` are the root prefix.
        by_cases hu0 : u.2.val = 0
        · -- `u` is root.
          have hv0 : v.2.val ≠ 0 := by
            intro hv0
            apply hpref
            ext
            simp [pref, hu0, hv0]
          -- Collision set: `k0 = f(prefix v)`, bound by projecting to the function component.
          set C : Finset (K × (Msg X ℓ → K)) :=
            (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
              pref u ≠ pref v ∧ lab p u = lab p v)
          have hC_le :
              C.card ≤ Fintype.card (Msg X ℓ → K) := by
            -- Inject `C ↪ (Msg X ℓ → K)` via `snd`.
            let ψ : (K × (Msg X ℓ → K)) → (Msg X ℓ → K) := Prod.snd
            have h_maps : ∀ p ∈ C, ψ p ∈ (Finset.univ : Finset (Msg X ℓ → K)) := by
              intro _ _; exact Finset.mem_univ _
            have h_inj : Set.InjOn ψ ↑C := by
              intro p₁ hp₁ p₂ hp₂ hψ
              have h₁ : lab p₁ u = lab p₁ v := (Finset.mem_filter.mp hp₁).2.2
              have h₂ : lab p₂ u = lab p₂ v := (Finset.mem_filter.mp hp₂).2.2
              -- With `u` root, `lab p u = p.1`; so `p.1` is determined by `p.2`.
              have hk₁ : p₁.1 = p₁.2 (takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0) := by
                have hu0' : u.2 = 0 := by
                  apply Fin.ext
                  simpa using hu0
                have hv0' : v.2 ≠ 0 := by
                  intro h
                  apply hv0
                  simp [h]
                have hk :
                    p₁.1 =
                      p₁.2 (takeMsg (ℓ := ℓ) (inputs v.1) v.2 (by
                        intro hv
                        apply hv0'
                        apply Fin.ext
                        simpa using hv)) := by
                  simpa [lab, u, v, hu0', hv0'] using h₁
                -- `takeMsg` does not depend on its proof argument.
                have htake :
                    takeMsg (ℓ := ℓ) (inputs v.1) v.2 (by
                      intro hv
                      apply hv0'
                      apply Fin.ext
                      simpa using hv) =
                      takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0 := by
                  apply Subtype.ext
                  rfl
                simpa [htake] using hk
              have hk₂ : p₂.1 = p₂.2 (takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0) := by
                have hu0' : u.2 = 0 := by
                  apply Fin.ext
                  simpa using hu0
                have hv0' : v.2 ≠ 0 := by
                  intro h
                  apply hv0
                  simp [h]
                have hk :
                    p₂.1 =
                      p₂.2 (takeMsg (ℓ := ℓ) (inputs v.1) v.2 (by
                        intro hv
                        apply hv0'
                        apply Fin.ext
                        simpa using hv)) := by
                  simpa [lab, u, v, hu0', hv0'] using h₂
                have htake :
                      takeMsg (ℓ := ℓ) (inputs v.1) v.2 (by
                        intro hv
                        apply hv0'
                        apply Fin.ext
                        simpa using hv) =
                        takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0 := by
                    apply Subtype.ext
                    rfl
                simpa [htake] using hk
              have hf : p₁.2 = p₂.2 := by
                simpa [ψ] using hψ
              have hk : p₁.1 = p₂.1 := by
                have hcongr :
                    p₁.2 (takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0) =
                      p₂.2 (takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0) := by
                  simpa using
                    congrArg (fun f => f (takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0)) hf
                exact hk₁.trans (hcongr.trans hk₂.symm)
              exact Prod.ext hk hf
            have h_card := Finset.card_le_card_of_injOn ψ h_maps h_inj
            simpa [C] using h_card
          -- Convert to probability ≤ 1/|K|.
          have h_all_pos : (0 : NNReal) < (Fintype.card (K × (Msg X ℓ → K)) : NNReal) :=
            Nat.cast_pos.mpr (Fintype.card_pos (α := K × (Msg X ℓ → K)))
          have hK_pos : (0 : NNReal) < (Fintype.card K : NNReal) :=
            Nat.cast_pos.mpr (Fintype.card_pos (α := K))
          -- Use `C.card ≤ |F|` and `|K×F| = |K|*|F|`.
          rw [div_le_div_iff₀ h_all_pos hK_pos]
          simp only [one_mul]
          -- Goal: C.card * |K| ≤ |K×F|
          have : C.card * Fintype.card K ≤ Fintype.card (K × (Msg X ℓ → K)) := by
            -- `C.card ≤ |F|`
            have h' : C.card * Fintype.card K ≤ Fintype.card (Msg X ℓ → K) * Fintype.card K :=
              Nat.mul_le_mul_right _ hC_le
            -- `|K×F| = |K|*|F|`
            simpa [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h'
          exact_mod_cast this
        · -- `u` is non-root.
          by_cases hv0 : v.2.val = 0
          · -- `v` is root: symmetric to previous case.
            -- Swap roles of `u` and `v` and reuse the same argument.
            have hu0' : u.2.val ≠ 0 := hu0
            -- Define `C` with swapped endpoints.
            set C : Finset (K × (Msg X ℓ → K)) :=
              (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                pref v ≠ pref u ∧ lab p v = lab p u)
            have hC_le :
                C.card ≤ Fintype.card (Msg X ℓ → K) := by
              let ψ : (K × (Msg X ℓ → K)) → (Msg X ℓ → K) := Prod.snd
              have h_maps : ∀ p ∈ C, ψ p ∈ (Finset.univ : Finset (Msg X ℓ → K)) := by
                intro _ _; exact Finset.mem_univ _
              have h_inj : Set.InjOn ψ ↑C := by
                intro p₁ hp₁ p₂ hp₂ hψ
                have h₁ : lab p₁ v = lab p₁ u := (Finset.mem_filter.mp hp₁).2.2
                have h₂ : lab p₂ v = lab p₂ u := (Finset.mem_filter.mp hp₂).2.2
                have hk₁ : p₁.1 = p₁.2 (takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0') := by
                  have hv0' : v.2 = 0 := by
                    apply Fin.ext
                    simpa using hv0
                  have hu0'' : u.2 ≠ 0 := by
                    intro h
                    apply hu0'
                    simpa using congrArg Fin.val h
                  have hk :
                      p₁.1 =
                        p₁.2 (takeMsg (ℓ := ℓ) (inputs u.1) u.2 (by
                          intro hu
                          apply hu0''
                          apply Fin.ext
                          simpa using hu)) := by
                    simpa [lab, hv0', hu0''] using h₁
                  have htake :
                      takeMsg (ℓ := ℓ) (inputs u.1) u.2 (by
                        intro hu
                        apply hu0''
                        apply Fin.ext
                        simpa using hu) =
                        takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0' := by
                    apply Subtype.ext
                    rfl
                  simpa [htake] using hk
                have hk₂ : p₂.1 = p₂.2 (takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0') := by
                  have hv0' : v.2 = 0 := by
                    apply Fin.ext
                    simpa using hv0
                  have hu0'' : u.2 ≠ 0 := by
                    intro h
                    apply hu0'
                    simpa using congrArg Fin.val h
                  have hk :
                      p₂.1 =
                        p₂.2 (takeMsg (ℓ := ℓ) (inputs u.1) u.2 (by
                          intro hu
                          apply hu0''
                          apply Fin.ext
                          simpa using hu)) := by
                    simpa [lab, hv0', hu0''] using h₂
                  have htake :
                      takeMsg (ℓ := ℓ) (inputs u.1) u.2 (by
                        intro hu
                        apply hu0''
                        apply Fin.ext
                        simpa using hu) =
                        takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0' := by
                    apply Subtype.ext
                    rfl
                  simpa [htake] using hk
                have hf : p₁.2 = p₂.2 := by simpa [ψ] using hψ
                have hk : p₁.1 = p₂.1 := by
                  have hcongr :
                      p₁.2 (takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0') =
                        p₂.2 (takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0') := by
                    simpa using
                      congrArg (fun f => f (takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0')) hf
                  exact hk₁.trans (hcongr.trans hk₂.symm)
                exact Prod.ext hk hf
              have h_card := Finset.card_le_card_of_injOn ψ h_maps h_inj
              simpa [C] using h_card
            have h_all_pos : (0 : NNReal) < (Fintype.card (K × (Msg X ℓ → K)) : NNReal) :=
              Nat.cast_pos.mpr (Fintype.card_pos (α := K × (Msg X ℓ → K)))
            have hK_pos : (0 : NNReal) < (Fintype.card K : NNReal) :=
              Nat.cast_pos.mpr (Fintype.card_pos (α := K))
            -- The target collision finset equals `C`.
            have hC_eq :
                (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                    pref (dec a) ≠ pref (dec b) ∧ lab p (dec a) = lab p (dec b)) = C := by
              ext p
              constructor
              · intro hp
                have hp' := (Finset.mem_filter.mp hp).2
                dsimp [C]
                refine Finset.mem_filter.mpr ?_
                refine ⟨Finset.mem_univ _, ?_⟩
                have hne : pref (dec a) ≠ pref (dec b) := hp'.1
                have heq : lab p (dec a) = lab p (dec b) := hp'.2
                constructor
                · dsimp [u, v]
                  intro h
                  apply hne
                  exact h.symm
                · dsimp [u, v]
                  exact heq.symm
              · intro hp
                have hp' : pref v ≠ pref u ∧ lab p v = lab p u := by
                  have hp' := hp
                  dsimp [C] at hp'
                  exact (Finset.mem_filter.mp hp').2
                refine Finset.mem_filter.mpr ?_
                refine ⟨Finset.mem_univ _, ?_⟩
                have hne : pref v ≠ pref u := hp'.1
                have heq : lab p v = lab p u := hp'.2
                constructor
                · dsimp [u, v] at hne
                  intro h
                  apply hne
                  exact h.symm
                · dsimp [u, v] at heq
                  exact heq.symm
            rw [hC_eq]
            rw [div_le_div_iff₀ h_all_pos hK_pos]
            simp only [one_mul]
            have : C.card * Fintype.card K ≤ Fintype.card (K × (Msg X ℓ → K)) := by
              have h' : C.card * Fintype.card K ≤ Fintype.card (Msg X ℓ → K) * Fintype.card K :=
                Nat.mul_le_mul_right _ hC_le
              simpa [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h'
            exact_mod_cast this
          · -- Both are non-root: use the uniform-function collision bound.
            -- Define the two nonce messages.
            let a₁ : Msg X ℓ := takeMsg (ℓ := ℓ) (inputs u.1) u.2 hu0
            let a₂ : Msg X ℓ := takeMsg (ℓ := ℓ) (inputs v.1) v.2 hv0
            have ha : a₁ ≠ a₂ := by
              intro h
              apply hpref
              -- Compare the underlying prefix lists.
              have := congrArg Subtype.val h
              simpa [a₁, a₂, pref, takeMsg] using this
            -- The collision set only depends on `f` and factors through `snd`.
            set Cfun : Finset (Msg X ℓ → K) :=
              (Finset.univ : Finset (Msg X ℓ → K)).filter (fun f => f a₁ = f a₂)
            have hCfun :
                Cfun.card * Fintype.card K ≤ Fintype.card (Msg X ℓ → K) :=
              fun_pair_collision_le (A := Msg X ℓ) (B := K) a₁ a₂ ha
            -- Lift to the product type by multiplying by `|K|` (the `k0` coordinate).
            have hC_prod :
                ((Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p => p.2 a₁ = p.2 a₂)).card *
                    Fintype.card K ≤
                  Fintype.card (K × (Msg X ℓ → K)) := by
              -- Filter-by-second-coordinate is a product.
              have h_eq :
                  (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p => p.2 a₁ = p.2 a₂) =
                    (Finset.univ : Finset K).product Cfun := by
                ext p
                rcases p with ⟨k0, f⟩
                simp [Cfun]
              -- Compute card and use `hCfun`.
              -- `|univ × Cfun| = |K| * |Cfun|`.
              have h_nat :
                  ((Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p => p.2 a₁ = p.2 a₂)).card =
                    Fintype.card K * Cfun.card := by
                  simp [h_eq, Finset.card_product, Finset.card_univ]
              -- Now multiply by `|K|` and apply `hCfun`.
              -- Goal becomes `|K|*|Cfun|*|K| ≤ |K×F| = |K|*|F|`.
              have h1 : (Fintype.card K * Cfun.card) * Fintype.card K ≤
                  Fintype.card K * Fintype.card (Msg X ℓ → K) := by
                -- from `Cfun.card*|K| ≤ |F|` multiply by `|K|`
                have := Nat.mul_le_mul_left (Fintype.card K) hCfun
                -- reorder
                simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
              -- rewrite cards
              simpa [h_nat, Fintype.card_prod, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h1
            -- The collision finset in the statement equals this product-filter (since `pref u ≠ pref v`).
            have hC_eq :
                (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p =>
                    pref (dec a) ≠ pref (dec b) ∧ lab p (dec a) = lab p (dec b)) =
                  (Finset.univ : Finset (K × (Msg X ℓ → K))).filter (fun p => p.2 a₁ = p.2 a₂) := by
              ext p
              have hprefab : pref (dec a) ≠ pref (dec b) := by simpa [u, v, dec] using hpref
              constructor
              · intro hp
                have hp' := (Finset.mem_filter.mp hp).2
                have hlab : lab p (dec a) = lab p (dec b) := hp'.2
                refine Finset.mem_filter.mpr ?_
                refine ⟨Finset.mem_univ _, ?_⟩
                have hu0a : (dec a).2.val ≠ 0 := by
                  simpa [u] using hu0
                have hv0b : (dec b).2.val ≠ 0 := by
                  simpa [v] using hv0
                have hlu :
                    lab p (dec a) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a) := by
                  dsimp [lab]
                  rw [dif_neg hu0a]
                have hlv :
                    lab p (dec b) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b) := by
                  dsimp [lab]
                  rw [dif_neg hv0b]
                have ha1 :
                    takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a = a₁ := by
                  dsimp [a₁, u]
                have ha2 :
                    takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b = a₂ := by
                  dsimp [a₂, v]
                have :
                    p.2 (takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b) := by
                  calc
                    p.2 (takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a) =
                        lab p (dec a) := by simpa using hlu.symm
                    _ = lab p (dec b) := hlab
                    _ =
                        p.2 (takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b) := hlv
                simpa [ha1, ha2] using this
              · intro hp
                have hp' := (Finset.mem_filter.mp hp).2
                refine Finset.mem_filter.mpr ?_
                refine ⟨Finset.mem_univ _, ?_⟩
                refine ⟨hprefab, ?_⟩
                have hu0a : (dec a).2.val ≠ 0 := by
                  simpa [u] using hu0
                have hv0b : (dec b).2.val ≠ 0 := by
                  simpa [v] using hv0
                have hlu :
                    lab p (dec a) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a) := by
                  dsimp [lab]
                  rw [dif_neg hu0a]
                have hlv :
                    lab p (dec b) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b) := by
                  dsimp [lab]
                  rw [dif_neg hv0b]
                have ha1 :
                    takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a = a₁ := by
                  dsimp [a₁, u]
                have ha2 :
                    takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b = a₂ := by
                  dsimp [a₂, v]
                have :
                    p.2 (takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b) := by
                  simpa [ha1.symm, ha2.symm] using hp'
                calc
                  lab p (dec a) =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec a).1) (dec a).2 hu0a) := hlu
                  _ =
                      p.2 (takeMsg (ℓ := ℓ) (inputs (dec b).1) (dec b).2 hv0b) := this
                  _ = lab p (dec b) := hlv.symm
            -- Convert the Nat bound to the NNReal probability inequality.
            have h_all_pos : (0 : NNReal) < (Fintype.card (K × (Msg X ℓ → K)) : NNReal) :=
              Nat.cast_pos.mpr (Fintype.card_pos (α := K × (Msg X ℓ → K)))
            have hK_pos : (0 : NNReal) < (Fintype.card K : NNReal) :=
              Nat.cast_pos.mpr (Fintype.card_pos (α := K))
            rw [hC_eq]
            rw [div_le_div_iff₀ h_all_pos hK_pos]
            simp only [one_mul]
            exact_mod_cast hC_prod

    -- Sum of `C(N,2)` copies of `1/|K|` equals the birthday bound.
    have h_sum_pairs :
        ∑ ij ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2),
            (1 : NNReal) / (Fintype.card K : NNReal)
          =
          birthdayBound N (Fintype.card K) := by
      rw [Finset.sum_const, nsmul_eq_mul, birthdayBound]
      have h_card := card_strictLTPairs (q := N)
      rw [mul_one_div]
      rw [show (N * (N - 1) : ℕ) =
          ((Finset.univ : Finset (Fin N × Fin N)).filter (fun ij => ij.1 < ij.2)).card * 2 from h_card.symm]
      push_cast
      ring

    -- Put everything together.
    rw [h_fail_uniform]
    rw [h_sum_eq]
    have hN : N = q * (ℓ + 1) := by
      simp [N, Pos, Fintype.card_prod, Fintype.card_fin]
    rw [← hN]
    refine le_trans ?_ (le_trans (Finset.sum_le_sum h_each_pair) (le_of_eq h_sum_pairs))
    exact h_union_bound

  -- Combine.
  exact le_trans h_data (le_trans h_trace_sd_le h_fail_le)

end BonehShoup6_4

namespace BonehShoup6_4

/-! ### Cascade from a non-uniform transition primitive -/

theorem advantageOn_URFfunCascadeOf_URFfun_prefixFree_le_statDist_add_birthday
    {K X : Type*}
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)]
    [Fintype (Transcript (Msg X ℓ) K q)] [DecidableEq (Transcript (Msg X ℓ) K q)]
    (Dh : Dist (K × X → K)) :
    advantageOn (URFfunCascadeOf (K := K) (X := X) (ℓ := ℓ) (q := q) Dh)
      (Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q))
      (PrefixFree X ℓ q)
      ≤
      statDist Dh (Dist.uniform (K × X → K)) +
        birthdayBound (q * (ℓ + 1)) (Fintype.card K) := by
  classical

  let S : PDS (Msg X ℓ) K q :=
    URFfunCascadeOf (K := K) (X := X) (ℓ := ℓ) (q := q) Dh
  let T : PDS (Msg X ℓ) K q :=
    URFfunCascadeIdeal (K := K) (X := X) (ℓ := ℓ) (q := q)
  let U : PDS (Msg X ℓ) K q :=
    Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q)

  -- Bound `statDist` pointwise on prefix-free inputs, then take the supremum.
  refine advantageOn_le_of_pointwise (S := S) (T := U) (Good := PrefixFree X ℓ q)
    (ε := statDist Dh (Dist.uniform (K × X → K)) +
      birthdayBound (q * (ℓ + 1)) (Fintype.card K)) ?_
  intro inputs hPF

  have h_triangle :
      statDist (S.transcriptDist inputs) (U.transcriptDist inputs) ≤
        statDist (S.transcriptDist inputs) (T.transcriptDist inputs) +
          statDist (T.transcriptDist inputs) (U.transcriptDist inputs) :=
    statDist_triangle _ _ _

  have h_ST_transcript :
      statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤ statDist S.dist T.dist := by
    simpa [PDS.transcriptDist] using
      (statDist_fTransform_le S.dist T.dist (fun s : DDS (Msg X ℓ) K q => DDS.transcript s inputs))

  have h_TU_transcript :
      statDist (T.transcriptDist inputs) (U.transcriptDist inputs) ≤
        birthdayBound (q * (ℓ + 1)) (Fintype.card K) := by
    have h_le_adv :
        statDist (T.transcriptDist inputs) (U.transcriptDist inputs) ≤
          advantageOn T U (PrefixFree X ℓ q) := by
      -- `advantageOn` is a supremum over prefix-free inputs.
      dsimp [advantageOn]
      refine Finset.le_sup (s := (Finset.univ.filter (PrefixFree X ℓ q)))
        (f := fun inputs : Fin q → Msg X ℓ =>
          statDist (T.transcriptDist inputs) (U.transcriptDist inputs))
        (b := inputs) ?_
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ inputs, hPF⟩
    refine le_trans h_le_adv ?_
    simpa [T, U] using
      (advantageOn_URFfunCascadeIdeal_URFfun_prefixFree_le_birthday
        (K := K) (X := X) (ℓ := ℓ) (q := q))

  have h_ST_dist :
      statDist S.dist T.dist ≤ statDist Dh (Dist.uniform (K × X → K)) := by
    -- `S.dist` and `T.dist` are pushforwards of the same map, with only `Dh` changing.
    dsimp [S, T, URFfunCascadeIdeal, URFfunCascadeOf]
    -- Data processing for the pushforward (collapse the outer `fTransform`).
    refine le_trans
      (statDist_fTransform_le
        (Dist.prod (Dist.uniform K) Dh)
        (Dist.prod (Dist.uniform K) (Dist.uniform (K × X → K)))
        (fun p : K × (K × X → K) =>
          DDS.ofFunq (q := q)
            (fun msg : Msg X ℓ => cascadeEval (K := K) (X := X) p.2 p.1 msg.1)))
      ?_
    -- Factor out the shared uniform `K` component.
    refine le_of_eq ?_
    calc
      statDist (Dist.prod (Dist.uniform K) Dh)
          (Dist.prod (Dist.uniform K) (Dist.uniform (K × X → K)))
          =
          (Dist.uniform K).weight * statDist Dh (Dist.uniform (K × X → K)) := by
            simpa using
              (statDist_prod_left (U := Dist.uniform K) (X := Dh) (Y := Dist.uniform (K × X → K)))
      _ = statDist Dh (Dist.uniform (K × X → K)) := by
            -- `uniform K` is a probability distribution, so its weight is 1.
            simp [Dist.weight, Dist.uniform]

  -- Combine the bounds.
  refine le_trans h_triangle ?_
  refine le_trans (add_le_add h_ST_transcript h_TU_transcript) ?_
  exact add_le_add h_ST_dist (le_rfl)

end BonehShoup6_4

end RandomSystems.Applications
