/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictContextTotal

/-!
# Strict contextual distance equals CR18 advantage on shared-domain laws

`maxEDist ≤ ENNReal.ofReal Δ` is unconditional (`StrictContextAdvantage`),
and equality is known on total laws (`StrictContextTotal`).  This module
extends the equality to the **shared-domain subcarrier**: pairs of laws all
of whose support atoms present one common domain — exactly the objects
Lanzenberger's Def 2.14 admits (a PDS is a distribution over deterministic
systems *with the same domain*).

The obstruction on the unrestricted carrier is CR18 Def 3.3's completion:
deleting a rejected query is a free domain probe the strict semantics does
not grant,
so `Δ` can genuinely exceed the strict distance
(`AttainmentCounterexample` exhibits the class-distance gap).  On a shared
domain that probe buys the distinguisher nothing, because rejection is a
*public* function of the query history: whether the completion answers `⊥`
depends only on the common domain, never on the sampled atom.  We therefore
**prune** the optimal CR18 environment: a fuel-bounded replay machine
(`pruneStep`/`pruneRun`) simulates the environment against the known
domain, synthesizes every `⊥` answer itself, and forwards only the accepted
queries.  The pruned distinguisher (`prunedDDD`) reproduces the CR18
verdict atom-by-atom while never receiving the completion symbol, so it
compiles to a strict test through the existing `testOfTruncDDD` bridge and
the CR18 advantage is attained strictly.

Headline: `maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain`.  The `≤`-only
rule thereby becomes a scoped statement — `≤` on the unrestricted carrier,
`=` on every object the sources admit.  The corollary
`maxEDist_filterDom_eq_ofReal_maxAdvantage` records the consequence for
same-predicate restrictions of total laws (CBC's `θ_r` and the `[q]` query
filter): their stalls are input-determined, so `Δ`-stated bounds on them
carry no metric slack.
-/

namespace RandomSystems.CR18.StrictContextSharedDomain

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.StrictContext
open scoped Classical ENNReal PFunDDS

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-! ## The shared-domain subcarrier

Every support atom of the law presents one common domain `D` — the
shared-domain discipline of Lanzenberger Def 2.14, read on a displayed
law.  The tree's one definition of the clause is `PFunPDS.HasFixedDomain`
(`RandomSystem.lean`); equality of the strict metric with
`ENNReal.ofReal Δ` is proved below for pairs of laws sharing one `D`. -/

/-- Total laws are shared-domain on the full nonempty-history domain, so
the shared-domain equality strictly generalizes the total one. -/
theorem sharedDomainOn_of_totalOnNonempty (law : PFunPDS X Y)
    (total : CondEquiv.TotalOnNonempty law) :
    PFunPDS.HasFixedDomain law {l : List X | l ≠ []} := by
  intro s hs
  ext l
  constructor
  · intro hl
    rintro rfl
    exact PFunDDS.empty_not_mem s hl
  · intro hl
    exact total s hs l hl

/-! ## Transcript pruning: the proper steps of a completed transcript -/

/-- The proper (non-`⊥`) steps of a completed transcript — the part of the
interaction the strict semantics can realize. -/
def properSteps (t : List (X × Option Y)) : List (X × Option Y) :=
  t.filter fun step => step.2.isSome

/-- The inputs the deletion pass keeps, read off the completed transcript:
exactly the inputs of the proper steps. -/
def keptTranscriptInputs (t : List (X × Option Y)) : List X :=
  (properSteps t)↓ₓ

@[simp]
theorem properSteps_nil : properSteps ([] : List (X × Option Y)) = [] := rfl

theorem properSteps_append_some (t : List (X × Option Y)) (x : X) (y : Y) :
    properSteps (t ++ [(x, some y)]) = properSteps t ++ [(x, some y)] := by
  simp [properSteps]

theorem properSteps_append_none (t : List (X × Option Y)) (x : X) :
    properSteps (t ++ [(x, none)]) = properSteps t := by
  simp [properSteps]

theorem keptTranscriptInputs_append_some (t : List (X × Option Y))
    (x : X) (y : Y) :
    keptTranscriptInputs (t ++ [(x, some y)]) =
      keptTranscriptInputs t ++ [x] := by
  unfold keptTranscriptInputs
  rw [properSteps_append_some]
  simp [PFunDDS.transcriptInputs]

theorem keptTranscriptInputs_append_none (t : List (X × Option Y)) (x : X) :
    keptTranscriptInputs (t ++ [(x, none)]) = keptTranscriptInputs t := by
  unfold keptTranscriptInputs
  rw [properSteps_append_none]

theorem properOutputs_append_some (t : List (X × Option Y)) (x : X) (y : Y) :
    (properSteps (t ++ [(x, some y)]))↓ᵧ =
      (properSteps t)↓ᵧ ++ [some y] := by
  rw [properSteps_append_some]
  simp [PFunDDS.transcriptOutputs]

theorem properOutputs_append_none (t : List (X × Option Y)) (x : X) :
    (properSteps (t ++ [(x, none)]))↓ᵧ = (properSteps t)↓ᵧ := by
  rw [properSteps_append_none]

theorem none_notMem_properSteps_outputs (t : List (X × Option Y)) :
    none ∉ (properSteps t)↓ᵧ := by
  intro hmem
  obtain ⟨step, hstep, hnone⟩ := List.mem_map.mp hmem
  have hsome : step.2.isSome := by simpa using (List.mem_filter.mp hstep).2
  rw [hnone] at hsome
  simp at hsome

theorem length_properSteps_le (t : List (X × Option Y)) :
    (properSteps t).length ≤ t.length :=
  List.length_filter_le _ t

/-- Reading `s⊥` one step past an arbitrary input history, as the
deletion-pass candidate test.  (The existing append reader
`output_fullyDefined_append_of_mem` assumes the history itself is kept;
the pruning induction needs the raw form on histories that already carry
deleted inputs.) -/
private theorem output_fullyDefined_append (s : PFunDDS.DDS X Y)
    (l : List X) (x : X) :
    PFunDDS.output (s⊥) (l ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      if hcand : PFunDDS.keptPrefix s l ++ [x] ∈ PFunDDS.dom s then
        some (PFunDDS.output s (PFunDDS.keptPrefix s l ++ [x]) hcand)
      else none := by
  rw [PFunDDS.output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  simp only [hdrop, hlast]

/-- The kept transcript inputs of a genuine completed transcript are the
deletion pass of its raw inputs: the transcript records `⊥` exactly where
the deletion pass drops the query. -/
theorem keptTranscriptInputs_transcript (s : PFunDDS.DDS X Y)
    (e : PFunDDS.DDE X Y) :
    ∀ f : ℕ,
      keptTranscriptInputs (PFunDDS.transcript s e f) =
        PFunDDS.keptPrefix s ((PFunDDS.transcript s e f)↓ₓ) := by
  intro f
  induction f with
  | zero => rfl
  | succ f ih =>
      rcases he : e ((PFunDDS.transcript s e f)↓ᵧ) with _ | x
      · rw [transcript_succ_stall he]
        exact ih
      · by_cases hcand :
            PFunDDS.keptPrefix s ((PFunDDS.transcript s e f)↓ₓ) ++ [x] ∈
              PFunDDS.dom s
        · have hout : PFunDDS.output (s⊥)
              ((PFunDDS.transcript s e f)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) =
              some (PFunDDS.output s _ hcand) := by
            rw [output_fullyDefined_append]
            exact dif_pos hcand
          rw [transcript_succ_fire he, hout,
            keptTranscriptInputs_append_some]
          simp only [transcriptInputs_append]
          rw [PFunDDS.keptPrefix_append_singleton, if_pos hcand, ih]
        · have hout : PFunDDS.output (s⊥)
              ((PFunDDS.transcript s e f)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
            rw [output_fullyDefined_append]
            exact dif_neg hcand
          rw [transcript_succ_fire he, hout,
            keptTranscriptInputs_append_none]
          simp only [transcriptInputs_append]
          rw [PFunDDS.keptPrefix_append_singleton, if_neg hcand, ih]

/-! ## The pruning replay machine

State: the virtual completed transcript rebuilt so far, and the real
answers not yet consumed.  One step simulates the environment on the
virtual transcript: a query the common domain rejects is answered `⊥`
internally, a query it accepts consumes the next real answer, and the
machine freezes on environment stall or when the next real answer has not
arrived yet. -/

/-- One step of the rejection-pruning replay. -/
def pruneStep (e : PFunDDS.DDE X Y) (D : Set (List X)) :
    List (X × Option Y) × List (Option Y) →
      List (X × Option Y) × List (Option Y) :=
  fun state =>
    match e (state.1↓ᵧ) with
    | none => state
    | some x =>
        if keptTranscriptInputs state.1 ++ [x] ∈ D then
          match state.2 with
          | [] => state
          | answer :: rest => (state.1 ++ [(x, answer)], rest)
        else (state.1 ++ [(x, none)], state.2)

/-- The machine state that awaits the next real answer: the environment
fires a query the common domain accepts, but no forwarded answer is
available yet. -/
def Blocked (e : PFunDDS.DDE X Y) (D : Set (List X))
    (state : List (X × Option Y) × List (Option Y)) : Prop :=
  state.2 = [] ∧
    ∃ x, e (state.1↓ᵧ) = some x ∧ keptTranscriptInputs state.1 ++ [x] ∈ D

theorem pruneStep_stall {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {t : List (X × Option Y)} {rest : List (Option Y)}
    (h : e (t↓ᵧ) = none) : pruneStep e D (t, rest) = (t, rest) := by
  unfold pruneStep
  dsimp only
  rw [h]

theorem pruneStep_reject {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {t : List (X × Option Y)} {rest : List (Option Y)} {x : X}
    (h : e (t↓ᵧ) = some x) (hx : keptTranscriptInputs t ++ [x] ∉ D) :
    pruneStep e D (t, rest) = (t ++ [(x, none)], rest) := by
  unfold pruneStep
  dsimp only
  rw [h]
  dsimp only
  rw [if_neg hx]

theorem pruneStep_consume {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {t : List (X × Option Y)} {answer : Option Y} {rest : List (Option Y)}
    {x : X} (h : e (t↓ᵧ) = some x)
    (hx : keptTranscriptInputs t ++ [x] ∈ D) :
    pruneStep e D (t, answer :: rest) = (t ++ [(x, answer)], rest) := by
  unfold pruneStep
  dsimp only
  rw [h]
  dsimp only
  rw [if_pos hx]

theorem pruneStep_blocked {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {state : List (X × Option Y) × List (Option Y)}
    (h : Blocked e D state) : pruneStep e D state = state := by
  obtain ⟨hrest, x, hfire, hacc⟩ := h
  obtain ⟨t, rest⟩ := state
  dsimp only at hrest
  subst hrest
  unfold pruneStep
  dsimp only
  rw [hfire]
  dsimp only
  rw [if_pos hacc]

/-- The pruning replay: from the real answers alone, rebuild the virtual
completed transcript after at most `fuel` virtual steps. -/
def pruneRun (e : PFunDDS.DDE X Y) (D : Set (List X)) (fuel : ℕ)
    (answers : List (Option Y)) : List (X × Option Y) × List (Option Y) :=
  (pruneStep e D)^[fuel] ([], answers)

theorem pruneRun_succ (e : PFunDDS.DDE X Y) (D : Set (List X)) (fuel : ℕ)
    (answers : List (Option Y)) :
    pruneRun e D (fuel + 1) answers =
      pruneStep e D (pruneRun e D fuel answers) := by
  unfold pruneRun
  exact Function.iterate_succ_apply' _ _ _

theorem pruneRun_add (e : PFunDDS.DDE X Y) (D : Set (List X))
    {small large : ℕ} (hle : small ≤ large) (answers : List (Option Y)) :
    pruneRun e D large answers =
      (pruneStep e D)^[large - small] (pruneRun e D small answers) := by
  unfold pruneRun
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]

/-- The machine never rebuilds more virtual steps than its fuel. -/
theorem pruneRun_fst_length_le (e : PFunDDS.DDE X Y) (D : Set (List X)) :
    ∀ (fuel : ℕ) (answers : List (Option Y)),
      (pruneRun e D fuel answers).1.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro answers; exact Nat.le_refl 0
  | succ fuel ih =>
      intro answers
      rw [pruneRun_succ]
      cases hp : pruneRun e D fuel answers with
      | mk t rest =>
      have hlen : t.length ≤ fuel := by
        have hlen' := ih answers
        rw [hp] at hlen'
        exact hlen'
      rcases he : e (t↓ᵧ) with _ | x
      · rw [pruneStep_stall he]
        exact Nat.le_succ_of_le hlen
      · by_cases hacc : keptTranscriptInputs t ++ [x] ∈ D
        · cases rest with
          | nil =>
              rw [pruneStep_blocked ⟨rfl, x, he, hacc⟩]
              exact Nat.le_succ_of_le hlen
          | cons answer rest =>
              rw [pruneStep_consume he hacc]
              simpa using Nat.succ_le_succ hlen
        · rw [pruneStep_reject he hacc]
          simpa using Nat.succ_le_succ hlen

/-- Extending the real answers either commutes with the replay or the
shorter replay froze awaiting an answer strictly before the fuel ran out.
This is what makes the pruned verdict final. -/
theorem pruneRun_append (e : PFunDDS.DDE X Y) (D : Set (List X))
    (extra : List (Option Y)) :
    ∀ (fuel : ℕ) (answers : List (Option Y)),
      pruneRun e D fuel (answers ++ extra) =
          ((pruneRun e D fuel answers).1,
            (pruneRun e D fuel answers).2 ++ extra) ∨
        ∃ j < fuel, Blocked e D (pruneRun e D j answers) := by
  intro fuel
  induction fuel with
  | zero => intro answers; exact Or.inl rfl
  | succ fuel ih =>
      intro answers
      rcases ih answers with heq | ⟨j, hj, hblocked⟩
      · rw [pruneRun_succ, pruneRun_succ, heq]
        cases hp : pruneRun e D fuel answers with
        | mk t rest =>
        rcases he : e (t↓ᵧ) with _ | x
        · rw [pruneStep_stall he, pruneStep_stall he]
          exact Or.inl rfl
        · by_cases hacc : keptTranscriptInputs t ++ [x] ∈ D
          · cases rest with
            | nil =>
                refine Or.inr ⟨fuel, Nat.lt_succ_self fuel, ?_⟩
                rw [hp]
                exact ⟨rfl, x, he, hacc⟩
            | cons answer rest =>
                rw [show (answer :: rest) ++ extra =
                  answer :: (rest ++ extra) from rfl,
                  pruneStep_consume he hacc, pruneStep_consume he hacc]
                exact Or.inl rfl
          · rw [pruneStep_reject he hacc, pruneStep_reject he hacc]
            exact Or.inl rfl
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hblocked⟩

/-- A blocked replay is frozen: the machine state never changes again. -/
theorem pruneRun_eq_of_blocked {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {answers : List (Option Y)} {j : ℕ}
    (hblocked : Blocked e D (pruneRun e D j answers)) {fuel : ℕ}
    (hle : j ≤ fuel) :
    pruneRun e D fuel answers = pruneRun e D j answers := by
  rw [pruneRun_add e D hle]
  exact Function.iterate_fixed (pruneStep_blocked hblocked) _

/-! ## The pruned distinguisher -/

/-- The move of the pruned distinguisher: replay the real answers for at
most `q` virtual steps, then forward the environment's next accepted query
while virtual budget remains, and otherwise stop with the accept verdict
on the rebuilt virtual transcript. -/
def prunedMove (e : PFunDDS.DDE X Y) (D : Set (List X)) (q : ℕ)
    (accept : List (X × Option Y) → Bool)
    (answers : List (Option Y)) : X ⊕ Bool :=
  match e ((pruneRun e D q answers).1↓ᵧ) with
  | none => Sum.inr (accept (pruneRun e D q answers).1)
  | some x =>
      if (pruneRun e D q answers).1.length < q then Sum.inl x
      else Sum.inr (accept (pruneRun e D q answers).1)

theorem prunedMove_of_stall {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {q : ℕ} {accept : List (X × Option Y) → Bool}
    {answers : List (Option Y)}
    (h : e ((pruneRun e D q answers).1↓ᵧ) = none) :
    prunedMove e D q accept answers =
      Sum.inr (accept (pruneRun e D q answers).1) := by
  unfold prunedMove
  rw [h]

theorem prunedMove_of_fire {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {q : ℕ} {accept : List (X × Option Y) → Bool}
    {answers : List (Option Y)} {x : X}
    (h : e ((pruneRun e D q answers).1↓ᵧ) = some x) :
    prunedMove e D q accept answers =
      if (pruneRun e D q answers).1.length < q then Sum.inl x
      else Sum.inr (accept (pruneRun e D q answers).1) := by
  unfold prunedMove
  rw [h]

/-- The pruned move reads only the rebuilt virtual transcript. -/
theorem prunedMove_congr_fst {e : PFunDDS.DDE X Y} {D : Set (List X)}
    {q : ℕ} {accept : List (X × Option Y) → Bool}
    {answers answers' : List (Option Y)}
    (h : (pruneRun e D q answers).1 = (pruneRun e D q answers').1) :
    prunedMove e D q accept answers = prunedMove e D q accept answers' := by
  unfold prunedMove
  rw [h]

/-- Rejection pruning of an environment against a known common domain: the
CR18 distinguisher that simulates `e`, answers rejected queries `⊥` by
itself, forwards only accepted queries, and accepts by `accept` on the
rebuilt virtual `q`-step transcript.  Its verdict is final because a
stopped replay is frozen (`pruneRun_append`). -/
def prunedDDD (e : PFunDDS.DDE X Y) (D : Set (List X)) (q : ℕ)
    (accept : List (X × Option Y) → Bool) : PFunDDS.DDD X Y :=
  ⟨prunedMove e D q accept, by
    intro answers answers' hpre b hb
    obtain ⟨extra, rfl⟩ := hpre
    rcases pruneRun_append e D extra q answers with heq | ⟨j, hj, hblocked⟩
    · have hfst : (pruneRun e D q (answers ++ extra)).1 =
          (pruneRun e D q answers).1 := by
        rw [heq]
      rw [prunedMove_congr_fst hfst]
      exact hb
    · exfalso
      have hfrozen := pruneRun_eq_of_blocked hblocked (Nat.le_of_lt hj)
      obtain ⟨hrest, x, hfire, hacc⟩ := hblocked
      have hlen : (pruneRun e D q answers).1.length < q := by
        rw [hfrozen]
        exact Nat.lt_of_le_of_lt
          (pruneRun_fst_length_le e D j answers) hj
      have hfire' : e ((pruneRun e D q answers).1↓ᵧ) = some x := by
        rw [hfrozen]
        exact hfire
      rw [prunedMove_of_fire hfire', if_pos hlen] at hb
      simp at hb⟩

/-! ## Replay fidelity on a shared-domain atom

Against a deterministic system whose domain is the common `D`, the machine
fed the proper answers of the completed transcript rebuilds that transcript
exactly — rejected steps are resynthesized from `D`, accepted steps consume
the forwarded answers verbatim. -/

section Atom

variable {D : Set (List X)} {s : PFunDDS.DDS X Y}

/-- Replay fidelity: `f` machine steps on the proper answers of the
`f`-step completed transcript rebuild that transcript, passing surplus
answers through untouched. -/
theorem pruneRun_properOutputs (e : PFunDDS.DDE X Y)
    (hdom : PFunDDS.dom s = D) :
    ∀ (f : ℕ) (extra : List (Option Y)),
      pruneRun e D f ((properSteps (PFunDDS.transcript s e f))↓ᵧ ++ extra) =
        (PFunDDS.transcript s e f, extra) := by
  intro f
  induction f with
  | zero => intro extra; rfl
  | succ f ih =>
      intro extra
      rcases he : e ((PFunDDS.transcript s e f)↓ᵧ) with _ | x
      · rw [transcript_succ_stall he, pruneRun_succ, ih extra,
          pruneStep_stall he]
      · by_cases hcand :
            PFunDDS.keptPrefix s ((PFunDDS.transcript s e f)↓ₓ) ++ [x] ∈
              PFunDDS.dom s
        · -- accepted: the machine consumes the forwarded answer verbatim
          have hout : PFunDDS.output (s⊥)
              ((PFunDDS.transcript s e f)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) =
              some (PFunDDS.output s _ hcand) := by
            rw [output_fullyDefined_append]
            exact dif_pos hcand
          have haccD :
              keptTranscriptInputs (PFunDDS.transcript s e f) ++ [x] ∈ D := by
            rw [keptTranscriptInputs_transcript s e f, ← hdom]
            exact hcand
          rw [transcript_succ_fire he, hout, properOutputs_append_some,
            List.append_assoc, List.singleton_append, pruneRun_succ,
            ih (some (PFunDDS.output s _ hcand) :: extra),
            pruneStep_consume he haccD]
        · -- rejected: the machine resynthesizes the `⊥` answer from `D`
          have hout : PFunDDS.output (s⊥)
              ((PFunDDS.transcript s e f)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
            rw [output_fullyDefined_append]
            exact dif_neg hcand
          have hrejD :
              keptTranscriptInputs (PFunDDS.transcript s e f) ++ [x] ∉ D := by
            intro hmem
            apply hcand
            rw [keptTranscriptInputs_transcript s e f, ← hdom] at hmem
            exact hmem
          rw [transcript_succ_fire he, hout, properOutputs_append_none,
            pruneRun_succ, ih extra, pruneStep_reject he hrejD]

/-- Run-ahead to a terminal state: with full fuel the machine passes the
`f`-step transcript and continues through rejected steps only, stopping at
a genuine transcript prefix that is either out of budget, stalled, or
blocked awaiting the next forwarded answer. -/
theorem pruneRun_reaches_terminal (e : PFunDDS.DDE X Y)
    (hdom : PFunDDS.dom s = D) :
    ∀ {f q : ℕ}, f ≤ q →
      ∃ f', f ≤ f' ∧ f' ≤ q ∧
        properSteps (PFunDDS.transcript s e f') =
          properSteps (PFunDDS.transcript s e f) ∧
        pruneRun e D q ((properSteps (PFunDDS.transcript s e f))↓ᵧ) =
          (PFunDDS.transcript s e f', []) ∧
        (f' = q ∨ e ((PFunDDS.transcript s e f')↓ᵧ) = none ∨
          Blocked e D (PFunDDS.transcript s e f', [])) := by
  suffices h : ∀ (gap : ℕ) {f q : ℕ}, q - f = gap → f ≤ q →
      ∃ f', f ≤ f' ∧ f' ≤ q ∧
        properSteps (PFunDDS.transcript s e f') =
          properSteps (PFunDDS.transcript s e f) ∧
        pruneRun e D q ((properSteps (PFunDDS.transcript s e f))↓ᵧ) =
          (PFunDDS.transcript s e f', []) ∧
        (f' = q ∨ e ((PFunDDS.transcript s e f')↓ᵧ) = none ∨
          Blocked e D (PFunDDS.transcript s e f', [])) by
    intro f q hfq
    exact h (q - f) rfl hfq
  intro gap
  induction gap with
  | zero =>
      intro f q hgap hfq
      obtain rfl : f = q := by omega
      refine ⟨f, Nat.le_refl f, Nat.le_refl f, rfl, ?_, Or.inl rfl⟩
      have hbase := pruneRun_properOutputs (s := s) e hdom f []
      rwa [List.append_nil] at hbase
  | succ gap ih =>
      intro f q hgap hfq
      have hflt : f < q := by omega
      have hbase := pruneRun_properOutputs (s := s) e hdom f []
      rw [List.append_nil] at hbase
      rcases he : e ((PFunDDS.transcript s e f)↓ᵧ) with _ | x
      · -- stalled: frozen at the `f`-step transcript
        refine ⟨f, Nat.le_refl f, hfq, rfl, ?_, Or.inr (Or.inl he)⟩
        rw [pruneRun_add e D hfq, hbase]
        exact Function.iterate_fixed (pruneStep_stall he) _
      · by_cases hcand :
            PFunDDS.keptPrefix s ((PFunDDS.transcript s e f)↓ₓ) ++ [x] ∈
              PFunDDS.dom s
        · -- accepted: blocked awaiting the forwarded answer
          have haccD :
              keptTranscriptInputs (PFunDDS.transcript s e f) ++ [x] ∈ D := by
            rw [keptTranscriptInputs_transcript s e f, ← hdom]
            exact hcand
          have hblocked : Blocked e D (PFunDDS.transcript s e f, []) :=
            ⟨rfl, x, he, haccD⟩
          refine ⟨f, Nat.le_refl f, hfq, rfl, ?_, Or.inr (Or.inr hblocked)⟩
          rw [pruneRun_add e D hfq, hbase]
          exact Function.iterate_fixed (pruneStep_blocked hblocked) _
        · -- rejected: the transcript and the machine run ahead in lockstep
          have hout : PFunDDS.output (s⊥)
              ((PFunDDS.transcript s e f)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
            rw [output_fullyDefined_append]
            exact dif_neg hcand
          have hstep : properSteps (PFunDDS.transcript s e (f + 1)) =
              properSteps (PFunDDS.transcript s e f) := by
            rw [transcript_succ_fire he, hout, properSteps_append_none]
          obtain ⟨f', hff', hf'q, hprop, hrun, hterm⟩ :=
            ih (f := f + 1) (q := q) (by omega) (by omega)
          rw [hstep] at hprop hrun
          exact ⟨f', Nat.le_of_succ_le hff', hf'q, hprop, hrun, hterm⟩

/-- The real interaction of the pruned distinguisher with a shared-domain
atom: every real transcript prefix is the proper part of a genuine
completed transcript of the unpruned environment, with the machine settled
at a terminal state on it. -/
theorem transcript_prunedDDD (e : PFunDDS.DDE X Y) (q : ℕ)
    (accept : List (X × Option Y) → Bool)
    (hdom : PFunDDS.dom s = D) :
    ∀ j : ℕ, ∃ f', f' ≤ q ∧
      PFunDDS.transcript s (PFunDDS.ddToDDE (prunedDDD e D q accept)) j =
        properSteps (PFunDDS.transcript s e f') ∧
      pruneRun e D q
          ((PFunDDS.transcript s
            (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ᵧ) =
        (PFunDDS.transcript s e f', []) ∧
      (f' = q ∨ e ((PFunDDS.transcript s e f')↓ᵧ) = none ∨
        Blocked e D (PFunDDS.transcript s e f', [])) := by
  intro j
  induction j with
  | zero =>
      obtain ⟨f', -, hf'q, hprop, hrun, hterm⟩ :=
        pruneRun_reaches_terminal (s := s) e hdom (Nat.zero_le q)
      exact ⟨f', hf'q, hprop.symm, hrun, hterm⟩
  | succ j ihj =>
      obtain ⟨f', hf'q, htranscript, hrun, hterm⟩ := ihj
      rcases he : e ((PFunDDS.transcript s e f')↓ᵧ) with _ | x
      · -- environment stalled: the pruned distinguisher stops too
        have hstall : PFunDDS.ddToDDE (prunedDDD e D q accept)
            ((PFunDDS.transcript s
              (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ᵧ) = none := by
          rw [PFunDDS.ddToDDE_eq_none_iff]
          refine ⟨accept (PFunDDS.transcript s e f'), ?_⟩
          show prunedMove e D q accept _ = _
          rw [prunedMove_of_stall (by rw [hrun]; exact he), hrun]
        rw [transcript_succ_stall hstall]
        exact ⟨f', hf'q, htranscript, hrun, hterm⟩
      · by_cases hlen : (PFunDDS.transcript s e f').length < q
        · -- budget remains: the pruned distinguisher forwards the query
          have hblocked : Blocked e D (PFunDDS.transcript s e f', []) := by
            rcases hterm with hfq | hstallterm | hblocked
            · exfalso
              subst hfq
              have hnone := PFunDDS.transcript_stall_of_length_lt hlen
              rw [hnone] at he
              simp at he
            · rw [hstallterm] at he
              simp at he
            · exact hblocked
          have hf'lt : f' < q := by
            rcases Nat.lt_or_ge f' q with h | h
            · exact h
            · exfalso
              obtain rfl : f' = q := Nat.le_antisymm hf'q h
              have hnone := PFunDDS.transcript_stall_of_length_lt hlen
              rw [hnone] at he
              simp at he
          have hacc' :
              keptTranscriptInputs (PFunDDS.transcript s e f') ++ [x] ∈ D := by
            obtain ⟨-, x', hfire', haccx'⟩ := hblocked
            dsimp only at hfire' haccx'
            rw [he] at hfire'
            rw [Option.some.inj hfire']
            exact haccx'
          have hfire : PFunDDS.ddToDDE (prunedDDD e D q accept)
              ((PFunDDS.transcript s
                (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ᵧ) =
              some x := by
            rw [PFunDDS.ddToDDE_eq_some_iff]
            show prunedMove e D q accept _ = _
            rw [prunedMove_of_fire (by rw [hrun]; exact he), hrun,
              if_pos hlen]
          -- the forwarded query is accepted; both sides record the same
          -- proper answer
          have hkeptreal : PFunDDS.keptPrefix s
              ((PFunDDS.transcript s
                (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ₓ) =
              PFunDDS.keptPrefix s ((PFunDDS.transcript s e f')↓ₓ) := by
            rw [htranscript]
            show PFunDDS.keptPrefix s
                (keptTranscriptInputs (PFunDDS.transcript s e f')) = _
            rw [keptTranscriptInputs_transcript s e f']
            exact PFunDDS.keptPrefix_eq_self_of_mem_or_empty s
              (PFunDDS.keptPrefix_mem_or s _)
          have hcand : PFunDDS.keptPrefix s
              ((PFunDDS.transcript s e f')↓ₓ) ++ [x] ∈ PFunDDS.dom s := by
            rw [hdom]
            rw [← keptTranscriptInputs_transcript s e f']
            exact hacc'
          have hcandreal : PFunDDS.keptPrefix s
              ((PFunDDS.transcript s
                (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ₓ) ++ [x] ∈
              PFunDDS.dom s := by
            rw [hkeptreal]
            exact hcand
          have hanswer : PFunDDS.output (s⊥)
              ((PFunDDS.transcript s
                (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) =
              PFunDDS.output (s⊥)
                ((PFunDDS.transcript s e f')↓ₓ ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp) := by
            rw [output_fullyDefined_append, output_fullyDefined_append,
              dif_pos hcandreal, dif_pos hcand]
            exact congrArg some
              (PFunDDS.output_congr s (by rw [hkeptreal]) _ _)
          obtain ⟨y, hy⟩ : ∃ y, PFunDDS.output (s⊥)
              ((PFunDDS.transcript s e f')↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            rw [output_fullyDefined_append, dif_pos hcand]
            exact ⟨_, rfl⟩
          have hnext : PFunDDS.transcript s
              (PFunDDS.ddToDDE (prunedDDD e D q accept)) j ++
                [(x, PFunDDS.output (s⊥)
                  ((PFunDDS.transcript s
                    (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ₓ ++ [x])
                  (by rw [PFunDDS.dom_fullyDefined]; simp))] =
              properSteps (PFunDDS.transcript s e (f' + 1)) := by
            rw [transcript_succ_fire he, hanswer, hy, htranscript,
              properSteps_append_some]
          obtain ⟨f'', hf''ge, hf''q, hprop, hrun'', hterm''⟩ :=
            pruneRun_reaches_terminal (s := s) e hdom
              (Nat.succ_le_of_lt hf'lt)
          refine ⟨f'', hf''q, ?_, ?_, hterm''⟩
          · rw [transcript_succ_fire hfire, hnext]
            exact hprop.symm
          · rw [transcript_succ_fire hfire, hnext]
            exact hrun''
        · -- budget exhausted: the pruned distinguisher stops
          have hstall : PFunDDS.ddToDDE (prunedDDD e D q accept)
              ((PFunDDS.transcript s
                (PFunDDS.ddToDDE (prunedDDD e D q accept)) j)↓ᵧ) = none := by
            rw [PFunDDS.ddToDDE_eq_none_iff]
            refine ⟨accept (PFunDDS.transcript s e f'), ?_⟩
            show prunedMove e D q accept _ = _
            rw [prunedMove_of_fire (by rw [hrun]; exact he), hrun,
              if_neg hlen]
          rw [transcript_succ_stall hstall]
          exact ⟨f', hf'q, htranscript, hrun, hterm⟩

/-- After `q` real rounds the pruned distinguisher has settled: its
environment view stalls and its value is the accept verdict on the genuine
`q`-step completed transcript of the unpruned environment. -/
theorem prunedDDD_settles (e : PFunDDS.DDE X Y) (q : ℕ)
    (accept : List (X × Option Y) → Bool)
    (hdom : PFunDDS.dom s = D) :
    PFunDDS.ddToDDE (prunedDDD e D q accept)
        ((PFunDDS.transcript s
          (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ) = none ∧
      (prunedDDD e D q accept).val
        ((PFunDDS.transcript s
          (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ) =
        Sum.inr (accept (PFunDDS.transcript s e q)) := by
  obtain ⟨f', hf'q, htranscript, hrun, hterm⟩ :=
    transcript_prunedDDD (s := s) e q accept hdom q
  rcases he : e ((PFunDDS.transcript s e f')↓ᵧ) with _ | x
  · -- environment stalled at `f'`: the virtual transcript is frozen there
    have hfreeze : PFunDDS.transcript s e q = PFunDDS.transcript s e f' :=
      transcript_freeze he hf'q
    have hval : (prunedDDD e D q accept).val
        ((PFunDDS.transcript s
          (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ) =
        Sum.inr (accept (PFunDDS.transcript s e q)) := by
      show prunedMove e D q accept _ = _
      rw [prunedMove_of_stall (by rw [hrun]; exact he), hrun, hfreeze]
    refine ⟨?_, hval⟩
    rw [PFunDDS.ddToDDE_eq_none_iff]
    exact ⟨_, hval⟩
  · -- environment fires: the budget must be exhausted
    have hge : ¬ (PFunDDS.transcript s e f').length < q := by
      intro hlen
      have hreallen : (PFunDDS.transcript s
          (PFunDDS.ddToDDE (prunedDDD e D q accept)) q).length < q := by
        rw [htranscript]
        exact Nat.lt_of_le_of_lt (length_properSteps_le _) hlen
      have hstallreal := PFunDDS.transcript_stall_of_length_lt hreallen
      rw [PFunDDS.ddToDDE_eq_none_iff] at hstallreal
      obtain ⟨b, hb⟩ := hstallreal
      have hb' : prunedMove e D q accept
          ((PFunDDS.transcript s
            (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ) =
          Sum.inr b := hb
      rw [prunedMove_of_fire (by rw [hrun]; exact he), hrun,
        if_pos hlen] at hb'
      simp at hb'
    have hf'eq : f' = q := by
      have hlenle := transcript_length_le (s := s) (e := e) f'
      have := hf'q
      omega
    have hval : (prunedDDD e D q accept).val
        ((PFunDDS.transcript s
          (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ) =
        Sum.inr (accept (PFunDDS.transcript s e q)) := by
      show prunedMove e D q accept _ = _
      rw [prunedMove_of_fire (by rw [hrun]; exact he), hrun, if_neg hge,
        hf'eq]
    refine ⟨?_, hval⟩
    rw [PFunDDS.ddToDDE_eq_none_iff]
    exact ⟨_, hval⟩

/-- The pruned verdict is the CR18 accept verdict at the unpruned
environment's `q`-step transcript — atom by atom on the shared domain. -/
theorem verdict_prunedDDD_iff (e : PFunDDS.DDE X Y) (q : ℕ)
    (accept : List (X × Option Y) → Bool)
    (hdom : PFunDDS.dom s = D) :
    PFunDDS.verdict (prunedDDD e D q accept) s ↔
      accept (PFunDDS.transcript s e q) = true := by
  obtain ⟨hstall, hval⟩ := prunedDDD_settles (s := s) e q accept hdom
  rw [PFunDDS.Cache.verdict_iff_at_stall _ s q hstall, hval]
  constructor
  · intro h
    exact Sum.inr.inj h
  · intro h
    rw [h]

/-- The `(q+1)`-truncation used by the strict-test bridge changes nothing:
the pruned interaction stops within `q` real rounds by itself. -/
theorem verdict_truncDDD_prunedDDD_iff (e : PFunDDS.DDE X Y) (q : ℕ)
    (accept : List (X × Option Y) → Bool)
    (hdom : PFunDDS.dom s = D) :
    PFunDDS.verdict (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept)) s ↔
      accept (PFunDDS.transcript s e q) = true := by
  obtain ⟨hstall, hval⟩ := prunedDDD_settles (s := s) e q accept hdom
  have hlenq : ((PFunDDS.transcript s
      (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ).length < q + 1 := by
    rw [transcriptOutputs_length]
    exact Nat.lt_succ_of_le (transcript_length_le q)
  have htr := PFunDDS.transcript_truncDDD (q + 1) (prunedDDD e D q accept) s
    (Nat.le_succ q)
  have hstall' : PFunDDS.ddToDDE
      (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept))
      ((PFunDDS.transcript s
        (PFunDDS.ddToDDE
          (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept))) q)↓ᵧ) =
      none := by
    rw [htr, PFunDDS.ddToDDE_truncDDD_of_lt hlenq]
    exact hstall
  rw [PFunDDS.Cache.verdict_iff_at_stall _ s q hstall', htr,
    PFunDDS.truncDDD_val_of_lt hlenq, hval]
  constructor
  · intro h
    exact Sum.inr.inj h
  · intro h
    rw [h]

/-- The pruned interaction never receives the completion symbol on a
shared-domain atom: exactly the run-level compatibility the strict-test
bridge needs, with no totality anywhere. -/
theorem properInteraction_truncDDD_prunedDDD (e : PFunDDS.DDE X Y) (q : ℕ)
    (accept : List (X × Option Y) → Bool)
    (hdom : PFunDDS.dom s = D) :
    StrictContextTotal.ProperInteraction
      (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept)) s := by
  have hbounded : ∀ fuel, fuel ≤ q → none ∉
      (PFunDDS.transcript s
        (PFunDDS.ddToDDE
          (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept))) fuel)↓ᵧ := by
    intro fuel hfuel
    rw [PFunDDS.transcript_truncDDD (q + 1) (prunedDDD e D q accept) s
      (Nat.le_succ_of_le hfuel)]
    obtain ⟨f', -, htranscript, -, -⟩ :=
      transcript_prunedDDD (s := s) e q accept hdom fuel
    rw [htranscript]
    exact none_notMem_properSteps_outputs _
  intro fuel
  rcases Nat.lt_or_ge q fuel with hfuel | hfuel
  case inr => exact hbounded fuel hfuel
  · obtain ⟨hstall, -⟩ := prunedDDD_settles (s := s) e q accept hdom
    have hlenq : ((PFunDDS.transcript s
        (PFunDDS.ddToDDE (prunedDDD e D q accept)) q)↓ᵧ).length < q + 1 := by
      rw [transcriptOutputs_length]
      exact Nat.lt_succ_of_le (transcript_length_le q)
    have hstall' : PFunDDS.ddToDDE
        (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept))
        ((PFunDDS.transcript s
          (PFunDDS.ddToDDE
            (PFunDDS.truncDDD (q + 1) (prunedDDD e D q accept))) q)↓ᵧ) =
        none := by
      rw [PFunDDS.transcript_truncDDD (q + 1) (prunedDDD e D q accept) s
        (Nat.le_succ q), PFunDDS.ddToDDE_truncDDD_of_lt hlenq]
      exact hstall
    rw [transcript_freeze hstall' (Nat.le_of_lt hfuel)]
    exact hbounded q (Nat.le_refl q)

end Atom

/-! ## Law level: the pruned strict test reads the transcript mass -/

/-- On a shared-domain law, the strict test compiled from the pruned
distinguisher accepts with exactly the transcript mass of the *unpruned*
environment — the equality the total-law bridge
(`acceptMass_testOfDDE_eq_transcriptMass_of_total`) grants only under
totality. -/
theorem acceptMass_pruned_eq_transcriptMass (e : PFunDDS.DDE X Y) (q : ℕ)
    (accept : List (X × Option Y) → Bool) (law : PFunPDS X Y)
    {D : Set (List X)} (hdom : PFunPDS.HasFixedDomain law D) :
    acceptMass
        (StrictContextTotal.testOfTruncDDD (q + 1) (prunedDDD e D q accept))
        law =
      (transcriptDist law e q).mass fun t => accept t = true := by
  unfold acceptMass transcriptDist
  rw [Dist.mass_fTransform]
  apply StrictContextTotal.mass_congr_support law
  intro s hs
  exact (StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_proper
      (q + 1) (prunedDDD e D q accept) s
      (properInteraction_truncDDD_prunedDDD e q accept (hdom s hs))).trans
    (verdict_truncDDD_prunedDDD_iff e q accept (hdom s hs))

/-- Every transcript distance of shared-domain laws is realized by a strict
test: prune the environment by the common domain and accept on the excess
set. -/
theorem ofReal_delta_transcriptDist_le_maxEDist_of_sharedDomain
    (left right : PFunPDS X Y) (leftNN : left.NonNeg) {D : Set (List X)}
    (leftDom : PFunPDS.HasFixedDomain left D)
    (rightDom : PFunPDS.HasFixedDomain right D)
    (e : PFunDDS.DDE X Y) (q : ℕ) :
    ENNReal.ofReal
        (RandomSystems.CR18.δ
          (transcriptDist right e q)
          (transcriptDist left e q) : Real) ≤
      maxEDist left right := by
  classical
  let accept : List (X × Option Y) → Bool := fun t =>
    decide ((transcriptDist left e q) t < (transcriptDist right e q) t)
  let test := StrictContextTotal.testOfTruncDDD (q + 1)
    (prunedDDD e D q accept)
  have leftAcceptance :=
    acceptMass_pruned_eq_transcriptMass e q accept left leftDom
  have rightAcceptance :=
    acceptMass_pruned_eq_transcriptMass e q accept right rightDom
  have acceptPredicate : (fun t => accept t = true) =
      fun t =>
        (transcriptDist left e q) t < (transcriptDist right e q) t := by
    funext t
    simp only [accept, decide_eq_true_eq]
  rw [acceptPredicate] at leftAcceptance rightAcceptance
  rw [RandomSystems.CR18.δ_eq_mass_sub_mass _
      (transcriptDist_nonNeg leftNN e q),
    ← rightAcceptance, ← leftAcceptance]
  calc
    ENNReal.ofReal
          (acceptMass test right - acceptMass test left) ≤
        ENNReal.ofReal
          (abs (acceptMass test right - acceptMass test left)) :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = edist (acceptMass test right) (acceptMass test left) := by
      rw [edist_dist, Real.dist_eq]
    _ = edist (acceptMass test left) (acceptMass test right) :=
      edist_comm _ _
    _ ≤ maxEDist left right :=
      le_iSup
        (fun current : Test X Y =>
          edist (acceptMass current left) (acceptMass current right)) test

/-- CR18 maximal advantage is attained by strict tests on shared-domain
laws. -/
theorem ofReal_maxAdvantage_le_maxEDist_of_sharedDomain
    (left right : PFunPDS X Y)
    (leftNN : left.NonNeg) (rightNN : right.NonNeg) {D : Set (List X)}
    (leftDom : PFunPDS.HasFixedDomain left D)
    (rightDom : PFunPDS.HasFixedDomain right D) :
    ENNReal.ofReal Δ(left, right) ≤ maxEDist left right := by
  obtain ⟨e, q, attainment⟩ := exists_adv_eq_δ_transcriptDist right leftNN
  rw [← adv_eq_maxAdvantage_swap rightNN leftNN, attainment]
  exact ofReal_delta_transcriptDist_le_maxEDist_of_sharedDomain
    left right leftNN leftDom rightDom e q

/-- **Rejection pruning (RP).**  On normalized laws whose support atoms all
present one common domain — the objects Lanzenberger Def 2.14 admits — the
strict contextual metric *equals* CR18 maximal distinguishing advantage.
CR18 Def 3.3's costless rejection buys nothing here because rejection is a
public function of the query history, so the pruned distinguisher realizes
the advantage strictly.  Together with the unconditional
`maxEDist_le_maxAdvantage` this scopes the `≤`-only rule: `≤` on the
unrestricted carrier, `=` on every object the sources admit. -/
theorem maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain
    (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist)
    {D : Set (List X)}
    (leftDom : PFunPDS.HasFixedDomain left D)
    (rightDom : PFunPDS.HasFixedDomain right D) :
    maxEDist left right = ENNReal.ofReal Δ(left, right) :=
  le_antisymm
    (StrictContextAdvantage.maxEDist_le_maxAdvantage
      left right leftProb rightProb)
    (ofReal_maxAdvantage_le_maxEDist_of_sharedDomain
      left right leftProb.nonNeg rightProb.nonNeg leftDom rightDom)

/-! ## Restrictions of total laws are shared-domain

CBC's `θ_r` block filter and the `[q]` query filter are `filterDom` images
of total laws, so their stalls are input-determined and the equality
applies: `Δ`-stated bounds on them carry no metric slack. -/

/-- A same-predicate restriction of a total law is shared-domain: every
atom stalls exactly on the histories the public predicate rejects. -/
theorem sharedDomainOn_filterDom (P : List X → Prop) [DecidablePred P]
    (hP : PrefixClosed P) (law : PFunPDS X Y)
    (total : CondEquiv.TotalOnNonempty law) :
    PFunPDS.HasFixedDomain (PFunPDS.filterDom P hP law)
      {l : List X | l ≠ [] ∧ P l} := by
  intro s hs
  obtain ⟨atom, hatom, rfl⟩ :=
    Dist.mem_support_fTransform (PFunDDS.filterDom P hP) law hs
  ext l
  constructor
  · rintro ⟨hdom, hPl⟩
    exact ⟨fun hnil => PFunDDS.empty_not_mem atom (hnil ▸ hdom), hPl⟩
  · rintro ⟨hnil, hPl⟩
    exact ⟨total atom hatom l hnil, hPl⟩

/-- **No metric slack on restricted laws (LOOSE).**  For same-predicate
`filterDom` restrictions of total laws — CBC's `θ_r` and every `[q]` query
filter — the strict metric attains the CR18 advantage exactly, so a
`Δ`-stated bound on such a pair is as tight for the strict metric as it is
for `Δ`: the completion's free probe is invisible when the stall pattern is a
public function of the query history. -/
theorem maxEDist_filterDom_eq_ofReal_maxAdvantage
    (P : List X → Prop) [DecidablePred P]
    (hP : PrefixClosed P) (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist)
    (leftTotal : CondEquiv.TotalOnNonempty left)
    (rightTotal : CondEquiv.TotalOnNonempty right) :
    maxEDist (PFunPDS.filterDom P hP left) (PFunPDS.filterDom P hP right) =
      ENNReal.ofReal
        Δ(PFunPDS.filterDom P hP left, PFunPDS.filterDom P hP right) :=
  maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain
    (PFunPDS.filterDom P hP left) (PFunPDS.filterDom P hP right)
    ((PFunPDS.isProbDist_filterDom_iff P hP leftProb.nonNeg).mpr leftProb)
    ((PFunPDS.isProbDist_filterDom_iff P hP rightProb.nonNeg).mpr rightProb)
    (sharedDomainOn_filterDom P hP left leftTotal)
    (sharedDomainOn_filterDom P hP right rightTotal)

end

end RandomSystems.CR18.StrictContextSharedDomain
