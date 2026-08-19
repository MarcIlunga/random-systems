/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PFunConverter
import RandomSystems.CausalApply

/-!
# Protocol converters and the realization theorem for CR18 Definition 3.9

A large class of converters — Maurer's "simple converters" (Def 4.20's `b` is
described as one) and every converter used by the applications so far — is
*outer-memoryless*: what it does inside one outer round depends only on the
current outside input and the inner answers received in that round.  Such a
converter is presented by a **protocol step function**

`step : U → List Y → X ⊕ V`

("given the outer input `u` and the inner answers received so far in this
round, either issue the next inner query `Sum.inl x` or answer outside
`Sum.inr v`").  This is exactly the converter presentation that
`RandomSystems.CausalApply` (the function-native, transcript-free apply used
by the HCTR2 development) takes as input.

This module closes the gap between the two realizations of CR18 Def 3.9:

* `DDC.ofStep step` — the protocol step function as an honest **DDC**
  (Definition 3.8 object): a DDS over the converter alphabets whose value at a
  converter history is the move `step` prescribes at the round state that
  history describes.  Histories that are not protocol traces (or contain a
  blocked `⊥` answer — `ofStep` converters are *strict*) are outside the
  domain.
* **Realization theorem** `apply_ofStep`:

  `(ofStep step) ·ᶜ S = CausalApply.applyG step S.1`

  the paper-facing converter application of Definition 3.9 (`DDC.apply`, the
  `PFun.fix` of one connection step against `s⊥`) is **extensionally equal**
  to the purely functional composition `applyG` (finite unrolling of the step
  function against the system's partial function).  This is the precise sense
  in which *applying a converter to a system is a (nontrivial) composition of
  the converter's function and the system's function*, and it retroactively
  certifies the `CausalApply` surface as a faithful realization of Def 3.9.

Downstream, `SimpleConverter`-style corollaries fall out by *computing*
`applyG` (an easy list induction) instead of reasoning about interaction
transcripts: see `simple_apply` (`αs = d ∘ s ∘ map c` — for a simple converter
the applied system is literally `S(c(input))` post-processed by `d`) and the
two-round interactive example `feedback`.
-/

namespace RandomSystems.CR18

/-! ### `CausalApply` support: `≤`-monotonicity and `applyRawAt` membership -/

namespace CausalApply

variable {U X Y V : Type*}

/-- `driveG` is monotone up to any larger fuel. -/
theorem driveG_mono_le (innerStep : List Y → X ⊕ V) (S : PFunDDS.Raw X Y)
    {fuel fuel' : ℕ} {xs : List X} {ys : List Y} {r : V × List X}
    (hle : fuel ≤ fuel') (h : r ∈ driveG innerStep S fuel xs ys) :
    r ∈ driveG innerStep S fuel' xs ys := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact driveG_mono innerStep S ih

/-- `driveOuter` is monotone up to any larger fuel. -/
theorem driveOuter_mono_le (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y)
    {fuel fuel' : ℕ} {xs : List X} {us : List U} {r : List V × List X}
    (hle : fuel ≤ fuel') (h : r ∈ driveOuter step S fuel xs us) :
    r ∈ driveOuter step S fuel' xs us := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact driveOuter_mono step S ih

/-- Membership characterization of the per-fuel applied raw function, matching
`DDC.mem_apply_iff` on the transcript side. -/
theorem mem_applyRawAt_iff (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y)
    (fuel : ℕ) (us : List U) (v : V) :
    v ∈ applyRawAt step S fuel us ↔
      ∃ r ∈ driveOuter step S fuel [] us, r.1.getLast? = some v := by
  simp only [applyRawAt, Part.mem_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  cases r.1.getLast? with
  | none => simp
  | some w => simp [Part.mem_some_iff, eq_comm]

/-- **Bounded-round fuel normalization**: when `step` issues an inner query
exactly while its answer list is shorter than the advertised round budget
`count`, every terminating round already terminates at fuel
`count query - answers.length + 1`. -/
theorem driveG_mem_at_count_succ
    (step : U → List Y → X ⊕ V) (count : U → ℕ)
    (issues_iff :
      ∀ query answers,
        (∃ inner, step query answers = Sum.inl inner) ↔
          answers.length < count query)
    (query : U) (system : PFunDDS.Raw X Y)
    {fuel : ℕ} {innerQueries : List X} {innerAnswers : List Y}
    {result : V × List X}
    (member :
      result ∈ driveG (step query) system fuel innerQueries innerAnswers) :
    result ∈
      driveG (step query) system (count query - innerAnswers.length + 1)
        innerQueries innerAnswers := by
  induction fuel generalizing innerQueries innerAnswers result with
  | zero =>
      simpa [driveG] using member
  | succ remaining ih =>
      simp only [driveG] at member ⊢
      cases stepEquation : step query innerAnswers with
      | inl innerQuery =>
          simp only [stepEquation, Part.mem_bind_iff] at member ⊢
          obtain ⟨innerAnswer, answerMember, resultMember⟩ := member
          refine ⟨innerAnswer, answerMember, ?_⟩
          have answersShort : innerAnswers.length < count query :=
            (issues_iff query innerAnswers).mp ⟨innerQuery, stepEquation⟩
          have normalizedMember := ih resultMember
          have fuelEquation :
              count query - (innerAnswers ++ [innerAnswer]).length + 1 =
                count query - innerAnswers.length := by
            simp only [List.length_append, List.length_singleton]
            omega
          rwa [fuelEquation] at normalizedMember
      | inr outerAnswer =>
          simpa only [stepEquation, Part.mem_some_iff] using member

/-- **Uniform fuel normalization** for the bounded causal driver: a uniform
bound on the per-round budget normalizes every successful outer run to the
single fuel `bound + 1`.  This is the bridge from a fixed-fuel driver
receipt to the fuel-free `applyG`. -/
theorem driveOuter_mem_at_uniform_count_succ
    (step : U → List Y → X ⊕ V) (count : U → ℕ)
    (issues_iff :
      ∀ query answers,
        (∃ inner, step query answers = Sum.inl inner) ↔
          answers.length < count query)
    (bound : ℕ) (count_le : ∀ query, count query ≤ bound)
    (system : PFunDDS.Raw X Y) :
    ∀ {queries : List U} {fuel : ℕ} {innerQueries : List X}
      {result : List V × List X},
      result ∈ driveOuter step system fuel innerQueries queries →
        result ∈ driveOuter step system (bound + 1) innerQueries queries := by
  intro queries
  induction queries with
  | nil =>
      intro fuel innerQueries result member
      simpa [driveOuter] using member
  | cons query rest ih =>
      intro fuel innerQueries result member
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at member ⊢
      obtain ⟨roundResult, roundMember, tailResult, tailMember, rfl⟩ := member
      have normalizedRound :=
        driveG_mem_at_count_succ step count issues_iff query system
          roundMember
      have normalizedRound' :
          roundResult ∈
            driveG (step query) system (count query + 1) innerQueries [] := by
        simpa using normalizedRound
      have boundedRound :
          roundResult ∈
            driveG (step query) system (bound + 1) innerQueries [] :=
        driveG_mono_le (step query) system
          (by simpa using Nat.add_le_add_right (count_le query) 1)
          normalizedRound'
      exact ⟨roundResult, boundedRound, tailResult, ih tailMember, rfl⟩

end CausalApply

namespace PFunConverter

open scoped PFunDDS

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

namespace DDC

/-! ### Protocol traces

A converter history (`List (CIn U Y)`) is a **protocol trace** of `step` when
it is the record of a legal interaction: it starts with an outside input, every
inner answer is a defined `some y` arriving while the round's step prescribes a
query, and a new outside input arrives only once the round's step has answered.
`runFrom`/`run` parse a history left-to-right into the current round state
`(u, ys)` — the outside input being processed and the inner answers received
so far — returning `none` exactly on non-traces.  These parsers are the
*private* representation device for `ofStep`; all paper-facing statements are
extensional DDS equalities. -/

namespace OfStep

/-- Left-to-right trace parser, from the round state `(u, ys)`.  Returns the
round state after the remaining history `l`, or `none` if `l` is not a legal
continuation. -/
def runFrom (step : U → List Y → X ⊕ V) :
    U → List Y → List (CIn U Y) → Option (U × List Y)
  | u, ys, [] => some (u, ys)
  | u, ys, Sum.inl (InLabel.outside, u') :: rest =>
      match step u ys with
      | Sum.inr _ => runFrom step u' [] rest
      | Sum.inl _ => none
  | u, ys, Sum.inr (InLabel.inside, some y) :: rest =>
      match step u ys with
      | Sum.inl _ => runFrom step u (ys ++ [y]) rest
      | Sum.inr _ => none
  | _, _, _ :: _ => none

/-- Trace parser from the initial (empty) state: a legal history must begin
with an outside input. -/
def run (step : U → List Y → X ⊕ V) : List (CIn U Y) → Option (U × List Y)
  | [] => none
  | Sum.inl (InLabel.outside, u) :: rest => runFrom step u [] rest
  | _ :: _ => none

theorem runFrom_append (step : U → List Y → X ⊕ V) :
    ∀ (l₁ l₂ : List (CIn U Y)) (u : U) (ys : List Y),
      runFrom step u ys (l₁ ++ l₂) =
        (runFrom step u ys l₁).bind fun s => runFrom step s.1 s.2 l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ u ys; simp [runFrom]
  | cons a rest ih =>
      intro l₂ u ys
      rcases a with ⟨lbl, u'⟩ | ⟨lbl, oy⟩
      · cases lbl
        · simp [runFrom]
        · cases hstep : step u ys with
          | inl x => simp [runFrom, hstep]
          | inr v => simpa [runFrom, hstep] using ih l₂ u' []
      · cases lbl
        · cases oy with
          | none => simp [runFrom]
          | some y =>
              cases hstep : step u ys with
              | inl x => simpa [runFrom, hstep] using ih l₂ u (ys ++ [y])
              | inr v => simp [runFrom, hstep]
        · simp [runFrom]

theorem run_append (step : U → List Y → X ⊕ V) (l₁ l₂ : List (CIn U Y))
    (hne : l₁ ≠ []) :
    run step (l₁ ++ l₂) = (run step l₁).bind fun s => runFrom step s.1 s.2 l₂ := by
  cases l₁ with
  | nil => exact absurd rfl hne
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩
      · cases lbl
        · simp [run]
        · simpa [run] using runFrom_append step rest l₂ u []
      · cases lbl <;> simp [run]

/-- Trace prefixes of traces are traces: the parse of a nonempty prefix of a
parsing history parses. -/
theorem run_isSome_of_append (step : U → List Y → X ⊕ V)
    {l₁ l₂ : List (CIn U Y)} (hne : l₁ ≠ [])
    (h : (run step (l₁ ++ l₂)).isSome) : (run step l₁).isSome := by
  rw [run_append step l₁ l₂ hne] at h
  cases hrun : run step l₁ with
  | none => rw [hrun] at h; simp at h
  | some s => simp

/-- Extending a parsed history by a *new outside input* parses to the fresh
round state `(u', [])` exactly when the current round has answered. -/
theorem run_snoc_out (step : U → List Y → X ⊕ V) {c : List (CIn U Y)}
    {u : U} {ys : List Y} {v : V} (hc : run step c = some (u, ys))
    (hstep : step u ys = Sum.inr v) (u' : U) :
    run step (c ++ [Sum.inl (InLabel.outside, u')]) = some (u', []) := by
  have hne : c ≠ [] := by rintro rfl; simp [run] at hc
  rw [run_append step c _ hne, hc]
  simp [runFrom, hstep]

/-- Extending a parsed history by a *defined inner answer* extends the round
state exactly when the current round's step is a query. -/
theorem run_snoc_in (step : U → List Y → X ⊕ V) {c : List (CIn U Y)}
    {u : U} {ys : List Y} {x : X} (hc : run step c = some (u, ys))
    (hstep : step u ys = Sum.inl x) (y : Y) :
    run step (c ++ [Sum.inr (InLabel.inside, some y)]) = some (u, ys ++ [y]) := by
  have hne : c ≠ [] := by rintro rfl; simp [run] at hc
  rw [run_append step c _ hne, hc]
  simp [runFrom, hstep]

/-- A blocked answer `⊥` kills the trace: `ofStep` converters are strict. -/
theorem run_snoc_in_none (step : U → List Y → X ⊕ V) (c : List (CIn U Y)) :
    run step (c ++ [Sum.inr (InLabel.inside, (none : Option Y))]) = none := by
  cases hc : run step c with
  | none =>
      cases hne : c with
      | nil => simp [run]
      | cons a rest =>
          rw [← hne, run_append step c _ (by simp [hne]), hc]
          rfl
  | some s =>
      have hne : c ≠ [] := by rintro rfl; simp [run] at hc
      rw [run_append step c _ hne, hc]
      cases hstep : step s.1 s.2 with
      | inl x => simp [runFrom]
      | inr v => simp [runFrom]

/-- The first outside input opens the first round. -/
theorem run_singleton_out (step : U → List Y → X ⊕ V) (u : U) :
    run step [Sum.inl (InLabel.outside, u)] = some (u, []) := rfl

/-- A converter history is **round-ready** when a fresh outside input may
arrive: it is empty, or it parses to a round whose step has answered. -/
def RoundReady (step : U → List Y → X ⊕ V) (c : List (CIn U Y)) : Prop :=
  c = [] ∨ ∃ u ys v, run step c = some (u, ys) ∧ step u ys = Sum.inr v

theorem run_out_of_roundReady (step : U → List Y → X ⊕ V)
    {c : List (CIn U Y)} (h : RoundReady step c) (u : U) :
    run step (c ++ [Sum.inl (InLabel.outside, u)]) = some (u, []) := by
  rcases h with rfl | ⟨u₀, ys₀, v₀, hrun, hstep⟩
  · simp [run_singleton_out]
  · exact run_snoc_out step hrun hstep u

end OfStep

/-- The move prescribed by a protocol step, in converter-output alphabet. -/
def moveOf (m : X ⊕ V) : COut V X :=
  match m with
  | Sum.inl x => Sum.inr (InLabel.inside, x)
  | Sum.inr v => Sum.inl (InLabel.outside, v)

@[simp] theorem moveOf_inl (x : X) :
    moveOf (Sum.inl x : X ⊕ V) = Sum.inr (InLabel.inside, x) := rfl

@[simp] theorem moveOf_inr (v : V) :
    moveOf (Sum.inr v : X ⊕ V) = Sum.inl (InLabel.outside, v) := rfl

/-- **The protocol converter.**  A protocol step function
`step : U → List Y → X ⊕ V` as an honest CR18 Definition 3.8 DDC: at a
converter history that is a protocol trace with current round state `(u, ys)`,
the converter's move is `step u ys` (an inner query or an outside answer);
non-traces — including any trace containing a blocked `⊥` answer, `ofStep`
converters are strict — are outside the domain. -/
def ofStep (step : U → List Y → X ⊕ V) : DDC U V X Y :=
  ⟨fun l =>
      (⟨(OfStep.run step l).isSome,
        fun h => moveOf (step ((OfStep.run step l).get h).1
          ((OfStep.run step l).get h).2)⟩ :
        Part (COut V X)),
    ⟨by simp [OfStep.run], by
      intro l₁ l₂ hpre hne hdom
      obtain ⟨t, rfl⟩ := hpre
      exact OfStep.run_isSome_of_append step hne hdom⟩⟩

theorem mem_ofStep_iff (step : U → List Y → X ⊕ V) (l : List (CIn U Y))
    (o : COut V X) :
    o ∈ (ofStep step).1 l ↔
      ∃ u ys, OfStep.run step l = some (u, ys) ∧ o = moveOf (step u ys) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨((OfStep.run step l).get h).1, ((OfStep.run step l).get h).2,
      (Option.some_get h).symm, rfl⟩
  · rintro ⟨u, ys, hrun, rfl⟩
    have h : (OfStep.run step l).isSome := by rw [hrun]; rfl
    have hget : (OfStep.run step l).get h = (u, ys) :=
      Option.some.inj ((Option.some_get h).trans hrun)
    refine ⟨h, ?_⟩
    show moveOf (step ((OfStep.run step l).get h).1 ((OfStep.run step l).get h).2)
        = moveOf (step u ys)
    rw [hget]

theorem ofStep_mem_of_run (step : U → List Y → X ⊕ V) {l : List (CIn U Y)}
    {u : U} {ys : List Y} (hrun : OfStep.run step l = some (u, ys)) :
    moveOf (step u ys) ∈ (ofStep step).1 l :=
  (mem_ofStep_iff step l _).mpr ⟨u, ys, hrun, rfl⟩

/-! ### Connection-step membership (CR18 Definition 3.9, one step) -/

theorem connStep_mem_inl (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    (st : List (CIn U Y) × List X) (b : V × (List (CIn U Y) × List X)) :
    Sum.inl b ∈ connStep α S st ↔
      Sum.inl (InLabel.outside, b.1) ∈ α.1 st.1 ∧ b.2 = st := by
  rw [connStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hb⟩
    rcases o with ⟨lbl, v0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;> simp_all
  · rintro ⟨hmem, hst⟩
    exact ⟨Sum.inl (InLabel.outside, b.1), hmem, by rw [← hst]; cases b; simp⟩

theorem connStep_mem_inr (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    (st st' : List (CIn U Y) × List X) :
    Sum.inr st' ∈ connStep α S st ↔
      ∃ x, Sum.inr (InLabel.inside, x) ∈ α.1 st.1 ∧
        st' = (st.1 ++ [Sum.inr (InLabel.inside,
            PFunDDS.output (S⊥) (st.2 ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp))],
          st.2 ++ [x]) := by
  rw [connStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hst'⟩
    rcases o with ⟨lbl, v0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;>
      simp only [Part.mem_some_iff, Part.notMem_none, reduceCtorEq,
        Sum.inr.injEq] at hst'
    exact ⟨x0, ho, hst'⟩
  · rintro ⟨x, hmem, rfl⟩
    exact ⟨Sum.inr (InLabel.inside, x), hmem, by simp⟩

/-- Off-trace states are dead: the connection step of a protocol converter is
undefined at a converter history that does not parse. -/
theorem connStep_ofStep_not_mem (step : U → List Y → X ⊕ V) (S : PFunDDS.DDS X Y)
    {st : List (CIn U Y) × List X} (h : OfStep.run step st.1 = none)
    (o : (V × (List (CIn U Y) × List X)) ⊕ (List (CIn U Y) × List X)) :
    o ∉ connStep (ofStep step) S st := by
  intro ho
  rw [connStep, Part.mem_bind_iff] at ho
  obtain ⟨o', ho', -⟩ := ho
  rw [mem_ofStep_iff] at ho'
  obtain ⟨u, ys, hrun, -⟩ := ho'
  rw [h] at hrun
  simp at hrun

/-! ### The inner round: `resolve` against `ofStep` ↔ `driveG` against the step

CR18 Def 3.9's inner loop (`resolve`, the least fixed point of `connStep`
against `s⊥`) coincides, on protocol traces, with the finite unrolling
`CausalApply.driveG` of the step function against the system's raw partial
function.  The invariant `xs ∈ dom S ∨ xs = []` says the recorded inner
history is live; strictness of `ofStep` (a `⊥` answer kills the trace)
guarantees it is maintained. -/

/-- Forward simulation: a terminating `driveG` run yields the corresponding
`resolve` membership, and the resulting converter history is a parsed trace of
the finished round. -/
theorem resolve_ofStep_of_driveG (step : U → List Y → X ⊕ V) (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {c : List (CIn U Y)} {xs : List X} {ys : List Y} {u : U}
      {p : V × List X},
      OfStep.run step c = some (u, ys) →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      p ∈ CausalApply.driveG (step u) S.1 fuel xs ys →
      ∃ c' ys',
        OfStep.run step c' = some (u, ys') ∧ step u ys' = Sum.inr p.1 ∧
        (p.2 ∈ PFunDDS.dom S ∨ p.2 = []) ∧
        (p.1, (c', p.2)) ∈ resolve (ofStep step) S (c, xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c xs ys u p _ _ hp
      simp [CausalApply.driveG] at hp
  | succ n ih =>
      intro c xs ys u p hrun hxs hp
      simp only [CausalApply.driveG] at hp
      cases hstep : step u ys with
      | inr v =>
          rw [hstep] at hp
          simp only [Part.mem_some_iff] at hp
          subst hp
          refine ⟨c, ys, hrun, hstep, hxs, ?_⟩
          have hmem : Sum.inl (InLabel.outside, v) ∈ (ofStep step).1 c := by
            have hmv := ofStep_mem_of_run step hrun
            rw [hstep] at hmv
            simpa using hmv
          exact resolve_out (ofStep step) S hmem
      | inl x =>
          rw [hstep] at hp
          rw [Part.mem_bind_iff] at hp
          obtain ⟨y, hy, hp⟩ := hp
          have hdomx : xs ++ [x] ∈ PFunDDS.dom S := by
            rw [PFunDDS.dom_def, PFun.mem_dom]
            exact ⟨y, hy⟩
          have hout : PFunDDS.output (S⊥) (xs ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            rw [PFunDDS.output_fullyDefined_append_of_mem S xs x hxs hdomx]
            have hyv : PFunDDS.output S (xs ++ [x]) hdomx = y :=
              Part.mem_unique (Part.get_mem _) hy
            rw [hyv]
          have hquery : Sum.inr (InLabel.inside, x) ∈ (ofStep step).1 c := by
            have hmv := ofStep_mem_of_run step hrun
            rw [hstep] at hmv
            simpa using hmv
          have hrun' : OfStep.run step (c ++ [Sum.inr (InLabel.inside, some y)])
              = some (u, ys ++ [y]) := OfStep.run_snoc_in step hrun hstep y
          obtain ⟨c', ys', hrun'', hstep'', hxs'', hres⟩ :=
            ih hrun' (Or.inl hdomx) hp
          refine ⟨c', ys', hrun'', hstep'', hxs'', ?_⟩
          rw [resolve_in (ofStep step) S hquery]
          simp only [hout]
          exact hres

/-- Backward simulation: a terminating `resolve` run against `ofStep` on a
parsed trace yields a terminating `driveG` run at some fuel, with matching
answer and inner history, and the final converter history parses to the
finished round. -/
theorem driveG_of_resolve_ofStep (step : U → List Y → X ⊕ V) (S : PFunDDS.DDS X Y)
    {u : U} {st : List (CIn U Y) × List X}
    {r : V × (List (CIn U Y) × List X)}
    (hr : r ∈ resolve (ofStep step) S st) :
    ∀ ys : List Y, OfStep.run step st.1 = some (u, ys) →
      (st.2 ∈ PFunDDS.dom S ∨ st.2 = []) →
      ∃ fuel ys',
        (r.1, r.2.2) ∈ CausalApply.driveG (step u) S.1 fuel st.2 ys ∧
        OfStep.run step r.2.1 = some (u, ys') ∧ step u ys' = Sum.inr r.1 ∧
        (r.2.2 ∈ PFunDDS.dom S ∨ r.2.2 = []) := by
  refine PFun.fixInduction hr (C := fun st₀ => ∀ ys : List Y,
      OfStep.run step st₀.1 = some (u, ys) →
      (st₀.2 ∈ PFunDDS.dom S ∨ st₀.2 = []) →
      ∃ fuel ys',
        (r.1, r.2.2) ∈ CausalApply.driveG (step u) S.1 fuel st₀.2 ys ∧
        OfStep.run step r.2.1 = some (u, ys') ∧ step u ys' = Sum.inr r.1 ∧
        (r.2.2 ∈ PFunDDS.dom S ∨ r.2.2 = [])) ?_
  intro st₀ hfix IH ys hrun hxs
  rw [PFun.mem_fix_iff] at hfix
  rcases hfix with hstop | ⟨st₁, hstep₁, hrec⟩
  · rw [connStep_mem_inl] at hstop
    obtain ⟨hmove, hsteq⟩ := hstop
    rw [mem_ofStep_iff] at hmove
    obtain ⟨u₀, ys₀, hrun₀, hmv⟩ := hmove
    rw [hrun] at hrun₀
    obtain ⟨rfl, rfl⟩ : u = u₀ ∧ ys = ys₀ := by
      have hpair := Option.some.inj hrun₀
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    cases hstep₀ : step u ys with
    | inl x =>
        rw [hstep₀] at hmv
        simp at hmv
    | inr v =>
        rw [hstep₀] at hmv
        simp only [moveOf_inr, Sum.inl.injEq, Prod.mk.injEq, true_and] at hmv
        refine ⟨1, ys, ?_, ?_, ?_, ?_⟩
        · simp only [CausalApply.driveG, hstep₀, Part.mem_some_iff]
          rw [hmv, hsteq]
        · rw [hsteq]; exact hrun
        · rw [hstep₀, hmv]
        · rw [hsteq]; exact hxs
  · have hstep₁' := hstep₁
    rw [connStep_mem_inr] at hstep₁'
    obtain ⟨x, hquery, hst₁⟩ := hstep₁'
    rw [mem_ofStep_iff] at hquery
    obtain ⟨u₀, ys₀, hrun₀, hmv⟩ := hquery
    rw [hrun] at hrun₀
    obtain ⟨rfl, rfl⟩ : u = u₀ ∧ ys = ys₀ := by
      have hpair := Option.some.inj hrun₀
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    cases hstep₀ : step u ys with
    | inr v =>
        rw [hstep₀] at hmv
        simp at hmv
    | inl x' =>
        rw [hstep₀] at hmv
        simp only [moveOf_inl, Sum.inr.injEq, Prod.mk.injEq, true_and] at hmv
        subst hmv
        rcases Option.eq_none_or_eq_some
            (PFunDDS.output (S⊥) (st₀.2 ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp)) with hans | ⟨y, hans⟩
        · -- blocked answer: the successor state is dead, contradicting `hrec`
          exfalso
          rw [hst₁] at hrec
          simp only [hans] at hrec
          have hdead : OfStep.run step
              (st₀.1 ++ [Sum.inr (InLabel.inside, (none : Option Y))]) = none :=
            OfStep.run_snoc_in_none step st₀.1
          rw [PFun.mem_fix_iff] at hrec
          rcases hrec with hbad | ⟨a, hbad, -⟩
          · exact connStep_ofStep_not_mem step S hdead _ hbad
          · exact connStep_ofStep_not_mem step S hdead _ hbad
        · obtain ⟨hdomx, houtS⟩ :=
            PFunDDS.mem_of_output_fullyDefined_append_eq_some S st₀.2 x hxs hans
          have hy : y ∈ S.1 (st₀.2 ++ [x]) := by
            rw [← houtS]
            exact Part.get_mem _
          have hrun₁ : OfStep.run step st₁.1 = some (u, ys ++ [y]) := by
            rw [hst₁]
            simp only [hans]
            exact OfStep.run_snoc_in step hrun hstep₀ y
          have hxs₁ : st₁.2 ∈ PFunDDS.dom S ∨ st₁.2 = [] := by
            rw [hst₁]
            exact Or.inl hdomx
          obtain ⟨fuel, ys', hdrive, hrun', hstep', hxs'⟩ :=
            IH st₁ hstep₁ (ys ++ [y]) hrun₁ hxs₁
          refine ⟨fuel + 1, ys', ?_, hrun', hstep', hxs'⟩
          simp only [CausalApply.driveG, hstep₀]
          rw [Part.mem_bind_iff]
          refine ⟨y, hy, ?_⟩
          have hst₁2 : st₁.2 = st₀.2 ++ [x] := by rw [hst₁]
          rw [← hst₁2]
          exact hdrive

/-! ### The outer iteration and the realization theorem -/

/-- Forward simulation, outer level: a `driveOuter` run yields the
corresponding `driveFrom` run of CR18 Def 3.9 against `ofStep`. -/
theorem driveFrom_ofStep_of_driveOuter (step : U → List Y → X ⊕ V)
    (S : PFunDDS.DDS X Y) {fuel : ℕ} :
    ∀ {us : List U} {c : List (CIn U Y)} {xs : List X} {p : List V × List X},
      OfStep.RoundReady step c → (xs ∈ PFunDDS.dom S ∨ xs = []) →
      p ∈ CausalApply.driveOuter step S.1 fuel xs us →
      ∃ c', (p.1, (c', p.2)) ∈ driveFrom (ofStep step) S (c, xs) us := by
  intro us
  induction us with
  | nil =>
      intro c xs p _ _ hp
      simp only [CausalApply.driveOuter, Part.mem_some_iff] at hp
      subst hp
      exact ⟨c, by simp [driveFrom]⟩
  | cons u rest ih =>
      intro c xs p hready hxs hp
      simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hp
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hp
      have hrun : OfStep.run step (c ++ [Sum.inl (InLabel.outside, u)])
          = some (u, []) := OfStep.run_out_of_roundReady step hready u
      obtain ⟨c₁, ys₁, hrun₁, hstep₁, hxs₁, hres⟩ :=
        resolve_ofStep_of_driveG step S hrun hxs hr₁
      obtain ⟨c₂, htail⟩ := ih (Or.inr ⟨u, ys₁, r₁.1, hrun₁, hstep₁⟩) hxs₁ hrr
      refine ⟨c₂, ?_⟩
      simp only [driveFrom, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r₁.1, (c₁, r₁.2)), hres, (rr.1, (c₂, rr.2)), htail, rfl⟩

/-- Backward simulation, outer level: a `driveFrom` run of CR18 Def 3.9
against `ofStep` yields a `driveOuter` run at some fuel. -/
theorem driveOuter_of_driveFrom_ofStep (step : U → List Y → X ⊕ V)
    (S : PFunDDS.DDS X Y) :
    ∀ {us : List U} {c : List (CIn U Y)} {xs : List X}
      {q : List V × (List (CIn U Y) × List X)},
      OfStep.RoundReady step c → (xs ∈ PFunDDS.dom S ∨ xs = []) →
      q ∈ driveFrom (ofStep step) S (c, xs) us →
      ∃ fuel, (q.1, q.2.2) ∈ CausalApply.driveOuter step S.1 fuel xs us := by
  intro us
  induction us with
  | nil =>
      intro c xs q _ _ hq
      simp only [driveFrom, Part.mem_some_iff] at hq
      subst hq
      exact ⟨0, by simp [CausalApply.driveOuter]⟩
  | cons u rest ih =>
      intro c xs q hready hxs hq
      simp only [driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at hq
      obtain ⟨r, hres, rr, htail, rfl⟩ := hq
      have hrun : OfStep.run step (c ++ [Sum.inl (InLabel.outside, u)])
          = some (u, []) := OfStep.run_out_of_roundReady step hready u
      obtain ⟨fuel₁, ys₁, hdrive, hrun₁, hstep₁, hxs₁⟩ :=
        driveG_of_resolve_ofStep step S hres [] hrun hxs
      obtain ⟨fuel₂, htail₂⟩ := ih (Or.inr ⟨u, ys₁, r.1, hrun₁, hstep₁⟩) hxs₁ htail
      refine ⟨max fuel₁ fuel₂, ?_⟩
      simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r.1, r.2.2),
        CausalApply.driveG_mono_le _ _ (le_max_left _ _) hdrive,
        (rr.1, rr.2.2),
        CausalApply.driveOuter_mono_le _ _ (le_max_right _ _) htail₂, rfl⟩

/-- **Realization theorem for CR18 Definition 3.9.**  For a protocol converter,
the paper-facing converter application (`DDC.apply`, the `PFun.fix` of the
connection step against `s⊥`) *is* the purely functional composition of the
converter's step function with the system's partial function
(`CausalApply.applyG`, the fuel-free finite unrolling):

`(ofStep step) ·ᶜ S = applyG step S.1`.

Applying a converter to a system therefore produces exactly the `(U,V)`-DDS
whose partial function is the (nontrivial) composition of the two component
functions — and every `CausalApply`-based development (HCTR2 in particular) is
retroactively a faithful instance of Definition 3.9. -/
theorem apply_ofStep (step : U → List Y → X ⊕ V) (S : PFunDDS.DDS X Y) :
    (ofStep step ·ᶜ S) = CausalApply.applyG step S.1 := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (ofStep step ·ᶜ S).1 = applyRaw (ofStep step) S from rfl,
    show (CausalApply.applyG step S.1).1 = CausalApply.applyRaw step S.1 from rfl,
    mem_apply_iff, CausalApply.mem_applyRaw]
  constructor
  · rintro ⟨r, hr, hlast⟩
    obtain ⟨fuel, hmem⟩ :=
      driveOuter_of_driveFrom_ofStep step S (Or.inl rfl) (Or.inr rfl) hr
    exact ⟨fuel, (CausalApply.mem_applyRawAt_iff step S.1 fuel us v).mpr
      ⟨(r.1, r.2.2), hmem, hlast⟩⟩
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.mem_applyRawAt_iff] at hv
    obtain ⟨r, hmem, hlast⟩ := hv
    obtain ⟨c', hr⟩ :=
      driveFrom_ofStep_of_driveOuter step S (Or.inl rfl) (Or.inr rfl) hmem
    exact ⟨(r.1, (c', r.2)), hr, hlast⟩

/-! ### Maurer's simple converters: `(simple c d) S = map d ∘ S ∘ map c`

A **simple converter** (Maurer's vocabulary, cf. CR18 Def 4.20 "`b` is the
simple converter that …") translates each outside query by `c : U → X`,
forwards it, and translates the answer back by `d : Y → V` — one inner query
per outer query, no state.  The recovery theorem `simple_apply` computes its
Def 3.9 application *against an arbitrary system* `S` as a genuine equality of
partial functions, domains included:

`((simple c d) ·ᶜ S) us = map d (S (map c us))`

— for `d = id` the applied system is literally `S(c(input))`. -/

/-- Protocol of the simple converter: with no answer yet, query `c u`; once an
answer `y` arrives, reply `d y` outside. -/
def simpleStep (c : U → X) (d : Y → V) : U → List Y → X ⊕ V := fun u ys =>
  match ys with
  | [] => Sum.inl (c u)
  | y :: _ => Sum.inr (d y)

/-- The simple converter with query translation `c` and answer translation `d`,
as a CR18 Definition 3.8 DDC. -/
def simple (c : U → X) (d : Y → V) : DDC U V X Y :=
  ofStep (simpleStep c d)

/-- One simple-converter round, closed form: query `c u`, answer `d y`. -/
theorem driveG_simpleStep (c : U → X) (d : Y → V) (S : PFunDDS.Raw X Y)
    (u : U) (n : ℕ) (xs : List X) :
    CausalApply.driveG (simpleStep c d u) S (n + 1 + 1) xs [] =
      (S (xs ++ [c u])).map fun y => (d y, xs ++ [c u]) := by
  simp only [CausalApply.driveG, simpleStep, List.nil_append]
  exact Part.bind_some_eq_map _ _

/-- Any terminating simple-converter round has the closed form. -/
theorem driveG_simpleStep_mem {c : U → X} {d : Y → V} {S : PFunDDS.Raw X Y}
    {u : U} {fuel : ℕ} {xs : List X} {p : V × List X}
    (hp : p ∈ CausalApply.driveG (simpleStep c d u) S fuel xs []) :
    ∃ y ∈ S (xs ++ [c u]), p = (d y, xs ++ [c u]) := by
  rcases fuel with _ | _ | n
  · simp [CausalApply.driveG] at hp
  · simp [CausalApply.driveG, simpleStep] at hp
  · rw [driveG_simpleStep c d S u n xs, Part.mem_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨y, hy, rfl⟩

/-- Definedness (forward) run of the simple converter over a whole outer
history: if `S` accepts the translated history, the fuel-2 `driveOuter` run
exists, threads exactly the translated history, and its last output is the
translated last answer of `S`. -/
theorem driveOuter_simpleStep_of_dom (c : U → X) (d : Y → V)
    (S : PFunDDS.DDS X Y) :
    ∀ (us : List U) (xs : List X),
      (xs ++ us.map c ∈ PFunDDS.dom S ∨ us = []) →
      ∃ vs, (vs, xs ++ us.map c) ∈
          CausalApply.driveOuter (simpleStep c d) S.1 2 xs us ∧
        ∀ h : xs ++ us.map c ∈ PFunDDS.dom S, us ≠ [] →
          vs.getLast? = some (d (PFunDDS.output S (xs ++ us.map c) h)) := by
  intro us
  induction us with
  | nil =>
      intro xs _
      refine ⟨[], ?_, fun _ hne => absurd rfl hne⟩
      simp [CausalApply.driveOuter]
  | cons u rest ih =>
      intro xs hdom
      have hdom' : xs ++ (u :: rest).map c ∈ PFunDDS.dom S := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hnext : xs ++ [c u] ∈ PFunDDS.dom S := by
        refine PFunDDS.prefix_closed S ⟨rest.map c, by simp⟩ (by simp) hdom'
      have hy : PFunDDS.output S (xs ++ [c u]) hnext ∈ S.1 (xs ++ [c u]) :=
        Part.get_mem _
      have hround : (d (PFunDDS.output S (xs ++ [c u]) hnext), xs ++ [c u]) ∈
          CausalApply.driveG (simpleStep c d u) S.1 2 xs [] := by
        rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, driveG_simpleStep, Part.mem_map_iff]
        exact ⟨_, hy, rfl⟩
      have hdomRest : (xs ++ [c u]) ++ rest.map c ∈ PFunDDS.dom S ∨ rest = [] :=
        Or.inl (by simpa [List.append_assoc] using hdom')
      obtain ⟨vs', hmem', hlast'⟩ := ih (xs ++ [c u]) hdomRest
      refine ⟨d (PFunDDS.output S (xs ++ [c u]) hnext) :: vs', ?_, ?_⟩
      · simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        refine ⟨(d (PFunDDS.output S (xs ++ [c u]) hnext), xs ++ [c u]), hround,
          (vs', (xs ++ [c u]) ++ rest.map c), hmem', ?_⟩
        simp [List.append_assoc]
      · intro h hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen := CausalApply.driveOuter_length (simpleStep c d) S.1 2
                (xs ++ [c u]) rest hmem'
              rw [hvs] at hlen
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
            subst hrest
            rw [List.getLast?_singleton]
            exact congrArg (fun t => some (d t))
              (PFunDDS.output_congr S (by simp) hnext h)
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen := CausalApply.driveOuter_length (simpleStep c d) S.1 2
                (xs ++ [c u]) rest hmem'
              rw [hvs] at hlen
              intro hnil
              rw [hnil] at hlen
              simp at hlen
            have h' : (xs ++ [c u]) ++ rest.map c ∈ PFunDDS.dom S := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg (fun t => some (d t))
              (PFunDDS.output_congr S (by simp) h' h)

/-- Backward run analysis of the simple converter: any terminating
`driveOuter` run threads exactly the translated history, and (on a nonempty
history) certifies `S`-definedness with the translated last answer. -/
theorem driveOuter_simpleStep_mem_imp (c : U → X) (d : Y → V)
    (S : PFunDDS.DDS X Y) :
    ∀ (us : List U) (xs : List X) {fuel : ℕ} {r : List V × List X},
      r ∈ CausalApply.driveOuter (simpleStep c d) S.1 fuel xs us →
      r.2 = xs ++ us.map c ∧
        (us ≠ [] → ∃ h : xs ++ us.map c ∈ PFunDDS.dom S,
          r.1.getLast? = some (d (PFunDDS.output S (xs ++ us.map c) h))) := by
  intro us
  induction us with
  | nil =>
      intro xs fuel r hr
      simp only [CausalApply.driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs fuel r hr
      simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨y, hy, rfl⟩ := driveG_simpleStep_mem hr₁
      obtain ⟨hthread, htail⟩ := ih (xs ++ [c u]) hrr
      have hnext : xs ++ [c u] ∈ PFunDDS.dom S := by
        rw [PFunDDS.dom_def, PFun.mem_dom]
        exact ⟨y, hy⟩
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [CausalApply.driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨by simpa using hnext, ?_⟩
          simp only [List.getLast?_singleton, Option.some.injEq]
          have hout : PFunDDS.output S (xs ++ [c u]) hnext = y :=
            Part.mem_unique (Part.get_mem _) hy
          rw [PFunDDS.output_congr S (l₂ := xs ++ [c u]) (by simp) _ hnext, hout]
      | cons r0 rs0 =>
          obtain ⟨h', hlast'⟩ := htail (by simp [hrest])
          refine ⟨by simpa [List.append_assoc, hrest] using h', ?_⟩
          have hlen := CausalApply.driveOuter_length (simpleStep c d) S.1 fuel
            (xs ++ [c u]) rest hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlen
              simp [hrest] at hlen
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              exact congrArg (fun t => some (d t))
                (PFunDDS.output_congr S (by simp [hrest]) h' _)

/-- **Simple-converter recovery (CR18 Def 3.9, computed).**  Applying the
simple converter to *any* system `S` yields exactly the composed partial
function — domains included:

`((simple c d) ·ᶜ S) (u₁ … u_k) = d (S (c u₁ … c u_k))`.

Validity of `S` is what collapses the round-by-round domain conditions to the
single condition `map c us ∈ dom S` (prefix closure). -/
theorem simple_apply (c : U → X) (d : Y → V) (S : PFunDDS.DDS X Y)
    (us : List U) :
    (simple c d ·ᶜ S).1 us = (S.1 (us.map c)).map d := by
  rw [simple, apply_ofStep]
  apply Part.ext
  intro v
  rw [show (CausalApply.applyG (simpleStep c d) S.1).1
      = CausalApply.applyRaw (simpleStep c d) S.1 from rfl,
    CausalApply.mem_applyRaw, Part.mem_map_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := CausalApply.driveOuter_length (simpleStep c d) S.1 fuel [] [] hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨-, htail⟩ := driveOuter_simpleStep_mem_imp c d S us [] hr
    obtain ⟨h, hlast'⟩ := htail hne
    rw [hlast] at hlast'
    refine ⟨PFunDDS.output S (us.map c) (by simpa using h), Part.get_mem _, ?_⟩
    have hv' := Option.some.inj hlast'
    rw [hv']
    exact congrArg d (PFunDDS.output_congr S (by simp) _ h)
  · rintro ⟨y, hy, rfl⟩
    have hdom : us.map c ∈ PFunDDS.dom S := by
      rw [PFunDDS.dom_def, PFun.mem_dom]
      exact ⟨y, hy⟩
    have hne : us ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem S (by simpa using hdom)
    obtain ⟨vs, hmem, hlastf⟩ :=
      driveOuter_simpleStep_of_dom c d S us [] (Or.inl (by simpa using hdom))
    refine ⟨2, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    refine ⟨(vs, [] ++ us.map c), hmem, ?_⟩
    have hout : PFunDDS.output S (us.map c) hdom = y :=
      Part.mem_unique (Part.get_mem _) hy
    have houtNil : PFunDDS.output S ([] ++ us.map c) (by simpa using hdom) = y := by
      rw [PFunDDS.output_congr S (l₂ := us.map c) (by simp) _ hdom]
      exact hout
    rw [hlastf (by simpa using hdom) hne, houtNil]

/-- `d = id`: the applied system is *literally* `S(c(input))`. -/
theorem simple_id_apply (c : U → X) (S : PFunDDS.DDS X Y) (us : List U) :
    (simple c (id : Y → Y) ·ᶜ S).1 us = S.1 (us.map c) := by
  rw [simple_apply]
  exact Part.map_id' (fun _ => rfl) _

/-- Domain form of the recovery: `us` is accepted by `(simple c d) S` exactly
when `S` accepts the translated history. -/
theorem simple_apply_dom (c : U → X) (d : Y → V) (S : PFunDDS.DDS X Y)
    (us : List U) :
    us ∈ PFunDDS.dom (simple c d ·ᶜ S) ↔ us.map c ∈ PFunDDS.dom S := by
  show ((simple c d ·ᶜ S).1 us).Dom ↔ (S.1 (us.map c)).Dom
  rw [simple_apply]
  exact Iff.rfl

/-- **The identity converter law**: the simple converter with identity
translations is the identity of the converter action — the unit of the
(memoryless) converter monoid acting on systems. -/
theorem simple_id_id_apply (S : PFunDDS.DDS X Y) :
    (simple (id : X → X) (id : Y → Y) ·ᶜ S) = S := by
  apply Subtype.ext
  funext us
  rw [simple_apply, List.map_id]
  exact Part.map_id' (fun _ => rfl) _

/-- **Simple applications compose into simple applications** (the memoryless
action law, DESIGN §10.5): two stacked simple converters are one simple
converter of the composed translations — the applied system never leaves the
simple class, and the proof is pure algebra over `simple_apply` (no
transcripts, no fixed points). -/
theorem simple_simple_apply {W : Type*} {V' : Type*} (c : U → X) (d : Y → V)
    (c' : W → U) (d' : V → V') (S : PFunDDS.DDS X Y) :
    (simple c' d' ·ᶜ (simple c d ·ᶜ S))
      = (simple (c ∘ c') (d' ∘ d) ·ᶜ S) := by
  apply Subtype.ext
  funext ws
  rw [simple_apply, simple_apply, simple_apply]
  rw [Part.map_map, List.map_map]

/-- Membership characterization of a stateless function evaluator: an answer
is the function applied to the last input. -/
theorem mem_functionEvaluator_iff (f : X → Y) (l : List X) (y : Y) :
    y ∈ (PFunDDS.functionEvaluator f).1 l ↔
      ∃ x, l.getLast? = some x ∧ y = f x := by
  constructor
  · rintro ⟨hne, rfl⟩
    exact ⟨l.getLast hne, List.getLast?_eq_some_getLast hne, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hne : l ≠ [] := by rintro rfl; simp at hx
    refine ⟨hne, ?_⟩
    have hlx : l.getLast hne = x := by
      have h := List.getLast?_eq_some_getLast hne
      rw [hx] at h
      exact (Option.some.inj h).symm
    show f (l.getLast hne) = f x
    rw [hlx]

/-- Stateless instance of the recovery: a simple converter applied to a
function evaluator is the function evaluator of the composed function,
`(simple c d) ·ᶜ ⌜f⌝ = ⌜d ∘ f ∘ c⌝`. -/
theorem simple_functionEvaluator (c : U → X) (d : Y → V) (f : X → Y) :
    (simple c d ·ᶜ PFunDDS.functionEvaluator f)
      = PFunDDS.functionEvaluator (fun u => d (f (c u))) := by
  apply Subtype.ext
  funext us
  rw [show (simple c d ·ᶜ PFunDDS.functionEvaluator f).1 us
      = ((PFunDDS.functionEvaluator f).1 (us.map c)).map d from
    simple_apply c d (PFunDDS.functionEvaluator f) us]
  apply Part.ext
  intro v
  rw [Part.mem_map_iff, mem_functionEvaluator_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_functionEvaluator_iff] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [List.getLast?_map] at hx
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨f (c u), ?_, rfl⟩
    rw [mem_functionEvaluator_iff]
    refine ⟨c u, ?_, rfl⟩
    rw [List.getLast?_map, hu]
    rfl

/-! ### An interactive (two-round) converter: query, feed back, query again

`feedback g` is a filter that makes **two adaptive inner queries per outer
query**: it forwards the outer query `x`, feeds the answer `y₁` back through
`g : Y → X` as a second query, and answers the second reply `y₂` outside.
This is the minimal genuinely interactive converter: the second query depends
on the system's first answer.

* `feedback_apply_singleton` computes its application against an **arbitrary
  (stateful) system**: the applied partial function at `[x]` is the *bind* of
  `S` against itself along `g` — the round structure as a composition formula.
* `feedback_functionEvaluator` computes the full applied system on a stateless
  evaluator: `feedback g ·ᶜ ⌜f⌝ = ⌜f ∘ g ∘ f⌝`. -/

/-- Protocol of the feedback converter: query `x`, then `g y₁`, then answer
`y₂`. -/
def feedbackStep (g : Y → X) : X → List Y → X ⊕ Y := fun x ys =>
  match ys with
  | [] => Sum.inl x
  | [y] => Sum.inl (g y)
  | _ :: y' :: _ => Sum.inr y'

/-- The feedback converter as a CR18 filter (Def 3.8 object over `(X,Y)`). -/
def feedback (g : Y → X) : Filter X Y :=
  ofStep (feedbackStep g)

/-- One feedback round, closed form: two chained queries, second one adaptive. -/
theorem driveG_feedbackStep (g : Y → X) (S : PFunDDS.Raw X Y) (x : X) (n : ℕ)
    (xs : List X) :
    CausalApply.driveG (feedbackStep g x) S (n + 1 + 1 + 1) xs [] =
      (S (xs ++ [x])).bind fun y₁ =>
        (S ((xs ++ [x]) ++ [g y₁])).map fun y₂ => (y₂, (xs ++ [x]) ++ [g y₁]) := by
  simp only [CausalApply.driveG, feedbackStep, List.nil_append, List.cons_append]
  congr 1
  funext y₁
  exact Part.bind_some_eq_map _ _

/-- Any terminating feedback round has the closed form. -/
theorem driveG_feedbackStep_mem {g : Y → X} {S : PFunDDS.Raw X Y} {x : X}
    {fuel : ℕ} {xs : List X} {p : Y × List X}
    (hp : p ∈ CausalApply.driveG (feedbackStep g x) S fuel xs []) :
    ∃ y₁ ∈ S (xs ++ [x]), ∃ y₂ ∈ S ((xs ++ [x]) ++ [g y₁]),
      p = (y₂, (xs ++ [x]) ++ [g y₁]) := by
  rcases fuel with _ | _ | _ | n
  · simp [CausalApply.driveG] at hp
  · simp [CausalApply.driveG, feedbackStep] at hp
  · simp [CausalApply.driveG, feedbackStep] at hp
  · rw [driveG_feedbackStep g S x n xs, Part.mem_bind_iff] at hp
    obtain ⟨y₁, hy₁, hp⟩ := hp
    rw [Part.mem_map_iff] at hp
    obtain ⟨y₂, hy₂, rfl⟩ := hp
    exact ⟨y₁, hy₁, y₂, hy₂, rfl⟩

/-- **Interactive rounds, general system.**  On one outer query, the applied
system is the bind of `S` against itself along `g`: query `x`, get `y₁`, query
`g y₁`, answer `y₂`.  An equality of partial functions on an arbitrary
*stateful* `S` — the adaptivity is visible in the second query's history
`[x, g y₁]`. -/
theorem feedback_apply_singleton (g : Y → X) (S : PFunDDS.DDS X Y) (x : X) :
    (feedback g ·ᶜ S).1 [x] = (S.1 [x]).bind fun y₁ => S.1 [x, g y₁] := by
  rw [feedback, apply_ofStep]
  apply Part.ext
  intro v
  rw [show (CausalApply.applyG (feedbackStep g) S.1).1
      = CausalApply.applyRaw (feedbackStep g) S.1 from rfl,
    CausalApply.mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.applyRawAt_singleton, Part.mem_map_iff] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := driveG_feedbackStep_mem hp
    rw [Part.mem_bind_iff]
    exact ⟨y₁, by simpa using hy₁, by simpa using hy₂⟩
  · intro hv
    rw [Part.mem_bind_iff] at hv
    obtain ⟨y₁, hy₁, hy₂⟩ := hv
    refine ⟨0 + 1 + 1 + 1, ?_⟩
    rw [CausalApply.applyRawAt_singleton, Part.mem_map_iff]
    refine ⟨(v, ([] ++ [x]) ++ [g y₁]), ?_, rfl⟩
    rw [driveG_feedbackStep, Part.mem_bind_iff]
    refine ⟨y₁, by simpa using hy₁, ?_⟩
    rw [Part.mem_map_iff]
    exact ⟨v, by simpa using hy₂, rfl⟩

/-- **CR18 Def 3.8's round bound**, as a named predicate: the step answers within `R` inner
queries on every outer input. -/
abbrev AnswersWithin (step : U → List Y → X ⊕ V) (R : ℕ) : Prop :=
  ∀ (u : U) (ys : List Y), R ≤ ys.length → ∃ v, step u ys = Sum.inr v

/-- **The round-driven outer closed form** (generic).  If each outer round `u` against the
stateless evaluator `⌜f⌝` computes `g u` while issuing the inner calls `calls u` — within a
per-round fuel `B u ≤ Bmax` — then the outer drive over any query list computes `map g` and
issues `flatMap calls`, at the uniform fuel `Bmax`.  (The per-protocol content is exactly the
one-round loop lemma `hround`; this and `apply_ofStep_functionEvaluator_of_round` package the
rest of the realization argument once, for every protocol.) -/
theorem driveOuter_functionEvaluator_of_round {U' : Type*} (step : U' → List Y → X ⊕ V)
    (f : X → Y) (g : U' → V) (calls : U' → List X) (B : U' → ℕ) {Bmax : ℕ}
    (hB : ∀ u, B u ≤ Bmax)
    (hround : ∀ (u : U') (n : ℕ) (xs : List X),
      CausalApply.driveG (step u) (PFunDDS.functionEvaluator f).1 (n + B u + 1) xs []
        = Part.some (g u, xs ++ calls u)) (n : ℕ) :
    ∀ (us : List U') (xs : List X),
      CausalApply.driveOuter step (PFunDDS.functionEvaluator f).1 (n + Bmax + 1) xs us
        = Part.some (us.map g, xs ++ us.flatMap calls) := by
  intro us
  induction us with
  | nil => intro xs; simp [CausalApply.driveOuter]
  | cons u rest ih =>
      intro xs
      have harith : (n + (Bmax - B u)) + B u + 1 = n + Bmax + 1 := by
        have := hB u; omega
      have hG := hround u (n + (Bmax - B u)) xs
      rw [harith] at hG
      simp only [CausalApply.driveOuter, hG, Part.bind_some, ih, Part.map_some]
      simp [List.append_assoc]

/-- **The round-driven realization equation** (generic): a step converter whose rounds against
`⌜f⌝` compute `g` is, applied by Def 3.9, exactly the evaluator `⌜g⌝` — a full DDS equality
across all outer histories, domains included. -/
theorem apply_ofStep_functionEvaluator_of_round {U' : Type*} (step : U' → List Y → X ⊕ V)
    (f : X → Y) (g : U' → V) (calls : U' → List X) (B : U' → ℕ) {Bmax : ℕ}
    (hB : ∀ u, B u ≤ Bmax)
    (hround : ∀ (u : U') (n : ℕ) (xs : List X),
      CausalApply.driveG (step u) (PFunDDS.functionEvaluator f).1 (n + B u + 1) xs []
        = Part.some (g u, xs ++ calls u)) :
    (ofStep step ·ᶜ PFunDDS.functionEvaluator f) = PFunDDS.functionEvaluator g := by
  rw [apply_ofStep]
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (CausalApply.applyG step (PFunDDS.functionEvaluator f).1).1
      = CausalApply.applyRaw step (PFunDDS.functionEvaluator f).1 from rfl,
    CausalApply.mem_applyRaw, mem_functionEvaluator_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    have hv' : v ∈ CausalApply.applyRawAt step
        (PFunDDS.functionEvaluator f).1 (fuel + Bmax + 1) us :=
      CausalApply.applyRawAt_mono_le _ _ (by omega) hv
    rw [CausalApply.mem_applyRawAt_iff] at hv'
    obtain ⟨r, hr, hlast⟩ := hv'
    rw [driveOuter_functionEvaluator_of_round step f g calls B hB hround fuel us [],
      Part.mem_some_iff] at hr
    subst hr
    rw [List.getLast?_map] at hlast
    obtain ⟨u, hu, hfu⟩ := Option.map_eq_some_iff.mp hlast
    exact ⟨u, hu, hfu.symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨0 + Bmax + 1, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    refine ⟨(us.map g, [] ++ us.flatMap calls), ?_, ?_⟩
    · rw [driveOuter_functionEvaluator_of_round step f g calls B hB hround 0 us []]
      exact Part.mem_some _
    · rw [List.getLast?_map, hu]
      rfl

/-- A round-bounded step drives the `f`-evaluator to completion: `driveG` is defined at any
fuel exceeding the remaining round budget. -/
theorem driveG_functionEvaluator_dom_of_answersWithin {U' : Type*}
    (step : U' → List Y → X ⊕ V) {R : ℕ} (hR : AnswersWithin step R) (f : X → Y) (u : U') :
    ∀ (k : ℕ) (ys : List Y) (xs : List X), R ≤ ys.length + k →
      (CausalApply.driveG (step u) (PFunDDS.functionEvaluator f).1 (k + 1) xs ys).Dom := by
  intro k
  induction k with
  | zero =>
      intro ys xs hk
      obtain ⟨v, hv⟩ := hR u ys (by omega)
      simp only [CausalApply.driveG, hv]
      exact trivial
  | succ k ih =>
      intro ys xs hk
      rcases hs : step u ys with x | v
      · have hih := ih (ys ++ [f x]) (xs ++ [x])
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        generalize k + 1 = k' at hih ⊢
        simp only [CausalApply.driveG, hs, CausalApply.functionEvaluator_raw_append,
          Part.bind_some]
        exact hih
      · simp only [CausalApply.driveG, hs]
        exact trivial

/-- A round-bounded step drives the `f`-evaluator through any outer query list. -/
theorem driveOuter_functionEvaluator_dom_of_answersWithin {U' : Type*}
    (step : U' → List Y → X ⊕ V) {R : ℕ} (hR : AnswersWithin step R) (f : X → Y) :
    ∀ (us : List U') (xs : List X),
      (CausalApply.driveOuter step (PFunDDS.functionEvaluator f).1 (R + 1) xs us).Dom := by
  intro us
  induction us with
  | nil => intro xs; exact trivial
  | cons u rest ih =>
      intro xs
      have hG := driveG_functionEvaluator_dom_of_answersWithin step hR f u R [] xs (by simp)
      obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp hG
      obtain ⟨rr, hrr⟩ := Part.dom_iff_mem.mp (ih r.2)
      exact Part.dom_iff_mem.mpr ⟨(r.1 :: rr.1, rr.2),
        Part.mem_bind_iff.mpr ⟨r, hr, Part.mem_map _ hrr⟩⟩

/-- **Round-bounded converters preserve totality on function evaluators**: the Def 3.9
application of a Def 3.8 round-bounded step to `⌜f⌝` is defined on every nonempty history. -/
theorem mem_dom_apply_ofStep_functionEvaluator_of_answersWithin {U' : Type*}
    (step : U' → List Y → X ⊕ V) {R : ℕ} (hR : AnswersWithin step R) (f : X → Y)
    {us : List U'} (hne : us ≠ []) :
    us ∈ PFunDDS.dom (ofStep step ·ᶜ PFunDDS.functionEvaluator f) := by
  rw [apply_ofStep]
  obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp
    (driveOuter_functionEvaluator_dom_of_answersWithin step hR f us [])
  have hAt := CausalApply.mem_dom_applyGAt_of_driveOuter step
    (PFunDDS.functionEvaluator f).1 (R + 1) us hne r hr
  rw [PFunDDS.dom, PFun.mem_dom] at hAt ⊢
  obtain ⟨v, hv⟩ := hAt
  refine ⟨v, ?_⟩
  rw [CausalApply.applyG_toPFun, CausalApply.mem_applyRaw]
  rw [CausalApply.applyGAt_toPFun] at hv
  exact ⟨R + 1, hv⟩

/-- The feedback converter over a stateless evaluator, all outer queries at
once: each round contributes `f (g (f x))` and appends `[x, g (f x)]` to the
inner history. -/
theorem driveG_feedbackStep_functionEvaluator_round (g : Y → X) (f : X → Y) (x : X)
    (n : ℕ) (xs : List X) :
    CausalApply.driveG (feedbackStep g x) (PFunDDS.functionEvaluator f).1 (n + 2 + 1) xs []
      = Part.some (f (g (f x)), xs ++ [x, g (f x)]) := by
  rw [show n + 2 + 1 = n + 1 + 1 + 1 from rfl, driveG_feedbackStep,
    CausalApply.functionEvaluator_raw_append f xs x, Part.bind_some,
    CausalApply.functionEvaluator_raw_append f (xs ++ [x]) (g (f x)), Part.map_some]
  simp

theorem driveOuter_feedbackStep_functionEvaluator (g : Y → X) (f : X → Y)
    (n : ℕ) :
    ∀ (us : List X) (xs : List X),
      CausalApply.driveOuter (feedbackStep g) (PFunDDS.functionEvaluator f).1
          (n + 1 + 1 + 1) xs us =
        Part.some (us.map fun x => f (g (f x)),
          xs ++ us.flatMap fun x => [x, g (f x)]) :=
  driveOuter_functionEvaluator_of_round (feedbackStep g) f (fun x => f (g (f x)))
    (fun x => [x, g (f x)]) (fun _ => 2) (fun _ => le_rfl)
    (driveG_feedbackStep_functionEvaluator_round g f) n

/-- **Interactive rounds, stateless system.**  The feedback converter applied
to a function evaluator is the evaluator of the composed function:
`feedback g ·ᶜ ⌜f⌝ = ⌜f ∘ g ∘ f⌝` — a full DDS equality across all outer
histories. -/
theorem feedback_functionEvaluator (g : Y → X) (f : X → Y) :
    (feedback g ·ᶜ PFunDDS.functionEvaluator f)
      = PFunDDS.functionEvaluator (fun x => f (g (f x))) := by
  rw [feedback]
  exact apply_ofStep_functionEvaluator_of_round (feedbackStep g) f (fun x => f (g (f x)))
    (fun x => [x, g (f x)]) (fun _ => 2) (fun _ => le_rfl)
    (driveG_feedbackStep_functionEvaluator_round g f)

end DDC

end PFunConverter

end RandomSystems.CR18
