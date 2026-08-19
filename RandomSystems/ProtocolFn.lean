/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepConverter
import RandomSystems.SemanticRegistry

/-!
# The protocol function ν and its trace tree (DESIGN §10.5)

The general presentation of a converter as a **single partial
history-function**, with no state carrier and no machine:

`ν : List U × List (Option Y) →. (X ⊕ V)`

— "after outer inputs `u^k` and inner answers `y^l` (cumulative, across
rounds), the converter's next move is an inner query `inl x` or an outer
answer `inr v`."  The converter's own past outputs are recomputable, so
nothing else is data; round boundaries are derived from ν itself.  Memory
classes (memoryless, outer-memoryless = `ofStep`, round counters, general)
are invariance *predicates* on ν, never part of the type.

This module implements the **identity discipline** of DESIGN §10.5:

* `Reach ν` — the trace tree: the pairs ν can actually be consulted at.
  Undefinedness *inside* the tree is honest partiality (a non-productive
  spot); values *off* the tree are junk.
* `JunkFree`, `normalize` (with stability `reach_normalize` and idempotence
  `normalize_normalize`), and **trace equality** `TraceEquiv ν ν' :⇔
  ν* = ν'*` — the working converter identity.
* `toDDC` — the canonical CR18 Def 3.8 object of a protocol function,
  defined on protocol traces only (junk-free by construction; the parse
  relation `ParsesTo` is deterministic and prefix-closed, which gives
  `Valid` with no further conditions).
* `toDDC_normalize` / `toDDC_congr` — the discipline cashed as theorems:
  `toDDC` only reads ν on its trace tree, so trace-equal protocol functions
  are literally the same DDC.

Stress tests against the worked examples (`simpleFn`, `queryLimitFn`, a
junk-carrying variant) are at the end of the file: the trace trees are
characterized in closed form and confirmed against the pen-and-paper
expectations of DESIGN §10.5.
-/

namespace RandomSystems.CR18

/-- A successful `Option`-valued `mapM` preserves list length.  (Answer
histories in this development live in `Y ∪ {⊥}`; sequencing one is the standing
way to say "every answer of this segment is proper", and its length is what the
round counters compare against.) -/
theorem mapM_length {A B : Type*} (f : A → Option B)
    {values : List A} {decoded : List B} (equation : values.mapM f = some decoded) :
    decoded.length = values.length := by
  induction values generalizing decoded with
  | nil =>
      change some [] = some decoded at equation
      have decodedEquation : ([] : List B) = decoded := Option.some.inj equation
      subst decoded
      rfl
  | cons value rest induction =>
      simp only [List.mapM_cons] at equation
      cases headEquation : f value with
      | none => simp [headEquation] at equation
      | some head =>
          simp only [headEquation] at equation
          cases tailEquation : rest.mapM f with
          | none => simp [tailEquation] at equation
          | some tail =>
              rw [tailEquation] at equation
              change some (head :: tail) = some decoded at equation
              have decodedEquation : head :: tail = decoded := Option.some.inj equation
              subst decoded
              simp only [List.length_cons]
              exact congrArg Nat.succ (induction tailEquation)

namespace PFunConverter

open scoped PFunDDS

universe u v w z

/-- DESIGN §10.5: a converter as a single partial history-function — given
the outer inputs and the (cumulative) inner answers so far, the next move.
No state, no machine; round boundaries are derived from the function
itself. -/
abbrev ProtocolFn (U : Type u) (V : Type w) (X : Type z) (Y : Type v) :=
  List U × List (Option Y) →. X ⊕ V

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ### The trace tree -/

/-- **The trace tree of ν**: the least set of `(outer inputs, inner answers)`
pairs at which ν can actually be consulted.  A first outer input opens the
tree; after a query (`inl`), *every* answer extends (the converter does not
know the system); after an outer answer (`inr`), *every* next outer input
extends.  Reachable pairs where ν is undefined are non-productive spots
(application diverges); values off the tree are junk. -/
inductive Reach (ν : ProtocolFn U V X Y) : List U × List (Option Y) → Prop
  | first (u : U) : Reach ν ([u], [])
  | answer {us : List U} {ys : List (Option Y)} {x : X} (hr : Reach ν (us, ys))
      (hx : Sum.inl x ∈ ν (us, ys)) (y : Option Y) : Reach ν (us, ys ++ [y])
  | next {us : List U} {ys : List (Option Y)} {v : V} (hr : Reach ν (us, ys))
      (hv : Sum.inr v ∈ ν (us, ys)) (u : U) : Reach ν (us ++ [u], ys)

/-- Every tree pair has a nonempty outer history. -/
theorem Reach.ne_nil {ν : ProtocolFn U V X Y}
    {p : List U × List (Option Y)} (h : Reach ν p) : p.1 ≠ [] := by
  induction h with
  | first u => simp
  | answer hr hx y ih => exact ih
  | next hr hv u ih => simp

/-- Junk-freedom: ν has values only on its own trace tree.  A `Prop`, not a
subtype — constructors produce junk-free values, mirroring how CR18
Def 3.8's query bound stays a predicate. -/
def JunkFree (ν : ProtocolFn U V X Y) : Prop :=
  ∀ p, (ν p).Dom → Reach ν p

/-- CR18 **Definition 3.8**'s finite-bound clause **localized at a single
pair**: from `p`, no streak of `B` consecutive queries opens.  This is the
whole mathematical content of the clause; the quantifier that carries `B`
over the trace tree is a separate, and consequential, choice — see
`AnswersWithin` (uniform), `AnswersWithinDepth` (uniform in the answers)
and `AnswersEventually` (pointwise). -/
def AnswersWithinAt (ν : ProtocolFn U V X Y)
    (p : List U × List (Option Y)) (B : ℕ) : Prop :=
  ∀ ext : List (Option Y), B ≤ ext.length →
    ¬ ∀ k (_ : k < ext.length), ∃ x, Sum.inl x ∈ ν (p.1, p.2 ++ ext.take k)

/-- A larger budget is a weaker demand. -/
theorem AnswersWithinAt.mono {ν : ProtocolFn U V X Y}
    {p : List U × List (Option Y)} {B B' : ℕ}
    (h : AnswersWithinAt ν p B) (hle : B ≤ B') : AnswersWithinAt ν p B' :=
  fun ext hlen => h ext (le_trans hle hlen)

/-- CR18 **Definition 3.8**, the finite-bound clause, verbatim: "There is
a finite upper bound on the number of consecutive outputs of the form
`(in, x)`."  On the trace tree: no reachable pair opens a streak of `B`
consecutive queries.  Silence (a filter going undefined, §3.4.3) remains
allowed — the clause bounds query streaks, nothing more.

**Quantifier order.**  This reads the clause with *one* `B` good at *every*
reachable pair (`∃B ∀p`).  Def 3.8's own prose is weaker — the converter
"invokes the system a finite number of times … and then returns an output",
i.e. `∀p ∃B` (`AnswersEventually`).  The two differ exactly by finiteness of
`sup_p B p`, and the gap is inhabited: `roundGrowthFn` below satisfies the
prose and fails this predicate.  The uniform reading is nevertheless the one
the downstream theory needs; see the `AnswersWithinDepth` docstring. -/
def AnswersWithin (ν : ProtocolFn U V X Y) (B : ℕ) : Prop :=
  ∀ p, Reach ν p → ∀ ext : List (Option Y), B ≤ ext.length →
    ¬ ∀ k (_ : k < ext.length), ∃ x, Sum.inl x ∈ ν (p.1, p.2 ++ ext.take k)

/-- The uniform clause **is** the pointwise clause, quantified over the tree
with a fixed budget.  Definitional: the factorization renames nothing. -/
theorem answersWithin_iff_forall_at (ν : ProtocolFn U V X Y) (B : ℕ) :
    AnswersWithin ν B ↔ ∀ p, Reach ν p → AnswersWithinAt ν p B :=
  Iff.rfl

/-- Localize a uniform budget at a reachable pair. -/
theorem AnswersWithin.at_of_reach {ν : ProtocolFn U V X Y} {B : ℕ}
    (h : AnswersWithin ν B) {p : List U × List (Option Y)} (hp : Reach ν p) :
    AnswersWithinAt ν p B :=
  h p hp

/-- CR18 **Definition 3.8**'s finite-bound clause as its own **prose** reads
it: at every reachable pair the converter invokes the system a finite number
of times.  No bound is claimed across the tree — `∀p ∃B`, against
`AnswersWithin`'s `∃B ∀p`.  CR18 states this reading informally and the
uniform one formally, and never discharges the obligation the bound exists
for (after Def 3.9: "one would have to show that the described object `αs`
is indeed a `(𝒰,𝒱)`-DDS.  Intuitively, this is obvious.").  We discharge it
in `EmulateRealization.lean` (`applyRaw_dom`).  That obligation is a
one-round-at-a-time argument and this class carries it mathematically —
though our present proof of `applyRaw_dom` routes through the uniform fuel
of `emuRun_terminal`, so it is not yet a witness to that.  What does *not*
survive the weakening is the layer above — the environment
emulation of MauRen11 Def 15/16 (`Emulable`), whose inner *fuel* is fixed
before the assumed system is; see `AnswersWithinDepth`. -/
def AnswersEventually (ν : ProtocolFn U V X Y) : Prop :=
  ∀ p, Reach ν p → ∃ B, AnswersWithinAt ν p B

/-- The finite-bound clause with a budget **uniform in the inner answers**
but free in the round index: at every reachable pair, a budget depending
only on how many outer inputs have arrived.

This is the class the downstream theory actually needs — weaker than
`AnswersWithin`, stronger than Def 3.8's prose.
`EmulateRealization.lean` turns the budget into *fuel*:
`transcript_apply` runs the emulated environment for `n * B` inner rounds
to cover `n` outer ones, and `Emulable` must produce that fuel **before**
the assumed system `s` is chosen.  A budget that varied with the answers
therefore cannot be summed into any fuel at all — the answers are `s`'s
output — whereas a budget varying with the round index sums to `∑_{i<n} F i`.
`AnswersEventually` is strictly too weak for that; `AnswersWithin` is
strictly stronger than needed (`roundGrowthFn`). -/
def AnswersWithinDepth (ν : ProtocolFn U V X Y) (F : ℕ → ℕ) : Prop :=
  ∀ p, Reach ν p → AnswersWithinAt ν p (F p.1.length)

theorem AnswersWithin.answersWithinDepth {ν : ProtocolFn U V X Y} {B : ℕ}
    (h : AnswersWithin ν B) : AnswersWithinDepth ν (fun _ => B) :=
  fun _ hp => h.at_of_reach hp

theorem AnswersWithinDepth.answersEventually {ν : ProtocolFn U V X Y}
    {F : ℕ → ℕ} (h : AnswersWithinDepth ν F) : AnswersEventually ν :=
  fun p hp => ⟨F p.1.length, h p hp⟩

theorem AnswersWithin.answersEventually {ν : ProtocolFn U V X Y} {B : ℕ}
    (h : AnswersWithin ν B) : AnswersEventually ν :=
  h.answersWithinDepth.answersEventually

/-- CR18 **Definition 3.8**, the input-alphabet clause, verbatim: "After
an output `(in, x)` the input alphabet is `Y`" — a DDC never moves past
the completion symbol `⊥`: at any reachable pair whose answers contain a
`none`, ν is silent.  (`Reach` extends the tree by *every* answer after
a query — Def 3.3's completed alphabet — so the clause is a definedness
restriction, not a tree restriction.) -/
def AnswersInY (ν : ProtocolFn U V X Y) : Prop :=
  ∀ p, Reach ν p → none ∈ p.2 → ¬ (ν p).Dom

/-- CR18 **Definition 3.8** as a predicate on protocol functions (the
`IsOfStep` pattern): ν is a deterministic discrete converter iff it
answers in `Y` (never moves past a `⊥`, `AnswersInY`) and has a finite
bound on consecutive inner queries (`AnswersWithin`). -/
@[rs_rule "rs.capability.is_ddc" rs_is_ddc random_systems]
def IsDDC (ν : ProtocolFn U V X Y) : Prop :=
  AnswersInY ν ∧ ∃ B, AnswersWithin ν B

/-- CR18 **Definition 3.8** read as its own prose reads it: the
input-alphabet clause, and a *pointwise* finite bound on query streaks.
Strictly weaker than `IsDDC` (`roundGrowthFn`), and the class every one of
this development's `isDDC_*` constructions lands in a fortiori
(`IsDDC.isDDCEventually`). -/
def IsDDCEventually (ν : ProtocolFn U V X Y) : Prop :=
  AnswersInY ν ∧ AnswersEventually ν

/-- Every DDC in the uniform sense is one in the prose sense: the 14
`isDDC_*` producers of this development remain valid witnesses for the
weaker class.  The converse fails — `roundGrowthFn`. -/
theorem IsDDC.isDDCEventually {ν : ProtocolFn U V X Y} (h : IsDDC ν) :
    IsDDCEventually ν :=
  ⟨h.1, h.2.elim fun _ hB => hB.answersEventually⟩

/-! ### Normalization and trace equality -/

/-- The canonical representative: ν restricted to its trace tree. -/
def normalize (ν : ProtocolFn U V X Y) : ProtocolFn U V X Y :=
  fun p => ⟨(ν p).Dom ∧ Reach ν p, fun h => (ν p).get h.1⟩

theorem mem_normalize_iff (ν : ProtocolFn U V X Y) (p : List U × List (Option Y))
    (m : X ⊕ V) :
    m ∈ normalize ν p ↔ m ∈ ν p ∧ Reach ν p := by
  constructor
  · rintro ⟨⟨hd, hr⟩, rfl⟩
    exact ⟨Part.get_mem hd, hr⟩
  · rintro ⟨hm, hr⟩
    have hd : (ν p).Dom := Part.dom_iff_mem.mpr ⟨m, hm⟩
    exact ⟨⟨hd, hr⟩, Part.get_eq_of_mem hm hd⟩

/-- **Stability**: normalization does not change the trace tree — reachability
only consults tree pairs, whose values survive the restriction. -/
theorem reach_normalize (ν : ProtocolFn U V X Y) (p : List U × List (Option Y)) :
    Reach (normalize ν) p ↔ Reach ν p := by
  constructor
  · intro h
    induction h with
    | first u => exact Reach.first u
    | answer hr hx y ih =>
        exact Reach.answer ih ((mem_normalize_iff ν _ _).mp hx).1 y
    | next hr hv u ih =>
        exact Reach.next ih ((mem_normalize_iff ν _ _).mp hv).1 u
  · intro h
    induction h with
    | first u => exact Reach.first u
    | answer hr hx y ih =>
        exact Reach.answer ih ((mem_normalize_iff ν _ _).mpr ⟨hx, hr⟩) y
    | next hr hv u ih =>
        exact Reach.next ih ((mem_normalize_iff ν _ _).mpr ⟨hv, hr⟩) u

/-- **Idempotence**: junk-free representatives are canonical. -/
theorem normalize_normalize (ν : ProtocolFn U V X Y) :
    normalize (normalize ν) = normalize ν := by
  funext p
  apply Part.ext
  intro m
  rw [mem_normalize_iff, mem_normalize_iff, reach_normalize]
  tauto

theorem junkFree_normalize (ν : ProtocolFn U V X Y) : JunkFree (normalize ν) := by
  rintro p ⟨hd, hr⟩
  exact (reach_normalize ν p).mpr hr

theorem normalize_eq_self_of_junkFree {ν : ProtocolFn U V X Y}
    (h : JunkFree ν) : normalize ν = ν := by
  funext p
  apply Part.ext
  intro m
  rw [mem_normalize_iff]
  exact ⟨fun hm => hm.1, fun hm => ⟨hm, h p (Part.dom_iff_mem.mpr ⟨m, hm⟩)⟩⟩

/-- **Trace equality** — the working converter identity (DESIGN §10.5):
agreement of the canonical junk-free representatives.  Strictly finer than
apply-equality (separated by dead queries), strictly coarser than raw
equality (junk invisible). -/
def TraceEquiv (ν ν' : ProtocolFn U V X Y) : Prop :=
  normalize ν = normalize ν'

theorem TraceEquiv.refl (ν : ProtocolFn U V X Y) : TraceEquiv ν ν := rfl

theorem TraceEquiv.symm {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    TraceEquiv ν' ν := Eq.symm h

theorem TraceEquiv.trans {ν₁ ν₂ ν₃ : ProtocolFn U V X Y}
    (h₁ : TraceEquiv ν₁ ν₂) (h₂ : TraceEquiv ν₂ ν₃) : TraceEquiv ν₁ ν₃ :=
  Eq.trans h₁ h₂

theorem traceEquiv_normalize (ν : ProtocolFn U V X Y) :
    TraceEquiv ν (normalize ν) :=
  (normalize_normalize ν).symm

/-- Two protocol functions that agree on each other's trace trees are trace
equal — the workhorse for identifying a junk-carrying presentation with its
clean version. -/
theorem reach_mono_of_eqOn {ν ν' : ProtocolFn U V X Y}
    (h : ∀ p, Reach ν p → ν p = ν' p) {p : List U × List (Option Y)}
    (hp : Reach ν p) : Reach ν' p := by
  induction hp with
  | first u => exact Reach.first u
  | answer hr hx y ih => exact Reach.answer ih (h _ hr ▸ hx) y
  | next hr hv u ih => exact Reach.next ih (h _ hr ▸ hv) u

theorem traceEquiv_of_eqOn_reach {ν ν' : ProtocolFn U V X Y}
    (h : ∀ p, Reach ν p → ν p = ν' p)
    (h' : ∀ p, Reach ν' p → ν' p = ν p) :
    TraceEquiv ν ν' := by
  funext p
  apply Part.ext
  intro m
  rw [mem_normalize_iff, mem_normalize_iff]
  constructor
  · rintro ⟨hm, hr⟩
    exact ⟨h p hr ▸ hm, reach_mono_of_eqOn h hr⟩
  · rintro ⟨hm, hr⟩
    exact ⟨h' p hr ▸ hm, reach_mono_of_eqOn h' hr⟩

/-! ### The Def 3.8 clauses are trace invariants -/

/-- Trace-equal protocol functions have the same trace trees. -/
theorem reach_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    (p : List U × List (Option Y)) : Reach ν p ↔ Reach ν' p := by
  rw [← reach_normalize ν, h, reach_normalize]

/-- Trace-equal protocol functions have the same members at tree pairs. -/
theorem mem_congr_of_reach {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    {p : List U × List (Option Y)} (hr : Reach ν p) (m : X ⊕ V) :
    m ∈ ν p ↔ m ∈ ν' p := by
  have h1 : m ∈ normalize ν p ↔ m ∈ normalize ν' p := by rw [h]
  rw [mem_normalize_iff, mem_normalize_iff] at h1
  constructor
  · intro hm
    exact (h1.mp ⟨hm, hr⟩).1
  · intro hm
    exact (h1.mpr ⟨hm, (reach_congr h p).mp hr⟩).1

/-- `AnswersInY` is a trace invariant. -/
theorem answersInY_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    AnswersInY ν ↔ AnswersInY ν' := by
  have hdom : ∀ p, Reach ν p → ((ν p).Dom ↔ (ν' p).Dom) := by
    intro p hr
    rw [Part.dom_iff_mem, Part.dom_iff_mem]
    exact exists_congr fun m => mem_congr_of_reach h hr m
  constructor
  · intro ha p hrp hnone hd
    exact ha p ((reach_congr h p).mpr hrp) hnone
      ((hdom p ((reach_congr h p).mpr hrp)).mpr hd)
  · intro ha p hrp hnone hd
    exact ha p ((reach_congr h p).mp hrp) hnone
      ((hdom p hrp).mp hd)

/-- `AnswersWithin` is a trace invariant. -/
theorem answersWithin_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    {B : ℕ} : AnswersWithin ν B ↔ AnswersWithin ν' B := by
  have key : ∀ {μ μ' : ProtocolFn U V X Y}, TraceEquiv μ μ' →
      AnswersWithin μ B → AnswersWithin μ' B := by
    intro μ μ' hμ ha p hrp ext hlen hall
    have hrp' : Reach μ p := (reach_congr hμ p).mpr hrp
    have hreachk : ∀ k, k ≤ ext.length →
        Reach μ (p.1, p.2 ++ ext.take k) := by
      intro k
      induction k with
      | zero =>
          intro _
          simpa only [List.take_zero, List.append_nil] using hrp'
      | succ j ih =>
          intro hjk
          have hj : j < ext.length := by omega
          obtain ⟨x, hx⟩ := hall j hj
          have hx' : Sum.inl x ∈ μ (p.1, p.2 ++ ext.take j) :=
            (mem_congr_of_reach hμ (ih (by omega)) _).mpr hx
          have hnext := Reach.answer (ih (by omega)) hx' (ext[j]'hj)
          rw [List.append_assoc, List.take_concat_get' ext j hj] at hnext
          exact hnext
    refine ha p hrp' ext hlen fun k hk => ?_
    obtain ⟨x, hx⟩ := hall k hk
    exact ⟨x, (mem_congr_of_reach hμ (hreachk k (by omega)) _).mpr hx⟩
  exact ⟨key h, key h.symm⟩

/-- `IsDDC` is a trace invariant. -/
theorem isDDC_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    IsDDC ν ↔ IsDDC ν' := by
  unfold IsDDC
  rw [answersInY_congr h]
  exact and_congr_right fun _ =>
    exists_congr fun B => answersWithin_congr h

/-! ### The canonical Def 3.8 object: `toDDC`

The parse relation `ParsesTo ν l p` reads a converter history left-to-right,
checking at each element that ν's value at the current pair permits it (an
answer — `⊥` included, Def 3.8's `Y ∪ {⊥}` input alphabet — only while a
query is pending, a fresh outer input only once the round has answered; an
off-protocol label has no parse).  It is deterministic and prefix-closed,
which makes `toDDC ν` a valid DDC with no side conditions. -/

/-- Left-to-right trace parse from a given pair. -/
def ParsesToAux (ν : ProtocolFn U V X Y) :
    List U × List (Option Y) → List (DDC.CIn U Y) → List U × List (Option Y) → Prop
  | st, [], p => p = st
  | st, Sum.inl (InLabel.outside, u) :: rest, p =>
      (∃ v, Sum.inr v ∈ ν st) ∧ ParsesToAux ν (st.1 ++ [u], st.2) rest p
  | st, Sum.inr (InLabel.inside, oy) :: rest, p =>
      (∃ x, Sum.inl x ∈ ν st) ∧ ParsesToAux ν (st.1, st.2 ++ [oy]) rest p
  | _, _ :: _, _ => False

/-- A converter history parses to a pair: it must open with an outer input. -/
def ParsesTo (ν : ProtocolFn U V X Y) :
    List (DDC.CIn U Y) → List U × List (Option Y) → Prop
  | [], _ => False
  | Sum.inl (InLabel.outside, u) :: rest, p => ParsesToAux ν ([u], []) rest p
  | _ :: _, _ => False

theorem parsesTo_nil (ν : ProtocolFn U V X Y) (p : List U × List (Option Y)) :
    ¬ ParsesTo ν [] p :=
  fun h => h

theorem parsesToAux_unique (ν : ProtocolFn U V X Y) :
    ∀ {l : List (DDC.CIn U Y)} {st p p'},
      ParsesToAux ν st l p → ParsesToAux ν st l p' → p = p' := by
  intro l
  induction l with
  | nil =>
      intro st p p' h h'
      exact h.trans h'.symm
  | cons a rest ih =>
      intro st p p' h h'
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · exact ih h.2 h'.2
      · exact ih h.2 h'.2
      · exact h.elim

theorem parsesTo_unique {ν : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {p p' : List U × List (Option Y)}
    (h : ParsesTo ν l p) (h' : ParsesTo ν l p') : p = p' := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · exact parsesToAux_unique ν h h'
      · exact h.elim
      · exact h.elim

theorem parsesToAux_append (ν : ProtocolFn U V X Y) :
    ∀ {l₁ l₂ : List (DDC.CIn U Y)} {st p},
      ParsesToAux ν st (l₁ ++ l₂) p ↔
        ∃ q, ParsesToAux ν st l₁ q ∧ ParsesToAux ν q l₂ p := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ st p
      constructor
      · intro h
        exact ⟨st, rfl, h⟩
      · rintro ⟨q, rfl, h⟩
        exact h
  | cons a rest ih =>
      intro l₂ st p
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · constructor
        · intro h; exact h.elim
        · rintro ⟨q, h, -⟩; exact h.elim
      · show ((∃ v, Sum.inr v ∈ ν st) ∧ ParsesToAux ν _ (rest ++ l₂) p) ↔ _
        rw [ih]
        constructor
        · rintro ⟨hv, q, h₁, h₂⟩
          exact ⟨q, ⟨hv, h₁⟩, h₂⟩
        · rintro ⟨q, ⟨hv, h₁⟩, h₂⟩
          exact ⟨hv, q, h₁, h₂⟩
      · show ((∃ x, Sum.inl x ∈ ν st) ∧ ParsesToAux ν _ (rest ++ l₂) p) ↔ _
        rw [ih]
        constructor
        · rintro ⟨hx, q, h₁, h₂⟩
          exact ⟨q, ⟨hx, h₁⟩, h₂⟩
        · rintro ⟨q, ⟨hx, h₁⟩, h₂⟩
          exact ⟨hx, q, h₁, h₂⟩
      · constructor
        · intro h; exact h.elim
        · rintro ⟨q, h, -⟩; exact h.elim

/-- Parses land in the trace tree. -/
theorem reach_of_parsesToAux (ν : ProtocolFn U V X Y) :
    ∀ {l : List (DDC.CIn U Y)} {st p},
      ParsesToAux ν st l p → Reach ν st → Reach ν p := by
  intro l
  induction l with
  | nil =>
      intro st p h hst
      rw [show p = st from h]
      exact hst
  | cons a rest ih =>
      intro st p h hst
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · obtain ⟨⟨v, hv⟩, hrest⟩ := h
        exact ih hrest (Reach.next hst hv u)
      · obtain ⟨⟨x, hx⟩, hrest⟩ := h
        exact ih hrest (Reach.answer hst hx oy)
      · exact h.elim

theorem ParsesTo.reach {ν : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {p : List U × List (Option Y)} (h : ParsesTo ν l p) : Reach ν p := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · exact reach_of_parsesToAux ν h (Reach.first u)
      · exact h.elim
      · exact h.elim

/-- Prefix closure of the parse, with the intermediate pair's definedness
witnessed whenever the history continues. -/
theorem parsesTo_prefix {ν : ProtocolFn U V X Y} {l₁ l₂ : List (DDC.CIn U Y)}
    {p : List U × List (Option Y)}
    (h : ParsesTo ν (l₁ ++ l₂) p) (h₁ : l₁ ≠ []) :
    ∃ q, ParsesTo ν l₁ q ∧ (l₂ ≠ [] → (ν q).Dom) := by
  cases l₁ with
  | nil => exact absurd rfl h₁
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · rw [show ((Sum.inl (InLabel.outside, u) :: rest : List (DDC.CIn U Y)) ++ l₂)
            = Sum.inl (InLabel.outside, u) :: (rest ++ l₂) from rfl] at h
        rw [show ParsesTo ν (Sum.inl (InLabel.outside, u) :: (rest ++ l₂)) p
            = ParsesToAux ν ([u], []) (rest ++ l₂) p from rfl] at h
        rw [parsesToAux_append] at h
        obtain ⟨q, hq, htail⟩ := h
        refine ⟨q, hq, ?_⟩
        intro hne
        cases l₂ with
        | nil => exact absurd rfl hne
        | cons b l₂' =>
            rcases b with ⟨lbl, u'⟩ | ⟨lbl, oy'⟩ <;> cases lbl
            · exact htail.elim
            · obtain ⟨⟨v, hv⟩, -⟩ := htail
              exact Part.dom_iff_mem.mpr ⟨_, hv⟩
            · obtain ⟨⟨x, hx⟩, -⟩ := htail
              exact Part.dom_iff_mem.mpr ⟨_, hx⟩
            · exact htail.elim
      · exact h.elim
      · exact h.elim

/-- The raw function of `toDDC`: at a history that parses to `p`, the move ν
prescribes at `p` (in converter-output alphabet); no parse, no value. -/
noncomputable def toDDCRaw (ν : ProtocolFn U V X Y) :
    PFunDDS.Raw (DDC.CIn U Y) (DDC.COut V X) :=
  fun l => (Part.assert (∃ p, ParsesTo ν l p) fun h => ν h.choose).map DDC.moveOf

theorem mem_toDDCRaw_iff (ν : ProtocolFn U V X Y) (l : List (DDC.CIn U Y))
    (o : DDC.COut V X) :
    o ∈ toDDCRaw ν l ↔
      ∃ p, ParsesTo ν l p ∧ ∃ m ∈ ν p, o = DDC.moveOf m := by
  rw [toDDCRaw, Part.mem_map_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Part.mem_assert_iff] at hm
    obtain ⟨h, hm⟩ := hm
    exact ⟨h.choose, h.choose_spec, m, hm, rfl⟩
  · rintro ⟨p, hp, m, hm, rfl⟩
    refine ⟨m, ?_, rfl⟩
    rw [Part.mem_assert_iff]
    refine ⟨⟨p, hp⟩, ?_⟩
    have hcp : (⟨p, hp⟩ : ∃ q, ParsesTo ν l q).choose = p :=
      parsesTo_unique (Exists.choose_spec _) hp
    rw [hcp]
    exact hm

/-- **The canonical CR18 Def 3.8 object of a protocol function** — junk-free
by construction (defined on protocol traces only), `Valid` with no side
conditions (the ν presentation needs no validity bureaucracy; the parse
relation is prefix-closed). -/
noncomputable def toDDC (ν : ProtocolFn U V X Y) : DDC U V X Y :=
  ⟨toDDCRaw ν, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]
      rintro ⟨o, ho⟩
      rw [mem_toDDCRaw_iff] at ho
      obtain ⟨p, hp, -⟩ := ho
      exact parsesTo_nil ν p hp
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨t, rfl⟩ := hpre
      cases t with
      | nil => simpa using hdom
      | cons b t' =>
          rw [PFun.mem_dom] at hdom
          obtain ⟨o, ho⟩ := hdom
          rw [mem_toDDCRaw_iff] at ho
          obtain ⟨p, hp, -⟩ := ho
          obtain ⟨q, hq, hdomq⟩ := parsesTo_prefix hp hne
          have hd : (ν q).Dom := hdomq (by simp)
          rw [PFun.mem_dom]
          refine ⟨DDC.moveOf ((ν q).get hd), ?_⟩
          rw [mem_toDDCRaw_iff]
          exact ⟨q, hq, (ν q).get hd, Part.get_mem hd, rfl⟩⟩

@[simp] theorem toDDC_toPFun (ν : ProtocolFn U V X Y) :
    (toDDC ν).1 = toDDCRaw ν := rfl

/-- `toDDC` reads ν only on its trace tree: normalization is invisible. -/
theorem parsesToAux_normalize (ν : ProtocolFn U V X Y) :
    ∀ {l : List (DDC.CIn U Y)} {st p}, Reach ν st →
      (ParsesToAux (normalize ν) st l p ↔ ParsesToAux ν st l p) := by
  intro l
  induction l with
  | nil => intro st p _; exact Iff.rfl
  | cons a rest ih =>
      intro st p hst
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact Iff.rfl
      · show ((∃ v, Sum.inr v ∈ normalize ν st) ∧ _) ↔ ((∃ v, Sum.inr v ∈ ν st) ∧ _)
        constructor
        · rintro ⟨⟨v, hv⟩, hrest⟩
          have hv' : Sum.inr v ∈ ν st := ((mem_normalize_iff ν st _).mp hv).1
          exact ⟨⟨v, hv'⟩, (ih (Reach.next hst hv' u)).mp hrest⟩
        · rintro ⟨⟨v, hv⟩, hrest⟩
          exact ⟨⟨v, (mem_normalize_iff ν st _).mpr ⟨hv, hst⟩⟩,
            (ih (Reach.next hst hv u)).mpr hrest⟩
      · show ((∃ x, Sum.inl x ∈ normalize ν st) ∧ _) ↔
          ((∃ x, Sum.inl x ∈ ν st) ∧ _)
        constructor
        · rintro ⟨⟨x, hx⟩, hrest⟩
          have hx' : Sum.inl x ∈ ν st := ((mem_normalize_iff ν st _).mp hx).1
          exact ⟨⟨x, hx'⟩, (ih (Reach.answer hst hx' oy)).mp hrest⟩
        · rintro ⟨⟨x, hx⟩, hrest⟩
          exact ⟨⟨x, (mem_normalize_iff ν st _).mpr ⟨hx, hst⟩⟩,
            (ih (Reach.answer hst hx oy)).mpr hrest⟩
      · exact Iff.rfl

theorem parsesTo_normalize (ν : ProtocolFn U V X Y) (l : List (DDC.CIn U Y))
    (p : List U × List (Option Y)) :
    ParsesTo (normalize ν) l p ↔ ParsesTo ν l p := by
  cases l with
  | nil => exact Iff.rfl
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact Iff.rfl
      · exact parsesToAux_normalize ν (Reach.first u)
      · exact Iff.rfl
      · exact Iff.rfl

/-- **The identity discipline, cashed (1/2)**: the canonical DDC of ν and of
its normalization coincide — `toDDC` cannot see junk. -/
theorem toDDC_normalize (ν : ProtocolFn U V X Y) :
    toDDC (normalize ν) = toDDC ν := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro o
  rw [show (toDDC (normalize ν)).1 = toDDCRaw (normalize ν) from rfl,
    show (toDDC ν).1 = toDDCRaw ν from rfl,
    mem_toDDCRaw_iff, mem_toDDCRaw_iff]
  constructor
  · rintro ⟨p, hp, m, hm, rfl⟩
    exact ⟨p, (parsesTo_normalize ν l p).mp hp,
      m, ((mem_normalize_iff ν p m).mp hm).1, rfl⟩
  · rintro ⟨p, hp, m, hm, rfl⟩
    exact ⟨p, (parsesTo_normalize ν l p).mpr hp,
      m, (mem_normalize_iff ν p m).mpr ⟨hm, hp.reach⟩, rfl⟩

/-- **The identity discipline, cashed (2/2)**: trace-equal protocol functions
present literally the same Def 3.8 converter (hence a fortiori the same
applied system, for every system). -/
theorem toDDC_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    toDDC ν = toDDC ν' := by
  rw [← toDDC_normalize ν, ← toDDC_normalize ν']
  exact congrArg toDDC h

theorem apply_toDDC_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    (S : PFunDDS.DDS X Y) :
    DDC.apply (toDDC ν) S = DDC.apply (toDDC ν') S := by
  rw [toDDC_congr h]

/-! ### Stress tests (DESIGN §10.5)

The worked examples, with their trace trees characterized in closed form and
checked against the pen-and-paper expectations.  With the `Y ∪ {⊥}` answer
alphabet (CR18 Def 3.8) the converters are *silent on `⊥`*: an answer
branch fires only on a proper answer `some y`.  Consequently the raw
(length-only) bodies carry invisible junk at improper-answer pairs — those
pairs are off the tree, hence invisible through
`normalize`/`TraceEquiv`/`toDDC` — and the tree characterizations record
the **someness discipline**: every answer consumed along a trace is proper.

* `simpleFn` (fixed arity 1 — lengths determine the round position): the
  tree is the length lattice `{k = l+1} ∪ {k = l > 0}` refined by the
  someness discipline (`reach_simpleFn_iff`).
* `queryLimitFn q` (the `[q]` filter — a *round counter*, the first
  converter outside the outer-memoryless class): the tree is the same
  length lattice cut at the budget, **including the breach pair**
  `(q+1 outer inputs, q answers)`, on which ν is *undefined* — the
  `(q+1)`-st query is a non-productive spot of the tree, not junk, exactly
  CR18 Def 3.10's "undefined as of the `(q+1)`-st query".
* `simpleFnJunk` (a junk-carrying variant of `simpleFn`): *not* junk-free,
  *not* raw-equal to `simpleFn`, but `TraceEquiv` to it — so `toDDC`
  identifies them (`toDDC_congr`).  Junk is invisible, exactly as the
  discipline demands. -/

section StressTests

/-- The simple converter `(c, d)` as a protocol function.  Fixed inner arity
1, so the round position is determined by lengths: one more input than
answers = query pending; equal (nonzero) lengths = round complete — and the
converter answers only if the round's answer was proper (`some y`); on `⊥`
it is silent. -/
@[rs_rule "rs.protocol.simple" rs_protocol random_systems]
def simpleFn (c : U → X) (d : Y → V) : ProtocolFn U V X Y := fun p =>
  if h : p.1.length = p.2.length + 1 then
    Part.some (Sum.inl (c (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega))))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2) with
    | some y => Part.some (Sum.inr (d y))
    | none => Part.none
  else Part.none

theorem simpleFn_inl_inv {c : U → X} {d : Y → V} {us : List U}
    {ys : List (Option Y)} {x : X} (h : Sum.inl x ∈ simpleFn c d (us, ys)) :
    us.length = ys.length + 1 := by
  simp only [simpleFn] at h
  split_ifs at h with h1 h2
  · exact h1
  · split at h <;> simp at h
  · simp at h

theorem simpleFn_inr_inv {c : U → X} {d : Y → V} {us : List U}
    {ys : List (Option Y)} {v : V} (h : Sum.inr v ∈ simpleFn c d (us, ys)) :
    us.length = ys.length ∧ ∃ (h0 : 0 < ys.length) (y : Y),
      ys.getLast (List.ne_nil_of_length_pos h0) = some y ∧ v = d y := by
  simp only [simpleFn] at h
  split_ifs at h with h1 h2
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨h2.1, h2.2, y, hy, h⟩
    · simp at h
  · simp at h

theorem simpleFn_inl_mem (c : U → X) (d : Y → V) {us : List U}
    {ys : List (Option Y)} (h : us.length = ys.length + 1) :
    Sum.inl (c (us.getLast (by apply List.ne_nil_of_length_pos; omega))) ∈
      simpleFn c d (us, ys) := by
  simp only [simpleFn]
  rw [dif_pos h]
  exact Part.mem_some _

theorem simpleFn_inr_mem (c : U → X) (d : Y → V) {us : List U}
    {ys : List (Option Y)} (h : us.length = ys.length) (h0 : 0 < ys.length)
    {y : Y} (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some y) :
    Sum.inr (d y) ∈ simpleFn c d (us, ys) := by
  simp only [simpleFn]
  rw [dif_neg (by omega), dif_pos ⟨h, h0⟩, hy]
  exact Part.mem_some _

/-- **Stress test — expected tree shape.**  The trace tree of `simpleFn` is
the length lattice `{k = l+1} ∪ {k = l > 0}` predicted by hand, refined by
the someness discipline: a completed round continues only if its answer was
proper, so every answer along a trace is proper — except possibly the last
one, while its round is still unanswered. -/
theorem reach_simpleFn_iff (c : U → X) (d : Y → V) (p : List U × List (Option Y)) :
    Reach (simpleFn c d) p ↔
      (p.1.length = p.2.length + 1 ∧ ∀ oy ∈ p.2, oy.isSome) ∨
        (p.1.length = p.2.length ∧ 0 < p.1.length ∧
          ∀ oy ∈ p.2.dropLast, oy.isSome) := by
  constructor
  · intro h
    induction h with
    | first u => simp
    | answer hr hx y ih =>
        have hlen := simpleFn_inl_inv hx
        dsimp only at ih ⊢
        rcases ih with ⟨-, hsome⟩ | ⟨h', -, -⟩
        · refine Or.inr ⟨?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · omega
          · rw [List.dropLast_concat]
            exact hsome
        · omega
    | next hr hv u ih =>
        rename_i us ys v
        obtain ⟨hlen, h0, y, hy, -⟩ := simpleFn_inr_inv hv
        dsimp only at ih ⊢
        rcases ih with ⟨h', -⟩ | ⟨-, -, hdrop⟩
        · omega
        · have hall : ∀ oy ∈ ys, oy.isSome := by
            intro oy hmem
            rw [← List.dropLast_append_getLast
              (List.ne_nil_of_length_pos h0)] at hmem
            rcases List.mem_append.mp hmem with hm | hm
            · exact hdrop oy hm
            · rw [List.mem_singleton.mp hm, hy]
              rfl
          refine Or.inl ⟨?_, hall⟩
          simp only [List.length_append, List.length_singleton]
          omega
  · obtain ⟨us, ys⟩ := p
    dsimp only
    intro h
    induction ys using List.reverseRecOn generalizing us with
    | nil =>
        simp only [List.length_nil] at h
        rcases h with ⟨h, -⟩ | ⟨h, hpos, -⟩
        · obtain ⟨u, rfl⟩ :=
            List.length_eq_one_iff.mp (by omega : us.length = 1)
          exact Reach.first u
        · exact absurd hpos (by omega)
    | append_singleton ys y ih =>
        have hB : ∀ us' : List U, us'.length = ys.length + 1 →
            (∀ oy ∈ ys, oy.isSome) →
            Reach (simpleFn c d) (us', ys ++ [y]) := by
          intro us' hlen hsome
          exact Reach.answer (ih (us := us') (Or.inl ⟨hlen, hsome⟩))
            (simpleFn_inl_mem c d hlen) y
        simp only [List.length_append, List.length_singleton] at h
        rcases h with ⟨h, hsome⟩ | ⟨h, hpos, hsome⟩
        · have hne : us ≠ [] := by
            apply List.ne_nil_of_length_pos
            omega
          obtain ⟨us', u, rfl⟩ := (List.eq_nil_or_concat us).resolve_left hne
          simp only [List.concat_eq_append, List.length_append,
            List.length_singleton] at h ⊢
          obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp
            (hsome y (List.mem_append_right _ (List.mem_singleton_self y)))
          exact Reach.next
            (hB us' (by omega)
              (fun oy hm => hsome oy (List.mem_append_left _ hm)))
            (simpleFn_inr_mem c d
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp)
              (by rw [List.getLast_concat]; exact hy'))
            u
        · rw [List.dropLast_concat] at hsome
          exact hB us (by omega) hsome

/-- `simpleFn` is silent past a `⊥`: on its tree a `⊥` can only be the
last answer, where both branches refuse. -/
theorem answersInY_simpleFn (c : U → X) (d : Y → V) :
    AnswersInY (simpleFn c d) := by
  rintro ⟨us, ys⟩ hr hn hd
  have hne' : ys ≠ [] := by
    rintro rfl
    simp at hn
  have hsome : ∀ oy ∈ ys.dropLast, oy.isSome := by
    rcases (reach_simpleFn_iff c d (us, ys)).mp hr with ⟨-, hs⟩ | ⟨-, -, hs⟩
    · exact fun oy hm => hs oy (List.mem_of_mem_dropLast hm)
    · exact hs
  have hlast : ys.getLast hne' = none := by
    have hn' := hn
    rw [← List.dropLast_append_getLast hne'] at hn'
    rcases List.mem_append.mp hn' with h' | h'
    · exact absurd (hsome _ h') (by simp)
    · exact (List.mem_singleton.mp h').symm
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  cases m with
  | inl x =>
      have h1 := simpleFn_inl_inv hm
      rcases (reach_simpleFn_iff c d (us, ys)).mp hr with ⟨-, hs⟩ |
        ⟨hlen, -, -⟩
      · exact absurd (hs _ hn) (by simp)
      · have hlen' : us.length = ys.length := hlen
        omega
  | inr v =>
      obtain ⟨-, h0, y, hgl, -⟩ := simpleFn_inr_inv hm
      have h1 : ys.getLast (List.ne_nil_of_length_pos h0) = none := hlast
      rw [h1] at hgl
      simp at hgl

/-- `simpleFn` never opens a streak of two queries: a query forces the
outer history one ahead, which one more answer destroys. -/
theorem answersWithin_simpleFn (c : U → X) (d : Y → V) :
    AnswersWithin (simpleFn c d) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  have h0 := simpleFn_inl_inv hx0
  have h1 := simpleFn_inl_inv hx1
  simp only [List.length_append, List.length_take] at h0 h1
  omega

/-- `simpleFn` is a DDC (CR18 Def 3.8) — membership in the class. -/
@[rs_rule "rs.is_ddc.simple" rs_is_ddc random_systems]
theorem isDDC_simpleFn (c : U → X) (d : Y → V) : IsDDC (simpleFn c d) :=
  ⟨answersInY_simpleFn c d, 2, answersWithin_simpleFn c d⟩

/-- **Smoke test — `toDDC` produces the expected first move**: on the
one-element history "outer input `u`", the canonical DDC of `simpleFn`
queries `c u` inside. -/
theorem toDDC_simpleFn_first_move (c : U → X) (d : Y → V) (u : U) :
    Sum.inr (InLabel.inside, c u) ∈
      (toDDC (simpleFn c d)).1 [Sum.inl (InLabel.outside, u)] := by
  rw [toDDC_toPFun, mem_toDDCRaw_iff]
  refine ⟨([u], []), ?_, Sum.inl (c u), ?_, rfl⟩
  · show ParsesToAux (simpleFn c d) ([u], []) [] ([u], [])
    rfl
  · have h := simpleFn_inl_mem c d (us := [u]) (ys := []) (by simp)
    simpa using h

/-- The identity restriction converter for a decidable predicate on query
histories. It forwards the newest query and its answer exactly while the
current history satisfies `P`, and becomes undefined when `P` is violated. -/
def restrictionFn (P : List X → Prop) [DecidablePred P] :
    ProtocolFn X Y X Y := fun p =>
  if h : p.1.length = p.2.length + 1 ∧ P p.1 then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos
      omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length ∧ P p.1 then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2.1) with
    | some y => Part.some (Sum.inr y)
    | none => Part.none
  else
    Part.none

theorem restrictionFn_inl_inv {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ restrictionFn P (us, ys)) :
    us.length = ys.length + 1 ∧ P us := by
  simp only [restrictionFn] at h
  split_ifs at h with hquery hanswer
  · exact hquery
  · split at h <;> simp at h
  · simp at h

theorem restrictionFn_inr_inv {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {v : Y}
    (h : Sum.inr v ∈ restrictionFn P (us, ys)) :
    us.length = ys.length ∧ P us ∧ ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some v := by
  simp only [restrictionFn] at h
  split_ifs at h with hquery hanswer
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨hanswer.1, hanswer.2.2, hanswer.2.1, by rw [hy, h]⟩
    · simp at h
  · simp at h

theorem restrictionFn_inl_val {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ restrictionFn P (us, ys)) :
    ∃ hne : us ≠ [], x = us.getLast hne := by
  simp only [restrictionFn] at h
  split_ifs at h with hquery hanswer
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨List.ne_nil_of_length_pos (by omega), h⟩
  · split at h <;> simp at h
  · simp at h

theorem restrictionFn_inl_mem (P : List X → Prop) [DecidablePred P]
    {us : List X} {ys : List (Option Y)}
    (hlen : us.length = ys.length + 1) (hP : P us) :
    Sum.inl (us.getLast (by
      apply List.ne_nil_of_length_pos
      omega)) ∈ restrictionFn P (us, ys) := by
  simp only [restrictionFn]
  rw [dif_pos ⟨hlen, hP⟩]
  exact Part.mem_some _

theorem restrictionFn_inr_mem (P : List X → Prop) [DecidablePred P]
    {us : List X} {ys : List (Option Y)}
    (hlen : us.length = ys.length) (h0 : 0 < ys.length) (hP : P us)
    {y : Y} (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some y) :
    Sum.inr y ∈ restrictionFn P (us, ys) := by
  simp only [restrictionFn]
  rw [dif_neg (by omega), dif_pos ⟨hlen, h0, hP⟩, hy]
  exact Part.mem_some _

/-- The `[q]` query filter as a protocol function — a **round counter**, the
first converter genuinely outside the outer-memoryless (`ofStep`) class:
its move depends on the *lengths* of the history, i.e. on the round number.
(The budget check on the answer branch keeps the never-consulted answered
pairs beyond round `q` silent — without it they would carry junk; the tree
characterization `reach_queryLimitFn_iff` cuts the length lattice at the
budget.  As everywhere under the `Y ∪ {⊥}` alphabet, the answer branch
fires only on a proper answer.) -/
@[rs_rule "rs.protocol.query_limit" rs_protocol random_systems]
def queryLimitFn (q : ℕ) : ProtocolFn X Y X Y := fun p =>
  if h : p.1.length = p.2.length + 1 ∧ p.1.length ≤ q then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length ∧ p.1.length ≤ q then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2.1) with
    | some y => Part.some (Sum.inr y)
    | none => Part.none
  else Part.none

theorem queryLimitFn_inl_inv {q : ℕ} {us : List X} {ys : List (Option Y)}
    {x : X} (h : Sum.inl x ∈ queryLimitFn q (us, ys)) :
    us.length = ys.length + 1 ∧ us.length ≤ q := by
  simp only [queryLimitFn] at h
  split_ifs at h with h1 h2
  · exact h1
  · split at h <;> simp at h
  · simp at h

theorem queryLimitFn_inr_inv {q : ℕ} {us : List X} {ys : List (Option Y)}
    {v : Y} (h : Sum.inr v ∈ queryLimitFn q (us, ys)) :
    us.length = ys.length ∧ us.length ≤ q ∧ ∃ (h0 : 0 < ys.length),
      ys.getLast (List.ne_nil_of_length_pos h0) = some v := by
  simp only [queryLimitFn] at h
  split_ifs at h with h1 h2
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨h2.1, h2.2.2, h2.2.1, by rw [hy, h]⟩
    · simp at h
  · simp at h

/-- Move inversion for `queryLimitFn`, query branch, value form: the
forwarded query is the last outer input. -/
theorem queryLimitFn_inl_val {q : ℕ} {us : List X} {ys : List (Option Y)}
    {x : X} (h : Sum.inl x ∈ queryLimitFn q (us, ys)) :
    ∃ hne : us ≠ [], x = us.getLast hne := by
  simp only [queryLimitFn] at h
  split_ifs at h with h1 h2
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨List.ne_nil_of_length_pos (by omega), h⟩
  · split at h <;> simp at h
  · simp at h

theorem queryLimitFn_inl_mem (q : ℕ) {us : List X} {ys : List (Option Y)}
    (h : us.length = ys.length + 1) (hq : us.length ≤ q) :
    Sum.inl (us.getLast (by apply List.ne_nil_of_length_pos; omega)) ∈
      queryLimitFn q (us, ys) := by
  simp only [queryLimitFn]
  rw [dif_pos ⟨h, hq⟩]
  exact Part.mem_some _

theorem queryLimitFn_inr_mem (q : ℕ) {us : List X} {ys : List (Option Y)}
    (h : us.length = ys.length) (h0 : 0 < ys.length) (hq : us.length ≤ q)
    {y : Y} (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some y) :
    Sum.inr y ∈ queryLimitFn q (us, ys) := by
  simp only [queryLimitFn]
  rw [dif_neg (by omega), dif_pos ⟨h, h0, hq⟩, hy]
  exact Part.mem_some _

/-- **Stress test — expected tree shape with a budget.**  The trace tree of
`[q]` is the length lattice cut at the budget, refined by the someness
discipline — and it *includes* the query-pending pairs at round `q+1` (the
breach arrives; ν is undefined there, see `queryLimitFn_breach`). -/
theorem reach_queryLimitFn_iff (q : ℕ) (p : List X × List (Option Y)) :
    Reach (queryLimitFn q) p ↔
      (p.1.length = p.2.length + 1 ∧ p.1.length ≤ q + 1 ∧
          ∀ oy ∈ p.2, oy.isSome) ∨
        (p.1.length = p.2.length ∧ 0 < p.1.length ∧ p.1.length ≤ q ∧
          ∀ oy ∈ p.2.dropLast, oy.isSome) := by
  constructor
  · intro h
    induction h with
    | first u =>
        dsimp only
        refine Or.inl ⟨by simp, ?_, by simp⟩
        simp only [List.length_singleton]
        omega
    | answer hr hx y ih =>
        obtain ⟨hlen, hq⟩ := queryLimitFn_inl_inv hx
        dsimp only at ih ⊢
        rcases ih with ⟨-, -, hsome⟩ | ⟨h', -⟩
        · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · omega
          · omega
          · rw [List.dropLast_concat]
            exact hsome
        · omega
    | next hr hv u ih =>
        rename_i us ys v
        obtain ⟨hlen, hq, h0, hy⟩ := queryLimitFn_inr_inv hv
        dsimp only at ih ⊢
        rcases ih with ⟨h', -⟩ | ⟨-, -, -, hdrop⟩
        · omega
        · have hall : ∀ oy ∈ ys, oy.isSome := by
            intro oy hmem
            rw [← List.dropLast_append_getLast
              (List.ne_nil_of_length_pos h0)] at hmem
            rcases List.mem_append.mp hmem with hm | hm
            · exact hdrop oy hm
            · rw [List.mem_singleton.mp hm, hy]
              rfl
          refine Or.inl ⟨?_, ?_, hall⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · simp only [List.length_append, List.length_singleton]
            omega
  · obtain ⟨us, ys⟩ := p
    dsimp only
    intro h
    induction ys using List.reverseRecOn generalizing us with
    | nil =>
        simp only [List.length_nil] at h
        rcases h with ⟨h, hq, -⟩ | ⟨h, hpos, -, -⟩
        · obtain ⟨u, rfl⟩ :=
            List.length_eq_one_iff.mp (by omega : us.length = 1)
          exact Reach.first u
        · exact absurd hpos (by omega)
    | append_singleton ys y ih =>
        have hB : ∀ us' : List X, us'.length = ys.length + 1 →
            us'.length ≤ q → (∀ oy ∈ ys, oy.isSome) →
            Reach (queryLimitFn q) (us', ys ++ [y]) := by
          intro us' hlen hq hsome
          exact Reach.answer
            (ih (us := us') (Or.inl ⟨hlen, by omega, hsome⟩))
            (queryLimitFn_inl_mem q hlen hq) y
        simp only [List.length_append, List.length_singleton] at h
        rcases h with ⟨h, hq, hsome⟩ | ⟨h, hpos, hq, hsome⟩
        · have hne : us ≠ [] := by
            apply List.ne_nil_of_length_pos
            omega
          obtain ⟨us', u, rfl⟩ := (List.eq_nil_or_concat us).resolve_left hne
          simp only [List.concat_eq_append, List.length_append,
            List.length_singleton] at h hq ⊢
          obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp
            (hsome y (List.mem_append_right _ (List.mem_singleton_self y)))
          exact Reach.next
            (hB us' (by omega) (by omega)
              (fun oy hm => hsome oy (List.mem_append_left _ hm)))
            (queryLimitFn_inr_mem q
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp) (by omega)
              (by rw [List.getLast_concat]; exact hy'))
            u
        · rw [List.dropLast_concat] at hsome
          exact hB us (by omega) (by omega) hsome

/-- `queryLimitFn` is silent past a `⊥`: on its tree a `⊥` can only be
the last answer, where both branches refuse. -/
theorem answersInY_queryLimitFn (q : ℕ) :
    AnswersInY (queryLimitFn (X := X) (Y := Y) q) := by
  rintro ⟨us, ys⟩ hr hn hd
  have hne' : ys ≠ [] := by
    rintro rfl
    simp at hn
  have hsome : ∀ oy ∈ ys.dropLast, oy.isSome := by
    rcases (reach_queryLimitFn_iff q (us, ys)).mp hr with ⟨-, -, hs⟩ |
      ⟨-, -, -, hs⟩
    · exact fun oy hm => hs oy (List.mem_of_mem_dropLast hm)
    · exact hs
  have hlast : ys.getLast hne' = none := by
    have hn' := hn
    rw [← List.dropLast_append_getLast hne'] at hn'
    rcases List.mem_append.mp hn' with h' | h'
    · exact absurd (hsome _ h') (by simp)
    · exact (List.mem_singleton.mp h').symm
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  cases m with
  | inl x =>
      obtain ⟨h1, -⟩ := queryLimitFn_inl_inv hm
      rcases (reach_queryLimitFn_iff q (us, ys)).mp hr with ⟨-, -, hs⟩ |
        ⟨hlen, -, -, -⟩
      · exact absurd (hs _ hn) (by simp)
      · have hlen' : us.length = ys.length := hlen
        omega
  | inr v =>
      obtain ⟨-, -, h0, hgl⟩ := queryLimitFn_inr_inv hm
      have h1 : ys.getLast (List.ne_nil_of_length_pos h0) = none := hlast
      rw [h1] at hgl
      simp at hgl

/-- `queryLimitFn` never opens a streak of two queries. -/
theorem answersWithin_queryLimitFn (q : ℕ) :
    AnswersWithin (queryLimitFn (X := X) (Y := Y) q) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  obtain ⟨h0, -⟩ := queryLimitFn_inl_inv hx0
  obtain ⟨h1, -⟩ := queryLimitFn_inl_inv hx1
  simp only [List.length_append, List.length_take] at h0 h1
  omega

/-- The `[q]` filter is a DDC (CR18 Def 3.8) — membership in the class:
the budget cut restricts the tree, never the two Def 3.8 clauses. -/
@[rs_rule "rs.is_ddc.query_limit" rs_is_ddc random_systems]
theorem isDDC_queryLimitFn (q : ℕ) :
    IsDDC (queryLimitFn (X := X) (Y := Y) q) :=
  ⟨answersInY_queryLimitFn q, 2, answersWithin_queryLimitFn q⟩

/-- **Stress test — the budget breach is a non-productive spot, not junk.**
The pair "q+1 outer inputs, q answers" is *reachable* (the `(q+1)`-st input
arrives), and ν is *undefined* on it — exactly CR18 Def 3.10's "`[q]s` is
undefined as of the `(q+1)`-st query", now read off the tree. -/
theorem queryLimitFn_breach (q : ℕ) (x : X) (y : Y) :
    Reach (queryLimitFn q)
        (List.replicate (q + 1) x, List.replicate q (some y)) ∧
      ¬ ((queryLimitFn q)
        (List.replicate (q + 1) x, List.replicate q (some y))).Dom := by
  constructor
  · rw [reach_queryLimitFn_iff]
    left
    refine ⟨by simp, by simp, fun oy hmem => ?_⟩
    rw [List.eq_of_mem_replicate hmem]
    rfl
  · intro hdom
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp hdom
    cases m with
    | inl x' =>
        obtain ⟨-, hq⟩ := queryLimitFn_inl_inv hm
        simp only [List.length_replicate] at hq
        omega
    | inr v =>
        obtain ⟨heq, -⟩ := queryLimitFn_inr_inv hm
        simp only [List.length_replicate] at heq
        omega

/-- A junk-carrying variant of `simpleFn`: an extra (never-consulted) value
at the off-tree pairs `k = l + 2`. -/
def simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) : ProtocolFn U V X Y :=
  fun p =>
    if p.1.length = p.2.length + 2 then Part.some (Sum.inl x₀)
    else simpleFn c d p

/-- The junk does not enlarge the tree: `simpleFnJunk`'s tree satisfies the
same length constraints (forward direction suffices for the tests). -/
theorem reach_simpleFnJunk_imp {c : U → X} {d : Y → V} {x₀ : X}
    {p : List U × List (Option Y)} (h : Reach (simpleFnJunk c d x₀) p) :
    p.1.length = p.2.length + 1 ∨
      (p.1.length = p.2.length ∧ 0 < p.1.length) := by
  induction h with
  | first u => simp
  | answer hr hx y ih =>
      rename_i us ys x
      dsimp only at ih ⊢
      have hlen : us.length = ys.length + 1 := by
        by_cases hj : us.length = ys.length + 2
        · exfalso
          rcases ih with h' | ⟨h', -⟩ <;> omega
        · rw [show simpleFnJunk c d x₀ (us, ys) = simpleFn c d (us, ys) from
            by simp [simpleFnJunk, hj]] at hx
          exact simpleFn_inl_inv hx
      simp only [List.length_append, List.length_singleton]
      omega
  | next hr hv u ih =>
      rename_i us ys v
      dsimp only at ih ⊢
      have hlen : us.length = ys.length ∧ 0 < ys.length := by
        by_cases hj : us.length = ys.length + 2
        · exfalso
          rcases ih with h' | ⟨h', -⟩ <;> omega
        · rw [show simpleFnJunk c d x₀ (us, ys) = simpleFn c d (us, ys) from
            by simp [simpleFnJunk, hj]] at hv
          obtain ⟨h1, h0, -⟩ := simpleFn_inr_inv hv
          exact ⟨h1, h0⟩
      simp only [List.length_append, List.length_singleton]
      omega

/-- **Stress test — junk is not junk-free**: the discipline detects the
off-tree value. -/
theorem not_junkFree_simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) (u : U) :
    ¬ JunkFree (simpleFnJunk c d x₀) := by
  intro h
  have hr := h ([u, u], []) (by simp [simpleFnJunk])
  have h2 := reach_simpleFnJunk_imp hr
  simp at h2

/-- **Stress test — junk is invisible to the identity**: the junk-carrying
variant is trace-equal to the clean one … -/
theorem traceEquiv_simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) :
    TraceEquiv (simpleFnJunk c d x₀) (simpleFn c d) := by
  apply traceEquiv_of_eqOn_reach
  · intro p hp
    have hlen := reach_simpleFnJunk_imp hp
    have hj : ¬ p.1.length = p.2.length + 2 := by
      rcases hlen with h | ⟨h, -⟩ <;> omega
    simp [simpleFnJunk, hj]
  · intro p hp
    have hlen := (reach_simpleFn_iff c d p).mp hp
    have hj : ¬ p.1.length = p.2.length + 2 := by
      rcases hlen with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    simp [simpleFnJunk, hj]

/-- … hence presents the same canonical DDC (`toDDC_congr` in action) … -/
theorem toDDC_simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) :
    toDDC (simpleFnJunk c d x₀) = toDDC (simpleFn c d) :=
  toDDC_congr (traceEquiv_simpleFnJunk c d x₀)

/-- … while being *raw*-distinct: the junk is real data, only invisible. -/
theorem simpleFnJunk_ne_simpleFn (c : U → X) (d : Y → V) (x₀ : X) (u : U) :
    simpleFnJunk c d x₀ ≠ simpleFn c d := by
  intro h
  have h2 := congrFun h ([u, u], [])
  simp only [simpleFnJunk, simpleFn] at h2
  rw [if_pos (by simp)] at h2
  rw [dif_neg (by simp), dif_neg (by simp)] at h2
  exact Part.some_ne_none _ h2

/-! #### The quantifier gap in Def 3.8

`AnswersWithin` reads Def 3.8's finite-bound clause as `∃B ∀p`; the
definition's own prose reads it `∀p ∃B`.  The two differ by finiteness of
`sup_p B p`, and this section shows the difference is real by inhabiting it.
-/

/-- **Stress test — the `∃B ∀p` / `∀p ∃B` gap is inhabited.**  The converter
that has issued exactly `k²` inner queries once `k` outer inputs have
arrived: on its `k`-th round it queries `2k−1` times, then answers.  At
every reachable pair it invokes the system a finite number of times and then
returns an output — Def 3.8's prose, verbatim — yet no single `B` bounds all
of its streaks.  (Outer and inner alphabets are `Unit`: the growth is in the
round index alone, nothing is hidden in the data.) -/
def roundGrowthFn : ProtocolFn Unit Unit Unit Unit := fun p =>
  if none ∈ p.2 then Part.none
  else if p.2.length < p.1.length * p.1.length then Part.some (Sum.inl ())
  else Part.some (Sum.inr ())

theorem roundGrowthFn_inl_mem {us : List Unit} {ys : List (Option Unit)}
    (hnone : none ∉ ys) (h : ys.length < us.length * us.length) :
    Sum.inl () ∈ roundGrowthFn (us, ys) := by
  simp only [roundGrowthFn, if_neg hnone, if_pos h]
  exact Part.mem_some _

theorem roundGrowthFn_inr_mem {us : List Unit} {ys : List (Option Unit)}
    (hnone : none ∉ ys) (h : ¬ ys.length < us.length * us.length) :
    Sum.inr () ∈ roundGrowthFn (us, ys) := by
  simp only [roundGrowthFn, if_neg hnone, if_neg h]
  exact Part.mem_some _

/-- `roundGrowthFn` satisfies Def 3.8's input-alphabet clause. -/
theorem answersInY_roundGrowthFn : AnswersInY roundGrowthFn := by
  intro p _ hnone hdom
  obtain ⟨mv, hm⟩ := Part.dom_iff_mem.mp hdom
  simp only [roundGrowthFn, if_pos hnone] at hm
  exact Part.notMem_none _ hm

/-- `roundGrowthFn` satisfies the finite-bound clause with a budget uniform
in the answers and growing with the round index — the `AnswersWithinDepth`
class, which is all the downstream fuel arguments need. -/
theorem answersWithinDepth_roundGrowthFn :
    AnswersWithinDepth roundGrowthFn (fun n => n * n + 1) := by
  intro p _ ext hlen hall
  obtain ⟨x, hx⟩ := hall (p.1.length * p.1.length)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlen)
  simp only [roundGrowthFn] at hx
  split_ifs at hx with h1 h2
  · exact Part.notMem_none _ hx
  · rw [List.length_append, List.length_take] at h2
    have hmin : min (p.1.length * p.1.length) ext.length
        = p.1.length * p.1.length :=
      min_eq_left (le_trans (Nat.le_succ _) hlen)
    omega
  · simp at hx

/-- Both Def 3.8 clauses hold in the prose reading. -/
theorem isDDCEventually_roundGrowthFn : IsDDCEventually roundGrowthFn :=
  ⟨answersInY_roundGrowthFn,
    answersWithinDepth_roundGrowthFn.answersEventually⟩

/-- One more answered query on the `k`-th round's open streak. -/
private theorem reach_roundGrowthFn_step {k m : ℕ}
    (h : Reach roundGrowthFn (List.replicate k (), List.replicate m (some ())))
    (hlt : m < k * k) :
    Reach roundGrowthFn
      (List.replicate k (), List.replicate (m + 1) (some ())) := by
  have hx : Sum.inl () ∈ roundGrowthFn
      (List.replicate k (), List.replicate m (some ())) :=
    roundGrowthFn_inl_mem (by simp) (by simpa using hlt)
  simpa [List.replicate_succ'] using Reach.answer h hx (some ())

/-- The round closes and the next outer input arrives. -/
private theorem reach_roundGrowthFn_next {k m : ℕ}
    (h : Reach roundGrowthFn (List.replicate k (), List.replicate m (some ())))
    (hge : ¬ m < k * k) :
    Reach roundGrowthFn
      (List.replicate (k + 1) (), List.replicate m (some ())) := by
  have hv : Sum.inr () ∈ roundGrowthFn
      (List.replicate k (), List.replicate m (some ())) :=
    roundGrowthFn_inr_mem (by simp) (by simpa using hge)
  simpa [List.replicate_succ'] using Reach.next h hv ()

/-- **The round anchors are reachable**: after `k` completed rounds exactly
`k²` answers have been consumed, and the `(k+1)`-st outer input is in. -/
private theorem reach_roundGrowthFn_anchor (k : ℕ) :
    Reach roundGrowthFn
      (List.replicate (k + 1) (), List.replicate (k * k) (some ())) := by
  induction k with
  | zero =>
      simpa only [List.replicate_one, Nat.zero_mul, List.replicate_zero] using
        Reach.first ()
  | succ k ih =>
      have hsq : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
      have hfill : ∀ j, j ≤ 2 * k + 1 →
          Reach roundGrowthFn (List.replicate (k + 1) (),
            List.replicate (k * k + j) (some ())) := by
        intro j
        induction j with
        | zero => intro _; simpa only [Nat.add_zero] using ih
        | succ j ihj =>
            intro hj
            have hlt : k * k + j < (k + 1) * (k + 1) := by omega
            exact reach_roundGrowthFn_step (ihj (by omega)) hlt
      exact reach_roundGrowthFn_next (hsq ▸ hfill (2 * k + 1) le_rfl)
        (by omega)

/-- **No uniform budget**: the `(B+1)`-st round of `roundGrowthFn` opens a
streak of `2B+1` queries, so `AnswersWithin` fails at every `B`. -/
theorem not_answersWithin_roundGrowthFn (B : ℕ) :
    ¬ AnswersWithin roundGrowthFn B := by
  intro h
  refine h (List.replicate (B + 1) (), List.replicate (B * B) (some ()))
    (reach_roundGrowthFn_anchor B) (List.replicate B (some ()))
    (by simp) ?_
  intro k hk
  rw [List.length_replicate] at hk
  refine ⟨(), roundGrowthFn_inl_mem ?_ ?_⟩
  · simp
  · simp only [List.length_append, List.length_take, List.length_replicate]
    have hsq : (B + 1) * (B + 1) = B * B + (2 * B + 1) := by ring
    omega

/-- **The separation**, kernel-checked: `roundGrowthFn` is a Def 3.8
converter in the prose reading and is not one in the formal reading.  The
class `IsDDC` cuts out is therefore strictly smaller than the class CR18
describes — every theorem proved about `IsDDC` stays sound, but converters
whose per-round query count grows with the round index are outside it. -/
theorem not_isDDC_roundGrowthFn : ¬ IsDDC roundGrowthFn := by
  rintro ⟨-, B, hB⟩
  exact not_answersWithin_roundGrowthFn B hB

/-! The second half of the map: `AnswersEventually` is not merely weaker than
`AnswersWithin`, it is weaker than `AnswersWithinDepth` — a *pointwise* bound
need not assemble into any bound at all as a function of the round index, and
the round index is the only thing a fuel budget may depend on
(`EmulateRealization.Emulable` fixes its inner fuel before the assumed system
is chosen).  `answerGrowthFn` inhabits that second gap. -/

/-- The number of queries `answerGrowthFn` is allowed to have issued: one in
the first round, and thereafter one more than the number the system named in
its first answer. -/
private def growBudget (p : List Unit × List (Option ℕ)) : ℕ :=
  if p.1.length ≤ 1 then 1
  else match p.2.head? with
    | some (some m) => m + 1
    | _ => 1

/-- **Stress test — a pointwise bound need not be a bound in the round
index.**  This converter queries once, reads the number `m` the system
answered, and spends its second round issuing `m` further queries.  At every
reachable pair it stops after finitely many queries — `m` is already fixed
there — but at the *round-two* pairs, all of which have two outer inputs, no
budget depending on the round index alone can cover every `m`. -/
def answerGrowthFn : ProtocolFn Unit Unit Unit ℕ := fun p =>
  if none ∈ p.2 then Part.none
  else if p.2.length < growBudget p then Part.some (Sum.inl ())
  else Part.some (Sum.inr ())

theorem answerGrowthFn_inl_mem {us : List Unit} {ys : List (Option ℕ)}
    (hnone : none ∉ ys) (h : ys.length < growBudget (us, ys)) :
    Sum.inl () ∈ answerGrowthFn (us, ys) := by
  simp only [answerGrowthFn, if_neg hnone, if_pos h]
  exact Part.mem_some _

theorem answerGrowthFn_inr_mem {us : List Unit} {ys : List (Option ℕ)}
    (hnone : none ∉ ys) (h : ¬ ys.length < growBudget (us, ys)) :
    Sum.inr () ∈ answerGrowthFn (us, ys) := by
  simp only [answerGrowthFn, if_neg hnone, if_neg h]
  exact Part.mem_some _

theorem answersInY_answerGrowthFn : AnswersInY answerGrowthFn := by
  intro p _ hnone hdom
  obtain ⟨mv, hm⟩ := Part.dom_iff_mem.mp hdom
  simp only [answerGrowthFn, if_pos hnone] at hm
  exact Part.notMem_none _ hm

/-- The trace invariant that makes the budget stable along a streak: a
second outer input arrives only after the first round has been answered, so
past round one the answer list is nonempty and its head is frozen. -/
private theorem reach_answerGrowthFn_inv {p : List Unit × List (Option ℕ)}
    (h : Reach answerGrowthFn p) : p.1.length ≤ 1 ∨ p.2 ≠ [] := by
  induction h with
  | first u => simp
  | answer hr hx y ih => right; simp
  | next hr hv u ih =>
      rename_i us ys v
      rcases ih with hlen | hne
      · refine Or.inr ?_
        show ys ≠ []
        rintro rfl
        have hb : growBudget (us, ([] : List (Option ℕ))) = 1 := by
          simp only [growBudget]
          rw [if_pos hlen]
        simp [answerGrowthFn, hb] at hv
      · exact Or.inr hne

/-- The budget does not move along a streak out of a reachable pair. -/
private theorem growBudget_append {p : List Unit × List (Option ℕ)}
    (h : Reach answerGrowthFn p) (l : List (Option ℕ)) :
    growBudget (p.1, p.2 ++ l) = growBudget p := by
  rcases reach_answerGrowthFn_inv h with hlen | hne
  · simp only [growBudget, if_pos hlen]
  · obtain ⟨a, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
    simp only [growBudget, hcons, List.cons_append, List.head?_cons]

/-- `answerGrowthFn` satisfies Def 3.8's finite-bound clause **pointwise** —
CR18's prose, verbatim. -/
theorem answersEventually_answerGrowthFn : AnswersEventually answerGrowthFn := by
  intro p hp
  refine ⟨growBudget p + 1, fun ext hlen hall => ?_⟩
  obtain ⟨x, hx⟩ := hall (growBudget p)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlen)
  simp only [answerGrowthFn] at hx
  split_ifs at hx with h1 h2
  · exact Part.notMem_none _ hx
  · rw [growBudget_append hp] at h2
    rw [List.length_append, List.length_take] at h2
    have hmin : min (growBudget p) ext.length = growBudget p :=
      min_eq_left (le_trans (Nat.le_succ _) hlen)
    omega
  · simp at hx

/-- Both Def 3.8 clauses hold in the prose reading. -/
theorem isDDCEventually_answerGrowthFn : IsDDCEventually answerGrowthFn :=
  ⟨answersInY_answerGrowthFn, answersEventually_answerGrowthFn⟩

/-- The round-two anchors — one for each answer the system may have given. -/
private theorem reach_answerGrowthFn_anchor (m : ℕ) :
    Reach answerGrowthFn ([(), ()], [some m]) := by
  have h1 : Reach answerGrowthFn ([()], []) := Reach.first ()
  have hq : Sum.inl () ∈ answerGrowthFn ([()], []) :=
    answerGrowthFn_inl_mem (by simp) (by simp [growBudget])
  have h2 : Reach answerGrowthFn ([()], [some m]) := by
    simpa using Reach.answer h1 hq (some m)
  have hv : Sum.inr () ∈ answerGrowthFn ([()], [some m]) :=
    answerGrowthFn_inr_mem (by simp) (by simp [growBudget])
  simpa using Reach.next h2 hv ()

/-- **No budget in the round index**: every round-two pair has two outer
inputs, and the streak they open is as long as the system's first answer. -/
theorem not_answersWithinDepth_answerGrowthFn (F : ℕ → ℕ) :
    ¬ AnswersWithinDepth answerGrowthFn F := by
  intro h
  refine h ([(), ()], [some (F 2)]) (reach_answerGrowthFn_anchor (F 2))
    (List.replicate (F 2) (some (F 2))) (by simp) ?_
  intro k hk
  rw [List.length_replicate] at hk
  refine ⟨(), answerGrowthFn_inl_mem ?_ ?_⟩
  · simp
  · simp only [growBudget, List.cons_append, List.head?_cons,
      List.length_append, List.length_take, List.length_replicate,
      List.length_cons, List.length_nil]
    norm_num
    omega

/-- **The second separation**, kernel-checked: the prose class is not merely
larger than `IsDDC`, it is larger than the answer-uniform class
`AnswersWithinDepth`.  Since `EmulateRealization`'s inner fuel is a function
of the outer round count *chosen before the assumed system is*, a merely
pointwise bound cannot be turned into fuel at all — which is why the
downstream theory cannot simply be re-based on `IsDDCEventually`. -/
theorem not_answersWithin_answerGrowthFn (B : ℕ) :
    ¬ AnswersWithin answerGrowthFn B := fun h =>
  not_answersWithinDepth_answerGrowthFn (fun _ => B) h.answersWithinDepth

end StressTests

end PFunConverter

end RandomSystems.CR18
