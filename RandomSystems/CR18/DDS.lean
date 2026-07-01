/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.DDS

/-!
# CR18 Deterministic Discrete Systems

This module formalizes CR18 Definition 3.2 faithfully, following project
decision D2: a deterministic discrete `(X, Y)`-system is a partial function
from nonempty input sequences to outputs, with a prefix-closed domain and a
total responder on that domain.

The legacy `RandomSystems/DDS.lean` model,
`Fin q -> (Fin (i + 1) -> X) -> Y`, is the finite total-table specialization:
the query bound is built into the type, so prefix closure is automatic there.
This CR18 module keeps Maurer's partial-function domain explicit.
-/

namespace RandomSystems.CR18

/-- CR18 Definition 3.2: a deterministic discrete `(X, Y)`-system.

Maurer's domain is a subset of `X* \ {eps}`. The field `nonempty_input`
excludes the empty input sequence. The prefix-closure condition is restricted
to nonempty prefixes so it does not force `[]` into the domain. -/
structure DDS (X Y : Type*) where
  dom : Set (List X)
  nonempty_input : [] ∉ dom
  prefix_closed : ∀ {l₁ l₂ : List X}, l₁ <+: l₂ → l₁ ≠ [] → l₂ ∈ dom → l₁ ∈ dom
  respond : (l : List X) → l ∈ dom → Y

namespace DDS

variable {X Y : Type*}

/-- CR18 Definition 3.2: a DDS is finite if its domain is contained in `X^n`
for some `n`. Here `X^n` is represented as lists of length at most `n`. -/
def IsFinite (s : DDS X Y) : Prop :=
  ∃ n : ℕ, ∀ l ∈ s.dom, l.length ≤ n

/-- The output produced by a DDS on an input sequence in its domain. -/
def output (s : DDS X Y) (l : List X) (h : l ∈ s.dom) : Y :=
  s.respond l h

/-- The response of a DDS depends only on the input history, not on the
particular in-domain proof: equal histories give equal responses. -/
theorem respond_congr (s : DDS X Y) {l₁ l₂ : List X} (hl : l₁ = l₂)
    (h₁ : l₁ ∈ s.dom) (h₂ : l₂ ∈ s.dom) :
    s.respond l₁ h₁ = s.respond l₂ h₂ := by
  subst hl; rfl

/-- Extensionality for `DDS`: two systems are equal when their domains agree and
their outputs agree pointwise on the common domain. The output (rather than
`respond`) form is used so the hypothesis is stated through `DDS.output`, which is
how the converter algebra computes; the underlying `respond` heterogeneous
equality is reconstructed internally from the domain equality. -/
theorem ext {s t : DDS X Y} (hdom : s.dom = t.dom)
    (houtput : ∀ (l : List X) (hs : l ∈ s.dom) (ht : l ∈ t.dom),
      s.output l hs = t.output l ht) : s = t := by
  obtain ⟨sdom, sne, spc, sresp⟩ := s
  obtain ⟨tdom, tne, tpc, tresp⟩ := t
  dsimp only at hdom
  subst hdom
  congr 1
  · funext l h
    exact houtput l h h

/- Future work: relate finite `CR18.DDS` values to the total table
`Fin q -> (Fin (i + 1) -> X) -> Y` from `RandomSystems/DDS.lean`. -/

end DDS

end RandomSystems.CR18

namespace RandomSystems.CR18

universe u

/-- CR18 Definition 3.1 (Y-source): the canonical unary trigger alphabet.

We use Lean's universe-polymorphic `PUnit` as the one-element alphabet; its sole
element represents Maurer's trigger symbol `⋄`. The inherited `PUnit` instances
provide the `Subsingleton`, `Unique`, and finite one-element structure expected
of a unary alphabet. -/
abbrev Trigger : Type u :=
  PUnit.{u + 1}

namespace Trigger

/-- CR18 Definition 3.1 (Y-source): the unique trigger symbol `⋄`. -/
abbrev diamond : Trigger :=
  PUnit.unit

end Trigger

/-- CR18 Definition 3.1 (Y-source): a `Y`-source is a DDS whose input alphabet
is unary, so each input is a trigger and each trigger input produces an output
in `Y`. -/
abbrev YSource (Y : Type u) :=
  DDS (Trigger.{u}) Y

namespace DDS

/-- CR18 Definition 3.1 (Y-source): alphabet-level characterization of when a
general deterministic discrete system is a `Y`-source. The defining property is
that its input alphabet is unary: exactly one trigger symbol `{⋄}`. This is
represented by `Nonempty X ∧ Subsingleton X`, excluding the empty alphabet. -/
def IsYSource {X Y : Type*} (_s : DDS X Y) : Prop :=
  Nonempty X ∧ Subsingleton X

end DDS

namespace YSource

/-- CR18 Definition 3.1 (Y-source): memoryless deterministic sources are those
whose output does not depend on the trigger history. This records the remark
that "a source can be memoryless or have memory" at the DDS layer by requiring
all in-domain trigger input sequences to produce the same output. -/
def Memoryless {Y : Type u} (s : YSource Y) : Prop :=
  ∀ {l₁ l₂ : List Trigger} (h₁ : l₁ ∈ s.dom) (h₂ : l₂ ∈ s.dom),
    DDS.output s l₁ h₁ = DDS.output s l₂ h₂

/-- CR18 Definition 3.1 (Y-source): the constant deterministic `Y`-source that
emits the fixed output `y₀` on every nonempty trigger history. -/
def constant {Y : Type u} (y₀ : Y) : YSource Y where
  dom := {l | l ≠ []}
  nonempty_input := fun h => h rfl
  prefix_closed := fun {_l₁ _l₂} _ h_nonempty _ => h_nonempty
  respond := fun _ _ => y₀

/-- CR18 Definition 3.1 (Y-source): the constant deterministic `Y`-source is
memoryless. -/
theorem constant_memoryless {Y : Type u} (y₀ : Y) :
    Memoryless (constant y₀) := by
  simp [Memoryless, constant, DDS.output]

end YSource

end RandomSystems.CR18

namespace RandomSystems.CR18

namespace DDS

variable {X Y : Type*}

/-- CR18 Example 3.1: the deterministic function-evaluator `(X, Y)`-system
computes a fixed function `f : X → Y` on every new input. Its domain is every
nonempty input sequence, and its response to a history is `f` applied to the
current input, represented by the last element of the nonempty sequence. -/
def functionEvaluator (f : X → Y) : DDS X Y where
  dom := {l | l ≠ []}
  nonempty_input := by
    exact fun h => h rfl
  prefix_closed := by
    exact fun {_l₁ _l₂} _ h_nonempty _ => h_nonempty
  respond := fun l h => f (l.getLast h)

/-- CR18 Example 3.1: on a sequence ending in the current input `x`, the
function-evaluator system outputs exactly `f x`, formalizing `Yᵢ = f Xᵢ`. -/
theorem functionEvaluator_output (f : X → Y) (l : List X) (x : X)
    (h : l ++ [x] ∈ (functionEvaluator f).dom) :
    (functionEvaluator f).output (l ++ [x]) h = f x := by
  simp [functionEvaluator, DDS.output]

/-- CR18 Example 3.1: the function-evaluator output depends only on the
current input, i.e. on the last element of the nonempty input sequence, and not
on the preceding history. -/
theorem functionEvaluator_output_eq_of_getLast_eq (f : X → Y)
    {l₁ l₂ : List X} (h₁ : l₁ ∈ (functionEvaluator f).dom)
    (h₂ : l₂ ∈ (functionEvaluator f).dom)
    (h_last : l₁.getLast h₁ = l₂.getLast h₂) :
    (functionEvaluator f).output l₁ h₁ = (functionEvaluator f).output l₂ h₂ := by
  exact congrArg f h_last

/-- CR18 Definition 3.3 / footnote 6: the kept prefix obtained by scanning an
input sequence from left to right and deleting exactly those next inputs that
would make the original partial DDS undefined.

The membership test for `s.dom` is not generally decidable, so the construction
is parameterized by an explicit `DecidablePred` witness for `s.dom`. -/
def keptPrefix (s : DDS X Y) [DecidablePred (fun l => l ∈ s.dom)] : List X → List X :=
  List.foldl (fun acc x => if acc ++ [x] ∈ s.dom then acc ++ [x] else acc) []

/-- CR18 Definition 3.3: the fully defined completion `s⊥` of a DDS `s`.

The codomain `Option Y` models `Y ∪ {⊥}`: `some y` is an original output
`y : Y`, while `none` is the distinguished bottom value `⊥`. The completed DDS
is defined on every nonempty input sequence. The deletion pass is run only on
the strict prefix of the input history; the final input is always appended and
then tested against the original domain, as in Maurer's footnote 6. -/
def fullyDefined (s : DDS X Y) [DecidablePred (fun l => l ∈ s.dom)] :
    DDS X (Option Y) where
  dom := {l | l ≠ []}
  nonempty_input := fun h => h rfl
  prefix_closed := fun {_l₁ _l₂} _ h_nonempty _ => h_nonempty
  respond := fun l h =>
    let ctx := keptPrefix s l.dropLast
    let cand := ctx ++ [l.getLast h]
    if hcand : cand ∈ s.dom then
      some (s.respond cand hcand)
    else
      none

/-- CR18 Definition 3.3: output characterization for the fully defined
completion `s⊥`. It runs the deletion pass on the strict prefix, force-appends
the final input, and returns `⊥` (`none`) precisely when that candidate is not
in the original domain. -/
@[simp]
theorem fullyDefined_output (s : DDS X Y) [DecidablePred (fun l => l ∈ s.dom)]
    (l : List X) (h : l ∈ (fullyDefined s).dom) :
    (fullyDefined s).output l h =
      let ctx := keptPrefix s l.dropLast
      let cand := ctx ++ [l.getLast h]
      if hcand : cand ∈ s.dom then
        some (s.respond cand hcand)
      else
        none := by
  rfl

/-- CR18 Definition 3.3: respond-level defining equation for the fully defined
completion `s⊥`, with the `let`-bindings of the definition unfolded. This is the
form used to chain `fullyDefined` with other defining equations. -/
theorem fullyDefined_respond (s : DDS X Y) [DecidablePred (fun l => l ∈ s.dom)]
    (l : List X) (h : l ∈ (fullyDefined s).dom) :
    (fullyDefined s).respond l h =
      if hcand : keptPrefix s l.dropLast ++ [l.getLast h] ∈ s.dom then
        some (s.respond (keptPrefix s l.dropLast ++ [l.getLast h]) hcand)
      else
        none := rfl

/-- CR18 Definition 3.3 / footnote 6: after the left-to-right deletion pass, the
kept prefix is either a valid input sequence for the original DDS or is empty.
The empty case is the situation where no accepted nonempty prefix has been kept,
so the fully defined completion returns `⊥`. -/
theorem keptPrefix_mem_or (s : DDS X Y) [DecidablePred (fun l => l ∈ s.dom)]
    (l : List X) : keptPrefix s l ∈ s.dom ∨ keptPrefix s l = [] := by
  let step : List X → X → List X := fun acc x =>
    if acc ++ [x] ∈ s.dom then acc ++ [x] else acc
  have hfold : ∀ xs acc, acc ∈ s.dom ∨ acc = [] →
      List.foldl step acc xs ∈ s.dom ∨ List.foldl step acc xs = [] := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons x xs ih =>
        intro acc hacc
        apply ih
        dsimp [step]
        by_cases hx : acc ++ [x] ∈ s.dom
        · left
          simp [hx]
        · simpa [hx] using hacc
  simpa [keptPrefix, step] using hfold l [] (Or.inr rfl)

private def footnote6IsBinaryInput (x : Nat) : Bool :=
  x == 0 || x == 1

private def footnote6IsBinaryHistory (l : List Nat) : Bool :=
  l.all footnote6IsBinaryInput

private def footnote6BinaryDDS : DDS Nat PUnit where
  dom := {l | l ≠ [] ∧ footnote6IsBinaryHistory l = true}
  nonempty_input := by
    simp
  prefix_closed := by
    intro l₁ l₂ hprefix hne hdom
    refine ⟨hne, ?_⟩
    apply List.all_eq_true.2
    intro x hx
    exact (List.all_eq_true.1 hdom.2) x
      (List.Sublist.mem hx (List.IsPrefix.sublist hprefix))
  respond := fun _ _ => PUnit.unit

private instance : DecidablePred (fun l => l ∈ footnote6BinaryDDS.dom) := by
  intro l
  unfold footnote6BinaryDDS footnote6IsBinaryHistory footnote6IsBinaryInput
  infer_instance

private example :
    (fullyDefined footnote6BinaryDDS).output [0, 2, 1, 2, 1]
      (by simp [fullyDefined]) = some PUnit.unit := by
  native_decide

private example :
    (fullyDefined footnote6BinaryDDS).output [0, 2, 1, 2, 1, 2]
      (by simp [fullyDefined]) = none := by
  native_decide

end DDS

end RandomSystems.CR18

namespace RandomSystems.CR18

namespace DDS

universe u v

variable {n : ℕ} {X : Fin n → Type u} {Y : Fin n → Type v}

/-- CR18 Definition 3.4: restrict a tagged parallel-composition input history
to the component with index `j`, keeping exactly the second components of
queries tagged by `j`.

This is the Lean encoding of `(x₁, ..., xₖ)|ⱼ`: the input alphabet of the
parallel system is the dependent tagged union `Sigma X`, and the equality check
on tags determines whether a payload can be transported into `X j`. -/
def restrict (j : Fin n) (l : List (Sigma X)) : List (X j) :=
  l.filterMap fun p =>
    if h : p.fst = j then
      some (cast (congrArg X h) p.snd)
    else
      none

/-- Restricting a tagged history to one component preserves prefix order. -/
theorem restrict_prefix (i : Fin n) {l₁ l₂ : List (Sigma X)} (h : l₁ <+: l₂) :
    restrict i l₁ <+: restrict i l₂ := by
  rcases h with ⟨t, rfl⟩
  use restrict i t
  simp [restrict, List.filterMap_append]

/-- If a tagged history ends in component `i`, its restriction to `i` is
nonempty. -/
theorem restrict_ne_nil_of_getLast_eq_some
    {i : Fin n} {x : X i} {l : List (Sigma X)}
    (hlast : l.getLast? = some ⟨i, x⟩) :
    restrict i l ≠ [] := by
  have hmem : (⟨i, x⟩ : Sigma X) ∈ l.getLast? := by
    simp [hlast]
  have hdecomp : l.dropLast ++ [⟨i, x⟩] = l :=
    List.dropLast_append_getLast? _ hmem
  intro hnil
  rw [← hdecomp] at hnil
  simp [restrict] at hnil

/-- Restriction of the empty tagged history is empty. -/
theorem restrict_nil (i : Fin n) : restrict i ([] : List (Sigma X)) = [] := rfl

/-- Restriction distributes over concatenation of tagged histories. -/
theorem restrict_append (i : Fin n) (l₁ l₂ : List (Sigma X)) :
    restrict i (l₁ ++ l₂) = restrict i l₁ ++ restrict i l₂ := by
  simp [restrict, List.filterMap_append]

/-- Restricting to the tag of a newly consed query keeps its payload. -/
theorem restrict_cons_self (j : Fin n) (x : X j) (l : List (Sigma X)) :
    restrict j (⟨j, x⟩ :: l) = x :: restrict j l := by
  simp [restrict]

/-- Restricting to a different tag drops a newly consed query. -/
theorem restrict_cons_ne {i j : Fin n} (hij : j ≠ i) (x : X j)
    (l : List (Sigma X)) :
    restrict i (⟨j, x⟩ :: l) = restrict i l := by
  simp [restrict, hij]

/-- Restricting to the tag of a newly appended query appends its payload. -/
theorem restrict_concat_self (j : Fin n) (x : X j) (l : List (Sigma X)) :
    restrict j (l ++ [⟨j, x⟩]) = restrict j l ++ [x] := by
  rw [restrict_append, restrict_cons_self, restrict_nil]

/-- Restricting to a different tag drops a newly appended query. -/
theorem restrict_concat_ne {i j : Fin n} (hij : j ≠ i) (x : X j)
    (l : List (Sigma X)) :
    restrict i (l ++ [⟨j, x⟩]) = restrict i l := by
  rw [restrict_append, restrict_cons_ne hij, restrict_nil, List.append_nil]

/-- CR18 Definition 3.4: parallel composition of deterministic discrete
systems.

For a family `s i` of `(X i, Y i)`-DDSs, the composed system has input alphabet
`Sigma X`, the tagged disjoint union of the component inputs, and output
alphabet `Sigma Y`, the tagged disjoint union of component outputs. On a
nonempty input history, the tag of the last query selects the active component;
the selected component receives the projection of the whole tagged history to
that tag. -/
def parallel (s : (i : Fin n) → DDS (X i) (Y i)) : DDS (Sigma X) (Sigma Y) where
  dom := {l | l ≠ [] ∧ ∀ i : Fin n, restrict i l = [] ∨ restrict i l ∈ (s i).dom}
  nonempty_input := by
    simp
  prefix_closed := by
    intro l₁ l₂ hprefix hnonempty hdom
    refine ⟨hnonempty, ?_⟩
    intro i
    rcases hdom.2 i with hrest_empty | hrest_dom
    · left
      rcases restrict_prefix i hprefix with ⟨t, ht⟩
      rw [hrest_empty] at ht
      simp at ht
      exact ht.1
    · by_cases hrest₁ : restrict i l₁ = []
      · exact Or.inl hrest₁
      · exact Or.inr ((s i).prefix_closed (restrict_prefix i hprefix) hrest₁ hrest_dom)
  respond := fun l h =>
    match hlast : l.getLast? with
    | some p =>
        Sigma.mk p.fst ((s p.fst).respond (restrict p.fst l) (by
          have hne : restrict p.fst l ≠ [] := by
            exact restrict_ne_nil_of_getLast_eq_some hlast
          rcases h.2 p.fst with hempty | hdom
          · exact False.elim (hne hempty)
          · exact hdom))
    | none =>
        False.elim (h.1 (List.getLast?_eq_none_iff.mp hlast))

/-- CR18 Definition 3.4: defining equation for parallel composition.

If the final tagged input in `l` has index `j`, then the composed DDS responds
with the response of subsystem `j` on the restriction of the tagged history to
that subsystem, re-tagged as an element of `Sigma Y`. -/
theorem parallel_output (s : (i : Fin n) → DDS (X i) (Y i))
    (l : List (Sigma X)) (h : l ∈ (parallel s).dom)
    {j : Fin n} {x : X j} (hlast : l.getLast? = some ⟨j, x⟩) :
    (parallel s).output l h =
      Sigma.mk j ((s j).respond (restrict j l) (by
        have hne : restrict j l ≠ [] := by
          exact restrict_ne_nil_of_getLast_eq_some hlast
        rcases h.2 j with hempty | hdom
        · exact False.elim (hne hempty)
        · exact hdom)) := by
  simp [parallel, DDS.output]
  split
  · rename_i p hp
    have hpj : p = Sigma.mk j x := by
      simpa [hp] using hlast
    cases hpj
    rfl
  · rename_i hn
    simp [hn] at hlast

/-- CR18 Definition 3.4: appending one tagged query `⟨j, x⟩` to a history whose
component restrictions are each empty or accepted lands in the parallel domain
iff component `j` accepts its extended restriction. This is the equational
membership law driving the deletion-pass commutation below. -/
theorem append_singleton_mem_parallel_dom_iff (s : (i : Fin n) → DDS (X i) (Y i))
    {acc : List (Sigma X)}
    (hinv : ∀ i : Fin n, restrict i acc = [] ∨ restrict i acc ∈ (s i).dom)
    (j : Fin n) (x : X j) :
    acc ++ [⟨j, x⟩] ∈ (parallel s).dom ↔ restrict j acc ++ [x] ∈ (s j).dom := by
  constructor
  · intro hmem
    rcases hmem.2 j with hempty | hdom
    · rw [restrict_concat_self] at hempty
      simp at hempty
    · rwa [restrict_concat_self] at hdom
  · intro hj
    refine ⟨by simp, fun i => ?_⟩
    by_cases hij : i = j
    · subst hij
      rw [restrict_concat_self]
      exact Or.inr hj
    · rw [restrict_concat_ne (Ne.symm hij)]
      exact hinv i

/-- CR18 Definition 3.4 / footnote 6: each component restriction of a kept
prefix of the parallel composition is empty or accepted by its component. -/
theorem restrict_keptPrefix_parallel_or (s : (i : Fin n) → DDS (X i) (Y i))
    [DecidablePred (fun l : List (Sigma X) => l ∈ (parallel s).dom)]
    (m : List (Sigma X)) (i : Fin n) :
    restrict i (keptPrefix (parallel s) m) = [] ∨
      restrict i (keptPrefix (parallel s) m) ∈ (s i).dom := by
  rcases keptPrefix_mem_or (parallel s) m with hdom | hempty
  · exact hdom.2 i
  · rw [hempty, restrict_nil]
    exact Or.inl rfl

/-- CR18 Definition 3.4 / footnote 6 (key commutation law): the left-to-right
deletion pass of the parallel composition commutes with restriction to any
component. Deleting the tagged queries that make `[s₁, …, sₙ]` undefined and
then projecting to component `j` is the same as projecting first and then
deleting the queries that make `sⱼ` undefined: a tagged query `⟨i, x⟩` is kept
by the parallel pass iff `x` is kept by component `i`'s pass, and it is
invisible to every other component. -/
theorem restrict_keptPrefix_parallel (s : (i : Fin n) → DDS (X i) (Y i))
    [∀ i : Fin n, DecidablePred (fun l : List (X i) => l ∈ (s i).dom)]
    [DecidablePred (fun l : List (Sigma X) => l ∈ (parallel s).dom)]
    (j : Fin n) (m : List (Sigma X)) :
    restrict j (keptPrefix (parallel s) m) = keptPrefix (s j) (restrict j m) := by
  suffices h : ∀ (xs acc : List (Sigma X)),
      (∀ i : Fin n, restrict i acc = [] ∨ restrict i acc ∈ (s i).dom) →
      restrict j (List.foldl
          (fun acc p => if acc ++ [p] ∈ (parallel s).dom then acc ++ [p] else acc)
          acc xs) =
        List.foldl
          (fun acc x => if acc ++ [x] ∈ (s j).dom then acc ++ [x] else acc)
          (restrict j acc) (restrict j xs) by
    simpa [keptPrefix, restrict_nil] using h m [] (fun i => Or.inl (restrict_nil i))
  intro xs
  induction xs with
  | nil =>
      intro acc _hinv
      simp [restrict_nil]
  | cons p xs ih =>
      intro acc hinv
      obtain ⟨i, r⟩ := p
      by_cases hmem : acc ++ [⟨i, r⟩] ∈ (parallel s).dom
      · have hinv' : ∀ k : Fin n, restrict k (acc ++ [⟨i, r⟩]) = [] ∨
            restrict k (acc ++ [⟨i, r⟩]) ∈ (s k).dom := fun k => hmem.2 k
        by_cases hij : i = j
        · subst hij
          simp only [List.foldl_cons, restrict_cons_self]
          rw [if_pos hmem,
            if_pos ((append_singleton_mem_parallel_dom_iff s hinv i r).mp hmem),
            ih _ hinv', restrict_concat_self]
        · simp only [List.foldl_cons, restrict_cons_ne hij]
          rw [if_pos hmem, ih _ hinv', restrict_concat_ne hij]
      · by_cases hij : i = j
        · subst hij
          simp only [List.foldl_cons, restrict_cons_self]
          rw [if_neg hmem,
            if_neg (fun hc => hmem
              ((append_singleton_mem_parallel_dom_iff s hinv i r).mpr hc)),
            ih _ hinv]
        · simp only [List.foldl_cons, restrict_cons_ne hij]
          rw [if_neg hmem, ih _ hinv]

/-- CR18 Definition 3.4: reindex the output of the parallel composition of
fully defined component systems into the output type of the fully defined
parallel system.

The left-hand construction has output alphabet `Option (Sigma Y)`, while the
right-hand construction has output alphabet `Sigma (fun i => Option (Y i))`.
This map is the evident comparison: `some y` stays tagged by its component, and
component-level `none` becomes global `none`. -/
def optionSigma : Sigma (fun i : Fin n => Option (Y i)) → Option (Sigma Y)
  | ⟨i, some y⟩ => some ⟨i, y⟩
  | ⟨_, none⟩ => none

/-- CR18 Definition 3.4: fully defining a parallel composition agrees
extensionally with taking the parallel composition of the fully defined
component systems, up to the canonical `Option`/`Sigma` reindexing.

This formalizes `[s₁, ..., sₙ]⊥ = [s₁⊥, ..., sₙ⊥]` at the output level. -/
theorem parallel_fullyDefined (s : (i : Fin n) → DDS (X i) (Y i))
    [∀ i : Fin n, DecidablePred (fun l : List (X i) => l ∈ (s i).dom)]
    [DecidablePred (fun l : List (Sigma X) => l ∈ (parallel s).dom)]
    (l : List (Sigma X))
    (hLeft : l ∈ (fullyDefined (parallel s)).dom)
    (hRight : l ∈ (parallel (fun i => fullyDefined (s i))).dom) :
    (fullyDefined (parallel s)).output l hLeft =
      optionSigma ((parallel (fun i => fullyDefined (s i))).output l hRight) := by
  -- Split off the final tagged query: `l = m ++ [⟨j, x⟩]`.
  have hne : l ≠ [] := hLeft
  obtain ⟨⟨j, x⟩, hlast⟩ : ∃ p : Sigma X, l.getLast? = some p :=
    ⟨l.getLast hne, List.getLast?_eq_some_getLast hne⟩
  obtain ⟨m, rfl⟩ : ∃ m : List (Sigma X), l = m ++ [⟨j, x⟩] :=
    ⟨l.dropLast, (List.dropLast_append_getLast? _ (by simp [hlast])).symm⟩
  have hlast' : (m ++ [(⟨j, x⟩ : Sigma X)]).getLast? = some (⟨j, x⟩ : Sigma X) :=
    List.getLast?_concat
  -- Defining-equation form of both sides.
  have hpar := parallel_output (fun i => fullyDefined (s i))
    (m ++ [(⟨j, x⟩ : Sigma X)]) hRight hlast'
  rw [hpar]
  simp only [DDS.output]
  rw [fullyDefined_respond (parallel s), fullyDefined_respond (s j)]
  simp only [restrict_concat_self, List.dropLast_concat, List.getLast_concat]
  -- The two deletion-pass candidates are accepted simultaneously, by the
  -- kept-prefix invariant and the deletion-pass commutation law.
  have hiff : keptPrefix (parallel s) m ++ [⟨j, x⟩] ∈ (parallel s).dom ↔
      keptPrefix (s j) (restrict j m) ++ [x] ∈ (s j).dom := by
    rw [append_singleton_mem_parallel_dom_iff s
        (restrict_keptPrefix_parallel_or s m) j x,
      restrict_keptPrefix_parallel s j m]
  by_cases hC : keptPrefix (s j) (restrict j m) ++ [x] ∈ (s j).dom
  · rw [dif_pos (hiff.mpr hC), dif_pos hC]
    have hrl : restrict j (keptPrefix (parallel s) m ++ [⟨j, x⟩]) =
        keptPrefix (s j) (restrict j m) ++ [x] := by
      rw [restrict_concat_self, restrict_keptPrefix_parallel s j m]
    have hout : (parallel s).output (keptPrefix (parallel s) m ++ [⟨j, x⟩])
        (hiff.mpr hC) = _ :=
      parallel_output s _ (hiff.mpr hC) List.getLast?_concat
    exact congrArg some (hout.trans (congrArg (Sigma.mk j)
      ((s j).respond_congr hrl _ hC)))
  · rw [dif_neg (fun hc => hC (hiff.mp hc)), dif_neg hC]
    rfl

/-- CR18 Definition 3.5: a deterministic resource with interface set `I`,
input alphabet `X`, and output alphabet `Y` is an `(I × X, Y)`-DDS. -/
def Resource (I A B : Type*) :=
  DDS (I × A) B

namespace Resource

variable {I A B : Type*}

/-- The interface component of one resource input. -/
def inputInterface (p : I × A) : I :=
  p.1

/-- The interface at which the output is delivered: the interface tag of the
last input in the history, when such an input exists. This records the CR18
remark that the output is given at the same interface where the input was
given. -/
def outputInterface? (l : List (I × A)) : Option I :=
  l.getLast?.map inputInterface

@[simp]
theorem outputInterface?_append_singleton (l : List (I × A)) (i : I) (x : A) :
    outputInterface? (l ++ [(i, x)]) = some i := by
  simp [outputInterface?, inputInterface]

/-- CR18 §3.2.3 (interface-partition notation): in the tagged `I × A` encoding
of Definition 3.5, the sub-alphabet of inputs given at interface `i` is
`Xᵢ = {i} × A` — the fiber of `inputInterface` over `i`. Maurer's untagged
partition `X = X₁ ∪ ⋯ ∪ Xₙ` (with `Xᵢ ∩ Xⱼ = {}` for `i ≠ j`) is realized by
these fibers; the two partition laws are `interfaceAlphabet_disjoint` and
`iUnion_interfaceAlphabet`. -/
def interfaceAlphabet (I A : Type*) (i : I) : Set (I × A) :=
  {p | inputInterface p = i}

/-- CR18 §3.2.3: the interface sub-alphabets are mutually disjoint
(`Xᵢ ∩ Xⱼ = {}` for `i ≠ j`). -/
theorem interfaceAlphabet_disjoint (I A : Type*) {i j : I} (hij : i ≠ j) :
    interfaceAlphabet I A i ∩ interfaceAlphabet I A j = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, interfaceAlphabet, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hi hj => hij (hi.symm.trans hj)

/-- CR18 §3.2.3: the interface sub-alphabets cover the input alphabet
(`X = X₁ ∪ ⋯ ∪ Xₙ`). -/
theorem iUnion_interfaceAlphabet (I A : Type*) :
    ⋃ i : I, interfaceAlphabet I A i = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, interfaceAlphabet, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact ⟨inputInterface p, rfl⟩

/-- Forget the tag of a uniformly tagged output. -/
def sigmaPayload {J : Type*} {B : Type v} : Sigma (fun _ : J => B) → B
  | ⟨_, y⟩ => y

/-- Re-tag a resource input as the corresponding `Sigma` input used by
`DDS.parallel`. -/
def prodToSigma {m : ℕ} {A : Type u} (p : Fin m × A) : Sigma (fun _ : Fin m => A) :=
  ⟨p.1, p.2⟩

/-- CR18 Definition 3.5, remark after Definition 3.5: with different
input/output alphabets at different interfaces, Definition 3.4 models the
resource as the tagged parallel composition over the interface set `Fin n`. -/
def taggedParallel {m : ℕ} {A : Fin m → Type u} {B : Fin m → Type v}
    (s : (i : Fin m) → DDS (A i) (B i)) : DDS (Sigma A) (Sigma B) :=
  parallel s

/-- CR18 Definition 3.5, remark after Definition 3.5: for a uniform family of
interfaces, Definition 3.4's parallel composition over `Fin n` yields a
resource by identifying `(Fin n) × X` with the tagged `Sigma` input alphabet and
forgetting the redundant output tag. -/
def uniformParallel {m : ℕ} {A : Type u} {B : Type v} (s : (i : Fin m) → DDS A B) :
    Resource (Fin m) A B where
  dom := {l | List.map prodToSigma l ∈ (parallel (fun i => s i)).dom}
  nonempty_input := by
    exact (parallel (fun i => s i)).nonempty_input
  prefix_closed := by
    intro l₁ l₂ hprefix hnonempty hdom
    exact (parallel (fun i => s i)).prefix_closed (by simpa using hprefix.map prodToSigma)
      (by simpa using hnonempty) hdom
  respond := fun l h =>
    sigmaPayload ((parallel (fun i => s i)).respond (List.map prodToSigma l) h)

/-- The uniform resource bridge computes by running `DDS.parallel` on the
corresponding tagged history, then dropping the redundant output tag. -/
theorem uniformParallel_output {m : ℕ} {A : Type u} {B : Type v}
    (s : (i : Fin m) → DDS A B) (l : List (Fin m × A))
    (h : l ∈ (uniformParallel s).dom) :
    (uniformParallel s).output l h =
      sigmaPayload ((parallel (fun i => s i)).output (List.map prodToSigma l) h) := by
  rfl

end Resource

end DDS

end RandomSystems.CR18

namespace RandomSystems.CR18

namespace DDS

variable {X Y : Type*} {q : ℕ}

/-- CR18 Definition 3.2: the finite-domain specialization whose domain is
exactly the nonempty input sequences of length at most `q`. -/
def FinDomain (X : Type*) (q : ℕ) : Set (List X) :=
  {l | l ≠ [] ∧ l.length ≤ q}

/-- CR18 Definition 3.2: the finite domain excludes the empty input sequence. -/
theorem FinDomain_nonempty_input (X : Type*) (q : ℕ) :
    [] ∉ FinDomain X q := by
  exact fun h => h.1 rfl

/-- CR18 Definition 3.2: the finite domain is closed under nonempty prefixes. -/
theorem FinDomain_prefix_closed {X : Type*} {q : ℕ} {l₁ l₂ : List X}
    (hprefix : l₁ <+: l₂) (hne : l₁ ≠ []) (hdom : l₂ ∈ FinDomain X q) :
    l₁ ∈ FinDomain X q := by
  exact ⟨hne, le_trans (List.IsPrefix.length_le hprefix) hdom.2⟩

/-- CR18 Definition 3.2: a legacy finite total-table DDS as the corresponding
partial-function DDS on exactly the nonempty histories of length at most `q`. -/
def finiteTableDDS (t : RandomSystems.DDS X Y q) : RandomSystems.CR18.DDS X Y where
  dom := FinDomain X q
  nonempty_input := FinDomain_nonempty_input X q
  prefix_closed := by
    intro l₁ l₂ hprefix hne hdom
    exact FinDomain_prefix_closed hprefix hne hdom
  respond := fun l h =>
    t.respond ⟨l.length - 1, by
      have hlen_pos : 0 < l.length := List.length_pos_iff.mpr h.1
      have hlen_le : l.length ≤ q := h.2
      omega⟩ (fun j => l.get ⟨j.val, by
        have hlen_pos : 0 < l.length := List.length_pos_iff.mpr h.1
        have hj : j.val < l.length - 1 + 1 := j.isLt
        omega⟩)

/-- CR18 Definition 3.2: the subtype of CR18 DDSs with exactly the finite
nonempty length-`≤ q` domain. -/
def FiniteTableDDS (X Y : Type*) (q : ℕ) :=
  {s : RandomSystems.CR18.DDS X Y // s.dom = FinDomain X q}

/-- CR18 Definition 3.2: equivalence between the legacy fixed-`q` table DDS and
the CR18 finite specialization with domain exactly the nonempty histories of
length at most `q`. -/
def finiteTableEquiv (X Y : Type*) (q : ℕ) :
    RandomSystems.DDS X Y q ≃ FiniteTableDDS X Y q where
  toFun t := ⟨finiteTableDDS t, rfl⟩
  invFun s :=
    { respond := fun i f =>
        let l : List X := List.ofFn f
        have hmem : l ∈ s.val.dom := by
          have hfin : l ∈ FinDomain X q := by
            constructor
            · apply List.length_pos_iff.mp
              dsimp [l]
              simp [List.length_ofFn]
            · dsimp [l]
              rw [List.length_ofFn]
              omega
          rw [s.property]
          exact hfin
        s.val.respond l hmem }
  left_inv := by
    intro t
    apply RandomSystems.DDS.ext
    funext i f
    apply RandomSystems.DDS.respond_congr_val t
    · simp [List.length_ofFn]
    · intro k hki hkj
      cases k <;> simp [List.getElem_ofFn]
  right_inv := by
    intro s
    rcases s with ⟨⟨dom, hne, hpref, resp⟩, hs⟩
    apply Subtype.ext
    dsimp at hs ⊢
    subst dom
    simp [finiteTableDDS]
    funext l h
    cases l with
    | nil => cases h.1 rfl
    | cons x xs => simp [List.ofFn_getElem]

end DDS

end RandomSystems.CR18
