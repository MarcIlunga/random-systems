/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.DDS

/-!
# PFun-native deterministic discrete systems

This module gives a parallel presentation of CR18 deterministic discrete
systems using mathlib's partial functions (`PFun`, notation `α →. β`).

The existing `RandomSystems.CR18.DDS` record remains the compatibility API used
by the current CR18 development.  This module does not replace it; it provides a
clean partial-function model and bridge maps so future Maurer-style proofs can
move in this direction without breaking existing downstream files.
-/

namespace RandomSystems.CR18

namespace PFunDDS

universe u v w

noncomputable section

open Classical

/-- Raw partial-function presentation of a deterministic discrete system. -/
abbrev Raw (X : Type u) (Y : Type v) : Type (max u v) :=
  List X →. Y

/-- Maurer's DDS domain condition for a raw partial function: the empty input
history is outside the domain, and the domain is closed under nonempty prefixes. -/
def Valid {X : Type u} {Y : Type v} (S : Raw X Y) : Prop :=
  [] ∉ S.Dom ∧
    ∀ {l₁ l₂ : List X}, l₁ <+: l₂ → l₁ ≠ [] → l₂ ∈ S.Dom → l₁ ∈ S.Dom

/-- PFun-native deterministic discrete systems, kept in parallel with the
existing `RandomSystems.CR18.DDS` record during migration. -/
abbrev DDS (X : Type u) (Y : Type v) : Type (max u v) :=
  { S : Raw X Y // Valid S }

variable {X : Type u} {Y : Type v}

/-- The partial function underlying a PFun-native DDS. -/
def toPFun (S : DDS X Y) : Raw X Y :=
  S.1

instance : Coe (DDS X Y) (Raw X Y) where
  coe := toPFun

/-- The domain of a PFun-native DDS. -/
def dom (S : DDS X Y) : Set (List X) :=
  S.1.Dom

@[simp]
theorem dom_def (S : DDS X Y) : dom S = S.1.Dom :=
  rfl

/-- The output produced by a PFun-native DDS on an input sequence in its domain. -/
def output (S : DDS X Y) (l : List X) (h : l ∈ dom S) : Y :=
  S.1.fn l h

/-- The output of a PFun-native DDS depends only on the input history, not on
the particular in-domain proof. -/
theorem output_congr (S : DDS X Y) {l₁ l₂ : List X} (hl : l₁ = l₂)
    (h₁ : l₁ ∈ dom S) (h₂ : l₂ ∈ dom S) :
    output S l₁ h₁ = output S l₂ h₂ := by
  subst hl
  rfl

/-- The validity proof bundled in a PFun-native DDS. -/
theorem valid (S : DDS X Y) : Valid S.1 :=
  S.2

theorem empty_not_mem (S : DDS X Y) : [] ∉ dom S :=
  (valid S).1

theorem prefix_closed (S : DDS X Y) {l₁ l₂ : List X}
    (hprefix : l₁ <+: l₂) (hne : l₁ ≠ []) (hdom : l₂ ∈ dom S) :
    l₁ ∈ dom S :=
  (valid S).2 hprefix hne hdom

/-! ### Stateless deterministic systems -/

/-- A function `f : X → Y` as a DDS: every nonempty input history is accepted,
and the answer is `f` applied to the most recent input. -/
def functionEvaluator (f : X → Y) : DDS X Y :=
  ⟨(fun l : List X =>
      (⟨l ≠ [], fun h => f (l.getLast h)⟩ : Part Y)),
    ⟨by simp, by
      intro _ _ _ hne _
      exact hne⟩⟩

@[simp]
theorem dom_functionEvaluator (f : X → Y) :
    dom (functionEvaluator f) = {l : List X | l ≠ []} := by
  ext l
  rfl

@[simp]
theorem functionEvaluator_output (f : X → Y) (l : List X) (x : X)
    (h : l ++ [x] ∈ dom (functionEvaluator f)) :
    output (functionEvaluator f) (l ++ [x]) h = f x := by
  simp [output, functionEvaluator]

/-! ### Definition 3.3: fully defined completion -/

/-- CR18 Definition 3.3 / footnote 6: the kept prefix obtained by scanning an
input sequence from left to right and deleting exactly those next inputs that
would make the original partial DDS undefined. -/
def keptPrefix (S : DDS X Y) : List X → List X :=
  List.foldl (fun acc x => if acc ++ [x] ∈ dom S then acc ++ [x] else acc) []

/-- CR18 Definition 3.3: the fully defined completion `s⊥` of a DDS `s`.

The codomain `Option Y` models `Y ∪ {⊥}`: `some y` is an original output
`y : Y`, while `none` is the distinguished no-output symbol. The completed DDS
is defined on every nonempty input sequence. -/
def fullyDefined (S : DDS X Y) : DDS X (Option Y) :=
  ⟨(fun l : List X =>
      (⟨l ≠ [], fun h =>
        let ctx := keptPrefix S l.dropLast
        let cand := ctx ++ [l.getLast h]
        if hcand : cand ∈ dom S then
          some (output S cand hcand)
        else
          none⟩ : Part (Option Y))),
    ⟨by simp, by
      intro l₁ _l₂ _ hne _
      exact hne⟩⟩

@[simp]
theorem dom_fullyDefined (S : DDS X Y) :
    dom (fullyDefined S) = {l : List X | l ≠ []} := by
  ext l
  rfl

@[simp]
theorem output_fullyDefined (S : DDS X Y)
    (l : List X) (h : l ∈ dom (fullyDefined S)) :
    output (fullyDefined S) l h =
      let ctx := keptPrefix S l.dropLast
      let cand := ctx ++ [l.getLast (by exact h)]
      if hcand : cand ∈ dom S then
        some (output S cand hcand)
      else
        none := rfl

/-- CR18 notation for Definition 3.3: `S⊥` is the fully defined completion of
the DDS `S`.  This is postfix notation for `fullyDefined S`, not notation for
the bottom value in the completed output alphabet. -/
scoped postfix:1024 "⊥" => fullyDefined

@[simp]
theorem fullyDefined_notation (S : DDS X Y) :
    S⊥ = fullyDefined S :=
  rfl

/-- CR18 Definition 3.3 / footnote 6: after the left-to-right deletion pass, the
kept prefix is either a valid input sequence for the original DDS or is empty. -/
theorem keptPrefix_mem_or (S : DDS X Y) (l : List X) :
    keptPrefix S l ∈ dom S ∨ keptPrefix S l = [] := by
  let step : List X → X → List X := fun acc x =>
    if acc ++ [x] ∈ dom S then acc ++ [x] else acc
  have hfold : ∀ xs acc, acc ∈ dom S ∨ acc = [] →
      List.foldl step acc xs ∈ dom S ∨ List.foldl step acc xs = [] := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons x xs ih =>
        intro acc hacc
        apply ih
        dsimp [step]
        split
        · rename_i hmem
          exact Or.inl hmem
        ·
          simpa [dom] using hacc
  simpa [keptPrefix, step] using hfold l [] (Or.inr rfl)

private theorem keptPrefix_foldl_eq_append_of_mem (S : DDS X Y) :
    ∀ (xs acc : List X), acc ++ xs ∈ dom S →
      List.foldl (fun acc x => if acc ++ [x] ∈ dom S then acc ++ [x] else acc)
        acc xs = acc ++ xs := by
  intro xs
  induction xs with
  | nil =>
      intro acc _h
      simp
  | cons x xs ih =>
      intro acc hdom
      have hstep : acc ++ [x] ∈ dom S := by
        exact prefix_closed S (by simp) (by simp) hdom
      simp only [List.foldl_cons]
      rw [if_pos hstep]
      simpa [List.append_assoc] using
        ih (acc ++ [x]) (by simpa [List.append_assoc] using hdom)

theorem keptPrefix_eq_self_of_mem (S : DDS X Y) {l : List X} (h : l ∈ dom S) :
    keptPrefix S l = l := by
  simpa [keptPrefix] using keptPrefix_foldl_eq_append_of_mem S l [] h

theorem keptPrefix_eq_self_of_mem_or_empty (S : DDS X Y) {l : List X}
    (h : l ∈ dom S ∨ l = []) :
    keptPrefix S l = l := by
  rcases h with hmem | hempty
  · exact keptPrefix_eq_self_of_mem S hmem
  · simp [hempty, keptPrefix]

theorem output_fullyDefined_append_of_mem (S : DDS X Y) (l : List X) (x : X)
    (hl : l ∈ dom S ∨ l = []) (hnext : l ++ [x] ∈ dom S) :
    output S⊥ (l ++ [x]) (by
      rw [dom_fullyDefined]
      simp) = some (output S (l ++ [x]) hnext) := by
  rw [output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  rw [hdrop, hlast, keptPrefix_eq_self_of_mem_or_empty S hl]
  dsimp
  have hnextRaw : l ++ [x] ∈ PFun.Dom S.1 := by
    simpa [dom, toPFun] using hnext
  rw [dif_pos hnextRaw]

theorem mem_of_output_fullyDefined_append_eq_some (S : DDS X Y) (l : List X)
    (x : X) (hl : l ∈ dom S ∨ l = []) {y : Y}
    (hout :
      output S⊥ (l ++ [x]) (by
        rw [dom_fullyDefined]
        simp) = some y) :
    ∃ hnext : l ++ [x] ∈ dom S, output S (l ++ [x]) hnext = y := by
  rw [output_fullyDefined] at hout
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  rw [hdrop, hlast, keptPrefix_eq_self_of_mem_or_empty S hl] at hout
  dsimp at hout
  split at hout
  · rename_i hnextRaw
    refine ⟨by simpa [dom, toPFun] using hnextRaw, ?_⟩
    exact Option.some.inj hout
  · simp at hout

/-! ### Definition 3.4: parallel composition -/

variable {n : ℕ} {Xs : Fin n → Type u} {Ys : Fin n → Type v}

/-- CR18 Definition 3.4: restrict a tagged parallel-composition input history
to the component with index `j`, keeping exactly the payloads of the queries
tagged by `j`.

This is Maurer's `(x₁, ..., xₖ)|ⱼ`. The input alphabet of the parallel system
is the dependent tagged union `Sigma Xs`, so when a tag equality is found the
payload is transported into the selected component alphabet. -/
def restrict (j : Fin n) (l : List (Sigma Xs)) : List (Xs j) :=
  l.filterMap fun p =>
    if h : p.fst = j then
      some (cast (congrArg Xs h) p.snd)
    else
      none

/-- CR18 projection notation: `l |ₚ j` is Maurer's history restriction
`l|ⱼ`, the subsequence of second components of queries tagged by `j`. -/
scoped notation:70 l:71 " |ₚ " j:70 => restrict j l

@[simp]
theorem restrict_notation (j : Fin n) (l : List (Sigma Xs)) :
    l |ₚ j = restrict j l :=
  rfl

private inductive PaperPayload where
  | a
  | b
  | c
  deriving DecidableEq

private abbrev paperAlphabet : Fin 4 → Type :=
  fun _ => PaperPayload

private def paper1 : Fin 4 := ⟨0, by decide⟩
private def paper2 : Fin 4 := ⟨1, by decide⟩
private def paper3 : Fin 4 := ⟨2, by decide⟩
private def paper4 : Fin 4 := ⟨3, by decide⟩

/-- CR18 Definition 3.4 example:
`((3,a), (2,b), (1,a), (2,c), (4,a), (2,a))|₂ = (b,c,a)`. -/
private example :
    ([(⟨paper3, PaperPayload.a⟩ : Sigma paperAlphabet),
      ⟨paper2, PaperPayload.b⟩,
      ⟨paper1, PaperPayload.a⟩,
      ⟨paper2, PaperPayload.c⟩,
      ⟨paper4, PaperPayload.a⟩,
      ⟨paper2, PaperPayload.a⟩] |ₚ paper2) =
      [PaperPayload.b, PaperPayload.c, PaperPayload.a] := by
  native_decide

/-- Restricting a tagged history to one component preserves prefix order. -/
theorem restrict_prefix (i : Fin n) {l₁ l₂ : List (Sigma Xs)} (h : l₁ <+: l₂) :
    restrict i l₁ <+: restrict i l₂ := by
  rcases h with ⟨t, rfl⟩
  use restrict i t
  simp [restrict, List.filterMap_append]

/-- If a tagged history ends in component `i`, its restriction to `i` is
nonempty. -/
theorem restrict_ne_nil_of_getLast_eq_some
    {i : Fin n} {x : Xs i} {l : List (Sigma Xs)}
    (hlast : l.getLast? = some ⟨i, x⟩) :
    restrict i l ≠ [] := by
  have hmem : (⟨i, x⟩ : Sigma Xs) ∈ l.getLast? := by
    simp [hlast]
  have hdecomp : l.dropLast ++ [⟨i, x⟩] = l :=
    List.dropLast_append_getLast? _ hmem
  intro hnil
  rw [← hdecomp] at hnil
  simp [restrict] at hnil

/-- Restriction of the empty tagged history is empty. -/
theorem restrict_nil (i : Fin n) : restrict i ([] : List (Sigma Xs)) = [] := rfl

/-- Restriction distributes over concatenation of tagged histories. -/
theorem restrict_append (i : Fin n) (l₁ l₂ : List (Sigma Xs)) :
    restrict i (l₁ ++ l₂) = restrict i l₁ ++ restrict i l₂ := by
  simp [restrict, List.filterMap_append]

/-- Restricting to the tag of a newly consed query keeps its payload. -/
theorem restrict_cons_self (j : Fin n) (x : Xs j) (l : List (Sigma Xs)) :
    restrict j (⟨j, x⟩ :: l) = x :: restrict j l := by
  simp [restrict]

/-- Restricting to a different tag drops a newly consed query. -/
theorem restrict_cons_ne {i j : Fin n} (hij : j ≠ i) (x : Xs j)
    (l : List (Sigma Xs)) :
    restrict i (⟨j, x⟩ :: l) = restrict i l := by
  simp [restrict, hij]

/-- Restricting to the tag of a newly appended query appends its payload. -/
theorem restrict_concat_self (j : Fin n) (x : Xs j) (l : List (Sigma Xs)) :
    restrict j (l ++ [⟨j, x⟩]) = restrict j l ++ [x] := by
  rw [restrict_append, restrict_cons_self, restrict_nil]

/-- Restricting to a different tag drops a newly appended query. -/
theorem restrict_concat_ne {i j : Fin n} (hij : j ≠ i) (x : Xs j)
    (l : List (Sigma Xs)) :
    restrict i (l ++ [⟨j, x⟩]) = restrict i l := by
  rw [restrict_append, restrict_cons_ne hij, restrict_nil, List.append_nil]

/-- CR18 Definition 3.4: the domain of the parallel composition.

A tagged history is accepted exactly when it is nonempty and every component
projection is either still empty or accepted by the corresponding component
DDS. This is the prefix-closed reading of Maurer's partial parallel
composition. -/
def parallelDom (S : (i : Fin n) → DDS (Xs i) (Ys i)) : Set (List (Sigma Xs)) :=
  {l | l ≠ [] ∧ ∀ i : Fin n, restrict i l = [] ∨ restrict i l ∈ dom (S i)}

/-- CR18 Definition 3.4: parallel composition as a DDS-level constructor. -/
def parallel (S : (i : Fin n) → DDS (Xs i) (Ys i)) : DDS (Sigma Xs) (Sigma Ys) :=
  ⟨(fun l : List (Sigma Xs) =>
      (⟨l ∈ parallelDom S, fun h =>
        match hlast : l.getLast? with
        | some p =>
            Sigma.mk p.fst (output (S p.fst) (restrict p.fst l) (by
              have hne : restrict p.fst l ≠ [] := by
                exact restrict_ne_nil_of_getLast_eq_some hlast
              rcases h.2 p.fst with hempty | hdom
              · exact False.elim (hne hempty)
              · exact hdom))
        | none =>
            False.elim (h.1 (List.getLast?_eq_none_iff.mp hlast))⟩ : Part (Sigma Ys))),
    ⟨by simp [parallelDom], by
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
        · exact Or.inr (prefix_closed (S i) (restrict_prefix i hprefix) hrest₁ hrest_dom)⟩⟩

/-- CR18 notation for Definition 3.4: `[S]ₚ` is the parallel composition of
the indexed family of DDSs `S`. The subscript avoids conflict with Lean's list
notation while retaining Maurer's bracket notation `[s₁, ..., sₙ]`. -/
scoped notation "[" S "]ₚ" => parallel S

@[simp]
theorem parallel_notation (S : (i : Fin n) → DDS (Xs i) (Ys i)) :
    [S]ₚ = parallel S :=
  rfl

/-- Domain equation for CR18 Definition 3.4. -/
@[simp]
theorem parallel_dom (S : (i : Fin n) → DDS (Xs i) (Ys i)) :
    dom (parallel S) = parallelDom S :=
  rfl

/-- Membership form of the domain equation for CR18 Definition 3.4. -/
theorem mem_parallel_dom (S : (i : Fin n) → DDS (Xs i) (Ys i))
    (l : List (Sigma Xs)) :
    l ∈ dom (parallel S) ↔
      l ≠ [] ∧ ∀ i : Fin n, restrict i l = [] ∨ restrict i l ∈ dom (S i) :=
  Iff.rfl

/-- CR18 Definition 3.4: appending one tagged query `⟨j, x⟩` to a history whose
component restrictions are each empty or accepted lands in the parallel domain
iff component `j` accepts its extended restriction. -/
theorem append_singleton_mem_parallel_dom_iff
    (S : (i : Fin n) → DDS (Xs i) (Ys i)) {acc : List (Sigma Xs)}
    (hinv : ∀ i : Fin n, restrict i acc = [] ∨ restrict i acc ∈ dom (S i))
    (j : Fin n) (x : Xs j) :
    acc ++ [⟨j, x⟩] ∈ dom (parallel S) ↔ restrict j acc ++ [x] ∈ dom (S j) := by
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
theorem restrict_keptPrefix_parallel_or (S : (i : Fin n) → DDS (Xs i) (Ys i))
    (m : List (Sigma Xs)) (i : Fin n) :
    restrict i (keptPrefix (parallel S) m) = [] ∨
      restrict i (keptPrefix (parallel S) m) ∈ dom (S i) := by
  rcases keptPrefix_mem_or (parallel S) m with hdom | hempty
  · exact hdom.2 i
  · rw [hempty, restrict_nil]
    exact Or.inl rfl

/-- CR18 Definition 3.4 / footnote 6: the deletion pass of the parallel
composition commutes with restriction to any component. -/
theorem restrict_keptPrefix_parallel (S : (i : Fin n) → DDS (Xs i) (Ys i))
    (j : Fin n) (m : List (Sigma Xs)) :
    restrict j (keptPrefix (parallel S) m) = keptPrefix (S j) (restrict j m) := by
  suffices h : ∀ (xs acc : List (Sigma Xs)),
      (∀ i : Fin n, restrict i acc = [] ∨ restrict i acc ∈ dom (S i)) →
      restrict j (List.foldl
          (fun acc p => if acc ++ [p] ∈ dom (parallel S) then acc ++ [p] else acc)
          acc xs) =
        List.foldl
          (fun acc x => if acc ++ [x] ∈ dom (S j) then acc ++ [x] else acc)
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
      by_cases hmem : acc ++ [⟨i, r⟩] ∈ dom (parallel S)
      · have hinv' : ∀ k : Fin n, restrict k (acc ++ [⟨i, r⟩]) = [] ∨
            restrict k (acc ++ [⟨i, r⟩]) ∈ dom (S k) := fun k => hmem.2 k
        by_cases hij : i = j
        · subst hij
          simp only [List.foldl_cons, restrict_cons_self]
          rw [if_pos hmem,
            if_pos ((append_singleton_mem_parallel_dom_iff S hinv i r).mp hmem),
            ih _ hinv', restrict_concat_self]
        · simp only [List.foldl_cons, restrict_cons_ne hij]
          rw [if_pos hmem, ih _ hinv', restrict_concat_ne hij]
      · by_cases hij : i = j
        · subst hij
          simp only [List.foldl_cons, restrict_cons_self]
          rw [if_neg hmem,
            if_neg (fun hc => hmem
              ((append_singleton_mem_parallel_dom_iff S hinv i r).mpr hc)),
            ih _ hinv]
        · simp only [List.foldl_cons, restrict_cons_ne hij]
          rw [if_neg hmem, ih _ hinv]

/-- Output equation for CR18 Definition 3.4.

If the last tagged input in `l` has index `j`, then the parallel composition
returns the response of subsystem `j` on the restricted history `l|ⱼ`,
re-tagged as an element of the dependent output union. -/
theorem parallel_output (S : (i : Fin n) → DDS (Xs i) (Ys i))
    (l : List (Sigma Xs)) (h : l ∈ dom (parallel S))
    {j : Fin n} {x : Xs j} (hlast : l.getLast? = some ⟨j, x⟩) :
    output (parallel S) l h =
      Sigma.mk j (output (S j) (restrict j l) (by
        have hne : restrict j l ≠ [] := by
          exact restrict_ne_nil_of_getLast_eq_some hlast
        rcases h.2 j with hempty | hdom
        · exact False.elim (hne hempty)
        · exact hdom)) := by
  simp [parallel, output]
  split
  · rename_i p hp
    have hpj : p = Sigma.mk j x := by
      simpa [hp] using hlast
    cases hpj
    rfl
  · rename_i hn
    simp [hn] at hlast

/-- Restricting a pure-tag-`i` history to `i` recovers the untagged payloads. -/
theorem restrict_map_self (i : Fin n) (xs : List (Xs i)) :
    restrict i (xs.map (Sigma.mk i)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, restrict_cons_self, ih]

/-- Restricting a pure-tag-`i` history to a different tag is empty. -/
theorem restrict_map_ne {i i' : Fin n} (hii' : i ≠ i') (xs : List (Xs i)) :
    restrict i' (xs.map (Sigma.mk i)) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, restrict_cons_ne hii', ih]

/-- **(R) — pure-tag routing.** Querying the parallel composition on a history all tagged `i`
(`xs` retagged) is exactly subsystem `i` queried on the untagged history `xs`, retagged into the
output union. This is the routing fact converter application factors through. -/
theorem parallel_raw_pure_tag (S : (i : Fin n) → DDS (Xs i) (Ys i)) (i : Fin n)
    (xs : List (Xs i)) :
    (parallel S).1 (xs.map (Sigma.mk i)) = ((S i).1 xs).map (Sigma.mk i) := by
  have hri : restrict i (xs.map (Sigma.mk i)) = xs := restrict_map_self i xs
  have hdom : (xs.map (Sigma.mk i)) ∈ dom (parallel S) ↔ xs ∈ dom (S i) := by
    rw [mem_parallel_dom]
    constructor
    · rintro ⟨hne, hall⟩
      have hxsne : xs ≠ [] := by rintro rfl; exact hne rfl
      rcases hall i with he | hd
      · rw [hri] at he; exact absurd he hxsne
      · rwa [hri] at hd
    · intro hxs
      have hxsne : xs ≠ [] := by rintro rfl; exact PFunDDS.empty_not_mem (S i) hxs
      refine ⟨fun h => hxsne (List.map_eq_nil_iff.mp h), fun i' => ?_⟩
      by_cases hii' : i = i'
      · subst hii'; exact Or.inr (by rw [hri]; exact hxs)
      · exact Or.inl (restrict_map_ne hii' xs)
  by_cases hxs : xs ∈ dom (S i)
  · have hldom : xs.map (Sigma.mk i) ∈ dom (parallel S) := hdom.mpr hxs
    have hxsne : xs ≠ [] := by rintro rfl; exact PFunDDS.empty_not_mem (S i) hxs
    have hlast : (xs.map (Sigma.mk i)).getLast? = some ⟨i, xs.getLast hxsne⟩ := by
      rw [List.getLast?_map, List.getLast?_eq_some_getLast hxsne]; rfl
    have hout : output (parallel S) (xs.map (Sigma.mk i)) hldom = ⟨i, output (S i) xs hxs⟩ := by
      rw [parallel_output S _ hldom hlast]
      exact congrArg (Sigma.mk i) (output_congr (S i) hri _ hxs)
    have e1 : (parallel S).1 (xs.map (Sigma.mk i)) = Part.some (⟨i, output (S i) xs hxs⟩ : Sigma Ys) := by
      rw [← hout]; exact (Part.some_get hldom).symm
    have e2 : (S i).1 xs = Part.some (output (S i) xs hxs) := (Part.some_get hxs).symm
    rw [e1, e2, Part.map_some]
  · have hldom : ¬ (xs.map (Sigma.mk i) ∈ dom (parallel S)) := fun h => hxs (hdom.mp h)
    rw [Part.eq_none_iff'.mpr hxs, Part.map_none, Part.eq_none_iff'.mpr hldom]

/-- **(R) for a mixed history.** Appending a tag-`i` query `⟨i,x⟩` to a *valid* history `xs` (each
component restriction empty or accepted) routes through component `i` on its own restriction: the
parallel answer is `S i`'s answer on `restrict i xs ++ [x]`, retagged. Generalizes
`parallel_raw_pure_tag` (whose pure-tag history is automatically valid). -/
theorem parallel_raw_concat_tag (S : (i : Fin n) → DDS (Xs i) (Ys i)) {i : Fin n}
    (xs : List (Sigma Xs)) (x : Xs i)
    (hinv : ∀ j, restrict j xs = [] ∨ restrict j xs ∈ dom (S j)) :
    (parallel S).1 (xs ++ [⟨i, x⟩]) = ((S i).1 (restrict i xs ++ [x])).map (Sigma.mk i) := by
  have hrc : restrict i (xs ++ [⟨i, x⟩]) = restrict i xs ++ [x] := restrict_concat_self i x xs
  by_cases hxs : restrict i xs ++ [x] ∈ dom (S i)
  · have hldom : xs ++ [⟨i, x⟩] ∈ dom (parallel S) :=
      (append_singleton_mem_parallel_dom_iff S hinv i x).mpr hxs
    have hlast : (xs ++ [(⟨i, x⟩ : Sigma Xs)]).getLast? = some (⟨i, x⟩ : Sigma Xs) := by
      rw [List.getLast?_concat]
    have hout : output (parallel S) (xs ++ [⟨i, x⟩]) hldom
        = ⟨i, output (S i) (restrict i xs ++ [x]) hxs⟩ := by
      rw [parallel_output S _ hldom hlast]
      exact congrArg (Sigma.mk i) (output_congr (S i) hrc _ hxs)
    have e1 : (parallel S).1 (xs ++ [⟨i, x⟩])
        = Part.some (⟨i, output (S i) (restrict i xs ++ [x]) hxs⟩ : Sigma Ys) := by
      rw [← hout]; exact (Part.some_get hldom).symm
    have e2 : (S i).1 (restrict i xs ++ [x])
        = Part.some (output (S i) (restrict i xs ++ [x]) hxs) := (Part.some_get hxs).symm
    rw [e1, e2, Part.map_some]
  · have hldom : ¬ (xs ++ [⟨i, x⟩] ∈ dom (parallel S)) :=
      fun h => hxs ((append_singleton_mem_parallel_dom_iff S hinv i x).mp h)
    rw [Part.eq_none_iff'.mpr hxs, Part.map_none, Part.eq_none_iff'.mpr hldom]

/-- Membership in the parallel raw function: a value is produced exactly at the (unique) output. -/
theorem mem_parallel_raw (S : (i : Fin n) → DDS (Xs i) (Ys i)) (l : List (Sigma Xs))
    (v : Sigma Ys) :
    v ∈ (parallel S).1 l ↔ ∃ h : l ∈ dom (parallel S), output (parallel S) l h = v := by
  constructor
  · intro hv
    have hdom : l ∈ dom (parallel S) := by rw [dom, PFun.mem_dom]; exact ⟨v, hv⟩
    exact ⟨hdom, Part.mem_unique (Part.get_mem hdom) hv⟩
  · rintro ⟨h, rfl⟩; exact Part.get_mem h

/-- **Parallel composition commutes with the fuel-eventual.** If a family `T` is the eventual (over a
monotone-in-fuel family `D`) componentwise, then the parallel of the eventuals produces a value iff
some single common fuel makes the parallel of `D` produce it — the routing fact behind the fuel-free
`applyG (q-fold C) (parallel S) = parallel (i ↦ applyG C (S i))`. The common fuel is `Finset.sup` of
the per-component fuels (bumped via monotonicity). -/
theorem parallel_eventual
    (D : ℕ → (i : Fin n) → DDS (Xs i) (Ys i)) (T : (i : Fin n) → DDS (Xs i) (Ys i))
    (hmono : ∀ {f f' : ℕ} {i : Fin n} {l : List (Xs i)} {w : Ys i}, f ≤ f' →
      w ∈ (D f i).1 l → w ∈ (D f' i).1 l)
    (hT : ∀ (i : Fin n) (l : List (Xs i)) (w : Ys i), w ∈ (T i).1 l ↔ ∃ f, w ∈ (D f i).1 l)
    (us : List (Sigma Xs)) (v : Sigma Ys) :
    v ∈ (parallel T).1 us ↔ ∃ f, v ∈ (parallel (D f)).1 us := by
  have hout_eq : ∀ (f : ℕ) (hf : us ∈ dom (parallel (D f))) (hg : us ∈ dom (parallel T)),
      output (parallel (D f)) us hf = output (parallel T) us hg := by
    intro f hf hg
    have hne : us ≠ [] := ((mem_parallel_dom T us).mp hg).1
    rw [parallel_output (D f) us hf (j := (us.getLast hne).1) (x := (us.getLast hne).2)
          (by rw [List.getLast?_eq_some_getLast hne]),
        parallel_output T us hg (j := (us.getLast hne).1) (x := (us.getLast hne).2)
          (by rw [List.getLast?_eq_some_getLast hne])]
    exact congrArg (Sigma.mk _)
      (Part.mem_unique ((hT _ _ _).mpr ⟨f, Part.get_mem _⟩) (Part.get_mem _))
  constructor
  · intro hv
    rw [mem_parallel_raw] at hv
    obtain ⟨hg, hout⟩ := hv
    have hcv : ∀ i, ∃ f, restrict i us = [] ∨ restrict i us ∈ dom (D f i) := by
      intro i
      rcases ((mem_parallel_dom T us).mp hg).2 i with he | hd
      · exact ⟨0, Or.inl he⟩
      · rw [dom, PFun.mem_dom] at hd
        obtain ⟨w, hw⟩ := hd
        obtain ⟨f, hf⟩ := (hT i _ w).mp hw
        exact ⟨f, Or.inr (by rw [dom, PFun.mem_dom]; exact ⟨w, hf⟩)⟩
    refine ⟨Finset.univ.sup (fun i => (hcv i).choose), ?_⟩
    rw [mem_parallel_raw]
    have hf : us ∈ dom (parallel (D (Finset.univ.sup (fun i => (hcv i).choose)))) := by
      rw [mem_parallel_dom]
      refine ⟨((mem_parallel_dom T us).mp hg).1, fun i => ?_⟩
      rcases (hcv i).choose_spec with he | hd
      · exact Or.inl he
      · right
        rw [dom, PFun.mem_dom] at hd ⊢
        obtain ⟨w, hw⟩ := hd
        exact ⟨w, hmono (Finset.le_sup (Finset.mem_univ i)) hw⟩
    exact ⟨hf, (hout_eq _ hf hg).trans hout⟩
  · rintro ⟨f, hv⟩
    rw [mem_parallel_raw] at hv ⊢
    obtain ⟨hf, hout⟩ := hv
    have hg : us ∈ dom (parallel T) := by
      rw [mem_parallel_dom]
      refine ⟨((mem_parallel_dom (D f) us).mp hf).1, fun i => ?_⟩
      rcases ((mem_parallel_dom (D f) us).mp hf).2 i with he | hd
      · exact Or.inl he
      · right
        rw [dom, PFun.mem_dom] at hd ⊢
        obtain ⟨w, hw⟩ := hd
        exact ⟨w, (hT i _ w).mpr ⟨f, hw⟩⟩
    exact ⟨hg, (hout_eq f hf hg).symm.trans hout⟩

/-- Updating component `j` in a parallel family affects the output of a
history ending at `j` exactly by replacing that component.  [serves:
PO-6/hParallelReplace] -/
theorem parallel_output_update_self
    (ctx : (i : Fin n) → DDS (Xs i) (Ys i)) (j : Fin n)
    (S : DDS (Xs j) (Ys j))
    (l : List (Sigma Xs)) (h : l ∈ dom (parallel (Function.update ctx j S)))
    {x : Xs j} (hlast : l.getLast? = some ⟨j, x⟩) :
    output (parallel (Function.update ctx j S)) l h =
      Sigma.mk j (output S (restrict j l) (by
        have hne : restrict j l ≠ [] := by
          exact restrict_ne_nil_of_getLast_eq_some hlast
        rcases h.2 j with hempty | hdom
        · exact False.elim (hne hempty)
        · simpa using hdom)) := by
  rw [parallel_output (Function.update ctx j S) l h hlast]
  simp only [Function.update_self]

/-- Updating component `j` in a parallel family leaves the output of histories
ending at any other component unchanged.  [serves: PO-6/hParallelReplace] -/
theorem parallel_output_update_ne
    (ctx : (i : Fin n) → DDS (Xs i) (Ys i)) {i j : Fin n}
    (hij : i ≠ j) (S : DDS (Xs j) (Ys j))
    (l : List (Sigma Xs)) (h : l ∈ dom (parallel (Function.update ctx j S)))
    {x : Xs i} (hlast : l.getLast? = some ⟨i, x⟩) :
    output (parallel (Function.update ctx j S)) l h =
      Sigma.mk i (output (ctx i) (restrict i l) (by
        have hne : restrict i l ≠ [] := by
          exact restrict_ne_nil_of_getLast_eq_some hlast
        rcases h.2 i with hempty | hdom
        · exact False.elim (hne hempty)
        · simpa [Function.update_of_ne hij] using hdom)) := by
  rw [parallel_output (Function.update ctx j S) l h hlast]
  simp only [Function.update_of_ne hij]

/-! ### §3.2.3: interfaces and resources as DDSs -/

/-- CR18 Definition 3.5: a deterministic resource with interface set `I`,
uniform input alphabet `A`, and output alphabet `B` is an `(I × A, B)`-DDS.

This is deliberately just a type synonym: in Maurer's model a resource is not a
new operational object, but a DDS whose input alphabet has been partitioned into
interface-tagged fibers. -/
abbrev Resource (I : Type u) (A : Type v) (B : Type w) : Type (max (max u v) w) :=
  DDS (I × A) B

namespace Resource

variable {I : Type u} {A : Type v} {B : Type w}

/-- The interface tag of one resource input. -/
def inputInterface (p : I × A) : I :=
  p.1

@[simp]
theorem inputInterface_mk (i : I) (x : A) :
    inputInterface (i, x) = i :=
  rfl

/-- CR18 §3.2.3: the sub-alphabet of inputs given at interface `i`.

In the tagged model for resources, Maurer's partition
`X = X₁ ∪ ... ∪ Xₙ` with pairwise disjoint `Xᵢ` is represented by the fibers
`Xᵢ = {i} × A` of the interface projection. -/
def interfaceAlphabet (I : Type u) (A : Type v) (i : I) : Set (I × A) :=
  {p | inputInterface p = i}

@[simp]
theorem mem_interfaceAlphabet_iff (i : I) (p : I × A) :
    p ∈ interfaceAlphabet I A i ↔ inputInterface p = i :=
  Iff.rfl

@[simp]
theorem mk_mem_interfaceAlphabet (i : I) (x : A) :
    (i, x) ∈ interfaceAlphabet I A i :=
  rfl

/-- CR18 §3.2.3: distinct interface sub-alphabets are disjoint:
`Xᵢ ∩ Xⱼ = ∅` for `i ≠ j`. -/
theorem interfaceAlphabet_disjoint (I : Type u) (A : Type v) {i j : I}
    (hij : i ≠ j) :
    interfaceAlphabet I A i ∩ interfaceAlphabet I A j = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, interfaceAlphabet, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hi hj => hij (hi.symm.trans hj)

/-- CR18 §3.2.3: the interface sub-alphabets cover the resource input alphabet:
`I × A = ⋃ i, Xᵢ`. -/
theorem iUnion_interfaceAlphabet (I : Type u) (A : Type v) :
    ⋃ i : I, interfaceAlphabet I A i = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, interfaceAlphabet, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact ⟨inputInterface p, rfl⟩

end Resource

/-! ### Definition 3.6: deterministic discrete environments -/

/-- CR18 Definition 3.6: a deterministic discrete environment for an
`(X, Y)`-DDS, i.e. a `(Y, X)`-DDE.

This is exactly Maurer's function `e : (Y ∪ {⊥})* → X ∪ {⊣}`.  We represent
`Y ∪ {⊥}` by `Option Y` and `X ∪ {⊣}` by `Option X`. -/
abbrev DDE (X : Type u) (Y : Type v) : Type (max u v) :=
  List (Option Y) → Option X

/-! ### Definition 3.7: transcripts -/

/-- Input projection of a transcript prefix:
`[(x₁,y₁), ..., (xₖ,yₖ)]↓ₓ = [x₁, ..., xₖ]`. -/
def transcriptInputs (t : List (X × Option Y)) : List X :=
  t.map Prod.fst

/-- Output projection of a transcript prefix:
`[(x₁,y₁), ..., (xₖ,yₖ)]↓ᵧ = [y₁, ..., yₖ]`. -/
def transcriptOutputs (t : List (X × Option Y)) : List (Option Y) :=
  t.map Prod.snd

/-- CR18 transcript input-projection notation. -/
scoped postfix:1024 "↓ₓ" => transcriptInputs

/-- CR18 transcript output-projection notation. -/
scoped postfix:1024 "↓ᵧ" => transcriptOutputs

@[simp]
theorem transcriptInputs_notation (t : List (X × Option Y)) :
    t↓ₓ = transcriptInputs t :=
  rfl

@[simp]
theorem transcriptOutputs_notation (t : List (X × Option Y)) :
    t↓ᵧ = transcriptOutputs t :=
  rfl

/-- CR18 Definition 3.7, **functional** form: the transcript `tr(s,e)` is the
(possibly infinite) sequence `x₁,y₁,x₂,y₂,…` defined by the recurrence
`xᵢ = e(y₁,…,yᵢ₋₁)`, `yᵢ = s⊥(x₁,…,xᵢ)`. We present it as the function sending a
length `n` to its length-`n` prefix; when the environment returns `⊣` the
sequence stalls (the prefix stops growing). This is `tr(·,·)` as the function
through which `tr(S,E)` is defined — *not* a relation or a set of prefixes. -/
noncomputable def transcript (s : DDS X Y) (e : DDE X Y) : ℕ → List (X × Option Y)
  | 0 => []
  | n + 1 =>
      let t := transcript s e n
      match e t↓ᵧ with
      | some x => t ++ [(x, output s⊥ (t↓ₓ ++ [x]) (by simp [fullyDefined, dom]))]
      | none => t

/-- CR18 Definition 3.7 notation: `tr(s,e)` is Maurer's transcript — the
function (sequence) `tr(s,e) : ℕ → List (X × Option Y)`, with `tr(s,e) n` its
length-`n` prefix. -/
scoped notation "tr" "(" s "," e ")" => transcript s e

/-- CR18 Definition 3.7, prefix predicate: `Transcript s e t` says `t` is a
finite prefix of Maurer's transcript `tr(s,e)`.

The empty list is the initial transcript. If `t = [(x₁,y₁), ..., (xₖ,yₖ)]`
is a transcript prefix and the environment emits `x` after seeing
`(y₁, ..., yₖ)`, then the next prefix appends `(x, s⊥(x₁, ..., xₖ, x))`.

This is a *characterization* of the `transcript` function (see
`transcript_mem_iff`), kept for the membership/prefix view — not the
definition of the transcript. -/
inductive Transcript (S : DDS X Y) (e : DDE X Y) :
    List (X × Option Y) → Prop where
  | nil : Transcript S e []
  | snoc {t : List (X × Option Y)} (ht : Transcript S e t)
      {x : X} (hx : e t↓ᵧ = some x) :
      Transcript S e
        (t ++ [(x, output S⊥ (t↓ₓ ++ [x]) (by
          simp [fullyDefined, dom]))])

/-- The inductive prefix predicate holds exactly on the prefixes produced by the
transcript function `tr(s,e)`: the relation is a *characterization* of the
function, not the definition. -/
theorem transcript_mem_iff (s : DDS X Y) (e : DDE X Y) (t : List (X × Option Y)) :
    Transcript s e t ↔ ∃ n, transcript s e n = t := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨0, rfl⟩
    | snoc _ht hx ih =>
        obtain ⟨n, rfl⟩ := ih
        exact ⟨n + 1, by simp only [transcript, hx]⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact Transcript.nil
    | succ n ih =>
        simp only [transcript]
        cases hx : e (transcript s e n)↓ᵧ with
        | none => simpa using ih
        | some x => exact Transcript.snoc ih hx

namespace Transcript

/-- CR18 Definition 3.7: a transcript prefix is complete exactly when the
environment stops after seeing its output projection.

This is the formal content of “if `e(y₁, ..., yᵢ₋₁) = ⊣`, the transcript ends
with `yᵢ₋₁`.” -/
def Complete {S : DDS X Y} {e : DDE X Y} (t : List (X × Option Y)) : Prop :=
  Transcript S e t ∧ e t↓ᵧ = none

/-- CR18 Definition 3.7 notation: `tr(s,e)✓ t` says that `t` is a complete
transcript, i.e. a valid transcript prefix where the environment has stopped.
(Pattern vars `sy`/`en` avoid capturing the named-argument labels `S`/`e`.) -/
scoped notation "tr" "(" sy "," en ")" "✓" => Complete (S := sy) (e := en)

end Transcript

/-- View an existing CR18 DDS record as a PFun-native DDS. -/
def fromDDS (S : RandomSystems.CR18.DDS X Y) : DDS X Y :=
  ⟨(fun l : List X => (⟨l ∈ S.dom, fun h => S.respond l h⟩ : Part Y)),
    ⟨by simpa using S.nonempty_input, by
      intro l₁ l₂ hprefix hne hdom
      exact S.prefix_closed hprefix hne (by simpa using hdom)⟩⟩

@[simp]
theorem dom_fromDDS (S : RandomSystems.CR18.DDS X Y) :
    dom (fromDDS S) = S.dom := by
  ext l
  rfl

@[simp]
theorem output_fromDDS (S : RandomSystems.CR18.DDS X Y) (l : List X) (h : l ∈ S.dom) :
    output (fromDDS S) l (by exact h) = S.respond l h := by
  change S.respond l (by exact h) = S.respond l h
  exact RandomSystems.CR18.DDS.respond_congr S rfl (by exact h) h

/-- Decidability transports across the compatibility view from the existing
record API to the PFun-native API. -/
instance decidablePred_dom_fromDDS (S : RandomSystems.CR18.DDS X Y)
    [DecidablePred (fun l => l ∈ S.dom)] :
    DecidablePred (fun l => l ∈ dom (fromDDS S)) := fun l => by
  change Decidable (l ∈ S.dom)
  infer_instance

/-- Repackage a PFun-native DDS as the existing CR18 DDS record. -/
def toDDS (S : DDS X Y) : RandomSystems.CR18.DDS X Y where
  dom := dom S
  nonempty_input := empty_not_mem S
  prefix_closed := prefix_closed S
  respond := output S

@[simp]
theorem toDDS_dom (S : DDS X Y) : (toDDS S).dom = dom S :=
  rfl

@[simp]
theorem toDDS_respond (S : DDS X Y) (l : List X) (h : l ∈ dom S) :
    (toDDS S).respond l h = output S l h :=
  rfl

@[simp]
theorem toDDS_fromDDS (S : RandomSystems.CR18.DDS X Y) :
    toDDS (fromDDS S) = S := by
  apply RandomSystems.CR18.DDS.ext
  · ext l
    rfl
  · intro l hs ht
    change S.respond l (by change l ∈ S.dom at hs; exact hs) = S.respond l ht
    exact RandomSystems.CR18.DDS.respond_congr S rfl (by change l ∈ S.dom at hs; exact hs) ht

@[simp]
theorem fromDDS_toDDS (S : DDS X Y) :
    fromDDS (toDDS S) = S := by
  apply Subtype.ext
  change (fromDDS (toDDS S)).1 = S.1
  apply PFun.ext'
  · intro l
    rfl
  · intro l h₁ h₂
    rfl

@[simp]
theorem fromDDS_parallel
    (S : (i : Fin n) → RandomSystems.CR18.DDS (Xs i) (Ys i)) :
    fromDDS (RandomSystems.CR18.DDS.parallel S) =
      parallel (fun i => fromDDS (S i)) := by
  apply Subtype.ext
  apply PFun.ext'
  · intro l
    rfl
  · intro l h₁ h₂
    rfl

@[simp]
theorem keptPrefix_fromDDS (S : RandomSystems.CR18.DDS X Y)
    [DecidablePred (fun l => l ∈ S.dom)] (l : List X) :
    keptPrefix (fromDDS S) l = RandomSystems.CR18.DDS.keptPrefix S l :=
  by
    suffices h : ∀ xs acc : List X,
        List.foldl
            (fun acc x => if acc ++ [x] ∈ dom (fromDDS S) then acc ++ [x] else acc)
            acc xs =
          List.foldl
            (fun acc x => if acc ++ [x] ∈ S.dom then acc ++ [x] else acc)
            acc xs by
      simpa [keptPrefix, RandomSystems.CR18.DDS.keptPrefix] using h l []
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        by_cases hx : acc ++ [x] ∈ S.dom
        · have hx' : acc ++ [x] ∈ dom (fromDDS S) := by
            rw [dom_fromDDS]
            exact hx
          rw [if_pos hx', if_pos hx]
          exact ih _
        · have hx' : acc ++ [x] ∉ dom (fromDDS S) := by
            rw [dom_fromDDS]
            exact hx
          rw [if_neg hx', if_neg hx]
          exact ih _

/-- CR18 Definition 3.4: reindex the output of the parallel composition of
fully defined component systems into the output type of the fully defined
parallel system.

The left-hand construction has output alphabet `Option (Sigma Ys)`, while the
right-hand construction has output alphabet `Sigma (fun i => Option (Ys i))`.
This map is the evident comparison: component-level `some y` stays tagged by
its component, and component-level `none` becomes the global `none`. -/
def optionSigma {n : ℕ} {Ys : Fin n → Type v} :
    Sigma (fun i : Fin n => Option (Ys i)) → Option (Sigma Ys)
  | ⟨i, some y⟩ => some ⟨i, y⟩
  | ⟨_, none⟩ => none

/-- CR18 Definition 3.4: fully defining a parallel composition agrees
extensionally with taking the parallel composition of the fully defined
component systems, up to the canonical `Option`/`Sigma` reindexing.

This is the PFun-native form of Maurer's
`[s₁, ..., sₙ]⊥ = [s₁⊥, ..., sₙ⊥]`. -/
theorem parallel_fullyDefined (S : (i : Fin n) → DDS (Xs i) (Ys i))
    (l : List (Sigma Xs))
    (hLeft : l ∈ dom (([S]ₚ)⊥))
    (hRight : l ∈ dom (parallel (fun i => (S i)⊥))) :
    output (([S]ₚ)⊥) l hLeft =
      optionSigma (output (parallel (fun i => (S i)⊥)) l hRight) := by
  have hne : l ≠ [] := hLeft
  obtain ⟨⟨j, x⟩, hlast⟩ : ∃ p : Sigma Xs, l.getLast? = some p :=
    ⟨l.getLast hne, List.getLast?_eq_some_getLast hne⟩
  obtain ⟨m, rfl⟩ : ∃ m : List (Sigma Xs), l = m ++ [⟨j, x⟩] :=
    ⟨l.dropLast, (List.dropLast_append_getLast? _ (by simp [hlast])).symm⟩
  have hlast' :
      (m ++ [(⟨j, x⟩ : Sigma Xs)]).getLast? = some (⟨j, x⟩ : Sigma Xs) :=
    List.getLast?_concat
  have hpar := parallel_output (fun i => (S i)⊥)
    (m ++ [(⟨j, x⟩ : Sigma Xs)]) hRight hlast'
  rw [hpar]
  rw [output_fullyDefined (parallel S), output_fullyDefined (S j)]
  simp only [restrict_concat_self, List.dropLast_concat, List.getLast_concat]
  have hiff : keptPrefix (parallel S) m ++ [⟨j, x⟩] ∈ dom (parallel S) ↔
      keptPrefix (S j) (restrict j m) ++ [x] ∈ dom (S j) := by
    rw [append_singleton_mem_parallel_dom_iff S
        (restrict_keptPrefix_parallel_or S m) j x,
      restrict_keptPrefix_parallel S j m]
  by_cases hC : keptPrefix (S j) (restrict j m) ++ [x] ∈ dom (S j)
  · rw [dif_pos (hiff.mpr hC), dif_pos hC]
    have hrl : restrict j (keptPrefix (parallel S) m ++ [⟨j, x⟩]) =
        keptPrefix (S j) (restrict j m) ++ [x] := by
      rw [restrict_concat_self, restrict_keptPrefix_parallel S j m]
    have hout : output (parallel S) (keptPrefix (parallel S) m ++ [⟨j, x⟩])
        (hiff.mpr hC) = _ :=
      parallel_output S _ (hiff.mpr hC) List.getLast?_concat
    exact congrArg some (hout.trans (congrArg (Sigma.mk j)
      (output_congr (S j) hrl _ hC)))
  · rw [dif_neg (fun hc => hC (hiff.mp hc)), dif_neg hC]
    rfl

end

end PFunDDS

end RandomSystems.CR18
