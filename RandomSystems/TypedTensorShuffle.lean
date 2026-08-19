/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedInterfaceRelabel

/-!
# `[R,S] ≅ [S,R]` and `[[R,S],T] ≅ [R,[S,T]]`

Disjoint-interface parallel composition (`Resource.tensor`, `TypedTensor.lean`)
grows the interface set: `[R,S]` lives at `I ⊕ J` and `[S,R]` at `J ⊕ I`.  The
two are therefore not even of the same type, and the commutativity a paper
writes down as an identity is here an identity **up to the bijective
re-indexing** `Equiv.sumComm` — which is exactly the operation
`TypedInterfaceRelabel.lean` supplies, and which is an isometry in both
directions.  Associativity is the same story at `Equiv.sumAssoc`.

Both statements are proved as plain equalities, not as `≈[0]` bounds: nothing
is lost and nothing is approximated, the two sides differ by the *names* of
their interfaces alone.
-/

/-- UPSTREAM-CANDIDATE: membership in the image of a `Part` under a bijection
is membership of the preimage.  (`Part.mem_map_iff` leaves the existential
that a bijection immediately discharges.) -/
theorem Part.mem_map_equiv_iff {alpha beta : Type*} (relabel : alpha ≃ beta)
    (value : Part alpha) (point : beta) :
    point ∈ value.map ⇑relabel ↔ relabel.symm point ∈ value := by
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨source, member, rfl⟩
    rwa [Equiv.symm_apply_apply]
  · exact fun member => ⟨relabel.symm point, member, relabel.apply_symm_apply point⟩

namespace RandomSystems.CR18.PFunDDS

universe ux uy ux' uy' ux'' uy''

variable {X : Type ux} {Y : Type uy} {X' : Type ux'} {Y' : Type uy'}
  {X'' : Type ux''} {Y'' : Type uy''}

/-! ## Sub-history projections under a re-tagging of the history -/

@[simp]
theorem filterMap_getLeft?_map_swap (history : List (X ⊕ X')) :
    (history.map Sum.swap).filterMap Sum.getLeft? =
      history.filterMap Sum.getRight? := by
  rw [List.filterMap_map]
  congr 1
  funext entry
  cases entry <;> rfl

@[simp]
theorem filterMap_getRight?_map_swap (history : List (X ⊕ X')) :
    (history.map Sum.swap).filterMap Sum.getRight? =
      history.filterMap Sum.getLeft? := by
  rw [List.filterMap_map]
  congr 1
  funext entry
  cases entry <;> rfl

/-- The left sub-history of a re-tagged history is the re-tagging of the left
sub-history: `par`'s two projections are natural in the alphabets. -/
@[simp]
theorem filterMap_getLeft?_map_sumMap {Z : Type*} {Z' : Type*}
    (onLeft : X → Z) (onRight : X' → Z') (history : List (X ⊕ X')) :
    (history.map (Sum.map onLeft onRight)).filterMap Sum.getLeft? =
      (history.filterMap Sum.getLeft?).map onLeft := by
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext entry
  cases entry <;> rfl

/-- Right-hand twin of `filterMap_getLeft?_map_sumMap`. -/
@[simp]
theorem filterMap_getRight?_map_sumMap {Z : Type*} {Z' : Type*}
    (onLeft : X → Z) (onRight : X' → Z') (history : List (X ⊕ X')) :
    (history.map (Sum.map onLeft onRight)).filterMap Sum.getRight? =
      (history.filterMap Sum.getRight?).map onRight := by
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext entry
  cases entry <;> rfl

/-- Re-associating a history splits off the first component's sub-history as
the first component of the first component's. -/
@[simp]
theorem filterMap_getLeft?_map_sumAssoc (history : List ((X ⊕ X') ⊕ X'')) :
    (history.map ⇑(Equiv.sumAssoc X X' X'')).filterMap Sum.getLeft? =
      (history.filterMap Sum.getLeft?).filterMap Sum.getLeft? := by
  rw [List.filterMap_map, List.filterMap_filterMap]
  congr 1
  funext entry
  rcases entry with first | third
  · cases first <;> rfl
  · rfl

/-- …the middle component's sub-history is reached one way on the left of the
re-association and the other way on its right. -/
@[simp]
theorem filterMap_getLeft?_getRight?_map_sumAssoc (history : List ((X ⊕ X') ⊕ X'')) :
    ((history.map ⇑(Equiv.sumAssoc X X' X'')).filterMap Sum.getRight?).filterMap
        Sum.getLeft? =
      (history.filterMap Sum.getLeft?).filterMap Sum.getRight? := by
  rw [List.filterMap_map, List.filterMap_filterMap, List.filterMap_filterMap]
  congr 1
  funext entry
  rcases entry with first | third
  · cases first <;> rfl
  · rfl

/-- …and the last component's sub-history survives the re-association. -/
@[simp]
theorem filterMap_getRight?_getRight?_map_sumAssoc (history : List ((X ⊕ X') ⊕ X'')) :
    ((history.map ⇑(Equiv.sumAssoc X X' X'')).filterMap Sum.getRight?).filterMap
        Sum.getRight? =
      history.filterMap Sum.getRight? := by
  rw [List.filterMap_map, List.filterMap_filterMap]
  congr 1
  funext entry
  rcases entry with first | third
  · cases first <;> rfl
  · rfl

/-- `getLast?`-shaped form of `TypedResource.getLast?_filterMap_getLeft`: a
history whose last entry is left-tagged has that entry last in its left
sub-history. -/
theorem getLast?_filterMap_getLeft? {alpha beta : Type*}
    {history : List (alpha ⊕ beta)} {value : alpha}
    (last : history.getLast? = some (Sum.inl value)) :
    (history.filterMap Sum.getLeft?).getLast? = some value := by
  have nonempty : history ≠ [] := by
    rintro rfl
    simp at last
  exact TypedResource.getLast?_filterMap_getLeft nonempty
    (Option.some.inj ((List.getLast?_eq_some_getLast nonempty).symm.trans last))

/-- Right-tagged twin of `getLast?_filterMap_getLeft?`. -/
theorem getLast?_filterMap_getRight? {alpha beta : Type*}
    {history : List (alpha ⊕ beta)} {value : beta}
    (last : history.getLast? = some (Sum.inr value)) :
    (history.filterMap Sum.getRight?).getLast? = some value := by
  have nonempty : history ≠ [] := by
    rintro rfl
    simp at last
  exact TypedResource.getLast?_filterMap_getRight nonempty
    (Option.some.inj ((List.getLast?_eq_some_getLast nonempty).symm.trans last))

/-! ## The domain of a tagged parallel

`mem_par_iff` leaves the active-query `match` in place.  The three statements
below resolve it: the composite is defined exactly when the history is
nonempty and each component is defined on its own sub-history, so the guard
`history ≠ [] → Dom` — the form in which one `par` meets another — is simply
the conjunction of the component guards, and once the tag of the last query is
known the composite's own guard on that side is redundant. -/

/-- Which histories a tagged parallel composition is defined on. -/
theorem dom_par_iff (s : DDS X Y) (t : DDS X' Y') (history : List (X ⊕ X')) :
    ((par s t).1 history).Dom ↔
      history ≠ [] ∧
        (history.filterMap Sum.getLeft? ≠ [] →
          (s.1 (history.filterMap Sum.getLeft?)).Dom) ∧
        (history.filterMap Sum.getRight? ≠ [] →
          (t.1 (history.filterMap Sum.getRight?)).Dom) := by
  constructor
  · intro defined
    obtain ⟨value, member⟩ := Part.dom_iff_mem.mp defined
    obtain ⟨leftGuard, rightGuard, active⟩ := (mem_par_iff s t history value).mp member
    refine ⟨?_, leftGuard, rightGuard⟩
    rintro rfl
    simp at active
  · rintro ⟨nonempty, leftGuard, rightGuard⟩
    refine Part.dom_iff_mem.mpr ?_
    rcases last : history.getLast? with _ | entry
    · exact absurd (List.getLast?_eq_none_iff.mp last) nonempty
    · cases entry with
      | inl query =>
          have subNonempty : history.filterMap Sum.getLeft? ≠ [] := by
            intro empty
            have tail := getLast?_filterMap_getLeft? last
            rw [empty] at tail
            simp at tail
          obtain ⟨answer, answerMem⟩ := Part.dom_iff_mem.mp (leftGuard subNonempty)
          exact ⟨Sum.inl answer, (mem_par_iff s t history _).mpr
            ⟨leftGuard, rightGuard, by simp only [last]; exact Part.mem_map _ answerMem⟩⟩
      | inr query =>
          have subNonempty : history.filterMap Sum.getRight? ≠ [] := by
            intro empty
            have tail := getLast?_filterMap_getRight? last
            rw [empty] at tail
            simp at tail
          obtain ⟨answer, answerMem⟩ := Part.dom_iff_mem.mp (rightGuard subNonempty)
          exact ⟨Sum.inr answer, (mem_par_iff s t history _).mpr
            ⟨leftGuard, rightGuard, by simp only [last]; exact Part.mem_map _ answerMem⟩⟩

/-- **The guard one `par` presents to another.**  The nonemptiness premise
absorbs the composite's own, so the guard of `s ∥ t` is exactly the pair of
component guards — which is what makes the two bracketings of a triple
parallel demand the same three conditions. -/
theorem guard_par_iff (s : DDS X Y) (t : DDS X' Y') (history : List (X ⊕ X')) :
    (history ≠ [] → ((par s t).1 history).Dom) ↔
      ((history.filterMap Sum.getLeft? ≠ [] →
          (s.1 (history.filterMap Sum.getLeft?)).Dom) ∧
        (history.filterMap Sum.getRight? ≠ [] →
          (t.1 (history.filterMap Sum.getRight?)).Dom)) := by
  constructor
  · intro guard
    constructor
    · intro subNonempty
      exact ((dom_par_iff s t history).mp
        (guard (List.ne_nil_of_length_pos (by
          rcases history with _ | ⟨entry, rest⟩
          · simp at subNonempty
          · simp)))).2.1 subNonempty
    · intro subNonempty
      exact ((dom_par_iff s t history).mp
        (guard (List.ne_nil_of_length_pos (by
          rcases history with _ | ⟨entry, rest⟩
          · simp at subNonempty
          · simp)))).2.2 subNonempty
  · rintro ⟨leftGuard, rightGuard⟩ nonempty
    exact (dom_par_iff s t history).mpr ⟨nonempty, leftGuard, rightGuard⟩

/-- Membership when the last query is known to be left-tagged: the composite's
own left guard is implied by the answer it produces, so only the *other*
component's guard survives. -/
theorem mem_par_of_getLast?_inl (s : DDS X Y) (t : DDS X' Y')
    {history : List (X ⊕ X')} {query : X}
    (last : history.getLast? = some (Sum.inl query)) (value : Y ⊕ Y') :
    value ∈ (par s t).1 history ↔
      (history.filterMap Sum.getRight? ≠ [] →
          (t.1 (history.filterMap Sum.getRight?)).Dom) ∧
        value ∈ (s.1 (history.filterMap Sum.getLeft?)).map Sum.inl := by
  rw [mem_par_iff]
  simp only [last]
  constructor
  · rintro ⟨-, rightGuard, member⟩
    exact ⟨rightGuard, member⟩
  · rintro ⟨rightGuard, member⟩
    obtain ⟨answer, answerMem, -⟩ := (Part.mem_map_iff _).mp member
    exact ⟨fun _ => Part.dom_iff_mem.mpr ⟨answer, answerMem⟩, rightGuard, member⟩

/-- Right-tagged twin of `mem_par_of_getLast?_inl`. -/
theorem mem_par_of_getLast?_inr (s : DDS X Y) (t : DDS X' Y')
    {history : List (X ⊕ X')} {query : X'}
    (last : history.getLast? = some (Sum.inr query)) (value : Y ⊕ Y') :
    value ∈ (par s t).1 history ↔
      (history.filterMap Sum.getLeft? ≠ [] →
          (s.1 (history.filterMap Sum.getLeft?)).Dom) ∧
        value ∈ (t.1 (history.filterMap Sum.getRight?)).map Sum.inr := by
  rw [mem_par_iff]
  simp only [last]
  constructor
  · rintro ⟨leftGuard, -, member⟩
    exact ⟨leftGuard, member⟩
  · rintro ⟨leftGuard, member⟩
    obtain ⟨answer, answerMem, -⟩ := (Part.mem_map_iff _).mp member
    exact ⟨leftGuard, fun _ => Part.dom_iff_mem.mpr ⟨answer, answerMem⟩, member⟩

/-! ## Commutativity of the tagged parallel -/

/-- **`s ∥ t` is `t ∥ s` with the tags swapped.**  Both sides guard on the two
sub-histories — the same two, read in the other order — and answer the last
query from the component owning its tag, so the only difference is which
summand that tag lives in. -/
theorem par_comm (s : DDS X Y) (t : DDS X' Y') :
    par s t = DDS.relabel (Equiv.sumComm X' X) (Equiv.sumComm Y' Y) (par t s) := by
  refine Subtype.ext (funext fun history => Part.ext fun value => ?_)
  show value ∈ (par s t).1 history ↔
    value ∈ ((par t s).1 (history.map (Sum.swap : X ⊕ X' → X' ⊕ X))).map
      ⇑(Equiv.sumComm Y' Y)
  rw [mem_par_iff, Part.mem_map_equiv_iff, mem_par_iff,
    filterMap_getLeft?_map_swap, filterMap_getRight?_map_swap,
    List.getLast?_map]
  rcases last : history.getLast? with _ | entry
  · simp
  · simp only [Equiv.sumComm_symm, Equiv.sumComm_apply, Option.map_some]
    cases entry with
    | inl _ =>
        constructor
        · rintro ⟨leftGuard, rightGuard, member⟩
          obtain ⟨answer, answerMem, rfl⟩ := (Part.mem_map_iff _).mp member
          exact ⟨rightGuard, leftGuard, Part.mem_map _ answerMem⟩
        · rintro ⟨rightGuard, leftGuard, member⟩
          obtain ⟨answer, answerMem, tagged⟩ := (Part.mem_map_iff _).mp member
          refine ⟨leftGuard, rightGuard, ?_⟩
          have recovered : value = Sum.inl answer := by
            simpa using (congrArg Sum.swap tagged).symm
          exact recovered ▸ Part.mem_map _ answerMem
    | inr _ =>
        constructor
        · rintro ⟨leftGuard, rightGuard, member⟩
          obtain ⟨answer, answerMem, rfl⟩ := (Part.mem_map_iff _).mp member
          exact ⟨rightGuard, leftGuard, Part.mem_map _ answerMem⟩
        · rintro ⟨rightGuard, leftGuard, member⟩
          obtain ⟨answer, answerMem, tagged⟩ := (Part.mem_map_iff _).mp member
          refine ⟨leftGuard, rightGuard, ?_⟩
          have recovered : value = Sum.inr answer := by
            simpa using (congrArg Sum.swap tagged).symm
          exact recovered ▸ Part.mem_map _ answerMem

/-! ## The tagged parallel is a bifunctor for relabelling -/

/-- A relabelled system's guard on a history is the original's guard on the
back-translated history — the relabelling preserves nonemptiness and does not
touch the domain. -/
theorem guard_relabel_iff {Z W : Type*} (query : X ≃ Z) (answer : Y ≃ W)
    (system : DDS X Y) (history : List Z) :
    (history ≠ [] → ((DDS.relabel query answer system).1 history).Dom) ↔
      (history.map ⇑query.symm ≠ [] →
        (system.1 (history.map ⇑query.symm)).Dom) := by
  constructor
  · intro guard nonempty
    exact guard fun empty => nonempty (by rw [empty]; rfl)
  · intro guard nonempty
    exact guard (by simpa using nonempty)

/-- **Relabelling the components is relabelling the composite.**  `par` is
natural in both alphabets: re-naming each component's queries and answers and
then composing is composing and then re-naming, along the sum of the two
re-namings. -/
theorem par_relabel {Z W Z' W' : Type*} (queryLeft : X ≃ Z) (answerLeft : Y ≃ W)
    (queryRight : X' ≃ Z') (answerRight : Y' ≃ W') (s : DDS X Y) (t : DDS X' Y') :
    par (DDS.relabel queryLeft answerLeft s)
        (DDS.relabel queryRight answerRight t) =
      DDS.relabel (Equiv.sumCongr queryLeft queryRight)
        (Equiv.sumCongr answerLeft answerRight) (par s t) := by
  refine Subtype.ext (funext fun history => Part.ext fun value => ?_)
  show value ∈ (par (DDS.relabel queryLeft answerLeft s)
      (DDS.relabel queryRight answerRight t)).1 history ↔
    value ∈ ((par s t).1
        (history.map (Sum.map ⇑queryLeft.symm ⇑queryRight.symm))).map
      ⇑(Equiv.sumCongr answerLeft answerRight)
  rw [mem_par_iff, Part.mem_map_equiv_iff, mem_par_iff,
    filterMap_getLeft?_map_sumMap, filterMap_getRight?_map_sumMap,
    List.getLast?_map]
  rcases last : history.getLast? with _ | entry
  · simp
  · cases entry with
    | inl _ =>
        simp only [Option.map_some, Sum.map_inl]
        constructor
        · rintro ⟨leftGuard, rightGuard, member⟩
          obtain ⟨tagged, taggedMem, rfl⟩ := (Part.mem_map_iff _).mp member
          obtain ⟨answer, answerMem, rfl⟩ := (Part.mem_map_iff _).mp taggedMem
          refine ⟨?_, ?_, ?_⟩
          · exact (guard_relabel_iff queryLeft answerLeft s _).mp leftGuard
          · exact (guard_relabel_iff queryRight answerRight t _).mp rightGuard
          · simpa using Part.mem_map (Sum.inl : Y → Y ⊕ Y') answerMem
        · rintro ⟨leftGuard, rightGuard, member⟩
          obtain ⟨answer, answerMem, tagged⟩ := (Part.mem_map_iff _).mp member
          refine ⟨?_, ?_, ?_⟩
          · exact (guard_relabel_iff queryLeft answerLeft s _).mpr leftGuard
          · exact (guard_relabel_iff queryRight answerRight t _).mpr rightGuard
          · have recovered : value = Sum.inl (answerLeft answer) := by
              have := congrArg ⇑(Equiv.sumCongr answerLeft answerRight) tagged
              simpa using this.symm
            rw [recovered]
            exact Part.mem_map Sum.inl (Part.mem_map _ answerMem)
    | inr _ =>
        simp only [Option.map_some, Sum.map_inr]
        constructor
        · rintro ⟨leftGuard, rightGuard, member⟩
          obtain ⟨tagged, taggedMem, rfl⟩ := (Part.mem_map_iff _).mp member
          obtain ⟨answer, answerMem, rfl⟩ := (Part.mem_map_iff _).mp taggedMem
          refine ⟨?_, ?_, ?_⟩
          · exact (guard_relabel_iff queryLeft answerLeft s _).mp leftGuard
          · exact (guard_relabel_iff queryRight answerRight t _).mp rightGuard
          · simpa using Part.mem_map (Sum.inr : Y' → Y ⊕ Y') answerMem
        · rintro ⟨leftGuard, rightGuard, member⟩
          obtain ⟨answer, answerMem, tagged⟩ := (Part.mem_map_iff _).mp member
          refine ⟨?_, ?_, ?_⟩
          · exact (guard_relabel_iff queryLeft answerLeft s _).mpr leftGuard
          · exact (guard_relabel_iff queryRight answerRight t _).mpr rightGuard
          · have recovered : value = Sum.inr (answerRight answer) := by
              have := congrArg ⇑(Equiv.sumCongr answerLeft answerRight) tagged
              simpa using this.symm
            rw [recovered]
            exact Part.mem_map Sum.inr (Part.mem_map _ answerMem)

/-- Relabelling the right component only. -/
theorem par_relabel_right {Z' W' : Type*} (queryRight : X' ≃ Z')
    (answerRight : Y' ≃ W') (s : DDS X Y) (t : DDS X' Y') :
    par s (DDS.relabel queryRight answerRight t) =
      DDS.relabel (Equiv.sumCongr (Equiv.refl X) queryRight)
        (Equiv.sumCongr (Equiv.refl Y) answerRight) (par s t) := by
  have general := par_relabel (Equiv.refl X) (Equiv.refl Y) queryRight
    answerRight s t
  rwa [DDS.relabel_refl] at general

/-- Relabelling the left component only. -/
theorem par_relabel_left {Z W : Type*} (queryLeft : X ≃ Z) (answerLeft : Y ≃ W)
    (s : DDS X Y) (t : DDS X' Y') :
    par (DDS.relabel queryLeft answerLeft s) t =
      DDS.relabel (Equiv.sumCongr queryLeft (Equiv.refl X'))
        (Equiv.sumCongr answerLeft (Equiv.refl Y')) (par s t) := by
  have general := par_relabel queryLeft answerLeft (Equiv.refl X')
    (Equiv.refl Y') s t
  rwa [DDS.relabel_refl] at general

/-! ## Associativity of the tagged parallel -/

/-- **`(s ∥ t) ∥ u` is `s ∥ (t ∥ u)` with the tags re-associated.**  Both
bracketings guard on the same three sub-histories — `guard_par_iff` is what
says so — and answer the last query from the same one of the three
components; only the nesting of the tag that names it differs. -/
theorem par_assoc (s : DDS X Y) (t : DDS X' Y') (u : DDS X'' Y'') :
    par (par s t) u =
      DDS.relabel (Equiv.sumAssoc X X' X'').symm (Equiv.sumAssoc Y Y' Y'').symm
        (par s (par t u)) := by
  refine Subtype.ext (funext fun history => Part.ext fun value => ?_)
  show value ∈ (par (par s t) u).1 history ↔
    value ∈ ((par s (par t u)).1
        (history.map ⇑(Equiv.sumAssoc X X' X''))).map
      ⇑(Equiv.sumAssoc Y Y' Y'').symm
  rw [Part.mem_map_equiv_iff, Equiv.symm_symm]
  rcases last : history.getLast? with _ | entry
  · have empty : history = [] := List.getLast?_eq_none_iff.mp last
    subst empty
    simp [mem_par_iff]
  · rcases entry with inner | third
    · cases inner with
      | inl query =>
          have lastAssoc : (history.map ⇑(Equiv.sumAssoc X X' X'')).getLast? =
              some (Sum.inl query) := by
            rw [List.getLast?_map, last]; rfl
          have lastInner : (history.filterMap Sum.getLeft?).getLast? =
              some (Sum.inl query) := getLast?_filterMap_getLeft? last
          rw [mem_par_of_getLast?_inl (par s t) u last,
            mem_par_of_getLast?_inl s (par t u) lastAssoc, guard_par_iff t u _,
            filterMap_getLeft?_map_sumAssoc,
            filterMap_getLeft?_getRight?_map_sumAssoc,
            filterMap_getRight?_getRight?_map_sumAssoc]
          simp only [Part.mem_map_iff, mem_par_of_getLast?_inl s t lastInner]
          constructor
          · rintro ⟨guardThird, inner, ⟨guardSecond, answer, answerMem, rfl⟩, rfl⟩
            exact ⟨⟨guardSecond, guardThird⟩, answer, answerMem, rfl⟩
          · rintro ⟨⟨guardSecond, guardThird⟩, answer, answerMem, tagged⟩
            refine ⟨guardThird, Sum.inl answer,
              ⟨guardSecond, answer, answerMem, rfl⟩, ?_⟩
            simpa using congrArg ⇑(Equiv.sumAssoc Y Y' Y'').symm tagged
      | inr query =>
          have lastAssoc : (history.map ⇑(Equiv.sumAssoc X X' X'')).getLast? =
              some (Sum.inr (Sum.inl query)) := by
            rw [List.getLast?_map, last]; rfl
          have lastInner : (history.filterMap Sum.getLeft?).getLast? =
              some (Sum.inr query) := getLast?_filterMap_getLeft? last
          have lastMiddle :
              ((history.map ⇑(Equiv.sumAssoc X X' X'')).filterMap
                Sum.getRight?).getLast? = some (Sum.inl query) :=
            getLast?_filterMap_getRight? lastAssoc
          rw [mem_par_of_getLast?_inl (par s t) u last,
            mem_par_of_getLast?_inr s (par t u) lastAssoc,
            filterMap_getLeft?_map_sumAssoc]
          simp only [Part.mem_map_iff, mem_par_of_getLast?_inr s t lastInner,
            mem_par_of_getLast?_inl t u lastMiddle,
            filterMap_getLeft?_getRight?_map_sumAssoc,
            filterMap_getRight?_getRight?_map_sumAssoc]
          constructor
          · rintro ⟨guardThird, inner, ⟨guardFirst, answer, answerMem, rfl⟩, rfl⟩
            exact ⟨guardFirst, Sum.inl answer,
              ⟨guardThird, answer, answerMem, rfl⟩, rfl⟩
          · rintro ⟨guardFirst, middle,
              ⟨guardThird, answer, answerMem, rfl⟩, tagged⟩
            refine ⟨guardThird, Sum.inr answer,
              ⟨guardFirst, answer, answerMem, rfl⟩, ?_⟩
            simpa using congrArg ⇑(Equiv.sumAssoc Y Y' Y'').symm tagged
    · have lastAssoc : (history.map ⇑(Equiv.sumAssoc X X' X'')).getLast? =
          some (Sum.inr (Sum.inr third)) := by
        rw [List.getLast?_map, last]; rfl
      have lastMiddle :
          ((history.map ⇑(Equiv.sumAssoc X X' X'')).filterMap
            Sum.getRight?).getLast? = some (Sum.inr third) :=
        getLast?_filterMap_getRight? lastAssoc
      rw [mem_par_of_getLast?_inr (par s t) u last,
        mem_par_of_getLast?_inr s (par t u) lastAssoc, guard_par_iff s t _,
        filterMap_getLeft?_map_sumAssoc]
      simp only [Part.mem_map_iff, mem_par_of_getLast?_inr t u lastMiddle,
        filterMap_getLeft?_getRight?_map_sumAssoc,
        filterMap_getRight?_getRight?_map_sumAssoc]
      constructor
      · rintro ⟨⟨guardFirst, guardSecond⟩, answer, answerMem, rfl⟩
        exact ⟨guardFirst, Sum.inr answer,
          ⟨guardSecond, answer, answerMem, rfl⟩, rfl⟩
      · rintro ⟨guardFirst, middle,
          ⟨guardSecond, answer, answerMem, rfl⟩, tagged⟩
        refine ⟨⟨guardFirst, guardSecond⟩, answer, answerMem, ?_⟩
        simpa using congrArg ⇑(Equiv.sumAssoc Y Y' Y'').symm tagged

end RandomSystems.CR18.PFunDDS

namespace RandomSystems

/-- UPSTREAM-CANDIDATE: the independent product is associative up to the
re-association of the three coordinates. -/
theorem Dist.fTransform_prodAssoc_prod {A B C : Type*} (firstLaw : Dist A)
    (secondLaw : Dist B) (thirdLaw : Dist C) :
    Dist.fTransform ⇑(Equiv.prodAssoc A B C)
        (Dist.prod (Dist.prod firstLaw secondLaw) thirdLaw) =
      Dist.prod firstLaw (Dist.prod secondLaw thirdLaw) := by
  ext point
  obtain ⟨firstPoint, secondPoint, thirdPoint⟩ := point
  calc Dist.fTransform ⇑(Equiv.prodAssoc A B C)
          (Dist.prod (Dist.prod firstLaw secondLaw) thirdLaw)
          (firstPoint, secondPoint, thirdPoint)
      = Dist.prod (Dist.prod firstLaw secondLaw) thirdLaw
          ((firstPoint, secondPoint), thirdPoint) :=
        Dist.fTransform_injective_apply _ _ (Equiv.prodAssoc A B C).injective
          ((firstPoint, secondPoint), thirdPoint)
    _ = Dist.prod firstLaw (Dist.prod secondLaw thirdLaw)
          (firstPoint, secondPoint, thirdPoint) := by
        rw [Dist.prod_apply, Dist.prod_apply, Dist.prod_apply, Dist.prod_apply,
          mul_assoc]

/-- UPSTREAM-CANDIDATE: the independent product is commutative up to the
exchange of the two coordinates. -/
theorem Dist.fTransform_swap_prod {A B : Type*} (leftLaw : Dist A)
    (rightLaw : Dist B) :
    Dist.fTransform Prod.swap (Dist.prod rightLaw leftLaw) =
      Dist.prod leftLaw rightLaw := by
  ext pair
  obtain ⟨first, second⟩ := pair
  calc Dist.fTransform Prod.swap (Dist.prod rightLaw leftLaw) (first, second)
      = Dist.prod rightLaw leftLaw (second, first) :=
        Dist.fTransform_injective_apply _ _ Prod.swap_injective (second, first)
    _ = Dist.prod leftLaw rightLaw (first, second) := by
        rw [Dist.prod_apply, Dist.prod_apply, mul_comm]

end RandomSystems

namespace RandomSystems.CR18.TypedResource

open RandomSystems (Dist)

noncomputable section

universe c i j k u v

variable {I : Type i} {J : Type j} {U : SignatureUniverse.{c, u, v}}

/-! ## The swap of a disjoint-union boundary

`[S,R]` and `[R,S]` sit at the two boundaries `Sum.elim right left` and
`Sum.elim left right`, which are genuinely different functions on genuinely
different interface sets.  The alphabet bijection between them is built from
the tensor's own re-association: split the tag off, swap the two summands,
put the tag back.  Nothing here mentions the *systems* — this is the
re-indexing, and `TagCompatible` (its route is `Sum.swap`) is what lets it
act on them at all. -/

section Swap

variable (left : Boundary U I) (right : Boundary U J)

/-- Queries of `[S,R]` read as queries of `[R,S]`. -/
def tensorSwapQueryEquiv :
    Query U (Sum.elim right left) ≃ Query U (Sum.elim left right) :=
  (tensorQueryEquiv right left).trans
    ((Equiv.sumComm _ _).trans (tensorQueryEquiv left right).symm)

/-- Flat answers of `[S,R]` read as flat answers of `[R,S]`. -/
def tensorSwapAnswerEquiv :
    FlatAnswer U (Sum.elim right left) ≃ FlatAnswer U (Sum.elim left right) :=
  (tensorAnswerEquiv right left).trans
    ((Equiv.sumComm _ _).trans (tensorAnswerEquiv left right).symm)

@[simp]
theorem tensorSwapQueryEquiv_index (query : Query U (Sum.elim right left)) :
    (tensorSwapQueryEquiv left right query).1 = Sum.swap query.1 := by
  obtain ⟨interface, value⟩ := query
  cases interface <;> rfl

@[simp]
theorem tensorSwapAnswerEquiv_index (answer : FlatAnswer U (Sum.elim right left)) :
    (tensorSwapAnswerEquiv left right answer).1 = Sum.swap answer.1 := by
  obtain ⟨interface, value⟩ := answer
  cases interface <;> rfl

/-- The swap is a re-indexing: it relocates queries and answers along the one
interface map `Sum.swap`. -/
theorem tagCompatible_tensorSwap :
    TagCompatible (tensorSwapQueryEquiv left right)
      (tensorSwapAnswerEquiv left right) :=
  tagCompatible_of_route Sum.swap (tensorSwapQueryEquiv_index left right)
    (tensorSwapAnswerEquiv_index left right)

/-- Cancelling the tensor's own re-association against the swap's: what is
left is the bare summand exchange. -/
theorem tensorQueryEquiv_symm_trans_swap :
    (tensorQueryEquiv right left).symm.trans (tensorSwapQueryEquiv left right) =
      (Equiv.sumComm (Query U right) (Query U left)).trans
        (tensorQueryEquiv left right).symm := by
  rw [tensorSwapQueryEquiv, ← Equiv.trans_assoc, Equiv.symm_trans_self,
    Equiv.refl_trans]

/-- Answer-side twin of `tensorQueryEquiv_symm_trans_swap`. -/
theorem tensorAnswerEquiv_symm_trans_swap :
    (tensorAnswerEquiv right left).symm.trans (tensorSwapAnswerEquiv left right) =
      (Equiv.sumComm (FlatAnswer U right) (FlatAnswer U left)).trans
        (tensorAnswerEquiv left right).symm := by
  rw [tensorSwapAnswerEquiv, ← Equiv.trans_assoc, Equiv.symm_trans_self,
    Equiv.refl_trans]

end Swap

/-! ## Commutativity up the tower -/

section CommTower

variable {left : Boundary U I} {right : Boundary U J}

/-- **`[R,S] = [S,R]` re-indexed, deterministic level.** -/
theorem DependentDDS.reindex_tensor_comm (leftSystem : DependentDDS U left)
    (rightSystem : DependentDDS U right) :
    DependentDDS.reindex (tagCompatible_tensorSwap left right)
        (rightSystem.tensor leftSystem) =
      leftSystem.tensor rightSystem := by
  apply DependentDDS.flatten_injective
  rw [DependentDDS.flatten_reindex, DependentDDS.flatten_tensor rightSystem leftSystem,
    PFunDDS.DDS.relabel_relabel, tensorQueryEquiv_symm_trans_swap,
    tensorAnswerEquiv_symm_trans_swap,
    DependentDDS.flatten_tensor leftSystem rightSystem,
    PFunDDS.par_comm leftSystem.flatten rightSystem.flatten,
    PFunDDS.DDS.relabel_relabel]

/-- **`[R,S] = [S,R]` re-indexed, law level.**  Both sides are pushforwards of
the same independent product; the exchange of the two coordinates carries one
to the other. -/
theorem DependentPDS.reindex_tensor_comm (leftLaw : DependentPDS U left)
    (rightLaw : DependentPDS U right) :
    DependentPDS.reindex (tagCompatible_tensorSwap left right)
        (DependentPDS.tensor rightLaw leftLaw) =
      DependentPDS.tensor leftLaw rightLaw := by
  unfold DependentPDS.reindex DependentPDS.tensor
  rw [Dist.fTransform_comp, ← Dist.fTransform_swap_prod leftLaw rightLaw,
    Dist.fTransform_comp]
  exact congrArg (fun step => Dist.fTransform step (Dist.prod rightLaw leftLaw))
    (funext fun pair => DependentDDS.reindex_tensor_comm pair.2 pair.1)

/-- **`[R,S] = [S,R]` re-indexed, normalized laws.** -/
theorem DependentPDS.Prob.reindex_tensor_comm (leftLaw : DependentPDS.Prob U left)
    (rightLaw : DependentPDS.Prob U right) :
    DependentPDS.Prob.reindex (tagCompatible_tensorSwap left right)
        (DependentPDS.Prob.tensor rightLaw leftLaw) =
      DependentPDS.Prob.tensor leftLaw rightLaw :=
  Subtype.ext (DependentPDS.reindex_tensor_comm leftLaw.val rightLaw.val)

variable [DecidableEq I] [DecidableEq J] [DecidableEq U.Code]

/-- **`[R,S] = [S,R]` re-indexed, contextual behavior.** -/
theorem DependentRandomSystem.reindex_tensor_comm
    (leftClass : DependentRandomSystem U left)
    (rightClass : DependentRandomSystem U right) :
    DependentRandomSystem.reindex (tagCompatible_tensorSwap left right)
        (DependentRandomSystem.tensor rightClass leftClass) =
      DependentRandomSystem.tensor leftClass rightClass := by
  induction leftClass using Quotient.inductionOn with
  | _ leftProb =>
      induction rightClass using Quotient.inductionOn with
      | _ rightProb =>
          show DependentRandomSystem.reindex _
              (DependentRandomSystem.ofProb
                (DependentPDS.Prob.tensor rightProb leftProb)) = _
          rw [DependentRandomSystem.reindex_ofProb,
            DependentPDS.Prob.reindex_tensor_comm]
          rfl

end CommTower

/-! ## The re-association of a nested disjoint-union boundary -/

section Assoc

variable {K : Type k}
variable (first : Boundary U I) (second : Boundary U J) (third : Boundary U K)

/-- Queries of `[R,[S,T]]` read as queries of `[[R,S],T]`: split both tags
off, re-associate the three summands, put both tags back. -/
def tensorAssocQueryEquiv :
    Query U (Sum.elim first (Sum.elim second third)) ≃
      Query U (Sum.elim (Sum.elim first second) third) :=
  (tensorQueryEquiv first (Sum.elim second third)).trans
    ((Equiv.sumCongr (Equiv.refl (Query U first))
        (tensorQueryEquiv second third)).trans
      ((Equiv.sumAssoc (Query U first) (Query U second)
            (Query U third)).symm.trans
        ((Equiv.sumCongr (tensorQueryEquiv first second).symm
            (Equiv.refl (Query U third))).trans
          (tensorQueryEquiv (Sum.elim first second) third).symm)))

/-- Flat answers of `[R,[S,T]]` read as flat answers of `[[R,S],T]`. -/
def tensorAssocAnswerEquiv :
    FlatAnswer U (Sum.elim first (Sum.elim second third)) ≃
      FlatAnswer U (Sum.elim (Sum.elim first second) third) :=
  (tensorAnswerEquiv first (Sum.elim second third)).trans
    ((Equiv.sumCongr (Equiv.refl (FlatAnswer U first))
        (tensorAnswerEquiv second third)).trans
      ((Equiv.sumAssoc (FlatAnswer U first) (FlatAnswer U second)
            (FlatAnswer U third)).symm.trans
        ((Equiv.sumCongr (tensorAnswerEquiv first second).symm
            (Equiv.refl (FlatAnswer U third))).trans
          (tensorAnswerEquiv (Sum.elim first second) third).symm)))

@[simp]
theorem tensorAssocQueryEquiv_index
    (query : Query U (Sum.elim first (Sum.elim second third))) :
    (tensorAssocQueryEquiv first second third query).1 =
      (Equiv.sumAssoc I J K).symm query.1 := by
  obtain ⟨interface, value⟩ := query
  rcases interface with _ | rest
  · rfl
  · cases rest <;> rfl

@[simp]
theorem tensorAssocAnswerEquiv_index
    (answer : FlatAnswer U (Sum.elim first (Sum.elim second third))) :
    (tensorAssocAnswerEquiv first second third answer).1 =
      (Equiv.sumAssoc I J K).symm answer.1 := by
  obtain ⟨interface, value⟩ := answer
  rcases interface with _ | rest
  · rfl
  · cases rest <;> rfl

/-- The re-association is a re-indexing: queries and answers both relocate
along `(Equiv.sumAssoc I J K).symm`. -/
theorem tagCompatible_tensorAssoc :
    TagCompatible (tensorAssocQueryEquiv first second third)
      (tensorAssocAnswerEquiv first second third) :=
  tagCompatible_of_route ⇑(Equiv.sumAssoc I J K).symm
    (tensorAssocQueryEquiv_index first second third)
    (tensorAssocAnswerEquiv_index first second third)

/-- Cancelling the two nested tensor re-associations against the composite
one: what is left is the bare re-association of the three summands. -/
theorem tensorQueryEquiv_assoc_cancel :
    (Equiv.sumCongr (Equiv.refl (Query U first))
          (tensorQueryEquiv second third).symm).trans
        ((tensorQueryEquiv first (Sum.elim second third)).symm.trans
          (tensorAssocQueryEquiv first second third)) =
      (Equiv.sumAssoc (Query U first) (Query U second)
            (Query U third)).symm.trans
        ((Equiv.sumCongr (tensorQueryEquiv first second).symm
            (Equiv.refl (Query U third))).trans
          (tensorQueryEquiv (Sum.elim first second) third).symm) := by
  refine Equiv.ext ?_
  rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl

/-- Answer-side twin of `tensorQueryEquiv_assoc_cancel`. -/
theorem tensorAnswerEquiv_assoc_cancel :
    (Equiv.sumCongr (Equiv.refl (FlatAnswer U first))
          (tensorAnswerEquiv second third).symm).trans
        ((tensorAnswerEquiv first (Sum.elim second third)).symm.trans
          (tensorAssocAnswerEquiv first second third)) =
      (Equiv.sumAssoc (FlatAnswer U first) (FlatAnswer U second)
            (FlatAnswer U third)).symm.trans
        ((Equiv.sumCongr (tensorAnswerEquiv first second).symm
            (Equiv.refl (FlatAnswer U third))).trans
          (tensorAnswerEquiv (Sum.elim first second) third).symm) := by
  refine Equiv.ext ?_
  rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl

end Assoc

/-! ## Associativity up the tower -/

section AssocTower

variable {K : Type k}
variable {first : Boundary U I} {second : Boundary U J} {third : Boundary U K}

/-- **`[[R,S],T] = [R,[S,T]]` re-indexed, deterministic level.** -/
theorem DependentDDS.reindex_tensor_assoc (firstSystem : DependentDDS U first)
    (secondSystem : DependentDDS U second)
    (thirdSystem : DependentDDS U third) :
    DependentDDS.reindex (tagCompatible_tensorAssoc first second third)
        (firstSystem.tensor (secondSystem.tensor thirdSystem)) =
      (firstSystem.tensor secondSystem).tensor thirdSystem := by
  apply DependentDDS.flatten_injective
  rw [DependentDDS.flatten_reindex,
    DependentDDS.flatten_tensor firstSystem (secondSystem.tensor thirdSystem),
    DependentDDS.flatten_tensor secondSystem thirdSystem,
    PFunDDS.par_relabel_right, PFunDDS.DDS.relabel_relabel,
    PFunDDS.DDS.relabel_relabel, tensorQueryEquiv_assoc_cancel,
    tensorAnswerEquiv_assoc_cancel,
    DependentDDS.flatten_tensor (firstSystem.tensor secondSystem) thirdSystem,
    DependentDDS.flatten_tensor firstSystem secondSystem,
    PFunDDS.par_relabel_left, PFunDDS.DDS.relabel_relabel, PFunDDS.par_assoc,
    PFunDDS.DDS.relabel_relabel]

/-- **`[[R,S],T] = [R,[S,T]]` re-indexed, law level.**  Both sides are
pushforwards of the same threefold independent product; the re-association of
the three coordinates carries one to the other. -/
theorem DependentPDS.reindex_tensor_assoc (firstLaw : DependentPDS U first)
    (secondLaw : DependentPDS U second) (thirdLaw : DependentPDS U third) :
    DependentPDS.reindex (tagCompatible_tensorAssoc first second third)
        (DependentPDS.tensor firstLaw
          (DependentPDS.tensor secondLaw thirdLaw)) =
      DependentPDS.tensor (DependentPDS.tensor firstLaw secondLaw) thirdLaw := by
  have distributeRight :
      Dist.prod firstLaw
          (Dist.fTransform
            (fun pair : DependentDDS U second × DependentDDS U third =>
              pair.1.tensor pair.2) (Dist.prod secondLaw thirdLaw)) =
        Dist.fTransform
          (fun triple : DependentDDS U first ×
              (DependentDDS U second × DependentDDS U third) =>
            (triple.1, triple.2.1.tensor triple.2.2))
          (Dist.prod firstLaw (Dist.prod secondLaw thirdLaw)) := by
    have step := Dist.pushforward_product_eq_product_pushforwards id
      (fun pair : DependentDDS U second × DependentDDS U third =>
        pair.1.tensor pair.2) firstLaw (Dist.prod secondLaw thirdLaw)
    rw [Dist.fTransform_id] at step
    exact step.symm
  have distributeLeft :
      Dist.prod
          (Dist.fTransform
            (fun pair : DependentDDS U first × DependentDDS U second =>
              pair.1.tensor pair.2) (Dist.prod firstLaw secondLaw)) thirdLaw =
        Dist.fTransform
          (fun triple : (DependentDDS U first × DependentDDS U second) ×
              DependentDDS U third =>
            (triple.1.1.tensor triple.1.2, triple.2))
          (Dist.prod (Dist.prod firstLaw secondLaw) thirdLaw) := by
    have step := Dist.pushforward_product_eq_product_pushforwards
      (fun pair : DependentDDS U first × DependentDDS U second =>
        pair.1.tensor pair.2) id (Dist.prod firstLaw secondLaw) thirdLaw
    rw [Dist.fTransform_id] at step
    exact step.symm
  have leftForm :
      DependentPDS.reindex (tagCompatible_tensorAssoc first second third)
          (DependentPDS.tensor firstLaw
            (DependentPDS.tensor secondLaw thirdLaw)) =
        Dist.fTransform
          (fun triple : DependentDDS U first ×
              (DependentDDS U second × DependentDDS U third) =>
            (triple.1.tensor triple.2.1).tensor triple.2.2)
          (Dist.prod firstLaw (Dist.prod secondLaw thirdLaw)) := by
    unfold DependentPDS.reindex DependentPDS.tensor
    rw [distributeRight, Dist.fTransform_comp, Dist.fTransform_comp]
    exact congrArg (fun step => Dist.fTransform step
        (Dist.prod firstLaw (Dist.prod secondLaw thirdLaw)))
      (funext fun triple =>
        DependentDDS.reindex_tensor_assoc triple.1 triple.2.1 triple.2.2)
  have rightForm :
      DependentPDS.tensor (DependentPDS.tensor firstLaw secondLaw) thirdLaw =
        Dist.fTransform
          (fun triple : DependentDDS U first ×
              (DependentDDS U second × DependentDDS U third) =>
            (triple.1.tensor triple.2.1).tensor triple.2.2)
          (Dist.prod firstLaw (Dist.prod secondLaw thirdLaw)) := by
    conv_lhs => unfold DependentPDS.tensor
    rw [distributeLeft, Dist.fTransform_comp,
      ← Dist.fTransform_prodAssoc_prod firstLaw secondLaw thirdLaw,
      Dist.fTransform_comp]
    rfl
  rw [leftForm, rightForm]

/-- **`[[R,S],T] = [R,[S,T]]` re-indexed, normalized laws.** -/
theorem DependentPDS.Prob.reindex_tensor_assoc
    (firstLaw : DependentPDS.Prob U first) (secondLaw : DependentPDS.Prob U second)
    (thirdLaw : DependentPDS.Prob U third) :
    DependentPDS.Prob.reindex (tagCompatible_tensorAssoc first second third)
        (DependentPDS.Prob.tensor firstLaw
          (DependentPDS.Prob.tensor secondLaw thirdLaw)) =
      DependentPDS.Prob.tensor (DependentPDS.Prob.tensor firstLaw secondLaw)
        thirdLaw :=
  Subtype.ext
    (DependentPDS.reindex_tensor_assoc firstLaw.val secondLaw.val thirdLaw.val)

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq U.Code]

/-- **`[[R,S],T] = [R,[S,T]]` re-indexed, contextual behavior.** -/
theorem DependentRandomSystem.reindex_tensor_assoc
    (firstClass : DependentRandomSystem U first)
    (secondClass : DependentRandomSystem U second)
    (thirdClass : DependentRandomSystem U third) :
    DependentRandomSystem.reindex (tagCompatible_tensorAssoc first second third)
        (DependentRandomSystem.tensor firstClass
          (DependentRandomSystem.tensor secondClass thirdClass)) =
      DependentRandomSystem.tensor
        (DependentRandomSystem.tensor firstClass secondClass) thirdClass := by
  induction firstClass using Quotient.inductionOn with
  | _ firstProb =>
      induction secondClass using Quotient.inductionOn with
      | _ secondProb =>
          induction thirdClass using Quotient.inductionOn with
          | _ thirdProb =>
              show DependentRandomSystem.reindex _
                  (DependentRandomSystem.ofProb
                    (DependentPDS.Prob.tensor firstProb
                      (DependentPDS.Prob.tensor secondProb thirdProb))) = _
              rw [DependentRandomSystem.reindex_ofProb,
                DependentPDS.Prob.reindex_tensor_assoc]
              rfl

end AssocTower

/-! ## Crossing the last boundary equality

Below the bundled carrier every statement above is a plain equality, because
`tensorSwapQueryEquiv` was built to land at `Sum.elim left right` on the nose.
`Resource.relabelInterfaces` instead lands at `relabelBoundary relabel _`,
which is the *same function* but not the same term, so the two re-indexings
are heterogeneous.  `Resource.relabelInterfaces_mk` is the one place where
that is crossed: given the boundary equality and the two equivalences
heterogeneously identified, `relabelInterfaces` may be read as re-indexing
along any tag-compatible pair at the equal boundary. -/

section Transport

variable {K K' : Type*}

/-- Two equivalences into the query- or answer-alphabet of two *equal*
boundaries agree heterogeneously as soon as they agree on tags and fibres.
Stated for an arbitrary code-indexed family so that `U.input` and `U.output`
are both instances. -/
theorem heq_equiv_sigma_of_boundary_eq {family : U.Code → Type*}
    {source target : Boundary U K} (boundaries : source = target)
    {alphabet : Type*}
    (fromSource : alphabet ≃ Σ interface : K, family (source interface))
    (fromTarget : alphabet ≃ Σ interface : K, family (target interface))
    (index : ∀ point, (fromSource point).1 = (fromTarget point).1)
    (fibre : ∀ point, HEq (fromSource point).2 (fromTarget point).2) :
    HEq fromSource fromTarget := by
  subst boundaries
  exact heq_of_eq (Equiv.ext fun point => Sigma.ext (index point) (fibre point))

variable [DecidableEq K] [DecidableEq K'] [DecidableEq U.Code]

/-- **Re-indexing along a bijection, retargeted at an equal boundary.**  The
bundled carrier absorbs the difference between `relabelBoundary relabel b` and
any boundary equal to it: `Resource.relabelInterfaces` *is* re-indexing along
the tag-compatible pair sitting at that boundary. -/
theorem Resource.relabelInterfaces_mk {relabel : K ≃ K'} {base : Boundary U K}
    {target : Boundary U K'}
    (boundaries : relabelBoundary relabel base = target)
    {queryE : Query U base ≃ Query U target}
    {answerE : FlatAnswer U base ≃ FlatAnswer U target}
    (sameQuery : HEq queryE (relabelQueryEquiv relabel base))
    (sameAnswer : HEq answerE (relabelAnswerEquiv relabel base))
    (compatible : TagCompatible queryE answerE)
    (system : DependentRandomSystem U base) :
    Resource.relabelInterfaces relabel ⟨base, system⟩ =
      ⟨target, DependentRandomSystem.reindex compatible system⟩ := by
  subst boundaries
  obtain rfl : queryE = relabelQueryEquiv relabel base := eq_of_heq sameQuery
  obtain rfl : answerE = relabelAnswerEquiv relabel base := eq_of_heq sameAnswer
  rfl

end Transport

/-! ## The headline: `[R,S]` and `[S,R]` differ only in the names -/

variable [DecidableEq I] [DecidableEq J] [DecidableEq U.Code]

/-- **Disjoint-interface parallel composition is commutative up to a bijective
re-indexing of the interface set.**  `[R,S]` at `I ⊕ J` and `[S,R]` at `J ⊕ I`
are the same resource: `Equiv.sumComm` renames every interface and nothing
else changes.  A plain equality, not an `≈[0]` bound — no error is spent,
because renaming is an isometry in both directions
(`Resource.edist_relabelInterfaces`). -/
theorem Resource.tensor_comm (leftResource : Resource I U)
    (rightResource : Resource J U) :
    Resource.tensor leftResource rightResource =
      Resource.relabelInterfaces (Equiv.sumComm J I)
        (Resource.tensor rightResource leftResource) := by
  rcases leftResource with ⟨leftBoundary, leftSystem⟩
  rcases rightResource with ⟨rightBoundary, rightSystem⟩
  have boundaries :
      relabelBoundary (Equiv.sumComm J I)
          (Sum.elim rightBoundary leftBoundary) =
        Sum.elim leftBoundary rightBoundary := by
    funext interface
    cases interface <;> rfl
  have sameQuery :
      HEq (tensorSwapQueryEquiv leftBoundary rightBoundary)
        (relabelQueryEquiv (Equiv.sumComm J I)
          (Sum.elim rightBoundary leftBoundary)) := by
    refine heq_equiv_sigma_of_boundary_eq boundaries.symm _ _ ?_ ?_
    · rintro ⟨interface, value⟩
      cases interface <;> rfl
    · rintro ⟨interface, value⟩
      cases interface <;> rfl
  have sameAnswer :
      HEq (tensorSwapAnswerEquiv leftBoundary rightBoundary)
        (relabelAnswerEquiv (Equiv.sumComm J I)
          (Sum.elim rightBoundary leftBoundary)) := by
    refine heq_equiv_sigma_of_boundary_eq boundaries.symm _ _ ?_ ?_
    · rintro ⟨interface, value⟩
      cases interface <;> rfl
    · rintro ⟨interface, value⟩
      cases interface <;> rfl
  show (⟨Sum.elim leftBoundary rightBoundary,
      DependentRandomSystem.tensor leftSystem rightSystem⟩ : Resource (I ⊕ J) U) =
    Resource.relabelInterfaces (Equiv.sumComm J I)
      ⟨Sum.elim rightBoundary leftBoundary,
        DependentRandomSystem.tensor rightSystem leftSystem⟩
  rw [Resource.relabelInterfaces_mk boundaries sameQuery sameAnswer
      (tagCompatible_tensorSwap leftBoundary rightBoundary),
    DependentRandomSystem.reindex_tensor_comm]

variable {K : Type k} [DecidableEq K]

/-- **Disjoint-interface parallel composition is associative up to a bijective
re-indexing of the interface set.**  `[[R,S],T]` at `(I ⊕ J) ⊕ K` and
`[R,[S,T]]` at `I ⊕ (J ⊕ K)` are the same resource: `Equiv.sumAssoc` re-brackets
every interface name and nothing else changes.  Again a plain equality, at no
error. -/
theorem Resource.tensor_assoc (firstResource : Resource I U)
    (secondResource : Resource J U) (thirdResource : Resource K U) :
    Resource.tensor (Resource.tensor firstResource secondResource)
        thirdResource =
      Resource.relabelInterfaces (Equiv.sumAssoc I J K).symm
        (Resource.tensor firstResource
          (Resource.tensor secondResource thirdResource)) := by
  rcases firstResource with ⟨firstBoundary, firstSystem⟩
  rcases secondResource with ⟨secondBoundary, secondSystem⟩
  rcases thirdResource with ⟨thirdBoundary, thirdSystem⟩
  have boundaries :
      relabelBoundary (Equiv.sumAssoc I J K).symm
          (Sum.elim firstBoundary (Sum.elim secondBoundary thirdBoundary)) =
        Sum.elim (Sum.elim firstBoundary secondBoundary) thirdBoundary := by
    funext interface
    rcases interface with inner | _
    · cases inner <;> rfl
    · rfl
  have sameQuery :
      HEq (tensorAssocQueryEquiv firstBoundary secondBoundary thirdBoundary)
        (relabelQueryEquiv (Equiv.sumAssoc I J K).symm
          (Sum.elim firstBoundary (Sum.elim secondBoundary thirdBoundary))) := by
    refine heq_equiv_sigma_of_boundary_eq boundaries.symm _ _ ?_ ?_ <;>
      rintro ⟨interface, value⟩ <;> rcases interface with _ | rest
    · rfl
    · cases rest <;> rfl
    · rfl
    · cases rest <;> rfl
  have sameAnswer :
      HEq (tensorAssocAnswerEquiv firstBoundary secondBoundary thirdBoundary)
        (relabelAnswerEquiv (Equiv.sumAssoc I J K).symm
          (Sum.elim firstBoundary (Sum.elim secondBoundary thirdBoundary))) := by
    refine heq_equiv_sigma_of_boundary_eq boundaries.symm _ _ ?_ ?_ <;>
      rintro ⟨interface, value⟩ <;> rcases interface with _ | rest
    · rfl
    · cases rest <;> rfl
    · rfl
    · cases rest <;> rfl
  show (⟨Sum.elim (Sum.elim firstBoundary secondBoundary) thirdBoundary,
      DependentRandomSystem.tensor
        (DependentRandomSystem.tensor firstSystem secondSystem) thirdSystem⟩ :
        Resource ((I ⊕ J) ⊕ K) U) =
    Resource.relabelInterfaces (Equiv.sumAssoc I J K).symm
      ⟨Sum.elim firstBoundary (Sum.elim secondBoundary thirdBoundary),
        DependentRandomSystem.tensor firstSystem
          (DependentRandomSystem.tensor secondSystem thirdSystem)⟩
  rw [Resource.relabelInterfaces_mk boundaries sameQuery sameAnswer
      (tagCompatible_tensorAssoc firstBoundary secondBoundary thirdBoundary),
    DependentRandomSystem.reindex_tensor_assoc]

end

/-! ## Receipts -/

/-- info: 'RandomSystems.CR18.TypedResource.Resource.tensor_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Resource.tensor_comm

/-- info: 'RandomSystems.CR18.TypedResource.Resource.tensor_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Resource.tensor_assoc

end RandomSystems.CR18.TypedResource
