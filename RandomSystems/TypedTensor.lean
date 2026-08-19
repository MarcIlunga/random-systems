/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedParallel

/-!
# Disjoint-interface parallel composition (Jost's `[R, S]`), and interface merging

`TypedParallel.lean` builds Abstract Cryptography's `R ∥ R'`: **the same
interface set**, each interface carrying the tagged sum of the two
components' alphabets (`sumBoundary`).  Jost's thesis (§2.2.2, printed
p. 17) builds the other operation: the two resources are required to have
**disjoint interface sets** and `[R, S]` simply is their union.  This
module is that operation on the typed carrier — `DependentDDS.tensor` at
the boundary `Sum.elim left right : Boundary U (I ⊕ J)` — together with
Jost's Prop. 2.2.3 (2) and the re-indexing calculus that recovers his
n-ary converters on top of it.

## What the disjoint form saves

The whole alphabet-coding layer.  `sumBoundary` has to *invent* a code at
each shared interface, which is why `TypedParallel` needs the `HasSumCode`
class and pays for it twice: once in `queryEquiv` (`HasSumCode.inputEquiv`
under the index, then `Equiv.sigmaSumDistrib`) and once in `answerEquiv`.
Here the boundary is `Sum.elim`, whose fibre at `Sum.inl i` **is** `left i`
by iota, so

```
Query U (Sum.elim left right) = Σ k : I ⊕ J, U.input (Sum.elim left right k)
                              ≃ Query U left ⊕ Query U right
```

is a single `Equiv.sumSigmaDistrib` and nothing else: no class, no code, no
alphabet isomorphism.  `tensorQueryEquiv` and `tensorAnswerEquiv` are
literally the same mathlib equivalence at two different families, and
`tensorQueryEquiv_inl`, `tensorAnswerEquiv_symm_inl_index` and the
attachment side condition `left i = source` are all `rfl`.

## Where the coding goes instead

It does not disappear from the development, it moves to where it belongs.
`§ Interface re-indexing` isolates the operation that *does* need a coded
alphabet: **merging** a block of interfaces into one
(`DependentDDS.mergeBlock`).  A block coding is exactly a pair
`U.input blockCode ≃ Query U block`, `U.output blockCode ≃ FlatAnswer U block`,
and in the two-interface case that pair **is** `HasSumCode.inputEquiv` /
`outputEquiv` (`twoBlockInputCode`, `DependentDDS.mergeTwo`).  So
`HasSumCode` stops being the coding for parallel composition and becomes
the coding for merge — which is what an n-ary converter needs, since a
converter reaching into two interfaces at once is a unary converter at
their merge.

Merging is a relabelling and therefore free of content in the only sense
that matters: `DependentRandomSystem.edist_mergeBlock` says it is an
**isometry** for the contextual metric, and `mergeBlock_injective` says it
loses nothing.  It is however **not** invertible
(`tagCompatible_not_symmetric`, `not_surjective_mergeBlock`): the merged
boundary admits resources that answer a block query on the *wrong side* of
the coded sum, which no unmerged resource can do.  The image is named
exactly by `DependentDDS.exists_reindex_eq_iff`.

## Structure

* `§ The uniform-chart routed parallel` — `PFunConverter.General.routedPar`,
  the disjoint-interface parallel in the boundary-erased chart that
  `TypedAttachment` uses.  Clause 2 lives there because its two sides sit at
  boundaries that are propositionally but not definitionally equal.
* `§ The disjoint-union boundary` — the two equivalences and their
  index-preservation lemmas.
* `§ Tag faithfulness of a relabelled flat parallel` —
  `tagFaithful_relabel_par_general`: `TypedParallel`'s
  `tag_faithful_relabel_par` with the two index maps made parameters, so
  `sumBoundary`'s instance (`id`/`id`) and the tensor's
  (`Sum.inl`/`Sum.inr`) are the same theorem.
* `§ The tensor tower` — deterministic (`DependentDDS.tensor`), law
  (`DependentPDS.tensor`), contextual quotient
  (`DependentRandomSystem.tensor`) and heterogeneous carrier
  (`Resource.tensor`), with `flatten_tensor` as the defining equation
  through which every strict fact (`StrictContext.maxEDist_par_le`,
  `equivalent_par`, the cancellation theorems) transports, plus
  `embed_tensor`, the same object in the uniform chart.
* `§ Jost's Proposition 2.2.3, clause 2` — `attach_tensor_inl` at all four
  levels, resting on the routing law
  `PFunConverter.General.attachAt_routedPar_left`: CR18 Def. 3.13 attachment
  at a left-tagged interface commutes with `routedPar`.  That law, not the
  frame's pass-through clauses, is the content of clause 2 (see the section
  docstring).
* `§ Interface re-indexing` and `§ Merging a block of interfaces`.

## The carrier

`Resource.tensor : Resource I U → Resource J U → Resource (I ⊕ J) U` is
genuinely heterogeneous in the interface type, so — unlike
`Resource.parallel` — it is *not* a binary operation on one `Resource I U`
and cannot be an AC-side `Par (Phi I U)` instance.  That is Jost's own
reading (parallel composition is defined only for disjoint interface sets)
rather than a defect, but it is the one thing the move costs.
-/

namespace RandomSystems.CR18.PFunDDS

universe ux uy ux' uy'

variable {X : Type ux} {Y : Type uy} {X' : Type ux'} {Y' : Type uy'}

/-- Membership in the tagged parallel composition with its two sub-history
guards made explicit.  (`CompatibleMetric.lean` and `EmulateRealization.lean`
each carry a `private` copy of this unfolding; this is the public statement,
and a migration candidate for `PFunDDS`.) -/
theorem mem_par_iff (s : DDS X Y) (t : DDS X' Y') (history : List (X ⊕ X'))
    (value : Y ⊕ Y') :
    value ∈ (par s t).1 history ↔
      ((history.filterMap Sum.getLeft? ≠ []) →
        (s.1 (history.filterMap Sum.getLeft?)).Dom) ∧
      ((history.filterMap Sum.getRight? ≠ []) →
        (t.1 (history.filterMap Sum.getRight?)).Dom) ∧
      value ∈ (match history.getLast? with
        | some (Sum.inl _) => (s.1 (history.filterMap Sum.getLeft?)).map Sum.inl
        | some (Sum.inr _) => (t.1 (history.filterMap Sum.getRight?)).map Sum.inr
        | none => Part.none) := by
  show value ∈ Part.assert _ _ ↔ _
  rw [Part.mem_assert_iff]
  constructor
  · rintro ⟨hleft, hmem⟩
    rw [Part.mem_assert_iff] at hmem
    obtain ⟨hright, hmem⟩ := hmem
    exact ⟨hleft, hright, hmem⟩
  · rintro ⟨hleft, hright, hmem⟩
    exact ⟨hleft, Part.mem_assert_iff.mpr ⟨hright, hmem⟩⟩

end RandomSystems.CR18.PFunDDS

/-! ## The uniform-chart routed parallel

Attachment (`TypedAttachment.lean`) is defined by crossing into the uniform
`(K × AmbientInput U, AmbientOutput U)` chart, where the boundary has been
erased from the *type*.  That chart is where a statement relating attachment
to a composition has to live, because the two sides of such a statement sit
at boundaries that are propositionally but not definitionally equal
(`Function.update` on `I ⊕ J` at `Sum.inl i` versus `Function.update` on `I`
at `i`), and `DependentDDS.heq_of_boundary_eq_of_embed_eq` is exactly the
transport that erases the difference.

`routedPar` is the disjoint-interface parallel in that chart.  Unlike
`PFunDDS.par` it needs no answer tag: both components already answer in the
shared `AmbientOutput U`, and the interface tag of the query says which one
answered.  It is `PFunDDS.par` re-associated along `Equiv.sumProdDistrib`
with the redundant answer tag collapsed, written out because every consumer
needs its two sub-history guards in explicit form. -/

namespace RandomSystems.CR18.PFunConverter.General

open scoped PFunDDS

universe up uq ux uy

variable {P : Type up} {Q : Type uq} {X : Type ux} {Y : Type uy}

/-- The sub-history a routed composite history sends to the left component. -/
def leftHistory (history : List ((P ⊕ Q) × X)) : List (P × X) :=
  history.filterMap fun entry =>
    match entry.1 with
    | Sum.inl left => some (left, entry.2)
    | Sum.inr _ => none

/-- The sub-history a routed composite history sends to the right component. -/
def rightHistory (history : List ((P ⊕ Q) × X)) : List (Q × X) :=
  history.filterMap fun entry =>
    match entry.1 with
    | Sum.inl _ => none
    | Sum.inr right => some (right, entry.2)

@[simp]
theorem leftHistory_append (first second : List ((P ⊕ Q) × X)) :
    leftHistory (first ++ second) = leftHistory first ++ leftHistory second :=
  List.filterMap_append

@[simp]
theorem rightHistory_append (first second : List ((P ⊕ Q) × X)) :
    rightHistory (first ++ second) = rightHistory first ++ rightHistory second :=
  List.filterMap_append

@[simp]
theorem leftHistory_cons_inl (interface : P) (value : X)
    (rest : List ((P ⊕ Q) × X)) :
    leftHistory ((Sum.inl interface, value) :: rest) =
      (interface, value) :: leftHistory rest :=
  rfl

@[simp]
theorem leftHistory_cons_inr (interface : Q) (value : X)
    (rest : List ((P ⊕ Q) × X)) :
    leftHistory ((Sum.inr interface, value) :: rest) = leftHistory rest :=
  rfl

@[simp]
theorem rightHistory_cons_inl (interface : P) (value : X)
    (rest : List ((P ⊕ Q) × X)) :
    rightHistory ((Sum.inl interface, value) :: rest) = rightHistory rest :=
  rfl

@[simp]
theorem rightHistory_cons_inr (interface : Q) (value : X)
    (rest : List ((P ⊕ Q) × X)) :
    rightHistory ((Sum.inr interface, value) :: rest) =
      (interface, value) :: rightHistory rest :=
  rfl

@[simp]
theorem leftHistory_inl (interface : P) (value : X) :
    leftHistory [((Sum.inl interface : P ⊕ Q), value)] = [(interface, value)] :=
  rfl

@[simp]
theorem leftHistory_inr (interface : Q) (value : X) :
    leftHistory [((Sum.inr interface : P ⊕ Q), value)] = ([] : List (P × X)) :=
  rfl

@[simp]
theorem rightHistory_inl (interface : P) (value : X) :
    rightHistory [((Sum.inl interface : P ⊕ Q), value)] = ([] : List (Q × X)) :=
  rfl

@[simp]
theorem rightHistory_inr (interface : Q) (value : X) :
    rightHistory [((Sum.inr interface : P ⊕ Q), value)] = [(interface, value)] :=
  rfl

@[simp]
theorem leftHistory_nil : leftHistory ([] : List ((P ⊕ Q) × X)) = [] := rfl

@[simp]
theorem rightHistory_nil : rightHistory ([] : List ((P ⊕ Q) × X)) = [] := rfl

/-- Membership in the left sub-history is left-tagged membership. -/
theorem mem_leftHistory_iff (history : List ((P ⊕ Q) × X)) (entry : P × X) :
    entry ∈ leftHistory history ↔
      ((Sum.inl entry.1 : P ⊕ Q), entry.2) ∈ history := by
  induction history with
  | nil => simp
  | cons head rest induction =>
      obtain ⟨interface, value⟩ := head
      cases interface with
      | inl _ => simp [induction, Prod.ext_iff]
      | inr _ => simp [induction]

/-- Membership in the right sub-history is right-tagged membership. -/
theorem mem_rightHistory_iff (history : List ((P ⊕ Q) × X)) (entry : Q × X) :
    entry ∈ rightHistory history ↔
      ((Sum.inr entry.1 : P ⊕ Q), entry.2) ∈ history := by
  induction history with
  | nil => simp
  | cons head rest induction =>
      obtain ⟨interface, value⟩ := head
      cases interface with
      | inl _ => simp [induction]
      | inr _ => simp [induction, Prod.ext_iff]

/-- **Jost's `[R, S]` on the uniform interface chart**: two resources side by
side at the *disjoint union* of their interface sets.  Each query is routed to
the component owning its interface tag, which answers on the sub-history of
its own inputs. -/
noncomputable def routedPar (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) : PFunDDS.Resource (P ⊕ Q) X Y :=
  ⟨fun history =>
    Part.assert (leftHistory history ≠ [] → (s.1 (leftHistory history)).Dom)
      fun _ =>
        Part.assert
          (rightHistory history ≠ [] → (t.1 (rightHistory history)).Dom)
          fun _ =>
            match history.getLast? with
            | some (Sum.inl _, _) => s.1 (leftHistory history)
            | some (Sum.inr _, _) => t.1 (rightHistory history)
            | none => Part.none, by
    constructor
    · rintro ⟨leftGuard, rightGuard, absurdity⟩
      exact absurdity
    · intro shorter longer hprefix nonempty hdom
      obtain ⟨leftDom, rightDom, -⟩ := hdom
      obtain ⟨extra, rfl⟩ := hprefix
      have shorterLeft : leftHistory shorter ≠ [] →
          (s.1 (leftHistory shorter)).Dom := by
        intro subNonempty
        have subPrefix : leftHistory shorter <+: leftHistory (shorter ++ extra) :=
          ⟨leftHistory extra, (leftHistory_append shorter extra).symm⟩
        by_cases wholeEmpty : leftHistory (shorter ++ extra) = []
        · rw [wholeEmpty] at subPrefix
          exact absurd (List.prefix_nil.mp subPrefix) subNonempty
        · exact PFunDDS.prefix_closed s subPrefix subNonempty (leftDom wholeEmpty)
      have shorterRight : rightHistory shorter ≠ [] →
          (t.1 (rightHistory shorter)).Dom := by
        intro subNonempty
        have subPrefix :
            rightHistory shorter <+: rightHistory (shorter ++ extra) :=
          ⟨rightHistory extra, (rightHistory_append shorter extra).symm⟩
        by_cases wholeEmpty : rightHistory (shorter ++ extra) = []
        · rw [wholeEmpty] at subPrefix
          exact absurd (List.prefix_nil.mp subPrefix) subNonempty
        · exact PFunDDS.prefix_closed t subPrefix subNonempty
            (rightDom wholeEmpty)
      refine ⟨shorterLeft, shorterRight, ?_⟩
      cases lastCase : shorter.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp lastCase) nonempty
      | some entry =>
          have lastValue : shorter.getLast nonempty = entry := by
            rw [List.getLast?_eq_some_getLast nonempty] at lastCase
            exact Option.some.inj lastCase
          obtain ⟨interface, value⟩ := entry
          cases interface with
          | inl leftInterface =>
              have contains : ((Sum.inl leftInterface : P ⊕ Q), value) ∈ shorter :=
                lastValue ▸ List.getLast_mem nonempty
              exact shorterLeft
                (List.ne_nil_of_mem
                  ((mem_leftHistory_iff shorter (leftInterface, value)).mpr contains))
          | inr rightInterface =>
              have contains : ((Sum.inr rightInterface : P ⊕ Q), value) ∈ shorter :=
                lastValue ▸ List.getLast_mem nonempty
              exact shorterRight
                (List.ne_nil_of_mem
                  ((mem_rightHistory_iff shorter (rightInterface, value)).mpr
                    contains))⟩

/-- Membership in the routed parallel with its two sub-history guards made
explicit. -/
theorem mem_routedPar_iff (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (history : List ((P ⊕ Q) × X)) (value : Y) :
    value ∈ (routedPar s t).1 history ↔
      (leftHistory history ≠ [] → (s.1 (leftHistory history)).Dom) ∧
      (rightHistory history ≠ [] → (t.1 (rightHistory history)).Dom) ∧
      value ∈ (match history.getLast? with
        | some (Sum.inl _, _) => s.1 (leftHistory history)
        | some (Sum.inr _, _) => t.1 (rightHistory history)
        | none => Part.none) := by
  show value ∈ Part.assert _ _ ↔ _
  rw [Part.mem_assert_iff]
  constructor
  · rintro ⟨hleft, hmem⟩
    rw [Part.mem_assert_iff] at hmem
    obtain ⟨hright, hmem⟩ := hmem
    exact ⟨hleft, hright, hmem⟩
  · rintro ⟨hleft, hright, hmem⟩
    exact ⟨hleft, Part.mem_assert_iff.mpr ⟨hright, hmem⟩⟩

/-- Value of the routed parallel on a history whose last entry is left-tagged:
the left component's own answer, guarded by the right sub-history's domain. -/
theorem routedPar_apply_inl (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (history : List ((P ⊕ Q) × X))
    (interface : P) (value : X)
    (rightDom : rightHistory history ∈ PFunDDS.dom t ∨ rightHistory history = [])
    (last : history.getLast? = some (Sum.inl interface, value)) :
    (routedPar s t).1 history = s.1 (leftHistory history) := by
  apply Part.ext
  intro answer
  rw [mem_routedPar_iff, last]
  constructor
  · rintro ⟨-, -, hmem⟩
    exact hmem
  · intro hmem
    refine ⟨fun _ => Part.dom_iff_mem.mpr ⟨answer, hmem⟩, ?_, hmem⟩
    intro nonempty
    rcases rightDom with inDom | empty
    · exact inDom
    · exact absurd empty nonempty

/-- Value of the routed parallel on a history whose last entry is
right-tagged. -/
theorem routedPar_apply_inr (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (history : List ((P ⊕ Q) × X))
    (interface : Q) (value : X)
    (leftDom : leftHistory history ∈ PFunDDS.dom s ∨ leftHistory history = [])
    (last : history.getLast? = some (Sum.inr interface, value)) :
    (routedPar s t).1 history = t.1 (rightHistory history) := by
  apply Part.ext
  intro answer
  rw [mem_routedPar_iff, last]
  constructor
  · rintro ⟨-, -, hmem⟩
    exact hmem
  · intro hmem
    refine ⟨?_, fun _ => Part.dom_iff_mem.mpr ⟨answer, hmem⟩, hmem⟩
    intro nonempty
    rcases leftDom with inDom | empty
    · exact inDom
    · exact absurd empty nonempty

/-! ### The routed parallel is transparent to a converter attached on the left

Everything below establishes CR18 Definition 3.13 compatibility of `attachAt`
with `routedPar`: attaching a converter at a left-tagged interface neither sees
nor disturbs the right component. -/

/-- The two sub-history domain guards are exactly what it takes for a composite
history to be a legal input of the routed parallel; this is the form
`PFunDDS.fullyDefined` (CR18 Definition 3.3) needs in order to read the routed
parallel without a deletion pass. -/
theorem routedPar_dom_or_nil (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (history : List ((P ⊕ Q) × X))
    (leftDom : leftHistory history ∈ PFunDDS.dom s ∨ leftHistory history = [])
    (rightDom : rightHistory history ∈ PFunDDS.dom t ∨ rightHistory history = []) :
    history ∈ PFunDDS.dom (routedPar s t) ∨ history = [] := by
  rcases List.eq_nil_or_concat history with rfl | ⟨front, entry, rfl⟩
  · exact Or.inr rfl
  · left
    rw [List.concat_eq_append] at leftDom rightDom ⊢
    obtain ⟨tag, value⟩ := entry
    have hlast : (front ++ [((tag : P ⊕ Q), value)]).getLast? = some (tag, value) := by
      simp
    cases tag with
    | inl left =>
        have hne : leftHistory (front ++ [((Sum.inl left : P ⊕ Q), value)]) ≠ [] := by
          simp
        have hdom :
            (s.1 (leftHistory (front ++ [((Sum.inl left : P ⊕ Q), value)]))).Dom :=
          leftDom.resolve_right hne
        obtain ⟨answer, hanswer⟩ := Part.dom_iff_mem.mp hdom
        show ((routedPar s t).1 _).Dom
        refine Part.dom_iff_mem.mpr ⟨answer, ?_⟩
        rw [mem_routedPar_iff, hlast]
        exact ⟨fun _ => hdom, fun hne' => rightDom.resolve_right hne', hanswer⟩
    | inr right =>
        have hne : rightHistory (front ++ [((Sum.inr right : P ⊕ Q), value)]) ≠ [] := by
          simp
        have hdom :
            (t.1 (rightHistory (front ++ [((Sum.inr right : P ⊕ Q), value)]))).Dom :=
          rightDom.resolve_right hne
        obtain ⟨answer, hanswer⟩ := Part.dom_iff_mem.mp hdom
        show ((routedPar s t).1 _).Dom
        refine Part.dom_iff_mem.mpr ⟨answer, ?_⟩
        rw [mem_routedPar_iff, hlast]
        exact ⟨fun hne' => leftDom.resolve_right hne', fun _ => hdom, hanswer⟩

/-- **Transparency of the routed parallel at a left query** (CR18 Definition 3.3
read on `routedPar`): a query at a left-tagged interface, asked after a history
whose two sub-histories are both legal, gets from the routed parallel exactly the
`⊥`-answer the left component alone gives on the left sub-history.  This is the
whole mathematical content of the attachment correspondence: the right component
contributes nothing to a left query. -/
theorem output_fullyDefined_routedPar_inl (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (base : List ((P ⊕ Q) × X)) (interface : P)
    (value : X)
    (leftDom : leftHistory base ∈ PFunDDS.dom s ∨ leftHistory base = [])
    (rightDom : rightHistory base ∈ PFunDDS.dom t ∨ rightHistory base = []) :
    PFunDDS.output (PFunDDS.fullyDefined (routedPar s t))
        (base ++ [((Sum.inl interface : P ⊕ Q), value)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      PFunDDS.output (PFunDDS.fullyDefined s)
        (leftHistory base ++ [(interface, value)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) := by
  have hlast :
      (base ++ [((Sum.inl interface : P ⊕ Q), value)]).getLast? =
        some (Sum.inl interface, value) := by simp
  have hright :
      rightHistory (base ++ [((Sum.inl interface : P ⊕ Q), value)]) =
        rightHistory base := by simp
  have hleft :
      leftHistory (base ++ [((Sum.inl interface : P ⊕ Q), value)]) =
        leftHistory base ++ [(interface, value)] := by simp
  have hpt : (routedPar s t).1 (base ++ [((Sum.inl interface : P ⊕ Q), value)]) =
      s.1 (leftHistory base ++ [(interface, value)]) := by
    rw [routedPar_apply_inl s t _ interface value (by rw [hright]; exact rightDom) hlast,
      hleft]
  have hbaseDom : base ∈ PFunDDS.dom (routedPar s t) ∨ base = [] :=
    routedPar_dom_or_nil s t base leftDom rightDom
  by_cases hmem : leftHistory base ++ [(interface, value)] ∈ PFunDDS.dom s
  · have hmemC : base ++ [((Sum.inl interface : P ⊕ Q), value)] ∈
        PFunDDS.dom (routedPar s t) := by
      show ((routedPar s t).1 (base ++ [(Sum.inl interface, value)])).Dom
      rw [hpt]; exact hmem
    rw [PFunDDS.output_fullyDefined_append_of_mem (routedPar s t) base
        (Sum.inl interface, value) hbaseDom hmemC,
      PFunDDS.output_fullyDefined_append_of_mem s (leftHistory base)
        (interface, value) leftDom hmem]
    congr 1
    have hv1 : PFunDDS.output (routedPar s t)
        (base ++ [((Sum.inl interface : P ⊕ Q), value)]) hmemC ∈
        (routedPar s t).1 (base ++ [((Sum.inl interface : P ⊕ Q), value)]) :=
      Part.get_mem _
    have hv2 : PFunDDS.output s (leftHistory base ++ [(interface, value)]) hmem ∈
        s.1 (leftHistory base ++ [(interface, value)]) := Part.get_mem _
    rw [hpt] at hv1
    exact Part.mem_unique hv1 hv2
  · have hmemC_not : base ++ [((Sum.inl interface : P ⊕ Q), value)] ∉
        PFunDDS.dom (routedPar s t) := by
      show ¬ ((routedPar s t).1 (base ++ [(Sum.inl interface, value)])).Dom
      rw [hpt]; exact hmem
    have hnoneR : PFunDDS.output (PFunDDS.fullyDefined s)
        (leftHistory base ++ [(interface, value)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      rcases Option.eq_none_or_eq_some
          (PFunDDS.output (PFunDDS.fullyDefined s)
            (leftHistory base ++ [(interface, value)])
            (by rw [PFunDDS.dom_fullyDefined]; simp)) with h | ⟨answer, hanswer⟩
      · exact h
      · obtain ⟨hmem', -⟩ :=
          PFunDDS.mem_of_output_fullyDefined_append_eq_some s (leftHistory base)
            (interface, value) leftDom hanswer
        exact absurd hmem' hmem
    have hnoneL : PFunDDS.output (PFunDDS.fullyDefined (routedPar s t))
        (base ++ [((Sum.inl interface : P ⊕ Q), value)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      rcases Option.eq_none_or_eq_some
          (PFunDDS.output (PFunDDS.fullyDefined (routedPar s t))
            (base ++ [((Sum.inl interface : P ⊕ Q), value)])
            (by rw [PFunDDS.dom_fullyDefined]; simp)) with h | ⟨answer, hanswer⟩
      · exact h
      · obtain ⟨hmem', -⟩ :=
          PFunDDS.mem_of_output_fullyDefined_append_eq_some (routedPar s t) base
            (Sum.inl interface, value) hbaseDom hanswer
        exact absurd hmem' hmemC_not
    rw [hnoneL, hnoneR]

open DDC

/-- The bisimulation relation behind the left-attachment correspondence: the two
converter histories agree, the left sub-history of the composite recorded history
is the recorded history of the left component alone, the right sub-history is a
*fixed* list (a left-tagged round never touches the right component), and both
sub-histories are legal inputs of their own components. -/
def RelPar (s : PFunDDS.Resource P X Y) (t : PFunDDS.Resource Q X Y)
    (right : List (Q × X))
    (composite : List (CIn X Y) × List ((P ⊕ Q) × X))
    (plain : List (CIn X Y) × List (P × X)) : Prop :=
  composite.1 = plain.1 ∧
    leftHistory composite.2 = plain.2 ∧
    rightHistory composite.2 = right ∧
    (plain.2 ∈ PFunDDS.dom s ∨ plain.2 = []) ∧
    (right ∈ PFunDDS.dom t ∨ right = [])

/-- The single step of the bisimulation, written once and used in *both*
directions: from `RelPar`-related states one inner query `query` of the converter
drives the composite side and the left-component side to `RelPar`-related
successors.  The only mathematical content is
`output_fullyDefined_routedPar_inl`. -/
theorem routedPar_step_rel (interface : P) (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (right : List (Q × X))
    {composite : List (CIn X Y) × List ((P ⊕ Q) × X)}
    {plain : List (CIn X Y) × List (P × X)}
    (hRel : RelPar s t right composite plain) (query : X) :
    RelPar s t right
      (composite.1 ++ [Sum.inr (InLabel.inside,
          PFunDDS.output (PFunDDS.fullyDefined (routedPar s t))
            (composite.2 ++ [((Sum.inl interface : P ⊕ Q), query)])
            (by rw [PFunDDS.dom_fullyDefined]; simp))],
        match PFunDDS.output (PFunDDS.fullyDefined (routedPar s t))
            (composite.2 ++ [((Sum.inl interface : P ⊕ Q), query)])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with
          | some _ => composite.2 ++ [((Sum.inl interface : P ⊕ Q), query)]
          | none => composite.2)
      (plain.1 ++ [Sum.inr (InLabel.inside,
          PFunDDS.output (PFunDDS.fullyDefined s) (plain.2 ++ [(interface, query)])
            (by rw [PFunDDS.dom_fullyDefined]; simp))],
        match PFunDDS.output (PFunDDS.fullyDefined s) (plain.2 ++ [(interface, query)])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with
          | some _ => plain.2 ++ [(interface, query)]
          | none => plain.2) := by
  obtain ⟨hconv, hleft, hright, hleftDom, hrightDom⟩ := hRel
  have htrans :
      PFunDDS.output (PFunDDS.fullyDefined (routedPar s t))
          (composite.2 ++ [((Sum.inl interface : P ⊕ Q), query)])
          (by rw [PFunDDS.dom_fullyDefined]; simp) =
        PFunDDS.output (PFunDDS.fullyDefined s) (plain.2 ++ [(interface, query)])
          (by rw [PFunDDS.dom_fullyDefined]; simp) :=
    (output_fullyDefined_routedPar_inl s t composite.2 interface query
        (by rw [hleft]; exact hleftDom) (by rw [hright]; exact hrightDom)).trans
      (PFunDDS.output_congr _ (by rw [hleft]) _ _)
  rcases Option.eq_none_or_eq_some
      (PFunDDS.output (PFunDDS.fullyDefined s) (plain.2 ++ [(interface, query)])
        (by rw [PFunDDS.dom_fullyDefined]; simp)) with hnone | ⟨answer, hanswer⟩
  · rw [htrans, hnone]
    exact ⟨by rw [hconv], hleft, hright, hleftDom, hrightDom⟩
  · rw [htrans, hanswer]
    refine ⟨by rw [hconv], by simp [hleft], by simp [hright], ?_, hrightDom⟩
    exact Or.inl (PFunDDS.mem_of_output_fullyDefined_append_eq_some s plain.2
      (interface, query) hleftDom hanswer).choose

/-- Forward half of the resolve correspondence: one round of `converter` at the
left-tagged interface `Sum.inl interface` against the routed parallel is mirrored,
step for step, by one round at `interface` against the left component alone — same
outside answer, same converter history, the composite recorded history projecting
to the left one, and the right sub-history untouched. -/
theorem attachResolve_routedPar_fwd (interface : P) (converter : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (t : PFunDDS.Resource Q X Y)
    {conv : List (CIn X Y)} {base : List ((P ⊕ Q) × X)}
    (leftDom : leftHistory base ∈ PFunDDS.dom s ∨ leftHistory base = [])
    (rightDom : rightHistory base ∈ PFunDDS.dom t ∨ rightHistory base = [])
    {answer : Y} {conv' : List (CIn X Y)} {base' : List ((P ⊕ Q) × X)}
    (hmem : (answer, (conv', base')) ∈
      attachResolve (Sum.inl interface) converter (routedPar s t) (conv, base)) :
    (answer, (conv', leftHistory base')) ∈
        attachResolve interface converter s (conv, leftHistory base) ∧
      rightHistory base' = rightHistory base := by
  have hstop : ∀ a a', RelPar s t (rightHistory base) a a' → ∀ b,
      Sum.inl b ∈ attachStep (Sum.inl interface) converter (routedPar s t) a →
      ∃ b', Sum.inl b' ∈ attachStep interface converter s a' ∧
        b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧ leftHistory b.2.2 = b'.2.2 ∧
          rightHistory b.2.2 = rightHistory base := by
    rintro a a' ⟨hconv, hleft, hright, -, -⟩ b hb
    rw [attachStep_mem_inl] at hb
    obtain ⟨hout, hbeq⟩ := hb
    exact ⟨(b.1, a'), by rw [attachStep_mem_inl]; exact ⟨hconv ▸ hout, rfl⟩, rfl,
      by rw [hbeq]; exact hconv, by rw [hbeq]; exact hleft,
      by rw [hbeq]; exact hright⟩
  have hstep : ∀ a a', RelPar s t (rightHistory base) a a' → ∀ a₁,
      Sum.inr a₁ ∈ attachStep (Sum.inl interface) converter (routedPar s t) a →
      ∃ a₁', Sum.inr a₁' ∈ attachStep interface converter s a' ∧
        RelPar s t (rightHistory base) a₁ a₁' := by
    rintro a a' hRel a₁ ha₁
    have hconv : a.1 = a'.1 := hRel.1
    rw [attachStep_mem_inr] at ha₁
    obtain ⟨query, hquery, rfl⟩ := ha₁
    exact ⟨_, by rw [attachStep_mem_inr]; exact ⟨query, hconv ▸ hquery, rfl⟩,
      routedPar_step_rel interface s t (rightHistory base) hRel query⟩
  obtain ⟨⟨mirrorAnswer, mirrorConv, mirrorBase⟩, hmirror, hy, hc, hl, hr⟩ :=
    PFun.fix_bisim hstop hstep hmem (conv, leftHistory base)
      ⟨rfl, rfl, rfl, leftDom, rightDom⟩
  obtain rfl := hy; obtain rfl := hc; obtain rfl := hl
  exact ⟨hmirror, hr⟩

/-- Backward half of the resolve correspondence: every round of `converter` at
`interface` against the left component alone is realized by a round at
`Sum.inl interface` against the routed parallel, on a composite recorded history
that projects back to it and leaves the right sub-history alone. -/
theorem attachResolve_routedPar_bwd (interface : P) (converter : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (t : PFunDDS.Resource Q X Y)
    {conv : List (CIn X Y)} {base : List ((P ⊕ Q) × X)}
    (leftDom : leftHistory base ∈ PFunDDS.dom s ∨ leftHistory base = [])
    (rightDom : rightHistory base ∈ PFunDDS.dom t ∨ rightHistory base = [])
    {answer : Y} {conv' : List (CIn X Y)} {plain' : List (P × X)}
    (hmem : (answer, (conv', plain')) ∈
      attachResolve interface converter s (conv, leftHistory base)) :
    ∃ base', (answer, (conv', base')) ∈
        attachResolve (Sum.inl interface) converter (routedPar s t) (conv, base) ∧
      leftHistory base' = plain' ∧ rightHistory base' = rightHistory base := by
  have hstop : ∀ a a', RelPar s t (rightHistory base) a' a → ∀ b,
      Sum.inl b ∈ attachStep interface converter s a →
      ∃ b', Sum.inl b' ∈
          attachStep (Sum.inl interface) converter (routedPar s t) a' ∧
        b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧ leftHistory b'.2.2 = b.2.2 ∧
          rightHistory b'.2.2 = rightHistory base := by
    rintro a a' ⟨hconv, hleft, hright, -, -⟩ b hb
    rw [attachStep_mem_inl] at hb
    obtain ⟨hout, hbeq⟩ := hb
    exact ⟨(b.1, a'), by rw [attachStep_mem_inl]; exact ⟨by rw [hconv]; exact hout, rfl⟩,
      rfl, by rw [hbeq]; exact hconv.symm, by rw [hbeq]; exact hleft, hright⟩
  have hstep : ∀ a a', RelPar s t (rightHistory base) a' a → ∀ a₁,
      Sum.inr a₁ ∈ attachStep interface converter s a →
      ∃ a₁', Sum.inr a₁' ∈
          attachStep (Sum.inl interface) converter (routedPar s t) a' ∧
        RelPar s t (rightHistory base) a₁' a₁ := by
    rintro a a' hRel a₁ ha₁
    have hconv : a'.1 = a.1 := hRel.1
    rw [attachStep_mem_inr] at ha₁
    obtain ⟨query, hquery, rfl⟩ := ha₁
    exact ⟨_, by rw [attachStep_mem_inr]; exact ⟨query, hconv ▸ hquery, rfl⟩,
      routedPar_step_rel interface s t (rightHistory base) hRel query⟩
  obtain ⟨⟨mirrorAnswer, mirrorConv, mirrorBase⟩, hmirror, hy, hc, hl, hr⟩ :=
    PFun.fix_bisim hstop hstep hmem (conv, base) ⟨rfl, rfl, rfl, leftDom, rightDom⟩
  obtain rfl := hy; obtain rfl := hc
  exact ⟨mirrorBase, hmirror, hl, hr⟩
/-- **Forward drive correspondence.**  Driving `converter`, attached at the
left-tagged interface `Sum.inl interface`, through a composite outside history is
mirrored by driving it at `interface` through the left component alone on the
left sub-history: the converter history agrees, the composite recorded history
projects onto the left recorded history, and its right sub-history is exactly the
right sub-history of everything seen so far — the converter never touches the
right component. -/
theorem attachDrive_routedPar_fwd [DecidableEq P] [DecidableEq Q] (interface : P)
    (converter : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (t : PFunDDS.Resource Q X Y)
    (outer : List ((P ⊕ Q) × X)) :
    ∀ {conv : List (CIn X Y)} {base : List ((P ⊕ Q) × X)},
      (leftHistory base ∈ PFunDDS.dom s ∨ leftHistory base = []) →
      (rightHistory base ∈ PFunDDS.dom t ∨ rightHistory base = []) →
      ∀ {result : List Y × (List (CIn X Y) × List ((P ⊕ Q) × X))},
        result ∈ attachDrive (Sum.inl interface) converter (routedPar s t)
          (conv, base) outer →
        (∃ outputs, (outputs, (result.2.1, leftHistory result.2.2)) ∈
            attachDrive interface converter s (conv, leftHistory base)
              (leftHistory outer)) ∧
          rightHistory result.2.2 = rightHistory (base ++ outer) ∧
          (rightHistory (base ++ outer) ∈ PFunDDS.dom t ∨
            rightHistory (base ++ outer) = []) := by
  induction outer with
  | nil =>
      intro conv base hleft hright result hmem
      simp only [attachDrive, Part.mem_some_iff] at hmem
      subst hmem
      exact ⟨⟨[], by simp [attachDrive, leftHistory]⟩, by simp, by simpa using hright⟩
  | cons entry rest ih =>
      intro conv base hleft hright result hmem
      simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff] at hmem
      obtain ⟨step, hstep, tail, htail, rfl⟩ := hmem
      obtain ⟨tag, value⟩ := entry
      cases tag with
      | inl left =>
          by_cases hleq : left = interface
          · rw [hleq] at hstep ⊢
            obtain ⟨stepAnswer, stepConv, stepBase⟩ := step
            have hentry : attachEntryStep (Sum.inl interface) converter (routedPar s t)
                (conv, base) ((Sum.inl interface : P ⊕ Q), value) =
                  attachResolve (Sum.inl interface) converter (routedPar s t)
                    (conv ++ [Sum.inl (InLabel.outside, value)], base) := by
              simp [attachEntryStep]
            rw [hentry] at hstep
            obtain ⟨hres, hstepRight⟩ :=
              attachResolve_routedPar_fwd interface converter s t hleft hright hstep
            have hstepLeftDom :
                leftHistory stepBase ∈ PFunDDS.dom s ∨ leftHistory stepBase = [] :=
              attachResolve_base_dom interface converter s
                (st := (conv ++ [Sum.inl (InLabel.outside, value)], leftHistory base))
                hleft hres
            have hstepRightDom :
                rightHistory stepBase ∈ PFunDDS.dom t ∨ rightHistory stepBase = [] := by
              rw [hstepRight]; exact hright
            obtain ⟨⟨outputs, htailDrive⟩, htailRight, htailDom⟩ :=
              ih hstepLeftDom hstepRightDom htail
            have hplain : attachEntryStep interface converter s (conv, leftHistory base)
                (interface, value) =
                  attachResolve interface converter s
                    (conv ++ [Sum.inl (InLabel.outside, value)], leftHistory base) := by
              simp [attachEntryStep]
            refine ⟨⟨stepAnswer :: outputs, ?_⟩, ?_, ?_⟩
            · simp only [leftHistory_cons_inl, attachDrive, Part.mem_bind_iff,
                Part.mem_map_iff]
              exact ⟨(stepAnswer, (stepConv, leftHistory stepBase)),
                by rw [hplain]; exact hres,
                (outputs, ((tail.2.1, leftHistory tail.2.2))), htailDrive, rfl⟩
            · rw [htailRight]; simp [hstepRight]
            · simpa [hstepRight] using htailDom
          · have hentry : attachEntryStep (Sum.inl interface) converter (routedPar s t)
                (conv, base) ((Sum.inl left : P ⊕ Q), value) =
                  ((routedPar s t).1 (base ++ [((Sum.inl left : P ⊕ Q), value)])).map
                    fun answer => (answer, (conv, base ++ [((Sum.inl left : P ⊕ Q), value)])) := by
              simp [attachEntryStep, hleq]
            have hvalue : (routedPar s t).1 (base ++ [((Sum.inl left : P ⊕ Q), value)]) =
                s.1 (leftHistory base ++ [(left, value)]) := by
              rw [routedPar_apply_inl s t _ left value (by simpa using hright) (by simp)]
              simp
            rw [hentry, hvalue, Part.mem_map_iff] at hstep
            obtain ⟨answer, hanswer, rfl⟩ := hstep
            have hleft' :
                leftHistory (base ++ [((Sum.inl left : P ⊕ Q), value)]) ∈ PFunDDS.dom s ∨
                  leftHistory (base ++ [((Sum.inl left : P ⊕ Q), value)]) = [] := by
              refine Or.inl ?_
              simp only [leftHistory_append, leftHistory_inl]
              rw [PFunDDS.dom_def, PFun.mem_dom]
              exact ⟨answer, hanswer⟩
            have hright' :
                rightHistory (base ++ [((Sum.inl left : P ⊕ Q), value)]) ∈ PFunDDS.dom t ∨
                  rightHistory (base ++ [((Sum.inl left : P ⊕ Q), value)]) = [] := by
              simpa using hright
            obtain ⟨⟨outputs, htailDrive⟩, htailRight, htailDom⟩ :=
              ih hleft' hright' htail
            have hplain : attachEntryStep interface converter s (conv, leftHistory base)
                (left, value) =
                  (s.1 (leftHistory base ++ [(left, value)])).map
                    fun answer => (answer, (conv, leftHistory base ++ [(left, value)])) := by
              simp [attachEntryStep, hleq]
            refine ⟨⟨answer :: outputs, ?_⟩, ?_, ?_⟩
            · simp only [leftHistory_cons_inl, attachDrive, Part.mem_bind_iff,
                Part.mem_map_iff]
              refine ⟨(answer, (conv, leftHistory base ++ [(left, value)])),
                by rw [hplain]; exact Part.mem_map _ hanswer,
                (outputs, ((tail.2.1, leftHistory tail.2.2))), ?_, rfl⟩
              simpa using htailDrive
            · rw [htailRight]; simp
            · simpa using htailDom
      | inr right =>
          have hentry : attachEntryStep (Sum.inl interface) converter (routedPar s t)
              (conv, base) ((Sum.inr right : P ⊕ Q), value) =
                ((routedPar s t).1 (base ++ [((Sum.inr right : P ⊕ Q), value)])).map
                  fun answer => (answer, (conv, base ++ [((Sum.inr right : P ⊕ Q), value)])) := by
            simp [attachEntryStep]
          have hvalue : (routedPar s t).1 (base ++ [((Sum.inr right : P ⊕ Q), value)]) =
              t.1 (rightHistory base ++ [(right, value)]) := by
            rw [routedPar_apply_inr s t _ right value (by simpa using hleft) (by simp)]
            simp
          rw [hentry, hvalue, Part.mem_map_iff] at hstep
          obtain ⟨answer, hanswer, rfl⟩ := hstep
          have hleft' :
              leftHistory (base ++ [((Sum.inr right : P ⊕ Q), value)]) ∈ PFunDDS.dom s ∨
                leftHistory (base ++ [((Sum.inr right : P ⊕ Q), value)]) = [] := by
            simpa using hleft
          have hright' :
              rightHistory (base ++ [((Sum.inr right : P ⊕ Q), value)]) ∈ PFunDDS.dom t ∨
                rightHistory (base ++ [((Sum.inr right : P ⊕ Q), value)]) = [] := by
            refine Or.inl ?_
            simp only [rightHistory_append, rightHistory_inr]
            rw [PFunDDS.dom_def, PFun.mem_dom]
            exact ⟨answer, hanswer⟩
          obtain ⟨⟨outputs, htailDrive⟩, htailRight, htailDom⟩ := ih hleft' hright' htail
          refine ⟨⟨outputs, ?_⟩, ?_, ?_⟩
          · simpa using htailDrive
          · rw [htailRight]; simp
          · simpa using htailDom

/-- **Backward drive correspondence.**  Every run of `converter` at `interface`
through the left component alone is realized by a run at `Sum.inl interface`
through the routed parallel — provided the right sub-history of the composite
outside history is a legal input of the right component, which is exactly what
the right-tagged queries of that history need in order to be answered. -/
theorem attachDrive_routedPar_bwd [DecidableEq P] [DecidableEq Q] (interface : P)
    (converter : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (t : PFunDDS.Resource Q X Y)
    (outer : List ((P ⊕ Q) × X)) :
    ∀ {conv : List (CIn X Y)} {base : List ((P ⊕ Q) × X)},
      (leftHistory base ∈ PFunDDS.dom s ∨ leftHistory base = []) →
      (rightHistory base ∈ PFunDDS.dom t ∨ rightHistory base = []) →
      (rightHistory (base ++ outer) ∈ PFunDDS.dom t ∨
        rightHistory (base ++ outer) = []) →
      ∀ {result : List Y × (List (CIn X Y) × List (P × X))},
        result ∈ attachDrive interface converter s (conv, leftHistory base)
          (leftHistory outer) →
        ∃ outputs composite,
          (outputs, (result.2.1, composite)) ∈
              attachDrive (Sum.inl interface) converter (routedPar s t)
                (conv, base) outer ∧
            leftHistory composite = result.2.2 ∧
            rightHistory composite = rightHistory (base ++ outer) := by
  induction outer with
  | nil =>
      intro conv base _ _ _ result hmem
      simp only [leftHistory_nil, attachDrive, Part.mem_some_iff] at hmem
      subst hmem
      exact ⟨[], base, by simp [attachDrive], rfl, by simp⟩
  | cons entry rest ih =>
      intro conv base hleft hright hfinal result hmem
      obtain ⟨tag, value⟩ := entry
      cases tag with
      | inl left =>
          by_cases hleq : left = interface
          · rw [hleq] at hmem hfinal ⊢
            simp only [leftHistory_cons_inl, attachDrive, Part.mem_bind_iff,
              Part.mem_map_iff] at hmem
            obtain ⟨step, hstep, tail, htail, rfl⟩ := hmem
            obtain ⟨stepAnswer, stepConv, stepBase⟩ := step
            have hplain : attachEntryStep interface converter s (conv, leftHistory base)
                (interface, value) =
                  attachResolve interface converter s
                    (conv ++ [Sum.inl (InLabel.outside, value)], leftHistory base) := by
              simp [attachEntryStep]
            rw [hplain] at hstep
            have hstepLeftDom : stepBase ∈ PFunDDS.dom s ∨ stepBase = [] :=
              attachResolve_base_dom interface converter s
                (st := (conv ++ [Sum.inl (InLabel.outside, value)], leftHistory base))
                hleft hstep
            obtain ⟨stepComposite, hstepComposite, hstepLeft, hstepRight⟩ :=
              attachResolve_routedPar_bwd interface converter s t hleft hright hstep
            have hentry : attachEntryStep (Sum.inl interface) converter (routedPar s t)
                (conv, base) ((Sum.inl interface : P ⊕ Q), value) =
                  attachResolve (Sum.inl interface) converter (routedPar s t)
                    (conv ++ [Sum.inl (InLabel.outside, value)], base) := by
              simp [attachEntryStep]
            obtain ⟨outputs, composite, hdrive, hleftEq, hrightEq⟩ :=
              ih (conv := stepConv) (base := stepComposite)
                (by rw [hstepLeft]; exact hstepLeftDom)
                (by rw [hstepRight]; exact hright)
                (by simpa [hstepRight] using hfinal)
                (by rw [hstepLeft]; exact htail)
            refine ⟨stepAnswer :: outputs, composite, ?_, hleftEq, ?_⟩
            · simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff]
              exact ⟨(stepAnswer, (stepConv, stepComposite)),
                by rw [hentry]; exact hstepComposite,
                (outputs, (tail.2.1, composite)), hdrive, rfl⟩
            · rw [hrightEq]; simp [hstepRight]
          · simp only [leftHistory_cons_inl, attachDrive, Part.mem_bind_iff,
              Part.mem_map_iff] at hmem
            obtain ⟨step, hstep, tail, htail, rfl⟩ := hmem
            have hplain : attachEntryStep interface converter s (conv, leftHistory base)
                (left, value) =
                  (s.1 (leftHistory base ++ [(left, value)])).map
                    fun answer => (answer, (conv, leftHistory base ++ [(left, value)])) := by
              simp [attachEntryStep, hleq]
            rw [hplain, Part.mem_map_iff] at hstep
            obtain ⟨answer, hanswer, rfl⟩ := hstep
            have hentry : attachEntryStep (Sum.inl interface) converter (routedPar s t)
                (conv, base) ((Sum.inl left : P ⊕ Q), value) =
                  ((routedPar s t).1 (base ++ [((Sum.inl left : P ⊕ Q), value)])).map
                    fun answer =>
                      (answer, (conv, base ++ [((Sum.inl left : P ⊕ Q), value)])) := by
              simp [attachEntryStep, hleq]
            have hvalue : (routedPar s t).1 (base ++ [((Sum.inl left : P ⊕ Q), value)]) =
                s.1 (leftHistory base ++ [(left, value)]) := by
              rw [routedPar_apply_inl s t _ left value (by simpa using hright) (by simp)]
              simp
            have hleft' :
                leftHistory (base ++ [((Sum.inl left : P ⊕ Q), value)]) ∈ PFunDDS.dom s ∨
                  leftHistory (base ++ [((Sum.inl left : P ⊕ Q), value)]) = [] := by
              refine Or.inl ?_
              simp only [leftHistory_append, leftHistory_inl]
              rw [PFunDDS.dom_def, PFun.mem_dom]
              exact ⟨answer, hanswer⟩
            obtain ⟨outputs, composite, hdrive, hleftEq, hrightEq⟩ :=
              ih (conv := conv) (base := base ++ [((Sum.inl left : P ⊕ Q), value)])
                hleft' (by simpa using hright) (by simpa using hfinal)
                (by simpa using htail)
            refine ⟨answer :: outputs, composite, ?_, hleftEq, ?_⟩
            · simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff]
              exact ⟨(answer, (conv, base ++ [((Sum.inl left : P ⊕ Q), value)])),
                by rw [hentry, hvalue]; exact Part.mem_map _ hanswer,
                (outputs, (tail.2.1, composite)), hdrive, rfl⟩
            · rw [hrightEq]; simp
      | inr right =>
          simp only [leftHistory_cons_inr] at hmem
          have hrightMem : rightHistory base ++ [(right, value)] ∈ PFunDDS.dom t := by
            have hne : rightHistory (base ++ ((Sum.inr right : P ⊕ Q), value) :: rest) ≠ [] := by
              simp
            refine PFunDDS.prefix_closed t ?_ (by simp) (hfinal.resolve_right hne)
            exact ⟨rightHistory rest, by simp⟩
          obtain ⟨answer, hanswer⟩ := Part.dom_iff_mem.mp hrightMem
          have hentry : attachEntryStep (Sum.inl interface) converter (routedPar s t)
              (conv, base) ((Sum.inr right : P ⊕ Q), value) =
                ((routedPar s t).1 (base ++ [((Sum.inr right : P ⊕ Q), value)])).map
                  fun answer =>
                    (answer, (conv, base ++ [((Sum.inr right : P ⊕ Q), value)])) := by
            simp [attachEntryStep]
          have hvalue : (routedPar s t).1 (base ++ [((Sum.inr right : P ⊕ Q), value)]) =
              t.1 (rightHistory base ++ [(right, value)]) := by
            rw [routedPar_apply_inr s t _ right value (by simpa using hleft) (by simp)]
            simp
          obtain ⟨outputs, composite, hdrive, hleftEq, hrightEq⟩ :=
            ih (conv := conv) (base := base ++ [((Sum.inr right : P ⊕ Q), value)])
              (by simpa using hleft)
              (by simpa using hrightMem)
              (by simpa using hfinal)
              (by simpa using hmem)
          refine ⟨answer :: outputs, composite, ?_, hleftEq, ?_⟩
          · simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff]
            exact ⟨(answer, (conv, base ++ [((Sum.inr right : P ⊕ Q), value)])),
              by rw [hentry, hvalue]; exact Part.mem_map _ hanswer,
              (outputs, (result.2.1, composite)), hdrive, rfl⟩
          · rw [hrightEq]; simp

universe ui

/-- The applied resource read on a history with a last entry: drive the prefix,
then take the answer of that last entry's own step.  `attachRaw` keeps only the
last output of the drive and a one-entry suffix contributes exactly one output,
so the `getLast?` bookkeeping collapses. -/
theorem attachRaw_append_singleton {I : Type ui} [DecidableEq I] (interface : I)
    (converter : DDC X Y X Y) (resource : PFunDDS.Resource I X Y)
    (front : List (I × X)) (entry : I × X) :
    attachRaw interface converter resource (front ++ [entry]) =
      (attachDrive interface converter resource ([], []) front).bind fun state =>
        (attachEntryStep interface converter resource state.2 entry).map Prod.fst := by
  rw [attachRaw, attachDrive_append]
  simp [attachDrive, Part.bind_assoc, Part.bind_some_eq_map]

/-- CR18 Definition 3.13, entry rule at the converter's own interface: such an
entry starts a fresh round of the converter with the entry value delivered on the
outside label. -/
theorem attachEntryStep_self {I : Type ui} [DecidableEq I] (interface : I)
    (converter : DDC X Y X Y) (resource : PFunDDS.Resource I X Y)
    (state : List (CIn X Y) × List (I × X)) (value : X) :
    attachEntryStep interface converter resource state (interface, value) =
      attachResolve interface converter resource
        (state.1 ++ [Sum.inl (InLabel.outside, value)], state.2) := by
  simp [attachEntryStep]

/-- CR18 Definition 3.13, entry rule at any other interface: the entry passes
straight through, so its answer is the resource's own answer on the recorded
history extended by that entry. -/
theorem map_fst_attachEntryStep_of_ne {I : Type ui} [DecidableEq I] (interface : I)
    (converter : DDC X Y X Y) (resource : PFunDDS.Resource I X Y)
    (state : List (CIn X Y) × List (I × X)) (entry : I × X)
    (hne : entry.1 ≠ interface) :
    (attachEntryStep interface converter resource state entry).map Prod.fst =
      resource.1 (state.2 ++ [entry]) := by
  rw [attachEntryStep, if_neg hne, Part.map_map]
  exact Part.map_id' (fun _ => rfl) _

/-- Half of CR18 Definition 3.13 for `routedPar`: every answer of the routed
parallel with `converter` attached at a left-tagged interface is an answer of the
routed parallel whose left component carries the converter. -/
theorem mem_routedPar_attachAt_of_mem_attachRaw [DecidableEq P] [DecidableEq Q]
    (interface : P) (converter : DDC X Y X Y) (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (history : List ((P ⊕ Q) × X)) {answer : Y}
    (hmem : answer ∈ attachRaw (Sum.inl interface) converter (routedPar s t) history) :
    answer ∈ (routedPar (attachAt interface converter s) t).1 history := by
  rcases List.eq_nil_or_concat history with rfl | ⟨front, entry, rfl⟩
  · simp [attachRaw, attachDrive] at hmem
  · rw [List.concat_eq_append] at hmem ⊢
    rw [attachRaw_append_singleton, Part.mem_bind_iff] at hmem
    obtain ⟨state, hstate, hanswer⟩ := hmem
    obtain ⟨⟨outputs, hplainDrive⟩, hstateRight, hfrontRight⟩ :=
      attachDrive_routedPar_fwd interface converter s t front (Or.inr rfl) (Or.inr rfl)
        hstate
    simp only [leftHistory_nil] at hplainDrive
    simp only [List.nil_append] at hstateRight hfrontRight
    have hstateLeftDom :
        leftHistory state.2.2 ∈ PFunDDS.dom s ∨ leftHistory state.2.2 = [] :=
      attachDrive_base_dom interface converter s (leftHistory front) (Or.inr rfl)
        hplainDrive
    have hstateRightDom :
        rightHistory state.2.2 ∈ PFunDDS.dom t ∨ rightHistory state.2.2 = [] := by
      rw [hstateRight]; exact hfrontRight
    obtain ⟨tag, value⟩ := entry
    rw [mem_routedPar_iff,
      show (front ++ [((tag : P ⊕ Q), value)]).getLast? = some (tag, value) by simp]
    cases tag with
    | inl left =>
        have hbranch : answer ∈ (attachAt interface converter s).1
            (leftHistory (front ++ [((Sum.inl left : P ⊕ Q), value)])) := by
          rw [show leftHistory (front ++ [((Sum.inl left : P ⊕ Q), value)]) =
            leftHistory front ++ [(left, value)] by simp]
          show answer ∈ attachRaw interface converter s (leftHistory front ++ [(left, value)])
          rw [attachRaw_append_singleton, Part.mem_bind_iff]
          refine ⟨(outputs, (state.2.1, leftHistory state.2.2)), hplainDrive, ?_⟩
          by_cases hleq : left = interface
          · rw [hleq] at hanswer ⊢
            rw [attachEntryStep_self] at hanswer ⊢
            rw [Part.mem_map_iff] at hanswer ⊢
            obtain ⟨⟨resAnswer, resConv, resBase⟩, hres, hreseq⟩ := hanswer
            obtain ⟨hplainRes, -⟩ :=
              attachResolve_routedPar_fwd interface converter s t hstateLeftDom
                hstateRightDom hres
            exact ⟨(resAnswer, (resConv, leftHistory resBase)), hplainRes, hreseq⟩
          · rw [map_fst_attachEntryStep_of_ne _ _ _ _ _ (by simpa using hleq),
              routedPar_apply_inl s t _ left value (by simpa using hstateRightDom)
                (by simp)] at hanswer
            rw [map_fst_attachEntryStep_of_ne _ _ _ _ _ hleq]
            simpa using hanswer
        refine ⟨fun _ => Part.dom_iff_mem.mpr ⟨answer, hbranch⟩, ?_, hbranch⟩
        simp only [rightHistory_append, rightHistory_inl, List.append_nil]
        exact fun hne => hfrontRight.resolve_right hne
    | inr right =>
        have hbranch : answer ∈
            t.1 (rightHistory (front ++ [((Sum.inr right : P ⊕ Q), value)])) := by
          rw [map_fst_attachEntryStep_of_ne _ _ _ _ _ (by simp),
            routedPar_apply_inr s t _ right value (by simpa using hstateLeftDom)
              (by simp)] at hanswer
          simp only [rightHistory_append, rightHistory_inr] at hanswer ⊢
          rw [hstateRight] at hanswer
          exact hanswer
        refine ⟨?_, fun _ => Part.dom_iff_mem.mpr ⟨answer, hbranch⟩, hbranch⟩
        simp only [leftHistory_append, leftHistory_inr, List.append_nil]
        intro hne
        exact (attachAt_dom_or_nil interface converter s
          (Part.eq_some_iff.mpr hplainDrive)).resolve_right hne

/-- The other half of CR18 Definition 3.13 for `routedPar`: every answer of the
routed parallel whose left component carries the converter is an answer of the
routed parallel with the converter attached at the left-tagged interface.  The
two sub-history guards of `routedPar` are exactly what the composite drive needs:
a left-tagged last entry consumes the *right* guard, a right-tagged one the
*left* guard. -/
theorem mem_attachRaw_of_mem_routedPar_attachAt [DecidableEq P] [DecidableEq Q]
    (interface : P) (converter : DDC X Y X Y) (s : PFunDDS.Resource P X Y)
    (t : PFunDDS.Resource Q X Y) (history : List ((P ⊕ Q) × X)) {answer : Y}
    (hmem : answer ∈ (routedPar (attachAt interface converter s) t).1 history) :
    answer ∈ attachRaw (Sum.inl interface) converter (routedPar s t) history := by
  rcases List.eq_nil_or_concat history with rfl | ⟨front, entry, rfl⟩
  · simp [mem_routedPar_iff] at hmem
  · rw [List.concat_eq_append] at hmem ⊢
    obtain ⟨tag, value⟩ := entry
    rw [mem_routedPar_iff,
      show (front ++ [((tag : P ⊕ Q), value)]).getLast? = some (tag, value) by simp] at hmem
    obtain ⟨hleftGuard, hrightGuard, hbranch⟩ := hmem
    rw [attachRaw_append_singleton, Part.mem_bind_iff]
    cases tag with
    | inl left =>
        rw [show leftHistory (front ++ [((Sum.inl left : P ⊕ Q), value)]) =
          leftHistory front ++ [(left, value)] by simp] at hbranch
        change answer ∈
          attachRaw interface converter s (leftHistory front ++ [(left, value)]) at hbranch
        rw [attachRaw_append_singleton, Part.mem_bind_iff] at hbranch
        obtain ⟨plainState, hplainState, hplainAnswer⟩ := hbranch
        rw [show rightHistory (front ++ [((Sum.inl left : P ⊕ Q), value)]) =
          rightHistory front by simp] at hrightGuard
        have hfrontRight :
            rightHistory front ∈ PFunDDS.dom t ∨ rightHistory front = [] := by
          by_cases hne : rightHistory front = []
          · exact Or.inr hne
          · exact Or.inl (hrightGuard hne)
        have hplainLeftDom :
            plainState.2.2 ∈ PFunDDS.dom s ∨ plainState.2.2 = [] :=
          attachDrive_base_dom interface converter s (leftHistory front) (Or.inr rfl)
            hplainState
        obtain ⟨outputs, composite, hcomposite, hcompLeft, hcompRight⟩ :=
          attachDrive_routedPar_bwd interface converter s t front
            (conv := ([] : List (CIn X Y))) (base := ([] : List ((P ⊕ Q) × X)))
            (Or.inr rfl) (Or.inr rfl) (by simpa using hfrontRight) hplainState
        simp only [List.nil_append] at hcompRight
        have hcompLeftDom :
            leftHistory composite ∈ PFunDDS.dom s ∨ leftHistory composite = [] := by
          rw [hcompLeft]; exact hplainLeftDom
        have hcompRightDom :
            rightHistory composite ∈ PFunDDS.dom t ∨ rightHistory composite = [] := by
          rw [hcompRight]; exact hfrontRight
        refine ⟨(outputs, (plainState.2.1, composite)), hcomposite, ?_⟩
        by_cases hleq : left = interface
        · rw [hleq] at hplainAnswer ⊢
          rw [attachEntryStep_self] at hplainAnswer ⊢
          rw [Part.mem_map_iff] at hplainAnswer ⊢
          obtain ⟨⟨resAnswer, resConv, resBase⟩, hres, hreseq⟩ := hplainAnswer
          rw [← hcompLeft] at hres
          obtain ⟨compBase, hcompRes, -, -⟩ :=
            attachResolve_routedPar_bwd interface converter s t hcompLeftDom
              hcompRightDom hres
          exact ⟨(resAnswer, (resConv, compBase)), hcompRes, hreseq⟩
        · rw [map_fst_attachEntryStep_of_ne _ _ _ _ _ hleq] at hplainAnswer
          rw [map_fst_attachEntryStep_of_ne _ _ _ _ _ (by simpa using hleq),
            routedPar_apply_inl s t _ left value (by simpa using hcompRightDom)
              (by simp)]
          simp only [leftHistory_append, leftHistory_inl, hcompLeft]
          exact hplainAnswer
    | inr right =>
        rw [show rightHistory (front ++ [((Sum.inr right : P ⊕ Q), value)]) =
          rightHistory front ++ [(right, value)] by simp] at hbranch
        rw [show leftHistory (front ++ [((Sum.inr right : P ⊕ Q), value)]) =
          leftHistory front by simp] at hleftGuard
        have hfrontRight :
            rightHistory front ∈ PFunDDS.dom t ∨ rightHistory front = [] := by
          by_cases hne : rightHistory front = []
          · exact Or.inr hne
          · refine Or.inl (PFunDDS.prefix_closed t ⟨[(right, value)], rfl⟩ hne ?_)
            exact Part.dom_iff_mem.mpr ⟨answer, hbranch⟩
        have hplainMem : ∃ plainState,
            plainState ∈ attachDrive interface converter s ([], []) (leftHistory front) := by
          by_cases hne : leftHistory front = []
          · exact ⟨([], ([], [])), by rw [hne]; simp [attachDrive]⟩
          · obtain ⟨plainAnswer, hplainAnswer⟩ :=
              Part.dom_iff_mem.mp (hleftGuard hne)
            change plainAnswer ∈ attachRaw interface converter s (leftHistory front)
              at hplainAnswer
            rw [attachRaw, Part.mem_bind_iff] at hplainAnswer
            obtain ⟨plainState, hplainState, -⟩ := hplainAnswer
            exact ⟨plainState, hplainState⟩
        obtain ⟨plainState, hplainState⟩ := hplainMem
        have hplainLeftDom :
            plainState.2.2 ∈ PFunDDS.dom s ∨ plainState.2.2 = [] :=
          attachDrive_base_dom interface converter s (leftHistory front) (Or.inr rfl)
            hplainState
        obtain ⟨outputs, composite, hcomposite, hcompLeft, hcompRight⟩ :=
          attachDrive_routedPar_bwd interface converter s t front
            (conv := ([] : List (CIn X Y))) (base := ([] : List ((P ⊕ Q) × X)))
            (Or.inr rfl) (Or.inr rfl) (by simpa using hfrontRight) hplainState
        simp only [List.nil_append] at hcompRight
        refine ⟨(outputs, (plainState.2.1, composite)), hcomposite, ?_⟩
        rw [map_fst_attachEntryStep_of_ne _ _ _ _ _ (by simp),
          routedPar_apply_inr s t _ right value
            (by simpa [hcompLeft] using hplainLeftDom) (by simp)]
        simp only [rightHistory_append, rightHistory_inr, hcompRight]
        exact hbranch

/-- **CR18 Definition 3.13 commutes with disjoint-interface parallel
composition.**  A converter attached at an interface of the *left* component of a
routed parallel neither sees nor disturbs the right component: its own inner
queries all carry the tag `Sum.inl i` and are answered by `s` on the left
sub-history, while queries at right-tagged interfaces pass through the
converter's frame untouched and are answered by `t` on the right sub-history.
Hence attaching inside the parallel composition is the same system as attaching
to the left component first. -/
theorem attachAt_routedPar_left [DecidableEq P] [DecidableEq Q]
    (i : P) (converter : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (t : PFunDDS.Resource Q X Y) :
    attachAt (Sum.inl i) converter (routedPar s t)
      = routedPar (attachAt i converter s) t := by
  apply Subtype.ext
  funext history
  apply Part.ext
  intro answer
  exact ⟨mem_routedPar_attachAt_of_mem_attachRaw i converter s t history,
    mem_attachRaw_of_mem_routedPar_attachAt i converter s t history⟩

end RandomSystems.CR18.PFunConverter.General

namespace RandomSystems.CR18.TypedResource

universe c i j k u v

variable {I : Type i} {J : Type j} {U : SignatureUniverse.{c, u, v}}

/-! ## The disjoint-union boundary -/

section Boundaries

variable (left : Boundary U I) (right : Boundary U J)

/-- The disjoint-union boundary determines both components. -/
theorem sum_elim_boundary_inj {left left' : Boundary U I}
    {right right' : Boundary U J}
    (same : Sum.elim left right = Sum.elim left' right') :
    left = left' ∧ right = right' :=
  ⟨funext fun interface => congrFun same (Sum.inl interface),
    funext fun interface => congrFun same (Sum.inr interface)⟩

/-- Queries at the disjoint-union boundary, re-associated as a tagged sum
of the components' queries.  **One** `Equiv.sumSigmaDistrib`: the fibre of
`Sum.elim left right` at `Sum.inl i` reduces to `left i`, so no alphabet
coding — no `HasSumCode`, no `sumCode` — enters at all. -/
def tensorQueryEquiv :
    Query U (Sum.elim left right) ≃ Query U left ⊕ Query U right :=
  Equiv.sumSigmaDistrib fun interface => U.input (Sum.elim left right interface)

/-- Flat answers at the disjoint-union boundary, re-associated the same
way — the same mathlib equivalence at the output family. -/
def tensorAnswerEquiv :
    FlatAnswer U (Sum.elim left right) ≃
      FlatAnswer U left ⊕ FlatAnswer U right :=
  Equiv.sumSigmaDistrib fun interface => U.output (Sum.elim left right interface)

@[simp]
theorem tensorQueryEquiv_inl (interface : I)
    (value : U.input (Sum.elim left right (Sum.inl interface))) :
    tensorQueryEquiv left right ⟨Sum.inl interface, value⟩ =
      Sum.inl ⟨interface, value⟩ :=
  rfl

@[simp]
theorem tensorQueryEquiv_inr (interface : J)
    (value : U.input (Sum.elim left right (Sum.inr interface))) :
    tensorQueryEquiv left right ⟨Sum.inr interface, value⟩ =
      Sum.inr ⟨interface, value⟩ :=
  rfl

/-- The query equivalence keeps the interface, re-tagged by the side it
landed on. -/
@[simp]
theorem tensorQueryEquiv_index (query : Query U (Sum.elim left right)) :
    Sum.map Sigma.fst Sigma.fst (tensorQueryEquiv left right query) =
      query.1 := by
  obtain ⟨interface, value⟩ := query
  cases interface <;> rfl

/-- The answer equivalence keeps the interface too. -/
@[simp]
theorem tensorAnswerEquiv_index (answer : FlatAnswer U (Sum.elim left right)) :
    Sum.map Sigma.fst Sigma.fst (tensorAnswerEquiv left right answer) =
      answer.1 := by
  obtain ⟨interface, value⟩ := answer
  cases interface <;> rfl

/-- Inverse form: a left-tagged answer sits at the left-tagged interface. -/
@[simp]
theorem tensorAnswerEquiv_symm_inl_index (answer : FlatAnswer U left) :
    ((tensorAnswerEquiv left right).symm (Sum.inl answer)).1 =
      Sum.inl answer.1 :=
  rfl

/-- Inverse form on the right component. -/
@[simp]
theorem tensorAnswerEquiv_symm_inr_index (answer : FlatAnswer U right) :
    ((tensorAnswerEquiv left right).symm (Sum.inr answer)).1 =
      Sum.inr answer.1 :=
  rfl

/-- Inverse form for queries, left component. -/
@[simp]
theorem tensorQueryEquiv_symm_inl_index (query : Query U left) :
    ((tensorQueryEquiv left right).symm (Sum.inl query)).1 =
      Sum.inl query.1 :=
  rfl

/-- Inverse form for queries, right component. -/
@[simp]
theorem tensorQueryEquiv_symm_inr_index (query : Query U right) :
    ((tensorQueryEquiv left right).symm (Sum.inr query)).1 =
      Sum.inr query.1 :=
  rfl

end Boundaries

/-! ## Tag faithfulness of a relabelled flat parallel, once and for all

`TypedParallel.lean` proves this for `sumBoundary`, where both components
are indexed by the *same* `I` and the two index maps are the identity.
Nothing in the argument uses that.  The statement below is the same proof
with the index maps `leftIndex`/`rightIndex` as parameters; `sumBoundary`
is the instance at `id`/`id` and the tensor is the instance at
`Sum.inl`/`Sum.inr`. -/

/-- If a merged history ends in a left-tagged query, the left sub-history
ends in exactly that query.  (`TypedParallel.lean` carries a `private` copy;
this is the public statement, and a migration candidate for whichever module
ends up owning the tagged-history calculus.) -/
theorem getLast?_filterMap_getLeft {alpha beta : Type*}
    {history : List (alpha ⊕ beta)} {value : alpha}
    (nonempty : history ≠ [])
    (last : history.getLast nonempty = Sum.inl value) :
    (history.filterMap Sum.getLeft?).getLast? = some value := by
  have decomposition :
      history = history.dropLast ++ [(Sum.inl value : alpha ⊕ beta)] := by
    rw [← last]
    exact (List.dropLast_append_getLast nonempty).symm
  have step : (history.dropLast ++
        [(Sum.inl value : alpha ⊕ beta)]).filterMap Sum.getLeft?
      = history.dropLast.filterMap Sum.getLeft? ++ [value] := by simp
  rw [decomposition, step, List.getLast?_concat]

/-- Right-tagged twin of `getLast?_filterMap_getLeft`. -/
theorem getLast?_filterMap_getRight {alpha beta : Type*}
    {history : List (alpha ⊕ beta)} {value : beta}
    (nonempty : history ≠ [])
    (last : history.getLast nonempty = Sum.inr value) :
    (history.filterMap Sum.getRight?).getLast? = some value := by
  have decomposition :
      history = history.dropLast ++ [(Sum.inr value : alpha ⊕ beta)] := by
    rw [← last]
    exact (List.dropLast_append_getLast nonempty).symm
  have step : (history.dropLast ++
        [(Sum.inr value : alpha ⊕ beta)]).filterMap Sum.getRight?
      = history.dropLast.filterMap Sum.getRight? ++ [value] := by simp
  rw [decomposition, step, List.getLast?_concat]

namespace DependentDDS

/-- **The `unflatten` obligation for any relabelled flat parallel.**  Given
a query and a flat-answer re-association of a composite boundary that both
respect the interface index — through arbitrary index maps `leftIndex` and
`rightIndex` — the relabelled flat parallel of two tag-faithful components
is tag-faithful.  `PFunDDS.par` answers a left-tagged query from the left
component, whose own tag-faithfulness names the interface of the last left
sub-query; `getLast?_filterMap_getLeft` identifies that sub-query with the
global last query, and the index hypotheses carry its interface across.

This is `TypedParallel.DependentDDS.tag_faithful_relabel_par` with the
index maps freed: that theorem is the case `leftIndex = rightIndex = id`,
`DependentDDS.tensor` below is the case `Sum.inl`/`Sum.inr`. -/
theorem tagFaithful_relabel_par_general
    {K : Type k} {boundary : Boundary U K}
    {left : Boundary U I} {right : Boundary U J}
    (queryE : Query U boundary ≃ Query U left ⊕ Query U right)
    (answerE : FlatAnswer U boundary ≃ FlatAnswer U left ⊕ FlatAnswer U right)
    {leftIndex : I → K} {rightIndex : J → K}
    (queryIndexLeft : ∀ (query : Query U boundary) (component : Query U left),
      queryE query = Sum.inl component → query.1 = leftIndex component.1)
    (queryIndexRight : ∀ (query : Query U boundary) (component : Query U right),
      queryE query = Sum.inr component → query.1 = rightIndex component.1)
    (answerIndexLeft : ∀ answer : FlatAnswer U left,
      (answerE.symm (Sum.inl answer)).1 = leftIndex answer.1)
    (answerIndexRight : ∀ answer : FlatAnswer U right,
      (answerE.symm (Sum.inr answer)).1 = rightIndex answer.1)
    {flatLeft : PFunDDS.DDS (Query U left) (FlatAnswer U left)}
    {flatRight : PFunDDS.DDS (Query U right) (FlatAnswer U right)}
    (faithfulLeft : TagFaithful flatLeft)
    (faithfulRight : TagFaithful flatRight) :
    TagFaithful
      (PFunDDS.DDS.relabel queryE.symm answerE.symm
        (PFunDDS.par flatLeft flatRight)) := by
  intro history member
  have nonempty : history ≠ [] := by
    intro empty
    subst empty
    exact PFunDDS.empty_not_mem _ member
  have member' : history.map ⇑queryE ∈
      PFunDDS.dom (PFunDDS.par flatLeft flatRight) := by
    have h := (PFunDDS.DDS.mem_dom_relabel queryE.symm answerE.symm
      (PFunDDS.par flatLeft flatRight) history).mp member
    simpa using h
  have mappedNe : history.map ⇑queryE ≠ [] := fun h =>
    nonempty (List.map_eq_nil_iff.mp h)
  have mappedLast : (history.map ⇑queryE).getLast mappedNe =
      queryE (history.getLast nonempty) := List.getLast_map _
  have houtput : PFunDDS.output
      (PFunDDS.DDS.relabel queryE.symm answerE.symm
        (PFunDDS.par flatLeft flatRight)) history member =
      answerE.symm
        (PFunDDS.output (PFunDDS.par flatLeft flatRight)
          (history.map ⇑queryE) member') := rfl
  rw [houtput]
  rcases hcase : queryE (history.getLast nonempty) with q | q
  · -- the last query is left-tagged, so the parallel answered from the left
    have mappedLast? : (history.map ⇑queryE).getLast? = some (Sum.inl q) := by
      rw [List.getLast?_eq_some_getLast mappedNe, mappedLast, hcase]
    have hraw : PFunDDS.output (PFunDDS.par flatLeft flatRight)
        (history.map ⇑queryE) member' ∈
        (flatLeft.1 ((history.map ⇑queryE).filterMap Sum.getLeft?)).map
          Sum.inl := by
      have hmem : PFunDDS.output (PFunDDS.par flatLeft flatRight)
          (history.map ⇑queryE) member' ∈
          (PFunDDS.par flatLeft flatRight).1
            (history.map ⇑queryE) := Part.get_mem member'
      simp only [PFunDDS.par] at hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      rw [mappedLast?] at hmem
      exact hmem
    obtain ⟨answer, answerMem, answerEq⟩ := (Part.mem_map_iff _).mp hraw
    have memberLeft : (history.map ⇑queryE).filterMap Sum.getLeft? ∈
        PFunDDS.dom flatLeft :=
      Part.dom_iff_mem.mpr ⟨answer, answerMem⟩
    have subLast? : ((history.map ⇑queryE).filterMap Sum.getLeft?).getLast? =
        some q :=
      getLast?_filterMap_getLeft mappedNe (mappedLast.trans hcase)
    have subNe : (history.map ⇑queryE).filterMap Sum.getLeft? ≠ [] := by
      intro empty
      rw [empty] at subLast?
      simp at subLast?
    have subLast : ((history.map ⇑queryE).filterMap Sum.getLeft?).getLast
        subNe = q :=
      Option.some.inj
        ((List.getLast?_eq_some_getLast subNe).symm.trans subLast?)
    have answerVal : PFunDDS.output flatLeft
        ((history.map ⇑queryE).filterMap Sum.getLeft?) memberLeft = answer :=
      Part.get_eq_of_mem answerMem memberLeft
    have answerTag : answer.1 = q.1 := by
      have hfaith := faithfulLeft _ memberLeft
      rw [answerVal] at hfaith
      rw [hfaith]
      exact congrArg Sigma.fst subLast
    rw [← answerEq, answerIndexLeft, answerTag]
    exact (queryIndexLeft (history.getLast nonempty) q hcase).symm
  · -- symmetric: the last query is right-tagged
    have mappedLast? : (history.map ⇑queryE).getLast? = some (Sum.inr q) := by
      rw [List.getLast?_eq_some_getLast mappedNe, mappedLast, hcase]
    have hraw : PFunDDS.output (PFunDDS.par flatLeft flatRight)
        (history.map ⇑queryE) member' ∈
        (flatRight.1 ((history.map ⇑queryE).filterMap Sum.getRight?)).map
          Sum.inr := by
      have hmem : PFunDDS.output (PFunDDS.par flatLeft flatRight)
          (history.map ⇑queryE) member' ∈
          (PFunDDS.par flatLeft flatRight).1
            (history.map ⇑queryE) := Part.get_mem member'
      simp only [PFunDDS.par] at hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      rw [mappedLast?] at hmem
      exact hmem
    obtain ⟨answer, answerMem, answerEq⟩ := (Part.mem_map_iff _).mp hraw
    have memberRight : (history.map ⇑queryE).filterMap Sum.getRight? ∈
        PFunDDS.dom flatRight :=
      Part.dom_iff_mem.mpr ⟨answer, answerMem⟩
    have subLast? : ((history.map ⇑queryE).filterMap Sum.getRight?).getLast? =
        some q :=
      getLast?_filterMap_getRight mappedNe (mappedLast.trans hcase)
    have subNe : (history.map ⇑queryE).filterMap Sum.getRight? ≠ [] := by
      intro empty
      rw [empty] at subLast?
      simp at subLast?
    have subLast : ((history.map ⇑queryE).filterMap Sum.getRight?).getLast
        subNe = q :=
      Option.some.inj
        ((List.getLast?_eq_some_getLast subNe).symm.trans subLast?)
    have answerVal : PFunDDS.output flatRight
        ((history.map ⇑queryE).filterMap Sum.getRight?) memberRight = answer :=
      Part.get_eq_of_mem answerMem memberRight
    have answerTag : answer.1 = q.1 := by
      have hfaith := faithfulRight _ memberRight
      rw [answerVal] at hfaith
      rw [hfaith]
      exact congrArg Sigma.fst subLast
    rw [← answerEq, answerIndexRight, answerTag]
    exact (queryIndexRight (history.getLast nonempty) q hcase).symm

end DependentDDS

/-! ## The tensor tower

Everything below is transport, exactly as in `TypedParallel.lean`: the
dependent tensor is *defined* as flatten → `PFunDDS.par` → relabel →
unflatten, so `flatten_tensor` is the single seam through which the strict
flat facts (`StrictContext.maxEDist_par_le`, `equivalent_par`, the
cancellation theorems) reach the typed carrier, through the relabelling
isometry `StrictContext.maxEDist_relabel` and metric full abstraction. -/

open RandomSystems (Dist)

noncomputable section

section TensorTower

variable {left : Boundary U I} {right : Boundary U J}

/-- The tensor's query re-association routes a left-tagged component to a
left-tagged interface. -/
theorem tensorQueryEquiv_index_left
    (query : Query U (Sum.elim left right)) (component : Query U left)
    (hits : tensorQueryEquiv left right query = Sum.inl component) :
    query.1 = Sum.inl component.1 := by
  obtain ⟨interface, value⟩ := query
  cases interface with
  | inl _ =>
      have same := Sum.inl.inj hits
      subst same
      rfl
  | inr other =>
      have clash : (Sum.inr ⟨other, value⟩ : Query U left ⊕ Query U right) =
          Sum.inl component := hits
      exact absurd clash (by simp)

/-- Right-tagged twin of `tensorQueryEquiv_index_left`. -/
theorem tensorQueryEquiv_index_right
    (query : Query U (Sum.elim left right)) (component : Query U right)
    (hits : tensorQueryEquiv left right query = Sum.inr component) :
    query.1 = Sum.inr component.1 := by
  obtain ⟨interface, value⟩ := query
  cases interface with
  | inl other =>
      have clash : (Sum.inl ⟨other, value⟩ : Query U left ⊕ Query U right) =
          Sum.inr component := hits
      exact absurd clash (by simp)
  | inr _ =>
      have same := Sum.inr.inj hits
      subst same
      rfl

namespace DependentDDS

/-- The `unflatten` obligation for the tensor: the instance of
`tagFaithful_relabel_par_general` at `leftIndex = Sum.inl`,
`rightIndex = Sum.inr`. -/
theorem tagFaithful_relabel_par_tensor
    {flatLeft : PFunDDS.DDS (Query U left) (FlatAnswer U left)}
    {flatRight : PFunDDS.DDS (Query U right) (FlatAnswer U right)}
    (faithfulLeft : TagFaithful flatLeft)
    (faithfulRight : TagFaithful flatRight) :
    TagFaithful
      (PFunDDS.DDS.relabel (tensorQueryEquiv left right).symm
        (tensorAnswerEquiv left right).symm
        (PFunDDS.par flatLeft flatRight)) :=
  tagFaithful_relabel_par_general _ _
    tensorQueryEquiv_index_left tensorQueryEquiv_index_right
    (tensorAnswerEquiv_symm_inl_index left right)
    (tensorAnswerEquiv_symm_inr_index left right)
    faithfulLeft faithfulRight

/-- **Jost's `[R, S]` on the deterministic typed carrier**: the two
resources side by side at the disjoint union of their interface sets.
Flatten both, compose with `PFunDDS.par`, relabel along the single
`Equiv.sumSigmaDistrib`, and read the result back as a native dependent
resource. -/
def tensor (leftSystem : DependentDDS U left)
    (rightSystem : DependentDDS U right) :
    DependentDDS U (Sum.elim left right) :=
  unflatten
    (PFunDDS.DDS.relabel (tensorQueryEquiv left right).symm
      (tensorAnswerEquiv left right).symm
      (PFunDDS.par leftSystem.flatten rightSystem.flatten))
    (tagFaithful_relabel_par_tensor (flatten_tag_faithful leftSystem)
      (flatten_tag_faithful rightSystem))

/-- **The defining equation of the tensor** (deterministic level). -/
theorem flatten_tensor (leftSystem : DependentDDS U left)
    (rightSystem : DependentDDS U right) :
    (leftSystem.tensor rightSystem).flatten =
      PFunDDS.DDS.relabel (tensorQueryEquiv left right).symm
        (tensorAnswerEquiv left right).symm
        (PFunDDS.par leftSystem.flatten rightSystem.flatten) :=
  flatten_unflatten _ _

/-! ### The tensor in the uniform chart

`DependentDDS.attach` is defined by crossing into the uniform chart
(`DependentDDS.embed`), and the two sides of the attachment/tensor
interchange sit at boundaries that are only propositionally equal.  The
chart is therefore where that interchange must be stated, and `embed_tensor`
is the bridge: the tensor of two typed resources embeds as the routed
parallel (`PFunConverter.General.routedPar`) of their embeddings.  The
left/right sub-histories the two sides use are written out unfolded —
`(history.map ⇑(tensorQueryEquiv left right)).filterMap Sum.getLeft?` is
`PFunDDS.par`'s own projection — because that is the form every rewrite in
the chain sees. -/

/-- Encoding one dependent query in the uniform chart. -/
@[simp]
theorem encodeQuery_mk {K : Type k} {boundary : Boundary U K} (interface : K)
    (value : U.input (boundary interface)) :
    encodeQuery (boundary := boundary) ⟨interface, value⟩ =
      (interface, ⟨boundary interface, value⟩) :=
  rfl

/-- Encoding one dependent flat answer in the uniform chart. -/
@[simp]
theorem encodeAnswer_mk {K : Type k} {boundary : Boundary U K} (interface : K)
    (value : U.output (boundary interface)) :
    encodeAnswer (boundary := boundary) ⟨interface, value⟩ =
      ⟨boundary interface, value⟩ :=
  rfl

/-- Encoding commutes with the left routing: the uniform chart's left
sub-history of an encoded tensor history is the encoding of the sub-history
`PFunDDS.par` routes to the left component. -/
theorem leftHistory_map_encodeQuery
    (history : List (Query U (Sum.elim left right))) :
    PFunConverter.General.leftHistory (history.map encodeQuery) =
      ((history.map (tensorQueryEquiv left right)).filterMap
        Sum.getLeft?).map encodeQuery := by
  induction history with
  | nil => rfl
  | cons query rest induction =>
      obtain ⟨interface, value⟩ := query
      cases interface with
      | inl _ =>
          rw [List.map_cons]
          exact congrArg (List.cons _) induction
      | inr _ =>
          rw [List.map_cons]
          exact induction

/-- Right-hand twin of `leftHistory_map_encodeQuery`. -/
theorem rightHistory_map_encodeQuery
    (history : List (Query U (Sum.elim left right))) :
    PFunConverter.General.rightHistory (history.map encodeQuery) =
      ((history.map (tensorQueryEquiv left right)).filterMap
        Sum.getRight?).map encodeQuery := by
  induction history with
  | nil => rfl
  | cons query rest induction =>
      obtain ⟨interface, value⟩ := query
      cases interface with
      | inl _ =>
          rw [List.map_cons]
          exact induction
      | inr _ =>
          rw [List.map_cons]
          exact congrArg (List.cons _) induction

/-- A left-tagged flat answer re-encodes to the encoding of its own
component's answer: the tensor's answer re-association is invisible in the
uniform chart. -/
@[simp]
theorem encodeAnswer_tensorAnswerEquiv_symm_inl (answer : FlatAnswer U left) :
    encodeAnswer ((tensorAnswerEquiv left right).symm (Sum.inl answer)) =
      encodeAnswer answer :=
  rfl

/-- Right-hand twin of `encodeAnswer_tensorAnswerEquiv_symm_inl`. -/
@[simp]
theorem encodeAnswer_tensorAnswerEquiv_symm_inr (answer : FlatAnswer U right) :
    encodeAnswer ((tensorAnswerEquiv left right).symm (Sum.inr answer)) =
      encodeAnswer answer :=
  rfl

/-- **The tensor in the uniform chart**: embedding the tensor is the routed
parallel of the embeddings.  Both sides guard on the two sub-histories and
answer from the component owning the last query's interface; the content is
that encoding commutes with the routing and that a code-incoherent history is
refused on both sides. -/
theorem embed_tensor (leftSystem : DependentDDS U left)
    (rightSystem : DependentDDS U right) :
    (leftSystem.tensor rightSystem).embed =
      PFunConverter.General.routedPar leftSystem.embed rightSystem.embed := by
  apply Subtype.ext
  funext ambient
  by_cases conforms : HistoryConforms (Sum.elim left right) ambient
  · obtain ⟨history, rfl⟩ :
        ∃ history : List (Query U (Sum.elim left right)),
          history.map encodeQuery = ambient :=
      ⟨decodeHistory (Sum.elim left right) ambient conforms,
        encode_history_decode _ ambient conforms⟩
    rw [DependentDDS.embed_apply_encoded, DependentDDS.flatten_tensor,
      PFunDDS.DDS.relabel_raw, Equiv.symm_symm, Part.map_map]
    apply Part.ext
    intro answer
    simp only [Part.mem_map_iff, PFunDDS.mem_par_iff,
      PFunConverter.General.mem_routedPar_iff, leftHistory_map_encodeQuery,
      rightHistory_map_encodeQuery, DependentDDS.embed_apply_encoded,
      List.getLast?_map, ne_eq, List.map_eq_nil_iff, Part.map_Dom,
      Function.comp_apply]
    rcases hlast : history.getLast? with _ | ⟨interface, value⟩
    · simp
    · cases interface with
      | inl leftInterface =>
          simp only [Option.map_some, encodeQuery_mk, tensorQueryEquiv_inl,
            Part.mem_map_iff]
          constructor
          · rintro ⟨raw, ⟨guardLeft, guardRight, component, componentMem, rfl⟩,
              rfl⟩
            exact ⟨guardLeft, guardRight, component, componentMem, rfl⟩
          · rintro ⟨guardLeft, guardRight, component, componentMem, rfl⟩
            exact ⟨Sum.inl component,
              ⟨guardLeft, guardRight, component, componentMem, rfl⟩, rfl⟩
      | inr rightInterface =>
          simp only [Option.map_some, encodeQuery_mk, tensorQueryEquiv_inr,
            Part.mem_map_iff]
          constructor
          · rintro ⟨raw, ⟨guardLeft, guardRight, component, componentMem, rfl⟩,
              rfl⟩
            exact ⟨guardLeft, guardRight, component, componentMem, rfl⟩
          · rintro ⟨guardLeft, guardRight, component, componentMem, rfl⟩
            exact ⟨Sum.inr component,
              ⟨guardLeft, guardRight, component, componentMem, rfl⟩, rfl⟩
  · obtain ⟨badQuery, badMember, badConforms⟩ :
        ∃ query ∈ ambient, ¬ QueryConforms (Sum.elim left right) query := by
      by_contra allConform
      push Not at allConform
      exact conforms allConform
    have leftNone :
        (leftSystem.tensor rightSystem).embed.1 ambient = Part.none :=
      Part.eq_none_iff'.mpr fun defined => conforms defined.1
    rw [leftNone]
    refine (Part.eq_none_iff'.mpr ?_).symm
    rintro ⟨guardLeft, guardRight, -⟩
    obtain ⟨badInterface, badInput⟩ := badQuery
    cases badInterface with
    | inl leftInterface =>
        have member : (leftInterface, badInput) ∈
            PFunConverter.General.leftHistory ambient :=
          (PFunConverter.General.mem_leftHistory_iff ambient
            (leftInterface, badInput)).mpr badMember
        exact badConforms
          ((guardLeft (List.ne_nil_of_mem member)).1 _ member)
    | inr rightInterface =>
        have member : (rightInterface, badInput) ∈
            PFunConverter.General.rightHistory ambient :=
          (PFunConverter.General.mem_rightHistory_iff ambient
            (rightInterface, badInput)).mpr badMember
        exact badConforms
          ((guardRight (List.ne_nil_of_mem member)).1 _ member)


end DependentDDS

namespace DependentPDS

/-- Tensor of finite-support laws: the independent product pushed through
the deterministic tensor. -/
def tensor (leftLaw : DependentPDS U left) (rightLaw : DependentPDS U right) :
    DependentPDS U (Sum.elim left right) :=
  Dist.fTransform
    (fun pair : DependentDDS U left × DependentDDS U right =>
      pair.1.tensor pair.2)
    (Dist.prod leftLaw rightLaw)

theorem tensor_weight (leftLaw : DependentPDS U left)
    (rightLaw : DependentPDS U right) :
    (tensor leftLaw rightLaw).weight = leftLaw.weight * rightLaw.weight := by
  unfold tensor
  rw [Dist.weight_fTransform, Dist.weight_prod]

/-- **The defining equation of the tensor** (law level): flattening
commutes with the tensor up to the boundary relabelling. -/
theorem flatten_tensor (leftLaw : DependentPDS U left)
    (rightLaw : DependentPDS U right) :
    DependentPDS.flatten (tensor leftLaw rightLaw) =
      PFunPDS.relabel (tensorQueryEquiv left right).symm
        (tensorAnswerEquiv left right).symm
        (PFunPDS.par (DependentPDS.flatten leftLaw)
          (DependentPDS.flatten rightLaw)) := by
  unfold DependentPDS.flatten tensor PFunPDS.relabel PFunPDS.par
  rw [← Dist.pushforward_product_eq_product_pushforwards,
    Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg
    (fun step => Dist.fTransform step (Dist.prod leftLaw rightLaw))
    (funext fun pair => DependentDDS.flatten_tensor pair.1 pair.2)

/-- Tensor of normalized laws. -/
def Prob.tensor (leftLaw : Prob U left) (rightLaw : Prob U right) :
    Prob U (Sum.elim left right) :=
  ⟨DependentPDS.tensor leftLaw.val rightLaw.val, by
    rw [← DependentPDS.flatten_is_probability_distribution_iff,
      DependentPDS.flatten_tensor]
    exact (PFunPDS.isProbDist_relabel_iff _ _ _).mpr
      (PFunPDS.isProbDist_par
        ((DependentPDS.flatten_is_probability_distribution_iff _).mpr
          leftLaw.property)
        ((DependentPDS.flatten_is_probability_distribution_iff _).mpr
          rightLaw.property))⟩

@[simp]
theorem Prob.tensor_val (leftLaw : Prob U left) (rightLaw : Prob U right) :
    (Prob.tensor leftLaw rightLaw).val =
      DependentPDS.tensor leftLaw.val rightLaw.val :=
  rfl

end DependentPDS

namespace DependentRandomSystem

variable [DecidableEq I] [DecidableEq J] [DecidableEq U.Code]

/-- Tensor of contextual behavior classes. -/
def tensor (leftClass : DependentRandomSystem U left)
    (rightClass : DependentRandomSystem U right) :
    DependentRandomSystem U (Sum.elim left right) :=
  Quotient.liftOn₂ leftClass rightClass
    (fun leftProb rightProb =>
      ofProb (DependentPDS.Prob.tensor leftProb rightProb))
    (fun leftA rightA leftB rightB leftEquiv rightEquiv => by
      have leftFlat : StrictContext.Equivalent
          (DependentPDS.flatten leftA.val) (DependentPDS.flatten leftB.val) :=
        (DependentPDS.contextually_equivalent_iff_flatten_equivalent _ _).mp
          ((DependentPDS.Prob.contextual_setoid_rel_iff leftA leftB).mp
            leftEquiv)
      have rightFlat : StrictContext.Equivalent
          (DependentPDS.flatten rightA.val)
          (DependentPDS.flatten rightB.val) :=
        (DependentPDS.contextually_equivalent_iff_flatten_equivalent _ _).mp
          ((DependentPDS.Prob.contextual_setoid_rel_iff rightA rightB).mp
            rightEquiv)
      refine ofProb_eq_of_flatten_equivalent _ _ ?_
      rw [DependentPDS.Prob.tensor_val, DependentPDS.Prob.tensor_val,
        DependentPDS.flatten_tensor, DependentPDS.flatten_tensor]
      exact StrictContext.equivalent_relabel _ _
        (StrictContext.equivalent_par leftB.flatten.property
          rightA.flatten.property leftFlat rightFlat))

@[simp]
theorem tensor_ofProb (leftProb : DependentPDS.Prob U left)
    (rightProb : DependentPDS.Prob U right) :
    tensor (ofProb leftProb) (ofProb rightProb) =
      ofProb (DependentPDS.Prob.tensor leftProb rightProb) :=
  rfl

/-- **Maurer11 eq. (3) for Jost's disjoint-interface `[R, S]`**: the tensor
is `‖`-non-expanding for the contextual metric.  Same chain as
`DependentRandomSystem.edist_parallel_le`: full abstraction → the defining
equation → the relabelling isometry → the strict `maxEDist_par_le`.  The
ε-accounting therefore survives the move to disjoint interface sets
unchanged. -/
theorem edist_tensor_le
    (leftA leftB : DependentRandomSystem U left)
    (rightA rightB : DependentRandomSystem U right) :
    edist (tensor leftA rightA) (tensor leftB rightB) ≤
      edist leftA leftB + edist rightA rightB := by
  induction leftA using Quotient.inductionOn with
  | _ leftA =>
      induction leftB using Quotient.inductionOn with
      | _ leftB =>
          induction rightA using Quotient.inductionOn with
          | _ rightA =>
              induction rightB using Quotient.inductionOn with
              | _ rightB =>
                  show edist
                      (ofProb (DependentPDS.Prob.tensor leftA rightA))
                      (ofProb (DependentPDS.Prob.tensor leftB rightB)) ≤
                    edist (ofProb leftA) (ofProb leftB) +
                      edist (ofProb rightA) (ofProb rightB)
                  rw [edist_of_prob, edist_of_prob, edist_of_prob,
                    DependentPDS.contextual_edist_eq_max_edist_flatten,
                    DependentPDS.contextual_edist_eq_max_edist_flatten,
                    DependentPDS.contextual_edist_eq_max_edist_flatten,
                    DependentPDS.Prob.tensor_val,
                    DependentPDS.Prob.tensor_val,
                    DependentPDS.flatten_tensor,
                    DependentPDS.flatten_tensor,
                    StrictContext.maxEDist_relabel]
                  exact StrictContext.maxEDist_par_le _ _ _ _
                    leftB.flatten.property rightA.flatten.property

/-- **The tensor decomposition of a contextual class is unique** — the
disjoint-interface mirror of `DependentRandomSystem.parallel_inj`. -/
theorem tensor_inj
    {leftA leftB : DependentRandomSystem U left}
    {rightA rightB : DependentRandomSystem U right}
    (same : tensor leftA rightA = tensor leftB rightB) :
    leftA = leftB ∧ rightA = rightB := by
  induction leftA using Quotient.inductionOn with
  | _ leftA =>
      induction leftB using Quotient.inductionOn with
      | _ leftB =>
          induction rightA using Quotient.inductionOn with
          | _ rightA =>
              induction rightB using Quotient.inductionOn with
              | _ rightB =>
                  have parFlat :=
                    (DependentPDS.contextually_equivalent_iff_flatten_equivalent
                        _ _).mp
                      ((DependentPDS.Prob.contextual_setoid_rel_iff _ _).mp
                        (Quotient.exact same))
                  rw [DependentPDS.Prob.tensor_val,
                    DependentPDS.Prob.tensor_val,
                    DependentPDS.flatten_tensor,
                    DependentPDS.flatten_tensor,
                    StrictContext.equivalent_relabel_iff] at parFlat
                  constructor
                  · apply Quotient.sound
                    apply (DependentPDS.Prob.contextual_setoid_rel_iff _ _).mpr
                    exact
                      (DependentPDS.contextually_equivalent_iff_flatten_equivalent
                        _ _).mpr
                      (StrictContext.equivalent_left_of_par_equivalent
                        rightA.flatten.property rightB.flatten.property parFlat)
                  · apply Quotient.sound
                    apply (DependentPDS.Prob.contextual_setoid_rel_iff _ _).mpr
                    exact
                      (DependentPDS.contextually_equivalent_iff_flatten_equivalent
                        _ _).mpr
                      (StrictContext.equivalent_right_of_par_equivalent
                        leftA.flatten.property leftB.flatten.property parFlat)

end DependentRandomSystem


namespace Resource

variable [DecidableEq I] [DecidableEq J] [DecidableEq U.Code]

/-- **Jost's `[R, S]` on the heterogeneous typed resource carrier.**  Unlike
`Resource.parallel` (`TypedParallel.lean`) this is not an operation on one
`Resource I U`: the interface set genuinely grows, so the tensor is a map
`Resource I U → Resource J U → Resource (I ⊕ J) U`.  That is Jost's own
reading — parallel composition is defined only for disjoint interface sets —
and it is what a `Par` instance on a fixed `Phi I U` cannot express. -/
def tensor (leftResource : Resource I U) (rightResource : Resource J U) :
    Resource (I ⊕ J) U :=
  ⟨Sum.elim leftResource.boundary rightResource.boundary,
    DependentRandomSystem.tensor leftResource.system rightResource.system⟩

@[simp]
theorem tensor_boundary (leftResource : Resource I U)
    (rightResource : Resource J U) :
    (tensor leftResource rightResource).boundary =
      Sum.elim leftResource.boundary rightResource.boundary :=
  rfl

/-- **The tensor decomposition of a typed resource is unique.**  Cheaper than
its merged counterpart `Resource.parallel_inj`: the boundary half is
`sum_elim_boundary_inj`, two `congrFun`s, where `sumBoundary_inj` has to
appeal to `HasSumCode.sumCode_inj` — an axiom of the coding class rather than
a fact about functions. -/
theorem tensor_inj {leftA leftB : Resource I U} {rightA rightB : Resource J U}
    (same : tensor leftA rightA = tensor leftB rightB) :
    leftA = leftB ∧ rightA = rightB := by
  rcases leftA with ⟨leftABoundary, leftASystem⟩
  rcases leftB with ⟨leftBBoundary, leftBSystem⟩
  rcases rightA with ⟨rightABoundary, rightASystem⟩
  rcases rightB with ⟨rightBBoundary, rightBSystem⟩
  have boundaries : Sum.elim leftABoundary rightABoundary =
      Sum.elim leftBBoundary rightBBoundary :=
    congrArg Resource.boundary same
  obtain ⟨rfl, rfl⟩ := sum_elim_boundary_inj boundaries
  rw [tensor, tensor, Resource.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := DependentRandomSystem.tensor_inj (eq_of_heq same.2)
  exact ⟨rfl, rfl⟩

/-- Distinct left components produce distinct compositions. -/
theorem tensor_ne_left {leftA leftB : Resource I U}
    {rightComponent : Resource J U} (different : leftA ≠ leftB) :
    tensor leftA rightComponent ≠ tensor leftB rightComponent :=
  fun collapse => different (tensor_inj collapse).1

/-- Within one pair of boundaries, resource-level tensor distance is
fibre-level tensor distance. -/
theorem edist_tensor_same (leftBoundary : Boundary U I)
    (rightBoundary : Boundary U J)
    (leftA leftB : DependentRandomSystem U leftBoundary)
    (rightA rightB : DependentRandomSystem U rightBoundary) :
    edist (tensor ⟨leftBoundary, leftA⟩ ⟨rightBoundary, rightA⟩)
        (tensor ⟨leftBoundary, leftB⟩ ⟨rightBoundary, rightB⟩) =
      edist (DependentRandomSystem.tensor leftA rightA)
        (DependentRandomSystem.tensor leftB rightB) :=
  Resource.edist_same _ _ _

/-- **Maurer11 §4.4 eq. (3) for Jost's `[R, S]` on the heterogeneous
carrier**: the contextual metric is non-expanding for the tensor.  Distinct
disjoint-union boundaries sit at `⊤` on both sides
(`sum_elim_boundary_inj`), and within one boundary pair the fibre-level
bound applies. -/
theorem edist_tensor_le (leftA leftB : Resource I U)
    (rightA rightB : Resource J U) :
    edist (tensor leftA rightA) (tensor leftB rightB) ≤
      edist leftA leftB + edist rightA rightB := by
  rcases leftA with ⟨leftABoundary, leftASystem⟩
  rcases leftB with ⟨leftBBoundary, leftBSystem⟩
  rcases rightA with ⟨rightABoundary, rightASystem⟩
  rcases rightB with ⟨rightBBoundary, rightBSystem⟩
  by_cases boundaries : leftABoundary = leftBBoundary ∧
      rightABoundary = rightBBoundary
  · obtain ⟨rfl, rfl⟩ := boundaries
    rw [edist_tensor_same, Resource.edist_same, Resource.edist_same]
    exact DependentRandomSystem.edist_tensor_le _ _ _ _
  · have different : Sum.elim leftABoundary rightABoundary ≠
        Sum.elim leftBBoundary rightBBoundary :=
      fun collapse => boundaries (sum_elim_boundary_inj collapse)
    rw [show tensor ⟨leftABoundary, leftASystem⟩
          ⟨rightABoundary, rightASystem⟩ =
        ⟨Sum.elim leftABoundary rightABoundary,
          DependentRandomSystem.tensor leftASystem rightASystem⟩ from rfl,
      show tensor ⟨leftBBoundary, leftBSystem⟩
          ⟨rightBBoundary, rightBSystem⟩ =
        ⟨Sum.elim leftBBoundary rightBBoundary,
          DependentRandomSystem.tensor leftBSystem rightBSystem⟩ from rfl,
      Resource.edist_ne different]
    rcases not_and_or.mp boundaries with leftDifferent | rightDifferent
    · rw [Resource.edist_ne leftDifferent]
      simp
    · rw [Resource.edist_ne rightDifferent]
      simp

end Resource

/-! ## Jost's Proposition 2.2.3, clause 2: attaching into one factor

Jost's thesis (§2.2.2, printed p. 18) states, for resources with *disjoint*
interface sets, that `π^γ [R, S] = [π^γ R, S]` whenever the connection
function `γ` lands in `R`'s interfaces.  On the typed carrier that is the
statement below.

The converter is an arbitrary `DeterministicConverter U source target` — it
is not modified, wrapped or lifted; only the boundary is transported, and
only because `Function.update` at `Sum.inl i` on `I ⊕ J` and `Function.update`
at `i` on `I` are propositionally, not definitionally, the same boundary
(`tensor_replaceBoundary_inl`).  That is why the statement is heterogeneous,
exactly as `ResourceAt.attach_comm` (`Jost/SurfaceAttach.lean`) is.

**The frame's pass-through clauses do not discharge this.**  What
`TypedFraming`'s `passStep`/`passAnswerStep` say is that the all-interface
frame forwards a query at a *non-selected* interface unchanged **to the same
resource**.  Here the content needed is different: that forwarding it to
`R ⊗ T` is the same as letting `T` answer it alone, and that the converter's
own inner queries never reach `T`.  That is a routing property of the
composition, not a property of the frame, and it is proved where the routing
lives — `PFunConverter.General.attachAt_routedPar_left`, in the uniform
chart. -/

section ClauseTwo

variable [DecidableEq I] [DecidableEq J] [DecidableEq U.Code]

omit [DecidableEq U.Code] in
/-- Updating the disjoint-union boundary at a left-tagged interface updates
the left component.  Propositional, not definitional: the two sides use
different `DecidableEq` instances inside `Function.update`. -/
theorem tensor_replaceBoundary_inl (interface : I) (target : U.Code)
    (left : Boundary U I) (right : Boundary U J) :
    replaceBoundary (Sum.elim left right) (Sum.inl interface) target =
      Sum.elim (replaceBoundary left interface target) right := by
  funext other
  cases other with
  | inl otherLeft =>
      by_cases same : otherLeft = interface
      · subst same
        simp [replaceBoundary]
      · simp [replaceBoundary, same]
  | inr otherRight => simp [replaceBoundary]

/-- **Clause 2, deterministic level.**  Attaching a converter at a
left-tagged interface of a tensor is attaching it to the left factor; the
right factor is untouched. -/
theorem DependentDDS.attach_tensor_inl
    {source target : U.Code} (interface : I)
    (converter : DeterministicConverter U source target)
    {left : Boundary U I} {right : Boundary U J}
    (sourceMatches : left interface = source)
    (leftSystem : DependentDDS U left) (rightSystem : DependentDDS U right) :
    HEq
      ((leftSystem.tensor rightSystem).attach (Sum.inl interface) converter
        sourceMatches)
      ((leftSystem.attach interface converter sourceMatches).tensor
        rightSystem) := by
  apply DependentDDS.heq_of_boundary_eq_of_embed_eq
    (tensor_replaceBoundary_inl interface target left right)
  rw [DependentDDS.embed_attach, DependentDDS.embed_tensor,
    DeterministicConverter.attachAmbient, DependentDDS.embed_tensor,
    DependentDDS.embed_attach, DeterministicConverter.attachAmbient]
  exact PFunConverter.General.attachAt_routedPar_left interface
    converter.embeddedDDC leftSystem.embed rightSystem.embed

omit [DecidableEq U.Code] in
/-- A law-level pushforward along two boundary-changing steps that agree
heterogeneously agrees heterogeneously.  (The two-map generalisation of
`DependentPDS.heq_fTransform_of_boundary_eq`, `TypedFramingMetric.lean`,
which is the special case `rightStep = id`.) -/
theorem DependentPDS.heq_fTransform_of_boundary_eq₂ {A : Type*} {K : Type k}
    {leftBoundary rightBoundary : Boundary U K}
    (boundaries : leftBoundary = rightBoundary)
    (leftStep : A → DependentDDS U leftBoundary)
    (rightStep : A → DependentDDS U rightBoundary)
    (pointwise : ∀ value, HEq (leftStep value) (rightStep value))
    (law : Dist A) :
    HEq (Dist.fTransform leftStep law) (Dist.fTransform rightStep law) := by
  subst boundaries
  have same : leftStep = rightStep := funext fun value =>
    eq_of_heq (pointwise value)
  rw [same]

/-- **Clause 2, law level.** -/
theorem DependentPDS.attach_tensor_inl
    {source target : U.Code} (interface : I)
    (converter : DeterministicConverter U source target)
    {left : Boundary U I} {right : Boundary U J}
    (sourceMatches : left interface = source)
    (leftLaw : DependentPDS U left) (rightLaw : DependentPDS U right) :
    HEq
      (DependentPDS.attach (Sum.inl interface) converter sourceMatches
        (DependentPDS.tensor leftLaw rightLaw))
      (DependentPDS.tensor
        (DependentPDS.attach interface converter sourceMatches leftLaw)
        rightLaw) := by
  have rightForm :
      DependentPDS.tensor
          (DependentPDS.attach interface converter sourceMatches leftLaw)
          rightLaw =
        Dist.fTransform
          (fun pair : DependentDDS U left × DependentDDS U right =>
            (pair.1.attach interface converter sourceMatches).tensor pair.2)
          (Dist.prod leftLaw rightLaw) := by
    have prodForm :
        Dist.prod
            (Dist.fTransform
              (fun system : DependentDDS U left =>
                system.attach interface converter sourceMatches) leftLaw)
            rightLaw =
          Dist.fTransform
            (fun pair : DependentDDS U left × DependentDDS U right =>
              (pair.1.attach interface converter sourceMatches, pair.2))
            (Dist.prod leftLaw rightLaw) := by
      have distribute :=
        RandomSystems.Dist.pushforward_product_eq_product_pushforwards
          (fun system : DependentDDS U left =>
            system.attach interface converter sourceMatches) id leftLaw rightLaw
      simpa using distribute.symm
    unfold DependentPDS.tensor DependentPDS.attach
    rw [prodForm]
    exact Dist.fTransform_comp_eq_of_pointwise _ _ _ _ fun _ => rfl
  have leftForm :
      DependentPDS.attach (Sum.inl interface) converter sourceMatches
          (DependentPDS.tensor leftLaw rightLaw) =
        Dist.fTransform
          (fun pair : DependentDDS U left × DependentDDS U right =>
            (pair.1.tensor pair.2).attach (Sum.inl interface) converter
              sourceMatches)
          (Dist.prod leftLaw rightLaw) := by
    unfold DependentPDS.tensor DependentPDS.attach
    exact Dist.fTransform_comp_eq_of_pointwise _ _ _ _ fun _ => rfl
  rw [leftForm, rightForm]
  refine DependentPDS.heq_fTransform_of_boundary_eq₂
    (tensor_replaceBoundary_inl interface target left right) _ _ ?_ _
  intro pair
  exact DependentDDS.attach_tensor_inl interface converter
    sourceMatches pair.1 pair.2

/-- **Clause 2, normalized laws.** -/
theorem DependentPDS.Prob.attach_tensor_inl
    {source target : U.Code} (interface : I)
    (converter : DeterministicConverter U source target)
    {left : Boundary U I} {right : Boundary U J}
    (sourceMatches : left interface = source)
    (leftLaw : DependentPDS.Prob U left) (rightLaw : DependentPDS.Prob U right) :
    HEq
      ((DependentPDS.Prob.tensor leftLaw rightLaw).attach (Sum.inl interface)
        converter sourceMatches)
      (DependentPDS.Prob.tensor
        (leftLaw.attach interface converter sourceMatches) rightLaw) :=
  DependentPDS.Prob.heq_of_boundary_eq_of_val_heq
    (tensor_replaceBoundary_inl interface target left right)
    (DependentPDS.attach_tensor_inl interface converter sourceMatches
      leftLaw.val rightLaw.val)

/-- **Clause 2 on the contextual quotient** — Jost Prop. 2.2.3 (2) where the
statement is actually used: `π^γ [R, S] = [π^γ R, S]` for behaviours. -/
theorem DependentRandomSystem.attach_tensor_inl
    {source target : U.Code} (interface : I)
    (converter : DeterministicConverter U source target)
    {left : Boundary U I} {right : Boundary U J}
    (sourceMatches : left interface = source)
    (leftClass : DependentRandomSystem U left)
    (rightClass : DependentRandomSystem U right) :
    HEq
      (DependentRandomSystem.attach (Sum.inl interface) converter sourceMatches
        (DependentRandomSystem.tensor leftClass rightClass))
      (DependentRandomSystem.tensor
        (DependentRandomSystem.attach interface converter sourceMatches
          leftClass)
        rightClass) := by
  induction leftClass using Quotient.inductionOn with
  | _ leftProb =>
      induction rightClass using Quotient.inductionOn with
      | _ rightProb =>
          exact DependentRandomSystem.of_prob_heq_of_boundary_eq
            (tensor_replaceBoundary_inl interface target left right)
            (DependentPDS.Prob.attach_tensor_inl interface converter
              sourceMatches leftProb rightProb)

end ClauseTwo

end TensorTower

/-! ## Interface re-indexing in general -/

section Reindex

variable {K K' : Type*} {boundary : Boundary U K} {boundary' : Boundary U K'}

/-- **Tag compatibility of an interface re-indexing.**  A pair of alphabet
equivalences between the global query and flat-answer types of two boundaries
is tag-compatible when, for every target-boundary query, an answer tagged by
the interface that query came from is sent to an answer tagged by the
interface that query goes to.

This is precisely the hypothesis under which relabelling a tag-faithful flat
system stays tag-faithful, so it is precisely the hypothesis under which a
re-indexing acts on native dependent resources at all. -/
def TagCompatible
    (queryE : Query U boundary ≃ Query U boundary')
    (answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary') : Prop :=
  ∀ (query : Query U boundary') (answer : FlatAnswer U boundary),
    answer.1 = (queryE.symm query).1 → (answerE answer).1 = query.1

/-- **The practical criterion.**  If both equivalences relocate a query and an
answer along one common map `route` on interfaces — queries at interface `k`
land at `route k`, and so do answers — then the pair is tag-compatible.  No
injectivity of `route` is needed: the condition only has to reproduce the tag
`queryE` chose, and `route` chooses it the same way on both alphabets. -/
theorem tagCompatible_of_route
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (route : K → K')
    (queryRoute : ∀ query : Query U boundary, (queryE query).1 = route query.1)
    (answerRoute : ∀ answer : FlatAnswer U boundary,
      (answerE answer).1 = route answer.1) :
    TagCompatible queryE answerE := by
  intro query answer sameTag
  rw [answerRoute, sameTag, ← queryRoute, Equiv.apply_symm_apply]

namespace DependentDDS

/-- **The `unflatten` obligation for a re-indexing**: relabelling the flat
presentation of a native dependent resource along a tag-compatible pair is
again tag-faithful.  The relabelled system answers a target history by
`answerE` of the source system's answer on the back-translated history, whose
tag is the interface of the back-translated active query; tag compatibility
turns that into the interface of the active query itself. -/
theorem tagFaithful_relabel_flatten
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (system : DependentDDS U boundary) :
    TagFaithful (PFunDDS.DDS.relabel queryE answerE system.flatten) := by
  intro history member
  have nonempty : history ≠ [] := by
    intro empty
    subst empty
    exact PFunDDS.empty_not_mem _ member
  have member' : history.map ⇑queryE.symm ∈ PFunDDS.dom system.flatten :=
    (PFunDDS.DDS.mem_dom_relabel queryE answerE system.flatten history).mp member
  have tag := system.flatten_tag_faithful (history.map ⇑queryE.symm) member'
  rw [PFunDDS.DDS.output_relabel]
  refine compatible (history.getLast nonempty) _ ?_
  rw [tag]
  exact congrArg Sigma.fst (List.getLast_map _)

/-- **Re-indexing a native dependent resource.**  Flatten, relabel along the
tag-compatible pair, and read the result back as a resource at the target
boundary. -/
def reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (system : DependentDDS U boundary) : DependentDDS U boundary' :=
  unflatten (PFunDDS.DDS.relabel queryE answerE system.flatten)
    (tagFaithful_relabel_flatten compatible system)

/-- **The defining equation of a re-indexing** (deterministic level):
flattening the re-indexed resource is relabelling the flattening. -/
theorem flatten_reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (system : DependentDDS U boundary) :
    (system.reindex compatible).flatten =
      PFunDDS.DDS.relabel queryE answerE system.flatten :=
  flatten_unflatten _ _

/-- Re-indexing never merges two resources: the alphabet relabelling is a
bijection on flat systems and flattening is injective. -/
theorem reindex_injective
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE) :
    Function.Injective
      (fun system : DependentDDS U boundary => system.reindex compatible) := by
  intro left right same
  apply flatten_injective
  have flat := congrArg DependentDDS.flatten same
  rw [flatten_reindex, flatten_reindex] at flat
  have back := congrArg
    (PFunDDS.DDS.relabel queryE.symm answerE.symm) flat
  rwa [PFunDDS.DDS.relabel_symm_relabel,
    PFunDDS.DDS.relabel_symm_relabel] at back

/-- **The image of a re-indexing, exactly.**  A resource at the target
boundary comes from one at the source boundary iff pulling its flat
presentation back along the inverse relabelling is *still* tag-faithful.
Since `TagCompatible` for the inverse pair may fail (see
`not_tagCompatible_mergeBlock_symm`), this is a genuine restriction: it is the
statement that the target resource never answers a query with an answer whose
source-boundary interface differs from the query's. -/
theorem exists_reindex_eq_iff
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (target : DependentDDS U boundary') :
    (∃ system : DependentDDS U boundary, system.reindex compatible = target) ↔
      TagFaithful (PFunDDS.DDS.relabel queryE.symm answerE.symm
        target.flatten) := by
  constructor
  · rintro ⟨system, rfl⟩
    rw [flatten_reindex, PFunDDS.DDS.relabel_symm_relabel]
    exact system.flatten_tag_faithful
  · intro faithful
    refine ⟨unflatten _ faithful, flatten_injective ?_⟩
    rw [flatten_reindex, flatten_unflatten,
      PFunDDS.DDS.relabel_relabel_symm]

/-- When the inverse pair is *also* tag-compatible, re-indexing back undoes
re-indexing forward.  Both hypotheses are needed: `TagCompatible` is not a
symmetric condition, because it constrains the answer equivalence only in the
direction the query equivalence already fixes. -/
theorem reindex_reindex_symm
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (inverseCompatible : TagCompatible queryE.symm answerE.symm)
    (system : DependentDDS U boundary) :
    (system.reindex compatible).reindex inverseCompatible = system := by
  apply flatten_injective
  rw [flatten_reindex, flatten_reindex, PFunDDS.DDS.relabel_symm_relabel]

/-- The other round trip: re-indexing forward undoes re-indexing back. -/
theorem reindex_symm_reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (inverseCompatible : TagCompatible queryE.symm answerE.symm)
    (system : DependentDDS U boundary') :
    (system.reindex inverseCompatible).reindex compatible = system := by
  apply flatten_injective
  rw [flatten_reindex, flatten_reindex, PFunDDS.DDS.relabel_relabel_symm]

/-- Two-sided tag compatibility makes re-indexing an **isomorphism of
deterministic resources** between the two boundaries. -/
def reindexEquiv
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (inverseCompatible : TagCompatible queryE.symm answerE.symm) :
    DependentDDS U boundary ≃ DependentDDS U boundary' where
  toFun system := system.reindex compatible
  invFun system := system.reindex inverseCompatible
  left_inv := reindex_reindex_symm compatible inverseCompatible
  right_inv := reindex_symm_reindex compatible inverseCompatible

end DependentDDS

namespace DependentPDS

/-- **Re-indexing a native dependent law**: the deterministic re-indexing
pushed through the distribution over deterministic representatives. -/
def reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (law : DependentPDS U boundary) : DependentPDS U boundary' :=
  Dist.fTransform (fun system => system.reindex compatible) law

/-- **The defining equation of a re-indexing** (law level): flattening
commutes with re-indexing up to the alphabet relabelling.  This is the single
seam through which the strict metric facts reach the re-indexed law. -/
theorem flatten_reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (law : DependentPDS U boundary) :
    DependentPDS.flatten (reindex compatible law) =
      PFunPDS.relabel queryE answerE (DependentPDS.flatten law) := by
  unfold DependentPDS.flatten reindex PFunPDS.relabel
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg (fun step => Dist.fTransform step law)
    (funext fun system => DependentDDS.flatten_reindex compatible system)

/-- Re-indexing preserves and reflects normalization. -/
@[simp]
theorem isProbDist_reindex_iff
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (law : DependentPDS U boundary) :
    (reindex compatible law).isProbDist ↔ law.isProbDist := by
  rw [← flatten_is_probability_distribution_iff, flatten_reindex,
    PFunPDS.isProbDist_relabel_iff, flatten_is_probability_distribution_iff]

/-- Re-indexing of a normalized native law. -/
def Prob.reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (law : Prob U boundary) : Prob U boundary' :=
  ⟨DependentPDS.reindex compatible law.val,
    (isProbDist_reindex_iff compatible law.val).2 law.property⟩

@[simp]
theorem Prob.reindex_val
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (law : Prob U boundary) :
    (Prob.reindex compatible law).val = DependentPDS.reindex compatible law.val :=
  rfl

end DependentPDS

namespace DependentRandomSystem

variable [DecidableEq K] [DecidableEq K'] [DecidableEq U.Code]

/-- **Re-indexing a contextual behavior class.**  Well-definedness is the
full-abstraction bridge (`contextually_equivalent_iff_flatten_equivalent`)
followed by the strict relabelling congruence — no new transcript argument. -/
def reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (resource : DependentRandomSystem U boundary) :
    DependentRandomSystem U boundary' :=
  Quotient.liftOn resource
    (fun law => ofProb (DependentPDS.Prob.reindex compatible law))
    (fun leftLaw rightLaw equivalent => by
      have flat : StrictContext.Equivalent
          (DependentPDS.flatten leftLaw.val)
          (DependentPDS.flatten rightLaw.val) :=
        (DependentPDS.contextually_equivalent_iff_flatten_equivalent _ _).mp
          ((DependentPDS.Prob.contextual_setoid_rel_iff leftLaw rightLaw).mp
            equivalent)
      refine ofProb_eq_of_flatten_equivalent _ _ ?_
      rw [DependentPDS.Prob.reindex_val, DependentPDS.Prob.reindex_val,
        DependentPDS.flatten_reindex, DependentPDS.flatten_reindex]
      exact StrictContext.equivalent_relabel _ _ flat)

@[simp]
theorem reindex_ofProb
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (law : DependentPDS.Prob U boundary) :
    reindex compatible (ofProb law) =
      ofProb (DependentPDS.Prob.reindex compatible law) :=
  rfl

/-- **Re-indexing is an isometry of contextual behavior** — an equality, not a
bound.  The chain is full abstraction, the defining equation, and the strict
relabelling isometry `StrictContext.maxEDist_relabel`, each of which is an
equation; nothing is lost because the alphabet bijection reindexes the
supremum over strict tests exactly. -/
@[simp]
theorem edist_reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (left right : DependentRandomSystem U boundary) :
    edist (reindex compatible left) (reindex compatible right) =
      edist left right := by
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right =>
          show edist (ofProb (DependentPDS.Prob.reindex compatible left))
              (ofProb (DependentPDS.Prob.reindex compatible right)) =
            edist (ofProb left) (ofProb right)
          rw [edist_of_prob, edist_of_prob,
            DependentPDS.contextual_edist_eq_max_edist_flatten,
            DependentPDS.contextual_edist_eq_max_edist_flatten,
            DependentPDS.Prob.reindex_val, DependentPDS.Prob.reindex_val,
            DependentPDS.flatten_reindex, DependentPDS.flatten_reindex,
            StrictContext.maxEDist_relabel]

/-- Re-indexing is injective on contextual behavior: it is an isometry and the
contextual quotient is separated. -/
theorem reindex_injective
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE) :
    Function.Injective
      (reindex compatible :
        DependentRandomSystem U boundary → DependentRandomSystem U boundary') := by
  intro left right same
  have zero : edist (reindex compatible left) (reindex compatible right) = 0 := by
    rw [same]
    exact edist_self _
  rw [edist_reindex] at zero
  exact (edist_eq_zero_iff_eq left right).mp zero

end DependentRandomSystem

end Reindex

/-! ## Merging a block of interfaces into one -/

section MergeBlock

variable {M P : Type*} {block : Boundary U P}

/-- **Queries across the merge.**  The whole `P`-block of interfaces collapses
to the single interface `Sum.inr ()`, whose signature code `blockCode` carries
the block's entire query alphabet through `inputCode`.  Built by composition:
`Equiv.sumSigmaDistrib` re-associates the sigma over `M ⊕ P` (the fibre at
`Sum.inl m` reduces to `base m` by iota, so no cast is involved),
`inputCode.symm` codes the block, `Equiv.uniqueSigma` reinstates the singleton
index, and `Equiv.sumSigmaDistrib` re-associates back over `M ⊕ Unit`. -/
def mergeQueryEquiv (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block) :
    Query U (Sum.elim base block) ≃
      Query U (Sum.elim base fun _ : Unit => blockCode) :=
  (Equiv.sumSigmaDistrib fun interface =>
      U.input (Sum.elim base block interface)).trans
    ((Equiv.sumCongr (Equiv.refl (Query U base))
        (inputCode.symm.trans
          (Equiv.uniqueSigma fun _ : Unit => U.input blockCode).symm)).trans
      (Equiv.sumSigmaDistrib fun interface : M ⊕ Unit =>
        U.input (Sum.elim base (fun _ : Unit => blockCode) interface)).symm)

/-- **Flat answers across the merge**, coded the same way by `outputCode`. -/
def mergeAnswerEquiv (base : Boundary U M) (blockCode : U.Code)
    (outputCode : U.output blockCode ≃ FlatAnswer U block) :
    FlatAnswer U (Sum.elim base block) ≃
      FlatAnswer U (Sum.elim base fun _ : Unit => blockCode) :=
  (Equiv.sumSigmaDistrib fun interface =>
      U.output (Sum.elim base block interface)).trans
    ((Equiv.sumCongr (Equiv.refl (FlatAnswer U base))
        (outputCode.symm.trans
          (Equiv.uniqueSigma fun _ : Unit => U.output blockCode).symm)).trans
      (Equiv.sumSigmaDistrib fun interface : M ⊕ Unit =>
        U.output (Sum.elim base (fun _ : Unit => blockCode) interface)).symm)

/-- The merge relocates a query along `Sum.map id (fun _ => ())`: base
interfaces are untouched, every block interface becomes the one merged
interface. -/
@[simp]
theorem mergeQueryEquiv_index (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (query : Query U (Sum.elim base block)) :
    (mergeQueryEquiv base blockCode inputCode query).1 =
      Sum.map id (fun _ : P => ()) query.1 := by
  obtain ⟨interface, value⟩ := query
  cases interface <;> rfl

/-- The merge relocates an answer along the same map on interfaces. -/
@[simp]
theorem mergeAnswerEquiv_index (base : Boundary U M) (blockCode : U.Code)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (answer : FlatAnswer U (Sum.elim base block)) :
    (mergeAnswerEquiv base blockCode outputCode answer).1 =
      Sum.map id (fun _ : P => ()) answer.1 := by
  obtain ⟨interface, value⟩ := answer
  cases interface <;> rfl

/-- Merging a block is a tag-compatible re-indexing, by the route criterion at
`route = Sum.map id (fun _ => ())`. -/
theorem tagCompatible_mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block) :
    TagCompatible (mergeQueryEquiv base blockCode inputCode)
      (mergeAnswerEquiv base blockCode outputCode) :=
  tagCompatible_of_route (Sum.map id fun _ : P => ())
    (mergeQueryEquiv_index base blockCode inputCode)
    (mergeAnswerEquiv_index base blockCode outputCode)

/-- **Merging a block of interfaces** (deterministic level): the resource is
unchanged, but the whole `P`-block is now addressed through the single coded
interface `Sum.inr ()`. -/
def DependentDDS.mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (system : DependentDDS U (Sum.elim base block)) :
    DependentDDS U (Sum.elim base fun _ : Unit => blockCode) :=
  system.reindex (tagCompatible_mergeBlock base blockCode inputCode outputCode)

/-- The defining equation of the merge at the deterministic level. -/
theorem DependentDDS.flatten_mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (system : DependentDDS U (Sum.elim base block)) :
    (system.mergeBlock base blockCode inputCode outputCode).flatten =
      PFunDDS.DDS.relabel (mergeQueryEquiv base blockCode inputCode)
        (mergeAnswerEquiv base blockCode outputCode) system.flatten :=
  DependentDDS.flatten_reindex _ _

/-- Merging never merges two resources. -/
theorem DependentDDS.mergeBlock_injective (base : Boundary U M)
    (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block) :
    Function.Injective
      (fun system : DependentDDS U (Sum.elim base block) =>
        system.mergeBlock base blockCode inputCode outputCode) :=
  DependentDDS.reindex_injective _

/-- **Merging a block of interfaces** (law level). -/
def DependentPDS.mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (law : DependentPDS U (Sum.elim base block)) :
    DependentPDS U (Sum.elim base fun _ : Unit => blockCode) :=
  DependentPDS.reindex
    (tagCompatible_mergeBlock base blockCode inputCode outputCode) law

/-- The defining equation of the merge at the law level. -/
theorem DependentPDS.flatten_mergeBlock (base : Boundary U M)
    (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (law : DependentPDS U (Sum.elim base block)) :
    DependentPDS.flatten
        (DependentPDS.mergeBlock base blockCode inputCode outputCode law) =
      PFunPDS.relabel (mergeQueryEquiv base blockCode inputCode)
        (mergeAnswerEquiv base blockCode outputCode)
        (DependentPDS.flatten law) :=
  DependentPDS.flatten_reindex _ _

/-- **Merging a block of interfaces** on a normalized law. -/
def DependentPDS.Prob.mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (law : DependentPDS.Prob U (Sum.elim base block)) :
    DependentPDS.Prob U (Sum.elim base fun _ : Unit => blockCode) :=
  DependentPDS.Prob.reindex
    (tagCompatible_mergeBlock base blockCode inputCode outputCode) law

section Quotient

variable [DecidableEq M] [DecidableEq P] [DecidableEq U.Code]

/-- **Merging a block of interfaces** on contextual behavior classes. -/
def DependentRandomSystem.mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (resource : DependentRandomSystem U (Sum.elim base block)) :
    DependentRandomSystem U (Sum.elim base fun _ : Unit => blockCode) :=
  DependentRandomSystem.reindex
    (tagCompatible_mergeBlock base blockCode inputCode outputCode) resource

/-- **Merging a block of interfaces is an isometry of contextual behavior.**
Collapsing a whole block onto one coded interface costs no distinguishing
advantage in either direction: everything the merged boundary can ask, the
unmerged boundary can ask, and conversely. -/
@[simp]
theorem DependentRandomSystem.edist_mergeBlock (base : Boundary U M)
    (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    (left right : DependentRandomSystem U (Sum.elim base block)) :
    edist (DependentRandomSystem.mergeBlock base blockCode inputCode outputCode left)
        (DependentRandomSystem.mergeBlock base blockCode inputCode outputCode right) =
      edist left right :=
  DependentRandomSystem.edist_reindex _ left right

/-- Merging is injective on contextual behavior classes. -/
theorem DependentRandomSystem.mergeBlock_injective (base : Boundary U M)
    (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block) :
    Function.Injective
      (DependentRandomSystem.mergeBlock base blockCode inputCode outputCode :
        DependentRandomSystem U (Sum.elim base block) →
          DependentRandomSystem U (Sum.elim base fun _ : Unit => blockCode)) :=
  DependentRandomSystem.reindex_injective _

end Quotient

/-! ### Merging is not invertible

`TagCompatible` is asymmetric, and the merge is where that bites.  The forward
pair routes every block interface to the single merged interface; the inverse
pair would have to route the merged interface *back* to the block interface of
the query — but the answer equivalence sees only the answer, and the answer's
own block interface is whatever `outputCode` decodes, not the query's. -/

/-- **The inverse of a block merge is never tag-compatible** once the block has
two distinct interfaces that can carry, respectively, a query and an answer.
The obstruction is explicit: the merged answer decoding to block interface
`answerIndex` is legal for *every* merged query, in particular for the merged
image of a block query at `queryIndex`, and the inverse answer equivalence
returns `answerIndex` where tag faithfulness demands `queryIndex`. -/
theorem not_tagCompatible_mergeBlock_symm (base : Boundary U M)
    (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    {answerIndex queryIndex : P} (different : answerIndex ≠ queryIndex)
    (queryValue : U.input (block queryIndex))
    (answerValue : U.output (block answerIndex)) :
    ¬ TagCompatible (mergeQueryEquiv base blockCode inputCode).symm
        (mergeAnswerEquiv base blockCode outputCode).symm := by
  intro compatible
  have key := compatible
    (⟨Sum.inr queryIndex, queryValue⟩ : Query U (Sum.elim base block))
    ⟨Sum.inr (), outputCode.symm ⟨answerIndex, answerValue⟩⟩ rfl
  rw [show (mergeAnswerEquiv base blockCode outputCode).symm
        ⟨Sum.inr (), outputCode.symm ⟨answerIndex, answerValue⟩⟩ =
      (⟨Sum.inr answerIndex, answerValue⟩ :
        FlatAnswer U (Sum.elim base block)) from
      (mergeAnswerEquiv base blockCode outputCode).symm_apply_eq.mpr rfl] at key
  exact different (Sum.inr.inj key)

/-- **`TagCompatible` is not a symmetric condition**, and therefore `reindex`
is not invertible in general.  The merge exhibits both halves at once: the
forward pair is tag-compatible and the inverse pair is not.

Where the asymmetry comes from: `TagCompatible queryE answerE` only asks
`answerE` to *reproduce* the tag that `queryE` has already chosen, so a query
equivalence that forgets interfaces — as the merge does, sending the whole
`P`-block to `()` — is free, since the answer equivalence forgets them the
same way.  The inverse condition asks `answerE.symm` to *recover* the block
interface of the query from the answer alone, and an answer at the merged
interface carries no record of which block interface asked for it. -/
theorem tagCompatible_not_symmetric (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    {answerIndex queryIndex : P} (different : answerIndex ≠ queryIndex)
    (queryValue : U.input (block queryIndex))
    (answerValue : U.output (block answerIndex)) :
    TagCompatible (mergeQueryEquiv base blockCode inputCode)
        (mergeAnswerEquiv base blockCode outputCode) ∧
      ¬ TagCompatible (mergeQueryEquiv base blockCode inputCode).symm
        (mergeAnswerEquiv base blockCode outputCode).symm :=
  ⟨tagCompatible_mergeBlock base blockCode inputCode outputCode,
    not_tagCompatible_mergeBlock_symm base blockCode inputCode outputCode
      different queryValue answerValue⟩

/-- **The wrong-side merged resource.**  It accepts exactly the one-query
history consisting of the merged image of the block query at `queryIndex`, and
answers it with the block answer at `answerIndex`.  At the merged boundary this
is a perfectly legal resource — the merged interface is a *single* interface,
so tag faithfulness there says nothing about which block interface the answer
decodes to — and that is exactly why it is outside the image of the merge. -/
def wrongSideWitness (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    {answerIndex queryIndex : P}
    (queryValue : U.input (block queryIndex))
    (answerValue : U.output (block answerIndex)) :
    DependentDDS U (Sum.elim base fun _ : Unit => blockCode) where
  domain :=
    {[mergeQueryEquiv base blockCode inputCode ⟨Sum.inr queryIndex, queryValue⟩]}
  empty_not_mem := by simp
  prefix_closed := by
    rintro left right ⟨tail, htail⟩ nonempty member
    rw [Set.mem_singleton_iff] at member
    subst member
    cases left with
    | nil => exact absurd rfl nonempty
    | cons head rest => simp_all
  output := fun history nonempty member =>
    cast
      (congrArg
        (fun interface =>
          U.output (Sum.elim base (fun _ : Unit => blockCode) interface))
        (show (Sum.inr () : M ⊕ Unit) = (history.getLast nonempty).1 from by
          rw [Set.mem_singleton_iff] at member
          subst member
          rfl))
      (outputCode.symm ⟨answerIndex, answerValue⟩)

/-- The wrong-side resource answers its one admitted history with the block
answer at `answerIndex`, coded into the merged interface's alphabet. -/
theorem wrongSideWitness_output (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    {answerIndex queryIndex : P}
    (queryValue : U.input (block queryIndex))
    (answerValue : U.output (block answerIndex))
    (nonempty :
      [mergeQueryEquiv base blockCode inputCode ⟨Sum.inr queryIndex, queryValue⟩] ≠ [])
    (member :
      [mergeQueryEquiv base blockCode inputCode ⟨Sum.inr queryIndex, queryValue⟩] ∈
        (wrongSideWitness base blockCode inputCode outputCode
          queryValue answerValue).domain) :
    (wrongSideWitness base blockCode inputCode outputCode queryValue answerValue).output
        [mergeQueryEquiv base blockCode inputCode ⟨Sum.inr queryIndex, queryValue⟩]
        nonempty member =
      outputCode.symm ⟨answerIndex, answerValue⟩ :=
  rfl

/-- **The wrong-side resource is outside the image of the merge.**  Pulling its
flat presentation back along the inverse relabelling is not tag-faithful: the
pulled-back system answers the block query at `queryIndex` with an answer
tagged `queryIndex ≠ answerIndex`. -/
theorem not_tagFaithful_relabel_symm_wrongSideWitness (base : Boundary U M)
    (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    {answerIndex queryIndex : P} (different : answerIndex ≠ queryIndex)
    (queryValue : U.input (block queryIndex))
    (answerValue : U.output (block answerIndex)) :
    ¬ DependentDDS.TagFaithful
      (PFunDDS.DDS.relabel (mergeQueryEquiv base blockCode inputCode).symm
        (mergeAnswerEquiv base blockCode outputCode).symm
        (wrongSideWitness base blockCode inputCode outputCode
          queryValue answerValue).flatten) := by
  intro faithful
  have key := faithful
    [(⟨Sum.inr queryIndex, queryValue⟩ : Query U (Sum.elim base block))] rfl
  have reduce : PFunDDS.output
      (PFunDDS.DDS.relabel (mergeQueryEquiv base blockCode inputCode).symm
        (mergeAnswerEquiv base blockCode outputCode).symm
        (wrongSideWitness base blockCode inputCode outputCode
          queryValue answerValue).flatten)
      [(⟨Sum.inr queryIndex, queryValue⟩ : Query U (Sum.elim base block))] rfl =
      (⟨Sum.inr answerIndex, answerValue⟩ :
        FlatAnswer U (Sum.elim base block)) := by
    show (mergeAnswerEquiv base blockCode outputCode).symm
      ⟨Sum.inr (), outputCode.symm ⟨answerIndex, answerValue⟩⟩ = _
    exact (mergeAnswerEquiv base blockCode outputCode).symm_apply_eq.mpr rfl
  exact different (Sum.inr.inj ((congrArg Sigma.fst reduce).symm.trans key))

/-- **Merging a block is injective but not surjective.**  Its image is exactly
the merged-boundary resources whose answers, decoded through `outputCode`, sit
at the same block interface as the decoded query — the merged boundary itself
imposes no such constraint, so the inclusion is strict as soon as the block has
two distinct interfaces that can carry a query and an answer. -/
theorem not_surjective_mergeBlock (base : Boundary U M) (blockCode : U.Code)
    (inputCode : U.input blockCode ≃ Query U block)
    (outputCode : U.output blockCode ≃ FlatAnswer U block)
    {answerIndex queryIndex : P} (different : answerIndex ≠ queryIndex)
    (queryValue : U.input (block queryIndex))
    (answerValue : U.output (block answerIndex)) :
    ¬ Function.Surjective
      (fun system : DependentDDS U (Sum.elim base block) =>
        system.mergeBlock base blockCode inputCode outputCode) := by
  intro surjective
  refine not_tagFaithful_relabel_symm_wrongSideWitness base blockCode inputCode
    outputCode different queryValue answerValue ?_
  refine (DependentDDS.exists_reindex_eq_iff
    (tagCompatible_mergeBlock base blockCode inputCode outputCode) _).mp ?_
  exact surjective _

/-! ### The binary corollary: merging two interfaces into one -/

section MergeTwo

variable [HasSumCode U]

/-- The two-interface block: `Sum.inl ()` carries `codeA`, `Sum.inr ()` carries
`codeB`. -/
abbrev twoBlock (codeA codeB : U.Code) : Boundary U (Unit ⊕ Unit) :=
  Sum.elim (fun _ => codeA) fun _ => codeB

/-- The alphabet coding supplied by `HasSumCode` *is* a block coding of the
two-interface block: the sum code's input alphabet carries the whole
two-interface query alphabet. -/
def twoBlockInputCode (codeA codeB : U.Code) :
    U.input (HasSumCode.sumCode codeA codeB) ≃ Query U (twoBlock codeA codeB) :=
  (HasSumCode.inputEquiv codeA codeB).trans
    ((Equiv.sumCongr (Equiv.uniqueSigma fun _ : Unit => U.input codeA).symm
        (Equiv.uniqueSigma fun _ : Unit => U.input codeB).symm).trans
      (Equiv.sumSigmaDistrib fun interface : Unit ⊕ Unit =>
        U.input (twoBlock codeA codeB interface)).symm)

/-- The output half of the same coding. -/
def twoBlockOutputCode (codeA codeB : U.Code) :
    U.output (HasSumCode.sumCode codeA codeB) ≃
      FlatAnswer U (twoBlock codeA codeB) :=
  (HasSumCode.outputEquiv codeA codeB).trans
    ((Equiv.sumCongr (Equiv.uniqueSigma fun _ : Unit => U.output codeA).symm
        (Equiv.uniqueSigma fun _ : Unit => U.output codeB).symm).trans
      (Equiv.sumSigmaDistrib fun interface : Unit ⊕ Unit =>
        U.output (twoBlock codeA codeB interface)).symm)

/-- **The `HasSumCode` coding is exactly the cost of merging two interfaces
into one**: collapsing the two-interface block onto the single interface
carrying `HasSumCode.sumCode codeA codeB` is a tag-compatible re-indexing. -/
theorem tagCompatible_mergeTwo (base : Boundary U M) (codeA codeB : U.Code) :
    TagCompatible
      (mergeQueryEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockInputCode codeA codeB))
      (mergeAnswerEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockOutputCode codeA codeB)) :=
  tagCompatible_mergeBlock base (HasSumCode.sumCode codeA codeB)
    (twoBlockInputCode codeA codeB) (twoBlockOutputCode codeA codeB)

/-- **Merging two interfaces into one** (deterministic level). -/
def DependentDDS.mergeTwo (base : Boundary U M) (codeA codeB : U.Code)
    (system : DependentDDS U (Sum.elim base (twoBlock codeA codeB))) :
    DependentDDS U
      (Sum.elim base fun _ : Unit => HasSumCode.sumCode codeA codeB) :=
  system.mergeBlock base (HasSumCode.sumCode codeA codeB)
    (twoBlockInputCode codeA codeB) (twoBlockOutputCode codeA codeB)

/-- **Merging two interfaces into one** on contextual behavior classes. -/
def DependentRandomSystem.mergeTwo [DecidableEq M] [DecidableEq U.Code]
    (base : Boundary U M) (codeA codeB : U.Code)
    (resource : DependentRandomSystem U (Sum.elim base (twoBlock codeA codeB))) :
    DependentRandomSystem U
      (Sum.elim base fun _ : Unit => HasSumCode.sumCode codeA codeB) :=
  DependentRandomSystem.mergeBlock base (HasSumCode.sumCode codeA codeB)
    (twoBlockInputCode codeA codeB) (twoBlockOutputCode codeA codeB) resource

/-- **Merging two interfaces into one is an isometry of contextual behavior.**
The alphabet coding `HasSumCode` supplies is all that the merge costs: no
distinguishing advantage is created or destroyed by addressing the two
interfaces through one sum-coded interface. -/
@[simp]
theorem DependentRandomSystem.edist_mergeTwo [DecidableEq M] [DecidableEq U.Code]
    (base : Boundary U M) (codeA codeB : U.Code)
    (left right : DependentRandomSystem U (Sum.elim base (twoBlock codeA codeB))) :
    edist (DependentRandomSystem.mergeTwo base codeA codeB left)
        (DependentRandomSystem.mergeTwo base codeA codeB right) =
      edist left right :=
  DependentRandomSystem.edist_mergeBlock _ _ _ _ left right

end MergeTwo

end MergeBlock

end

end RandomSystems.CR18.TypedResource
