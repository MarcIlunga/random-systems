/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedTensor

/-!
# Bijective interface re-indexing

`TypedTensor.lean` builds the general re-indexing calculus: a tag-compatible
pair of alphabet equivalences acts on every layer of the tower, and the action
is an isometry (`DependentRandomSystem.edist_reindex`).  Two of its instances
are already in place — the *split* of an interface set along a connection, and
the *merge* of a block of interfaces into one.  The merge is deliberately
one-way (`not_surjective_mergeBlock`).

This module supplies the third and simplest instance, the one that IS
invertible: a **bijection of the interface set**.  Nothing about the resource
changes; only the names of its interfaces do.  Concretely, for `relabel : K ≃ K'`
the boundary travels as `boundary ∘ relabel.symm`, both alphabet equivalences
relocate along the single route `relabel`, and — because `relabel.symm` is
again a route — the *inverse* pair is tag-compatible too
(`tagCompatible_relabelInterfaces_symm`).  That two-sidedness is what makes
the isometry `edist_relabelInterfaces` an **equation in both directions**
rather than the one-way bound a merge has to settle for.

The material is kept out of `TypedTensor.lean` on purpose: that module owns the
non-invertible re-indexings (split, merge) and its statement of intent is that
they may be used forward only.  This one may be used in both directions, and
saying so in a separate module keeps the two regimes apart.
-/

namespace RandomSystems.CR18.TypedResource

open RandomSystems (Dist)

noncomputable section

universe i u v c

variable {U : SignatureUniverse}

section InterfaceRelabel

variable {K K' : Type*}

/-- The boundary carried across a bijective re-indexing: the interface named
`k'` on the far side provides whatever `relabel.symm k'` provided here. -/
abbrev relabelBoundary (relabel : K ≃ K') (boundary : Boundary U K) :
    Boundary U K' :=
  fun interface => boundary (relabel.symm interface)

theorem relabelBoundary_apply (relabel : K ≃ K') (boundary : Boundary U K)
    (interface : K) :
    relabelBoundary relabel boundary (relabel interface) = boundary interface :=
  congrArg boundary (relabel.symm_apply_apply interface)

/-- Queries travel with their interface.  Built exactly as the split's
(`ResourceSystem.splitQueryEquiv`): cast the fibre along
`boundary (relabel.symm (relabel k)) = boundary k`, then re-index the sigma. -/
def relabelQueryEquiv (relabel : K ≃ K') (boundary : Boundary U K) :
    Query U boundary ≃ Query U (relabelBoundary relabel boundary) :=
  (Equiv.sigmaCongrRight fun interface =>
      Equiv.cast (congrArg U.input
        (relabelBoundary_apply relabel boundary interface).symm)).trans
    (Equiv.sigmaCongrLeft
      (β := fun interface => U.input (relabelBoundary relabel boundary interface))
      relabel)

/-- Flat answers travel the same way. -/
def relabelAnswerEquiv (relabel : K ≃ K') (boundary : Boundary U K) :
    FlatAnswer U boundary ≃ FlatAnswer U (relabelBoundary relabel boundary) :=
  (Equiv.sigmaCongrRight fun interface =>
      Equiv.cast (congrArg U.output
        (relabelBoundary_apply relabel boundary interface).symm)).trans
    (Equiv.sigmaCongrLeft
      (β := fun interface => U.output (relabelBoundary relabel boundary interface))
      relabel)

@[simp]
theorem relabelQueryEquiv_index (relabel : K ≃ K') (boundary : Boundary U K)
    (query : Query U boundary) :
    (relabelQueryEquiv relabel boundary query).1 = relabel query.1 :=
  rfl

@[simp]
theorem relabelAnswerEquiv_index (relabel : K ≃ K') (boundary : Boundary U K)
    (answer : FlatAnswer U boundary) :
    (relabelAnswerEquiv relabel boundary answer).1 = relabel answer.1 :=
  rfl

@[simp]
theorem relabelQueryEquiv_symm_index (relabel : K ≃ K') (boundary : Boundary U K)
    (query : Query U (relabelBoundary relabel boundary)) :
    ((relabelQueryEquiv relabel boundary).symm query).1 = relabel.symm query.1 := by
  have route := relabelQueryEquiv_index relabel boundary
    ((relabelQueryEquiv relabel boundary).symm query)
  rw [Equiv.apply_symm_apply] at route
  rw [route, Equiv.symm_apply_apply]

@[simp]
theorem relabelAnswerEquiv_symm_index (relabel : K ≃ K')
    (boundary : Boundary U K)
    (answer : FlatAnswer U (relabelBoundary relabel boundary)) :
    ((relabelAnswerEquiv relabel boundary).symm answer).1 =
      relabel.symm answer.1 := by
  have route := relabelAnswerEquiv_index relabel boundary
    ((relabelAnswerEquiv relabel boundary).symm answer)
  rw [Equiv.apply_symm_apply] at route
  rw [route, Equiv.symm_apply_apply]

/-- **A bijective re-indexing is tag-compatible**, by the route criterion at
`route = relabel`. -/
theorem tagCompatible_relabelInterfaces (relabel : K ≃ K')
    (boundary : Boundary U K) :
    TagCompatible (relabelQueryEquiv relabel boundary)
      (relabelAnswerEquiv relabel boundary) :=
  tagCompatible_of_route relabel (fun _ => rfl) fun _ => rfl

/-- …and so is its inverse, at `route = relabel.symm`.  This is what a merge
does **not** have (`not_tagCompatible_mergeBlock_symm`), and it is the whole
difference between a re-naming and a genuine loss of addressing. -/
theorem tagCompatible_relabelInterfaces_symm (relabel : K ≃ K')
    (boundary : Boundary U K) :
    TagCompatible (relabelQueryEquiv relabel boundary).symm
      (relabelAnswerEquiv relabel boundary).symm :=
  tagCompatible_of_route relabel.symm
    (relabelQueryEquiv_symm_index relabel boundary)
    (relabelAnswerEquiv_symm_index relabel boundary)

end InterfaceRelabel

/-! ## The bundled carrier -/

namespace Resource

variable {K K' : Type*}
variable [DecidableEq K] [DecidableEq K'] [DecidableEq U.Code]

/-- **Re-indexing a bundled resource along a bijection of its interface set.**
The same resource, its interfaces renamed: the boundary travels along
`relabel.symm` and the behavior along the tag-compatible pair. -/
def relabelInterfaces (relabel : K ≃ K') (resource : Resource K U) :
    Resource K' U :=
  ⟨relabelBoundary relabel resource.boundary,
    DependentRandomSystem.reindex
      (tagCompatible_relabelInterfaces relabel resource.boundary)
      resource.system⟩

@[simp]
theorem relabelInterfaces_boundary (relabel : K ≃ K') (resource : Resource K U) :
    (relabelInterfaces relabel resource).boundary =
      relabelBoundary relabel resource.boundary :=
  rfl

omit [DecidableEq K] [DecidableEq K'] [DecidableEq U.Code] in
/-- Two boundaries agree after a bijective re-indexing exactly when they agree
before it. -/
theorem relabelBoundary_inj (relabel : K ≃ K') {left right : Boundary U K}
    (same : relabelBoundary relabel left = relabelBoundary relabel right) :
    left = right := by
  funext interface
  have step := congrFun same (relabel interface)
  simp only [relabelBoundary, Equiv.symm_apply_apply] at step
  exact step

/-- **Bijective re-indexing is an isometry of the bundled carrier** — an
equality, not a bound, and in both directions: the boundary halves are
identified by `relabelBoundary_inj`, so a pair at `⊤` stays at `⊤`, and inside
one boundary the fibre statement is `DependentRandomSystem.edist_reindex`. -/
@[simp]
theorem edist_relabelInterfaces (relabel : K ≃ K') (left right : Resource K U) :
    edist (relabelInterfaces relabel left) (relabelInterfaces relabel right) =
      edist left right := by
  rcases left with ⟨leftBoundary, leftSystem⟩
  rcases right with ⟨rightBoundary, rightSystem⟩
  by_cases same : leftBoundary = rightBoundary
  · subst same
    show edist (Resource.mk (relabelBoundary relabel leftBoundary) _)
        (Resource.mk (relabelBoundary relabel leftBoundary) _) = _
    rw [Resource.edist_same, Resource.edist_same,
      DependentRandomSystem.edist_reindex]
  · have different : relabelBoundary relabel leftBoundary ≠
        relabelBoundary relabel rightBoundary :=
      fun collapse => same (relabelBoundary_inj relabel collapse)
    show edist (Resource.mk (relabelBoundary relabel leftBoundary) _)
        (Resource.mk (relabelBoundary relabel rightBoundary) _) = _
    rw [Resource.edist_ne different, Resource.edist_ne same]

end Resource

end

end RandomSystems.CR18.TypedResource
