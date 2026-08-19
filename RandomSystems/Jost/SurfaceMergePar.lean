/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceShuffle

/-!
# The authoring surface, part 6: a connection into one factor

Part 5 gave the author `ResourceSystem.reindex`, the rename that reconciles the
two spellings a paper treats as one interface set.  This module cashes the
first law that needs it:

```
[R, T] ••[γ‖J]  =  reindex outerShuffle [R ••[γ], T]
```

*a connection landing inside the left component merges that component and
leaves the other one untouched* — Jost Prop. 2.2.3 (2)'s reading of `π^γ [R,Q]
= [π^γ R, Q]` at the level of the re-addressing, one step below
`Converter.attachAt_par_left`, which is its unary-converter case.  The two
sides carry the same layout at every interface; what the theorem says is that
they carry the same *behavior*.

## How it is proved, and what is reusable

`mergeAlong` and `∥` are both re-indexings of the same kernel object, so the
proof is a calculation in one calculus and every step of it is stated
separately:

* `PFunDDS.par_relabel_left` (`TypedTensorShuffle.lean`) — renaming one
  component's alphabets commutes with the tagged parallel.  That is the flat
  fact everything here rests on; it is consumed, not reproved.
* `tensorLeftQueryEquiv` / `tagCompatible_tensorLeft` /
  `DependentDDS.tensor_reindex_left` and its `DependentPDS` and
  `DependentRandomSystem` lifts — *re-index one factor, then compose* is
  *compose, then re-index*.
* `tagCompatible_trans`, `DependentDDS.reindex_reindex` and its lifts —
  re-indexing is functorial, so a chain of them is one of them.
* `sigmaReindex` — the same re-indexing of a sigma type as
  `Equiv.sigmaCongrLeft`, but with an inverse that *computes*: mathlib's
  transports along `e (e.symm b) = b`, which is stuck for an opaque `e`, and a
  connection's `split` is opaque.  With it, both sides of the final comparison
  reduce and the six fibre goals are `rfl`.
* `Resource.reindex_congr` — two re-indexings of one behavior that land at the
  same layout and relocate every query and answer the same way agree.  This is
  the shape in which any further `mergeAlong`/`∥`/`reindex` identity should be
  reduced to a finite check.

`ResourceSystem.mergeAlong_eq_reindex` is the entry point: it presents
`mergeAlong` as the single re-indexing `mergeAlongQueryEquiv` /
`mergeAlongAnswerEquiv`, which is the form the calculus consumes.

**The split.**  `Jost/SurfaceCarrier.lean` builds `mergeAlong` from
`splitLayout`, `splitQueryEquiv`, `splitAnswerEquiv` and `tagCompatible_split`;
they are public there precisely so that this module and
`Jost/SurfaceMergeLocality.lean` can name the re-indexing they describe.
-/

namespace RandomSystems.CR18.TypedResource

open RandomSystems (Dist)

universe i j c u v

variable {U : SignatureUniverse.{c, u, v}}

/-- **A sigma type re-indexed along a bijection of its index**, in a form in
which *both* directions compute: each is a `cast` along a fibre equation the
caller supplies, so on a concrete index — where the two fibres are the same
type — the cast collapses.

The equivalence `Equiv.sigmaCongrLeft` builds is the same map, but its inverse
transports along `relocate (relocate.symm b) = b`, which is stuck whenever
`relocate` is an opaque bijection; that is exactly the situation of a
connection's `split`. -/
def sigmaReindex {A B : Type*} {F : A → Type u} {G : B → Type u}
    (relocate : A ≃ B) (forward : ∀ a, F a = G (relocate a))
    (backward : ∀ b, G b = F (relocate.symm b)) :
    (Σ a, F a) ≃ (Σ b, G b) where
  toFun index := ⟨relocate index.1, cast (forward index.1) index.2⟩
  invFun index := ⟨relocate.symm index.1, cast (backward index.1) index.2⟩
  left_inv index :=
    Sigma.ext (relocate.symm_apply_apply index.1)
      ((cast_heq _ _).trans (cast_heq _ _))
  right_inv index :=
    Sigma.ext (relocate.apply_symm_apply index.1)
      ((cast_heq _ _).trans (cast_heq _ _))

/-! ## Re-indexing is functorial -/

section Functorial

variable {K K' K'' : Type*} {boundary : Boundary U K} {boundary' : Boundary U K'}
  {boundary'' : Boundary U K''}
  {queryE : Query U boundary ≃ Query U boundary'}
  {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
  {queryE' : Query U boundary' ≃ Query U boundary''}
  {answerE' : FlatAnswer U boundary' ≃ FlatAnswer U boundary''}

/-- **Tag compatibility composes**: if each of two re-addressings reproduces
the tag its query equivalence chose, so does their composite. -/
theorem tagCompatible_trans (compatible : TagCompatible queryE answerE)
    (compatible' : TagCompatible queryE' answerE') :
    TagCompatible (queryE.trans queryE') (answerE.trans answerE') :=
  fun query answer sameTag =>
    compatible' query (answerE answer) (compatible (queryE'.symm query) answer sameTag)

/-- **Consecutive re-indexings compose** (deterministic level): re-addressing
twice is re-addressing once along the composed alphabet equivalences. -/
theorem DependentDDS.reindex_reindex (compatible : TagCompatible queryE answerE)
    (compatible' : TagCompatible queryE' answerE')
    (composed : TagCompatible (queryE.trans queryE') (answerE.trans answerE'))
    (system : DependentDDS U boundary) :
    (system.reindex compatible).reindex compatible' = system.reindex composed := by
  apply DependentDDS.flatten_injective
  rw [DependentDDS.flatten_reindex, DependentDDS.flatten_reindex,
    DependentDDS.flatten_reindex, PFunDDS.DDS.relabel_relabel]

/-- Consecutive re-indexings compose (law level). -/
theorem DependentPDS.reindex_reindex (compatible : TagCompatible queryE answerE)
    (compatible' : TagCompatible queryE' answerE')
    (composed : TagCompatible (queryE.trans queryE') (answerE.trans answerE'))
    (law : DependentPDS U boundary) :
    DependentPDS.reindex compatible' (DependentPDS.reindex compatible law) =
      DependentPDS.reindex composed law := by
  unfold DependentPDS.reindex
  rw [Dist.fTransform_comp]
  exact congrArg (fun step => Dist.fTransform step law)
    (funext fun system =>
      DependentDDS.reindex_reindex compatible compatible' composed system)

variable [DecidableEq K] [DecidableEq K'] [DecidableEq K''] [DecidableEq U.Code]

/-- **A re-indexing depends only on where it sends queries and answers.**  Two
tag-compatible pairs with the same alphabet equivalences act identically — the
compatibility proofs are proofs. -/
theorem DependentRandomSystem.reindex_congr_equiv
    {queryE'' : Query U boundary ≃ Query U boundary'}
    {answerE'' : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (compatible'' : TagCompatible queryE'' answerE'')
    (sameQuery : queryE = queryE'') (sameAnswer : answerE = answerE'')
    (resource : DependentRandomSystem U boundary) :
    DependentRandomSystem.reindex compatible resource =
      DependentRandomSystem.reindex compatible'' resource := by
  subst sameQuery
  subst sameAnswer
  rfl

/-- Consecutive re-indexings compose on contextual behavior classes. -/
theorem DependentRandomSystem.reindex_reindex
    (compatible : TagCompatible queryE answerE)
    (compatible' : TagCompatible queryE' answerE')
    (composed : TagCompatible (queryE.trans queryE') (answerE.trans answerE'))
    (resource : DependentRandomSystem U boundary) :
    DependentRandomSystem.reindex compatible'
        (DependentRandomSystem.reindex compatible resource) =
      DependentRandomSystem.reindex composed resource := by
  induction resource using Quotient.inductionOn with
  | _ law =>
      show DependentRandomSystem.ofProb
          (DependentPDS.Prob.reindex compatible'
            (DependentPDS.Prob.reindex compatible law)) =
        DependentRandomSystem.ofProb (DependentPDS.Prob.reindex composed law)
      exact congrArg DependentRandomSystem.ofProb (Subtype.ext
        (DependentPDS.reindex_reindex compatible compatible' composed law.val))

end Functorial

/-! ## Re-indexing one factor of a tensor -/

section TensorLeft

variable {I : Type i} {I' : Type*} {J : Type j} {left : Boundary U I}
  {left' : Boundary U I'} {right : Boundary U J}

/-- **A left-factor re-indexing, read on the composite.**  Queries of
`Sum.elim left right` split into the two components' (`tensorQueryEquiv`); the
re-indexing acts on the left summand and the identity on the right, and the
two components are re-assembled at the new left boundary. -/
def tensorLeftQueryEquiv (queryE : Query U left ≃ Query U left')
    (right : Boundary U J) :
    Query U (Sum.elim left right) ≃ Query U (Sum.elim left' right) :=
  (tensorQueryEquiv left right).trans
    ((Equiv.sumCongr queryE (Equiv.refl (Query U right))).trans
      (tensorQueryEquiv left' right).symm)

/-- Flat answers travel the same way. -/
def tensorLeftAnswerEquiv (answerE : FlatAnswer U left ≃ FlatAnswer U left')
    (right : Boundary U J) :
    FlatAnswer U (Sum.elim left right) ≃ FlatAnswer U (Sum.elim left' right) :=
  (tensorAnswerEquiv left right).trans
    ((Equiv.sumCongr answerE (Equiv.refl (FlatAnswer U right))).trans
      (tensorAnswerEquiv left' right).symm)

/-- **A tag-compatible re-indexing stays tag-compatible on a composite.**  A
right-tagged query is answered right-tagged by the identity half; a left-tagged
one is answered by the component pair, which reproduces the tag by hypothesis.
-/
theorem tagCompatible_tensorLeft
    {queryE : Query U left ≃ Query U left'}
    {answerE : FlatAnswer U left ≃ FlatAnswer U left'}
    (compatible : TagCompatible queryE answerE) :
    TagCompatible (tensorLeftQueryEquiv queryE right)
      (tensorLeftAnswerEquiv answerE right) := by
  rintro ⟨index, value⟩ ⟨answerIndex, answerValue⟩ sameTag
  cases index with
  | inl interface =>
      have route : (Sum.inl (queryE.symm ⟨interface, value⟩).1 : I ⊕ J) = answerIndex :=
        sameTag.symm
      cases answerIndex with
      | inl answerInterface =>
          have step : (answerE ⟨answerInterface, answerValue⟩).1 = interface :=
            compatible ⟨interface, value⟩ ⟨answerInterface, answerValue⟩
              (Sum.inl.inj route).symm
          show (Sum.inl (answerE ⟨answerInterface, answerValue⟩).1 : I' ⊕ J) = _
          rw [step]
      | inr answerInterface => exact absurd route (by simp)
  | inr interface =>
      have route : (Sum.inr interface : I ⊕ J) = answerIndex := sameTag.symm
      cases answerIndex with
      | inl answerInterface => exact absurd route (by simp)
      | inr answerInterface =>
          show (Sum.inr answerInterface : I' ⊕ J) = Sum.inr interface
          rw [Sum.inr.inj route]

/-- **Re-indexing one factor and composing is composing and re-indexing**
(deterministic level).  Both sides are the same tagged parallel of the two
flattened components, relabelled along the same alphabet equivalence: the
composite's own re-association cancels against itself. -/
theorem DependentDDS.tensor_reindex_left
    {queryE : Query U left ≃ Query U left'}
    {answerE : FlatAnswer U left ≃ FlatAnswer U left'}
    (compatible : TagCompatible queryE answerE)
    (composite : TagCompatible (tensorLeftQueryEquiv queryE right)
      (tensorLeftAnswerEquiv answerE right))
    (leftSystem : DependentDDS U left) (rightSystem : DependentDDS U right) :
    (leftSystem.reindex compatible).tensor rightSystem =
      (leftSystem.tensor rightSystem).reindex composite := by
  apply DependentDDS.flatten_injective
  rw [DependentDDS.flatten_tensor, DependentDDS.flatten_reindex,
    DependentDDS.flatten_reindex, DependentDDS.flatten_tensor,
    PFunDDS.par_relabel_left, PFunDDS.DDS.relabel_relabel,
    PFunDDS.DDS.relabel_relabel]
  unfold tensorLeftQueryEquiv tensorLeftAnswerEquiv
  simp only [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]

/-- Re-indexing one factor and composing is composing and re-indexing (law
level): the independent product is pushed forward componentwise, so the
deterministic identity transports through both `fTransform`s. -/
theorem DependentPDS.tensor_reindex_left
    {queryE : Query U left ≃ Query U left'}
    {answerE : FlatAnswer U left ≃ FlatAnswer U left'}
    (compatible : TagCompatible queryE answerE)
    (composite : TagCompatible (tensorLeftQueryEquiv queryE right)
      (tensorLeftAnswerEquiv answerE right))
    (leftLaw : DependentPDS U left) (rightLaw : DependentPDS U right) :
    DependentPDS.tensor (DependentPDS.reindex compatible leftLaw) rightLaw =
      DependentPDS.reindex composite (DependentPDS.tensor leftLaw rightLaw) := by
  have product : Dist.prod
        (Dist.fTransform
          (fun system : DependentDDS U left => system.reindex compatible) leftLaw)
        rightLaw =
      Dist.fTransform
        (fun pair : DependentDDS U left × DependentDDS U right =>
          (pair.1.reindex compatible, pair.2)) (Dist.prod leftLaw rightLaw) := by
    rw [Dist.pushforward_product_eq_product_pushforwards
      (fun system : DependentDDS U left => system.reindex compatible)
      (fun system : DependentDDS U right => system) leftLaw rightLaw]
    exact congrArg (Dist.prod _) (Dist.fTransform_id rightLaw).symm
  unfold DependentPDS.tensor DependentPDS.reindex
  rw [product, Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg (fun step => Dist.fTransform step (Dist.prod leftLaw rightLaw))
    (funext fun pair =>
      DependentDDS.tensor_reindex_left compatible composite pair.1 pair.2)

variable [DecidableEq I] [DecidableEq I'] [DecidableEq J] [DecidableEq U.Code]

/-- Re-indexing one factor and composing is composing and re-indexing, on
contextual behavior classes. -/
theorem DependentRandomSystem.tensor_reindex_left
    {queryE : Query U left ≃ Query U left'}
    {answerE : FlatAnswer U left ≃ FlatAnswer U left'}
    (compatible : TagCompatible queryE answerE)
    (composite : TagCompatible (tensorLeftQueryEquiv queryE right)
      (tensorLeftAnswerEquiv answerE right))
    (leftClass : DependentRandomSystem U left)
    (rightClass : DependentRandomSystem U right) :
    DependentRandomSystem.tensor
        (DependentRandomSystem.reindex compatible leftClass) rightClass =
      DependentRandomSystem.reindex composite
        (DependentRandomSystem.tensor leftClass rightClass) := by
  induction leftClass using Quotient.inductionOn with
  | _ leftLaw =>
      induction rightClass using Quotient.inductionOn with
      | _ rightLaw =>
          show DependentRandomSystem.ofProb
              (DependentPDS.Prob.tensor
                (DependentPDS.Prob.reindex compatible leftLaw) rightLaw) =
            DependentRandomSystem.ofProb (DependentPDS.Prob.reindex composite
              (DependentPDS.Prob.tensor leftLaw rightLaw))
          exact congrArg DependentRandomSystem.ofProb (Subtype.ext
            (DependentPDS.tensor_reindex_left compatible composite
              leftLaw.val rightLaw.val))

end TensorLeft

/-! ## A bijective interface re-indexing, in computing form -/

section RelabelReindex

variable {K K' : Type*} (relabel : K ≃ K') (boundary : Boundary U K)

/-- `relabelQueryEquiv` with a computing inverse (`sigmaReindex`): the backward
fibre equation is `rfl`, because `relabelBoundary` is *defined* by composing
with `relabel.symm`. -/
def relabelQueryReindex :
    Query U boundary ≃ Query U (relabelBoundary relabel boundary) :=
  sigmaReindex relabel
    (fun interface =>
      congrArg U.input (relabelBoundary_apply relabel boundary interface).symm)
    fun _ => rfl

/-- `relabelAnswerEquiv` with a computing inverse. -/
def relabelAnswerReindex :
    FlatAnswer U boundary ≃ FlatAnswer U (relabelBoundary relabel boundary) :=
  sigmaReindex relabel
    (fun interface =>
      congrArg U.output (relabelBoundary_apply relabel boundary interface).symm)
    fun _ => rfl

theorem relabelQueryEquiv_eq :
    relabelQueryEquiv relabel boundary = relabelQueryReindex relabel boundary :=
  Equiv.ext fun _ => rfl

theorem relabelAnswerEquiv_eq :
    relabelAnswerEquiv relabel boundary = relabelAnswerReindex relabel boundary :=
  Equiv.ext fun _ => rfl

theorem tagCompatible_relabelReindex :
    TagCompatible (relabelQueryReindex relabel boundary)
      (relabelAnswerReindex relabel boundary) :=
  (relabelQueryEquiv_eq relabel boundary) ▸ (relabelAnswerEquiv_eq relabel boundary) ▸
    tagCompatible_relabelInterfaces relabel boundary

end RelabelReindex

/-! ## Two re-indexings that land at the same place agree -/

/-- **A resource is determined by where its re-indexing sends queries and
answers.**  Two re-indexings of one behavior that land at the same boundary and
relocate every query and every answer the same way produce the same resource —
the tag-compatibility proofs never enter, being proofs. -/
theorem Resource.reindex_congr {K K' : Type*}
    [DecidableEq K] [DecidableEq K'] [DecidableEq U.Code]
    {boundary : Boundary U K} {target target' : Boundary U K'}
    {queryE : Query U boundary ≃ Query U target}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U target}
    {queryE' : Query U boundary ≃ Query U target'}
    {answerE' : FlatAnswer U boundary ≃ FlatAnswer U target'}
    (compatible : TagCompatible queryE answerE)
    (compatible' : TagCompatible queryE' answerE')
    (sameTarget : target = target')
    (sameQuery : ∀ (interface : K') (value : U.input (target' interface)),
      queryE'.symm ⟨interface, value⟩ =
        queryE.symm ⟨interface, cast (congrArg (fun b : Boundary U K' =>
          U.input (b interface)) sameTarget.symm) value⟩)
    (sameAnswer : ∀ (interface : K') (value : U.output (target' interface)),
      answerE'.symm ⟨interface, value⟩ =
        answerE.symm ⟨interface, cast (congrArg (fun b : Boundary U K' =>
          U.output (b interface)) sameTarget.symm) value⟩)
    (system : DependentRandomSystem U boundary) :
    (⟨target, DependentRandomSystem.reindex compatible system⟩ : Resource K' U) =
      ⟨target', DependentRandomSystem.reindex compatible' system⟩ := by
  subst sameTarget
  have queryInverse : queryE.symm = queryE'.symm :=
    Equiv.ext fun query => (sameQuery query.1 query.2).symm
  have answerInverse : answerE.symm = answerE'.symm :=
    Equiv.ext fun answer => (sameAnswer answer.1 answer.2).symm
  have sameQueryEquiv : queryE = queryE' := by
    rw [← Equiv.symm_symm queryE, queryInverse, Equiv.symm_symm]
  have sameAnswerEquiv : answerE = answerE' := by
    rw [← Equiv.symm_symm answerE, answerInverse, Equiv.symm_symm]
  subst sameQueryEquiv
  subst sameAnswerEquiv
  rfl

end RandomSystems.CR18.TypedResource

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open scoped ResourceSystem

namespace ResourceSystem

section MergeReindex

variable {S : Services} {K rest : Type}

/-! ### The merge along a connection, as a single re-indexing

`ResourceSystem.mergeAlong` (`Jost/SurfaceCarrier.lean`) is *re-index along the
split, then merge the trailing two-interface block*.  Its four helpers —
`splitLayout`, `splitQueryEquiv`, `splitAnswerEquiv`, `tagCompatible_split` —
are public there, and this section composes the two re-indexings into one. -/

/-- The split presentation read backwards: the interface a split slot came
from is `γ.split.symm` of it, and it kept its service. -/
theorem splitLayout_symm (γ : Connection K rest)
    (layout : Boundary S.sig K) (slot : rest ⊕ (Unit ⊕ Unit)) :
    splitLayout γ layout slot = layout (γ.split.symm slot) := by
  rcases slot with name | connected
  · rfl
  · rcases connected with _ | _ <;> rfl

/-- The split's query relocation with a computing inverse. -/
def splitQueryReindex (γ : Connection K rest) (layout : Boundary S.sig K) :
    Query S.sig layout ≃ Query S.sig (splitLayout γ layout) :=
  sigmaReindex γ.split
    (fun interface =>
      congrArg S.sig.input (splitLayout_split γ layout interface).symm)
    fun slot => congrArg S.sig.input (splitLayout_symm γ layout slot)

/-- The split's answer relocation with a computing inverse. -/
def splitAnswerReindex (γ : Connection K rest) (layout : Boundary S.sig K) :
    FlatAnswer S.sig layout ≃ FlatAnswer S.sig (splitLayout γ layout) :=
  sigmaReindex γ.split
    (fun interface =>
      congrArg S.sig.output (splitLayout_split γ layout interface).symm)
    fun slot => congrArg S.sig.output (splitLayout_symm γ layout slot)

theorem splitQueryEquiv_eq (γ : Connection K rest) (layout : Boundary S.sig K) :
    splitQueryEquiv γ layout = splitQueryReindex γ layout :=
  Equiv.ext fun _ => rfl

theorem splitAnswerEquiv_eq (γ : Connection K rest) (layout : Boundary S.sig K) :
    splitAnswerEquiv γ layout = splitAnswerReindex γ layout :=
  Equiv.ext fun _ => rfl

theorem tagCompatible_splitReindex (γ : Connection K rest)
    (layout : Boundary S.sig K) :
    TagCompatible (splitQueryReindex γ layout) (splitAnswerReindex γ layout) :=
  (splitQueryEquiv_eq γ layout) ▸ (splitAnswerEquiv_eq γ layout) ▸
    tagCompatible_split γ layout

variable [HasSumCode S.sig]

/-- **The layout a merge produces**: untouched interfaces keep their services,
the merged interface carries the paired service of the two the connection
reaches. -/
def mergedLayout (γ : Connection K rest) (layout : Boundary S.sig K) :
    Boundary S.sig (rest ⊕ Unit) :=
  Sum.elim (fun interface => layout (γ.untouched interface))
    fun _ => HasSumCode.sumCode (layout γ.first) (layout γ.second)

/-- **Where a merge sends a query**: first to the split presentation, then
across the two-interface block onto the single merged interface. -/
def mergeAlongQueryEquiv (γ : Connection K rest) (layout : Boundary S.sig K) :
    Query S.sig layout ≃ Query S.sig (mergedLayout γ layout) :=
  (splitQueryReindex γ layout).trans
    (mergeQueryEquiv (fun interface => layout (γ.untouched interface))
      (HasSumCode.sumCode (layout γ.first) (layout γ.second))
      (twoBlockInputCode (layout γ.first) (layout γ.second)))

/-- Answers travel the same way. -/
def mergeAlongAnswerEquiv (γ : Connection K rest) (layout : Boundary S.sig K) :
    FlatAnswer S.sig layout ≃ FlatAnswer S.sig (mergedLayout γ layout) :=
  (splitAnswerReindex γ layout).trans
    (mergeAnswerEquiv (fun interface => layout (γ.untouched interface))
      (HasSumCode.sumCode (layout γ.first) (layout γ.second))
      (twoBlockOutputCode (layout γ.first) (layout γ.second)))

theorem tagCompatible_mergeAlong (γ : Connection K rest)
    (layout : Boundary S.sig K) :
    TagCompatible (mergeAlongQueryEquiv γ layout)
      (mergeAlongAnswerEquiv γ layout) :=
  tagCompatible_trans (tagCompatible_splitReindex γ layout)
    (tagCompatible_mergeTwo _ _ _)

variable [DecidableEq K] [DecidableEq rest]

/-- **The merge along a connection is one re-indexing.**  Splitting the
interface set and then collapsing the connection's two-interface block is a
single tag-compatible re-addressing of the same behavior — the form every
algebraic law about `mergeAlong` is proved in. -/
theorem mergeAlong_eq_reindex (γ : Connection K rest)
    (resource : ResourceSystem S K) :
    resource.mergeAlong γ =
      ⟨mergedLayout γ resource.boundary,
        DependentRandomSystem.reindex (tagCompatible_mergeAlong γ resource.boundary)
          resource.system⟩ := by
  show (⟨mergedLayout γ resource.boundary,
      DependentRandomSystem.reindex
        (tagCompatible_mergeTwo (fun interface => resource.boundary (γ.untouched interface))
          (resource.boundary γ.first) (resource.boundary γ.second))
        (DependentRandomSystem.reindex (tagCompatible_split γ resource.boundary)
          resource.system)⟩ : ResourceSystem S (rest ⊕ Unit)) = _
  have computing : DependentRandomSystem.reindex
        (tagCompatible_split γ resource.boundary) resource.system =
      DependentRandomSystem.reindex
        (tagCompatible_splitReindex γ resource.boundary) resource.system :=
    DependentRandomSystem.reindex_congr_equiv _ _
      (splitQueryEquiv_eq γ resource.boundary)
      (splitAnswerEquiv_eq γ resource.boundary) resource.system
  exact congrArg
    (fun system => (⟨mergedLayout γ resource.boundary, system⟩ :
      ResourceSystem S (rest ⊕ Unit)))
    ((congrArg (DependentRandomSystem.reindex
        (tagCompatible_mergeTwo
          (fun interface => resource.boundary (γ.untouched interface))
          (resource.boundary γ.first) (resource.boundary γ.second))) computing).trans
      (DependentRandomSystem.reindex_reindex _ _ _ resource.system))

end MergeReindex

section ParLeft

variable {S : Services} {I J rest : Type} [HasSumCode S.sig]
  [DecidableEq I] [DecidableEq J] [DecidableEq rest]

/-- **Jost Proposition 2.2.3, second clause, for a connection reaching two
interfaces** (printed p. 18 states it for a converter; this is the
re-addressing underneath it).  Merging two interfaces of the left component of
`[R, T]` is merging them in `R` and then composing: `[R, T] ••[γ‖J] = [R ••[γ],
T]`, the two sides differing only in the spelling of the interface set —
`(rest ⊕ J) ⊕ Unit` against `(rest ⊕ Unit) ⊕ J`, which `outerShuffle` renames.

The composite `T` is untouched throughout, which is the content: a connection
into one factor sees nothing of the other, so an author may make it wherever
it is convenient and rename afterwards, at no error
(`ResourceSystem.close_reindex`). -/
@[cc_surface]
theorem mergeAlong_par_left (γ : Connection I rest)
    (left : ResourceSystem S I) (right : ResourceSystem S J) :
    (left ∥ right).mergeAlong (γ.parLeft J) =
      ResourceSystem.reindex (Connection.outerShuffle rest J)
        ((left.mergeAlong γ) ∥ right) := by
  rw [ResourceSystem.mergeAlong_eq_reindex (γ.parLeft J) (left ∥ right),
    ResourceSystem.mergeAlong_eq_reindex γ left]
  show (⟨mergedLayout (γ.parLeft J) (Sum.elim left.boundary right.boundary),
      DependentRandomSystem.reindex
        (tagCompatible_mergeAlong (γ.parLeft J)
          (Sum.elim left.boundary right.boundary))
        (DependentRandomSystem.tensor left.system right.system)⟩ :
      ResourceSystem S ((rest ⊕ J) ⊕ Unit)) =
    ⟨relabelBoundary (Connection.outerShuffle rest J)
        (Sum.elim (mergedLayout γ left.boundary) right.boundary),
      DependentRandomSystem.reindex
        (tagCompatible_relabelInterfaces (Connection.outerShuffle rest J)
          (Sum.elim (mergedLayout γ left.boundary) right.boundary))
        (DependentRandomSystem.tensor
          (DependentRandomSystem.reindex (tagCompatible_mergeAlong γ left.boundary)
            left.system)
          right.system)⟩
  rw [DependentRandomSystem.tensor_reindex_left
      (tagCompatible_mergeAlong γ left.boundary)
      (tagCompatible_tensorLeft (tagCompatible_mergeAlong γ left.boundary)),
    DependentRandomSystem.reindex_reindex _ _
      (tagCompatible_trans
        (tagCompatible_tensorLeft (tagCompatible_mergeAlong γ left.boundary))
        (tagCompatible_relabelInterfaces (Connection.outerShuffle rest J)
          (Sum.elim (mergedLayout γ left.boundary) right.boundary))),
    DependentRandomSystem.reindex_congr_equiv _
      (tagCompatible_trans
        (tagCompatible_tensorLeft (tagCompatible_mergeAlong γ left.boundary))
        (tagCompatible_relabelReindex (Connection.outerShuffle rest J)
          (Sum.elim (mergedLayout γ left.boundary) right.boundary)))
      (congrArg (fun step =>
          (tensorLeftQueryEquiv (mergeAlongQueryEquiv γ left.boundary)
            right.boundary).trans step)
        (relabelQueryEquiv_eq (Connection.outerShuffle rest J)
          (Sum.elim (mergedLayout γ left.boundary) right.boundary)))
      (congrArg (fun step =>
          (tensorLeftAnswerEquiv (mergeAlongAnswerEquiv γ left.boundary)
            right.boundary).trans step)
        (relabelAnswerEquiv_eq (Connection.outerShuffle rest J)
          (Sum.elim (mergedLayout γ left.boundary) right.boundary)))
      (DependentRandomSystem.tensor left.system right.system)]
  refine Resource.reindex_congr _ _ ?_ ?_ ?_ _
  · funext interface
    rcases interface with (name | interface) | merged <;> rfl
  · rintro ((name | interface) | merged) value <;> rfl
  · rintro ((name | interface) | merged) value <;> rfl

end ParLeft

end ResourceSystem

/-! ## Receipts -/

/-- info: 'RandomSystems.CC.ResourceSystem.mergeAlong_par_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.mergeAlong_par_left

#cc_surface_check ResourceSystem.mergeAlong_par_left

end RandomSystems.CC
