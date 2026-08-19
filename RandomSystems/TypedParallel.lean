/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedAction
import RandomSystems.StrictRelabel
import RandomSystems.StrictParallel
import RandomSystems.TypedFramingMetric

/-!
# Parallel composition of typed boundaries

Abstract Cryptography's `R ∥ R'` gives **every party both resources**: the
interface set is unchanged and each interface carries the tagged sum of the two
components' alphabets.  On the typed carrier that is a boundary-level
operation, `sumBoundary`, and this module establishes the alphabet
bookkeeping it forces.

The content is one equivalence and its inverse-image on answers:

```
Query U (σ ⊞ σ') = Σ i, U.input (sumCode (σ i) (σ' i))   -- σ ⊞ σ' = sumBoundary σ σ'
                 ≃ Σ i, (U.input (σ i) ⊕ U.input (σ' i))   -- HasSumCode.inputEquiv
                 ≃ (Σ i, U.input (σ i)) ⊕ (Σ i, U.input (σ' i))
                 = Query U σ ⊕ Query U σ'
```

Neither step is a type equality.  The first is `HasSumCode.inputEquiv`
transported pointwise under the index: the class states its alphabet laws as
`≃`, not `=`, because signatures whose alphabets distribute only up to
isomorphism — `withEvents`' `𝒳 × 2^ℰ`, where `(X ⊕ Y) × ℰ` is
`Equiv.sumProdDistrib`-equivalent to `(X × ℰ) ⊕ (Y × ℰ)` and nothing more —
would otherwise be excluded from `∥` outright.  The second is mathlib's
`Equiv.sigmaSumDistrib`, which could never be an equality: `Σ i, (Aᵢ ⊕ Bᵢ)`
and `(Σ i, Aᵢ) ⊕ (Σ i, Bᵢ)` are not the same type.  So the parallel of two
typed resources cannot be obtained by `cast` at all and needs
behavior-preserving relabelling (`RandomSystems.StrictRelabel`) throughout.

The second half of the module is that transport: parallel composition of
the *behavior* carried at the two boundaries, at every level of the tower —
deterministic (`DependentDDS.parallel`), law (`DependentPDS.parallel`),
contextual class (`DependentRandomSystem.parallel`), and heterogeneous
resource (`Resource.parallel`).  None of it re-proves parallel machinery:
the dependent parallel is *defined* as flatten → `PFunDDS.par` → relabel
along the equivalences above → unflatten, so P1's flat facts
(`maxEDist_par_le`, `equivalent_par`, the cancellation theorems) transport
verbatim through metric full abstraction
(`contextual_edist_eq_max_edist_flatten`) and the relabelling isometry
(`maxEDist_relabel`).  The `TagFaithful` obligation of `unflatten` is
discharged exactly by the index-compatibility lemmas: `PFunDDS.par` routes
a left-tagged query to the left component, whose own tag-faithfulness
names the query's interface, and both equivalences preserve it.
-/

namespace RandomSystems.CR18.TypedResource

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}

/-- The parallel boundary: **the same interfaces**, each carrying the sum code
of the two components'.  This is what makes `∥` mean "every party holds both
resources" rather than "there are now twice as many parties" — the latter would
make the alphabet bookkeeping a definitional equality, and would also be the
wrong operation. -/
def sumBoundary [HasSumCode U] (left right : Boundary U I) : Boundary U I :=
  fun interface => HasSumCode.sumCode (left interface) (right interface)

section

variable [HasSumCode U] (left right : Boundary U I)

@[simp]
theorem sumBoundary_apply (interface : I) :
    sumBoundary left right interface =
      HasSumCode.sumCode (left interface) (right interface) :=
  rfl

/-- The parallel boundary determines both components — the boundary-level half
of the uniqueness of a parallel decomposition. -/
theorem sumBoundary_inj {left right left' right' : Boundary U I}
    (same : sumBoundary left right = sumBoundary left' right') :
    left = left' ∧ right = right' := by
  refine ⟨funext fun interface => ?_, funext fun interface => ?_⟩
  · exact (HasSumCode.sumCode_inj (congrFun same interface)).1
  · exact (HasSumCode.sumCode_inj (congrFun same interface)).2

/-- Queries at the parallel boundary, re-associated as a tagged sum of the
components' queries.  The first step is `HasSumCode.inputEquiv` under the
index; `Equiv.sigmaSumDistrib` re-associates the sigma over the sum. -/
def queryEquiv :
    Query U (sumBoundary left right) ≃ Query U left ⊕ Query U right :=
  (Equiv.sigmaCongrRight fun interface =>
      HasSumCode.inputEquiv (left interface) (right interface)).trans
    (Equiv.sigmaSumDistrib (fun interface => U.input (left interface))
      (fun interface => U.input (right interface)))

/-- Flat answers at the parallel boundary, re-associated the same way. -/
def answerEquiv :
    FlatAnswer U (sumBoundary left right) ≃
      FlatAnswer U left ⊕ FlatAnswer U right :=
  (Equiv.sigmaCongrRight fun interface =>
      HasSumCode.outputEquiv (left interface) (right interface)).trans
    (Equiv.sigmaSumDistrib (fun interface => U.output (left interface))
      (fun interface => U.output (right interface)))

/-! ## The equivalences preserve the interface index

Tag-faithfulness of the parallel — every answer carries the interface of the
query that provoked it — survives the re-association only because both
equivalences move a query or answer *within its own interface*.  Both steps do:
`Equiv.sigmaCongrRight` acts fibrewise by construction, and
`Equiv.sigmaSumDistrib` sends `⟨i, x⟩` to a sum branch that re-tags with the
same `i`. -/

/-- `Equiv.sigmaSumDistrib` re-tags with the index it started from, on either
branch.  Stated separately because the index must be exposed to `cases` before
the branch is visible in the goal. -/
private theorem sigmaSumDistrib_index {J : Type*} {alpha beta : J → Type*}
    (pair : Σ index, alpha index ⊕ beta index) :
    Sum.elim Sigma.fst Sigma.fst (Equiv.sigmaSumDistrib alpha beta pair) =
      pair.1 := by
  obtain ⟨index, value⟩ := pair
  cases value <;> rfl

/-- The query equivalence keeps the interface, whichever side it lands on. -/
@[simp]
theorem queryEquiv_index (query : Query U (sumBoundary left right)) :
    Sum.elim Sigma.fst Sigma.fst (queryEquiv left right query) = query.1 := by
  obtain ⟨interface, value⟩ := query
  exact sigmaSumDistrib_index _

/-- The answer equivalence keeps the interface too. -/
@[simp]
theorem answerEquiv_index (answer : FlatAnswer U (sumBoundary left right)) :
    Sum.elim Sigma.fst Sigma.fst (answerEquiv left right answer) = answer.1 := by
  obtain ⟨interface, value⟩ := answer
  exact sigmaSumDistrib_index _

/-- Inverse form: a left-tagged answer of the left component is re-tagged at
its own interface. -/
@[simp]
theorem answerEquiv_symm_inl_index (answer : FlatAnswer U left) :
    ((answerEquiv left right).symm (Sum.inl answer)).1 = answer.1 :=
  rfl

/-- Inverse form on the right component. -/
@[simp]
theorem answerEquiv_symm_inr_index (answer : FlatAnswer U right) :
    ((answerEquiv left right).symm (Sum.inr answer)).1 = answer.1 :=
  rfl

/-- Inverse form for queries, left component. -/
@[simp]
theorem queryEquiv_symm_inl_index (query : Query U left) :
    ((queryEquiv left right).symm (Sum.inl query)).1 = query.1 :=
  rfl

/-- Inverse form for queries, right component. -/
@[simp]
theorem queryEquiv_symm_inr_index (query : Query U right) :
    ((queryEquiv left right).symm (Sum.inr query)).1 = query.1 :=
  rfl

end

/-! ## The fibre-level parallel: flatten, compose flatly, relabel, unflatten

Everything below is transport.  `PFunDDS.par`/`PFunPDS.par` already carry
the routing semantics and (in `StrictParallel`) the `‖`-non-expansion and
cancellation facts for the strict metric; `queryEquiv`/`answerEquiv` carry
the alphabet bookkeeping; `maxEDist_relabel` says the strict metric cannot
see the relabelling; and metric full abstraction says the typed contextual
metric *is* the strict metric of the flattening.  So the dependent parallel
is defined by the round trip and every fact about it is a rewrite chain. -/

open RandomSystems (Dist)

noncomputable section

section ParallelTower

variable [HasSumCode U] {left right : Boundary U I}

/-- If a merged history ends in a left-tagged query, the left sub-history
ends in exactly that query — the list-level core of tag-faithfulness of the
parallel. -/
private theorem getLast?_filterMap_getLeft {alpha beta : Type*}
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
private theorem getLast?_filterMap_getRight {alpha beta : Type*}
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

/-- **The `unflatten` obligation for the parallel**: the flat parallel of
two tag-faithful components, relabelled back to the parallel boundary, is
itself tag-faithful.  `PFunDDS.par` answers a left-tagged query from the
left component, whose own tag-faithfulness names the interface of the last
left sub-query; `getLast?_filterMap_getLeft` identifies that sub-query with
the global last query, and the two equivalences preserve its interface
(`queryEquiv_index`, `answerEquiv_symm_inl_index`).  Symmetrically on the
right. -/
theorem tag_faithful_relabel_par
    {flatLeft : PFunDDS.DDS (Query U left) (FlatAnswer U left)}
    {flatRight : PFunDDS.DDS (Query U right) (FlatAnswer U right)}
    (faithfulLeft : TagFaithful flatLeft)
    (faithfulRight : TagFaithful flatRight) :
    TagFaithful
      (PFunDDS.DDS.relabel (queryEquiv left right).symm
        (answerEquiv left right).symm (PFunDDS.par flatLeft flatRight)) := by
  intro history member
  have nonempty : history ≠ [] := by
    intro empty
    subst empty
    exact PFunDDS.empty_not_mem _ member
  have member' : history.map ⇑(queryEquiv left right) ∈
      PFunDDS.dom (PFunDDS.par flatLeft flatRight) := by
    have h := (PFunDDS.DDS.mem_dom_relabel (queryEquiv left right).symm
      (answerEquiv left right).symm (PFunDDS.par flatLeft flatRight)
      history).mp member
    simpa using h
  have mappedNe : history.map ⇑(queryEquiv left right) ≠ [] := fun h =>
    nonempty (List.map_eq_nil_iff.mp h)
  have mappedLast : (history.map ⇑(queryEquiv left right)).getLast mappedNe =
      queryEquiv left right (history.getLast nonempty) := List.getLast_map _
  have houtput : PFunDDS.output
      (PFunDDS.DDS.relabel (queryEquiv left right).symm
        (answerEquiv left right).symm (PFunDDS.par flatLeft flatRight))
      history member =
      (answerEquiv left right).symm
        (PFunDDS.output (PFunDDS.par flatLeft flatRight)
          (history.map ⇑(queryEquiv left right)) member') := rfl
  rw [houtput]
  rcases hcase : queryEquiv left right (history.getLast nonempty) with q | q
  · -- the last query is left-tagged, so the parallel answered from the left
    have mappedLast? : (history.map ⇑(queryEquiv left right)).getLast? =
        some (Sum.inl q) := by
      rw [List.getLast?_eq_some_getLast mappedNe, mappedLast, hcase]
    have hraw : PFunDDS.output (PFunDDS.par flatLeft flatRight)
        (history.map ⇑(queryEquiv left right)) member' ∈
        (flatLeft.1 ((history.map ⇑(queryEquiv left right)).filterMap
          Sum.getLeft?)).map Sum.inl := by
      have hmem : PFunDDS.output (PFunDDS.par flatLeft flatRight)
          (history.map ⇑(queryEquiv left right)) member' ∈
          (PFunDDS.par flatLeft flatRight).1
            (history.map ⇑(queryEquiv left right)) := Part.get_mem member'
      simp only [PFunDDS.par] at hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      rw [mappedLast?] at hmem
      exact hmem
    obtain ⟨answer, answerMem, answerEq⟩ := (Part.mem_map_iff _).mp hraw
    have memberLeft : (history.map ⇑(queryEquiv left right)).filterMap
        Sum.getLeft? ∈ PFunDDS.dom flatLeft :=
      Part.dom_iff_mem.mpr ⟨answer, answerMem⟩
    have subLast? : ((history.map ⇑(queryEquiv left right)).filterMap
        Sum.getLeft?).getLast? = some q :=
      getLast?_filterMap_getLeft mappedNe (mappedLast.trans hcase)
    have subNe : (history.map ⇑(queryEquiv left right)).filterMap
        Sum.getLeft? ≠ [] := by
      intro empty
      rw [empty] at subLast?
      simp at subLast?
    have subLast : ((history.map ⇑(queryEquiv left right)).filterMap
        Sum.getLeft?).getLast subNe = q :=
      Option.some.inj
        ((List.getLast?_eq_some_getLast subNe).symm.trans subLast?)
    have answerVal : PFunDDS.output flatLeft
        ((history.map ⇑(queryEquiv left right)).filterMap Sum.getLeft?)
        memberLeft = answer :=
      Part.get_eq_of_mem answerMem memberLeft
    have answerTag : answer.1 = q.1 := by
      have hfaith := faithfulLeft _ memberLeft
      rw [answerVal] at hfaith
      rw [hfaith]
      exact congrArg Sigma.fst subLast
    rw [← answerEq, answerEquiv_symm_inl_index, answerTag]
    have hindex := queryEquiv_index left right (history.getLast nonempty)
    rw [hcase] at hindex
    exact hindex
  · -- symmetric: the last query is right-tagged
    have mappedLast? : (history.map ⇑(queryEquiv left right)).getLast? =
        some (Sum.inr q) := by
      rw [List.getLast?_eq_some_getLast mappedNe, mappedLast, hcase]
    have hraw : PFunDDS.output (PFunDDS.par flatLeft flatRight)
        (history.map ⇑(queryEquiv left right)) member' ∈
        (flatRight.1 ((history.map ⇑(queryEquiv left right)).filterMap
          Sum.getRight?)).map Sum.inr := by
      have hmem : PFunDDS.output (PFunDDS.par flatLeft flatRight)
          (history.map ⇑(queryEquiv left right)) member' ∈
          (PFunDDS.par flatLeft flatRight).1
            (history.map ⇑(queryEquiv left right)) := Part.get_mem member'
      simp only [PFunDDS.par] at hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      obtain ⟨-, hmem⟩ := Part.mem_assert_iff.mp hmem
      rw [mappedLast?] at hmem
      exact hmem
    obtain ⟨answer, answerMem, answerEq⟩ := (Part.mem_map_iff _).mp hraw
    have memberRight : (history.map ⇑(queryEquiv left right)).filterMap
        Sum.getRight? ∈ PFunDDS.dom flatRight :=
      Part.dom_iff_mem.mpr ⟨answer, answerMem⟩
    have subLast? : ((history.map ⇑(queryEquiv left right)).filterMap
        Sum.getRight?).getLast? = some q :=
      getLast?_filterMap_getRight mappedNe (mappedLast.trans hcase)
    have subNe : (history.map ⇑(queryEquiv left right)).filterMap
        Sum.getRight? ≠ [] := by
      intro empty
      rw [empty] at subLast?
      simp at subLast?
    have subLast : ((history.map ⇑(queryEquiv left right)).filterMap
        Sum.getRight?).getLast subNe = q :=
      Option.some.inj
        ((List.getLast?_eq_some_getLast subNe).symm.trans subLast?)
    have answerVal : PFunDDS.output flatRight
        ((history.map ⇑(queryEquiv left right)).filterMap Sum.getRight?)
        memberRight = answer :=
      Part.get_eq_of_mem answerMem memberRight
    have answerTag : answer.1 = q.1 := by
      have hfaith := faithfulRight _ memberRight
      rw [answerVal] at hfaith
      rw [hfaith]
      exact congrArg Sigma.fst subLast
    rw [← answerEq, answerEquiv_symm_inr_index, answerTag]
    have hindex := queryEquiv_index left right (history.getLast nonempty)
    rw [hcase] at hindex
    exact hindex

/-- Parallel composition of dependent deterministic resources: flatten
both, compose with `PFunDDS.par`, relabel to the parallel boundary, and
read the result back as a native dependent resource.  `unflatten` is
legitimate by `tag_faithful_relabel_par`. -/
noncomputable def parallel (leftSystem : DependentDDS U left)
    (rightSystem : DependentDDS U right) :
    DependentDDS U (sumBoundary left right) :=
  unflatten
    (PFunDDS.DDS.relabel (queryEquiv left right).symm
      (answerEquiv left right).symm
      (PFunDDS.par leftSystem.flatten rightSystem.flatten))
    (tag_faithful_relabel_par (flatten_tag_faithful leftSystem)
      (flatten_tag_faithful rightSystem))

/-- **The defining equation of the dependent parallel** (deterministic
level): flattening the native parallel is the relabelled flat parallel of
the flattenings.  Near-definitional via `flatten_unflatten`. -/
theorem flatten_parallel (leftSystem : DependentDDS U left)
    (rightSystem : DependentDDS U right) :
    (leftSystem.parallel rightSystem).flatten =
      PFunDDS.DDS.relabel (queryEquiv left right).symm
        (answerEquiv left right).symm
        (PFunDDS.par leftSystem.flatten rightSystem.flatten) :=
  flatten_unflatten _ _

end DependentDDS

namespace DependentPDS

/-- Parallel composition of finite-support laws: the independent product
pushed through the deterministic parallel — the dependent mirror of
`PFunPDS.par`. -/
noncomputable def parallel (leftLaw : DependentPDS U left)
    (rightLaw : DependentPDS U right) :
    DependentPDS U (sumBoundary left right) :=
  Dist.fTransform
    (fun pair : DependentDDS U left × DependentDDS U right =>
      pair.1.parallel pair.2)
    (Dist.prod leftLaw rightLaw)

/-- Parallel composition multiplies total mass, so it preserves
normalization. -/
theorem parallel_weight (leftLaw : DependentPDS U left)
    (rightLaw : DependentPDS U right) :
    (parallel leftLaw rightLaw).weight =
      leftLaw.weight * rightLaw.weight := by
  unfold parallel
  rw [Dist.weight_fTransform, Dist.weight_prod]

/-- **The defining equation of the dependent parallel** (law level):
flattening commutes with parallel composition up to the boundary
relabelling.  This is the single seam through which every strict flat
parallel fact reaches the typed carrier. -/
theorem flatten_parallel (leftLaw : DependentPDS U left)
    (rightLaw : DependentPDS U right) :
    DependentPDS.flatten (parallel leftLaw rightLaw) =
      PFunPDS.relabel (queryEquiv left right).symm
        (answerEquiv left right).symm
        (PFunPDS.par (DependentPDS.flatten leftLaw)
          (DependentPDS.flatten rightLaw)) := by
  unfold DependentPDS.flatten parallel PFunPDS.relabel PFunPDS.par
  rw [← Dist.pushforward_product_eq_product_pushforwards,
    Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg
    (fun step => Dist.fTransform step (Dist.prod leftLaw rightLaw))
    (funext fun pair => DependentDDS.flatten_parallel pair.1 pair.2)

/-- Parallel composition of normalized laws. -/
noncomputable def Prob.parallel (leftLaw : Prob U left)
    (rightLaw : Prob U right) : Prob U (sumBoundary left right) :=
  ⟨DependentPDS.parallel leftLaw.val rightLaw.val, by
    rw [← DependentPDS.flatten_is_probability_distribution_iff,
      DependentPDS.flatten_parallel]
    exact (PFunPDS.isProbDist_relabel_iff _ _ _).mpr
      (PFunPDS.isProbDist_par
        ((DependentPDS.flatten_is_probability_distribution_iff _).mpr
          leftLaw.property)
        ((DependentPDS.flatten_is_probability_distribution_iff _).mpr
          rightLaw.property))⟩

@[simp]
theorem Prob.parallel_val (leftLaw : Prob U left) (rightLaw : Prob U right) :
    (Prob.parallel leftLaw rightLaw).val =
      DependentPDS.parallel leftLaw.val rightLaw.val :=
  rfl

omit [HasSumCode U] in
/-- Typed contextual equivalence **is** strict equivalence of the
flattenings — the equivalence form of metric full abstraction, and the
bridge every quotient descent below travels. -/
theorem contextually_equivalent_iff_flatten_equivalent
    [DecidableEq I] [DecidableEq U.Code] {boundary : Boundary U I}
    (leftLaw rightLaw : DependentPDS U boundary) :
    ContextuallyEquivalent leftLaw rightLaw ↔
      StrictContext.Equivalent (DependentPDS.flatten leftLaw)
        (DependentPDS.flatten rightLaw) := by
  rw [← contextual_edist_eq_zero_iff, contextual_edist_eq_max_edist_flatten,
    StrictContext.max_edist_eq_zero_iff]

end DependentPDS

namespace DependentRandomSystem

variable [DecidableEq I] [DecidableEq U.Code]

/-- Parallel composition of contextual behavior classes.  Well-definedness
is the full-abstraction bridge plus the strict congruence `equivalent_par`
plus the relabelling congruence — no new transcript argument. -/
noncomputable def parallel (leftClass : DependentRandomSystem U left)
    (rightClass : DependentRandomSystem U right) :
    DependentRandomSystem U (sumBoundary left right) :=
  Quotient.liftOn₂ leftClass rightClass
    (fun leftProb rightProb =>
      ofProb (DependentPDS.Prob.parallel leftProb rightProb))
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
      rw [DependentPDS.Prob.parallel_val, DependentPDS.Prob.parallel_val,
        DependentPDS.flatten_parallel, DependentPDS.flatten_parallel]
      exact StrictContext.equivalent_relabel _ _
        (StrictContext.equivalent_par leftB.flatten.property
          rightA.flatten.property leftFlat rightFlat))

@[simp]
theorem parallel_ofProb (leftProb : DependentPDS.Prob U left)
    (rightProb : DependentPDS.Prob U right) :
    parallel (ofProb leftProb) (ofProb rightProb) =
      ofProb (DependentPDS.Prob.parallel leftProb rightProb) :=
  rfl

/-- **Maurer11 eq. (3) on the typed contextual fibres**: parallel
composition is `‖`-non-expanding for the contextual metric.  The chain is
full abstraction → the defining equation → the relabelling isometry → the
strict `maxEDist_par_le`. -/
theorem edist_parallel_le
    (leftA leftB : DependentRandomSystem U left)
    (rightA rightB : DependentRandomSystem U right) :
    edist (parallel leftA rightA) (parallel leftB rightB) ≤
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
                      (ofProb (DependentPDS.Prob.parallel leftA rightA))
                      (ofProb (DependentPDS.Prob.parallel leftB rightB)) ≤
                    edist (ofProb leftA) (ofProb leftB) +
                      edist (ofProb rightA) (ofProb rightB)
                  rw [edist_of_prob, edist_of_prob, edist_of_prob,
                    DependentPDS.contextual_edist_eq_max_edist_flatten,
                    DependentPDS.contextual_edist_eq_max_edist_flatten,
                    DependentPDS.contextual_edist_eq_max_edist_flatten,
                    DependentPDS.Prob.parallel_val,
                    DependentPDS.Prob.parallel_val,
                    DependentPDS.flatten_parallel,
                    DependentPDS.flatten_parallel,
                    StrictContext.maxEDist_relabel]
                  exact StrictContext.maxEDist_par_le _ _ _ _
                    leftB.flatten.property rightA.flatten.property

/-- **The parallel decomposition of a contextual class is unique** — the
typed mirror of the strict cancellation theorem, and the behavioral half
of the uniqueness of a resource's parallel decomposition. -/
theorem parallel_inj
    {leftA leftB : DependentRandomSystem U left}
    {rightA rightB : DependentRandomSystem U right}
    (same : parallel leftA rightA = parallel leftB rightB) :
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
                  rw [DependentPDS.Prob.parallel_val,
                    DependentPDS.Prob.parallel_val,
                    DependentPDS.flatten_parallel,
                    DependentPDS.flatten_parallel,
                    StrictContext.equivalent_relabel_iff] at parFlat
                  constructor
                  · apply Quotient.sound
                    apply (DependentPDS.Prob.contextual_setoid_rel_iff _ _).mpr
                    exact (DependentPDS.contextually_equivalent_iff_flatten_equivalent
                        _ _).mpr
                      (StrictContext.equivalent_left_of_par_equivalent
                        rightA.flatten.property rightB.flatten.property parFlat)
                  · apply Quotient.sound
                    apply (DependentPDS.Prob.contextual_setoid_rel_iff _ _).mpr
                    exact (DependentPDS.contextually_equivalent_iff_flatten_equivalent
                        _ _).mpr
                      (StrictContext.equivalent_right_of_par_equivalent
                        leftA.flatten.property leftB.flatten.property parFlat)

end DependentRandomSystem

namespace Resource

variable [DecidableEq I] [DecidableEq U.Code]

/-- Parallel composition on the heterogeneous typed resource carrier: the
same interfaces, each holding both components (`sumBoundary`), carrying the
parallel of the two contextual classes.  This is the operation the AC-side
`Par (Phi I U)` instance exposes. -/
noncomputable def parallel (leftResource rightResource : Resource I U) :
    Resource I U :=
  ⟨sumBoundary leftResource.boundary rightResource.boundary,
    DependentRandomSystem.parallel leftResource.system rightResource.system⟩

@[simp]
theorem parallel_boundary (leftResource rightResource : Resource I U) :
    (parallel leftResource rightResource).boundary =
      sumBoundary leftResource.boundary rightResource.boundary :=
  rfl

/-- **The parallel decomposition of a typed resource is unique**: sum
boundaries are injective and the parallel decomposition of a contextual
class is unique. -/
theorem parallel_inj {leftA leftB rightA rightB : Resource I U}
    (same : parallel leftA rightA = parallel leftB rightB) :
    leftA = leftB ∧ rightA = rightB := by
  rcases leftA with ⟨leftABoundary, leftASystem⟩
  rcases leftB with ⟨leftBBoundary, leftBSystem⟩
  rcases rightA with ⟨rightABoundary, rightASystem⟩
  rcases rightB with ⟨rightBBoundary, rightBSystem⟩
  have hboundary : sumBoundary leftABoundary rightABoundary =
      sumBoundary leftBBoundary rightBBoundary :=
    congrArg Resource.boundary same
  obtain ⟨rfl, rfl⟩ := sumBoundary_inj hboundary
  rw [parallel, parallel, Resource.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ :=
    DependentRandomSystem.parallel_inj (eq_of_heq same.2)
  exact ⟨rfl, rfl⟩

/-- Distinct left components produce distinct compositions — the
non-vacuity receipt for the parallel: the operation genuinely remembers
both components. -/
theorem parallel_ne_left {leftA leftB rightComponent : Resource I U}
    (different : leftA ≠ leftB) :
    parallel leftA rightComponent ≠ parallel leftB rightComponent :=
  fun collapse => different (parallel_inj collapse).1

/-- Within one pair of boundaries, resource-level parallel distance is
fibre-level parallel distance. -/
theorem edist_parallel_same (leftBoundary rightBoundary : Boundary U I)
    (leftA leftB : DependentRandomSystem U leftBoundary)
    (rightA rightB : DependentRandomSystem U rightBoundary) :
    edist (parallel ⟨leftBoundary, leftA⟩ ⟨rightBoundary, rightA⟩)
        (parallel ⟨leftBoundary, leftB⟩ ⟨rightBoundary, rightB⟩) =
      edist (DependentRandomSystem.parallel leftA rightA)
        (DependentRandomSystem.parallel leftB rightB) :=
  Resource.edist_same _ _ _

/-- **Maurer11 §4.4 Definition 3 / eq. (3) on the typed resource
carrier**: the contextual metric is `‖`-non-expanding.  Distinct sum
boundaries sit at `⊤` on both sides (`sumBoundary` is injective), and
within one boundary pair the fibre-level bound applies.  This is the fact
the AC-side `IsNonexpandingPar (Phi I U)` instance repackages. -/
theorem edist_parallel_le (leftA leftB rightA rightB : Resource I U) :
    edist (parallel leftA rightA) (parallel leftB rightB) ≤
      edist leftA leftB + edist rightA rightB := by
  rcases leftA with ⟨leftABoundary, leftASystem⟩
  rcases leftB with ⟨leftBBoundary, leftBSystem⟩
  rcases rightA with ⟨rightABoundary, rightASystem⟩
  rcases rightB with ⟨rightBBoundary, rightBSystem⟩
  by_cases hboundaries : leftABoundary = leftBBoundary ∧
      rightABoundary = rightBBoundary
  · obtain ⟨rfl, rfl⟩ := hboundaries
    rw [edist_parallel_same, Resource.edist_same, Resource.edist_same]
    exact DependentRandomSystem.edist_parallel_le _ _ _ _
  · have hsum : sumBoundary leftABoundary rightABoundary ≠
        sumBoundary leftBBoundary rightBBoundary :=
      fun collapse => hboundaries (sumBoundary_inj collapse)
    rw [show parallel ⟨leftABoundary, leftASystem⟩
          ⟨rightABoundary, rightASystem⟩ =
        ⟨sumBoundary leftABoundary rightABoundary,
          DependentRandomSystem.parallel leftASystem rightASystem⟩ from rfl,
      show parallel ⟨leftBBoundary, leftBSystem⟩
          ⟨rightBBoundary, rightBSystem⟩ =
        ⟨sumBoundary leftBBoundary rightBBoundary,
          DependentRandomSystem.parallel leftBSystem rightBSystem⟩ from rfl,
      Resource.edist_ne hsum]
    rcases not_and_or.mp hboundaries with hleft | hright
    · rw [Resource.edist_ne hleft]
      simp
    · rw [Resource.edist_ne hright]
      simp

end Resource

end ParallelTower

end

end RandomSystems.CR18.TypedResource
