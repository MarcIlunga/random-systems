/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceCarrier
import RandomSystems.TypedPullback

/-!
# Merging the two interfaces a connection reaches is local

Jost's connection function `γ` (printed p. 18) names two interfaces of a
resource and leaves every other one alone; `ResourceSystem.mergeAlong` addresses
those two through one interface carrying their paired service.  This module
proves that the merge is **local**: a converter attached at an interface the
connection leaves alone may be attached before or after the merge.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.PFunConverter.General
open scoped Converter ResourceSystem

namespace ResourceSystem

variable {S : Services} {K rest : Type} [DecidableEq K] [DecidableEq rest]

/-- The layout the merge leaves behind: untouched interfaces keep their
services, the merged one carries the paired service. -/
def mergeLayout [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) : Boundary S.sig (rest ⊕ Unit) :=
  Sum.elim (fun interface => layout (γ.untouched interface))
    fun _ => S.paired (layout γ.first) (layout γ.second)

/-! ## The connection's three interfaces are distinct -/

end ResourceSystem

namespace Connection

variable {K rest : Type}

/-- Distinct untouched names are distinct interfaces: `γ` presents the interface
set, so its untouched part is an injection. -/
theorem untouched_injective (γ : Connection K rest) :
    Function.Injective γ.untouched := by
  intro left right same
  exact Sum.inl.inj (γ.split.symm.injective same)

/-- The first interface a connection reaches is not one it leaves alone. -/
theorem first_ne_untouched (γ : Connection K rest) (interface : rest) :
    γ.first ≠ γ.untouched interface := by
  intro same
  exact absurd (γ.split.symm.injective same) (by simp)

/-- …and neither is the second. -/
theorem second_ne_untouched (γ : Connection K rest) (interface : rest) :
    γ.second ≠ γ.untouched interface := by
  intro same
  exact absurd (γ.split.symm.injective same) (by simp)

end Connection

namespace ResourceSystem

variable {S : Services} {K rest : Type} [DecidableEq K] [DecidableEq rest]

/-! ## The merge in the boundary-independent ambient chart -/

/-- Re-tagging a dependent pair and casting its payload along the same equality
of tags is the identity. -/
theorem sigma_mk_cast {A : Type*} {family : A → Type*} {left right : A}
    (same : left = right) (value : family left) :
    (⟨right, cast (congrArg family same) value⟩ : Σ index, family index) =
      ⟨left, value⟩ := by
  cases same
  rfl

omit [DecidableEq K] [DecidableEq rest] in
/-- **The split is a pure renaming in the ambient chart**: a query keeps its
payload and only changes address. -/
theorem encodeQuery_splitQueryEquiv (γ : Connection K rest)
    (layout : Boundary S.sig K) (query : Query S.sig layout) :
    encodeQuery (splitQueryEquiv γ layout query) =
      Prod.map ⇑γ.split id (encodeQuery query) := by
  obtain ⟨interface, value⟩ := query
  exact congrArg (fun payload => (γ.split interface, payload))
    (sigma_mk_cast (splitLayout_split γ layout interface).symm value)

omit [DecidableEq K] [DecidableEq rest] in
/-- …and so does an answer, which does not even change address in the ambient
chart, because an answer is coded by its service alone. -/
theorem encodeAnswer_splitAnswerEquiv (γ : Connection K rest)
    (layout : Boundary S.sig K) (answer : FlatAnswer S.sig layout) :
    encodeAnswer (splitAnswerEquiv γ layout answer) = encodeAnswer answer := by
  obtain ⟨interface, value⟩ := answer
  exact sigma_mk_cast (splitLayout_split γ layout interface).symm value

omit [DecidableEq K] [DecidableEq rest] in
/-- **The split of an interface set is a pull-back** along `γ.split.symm`. -/
theorem isPullback_split (γ : Connection K rest) (layout : Boundary S.sig K)
    (system : DependentDDS S.sig layout) :
    IsPullback (Prod.map ⇑γ.split.symm id) (fun _ => id) system.embed
      (system.reindex (tagCompatible_split γ layout)).embed :=
  DependentDDS.isPullback_embed_reindex_of_rename (tagCompatible_split γ layout)
    γ.split (splitLayout_split γ layout) (encodeQuery_splitQueryEquiv γ layout)
    (encodeAnswer_splitAnswerEquiv γ layout) system

/-- The behaviour underneath `mergeAlong`: split the interface set along the
connection, then merge the two-interface block into one. -/
noncomputable def mergeAlongDDS [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) (system : DependentDDS S.sig layout) :
    DependentDDS S.sig (mergeLayout γ layout) :=
  DependentDDS.mergeTwo (fun interface => layout (γ.untouched interface))
    (layout γ.first) (layout γ.second)
    (system.reindex (tagCompatible_split γ layout))

/-- **The ambient re-addressing behind `mergeAlong`**: undo the merge of the two
connected interfaces, then read the resulting split address back through the
connection. -/
noncomputable def mergeAlongRoute [HasSumCode S.sig] (γ : Connection K rest)
    (codeA codeB : S.Service) :
    AmbientQuery (rest ⊕ Unit) S.sig → AmbientQuery K S.sig :=
  Prod.map ⇑γ.split.symm id ∘ mergeTwoRoute codeA codeB

/-- The answer half of the same re-addressing. -/
noncomputable def mergeAlongRecode [HasSumCode S.sig] (codeA codeB : S.Service) :
    AmbientQuery (rest ⊕ Unit) S.sig → AmbientOutput S.sig → AmbientOutput S.sig :=
  fun entry => mergeTwoRecode codeA codeB entry ∘ id

omit [DecidableEq K] [DecidableEq rest] in
/-- **Merging along a connection is a pull-back.**  The codes are supplied
separately from the layout so that the *same* translation serves a layout and
any update of it at an untouched interface — which is exactly the situation the
locality theorem is about. -/
theorem isPullback_mergeAlong [HasSumCode S.sig] (γ : Connection K rest)
    {layout : Boundary S.sig K} {codeA codeB : S.Service}
    (firstCode : layout γ.first = codeA) (secondCode : layout γ.second = codeB)
    (system : DependentDDS S.sig layout) :
    IsPullback (mergeAlongRoute γ codeA codeB)
      (mergeAlongRecode (rest := rest) codeA codeB)
      system.embed (mergeAlongDDS γ layout system).embed := by
  subst firstCode
  subst secondCode
  exact (isPullback_split γ layout system).trans
    (DependentDDS.isPullback_embed_mergeTwo _ _ _ _)

omit [DecidableEq K] [DecidableEq rest] in
/-- The re-addressing carries an untouched interface identically. -/
theorem mergeAlongRoute_untouched [HasSumCode S.sig] (γ : Connection K rest)
    (codeA codeB : S.Service) (interface : rest) (value : AmbientInput S.sig) :
    mergeAlongRoute γ codeA codeB (Sum.inl interface, value) =
      (γ.untouched interface, value) :=
  rfl

omit [DecidableEq K] [DecidableEq rest] in
/-- …and recodes nothing there. -/
theorem mergeAlongRecode_untouched [HasSumCode S.sig] (codeA codeB : S.Service)
    (interface : rest) (value : AmbientInput S.sig) :
    mergeAlongRecode (rest := rest) codeA codeB (Sum.inl interface, value) = id :=
  rfl

omit [DecidableEq K] [DecidableEq rest] in
/-- …and sends no other query onto it: the untouched interfaces are pairwise
distinct and the merged one lands on the two the connection reaches. -/
theorem mergeAlongRoute_reflect [HasSumCode S.sig] (γ : Connection K rest)
    (codeA codeB : S.Service) (interface : rest) (entry : AmbientQuery (rest ⊕ Unit) S.sig)
    (different : entry.1 ≠ Sum.inl interface) :
    (mergeAlongRoute γ codeA codeB entry).1 ≠ γ.untouched interface := by
  obtain ⟨address, payload⟩ := entry
  cases address with
  | inl other =>
      intro collapse
      exact different (congrArg Sum.inl (γ.untouched_injective collapse))
  | inr merged =>
      obtain ⟨block, lands⟩ := mergeTwoRoute_inr codeA codeB merged payload
      show γ.split.symm (mergeTwoRoute codeA codeB (Sum.inr merged, payload)).1 ≠
        γ.split.symm (Sum.inl interface)
      rw [lands]
      intro collapse
      exact absurd (γ.split.symm.injective collapse) (by simp)

/-! ## Locality, from the deterministic level up -/

/-- **The merged layout is local**: updating the service of an untouched
interface before the merge is updating it after. -/
theorem mergeLayout_replaceBoundary [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) (interface : rest) (target : S.Service) :
    mergeLayout γ (replaceBoundary layout (γ.untouched interface) target) =
      replaceBoundary (mergeLayout γ layout) (Sum.inl interface) target := by
  funext address
  cases address with
  | inl other =>
      by_cases same : other = interface
      · subst same
        simp [mergeLayout, replaceBoundary]
      · rw [replace_boundary_ne _ (by simpa using same)]
        show replaceBoundary layout (γ.untouched interface) target (γ.untouched other) = _
        rw [replace_boundary_ne _ fun collapse => same (γ.untouched_injective collapse)]
        rfl
  | inr merged =>
      rw [replace_boundary_ne _ (by simp)]
      show S.paired (replaceBoundary layout (γ.untouched interface) target γ.first)
          (replaceBoundary layout (γ.untouched interface) target γ.second) = _
      rw [replace_boundary_ne _ (γ.first_ne_untouched interface),
        replace_boundary_ne _ (γ.second_ne_untouched interface)]
      rfl

/-- **Locality at the deterministic level.**  Both sides are the same pull-back
of the same attached resource — the merge re-addresses only interfaces the
converter never names, so the converter cannot tell the two orders apart
(`IsPullback.attachAt`), and a pull-back is determined by what it pulls back
(`IsPullback.unique`). -/
theorem heq_mergeAlongDDS_attach [HasSumCode S.sig] {source target : S.Service}
    (converter : Converter S source target) (γ : Connection K rest)
    (interface : rest) {layout : Boundary S.sig K}
    (provides : layout (γ.untouched interface) = source)
    (system : DependentDDS S.sig layout) :
    HEq
      (mergeAlongDDS γ (replaceBoundary layout (γ.untouched interface) target)
        (system.attach (γ.untouched interface) converter provides))
      ((mergeAlongDDS γ layout system).attach (Sum.inl interface) converter provides) := by
  refine DependentDDS.heq_of_boundary_eq_of_embed_eq
    (mergeLayout_replaceBoundary γ layout interface target) ?_
  rw [DependentDDS.embed_attach]
  refine IsPullback.unique
    (isPullback_mergeAlong γ
      (replace_boundary_ne layout (γ.first_ne_untouched interface) target)
      (replace_boundary_ne layout (γ.second_ne_untouched interface) target)
      (system.attach (γ.untouched interface) converter provides)) ?_
  rw [DependentDDS.embed_attach]
  exact IsPullback.attachAt converter.embeddedDDC
    (isPullback_mergeAlong γ rfl rfl system)
    (mergeAlongRoute_untouched γ _ _ interface)
    (mergeAlongRecode_untouched _ _ interface)
    (fun entry different => mergeAlongRoute_reflect γ _ _ interface entry different)

/-! ## Up the tower: laws, behaviours, resource systems -/

/-- `mergeAlongDDS` on a finite-support law. -/
noncomputable def mergeAlongProb [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) (law : DependentPDS.Prob S.sig layout) :
    DependentPDS.Prob S.sig (mergeLayout γ layout) :=
  DependentPDS.Prob.reindex
    (tagCompatible_mergeTwo (fun interface => layout (γ.untouched interface))
      (layout γ.first) (layout γ.second))
    (DependentPDS.Prob.reindex (tagCompatible_split γ layout) law)

omit [DecidableEq K] [DecidableEq rest] in
/-- The law-level merge is the deterministic one pushed forward. -/
theorem mergeAlongProb_val [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) (law : DependentPDS.Prob S.sig layout) :
    (mergeAlongProb γ layout law).val =
      RandomSystems.Dist.fTransform (mergeAlongDDS γ layout) law.val := by
  show DependentPDS.reindex _ (DependentPDS.reindex _ law.val) = _
  unfold DependentPDS.reindex
  exact RandomSystems.Dist.fTransform_comp_eq_of_pointwise _ _ _ law.val fun _ => rfl

/-- `mergeAlongDDS` on a behaviour class. -/
noncomputable def mergeAlongDRS [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) (system : DependentRandomSystem S.sig layout) :
    DependentRandomSystem S.sig (mergeLayout γ layout) :=
  DependentRandomSystem.mergeTwo (fun interface => layout (γ.untouched interface))
    (layout γ.first) (layout γ.second)
    (DependentRandomSystem.reindex (tagCompatible_split γ layout) system)

/-- **The merge, spelled out**: re-index the interface set along the connection,
then merge the two-interface block into one.  Definitionally the surface
operation, since it is built from `Jost/SurfaceCarrier.lean`'s own split
helpers. -/
theorem mergeAlong_eq [HasSumCode S.sig] (γ : Connection K rest)
    (layout : Boundary S.sig K) (system : DependentRandomSystem S.sig layout) :
    mergeAlong γ (⟨layout, system⟩ : ResourceSystem S K) =
      ⟨mergeLayout γ layout, mergeAlongDRS γ layout system⟩ :=
  rfl

/-- **Locality at the law level.** -/
theorem heq_mergeAlongProb_attach [HasSumCode S.sig] {source target : S.Service}
    (converter : Converter S source target) (γ : Connection K rest)
    (interface : rest) {layout : Boundary S.sig K}
    (provides : layout (γ.untouched interface) = source)
    (law : DependentPDS.Prob S.sig layout) :
    HEq
      (mergeAlongProb γ (replaceBoundary layout (γ.untouched interface) target)
        (law.attach (γ.untouched interface) converter provides))
      ((mergeAlongProb γ layout law).attach (Sum.inl interface) converter provides) := by
  refine DependentPDS.Prob.heq_of_boundary_eq_of_val_heq
    (mergeLayout_replaceBoundary γ layout interface target) ?_
  rw [mergeAlongProb_val, DependentPDS.prob_attach_coe, DependentPDS.prob_attach_coe,
    mergeAlongProb_val]
  show HEq (RandomSystems.Dist.fTransform _
      (RandomSystems.Dist.fTransform _ law.val))
    (RandomSystems.Dist.fTransform _ (RandomSystems.Dist.fTransform _ law.val))
  rw [RandomSystems.Dist.fTransform_comp, RandomSystems.Dist.fTransform_comp]
  refine DependentPDS.heq_fTransform_of_boundary_eq₂
    (mergeLayout_replaceBoundary γ layout interface target) _ _ ?_ law.val
  intro deterministic
  exact heq_mergeAlongDDS_attach converter γ interface provides deterministic

/-- **Locality at the behavioural level.** -/
theorem heq_mergeAlongDRS_attach [HasSumCode S.sig] {source target : S.Service}
    (converter : Converter S source target) (γ : Connection K rest)
    (interface : rest) {layout : Boundary S.sig K}
    (provides : layout (γ.untouched interface) = source)
    (system : DependentRandomSystem S.sig layout) :
    HEq
      (mergeAlongDRS γ (replaceBoundary layout (γ.untouched interface) target)
        (DependentRandomSystem.attach (γ.untouched interface) converter provides system))
      (DependentRandomSystem.attach (Sum.inl interface) converter provides
        (mergeAlongDRS γ layout system)) := by
  induction system using Quotient.inductionOn with
  | _ law =>
      exact DependentRandomSystem.of_prob_heq_of_boundary_eq
        (mergeLayout_replaceBoundary γ layout interface target)
        (heq_mergeAlongProb_attach converter γ interface provides law)

/-! ## The statement -/

/-- **Merging the two interfaces a connection reaches is local.**  A converter
attached at an interface the connection leaves alone may be attached before or
after the merge; the merged interface is untouched either way.

Total, like both operations it relates: on an interface that does not provide
the converter's source service both attachments are the identity, and on one
that does, the merge only re-addresses interfaces the converter never names.
That is the whole content — `IsPullback.attachAt` in the kernel — and it is why
Jost's `π^γ` may be read off one component of a composite at a time. -/
@[cc_surface]
theorem mergeAlong_attachAt_untouched [HasSumCode S.sig]
    (γ : Connection K rest) (interface : rest)
    {source target : S.Service} (converter : Converter S source target)
    (resource : ResourceSystem S K) :
    (converter •[γ.untouched interface] resource).mergeAlong γ =
      converter •[Sum.inl interface] (resource.mergeAlong γ) := by
  rcases resource with ⟨layout, system⟩
  by_cases provides : layout (γ.untouched interface) = source
  · show mergeAlong γ ((Primitive.mk source target converter :
        Primitive K S.sig (γ.untouched interface)).act ⟨layout, system⟩) =
      (Primitive.mk source target converter :
        Primitive (rest ⊕ Unit) S.sig (Sum.inl interface)).act
        (mergeAlong γ ⟨layout, system⟩)
    rw [Primitive.act_of_matches _ layout provides system, mergeAlong_eq,
      mergeAlong_eq,
      Primitive.act_of_matches (Primitive.mk source target converter :
        Primitive (rest ⊕ Unit) S.sig (Sum.inl interface))
        (mergeLayout γ layout) provides,
      Resource.mk.injEq]
    exact ⟨mergeLayout_replaceBoundary γ layout interface target,
      heq_mergeAlongDRS_attach converter γ interface provides system⟩
  · rw [Converter.attachAt_of_not_provides converter (γ.untouched interface)
        (⟨layout, system⟩ : ResourceSystem S K) provides,
      Converter.attachAt_of_not_provides converter (Sum.inl interface)
        (mergeAlong γ (⟨layout, system⟩ : ResourceSystem S K)) provides]

end ResourceSystem

/--
info: 'RandomSystems.CC.ResourceSystem.mergeAlong_attachAt_untouched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ResourceSystem.mergeAlong_attachAt_untouched

#cc_surface_check ResourceSystem.mergeAlong_attachAt_untouched

end RandomSystems.CC
