/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedFramingMetric
import RandomSystemsCC.TypedFinite
import RandomSystems.StrictContextTotal

/-!
# The strict-observation distinguisher class of the typed RS carrier

The first concrete instance of `AbstractCrypto.DistinguisherClass`
(MauRen11 Definition 15 p. 13 and Definition 16 p. 14), on the production
typed random-systems carrier `TypedFinite.Phi I U` with converter monoid
`TypedFinite.Protocol I U`.

A test admits, at every dependent boundary, either no observation or the
acceptance mass of one strict deterministic observation of the flattened
global law (`StrictContext.Test` on `Query U boundary`/`FlatAnswer U
boundary`).  Definition 15's `[0, 1]` bound is the total mass of a
normalized law: acceptance mass is `Dist.mass`, bounded by `Dist.weight = 1`
(`Dist.mass_le_one`).  Definition 16's converter-emulation closure is exactly
the already-proved context absorption: attaching a typed deterministic
converter and then observing strictly is observing the source with the
absorbed test (`TypedFramingMetric.flatten_attach_eq_apply_law_framed` +
`StrictContext.accept_mass_apply`); the closure extends from primitives to
the whole generated protocol monoid because "absorbs into the test set" is a
submonoid condition.

## The derived metric versus the installed metric

The relation proved here is honest about its direction:

* globally, `edistD ≤ edist` (`strict_test_class_edistD_le_edist`) — this is
  the sound direction, and the exact hypothesis shape consumed by
  `RandomSystemsCC.Frost.Instantiation`;
* on one fixed boundary the two metrics agree exactly
  (`strict_test_class_edistD_same_boundary`), by metric full abstraction
  (`DependentPDS.contextual_edist_eq_max_edist_flatten`);
* across distinct boundaries equality **fails**: the installed heterogeneous
  metric is `⊤` there while every test class is `1`-bounded
  (`strict_test_class_edistD_lt_edist_of_boundary_ne`).

Following `../abstract-crypto/LIBRARY_GUIDE.md` §3, this module does **not**
register `DistinguisherClass.toPseudoEMetricSpace` as an instance: `Phi I U`
already carries the contextual quotient metric globally, and a second global
metric instance would be a competing-instance bug.  Consumers needing the
derived metric install it with a local `letI`.

## Query budgets as class restrictions

`boundedTests I U q` admits per-boundary observations only through
`StrictContextTotal.testOfTruncDDD q` — a CR18 distinguisher truncated at `q`
queries (`PFunDDS.truncDDD`, CR18 §4.10.1) read as a strict test.  This makes
a query budget a distinguisher-class restriction, the AC-native rendering of
what application files currently encode as converter filters (CBC's
`θ_r`/`[r]`).  For a **fixed** budget, Definition 16's closure holds only for
the neutral converter — a nontrivial converter changes the budget — so the
subclass is a `DistinguisherClass` over the trivial submonoid
`(⊥ : Submonoid (Protocol I U))`; budgets filter upward
(`bounded_tests_mono`), every budgeted test is admitted unbudgeted
(`bounded_tests_subset_strict_tests`), and the budgeted class metric is
dominated by the full class metric (`bounded_edistD_le_edistD`).

Non-vacuity of both classes — a concrete separating test on a concrete
resource pair with class distance exactly `1` — is proved in
`RandomSystemsCC.TypedDistinguisherChecks`.
-/

namespace RandomSystemsCC.TypedDistinguisher

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped Classical ENNReal

noncomputable section

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [DecidableEq I] [DecidableEq U.Code]

/-! ## Strict acceptance mass on contextual behavior -/

/-- Acceptance mass of one strict flattened observation against contextual
behavior.  Well defined on the quotient because a strict flattened test is
literally the terminal typed experiment `Experiment.test`. -/
def strictMass {boundary : Boundary U I}
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary))
    (system : DependentRandomSystem U boundary) : NNReal :=
  Quotient.liftOn system
    (fun representative =>
      StrictContext.acceptMass test (DependentPDS.flatten representative.val))
    (fun left right equivalent =>
      ((DependentPDS.Prob.contextual_setoid_rel_iff left right).mp equivalent)
        (.test test))

@[simp]
theorem strict_mass_of_prob {boundary : Boundary U I}
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary))
    (representative : DependentPDS.Prob U boundary) :
    strictMass test (DependentRandomSystem.ofProb representative) =
      StrictContext.acceptMass test
        (DependentPDS.flatten representative.val) :=
  rfl

/-- MauRen11 Definition 15's `[0, 1]` bound: acceptance mass of a normalized
law is bounded by its total weight `1`. -/
theorem strict_mass_le_one {boundary : Boundary U I}
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary))
    (system : DependentRandomSystem U boundary) :
    strictMass test system ≤ 1 := by
  induction system using Quotient.inductionOn with
  | _ representative =>
      exact RandomSystems.Dist.mass_le_one
        ((DependentPDS.flatten_is_probability_distribution_iff
          representative.val).2 representative.property) _

/-- Context absorption on the quotient: observing behind one typed
deterministic attachment is observing the source with the absorbed framed
test.  This is the already-proved absorption theorem
(`flatten_attach_eq_apply_law_framed` + `accept_mass_apply`) and the entire
content of the distinguisher class's converter-emulation law. -/
theorem strict_mass_attach {boundary : Boundary U I} {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (test : StrictContext.Test
      (Query U (replaceBoundary boundary interface target))
      (FlatAnswer U (replaceBoundary boundary interface target)))
    (system : DependentRandomSystem U boundary) :
    strictMass test
        (DependentRandomSystem.attach interface converter sourceMatches
          system) =
      strictMass
        (StrictContext.absorb test
          (TypedFraming.framedConverter interface boundary converter
            sourceMatches))
        system := by
  induction system using Quotient.inductionOn with
  | _ representative =>
      show StrictContext.acceptMass test
          (DependentPDS.flatten
            (DependentPDS.attach interface converter sourceMatches
              representative.val)) =
        StrictContext.acceptMass
          (StrictContext.absorb test
            (TypedFraming.framedConverter interface boundary converter
              sourceMatches))
          (DependentPDS.flatten representative.val)
      rw [DependentPDS.flatten_attach_eq_apply_law_framed
        interface converter sourceMatches representative.val]
      exact StrictContext.accept_mass_apply test
        (TypedFraming.framedConverter interface boundary converter
          sourceMatches)
        (DependentPDS.flatten representative.val)

/-- One strict flattened observation always compares within the installed
fibre metric: it is one term of the flattened strict supremum, which equals
the contextual metric by full abstraction. -/
theorem edist_strict_mass_le {boundary : Boundary U I}
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary))
    (left right : DependentRandomSystem U boundary) :
    edist (strictMass test left) (strictMass test right) ≤
      edist left right := by
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      show edist
          (StrictContext.acceptMass test (DependentPDS.flatten left.val))
          (StrictContext.acceptMass test (DependentPDS.flatten right.val)) ≤
        DependentPDS.contextualEDist left.val right.val
      rw [DependentPDS.contextual_edist_eq_max_edist_flatten]
      exact le_iSup
        (fun current : StrictContext.Test
            (Query U boundary) (FlatAnswer U boundary) =>
          edist
            (StrictContext.acceptMass current (DependentPDS.flatten left.val))
            (StrictContext.acceptMass current
              (DependentPDS.flatten right.val)))
        test

/-! ## The admitted test set -/

/-- The admitted tests: at every dependent boundary the test is either blind
(value `0`) or the acceptance mass of one strict flattened observation.  The
two-sided fibre condition is forced by closure under the total primitive
action, whose mismatch branch is the identity. -/
def strictTests (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] : Set (Phi I U → ℝ≥0∞) :=
  {t | ∀ boundary : Boundary U I,
    (∀ system : DependentRandomSystem U boundary,
      t ⟨boundary, system⟩ = 0) ∨
    ∃ test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary),
      ∀ system : DependentRandomSystem U boundary,
        t ⟨boundary, system⟩ = (strictMass test system : ℝ≥0∞)}

/-- One strict observation at one boundary, read as a test on the whole
heterogeneous carrier: resources at any other boundary are unobserved. -/
def boundaryTest (boundary : Boundary U I)
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary)) :
    Phi I U → ℝ≥0∞ :=
  fun resource =>
    if sourceMatches : resource.boundary = boundary then
      (strictMass test (sourceMatches ▸ resource.system) : ℝ≥0∞)
    else 0

@[simp]
theorem boundary_test_same {boundary : Boundary U I}
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary))
    (system : DependentRandomSystem U boundary) :
    boundaryTest boundary test ⟨boundary, system⟩ =
      (strictMass test system : ℝ≥0∞) := by
  unfold boundaryTest
  exact dif_pos rfl

theorem boundary_test_ne {boundary : Boundary U I}
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary))
    {resource : Phi I U} (different : resource.boundary ≠ boundary) :
    boundaryTest boundary test resource = 0 :=
  dif_neg different

theorem boundary_test_mem_strict_tests (boundary : Boundary U I)
    (test : StrictContext.Test (Query U boundary) (FlatAnswer U boundary)) :
    boundaryTest boundary test ∈ strictTests I U := by
  intro fibre
  by_cases same : fibre = boundary
  · subst same
    exact Or.inr ⟨test, fun system => boundary_test_same test system⟩
  · exact Or.inl fun system => boundary_test_ne test same

/-! ## Closure under the full protocol monoid -/

/-- Fibrewise closure under one arbitrary stateful typed primitive.  The
matching branch absorbs the framed converter into the fibre test; the
mismatch branch is the identity and inherits the fibre condition. -/
theorem strict_tests_comp_act {interface : I}
    (primitive : Primitive I U interface)
    {t : Phi I U → ℝ≥0∞} (admitted : t ∈ strictTests I U) :
    (fun resource => t (primitive.act resource)) ∈ strictTests I U := by
  intro boundary
  by_cases sourceMatches : boundary interface = primitive.source
  · rcases admitted (replaceBoundary boundary interface primitive.target)
      with blind | ⟨test, observed⟩
    · refine Or.inl fun system => ?_
      show t (primitive.act ⟨boundary, system⟩) = 0
      rw [Primitive.act_of_matches primitive boundary sourceMatches system]
      exact blind _
    · refine Or.inr
        ⟨StrictContext.absorb test
          (TypedFraming.framedConverter interface boundary
            primitive.converter sourceMatches),
          fun system => ?_⟩
      show t (primitive.act ⟨boundary, system⟩) = _
      rw [Primitive.act_of_matches primitive boundary sourceMatches system,
        observed]
      exact congrArg _
        (strict_mass_attach interface primitive.converter sourceMatches
          test system)
  · rcases admitted boundary with blind | ⟨test, observed⟩
    · refine Or.inl fun system => ?_
      show t (primitive.act ⟨boundary, system⟩) = 0
      rw [Primitive.act_of_not_matches primitive boundary sourceMatches
        system]
      exact blind system
    · refine Or.inr ⟨test, fun system => ?_⟩
      show t (primitive.act ⟨boundary, system⟩) = _
      rw [Primitive.act_of_not_matches primitive boundary sourceMatches
        system]
      exact observed system

/-- The non-expanding resource endomorphisms whose precomposition preserves
the admitted test set.  "Absorbs into the test set" is a submonoid condition,
so primitive closure extends to the whole generated converter monoid. -/
def absorbingEnd (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] :
    Submonoid (nonexpandingEnd (Phi I U)) where
  carrier := {converter | ∀ t ∈ strictTests I U,
    (fun resource => t (converter.val resource)) ∈ strictTests I U}
  one_mem' := fun _ admitted => admitted
  mul_mem' := fun outer inner t admitted => inner _ (outer t admitted)

theorem mem_absorbing_end {converter : nonexpandingEnd (Phi I U)} :
    converter ∈ absorbingEnd I U ↔
      ∀ t ∈ strictTests I U,
        (fun resource => t (converter.val resource)) ∈ strictTests I U :=
  Iff.rfl

theorem generated_converter_monoid_le_absorbing_end (interface : I) :
    generatedConverterMonoid (I := I) (U := U) interface ≤
      absorbingEnd I U := by
  refine Submonoid.closure_le.mpr ?_
  rintro _ ⟨primitive, rfl⟩
  exact mem_absorbing_end.mpr fun t admitted =>
    strict_tests_comp_act primitive admitted

theorem mrange_protocol_end_hom_le_absorbing_end [Fintype I] :
    MonoidHom.mrange (protocolEndHom (I := I) (U := U)) ≤
      absorbingEnd I U := by
  unfold protocolEndHom
  rw [MonoidHom.noncommPiCoprod_mrange]
  refine iSup_le fun interface => ?_
  rw [mrange_gammaInclusion_eq_generatedConverterMonoid]
  exact generated_converter_monoid_le_absorbing_end interface

/-- MauRen11 Definition 16's closure over the whole protocol monoid: the AC
tuple action is a product of generated one-interface converters, each of
which absorbs. -/
theorem strict_tests_comp_smul [Fintype I] (protocol : Protocol I U)
    {t : Phi I U → ℝ≥0∞} (admitted : t ∈ strictTests I U) :
    (fun resource => t (protocol • resource)) ∈ strictTests I U :=
  mem_absorbing_end.mp
    (mrange_protocol_end_hom_le_absorbing_end
      (MonoidHom.mem_mrange.mpr ⟨protocol, rfl⟩))
    t admitted

/-! ## The distinguisher class -/

/-- **The first concrete `DistinguisherClass`** (MauRen11 Definitions 15–16,
pp. 13–14): strict flattened observations of the typed heterogeneous
carrier, closed under emulation of every AC protocol. -/
def strictTestClass (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] [Fintype I] :
    DistinguisherClass (Protocol I U) (Phi I U) where
  tests := strictTests I U
  test_le_one := by
    intro t admitted resource
    obtain ⟨boundary, system⟩ := resource
    rcases admitted boundary with blind | ⟨test, observed⟩
    · rw [blind system]
      exact zero_le_one
    · rw [observed system]
      exact_mod_cast strict_mass_le_one test system
  test_attach := by
    intro protocol t admitted
    exact strict_tests_comp_smul protocol admitted

@[simp]
theorem strict_test_class_tests [Fintype I] :
    (strictTestClass I U).tests = strictTests I U :=
  rfl

/-! ## The derived metric versus the installed metric -/

/-- The `ℝ≥0∞`-valued symmetric difference of two coerced masses is their
`NNReal` extended distance. -/
theorem coe_tsub_sup_coe_tsub_eq_edist (left right : NNReal) :
    ((left : ℝ≥0∞) - right) ⊔ ((right : ℝ≥0∞) - left) = edist left right := by
  rw [edist_nndist, NNReal.nndist_eq, ENNReal.coe_max, ENNReal.coe_sub,
    ENNReal.coe_sub]

/-- **The sound global direction**: the derived class metric is dominated by
the installed contextual metric.  On a fixed boundary this is sharp
(`strict_test_class_edistD_same_boundary`); across boundaries it is strict
(`strict_test_class_edistD_lt_edist_of_boundary_ne`), so a global equality is
false and is not claimed. -/
theorem strict_test_class_edistD_le_edist [Fintype I]
    (left right : Phi I U) :
    (strictTestClass I U).edistD left right ≤ edist left right := by
  refine iSup₂_le fun t admitted => ?_
  obtain ⟨leftBoundary, leftSystem⟩ := left
  obtain ⟨rightBoundary, rightSystem⟩ := right
  by_cases same : leftBoundary = rightBoundary
  · subst same
    rw [Resource.edist_same]
    rcases admitted leftBoundary with blind | ⟨test, observed⟩
    · simp [DistinguisherClass.adv, blind leftSystem, blind rightSystem]
    · unfold DistinguisherClass.adv
      rw [observed leftSystem, observed rightSystem,
        coe_tsub_sup_coe_tsub_eq_edist]
      exact edist_strict_mass_le test leftSystem rightSystem
  · rw [Resource.edist_ne same]
    exact le_top

/-- **Fibrewise metric full abstraction for the class**: on one fixed
boundary the derived class metric is exactly the installed contextual
metric.  The sharp direction compiles the contextual supremum to strict
flattened tests (`contextual_edist_eq_max_edist_flatten`), each of which is
an admitted `boundaryTest`. -/
theorem strict_test_class_edistD_same_boundary [Fintype I]
    (boundary : Boundary U I)
    (left right : DependentRandomSystem U boundary) :
    (strictTestClass I U).edistD ⟨boundary, left⟩ ⟨boundary, right⟩ =
      edist (Resource.mk boundary left) (Resource.mk boundary right) := by
  refine le_antisymm (strict_test_class_edistD_le_edist _ _) ?_
  rw [Resource.edist_same]
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      show DependentPDS.contextualEDist left.val right.val ≤
        (strictTestClass I U).edistD
          ⟨boundary, DependentRandomSystem.ofProb left⟩
          ⟨boundary, DependentRandomSystem.ofProb right⟩
      rw [DependentPDS.contextual_edist_eq_max_edist_flatten]
      refine iSup_le fun test => ?_
      calc
        edist
            (StrictContext.acceptMass test (DependentPDS.flatten left.val))
            (StrictContext.acceptMass test (DependentPDS.flatten right.val)) =
            DistinguisherClass.adv (boundaryTest boundary test)
              ⟨boundary, DependentRandomSystem.ofProb left⟩
              ⟨boundary, DependentRandomSystem.ofProb right⟩ := by
          unfold DistinguisherClass.adv
          rw [boundary_test_same, boundary_test_same, strict_mass_of_prob,
            strict_mass_of_prob, coe_tsub_sup_coe_tsub_eq_edist]
        _ ≤ (strictTestClass I U).edistD
              ⟨boundary, DependentRandomSystem.ofProb left⟩
              ⟨boundary, DependentRandomSystem.ofProb right⟩ :=
          (strictTestClass I U).adv_le_edistD
            (boundary_test_mem_strict_tests boundary test) _ _

/-- Across distinct boundaries the two metrics genuinely disagree: every
distinguisher class is `1`-bounded, while the installed heterogeneous metric
is `⊤`.  This is why only the `≤` direction holds globally. -/
theorem strict_test_class_edistD_lt_edist_of_boundary_ne [Fintype I]
    {leftBoundary rightBoundary : Boundary U I}
    (different : leftBoundary ≠ rightBoundary)
    (left : DependentRandomSystem U leftBoundary)
    (right : DependentRandomSystem U rightBoundary) :
    (strictTestClass I U).edistD ⟨leftBoundary, left⟩
        ⟨rightBoundary, right⟩ <
      edist (Resource.mk leftBoundary left)
        (Resource.mk rightBoundary right) := by
  rw [Resource.edist_ne different]
  exact lt_of_le_of_lt ((strictTestClass I U).edistD_le_one _ _)
    ENNReal.one_lt_top

/-! ## The `q`-bounded subclass -/

/-- The `q`-bounded test set: every observed fibre reads through a CR18
distinguisher truncated at `q` queries (`truncDDD`, CR18 §4.10.1), compiled
to a strict test by `StrictContextTotal.testOfTruncDDD`.  A query budget is
thereby a distinguisher-class restriction rather than a converter filter on
the resource. -/
def boundedTests (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] (queryBound : ℕ) :
    Set (Phi I U → ℝ≥0∞) :=
  {t | ∀ boundary : Boundary U I,
    (∀ system : DependentRandomSystem U boundary,
      t ⟨boundary, system⟩ = 0) ∨
    ∃ d : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary),
      ∀ system : DependentRandomSystem U boundary,
        t ⟨boundary, system⟩ =
          (strictMass (StrictContextTotal.testOfTruncDDD queryBound d)
              system : ℝ≥0∞)}

/-- Every budgeted test is an admitted strict test: dropping the budget only
enlarges the class. -/
theorem bounded_tests_subset_strict_tests (queryBound : ℕ) :
    boundedTests I U queryBound ⊆ strictTests I U := by
  intro t admitted boundary
  rcases admitted boundary with blind | ⟨d, observed⟩
  · exact Or.inl blind
  · exact Or.inr
      ⟨StrictContextTotal.testOfTruncDDD queryBound d, observed⟩

theorem boundary_test_mem_bounded_tests (boundary : Boundary U I)
    (queryBound : ℕ)
    (d : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary)) :
    boundaryTest boundary (StrictContextTotal.testOfTruncDDD queryBound d) ∈
      boundedTests I U queryBound := by
  intro fibre
  by_cases same : fibre = boundary
  · subst same
    exact Or.inr ⟨d, fun system => boundary_test_same _ system⟩
  · exact Or.inl fun system => boundary_test_ne _ same

/-- Re-truncating an already truncated distinguisher at a larger budget
changes nothing: the smaller cut has already frozen the run. -/
theorem truncDDD_truncDDD_of_le {X : Type*} {Y : Type*} {small large : ℕ}
    (smaller : small ≤ large) (d : PFunDDS.DDD X Y) :
    PFunDDS.truncDDD large (PFunDDS.truncDDD small d) =
      PFunDDS.truncDDD small d := by
  apply Subtype.ext
  funext history
  by_cases belowLarge : history.length < large
  · exact PFunDDS.truncDDD_val_of_lt belowLarge
  · have largeLe : large ≤ history.length := not_lt.mp belowLarge
    have smallLe : small ≤ history.length := smaller.trans largeLe
    have takeLe : small ≤ (history.take large).length := by
      rw [List.length_take]
      exact le_min smaller smallLe
    rw [PFunDDS.truncDDD_val_of_ge largeLe,
      PFunDDS.truncDDD_val_of_ge smallLe,
      PFunDDS.truncDDD_val_of_ge takeLe, List.take_take,
      min_eq_left smaller]
    rcases d.val (history.take small) with query | bit <;> rfl

theorem test_of_truncDDD_truncDDD_of_le {X : Type*} {Y : Type*}
    {small large : ℕ} (smaller : small ≤ large) (d : PFunDDS.DDD X Y) :
    StrictContextTotal.testOfTruncDDD large (PFunDDS.truncDDD small d) =
      StrictContextTotal.testOfTruncDDD small d :=
  Subtype.ext
    (congrArg StrictContextTotal.protocolOfDDD
      (truncDDD_truncDDD_of_le smaller d))

/-- Budgets filter upward: a `q`-bounded test is `q'`-bounded for every
`q ≤ q'`. -/
theorem bounded_tests_mono {small large : ℕ} (smaller : small ≤ large) :
    boundedTests I U small ⊆ boundedTests I U large := by
  intro t admitted boundary
  rcases admitted boundary with blind | ⟨d, observed⟩
  · exact Or.inl blind
  · refine Or.inr ⟨PFunDDS.truncDDD small d, fun system => ?_⟩
    rw [observed system, test_of_truncDDD_truncDDD_of_le smaller d]

/-- **The `q`-budgeted distinguisher class.**  For a fixed budget,
MauRen11 Definition 16's emulation closure holds only for the neutral
converter — attaching a nontrivial converter changes the budget — so the
class is honest about its converter set: the trivial submonoid
`(⊥ : Submonoid (Protocol I U))`.  Budget shifting under attachment is the
graded statement `strict_tests_comp_smul` on the full class, not a fixed-`q`
closure. -/
def boundedStrictTestClass (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] [Fintype I] (queryBound : ℕ) :
    DistinguisherClass (⊥ : Submonoid (Protocol I U)) (Phi I U) where
  tests := boundedTests I U queryBound
  test_le_one := by
    intro t admitted resource
    obtain ⟨boundary, system⟩ := resource
    rcases admitted boundary with blind | ⟨d, observed⟩
    · rw [blind system]
      exact zero_le_one
    · rw [observed system]
      exact_mod_cast strict_mass_le_one _ system
  test_attach := by
    intro neutral t admitted
    have isOne : (neutral : Protocol I U) = 1 :=
      Submonoid.mem_bot.mp neutral.property
    have unchanged :
        (fun resource : Phi I U => t (neutral • resource)) = t := by
      funext resource
      have : neutral • resource = resource := by
        show (neutral : Protocol I U) • resource = resource
        rw [isOne, one_smul]
      rw [this]
    rw [unchanged]
    exact admitted

@[simp]
theorem bounded_strict_test_class_tests [Fintype I] (queryBound : ℕ) :
    (boundedStrictTestClass I U queryBound).tests =
      boundedTests I U queryBound :=
  rfl

/-- The budgeted class metric is dominated by the full class metric — and
hence, by `strict_test_class_edistD_le_edist`, by the installed contextual
metric. -/
theorem bounded_edistD_le_edistD [Fintype I] (queryBound : ℕ)
    (left right : Phi I U) :
    (boundedStrictTestClass I U queryBound).edistD left right ≤
      (strictTestClass I U).edistD left right := by
  refine iSup₂_le fun t admitted => ?_
  exact (strictTestClass I U).adv_le_edistD
    (bounded_tests_subset_strict_tests queryBound admitted) left right

theorem bounded_edistD_le_edist [Fintype I] (queryBound : ℕ)
    (left right : Phi I U) :
    (boundedStrictTestClass I U queryBound).edistD left right ≤
      edist left right :=
  (bounded_edistD_le_edistD queryBound left right).trans
    (strict_test_class_edistD_le_edist left right)

end

end RandomSystemsCC.TypedDistinguisher
