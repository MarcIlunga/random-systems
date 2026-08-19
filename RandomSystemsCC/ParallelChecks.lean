/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.ResourceParallel

/-!
# Regression: the parallel axis, exercised on a concrete carrier

A minimal `⊕`-closed signature universe (free binary sums over one `Bool`
signature) instantiates every class of the parallel axis, and the AC
parallel calculus is *applied*, not merely type-checked:

* `extract_constructs` — a genuine construction at radius zero: the
  left-interface extraction converter constructs the left component from
  a parallel composition (behavioral content:
  `System.apply_embedInl_parallel`);
* `extract_constructs_par` — **`Constructs.eball_par_resource` applied on
  the concrete carrier**: the same construction remains valid with an
  untouched right context, at protocol `π ∥ 1`;
* `constant_resources_distinct` / `par_constant_resources_distinct` — the
  non-vacuity receipts: two same-code resources are separated by a
  one-query strict test, and parallel composition *remembers* its
  components (`Resource.par_ne_left`, i.e. strict cancellation), so
  nothing above is true by degeneracy.
-/

namespace RandomSystemsCC.ParallelChecks

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.StrictContext
open RandomSystemsCC.CR18
open scoped AbstractCrypto Classical PFunDDS

/-! ## A `⊕`-closed demo signature universe -/

/-- Free binary sums over one base signature. -/
inductive DemoCode : Type
  | base
  | sum (left right : DemoCode)
  deriving DecidableEq

/-- `Bool` at the base; tagged sums at a sum code. -/
def demoAlphabet : DemoCode → Type
  | .base => Bool
  | .sum left right => demoAlphabet left ⊕ demoAlphabet right

/-- The demo universe: codes are free sums, both alphabets are
`demoAlphabet`. -/
def DemoU : SignatureUniverse :=
  ⟨DemoCode, demoAlphabet, demoAlphabet⟩

instance : DecidableEq DemoU.Code :=
  inferInstanceAs (DecidableEq DemoCode)

instance : HasSumCode DemoU where
  sumCode := .sum
  inputEquiv _ _ := Equiv.refl _
  outputEquiv _ _ := Equiv.refl _
  sumCode_inj h := by
    injection h with h₁ h₂
    exact ⟨h₁, h₂⟩

/-! ## Concrete resources at the base signature -/

/-- The deterministic constant-answer oracle. -/
def constantSystem (answer : Bool) : PFunDDS.DDS Bool Bool :=
  ⟨fun history => ⟨history ≠ [], fun _ => answer⟩,
    ⟨fun h => (h : ¬([] : List Bool) = []) rfl,
      fun _ hne _ => hne⟩⟩

/-- Its point-mass law. -/
noncomputable def constantLaw (answer : Bool) : PFunPDS.Prob Bool Bool :=
  ⟨Finsupp.single (constantSystem answer) 1, by
    show RandomSystems.Dist.weight _ = 1
    rw [RandomSystems.Dist.weight_eq_finsupp_sum,
      Finsupp.sum_single_index rfl]⟩

/-- The constant oracle as a resource at the base signature. -/
noncomputable def constantResource (answer : Bool) : Resource DemoU :=
  ⟨DemoCode.base, System.ofProb (constantLaw answer)⟩

/-! ## The extraction construction and the AC parallel calculus -/

/-- The left-interface extraction converter, placed between the sum code
and the base. -/
def extractLeft : Primitive DemoU :=
  ⟨DemoCode.sum .base .base, DemoCode.base, embedInlFn, isDDC_embedInlFn⟩

/-- The behavioral fact: extraction applied to a parallel composition of
base resources is the left component. -/
theorem extractLeft_act (left right : System Bool Bool) :
    extractLeft.act
        ((⟨DemoCode.base, left⟩ : Resource DemoU) ∥ ⟨DemoCode.base, right⟩)
      = ⟨DemoCode.base, left⟩ := by
  -- `DemoU`'s sum alphabets *are* the tagged sums, so the boundary
  -- relabelling of `∥` is the identity relabelling (`System.relabel_refl`).
  have hpar : ((⟨DemoCode.base, left⟩ : Resource DemoU) ∥
        ⟨DemoCode.base, right⟩)
      = ⟨extractLeft.source, System.parallel left right⟩ :=
    congrArg
      (fun behavior : System (Bool ⊕ Bool) (Bool ⊕ Bool) =>
        (⟨DemoCode.sum DemoCode.base DemoCode.base, behavior⟩ : Resource DemoU))
      (System.relabel_refl (System.parallel left right))
  rw [hpar, Primitive.act_of_matches]
  exact congrArg _ (System.apply_embedInl_parallel left right)

/-- **A worked construction at radius zero**: extraction constructs the
left component from a parallel composition. -/
theorem extract_constructs (left right : System Bool Bool) :
    ApproximatelyConstructs (ParProtocol.ofPrimitive extractLeft) 0
      ({(⟨DemoCode.base, left⟩ : Resource DemoU) ∥
        ⟨DemoCode.base, right⟩} : Set (Resource DemoU))
      {(⟨DemoCode.base, left⟩ : Resource DemoU)} := by
  rw [ApproximatelyConstructs, constructs_singleton_eball_iff]
  rw [show ParProtocol.ofPrimitive extractLeft •
        ((⟨DemoCode.base, left⟩ : Resource DemoU) ∥ ⟨DemoCode.base, right⟩)
      = extractLeft.act
        ((⟨DemoCode.base, left⟩ : Resource DemoU) ∥ ⟨DemoCode.base, right⟩)
    from rfl]
  rw [extractLeft_act, edist_self]

/-- **`Constructs.eball_par_resource`, applied on the concrete carrier**:
the extraction construction remains valid with an untouched right
context, at protocol `π ∥ 1`.  This exercises `Par` on both carriers,
`SMulParClass`, and `IsNonexpandingPar` in one AC theorem. -/
theorem extract_constructs_par (left right ctx : System Bool Bool) :
    ApproximatelyConstructs
      (ParProtocol.ofPrimitive extractLeft ∥ (1 : ParProtocol DemoU)) 0
      ({((⟨DemoCode.base, left⟩ : Resource DemoU) ∥
          ⟨DemoCode.base, right⟩) ∥ ⟨DemoCode.base, ctx⟩} :
        Set (Resource DemoU))
      {(⟨DemoCode.base, left⟩ : Resource DemoU) ∥ ⟨DemoCode.base, ctx⟩} :=
  Constructs.eball_par_resource (extract_constructs left right)
    ⟨DemoCode.base, ctx⟩

/-! ## Non-vacuity: the strict metric separates, and `‖` remembers -/

/-- The one-query reader: query once, output the answer as the verdict. -/
def readTest : Test Bool Bool :=
  ⟨simpleFn (fun _ => true) id, isDDC_simpleFn _ _⟩

/-- The reader observes the constant oracle's answer. -/
theorem observe_readTest_constant (answer : Bool) :
    answer ∈ observe readTest (constantSystem answer) := by
  rw [observe, show readTest.val = simpleFn (fun _ => true) id from rfl,
    mem_applyRaw]
  refine ⟨2, ?_⟩
  rw [mem_applyRawAt_iff]
  have hout : PFunDDS.output ((constantSystem answer)⊥)
      ([] ++ [true]) (by rw [PFunDDS.dom_fullyDefined]; simp)
      = some answer := by
    rw [PFunDDS.output_fullyDefined_append_of_mem (constantSystem answer)
      [] true (Or.inr rfl) (by show ¬([true] : List Bool) = []; simp)]
    rfl
  have hround : ((answer : Bool), [true], [some answer]) ∈
      drive (simpleFn (fun _ : Unit => true) (id : Bool → Bool))
        (constantSystem answer) 2 [()] [] [] := by
    have hm : Sum.inl true ∈
        simpleFn (fun _ : Unit => true) (id : Bool → Bool) ([()], []) := by
      have := simpleFn_inl_mem (fun _ : Unit => true) (id : Bool → Bool)
        (us := [()]) (ys := []) (by simp)
      simpa using this
    refine drive_mem_query _ (constantSystem answer) hm ?_
    rw [hout]
    have hm₂ : Sum.inr answer ∈
        simpleFn (fun _ : Unit => true) (id : Bool → Bool)
          ([()], [some answer]) := by
      have := simpleFn_inr_mem (fun _ : Unit => true) (id : Bool → Bool)
        (us := [()]) (ys := [some answer]) (by simp) (by simp)
        (y := answer) (by simp)
      simpa using this
    exact drive_mem_answer _ (constantSystem answer) hm₂ 0
  refine ⟨([answer], [true], [some answer]), ?_, by simp⟩
  simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
  exact ⟨(answer, [true], [some answer]), hround,
    ([], [true], [some answer]), by simp, rfl⟩

/-- Strict acceptance separates the two constant laws. -/
theorem acceptMass_readTest_constant (answer : Bool) :
    acceptMass readTest (constantLaw answer).val
      = if answer then 1 else 0 := by
  show RandomSystems.Dist.mass
      (Finsupp.single (constantSystem answer) 1) _ = _
  rw [RandomSystems.Dist.mass]
  rw [Finsupp.sum_single_index (by simp)]
  by_cases h : answer = true
  · subst h
    rw [if_pos (observe_readTest_constant true), if_pos rfl]
  · have hfalse : answer = false := by
      cases answer
      · rfl
      · exact absurd rfl h
    subst hfalse
    rw [if_neg, if_neg (by simp)]
    intro htrue
    exact Bool.noConfusion
      (Part.mem_unique htrue (observe_readTest_constant false))

/-- **Non-vacuity of the carrier**: two same-code resources at genuinely
different behavior are distinct — the strict metric separates them. -/
theorem constant_resources_distinct :
    constantResource true ≠ constantResource false := by
  intro h
  have hsys : System.ofProb (constantLaw true)
      = System.ofProb (constantLaw false) := by
    have := (Resource.mk.injEq _ _ _ _).mp h
    exact eq_of_heq this.2
  have hequiv : StrictContext.Equivalent
      (constantLaw true).val (constantLaw false).val :=
    Quotient.exact hsys
  have := hequiv readTest
  rw [acceptMass_readTest_constant, acceptMass_readTest_constant] at this
  simp at this

/-- **Non-vacuity of `Par`**: parallel composition remembers its
components — strict cancellation at work. -/
theorem par_constant_resources_distinct :
    constantResource true ∥ constantResource false ≠
      constantResource false ∥ constantResource false :=
  Resource.par_ne_left constant_resources_distinct

end RandomSystemsCC.ParallelChecks
