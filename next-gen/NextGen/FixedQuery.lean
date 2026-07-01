/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.CR18Tactics

/-!
# Fixed-query CR18 transcript laws

This module contains the application-independent fixed-query bridge over the
`NextGen` CR18 transcript-law surface.

Source status:

* support lemma forced by formalization; candidate for upstream: identify
  query-indexed functions `Fin q -> X` with length-`q` CR18 vectors;
* source-theorem bridge: construct the exact fixed-query CR18 environment as a
  generic `DDE X Y`, with no dummy query outside the budget;
* source-theorem bridge: under that fixed-query environment, concrete
  `PFunPDE.transcriptLaw` mass reduces exactly to the CR18 system factor on the
  fixed input tuple and is zero off that tuple.

Migration note: this is the support layer for fixed deterministic environments.
Public H-technique/application endpoints should normally use
`ProbPDS.fixedQueryTranscriptDist` from `Migration.HTechnique.FixedQueryLaw`,
which constructs this environment internally.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace CR18

variable {X Y : Type*} {q : Nat}

/-- Local abbreviation for the CR18 transcript-prefix carrier used in
`NextGen.PDS`. -/
abbrev CR18TranscriptPrefix (X Y : Type*) (q : Nat) :=
  PFunPDE.TranscriptPrefix X Y q

/-- **Support lemma forced by formalization; candidate for upstream.** Convert a
query-indexed tuple to the length-indexed vector used by CR18 transcript
prefixes. -/
def vectorOfFunction (x : Fin q → X) : List.Vector X q :=
  List.Vector.ofFn x

/-- **Support lemma forced by formalization; candidate for upstream.** Convert a
CR18 length-indexed vector back to its query-indexed function. -/
def functionOfVector (v : List.Vector X q) : Fin q → X :=
  fun i => v.get i

@[simp]
theorem functionOfVector_vectorOfFunction (x : Fin q → X) :
    functionOfVector (vectorOfFunction x) = x := by
  funext i
  simp [functionOfVector, vectorOfFunction]

@[simp]
theorem vectorOfFunction_functionOfVector (v : List.Vector X q) :
    vectorOfFunction (functionOfVector v) = v := by
  ext i
  simp [vectorOfFunction, functionOfVector]

/-- **Support lemma forced by formalization; candidate for upstream.** The
canonical equivalence between query-indexed tuples and CR18 length-indexed
vectors. -/
def vectorFunctionEquiv (X : Type*) (q : Nat) : (Fin q → X) ≃ List.Vector X q where
  toFun := vectorOfFunction
  invFun := functionOfVector
  left_inv := by
    intro x
    exact functionOfVector_vectorOfFunction x
  right_inv := by
    intro v
    exact vectorOfFunction_functionOfVector v

@[simp]
theorem vectorFunctionEquiv_apply (x : Fin q → X) :
    vectorFunctionEquiv X q x = vectorOfFunction x := by
  rfl

@[simp]
theorem vectorFunctionEquiv_symm_apply (v : List.Vector X q) :
    (vectorFunctionEquiv X q).symm v = functionOfVector v := by
  rfl

/-- **Support lemma forced by formalization; candidate for upstream.** Embed a
fixed input tuple `xs` and an output tuple `ys` as the CR18 transcript prefix
`(x^q, y^q)`. -/
def fixedInputTranscriptPrefix (xs : Fin q → X) (ys : Fin q → Y) :
    CR18TranscriptPrefix X Y q :=
  (vectorOfFunction xs, vectorOfFunction ys)

/-- **Support lemma forced by formalization; candidate for upstream.** For a
fixed input tuple, embedding output tuples into CR18 transcript prefixes is
injective. -/
theorem fixedInputTranscriptPrefix_injective (xs : Fin q → X) :
    Function.Injective (fixedInputTranscriptPrefix (X := X) (Y := Y) (q := q) xs) := by
  intro y₁ y₂ h
  have hvec : vectorFunctionEquiv Y q y₁ = vectorFunctionEquiv Y q y₂ := by
    simpa using congrArg Prod.snd h
  exact (vectorFunctionEquiv Y q).injective hvec

/-- **Support lemma forced by formalization; candidate for upstream.** Lift an
output-vector distribution to the fixed-input transcript-prefix carrier by the
exact embedding `ys ↦ (xs, ys)`. This is a deterministic pushforward, so it adds
no default value and no over-approximation. -/
def fixedInputLiftDist (xs : Fin q → X) (D : RandomSystems.Dist (Fin q → Y)) :
    RandomSystems.Dist (CR18TranscriptPrefix X Y q) := by
  classical
  exact RandomSystems.Dist.fTransform (fixedInputTranscriptPrefix xs) D

/-- **Support lemma forced by formalization; candidate for upstream.** The
fixed-input lift has exactly the original output-vector mass at embedded
transcript prefixes. -/
theorem fixedInputLiftDist_apply_fixed
    (xs : Fin q → X) (ys : Fin q → Y) (D : RandomSystems.Dist (Fin q → Y)) :
    fixedInputLiftDist xs D (fixedInputTranscriptPrefix xs ys) = D ys := by
  classical
  exact RandomSystems.Dist.fTransform_injective_apply D (fixedInputTranscriptPrefix xs)
    (fixedInputTranscriptPrefix_injective xs) ys

/-- **Support lemma forced by formalization; candidate for upstream.** The
fixed-input lift has zero mass outside the fixed input tuple. -/
theorem fixedInputLiftDist_apply_of_input_ne
    (xs : Fin q → X) (D : RandomSystems.Dist (Fin q → Y))
    (xv : List.Vector X q) (yv : List.Vector Y q) (h : xv ≠ vectorOfFunction xs) :
    fixedInputLiftDist xs D (xv, yv) = 0 := by
  classical
  refine RandomSystems.Dist.fTransform_apply_of_forall_ne D
    (fixedInputTranscriptPrefix (X := X) (Y := Y) (q := q) xs) (xv, yv) ?_
  intro ys hys
  exact h (congrArg Prod.fst hys).symm

/-- **Support lemma forced by formalization; candidate for upstream.** A
deterministic fixed-input lift preserves total mass. -/
theorem fixedInputLiftDist_weight (xs : Fin q → X)
    (D : RandomSystems.Dist (Fin q → Y)) :
    (fixedInputLiftDist xs D).weight = D.weight := by
  classical
  simp [fixedInputLiftDist, RandomSystems.Dist.weight_fTransform]

/-- **Support lemma forced by formalization; candidate for upstream.** A
pointwise lower bound on output-vector laws transfers through the exact
fixed-input transcript-prefix lift.  The off-fixed-input branch is tight: both
lifted laws have zero mass there. -/
theorem fixedInputLiftDist_pointwise_lower_bound
    (xs : Fin q → X) (real ideal : RandomSystems.Dist (Fin q → Y))
    (eps : NNReal)
    (h_lower : ∀ ys : Fin q → Y, (1 - eps) * ideal ys ≤ real ys)
    (t : CR18TranscriptPrefix X Y q) :
    (1 - eps) * fixedInputLiftDist xs ideal t ≤ fixedInputLiftDist xs real t := by
  rcases t with ⟨xv, yv⟩
  by_cases hxv : xv = vectorOfFunction xs
  · subst xv
    let ys : Fin q → Y := functionOfVector yv
    have ht : (vectorOfFunction xs, yv) = fixedInputTranscriptPrefix xs ys := by
      simp [fixedInputTranscriptPrefix, ys]
    rw [ht, fixedInputLiftDist_apply_fixed, fixedInputLiftDist_apply_fixed]
    exact h_lower ys
  · rw [fixedInputLiftDist_apply_of_input_ne xs ideal xv yv hxv,
      fixedInputLiftDist_apply_of_input_ne xs real xv yv hxv]
    simp

/-- **Support lemma forced by formalization; candidate for upstream.** A
deterministic transformation of visible output tuples commutes with the exact
fixed-input transcript lift.  The transcript map ignores off-fixed-input mass
because `fixedInputLiftDist xs' D` is supported exactly on the fixed input
tuple `xs'`. -/
theorem fixedInputLiftDist_fTransform
    {X' Y' : Type*} {q' : Nat}
    (xs : Fin q → X) (xs' : Fin q' → X')
    (f : (Fin q' → Y') → (Fin q → Y))
    (D : RandomSystems.Dist (Fin q' → Y')) :
    fixedInputLiftDist xs (RandomSystems.Dist.fTransform f D) =
      RandomSystems.Dist.fTransform
        (fun t : CR18TranscriptPrefix X' Y' q' =>
          fixedInputTranscriptPrefix xs (f (functionOfVector t.2)))
        (fixedInputLiftDist xs' D) := by
  unfold fixedInputLiftDist
  rw [RandomSystems.Dist.fTransform_comp, RandomSystems.Dist.fTransform_comp]
  congr 1
  funext ys
  simp [fixedInputTranscriptPrefix]

/-- **Source-theorem bridge.** The deterministic CR18 environment that asks the
fixed query tuple `xs` and then stops.  Its input is the previous output history
in `Y ∪ {⊥}`; the next query is selected by the length of that history. -/
def fixedQueryDDE (xs : Fin q → X) :
    PFunDDS.DDE X Y :=
  fun ys => if h : ys.length < q then some (xs ⟨ys.length, h⟩) else none

/-- **Source-theorem bridge.** The fixed-query DDE as a deterministic PDE
random variable over the unit experiment. -/
def fixedQueryEnvironment (xs : Fin q → X) :
    PFunPDE.RV PUnit X Y :=
  fun _ => fixedQueryDDE xs

/-- **UPSTREAM-CANDIDATE.** Transcript distribution for a law-level PDS against
the deterministic fixed-query CR18 environment.  This is the owner-level
constructor behind the H-technique fixed-query surface: its public inputs are
only the PDS law and the fixed query vector, and the CR18 environment is built
inside the definition. -/
noncomputable def PFunPDS.Prob.fixedQueryTranscriptDist
    (S : PFunPDS.Prob X Y) (xs : Fin q → X)
    [Fintype (CR18TranscriptPrefix X Y q)] :
    RandomSystems.Dist (CR18TranscriptPrefix X Y q) :=
  PFunPDS.Prob.deterministicTranscriptDist (q := q) S (fixedQueryDDE (Y := Y) xs)

/-- **Source-theorem bridge.** The fixed-query environment is total for exactly
its `q` scheduled queries. -/
theorem fixedQueryEnvironment_KQueryTotal (xs : Fin q → X) :
    PFunPDE.RV.KQueryTotal (fixedQueryEnvironment (Y := Y) xs) q := by
  intro ω ys hlen
  refine ⟨xs ⟨ys.length, hlen⟩, ?_⟩
  simp [fixedQueryEnvironment, fixedQueryDDE, hlen]

@[simp]
theorem fixedQueryDDE_apply_of_lt (xs : Fin q → X)
    (ys : List (Option Y)) (h : ys.length < q) :
    fixedQueryDDE xs ys = some (xs ⟨ys.length, h⟩) := by
  simp [fixedQueryDDE, h]

/-- **Source-theorem bridge.** A length-`q` transcript prefix is compatible with
the fixed-query environment exactly when its input vector is the fixed query
tuple. This is the precise CR18 environment condition `E() = x1, E(y1)=x2, ...`;
no default value or over-approximation is used. -/
theorem transcriptEnvironmentEvent_fixedQueryEnvironment_iff
    (xs : Fin q → X) (xv : List.Vector X q) (yv : List.Vector Y q) :
    PFunPDE.transcriptEnvironmentEvent
        (fixedQueryEnvironment xs) xv yv PUnit.unit ↔
      xv = vectorOfFunction xs := by
  constructor
  · intro h
    ext i
    have hi : i.1 < q := i.2
    have hstep := h i.1 hi
    have hylen : yv.toList.length = q := yv.2
    have hlen_eq : ((yv.toList.take i.1).map some).length = i.1 := by
      rw [List.length_map, List.length_take, hylen, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hlen : ((yv.toList.take i.1).map some).length < q := by
      rw [hlen_eq]
      exact hi
    have hidx : (⟨((yv.toList.take i.1).map some).length, hlen⟩ : Fin q) = i := by
      ext
      exact hlen_eq
    rw [fixedQueryEnvironment, fixedQueryDDE_apply_of_lt xs _ hlen] at hstep
    have hxs : xs (⟨((yv.toList.take i.1).map some).length, hlen⟩ : Fin q) = xs i :=
      congrArg xs hidx
    have hxi : xv.get i = xs i :=
      (Option.some.inj hstep).symm.trans hxs
    simpa [vectorOfFunction] using hxi
  · intro hx
    subst hx
    intro i hi
    have hylen : yv.toList.length = q := yv.2
    have hlen_eq : ((yv.toList.take i).map some).length = i := by
      rw [List.length_map, List.length_take, hylen, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hlen : ((yv.toList.take i).map some).length < q := by
      rw [hlen_eq]
      exact hi
    have hidx : (⟨((yv.toList.take i).map some).length, hlen⟩ : Fin q) = ⟨i, hi⟩ := by
      ext
      exact hlen_eq
    rw [fixedQueryEnvironment, fixedQueryDDE_apply_of_lt xs _ hlen]
    rw [show xs (⟨((yv.toList.take i).map some).length, hlen⟩ : Fin q) =
        xs ⟨i, hi⟩ from congrArg xs hidx]
    simp [vectorOfFunction]

/-- **Source-theorem bridge.** Under the fixed-query environment, the CR18
environment factor has mass `1` when the transcript input vector is exactly the
fixed query tuple. -/
theorem transcriptEnvironmentFactor_fixedQueryEnvironment_of_eq
    (xs : Fin q → X) (xv : List.Vector X q) (yv : List.Vector Y q)
    (h : xv = vectorOfFunction xs) :
    PFunPDE.transcriptEnvironmentFactor RandomSystems.Dist.unitProbDist.{0}
      (fixedQueryEnvironment xs) xv yv = 1 := by
  unfold PFunPDE.transcriptEnvironmentFactor
  change (RandomSystems.Dist.uniform PUnit).mass
      (PFunPDE.transcriptEnvironmentEvent
        (fixedQueryEnvironment xs) xv yv) = 1
  have hcongr :
      (RandomSystems.Dist.uniform PUnit).mass
          (PFunPDE.transcriptEnvironmentEvent
            (fixedQueryEnvironment xs) xv yv) =
        (RandomSystems.Dist.uniform PUnit).mass (fun _ : PUnit => True) := by
    apply RandomSystems.Dist.mass_congr
    intro ω
    cases ω
    rw [transcriptEnvironmentEvent_fixedQueryEnvironment_iff]
    simp [h]
  rw [hcongr, RandomSystems.Dist.mass_true, RandomSystems.Dist.weight_uniform]

/-- **Source-theorem bridge.** Under the fixed-query environment, the CR18
environment factor has mass `0` when the transcript input vector is not the
fixed query tuple. -/
theorem transcriptEnvironmentFactor_fixedQueryEnvironment_of_ne
    (xs : Fin q → X) (xv : List.Vector X q) (yv : List.Vector Y q)
    (h : xv ≠ vectorOfFunction xs) :
    PFunPDE.transcriptEnvironmentFactor RandomSystems.Dist.unitProbDist.{0}
      (fixedQueryEnvironment xs) xv yv = 0 := by
  unfold PFunPDE.transcriptEnvironmentFactor
  change (RandomSystems.Dist.uniform PUnit).mass
      (PFunPDE.transcriptEnvironmentEvent
        (fixedQueryEnvironment xs) xv yv) = 0
  have hcongr :
      (RandomSystems.Dist.uniform PUnit).mass
          (PFunPDE.transcriptEnvironmentEvent
            (fixedQueryEnvironment xs) xv yv) =
        (RandomSystems.Dist.uniform PUnit).mass (fun _ : PUnit => False) := by
    apply RandomSystems.Dist.mass_congr
    intro ω
    cases ω
    rw [transcriptEnvironmentEvent_fixedQueryEnvironment_iff]
    simp [h]
  rw [hcongr, RandomSystems.Dist.mass_eq_sum]
  simp

/-- **Source-theorem bridge.** A concrete `PFunPDE.transcriptLaw` under the
fixed-query environment reduces to the system factor on the fixed input vector.
Applications only have to identify this system factor with their concrete
fixed-transcript mass function. -/
theorem transcriptLaw_fixedQueryEnvironment_of_eq {Ω : Type*}
    (pS : RandomSystems.Dist.ProbDist Ω)
    (S : PFunPDS.RV Ω X Y)
    (xs : Fin q → X) (yv : List.Vector Y q) :
    PFunPDE.transcriptLaw pS RandomSystems.Dist.unitProbDist.{0} S
        (fixedQueryEnvironment xs) q (vectorOfFunction xs, yv) =
      PFunPDE.transcriptSystemFactor pS S (vectorOfFunction xs) yv := by
  cr18_transcript
  rw [transcriptEnvironmentFactor_fixedQueryEnvironment_of_eq xs (vectorOfFunction xs) yv rfl]
  simp

/-- **Source-theorem bridge.** A concrete `PFunPDE.transcriptLaw` under the
fixed-query environment assigns zero mass to transcript prefixes whose input
vector is not the fixed query tuple. -/
theorem transcriptLaw_fixedQueryEnvironment_of_ne {Ω : Type*}
    (pS : RandomSystems.Dist.ProbDist Ω)
    (S : PFunPDS.RV Ω X Y)
    (xs : Fin q → X) (xv : List.Vector X q) (yv : List.Vector Y q)
    (h : xv ≠ vectorOfFunction xs) :
    PFunPDE.transcriptLaw pS RandomSystems.Dist.unitProbDist.{0} S
        (fixedQueryEnvironment xs) q (xv, yv) = 0 := by
  cr18_transcript
  rw [transcriptEnvironmentFactor_fixedQueryEnvironment_of_ne xs xv yv h]
  simp

end CR18
end RandomSystems
