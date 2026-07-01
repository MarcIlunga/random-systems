/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.FixedQuery
import NextGen.Counting

/-!
# Function-evaluator CR18 systems

This module contains application-independent CR18 facts for systems sampled as
ordinary functions and embedded through `PFunDDS.functionEvaluator`.

Source status:

* support lemma forced by formalization; candidate for upstream: a
  function-valued random system embedded via `PFunDDS.functionEvaluator` has a
  transcript system event exactly when the sampled function matches the output
  vector on the input vector.
* support lemma forced by formalization; candidate for upstream: evaluating a
  uniform random function on an injective fixed query vector yields the uniform
  distribution on output vectors.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace CR18

/-- **Support lemma forced by formalization; candidate for upstream.** A
function-valued random system embedded as a CR18 `functionEvaluator`. -/
def functionEvaluatorRV {Ω X Y : Type*} (F : Ω → X → Y) :
    PFunPDS.RV Ω X Y :=
  fun ω => PFunDDS.functionEvaluator (F ω)

/-- **UPSTREAM-CANDIDATE.** A law-level CR18 PDS obtained by sampling an ordinary
function and embedding it as a `PFunDDS.functionEvaluator`. -/
noncomputable def PFunPDS.Prob.functionEvaluator {Ω X Y : Type*}
    (p : Dist.ProbDist Ω) (F : Ω → X → Y) :
    PFunPDS.Prob X Y :=
  Dist.PMF p (functionEvaluatorRV F)

/-- **Support lemma forced by formalization; candidate for upstream.** The
`i+1` prefix is the `i` prefix followed by the original `i`-th entry. -/
theorem list_take_succ_eq_take_append_get {α : Type*} (l : List α) (i : Fin l.length) :
    l.take (i.1 + 1) = l.take i.1 ++ [l.get i] := by
  exact (List.take_concat_get' l i.1 i.2).symm

/-- **Support lemma forced by formalization; candidate for upstream.** Evaluating
a function-evaluator system on an appended current input returns the sampled
function at that input.  This is the RV/eval bridge to
`PFunDDS.functionEvaluator_output`. -/
theorem functionEvaluatorRV_eval_append {Ω X Y : Type*}
    (F : Ω → X → Y) (ω : Ω) (l : List X) (x : X) :
    RandomSystems.Dist.RV.eval
        (PFunPDS.funView (functionEvaluatorRV F))
        (l ++ [x]) ω = Part.some (F ω x) := by
  unfold RandomSystems.Dist.RV.eval PFunPDS.funView functionEvaluatorRV
  show (PFunDDS.functionEvaluator (F ω)).1 (l ++ [x]) =
    Part.some (F ω x)
  have hdom : ((PFunDDS.functionEvaluator (F ω)).1 (l ++ [x])).Dom := by
    simp [PFunDDS.functionEvaluator]
  rw [← Part.some_get hdom]
  congr 1
  change PFunDDS.output
      (PFunDDS.functionEvaluator (F ω)) (l ++ [x]) ?_ = F ω x
  exact PFunDDS.functionEvaluator_output (F ω) l x _

/-- **Support lemma forced by formalization; candidate for upstream.** Evaluating
a function-evaluator system on the `i+1` prefix returns the sampled function at
the `i`-th input. -/
theorem functionEvaluatorRV_eval_vector_take_succ {Ω X Y : Type*}
    (F : Ω → X → Y) {k : Nat} (xs : List.Vector X k) (ω : Ω) (i : Fin k) :
    RandomSystems.Dist.RV.eval
        (PFunPDS.funView (functionEvaluatorRV F))
        (xs.toList.take (i.1 + 1)) ω = Part.some (F ω (xs.get i)) := by
  rw [list_take_succ_eq_take_append_get (l := xs.toList) ⟨i.1, by simp [i.2]⟩]
  exact functionEvaluatorRV_eval_append F ω (xs.toList.take i.1) (xs.get i)

/-- **Support lemma forced by formalization; candidate for upstream.** For a
function-evaluator system, the CR18 system rectangle event is just pointwise
agreement between the sampled function and the fixed output vector. -/
theorem transcriptSystemEvent_functionEvaluatorRV_iff {Ω X Y : Type*}
    (F : Ω → X → Y) {k : Nat} (xs : List.Vector X k) (ys : List.Vector Y k)
    (ω : Ω) :
    PFunPDE.transcriptSystemEvent
        (functionEvaluatorRV F) xs ys ω ↔
      ∀ i : Fin k, F ω (xs.get i) = ys.get i := by
  constructor
  · intro h i
    have hstep := h i.1 i.2
    rw [functionEvaluatorRV_eval_vector_take_succ F xs ω i] at hstep
    simpa using hstep
  · intro h i hi
    rw [functionEvaluatorRV_eval_vector_take_succ F xs ω ⟨i, hi⟩]
    simpa using h ⟨i, hi⟩

/-- **Support lemma forced by formalization; candidate for upstream.**
Evaluating a uniform random function on an injective fixed query vector gives
the uniform distribution on output vectors.  The statement deliberately has no
`[Nonempty X]` hypothesis: for `q = 0` the output vector space is already
inhabited, and for `q > 0` the tuple `xs : Fin q -> X` supplies an input. -/
theorem uniformFunction_eval_uniform {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : ℕ} (xs : Fin q → X) (hxs : Function.Injective xs) :
    RandomSystems.Dist.fTransform
        (fun f : X → Y => fun i : Fin q => f (xs i))
        (RandomSystems.Dist.uniform (X → Y)) =
      RandomSystems.Dist.uniform (Fin q → Y) := by
  classical
  let evalTuple : (X → Y) → (Fin q → Y) := fun f => fun i => f (xs i)
  change RandomSystems.Dist.fTransform evalTuple (RandomSystems.Dist.uniform (X → Y)) =
      RandomSystems.Dist.uniform (Fin q → Y)
  refine RandomSystems.Dist.fTransform_uniform_eq_uniform_of_card_fiber_mul evalTuple ?_
  intro ys
  have hq : q ≤ Fintype.card X :=
    Fintype.card_fin q ▸ Fintype.card_le_of_injective xs hxs
  have hnat : ((Finset.univ.filter (fun f : X → Y => evalTuple f = ys)).card) *
      Fintype.card (Fin q → Y) = Fintype.card (X → Y) := by
    have hfiber : ((Finset.univ.filter (fun f : X → Y => evalTuple f = ys)).card) =
        Fintype.card Y ^ (Fintype.card X - q) := by
      simpa [evalTuple] using
        (RandomSystems.CR18.Counting.card_function_fiber_multipoint
          (X := X) (Y := Y) xs ys hxs)
    calc
      ((Finset.univ.filter (fun f : X → Y => evalTuple f = ys)).card) *
          Fintype.card (Fin q → Y)
          = Fintype.card Y ^ (Fintype.card X - q) * Fintype.card (Fin q → Y) := by
            rw [hfiber]
      _ = Fintype.card (X → Y) := by
            rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
            rw [← pow_add, Nat.sub_add_cancel hq]
  convert hnat using 1
  apply congrArg (fun n => n * Fintype.card (Fin q → Y))
  apply congrArg Finset.card
  ext f
  simp

/-- **Source-theorem bridge; candidate for upstream.** For any sampled
function-evaluator random system under the exact fixed-query environment, the
CR18 transcript-prefix law is exactly the fixed-input lift of the output-vector
law obtained by evaluating the sampled function on the fixed query vector. -/
theorem transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist
    {Ω X Y : Type*} {q : Nat} [Fintype (CR18TranscriptPrefix X Y q)]
    (pΩ : RandomSystems.Dist.ProbDist Ω) (F : Ω → X → Y) (xs : Fin q → X) :
    PFunPDE.transcriptLawDist
        (PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
          (functionEvaluatorRV F) (fixedQueryEnvironment xs) q) =
      fixedInputLiftDist xs
        (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i)) pΩ.val) := by
  classical
  apply Finsupp.ext
  intro t
  rcases t with ⟨xv, yv⟩
  by_cases hxv : xv = vectorOfFunction xs
  · subst xv
    calc
      PFunPDE.transcriptLawDist
          (PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
            (functionEvaluatorRV F) (fixedQueryEnvironment xs) q)
          (vectorOfFunction xs, yv)
          = PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
              (functionEvaluatorRV F) (fixedQueryEnvironment xs) q
              (vectorOfFunction xs, yv) := by
              rw [PFunPDE.transcriptLawDist_apply]
      _ = PFunPDE.transcriptSystemFactor pΩ (functionEvaluatorRV F)
            (vectorOfFunction xs) yv := by
              rw [transcriptLaw_fixedQueryEnvironment_of_eq]
      _ = RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i))
            pΩ.val (functionOfVector yv) := by
              unfold PFunPDE.transcriptSystemFactor
              rw [RandomSystems.Dist.fTransform_apply_eq_mass]
              apply RandomSystems.Dist.mass_congr
              intro ω
              rw [transcriptSystemEvent_functionEvaluatorRV_iff]
              constructor
              · intro h
                funext i
                simpa [vectorOfFunction] using h i
              · intro h i
                simpa [vectorOfFunction] using congr_fun h i
      _ = fixedInputLiftDist xs
            (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i))
              pΩ.val)
            (vectorOfFunction xs, yv) := by
              have h := fixedInputLiftDist_apply_fixed (X := X) (Y := Y) (q := q) xs
                (functionOfVector yv)
                (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i))
                  pΩ.val)
              simpa [fixedInputTranscriptPrefix] using h.symm
  · calc
      PFunPDE.transcriptLawDist
          (PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
            (functionEvaluatorRV F) (fixedQueryEnvironment xs) q)
          (xv, yv)
          = PFunPDE.transcriptLaw pΩ RandomSystems.Dist.unitProbDist.{0}
              (functionEvaluatorRV F) (fixedQueryEnvironment xs) q (xv, yv) := by
              rw [PFunPDE.transcriptLawDist_apply]
      _ = 0 := by
              exact transcriptLaw_fixedQueryEnvironment_of_ne pΩ (functionEvaluatorRV F) xs xv yv hxv
      _ = fixedInputLiftDist xs
            (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i))
              pΩ.val)
            (xv, yv) := by
              have h := fixedInputLiftDist_apply_of_input_ne (X := X) (Y := Y) (q := q) xs
                (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i))
                  pΩ.val)
                xv yv hxv
              simpa using h.symm

/-- **UPSTREAM-CANDIDATE.** A law-level fixed-query transcript distribution
induced by a sampled function evaluator reduces to the fixed-input lift of the
sampled output-vector law.  This is the owner-level bridge used by H-technique
application proofs. -/
theorem PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
    {Ω X Y : Type*} {q : Nat} [Fintype (CR18TranscriptPrefix X Y q)]
    (p : RandomSystems.Dist.ProbDist Ω) (F : Ω → X → Y) (xs : Fin q → X) :
    PFunPDS.Prob.fixedQueryTranscriptDist
        (PFunPDS.Prob.functionEvaluator p F) xs =
      fixedInputLiftDist xs
        (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i)) p.val) := by
  change PFunPDS.Prob.fixedQueryTranscriptDist
        (RandomSystems.Dist.PMF p (functionEvaluatorRV F)) xs =
      fixedInputLiftDist xs
        (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i)) p.val)
  ext t
  unfold PFunPDS.Prob.fixedQueryTranscriptDist
    PFunPDS.Prob.deterministicTranscriptDist
  rw [PFunPDE.deterministicTranscriptLawDist_apply]
  rw [PFunPDE.deterministicTranscriptLaw_pmf]
  have hdist :=
    transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist
      (pΩ := p) (F := F) (xs := xs)
  have hpoint := congrArg
    (fun D : RandomSystems.Dist (CR18TranscriptPrefix X Y q) => D t)
    hdist
  simpa [PFunPDE.transcriptLawDist_apply] using hpoint

/-- **UPSTREAM-CANDIDATE.** The canonical law-level URF fixed-query transcript
distribution is the fixed-input lift of the sampled output-vector law. -/
theorem PFunPDS.Prob.fixedQueryTranscriptDist_urf
    {X Y : Type*} {q : Nat} [Fintype (X → Y)] [Nonempty (X → Y)]
    [Fintype (CR18TranscriptPrefix X Y q)] (xs : Fin q → X) :
    PFunPDS.Prob.fixedQueryTranscriptDist
        (PFunPDS.Prob.urf (X := X) (Y := Y)) xs =
      fixedInputLiftDist xs
        (RandomSystems.Dist.fTransform
          (fun f : X → Y => fun i : Fin q => f (xs i))
          (PFunPDS.uniformP (X := X) (Y := Y)).val) := by
  change PFunPDS.Prob.fixedQueryTranscriptDist
        (PFunPDS.Prob.functionEvaluator
          (PFunPDS.uniformP (X := X) (Y := Y))
          (fun f : X → Y => f)) xs =
      fixedInputLiftDist xs
        (RandomSystems.Dist.fTransform
          (fun f : X → Y => fun i : Fin q => f (xs i))
          (PFunPDS.uniformP (X := X) (Y := Y)).val)
  exact PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
    (PFunPDS.uniformP (X := X) (Y := Y))
    (fun f : X → Y => f)
    xs

/-- **Support lemma forced by formalization; candidate for upstream.** A
function-evaluator random system is total for every finite query budget. -/
theorem functionEvaluatorRV_KStepTotal {Ω X Y : Type*}
    (F : Ω → X → Y) (k : ℕ) :
    PFunPDS.RV.KStepTotal (functionEvaluatorRV F) k := by
  intro ω xs hne _hlen
  refine ⟨F ω (xs.getLast hne), ?_⟩
  change (PFunDDS.functionEvaluator (F ω)).1 xs = Part.some (F ω (xs.getLast hne))
  have hdom : xs ∈ PFunDDS.dom (PFunDDS.functionEvaluator (F ω)) := by
    rw [PFunDDS.dom_functionEvaluator]
    exact hne
  rw [← Part.some_get hdom]
  congr 1

/-- **Support lemma forced by formalization; candidate for upstream.** A
law-level PDS induced by sampled function evaluators is total for every finite
query budget. -/
theorem functionEvaluatorProb_KStepTotal {Ω X Y : Type*}
    (p : Dist.ProbDist Ω) (F : Ω → X → Y) (k : ℕ) :
    PFunPDS.Prob.KStepTotal (PFunPDS.Prob.functionEvaluator p F) k := by
  change PFunPDS.Prob.KStepTotal (Dist.PMF p (functionEvaluatorRV F)) k
  exact PFunPDS.Prob.KStepTotal_pmf_of_rv p
    (functionEvaluatorRV F)
    (functionEvaluatorRV_KStepTotal F k)

/-- **Support lemma forced by formalization; candidate for upstream.** A
law-level PDS induced by sampled function evaluators is total on every nonempty
history in its support. -/
theorem functionEvaluatorProb_totalOnNonempty {Ω X Y : Type*}
    (p : Dist.ProbDist Ω) (F : Ω → X → Y) :
    CondEquiv.TotalOnNonempty (PFunPDS.Prob.functionEvaluator p F).val := by
  intro s hs xs hxs
  unfold PFunPDS.Prob.functionEvaluator Dist.PMF at hs
  obtain ⟨ω, _hω, rfl⟩ := Dist.mem_support_fTransform (functionEvaluatorRV F) p.val hs
  change xs ∈ PFunDDS.dom (PFunDDS.functionEvaluator (F ω))
  rw [PFunDDS.dom_functionEvaluator]
  exact hxs

/-- **Support lemma forced by formalization; candidate for upstream.** The
law-level URF is q-step-total for every finite query budget. -/
theorem PFunPDS.Prob.urf_KStepTotal {X Y : Type*}
    [Fintype (X → Y)] [Nonempty (X → Y)] (k : ℕ) :
    PFunPDS.Prob.KStepTotal (PFunPDS.Prob.urf (X := X) (Y := Y)) k := by
  change PFunPDS.Prob.KStepTotal
    (PFunPDS.Prob.functionEvaluator (PFunPDS.uniformP (X := X) (Y := Y))
      (fun f : X → Y => f)) k
  exact functionEvaluatorProb_KStepTotal
    (PFunPDS.uniformP (X := X) (Y := Y))
    (fun f : X → Y => f)
    k

end CR18
end RandomSystems
