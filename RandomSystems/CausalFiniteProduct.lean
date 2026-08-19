import RandomSystems.StatDist

/-!
# Causal finite products

This module supplies the finite Markov-kernel calculation needed when the law
used at round `i` is allowed to depend on every earlier sample.  It is the
sequential counterpart of an independent finite product.

The central theorem, `causalProduct_statDist_le_sum`, says that pointwise
bounds on the distance between the two next-sample laws add along the causal
product.  No independence assumption is made about the choice of a later law.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems

universe u v

variable {H : Type u} {A : Type v}

/-! ## One finite kernel extension -/

/-- Extend a finite base law by a history-dependent next-sample law. -/
def finiteKernelExtend [Fintype H] [Fintype A]
    (base : Dist H) (kernel : H → Dist A) : Dist (H × A) :=
  Dist.ofFiniteMassFunction fun sample =>
    base sample.1 * kernel sample.1 sample.2

@[simp]
theorem finiteKernelExtend_apply [Fintype H] [Fintype A]
    (base : Dist H) (kernel : H → Dist A) (sample : H × A) :
    finiteKernelExtend base kernel sample =
      base sample.1 * kernel sample.1 sample.2 := by
  simp [finiteKernelExtend]

/-- Kernel extension preserves nonnegativity. -/
theorem finiteKernelExtend_nonNeg [Fintype H] [Fintype A]
    {base : Dist H} {kernel : H → Dist A}
    (baseNonnegative : base.NonNeg)
    (kernelNonnegative : ∀ history, (kernel history).NonNeg) :
    (finiteKernelExtend base kernel).NonNeg := by
  intro sample
  exact mul_nonneg (baseNonnegative sample.1)
    (kernelNonnegative sample.1 sample.2)

/-- The total weight of a kernel extension is the base-weighted sum of the
kernel weights. -/
theorem finiteKernelExtend_weight [Fintype H] [Fintype A]
    (base : Dist H) (kernel : H → Dist A) :
    (finiteKernelExtend base kernel).weight =
      ∑ history : H, base history * (kernel history).weight := by
  rw [finiteKernelExtend, Dist.weight_ofFiniteMassFunction,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro history _member
  rw [Dist.weight_eq_sum, Finset.mul_sum]

/-- Extending a probability law by probability kernels gives a probability
law. -/
theorem finiteKernelExtend_isProbDist [Fintype H] [Fintype A]
    {base : Dist H} {kernel : H → Dist A}
    (baseProbability : base.isProbDist)
    (kernelProbability : ∀ history, (kernel history).isProbDist) :
    (finiteKernelExtend base kernel).isProbDist := by
  constructor
  · exact finiteKernelExtend_nonNeg baseProbability.nonNeg fun history =>
      (kernelProbability history).nonNeg
  · rw [finiteKernelExtend_weight]
    simp_rw [(kernelProbability _).weight_eq, mul_one]
    rw [← Dist.weight_eq_sum]
    exact baseProbability.weight_eq

/-- Applying the same probability kernel to both base laws preserves their
one-sided statistical distance exactly. -/
theorem finiteKernelExtend_sameKernel [Fintype H] [Fintype A]
    (left right : Dist H) (kernel : H → Dist A)
    (kernelProbability : ∀ history, (kernel history).isProbDist) :
    statDist (finiteKernelExtend left kernel)
        (finiteKernelExtend right kernel) =
      statDist left right := by
  rw [statDist_eq_sum_univ, Fintype.sum_prod_type, statDist_eq_sum_univ]
  apply Finset.sum_congr rfl
  intro history _member
  calc
    (∑ next : A,
        max (finiteKernelExtend left kernel (history, next) -
          finiteKernelExtend right kernel (history, next)) 0) =
        ∑ next : A, kernel history next *
          max (left history - right history) 0 := by
      apply Finset.sum_congr rfl
      intro next _member
      rw [finiteKernelExtend_apply, finiteKernelExtend_apply,
        mul_comm (left history) (kernel history next),
        mul_comm (right history) (kernel history next),
        ← mul_sub,
        mul_max_of_nonneg _ _
          ((kernelProbability history).nonNeg next),
        mul_zero]
    _ = (kernel history).weight *
        max (left history - right history) 0 := by
      rw [Dist.weight_eq_sum, Finset.sum_mul]
    _ = max (left history - right history) 0 := by
      rw [(kernelProbability history).weight_eq, one_mul]

/-- With a shared nonnegative base law, the distance between two kernel
extensions is the base-weighted average of their local distances. -/
theorem finiteKernelExtend_sameBase [Fintype H] [Fintype A]
    (base : Dist H) (left right : H → Dist A)
    (baseNonnegative : base.NonNeg) :
    statDist (finiteKernelExtend base left)
        (finiteKernelExtend base right) =
      ∑ history : H,
        base history * statDist (left history) (right history) := by
  rw [statDist_eq_sum_univ, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro history _member
  rw [statDist_eq_sum_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro next _member
  rw [finiteKernelExtend_apply, finiteKernelExtend_apply, ← mul_sub,
    mul_max_of_nonneg _ _ (baseNonnegative history), mul_zero]

/-- One causal extension costs the old-history distance plus the average
distance of its two next-sample kernels. -/
theorem finiteKernelExtend_statDist_le [Fintype H] [Fintype A]
    (leftBase rightBase : Dist H)
    (leftKernel rightKernel : H → Dist A)
    (rightProbability : rightBase.isProbDist)
    (leftKernelProbability : ∀ history,
      (leftKernel history).isProbDist) :
    statDist
        (finiteKernelExtend leftBase leftKernel)
        (finiteKernelExtend rightBase rightKernel) ≤
      statDist leftBase rightBase +
        ∑ history : H, rightBase history *
          statDist (leftKernel history) (rightKernel history) := by
  calc
    statDist
        (finiteKernelExtend leftBase leftKernel)
        (finiteKernelExtend rightBase rightKernel) ≤
      statDist
          (finiteKernelExtend leftBase leftKernel)
          (finiteKernelExtend rightBase leftKernel) +
        statDist
          (finiteKernelExtend rightBase leftKernel)
          (finiteKernelExtend rightBase rightKernel) :=
      statDist_triangle _ _ _
    _ = statDist leftBase rightBase +
        ∑ history : H, rightBase history *
          statDist (leftKernel history) (rightKernel history) := by
      rw [finiteKernelExtend_sameKernel leftBase rightBase leftKernel
          leftKernelProbability,
        finiteKernelExtend_sameBase rightBase leftKernel rightKernel
          rightProbability.nonNeg]

/-! ## Iterated causal products -/

/-- The canonical equivalence between a history plus its next sample and the
extended history. -/
def finSnocEquiv (A : Type v) (n : ℕ) :
    ((Fin n → A) × A) ≃ (Fin (n + 1) → A) :=
  (Equiv.prodComm (Fin n → A) A).trans
    (Fin.snocEquiv (fun _ : Fin (n + 1) => A))

/-- A family of next-sample laws indexed by the complete strict past. -/
structure CausalLaws (A : Type v) where
  law : {i : ℕ} → (Fin i → A) → Dist A

/-- Sequential product of history-dependent finite laws. -/
def causalProduct [Fintype A] (laws : CausalLaws A) :
    (n : ℕ) → Dist (Fin n → A)
  | 0 => Dist.ofFiniteMassFunction fun _values => 1
  | n + 1 =>
      Dist.fTransform (finSnocEquiv A n)
        (finiteKernelExtend (causalProduct laws n)
          (fun history => laws.law history))

@[simp]
theorem causalProduct_zero_apply [Fintype A]
    (laws : CausalLaws A) (values : Fin 0 → A) :
    causalProduct laws 0 values = 1 := by
  simp [causalProduct]

@[simp]
theorem causalProduct_succ [Fintype A]
    (laws : CausalLaws A) (n : ℕ) :
    causalProduct laws (n + 1) =
      Dist.fTransform (finSnocEquiv A n)
        (finiteKernelExtend (causalProduct laws n)
          (fun history => laws.law history)) := by
  rfl

/-- A causal product of probability kernels is a probability distribution. -/
theorem causalProduct_isProbDist [Fintype A]
    (laws : CausalLaws A)
    (probability : ∀ {i} (history : Fin i → A),
      (laws.law history).isProbDist) :
    ∀ n, (causalProduct laws n).isProbDist := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro values
        simp [causalProduct]
      · rw [causalProduct, Dist.weight_ofFiniteMassFunction]
        simp
  | succ n inductionHypothesis =>
      exact Dist.fTransform_isProbDist (finSnocEquiv A n)
        (finiteKernelExtend_isProbDist inductionHypothesis fun history =>
          probability history)

/-- Sequential statistical-distance bound.  The round-`i` kernel may depend
on every one of the first `i` samples; only its pointwise distance bound must
be independent of the realized history. -/
theorem causalProduct_statDist_le_sum [Fintype A] [DecidableEq A]
    (left right : CausalLaws A)
    (leftProbability : ∀ {i} (history : Fin i → A),
      (left.law history).isProbDist)
    (rightProbability : ∀ {i} (history : Fin i → A),
      (right.law history).isProbDist)
    (epsilon : ℕ → ℝ)
    (localBound : ∀ {i} (history : Fin i → A),
      statDist (left.law history) (right.law history) ≤ epsilon i) :
    ∀ n,
      statDist (causalProduct left n) (causalProduct right n) ≤
        ∑ i ∈ Finset.range n, epsilon i := by
  intro n
  induction n with
  | zero => simp [causalProduct, statDist_eq_sum_univ]
  | succ n inductionHypothesis =>
      rw [causalProduct_succ, causalProduct_succ,
        statDist_fTransform_injective _ _ (finSnocEquiv A n)
          (finSnocEquiv A n).injective]
      calc
        statDist
            (finiteKernelExtend (causalProduct left n)
              (fun history => left.law history))
            (finiteKernelExtend (causalProduct right n)
              (fun history => right.law history)) ≤
          statDist (causalProduct left n) (causalProduct right n) +
            ∑ history : Fin n → A,
              causalProduct right n history *
                statDist (left.law history) (right.law history) :=
          finiteKernelExtend_statDist_le _ _ _ _
            (causalProduct_isProbDist right rightProbability n)
            (fun history => leftProbability history)
        _ ≤ (∑ i ∈ Finset.range n, epsilon i) +
            ∑ history : Fin n → A,
              causalProduct right n history * epsilon n := by
          apply add_le_add inductionHypothesis
          apply Finset.sum_le_sum
          intro history _member
          exact mul_le_mul_of_nonneg_left (localBound history)
            ((causalProduct_isProbDist right rightProbability n).nonNeg
              history)
        _ = (∑ i ∈ Finset.range n, epsilon i) + epsilon n := by
          rw [← Finset.sum_mul, ← Dist.weight_eq_sum,
            (causalProduct_isProbDist right rightProbability n).weight_eq,
            one_mul]
        _ = ∑ i ∈ Finset.range (n + 1), epsilon i := by
          rw [Finset.sum_range_succ]

end RandomSystems
