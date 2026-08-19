/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.ConditionBased
import RandomSystems.Legacy.Instances.URF
import RandomSystems.Legacy.Instances.URP

/-!
# PRF/PRP Switching Lemma

The PRF/PRP switching lemma bounds the distinguishing advantage between
a Uniform Random Function (URF) and a Uniform Random Permutation (URP).

## Main Results

* `prf_prp_switching_q1` — Adv(URF, URP) = 0 for q = 1

## Proof Strategy (Maurer 2002)

Define the condition A = "all outputs in the transcript are distinct."
- Conditioned on A, the URF and URP produce identical transcript
  distributions (both are uniform over distinct-output sequences).
- The probability that A fails under URF is the birthday bound:
  Pr[collision in q draws from |X|] ≤ q(q-1)/(2|X|).

## References

* Maurer, U. (2002). "Indistinguishability of Random Systems." EUROCRYPT 2002.
  Section 4.1.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

variable {X : Type*}
  [Fintype X] [DecidableEq X]

/-- The "all outputs distinct" condition for transcripts.

For q queries, this checks that no two outputs in the transcript are equal.
This is the monotone condition used in the PRF/PRP switching proof. -/
def allOutputsDistinct (X : Type*) [DecidableEq X] (q : ℕ) :
    TranscriptCondition X X q where
  holds := fun t => Function.Injective (fun i => (t i).2)
  dec := inferInstance

/-- The birthday bound: probability that q uniform draws from a set of
size N produce a collision.

  Pr[collision] ≤ q * (q - 1) / (2 * N) -/
def birthdayBound (q : ℕ) (N : ℕ) : NNReal :=
  (q * (q - 1) : ℕ) / (2 * N : ℕ)

/-- For q=1, any function `Fin 1 → α` is injective. -/
private lemma fin1_injective {α : Type*} (f : Fin 1 → α) : Function.Injective f := by
  intro i j _
  exact Subsingleton.elim i j

omit [Fintype X] in
/-- For q=1, the allOutputsDistinct condition always holds. -/
private lemma allOutputsDistinct_trivial_q1
    (t : Transcript X X 1) : (allOutputsDistinct X 1).holds t :=
  fin1_injective _

omit [Fintype X] [DecidableEq X] in
/-- The transcript function for q=1 only depends on the output at inputs 0. -/
private lemma transcript_q1_eq (s : DDS X X 1) (inputs : Fin 1 → X) :
    DDS.transcript s inputs = fun _ => (inputs 0, s.firstQuery Nat.zero_lt_one (inputs 0)) := by
  funext ⟨i, hi⟩
  have : i = 0 := by omega
  subst this
  simp only [DDS.transcript, DDS.firstQuery]
  apply Prod.ext
  · rfl
  · apply DDS.respond_congr_val s 0 0 hi Nat.zero_lt_one rfl _ _ (fun k hki hkj => by
      obtain rfl : k = 0 := by omega
      rfl)

/-- Evaluation at a point pushes uniform-on-functions to uniform-on-outputs.

For any x₀ ∈ X: `(fTransform (eval at x₀) (uniform (DDS X X 1))) y = 1/|X|`

Proof idea: `|{f : X→X | f(x₀) = y}| / |X→X| = |X|^(|X|-1) / |X|^|X| = 1/|X|`. -/
private lemma urf_eval_eq [Nonempty (DDS X X 1)] (x₀ y : X) :
    (Dist.fTransform (fun s : DDS X X 1 => s.firstQuery Nat.zero_lt_one x₀)
      (Dist.uniform (DDS X X 1))) y =
    (1 : NNReal) / (Fintype.card X : NNReal) := by
  -- Unfold to a sum: ∑ s with firstQuery s x₀ = y, 1/|DDS|
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, Dist.uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
    (fun _ : DDS X X 1 => (1 : NNReal) / (Fintype.card (DDS X X 1) : NNReal))).support
    = Finset.univ := by
    ext s; simp_all [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul,
    mul_one_div]
  -- Goal: ↑|{s | firstQuery s x₀ = y}| / ↑|DDS X X 1| = 1 / ↑|X|
  -- Step 1: Count the fiber via dds1Equiv
  have h_fiber_card : (Finset.univ.filter
      (fun s : DDS X X 1 => s.firstQuery Nat.zero_lt_one x₀ = y)).card =
      Fintype.card X ^ (Fintype.card X - 1) := by
    rw [show (Finset.univ.filter
        (fun s : DDS X X 1 => s.firstQuery Nat.zero_lt_one x₀ = y)).card =
        (Finset.univ.filter (fun f : X → X => f x₀ = y)).card from by
      apply Finset.card_bij (fun s _ => dds1Equiv X X s)
      · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢; exact hs
      · intro s₁ _ s₂ _ h; exact (dds1Equiv X X).injective h
      · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        refine ⟨(dds1Equiv X X).symm f, ?_, (dds1Equiv X X).apply_symm_apply f⟩
        simp only [dds1Equiv]; exact hf]
    have h := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset X) x₀
      (Finset.mem_univ y)
    rw [Fintype.piFinset_univ, Finset.card_univ] at h; exact h
  -- Step 2: Count total DDS
  have h_total_card : Fintype.card (DDS X X 1) = Fintype.card X ^ Fintype.card X := by
    exact Fintype.card_congr (dds1Equiv X X) ▸ Fintype.card_fun
  -- Step 3: Compute the ratio |X|^(|X|-1) / |X|^|X| = 1/|X|
  rw [h_fiber_card, h_total_card]
  push_cast
  haveI : Nonempty X := ⟨x₀⟩
  set n := (Fintype.card X : NNReal)
  have h_pos : 0 < Fintype.card X := Fintype.card_pos
  set k := Fintype.card X - 1
  have h_ne : n ≠ 0 := Nat.cast_ne_zero.mpr h_pos.ne'
  have h_pow_ne : n ^ k ≠ 0 := pow_ne_zero _ h_ne
  have h_card_eq : Fintype.card X = k + 1 := by omega
  rw [h_card_eq, pow_succ]
  -- Goal: n ^ k / (n ^ k * n) = 1 / n
  rw [show n ^ k / (n ^ k * n) = n ^ k * (n ^ k * n)⁻¹ from rfl]
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h_pow_ne, one_mul]
  exact (one_div n).symm

-- Helper: the first-query function of (dds1Equiv).symm f is f
omit [Fintype X] [DecidableEq X] in
private lemma firstQuery_dds1Equiv_symm (f : X → X) :
    ((dds1Equiv X X).symm f).firstQuery Nat.zero_lt_one = f :=
  DDS.ofFun_firstQuery f

/-- For any two elements y₁ y₂, the number of permutation-DDS mapping x₀ to y₁
equals the number mapping x₀ to y₂. This is because composing with swap(y₁,y₂)
gives a bijection between the two fibers. -/
private lemma perm_fiber_card_eq (x₀ y₁ y₂ : X) :
    ((Finset.univ : Finset (DDS X X 1)).filter
      (fun s => Instances.DDS.isPermutation s ∧ s.firstQuery Nat.zero_lt_one x₀ = y₁)).card =
    ((Finset.univ : Finset (DDS X X 1)).filter
      (fun s => Instances.DDS.isPermutation s ∧ s.firstQuery Nat.zero_lt_one x₀ = y₂)).card := by
  -- Bijection: s ↦ ofFun ((swap y₁ y₂) ∘ (dds1Equiv s))
  set φ := fun (s : DDS X X 1) => (dds1Equiv X X).symm ((Equiv.swap y₁ y₂) ∘ (dds1Equiv X X s))
  -- Key fact: firstQuery of φ s = swap ∘ firstQuery s
  have φ_firstQuery : ∀ s : DDS X X 1,
      (φ s).firstQuery Nat.zero_lt_one = (Equiv.swap y₁ y₂) ∘ (s.firstQuery Nat.zero_lt_one) := by
    intro s
    simp only [φ]
    rw [firstQuery_dds1Equiv_symm]
    rfl
  apply Finset.card_bij (fun s _ => φ s)
  · -- φ maps fiber-y₁ to fiber-y₂
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    constructor
    · -- φ s is a permutation
      unfold Instances.DDS.isPermutation
      rw [φ_firstQuery, Equiv.comp_bijective]
      exact hs.1
    · -- φ s sends x₀ to y₂
      have := congr_fun (φ_firstQuery s) x₀
      simp only [Function.comp] at this
      rw [this, hs.2, Equiv.swap_apply_left]
  · -- φ is injective on fiber-y₁
    intro s₁ _ s₂ _ h
    simp only [φ] at h
    exact (dds1Equiv X X).injective
      ((Equiv.swap y₁ y₂).injective.comp_left ((dds1Equiv X X).symm.injective h))
  · -- φ is surjective: for t in fiber-y₂, preimage is ofFun ((swap y₁ y₂) ∘ (dds1Equiv t))
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine ⟨(dds1Equiv X X).symm ((Equiv.swap y₁ y₂) ∘ (dds1Equiv X X t)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have φt_firstQuery : ((dds1Equiv X X).symm ((Equiv.swap y₁ y₂) ∘ (dds1Equiv X X t))).firstQuery
          Nat.zero_lt_one = (Equiv.swap y₁ y₂) ∘ (t.firstQuery Nat.zero_lt_one) := by
        rw [firstQuery_dds1Equiv_symm]; rfl
      constructor
      · unfold Instances.DDS.isPermutation
        rw [φt_firstQuery, Equiv.comp_bijective]
        exact ht.1
      · have := congr_fun φt_firstQuery x₀
        simp only [Function.comp] at this
        rw [this, ht.2, Equiv.swap_apply_right]
    · simp only [φ]
      -- Goal: (dds1Equiv).symm (swap ∘ dds1Equiv ((dds1Equiv).symm (swap ∘ dds1Equiv t))) = t
      conv_lhs => rw [Equiv.apply_symm_apply (dds1Equiv X X) ((Equiv.swap y₁ y₂) ∘ (dds1Equiv X X t))]
      -- Goal: (dds1Equiv).symm (swap ∘ swap ∘ dds1Equiv t) = t
      have : (Equiv.swap y₁ y₂) ∘ (Equiv.swap y₁ y₂) ∘ (dds1Equiv X X t) = dds1Equiv X X t := by
        ext x; simp [Function.comp, Equiv.swap_apply_self]
      rw [this, Equiv.symm_apply_apply]

/-- The permutation DDS partition into |X| equal-sized fibers based on where they send x₀. -/
private lemma perm_fiber_card_eq_div (x₀ y : X) :
    ((Finset.univ : Finset (DDS X X 1)).filter
      (fun s => Instances.DDS.isPermutation s ∧ s.firstQuery Nat.zero_lt_one x₀ = y)).card *
      (Fintype.card X) =
    ((Finset.univ : Finset (DDS X X 1)).filter Instances.DDS.isPermutation).card := by
  set perms := (Finset.univ : Finset (DDS X X 1)).filter Instances.DDS.isPermutation
  set fiber := fun (z : X) => perms.filter (fun s => s.firstQuery Nat.zero_lt_one x₀ = z)
  -- Step 1: |perms| = ∑ z, |fiber(z)| (fiberwise decomposition)
  have h_decomp : perms.card = ∑ z : X, (fiber z).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun s => s.firstQuery Nat.zero_lt_one x₀)
        (t := Finset.univ) (by intro _ _; exact Finset.mem_univ _)]
  -- Step 2: each |fiber(z)| = |fiber(y)| (by perm_fiber_card_eq)
  have h_const : ∀ z : X, (fiber z).card = (fiber y).card := by
    intro z
    simp only [fiber, perms]
    -- Need to show the filter on perms = filter on univ with conjunction
    have : ∀ w : X, (((Finset.univ : Finset (DDS X X 1)).filter Instances.DDS.isPermutation).filter
        (fun s => s.firstQuery Nat.zero_lt_one x₀ = w)).card =
        ((Finset.univ : Finset (DDS X X 1)).filter
        (fun s => Instances.DDS.isPermutation s ∧ s.firstQuery Nat.zero_lt_one x₀ = w)).card := by
      intro w; congr 1; ext s; simp [Finset.mem_filter]
    rw [this z, this y]
    exact perm_fiber_card_eq x₀ z y
  -- Step 3: ∑ z, |fiber(y)| = |fiber(y)| * |X|
  rw [h_decomp, Finset.sum_congr rfl (fun z _ => h_const z)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  -- Now need: fiber y as filter on perms = filter on univ with conjunction
  congr 1
  simp only [fiber, perms]
  congr 1; ext s; simp [Finset.mem_filter]

private lemma urp_eval_eq (x₀ y : X) :
    (Dist.fTransform (fun s : DDS X X 1 => s.firstQuery Nat.zero_lt_one x₀)
      (Instances.URP (X := X)).dist) y =
    (1 : NNReal) / (Fintype.card X : NNReal) := by
  set eval : DDS X X 1 → X := fun s => s.firstQuery Nat.zero_lt_one x₀
  set perms := (Finset.univ : Finset (DDS X X 1)).filter Instances.DDS.isPermutation
  -- URP.dist = perms.sum (fun s => single s (1/|perms|))
  -- fTransform distributes over Finsupp.sum
  show (Finsupp.mapDomain eval (Instances.URP (X := X)).dist) y = _
  simp only [Instances.URP]
  rw [show (∑ s ∈ perms, Finsupp.single s ((1 : NNReal) / (perms.card : NNReal))) =
    (perms.sum fun s => Finsupp.single s ((1 : NNReal) / (perms.card : NNReal))) from rfl]
  rw [Finsupp.mapDomain_finset_sum]
  simp only [Finsupp.mapDomain_single]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [Finsupp.single_apply]
  -- Goal: ∑ s in perms, if eval s = y then 1/|perms| else 0 = 1/|X|
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  -- Goal: ↑|{s ∈ perms | eval s = y}| / ↑|perms| = 1 / ↑|X|
  -- Use perm_fiber_card_eq_div: |fiber| * |X| = |perms|
  have h_fiber := perm_fiber_card_eq_div x₀ y
  -- Need to show the filter set matches
  have h_filter_eq : (perms.filter (fun s => eval s = y)).card =
      ((Finset.univ : Finset (DDS X X 1)).filter
        (fun s => Instances.DDS.isPermutation s ∧ s.firstQuery Nat.zero_lt_one x₀ = y)).card := by
    congr 1; ext s; simp [Finset.mem_filter, perms, eval]
  rw [h_filter_eq]
  -- Goal: ↑|fiber| / ↑|perms| = 1 / ↑|X|
  -- From h_fiber: |fiber| * |X| = |perms|
  rw [div_eq_div_iff]
  · simp only [one_mul]; exact_mod_cast h_fiber
  · -- |perms| ≠ 0 (there's at least one permutation: the identity)
    exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr
      ⟨DDS.ofFun id, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.bijective_id⟩⟩).ne'
  · -- |X| ≠ 0
    haveI : Nonempty X := ⟨x₀⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_pos.ne'

/-- For q=1, the URF and URP have the same transcript distributions for all inputs.

Both produce a uniform distribution over outputs for any fixed input. -/
private lemma urf_urp_transcriptDist_eq [Nonempty (DDS X X 1)]
    (inputs : Fin 1 → X) :
    (Instances.URF (X := X) (Y := X) (q := 1)).transcriptDist inputs =
    (Instances.URP (X := X)).transcriptDist inputs := by
  -- Strategy: factor the transcript map as embed ∘ eval, where
  --   eval s = firstQuery s x₀ (output at x₀)
  --   embed y = fun _ => (x₀, y) (embed into transcript type)
  -- Then transcriptDist = fTransform embed (fTransform eval dist).
  -- Show fTransform eval gives uniform on X for both URF and URP.
  set x₀ := inputs 0
  set eval : DDS X X 1 → X := fun s => s.firstQuery Nat.zero_lt_one x₀
  set embed : X → Transcript X X 1 := fun y _ => (x₀, y)
  -- Factor: transcript · inputs = embed ∘ eval
  have h_factor : (fun s : DDS X X 1 => DDS.transcript s inputs) = embed ∘ eval := by
    funext s
    rw [transcript_q1_eq s inputs]
    rfl
  -- transcriptDist is fTransform (transcript · inputs) dist
  -- = fTransform (embed ∘ eval) dist
  -- = fTransform embed (fTransform eval dist)  (by mapDomain_comp)
  simp only [PDS.transcriptDist, h_factor]
  -- fTransform (embed ∘ eval) = fTransform embed ∘ fTransform eval
  -- So it suffices to show fTransform eval gives same result for both dists
  show Dist.fTransform (embed ∘ eval) (Instances.URF (X := X) (Y := X) (q := 1)).dist =
       Dist.fTransform (embed ∘ eval) (Instances.URP (X := X)).dist
  -- Factor: fTransform (embed ∘ eval) = fTransform embed ∘ fTransform eval
  -- Since embed is injective, it suffices to show fTransform eval gives same result
  suffices h : Dist.fTransform eval (Instances.URF (X := X) (Y := X) (q := 1)).dist =
      Dist.fTransform eval (Instances.URP (X := X)).dist by
    show Finsupp.mapDomain (embed ∘ eval) (Instances.URF (X := X) (Y := X) (q := 1)).dist =
         Finsupp.mapDomain (embed ∘ eval) (Instances.URP (X := X)).dist
    rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp]
    exact congrArg (Finsupp.mapDomain embed) h
  -- Now show: fTransform eval URF.dist = fTransform eval URP.dist
  -- Both assign 1/|X| to each y ∈ X.
  ext y
  -- LHS: (fTransform eval (uniform DDS)) y = |{s | eval s = y}| / |DDS|
  -- RHS: (fTransform eval URP.dist) y = |{π | eval π = y}| / |perms|
  -- Both = 1/|X|
  -- Show LHS = 1/|X|
  have h_lhs : (Dist.fTransform eval (Instances.URF (X := X) (Y := X) (q := 1)).dist) y =
      (1 : NNReal) / (Fintype.card X : NNReal) :=
    urf_eval_eq x₀ y
  have h_rhs : (Dist.fTransform eval (Instances.URP (X := X)).dist) y =
      (1 : NNReal) / (Fintype.card X : NNReal) :=
    urp_eval_eq x₀ y
  simp [h_lhs, h_rhs]

/-- Conditioned on all outputs being distinct, URF and URP produce
the same transcript distributions for single-query systems.

For q = 1, this is trivially true (one output is always "distinct").
For general q, both systems produce uniform distributions over
sequences of q distinct elements from X. -/
theorem urf_urp_cond_equiv [Nonempty (DDS X X 1)] :
    PDS.condEquiv
      (Instances.URF (X := X) (Y := X) (q := 1))
      (Instances.URP (X := X))
      (allOutputsDistinct X 1) := by
  intro inputs t _
  have h := urf_urp_transcriptDist_eq inputs
  exact congr_fun (congr_arg DFunLike.coe h) t

/-- The failure probability of the all-outputs-distinct condition under URF
is bounded by the birthday bound.

  ν(URF, allOutputsDistinct) ≤ q(q-1)/(2|X|)

For q = 1, this is 0 (a single output trivially has no collision). -/
theorem urf_collision_bound [Nonempty (DDS X X 1)] :
    maxConditionFailure
      (Instances.URF (X := X) (Y := X) (q := 1))
      (allOutputsDistinct X 1)
    ≤ birthdayBound 1 (Fintype.card X) := by
  -- birthdayBound 1 |X| = (1 * 0) / (2 * |X|) = 0
  have h_bound_zero : birthdayBound 1 (Fintype.card X) = 0 := by
    simp [birthdayBound]
  rw [h_bound_zero]
  -- maxConditionFailure = sup of conditionFailureProb, which is 0 for all inputs
  simp only [maxConditionFailure]
  apply Finset.sup_le
  intro inputs _
  -- conditionFailureProb = 0 because ¬A never holds for q=1
  simp only [conditionFailureProb]
  -- For q=1, allOutputsDistinct always holds (one element is trivially injective)
  have h_no_fail : ∀ s : DDS X X 1, (allOutputsDistinct X 1).holds (DDS.transcript s inputs) := by
    intro s
    simp only [allOutputsDistinct]
    intro i j _
    exact Subsingleton.elim i j
  -- So the filter is empty
  have h_empty : (Finset.univ : Finset (DDS X X 1)).filter
      (fun s => ¬(allOutputsDistinct X 1).holds (DDS.transcript s inputs)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro s _
    exact not_not.mpr (h_no_fail s)
  rw [h_empty]
  simp

/-- **PRF/PRP Switching Lemma** (single-query case).

  Adv(URF, URP) = 0 for q = 1.

For a single query, URF and URP are both uniform over X, so they
are perfectly indistinguishable. The interesting case is q > 1,
which requires multi-query DDS (not yet formalized for URP). -/
theorem prf_prp_switching_q1 [Nonempty (DDS X X 1)] :
    advantage
      (Instances.URF (X := X) (Y := X) (q := 1))
      (Instances.URP (X := X))
    = 0 := by
  simp only [advantage]
  apply le_antisymm
  · apply Finset.sup_le
    intro inputs _
    rw [urf_urp_transcriptDist_eq inputs]
    exact le_of_eq (statDist_self _)
  · exact zero_le _

/-! ## General PRF/PRP Switching (Birthday Bound)

The general switching lemma: for q queries, the probability that a URF
produces a collision in the outputs is at most q(q-1)/(2|X|).

This is proved via the union bound:
- For each pair (i,j) with i < j, Pr[output_i = output_j] = 1/|X|
- There are C(q,2) = q(q-1)/2 such pairs
- By union bound: Pr[∃ collision] ≤ q(q-1)/(2|X|)
-/

variable {q : ℕ} [Fintype (DDS X X q)] [Fintype (Transcript X X q)]
  [DecidableEq (Transcript X X q)]

omit [Fintype (Transcript X X q)] [DecidableEq (Transcript X X q)] in
/-- For a pair (i,j) with i ≠ j, the fraction of DDS whose transcript outputs
collide at positions i and j is exactly 1/|X|.

This holds because outputs at positions i and j access independent cells of the
DDS respond function (since i ≠ j). Under uniform distribution, the pairwise
collision probability for independent uniform random variables over X is 1/|X|. -/
private lemma urf_pairwise_collision_frac
    (inputs : Fin q → X) (i j : Fin q) (hij : i ≠ j)
    [Nonempty (DDS X X q)] :
    ((Finset.univ : Finset (DDS X X q)).filter
      (fun s => (DDS.transcript s inputs i).2 = (DDS.transcript s inputs j).2)).card *
      (Fintype.card X) ≤
    Fintype.card (DDS X X q) := by
  -- Step 1: Define the input restriction for cell i
  set inp_i : Fin (i.val + 1) → X := fun k => inputs ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt i.isLt)⟩
  -- Step 2: Define the modify function (replace cell i's output at inp_i with x)
  let modify : DDS X X q → X → DDS X X q := fun s x => ⟨Function.update s.respond i (Function.update (s.respond i) inp_i x)⟩
  -- Step 3: Name the collision set
  set C := (Finset.univ : Finset (DDS X X q)).filter
    (fun s => (DDS.transcript s inputs i).2 = (DDS.transcript s inputs j).2)
  -- Step 4: The injection from C ×ˢ Finset.univ to Finset.univ
  let φ : DDS X X q × X → DDS X X q := fun p => modify p.1 p.2
  have h_maps : ∀ p ∈ C ×ˢ (Finset.univ : Finset X), φ p ∈ (Finset.univ : Finset (DDS X X q)) := by
    intro p _; exact Finset.mem_univ _
  have h_inj : Set.InjOn φ ↑(C ×ˢ (Finset.univ : Finset X)) := by
    intro ⟨s₁, x₁⟩ hp₁ ⟨s₂, x₂⟩ hp₂ heq
    -- Extract collision condition from membership in C
    rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
    have hs₁ := (Finset.mem_filter.mp hp₁.1).2
    have hs₂ := (Finset.mem_filter.mp hp₂.1).2
    -- Extract respond-level equality from φ equality
    have heq_respond : Function.update s₁.respond i (Function.update (s₁.respond i) inp_i x₁) =
        Function.update s₂.respond i (Function.update (s₂.respond i) inp_i x₂) := by
      have := congr_arg DDS.respond heq; exact this
    -- At positions k ≠ i, the respond functions agree
    have h_other : ∀ k : Fin q, k ≠ i → s₁.respond k = s₂.respond k := by
      intro k hk
      have := congr_fun heq_respond k
      rwa [Function.update_of_ne hk, Function.update_of_ne hk] at this
    -- At position i, the updated inner functions agree
    have heq_i : Function.update (s₁.respond i) inp_i x₁ =
        Function.update (s₂.respond i) inp_i x₂ := by
      have := congr_fun heq_respond i
      rwa [Function.update_self, Function.update_self] at this
    -- From heq_i at inp_i: x₁ = x₂
    have hx : x₁ = x₂ := by
      have := congr_fun heq_i inp_i
      rwa [Function.update_self, Function.update_self] at this
    -- From heq_i at p ≠ inp_i: s₁.respond i p = s₂.respond i p
    have h_other_i : ∀ p : Fin (i.val + 1) → X, p ≠ inp_i → s₁.respond i p = s₂.respond i p := by
      intro p hp
      have := congr_fun heq_i p
      rwa [Function.update_of_ne hp, Function.update_of_ne hp] at this
    -- Use collision condition to get s₁.respond i inp_i = s₂.respond i inp_i
    -- hs₁ says: (s₁.transcript inputs i).2 = (s₁.transcript inputs j).2
    -- Which unfolds to: s₁.respond i inp_i = s₁.respond j inp_j
    -- (where inp_i/inp_j are the input restrictions)
    -- Since j ≠ i, h_other gives s₁.respond j = s₂.respond j, so:
    -- s₁.respond i inp_i = s₁.respond j inp_j = s₂.respond j inp_j = s₂.respond i inp_i
    have hij' : j ≠ i := Ne.symm hij
    have h_j_agree : s₁.respond j = s₂.respond j := h_other j hij'
    have h_eq_at_inp_i : s₁.respond i inp_i = s₂.respond i inp_i := by
      simp only [DDS.transcript] at hs₁ hs₂
      -- Define inp_j analogously to inp_i
      set inp_j : Fin (j.val + 1) → X := fun k => inputs ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt j.isLt)⟩
      -- Chain: s₁.respond i inp_i = s₁.respond j inp_j = s₂.respond j inp_j = s₂.respond i inp_i
      calc s₁.respond i inp_i
          = s₁.respond j inp_j := by convert hs₁ using 2
        _ = s₂.respond j inp_j := by rw [h_j_agree]
        _ = s₂.respond i inp_i := by convert hs₂.symm using 2
    -- Now combine: s₁ = s₂ by ext
    have hs : s₁ = s₂ := by
      apply DDS.ext
      funext k
      by_cases hk : k = i
      · subst hk
        funext p
        by_cases hp : p = inp_i
        · subst hp; exact h_eq_at_inp_i
        · exact h_other_i p hp
      · exact h_other k hk
    exact Prod.ext hs hx
  have h_card_le := Finset.card_le_card_of_injOn φ h_maps h_inj
  rw [Finset.card_product, Finset.card_univ] at h_card_le
  exact h_card_le

/-- The number of strict-lower-triangular pairs in `Fin q × Fin q` is `q*(q-1)/2`.

This is the combinatorial identity `|{(i,j) : Fin q | i < j}| = C(q,2) = q(q-1)/2`,
expressed as `|pairs| * 2 = q * (q-1)` to avoid division in ℕ. -/
theorem card_strictLTPairs :
    ((Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)).card * 2
    = q * (q - 1) := by
  set lt_pairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)
  set gt_pairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.2 < p.1)
  have h_sym : lt_pairs.card = gt_pairs.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [gt_pairs, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [lt_pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.ext (by exact (Prod.mk.inj h).2) (by exact (Prod.mk.inj h).1)
    · intro p hp
      simp only [lt_pairs, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [gt_pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), hp, rfl⟩
  have h_disj : Disjoint lt_pairs gt_pairs := by
    simp only [lt_pairs, gt_pairs]
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  have h_union : lt_pairs ∪ gt_pairs = (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, lt_pairs, gt_pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Fin.ne_of_lt h
      · exact Ne.symm (Fin.ne_of_lt h)
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
  have h_offdiag : ((Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2)).card = q * (q - 1) := by
    rcases q with _ | n
    · simp
    · rw [show (Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter (fun p => p.1 ≠ p.2) = Finset.univ.offDiag from by
        ext ⟨a, b⟩; simp [Finset.mem_offDiag]]
      rw [Finset.offDiag_card]
      simp only [Finset.card_univ, Fintype.card_fin, Nat.succ_sub_one]
      ring_nf; omega
  have h_sum : lt_pairs.card + gt_pairs.card = q * (q - 1) := by
    rw [← h_offdiag, ← h_union]
    exact (Finset.card_union_of_disjoint h_disj).symm
  omega

omit [Fintype (Transcript X X q)] [DecidableEq (Transcript X X q)] in
/-- The condition failure probability under URF for a fixed input sequence
is bounded by the birthday bound.

  conditionFailureProb URF (allOutputsDistinct X q) inputs ≤ q(q-1)/(2|X|)

Proof: By union bound over all pairs (i,j) with i < j. -/
private lemma urf_collision_prob_le_birthday
    (inputs : Fin q → X) [Nonempty (DDS X X q)] :
    conditionFailureProb
      (Instances.URF (X := X) (Y := X) (q := q))
      (allOutputsDistinct X q) inputs
    ≤ birthdayBound q (Fintype.card X) := by
  -- Step 1: Unfold conditionFailureProb for URF (uniform dist)
  -- Under URF, each DDS has mass 1/|DDS|, so the sum is |bad set| / |DDS|
  simp only [conditionFailureProb, Instances.URF, Dist.uniform]
  -- Step 2: Convert the sum to cardinality * (1/|DDS|)
  have h_sum_eq : ∑ s ∈ (Finset.univ : Finset (DDS X X q)).filter
      (fun s => ¬(allOutputsDistinct X q).holds (DDS.transcript s inputs)),
      (Finsupp.equivFunOnFinite.invFun
        fun _ : DDS X X q => (1 : NNReal) / ↑(Fintype.card (DDS X X q))) s =
      ((Finset.univ.filter
        (fun s => ¬(allOutputsDistinct X q).holds (DDS.transcript s inputs))).card : NNReal) /
      (Fintype.card (DDS X X q) : NNReal) := by
    simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [h_sum_eq]
  -- Step 3: Use union bound — the "bad set" (collision set) is contained in
  -- the union of pairwise collision sets
  -- |{s : ¬injective}| ≤ ∑_{i<j} |{s : output_i = output_j}|
  have h_union_bound : ((Finset.univ.filter
      (fun s : DDS X X q => ¬(allOutputsDistinct X q).holds (DDS.transcript s inputs))).card : NNReal) /
      (Fintype.card (DDS X X q) : NNReal) ≤
    ∑ p ∈ (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2),
      ((Finset.univ.filter
        (fun s : DDS X X q => (DDS.transcript s inputs p.1).2 = (DDS.transcript s inputs p.2).2)).card : NNReal) /
      (Fintype.card (DDS X X q) : NNReal) := by
    -- Suffices to show the Nat cardinality inequality (same denominator)
    -- |{s | ¬injective}| ≤ ∑_{i<j} |{s | out_i = out_j}|
    have h_nat_ub : ((Finset.univ : Finset (DDS X X q)).filter
        (fun s => ¬(allOutputsDistinct X q).holds (DDS.transcript s inputs))).card ≤
      ∑ p ∈ (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2),
        ((Finset.univ : Finset (DDS X X q)).filter
          (fun s => (DDS.transcript s inputs p.1).2 = (DDS.transcript s inputs p.2).2)).card := by
      -- Union bound: ¬injective means ∃ i < j, out_i = out_j
      -- So {¬injective} ⊆ ⋃_{i<j} {out_i = out_j}
      set pairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)
      set collision := fun (p : Fin q × Fin q) =>
        (Finset.univ : Finset (DDS X X q)).filter
          (fun s => (DDS.transcript s inputs p.1).2 = (DDS.transcript s inputs p.2).2)
      -- The bad set is a subset of the biUnion
      have h_subset : (Finset.univ : Finset (DDS X X q)).filter
          (fun s => ¬(allOutputsDistinct X q).holds (DDS.transcript s inputs)) ⊆
          pairs.biUnion collision := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, allOutputsDistinct] at hs
        -- hs : ¬Function.Injective (fun i => (s.transcript inputs i).2)
        rw [Function.Injective] at hs
        push_neg at hs
        obtain ⟨a, b, hab, hne⟩ := hs
        rw [Finset.mem_biUnion]
        by_cases h : a < b
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
        · have hba : b < a := lt_of_le_of_ne (Fin.not_lt.mp h) (Ne.symm hne)
          exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩⟩
      calc ((Finset.univ : Finset (DDS X X q)).filter _).card
          ≤ (pairs.biUnion collision).card := Finset.card_le_card h_subset
        _ ≤ ∑ p ∈ pairs, (collision p).card := Finset.card_biUnion_le
    -- a/c ≤ ∑ (bᵢ/c) when a ≤ ∑ bᵢ
    calc ((Finset.univ.filter _).card : NNReal) / (Fintype.card (DDS X X q) : NNReal)
        ≤ (∑ p ∈ (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2),
          ((Finset.univ.filter (fun s : DDS X X q =>
            (DDS.transcript s inputs p.1).2 = (DDS.transcript s inputs p.2).2)).card : NNReal)) /
          (Fintype.card (DDS X X q) : NNReal) := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast h_nat_ub
      _ = _ := by
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul]
  -- Step 4: Each pairwise collision term ≤ 1/|X| (by urf_pairwise_collision_frac)
  have h_each_pair : ∀ p ∈ (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2),
      ((Finset.univ.filter
        (fun s : DDS X X q => (DDS.transcript s inputs p.1).2 = (DDS.transcript s inputs p.2).2)).card : NNReal) /
      (Fintype.card (DDS X X q) : NNReal) ≤
    (1 : NNReal) / (Fintype.card X : NNReal) := by
    intro ⟨pi, pj⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hij : pi ≠ pj := Fin.ne_of_lt hp
    have h_frac := urf_pairwise_collision_frac inputs pi pj hij
    -- Convert: |collision| * |X| ≤ |DDS| implies |collision| / |DDS| ≤ 1 / |X|
    have h_dds_pos : (0 : NNReal) < (Fintype.card (DDS X X q) : NNReal) :=
      Nat.cast_pos.mpr (Fintype.card_pos (α := DDS X X q))
    haveI : Nonempty X := ⟨inputs pi⟩
    have h_x_pos : (0 : NNReal) < (Fintype.card X : NNReal) :=
      Nat.cast_pos.mpr (Fintype.card_pos (α := X))
    rw [div_le_div_iff₀ h_dds_pos h_x_pos]
    simp only [one_mul]; exact_mod_cast h_frac
  -- Step 5: Sum of C(q,2) copies of 1/|X| = q(q-1)/(2|X|) = birthdayBound
  have h_sum_pairs : ∑ p ∈ (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2),
      (1 : NNReal) / (Fintype.card X : NNReal) =
    birthdayBound q (Fintype.card X) := by
    rw [Finset.sum_const, nsmul_eq_mul, birthdayBound]
    -- Goal: ↑|{(i,j) | i < j}| * (1/|X|) = ↑(q*(q-1)) / ↑(2*|X|)
    have h_card := card_strictLTPairs (q := q)
    rw [mul_one_div]
    rw [show (q * (q - 1) : ℕ) = ((Finset.univ : Finset (Fin q × Fin q)).filter
        (fun p => p.1 < p.2)).card * 2 from h_card.symm]
    push_cast
    ring
  -- Combine
  exact le_trans h_union_bound (le_trans (Finset.sum_le_sum h_each_pair) (le_of_eq h_sum_pairs))

omit [Fintype (Transcript X X q)] [DecidableEq (Transcript X X q)] in
/-- **General PRF/PRP Switching Lemma** (Birthday Bound).

The maximum probability that a URF produces a collision in q outputs
is at most q(q-1)/(2|X|).

  ν(URF, allOutputsDistinct) ≤ q(q-1)/(2|X|)

Combined with `advantage_le_single_failure`, this gives for any system T
conditionally equivalent to URF under allOutputsDistinct:

  Adv(URF, T) ≤ q(q-1)/(2|X|) -/
theorem urf_collision_bound_general [Nonempty (DDS X X q)] :
    maxConditionFailure
      (Instances.URF (X := X) (Y := X) (q := q))
      (allOutputsDistinct X q)
    ≤ birthdayBound q (Fintype.card X) := by
  simp only [maxConditionFailure]
  apply Finset.sup_le
  intro inputs _
  exact urf_collision_prob_le_birthday inputs

end RandomSystems.Applications
