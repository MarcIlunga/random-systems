/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.PRPPRFSwitching
import RandomSystems.StatDist
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# General PRF/PRP Switching Lemma

The switching lemma for general q:
  `statDist(URF.transcriptDist, URPq.transcriptDist) ≤ birthdayBound q |X|`

for any injective input sequence.

## Strategy

Split transcript-level statDist into injective and non-injective output transcripts:
1. On injective-output transcripts: URPq mass ≥ URF mass (fiber counting),
   so the NNReal truncated subtraction is 0.
2. On non-injective-output transcripts: bound by `tsub_le_self`, giving
   `conditionFailureProb URF (allOutputsDistinct) inputs ≤ birthdayBound`.

## Main Result

* `prf_prp_switching_general` — `statDist ≤ birthdayBound q |X|`
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

variable {X : Type*} [Fintype X] [DecidableEq X]
  {q : ℕ} [Fintype (DDS X X q)]

/-! ### Output extraction and transcript factoring -/

/-- The output extraction: extract the vector of responses at fixed inputs. -/
private def outputMap (inputs : Fin q → X) (s : DDS X X q) : Fin q → X :=
  fun i => s.respond i (fun j => inputs ⟨j.val,
    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)

/-- The transcript embedding: pairs each output with its corresponding input. -/
private def transcriptEmbed' (inputs : Fin q → X) (ys : Fin q → X) :
    Transcript X X q :=
  fun i => (inputs i, ys i)

omit [Fintype X] [DecidableEq X] [Fintype (DDS X X q)] in
/-- The transcript map factors as `transcriptEmbed' ∘ outputMap`. -/
private lemma transcript_factors (inputs : Fin q → X) :
    (fun s : DDS X X q => DDS.transcript s inputs) =
    transcriptEmbed' inputs ∘ outputMap inputs := by
  funext s i
  simp [DDS.transcript, outputMap, transcriptEmbed']

omit [Fintype X] [DecidableEq X] [Fintype (DDS X X q)] in
/-- `transcriptEmbed'` is injective when inputs are fixed. -/
private lemma transcriptEmbed'_injective (inputs : Fin q → X) :
    Function.Injective (transcriptEmbed' inputs) := by
  intro ys₁ ys₂ h
  funext i
  exact (Prod.mk.inj (congr_fun h i)).2

/-! ### Dependent product equivalence (needed for DDS decomposition) -/

/-- Dependent product equivalence: `(i → X × Bᵢ) ≃ (i → X) × (i → Bᵢ)`. -/
private def piProdEquiv {ι : Type*} {B : ι → Type*} :
    ((i : ι) → X × B i) ≃ (ι → X) × ((i : ι) → B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv f := by ext i <;> simp
  right_inv p := by ext <;> simp

/-- The query prefix function. -/
private def qPrefix (inputs : Fin q → X) (i : Fin q) : Fin (i.val + 1) → X :=
  fun j => inputs ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩

/-- The DDS decomposition:
  `DDS X X q ≃ (Fin q → X) × Rest` -/
private def ddsDecomp (inputs : Fin q → X) :
    DDS X X q ≃
    (Fin q → X) ×
    ((i : Fin q) → ({f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → X)) :=
  (DDS.equivRespond X X q).trans
    ((Equiv.piCongrRight (fun i =>
      Equiv.funSplitAt (qPrefix inputs i) X)).trans
      piProdEquiv)

omit [Fintype X] [Fintype (DDS X X q)] in
/-- The output extraction equals `Prod.fst` after the DDS decomposition. -/
private lemma outputMap_eq_fst_decomp (inputs : Fin q → X) :
    outputMap inputs = Prod.fst ∘ ddsDecomp inputs := by
  funext s
  simp only [Function.comp, ddsDecomp, Equiv.trans_apply, DDS.equivRespond,
    Equiv.funSplitAt, piProdEquiv]
  rfl

/-! ### URF output uniformity -/

/-- Extracting responses from a URF produces uniform output vectors. -/
private lemma urf_output_uniform [Nonempty (DDS X X q)]
    (inputs : Fin q → X) [Nonempty (Fin q → X)] :
    Dist.fTransform (outputMap inputs) (Dist.uniform (DDS X X q)) =
    Dist.uniform (Fin q → X) := by
  classical
  -- Provide the `Nonempty` witnesses for the intermediate carriers up front: the
  -- `Dist` API (`fTransform_comp`, `fTransform_equiv_uniform`) now requires them.
  haveI : Nonempty ((Fin q → X) ×
    ((i : Fin q) → ({f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → X))) :=
    ⟨(ddsDecomp inputs) (Classical.arbitrary _)⟩
  haveI : Nonempty ((i : Fin q) →
    ({f : Fin (i.val + 1) → X // f ≠ qPrefix inputs i} → X)) :=
    ⟨((ddsDecomp inputs) (Classical.arbitrary _)).2⟩
  rw [outputMap_eq_fst_decomp]
  rw [← Dist.fTransform_comp Prod.fst (ddsDecomp inputs) _]
  rw [Dist.fTransform_equiv_uniform (ddsDecomp inputs)]
  exact Dist.fTransform_fst_uniform _ _

/-! ### URPq output: zero on non-injective -/

omit [Fintype X] [DecidableEq X] [Fintype (DDS X X q)] in
/-- A stateless-perm DDS maps injective inputs to injective outputs. -/
private lemma statelessPerm_injective_outputs
    (s : DDS X X q) (hs : Instances.isStatelessPerm s)
    (inputs : Fin q → X) (h_inj : Function.Injective inputs) :
    Function.Injective (outputMap inputs s) := by
  obtain ⟨π, hπ⟩ := hs
  intro i j hij
  simp only [outputMap] at hij
  rw [hπ i, hπ j] at hij
  exact h_inj (π.injective hij)

/-- For non-injective output vectors, URPq assigns zero mass. -/
private lemma urpq_zero_on_non_injective
    (inputs : Fin q → X) (h_inj : Function.Injective inputs)
    (ys : Fin q → X) (h_not_inj : ¬Function.Injective ys) :
    (Dist.fTransform (outputMap inputs) (Instances.URPq (X := X) (q := q)).dist) ys = 0 := by
  simp only [Instances.URPq, Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro s hs
  simp only [Finsupp.mem_support_iff] at hs
  have h_perm : Instances.isStatelessPerm s := by
    by_contra h_not
    apply hs
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_filter] at ht
    have : t ≠ s := by intro heq; subst heq; exact h_not ht.2
    simp [this]
  rw [if_neg]
  intro heq
  exact h_not_inj (heq ▸ statelessPerm_injective_outputs s h_perm inputs h_inj)

/-! ### Fiber counting for permutations with prescribed values -/

set_option linter.unusedSectionVars false in
/-- The number of permutations fixing prescribed values.

  |{π : Perm X | ∀ i, π (inputs i) = ys i}| = (|X| - q)!

when `inputs` and `ys` are both injective and `q ≤ |X|`.

This is a reusable fiber-counting lemma proved via the orbit-stabilizer
argument using `MulAction.IsPretransitive` on `Fin q ↪ X`. -/
theorem card_perm_fiber
    (inputs : Fin q → X) (h_inj : Function.Injective inputs)
    (ys : Fin q → X) (h_ys_inj : Function.Injective ys)
    (h_q_le : q ≤ Fintype.card X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card =
    (Fintype.card X - q).factorial := by
  -- Use orbit-stabilizer counting argument.
  -- All fibers equal via multiply pretransitive action.
  set S := Finset.univ.image inputs with hS_def
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]
  have h_desc_pos : 0 < (Fintype.card X).descFactorial q :=
    Nat.descFactorial_pos.mpr h_q_le
  suffices h_prod : ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card *
      (Fintype.card X).descFactorial q = (Fintype.card X).factorial by
    have h_eq := Nat.factorial_mul_descFactorial h_q_le
    exact Nat.eq_of_mul_eq_mul_right h_desc_pos (h_prod.trans h_eq.symm)
  -- Define the map Φ and the set of injective q-tuples
  set Φ : Equiv.Perm X → (Fin q ↪ X) :=
    fun π => ⟨fun i => π (inputs i), (π.injective.comp h_inj)⟩
  set injTuples := (Finset.univ : Finset (Fin q ↪ X))
  -- Step 1: Partition Perm X by Φ
  have h_partition : (Finset.univ : Finset (Equiv.Perm X)).card =
      ∑ z ∈ injTuples, (Finset.univ.filter (fun π => Φ π = z)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  -- Step 2: All fibers have equal size via multiply pretransitive action.
  set ys_emb : Fin q ↪ X := ⟨ys, h_ys_inj⟩
  have h_fiber_eq : ∀ z ∈ injTuples,
      (Finset.univ.filter (fun π => Φ π = z)).card =
      (Finset.univ.filter (fun π => Φ π = ys_emb)).card := by
    intro z _
    have h_pt : MulAction.IsPretransitive (Equiv.Perm X) (Fin q ↪ X) :=
      Equiv.Perm.isMultiplyPretransitive X q
    obtain ⟨τ, hτ⟩ := h_pt.exists_smul_eq ys_emb z
    -- τ • ys_emb = z means ∀ i, τ (ys i) = z i
    have hτ_app : ∀ i, τ (ys i) = z i := fun i => congr_fun (congr_arg (↑·) hτ) i
    -- Bijection: fiber(z) ≃ fiber(ys_emb) via π ↦ τ⁻¹ * π and σ ↦ τ * σ
    apply Finset.card_bij'
      (fun π _ => τ⁻¹ * π)  -- fiber(z) → fiber(ys_emb)
      (fun σ _ => τ * σ)     -- fiber(ys_emb) → fiber(z)
    · -- hi: τ⁻¹ * π ∈ fiber(ys_emb)
      intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      ext i
      show τ⁻¹ (π (inputs i)) = ys i
      have : π (inputs i) = z i := congr_fun (congr_arg (↑·) hπ) i
      rw [this, ← hτ_app i]; simp
    · -- hj: τ * σ ∈ fiber(z)
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      ext i
      show τ (σ (inputs i)) = z i
      have : σ (inputs i) = ys i := congr_fun (congr_arg (↑·) hσ) i
      rw [this, hτ_app i]
    · -- left_inv
      intro π _; simp
    · -- right_inv
      intro σ _; simp
  -- Step 3: Fiber of our target ys equals the filter set
  have h_fiber_match : (Finset.univ.filter (fun π : Equiv.Perm X => ∀ i, π (inputs i) = ys i)) =
      (Finset.univ.filter (fun π => Φ π = ys_emb)) := by
    ext π; simp [Finset.mem_filter, Φ, ys_emb, Function.Embedding.ext_iff]
  -- Step 4: Cardinality of injective tuples
  have h_inj_card : injTuples.card = (Fintype.card X).descFactorial q := by
    simp only [injTuples, Finset.card_univ]
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
  -- Step 5: Assemble
  rw [h_fiber_match]
  -- All fibers are equal, so the sum is fiber_size × #fibers
  have h_sum_eq : ∑ z ∈ injTuples,
      (Finset.univ.filter (fun π => Φ π = z)).card =
      (Finset.univ.filter (fun π => Φ π = ys_emb)).card * injTuples.card := by
    rw [Finset.sum_const_nat (fun z hz => h_fiber_eq z hz), mul_comm]
  -- |Perm X| = fiber_size × #injTuples
  have h_card_perm : (Finset.univ : Finset (Equiv.Perm X)).card = Fintype.card (Equiv.Perm X) :=
    Finset.card_univ
  rw [mul_comm]
  calc (Fintype.card X).descFactorial q *
        (Finset.univ.filter (fun π => Φ π = ys_emb)).card
      = injTuples.card * (Finset.univ.filter (fun π => Φ π = ys_emb)).card := by
          rw [h_inj_card]
    _ = (Finset.univ.filter (fun π => Φ π = ys_emb)).card * injTuples.card := by
          rw [mul_comm]
    _ = ∑ z ∈ injTuples, (Finset.univ.filter (fun π => Φ π = z)).card := h_sum_eq.symm
    _ = (Finset.univ : Finset (Equiv.Perm X)).card := h_partition.symm
    _ = Fintype.card (Equiv.Perm X) := h_card_perm
    _ = (Fintype.card X).factorial := Fintype.card_perm

/-- The DDS fiber count equals the Perm fiber count. -/
private lemma card_perm_fiber_dds (hq : 0 < q)
    (inputs : Fin q → X) (h_inj : Function.Injective inputs)
    (ys : Fin q → X) (h_ys_inj : Function.Injective ys) :
    ((Finset.univ.filter Instances.isStatelessPerm).filter
      (fun s : DDS X X q => outputMap inputs s = ys)).card =
    ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card := by
  have h_rewrite : (Finset.univ.filter Instances.isStatelessPerm).filter
      (fun s : DDS X X q => outputMap inputs s = ys) =
      Finset.univ.filter (fun s => Instances.isStatelessPerm s ∧ outputMap inputs s = ys) := by
    ext s; simp [Finset.mem_filter]
  rw [h_rewrite]
  apply Finset.card_bij'
    (fun s (hs : s ∈ Finset.univ.filter
      (fun s => Instances.isStatelessPerm s ∧ outputMap inputs s = ys)) =>
      (Finset.mem_filter.mp hs).2.1.choose)
    (fun π _ => Instances.ofPerm π)
  · -- hi: forward maps into the target set
    intro s hs
    have hmem := (Finset.mem_filter.mp hs).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    have hπ := hmem.1.choose_spec i
    have := congr_fun hmem.2 i
    simp only [outputMap] at this
    rw [hπ] at this; exact this
  · -- left_inv: ofPerm (choose ...) = s
    intro s hs
    have hmem := (Finset.mem_filter.mp hs).2
    exact (Instances.isStatelessPerm_eq_ofPerm s hmem.1).symm
  · -- right_inv: choose (ofPerm π ...) = π
    intro π _
    exact Instances.ofPerm_injective hq
      (Instances.isStatelessPerm_eq_ofPerm _ (Instances.ofPerm_isStatelessPerm π)).symm
  · -- hj: inverse maps into the source set
    intro π hπ
    have hπ' := (Finset.mem_filter.mp hπ).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Instances.ofPerm_isStatelessPerm π, ?_⟩
    funext i; simp only [outputMap, Instances.ofPerm]; exact hπ' i

/-! ### URPq transcript mass dominates URF on injective-output transcripts -/

/-- For injective-output transcripts, URPq assigns at least as much mass as URF. -/
private lemma urpq_ge_urf_on_injective_transcript
    [Nonempty (DDS X X q)]
    [Fintype (Transcript X X q)] [DecidableEq (Transcript X X q)]
    (inputs : Fin q → X) (h_inj : Function.Injective inputs) (hq : 0 < q)
    (t : Transcript X X q) (ht : (allOutputsDistinct X q).holds t) :
    (Instances.URF (X := X) (Y := X) (q := q)).transcriptDist inputs t ≤
    (Instances.URPq (X := X) (q := q)).transcriptDist inputs t := by
  by_cases h_in_image : ∃ s : DDS X X q, DDS.transcript s inputs = t
  case neg =>
    have h_zero : ∀ (D : Dist (DDS X X q)),
        (Dist.fTransform (fun s => DDS.transcript s inputs) D) t = 0 := by
      intro D
      show (Finsupp.mapDomain (fun s => DDS.transcript s inputs) D) t = 0
      rw [Finsupp.mapDomain, Finsupp.sum]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
      apply Finset.sum_eq_zero
      intro s _; rw [if_neg (fun h => h_in_image ⟨s, h⟩)]
    simp only [PDS.transcriptDist, Instances.URF]
    rw [h_zero]; exact zero_le _
  case pos =>
  obtain ⟨s₀, hs₀⟩ := h_in_image
  have h_inputs : ∀ i, (t i).1 = inputs i := by
    intro i
    have h := congr_fun hs₀ i
    simp only [DDS.transcript] at h
    exact (congr_arg Prod.fst h).symm
  set ys := fun i => (t i).2
  have h_t_eq : t = transcriptEmbed' inputs ys := by
    funext i; show t i = (inputs i, ys i); exact Prod.ext (h_inputs i) rfl
  have h_factor_eq : ∀ (D : Dist (DDS X X q)),
      (Dist.fTransform (fun s => DDS.transcript s inputs) D) t =
      (Dist.fTransform (outputMap inputs) D) ys := by
    intro D
    conv_lhs => rw [show (fun s : DDS X X q => DDS.transcript s inputs) =
      transcriptEmbed' inputs ∘ outputMap inputs from transcript_factors inputs]
    show (Finsupp.mapDomain (transcriptEmbed' inputs ∘ outputMap inputs) D) t =
      (Finsupp.mapDomain (outputMap inputs) D) ys
    rw [Finsupp.mapDomain_comp]
    rw [h_t_eq]
    exact fTransform_injective_apply _ _ (transcriptEmbed'_injective inputs) ys
  simp only [PDS.transcriptDist, Instances.URF]
  rw [h_factor_eq, h_factor_eq]
  haveI : Nonempty (Fin q → X) := ⟨outputMap inputs (Classical.arbitrary _)⟩
  rw [urf_output_uniform inputs]
  -- q > 0 by hypothesis hq
  have hq_ne : q ≠ 0 := hq.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq_ne
  set perms := (Finset.univ : Finset (DDS X X (n + 1))).filter Instances.isStatelessPerm
  set perm_fiber := perms.filter (fun s => outputMap inputs s = ys)
  have h_lhs_val : (Dist.uniform (Fin (n + 1) → X)) ys =
      (1 : NNReal) / (Fintype.card (Fin (n + 1) → X) : NNReal) := by
    simp [Dist.uniform, Finsupp.equivFunOnFinite]
  have h_rhs_val : (Dist.fTransform (outputMap inputs)
      (Instances.URPq (X := X) (q := n + 1)).dist) ys =
      (perm_fiber.card : NNReal) / (perms.card : NNReal) := by
    classical
    show (Finsupp.mapDomain (outputMap inputs)
      (Instances.URPq (X := X) (q := n + 1)).dist) ys = _
    simp only [Instances.URPq]
    rw [Finsupp.mapDomain_finset_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    rfl
  have h_perms_card : perms.card = (Fintype.card X).factorial := by
    change (Finset.filter Instances.isStatelessPerm Finset.univ).card = _
    convert Instances.card_statelessPerm hq <;> infer_instance
  have h_ys_inj : Function.Injective ys := by
    have : (allOutputsDistinct X (n + 1)).holds t := ht
    simp only [allOutputsDistinct] at this
    rw [h_t_eq] at this
    exact this
  have h_q_le : n + 1 ≤ Fintype.card X := by
    haveI : Nonempty X := ⟨inputs ⟨0, hq⟩⟩
    rw [← Fintype.card_fin (n + 1)]
    exact Fintype.card_le_of_injective inputs h_inj
  have h_perm_fiber_card :
      perm_fiber.card * (Fintype.card X).descFactorial (n + 1) = perms.card := by
    rw [h_perms_card, ← Nat.factorial_mul_descFactorial h_q_le]
    congr 1
    rw [show perm_fiber = (Finset.univ.filter Instances.isStatelessPerm).filter
      (fun s : DDS X X (n + 1) => outputMap inputs s = ys) from rfl]
    rw [card_perm_fiber_dds hq inputs h_inj ys h_ys_inj]
    exact card_perm_fiber inputs h_inj ys h_ys_inj h_q_le
  rw [h_lhs_val, h_rhs_val]
  have h_lhs_eq : (Fintype.card (Fin (n + 1) → X) : NNReal) =
      ((Fintype.card X) ^ (n + 1) : NNReal) := by
    exact_mod_cast (show Fintype.card (Fin (n + 1) → X) = (Fintype.card X) ^ (n + 1) from by
      simp [Fintype.card_fin])
  have h_perms_eq : (perms.card : NNReal) = ((Fintype.card X).factorial : NNReal) := by
    exact_mod_cast h_perms_card
  rw [h_lhs_eq, h_perms_eq]
  have h_desc_le := Nat.descFactorial_le_pow (Fintype.card X) (n + 1)
  haveI : Nonempty X := ⟨inputs ⟨0, hq⟩⟩
  have h_pow_pos : (0 : NNReal) < ((Fintype.card X) ^ (n + 1) : NNReal) := by
    exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero _ (Fintype.card_pos (α := X)).ne')
  have h_fact_pos : (0 : NNReal) < ((Fintype.card X).factorial : NNReal) := by
    exact_mod_cast Nat.factorial_pos _
  rw [div_le_div_iff₀ h_pow_pos h_fact_pos, one_mul]
  have h_fiber_eq : (perm_fiber.card : NNReal) * ((Fintype.card X).descFactorial (n + 1) : NNReal) =
      ((Fintype.card X).factorial : NNReal) := by
    rw [show ((Fintype.card X).factorial : NNReal) = (perms.card : NNReal) from h_perms_eq.symm]
    exact_mod_cast h_perm_fiber_card
  calc ((Fintype.card X).factorial : NNReal)
      = (perm_fiber.card : NNReal) * ((Fintype.card X).descFactorial (n + 1) : NNReal) := h_fiber_eq.symm
    _ ≤ (perm_fiber.card : NNReal) * ((Fintype.card X) ^ (n + 1) : NNReal) := by
        gcongr
        exact_mod_cast h_desc_le

/-! ### Main theorem -/

/-- **General PRF/PRP Switching Lemma**.

For any injective input sequence of length q:
  `statDist(URF.transcriptDist, URPq.transcriptDist) ≤ q(q-1)/(2|X|)`

This is the "direct" switching bound that bypasses the condEquiv framework. -/
theorem prf_prp_switching_general
    [Nonempty (DDS X X q)]
    [Fintype (Transcript X X q)] [DecidableEq (Transcript X X q)]
    (inputs : Fin q → X) (h_inj : Function.Injective inputs) :
    statDist
      ((Instances.URF (X := X) (Y := X) (q := q)).transcriptDist inputs)
      ((Instances.URPq (X := X) (q := q)).transcriptDist inputs)
    ≤ birthdayBound q (Fintype.card X) := by
  -- Handle q = 0 trivially: both distributions are equal
  obtain rfl | hq := Nat.eq_zero_or_pos q
  · simp only [statDist]
    apply le_of_eq_of_le _ (zero_le _)
    apply Finset.sum_eq_zero; intro t _
    apply tsub_eq_zero_of_le
    show (Instances.URF.transcriptDist inputs) t ≤ (Instances.URPq.transcriptDist inputs) t
    haveI : Subsingleton (DDS X X 0) :=
      ⟨fun a b => DDS.ext (funext (fun i => i.elim0))⟩
    have h_dist_eq : (Instances.URF (X := X) (Y := X) (q := 0)).dist =
        (Instances.URPq (X := X) (q := 0)).dist := by
      ext s; obtain ⟨s₀⟩ := ‹Nonempty (DDS X X 0)›
      have hs : s = s₀ := Subsingleton.elim _ _; subst hs
      simp only [Instances.URF, Dist.uniform, Finsupp.equivFunOnFinite, Finsupp.coe_mk,
        Instances.URPq]
      have h_all_perm : ∀ x : DDS X X 0, Instances.isStatelessPerm x :=
        fun x => ⟨1, fun i => i.elim0⟩
      rw [Finset.filter_true_of_mem (fun x _ => h_all_perm x)]
      simp
    simp only [PDS.transcriptDist]; rw [h_dist_eq]
  · -- q > 0: use statDist_eq_conditionFailure_when_dominated + birthday bound
    set A := allOutputsDistinct X q
    -- Step 1: URPq = 0 on bad (non-injective output) transcripts
    have h_urp_zero : ∀ t, ¬A.holds t →
        (Instances.URPq (X := X) (q := q)).transcriptDist inputs t = 0 := by
      intro t ht
      simp only [PDS.transcriptDist]
      by_cases h_in : ∃ s : DDS X X q, DDS.transcript s inputs = t
      · obtain ⟨s₀, hs₀⟩ := h_in
        have h_inputs : ∀ i, (t i).1 = inputs i := by
          intro i; have h := congr_fun hs₀ i
          simp only [DDS.transcript] at h
          exact (congr_arg Prod.fst h).symm
        set ys := fun i => (t i).2
        have h_t_eq : t = transcriptEmbed' inputs ys := by
          funext i; exact Prod.ext (h_inputs i) rfl
        have h_not_inj : ¬Function.Injective ys := by
          intro h_ys_inj
          exact ht (by simp only [A, allOutputsDistinct]; rw [h_t_eq]; exact h_ys_inj)
        conv_lhs => rw [show (fun s => DDS.transcript s inputs) =
          transcriptEmbed' inputs ∘ outputMap inputs from transcript_factors inputs]
        show (Finsupp.mapDomain (transcriptEmbed' inputs ∘ outputMap inputs)
          (Instances.URPq (X := X) (q := q)).dist) t = 0
        rw [Finsupp.mapDomain_comp, h_t_eq]
        have h_inj_embed := transcriptEmbed'_injective inputs
        rw [show (Finsupp.mapDomain (transcriptEmbed' inputs)
            (Finsupp.mapDomain (outputMap inputs)
              (Instances.URPq (X := X) (q := q)).dist))
            (transcriptEmbed' inputs ys) =
          (Finsupp.mapDomain (outputMap inputs)
            (Instances.URPq (X := X) (q := q)).dist) ys from
          fTransform_injective_apply _ _ h_inj_embed ys]
        exact urpq_zero_on_non_injective inputs h_inj ys h_not_inj
      · show (Finsupp.mapDomain (fun s => DDS.transcript s inputs)
            (Instances.URPq (X := X) (q := q)).dist) t = 0
        rw [Finsupp.mapDomain, Finsupp.sum]
        simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
        apply Finset.sum_eq_zero
        intro s _; rw [if_neg (fun h => h_in ⟨s, h⟩)]
    -- Step 2: On good (injective-output) transcripts, URF ≤ URPq
    have h_urf_le : ∀ t, A.holds t →
        (Instances.URF (X := X) (Y := X) (q := q)).transcriptDist inputs t ≤
        (Instances.URPq (X := X) (q := q)).transcriptDist inputs t :=
      fun t ht => urpq_ge_urf_on_injective_transcript inputs h_inj hq t ht
    -- Step 3: statDist = conditionFailureProb (via bridge lemma)
    rw [statDist_eq_conditionFailure_when_dominated _ _ A inputs h_urp_zero h_urf_le]
    -- Step 4: conditionFailureProb ≤ maxConditionFailure ≤ birthdayBound
    exact le_trans (Finset.le_sup (f := fun i =>
      conditionFailureProb (Instances.URF (X := X) (Y := X) (q := q)) A i)
      (Finset.mem_univ inputs))
      urf_collision_bound_general

end RandomSystems.Applications
