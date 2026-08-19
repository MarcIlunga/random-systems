/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.ConditionBased
import RandomSystems.Legacy.Instances.URF
import RandomSystems.Legacy.Applications.PRPPRFSwitching

/-!
# CTR-Mode Encryption Security

CTR-mode encryption with a uniform random function (URF) is perfectly
indistinguishable from a URF when nonces are distinct.

## Construction

Given a block function `F : X → X` and input `(nonce, plaintext)`,
CTR mode outputs `F(nonce) + plaintext`. Under a uniform random F,
this is a pushforward PDS on `X × X → X`.

## Main Result

* `ctr_equiv_urf` — for any input sequence with distinct nonces,
  `ctrPDS.transcriptDist inputs = URF.transcriptDist inputs`

This is a perfect equivalence (advantage = 0), not just a bound.
The proof factors both transcript distributions through a common
"independent uniform outputs" distribution.

## References

* Maurer, U. (2002). "Indistinguishability of Random Systems." EUROCRYPT 2002.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

variable {X : Type*} [AddCommGroup X] [Fintype X] [DecidableEq X] {q : ℕ}

/-- CTR-mode encryption as a DDS: given `F : X → X`, encrypt `(nonce, msg)`
as `F(nonce) + msg`. The DDS is stateless — each response depends only on the
current input, not on the history. -/
def ctrDDS (F : X → X) : DDS (X × X) X q where
  respond := fun i inputs =>
    let inp := inputs ⟨i, Nat.lt_succ_iff.mpr le_rfl⟩
    F inp.1 + inp.2

/-- CTR-mode PDS: the pushforward of the uniform distribution on `X → X`
(modeled as `DDS X X 1` via `dds1Equiv`) through the CTR-DDS construction. -/
def ctrPDS [Nonempty (DDS X X 1)] : PDS (X × X) X q where
  dist := Dist.fTransform
    (fun (s : DDS X X 1) => ctrDDS (X := X) (q := q) (dds1Equiv X X s))
    (Dist.uniform (DDS X X 1))

omit [Fintype X] [DecidableEq X] in
/-- The CTR transcript simplifies: each entry is `(input_i, F(nonce_i) + msg_i)`. -/
lemma ctrDDS_transcript (F : X → X) (inputs : Fin q → X × X) (i : Fin q) :
    DDS.transcript (ctrDDS F) inputs i = (inputs i, F (inputs i).1 + (inputs i).2) := by
  simp [DDS.transcript, ctrDDS]

omit [AddCommGroup X] [Fintype X] [DecidableEq X] in
/-- Distinct nonces imply distinct inputs as `X × X` pairs:
if `Prod.fst ∘ inputs` is injective, so is `inputs`. -/
lemma injective_of_fst_injective (inputs : Fin q → X × X)
    (h : Function.Injective (fun i => (inputs i).1)) :
    Function.Injective inputs :=
  fun _ _ hij => h (congrArg Prod.fst hij)

/-! ### Factoring transcript maps through output extraction -/

/-- The CTR output extraction: maps a DDS X X 1 (≃ function X → X) to the
vector of outputs at each query. -/
private def ctrOutput (inputs : Fin q → X × X) (s : DDS X X 1) : Fin q → X :=
  fun i => (dds1Equiv X X s) (inputs i).1 + (inputs i).2

/-- The URF output extraction: maps a DDS (X×X) X q to the vector of
responses at the fixed input sequence. -/
private def urfOutput (inputs : Fin q → X × X) (s : DDS (X × X) X q) : Fin q → X :=
  fun i => s.respond i (fun j => inputs ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)

/-- The transcript embedding: pairs each output with its corresponding input. -/
private def transcriptEmbed (inputs : Fin q → X × X) (ys : Fin q → X) :
    Transcript (X × X) X q :=
  fun i => (inputs i, ys i)

/-- The CTR transcript map factors as `transcriptEmbed ∘ ctrOutput`. -/
private lemma ctr_factors (inputs : Fin q → X × X) :
    (fun s : DDS X X 1 => DDS.transcript (ctrDDS (dds1Equiv X X s)) inputs) =
    transcriptEmbed inputs ∘ ctrOutput inputs := by
  funext s; funext i
  simp [DDS.transcript, ctrDDS, ctrOutput, transcriptEmbed, dds1Equiv, DDS.firstQuery]

/-- The URF transcript map factors as `transcriptEmbed ∘ urfOutput`. -/
private lemma urf_factors (inputs : Fin q → X × X) :
    (fun s : DDS (X × X) X q => DDS.transcript s inputs) =
    transcriptEmbed inputs ∘ urfOutput inputs := by
  funext s; funext i
  simp [DDS.transcript, urfOutput, transcriptEmbed]

/-! ### CTR output uniformity -/

/-- Evaluating a uniform random function at distinct nonces and adding fixed messages
produces a uniform distribution over output vectors. -/
private lemma ctr_output_uniform [Nonempty (DDS X X 1)]
    (inputs : Fin q → X × X) [Nonempty (Fin q → X)]
    (h_distinct : Function.Injective (fun i => (inputs i).1)) :
    Dist.fTransform (ctrOutput inputs) (Dist.uniform (DDS X X 1)) =
    Dist.uniform (Fin q → X) := by
  haveI : Nonempty X := ⟨(dds1Equiv X X (Classical.arbitrary _)) (Classical.arbitrary X)⟩
  -- Decompose ctrOutput as: addMsgs ∘ evalNonces ∘ dds1Equiv (definitional)
  show Dist.fTransform (
    (fun ys : Fin q → X => fun i => ys i + (inputs i).2) ∘
    ((fun f : X → X => fun i => f (inputs i).1) ∘ ⇑(dds1Equiv X X)))
    (Dist.uniform (DDS X X 1)) = _
  rw [← Dist.fTransform_comp _ _ _, ← Dist.fTransform_comp _ _ _]
  -- Step 1: dds1Equiv pushes uniform DDS to uniform (X → X)
  rw [Dist.fTransform_equiv_uniform (dds1Equiv X X)]
  -- Step 2: eval at nonces pushes uniform (X → X) to uniform (Fin q → X)
  rw [Instances.eval_nonces_uniform (fun i => (inputs i).1) h_distinct]
  -- Step 3: adding messages is a bijection, preserves uniform
  exact Dist.fTransform_bijection_uniform _ ⟨
    fun ys₁ ys₂ h => by ext i; exact add_right_cancel (congr_fun h i),
    fun ys => ⟨fun i => ys i - (inputs i).2, by ext i; simp [sub_add_cancel]⟩⟩

/-! ### URF output uniformity -/

/-- The query prefix function: the first `i+1` inputs. -/
private def qPrefix (inputs : Fin q → X × X) (i : Fin q) : Fin (i.val + 1) → X × X :=
  fun j => inputs ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩

/-- Dependent product distribution: `(i → Aᵢ × Bᵢ) ≃ (i → Aᵢ) × (i → Bᵢ)`. -/
private def piProdEquiv {ι : Type*} (B : ι → Type*) :
    ((i : ι) → X × B i) ≃ (ι → X) × ((i : ι) → B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv f := by ext i <;> simp
  right_inv p := by ext <;> simp

/-- The DDS decomposition: split each respond level at its query prefix. -/
private def ddsDecomp (inputs : Fin q → X × X) :
    DDS (X × X) X q ≃
    (Fin q → X) ×
    ((i : Fin q) → ({f : Fin (i.val + 1) → X × X // f ≠ qPrefix inputs i} → X)) :=
  (DDS.equivRespond (X × X) X q).trans
    ((Equiv.piCongrRight (fun i => Equiv.funSplitAt (qPrefix inputs i) X)).trans
      (piProdEquiv _))

/-- The URF output extraction equals `Prod.fst` after the DDS decomposition. -/
private lemma urfOutput_eq_fst_decomp (inputs : Fin q → X × X) :
    urfOutput inputs = Prod.fst ∘ ddsDecomp inputs := by
  funext s
  simp only [Function.comp, ddsDecomp, Equiv.trans_apply, DDS.equivRespond,
    Equiv.funSplitAt, piProdEquiv]
  rfl

/-- Extracting responses from a uniform random DDS at fixed inputs
produces a uniform distribution over output vectors. -/
private lemma urf_output_uniform [Nonempty (DDS (X × X) X q)]
    (inputs : Fin q → X × X) [Nonempty (Fin q → X)] :
    Dist.fTransform (urfOutput inputs) (Dist.uniform (DDS (X × X) X q)) =
    Dist.uniform (Fin q → X) := by
  classical
  rw [urfOutput_eq_fst_decomp]
  rw [← Dist.fTransform_comp Prod.fst (ddsDecomp inputs) _]
  haveI : Nonempty ((Fin q → X) ×
    ((i : Fin q) → ({f : Fin (i.val + 1) → X × X // f ≠ qPrefix inputs i} → X))) :=
    ⟨(ddsDecomp inputs) (Classical.arbitrary _)⟩
  rw [Dist.fTransform_equiv_uniform (ddsDecomp inputs)]
  haveI : Nonempty ((i : Fin q) →
    ({f : Fin (i.val + 1) → X × X // f ≠ qPrefix inputs i} → X)) :=
    ⟨((ddsDecomp inputs) (Classical.arbitrary _)).2⟩
  exact Dist.fTransform_fst_uniform _ _

/-! ### Main theorem -/

/-- **Main theorem**: CTR mode with a URF is perfectly equivalent to a URF
when nonces are distinct.

For any input sequence where the nonce components are injective,
the transcript distributions of CTR[URF] and URF are identical.

The proof factors both distributions as:
  `fTransform (transcriptEmbed inputs) (uniform (Fin q → X))`
using the output uniformity lemmas. -/
theorem ctr_equiv_urf
    [Nonempty (DDS X X 1)] [Nonempty (DDS (X × X) X q)]
    (inputs : Fin q → X × X)
    (h_distinct : Function.Injective (fun i => (inputs i).1)) :
    (ctrPDS (X := X) (q := q)).transcriptDist inputs =
    (Instances.URF (X := X × X) (Y := X) (q := q)).transcriptDist inputs := by
  haveI : Nonempty (Fin q → X) := ⟨fun _ => Classical.arbitrary X⟩
  -- Unfold transcript distributions as fTransforms
  show Dist.fTransform (fun s => DDS.transcript s inputs)
      (Dist.fTransform (fun s => ctrDDS (dds1Equiv X X s)) (Dist.uniform (DDS X X 1))) =
    Dist.fTransform (fun s => DDS.transcript s inputs) (Dist.uniform (DDS (X × X) X q))
  -- Compose the CTR fTransforms
  rw [Dist.fTransform_comp]
  -- Factor both sides through transcriptEmbed
  rw [show (fun s => DDS.transcript s inputs) ∘
      (fun s : DDS X X 1 => ctrDDS (dds1Equiv X X s)) =
    transcriptEmbed inputs ∘ ctrOutput inputs from ctr_factors inputs]
  rw [show (fun s : DDS (X × X) X q => DDS.transcript s inputs) =
    transcriptEmbed inputs ∘ urfOutput inputs from urf_factors inputs]
  -- Decompose into embed ∘ output_map
  rw [(Dist.fTransform_comp (transcriptEmbed inputs) (ctrOutput inputs) _).symm]
  rw [(Dist.fTransform_comp (transcriptEmbed inputs) (urfOutput inputs) _).symm]
  -- Both output maps produce uniform (Fin q → X)
  rw [ctr_output_uniform inputs h_distinct, urf_output_uniform inputs]

end RandomSystems.Applications
