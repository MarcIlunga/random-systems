import SequenceHash.RandomSystems.SequenceMACGenericBad
import RandomSystems.SwitchingLemma

/-!
# SequenceFunction fresh compression fibers

This module is the first, freshness-only part of the equality-on-good layer
for the R4 ideal-compression proof.  Off `Bad_SEQ`, the revealed construction
compression inputs are disjoint from every visible primitive input and are
pairwise distinct in execution order.  Restricting the uniform compression
table to those sites is therefore a jointly uniform function.

The representative reveal maps and the real/ideal extended-mass fiber
identity are intentionally left to the next layer.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems
open RandomSystems.CR18
open RandomSystems.HTechnique.IdealCompression

universe uBlock

/-! ## Freshness off `Bad_SEQ` -/

/-- The compression-freshness invariant supplied by the complement of
`Bad_SEQ`: every construction input avoids the visible primitive inputs, and
the construction inputs are pairwise distinct in their revealed execution
order. -/
def SequenceFunctionCompressionFresh {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  (∀ input ∈ sequenceFunctionRevealedConstructionInputs tz.2,
      input ∉ sequenceFunctionVisiblePrimInputs tz.1) ∧
    (sequenceFunctionRevealedConstructionInputs tz.2).Nodup

/-- `Bad_SEQ` is exactly the failure of the compression-freshness invariant. -/
theorem not_Bad_SEQ_iff_compressionFresh {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :
    ¬ Bad_SEQ tz ↔ SequenceFunctionCompressionFresh tz := by
  simp only [Bad_SEQ, SequenceFunctionCompressionFresh, not_or,
    not_exists, not_and]
  grind

/-- Off `Bad_SEQ`, an indexed construction compression call is fresh against
every visible primitive call and against every earlier construction call. -/
theorem sequenceFunctionConstructionCall_fresh_of_not_Bad_SEQ
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hgood : ¬ Bad_SEQ tz)
    (i : Fin (sequenceFunctionRevealedConstructionInputs tz.2).length) :
    let input := (sequenceFunctionRevealedConstructionInputs tz.2).get i
    input ∉ sequenceFunctionVisiblePrimInputs tz.1 ∧
      ∀ j : Fin (sequenceFunctionRevealedConstructionInputs tz.2).length,
        j < i →
          (sequenceFunctionRevealedConstructionInputs tz.2).get j ≠ input := by
  have hfresh := (not_Bad_SEQ_iff_compressionFresh tz).1 hgood
  dsimp only
  refine ⟨hfresh.1 _ (List.get_mem _ _), ?_⟩
  intro j hji heq
  exact (Fin.ne_of_lt hji) (hfresh.2.injective_get heq)

/-- The finite sites whose compression-table values are exposed by a good
extended transcript: the distinct visible primitive inputs, followed by the
ordered construction inputs. -/
abbrev SequenceFunctionFreshCompressionSite {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    [DecidableEq Block]
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :=
  ↥(sequenceFunctionVisiblePrimInputs tz.1).toFinset ⊕
    Fin (sequenceFunctionRevealedConstructionInputs tz.2).length

/-- Off `Bad_SEQ`, visible primitive sites and ordered construction sites
embed disjointly into the compression-function domain. -/
def sequenceFunctionFreshCompressionEmbedding
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [DecidableEq Block]
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hgood : ¬ Bad_SEQ tz) :
    SequenceFunctionFreshCompressionSite tz ↪ HashOutput L × Block where
  toFun
    | .inl input => input.1
    | .inr i => (sequenceFunctionRevealedConstructionInputs tz.2).get i
  inj' := by
    have hfresh := (not_Bad_SEQ_iff_compressionFresh tz).1 hgood
    intro i j hij
    cases i with
    | inl input =>
        cases j with
        | inl input' =>
            exact congrArg Sum.inl (Subtype.ext hij)
        | inr j =>
            exfalso
            have hprim : input.1 ∈ sequenceFunctionVisiblePrimInputs tz.1 :=
              List.mem_toFinset.mp input.2
            change input.1 =
              (sequenceFunctionRevealedConstructionInputs tz.2).get j at hij
            rw [hij] at hprim
            exact hfresh.1 _ (List.get_mem _ _) hprim
    | inr i =>
        cases j with
        | inl input =>
            exfalso
            have hprim : input.1 ∈ sequenceFunctionVisiblePrimInputs tz.1 :=
              List.mem_toFinset.mp input.2
            change (sequenceFunctionRevealedConstructionInputs tz.2).get i =
              input.1 at hij
            rw [← hij] at hprim
            exact hfresh.1 _ (List.get_mem _ _) hprim
        | inr j =>
            exact congrArg Sum.inr (hfresh.2.injective_get hij)

/-! ## Fresh uniform compression values -/

/-- **Per-call freshness implies independence.**  Off `Bad_SEQ`, the
compression-function values at all distinct visible primitive sites and all
ordered construction sites form one jointly uniform function.  In
particular, every construction call is a fresh uniform value independent of
the preceding visible and construction calls.

This is `uniform_restrict` after uncurrying the facade's compression-function
carrier `C → B → C` to the point-table carrier `(C × B) → C`. -/
theorem sequenceFunctionFreshCompressionValues_uniform
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hgood : ¬ Bad_SEQ tz) :
    Dist.fTransform
        (fun h : CompressionFunction (HashOutput L) Block =>
          fun site : SequenceFunctionFreshCompressionSite tz =>
            let input := sequenceFunctionFreshCompressionEmbedding tz hgood site
            h input.1 input.2)
        (Dist.uniform (CompressionFunction (HashOutput L) Block)) =
      Dist.uniform
        (SequenceFunctionFreshCompressionSite tz → HashOutput L) := by
  let uncurryCompression :=
    (Equiv.curry (HashOutput L) Block (HashOutput L)).symm
  have huncurry := Dist.fTransform_equiv_uniform uncurryCompression
  have hrestrict := uniform_restrict
    (O := HashOutput L) (sequenceFunctionFreshCompressionEmbedding tz hgood)
  rw [← huncurry, Dist.fTransform_comp] at hrestrict
  simpa [uncurryCompression, Function.comp_def] using hrestrict

end RandomSystemsModel
end SequenceHash
