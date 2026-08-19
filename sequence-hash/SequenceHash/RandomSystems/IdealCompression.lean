import RandomSystems.HTechnique.IdealCompression
import SequenceHash.RandomSystems.SequenceFunctionCore

/-!
# Canonical SequenceFunction ideal-compression facade

This module instantiates the generic joint ideal-compression H-technique
facade with C2SP's canonical `SequenceFunction` over Merkle--Damgard.  It does
not restate the NMAC-shaped inner/outer construction: the real `eval` branch is
definitionally a call to `SequenceHash.sequenceFunction` at the SequenceMAC
function name `F = 1`.

The structural equality-on-good theorem, role classifier, concrete traces,
and bad-event bound belong to the next R4 dispatch.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems RandomSystems.CR18
open RandomSystems.HTechnique.IdealCompression

universe u

/-! ## Frozen compression model and trace-bound type -/

/-- The compression model used by R4: C2SP's digest type is also the MD
chaining state, `codec` fixes byte-to-block processing, and `iv` fixes the
public initial chaining value.  Thus the digest width is the type index
`L : U128`, i.e. `HashOutput L`, rather than an omitted scalar parameter. -/
structure SequenceFunctionCompressionModel (Block : Type u) (L : U128) where
  codec : MDCodec Block
  iv : HashOutput L

/-- Compression work of one raw `Derive` input.  Short inputs are padded
without calling the hash; long inputs make one MD call over `codec.blockify`. -/
def sequenceFunctionDeriveCompressionCost {Block : Type u} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (input : List Byte) : ℕ :=
  if input.length ≤ b.val then 0 else (model.codec.blockify input).length

/-- Public per-`Eval` cost used by `TaggedBudgetRespects`.  It is the existing
finite supremum over the canonical `SequenceFunction` hash-call schedule, with
at most four fixed-output hash calls and no direct `Prim` calls charged here. -/
noncomputable def sequenceFunctionEvalCost {Block : Type u} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) {users : ℕ} :
    Fin users × InputSequence → ℕ :=
  fun _ => sequenceFunctionCompressionCost model.codec b S L 4 0

/--
The exact R4 trace-bound hypothesis frozen for the structural dispatch.

* `evalCost_le` bounds the complete canonical SequenceFunction compression
  schedule of one `Eval` call by `lambda`;
* `keyDeriveCost_le` separately accounts for a long-key derivation by `rK`;
* `customizationDeriveCost_le` accounts for the fixed customization derivation
  by `rS`.

The key clause is uniform because the schematic R4 statement intentionally
does not hide a support restriction inside the trace hypothesis.
-/
structure SequenceFunctionTraceBound {Block : Type u} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (lambda rK rS : ℕ) : Prop where
  evalCost_le :
    sequenceFunctionCompressionCost model.codec b S L 4 0 ≤ lambda
  keyDeriveCost_le : ∀ K : SequenceMACKey,
    sequenceFunctionDeriveCompressionCost model b K.1.val ≤ rK
  customizationDeriveCost_le :
    sequenceFunctionDeriveCompressionCost model b S.val ≤ rS

theorem SequenceFunctionTraceBound.evalCost_apply_le
    {Block : Type u} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString} {lambda rK rS users : ℕ}
    (h : SequenceFunctionTraceBound model b S lambda rK rS)
    (request : Fin users × InputSequence) :
    sequenceFunctionEvalCost model b S request ≤ lambda := by
  simpa [sequenceFunctionEvalCost] using h.evalCost_le

/-! ## Canonical shared-Prim worlds -/

/-- R4 query alphabet: direct compression queries or per-user SequenceMAC
evaluations. -/
abbrev SequenceFunctionICQuery (Block : Type u) (L : U128) (users : ℕ) :=
  RandomSystems.HTechnique.IdealCompression.Query
    (HashOutput L) Block (Fin users) InputSequence

/-- R4 response alphabet: a compression state or SequenceMAC digest. -/
abbrev SequenceFunctionICReply (L : U128) :=
  RandomSystems.HTechnique.IdealCompression.Reply
    (HashOutput L) (HashOutput L)

/-- The canonical real `Eval` function.  This starts from
`SequenceFunction(H,K,S,F;M)` itself; the only supplied hash is `MD[h]`. -/
def sequenceFunctionICEval {Block : Type u} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) : HashOutput L :=
  sequenceFunction b (mdHash model.codec h model.iv) K.1 S fSeqMac M

/-- Typed real coins: the public ideal compression function and all user keys. -/
abbrev SequenceFunctionICRealCoins (Block : Type u) (L : U128) (users : ℕ) :=
  RealCoins (HashOutput L) Block (Fin users) SequenceMACKey

/-- Typed ideal coins: the same public compression/key types and independent
per-user ideal evaluation functions. -/
abbrev SequenceFunctionICIdealCoins (Block : Type u) (L : U128) (users : ℕ) :=
  IdealCoins (HashOutput L) Block (Fin users) SequenceMACKey
    InputSequence (HashOutput L)

noncomputable def sequenceFunctionICRealP {Block : Type u} {L : U128}
    [Fintype Block] (users : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    Dist.ProbDist (SequenceFunctionICRealCoins Block L users) :=
  realP keysP

def sequenceFunctionICRealF {Block : Type u} {L : U128} {users : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) :
    PFunPDS.RV (SequenceFunctionICRealCoins Block L users)
      (SequenceFunctionICQuery Block L users) (SequenceFunctionICReply L) :=
  realF (sequenceFunctionICEval model b S)

noncomputable def sequenceFunctionICReal {Block : Type u} {L : U128}
    [Fintype Block] (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (users : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    ProbPDS (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) :=
  real keysP (sequenceFunctionICEval model b S)

noncomputable def sequenceFunctionICIdealP {Block : Type u} {L : U128}
    [Fintype Block] (users : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    Dist.ProbDist (SequenceFunctionICIdealCoins Block L users) :=
  idealP keysP

def sequenceFunctionICIdealF {Block : Type u} {L : U128} {users : ℕ} :
    PFunPDS.RV (SequenceFunctionICIdealCoins Block L users)
      (SequenceFunctionICQuery Block L users) (SequenceFunctionICReply L) :=
  idealF

noncomputable def sequenceFunctionICIdeal {Block : Type u} {L : U128}
    [Fintype Block] (users : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    ProbPDS (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) :=
  ideal keysP

theorem sequenceFunctionICReal_KStepTotal {Block : Type u} {L : U128}
    [Fintype Block] (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (users n : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    (sequenceFunctionICReal model b S users keysP).KStepTotal n :=
  real_KStepTotal keysP (sequenceFunctionICEval model b S) n

theorem sequenceFunctionICIdeal_KStepTotal {Block : Type u} {L : U128}
    [Fintype Block] (users n : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).KStepTotal n :=
  ideal_KStepTotal keysP n

/-- The canonical real shared-compression world is total on every nonempty
history in its support. -/
theorem sequenceFunctionICReal_totalOnNonempty
    {Block : Type u} {L : U128} [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (users : ℕ)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    CondEquiv.TotalOnNonempty
      (sequenceFunctionICReal model b S users keysP).val := by
  unfold sequenceFunctionICReal
  exact functionEvaluatorProb_totalOnNonempty _ _

/-- The canonical ideal shared-compression world is total on every nonempty
history in its support. -/
theorem sequenceFunctionICIdeal_totalOnNonempty
    {Block : Type u} {L : U128} [Fintype Block]
    (users : ℕ) (keysP : Dist.ProbDist (Fin users → SequenceMACKey)) :
    CondEquiv.TotalOnNonempty
      (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP).val := by
  unfold sequenceFunctionICIdeal
  exact functionEvaluatorProb_totalOnNonempty _ _

/-! ## Budget and reveal carriers for dispatch 2 -/

/-- SequenceFunction specialization of the generic tagged transcript filter. -/
def SequenceFunctionTaggedBudgetRespects {Block : Type u} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) (p q lambda users : ℕ) :
    TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q) → Prop :=
  TaggedBudgetRespects p q lambda (sequenceFunctionEvalCost model b S)

/-- Finite reveal carrier shared by the real and ideal extensions.  Its `q`
traces correspond to the permitted `Eval` calls and each trace is padded to
`lambda` compression entries. -/
abbrev SequenceFunctionICReveal (Role : Type*) (Block : Type u) (L : U128)
    (users q lambda : ℕ) :=
  Reveal (Fin users) SequenceMACKey Role (HashOutput L) Block q lambda

/-- Real representative reveal-map type. -/
abbrev SequenceFunctionICRealRevealMap (Role : Type*) (Block : Type u)
    (L : U128) (users p q lambda : ℕ) :=
  RevealMap (SequenceFunctionICRealCoins Block L users)
    (Fin users) SequenceMACKey Role (HashOutput L) Block InputSequence
    (HashOutput L) (p + q) q lambda

/-- Ideal representative reveal-map type. -/
abbrev SequenceFunctionICIdealRevealMap (Role : Type*) (Block : Type u)
    (L : U128) (users p q lambda : ℕ) :=
  RevealMap (SequenceFunctionICIdealCoins Block L users)
    (Fin users) SequenceMACKey Role (HashOutput L) Block InputSequence
    (HashOutput L) (p + q) q lambda

end RandomSystemsModel
end SequenceHash
