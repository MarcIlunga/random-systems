import SequenceHash.RandomSystems.MDHash
import SequenceHash.RandomSystems.Finite
import RandomSystems.HTechnique.SecurityDefs

/-!
# SequenceMAC PRF security — R2 GOAL (Gaži 2014)

This file holds the R2 **goal theorem** `sequenceMAC_prf_bound` — the guardrail —
frozen from the S2 pen-and-paper sketch (PLAN §4 A2).

The compression system `compSystem` is the real uniform-key function-evaluator
law. The remaining construction-specific systems (`sequenceMACSystem`,
`framedNMACSystem`) and bound terms (`epsKS`, `omegaS`) are scaffolding stubs
for the next object task. Only the GOAL statement is the frozen contract. The
five-term bound is Gaži Theorem 1
(`ε_ad + (ℓ+1)q·ε_na + q²/N`) plus the key-derivation term `ε_KS` plus the
long-customization derivation-overlap term `δ_S`.

NOTE: SequenceMAC's key derivation is *better* than HMAC — a single `Derive(K)`
processed from two distinct domain-separated run-ups (`HeaderI`/`HeaderO`) gives
independently-keyed inner/outer hashes under ordinary (data-input) PRF security
of the compression, with **no** related-key assumption; so `ε_KS` is an
ordinary-PRF cost, not an HMAC→NMAC RKA loss. R2 is proved by classical
game-hop/hybrid reductions, **not** the H-technique (that is R4).
-/

noncomputable section

open scoped BigOperators NNReal RandomSystems.CR18

namespace SequenceHash.MACPRF

open RandomSystems RandomSystems.CR18 RandomSystems.HTechnique
open RandomSystems.HTechnique.SecurityDefs

variable {B C : Type*}
  [Fintype B] [Nonempty B] [DecidableEq B]
  [Fintype C] [Nonempty C] [DecidableEq C]
variable {q : ℕ}
variable [FiniteTranscriptSpace InputSequence C q]
variable [FiniteTranscriptSpace B C q]

/-- Keyed MD compression `f : C → B → C` as a law-level system: sample
the chaining-input key uniformly and expose the resulting function evaluator. -/
def compSystem (f : C → B → C) : ProbPDS B C :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform C, Dist.uniform_isProbDist⟩ (fun k m => f k m)

/-- `SequenceMAC_{f,S}` as a law-level PRF over item sequences. Its output is a
full compression digest, so the codomain is the chaining/digest type `C` (the
same `C` the shared `f` outputs). -/
def sequenceMACSystem (codec : MDCodec B) (iv : C) (L : U128)
    (digestBytes : C ↪ HashOutput L) (b : BlockSize) (κ : ℕ)
    (hκU128 : κ < u128Modulus) (S : ByteString) (f : C → B → C) :
    ProbPDS InputSequence C :=
  let Key := {K : ByteString // K.val.length = κ}
  let key₀ : Key :=
    ⟨⟨List.replicate κ 0, by simpa using hκU128⟩, by simp⟩
  letI : Nonempty Key := ⟨key₀⟩
  let H : FixedHash L := fun x => digestBytes (mdHash codec f iv x)
  let F : U128 := ⟨1, by norm_num [u128Modulus]⟩
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform Key, Dist.uniform_isProbDist⟩ fun K M =>
      let K' := derive K.val.val H b
      let S' := derive S.val H b
      let inner := mdHash codec f iv
        (headerI b F K.val ++ K' ++ encodeItems M)
      mdHash codec f iv
        (headerO b F S K.val ++ S' ++ K' ++
          encodeMSBF ⟨M.val.length, M.property⟩ ++ encodeMSBF L ++
          (digestBytes inner).val)

/-- Framed NMAC with independent uniform inner and outer chaining keys.

The codec supplies the complete native-padding block strings for both the
inner item encoding and the outer framing.  In particular, the outer path is
an `mdIterate` over every block of the framed tag, not an implicit one-call
compression shortcut. -/
def framedNMACSystem (codec : MDCodec B) (iv : C) (L : U128)
    (digestBytes : C ↪ HashOutput L) (b : BlockSize) (S : ByteString)
    (f : C → B → C) : ProbPDS InputSequence C :=
  PFunPDS.Prob.functionEvaluator
    (Dist.prodProbDist
      (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C)
      (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C))
    fun keys M =>
      let inner := mdIterate f keys.1 (codec.blockify (encodeItems M))
      let outerTag :=
        encodeMSBF ⟨M.val.length, M.property⟩ ++ encodeMSBF L ++
          (digestBytes inner).val
      mdIterate f keys.2 (codec.blockify outerTag)

/-- Key-derivation term `ε_KS` — the PDS distinguishing advantage between the
actual single-key system and the independent-key framed system (NOT a game
probability). Codex (P2.sys) defines it as `Adv[q]` between the two systems. -/
def epsKS (codec : MDCodec B) (iv : C) (L : U128) (digestBytes : C ↪ HashOutput L)
    (b : BlockSize) (κ : ℕ) (hκU128 : κ < u128Modulus) (S : ByteString)
    (f : C → B → C) : ℝ :=
  Adv (q := q)
    (sequenceMACSystem codec iv L digestBytes b κ hκU128 S f)
    (framedNMACSystem codec iv L digestBytes b S f)

/-- Long-customization raw-derivation overlap `ω_S(q)` — a PDS bad-event
advantage. Stub — Codex (P2.long). -/
def omegaS (codec : MDCodec B) (iv : C) (L : U128) (digestBytes : C ↪ HashOutput L)
    (b : BlockSize) (κ : ℕ) (hκU128 : κ < u128Modulus) (S : ByteString)
    (f : C → B → C) (q : ℕ) : ℝ := sorry

/-- **GOAL (R2).** SequenceMAC over `MD[f]`, with `f` a keyed compression
function secure as a (non)adaptive PRF, is a PRF. The bound is Gaži Theorem 1
plus the key-derivation term `ε_KS` plus the long-customization term `δ_S`
(`0` when `|S| ≤ b`, `ω_S(q)` otherwise). `ℓ` bounds the inner block length;
`N = |C|`. -/
-- GUARDRAIL (R2 goal)
theorem sequenceMAC_prf_bound
    (codec : MDCodec B) (iv : C) (L : U128) (digestBytes : C ↪ HashOutput L)
    (b : BlockSize) (κ : ℕ) (hκ : 32 ≤ κ) (hκU128 : κ < u128Modulus) (ℓ : ℕ)
    (S : ByteString) (f : C → B → C) :
    advPRF (q := q) (sequenceMACSystem codec iv L digestBytes b κ hκU128 S f)
      ≤ epsKS (q := q) codec iv L digestBytes b κ hκU128 S f
        + advPRF (q := q) (compSystem f)
        + (((ℓ + 1) * q : ℕ) : ℝ) * advNPRF (q := q) (compSystem f)
        + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ)
        + (if S.val.length ≤ b.val then 0
            else omegaS codec iv L digestBytes b κ hκU128 S f q) := by
  sorry

end SequenceHash.MACPRF
