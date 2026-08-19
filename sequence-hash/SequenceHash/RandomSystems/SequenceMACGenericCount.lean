import SequenceHash.RandomSystems.SequenceMACGeneric

/-!
# SequenceFunction bad-mass decomposition

This module is the statement-first counting layer for the R4 ideal-compression
bound.  It decomposes `Bad_SEQ` into cascade, key, and derivation parts and
then decomposes the cascade part into a primitive hit, a single collision,
and a double-collision graph event.  The probability leaves are deliberately
named propositions: the graph leaf contains the corrected-BPR05 equal-top
merge corner and is not asserted as an axiom.
-/

noncomputable section

open scoped NNReal RandomSystems.CR18

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems
open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique.IdealCompression

universe uBlock

/-! ## Exact event decomposition -/

/-- The first disjunct of `Bad_SEQ`: a construction compression input hits a
visible primitive input. -/
def PrimHit_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  ∃ input,
    input ∈ sequenceFunctionRevealedConstructionInputs tz.2 ∧
    input ∈ sequenceFunctionVisiblePrimInputs tz.1

/-- The second disjunct of `Bad_SEQ`: two construction compression inputs
coincide. -/
def ConstructionCollision_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  ¬ (sequenceFunctionRevealedConstructionInputs tz.2).Nodup

/-- `Bad_SEQ` is exactly primitive-hit or construction-input collision. -/
theorem Bad_SEQ_iff_primHit_or_constructionCollision
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :
    Bad_SEQ tz ↔ PrimHit_SEQ tz ∨ ConstructionCollision_SEQ tz := by
  rfl

/-- Raw-key repetition in the revealed multi-user key vector. -/
def KeyRepeat_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  ∃ i j : Fin users, i ≠ j ∧ tz.2.keys i = tz.2.keys j

/-- The two long-input derivation roles. -/
def SequenceFunctionCompressionRole.IsDerive :
    SequenceFunctionCompressionRole → Prop
  | .deriveKey | .deriveCustomization => True
  | .inner | .outer => False

/-- A derivation-role construction call hits a visible primitive input. -/
def DerivePrimHit_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  ∃ entry ∈ sequenceFunctionRevealedConstructionCalls tz.2,
    entry.role.IsDerive ∧
      entry.input ∈ sequenceFunctionVisiblePrimInputs tz.1

/-- A construction-input collision involving at least one derivation-role
call.  This includes same-derive and cross-role compression-level collisions;
input-level domain separation does not erase either kind of random MD event. -/
def DeriveCollision_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  let calls := sequenceFunctionRevealedConstructionCalls tz.2
  ∃ i j : Fin calls.length,
    i ≠ j ∧ (calls.get i).input = (calls.get j).input ∧
      ((calls.get i).role.IsDerive ∨ (calls.get j).role.IsDerive)

/-- The derivation contribution: a bad compression event with an actual
derivation-role witness. -/
def DeriveBad_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  DerivePrimHit_SEQ tz ∨ DeriveCollision_SEQ tz

/-- The key event currently represented by the information already present
in the generic reveal: raw-key repetition.  The later key leaf must additionally
classify codec-specific secret-bearing primitive guesses before it can be
discharged from `KeyPointMassBound`; keeping that work in the named leaf avoids
inventing a false generic codec theorem. -/
def KeyBad_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  KeyRepeat_SEQ tz

/-- Priority residual after removing key and derivation events.  It contains
exactly the cascade-inherent part of `Bad_SEQ` left for structure-graph
counting. -/
def CascadeBad_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  Bad_SEQ tz ∧ ¬ KeyBad_SEQ tz ∧ ¬ DeriveBad_SEQ tz

/-- Exact three-way cover used by the probability union bound. -/
theorem Bad_SEQ_cover_cascade_key_derive
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :
    Bad_SEQ tz →
      CascadeBad_SEQ tz ∨ KeyBad_SEQ tz ∨ DeriveBad_SEQ tz := by
  intro hbad
  by_cases hkey : KeyBad_SEQ tz
  · exact Or.inr (Or.inl hkey)
  · by_cases hderive : DeriveBad_SEQ tz
    · exact Or.inr (Or.inr hderive)
    · exact Or.inl ⟨hbad, hkey, hderive⟩

/-! ## Single- versus double-collision structure graph -/

/-- A sorted construction-call collision pair.  The second coordinate is the
pair's graph top. -/
def SequenceConstructionCollisionPair
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (pair : Fin (sequenceFunctionRevealedConstructionInputs tz.2).length ×
      Fin (sequenceFunctionRevealedConstructionInputs tz.2).length) : Prop :=
  pair.1.val < pair.2.val ∧
    (sequenceFunctionRevealedConstructionInputs tz.2).get pair.1 =
      (sequenceFunctionRevealedConstructionInputs tz.2).get pair.2

/-- A construction collision exists exactly when there is a sorted collision
pair. -/
theorem ConstructionCollision_SEQ_iff_exists_pair
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :
    ConstructionCollision_SEQ tz ↔
      ∃ pair, SequenceConstructionCollisionPair tz pair := by
  classical
  let inputs := sequenceFunctionRevealedConstructionInputs tz.2
  rw [ConstructionCollision_SEQ, List.nodup_iff_injective_get,
    Function.Injective]
  constructor
  · intro hcollision
    push Not at hcollision
    obtain ⟨i, j, hij, hne⟩ := hcollision
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
    · exact ⟨(i, j), hlt, hij⟩
    · exact ⟨(j, i), hgt, hij.symm⟩
  · rintro ⟨⟨i, j⟩, hlt, hij⟩ hinj
    exact (Fin.ne_of_val_ne (Nat.ne_of_lt hlt)) (hinj hij)

/-- Exactly one sorted construction collision pair: the single-charge
linear collision event. -/
def SingleColl_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  ∃ pair, SequenceConstructionCollisionPair tz pair ∧
    ∀ other, SequenceConstructionCollisionPair tz other → other = pair

/-- At least two sorted construction collision pairs.  Distinct tops admit
the generic double charge; equal tops are the corrected-BPR05 merge corner. -/
def SequenceGraphBad_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  ∃ pair₁ pair₂,
    pair₁ ≠ pair₂ ∧ SequenceConstructionCollisionPair tz pair₁ ∧
      SequenceConstructionCollisionPair tz pair₂

/-- Every construction collision is either the single-charge case or the
double-collision graph case. -/
theorem ConstructionCollision_SEQ_cover_single_graph
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :
    ConstructionCollision_SEQ tz →
      SingleColl_SEQ tz ∨ SequenceGraphBad_SEQ tz := by
  intro hcollision
  obtain ⟨pair, hpair⟩ :=
    (ConstructionCollision_SEQ_iff_exists_pair tz).1 hcollision
  by_cases hunique : ∀ other, SequenceConstructionCollisionPair tz other →
      other = pair
  · exact Or.inl ⟨pair, hpair, hunique⟩
  · push Not at hunique
    obtain ⟨other, hother, hne⟩ := hunique
    exact Or.inr ⟨pair, other, hne.symm, hpair, hother⟩

/-- Cascade primitive-hit leaf. -/
def CascadePrimHit_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  CascadeBad_SEQ tz ∧ PrimHit_SEQ tz

/-- Cascade single-collision leaf. -/
def CascadeSingleColl_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  CascadeBad_SEQ tz ∧ SingleColl_SEQ tz

/-- Cascade double-collision graph leaf. -/
def CascadeGraphBad_SEQ {Block : Type uBlock} {L : U128}
    {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) : Prop :=
  CascadeBad_SEQ tz ∧ SequenceGraphBad_SEQ tz

/-- Exact cascade cover consumed by the three probability leaves. -/
theorem CascadeBad_SEQ_cover_prim_single_graph
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda) :
    CascadeBad_SEQ tz →
      CascadePrimHit_SEQ tz ∨
        CascadeSingleColl_SEQ tz ∨ CascadeGraphBad_SEQ tz := by
  intro hcascade
  rcases (Bad_SEQ_iff_primHit_or_constructionCollision tz).1 hcascade.1 with
    hprim | hcollision
  · exact Or.inl ⟨hcascade, hprim⟩
  · rcases ConstructionCollision_SEQ_cover_single_graph tz hcollision with
      hsingle | hgraph
    · exact Or.inr (Or.inl ⟨hcascade, hsingle⟩)
    · exact Or.inr (Or.inr ⟨hcascade, hgraph⟩)

/-! ## Named probability leaves -/

/-- The ideal extended-transcript law used by every counting leaf. -/
noncomputable abbrev sequenceFunctionICIdealExtension
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (p q lambda : ℕ)
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (E : PFunDDS.DDE (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L)) :=
  extendedTranscriptDistRep (q := p + q)
    (sequenceFunctionICIdealP (Block := Block) (L := L) users keysP)
    sequenceFunctionICIdealF
    (sequenceFunctionICIdealReveal (p := p) (q := q) (lambda := lambda)
      model b S) E

/-- Single-charge primitive-hit leaf. -/
def SequencePrimHitMassBound
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda c : ℕ) : Prop :=
  ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q),
    EnvRespects (SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users) E →
    probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
        (CascadePrimHit_SEQ (p := p) (q := q) (lambda := lambda)) ≤
      (p * q * lambda : NNReal) / (2 : NNReal) ^ c

/-- Single-charge construction-collision leaf. -/
def SequenceSingleCollMassBound
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda c : ℕ) : Prop :=
  ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q),
    EnvRespects (SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users) E →
    probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
        (CascadeSingleColl_SEQ (p := p) (q := q) (lambda := lambda)) ≤
      (Nat.choose q 2 : NNReal) *
        ((lambda + 2 : ℕ) : NNReal) / (2 : NNReal) ^ c

/-- The double-collision graph bound.  The distinct-top part is the generic
two-slice argument; two distinct collision pairs with the same top are the
corrected-BPR05 Lemma-10 corner.  This proposition is the one named residual,
not an axiom or a theorem with a hidden `sorry`. -/
def sequenceGraphBad_equalTop
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda c : ℕ) : Prop :=
  ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q),
    EnvRespects (SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users) E →
    probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
        (CascadeGraphBad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
      (Nat.choose q 2 : NNReal) *
        (64 * lambda ^ 4 : NNReal) / (2 : NNReal) ^ (2 * c)

/-- The key-related leaf, to be discharged from `KeyPointMassBound` after
the codec-specific secret-bearing call sites are exposed. -/
def SequenceKeyMassBound
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda kappaStar : ℕ) : Prop :=
  ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q),
    EnvRespects (SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users) E →
    probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
        (KeyBad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
      B_key p users kappaStar

/-- The long-key/customization derivation leaf. -/
def SequenceDeriveMassBound
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda rK rS c kappaStar : ℕ) : Prop :=
  ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q),
    EnvRespects (SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users) E →
    probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
        (DeriveBad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
      deriveCostGeneric p q users lambda rK rS c kappaStar

/-! ## Probability assembly -/

/-- Assemble the cascade bound from the primitive, single-collision, and
double-collision/equal-top leaves. -/
theorem sequenceCascadeBad_mass_le
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda c : ℕ)
    (h_primHit : SequencePrimHitMassBound model b S keysP p q lambda c)
    (h_singleColl : SequenceSingleCollMassBound model b S keysP p q lambda c)
    (h_equalTop : sequenceGraphBad_equalTop model b S keysP p q lambda c) :
    ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
          (CascadeBad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
        B_cascade p q lambda c := by
  intro E hE
  let D := sequenceFunctionICIdealExtension p q lambda model b S keysP E.1
  calc
    probBad D (CascadeBad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
        probBad D (fun tz =>
          CascadePrimHit_SEQ (p := p) (q := q) (lambda := lambda) tz ∨
          (CascadeSingleColl_SEQ (p := p) (q := q) (lambda := lambda) tz ∨
            CascadeGraphBad_SEQ (p := p) (q := q) (lambda := lambda) tz)) :=
      HTechniqueDerivation.mass_mono D
        (CascadeBad_SEQ_cover_prim_single_graph)
    _ ≤ probBad D
          (CascadePrimHit_SEQ (p := p) (q := q) (lambda := lambda)) +
        (probBad D
            (CascadeSingleColl_SEQ (p := p) (q := q) (lambda := lambda)) +
          probBad D
            (CascadeGraphBad_SEQ (p := p) (q := q) (lambda := lambda))) :=
      (mass_or_le D
        (CascadePrimHit_SEQ (p := p) (q := q) (lambda := lambda))
        (fun tz =>
          CascadeSingleColl_SEQ (p := p) (q := q) (lambda := lambda) tz ∨
          CascadeGraphBad_SEQ (p := p) (q := q) (lambda := lambda) tz)).trans
        (add_le_add_right
          (mass_or_le D
            (CascadeSingleColl_SEQ (p := p) (q := q) (lambda := lambda))
            (CascadeGraphBad_SEQ (p := p) (q := q) (lambda := lambda))) _)
    _ ≤ (p * q * lambda : NNReal) / (2 : NNReal) ^ c +
        ((Nat.choose q 2 : NNReal) *
            ((lambda + 2 : ℕ) : NNReal) / (2 : NNReal) ^ c +
          (Nat.choose q 2 : NNReal) *
            (64 * lambda ^ 4 : NNReal) / (2 : NNReal) ^ (2 * c)) := by
      gcongr
      · exact h_primHit E hE
      · exact h_singleColl E hE
      · exact h_equalTop E hE
    _ = B_cascade p q lambda c := by
      unfold B_cascade
      ring

/-- Assemble the complete `h_badmass` premise from the three event parts. -/
theorem sequenceFunction_badmass_of_subbounds
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda rK rS c kappaStar : ℕ)
    (h_cascade : ∀ E : QQueryEnvironment
      (SequenceFunctionICQuery Block L users) (SequenceFunctionICReply L)
      (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
        (CascadeBad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
          B_cascade p q lambda c)
    (h_key : SequenceKeyMassBound model b S keysP
      p q lambda kappaStar)
    (h_derive : SequenceDeriveMassBound model b S keysP
      p q lambda rK rS c kappaStar) :
    ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
          (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
        B_SEQ p q users lambda rK rS c kappaStar := by
  intro E hE
  let D := sequenceFunctionICIdealExtension p q lambda model b S keysP E.1
  calc
    probBad D (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
        probBad D (fun tz =>
          CascadeBad_SEQ (p := p) (q := q) (lambda := lambda) tz ∨
          (KeyBad_SEQ (p := p) (q := q) (lambda := lambda) tz ∨
            DeriveBad_SEQ (p := p) (q := q) (lambda := lambda) tz)) :=
      HTechniqueDerivation.mass_mono D
        (Bad_SEQ_cover_cascade_key_derive)
    _ ≤ probBad D
          (CascadeBad_SEQ (p := p) (q := q) (lambda := lambda)) +
        (probBad D (KeyBad_SEQ (p := p) (q := q) (lambda := lambda)) +
          probBad D
            (DeriveBad_SEQ (p := p) (q := q) (lambda := lambda))) :=
      (mass_or_le D
        (CascadeBad_SEQ (p := p) (q := q) (lambda := lambda))
        (fun tz =>
          KeyBad_SEQ (p := p) (q := q) (lambda := lambda) tz ∨
          DeriveBad_SEQ (p := p) (q := q) (lambda := lambda) tz)).trans
        (add_le_add_right
          (mass_or_le D
            (KeyBad_SEQ (p := p) (q := q) (lambda := lambda))
            (DeriveBad_SEQ (p := p) (q := q) (lambda := lambda))) _)
    _ ≤ B_cascade p q lambda c +
        (B_key p users kappaStar +
          deriveCostGeneric p q users lambda rK rS c kappaStar) := by
      gcongr
      · exact h_cascade E hE
      · exact h_key E hE
      · exact h_derive E hE
    _ = B_SEQ p q users lambda rK rS c kappaStar := by
      simp [B_SEQ, add_assoc]

/-- The decomposition skeleton reduced all of `h_badmass` to the four named
tractable leaves plus the one named graph corner. -/
theorem sequenceFunction_badmass_of_named_leaves
    {Block : Type uBlock} {L : U128} {users : ℕ}
    [Fintype Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (p q lambda rK rS c kappaStar : ℕ)
    (h_primHit : SequencePrimHitMassBound model b S keysP p q lambda c)
    (h_singleColl : SequenceSingleCollMassBound model b S keysP p q lambda c)
    (h_equalTop : sequenceGraphBad_equalTop model b S keysP p q lambda c)
    (h_key : SequenceKeyMassBound model b S keysP p q lambda kappaStar)
    (h_derive : SequenceDeriveMassBound model b S keysP
      p q lambda rK rS c kappaStar) :
    ∀ E : QQueryEnvironment (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (sequenceFunctionICIdealExtension p q lambda model b S keysP E.1)
          (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
        B_SEQ p q users lambda rK rS c kappaStar := by
  exact sequenceFunction_badmass_of_subbounds model b S keysP
    p q lambda rK rS c kappaStar
    (sequenceCascadeBad_mass_le model b S keysP p q lambda c
      h_primHit h_singleColl h_equalTop)
    h_key h_derive

end RandomSystemsModel
end SequenceHash
