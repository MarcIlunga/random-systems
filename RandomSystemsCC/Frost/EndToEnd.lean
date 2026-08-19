/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Frost.Model
import RandomSystemsCC.Frost.Instantiation

/-!
# The concrete FROST security theorem at the threshold structure

FROST over the concrete typed random-systems carrier of
`RandomSystemsCC.Frost.Model`, secure against every set of at most
`t = τ - 1` dishonest parties — assembled **modularly**, the way CC
intends: the fixed carrier data is bundled once into a `Setup`, each
stage's cryptographic content is a named leaf predicate, the two stage
constructions are reusable lemmas, and the end-to-end theorem is their
composition.

The pipeline (per tolerated dishonest set `Z`) is

```text
NET  —[dkg]→  KEYS∗Z      (Setup.dkgStage, from a DkgLeaf)
KEYS∗Z —[sign]→ TSS∗Z     (Setup.signStage, from a SignLeaf)
────────────────────────  compose (Constructs.eball_trans, inside frost_instantiated)
NET  —[sign·dkg]→ TSS∗Z   within εDkg + εSign
```

and the ideal's unforgeability (`GameLeaf`) transfers along the
class metric to the real system.  There is **no honest-majority
requirement**: the `[NET, BC, RO]` resources are assumed, so LiuMau20's
broadcast regime (`Q³`) is not needed.
-/

namespace RandomSystemsCC.Frost

open AbstractCrypto
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped ENNReal Pointwise

/-- The concrete FROST carrier: the typed random-systems resources over the
FROST signature universe with `n` parties and quorum `τ`. -/
abbrev Carrier (F V Msg SId RoIn : Type) (n τ : ℕ) :=
  TypedFinite.Phi (Fin n) (signatures F V Msg SId RoIn n τ)

/-- The concrete FROST protocol type. -/
abbrev Proto (F V Msg SId RoIn : Type) (n τ : ℕ) :=
  TypedFinite.Protocol (Fin n) (signatures F V Msg SId RoIn n τ)

variable {F V Msg SId RoIn : Type} {n τ : ℕ}

/-- The fixed data of a concrete FROST deployment, bundled once so the
security theorems take a single `Setup` rather than a dozen repeated
carrier arguments.  It carries **no** cryptographic content — only the
protocols, the three resources, the feasible distinguisher class with its
comparison to the operational metric, and the base forgery-test family.
The per-stage security assumptions are the separate leaf predicates
below. -/
structure Setup (F V Msg SId RoIn : Type) (n τ : ℕ) where
  /-- The DKG protocol (Komlo–Goldberg round 1–2). -/
  dkg : Proto F V Msg SId RoIn n τ
  /-- The two-round signing protocol (RFC 9591 §5). -/
  sign : Proto F V Msg SId RoIn n τ
  /-- The assumed `[NET, BC, RO, COIN]` specification, per dishonest set. -/
  net : Set (Fin n) → Set (Carrier F V Msg SId RoIn n τ)
  /-- The intermediate uniform-key ideal. -/
  keys : Carrier F V Msg SId RoIn n τ
  /-- The final gated-real-signer ideal. -/
  tss : Carrier F V Msg SId RoIn n τ
  /-- The feasible distinguisher class. -/
  dist : DistinguisherClass (Proto F V Msg SId RoIn n τ)
    (Carrier F V Msg SId RoIn n τ)
  /-- The class metric is bounded by the operational metric (equality on
  the carrier); the feasible-class receipt. -/
  distLe : ∀ l r : Carrier F V Msg SId RoIn n τ, dist.edistD l r ≤ edist l r
  /-- The base forgery-test family per dishonest set. -/
  baseTests : Set (Fin n) → Set (Carrier F V Msg SId RoIn n τ → ℝ≥0∞)
  /-- The dishonest closure of the base tests is admitted by the class. -/
  baseTestsAdmitted : ∀ Z,
    dishonestClosure (M := Proto F V Msg SId RoIn n τ) tupleGamma Z
      (baseTests Z) ⊆ dist.tests

namespace Setup

variable (S : Setup F V Msg SId RoIn n τ)

/-- The forgery-test family at dishonest set `Z`: the dishonest-side
closure of the base tests, whose `Z`-closure is automatic. -/
abbrev tests (Z : Set (Fin n)) : Set (Carrier F V Msg SId RoIn n τ → ℝ≥0∞) :=
  dishonestClosure (M := Proto F V Msg SId RoIn n τ) tupleGamma Z (S.baseTests Z)

/-! ### The three cryptographic leaves -/

/-- **DKG leaf**: over the tolerated sets, the DKG protocol run at the
honest interfaces turns every assumed resource into a dishonest-side
converter applied to the key ideal, up to statistical distance `εDkg`
(random-oracle programming; `εDkg = 0` with the bias-absorbing key
ideal). -/
def DkgLeaf (t : ℕ) (εDkg : ℝ≥0∞) : Prop :=
  ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ S.net Z,
    ∃ s ∈ zSub (M := Proto F V Msg SId RoIn n τ) tupleGamma Z,
      edist (patternAttach Zᶜ S.dkg • R) (s • S.keys) ≤ εDkg

/-- **Signing leaf**: over the tolerated sets, the signing protocol turns
every `∗Z`-relaxed key resource into a dishonest-side converter applied to
the threshold-signature ideal, up to statistical distance `εSign` (the
gated ideal's transcripts are real-shaped). -/
def SignLeaf (t : ℕ) (εSign : ℝ≥0∞) : Prop :=
  ∀ Z ∈ (AdversaryStructure.threshold n t).sets,
    ∀ R ∈ zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.keys},
      ∃ s ∈ zSub (M := Proto F V Msg SId RoIn n τ) tupleGamma Z,
        edist (patternAttach Zᶜ S.sign • R) (s • S.tss) ≤ εSign

/-- **Game leaf**: the ideal signer meets the unforgeability bound `εGame`
against every admitted forgery test — the single computational obligation,
discharged in `RandomSystemsCC.Frost.Reduction` from AOMDL. -/
def GameLeaf (t : ℕ) (εGame : ℝ≥0∞) : Prop :=
  ∀ Z ∈ (AdversaryStructure.threshold n t).sets,
    S.tss ∈ gameSpec (S.tests Z) εGame

/-! ### The two stage constructions (reusable) -/

/-- **Stage 1 — DKG**: from the DKG leaf, for each tolerated `Z` the
protocol constructs the `∗Z`-relaxed key ideal from the `∗Z`-relaxed
assumed specification, within `εDkg`.  A direct instance of the abstract
`constructs_zStar_eps_of_leaf`. -/
theorem dkgStage {t : ℕ} {εDkg : ℝ≥0∞} (h : S.DkgLeaf t εDkg)
    {Z : Set (Fin n)} (hZ : Z ∈ (AdversaryStructure.threshold n t).sets) :
    patternAttach Zᶜ S.dkg •
        zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z (S.net Z) ⊆
      Relaxation.eball εDkg
        (zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.keys}) :=
  constructs_zStar_eps_of_leaf S.dkg (h Z hZ)

/-- **Stage 2 — signing**: from the signing leaf, for each tolerated `Z`
the protocol constructs the `∗Z`-relaxed signature ideal from the
`∗Z`-relaxed key ideal, within `εSign`. -/
theorem signStage {t : ℕ} {εSign : ℝ≥0∞} (h : S.SignLeaf t εSign)
    {Z : Set (Fin n)} (hZ : Z ∈ (AdversaryStructure.threshold n t).sets) :
    patternAttach Zᶜ S.sign •
        zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.keys} ⊆
      Relaxation.eball εSign
        (zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.tss}) := by
  have hstage := constructs_zStar_eps_of_leaf S.sign (h Z hZ)
  rwa [zStar_idem (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.keys}]
    at hstage

/-! ### The end-to-end security theorem -/

/-- **FROST security at the threshold structure.**  The three named leaves
compose: for every set `Z` of at most `t = τ - 1` dishonest parties, the
composed protocol lands within `εDkg + εSign` of the `∗Z`-relaxed gated
ideal, and the real resource meets the unforgeability bound
`εGame + (εDkg + εSign)`.  The assembly is a single application of the
abstract two-stage theorem to this `Setup`'s data and leaves. -/
theorem secure {t : ℕ} {εDkg εSign εGame : ℝ≥0∞}
    (hdkg : S.DkgLeaf t εDkg) (hsign : S.SignLeaf t εSign)
    (hgame : S.GameLeaf t εGame) :
    ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ S.net Z,
      patternAttach Zᶜ (S.sign * S.dkg) • R ∈
          Relaxation.eball (εDkg + εSign)
            (zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.tss})
      ∧ patternAttach Zᶜ (S.sign * S.dkg) • R ∈
          gameSpec (S.tests Z) (εGame + (εDkg + εSign)) :=
  frost_instantiated (AdversaryStructure.threshold n t) S.dkg S.sign S.net
    S.keys S.tss S.dist S.distLe S.tests εDkg εSign εGame
    (fun Z => S.baseTestsAdmitted Z) hdkg hsign
    (fun Z _ => zClosed_dishonestClosure (M := Proto F V Msg SId RoIn n τ)
      tupleGamma (S.baseTests Z))
    hgame

/-- **Availability is the honest `Z = ∅` case.**  With no dishonest party
the merged class is trivial, so the honestly-run protocol lands within
`εDkg + εSign` of the *exact* ideal (`zStar tupleGamma ∅ {tss} = {tss}`) —
correctness of the full honest path.  `∅` is tolerated for every `t`. -/
theorem available {t : ℕ} {εDkg εSign εGame : ℝ≥0∞}
    (hdkg : S.DkgLeaf t εDkg) (hsign : S.SignLeaf t εSign)
    (hgame : S.GameLeaf t εGame)
    {R : Carrier F V Msg SId RoIn n τ} (hR : R ∈ S.net ∅) :
    patternAttach (∅ : Set (Fin n))ᶜ (S.sign * S.dkg) • R ∈
      Relaxation.eball (εDkg + εSign)
        (zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma ∅ {S.tss}) :=
  (S.secure hdkg hsign hgame ∅
    (by show (∅ : Set (Fin n)).ncard ≤ t; rw [Set.ncard_empty]; exact Nat.zero_le t)
    R hR).1

end Setup

end RandomSystemsCC.Frost
