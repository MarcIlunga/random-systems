/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CBCMAC
import RandomSystems.FilterDomNormalization
import RandomSystemsCC.CBCModel

/-!
# CBC-MAC as a randomness expander (CR18 §6.2.3, Theorem 6.1)

The objects and final construction theorem live here.  The formalization setup
(interface alignment and carrier instances) lives in `RandomSystemsCC.CBCModel` and
never appears in the paper-facing argument below.

Objects are pure PDS / converters: `R = U(X,X)` and `Vₙ : M → X` are
`PFunPDS.URF`; the ideal is the total-block-restricted `θ_r ∙ Vₙ`.
-/

namespace RandomSystemsCC.CBCMAC

open RandomSystems
open CR18
open CR18.TypedResource
open scoped RandomSystemsCC.CR18 CR18 CR18.CondEquiv

universe u

/-- `|X|` — the cardinality `Fintype.card X`, coercing into the ambient number
type (here `ℝ`) so the bound reads `r² / (2|X|)`. -/
local notation:max "|" X "|" => Fintype.card X

section

variable {X M : Type u}
variable [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
variable [Fintype M] [DecidableEq M]

-- The fixed scheme: a block-former `bf`.  Its block bound (needed to prove CBC
-- is a DDC) is *free* for the finite message space of Theorem 6.1, so it is
-- discharged inside `Converter.cbc` rather than threaded as a hypothesis.
variable (bf : M -> List X)

/-! ## Objects

`R = U(X,X)` the uniform round function and `Vₙ : M → X` the ideal VIL random
function — both the pure PDS `PFunPDS.URF`. -/

/-- `R = U(X,X)`, the uniform round function. -/
noncomputable abbrev R : PFunPDS.Prob X X :=
  ⟨PFunPDS.URF, PFunPDS.URF_isProbDist⟩

/-- `P = P(X,X)`, the uniform random permutation. -/
noncomputable abbrev P : PFunPDS.Prob X X :=
  ⟨PFunPDS.URP X, PFunPDS.URP_isProbDist X⟩

/-- `Vₙ : M → X`, the ideal variable-input-length random function. -/
noncomputable abbrev Vₙ : PFunPDS.Prob M X :=
  ⟨Vn, Vn_isProbDist⟩

/-- The CBC converter. -/
noncomputable abbrev CBC :=
  Converter.cbc bf

/-- The restriction converter `θ_r` (CR18 §6.2.3): bounds by `r` the *total
number of blocks* — it forwards messages and only *counts* blocks via the
fixed block-former. -/
noncomputable abbrev θ (r : Nat) :=
  Converter.θ bf r

/-- The round-function query filter, written `[r]` as in the paper. -/
noncomputable abbrev roundLimit (r : Nat) :=
  Converter.roundLimit (X := X) r

local notation (priority := 1100) "[" r "]" =>
  roundLimit (X := X) r

/-! ## The final theorem -/

/-- **CBC-MAC is a randomness expander** (CR18 Theorem 6.1): `θ_r · CBC · [r]`
over the uniform round function `R` constructs the restricted VIL random
function `θ_r • Vₙ`, within `½·r² / |X|`. -/
theorem cbc_randomness_expander [Nontrivial M] (r : Nat)
    (prefixFree : PrefixFree bf) :
    (R (X := X) : Resource X M)
      —[θ bf r * (CBC bf * [r]); (r : ℝ) ^ 2 / (2 * |X|)]→
        θ bf r * liftVIF (Vₙ (X := X) (M := M)) := by
  let θr {Y : Type u} := (Converter.restriction (Y := Y) bf r).run
  rw [← Converter.theta_cbc_eq_theta_cbc_round_limit]
  cr18_construct
  rw [Converter.cbc_URF_eq_cbcReal]
  show Δ(θr ∙ cbcReal bf, θr ∙ Vn) ≤ (r : ℝ) ^ 2 / (2 * |X|)
  let R : RandomSystems.Dist (X → X) :=
    RandomSystems.Dist.uniform (X → X)
  let state : (X → X) → List X → X :=
    fun f blocks => blocks.foldl (fun y block => f (y + block)) 0
  let input : (X → X) → List X → ℕ → X :=
    fun f blocks j => state f (blocks.take j) + blocks.getD j 0
  let A : (X → X) → List M → Prop :=
    fun f messages =>
      ∃ m ∈ messages, ∃ m' ∈ messages,
        ∃ j < (bf m).length, ∃ j' < (bf m').length,
          (bf m).take (j + 1) ≠ (bf m').take (j' + 1) ∧
            input f (bf m) j = input f (bf m') j'
  let ĈBC : PFunPDS M (X × Bool) :=
    RandomSystems.Dist.fTransform
      (fun f =>
        PFunDDS.historyEvaluator fun messages h =>
          (state f (bf (messages.getLast h)), decide (A f messages)))
      R
  have conditional_equivalence : ĈBC |≡ Vn :=
    cbc_condEquiv bf prefixFree
  calc
    -- **MBO strip** — `CBC R` is `ĈBC R` with its MBO ignored:
    Δ(θr ∙ cbcReal bf, θr ∙ Vn) =
        Δ(θr ∙ PFunPDS.ignoreMBO ĈBC, θr ∙ Vn) := by
      rw [← cbcGame_ignoreMBO bf]
      rfl
    -- **CR18 Theorem 4.17** — `ĈBC R |≡ Vₙ` bounds the restricted advantage by
    -- the blinded winning probability of `θr ĈBC R`:
    _ ≤ (Γᵇ (θr ∙ ĈBC) : ℝ) := by
      exact theta_advantage_le_blind_game_of_cond_equiv
        bf r (cbcGame bf) Vn conditional_equivalence
    -- **CR18 Lemma 4.18** — the blinded collision game has birthday mass:
    _ ≤ (r : ℝ) ^ 2 / (2 * |X|) := by
      change (Γᵇ (θr ∙ cbcGame bf) : ℝ) ≤ _
      have collision :
          (Γᵇ (θr ∙ cbcGame bf) : ℝ) ≤
            (pairCollisionUnionBound X r : ℝ) := by
        exact_mod_cast blindMaxWinProb_theta_cbcGame_le bf r
      exact collision.trans
        ((pairCollisionUnionBound_le_birthday X r).trans_eq (by ring))

/-! ## The two-hop composite: CBC over a URP

Theorem 6.1 composes in AC's ε-calculus because every deterministic discrete
converter acts non-expandingly on the strict carrier
(`Constructs.eball_trans` applies with no compatibility certificate).  The
second leg is the URP–URF switching lemma (CR18 Lemma 4.19) as a
construction.  The composite's radius is literally the sum of the two legs'
radii, and its proof is converter algebra only — every transcript and
probability fact lives inside the two named legs. -/

omit [AddCommGroup X] [Fintype M] [DecidableEq M] in
/-- **The switching lemma as a construction** (CR18 Lemma 4.19): the round
limit `[r]` over the uniform random permutation `P` constructs the
round-limited uniform round function `[r] · R`, within the birthday bound. -/
theorem urp_constructs_round_limited_urf (r : Nat) :
    (P (X := X) : Resource X M)
      —[[r]; (r : ℝ) ^ 2 / (2 * |X|)]→
        [r] * (R (X := X) : Resource X M) := by
  apply DDConverter.constructs_apply_liftProb_of_advantage
  rw [Converter.roundLimit_apply, Converter.roundLimit_apply]
  rw [maxAdvantage_comm
    ((PFunPDS.isProbDist_filterQueries_iff r _).2 (PFunPDS.URP_isProbDist X))
    ((PFunPDS.isProbDist_filterQueries_iff r _).2 PFunPDS.URF_isProbDist)]
  exact (urf_urp_switching X r).trans_eq (by ring)

/-- Theorem 6.1 with its round limit shifted onto the assumed resource: over
the round-limited round function, `θ_r · CBC` constructs the restricted VIL
random function.  Derived from `cbc_randomness_expander` by converter
algebra alone — CR18 equation (6.1) read as an action law. -/
theorem round_limited_cbc_randomness_expander [Nontrivial M] (r : Nat)
    (prefixFree : PrefixFree bf) :
    ([r] * (R (X := X) : Resource X M))
      —[θ bf r * CBC bf; (r : ℝ) ^ 2 / (2 * |X|)]→
        θ bf r * liftVIF (Vₙ (X := X) (M := M)) := by
  refine (AbstractCrypto.constructs_singleton_eball_iff).mpr ?_
  refine le_trans (le_of_eq ?_)
    ((AbstractCrypto.constructs_singleton_eball_iff).mp
      (cbc_randomness_expander bf r prefixFree))
  congr 1
  simp only [converter_mul_liftProb, protocolOf_liftConverter_smul_liftProb]
  congr 1
  apply Subtype.ext
  simp only [PFunPDS.Prob.applyConverter, DDConverter.apply_mul]

/-- **CBC-MAC over a uniform random permutation is a randomness expander** —
the two-hop composite, assembled purely in AC's ε-composition calculus:
`Constructs.eball_trans` chains the switching construction with Theorem 6.1
and the radii add.  No transcript or probability reasoning occurs below;
the probability facts live in the two named legs. -/
theorem cbc_urp_randomness_expander [Nontrivial M] (r : Nat)
    (prefixFree : PrefixFree bf) :
    (P (X := X) : Resource X M)
      —[θ bf r * (CBC bf * [r]);
          (r : ℝ) ^ 2 / (2 * |X|) + (r : ℝ) ^ 2 / (2 * |X|)]→
        θ bf r * liftVIF (Vₙ (X := X) (M := M)) := by
  have composed :=
    AbstractCrypto.Constructs.eball_trans
      (urp_constructs_round_limited_urf (M := M) r)
      (round_limited_cbc_randomness_expander bf r prefixFree)
  refine (AbstractCrypto.constructs_singleton_eball_iff).mpr ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_trans (le_of_eq ?_)
    ((AbstractCrypto.constructs_singleton_eball_iff).mp composed)
  congr 1
  rw [mul_smul]
  simp only [protocolOf_liftConverter_smul_liftProb]
  congr 1
  apply Subtype.ext
  simp only [PFunPDS.Prob.applyConverter, DDConverter.apply_mul]

end

end RandomSystemsCC.CBCMAC
