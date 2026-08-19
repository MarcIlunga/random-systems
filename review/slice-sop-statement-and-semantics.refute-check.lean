import RandomSystems.SumOfPermutationsTight
import RandomSystems.SumOfPermutations

/-! REFUTATION-ATTEMPT PROBE (scratch, /tmp).  Two questions:
  (1) is the reviewer's restatement literally the theorem's type?
  (2) does the statement follow from the committed birthday argument WITHOUT the `min 1` cap
      (i.e. without leaning on `maxAdvantage_le_one`)?
-/

noncomputable section
namespace RefuteProbe
open RandomSystems (Dist)
open RandomSystems.CR18
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

universe u

/-- The statement, restated here.  Proved by `exact`-ing the library theorem: if this
typechecks, the restatement is *defeq* to `sop_randomness_expander_tight`'s type. -/
theorem theStatement :
    ∃ ε : ℕ → ℕ → ℝ,
      (∀ (H : Type u) [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H] (q : ℕ),
          Δ(⌈q⌉ (SoPTight.sopReal (G := H)), ⌈q⌉ (SoPTight.sopIdeal (G := H)))
            ≤ ε (Fintype.card H) q) ∧
      (∀ N q : ℕ, 1 < q → q < N → ε N q < (q : ℝ) ^ 2 / (N : ℝ)) :=
  RandomSystems.CR18.SoPTight.sop_randomness_expander_tight

/-- The committed birthday argument, stopped one weakening step earlier than
`SoP.sop_randomness_expander` does (it throws the factor `1/2` away at its last calc step). -/
theorem birthday_half {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G]
    [AddCommGroup G] (q : ℕ) :
    Δ(⌈q⌉ (SoP.sopReal (G := G)), ⌈q⌉ (SoP.sopIdeal (G := G)))
      ≤ (1/2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) := by
  calc Δ(⌈q⌉ (SoP.sopReal (G := G)), ⌈q⌉ (SoP.sopIdeal (G := G)))
      = Δ(⌈q⌉ (SoP.sopIdeal (G := G)), ⌈q⌉ (SoP.sopReal (G := G))) := by
        exact maxAdvantage_comm (by cr18_prob; exact SoP.sopReal_isProbDist)
          (by cr18_prob; exact SoP.sopIdeal_isProbDist)
    _ = Δ(⌈q⌉ PFunPDS.ignoreMBO (SoP.sopGame (G := G)), ⌈q⌉ (SoP.sopReal (G := G))) := by
        rw [SoP.sopGame_ignoreMBO]
    _ ≤ (pairCollisionUnionBound G q : ℝ) :=
        maxAdvantage_filterQueries_seededConditionCGame_le (SoP.sopSeed (G := G))
          SoP.sopMidFunction SoP.sopBad (fun p => seededHashCollision_monotone _ p) q
          SoP.sopReal (pairCollisionUnionBound G q) SoP.sop_condEquiv SoP.sopSeed_isProbDist
          SoP.sopReal_isProbDist SoP.sopReal_totalOnNonempty
          (fun w _ => SoP.mass_sopBad_le (blindQueryList w q) q (blindQueryList_length_le w q))
    _ ≤ (1/2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) :=
        pairCollisionUnionBound_le_birthday G q

/-- The SAME statement (see `theStatement` above for the defeq check), from the birthday
argument with **no cap at all**: `ε N q := q²/(2N)`. -/
theorem theStatement_FROM_BIRTHDAY_UNCAPPED :
    ∃ ε : ℕ → ℕ → ℝ,
      (∀ (H : Type u) [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H] (q : ℕ),
          Δ(⌈q⌉ (SoPTight.sopReal (G := H)), ⌈q⌉ (SoPTight.sopIdeal (G := H)))
            ≤ ε (Fintype.card H) q) ∧
      (∀ N q : ℕ, 1 < q → q < N → ε N q < (q : ℝ) ^ 2 / (N : ℝ)) := by
  refine ⟨fun N q => (1/2 : ℝ) * (q : ℝ) ^ 2 / (N : ℝ), ?_, ?_⟩
  · intro H _ _ _ _ q
    exact birthday_half q
  · intro N q hq hqN
    have hN : (0:ℝ) < N := by
      have : 0 < N := lt_trans (by omega) hqN
      exact_mod_cast this
    have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
    rw [div_lt_div_iff_of_pos_right hN]
    nlinarith

#print axioms theStatement_FROM_BIRTHDAY_UNCAPPED

/-! Subsidiary claim (b): `q < N` is a needless hypothesis — for `N ≤ q` and `1 < q` the
floor `q²/N ≥ 2` is above the cap `1 ≥ sopEps`, so the conjunct holds there too. -/
theorem clause_holds_without_qN (N q : ℕ) (hq : 1 < q) (hN : 0 < N) (hge : N ≤ q) :
    SoPTight.sopEps N q < (q : ℝ) ^ 2 / (N : ℝ) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hgeR : (N:ℝ) ≤ q := by exact_mod_cast hge
  have hcap : SoPTight.sopEps N q ≤ 1 := min_le_left _ _
  have : (1:ℝ) < (q:ℝ)^2 / (N:ℝ) := by
    rw [lt_div_iff₀ hNR, one_mul]
    nlinarith
  linarith

end RefuteProbe
