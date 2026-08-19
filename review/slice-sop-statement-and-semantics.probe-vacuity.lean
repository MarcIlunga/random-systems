import RandomSystems.SumOfPermutationsTight
import RandomSystems.SumOfPermutations

/-!  ADVERSARIAL REVIEW PROBE (review-only; not part of the library).

Does the *statement* of `sop_randomness_expander_tight` certify any improvement over the
birthday bound?  Below we prove the SAME statement using only the OLD birthday argument
(`RandomSystems.SumOfPermutations`), capped at 1.  It compiles axiom-clean, so the
"strictly better than birthday" conjunct does NOT exclude restating the birthday bound.

Run with:  lake env lean review/slice-sop-statement-and-semantics.probe-vacuity.lean
-/

noncomputable section
namespace ReviewProbe
open RandomSystems (Dist)
open RandomSystems.CR18
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

universe u

/-- The *birthday* bound, capped at 1. -/
def birthdayEps (N q : ℕ) : ℝ := min 1 ((1/2 : ℝ) * (q : ℝ) ^ 2 / (N : ℝ))

theorem sop_birthday_half {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G]
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

/-- `SoPTight.sopReal` / `sopIdeal` are the *same objects* as `SoP.sopReal` / `SoP.sopIdeal`. -/
theorem tight_real_eq {G : Type u} [Fintype G] [DecidableEq G] [AddCommGroup G] :
    SoPTight.sopReal (G := G) = SoP.sopReal (G := G) := rfl

theorem tight_ideal_eq {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] :
    SoPTight.sopIdeal (G := G) = SoP.sopIdeal (G := G) := rfl

/-- **The probe.**  Verbatim the statement of `sop_randomness_expander_tight`,
proved from the birthday bound alone. -/
theorem sop_randomness_expander_tight_FROM_BIRTHDAY :
    ∃ ε : ℕ → ℕ → ℝ,
      (∀ (H : Type u) [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H] (q : ℕ),
          Δ(⌈q⌉ (SoPTight.sopReal (G := H)), ⌈q⌉ (SoPTight.sopIdeal (G := H)))
            ≤ ε (Fintype.card H) q) ∧
      (∀ N q : ℕ, 1 < q → q < N → ε N q < (q : ℝ) ^ 2 / (N : ℝ)) := by
  refine ⟨birthdayEps, ?_, ?_⟩
  · intro H _ _ _ _ q
    rw [tight_real_eq, tight_ideal_eq]
    refine le_min ?_ (sop_birthday_half q)
    exact maxAdvantage_le_one (by cr18_prob; exact SoP.sopReal_isProbDist)
      (by cr18_prob; exact SoP.sopIdeal_isProbDist)
  · intro N q hq hqN
    have hN : (0:ℝ) < N := by
      have : 0 < N := lt_trans (by omega) hqN
      exact_mod_cast this
    have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
    have hx : (0:ℝ) < (1/2 : ℝ) * (q:ℝ)^2 / (N:ℝ) := by positivity
    have : (1/2 : ℝ) * (q:ℝ)^2 / (N:ℝ) < (q:ℝ)^2 / (N:ℝ) := by
      rw [div_lt_div_iff_of_pos_right hN]; nlinarith
    exact lt_of_le_of_lt (min_le_right _ _) this

#print axioms sop_randomness_expander_tight_FROM_BIRTHDAY

end ReviewProbe
