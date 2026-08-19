/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Frost.EndToEnd
import RandomSystems.CR18.AbstractProblem
import RandomSystems.Dist

/-!
# The security reduction: FROST unforgeability from AOMDL

The single computational obligation is the ideal signer's game bound
(`Setup.GameLeaf`).  This module derives it from a reduction to AOMDL and
contains everything about that reduction:

* the generic Problem⟶`gameSpec` bridge (`gameBound_of_reduction`,
  `gameBound_of_problem_reduction`) — links *any* CR18 hardness `Problem`
  to the CC game bound;
* AOMDL as a genuine CR18 `Problem` over distributions (`aomdlProblem`),
  the forking reduction (`reduce`) and its tightness (`reduction_winProb`);
* the AOMDL instantiation of the bridge (`gameBound_of_aomdl`); and
* the `Setup`-level contracts (`AomdlHard`, `AomdlReduction`) and the final
  security theorem (`secure_of_aomdl`).

What stays assumed is only AOMDL hardness (`AomdlHard`) and the reduction
soundness / forking bound (`AomdlReduction` / `ForkingLemma`); the
deterministic core — that extraction never fails, so the reduction is tight
— is proved.
-/

namespace RandomSystemsCC.Frost

open AbstractCrypto
open RandomSystems.CR18 (Problem)
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped ENNReal

/-! ## The generic Problem ⟶ gameSpec bridge -/

/-- **The game leaf from a reduction** (CR18 §4.4.4 performance-upper-bound
transfer, at the game-test functional).  If every admitted test's win
probability against `ideal` is dominated by some solver's advantage up to
`slack`, and that advantage is capped at `εAomdl`, then `ideal` satisfies
the game bound `εAomdl + slack`. -/
theorem gameBound_of_reduction {Ψ Solver : Type*}
    (ideal : Ψ) (tests : Set (Ψ → ℝ≥0∞))
    (adv : Solver → ℝ≥0∞) (εAomdl slack : ℝ≥0∞)
    (hard : ∀ s, adv s ≤ εAomdl)
    (sound : ∀ t ∈ tests, ∃ s, t ideal ≤ adv s + slack) :
    ideal ∈ gameSpec tests (εAomdl + slack) := by
  intro t ht
  obtain ⟨s, hs⟩ := sound t ht
  exact hs.trans (by gcongr; exact hard s)

/-- **The game leaf from *any* CR18 hardness `Problem`** — the generic
Problem⟶`gameSpec` bridge, not specific to AOMDL.  This is
`gameBound_of_reduction` with the abstract advantage functional factored as
"performance of the target `Problem`".  Any assumption phrased as a CR18
`Problem` — DL, CDH, OMDL, AOMDL — plugs in; `gameBound_of_aomdl` below is
one instantiation. -/
theorem gameBound_of_problem_reduction {Ψ P Sol : Type*}
    (prob : Problem P Sol NNReal) (p : P)
    (ideal : Ψ) (tests : Set (Ψ → ℝ≥0∞))
    (ρ : (Ψ → ℝ≥0∞) → Sol) (εHard slack : ℝ≥0∞)
    (hhard : ∀ s, (prob.perf p s : ℝ≥0∞) ≤ εHard)
    (hsound : ∀ t ∈ tests, t ideal ≤ (prob.perf p (ρ t) : ℝ≥0∞) + slack) :
    ideal ∈ gameSpec tests (εHard + slack) :=
  gameBound_of_reduction ideal tests
    (fun s => (prob.perf p s : ℝ≥0∞)) εHard slack hhard
    (fun t ht => ⟨ρ t, hsound t ht⟩)

/-! ## AOMDL as a CR18 problem over distributions, and the forking reduction -/

namespace FrostGroup

variable (G : FrostGroup)

/-- **The forking output**: two accepting Schnorr transcripts against the
challenge `Y`, sharing the commitment `R` but with distinct challenges. -/
structure Fork (Y : G.V) where
  R : G.V
  c : ZMod G.q
  c' : ZMod G.q
  z : ZMod G.q
  z' : ZMod G.q
  accepts : z • G.g = R + c • Y
  accepts' : z' • G.g = R + c' • Y
  distinct : c ≠ c'

/-- **The extractor**: the discrete logarithm from a fork by Schnorr
special soundness, `(c − c')⁻¹ · (z − z')`. -/
def Fork.dlog {Y : G.V} (fk : G.Fork Y) : ZMod G.q :=
  (fk.c - fk.c')⁻¹ * (fk.z - fk.z')

/-- **The extractor never fails**: a fork's `dlog` solves the challenge,
`dlog • g = Y` (`schnorr_extract_dlog`). -/
theorem Fork.dlog_correct {Y : G.V} (fk : G.Fork Y) :
    fk.dlog • G.g = Y :=
  AbstractCrypto.Frost.schnorr_extract_dlog G.g Y fk.R fk.c fk.c' fk.z fk.z'
    fk.accepts fk.accepts' fk.distinct

/-- An AOMDL solver: a distribution over candidate discrete logs. -/
abbrev AomdlSolver : Type := RandomSystems.Dist (Option (ZMod G.q))

/-- The AOMDL winning event at `Y`: the output is a discrete log of `Y`. -/
def AomdlWins (Y : G.V) : Option (ZMod G.q) → Prop
  | some x => x • G.g = Y
  | none => False

/-- **AOMDL as a CR18 `Problem`**: performance is the winning probability
(`Dist.mass` of the winning event) — a proper game with an instantiated
distribution. -/
noncomputable def aomdlProblem : Problem G.V G.AomdlSolver NNReal where
  perf Y solver := solver.mass (G.AomdlWins Y)

@[simp] theorem aomdlProblem_perf (Y : G.V) (solver : G.AomdlSolver) :
    G.aomdlProblem.perf Y solver = solver.mass (G.AomdlWins Y) :=
  rfl

/-- **The reduction's solver map**: apply the extractor to each of a
forger's fork outputs. -/
noncomputable def reduce {Y : G.V}
    (forker : RandomSystems.Dist (Option (G.Fork Y))) : G.AomdlSolver :=
  RandomSystems.Dist.fTransform (fun o => o.map (Fork.dlog G)) forker

/-- **The reduction is tight**: the reduced solver's winning probability
equals the forger's fork-production probability, because extraction never
fails (`Fork.dlog_correct`). -/
theorem reduction_winProb {Y : G.V}
    (forker : RandomSystems.Dist (Option (G.Fork Y))) :
    G.aomdlProblem.perf Y (G.reduce forker) =
      forker.mass (fun o => o.isSome) := by
  rw [aomdlProblem_perf]
  unfold reduce
  rw [RandomSystems.Dist.mass_fTransform]
  refine RandomSystems.Dist.mass_congr forker (fun o => ?_)
  cases o with
  | none => simp [AomdlWins]
  | some fk => simp [AomdlWins, fk.dlog_correct]

/-- **The forking lemma contract** (the sole probabilistic residual): a
forking procedure produces a fork with probability at least `forkBound`. -/
def ForkingLemma {Y : G.V} (forker : RandomSystems.Dist (Option (G.Fork Y)))
    (advForger forkBound : NNReal) : Prop :=
  forkBound ≤ forker.mass (fun o => o.isSome)

/-- Reduction + forking lower bound ⇒ AOMDL performance lower bound. -/
theorem aomdl_perf_ge_of_forking {Y : G.V}
    (forker : RandomSystems.Dist (Option (G.Fork Y)))
    {advForger forkBound : NNReal}
    (hfork : G.ForkingLemma forker advForger forkBound) :
    forkBound ≤ G.aomdlProblem.perf Y (G.reduce forker) := by
  rw [reduction_winProb]; exact hfork

/-- **The `gameSpec` game bound from the concrete AOMDL reduction** — the
generic bridge at `prob := aomdlProblem`, `ρ := reduce ∘ forkerOf`.  AOMDL
is the instance; the bridge is not. -/
theorem gameBound_of_aomdl {Ψ : Type*} (Y : G.V) (ideal : Ψ)
    (tests : Set (Ψ → ℝ≥0∞))
    (forkerOf : (Ψ → ℝ≥0∞) → RandomSystems.Dist (Option (G.Fork Y)))
    (εAomdl slack : ℝ≥0∞)
    (hhard : ∀ sol : G.AomdlSolver,
      (G.aomdlProblem.perf Y sol : ℝ≥0∞) ≤ εAomdl)
    (hsound : ∀ t ∈ tests,
      t ideal ≤ (G.aomdlProblem.perf Y (G.reduce (forkerOf t)) : ℝ≥0∞) + slack) :
    ideal ∈ gameSpec tests (εAomdl + slack) :=
  gameBound_of_problem_reduction G.aomdlProblem Y ideal tests
    (fun t => G.reduce (forkerOf t)) εAomdl slack hhard hsound

/-- The same bound, soundness phrased by forking success (via the
tightness `reduction_winProb`). -/
theorem gameBound_of_forking {Ψ : Type*} (Y : G.V) (ideal : Ψ)
    (tests : Set (Ψ → ℝ≥0∞))
    (forkerOf : (Ψ → ℝ≥0∞) → RandomSystems.Dist (Option (G.Fork Y)))
    (εAomdl slack : ℝ≥0∞)
    (hhard : ∀ sol : G.AomdlSolver,
      (G.aomdlProblem.perf Y sol : ℝ≥0∞) ≤ εAomdl)
    (hsound : ∀ t ∈ tests,
      t ideal ≤ ((forkerOf t).mass (fun o => o.isSome) : ℝ≥0∞) + slack) :
    ideal ∈ gameSpec tests (εAomdl + slack) :=
  gameBound_of_aomdl G Y ideal tests forkerOf εAomdl slack hhard
    (fun t ht => by rw [reduction_winProb]; exact hsound t ht)

end FrostGroup

/-! ## The Setup-level game leaf and the final security theorem -/

variable {F V Msg SId RoIn : Type} {n τ : ℕ}

/-- **AOMDL hardness**: an advantage functional (per dishonest set) capped
at `εAomdl`.  A hardness *assumption* about the group. -/
def AomdlHard {Solver : Type} (adv : Set (Fin n) → Solver → ℝ≥0∞)
    (εAomdl : ℝ≥0∞) : Prop :=
  ∀ Z, ∀ s, adv Z s ≤ εAomdl

namespace Setup

variable (S : Setup F V Msg SId RoIn n τ)

/-- **The AOMDL reduction contract**: each admitted forgery test is
dominated by some AOMDL solver's advantage up to `slack`. -/
def AomdlReduction {Solver : Type} (adv : Set (Fin n) → Solver → ℝ≥0∞)
    (t : ℕ) (slack : ℝ≥0∞) : Prop :=
  ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ test ∈ S.tests Z,
    ∃ s, test S.tss ≤ adv Z s + slack

/-- **The game leaf, derived from AOMDL** — feeds `Setup.secure` directly. -/
theorem gameLeaf_of_aomdl {Solver : Type} {adv : Set (Fin n) → Solver → ℝ≥0∞}
    {t : ℕ} {εAomdl slack : ℝ≥0∞}
    (hard : AomdlHard adv εAomdl)
    (sound : S.AomdlReduction adv t slack) :
    S.GameLeaf t (εAomdl + slack) :=
  fun Z hZ =>
    gameBound_of_reduction S.tss (S.tests Z) (adv Z) εAomdl slack
      (hard Z) (sound Z hZ)

/-- **FROST security, game leaf discharged to AOMDL.**  The only
cryptographic inputs are the two statistical simulators, AOMDL hardness,
and the reduction contract; the unforgeability bound is
`(εAomdl + slack) + (εDkg + εSign)`. -/
theorem secure_of_aomdl {Solver : Type} {adv : Set (Fin n) → Solver → ℝ≥0∞}
    {t : ℕ} {εDkg εSign εAomdl slack : ℝ≥0∞}
    (hdkg : S.DkgLeaf t εDkg) (hsign : S.SignLeaf t εSign)
    (hard : AomdlHard adv εAomdl)
    (sound : S.AomdlReduction adv t slack) :
    ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ S.net Z,
      patternAttach Zᶜ (S.sign * S.dkg) • R ∈
          Relaxation.eball (εDkg + εSign)
            (zStar (M := Proto F V Msg SId RoIn n τ) tupleGamma Z {S.tss})
      ∧ patternAttach Zᶜ (S.sign * S.dkg) • R ∈
          gameSpec (S.tests Z) ((εAomdl + slack) + (εDkg + εSign)) :=
  S.secure hdkg hsign (S.gameLeaf_of_aomdl hard sound)

end Setup

end RandomSystemsCC.Frost
