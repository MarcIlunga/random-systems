/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BoundedAttainment
import RandomSystems.GameOf

/-!
# Game Winnability (Lanzenberger thesis §2.3.3 and §2.4.3)

The **game half** of the thesis's Chapter 2 foundations: Definitions 2.21, 2.22,
2.25, 2.35, 2.36 and **Theorem 2.37 (Winnability Theorem)** — `ν(S^A) = ω(S^A)`,
attained.  (Definition 2.20's carriers already exist: `PFunDDS.IsMBO`,
`PFunDDS.DDS.IsGame`, `PFunDDS.DDG` in `PDS.lean` and `PFunDDS.gameOfDDS` /
`PFunDDS.MonotoneCond` in `GameOf.lean`.)

## Model bridge (thesis MC-pair vs repository MBO carrier)

The thesis's deterministic game (Def 2.20) is a *pair* `s^A = (s, A)` of an
`(X,Y)`-DDS and a monotone input-history predicate `A : X* → {0,1}`; the game
transcript (Def 2.21) is `(tr(s,e), A(t'))` — the MC value is revealed only at
the *end*, and the environment `e` is a plain `(Y,X)`-DDE which never observes
the MC during the interaction (Remark 2.23).  The repository's game carrier is
CR18's monotone-binary-output form: a game is a `PFunPDS X (Y × Bool)` whose
per-round output carries the MC bit.  The bridge, used throughout this file:

* a thesis pair `(s, A)` is `PFunDDS.gameOfDDS` at an input-only condition —
  the bit shown at history `l` is the MC evaluated at the kept input history;
* the thesis environment is exactly `PFunDDS.Winner X Y = DDE X Y` acting
  through `PFunDDS.winnerView` (the bit-blind lift, CR18 Def 3.23);
* the thesis observable (Def 2.21) is `gameTranscriptDist` below: the
  bit-stripped transcript together with the single `wonFlag` bit;
* the thesis winning-transcript set `𝒯_w` (Def 2.25) is `WinningTranscript`:
  *some answered query carries MC bit `1`*.  For the thesis's **monotone** MC
  and an interaction whose queries are answered this coincides with "the
  transcript ends with `(·,1)`"; the `∃`-form is the faithful reading in the
  `⊥`-totalized model (where a rejected query is answered `none` and deleted),
  and matches `winsDDS` (CR18 Def 3.23) exactly.

Two deliberate deviations from the thesis's letter, both *documented gains*:

* **Monotonicity of the MC is never assumed.**  Def 2.20 requires `A`
  monotone; every statement here holds for an arbitrary MBO because the
  winning event "some answered bit is `1`" is itself monotone along the
  interaction.  The theorems are strictly more general than the thesis's.
* **No probability-distribution hypothesis.**  Like the system half
  (Thm 2.31/2.32 in `BoundedAttainment.lean` / `RandomSystemCoupling.lean`),
  everything is stated at Def 2.1's arbitrary-weight generality.

## Theorem 2.37, proof route

We follow the thesis's own **"Alternative Proof of Theorem 2.37"** (printed
p. 26), which reduces winnability to Theorem 2.31 — already proved in
`BoundedAttainment.lean` — instead of repeating its induction:

1. `ν ≤ ω` (`supWinProb_le_infWinnability`): a winning transcript certifies a
   winnable realization, for every representative of the class.
2. The **never-won twin** `V := zeroMBODist G` (`T` vs `V` in the thesis's
   sketch): same `Y`-behavior and domains, MC bit forced to `0`.
3. Theorem 2.31 attainment on `(G, V)` yields representatives `G' ≡ G`,
   `V' ≡ V` with `δ(G', V') = Adv(G, V)`.
4. Every `Equivalent`-representative of `V` has **no winnable atom**
   (`mass_winnable_eq_zero_of_equivalent_zeroMBODist`): a winnable atom would
   force positive winning mass under its own fixed-query environment
   (`playQueries`), which `V` cannot produce.
5. `G'.mass Winnable ≤ δ(G', V')` (`mass_sub_mass_le_δ` with step 4).
6. `Adv(G, V) ≤ ν(G)` (`adv_zeroMBODist_le_supWinProb`): per environment the
   transcript distance to the twin is at most the winning mass (`zeroMBO`
   changes nothing on a not-yet-won run), and **bit-adaptivity is useless**
   (`winningMass_eq_winningMass_blindize`) so the bound lands on the thesis's
   bit-blind supremum.
7. The chain `ν ≤ ω ≤ G'.mass Winnable ≤ Adv(G,V) ≤ ν` collapses; `G'`
   attains the infimum.

The hypotheses are the thesis's standing finiteness assumptions (Def 2.9
"finite", Def 2.14 common domain), exactly as in Theorem 2.31: `[Fintype X]`,
one fixed atom domain `D`, and a uniform depth bound on `D`.

## CR18 reconciliation

`maxWinProb_eq_supWinProb` proves that CR18's `Γ` (Definition 4.17, the
supremum over probability-distribution winners of `winProb`) **equals** the
thesis's `ν` (Definition 2.25, the supremum over deterministic environments of
the winning-transcript mass) — the audit fact that the repository's
CR18-shaped game-performance layer states the thesis's Definition 2.25.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open PFunDDS

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Winning transcripts (thesis Def 2.25's `𝒯_w`) -/

/-- Thesis Definition 2.25's winning-transcript set `𝒯_w`, in the MBO carrier:
a transcript prefix is **winning** when some answered query carries the MC bit
`1`.  For a monotone MC (thesis Def 2.20) and an interaction whose queries are
answered this is "the transcript ends with `(·, 1)`"; the `∃`-form is the
faithful reading in the `⊥`-totalized model and matches `winsDDS`
(CR18 Def 3.23) literally. -/
def WinningTranscript (t : List (X × Option (Y × Bool))) : Prop :=
  ∃ y : Y, (some (y, true) : Option (Y × Bool)) ∈ t↓ᵧ

/-- Winning is monotone along the interaction: a winning prefix stays winning.
This is why the thesis's Def 2.20 monotonicity of the MC is never needed for
the winnability results — the *event* is monotone regardless of the MC. -/
theorem winningTranscript_mono {t t' : List (X × Option (Y × Bool))}
    (hprefix : t <+: t') (hwin : WinningTranscript t) : WinningTranscript t' := by
  obtain ⟨y, hy⟩ := hwin
  exact ⟨y, (hprefix.map Prod.snd).subset hy⟩

@[simp] theorem not_winningTranscript_nil :
    ¬ WinningTranscript ([] : List (X × Option (Y × Bool))) := by
  rintro ⟨y, hy⟩
  simp [transcriptOutputs] at hy

/-- The winning-transcript mass of a probabilistic game under environment `e`
after `n` rounds: `Pr^{eG}(tr(G,e) ∈ 𝒯_w)`, the quantity whose supremum is
thesis Definition 2.25. -/
noncomputable def winningMass (G : PFunPDS X (Y × Bool))
    (e : DDE X (Y × Bool)) (n : ℕ) : ℝ :=
  G.mass fun g => WinningTranscript (transcript g e n)

/-- The winning mass reads off the transcript distribution (thesis Def 2.12's
`tr(S,e)`) — it is the `𝒯_w`-mass of the transcript law. -/
theorem winningMass_eq_mass_transcriptDist (G : PFunPDS X (Y × Bool))
    (e : DDE X (Y × Bool)) (n : ℕ) :
    winningMass G e n = (transcriptDist G e n).mass WinningTranscript := by
  unfold winningMass transcriptDist
  rw [Dist.mass_fTransform]

/-- Transcript-equivalent games have the same winning mass in every
environment — the winning flag is transcript-observable. -/
theorem winningMass_congr_equivalent {G H : PFunPDS X (Y × Bool)}
    (hequiv : Equivalent G H) (e : DDE X (Y × Bool)) (n : ℕ) :
    winningMass G e n = winningMass H e n := by
  rw [winningMass_eq_mass_transcriptDist, winningMass_eq_mass_transcriptDist,
    hequiv e n]

/-! ### Thesis Definition 2.21/2.22 — the game transcript and PDG equivalence

Thesis Def 2.21: the transcript of a game under a (bit-blind) environment is
the pair `(t, A(t'))` — the underlying transcript plus the *single* final MC
value; the environment does not see the MC during the interaction
(Remark 2.23).  In the MBO carrier this is the bit-stripped transcript paired
with the `wonFlag` bit.  Def 2.22: two probabilistic games are equivalent when
these observables agree under every environment. -/

/-- The computable won-flag of a transcript prefix: `true` iff some answered
query carries MC bit `1`.  Boolean form of `WinningTranscript` (thesis
Def 2.21's `A(t')`, read on the kept inputs). -/
def wonFlag (t : List (X × Option (Y × Bool))) : Bool :=
  t.any fun p => ((p.2.map Prod.snd).getD false)

theorem wonFlag_eq_true_iff (t : List (X × Option (Y × Bool))) :
    wonFlag t = true ↔ WinningTranscript t := by
  unfold wonFlag WinningTranscript
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨x, o⟩, hmem, hflag⟩
    rcases o with _ | ⟨y, b⟩
    · simp at hflag
    · simp only [Option.map_some, Option.getD_some] at hflag
      subst hflag
      exact ⟨y, List.mem_map.mpr ⟨(x, some (y, true)), hmem, rfl⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hmem, hsnd⟩ := List.mem_map.mp hy
    exact ⟨p, hmem, by simp [hsnd]⟩

/-- Thesis Definition 2.21, the observable of one deterministic run: the
bit-stripped transcript together with the final won flag `A(t')`.  The
per-round MC bits are *not* part of the observable (Remark 2.23). -/
def gameTranscriptView (t : List (X × Option (Y × Bool))) :
    List (X × Option Y) × Bool :=
  (t.map fun p => (p.1, p.2.map Prod.fst), wonFlag t)

/-- Thesis Definition 2.21/2.22, the game-transcript distribution
`tr(S^A, e)`: the law of `(t, A(t'))` under a bit-blind deterministic
environment (`Winner X Y = DDE X Y` through `winnerView`). -/
noncomputable def gameTranscriptDist (G : PFunPDS X (Y × Bool))
    (winner : Winner X Y) (n : ℕ) : Dist (List (X × Option Y) × Bool) :=
  Dist.fTransform
    (fun g => gameTranscriptView (transcript g (winnerView winner) n)) G

/-- Thesis Definition 2.22: two probabilistic games are **equivalent** when
their game-transcript distributions (Def 2.21) agree under every deterministic
environment.  The thesis's same-domain clause is absorbed by the `⊥`-totalized
model exactly as in Def 2.17 (domains are observable through the
`none`-answers of the stripped transcript). -/
def GameEquivalent (G H : PFunPDS X (Y × Bool)) : Prop :=
  ∀ (winner : Winner X Y) (n : ℕ),
    gameTranscriptDist G winner n = gameTranscriptDist H winner n

theorem gameEquivalent_refl (G : PFunPDS X (Y × Bool)) : GameEquivalent G G :=
  fun _ _ => rfl

/-- Remark 2.23, quantitative half: system-transcript equivalence (where the
environment *does* observe the per-round MC bits) refines game equivalence.
The thesis's warning is that the converse fails — observing the MC may reveal
strictly more. -/
theorem gameEquivalent_of_equivalent {G H : PFunPDS X (Y × Bool)}
    (hequiv : Equivalent G H) : GameEquivalent G H := by
  intro winner n
  calc gameTranscriptDist G winner n
      = Dist.fTransform gameTranscriptView
          (transcriptDist G (winnerView winner) n) :=
        (Dist.fTransform_comp gameTranscriptView
          (fun g => transcript g (winnerView winner) n) G).symm
    _ = Dist.fTransform gameTranscriptView
          (transcriptDist H (winnerView winner) n) := by
        rw [hequiv (winnerView winner) n]
    _ = gameTranscriptDist H winner n :=
        Dist.fTransform_comp gameTranscriptView
          (fun g => transcript g (winnerView winner) n) H

/-- The winning mass under a bit-blind environment is the won-flag mass of the
game-transcript distribution — the winning probability is a Def 2.21
observable. -/
theorem winningMass_winnerView_eq_mass_gameTranscriptDist
    (G : PFunPDS X (Y × Bool)) (winner : Winner X Y) (n : ℕ) :
    winningMass G (winnerView winner) n
      = (gameTranscriptDist G winner n).mass fun pair => pair.2 = true := by
  unfold winningMass gameTranscriptDist
  rw [Dist.mass_fTransform]
  exact Dist.mass_congr G fun g =>
    (wonFlag_eq_true_iff (transcript g (winnerView winner) n)).symm

/-- Game-equivalent games have the same winning mass under every bit-blind
environment (thesis Def 2.22 preserves Def 2.25's observable). -/
theorem winningMass_winnerView_congr_gameEquivalent
    {G H : PFunPDS X (Y × Bool)} (hequiv : GameEquivalent G H)
    (winner : Winner X Y) (n : ℕ) :
    winningMass G (winnerView winner) n = winningMass H (winnerView winner) n := by
  rw [winningMass_winnerView_eq_mass_gameTranscriptDist,
    winningMass_winnerView_eq_mass_gameTranscriptDist, hequiv winner n]

/-! ### Thesis Definition 2.25 — the supremum winning probability `ν` -/

/-- Thesis Definition 2.25: the **supremum winning probability**
`ν(S^A) := sup_e Pr^{eS^A}(tr(S^A, e) ∈ 𝒯_w)`, the supremum over all
deterministic (bit-blind, Remark 2.23) environments and all prefix lengths of
the winning-transcript mass.  Well-defined on the equivalence class by
`winningMass_winnerView_congr_gameEquivalent`. -/
noncomputable def supWinProb (G : PFunPDS X (Y × Bool)) : ℝ :=
  sSup {a : ℝ | ∃ (winner : Winner X Y) (n : ℕ),
    a = winningMass G (winnerView winner) n}

theorem supWinProb_set_nonempty (G : PFunPDS X (Y × Bool)) :
    {a : ℝ | ∃ (winner : Winner X Y) (n : ℕ),
      a = winningMass G (winnerView winner) n}.Nonempty :=
  ⟨_, (fun _ => none), 0, rfl⟩

/-- The `ν`-set is bounded by the game's weight.  On the signed carrier a
distribution's event mass is only below its weight when the law is
non-negative, so `ν` is a genuine supremum exactly on Def 2.1's
distributions. -/
theorem bddAbove_supWinProb_set {G : PFunPDS X (Y × Bool)} (hG : G.NonNeg) :
    BddAbove {a : ℝ | ∃ (winner : Winner X Y) (n : ℕ),
      a = winningMass G (winnerView winner) n} := by
  refine ⟨G.weight, ?_⟩
  rintro a ⟨winner, n, rfl⟩
  exact Dist.mass_le_weight hG _

/-- Definition 2.25's defining property: every environment's winning mass is a
lower bound on `ν`. -/
theorem winningMass_winnerView_le_supWinProb {G : PFunPDS X (Y × Bool)}
    (hG : G.NonNeg) (winner : Winner X Y) (n : ℕ) :
    winningMass G (winnerView winner) n ≤ supWinProb G :=
  le_csSup (bddAbove_supWinProb_set hG) ⟨winner, n, rfl⟩

/-! ### Thesis Definition 2.35/2.36 — winnability and `ω` -/

/-- Thesis Definition 2.35: a deterministic game is **winnable** if some
in-domain input sequence triggers the winning condition — in the MBO carrier,
some in-domain history carries MC bit `1`.  A *static* property of the
realization, independent of any environment. -/
def PFunDDS.Winnable (g : DDS X (Y × Bool)) : Prop :=
  ∃ (l : List X) (hl : l ∈ dom g), (output g l hl).2 = true

/-- Thesis Definition 2.36: the **infimum winnability**
`ω(S^A) := inf_{S^A ∈ [S^A]} Pr^{S^A}(S^A is winnable)` — the infimum of the
winnable mass over all representatives of the game-equivalence class
(Def 2.22).

A *representative* is a probability system in Def 2.1's sense, i.e. a
non-negative law.  On the `NNReal` carrier that was the carrier itself; on the
signed carrier the conjunct `H.NonNeg` has to be written down, and it is the
same index set as before — dropping it would let a signed `H` with the same
observable drive the infimum to `−∞`. -/
noncomputable def infWinnability (G : PFunPDS X (Y × Bool)) : ℝ :=
  sInf ((fun H : PFunPDS X (Y × Bool) => H.mass PFunDDS.Winnable) ''
    {H | H.NonNeg ∧ GameEquivalent H G})

/-- The `ω`-set is bounded below by `0`: every representative is a
non-negative law, so its winnable mass is non-negative. -/
theorem bddBelow_infWinnability_set (G : PFunPDS X (Y × Bool)) :
    BddBelow ((fun H : PFunPDS X (Y × Bool) => H.mass PFunDDS.Winnable) ''
      {H | H.NonNeg ∧ GameEquivalent H G}) := by
  refine ⟨0, ?_⟩
  rintro b ⟨H, ⟨hH, -⟩, rfl⟩
  exact hH.mass_nonneg _

/-- A winning transcript certifies a winnable realization (thesis proof of
Thm 2.37, the trivial direction `ω ≥ ν`, deterministic core): the winning
answer sits at an in-domain kept-input history with MC bit `1`. -/
theorem PFunDDS.winnable_of_winningTranscript {g : DDS X (Y × Bool)}
    {e : DDE X (Y × Bool)} {n : ℕ}
    (hwin : WinningTranscript (transcript g e n)) : PFunDDS.Winnable g := by
  obtain ⟨y, hy⟩ := hwin
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hy
  have hk' : k < (transcript g e n).length := by
    simpa [transcriptOutputs] using hk
  have hval := (transcript_consistent g e n).2 k hk'
  have hsnd : (transcript g e n)[k].2 = some (y, true) := by
    have : (transcript g e n)↓ᵧ[k] = (transcript g e n)[k].2 := by
      simp [transcriptOutputs]
    rw [← this]
    exact hget
  rw [hsnd] at hval
  obtain ⟨hdom', hgeteq⟩ := Part.eq_some_iff.mp hval
  have hout : output (fullyDefined g) (((transcript g e n).take (k + 1))↓ₓ)
      hdom' = some (y, true) := hgeteq
  simp only [output_fullyDefined] at hout
  split at hout
  · rename_i hcand
    refine ⟨_, hcand, ?_⟩
    have houtval := Option.some_injective _ hout
    rw [houtval]
  · exact absurd hout (by simp)

/-- Thesis Theorem 2.37, the trivial direction: `ν(S^A) ≤ ω(S^A)`.  For every
representative and every environment, winning the interaction requires a
winnable realization. -/
theorem supWinProb_le_infWinnability {G : PFunPDS X (Y × Bool)} (hG : G.NonNeg) :
    supWinProb G ≤ infWinnability G := by
  refine le_csInf ⟨G.mass PFunDDS.Winnable, G, ⟨hG, gameEquivalent_refl G⟩, rfl⟩ ?_
  rintro b ⟨H, ⟨hHnn, hH⟩, rfl⟩
  refine csSup_le (supWinProb_set_nonempty G) ?_
  rintro a ⟨winner, n, rfl⟩
  calc winningMass G (winnerView winner) n
      = winningMass H (winnerView winner) n :=
        (winningMass_winnerView_congr_gameEquivalent hH winner n).symm
    _ ≤ H.mass PFunDDS.Winnable :=
        mass_mono hHnn fun g hg => PFunDDS.winnable_of_winningTranscript hg

/-! ### The never-won twin `V` (thesis p. 26, the system that "always outputs
the bit `bᵢ = 0`") -/

/-- The **never-won twin** of a deterministic game: same domain, same
`Y`-outputs, MC bit forced to `0`.  Reuses `gameOfDDS` at the constantly-false
condition over the stripped system. -/
def PFunDDS.zeroMBO (g : DDS X (Y × Bool)) : DDS X (Y × Bool) :=
  gameOfDDS (fun _ => false) (ignoreMBO g)

@[simp] theorem PFunDDS.dom_zeroMBO (g : DDS X (Y × Bool)) :
    dom (PFunDDS.zeroMBO g) = dom g := rfl

theorem PFunDDS.output_zeroMBO (g : DDS X (Y × Bool)) (l : List X)
    (hl : l ∈ dom (PFunDDS.zeroMBO g)) (hl' : l ∈ dom g) :
    output (PFunDDS.zeroMBO g) l hl = ((output g l hl').1, false) :=
  output_gameOfDDS (fun _ => false) (ignoreMBO g) l hl hl'

theorem PFunDDS.outputBit_zeroMBO (g : DDS X (Y × Bool)) (l : List X)
    (hl : l ∈ dom (PFunDDS.zeroMBO g)) :
    (output (PFunDDS.zeroMBO g) l hl).2 = false := by
  rw [PFunDDS.output_zeroMBO g l hl hl]

/-- The probabilistic never-won twin (thesis p. 26's `V`): push `zeroMBO`
through the distribution. -/
noncomputable def zeroMBODist (G : PFunPDS X (Y × Bool)) :
    PFunPDS X (Y × Bool) :=
  Dist.fTransform PFunDDS.zeroMBO G

/-- The twin's completed outputs are the base's with the MC bit forced to `0`
(same kept prefixes, same domain test). -/
theorem PFunDDS.output_fullyDefined_zeroMBO (g : DDS X (Y × Bool))
    (l : List X) (hl : l ∈ dom (fullyDefined (PFunDDS.zeroMBO g)))
    (hl' : l ∈ dom (fullyDefined g)) :
    output (fullyDefined (PFunDDS.zeroMBO g)) l hl
      = Option.map (fun p : Y × Bool => (p.1, false))
          (output (fullyDefined g) l hl') := by
  simp only [output_fullyDefined]
  have hkept : keptPrefix (PFunDDS.zeroMBO g) l.dropLast
      = keptPrefix g l.dropLast := by
    unfold PFunDDS.zeroMBO
    rw [keptPrefix_gameOfDDS, keptPrefix_ignoreMBO]
  rw [hkept]
  by_cases hcand :
      keptPrefix g l.dropLast ++ [l.getLast (by exact hl')] ∈ dom g
  · rw [dif_pos hcand,
      dif_pos (show keptPrefix g l.dropLast ++ [l.getLast (by exact hl)]
        ∈ dom (PFunDDS.zeroMBO g) from hcand),
      PFunDDS.output_zeroMBO g _ _ hcand]
    rfl
  · rw [dif_neg hcand,
      dif_neg (show keptPrefix g l.dropLast ++ [l.getLast (by exact hl)]
        ∉ dom (PFunDDS.zeroMBO g) from hcand)]
    rfl

/-- The never-won twin never produces a winning transcript, against **any**
environment: its answered bits are all `0`. -/
theorem PFunDDS.not_winningTranscript_zeroMBO (g : DDS X (Y × Bool))
    (e : DDE X (Y × Bool)) (n : ℕ) :
    ¬ WinningTranscript (transcript (PFunDDS.zeroMBO g) e n) := by
  induction n with
  | zero => exact not_winningTranscript_nil
  | succ n ih =>
      rcases he : e ((transcript (PFunDDS.zeroMBO g) e n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall he]
        exact ih
      · rw [transcript_succ_fire he]
        rintro ⟨y, hy⟩
        rw [transcriptOutputs_append] at hy
        rcases List.mem_append.mp hy with hmem | hmem
        · exact ih ⟨y, hmem⟩
        · have hval := (List.mem_singleton.mp hmem).symm
          simp only [output_fullyDefined] at hval
          split at hval
          · rename_i hcand
            have hbit := congrArg (fun o : Option (Y × Bool) =>
              (o.map Prod.snd).getD false) hval
            simp only [Option.map_some, Option.getD_some] at hbit
            rw [PFunDDS.outputBit_zeroMBO] at hbit
            exact Bool.false_ne_true hbit
          · exact absurd hval (by simp)

/-! ### The probing run: a winnable atom wins its own fixed-query environment -/

/-- The **probing run** (used for step 4 of the Thm 2.37 route): a winnable
deterministic game produces a winning transcript against the fixed-query
environment that plays the winnable input sequence.  All prefixes are
in-domain (prefix closure), so every query of `playQueries l` is answered and
the final answer carries the MC bit `1`. -/
theorem PFunDDS.winningTranscript_playQueries_of_winnable
    {g : DDS X (Y × Bool)} {l : List X} (hdom : l ∈ dom g)
    (hbit : (output g l hdom).2 = true) :
    WinningTranscript (transcript g (playQueries l) l.length) := by
  have hne : l ≠ [] := fun hnil => empty_not_mem g (hnil ▸ hdom)
  have hlpos : 0 < l.length := List.length_pos_iff.mpr hne
  -- the canonical run: after `k ≤ |l|` rounds the transcript has played
  -- exactly `l.take k`
  have hinv : ∀ k, k ≤ l.length →
      (transcript g (playQueries l) k).length = k ∧
      (transcript g (playQueries l) k)↓ₓ = l.take k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨rfl, by simp [transcriptInputs]⟩
    | succ k ih =>
        intro hk1
        obtain ⟨hlength, hinputs⟩ := ih (by omega)
        have hklt : k < l.length := by omega
        have hfire : playQueries (Y := Y × Bool) l
            ((transcript g (playQueries l) k)↓ᵧ) = some l[k] := by
          show l[((transcript g (playQueries l) k)↓ᵧ).length]? = some l[k]
          rw [transcriptOutputs_length, hlength, List.getElem?_eq_getElem hklt]
        rw [transcript_succ_fire hfire]
        refine ⟨by simp [hlength], ?_⟩
        rw [transcriptInputs_append, hinputs, take_succ_get' l k hklt,
          List.get_eq_getElem]
  -- final round: fire the last query and read the winning bit
  obtain ⟨hlength, hinputs⟩ := hinv (l.length - 1) (by omega)
  have hklt : l.length - 1 < l.length := by omega
  have hfire : playQueries (Y := Y × Bool) l
      ((transcript g (playQueries l) (l.length - 1))↓ᵧ)
        = some l[l.length - 1] := by
    show l[((transcript g (playQueries l) (l.length - 1))↓ᵧ).length]?
      = some l[l.length - 1]
    rw [transcriptOutputs_length, hlength, List.getElem?_eq_getElem hklt]
  have hstep : l.length = (l.length - 1) + 1 := by omega
  rw [hstep, transcript_succ_fire hfire]
  -- the appended answer is `some (output g l hdom)`
  have htake : l.take (l.length - 1) ++ [l[l.length - 1]] = l := by
    have hsucc := take_succ_get' l (l.length - 1) hklt
    rw [List.get_eq_getElem] at hsucc
    rw [← hsucc, ← hstep, List.take_length]
  have hprefixOrNil : l.take (l.length - 1) ∈ dom g ∨ l.take (l.length - 1) = [] := by
    rcases Nat.eq_zero_or_pos (l.length - 1) with hzero | hpos
    · right
      rw [hzero, List.take_zero]
    · left
      refine prefix_closed g (List.take_prefix (l.length - 1) l) ?_ hdom
      intro hnil
      rcases List.take_eq_nil_iff.mp hnil with h | h <;>
        first | omega | exact hne h
  have hnext : l.take (l.length - 1) ++ [l[l.length - 1]] ∈ dom g := by
    rw [htake]; exact hdom
  have hlist : (transcript g (playQueries l) (l.length - 1))↓ₓ
        ++ [l[l.length - 1]]
      = l.take (l.length - 1) ++ [l[l.length - 1]] := by
    rw [hinputs]
  have hanswer : output (fullyDefined g)
      ((transcript g (playQueries l) (l.length - 1))↓ₓ ++ [l[l.length - 1]])
        (by simp [fullyDefined, dom])
      = some (output g l hdom) := by
    rw [output_congr (fullyDefined g) hlist _
        (by rw [dom_fullyDefined]; simp [hne]),
      output_fullyDefined_append_of_mem g _ _ hprefixOrNil hnext]
    exact congrArg some (output_congr g htake hnext hdom)
  refine ⟨(output g l hdom).1, ?_⟩
  rw [transcriptOutputs_append]
  refine List.mem_append_right _ ?_
  rw [List.mem_singleton, hanswer]
  have hpair : output g l hdom = ((output g l hdom).1, true) :=
    Prod.ext_iff.mpr ⟨rfl, hbit⟩
  exact congrArg some hpair.symm

/-- Every atom below a distribution's event mass: `X(a) ≤ X(P)` when `P a`.
Non-negativity is what makes the other summands harmless, structural on the
`NNReal` carrier and a hypothesis on the signed one.
(UPSTREAM-CANDIDATE: `Dist.mass` companion to `Finset.single_le_sum`.) -/
theorem apply_le_mass {A : Type*} {X : Dist A} (hX : X.NonNeg) {P : A → Prop}
    {a : A} (ha : P a) : X a ≤ X.mass P := by
  classical
  by_cases hsupport : a ∈ X.support
  · unfold Dist.mass Finsupp.sum
    calc X a = (if P a then X a else 0) := (if_pos ha).symm
      _ ≤ _ := Finset.single_le_sum
          (f := fun a' => if P a' then X a' else 0)
          (fun a' _ => by by_cases h : P a' <;> simp [h, hX a']) hsupport
  · rw [Finsupp.notMem_support_iff.mp hsupport]
    exact hX.mass_nonneg _

/-- **Step 4 of the Thm 2.37 route**: every transcript-equivalent
representative of the never-won twin has winnable mass `0`.  A winnable
support atom would give positive winning mass against its own fixed-query
environment (`winningTranscript_playQueries_of_winnable`), but the twin's
winning mass is `0` in every environment
(`not_winningTranscript_zeroMBO`) and winning mass is a transcript
observable.  No finiteness is needed: the finite support carries the
probing. -/
theorem mass_winnable_eq_zero_of_equivalent_zeroMBODist
    {G V' : PFunPDS X (Y × Bool)} (hV' : V'.NonNeg)
    (hequiv : Equivalent V' (zeroMBODist G)) :
    V'.mass PFunDDS.Winnable = 0 := by
  rw [mass_congr_support V' (Q := fun _ => False) ?_]
  · exact Dist.mass_eq_zero_of_forall_not V' fun _ h => h
  intro v hv
  simp only [iff_false]
  rintro ⟨l, hdom, hbit⟩
  have hwin : WinningTranscript (transcript v (playQueries l) l.length) :=
    PFunDDS.winningTranscript_playQueries_of_winnable hdom hbit
  have hzero : winningMass V' (playQueries l) l.length = 0 := by
    rw [winningMass_congr_equivalent hequiv (playQueries l) l.length]
    unfold winningMass zeroMBODist
    rw [Dist.mass_fTransform]
    exact Dist.mass_eq_zero_of_forall_not G fun g =>
      PFunDDS.not_winningTranscript_zeroMBO g (playQueries l) l.length
  have hpos : V' v ≤ winningMass V' (playQueries l) l.length :=
    apply_le_mass hV' hwin
  rw [hzero] at hpos
  exact Finsupp.mem_support_iff.mp hv (le_antisymm hpos (hV' v))

/-! ### Step 6: per-environment distance to the twin is at most the winning
mass -/

/-- On a not-yet-won run the never-won twin is indistinguishable from the
game: while no answered bit is `1`, forcing the bits to `0` changes nothing,
so the transcripts coincide. -/
theorem PFunDDS.transcript_zeroMBO_eq_of_not_winningTranscript
    {g : DDS X (Y × Bool)} {e : DDE X (Y × Bool)} :
    ∀ {n : ℕ}, ¬ WinningTranscript (transcript g e n) →
      transcript (PFunDDS.zeroMBO g) e n = transcript g e n := by
  intro n
  induction n with
  | zero => exact fun _ => rfl
  | succ n ih =>
      intro hnotwin
      have hnotwin' : ¬ WinningTranscript (transcript g e n) := fun hwin =>
        hnotwin (winningTranscript_mono
          (transcript_prefix_of_le g e (Nat.le_succ n)) hwin)
      have heq := ih hnotwin'
      rcases he : e ((transcript g e n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall
          (show e ((transcript (PFunDDS.zeroMBO g) e n)↓ᵧ) = none by
            rw [heq]; exact he),
          transcript_succ_stall he]
        exact heq
      · have hez : e ((transcript (PFunDDS.zeroMBO g) e n)↓ᵧ) = some x := by
          rw [heq]; exact he
        rw [transcript_succ_fire hez, transcript_succ_fire he]
        -- the answered outputs agree because the run is not yet won
        have hlist : (transcript (PFunDDS.zeroMBO g) e n)↓ₓ ++ [x]
            = (transcript g e n)↓ₓ ++ [x] := by
          rw [heq]
        have hanswer : output (fullyDefined (PFunDDS.zeroMBO g))
            ((transcript (PFunDDS.zeroMBO g) e n)↓ₓ ++ [x])
              (by simp [fullyDefined, dom])
            = output (fullyDefined g) ((transcript g e n)↓ₓ ++ [x])
              (by simp [fullyDefined, dom]) := by
          rw [output_congr (fullyDefined (PFunDDS.zeroMBO g)) hlist
              _ (by rw [dom_fullyDefined]; simp),
            PFunDDS.output_fullyDefined_zeroMBO g _ _
              (by rw [dom_fullyDefined]; simp)]
          rcases hval : output (fullyDefined g)
              ((transcript g e n)↓ₓ ++ [x])
              (by rw [dom_fullyDefined]; simp) with _ | ⟨y, b⟩
          · rfl
          · rcases b with _ | _
            · rfl
            · exfalso
              refine hnotwin ⟨y, ?_⟩
              rw [transcript_succ_fire he, transcriptOutputs_append]
              exact List.mem_append_right _
                (List.mem_singleton.mpr hval.symm)
        rw [hanswer, heq]

/-- One-sided `δ` against a pointwise-dominating law concentrates on the
excess event: if `μ ≤ ν` off `P` then `δ(μ, ν) ≤ μ(P)`.  Both laws must be
non-negative: on `P` the summand `max (μ a − ν a) 0` is below `μ a` only when
neither value is negative.
(UPSTREAM-CANDIDATE: Def 2.4 toolkit.) -/
theorem δ_le_mass_of_le_on_compl {A : Type*} {μ ν : Dist A} (hμ : μ.NonNeg)
    (hν : ν.NonNeg) (P : A → Prop)
    (hle : ∀ a, ¬ P a → μ a ≤ ν a) : δ μ ν ≤ μ.mass P := by
  classical
  unfold δ Dist.mass
  refine Finsupp.sum_le_sum fun a _ => ?_
  by_cases hP : P a
  · rw [if_pos hP]
    exact max_le (sub_le_self _ (hν a)) (hμ a)
  · rw [if_neg hP]
    exact le_of_eq (max_eq_right (sub_nonpos.mpr (hle a hP)))

/-- Per environment, the transcript distance between a game and its never-won
twin is at most the winning mass: on the not-won region the twin dominates
(`transcript_zeroMBO_eq_of_not_winningTranscript`), so the one-sided excess
lives on `𝒯_w`. -/
theorem δ_transcriptDist_zeroMBODist_le_winningMass
    {G : PFunPDS X (Y × Bool)} (hG : G.NonNeg) (e : DDE X (Y × Bool)) (n : ℕ) :
    δ (transcriptDist G e n) (transcriptDist (zeroMBODist G) e n)
      ≤ winningMass G e n := by
  rw [winningMass_eq_mass_transcriptDist]
  refine δ_le_mass_of_le_on_compl (transcriptDist_nonNeg hG e n)
    (show (transcriptDist (zeroMBODist G) e n).NonNeg from
      transcriptDist_nonNeg (hG.fTransform _) e n)
    WinningTranscript fun t hnotwin => ?_
  have hleft : transcriptDist G e n t
      = G.mass fun g => transcript g e n = t :=
    Dist.fTransform_apply_eq_mass _ _ _
  have hright : transcriptDist (zeroMBODist G) e n t
      = G.mass fun g => transcript (PFunDDS.zeroMBO g) e n = t := by
    unfold transcriptDist zeroMBODist
    rw [Dist.fTransform_comp]
    exact Dist.fTransform_apply_eq_mass _ _ _
  rw [hleft, hright]
  refine mass_mono hG fun g hg => ?_
  exact (PFunDDS.transcript_zeroMBO_eq_of_not_winningTranscript
    (fun hwin => hnotwin (hg ▸ hwin))).trans hg

/-! ### Bit-adaptivity is useless (justifies Def 2.25's environment class) -/

/-- The **bit-blinding** of an arbitrary game environment: pretend every
answered bit was `0`.  Produces a thesis environment (`Winner X Y`). -/
def blindize (e : DDE X (Y × Bool)) : Winner X Y :=
  fun ys => e (ys.map (Option.map fun y : Y => (y, false)))

theorem winnerView_blindize_apply (e : DDE X (Y × Bool))
    (ys : List (Option (Y × Bool))) :
    winnerView (blindize e) ys
      = e (ys.map (Option.map fun p : Y × Bool => (p.1, false))) := by
  unfold winnerView blindize
  rw [List.map_map]
  refine congrArg e (List.map_congr_left fun o _ => ?_)
  rcases o with _ | p <;> rfl

/-- On a not-yet-won transcript, zeroing the answered bits is the identity. -/
theorem map_zeroAnswers_eq_of_not_winningTranscript
    {t : List (X × Option (Y × Bool))} (hnotwin : ¬ WinningTranscript t) :
    (t↓ᵧ).map (Option.map fun p : Y × Bool => (p.1, false)) = t↓ᵧ := by
  have hpointwise : ∀ o ∈ t↓ᵧ,
      Option.map (fun p : Y × Bool => (p.1, false)) o = o := by
    intro o ho
    rcases o with _ | ⟨y, b⟩
    · rfl
    · rcases b with _ | _
      · rfl
      · exact absurd ⟨y, ho⟩ hnotwin
  rw [List.map_congr_left hpointwise]
  exact List.map_id' _

/-- **Adaptivity on the MC bit is useless for winning** (Remark 2.23 made
quantitative; the CR18-side analogue is `Γᵇ` vs `Γ`): against any game
realization, an arbitrary environment and its bit-blinding produce winning
transcripts simultaneously — before the first winning answer the two runs
coincide, and afterwards both are already won. -/
theorem winningTranscript_winnerView_blindize_iff (g : DDS X (Y × Bool))
    (e : DDE X (Y × Bool)) (n : ℕ) :
    WinningTranscript (transcript g (winnerView (blindize e)) n)
      ↔ WinningTranscript (transcript g e n) := by
  suffices hinv : ∀ m : ℕ,
      (transcript g (winnerView (blindize e)) m = transcript g e m ∧
        ¬ WinningTranscript (transcript g e m)) ∨
      (WinningTranscript (transcript g (winnerView (blindize e)) m) ∧
        WinningTranscript (transcript g e m)) by
    rcases hinv n with ⟨heq, hnotwin⟩ | ⟨hwin, hwin'⟩
    · rw [heq]
    · exact iff_of_true hwin hwin'
  intro m
  induction m with
  | zero => exact Or.inl ⟨rfl, not_winningTranscript_nil⟩
  | succ m ih =>
      rcases ih with ⟨heq, hnotwin⟩ | ⟨hwin, hwin'⟩
      · have hquery : winnerView (blindize e)
            ((transcript g (winnerView (blindize e)) m)↓ᵧ)
            = e ((transcript g e m)↓ᵧ) := by
          rw [heq, winnerView_blindize_apply,
            map_zeroAnswers_eq_of_not_winningTranscript hnotwin]
        rcases he : e ((transcript g e m)↓ᵧ) with _ | x
        · rw [transcript_succ_stall (hquery.trans he),
            transcript_succ_stall he]
          exact Or.inl ⟨heq, hnotwin⟩
        · rw [transcript_succ_fire (hquery.trans he), transcript_succ_fire he]
          have hanswer : output (fullyDefined g)
              ((transcript g (winnerView (blindize e)) m)↓ₓ ++ [x])
                (by simp [fullyDefined, dom])
              = output (fullyDefined g) ((transcript g e m)↓ₓ ++ [x])
                (by simp [fullyDefined, dom]) :=
            output_congr (fullyDefined g) (by rw [heq]) _ _
          rw [hanswer, heq]
          by_cases hwin1 : WinningTranscript (transcript g e m ++
              [(x, output (fullyDefined g) ((transcript g e m)↓ₓ ++ [x])
                (by simp [fullyDefined, dom]))])
          · exact Or.inr ⟨hwin1, hwin1⟩
          · exact Or.inl ⟨rfl, hwin1⟩
      · exact Or.inr
          ⟨winningTranscript_mono
            (transcript_prefix_of_le _ _ (Nat.le_succ m)) hwin,
          winningTranscript_mono
            (transcript_prefix_of_le _ _ (Nat.le_succ m)) hwin'⟩

/-- Winning-mass form of bit-blinding: every environment's winning mass is
achieved by a thesis (bit-blind) environment. -/
theorem winningMass_eq_winningMass_blindize (G : PFunPDS X (Y × Bool))
    (e : DDE X (Y × Bool)) (n : ℕ) :
    winningMass G e n = winningMass G (winnerView (blindize e)) n :=
  Dist.mass_congr G fun g =>
    (winningTranscript_winnerView_blindize_iff g e n).symm

/-- **Step 6 of the Thm 2.37 route**: the optimal advantage against the
never-won twin is at most the supremum winning probability,
`Adv(G, V) ≤ ν(G)`.  (The thesis states the reverse-flavored equality
`Adv(T, V) = ν(S^A)` on p. 26; only this direction is needed.) -/
theorem adv_zeroMBODist_le_supWinProb {G : PFunPDS X (Y × Bool)} (hG : G.NonNeg) :
    Adv G (zeroMBODist G) ≤ supWinProb G := by
  refine csSup_le ⟨_, (fun _ => none), 0, rfl⟩ ?_
  rintro a ⟨e, n, rfl⟩
  have hδ := δ_transcriptDist_zeroMBODist_le_winningMass hG e n
  have hν : winningMass G e n ≤ supWinProb G := by
    rw [winningMass_eq_winningMass_blindize G e n]
    exact winningMass_winnerView_le_supWinProb hG (blindize e) n
  exact hδ.trans hν

/-! ### Thesis Theorem 2.37 — the Winnability Theorem -/

/-- **Thesis Theorem 2.37 (Winnability Theorem)**, via the thesis's own
alternative proof (p. 26) on top of Theorem 2.31's attainment
(`BoundedAttainment.lean`): for a finite fixed-domain game,

* `ν(S^A) = ω(S^A)` — the supremum winning probability (Def 2.25) equals the
  infimum winnability (Def 2.36), and
* the infimum is **attained**: some transcript-equivalent representative `G'`
  has winnable mass exactly `ν(S^A)`.

The attained representative is `Equivalent` (Def 2.17 at the MBO output
alphabet) — strictly stronger than the Def 2.22 game equivalence that `ω`
quantifies over (`gameEquivalent_of_equivalent`).  This is the precise sense
in which a game with maximal winning probability `δ` is **unwinnable with
probability `1 − δ` over the randomness of the game itself**, independent of
any strategy: for a probability-distribution `G`, `G'` is a probability
distribution of deterministic games of which all but `ν`-mass are statically
unwinnable.  Hypotheses are the thesis's standing finiteness assumptions
(Def 2.9/2.14), exactly as in Theorem 2.31; monotonicity of the MC
(Def 2.20) is not needed. -/
theorem winnability_theorem_of_fixed_domain_and_bounded
    [Fintype X] {G : PFunPDS X (Y × Bool)} {D : Set (List X)} {q : ℕ}
    (hG : G.NonNeg)
    (hdomain : PFunPDS.HasFixedDomain G D) (hbounded : QBounded D q) :
    supWinProb G = infWinnability G ∧
      ∃ G' : PFunPDS X (Y × Bool), G'.NonNeg ∧ Equivalent G' G ∧
        G'.mass PFunDDS.Winnable = supWinProb G := by
  -- the never-won twin shares the fixed domain
  have htwin : PFunPDS.HasFixedDomain (zeroMBODist G) D := by
    intro v hv
    obtain ⟨g, hg, rfl⟩ := Dist.mem_support_fTransform _ _ hv
    rw [PFunDDS.dom_zeroMBO]
    exact hdomain g hg
  -- Theorem 2.31 attainment against the twin
  obtain ⟨G', V', hG'nn, hV'nn, hG', hV', -, -, hδadv⟩ :=
    exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded
      (S := G) (T := zeroMBODist G) hG (hG.fTransform _)
      ⟨hdomain, htwin, hbounded⟩
  -- the attained representative's winnable mass is at most ν
  have htwinzero : V'.mass PFunDDS.Winnable = 0 :=
    mass_winnable_eq_zero_of_equivalent_zeroMBODist hV'nn hV'
  have hmass_le : G'.mass PFunDDS.Winnable ≤ supWinProb G := by
    have hgap := mass_sub_mass_le_δ G' hV'nn PFunDDS.Winnable
    rw [htwinzero] at hgap
    calc G'.mass PFunDDS.Winnable
        = G'.mass PFunDDS.Winnable - 0 := (sub_zero _).symm
      _ ≤ δ G' V' := hgap
      _ = Adv G (zeroMBODist G) := hδadv
      _ ≤ supWinProb G := adv_zeroMBODist_le_supWinProb hG
  -- assemble the sandwich ν ≤ ω ≤ mass(G') ≤ ν
  have hν_le_ω : supWinProb G ≤ infWinnability G :=
    supWinProb_le_infWinnability hG
  have hω_le_mass : infWinnability G ≤ G'.mass PFunDDS.Winnable :=
    csInf_le (bddBelow_infWinnability_set G)
      ⟨G', ⟨hG'nn, gameEquivalent_of_equivalent hG'⟩, rfl⟩
  exact ⟨le_antisymm hν_le_ω (hω_le_mass.trans hmass_le), G', hG'nn, hG',
    le_antisymm hmass_le (hν_le_ω.trans hω_le_mass)⟩

/-! ### CR18 reconciliation: `Γ` (Def 4.17) states the thesis's `ν` (Def 2.25)

The repository's game-performance layer (`WinProb.lean` / `MaxWinProb.lean`)
is labelled from CR18.  The two suprema have different shapes — `Γ` ranges
over probability-distribution winners of the *unbounded* winning predicate
`winsDDS`, `ν` over deterministic environments and fixed round counts — but
they are equal: `winProb` is affine in the winner (so deterministic winners
suffice, the thesis's own remark under Def 2.24), and a finite-support game
admits a uniform round bound (so the `∃ n` inside `winsDDS` is realized at a
single `n`). -/

/-- CR18 Definition 4.5 unfolded: the winning probability is the
winner-weighted sum of per-winner winning masses. -/
theorem winProb_eq_sum_mass (W : Dist (Winner X Y)) (G : PFunPDS X (Y × Bool)) :
    winProb W G = W.sum fun w wp => wp * G.mass (winsDDS w) := by
  unfold winProb GamePerf.winProb Dist.mass
  refine Finsupp.sum_congr fun w _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  split_ifs with hwin <;> ring

/-- A deterministic (Dirac) winner's winning probability is its winning
mass. -/
theorem winProb_single_eq_mass (w : Winner X Y) (G : PFunPDS X (Y × Bool)) :
    winProb (Finsupp.single w 1) G = G.mass (winsDDS w) := by
  rw [winProb_eq_sum_mass,
    Finsupp.sum_single_index (by rw [zero_mul]), one_mul]

/-- The Dirac winner is a probability distribution. -/
theorem isProbDist_single_one (w : Winner X Y) :
    Dist.isProbDist (Finsupp.single w 1 : Dist (Winner X Y)) := by
  classical
  refine ⟨fun w' => ?_, ?_⟩
  · rw [Finsupp.single_apply]
    split <;> norm_num
  · rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]

/-- **Uniform round bound on a finite support**: a fixed winner's unbounded
winning event (`winsDDS`, an `∃` over rounds) is realized at one round count
`N` across the whole support — the winning mass is a `winningMass`. -/
theorem exists_mass_winsDDS_eq_winningMass (G : PFunPDS X (Y × Bool))
    (w : Winner X Y) :
    ∃ N : ℕ, G.mass (winsDDS w) = winningMass G (winnerView w) N := by
  classical
  refine ⟨G.support.sup fun g =>
    if hwin : winsDDS w g then hwin.choose else 0, ?_⟩
  refine mass_congr_support G fun g hg => ?_
  constructor
  · intro hwin
    have hle : hwin.choose ≤ G.support.sup fun g' =>
        if hwin' : winsDDS w g' then hwin'.choose else 0 := by
      calc hwin.choose
          = if hwin' : winsDDS w g then hwin'.choose else 0 :=
            (dif_pos hwin).symm
        _ ≤ _ := Finset.le_sup
            (f := fun g' => if hwin' : winsDDS w g' then hwin'.choose else 0)
            hg
    exact winningTranscript_mono
      (transcript_prefix_of_le g (winnerView w) hle) hwin.choose_spec
  · rintro ⟨y, hy⟩
    exact ⟨_, y, hy⟩

/-- **CR18 Definition 4.17 = thesis Definition 2.25**: the maximal winning
probability `Γ(G)` (supremum over probability-distribution winners) equals the
supremum winning probability `ν(G)` (supremum over deterministic environments
and round counts).  `≤` is affinity of `winProb` in the winner plus the
uniform round bound; `≥` is the Dirac winner.  This is the named
reconciliation between the repository's CR18-shaped game-performance layer
and the thesis's game definitions. -/
theorem maxWinProb_eq_supWinProb {G : PFunPDS X (Y × Bool)} (hG : G.NonNeg) :
    maxWinProb G = supWinProb G := by
  refine le_antisymm ?_ ?_
  · refine csSup_le
      ⟨_, ⟨Finsupp.single (fun _ => none : Winner X Y) 1,
        isProbDist_single_one _, rfl⟩⟩ ?_
    rintro a ⟨W, hW, rfl⟩
    show winProb W G ≤ supWinProb G
    rw [winProb_eq_sum_mass]
    have hterm : ∀ w ∈ W.support,
        W w * G.mass (winsDDS w) ≤ W w * supWinProb G := by
      intro w _
      have hfactor : G.mass (winsDDS w) ≤ supWinProb G := by
        obtain ⟨N, hN⟩ := exists_mass_winsDDS_eq_winningMass G w
        rw [hN]
        exact winningMass_winnerView_le_supWinProb hG w N
      exact mul_le_mul_of_nonneg_left hfactor (hW.1 w)
    calc W.sum (fun w wp => wp * G.mass (winsDDS w))
        ≤ W.sum fun w wp => wp * supWinProb G :=
          Finsupp.sum_le_sum hterm
      _ = W.weight * supWinProb G := by
          rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_mul]
      _ = supWinProb G := by rw [hW.2, one_mul]
  · refine csSup_le (supWinProb_set_nonempty G) ?_
    rintro a ⟨w, n, rfl⟩
    have hmono : winningMass G (winnerView w) n ≤ G.mass (winsDDS w) :=
      mass_mono hG fun g hg => hg.elim fun y hy => ⟨n, y, hy⟩
    rw [← winProb_single_eq_mass] at hmono
    exact hmono.trans
      (winProb_le_maxWinProb (Finsupp.single w 1) G (isProbDist_single_one w))

end RandomSystems.CR18
