/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Lemma415
import RandomSystems.Distinguishing
import RandomSystems.SystemMBO

/-!
# CR18 §4.10.3 — Relating game winning and distinguishing (towards Lemma 4.16)

We build the three pieces behind Lemma 4.16 (`S ≡ᵍ T ⟹ ⟨S⁻|T⁻⟩ ≤ S`):

(a) **Definition 4.18, `S⁻`** — canonically defined in `SystemMBO.lean` as the `(X, Y)`-system obtained
    from a game `S` by ignoring the MBO — and the **transcript-projection identity**: a distinguisher's
    run against `S⁻` is exactly the `Y`-projection of the `winnerView`-run against the game `S`. This is
    what lets `Z` (the verdict) and `Aᵢ` (the MBO) be analyzed in one experiment.

This file: the projection lemmas and Lemma-4.16 assembly built on part (a). The legacy name
`ignoreMBO` remains as a compatibility spelling for canonical `stripMBO` / `S⁻`.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

namespace PFunDDS

/-! ### CR18 Definition 4.18 — compatibility spelling for the MBO-ignoring system `S⁻` -/

/-- **Compatibility spelling for CR18 Definition 4.18.** The canonical operation is
`PFunDDS.stripMBO`, with paper notation `S⁻` from `SystemMBO.lean`. Existing Lemma-4.16/Theorem-4.17
proofs historically used the name `ignoreMBO`; keep it as an abbreviation so there is only one
definition of the operation. -/
abbrev ignoreMBO (S : DDS X (Y × Bool)) : DDS X Y :=
  stripMBO S

@[inherit_doc ignoreMBO] scoped postfix:max "⁻ᴹ" => ignoreMBO

@[simp] theorem dom_ignoreMBO (S : DDS X (Y × Bool)) : dom (ignoreMBO S) = dom S := rfl

theorem output_ignoreMBO (S : DDS X (Y × Bool)) (l : List X) (h : l ∈ dom (ignoreMBO S)) :
    output (ignoreMBO S) l h = (output S l h).1 := rfl

theorem keptPrefix_ignoreMBO (S : DDS X (Y × Bool)) :
    keptPrefix (ignoreMBO S) = keptPrefix S := rfl

/-- `S⁻`'s fully-defined completion is the `Y`-projection of `S`'s — its output is `S⊥`'s output with
the MBO mapped away. The step-level bridge for the transcript projection below. -/
theorem output_fullyDefined_ignoreMBO (S : DDS X (Y × Bool)) (l : List X)
    (h : l ∈ dom ((ignoreMBO S)⊥)) (h' : l ∈ dom (S⊥)) :
    output ((ignoreMBO S)⊥) l h = Option.map Prod.fst (output (S⊥) l h') := by
  have hl : l ≠ [] := by have hh := h; rw [dom_fullyDefined] at hh; exact hh
  rw [output_fullyDefined, output_fullyDefined, keptPrefix_ignoreMBO]
  simp only [dom_ignoreMBO]
  by_cases hc : keptPrefix S l.dropLast ++ [l.getLast hl] ∈ dom S
  · rw [dif_pos hc, dif_pos hc, output_ignoreMBO]; rfl
  · rw [dif_neg hc, dif_neg hc]; rfl

/-! ### The transcript-projection identity -/

/-- The `Y`-projection of a game transcript prefix: drop the MBO bit from each output. -/
def projT (t : List (X × Option (Y × Bool))) : List (X × Option Y) :=
  t.map (fun p => (p.1, p.2.map Prod.fst))

@[simp] theorem projT_nil : projT ([] : List (X × Option (Y × Bool))) = [] := rfl

@[simp] theorem projT_append (t : List (X × Option (Y × Bool))) (p : X × Option (Y × Bool)) :
    projT (t ++ [p]) = projT t ++ [(p.1, p.2.map Prod.fst)] := by simp [projT]

@[simp] theorem projT_inputs (t : List (X × Option (Y × Bool))) : (projT t)↓ₓ = t↓ₓ := by
  simp [projT, transcriptInputs, List.map_map, Function.comp]

@[simp] theorem projT_outputs (t : List (X × Option (Y × Bool))) :
    (projT t)↓ᵧ = (t↓ᵧ).map (Option.map Prod.fst) := by
  simp [projT, transcriptOutputs, List.map_map, Function.comp]

/-- **The transcript-projection identity (CR18 §4.10.3).** A distinguisher-style environment `e`
interacting with `S⁻` produces exactly the `Y`-projection of `e`'s `winnerView` interacting with the
game `S`. So the verdict (`Z`) read against `S⁻` and the MBO (`Aᵢ`) of the game `S` live in *one* run. -/
theorem transcript_ignoreMBO (S : DDS X (Y × Bool)) (e : DDE X Y) (n : ℕ) :
    transcript (ignoreMBO S) e n = projT (transcript S (winnerView e) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      -- the two runs fire/stall together: the projected outputs feed `e` exactly as `winnerView e`
      have hview : e (transcript (ignoreMBO S) e n)↓ᵧ
          = winnerView e (transcript S (winnerView e) n)↓ᵧ := by
        rw [ih, projT_outputs]; rfl
      rcases hfire : winnerView e (transcript S (winnerView e) n)↓ᵧ with _ | x
      · rw [transcript_succ_stall (by rw [hview, hfire]), transcript_succ_stall hfire, ih]
      · rw [transcript_succ_fire (by rw [hview, hfire]), transcript_succ_fire hfire, ih,
          projT_append, projT_inputs]
        refine congrArg (fun z => projT (transcript S (winnerView e) n) ++ [(x, z)]) ?_
        exact output_fullyDefined_ignoreMBO S _ _ _

/-- The verdict of `D` against `S⁻` reads exactly the `Y`-projection of `D`-as-winner's run against the
game `S` (corollary of `transcript_ignoreMBO`). Connects the §4.10.2 verdict to the game experiment. -/
theorem verdict_ignoreMBO (d : DDD X Y) (S : DDS X (Y × Bool)) :
    verdict d (ignoreMBO S) ↔
      ∃ n, d.val ((projT (transcript S (winnerView (ddToDDE d)) n))↓ᵧ) = Sum.inr true := by
  unfold verdict
  simp only [transcript_ignoreMBO]

end PFunDDS

/-! ### (b) `Pr(Aq=1) = winning` — the distinguisher's winning probability -/

open scoped Classical in
/-- **Winner pushforward of `winProb`** (UPSTREAM-CANDIDATE, generic): reindexing the winner along
`f` and then taking the winning probability equals using the composed predicate `win ∘ f` on the
original winner distribution. `Pr` over the pushed-forward winners = `Pr` over the originals. -/
theorem winProb_fTransform {Winner Winner' Game : Type*} (win : Winner' → Game → Prop)
    (f : Winner → Winner') (W : Dist Winner) (G : Dist Game) :
    GamePerf.winProb win (Dist.fTransform f W) G
      = GamePerf.winProb (fun w => win (f w)) W G := by
  unfold GamePerf.winProb
  rw [show Dist.fTransform f W = Finsupp.mapDomain f W from rfl,
    Finsupp.sum_mapDomain_index (h := fun w wp => G.sum fun g gp => wp * gp * if win w g then 1 else 0)]
  · intro b; simp
  · intro b m₁ m₂
    rw [← Finsupp.sum_add]
    exact Finsupp.sum_congr fun g _ => by ring

open scoped Classical in
/-- **Game pushforward of `winProb`** (UPSTREAM-CANDIDATE, generic): reindexing the *game* along `f`.
The dual of `winProb_fTransform`; used to push `verdictProb` through `ignoreMBO`. -/
theorem winProb_fTransform_game {Winner Game Game' : Type*} (win : Winner → Game' → Prop)
    (f : Game → Game') (W : Dist Winner) (G : Dist Game) :
    GamePerf.winProb win W (Dist.fTransform f G)
      = GamePerf.winProb (fun w g => win w (f g)) W G := by
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun w _ => ?_
  rw [show Dist.fTransform f G = Finsupp.mapDomain f G from rfl,
    Finsupp.sum_mapDomain_index (h := fun g gp => W w * gp * if win w g then 1 else 0)]
  · intro b; simp
  · intro b m₁ m₂; ring

/-- **CR18 §4.10.3 step 6 — `Pr^{DG}(Aq=1) = G(D)`**: the probability that distinguisher `D`, viewed as
a winner via `ddToDDE`, wins game `G` (its MBO reaches `1`) equals the winning probability of `D`'s
winner-image. `Pr(Aq=1)` over the joint `(d, g)` experiment *is* the winning probability. -/
theorem winProb_ddToDDE (D : Dist (PFunDDS.DDD X Y)) (G : PFunPDS X (Y × Bool)) :
    winProb (Dist.fTransform PFunDDS.ddToDDE D) G
      = GamePerf.winProb (fun d g => winsDDS (PFunDDS.ddToDDE d) g) D G :=
  winProb_fTransform winsDDS PFunDDS.ddToDDE D G

/-! ### (c) The verdict-weighted `Aq=0` cancellation — immediate on the behavior primitive -/

/-- The verdict event as a function of `D` and the visible transcript `yⁱ`. On an `Aq=0` run every
output is `some (yᵢ, false)`, so the verdict reads `yⁱ` tagged with `some`: `D` outputs `1` at some
round `n ≤ i+1`. (`p^D_{Z|XⁱYⁱ}(1, ·)` — a `D`-and-`yⁱ` predicate, independent of the game.) -/
def verdictMatches (d : PFunDDS.DDD X Y) (i : ℕ) (ys : Vector Y (i + 1)) : Prop :=
  ∃ n, n ≤ i + 1 ∧ d.val ((ys.toList.take n).map some) = Sum.inr true

/-- **Behavior-side `Pr^{DG}(Z=1 ∧ Aq=0)`** (CR18 §4.10.2, the `(4.35)`-analog transcript sum): sum over
transcripts of `[D produces xⁱ as a winner and verdicts 1 on yⁱ] · p^G_{Yⁱ,Aᵢ=0|Xⁱ}`. The game `G`
enters **only** through `massYAfalse G` — exactly as `winProbBehavior` for game winning. -/
noncomputable def distNotWonZ1 (D : Dist (PFunDDS.DDD X Y)) (G : PFunPDS X (Y × Bool)) (i : ℕ) :
    ℝ :=
  ∑' p : Vector X (i + 1) × Vector Y (i + 1),
    Dist.mass D (fun d => winnerMatches (PFunDDS.ddToDDE d) i p.1 p.2 ∧ verdictMatches d i p.2)
      * CondEquiv.massYAfalse G i p.2 p.1

/-- **CR18 Lemma 4.16, step 3 — the `Aq=0` cancellation.** `S ≡ᵍ T ⟹ Pr^{DS}(Z=1∧Aq=0) =
Pr^{DT}(Z=1∧Aq=0)`. *Immediate* on the behavior primitive: `G` enters only through `massYAfalse G`, so
the pre-winning congruence (piece A) substituted termwise under the `tsum` finishes — the Lemma 4.15
argument, now verdict-weighted. "Replacing `S` by `T` leaves all terms unchanged." -/
theorem distNotWonZ1_congr_gameEquiv (D : Dist (PFunDDS.DDD X Y))
    {S T : PFunPDS X (Y × Bool)} (hS : S.isProbDist) (hT : T.isProbDist)
    (hST : S ≡ᵍ T) (i : ℕ) : distNotWonZ1 D S i = distNotWonZ1 D T i := by
  unfold distNotWonZ1
  refine tsum_congr fun p => ?_
  rw [massYAfalse_congr_gameEquiv hS hT hST p.2 p.1]

/-! ### Lemma 4.16 — assembly (copying the PDF proof chain)

`⟨S⁻|T⁻⟩(D) = Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`
`            = [Pr^{DT}(Z1∧Aq0)+Pr^{DT}(Z1∧Aq1)] − [Pr^{DS}(Z1∧Aq0)+Pr^{DS}(Z1∧Aq1)]`  (split Aq)
`            = Pr^{DT}(Z1∧Aq1) − Pr^{DS}(Z1∧Aq1)`                                       (Aq0 cancels — (c))
`            ≤ Pr^{DT}(Z1∧Aq1) ≤ Pr^{DT}(Aq1)`                                          (drop ≥0; Z1∧Aq1⊆Aq1)
`            = T(D) = S(D).`                                                            ((b); Lemma 4.15) -/

/-- **Compatibility spelling for `S⁻` at the probabilistic level**: the canonical operation is
`PFunPDS.stripMBO`; this abbreviation keeps existing proof names stable while avoiding a second Def-4.18
implementation. -/
noncomputable abbrev PFunPDS.ignoreMBO (G : PFunPDS X (Y × Bool)) : PFunPDS X Y :=
  PFunPDS.stripMBO G

/-- Stripping the MBO commutes with a prefix-closed domain restriction: both
operations are deterministic pushforwards, and their DDS maps commute. -/
theorem PFunPDS.ignoreMBO_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (G : PFunPDS X (Y × Bool)) :
    PFunPDS.ignoreMBO (PFunPDS.filterDom P hP G) =
      PFunPDS.filterDom P hP (PFunPDS.ignoreMBO G) := by
  unfold PFunPDS.ignoreMBO PFunPDS.stripMBO PFunPDS.filterDom
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  congr 1

/-- Stripping the MBO commutes with the query filter
(`stripMBO ∘ [q] = [q] ∘ stripMBO`). -/
theorem PFunPDS.ignoreMBO_filterQueries (q : ℕ) (G : PFunPDS X (Y × Bool)) :
    PFunPDS.ignoreMBO (⌈q⌉ G) = ⌈q⌉ (PFunPDS.ignoreMBO G) := by
  exact PFunPDS.ignoreMBO_filterDom (fun xs => xs.length ≤ q)
    (prefixClosed_length_le q) G

/-! ### Generic mass facts (UPSTREAM-CANDIDATE) -/

open scoped Classical in
/-- Split a mass by a side predicate `Q`: `mass P = mass (P ∧ Q) + mass (P ∧ ¬Q)`. -/
theorem mass_split {A : Type*} (X : Dist A) (P Q : A → Prop) :
    X.mass P = X.mass (fun a => P a ∧ Q a) + X.mass (fun a => P a ∧ ¬ Q a) := by
  rw [Dist.mass, Dist.mass, Dist.mass, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun a _ => ?_
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

open scoped Classical in
/-- Monotonicity of mass under implication (for a non-negative law). -/
theorem mass_mono {A : Type*} {X : Dist A} (hX : X.NonNeg) {P Q : A → Prop}
    (h : ∀ a, P a → Q a) :
    X.mass P ≤ X.mass Q :=
  Dist.mass_mono hX h

/-! ### CR18 Lemma 4.16 — algebraic assembly helper (`_abstract`)

NOTE (MODELING_REVIEW #5 / fix F1.5): this is **not** the paper-facing Lemma 4.16. It is the algebraic
**assembly** scaffold that takes the central content of the proof — the verdict-as-mass wiring
(`hadvS`/`hadvT`), the operational `Aq=0` cancellation (`hcancel`), part (b) (`hWeq`), and the Lemma-4.15
equality (`h415`) — **as hypotheses**, then assembles Maurer's chain into the bound. The paper-facing
public Lemma 4.16 is `advantage_le_winProb_of_gameEquiv` below, which takes only game systems + game equivalence `S ≡ᵍ T` and
**discharges** all four obligations internally. The `_abstract` suffix marks this non-endpoint helper role;
it is kept (proof unchanged) because the mass-variant `advantage_le_winProb_of_massYAfalseEq` (Theorem417.lean) reuses
the same assembly with the cancellation discharged from `MassYAfalseEq` instead of `≡ᵍ`.

The advantage `⟨S⁻|T⁻⟩(D)` and the winning probability `S(D)` are the actual `advantage`/`winProb`. The
proof is Maurer's chain. The remaining obligations are stated **explicitly** as hypotheses over
the real objects — not as abstract reals — so nothing is hidden:
* `hadvS`/`hadvT` — the verdict probability against `S⁻` equals the `Z=1` mass over the game run
  (`(a)` + `winProb` game-pushforward + `P0`); *the wiring*.
* `hcancel` — the operational `Aq=0` cancellation (`(c)` lifted operationally — the one substantive
  bridge, analog of `winProb_eq_behavior`).
* `hWeq` — `Pr^{DT}(Aq=1) = T(D)` over the product (`(b)`, `winProb_ddToDDE` + `P0`).
* `h415` — `T(D) = S(D)` (Lemma 4.15 operational). -/
theorem advantage_le_winProb_assemble (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool))
    (hDnn : D.NonNeg) (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (hadvS : verdictProb D (PFunPDS.ignoreMBO S)
      = (Dist.prod D S).mass (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2)))
    (hadvT : verdictProb D (PFunPDS.ignoreMBO T)
      = (Dist.prod D T).mass (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2)))
    (hcancel : (Dist.prod D T).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2)
      = (Dist.prod D S).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2))
    (hWeq : (Dist.prod D T).mass (fun dg => winsDDS (PFunDDS.ddToDDE dg.1) dg.2)
      = winProb (Dist.fTransform PFunDDS.ddToDDE D) T)
    (h415 : winProb (Dist.fTransform PFunDDS.ddToDDE D) T
      = winProb (Dist.fTransform PFunDDS.ddToDDE D) S) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ) := by
  classical
  -- abbreviations for the verdict / won predicates on the game run
  set V : PFunDDS.DDD X Y × PFunDDS.DDS X (Y × Bool) → Prop :=
    fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) with hV
  set A1 : PFunDDS.DDD X Y × PFunDDS.DDS X (Y × Bool) → Prop :=
    fun dg => winsDDS (PFunDDS.ddToDDE dg.1) dg.2 with hA1
  -- split `Pr(Z=1)` by `Aq` for both `T` and `S`
  have hsplitT := mass_split (Dist.prod D T) V A1
  have hsplitS := mass_split (Dist.prod D S) V A1
  -- the `Z1∧Aq1 ⊆ Aq1` bound
  have hmonoT : (Dist.prod D T).mass (fun dg => V dg ∧ A1 dg)
      ≤ (Dist.prod D T).mass A1 := mass_mono (hDnn.prod hTnn) fun _ h => h.2
  -- assemble (the chain, as reals)
  have key : advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T)
      = ((Dist.prod D T).mass (fun dg => V dg ∧ A1 dg) : ℝ)
        - ((Dist.prod D S).mass (fun dg => V dg ∧ A1 dg) : ℝ) := by
    unfold advantage
    rw [hadvT, hadvS, hsplitT, hsplitS]
    linarith [hcancel]
  rw [key]
  have h0 : (0 : ℝ) ≤ ((Dist.prod D S).mass (fun dg => V dg ∧ A1 dg) : ℝ) :=
    (hDnn.prod hSnn).mass_nonneg _
  have hmonoT' : ((Dist.prod D T).mass (fun dg => V dg ∧ A1 dg) : ℝ)
      ≤ ((Dist.prod D T).mass A1 : ℝ) := by exact_mod_cast hmonoT
  have hWeq' : ((Dist.prod D T).mass A1 : ℝ)
      = (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ) := by
    exact_mod_cast hWeq.trans h415
  linarith [hmonoT', hWeq'.le, hWeq'.ge]

/-! ### The operational `Aq=0` cancellation, proven (the verdict version of `notWonProb_eq_fiber`) -/

open PFunDDS in
/-- The `Y`-projected verdict-visible outputs of the *forced* run reaching `(xⁱ,yⁱ)`: at round `m` they
are `yⁱ.take (min m (i+1))` tagged with `some`. From `run_proj` (`Aq=0` run outputs) + `projT` + freeze. -/
theorem projT_run_outputs {d : DDD X Y} {g : DDS X (Y × Bool)} {i : ℕ}
    {xs : Vector X (i + 1)} {ys : Vector Y (i + 1)}
    (hWM : winnerMatches (ddToDDE d) i xs ys) (hGM : gameMatches g i ys xs)
    (hstop : winnerView (ddToDDE d) (transcript g (winnerView (ddToDDE d)) (i + 1))↓ᵧ = none) (m : ℕ) :
    (projT (transcript g (winnerView (ddToDDE d)) m))↓ᵧ = (ys.toList.take (min m (i + 1))).map some := by
  rw [projT_outputs]
  rcases Nat.lt_or_ge m (i + 1) with hm | hm
  · rw [min_eq_left (le_of_lt hm), (run_proj (ddToDDE d) g i xs ys hWM hGM (le_of_lt hm)).2,
      List.map_map]
    rfl
  · rw [min_eq_right hm, transcript_freeze hstop hm,
      (run_proj (ddToDDE d) g i xs ys hWM hGM (le_refl (i + 1))).2, List.map_map]
    rfl

open PFunDDS in
/-- On a forced `Aq=0` run, `D`'s verdict against `S⁻` *is* `verdictMatches` on the visible transcript
`yⁱ` — `verdict_ignoreMBO` + `projT_run_outputs` (verdict's unbounded `∃n` collapses to `n ≤ i+1`). -/
theorem verdict_iff_verdictMatches {d : DDD X Y} {g : DDS X (Y × Bool)} {i : ℕ}
    {xs : Vector X (i + 1)} {ys : Vector Y (i + 1)}
    (hWM : winnerMatches (ddToDDE d) i xs ys) (hGM : gameMatches g i ys xs)
    (hstop : winnerView (ddToDDE d) (transcript g (winnerView (ddToDDE d)) (i + 1))↓ᵧ = none) :
    verdict d (ignoreMBO g) ↔ verdictMatches d i ys := by
  rw [verdict_ignoreMBO]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨min m (i + 1), min_le_right _ _, by rwa [projT_run_outputs hWM hGM hstop m] at hm⟩
  · rintro ⟨n, hn, hv⟩
    exact ⟨n, by rw [projT_run_outputs hWM hGM hstop n, min_eq_left hn]; exact hv⟩

open PFunDDS in
/-- **The operational `Aq=0` cancellation bridge.** The operational verdict-and-not-won mass equals the
behavior sum `distNotWonZ1` — the verdict version of `notWonProb_eq_fiber`, with the verdict riding the
winner side (`run_proj`/`run_to_matches`/`mass_eq_tsum_of_unique`/`mass_prod_and` reused verbatim, plus
`verdict_iff_verdictMatches`). With it, the cancellation is `distNotWonZ1_congr_gameEquiv`, not a hypothesis. -/
theorem verdictNotWon_eq_distNotWonZ1 (D : Dist (DDD X Y)) (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hG : TotalUpTo G (i + 1)) :
    (Dist.prod D G).mass (fun dg => verdict dg.1 (ignoreMBO dg.2) ∧ ¬ winsDDS (ddToDDE dg.1) dg.2)
      = distNotWonZ1 D G i := by
  rw [mass_eq_tsum_of_unique (Dist.prod D G)
      (fun dg => verdict dg.1 (ignoreMBO dg.2) ∧ ¬ winsDDS (ddToDDE dg.1) dg.2)
      (fun dg (p : Vector X (i + 1) × Vector Y (i + 1)) =>
        (winnerMatches (ddToDDE dg.1) i p.1 p.2 ∧ verdictMatches dg.1 i p.2)
          ∧ gameMatches dg.2 i p.2 p.1) ?hex ?huniq,
    distNotWonZ1]
  · refine tsum_congr fun p => ?_
    rw [Dist.mass_prod_and D G
        (fun d => winnerMatches (ddToDDE d) i p.1 p.2 ∧ verdictMatches d i p.2)
        (fun g => gameMatches g i p.2 p.1), massYAfalse_eq_mass_gameMatches]
  case hex =>
    rintro ⟨d, g⟩ hdg
    have hdmem : d ∈ D.support := by
      have hne : (Dist.prod D G) (d, g) ≠ 0 := Finsupp.mem_support_iff.mp hdg
      rw [Dist.prod_apply] at hne
      exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have hgmem : g ∈ G.support := by
      have hne : (Dist.prod D G) (d, g) ≠ 0 := Finsupp.mem_support_iff.mp hdg
      rw [Dist.prod_apply] at hne
      exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    have hQE := hQ d hdmem
    have hsome : ∀ h : List (Option (Y × Bool)), h.length < i + 1 →
        (winnerView (ddToDDE d) h).isSome := fun h hh => hQE.1 _ (by rwa [List.length_map])
    have hlen : (transcript g (winnerView (ddToDDE d)) (i + 1)).length = i + 1 :=
      transcript_length_eq hsome (le_refl (i + 1))
    have hstop : winnerView (ddToDDE d) (transcript g (winnerView (ddToDDE d)) (i + 1))↓ᵧ = none :=
      hQE.2 _ (by simp [hlen])
    constructor
    · rintro ⟨hverdict, hnwin⟩
      obtain ⟨xs, ys, hWM, hGM⟩ := run_to_matches (ddToDDE d) g i hsome (hG g hgmem) hnwin
      exact ⟨(xs, ys), ⟨hWM, (verdict_iff_verdictMatches hWM hGM hstop).mp hverdict⟩, hGM⟩
    · rintro ⟨⟨px, py⟩, ⟨hWM, hVM⟩, hGM⟩
      refine ⟨(verdict_iff_verdictMatches hWM hGM hstop).mpr hVM, ?_⟩
      rintro ⟨n, y, hmem⟩
      have hmem' : some (y, true)
          ∈ (transcript g (winnerView (ddToDDE d)) (min n (i + 1)))↓ᵧ := by
        rcases Nat.lt_or_ge n (i + 1) with hn | hn
        · rwa [min_eq_left (le_of_lt hn)]
        · rw [min_eq_right hn]; rwa [transcript_freeze hstop hn] at hmem
      rw [(run_proj (ddToDDE d) g i px py hWM hGM (min_le_right n (i + 1))).2] at hmem'
      obtain ⟨y', _, hy'⟩ := List.mem_map.mp hmem'
      exact absurd hy' (by simp)
  case huniq =>
    rintro ⟨d, g⟩ _ ⟨px, py⟩ ⟨px', py'⟩ ⟨⟨hWM, _⟩, hGM⟩ ⟨⟨hWM', _⟩, hGM'⟩
    have e1 := run_proj (ddToDDE d) g i px py hWM hGM (le_refl (i + 1))
    have e2 := run_proj (ddToDDE d) g i px' py' hWM' hGM' (le_refl (i + 1))
    have hxeq : px.toList = px'.toList := by
      have h1 := e1.1; have h2 := e2.1
      rw [List.take_of_length_le (show px.toList.length ≤ i + 1 by simp)] at h1
      rw [List.take_of_length_le (show px'.toList.length ≤ i + 1 by simp)] at h2
      rw [← h1, ← h2]
    have hyeq : py.toList = py'.toList := by
      have h1 := e1.2; have h2 := e2.2
      rw [List.take_of_length_le (show py.toList.length ≤ i + 1 by simp)] at h1
      rw [List.take_of_length_le (show py'.toList.length ≤ i + 1 by simp)] at h2
      have hmap : py.toList.map (fun y => some (y, false))
          = py'.toList.map (fun y => some (y, false)) := by rw [← h1, ← h2]
      exact List.map_injective_iff.mpr (fun a b hab => by simpa using hab) hmap
    exact Prod.ext_iff.mpr ⟨Vector.toList_inj.mp hxeq, Vector.toList_inj.mp hyeq⟩

/-- **CR18 Lemma 4.16 (paper-facing endpoint)** — `S ≡ᵍ T ⟹ ⟨S⁻|T⁻⟩(D) ≤ S(D)`. This is the faithful
public Lemma 4.16 over game systems: its only inputs are the two games `S T`, their game-equivalence
`S ≡ᵍ T`, and Maurer's standing assumptions (probability distributions, the `q`-query bound, game
totality). All four mechanical obligations of the assembly helper `advantage_le_winProb_assemble` are
**discharged here by reuse**, leaving only the one substantive bridge `hcancel` (the operational
`Aq=0` cancellation) which is itself proven (not assumed). `hadvS`/`hadvT` are the
`verdictProb`-as-mass wiring (`winProb_fTransform_game` + `winProb_eq_prod_mass`); `hWeq` is part (b)
(`winProb_ddToDDE` + `winProb_eq_prod_mass`); `h415` is Lemma 4.15 (`winProb_eq_behavior` +
`winProbBehavior_congr_gameEquiv`). -/
theorem advantage_le_winProb_of_gameEquiv (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hDnn : D.NonNeg)
    (hS : S.isProbDist) (hT : T.isProbDist) (hST : S ≡ᵍ T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ) := by
  -- lift the query bound to `ddToDDE`'s winner-image (for Lemma 4.15)
  have hQ' : ∀ w ∈ (Dist.fTransform PFunDDS.ddToDDE D).support, QueriesExactly w (i + 1) := by
    intro w hw; obtain ⟨d, hd, rfl⟩ := mem_support_fTransform _ _ hw; exact hQ d hd
  -- the `Aq=0` cancellation, PROVEN: operational mass = distNotWonZ1, then (c)
  have hcancel : (Dist.prod D T).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2)
      = (Dist.prod D S).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2) := by
    rw [verdictNotWon_eq_distNotWonZ1 D T i hQ hTotT, verdictNotWon_eq_distNotWonZ1 D S i hQ hTotS,
      distNotWonZ1_congr_gameEquiv D hS hT hST i]
  refine advantage_le_winProb_assemble D S T hDnn hS.nonNeg hT.nonNeg ?_ ?_ hcancel ?_ ?_
  · -- hadvS: verdictProb against S⁻ = the Z=1 mass over the game-S run
    unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO
    rw [winProb_fTransform_game, winProb_eq_prod_mass]
  · unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO
    rw [winProb_fTransform_game, winProb_eq_prod_mass]
  · -- hWeq: Pr(Aq=1) over the product = winProb of D-as-winner (part b)
    rw [winProb_ddToDDE, winProb_eq_prod_mass]
  · -- h415: T(D) = S(D), Lemma 4.15 (operational, via the bridge + behavior congruence)
    rw [winProb_eq_behavior _ T i hQ' hTotT, winProb_eq_behavior _ S i hQ' hTotS,
      winProbBehavior_congr_gameEquiv _ hT hS hST.symm i]

/-! ### CR18 Lemma 4.16 — adaptive corollary `⟨S⁻|T⁻⟩(D) ≤ Γ(S)` over game-equivalent systems -/

/-- **CR18 Lemma 4.16, adaptive corollary** (`⟨S⁻|T⁻⟩(D) ≤ Γ(S)`, per distinguisher): for two
already-game-enhanced, game-equivalent systems `S ≡ᵍ T` (paper: `S ≡ T` as games, Def 4.16), the
distinguishing advantage of any `D` between the MBO-ignored systems `S⁻, T⁻` is bounded by the
**maximal game-winning probability** `Γ(S)` (Def 4.17). This is the `hS⁻ | T⁻ i ≤ Γ(S)` statement of
Lemma 4.16 (`papers/CR18_LN.txt:5508-5509`), specialised to the adaptive `Γ(S)` supremum.

NOTE (MODELING_REVIEW #4 / fix F1.4): this is **not** CR18 Theorem 4.17. Theorem 4.17 takes a *base*
`(X,Y)`-system `S`, *constructs* the game-enhancement `Ŝ` from an MBO with `Ŝ |≡ T`, and concludes the
*blind* bound `Δ(S,T) ≤ Γ(bŜ)` (`papers/CR18_LN.txt:5600`). That base-object theorem is
`GameOf.maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf` (fix F1.1). The present lemma takes two enhanced games and `S ≡ᵍ T` directly, so it is a
Lemma-4.16 corollary, hence the name.

*Immediate*: `advantage_le_winProb_of_gameEquiv` bounds the advantage by `D`-as-winner's winning probability, then
`winProb_le_maxWinProb` (`Γ` is the supremum). Faithful, no extra assumptions. -/
theorem advantage_le_maxWinProb_of_gameEquiv
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hST : S ≡ᵍ T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ) ≤ (maxWinProb S : ℝ) := by
  refine (advantage_le_winProb_of_gameEquiv D S T i hD.nonNeg hS hT hST hQ hTotS hTotT).trans ?_
  have hD' : (Dist.fTransform PFunDDS.ddToDDE D).isProbDist := by
    exact Dist.fTransform_isProbDist PFunDDS.ddToDDE hD
  exact_mod_cast winProb_le_maxWinProb (Dist.fTransform PFunDDS.ddToDDE D) S hD'

end RandomSystems.CR18
