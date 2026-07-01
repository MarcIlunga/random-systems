/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.WinProb

/-!
# CR18 §4.10.2 — Distinguishing `(X, Y)`-systems

A **distinguisher** `D` (Def 3.24, `PFunDDS.DDD`) is connected to a system `S` and emits a final output
**bit `Z`** when it stops. The raw `DDD` type enforces finality of the verdict, not a fixed query count;
CR18 §4.10.1 then analyzes a fixed finite upper bound `q` and pads stopped distinguishers with dummy
queries for that analysis. CR18 §4.10.2 fixes:

* the **verdict probability** `Pr^{DS}(Z = 1)` — the probability `D` outputs `1` against `S`;
* the **distinguishing advantage** `∆^D(S,T) = ⟨S|T⟩(D) = Pr^{DT}(Z=1) − Pr^{DS}(Z=1)` (Def 4.1) — the
  *signed* advantage of `D` between `S` and `T` (Maurer keeps the sign; the literature's absolute value
  is a derived notion), hence `ℝ`-valued;
* the **maximal distinguishing advantage** `∆(S,T) := sup_D ∆^D(S,T)`.

Everything is **pure reuse**: the verdict (`Z = 1`) is `PFunDDS.verdict` (Def 3.24, an `∃` over the run,
exactly like `Wins`), so `Pr^{DS}(Z=1)` is `GamePerf.winProb` at `verdict`, and `∆` is — faithful to the
topic — *literally a supremum*, the signed analog of `Γ` (Def 4.17). No new probability machinery.

The query bound is **not** baked into `∆`: as for `Γ`, the `q`-query advantage is `∆([q]S, [q]T)` via the
filter `[q]` (`PFunPDS.filterQueries`, §3.4.3). The missing generic bridge is CR18 §4.10.1's WLOG
normalization: for filtered systems, any raw distinguisher can be collapsed to a finite/exact-query
distinguisher by simulating dummy post-stop/post-filter replies internally. The per-`D` Lemma-4.16 and
Theorem-4.17 chain already consumes that normalized form via `QueriesExactly`; this module's raw
`maxAdvantage` has not yet internalized the normalization.

Thesis reconciliation: Lanzenberger's 2023 thesis treats random systems as equivalence classes of PDS
representatives and proves the static distance `A(S,T)` equals adaptive `Adv(S,T)`. This file still
defines the CR18 representative-level supremum over `PFunPDS` representatives. The intended upstream
closure is a `PFunPDS` analogue of the older fixed-query `RandomSystems.Advantage` /
`RandomSystems.AdvantageEquiv` layer: prove this `∆` respects behavior/equivalence where needed, and
relate it to the thesis-style `Adv`/`A` view rather than adding theorem-specific hypotheses.

This file stops at §4.10.2; relating game winning and distinguishing (§4.10.3, Def 4.18 `S⁻`, the
`(4.35)`-analog transcript factorization, Lemma 4.15) is next.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-- The deterministic distinguisher that immediately stops with verdict bit `0`.

This is the canonical inhabitedness witness for supremums over probabilistic
distinguishers; it is not a protocol step. -/
def PFunDDS.rejectDDD (X : Type u) (Y : Type v) : PFunDDS.DDD X Y :=
  ⟨fun _ => Sum.inr false, by
    intro _ _ _ _ hb
    exact hb⟩

/-- The point mass on `PFunDDS.rejectDDD`. -/
noncomputable def rejectDistinguisher (X : Type u) (Y : Type v) :
    Dist (PFunDDS.DDD X Y) :=
  Finsupp.single (PFunDDS.rejectDDD X Y) 1

/-- `rejectDistinguisher` is a probability distribution. -/
theorem rejectDistinguisher_isProbDist (X : Type u) (Y : Type v) :
    (rejectDistinguisher X Y).isProbDist := by
  show Dist.weight (Finsupp.single (PFunDDS.rejectDDD X Y) (1 : NNReal)) = 1
  rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]

/-- **CR18 §4.10.2 — the verdict probability `Pr^{DS}(Z = 1)`**: the probability that distinguisher `D`
outputs `1` (verdict bit true, `PFunDDS.verdict`, Def 3.24) against the probabilistic system `S`. Pure
reuse of `GamePerf.winProb` at the `verdict` predicate — the distinguishing analog of `winProb`. -/
noncomputable def verdictProb (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y) : NNReal :=
  GamePerf.winProb PFunDDS.verdict D S

/-- **CR18 Definition 4.1 / §4.10.2 — the distinguishing advantage `∆^D(S,T) = ⟨S|T⟩(D)`**: the
*signed* advantage of distinguisher `D` between `S` and `T`,
`Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`. Signed (`ℝ`), faithful to Maurer (no absolute value). -/
noncomputable def advantage (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y) : ℝ :=
  (verdictProb D T : ℝ) - (verdictProb D S : ℝ)

/-- The advantage of a probability-distribution distinguisher is bounded above by `T`'s mass
(`Pr^{DT}(Z=1) ≤ T.weight`, `Pr^{DS}(Z=1) ≥ 0`), so the defining set of `∆(S,T)` is bounded — `∆` is a
genuine supremum, not a junk `sSup`. -/
theorem bddAbove_advantage_image (S T : PFunPDS X Y) :
    BddAbove ((fun D : Dist (PFunDDS.DDD X Y) => advantage D S T) '' {D | D.isProbDist}) := by
  refine ⟨(T.weight : ℝ), ?_⟩
  rintro x ⟨D, hD, rfl⟩
  have h1 : verdictProb D T ≤ T.weight := GamePerf.winProb_le_weight PFunDDS.verdict D T hD
  have h1' : (verdictProb D T : ℝ) ≤ (T.weight : ℝ) := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ (verdictProb D S : ℝ) := by positivity
  unfold advantage
  linarith

/-- **CR18 §4.10.2 — the maximal distinguishing advantage `∆(S,T) := sup_D ∆^D(S,T)`** — the raw
representative-level supremum over all **probability-distribution** distinguishers `D` (the restriction
is essential, exactly as for `Γ`). The signed-`sup` analog of `Γ` (Def 4.17).

This is intentionally the broad CR18 notation. Proofs that invoke the fixed-query transcript algebra
must first pass through the generic §4.10.1 normalization/padding bridge; do not add `QueriesExactly`
or totality hypotheses to paper-facing protocol statements just to use the lower-level lemmas. -/
noncomputable def maxAdvantage (S T : PFunPDS X Y) : ℝ :=
  sSup ((fun D : Dist (PFunDDS.DDD X Y) => advantage D S T) '' {D | D.isProbDist})

@[inherit_doc maxAdvantage] scoped notation:max "Δ(" S ", " T ")" => maxAdvantage S T

/-- The defining set for `∆(S,T)` is nonempty: it contains the immediate-reject
distinguisher. This is the reusable `sSup` inhabitedness fact for `maxAdvantage`. -/
theorem advantage_image_nonempty (S T : PFunPDS X Y) :
    ((fun D : Dist (PFunDDS.DDD X Y) => advantage D S T) '' {D | D.isProbDist}).Nonempty := by
  exact ⟨advantage (rejectDistinguisher X Y) S T,
    ⟨rejectDistinguisher X Y, rejectDistinguisher_isProbDist X Y, rfl⟩⟩

/-- **Maurer's overlined angle-bracket notation `〈S | T〉` for the maximal distinguishing advantage**
(CR18 §4.10.2): the *best-distinguisher* advantage, i.e. the same object as `Δ(S, T) = maxAdvantage S T`.
The **plain** bracket `〈S | T〉(D)` is the per-distinguisher `advantage D S T`; the **bar on top** denotes
the supremum over `D`. So `〈S | T〉` and `Δ(S, T)` are two notations for one definition. (The angle
brackets are `〈〉` (U+3008/9), not the `⟨⟩` reserved by Lean's anonymous-constructor syntax — same
reason `⌈q⌉` stands in for Maurer's `[q]`.) -/
scoped notation:max "〈" S " | " T "〉" => maxAdvantage S T

/-- **CR18 §4.10.2**: `∆^D(S,T) ≤ ∆(S,T)` — every probability-distribution distinguisher's advantage is
a lower bound on the maximal distinguishing advantage. -/
theorem advantage_le_maxAdvantage (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hD : D.isProbDist) : advantage D S T ≤ Δ(S, T) :=
  le_csSup (bddAbove_advantage_image S T) ⟨D, hD, rfl⟩

/-- Identical systems have nonpositive maximal signed distinguishing advantage. -/
theorem maxAdvantage_self_le_zero (S : PFunPDS X Y) :
    Δ(S, S) ≤ 0 := by
  unfold maxAdvantage
  refine csSup_le ?_ ?_
  · exact advantage_image_nonempty S S
  · rintro b ⟨D, _hD, rfl⟩
    simp [advantage]

end RandomSystems.CR18
