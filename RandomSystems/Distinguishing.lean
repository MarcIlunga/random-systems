/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.WinProb
-- The theory-free `CCDiagram` proof-widget engine (abstract-crypto's
-- `CCWidget` lib): importing it here, where `Δ`/`Γ`/`Γᵇ` live,
-- auto-displays goal diagrams in every downstream file — zero ceremony.
import CCWidget

/-! Semantic roles consumed by the shared blackboard renderer.  This is the
RS instantiation registry: carrier-specific application heads elaborate to the
same diagram operations as the abstract resource algebra. -/
cc_diagram_application RandomSystems.CR18.PFunPDS.applyDDC 1 0
cc_diagram_application RandomSystems.CR18.CausalApply.applyG 1 0
cc_diagram_application RandomSystems.CR18.PFunConverter.DDC.apply 1 0
cc_diagram_application RandomSystems.CR18.PFunPDC.apply 1 0
cc_diagram_application RandomSystems.CR18.apply 1 0
cc_diagram_game RandomSystems.CR18.gameOf 1 0
cc_diagram_transparent RandomSystems.CR18.PFunPDS.ofFunDist 0
cc_diagram_attachment RandomSystemsCC.attach 2 1 0
cc_diagram_attachment RandomSystemsCC.memAttach 2 1 0
cc_diagram_attachment RandomSystemsCC.Syn.attach 2 1 0
cc_diagram_attachment RandomSystemsCC.attachP 2 1 0
cc_diagram_attachment RandomSystemsCC.attachPT 2 1 0
cc_diagram_attachment RandomSystemsCC.Syn.attachP 2 1 0
cc_diagram_attachment RandomSystemsCC.Syn.attachPT 2 1 0
cc_diagram_distance RandomSystems.CR18.maxAdvantage 1 0 "Δ"
cc_diagram_distance RandomSystems.statDist 1 0 "δ"
cc_diagram_winning RandomSystems.CR18.maxWinProb 0 "Γ"
cc_diagram_winning RandomSystems.CR18.blindMaxWinProb 0 "Γᵇ"
cc_diagram_conditional RandomSystems.CR18.CondEquiv.CondEquiv 1 0
#cc_diagram_rule_check RandomSystems.CR18.PFunPDS.applyDDC
#cc_diagram_rule_check RandomSystems.CR18.PFunConverter.DDC.apply
#cc_diagram_rule_check RandomSystems.CR18.apply
#cc_diagram_rule_check RandomSystems.CR18.gameOf
#cc_diagram_rule_check RandomSystems.CR18.maxAdvantage
#cc_diagram_rule_check RandomSystems.CR18.CondEquiv.CondEquiv

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
    (rejectDistinguisher X Y).isProbDist :=
  Dist.isProbDist_single (PFunDDS.rejectDDD X Y)

/-- **CR18 §4.10.2 — the verdict probability `Pr^{DS}(Z = 1)`**: the probability that distinguisher `D`
outputs `1` (verdict bit true, `PFunDDS.verdict`, Def 3.24) against the probabilistic system `S`. Pure
reuse of `GamePerf.winProb` at the `verdict` predicate — the distinguishing analog of `winProb`. -/
noncomputable def verdictProb (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y) : ℝ :=
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
  refine ⟨(T.sum fun _ gp => max gp 0) - (S.sum fun _ gp => min gp 0), ?_⟩
  rintro x ⟨D, hD, rfl⟩
  have h1 : verdictProb D T ≤ T.sum fun _ gp => max gp 0 :=
    GamePerf.winProb_le_sum_posPart PFunDDS.verdict D T hD
  have h0 : (S.sum fun _ gp => min gp 0) ≤ verdictProb D S :=
    GamePerf.sum_negPart_le_winProb PFunDDS.verdict D S hD
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

/-- The reusable `sSup`-bounding idiom for `∆`: to bound `∆(S,T)`, bound every
probability-distribution distinguisher's advantage. -/
theorem maxAdvantage_le_of_forall_advantage_le {S T : PFunPDS X Y} {c : ℝ}
    (h : ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist → advantage D S T ≤ c) :
    Δ(S, T) ≤ c := by
  refine csSup_le (advantage_image_nonempty S T) ?_
  rintro x ⟨D, hD, rfl⟩
  exact h D hD

/-! ### Derandomisation of distinguishers (CR18 remark after Definition 2.7, p. 25)

"One can easily show that probabilistic distinguishers are not more powerful than deterministic ones
in the sense that best deterministic distinguisher has the same advantage as the best probabilistic
distinguisher."  The reason is that `∆^D(S,T)` is *affine* in `D` — Def 4.5's double sum is bilinear,
so `advantage_eq_expect_single` writes a mixture's advantage as the mixture of the mixed advantages —
and a supremum of an affine functional over the probability simplex is attained on the extreme
points, which are the point masses `δ_d`.

`maxAdvantage` is not rewritten: the deterministic supremum is expressed *inside* the statement, in
the library's `sSup`-over-image idiom, as a supremum over the raw distinguisher type `DDD X Y`.  No
parallel definition of `∆` is introduced. -/

/-- **`∆^D(S,T)` is affine in the distinguisher**: the advantage of a probabilistic distinguisher is
the `D`-average of the advantages of the deterministic distinguishers it mixes.  Signed layer — no
hypothesis on `D`, since this is bilinearity of Def 4.5, not normalization. -/
theorem advantage_eq_expect_single (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y) :
    advantage D S T = D.expect fun d => advantage (Finsupp.single d 1) S T := by
  unfold advantage verdictProb
  rw [Dist.expect_sub_right, ← GamePerf.winProb_eq_expect_single,
    ← GamePerf.winProb_eq_expect_single]

/-- **CR18 remark after Definition 2.7 — derandomisation of distinguishers.**  The maximal advantage
over all *probabilistic* distinguishers equals the supremum over the *deterministic* ones, each read
as the point mass `δ_d` it induces.

Both inequalities are cheap once `advantage_eq_expect_single` is available: `≥` because every point
mass is a probability distribution (`Dist.isProbDist_single`), and `≤` because a probability
distribution's expectation of a function bounded by `c` on its support is at most `c · |D| = c`
(`Dist.expect_le_mul_weight`).  The deterministic supremum is a genuine one: `DDD X Y` is inhabited
by `PFunDDS.rejectDDD`, and the image is bounded above by `∆(S,T)`. -/
theorem maxAdvantage_eq_sSup_deterministic (S T : PFunPDS X Y) :
    Δ(S, T) =
      sSup ((fun d : PFunDDS.DDD X Y => advantage (Finsupp.single d 1) S T) '' Set.univ) := by
  set f : PFunDDS.DDD X Y → ℝ := fun d => advantage (Finsupp.single d 1) S T
  have hsingle : ∀ d : PFunDDS.DDD X Y,
      Dist.isProbDist (Finsupp.single d (1 : ℝ) : Dist (PFunDDS.DDD X Y)) :=
    fun d => Dist.isProbDist_single d
  have hbdd : BddAbove (f '' Set.univ) := by
    refine ⟨Δ(S, T), ?_⟩
    rintro x ⟨d, -, rfl⟩
    exact advantage_le_maxAdvantage _ S T (hsingle d)
  have hne : (f '' Set.univ).Nonempty :=
    ⟨f (PFunDDS.rejectDDD X Y), ⟨_, Set.mem_univ _, rfl⟩⟩
  refine le_antisymm ?_ (csSup_le hne ?_)
  · refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
    rw [advantage_eq_expect_single]
    calc D.expect f ≤ sSup (f '' Set.univ) * D.weight :=
          Dist.expect_le_mul_weight hD.1
            (fun d _ => le_csSup hbdd ⟨d, Set.mem_univ d, rfl⟩)
      _ = sSup (f '' Set.univ) := by rw [hD.2, mul_one]
  · rintro x ⟨d, -, rfl⟩
    exact advantage_le_maxAdvantage _ S T (hsingle d)

/-- Identical systems have nonpositive maximal signed distinguishing advantage. -/
theorem maxAdvantage_self_le_zero (S : PFunPDS X Y) :
    Δ(S, S) ≤ 0 := by
  unfold maxAdvantage
  refine csSup_le ?_ ?_
  · exact advantage_image_nonempty S S
  · rintro b ⟨D, _hD, rfl⟩
    simp [advantage]

end RandomSystems.CR18
