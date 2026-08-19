/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SwitchingLemma
import RandomSystems.FilterDomNormalization
import RandomSystems.AbsorbDPI
import RandomSystems.AdaptiveLawBridge
import RandomSystems.SumOfPermutations
import RandomSystems.SoP.SoP2
import RandomSystems.SoP.DNSMirror

/-!
# Sum of two independent random permutations — how close to optimal?

Same construction as `RandomSystems.SumOfPermutations` and
`RandomSystems.SumOfPermutationsTight`: sample two independent uniform permutations
`π₁, π₂` of a finite abelian group `G` and answer a query `x` with `π₁ x + π₂ x`.

This file is the **reach** attempt.  The bound `ε` is existentially quantified, so it is an
output of the proof, and the improvement clause is only a floor that excludes restating the
birthday bound `q²/N`.  The result of interest is which `ε` you can prove.

## Benchmarks, for calibration

| bound | where | carrier |
|---|---|---|
| `q³/N²` | `HTechnique/SoP/LawAdvantage.lean:163` (`filteredDelta_bound`, needs `q³ ≤ N²`) | **already this carrier** |
| `2q³/3N²` | `SoP/SoP2.lean` Corollary 9 (`sop_advantage_closed_bound`, needs `q³ ≤ N²`) | `adaptiveTranscriptAdvantage` |
| `(q/N)^{3/2}` | Dai–Hoang–Tessaro, chi-squared method (`q ≤ N/16`) | not formalized here |
| `(10q² + 5n³)/N²` | formal DNS mirror proof (`N = 2ⁿ`, `q ≤ N/17`, exact finite-sum theorem underneath) | proved for XOR in `SoP/DNSMirror.lean` |

`SoP/SoP2.lean` also proves **Theorem 6**, an *exact* characterization of the adaptive
advantage as a compatible-count `L¹` deviation, and a saturation lower bound (Prop. 11)
showing the advantage really is `≥ 1 − 1/N` once the whole domain is queried.

## Outcome of this file

* **Closed, axiom-clean**: `sop_randomness_expander_optimal` with
  `ε N q = q(q−1)(2q−1)/(3N²)` for `q³ ≤ N²`, capped at `1` outside — Corollary 9's
  sequential-coupling bound carried to the raw CR18 filtered-`Δ` carrier
  (`sopOptimalBound`, exponent `q³/N²`).
* **The group-general reach**: `sop_randomness_expander_mirror` proves the `q²/N²`-regime bound
  `(19q² + 8⌈log₂N⌉³)/N²` on the same carrier, conditional on exactly one named
  counting lemma, `MirrorCountingBound`.  The XOR specialization of that counting
  lemma is closed in `SoP/DNSMirror.lean`; the broader finite-abelian-group statement
  remains open here.  Theorem 6 makes the conversion from
  that pointwise fiber bound to the adaptive advantage exact
  (`adaptiveTranscriptAdvantage_le_of_mirrorCountingBound`); the counting lemma is the
  only unproved statement on the route, and the alternatives (χ², refined couplings)
  provably cannot reach the exponent — see the reach section's header.
-/

noncomputable section

namespace RandomSystems.CR18.SoPOptimal

open RandomSystems (Dist)
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

universe u

variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] [AddCommGroup G]

/-- The sum-of-permutations function determined by a pair of permutations:
`x ↦ π₁ x + π₂ x`. -/
def sopFunction (p : Equiv.Perm G × Equiv.Perm G) : G → G :=
  fun x => p.1 x + p.2 x

/-- **The real system** `XoP`: two independent uniform permutations, queried as the
function `x ↦ π₁ x + π₂ x`. -/
def sopReal : PFunPDS G G :=
  Dist.fTransform
    (fun p : Equiv.Perm G × Equiv.Perm G => PFunDDS.functionEvaluator (sopFunction p))
    (Dist.uniform (Equiv.Perm G × Equiv.Perm G))

/-- **The ideal system**: a uniform random function `G → G`. -/
def sopIdeal : PFunPDS G G :=
  Dist.fTransform PFunDDS.functionEvaluator (Dist.uniform (G → G))

/-- The closed bound: the sequential-coupling sum-of-squares bound of `SoP2.md` Corollary 9
in its validity range `q³ ≤ N²`, capped by the trivial bound `1` outside it.  The cap is not
cosmetic: at `q³ > N²` the cubic formula can dip below `1` on a boundary sliver where no
in-tree bound covers it, while `1` always does. -/
def sopOptimalBound (N q : ℕ) : ℝ :=
  if q ^ 3 ≤ N ^ 2 then
    ((q * (q - 1) * (2 * q - 1) : ℕ) : ℝ) / ((3 * N ^ 2 : ℕ) : ℝ)
  else 1

/-- **Support lemma forced by formalization; candidate for upstream (`Dist.lean`).**
Pushing a function through the uniform distribution does not depend on the `Fintype`
instance: `Fintype` is a subsingleton. -/
theorem fTransform_uniform_fintypeIrrel {α : Type*} {β : Type*} [Nonempty α] (F : α → β)
    (i₁ i₂ : Fintype α) :
    Dist.fTransform F (@Dist.uniform α i₁ ‹_›) =
      Dist.fTransform F (@Dist.uniform α i₂ ‹_›) := by
  cases Subsingleton.elim i₁ i₂
  rfl

omit [Nonempty G] in
/-- The local real system is the coupling development's `xop` law.  The two definitions
differ only in the `Fintype` instances baked into the uniform seed distribution
(`SoP2.lean` works under `Classical.decEq`), so the identification is instance
subsingleton-elimination. -/
theorem sopReal_eq_xop_val : sopReal (G := G) = (RandomSystems.SoP.xop G).val :=
  fTransform_uniform_fintypeIrrel _ _ _

/-- The local ideal system is the coupling development's `urf` law, by the same
instance-subsingleton identification. -/
theorem sopIdeal_eq_urf_val : sopIdeal (G := G) = (RandomSystems.SoP.urf G).val :=
  fTransform_uniform_fintypeIrrel _ _ _

/-- **The carrier bridge.**  The raw CR18 filtered distinguishing advantage of the
concrete pair is dominated by the thesis-style law-level adaptive transcript advantage
of the coupling development's systems.  Both bounds below ride this hop. -/
theorem filteredDelta_le_adaptiveTranscriptAdvantage (q : ℕ) :
    Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G))) ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) := by
  have hS : PFunPDS.Prob.KStepTotal (RandomSystems.SoP.xop G) q :=
    functionEvaluatorProb_KStepTotal _ _ q
  have hT : PFunPDS.Prob.KStepTotal (RandomSystems.SoP.urf G) q :=
    functionEvaluatorProb_KStepTotal _ _ q
  have hNorm : DeltaFilteredFiniteQueryNormalization q
      (RandomSystems.SoP.xop G).val (RandomSystems.SoP.urf G).val :=
    deltaFilteredFiniteQueryNormalization_of_totalOnNonempty (0 : G) q _ _
      (functionEvaluatorProb_totalOnNonempty _ _)
      (functionEvaluatorProb_totalOnNonempty _ _)
  calc Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G)))
      = Δ(⌈q⌉ (RandomSystems.SoP.xop G).val, ⌈q⌉ (RandomSystems.SoP.urf G).val) := by
        rw [sopReal_eq_xop_val, sopIdeal_eq_urf_val]
    _ ≤ PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
          (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) :=
        maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage
          (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) hS hT hNorm

/-- **How close to optimal can the bound be pushed?**

Exhibit a bound `ε N q` on the `q`-query distinguishing advantage over a group of order `N`,
together with a proof that it strictly improves on the birthday bound `q²/N` wherever the
birthday bound says anything.

`ε` is quantified **outside** the group and takes `(N, q)`, so it must be one formula that
holds for every group of that order.  That is deliberate: with `ε` chosen after the group it
could be instantiated as the advantage itself, making the first conjunct `le_refl` and the
theorem vacuous.

The floor merely excludes restating the birthday bound.  The target is the `q²/N²` regime —
see the benchmark table in the module docstring. -/
theorem sop_randomness_expander_optimal :
    ∃ ε : ℕ → ℕ → ℝ,
      (∀ (H : Type u) [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H] (q : ℕ),
          Δ(⌈q⌉ (sopReal (G := H)), ⌈q⌉ (sopIdeal (G := H))) ≤ ε (Fintype.card H) q) ∧
      (∀ N q : ℕ, 1 < q → q < N → ε N q < (q : ℝ) ^ 2 / (N : ℝ)) := by
  classical
  refine ⟨sopOptimalBound, ?_, ?_⟩
  · -- the advantage bound, for every abelian group of order `N` and every `q`
    intro H _ _ _ _ q
    by_cases hcube : q ^ 3 ≤ Fintype.card H ^ 2
    · -- Corollary 9's range: bridge to the law-level adaptive transcript advantage
      -- and cite the sequential-coupling bound.
      have hchain : Δ(⌈q⌉ (sopReal (G := H)), ⌈q⌉ (sopIdeal (G := H))) ≤
          ((q * (q - 1) * (2 * q - 1) : ℕ) : ℝ) / ((3 * Fintype.card H ^ 2 : ℕ) : ℝ) :=
        calc Δ(⌈q⌉ (sopReal (G := H)), ⌈q⌉ (sopIdeal (G := H)))
            ≤ PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
                (RandomSystems.SoP.xop H) (RandomSystems.SoP.urf H) :=
              filteredDelta_le_adaptiveTranscriptAdvantage (G := H) q
          _ ≤ ((((q * (q - 1) * (2 * q - 1) : ℕ) : NNReal) /
                ((3 * Fintype.card H ^ 2 : ℕ) : NNReal) : NNReal) : ℝ) :=
              (RandomSystems.SoP.sop_advantage_closed_bound H q hcube).1
          _ = ((q * (q - 1) * (2 * q - 1) : ℕ) : ℝ) /
                ((3 * Fintype.card H ^ 2 : ℕ) : ℝ) := by
              simp only [NNReal.coe_div, NNReal.coe_natCast]
      simpa only [sopOptimalBound, if_pos hcube] using hchain
    · -- outside the cubic range the trivial probability-system bound `Δ ≤ 1` applies
      have hone : Δ(⌈q⌉ (sopReal (G := H)), ⌈q⌉ (sopIdeal (G := H))) ≤ 1 :=
        maxAdvantage_le_one
          (by cr18_prob; exact RandomSystems.CR18.SoP.sopReal_isProbDist)
          (by cr18_prob; exact RandomSystems.CR18.SoP.sopIdeal_isProbDist)
      simpa only [sopOptimalBound, if_neg hcube] using hone
  · -- strict improvement over the birthday bound `q²/N` on `1 < q < N`
    intro N q hq hqN
    have hN : 0 < N := by omega
    by_cases hcube : q ^ 3 ≤ N ^ 2
    · -- `q(q−1)(2q−1)·N < q²·3N²` because `q(q−1)(2q−1) ≤ 2q³` and `2q < 3N`
      have h₁ : q * (q - 1) * (2 * q - 1) ≤ 2 * q ^ 3 :=
        calc q * (q - 1) * (2 * q - 1) ≤ q * q * (2 * q) :=
              Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le q 1)) (Nat.sub_le (2 * q) 1)
          _ = 2 * q ^ 3 := by ring
      have h₂ : 2 * q ^ 3 * N < q ^ 2 * (3 * N ^ 2) :=
        calc 2 * q ^ 3 * N = (2 * q) * (q ^ 2 * N) := by ring
          _ < (3 * N) * (q ^ 2 * N) :=
              mul_lt_mul_of_pos_right (by omega)
                (mul_pos (pow_pos (by omega : 0 < q) 2) hN)
          _ = q ^ 2 * (3 * N ^ 2) := by ring
      have hkey : q * (q - 1) * (2 * q - 1) * N < q ^ 2 * (3 * N ^ 2) :=
        lt_of_le_of_lt (Nat.mul_le_mul h₁ le_rfl) h₂
      have hlt : ((q * (q - 1) * (2 * q - 1) : ℕ) : ℝ) / ((3 * N ^ 2 : ℕ) : ℝ) <
          (q : ℝ) ^ 2 / (N : ℝ) := by
        have h3N : (0 : ℝ) < ((3 * N ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast mul_pos (by norm_num : (0 : ℕ) < 3) (pow_pos hN 2)
        rw [div_lt_div_iff₀ h3N (by exact_mod_cast hN)]
        exact_mod_cast hkey
      simpa only [sopOptimalBound, if_pos hcube] using hlt
    · -- `q³ > N²` forces `q² > N`, so even the trivial cap `1` beats `q²/N`
      have hc : N ^ 2 < q ^ 3 := not_le.mp hcube
      have hq2 : N < q ^ 2 := by
        have h1 : q * q ^ 2 < N * q ^ 2 :=
          mul_lt_mul_of_pos_right hqN (pow_pos (by omega : 0 < q) 2)
        nlinarith
      have hlt : (1 : ℝ) < (q : ℝ) ^ 2 / (N : ℝ) := by
        rw [lt_div_iff₀ (by exact_mod_cast hN)]
        rw [one_mul]
        exact_mod_cast hq2
      simpa only [sopOptimalBound, if_neg hcube] using hlt

/-! ## The reach: the mirror-theory regime, isolated to one named counting lemma

`SoP/SoP2.lean`'s Theorem 6 (`sop_advantage_eq_half_l1_compatible_count`) characterizes
the adaptive advantage **exactly** as a compatible-count `L¹` deviation, so a pointwise
lower bound on the compatible fibers converts directly into an advantage bound with no
further slack.  Mirror theory for `ξ_max = 2` (Dutta–Nandi–Saha, ePrint 2020/669) is
precisely such a pointwise bound, in the `q²/N²` regime — full `n`-bit security.

Everything from the pointwise bound down to the `Δ`-carrier statement is proved below,
axiom-clean; the pointwise bound itself is the **one named gap**, `MirrorCountingBound`.

Routed and rejected alternatives, so nobody re-explores them:

* **χ² method** (Dai–Hoang–Tessaro, ePrint 2017/537): the per-step conditional variance
  of the image-collision count `c_z` equals its mean up to `1 + o(1)`, so the transcript
  KL/χ² is genuinely `Θ(q³/N³)` and Pinsker's terminal square root cannot land below
  `(q/N)^{3/2}`.  No divergence-style argument reaches `q²/N²` for this construction.
* **Sequential couplings**: `SoP2.lean`'s online coupling pays the worst-case one-step
  `L¹` distance `r²/(N(N−r))` per fresh query; that is Corollary 9's cubic bound, and
  refining to the expected one-step distance at the reached state cannot beat the
  `Σ_r E‖·‖₁`-floor of the agree-until-failure class, which sits at `~q²/N^{3/2}`.
  The maximal coupling is exact (Theorem 6) but is not stepwise-estimable — bounding
  its overlap **is** the compatible-count problem below.
* **Exact small-`q` audits** (`SoP2.md` Prop. 10): `Adv₂ = 1/(N(N−1))`,
  `Adv₃ ≈ 3/N²` — the truth is `Θ(q²/N²)`, so the mirror regime is the right target
  and only its constants are negotiable. -/

/-- **Support lemma forced by formalization; candidate for upstream.**  If a finite
family `p` has the same total mass as the constant reference `u ≥ 0`, pointwise
deficiency at most `ε·u`, and reference mass at most one, then its half-`L¹` distance
to the reference is at most `ε`.  This is the standard "no bad transcripts"
H-coefficient conversion, for plain reals: the signed terms cancel by equal mass, so
the `L¹` sum is twice the deficiency sum, and the deficiency is pointwise small. -/
theorem half_l1_le_of_pointwise_lower {α : Type*} [Fintype α]
    (p : α → ℝ) (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (hsum : ∑ y : α, p y = ∑ _y : α, u)
    (hlow : ∀ y : α, (1 - ε) * u ≤ p y)
    (husum : ∑ _y : α, u ≤ 1) :
    (1 / 2 : ℝ) * ∑ y : α, |p y - u| ≤ ε := by
  have habs : ∀ a b : ℝ, |a - b| = (a - b) + 2 * max (b - a) 0 := by
    intro a b
    rcases le_total a b with hab | hab
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
  have hmax : ∀ y : α, max (u - p y) 0 ≤ ε * u := fun y =>
    max_le (by nlinarith [hlow y]) (mul_nonneg hε hu)
  have hsplit : ∑ y : α, |p y - u| =
      ((∑ y : α, p y) - ∑ _y : α, u) + 2 * ∑ y : α, max (u - p y) 0 := by
    rw [Finset.sum_congr rfl fun y _ => habs (p y) u, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hmaxsum : ∑ y : α, max (u - p y) 0 ≤ ε :=
    calc ∑ y : α, max (u - p y) 0 ≤ ∑ _y : α, ε * u :=
          Finset.sum_le_sum fun y _ => hmax y
      _ = ε * ∑ _y : α, u := by rw [← Finset.mul_sum]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left husum hε
      _ = ε := mul_one ε
  rw [hsplit, hsum]
  linarith

/-- **The reach gap — the single unproved statement on the mirror route.**

Group-general mirror theory for `ξ_max = 2`: every compatible-assignment fiber of the
sum of two independent uniform permutations is within `(19q² + 8⌈log₂N⌉³)/N²` of its
ideal size `(N)_q²/N^q`, **from below, pointwise in the output vector `y`**.

For `G = (𝔽₂)ⁿ` this is exactly Dutta–Nandi–Saha, ePrint 2020/669, Lemma 8 (their
`P(γ^q) = C_G(y)/N^q`, and `Nat.clog 2 N = n`), asserted for `17q ≤ N` and `n ≥ 7`;
a consumer of this predicate should carry those hypotheses, since near saturation the
inequality's status is open (for `(1−ε) ≤ 0` it is trivially true).  Their proof —
one exact link-deletion identity, an insertion bound, a differential-term recursion
with multiplicity-controlled matching (their Lemma 13), and a depth-`2·log₂N`
double-sequence recursion (their Lemma 1) — is now formalized separately for
`G = (𝔽₂)ⁿ` in `SoP/DNSMirror.lean`.  The formal audit exposes a genuine
characteristic-two recentering at the zero-link boundary.  Consequently that proof
does **not** silently port to every finite abelian group and does not discharge this
deliberately broader predicate; a replacement for that step is part of the open
generalization. -/
def MirrorCountingBound (q : ℕ) : Prop :=
  ∀ y : Fin q → G,
    (1 - (19 * (q : ℝ) ^ 2 + 8 * (Nat.clog 2 (Fintype.card G) : ℝ) ^ 3) /
          (Fintype.card G : ℝ) ^ 2) *
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : ℕ) : ℝ) ≤
      (RandomSystems.SoP.compatible_count G y : ℝ) * ((Fintype.card G ^ q : ℕ) : ℝ)

omit [DecidableEq G] in
/-- Generic exact-L1 conversion for a pointwise compatible-fiber lower bound.
This isolates the carrier-independent part of the mirror argument and lets the
proved XOR theorem retain its sharper error instead of first weakening to the
legacy `MirrorCountingBound` constants. -/
theorem adaptiveTranscriptAdvantage_le_of_compatible_counting_bound
    (q : ℕ) (hq : q ≤ Fintype.card G) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ y : Fin q → G,
      (1 - ε) *
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : ℕ) : ℝ) ≤
        (RandomSystems.SoP.compatible_count G y : ℝ) *
          ((Fintype.card G ^ q : ℕ) : ℝ)) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) ≤ ε := by
  classical
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hD : 0 < (Fintype.card G).descFactorial q := Nat.descFactorial_pos.mpr hq
  have hDD : (0 : ℝ) <
      (((Fintype.card G).descFactorial q *
        (Fintype.card G).descFactorial q : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hD hD
  have hNq : (0 : ℝ) < ((Fintype.card G ^ q : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hN q
  rw [RandomSystems.SoP.sop_advantage_eq_half_l1_compatible_count_of_le_card G q hq]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one]
  refine half_l1_le_of_pointwise_lower _ _ _ (by positivity) hε ?sum ?low ?ref
  case sum =>
    have hCsum : ∑ y : Fin q → G, (RandomSystems.SoP.compatible_count G y : ℝ) =
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ))
        (RandomSystems.SoP.compatible_count_sum G q)
    have hPsum : ∑ y : Fin q → G,
        ((RandomSystems.SoP.compatible_count G y : ℝ) /
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : ℕ) : ℝ)) = 1 := by
      rw [← Finset.sum_div, hCsum, div_self hDD.ne']
    have hUsum : ∑ _y : Fin q → G,
        (1 / ((Fintype.card G ^ q : ℕ) : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, mul_one_div]
      exact div_self hNq.ne'
    rw [hPsum, hUsum]
  case low =>
    intro y
    rw [mul_one_div, div_le_div_iff₀ hNq hDD]
    exact h y
  case ref =>
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, mul_one_div, div_self hNq.ne']

omit [DecidableEq G] in
/-- **The reach reduction: everything below the gap, proved.**  The mirror pointwise
bound feeds Theorem 6's exact characterization: the real fiber probabilities sum to one
(compatible fibers partition the injective-tape square, `compatible_count_sum`), the
uniform reference sums to one, and the pointwise deficiency is at most `ε/N^q`, so the
half-`L¹` deviation — which **is** the exact adaptive advantage — is at most `ε`. -/
theorem adaptiveTranscriptAdvantage_le_of_mirrorCountingBound
    (q : ℕ) (hq : q ≤ Fintype.card G) (h : MirrorCountingBound (G := G) q) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) ≤
      (19 * (q : ℝ) ^ 2 + 8 * (Nat.clog 2 (Fintype.card G) : ℝ) ^ 3) /
        (Fintype.card G : ℝ) ^ 2 := by
  classical
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hD : 0 < (Fintype.card G).descFactorial q := Nat.descFactorial_pos.mpr hq
  have hDD : (0 : ℝ) <
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hD hD
  have hNq : (0 : ℝ) < ((Fintype.card G ^ q : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hN q
  have hε : 0 ≤ (19 * (q : ℝ) ^ 2 + 8 * (Nat.clog 2 (Fintype.card G) : ℝ) ^ 3) /
      (Fintype.card G : ℝ) ^ 2 := by positivity
  rw [RandomSystems.SoP.sop_advantage_eq_half_l1_compatible_count_of_le_card G q hq]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one]
  refine half_l1_le_of_pointwise_lower _ _ _ (by positivity) hε ?sum ?low ?ref
  case sum =>
    -- both sides have total mass one
    have hCsum : ∑ y : Fin q → G, (RandomSystems.SoP.compatible_count G y : ℝ) =
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ))
        (RandomSystems.SoP.compatible_count_sum G q)
    have hPsum : ∑ y : Fin q → G,
        ((RandomSystems.SoP.compatible_count G y : ℝ) /
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : ℕ) : ℝ)) = 1 := by
      rw [← Finset.sum_div, hCsum, div_self hDD.ne']
    have hUsum : ∑ _y : Fin q → G, (1 / ((Fintype.card G ^ q : ℕ) : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, mul_one_div]
      exact div_self hNq.ne'
    rw [hPsum, hUsum]
  case low =>
    -- the mirror pointwise bound, divided through by `(N)_q² · N^q`
    intro y
    rw [mul_one_div, div_le_div_iff₀ hNq hDD]
    exact h y
  case ref =>
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one_div, div_self hNq.ne']

/-- **The reach, on the target carrier, conditional on the one named gap.**

Modulo `MirrorCountingBound` — mirror theory for `ξ_max = 2`, the single missing
counting lemma — the sum of two independent uniform permutations of any finite abelian
group of order `N` is within `(19q² + 8⌈log₂N⌉³)/N²` of a uniform random function
against every adaptive `q`-query distinguisher: the `q²/N²` regime, which no
unconditional bound in this tree reaches. -/
theorem sop_randomness_expander_mirror
    (q : ℕ) (hq : q ≤ Fintype.card G) (h : MirrorCountingBound (G := G) q) :
    Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G))) ≤
      (19 * (q : ℝ) ^ 2 + 8 * (Nat.clog 2 (Fintype.card G) : ℝ) ^ 3) /
        (Fintype.card G : ℝ) ^ 2 :=
  calc Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G)))
      ≤ PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
          (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) :=
        filteredDelta_le_adaptiveTranscriptAdvantage q
    _ ≤ (19 * (q : ℝ) ^ 2 + 8 * (Nat.clog 2 (Fintype.card G) : ℝ) ^ 3) /
          (Fintype.card G : ℝ) ^ 2 :=
        adaptiveTranscriptAdvantage_le_of_mirrorCountingBound q hq h

/-! ## Closed DNS endpoints on the published XOR carrier

These theorems do not assume `MirrorCountingBound`.  They instantiate the exact
compatible-count proof in `SoP/DNSMirror.lean`; the group-general predicate above
remains open. -/

/-- The formal XOR proof supplies the published `19,8` predicate as a corollary,
although its native constants are stronger. -/
theorem xor_mirrorCountingBound
    (n q : ℕ) (hn : 7 ≤ n) (hrange : 17 * q ≤ 2 ^ n) :
    MirrorCountingBound (G := RandomSystems.SoP.DNS.XorSpace n) q := by
  intro y
  have h := RandomSystems.SoP.DNS.dns_published_counting_bound y hn hrange
  simpa [RandomSystems.SoP.DNS.card_xorSpace,
    Nat.clog_pow 2 n (by norm_num)] using h

/-- Exact finite-sum adaptive advantage bound furnished by the formal DNS proof. -/
theorem xor_adaptiveTranscriptAdvantage_le_dnsExactError
    (n q : ℕ) (hn : 7 ≤ n) (hrange : 17 * q ≤ 2 ^ n) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (RandomSystems.SoP.xop (RandomSystems.SoP.DNS.XorSpace n))
        (RandomSystems.SoP.urf (RandomSystems.SoP.DNS.XorSpace n)) ≤
      RandomSystems.SoP.DNS.dnsExactError n q := by
  have hq : q ≤ Fintype.card (RandomSystems.SoP.DNS.XorSpace n) := by
    rw [RandomSystems.SoP.DNS.card_xorSpace]
    omega
  have hε : 0 ≤ RandomSystems.SoP.DNS.dnsExactError n q := by
    unfold RandomSystems.SoP.DNS.dnsExactError
    exact Finset.sum_nonneg fun k _ =>
      RandomSystems.SoP.DNS.dnsStepLoss_nonneg n k
  apply adaptiveTranscriptAdvantage_le_of_compatible_counting_bound q hq _ hε
  intro y
  simpa [RandomSystems.SoP.DNS.card_xorSpace] using
    RandomSystems.SoP.DNS.dns_exact_counting_bound y hn hrange

/-- Closed adaptive bound from the same proof.  The exact finite sum above is
strictly preferred when concrete parameters are available. -/
theorem xor_adaptiveTranscriptAdvantage_le_dnsClosed
    (n q : ℕ) (hn : 7 ≤ n) (hrange : 17 * q ≤ 2 ^ n) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q)
        (RandomSystems.SoP.xop (RandomSystems.SoP.DNS.XorSpace n))
        (RandomSystems.SoP.urf (RandomSystems.SoP.DNS.XorSpace n)) ≤
      (10 * (q : ℝ) ^ 2 + 5 * (n : ℝ) ^ 3) /
        (((2 ^ n : ℕ) : ℝ) ^ 2) :=
  (xor_adaptiveTranscriptAdvantage_le_dnsExactError n q hn hrange).trans
    (RandomSystems.SoP.DNS.dnsExactError_le_closed hrange)

/-- Final CR18 filtered-`Δ` theorem, with no mirror-theory assumption. -/
theorem sop_randomness_expander_dns_exact
    (n q : ℕ) (hn : 7 ≤ n) (hrange : 17 * q ≤ 2 ^ n) :
    Δ(⌈q⌉ (sopReal (G := RandomSystems.SoP.DNS.XorSpace n)),
      ⌈q⌉ (sopIdeal (G := RandomSystems.SoP.DNS.XorSpace n))) ≤
        RandomSystems.SoP.DNS.dnsExactError n q :=
  (filteredDelta_le_adaptiveTranscriptAdvantage
      (G := RandomSystems.SoP.DNS.XorSpace n) q).trans
    (xor_adaptiveTranscriptAdvantage_le_dnsExactError n q hn hrange)

/-- Convenient closed CR18 corollary (`10,5`, versus DNS's published `19,8`). -/
theorem sop_randomness_expander_dns_closed
    (n q : ℕ) (hn : 7 ≤ n) (hrange : 17 * q ≤ 2 ^ n) :
    Δ(⌈q⌉ (sopReal (G := RandomSystems.SoP.DNS.XorSpace n)),
      ⌈q⌉ (sopIdeal (G := RandomSystems.SoP.DNS.XorSpace n))) ≤
      (10 * (q : ℝ) ^ 2 + 5 * (n : ℝ) ^ 3) /
        (((2 ^ n : ℕ) : ℝ) ^ 2) :=
  (sop_randomness_expander_dns_exact n q hn hrange).trans
    (RandomSystems.SoP.DNS.dnsExactError_le_closed hrange)

end RandomSystems.CR18.SoPOptimal
