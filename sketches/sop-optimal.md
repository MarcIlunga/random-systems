# sop_randomness_expander_optimal — sketch and route ledger

Target: `RandomSystems/SumOfPermutationsOptimal.lean`, existential ε over (N, q):
(1) `Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ ε (card H) q` for every finite abelian H, every q;
(2) `ε N q < q²/N` for all `1 < q < N`.
Research objective: the q²/N² exponent (mirror-theory regime). Statement frozen.

## Deliverable 1 (floor, fully closed) — technique: family II reuse, all [LIB]

**ε N q := if q³ ≤ N² then q(q−1)(2q−1)/(3N²) else 1.**

Route (one `calc`, every hop cited):

```
Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal)
  = Δ(⌈q⌉ (SoP.xop H).val, ⌈q⌉ (SoP.urf H).val)      -- defs agree up to Fintype-instance
                                                       -- subsingletons (SoP2 uses Classical.decEq)
  ≤ adaptiveTranscriptAdvantage q (xop H) (urf H)      -- maxAdvantage_filterQueries_le_
                                                       --   adaptiveTranscriptAdvantage
                                                       --   (AdaptiveLawBridge.lean:586)
  ≤ q(q−1)(2q−1)/(3N²)                                 -- sop_advantage_closed_bound.1
                                                       --   (SoP2.lean:5053, Cor 9, needs q³ ≤ N²)
```

q³ > N² branch: `maxAdvantage_le_one` (CompatibleMetric.lean:1470) with filtered isProbDist.

Bridge hypotheses, all [LIB]/[ROUTINE]:
- `KStepTotal (xop H) q` — `functionEvaluatorProb_KStepTotal`
- `KStepTotal (urf H) q` — `PFunPDS.Prob.urf_KStepTotal`
- `DeltaFilteredFiniteQueryNormalization` — `deltaFilteredFiniteQueryNormalization_of_totalOnNonempty (0 : H)`
  + `functionEvaluatorProb_totalOnNonempty` twice

Improvement clause (pure arithmetic):
- q³ ≤ N² branch: q(q−1)(2q−1)·N < 3N²·q² since q(q−1)(2q−1) ≤ 2q³ and 2q < 3N.
- q³ > N² branch: 1 < q²/N because q² ≤ N would give q³ ≤ qN < N².

DAG has zero [CREATIVE] nodes ⇒ skeleton stage skipped per skill (finished calc directly).

## OUTCOME (final)

* `sop_randomness_expander_optimal` — **PROVED, zero sorry, axioms `[propext, Classical.choice,
  Quot.sound]`** with `ε N q = if q³ ≤ N² then q(q−1)(2q−1)/(3N²) else 1` (`sopOptimalBound`).
* Reach — **`sop_randomness_expander_mirror`**: `Δ(⌈q⌉ real, ⌈q⌉ ideal) ≤ (19q² + 8⌈log₂N⌉³)/N²`
  for `q ≤ N`, conditional on exactly ONE named lemma, `MirrorCountingBound` (group-general
  DNS Lemma 8: pointwise `(1−ε)·(N)_q² ≤ C_G(y)·N^q`).  The reduction
  (`adaptiveTranscriptAdvantage_le_of_mirrorCountingBound`, via the new generic
  `half_l1_le_of_pointwise_lower`) and the carrier bridge are proved axiom-clean.
* New public glue: `fTransform_uniform_fintypeIrrel`, `sopReal_eq_xop_val`,
  `sopIdeal_eq_urf_val`, `filteredDelta_le_adaptiveTranscriptAdvantage`,
  `half_l1_le_of_pointwise_lower` (upstream candidates marked in-file).

## Reach — synthesis (2 scouts returned, 4 killed by org spend limit)

Benchmarks: in-tree 2q³/3N² (Cor 9); χ² (q/N)^{3/2}; mirror (19q²+8n³)/N².
Exact audits Adv₂ = 1/(N(N−1)), Adv₃ ≈ 3/N² ⇒ truth is ~binom(q,2)/N² at small q.

Scout verdicts:
- **χ² (returned)**: (q/N)^{3/2} costs a finite divergence layer (Pinsker [fiddly], KL chain
  rule [bookkeeping], KL ≤ χ², conditional Jensen) + a two-page second-moment computation on
  c_z that matches in-tree `p_r(z)` exactly. Fully group-general, no bit structure. **Barrier:
  transcript χ² is genuinely Θ(q³/N³) (variance ≈ mean for c_z), so χ²/KL can never give
  q²/N². The target exponent needs pointwise/mirror-style counting with sign cancellation.**
- **DNS mirror (returned — WINNER)**: read all 31 pages visually. Lemma 8 (independent-
  permutations track) is exactly our pointwise bound for arbitrary y (repeats and identity
  coordinates allowed). Proof skeleton: base regime (trivial insertion, 2·log₂N steps —
  the whole source of 8n³) + main regime per-step ratio ≥ (1−α/N)²(1−17α/N²) via exact
  link-deletion identity (their Lemma 11/Eqn 30) + Core Lemma 12 (differential term
  D(α,ℓ) recursion, Lemma 13 matching with ≤3Δ unmatched indices) + Lemma 1 Pascal-walk
  double induction (depth 2n forced by 2^{−d/2} ≤ 1/N). Fully group-general: never uses
  bit-linearity; port n → ⌈log₂N⌉, n ≥ 7 → N ≥ 128. Errata (all confirmed): Thm 3 repeats
  the x₁ equation; "non-zero γ" stale; range is N/17 not 2^{n/17}. Plus one real
  off-by-one: Core Lemma needs q ≥ 2n+1 at depth 2n — re-derive boundary constants.
  Hard cores: Lemma 13 matching (label/multiset bookkeeping) and Lemma 1's coefficient
  induction. ≈ 8–9 pages after de-duplication. Structurally simpler alternative to check
  next: Cogliati–Patarin ePrint 2020/734.
- direct L¹, coupling interpolation, cross-field identification, lower bounds: scouts
  KILLED by org monthly spend limit before reporting. Covered inline: coupling floor
  argument (per-step E‖·‖₁ ≥ per-step TV ⇒ agree-until-failure class floors at
  ~q²/N^{3/2}); truth pinned at Θ(q²/N²) by the exact q=2,3 audits (collision-count
  attack gives the matching lower bound: P_real(Y_i=Y_j) = 1/(N−1) vs 1/N per pair).

Decision rule: reach = best provable exponent with the gap (if any) isolated as ONE named
lemma, stated in Lean with everything around it proved. Candidate gap shape: pointwise
compatible-count lower bound `N^m · C_G(y) ≥ (1 − ε)(N)_m²` feeding Theorem 6
(`sop_advantage_eq_half_l1_compatible_count`, SoP2.lean).
