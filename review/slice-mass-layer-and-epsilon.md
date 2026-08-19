# Slice review — `mass-layer-and-epsilon`

Adversarial review of the 20-node slice "counts become probabilities, and is `ε` what it says".
Read-only: no proof file was modified. Scratch experiments were run outside the repo and deleted.

**Verdict: 20/20 nodes checked, 0 CRITICAL, 0 MAJOR, 3 MINOR (all presentational/scope), 17 CLEAN.**
I could not find a way to make any node in this slice false, vacuous, or misdescribed in substance.
The two hypotheses the brief flagged as load-bearing (the factor order in the cardinality premise,
and the `min 1` degenerate branch) were both checked directly and both come out clean, with one
quantified caveat about *which conjunct of the top-level theorem* the `min 1` is carrying.

## 0. Method

Two independent passes per node.

**(a) Lean check** — elaborated statements read from `review/sop-dag.tsv` (`NODE` rows carry the
`Expr`-level type, so nothing is taken from source pretty-printing), plus live goal states pulled
with the lean-lsp MCP at lines 546, 560, 677, 751 of `RandomSystems/SumOfPermutationsTight.lean`.
`lean_diagnostic_messages` on that file returns `success: true, items: []` — the file elaborates
clean today, so the goal states below are the real ones.

**(b) Math check** — pen-and-paper derivation of each identity, plus an *independent
reimplementation* in Python that brute-forces every pair of permutations for `N ≤ 5` and every
transcript, using its own selection rule for the `canonSubset` choice (legitimate: `card_avail_fresh`
depends on `freshKeep` only through its cardinality, so any `m`-element selection reproduces the
same counts). Plus an exact-rational computation of the true statistical distance of the two systems
for `N ≤ 8`, `q ≤ 5`, compared against `sopEps`.

## 1. The two premises the brief singled out

### 1.1 Factor order in `Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq` — CLEAN

The lemma is
`(#P · |B| = #Q · #E) → (uniform A).mass P = (uniform B).mass Q * (uniform A).mass E`,
with `P E : A → Prop` and `Q : B → Prop`. That is arithmetically forced and correct:
`#P/|A| = (#Q/|B|)·(#E/|A|) ⟺ #P·|B| = #Q·#E`. `|A| ≠ 0` and `|B| ≠ 0` come from `Nonempty`, so no
NNReal division-by-zero convention is being leaned on.

The instantiation was read off the live goal, not from the source, at line 546 of
`SumOfPermutationsTight.lean`:

```
goals_after:
⊢ {p | (∀ (s : ↥S), sopFunction p ↑s = a s) ∧ ¬sopTightBad p l}.card * Fintype.card (G → G) =
    {g | ∀ (s : ↥S), g ↑s = a s}.card * {p | ¬sopTightBad p l}.card
```

so `P := agree ∧ good` on the seed space, `Q := agree` on the URF space `B = G → G`,
`E := good` on the seed space. That is the intended `#P·|B| = #Q·#E`, **not** transposed.
The closing arithmetic (goal at line 560) is

```
⊢ goodCount G S.card * Fintype.card G ^ Fintype.card G =
    Fintype.card G ^ (Fintype.card G - S.card) * (Fintype.card G ^ S.card * goodCount G S.card)
```

i.e. `gc·N^N = N^(N−|S|)·(N^|S|·gc)`, true because `|S| ≤ N` (supplied by `Finset.card_le_univ`).
A transposition of `Q` and `E` here would have produced `N^{N−|S|}` where `N^{|S|}·gc` belongs and
would not close. Checked, correct.

### 1.2 Does `min 1` carry the theorem? — mostly NO, with one precise exception

`mass_sopTightBad_le` opens with `refine le_min hmass_le_one ?_`, so the `min` **does not weaken the
obligation**: the proof must supply *both* `mass ≤ 1` and `mass ≤ Σ_{k<q} k²/(N−k)²`. The `min 1` is
a strengthening of `ε`, not an escape hatch, and the extra work it costs is exactly
`sopEps_ge_one_of_large`.

The one place `min 1` is genuinely load-bearing is the **second** conjunct of the top-level theorem
(`ε N q < q²/N` for `1 < q < N`), discharged for all `q² > N` by `min_le_left` (line 797). Measured:
the *uncapped* sum first exceeds `q²/N` at

| N | first q with Σ > q²/N | ≈ |
|---|---|---|
| 4 | 4 | 1.00 N |
| 8 | 7 | 0.88 N |
| 64 | 43 | 0.67 N |
| 1024 | 674 | 0.66 N |
| 65536 | 43037 | 0.657 N |

So without the cap the second conjunct would be **false** for `q ≳ 0.66 N`, and the proof takes the
cap even earlier (`q > √N`). Recorded as MINOR-3 below. The docstring already says this conjunct is
"a floor, not the target".

### 1.3 Is the *first* conjunct (the actual security bound) carried by a degenerate branch? — NO

This is the sharpest anti-vacuity question in the slice, and it comes out clean for a structural
reason worth recording.

* A single term `k²/(N−k)²` is `≥ 1` exactly when `2k ≥ N` (for `k < N`); the `k = N` term is `0`
  by Lean's division convention and every `k > N` term is `≥ 1`. Hence for `N ≥ 2`,
  `Σ_{k<q} k²/(N−k)² < 1 ⟹ q ≤ ⌈N/2⌉`.
* `goodCount G d = ((N−d)!)²·∏_{k<d}(N−2k)` vanishes exactly when some `k < d` has `2k ≥ N`, i.e.
  exactly when `d ≥ ⌈N/2⌉+1`.

**The two thresholds coincide.** Therefore there is *no* `(N,q)` at which `sopEps N q < 1` while the
conditioning event `¬sopTightBad` is null. The `mass ≤ 1 ≤ Σ` branch of `mass_sopTightBad_le` is only
ever reached where `ε` is already `1`. Measured margin (the real range is far inside the boundary):

| N | 8 | 16 | 64 | 256 | 1024 | 4096 | 65536 | 2^20 | 2^24 |
|---|---|---|---|---|---|---|---|---|---|
| largest q with ε<1 | 4 | 7 | 19 | 52 | 136 | 353 | 2303 | 14781 | 94253 |
| ⌈N/2⌉ (vacuity edge) | 4 | 8 | 32 | 128 | 512 | 2048 | 32768 | 524288 | 8388608 |

## 2. Per-node results

### NEW nodes (7)

**`sopEps` — `SumOfPermutationsTight.lean:600` — CLEAN**
(a) `def sopEps (N q : ℕ) : ℝ := min 1 (∑ k ∈ Finset.range q, (k:ℝ)^2 / ((N:ℝ) - k)^2)`. Elaborated
type `ℕ → ℕ → ℝ`: it depends on nothing but `(N,q)`, which is what makes the top-level ∃ non-vacuous
(ε is quantified outside the group). No `Fintype`/carrier leakage.
(b) Behaviour fully characterised. Nontrivial (`<1`) exactly for `q ≤ ~1.442·N^{2/3}`; measured
`qmax/(3N²)^{1/3}` = 0.693 (N=8) → 0.928 (N=1024) → 0.997 (N=2^24), so the "≈ q³/3N²" of the file
docstring is asymptotically exact, not decorative. Ratio `Σ / (q³/3N²)`: 0.867 at (10³,10), 1.047 at
(10³,50), 1.152 at (10³,100), 1.000 at (10⁶,10³), 1.015 at (10⁶,10⁴) — i.e. the sum is the stated
`q³/3N²` to within 26 % everywhere the bound says anything, and to within 1.5 % in the large-N
regime. Genuinely beyond birthday (`√N`), and honestly far short of the `~N` the construction is
believed to reach; the file docstring does not claim otherwise.
Division-by-zero probe: the `k = N` term evaluates to `0` in Lean rather than `+∞`. Checked that this
cannot make `ε` too small anywhere: reaching `k = N` requires `q ≥ N+1`, and the `k = N−1` term is
already `(N−1)² ≥ 1` for `N ≥ 2`, so `ε = 1` there regardless. For `N = 1` both systems are
deterministic and `Δ = 0 = ε` for `q ≤ 2`. No hole.

**`sopEps_nonneg` — :603 — CLEAN**
(a) `∀ N q, 0 ≤ sopEps N q`; proof `le_min zero_le_one (sum_nonneg …)` — correct use of `le_min`
(needs `0 ≤ 1` *and* `0 ≤ Σ`), not `min_le`.
(b) True; every summand is a ratio of squares, nonneg even at `k = N` (`x/0 = 0`).
Load-bearing, not decorative: it is consumed twice at the endpoint (lines 786, 788) to cross the
`ℝ`/`NNReal` boundary via `Real.le_toNNReal_iff_coe_le` and `Real.coe_toNNReal`. Direction of that
conversion checked: `↑mass ≤ ε` (ℝ) ↦ `mass ≤ ε.toNNReal` (NNReal), which is the shape the endpoint
wants.

**`sopEps_ge_one_of_large` — :680 — MINOR-1 (naming), math CLEAN**
(a) Elaborated: `∀ {N q k}, k < q → k < N → N ≤ 2*k → 1 ≤ ∑ j ∈ range q, ↑j^2/(↑N-↑j)^2`.
**The name mentions `sopEps` but the statement never does** — the conclusion is the *uncapped* sum.
It has no docstring. `_of_large` reads as "for large q/N" but the real content is "there exists one
index `k` past the half-way point". Substantively harmless: inside `mass_sopTightBad_le` the goal
after `le_min` *is* the uncapped sum, so the lemma is used exactly right. Hypotheses satisfiable
(e.g. `N=2, k=1, q=2`), so not vacuous.
(b) True: `k < N` gives `N−k > 0`; `N ≤ 2k` gives `N−k ≤ k`; so `(N−k)² ≤ k²` and the `k`-th term is
`≥ 1`; `Finset.single_le_sum` with nonneg terms lifts it to the sum.

**`mass_agree_and_good` — :520 — CLEAN**
(a) Statement is the product law
`mass_seed(realizes a ∧ good) = mass_URF(realizes a) · mass_seed(good)`, i.e. eq. (4.38) in the form
"conditioned on the monitor, the transcript is exactly URF-distributed **and** independent of the
monitor". The seed distribution is literally `Dist.uniform (Equiv.Perm G × Equiv.Perm G)`, the same
object `sopReal`/`sopTightGame` are built from — `uniform` on a product type is the product of two
independent uniforms (mass `1/(N!)²` per pair), so "two independent uniform permutations" is
faithfully modelled. The right-hand factor `Dist.uniform (G → G)` is literally `sopIdeal`'s seed.
Hypothesis `hl : ∀ x, x ∈ l ↔ x ∈ S` is exactly "l enumerates S", satisfiable (`l = []`, `S = ∅`
included); no unsatisfiable premise.
The `ã` total extension was checked in both directions (`hagree`, lines 534–545): forward uses
`hl.mp` + `dif_pos`, backward uses `hl.mpr s.2` + `Subtype.eta`. The default value `0` is arbitrary
and harmless because `card_goodAgree` is proved for an arbitrary total `a : G → G`.
Factor order verified from the live goal — see §1.1.
(b) True, and verified *exhaustively* rather than argued. Brute force over all `(N!)²` permutation
pairs, `N ∈ {2,3,4,5}`, lists `[]`, `[0]`, `[0,0]`, `[0,1]`, `[0,1,0]`, `[0,1,2]`, `[0,1,2,3]`,
`[1,0,1,2]`: the number of surviving pairs realizing a prescribed transcript is **constant across all
`N^d` transcripts** and equals `goodCount G d` in every single case. That constancy *is* the content
of this lemma. Sample: `N=5, l=[0,1,2]`: 14400 pairs, 7500 good, and every one of the 125 transcripts
is realized by exactly 60 — and `60 = 7500/125` is precisely
`mass(agree∧good) = N^{-3}·mass(good)`.
Non-vacuous: `mass(good) = 25/48 ≠ 0` there. Degenerate (`0 = 0`) only for `d ≥ ⌈N/2⌉+1`, which §1.3
shows is outside the range where `ε < 1`.

**`mass_good_eq_prod` — :610 — CLEAN**
(a) `hsmall : ∀ k < l.toFinset.card, 2*k < Fintype.card G` is genuinely needed and is used in exactly
one place, `hprod2` (line 633), to license `Nat.cast_sub` on the truncated `N − 2k`. Without it the
statement is *false*, not merely unprovable: for `2k > N` the ℕ factor is `0` (so the LHS mass is 0)
while the ℝ factor `1 − k²/(N−k)²` is negative and a product of two such factors is positive.
Correctly guarded. `[Nonempty G]` is omitted here (and in `mass_sopTightBad_le`), which is fine —
`Nonempty (Perm G × Perm G)` holds even for empty `G`.
The `hfac` step (`N! = (N−d)!·∏_{k<d}(N−k)`) routes through `Nat.factorial_mul_descFactorial hd` and
`Nat.descFactorial_eq_prod_range`, with the per-factor cast `((N−k : ℕ):ℝ) = (N:ℝ)−k` guarded by
`k < d ≤ N`. Correct.
(b) True, and it is an **exact equality with no slack**:
`(N−k)² − k² = N(N−2k)`, so `∏(1 − k²/(N−k)²) = N^d ∏(N−2k) / (∏(N−k))²`, which is exactly
`N^d·goodCount(d)/(N!)²`. Verified as an exact rational identity by brute force for every
`(N ≤ 5, l)` pair satisfying `hsmall`: `N=3,d=2 → 3/4`; `N=4,d=2 → 8/9`; `N=5,d=2 → 15/16`;
`N=5,d=3 → 25/48`. All matched to the last bit.
Minor docstring imprecision: "Below `N/2` distinct queries" — the hypothesis actually permits
`d = (N+1)/2` when `N` is odd (e.g. `N=5, d=3` is allowed and non-degenerate). Not worth a finding.

**`mass_sopTightBad_le` — :699 — CLEAN**
(a) Conclusion `↑mass(bad on l) ≤ sopEps (Fintype.card G) q`, `q` bounded via `hlen : l.length ≤ q`.
`refine le_min hmass_le_one ?_` means the `min` is not an escape hatch (§1.2). The case split
`hbig : ∃ k < d, N ≤ 2k` is exhaustive and its negation is turned into `hsmall` by
`mass_sopTightBad_le._proof_1_2` (trichotomy, see below).
Note: `hlen` is *stronger* than what the proof consumes — only `hdq : l.toFinset.card ≤ q` (line 703,
via `List.toFinset_card_le`) is used. That is the safe direction (a weaker lemma), and it is the
right interface for the blind-game caller, which can bound raw list length but not distinct-query
count. Not a defect.
Live goal at line 751 confirms the final `linarith [hone, hgood, hlow, hmono]` closes
`↑mass(bad) ≤ ∑_{k<q} k²/(N−k)²` from `mass(bad)+mass(good)=1`, `mass(good)=∏`, `∏ ≥ 1−Σ_d`,
`Σ_d ≤ Σ_q` — the chain is `1−∏ ≤ Σ_d ≤ Σ_q`, all four inequalities in the right direction.
(b) True. `hle1` (`k²/(N−k)² ≤ 1` for `k < d`) is exactly the Weierstrass side condition and follows
from `2k < N`; it is supplied for the same index range `k < d` that `chain_product_lower_bound`
demands. `hmono` uses `Finset.sum_le_sum_of_subset_of_nonneg` with nonnegativity only on the extra
indices — correct, and nonnegativity survives even the `k = N` division-by-zero index.
End-to-end sanity: exact-rational true statistical distance of the two systems vs `sopEps`, all
distinct-query schedules, `N ∈ {3..8}`, `q ∈ {2..5}` — **no violation in any of the 22 cases**, and at
`q = 2` the ratio is exactly `N/(N−1)` (1.500, 1.333, 1.250, 1.200, 1.167, 1.143 for `N = 3..8`),
confirming the file docstring's tightness claim at `q = 2` to the digit. At `q = 3` the bound is
already 3.5×–9× loose, so "tight" is correctly scoped to `q = 2` in the docstring.

**`mass_sopTightBad_le._proof_1_2` (auto) — CLEAN**
`∀ {G} [Fintype G] [DecidableEq G] (l : List G) (q k : ℕ), ¬2*k < card G → ¬card G ≤ 2*k → False`.
The `omega` inside `hsmall`'s `by_contra`. Trichotomy on ℕ; the `l`, `q`, `G` arguments are unused
noise from extraction. True.

### LIB nodes (13)

**`Counting.chain_product_lower_bound` — `Counting.lean:43` — CLEAN**
(a) `(∀ k < q, 0 ≤ f k) → (∀ k < q, f k ≤ 1) → ∏_{k<q}(1−f k) ≥ 1 − ∑_{k<q} f k`. Hypotheses
restricted to `k < q`, which is exactly the index range the product and sum touch — not silently
strengthened to `∀ k`, and not silently weakened. Direction is `≥` on the product side, which is what
`mass_sopTightBad_le` needs (a *lower* bound on survival = *upper* bound on firing).
(b) True (Weierstrass). Verified the underlying induction by hand: `∏·(1−a_last) ≥ (1−S)(1−a_last)`
needs `1−a_last ≥ 0` (from `a ≤ 1`) and then `= 1−S−a_last+S·a_last ≥ 1−S−a_last` needs `S·a_last ≥ 0`
(from nonneg) — both hints are present in the `nlinarith` call at `Counting.lean:38`.

**`Counting.prod_one_sub_ge_one_sub_sum` — `Counting.lean:27` — CLEAN**
The `Fin n` form `chain_product_lower_bound` delegates to. Hypotheses `∀ i, 0 ≤ a i` / `∀ i, a i ≤ 1`
over all of `Fin n` — the honest full-range form; the `range q` wrapper re-derives them from
`i.isLt`. Base case `n = 0`: `1 ≥ 1`. True.

**`Counting.card_function_fiber_finset` — `Counting.lean:345` — CLEAN**
(a) `#{f : X → Y | ∀ x : ↥S, f ↑x = g x} = |Y|^(|X| − S.card)`. No `Nonempty` needed; truncated
subtraction is safe because `S.card ≤ |X|` always. Proof is an explicit `Finset.card_bij` onto
`↥Sᶜ → Y`, so it is a real bijection argument, not a `decide`.
(b) True; edge cases `S = univ` (`1 = |Y|^0`) and `Y` empty both check out.
Used once, in `mass_agree_and_good`, to evaluate the URF-side count `#Q = N^{N−|S|}` — read off the
live goal at line 560, so the instantiation `X = Y = G` is confirmed, not assumed.

**`Counting.card_function_fiber_finset._simp_1_3` / `._simp_1_4` / `.match_1_1` (auto) — CLEAN**
`(a ∈ Finset.filter p s) = (a ∈ s ∧ p a)`, `(x ∈ Finset.univ) = True`, and the subtype-match motive
eliminator for `↥Sᶜ`. All three are standard, all true, none carry mathematical content.

**`Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq` — `Dist.lean:1317` — CLEAN**
See §1.1. One instance-coherence note checked and cleared: `Dist.mass` (`Dist.lean:150`) bakes in
`Classical.propDecidable` (file-local instance at `Dist.lean:62`), while this lemma's `Finset.filter`s
use the caller's `[DecidablePred _]`. `Decidable` is a subsingleton so the two filters are equal;
worst case this is a `rw` inconvenience, never a semantic difference. No diamond.

**`Dist.uniform_mass_eq_card_filter` — `Dist.lean:1306` — CLEAN**
`(uniform A).mass P = #(filter P univ) / |A|`. This is the single bridge from counting to
probability, and it is correct because `Dist.uniform` (`Dist.lean:431`) really is `1/|A|` pointwise
and `weight_uniform` (`Dist.lean:475`) proves it has total weight `1`. **This closes the "Dist is not
normalised" concern for this slice**: every distribution the mass layer touches is `Dist.uniform`,
which is a genuine probability distribution, so `mass` here is a genuine probability.

**`Dist.mass_eq_sum` — `Dist.lean:1281` — CLEAN**
`X.mass P = ∑ a, if P a then X a else 0` on a `Fintype` carrier. Correct rendering of the
`Finsupp.sum` definition (`Finsupp.sum_fintype` with the `ite_self` side condition). True.

**`Dist.mass.eq_1` (auto) — CLEAN** — the definitional equation for `mass`. True by `rfl`.

**`Dist.mass_add_compl` — `Dist.lean:205` — CLEAN**
`X.mass P + X.mass (¬P) = X.weight`. Note it lands on `weight`, **not** on `1` — the normalisation
has to be supplied separately, and `mass_sopTightBad_le` does supply it (`Dist.uniform_isProbDist`,
line 724). No smuggled normalisation. True.

**`Dist.mass_le_weight` — `Dist.lean:212` — CLEAN** — `mass P ≤ weight`, from `mass_add_compl` +
`le_self_add`. True in NNReal.

**`Dist.mass_le_one` — `Dist.lean:312` — CLEAN**
`X.isProbDist → X.mass P ≤ 1`. The `isProbDist` hypothesis is real and is discharged with
`Dist.uniform_isProbDist`. This is the `mass ≤ 1` half of `le_min` in `mass_sopTightBad_le`, and the
`exact_mod_cast` to ℝ is sound (NNReal→ℝ coercion is order-preserving). True.

## 3. Findings

**MINOR-1 — `sopEps_ge_one_of_large` name promises a statement it does not make.**
`SumOfPermutationsTight.lean:680`. The conclusion is `1 ≤ ∑ j ∈ range q, j²/(N−j)²`, the *uncapped*
sum; `sopEps` appears nowhere in the statement, and there is no docstring. `_of_large` also suggests
a largeness hypothesis on `q` or `N`, whereas the real hypothesis is "some index `k < q` has
`2k ≥ N`". Correct and correctly used; only a reader-facing mismatch.

**MINOR-2 — `mass_good_eq_prod` docstring says "Below `N/2`", hypothesis allows `⌈N/2⌉`.**
`SumOfPermutationsTight.lean:608`. `hsmall` admits `d = (N+1)/2` for odd `N` (e.g. `N=5, d=3`, where
the lemma is non-degenerate: mass `= 25/48`). Cosmetic.

**MINOR-3 — the `min 1` cap, not the construction, is what makes the "beats birthday" conjunct true
for `q > √N`.** The uncapped `Σ_{k<q} k²/(N−k)²` exceeds `q²/N` once `q ≳ 0.66 N` (measured: first
crossing at `q = 43` for `N = 64`, `q = 674` for `N = 1024`, `q = 43037` for `N = 65536`), so the
second conjunct of `sop_randomness_expander_tight` would be **false** without the cap, and the proof
discharges everything with `q² > N` by `min_le_left` — where the claim degenerates to `ε ≤ 1 < q²/N`
and says nothing about the construction. Substantive content survives only for `q ≤ √N`. The file
docstring already frames this conjunct as "a floor... merely excludes restating the birthday bound",
so this is a calibration note rather than a hidden defect. **The first conjunct — the actual security
bound — is not carried by any degenerate branch (§1.3).**

## 4. Not checked / out of slice

Everything in the 20-node slice was checked. Deliberately *not* checked (other slices own them):

* `card_good`, `card_goodAgree`, `goodCount_step`, `card_fresh_pair_refine`, `card_avail_fresh*`,
  `freshKeep`/`canonSubset` — the counting slice. I consumed `card_good` / `card_goodAgree` as
  black boxes in the Lean pass, but my brute force independently reproduced both for `N ≤ 5`, so
  they are corroborated, not assumed.
* `sopTight_condEquiv`, `condEquiv_of_transcript_mass_reductions`, the `decide`/`Prop` bridge, and
  the *meaning* of `|≡` against Maurer13b — the `condequiv-instantiation` slice. In particular the
  "empty good world for `d > N/2`" concern raised in the DAG belongs there; from this slice's side I
  can only report the quantitative fact in §1.3 (it never overlaps the range where `ε < 1`).
* `maxAdvantage_filterQueries_seededConditionCGame_le`, `blindQueryList`,
  `blindQueryList_length_le`, and whether a *fixed*-list bound suffices for an *adaptive*
  distinguisher — the `blind-game-endpoint` slice. `mass_sopTightBad_le` is uniform over lists of
  length `≤ q`, which is the right shape for that reduction, but I did not verify the reduction.
* The top-level `sop_randomness_expander_tight` second-conjunct arithmetic beyond the `min_le_left`
  branch (lines 800–838) — the root slice. I only measured where the cap becomes necessary.
* Papers: I did not open `MaPiRe07.pdf` / `Maurer13b.pdf` for this slice; nothing in the mass layer
  cites a paper statement. The `q = 2` "true distance `1/(N(N−1))`" claim in the file docstring I
  verified by direct computation instead, and it is exactly right.
