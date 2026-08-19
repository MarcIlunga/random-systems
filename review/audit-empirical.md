# Audit slice `empirical` — `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight`

Reviewer: adversarial pass, **read-only**. No proof or framework file was modified.
Four reproducible probes live next to this report:

| probe | reproduce with |
|---|---|
| `review/slice-empirical.brute-force-adaptive.py` | `uv run python3 review/slice-empirical.brute-force-adaptive.py` |
| `review/slice-empirical.exact-tv-large-N.py` | `uv run --with numpy python3 review/slice-empirical.exact-tv-large-N.py` |
| `review/slice-empirical.probe-eval.lean` | `lake env lean review/slice-empirical.probe-eval.lean` |
| `review/slice-empirical.probe-attainment.lean` | `lake env lean review/slice-empirical.probe-attainment.lean` |
| `review/slice-empirical.probe-degenerate.lean` | `lake env lean review/slice-empirical.probe-degenerate.lean` |

All five were re-run from those paths and pass. The two `.lean` probes are sorry-free; the
attainment theorems print `[propext, Classical.choice, Quot.sound]`.

> **Build note.** `RandomSystems/PermFreshCounting.olean` and
> `RandomSystems/SumOfPermutationsTight.olean` did not exist in `.lake/build` — neither module is
> reachable from the `RandomSystems` default target, and `lake build RandomSystems.SumOfPermutationsTight`
> silently builds the *default lib* instead of the named module (name-prefix match). I produced the
> two oleans with `lake env lean <file> -o <olean>`. Only `RandomSystemsApplications` reaches these
> modules. Not a defect of the theorem; a build-target ergonomics note.

---

## Verdict

**CLEAN on the empirical axis.** Every number the theorem and its docstring claim checks out
against independent enumeration, at every instance I could reach:

* the reference point holds **exactly**: the true `q = 2` advantage is `1/(N(N−1))` and
  `sopEps N 2 = 1/(N−1)²`, ratio `N/(N−1)`, for every `N` tested (2 … 28);
* `sopReal`'s transcript law, evaluated **in Lean from the repo's own `sopFunction`**, is
  digit-for-digit the XoP law computed independently;
* the bound is never violated: 78 `(group, q)` instances, `N ≤ 28`, `q ≤ 5`, including four
  **non-cyclic** abelian groups;
* every degenerate regime behaves, and two of them are *knife-edge exact* (`q = 0` and `q = 1`
  force `Δ = 0`, and the truth is `0`);
* **the left-hand side is not vacuous.** I built a concrete distinguisher in Lean and
  kernel-checked `Δ(⌈2⌉sopReal, ⌈2⌉sopIdeal) ≥ 1/2, 1/6, 1/12` at `ZMod 2/3/4` — exactly the
  true values. Every other probe in this review bounds `Δ` from above; a definition that
  deflated `Δ` (broken `verdict`, broken `filterQueries`, an empty distinguisher class) would
  survive all of them and die here. It does not die here.

Two **MINOR** observations are recorded in §7: a division-by-zero artefact in `sopEps` at `N = 1`
that is harmless but load-bearing-adjacent, and the honest range in which the bound says anything.
No CRITICAL or MAJOR finding on this axis. The statement-strength defect found by the
`sop-statement-and-semantics` slice is real and I reproduce it in §6 from the empirical side, but
it is that slice's finding, not mine.

---

## 1. What "true advantage" means here, and how I computed it

`Δ(S,T) = sup_D (Pr^{DT}[Z=1] − Pr^{DS}[Z=1])` over probability-distribution distinguishers
(`RandomSystems/Distinguishing.lean:136`) — a **signed** supremum. For two random-function
systems under `⌈q⌉`, that supremum equals

```
V([], q)   where   V(h,0) = max(0, P_ideal(h) − P_real(h))
                   V(h,d) = max( V(h,0), max_{x ∉ h} Σ_y V(h+(x,y), d−1) )
```

The recursion ranges over **adaptive** strategies, so I did not assume the folklore
"non-adaptive is WLOG" reduction — I let the enumeration discover it. (It does: the adaptive
optimum coincides with the non-adaptive `q`-distinct-query total variation at every instance
where I computed both, `N ≤ 9`, `q ≤ 5`. That independently corroborates the WLOG argument the
sibling slice's script *assumes*.)

`P_real(h)` is counted over all `(π₁,π₂) ∈ S_N²` directly for `N ≤ 4`, and by the equivalent
injective-tuple count for larger `N`; the two agree wherever both ran.

---

## 2. True advantage vs `sopEps` — cyclic groups, full adaptive enumeration

`ε(N,q) = min 1 (Σ_{k<q} k²/(N−k)²)`, evaluated with Lean's division convention (`x/0 = 0`).

| N | q=0 | q=1 | q=2 | q=3 | q=4 | q=5 |
|---|---|---|---|---|---|---|
| **1** true | 0 | 0 | 0 | 0 | 0 | 0 |
| ε | 0 | 0 | **0** | 1 | 1 | 1 |
| **2** true | 0 | 0 | **1/2** | 1/2 | 1/2 | 1/2 |
| ε | 0 | 0 | 1 | 1 | 1 | 1 |
| **3** true | 0 | 0 | **1/6** | 2/3 | 2/3 | 2/3 |
| ε | 0 | 0 | **1/4** | 1 | 1 | 1 |
| **4** true | 0 | 0 | **1/12** | 5/48 | 3/4 | 3/4 |
| ε | 0 | 0 | **1/9** | 1 | 1 | 1 |
| **5** true | 0 | 0 | **1/20** | 19/300 | 391/3000 | 4/5 |
| ε | 0 | 0 | **1/16** | 73/144 | 1 | 1 |
| **6** true | 0 | 0 | **1/30** | 1/18 | 31/450 | — |
| ε | 0 | 0 | **1/25** | 29/100 | 1 | — |
| **7** true | 0 | 0 | **1/42** | 67/1470 | 9917/205800 | — |
| ε | 0 | 0 | **1/36** | 169/900 | 2701/3600 | — |

**`true ≤ ε` at every entry.** No violation.

**Reference point 1 — the `q = 2` true distance.** The brief said it should be `1/(N(N−1))`.
Confirmed as an exact rational identity for `N = 2 … 9` (adaptive enumeration) and `N = 8, 10,
12, 16, 20, 24, 28` (closed form): `1/2, 1/6, 1/12, 1/20, 1/30, 1/42, 1/56, 1/72, 1/90, 1/132,
1/240, 1/380, 1/552, 1/756`.

**Reference point 2 — `ε` at `q = 2`.** The brief said it should be `1/(N−1)²`. Confirmed, and
verified *inside Lean* by `norm_num` on the repo's `sopEps` at `N = 2,3,4,5`
(`probe-eval.lean`): `1, 1/4, 1/9, 1/16`.

**Ratio `ε/true` at `q = 2` is exactly `N/(N−1)`** — the docstring's "tight up to `N/(N−1)`"
claim (line 28) is correct: `2.00, 1.50, 1.33, 1.25, 1.20, 1.17, 1.14 …`

---

## 3. Non-cyclic abelian groups

`ε` depends on the group **order only**, so a group-structure dependence in the truth would
break the theorem. I checked every abelian group of order 4, 8 and 9:

| group | q=2 | q=3 |
|---|---|---|
| `Z4` | 1/12 | 5/48 |
| `Z2×Z2` | 1/12 | 5/48 |
| `Z8` | 1/56 | 25/672 |
| `Z4×Z2` | 1/56 | 25/672 |
| `Z2×Z2×Z2` | 1/56 | 25/672 |
| `Z9` | 1/72 | 139/4536 |
| `Z3×Z3` | 1/72 | 139/4536 |

**Identical within each order** (also at `q = 4` for order 4: `3/4` for both). The
order-only parametrisation of `ε` is not an over-claim.

---

## 4. The scaling question — does the bound ever get overtaken?

This is the one place small-`N` data can lie. `ε ≈ q³/3N²`. The literature's tight upper bound
for XoP2 (Dai–Hoang–Steinberger) is `q^{1.5}/N^{1.5}`, and `q^{1.5}/N^{1.5} ≫ q³/3N²` for
`q ≪ √N`. **If the truth actually scaled like `q^{1.5}/N^{1.5}`, `ε` would be crossed and the
theorem would be false.** Extrapolating naively from `N ≤ 9` at `q = 3` I got a fitted exponent
near `N^{-1.5}` and a predicted crossing around `N ≈ 36` — so I computed it exactly.

`q = 3`, exact, via the closed-form count (validated against the adaptive enumeration for
`N ≤ 9`):

| N | true TV | ε(N,3) | true/ε | true·N² |
|---|---|---|---|---|
| 10 | 0.025555556 | 0.074845679 | 0.341 | 2.556 |
| 16 | 0.010788690 | 0.024852608 | 0.434 | 2.762 |
| 32 | 0.002826781 | 0.005485027 | 0.515 | 2.895 |
| 64 | 0.000720296 | 0.001292535 | 0.557 | 2.951 |
| 128 | 0.000181633 | 0.000313953 | 0.579 | 2.976 |
| 256 | 0.000045595 | 0.000077379 | 0.589 | 2.988 |
| 512 | 0.000011422 | 0.000019208 | 0.595 | 2.994 |
| **1024** | **0.000002858** | **0.000004785** | **0.597** | **2.997** |

`true·N² → 3` and `true/ε → 3/5`. The scaling is `Θ(N^{-2})`, **not** `N^{-1.5}`; my small-`N`
extrapolation was a finite-size artefact. No crossing. The `q^{1.5}/N^{1.5}` bound is simply
not tight at fixed small `q`.

`q = 4` and `q = 5`:

| N | q | true TV | ε(N,q) | true/ε | true·N² |
|---|---|---|---|---|---|
| 12 | 4 | 0.026849939 | 0.159375574 | 0.169 | 3.87 |
| 16 | 4 | 0.017261866 | 0.078107046 | 0.221 | 4.42 |
| 20 | 4 | 0.011866208 | 0.046257631 | 0.257 | 4.75 |
| 24 | 4 | 0.008614889 | 0.030562985 | 0.282 | 4.96 |
| 28 | 4 | 0.006523933 | 0.021688902 | 0.301 | 5.11 |
| 7 | 5 | 0.074729279 | 1 | 0.075 | 3.66 |
| 8 | 5 | 0.058862139 | 1 | 0.059 | 3.77 |
| 9 | 5 | 0.045981705 | 0.987257653 | 0.047 | 3.72 |
| 10 | 5 | 0.037471974 | 0.702963593 | 0.053 | 3.75 |

`true·N²` converges to `≈1, 3, ≈5.7` for `q = 2, 3, 4` against `ε`-coefficients `1, 5, 14`.
The slack **grows** with `q` in this window. Reading the coefficients as `c_q`, they sit between
`q²` and `q³` (`c_q/q^{2.5} ≈ 0.18` at `q = 2,3,4`), comfortably under `ε`'s `q³/3`.

**Coverage limit, stated honestly.** This settles the question for `q ≤ 5`. It does *not* settle
`q` in the interesting asymptotic window `q ~ N^{2/3}`, which is computationally out of reach
(the state space is `N^q`). The proof is machine-checked, so soundness there rests on the
framework, not on my numbers.

---

## 5. What the objects actually evaluate to in Lean

### 5.1 Computability status (asked for explicitly by the brief)

| object | computable? | why |
|---|---|---|
| `sopFunction` | **yes** | plain `π₁ x + π₂ x` |
| `goodCount` | **yes** | factorials and a `Finset.prod` over `ℕ` |
| `sopEps` | no (`ℝ`), but `norm_num`-decidable | closed form |
| `sopReal`, `sopIdeal` | no | `Dist.uniform` uses `Finsupp.equivFunOnFinite`, division in `ℝ≥0` |
| `freshKeep`, `sopFresh`, `sopTightBad` | **no, and not `decide`-able either** | `Counting.canonSubset` is `(Finset.exists_subset_card_eq h).choose`; `sopTightBad_decidable` is `Classical.dec` |

So the monitored condition itself cannot be evaluated at a point, by `#eval` or by `decide`.
Where the definitions were not computable I went through the mass/cardinality API
(`Dist.uniform_mass_eq_card_filter`, `Dist.mass_fTransform`) and `decide`d the resulting
`Finset.card`, which *is* an evaluation of the repo's own definitions and not a re-implementation.
What remains genuinely unchecked is listed in §8.

### 5.2 `sopReal`'s transcript law — 2 queries (`#eval`, `probe-eval.lean`)

Fiber counts `#{p : sopFunction p x₀ = a ∧ sopFunction p x₁ = b}`:

| carrier | total pairs | diagonal `a=b` | off-diagonal |
|---|---|---|---|
| `ZMod 2` | 4 | **2** (= 1/2) | **0** |
| `ZMod 3` | 36 | **6** (= 1/6) | **3** (= 1/12) |
| `ZMod 4` | 576 | **48** (= 1/12) | **32** (= 1/18) |

Theory: `1/(N(N−1))` on the diagonal and `(N−2)/(N(N−1)²)` off it — `1/6, 1/12`; `1/12, 1/18`.
**Exact match.** The `ZMod 2` row is the docstring's own remark (line 57, "in `ℤ/2` with two
distinct queries the two answers always agree") — confirmed: the off-diagonal count is `0`.

3 queries over `ZMod 3`: support is exactly the 9 triples with `y₀+y₁+y₂ = 0`, counts `6` on the
three constant triples and `3` on the six others; total `18+18 = 36`. Total variation against
uniform-on-27: `2/3` — which is what the adaptive enumeration returns for `N=3, q=3`.

### 5.3 `goodCount` and the surviving mass (`#eval`, `probe-eval.lean`)

`#eval goodCount (ZMod N) d`:

| N | d=0 | d=1 | d=2 | d=3 |
|---|---|---|---|---|
| 2 | 4 | 2 | **0** | — |
| 3 | 36 | 12 | 3 | **0** |
| 4 | 576 | 144 | 32 | **0** |
| 5 | 14400 | 2880 | 540 | 60 |

Derived good-world mass `N^d · goodCount d / (N!)²` (this is `card_good` divided by
`Fintype.card (Perm G × Perm G)`), against `mass_good_eq_prod`'s claim `∏_{k<d}(1 − k²/(N−k)²)`:

| N, d | good mass | `∏(1 − k²/(N−k)²)` | `mass bad` | `sopEps N d` |
|---|---|---|---|---|
| 2, 2 | 4·0/4 = **0** | — (`hsmall` fails) | 1 | 1 |
| 3, 2 | 9·3/36 = **3/4** | 3/4 ✓ | **1/4** | **1/4** (exact) |
| 3, 3 | **0** | — | 1 | 1 |
| 4, 2 | 16·32/576 = **8/9** | 8/9 ✓ | **1/9** | **1/9** (exact) |
| 4, 3 | **0** | — | 1 | 1 |
| 5, 2 | 25·540/14400 = **15/16** | 15/16 ✓ | **1/16** | **1/16** (exact) |
| 5, 3 | 125·60/14400 = **25/48** | (15/16)(5/9) = 25/48 ✓ | 23/48 ≈ 0.479 | 73/144 ≈ 0.507 |

Three independent confirmations here: (a) the product formula matches the count; (b) the
Weierstrass step (`chain_product_lower_bound`) is *exact* at `d ≤ 2` (single non-zero term) and
loses `0.028` at `N=5, d=3` — the right order; (c) `goodCount` hits `0` exactly when `2k ≥ N`
for some `k < d`, i.e. `freshKeep` empties, matching the docstring's line 58 and pushing the
proof onto the `sopEps_ge_one_of_large` branch, where `ε = 1` — verified: `ε(2,2) = ε(3,3) =
ε(4,3) = 1`.

---

## 6. Attainment — the left-hand side is real (kernel-checked)

`review/slice-empirical.probe-attainment.lean` constructs, generically in `G`, the
`PFunDDS.DDD G G`

```
d []            = inl x₀
d [_]           = inl x₁
d (y₁::y₂::_)   = inr (decide (y₁ ≠ y₂))
```

proves `StopFinal`, unrolls `PFunDDS.transcript` against
`PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f)` (through `fullyDefined`/`keptPrefix`),
and proves

```
PFunDDS.verdict (dsep x₀ x₁) (⌈2⌉ functionEvaluator f) ↔ f x₀ ≠ f x₁
```

then computes both verdict probabilities from `Dist.mass_fTransform` +
`Dist.uniform_mass_eq_card_filter` + `decide` on the `Finset.card`s:

| carrier | `Pr[ideal says 1]` | `Pr[real says 1]` | `advantage` | true `Δ` (brute force) | `sopEps N 2` |
|---|---|---|---|---|---|
| `ZMod 2` | 2/4 | 0/4 | **1/2** | **1/2** | 1 |
| `ZMod 3` | 18/27 | 18/36 | **1/6** | **1/6** | 1/4 |
| `ZMod 4` | 192/256 | 384/576 | **1/12** | **1/12** | 1/9 |

and concludes, via `advantage_le_maxAdvantage`:

```
lb_zmod2 : (1:ℝ)/2  ≤ Δ(⌈2⌉ sopReal, ⌈2⌉ sopIdeal)   -- G = ZMod 2
lb_zmod3 : (1:ℝ)/6  ≤ Δ(⌈2⌉ sopReal, ⌈2⌉ sopIdeal)   -- G = ZMod 3
lb_zmod4 : (1:ℝ)/12 ≤ Δ(⌈2⌉ sopReal, ⌈2⌉ sopIdeal)   -- G = ZMod 4
```

`#print axioms lb_zmod2 / lb_zmod3` → `[propext, Classical.choice, Quot.sound]`.

**Why this matters.** All the other evidence in this review is of the form `Δ ≤ something`. A
`Δ` that were degenerately small — an uninhabited or crippled distinguisher class, a `verdict`
predicate never satisfiable, a `filterQueries` that blanked every answer — would make every
upper bound in the development true and meaningless. These three theorems rule that out at the
carrier where the pathology would be easiest to hide (`ZMod 2`, where `freshKeep` empties
immediately). Combined with the sibling slice's `explicit_bound`, `ZMod 3, q = 2` is pinned:
`1/6 ≤ Δ ≤ 1/4`, with the truth `1/6`.

**Side observation reproduced from the empirical angle** (this is the
`sop-statement-and-semantics` slice's MAJOR finding, not a new one): I proved in
`probe-attainment.lean` that *everything the ∃-statement yields at `ZMod 3, q = 2`* is
`Δ < 4/3` (`statement_content_zmod3`) — vacuous, since `Δ ≤ 1` always. The `1/4` is only
reachable by re-running the proof's `calc` chain, because there is no exported
`Δ ≤ sopEps (card G) q` corollary. Empirically: at every instance I tested, the *statement*
carries no numeric content beyond `Δ < q²/N`, and for `q² ≥ N` not even that.

---

## 7. Degenerate regimes

All verified in Lean (`probe-degenerate.lean`, `probe-attainment.lean`) unless noted.

**`q = 0`.** `⌈0⌉` makes even the first query return `⊥`
(`first_answer_bot_of_zero`), and `⌈0⌉ sopReal = ⌈0⌉ sopIdeal` as `PFunPDS` values
(`filterQueries_zero_eq`) — both collapse to the point mass on the nowhere-defined DDS. So
`Δ = 0`, and `sopEps N 0 = 0`. **The bound is exactly tight here**, not merely valid.

**`q = 1`.** `sopEps N 1 = 0` for every `N` (`q_one_is_exact`), and `Δ ≥ 0` always
(`maxAdvantage_nonneg`, proved from `rejectDistinguisher`). So the theorem's `q = 1` instance
asserts **`Δ = 0` exactly: one query is perfectly secure.** That is a knife-edge claim — any
upward miscalibration of `Δ`, or any off-by-one in `⌈q⌉` letting a second query through, would
falsify it. Brute force: the true `q = 1` advantage is `0` for every group tested. ✓
(For a single query `π₁x + π₂x` is genuinely uniform: `π₁x` alone already is.)

**`⌈q⌉` truncates at exactly `q`, no off-by-one either way.** Proved for `functionEvaluator`:
with the filter at `1` the **second** answer is `none`; with the filter at `2` the second answer
is `some (f x₁)` and the **third** is `none`. (`second_answer_bot`, `second_answer_ok`,
`third_answer_bot`.)

**`q ≥ N`.** `sopEps N q = 1` for all `q ≥ N`, `N ≥ 2`: the `k = N−1` term alone is
`(N−1)²/1 ≥ 1`. Trivial but sound. True advantages there: `1/2 (N=2), 2/3 (N=3), 3/4 (N=4),
4/5 (N=5)` — i.e. `1 − 1/N`, which is what a distinguisher gets from the parity constraint
`Σ_x f(x) = 2Σ_x x`.

**`N = 2`, where `freshKeep` empties immediately.** `goodCount (ZMod 2) 2 = 0`, so `card_good`
gives *zero* surviving permutation pairs from the second distinct query on, the conditional
equivalence holds as `0 = 0`, and `mass bad = 1 = sopEps 2 2`. The docstring (lines 54–60) says
exactly this. True advantage `1/2`, bound `1`: sound, uninformative, correctly documented.

**`N = 1`.** `Fintype.card G = 1`; `sopReal` and `sopIdeal` are literally the same system, true
advantage `0`. `sopEps 1 2 = 0` — **and it is `0` only because of Lean's `x/0 = 0`**: the `k=1`
term is `1/(1−1)² = 1/0 = 0`. See §7.1.

### 7.1 MINOR — `sopEps`'s division-by-zero artefact

`sopEps N q` sums `k²/((N:ℝ)−k)²` for `k < q` with no guard on `k = N`. In Lean the `k = N` term
is `N²/0 = 0`, so the summand *silently vanishes* exactly where the real-analytic expression
diverges. Verified in Lean (`N_one_quirk`):

```
sopEps 1 2 = 0     -- the k=1 term is 1/0 = 0
sopEps 1 3 = 1     -- the k=2 term is 4/1 = 4, so the cap fires
```

I checked whether this can ever make `ε` **too small**: it cannot, because `k = N` is only
reached when `q > N`, and then `k = N−1 < q` already contributes `(N−1)² ≥ 1` for `N ≥ 2`,
capping `ε` at `1`. The single surviving case is `N = 1, q = 2`, where `ε = 0` and the true
advantage is also `0` — sound by accident, not by design. `mass_sopTightBad_le` never touches
the `k = N` term either (`hbig` only produces `k < l.toFinset.card ≤ N`).

**Not a defect today; a trap for tomorrow.** Any future strengthening of the cap (dropping the
`min 1`, or re-deriving `ε` in a form without it) inherits a summand that is `0` where it should
be `+∞`. Worth a comment at `sopEps` (`SumOfPermutationsTight.lean:600`) recording that the
`k ≥ N` terms are junk and that soundness at `q > N` rests on the `k = N−1` term, not on them.

### 7.2 MINOR — the honest range in which the bound says anything

`ε < 1` (the only range where the theorem beats "advantage ≤ 1") holds up to
`q* ≈ (3N²)^{1/3} ≈ 1.44 N^{2/3}`:

| N | largest `q` with `ε(N,q) < 1` | `√N` | ratio `q*/√N` |
|---|---|---|---|
| 2^4 | 7 | 4 | 1.75 |
| 2^8 | 52 | 16 | 3.25 |
| 2^12 | 353 | 64 | 5.52 |
| 2^16 | 2 303 | 256 | 9.0 |
| 2^20 | 14 781 | 1 024 | 14.4 |
| 2^24 | 94 253 | 4 096 | 23.0 |
| 2^64 | ≈ 2^42.9 | 2^32 | ≈ 2^10.9 |
| 2^128 | ≈ 2^85.9 | 2^64 | ≈ 2^21.9 |

So the result **is** genuinely beyond birthday — a real `N^{1/2} → N^{2/3}` improvement, and at
`N = 2^128` that is `2^64 → 2^85.9`. It is also far from what XoP is believed to give
(`~N`), which the docstring says (lines 766–768). No over-claim; recorded so the number is on
the table.

I also scanned the second conjunct `∀ N q, 1 < q → q < N → ε N q < q²/N` exhaustively for
`2 ≤ N < 120`: **no violations**, as expected from a machine-checked statement. Note however
that it is only a *constraint* when `q² < N`; for `q > √N` the clause is satisfied by `ε ≡ 1`.
That is the sibling slice's finding, quantified.

---

## 8. Coverage — what I checked and what I did not

**Empirically exercised: 31 objects.**

*From `SumOfPermutationsTight.lean` (14 of 34 declarations):* `sopFunction`, `sopReal`,
`sopIdeal`, `sopEps`, `sopEps_nonneg`, `sopEps_ge_one_of_large`, `goodCount`, `goodCount_step`,
`card_good`, `mass_good_eq_prod`, `mass_sopTightBad_le`, `freshKeep`/`card_freshKeep` (through
`goodCount`'s zeros), `sop_randomness_expander_tight`.

*Framework objects re-derived or evaluated (17):* `maxAdvantage`, `advantage`,
`advantage_le_maxAdvantage`, `verdictProb`, `GamePerf.winProb`, `PFunPDS.filterQueries`,
`PFunDDS.filterQueries`, `PFunDDS.functionEvaluator`, `PFunDDS.fullyDefined`,
`PFunDDS.keptPrefix`, `PFunDDS.transcript`, `PFunDDS.verdict`, `PFunDDS.ddToDDE`,
`PFunDDS.StopFinal`/`DDD`, `Dist.uniform`, `Dist.fTransform`/`Dist.mass`, `PFunPDS.URF`.

**Not empirically checkable — stated plainly (7 declarations).** `freshFiber`,
`mem_freshFiber`, `card_freshFiber_ge`, `sopFresh`, `sopTightBad` (+ `_monotone`, `_concat`,
`_congr`), `card_avail_fresh_answer`, `card_avail_fresh`, `card_goodAgree`,
`mass_agree_and_good`, `sopTight_condEquiv`, `sopTightGame`, `sopTightGame_ignoreMBO`. Two
reasons:

1. `Counting.canonSubset` is defined by `Exists.choose`, and `sopTightBad_decidable` is
   `Classical.dec` over an `∃ pre : List G`. Neither `#eval` nor `decide` can touch them; there
   is no numeric handle on "did the monitor fire at this `(π₁,π₂,l)`".
2. Consequently I verified the counting chain only **in aggregate** — `card_good`'s consequence
   (the surviving mass) matched `∏(1 − k²/(N−k)²)` at `N = 2,3,4,5` — and **not** per-transcript.
   In particular `card_goodAgree`'s key property, *independence of the prescribed transcript `a`*
   (which is what eq. (4.38) / the conditional equivalence rests on), was **not** exercised at a
   concrete `a`. That is the counting-core slice's territory and it should not be assumed covered
   by this report.

Also not checked here: `q ≥ 6` at any `N`, and any `N > 28` at `q ≥ 4` (state space `N^q`);
`sopTightGame`'s MBO wiring; the blind-game reduction.
