# Adversarial review — DAG slice `sop-counting-core`

Reviewer: subagent. Read-only; no proof file touched. Scratch under my session scratchpad and
`/tmp/sopcheck*.lean` only.

**Verdict: no defect found. 34 / 34 nodes checked, all CLEAN. Three MINOR notes (two
documentation, one reuse trap), no MAJOR, no CRITICAL.**

---

## 0. Method

Two independent passes per node, as instructed.

**(a) Lean check.** I did *not* trust the source text. I elaborated every declaration in the
slice and read the **elaborated types** (`#check @…`, `#print`) against a build using the
existing olean set:

```
LEAN_PATH=".lake/verify-rs-prover-d0/lib/lean:.lake/build/lib/lean" lake env lean /tmp/sopcheck*.lean
```

(`.lake/build/lib/lean` has no `SumOfPermutationsTight.olean`; `.lake/verify-rs-prover-d0`
does. Nothing was rebuilt.) Every printed type matched the source verbatim — no silently
inserted/omitted hypothesis, no instance surprise. Axiom check re-confirmed:
`card_good`, `card_goodAgree`, `card_avail_fresh_answer` each depend on exactly
`[propext, Classical.choice, Quot.sound]`.

**(b) Math check.** I re-derived every claim on paper, then built an **independent
brute-force model in Python** that mirrors the *definitions* (not the proofs) and enumerated
`S_N × S_N` exhaustively. This is the strongest available check because it validates the
composite `card_good` / `card_goodAgree` end-to-end, including the `card_fresh_pair_refine`
step that lives in another slice.

Model: `freshFiber`, `canonSubset` (with the `if m ≤ |s| … else s` branch), `freshKeep`
(with **truncated** `max(0, N − 2|U|)`), `sopFresh`, `sopTightBad` (first-occurrence
scan), `goodCount`, `availPairs` — all transcribed from `#print` output, and keyed exactly
as Lean keys them (`canonSubset` is memoised on `(frozenset, m)`, matching the fact that Lean's
`canonSubset` is a function of the *set* `freshFiber U V y` and `m`, not of `(U,V,y)`).

Because `canonSubset` is choice-defined, I ran **three different selection rules** —
lexicographic-first, lexicographic-last, and an MD5-seeded pseudo-random one — to test the
claim "no argument depends on which subset is chosen".

---

## 1. What the brute force established

| check | scope | result |
|---|---|---|
| `card_avail_fresh_answer` + `card_avail_fresh` | **all** `U,V` with `\|U\|=\|V\|`, **all** `c`, for `Z/3, Z/4, (Z/2)², Z/5` (all `k`) and `Z/6` (`k ≤ 3`); × 3 selection rules | exact match, incl. the degenerate `2k ≥ N` regime (count = 0) |
| `card_good` | **all** lists of length ≤ N over `Z/3`, `Z/4`, `(Z/2)²` (i.e. 3+9+27+81 = 120 lists for N=3, 341 for N=4, twice) × 3 selection rules; plus 13 sampled lists over `Z/5` × 2 rules | exact match |
| `card_goodAgree`, **every** prescribed `a` | `Z/3, Z/4, (Z/2)²`, `l ∈ {[0],[0,1],[1,0],[0,1,0,1],[0,1,2]}`, full enumeration of `a : S → G` (up to 4³ = 64 assignments) | exact match — count independent of `a` |
| `card_goodAgree`, sampled `a` | all lists of length ≤ N for N=3,4 (both groups), × 3 rules | exact match |
| choice-independence | all of the above under first / last / hash selection | identical counts every time |

Cross-validated against Lean's own arithmetic: `#eval goodCount (ZMod 5) k` gives
`(14400, 2880, 540, 60, 0)` for `k = 0..4` and `#eval Fintype.card (ZMod 5)^2 * goodCount (ZMod 5) 2 = 13500`
— exactly the exhaustive counts over the 14 400 permutation pairs of `Z/5`. `(5!)² = 14400 = goodCount 0`.

**Non-vacuity is established, not assumed.** `goodCount (ZMod 5) 2 = 540 ≠ 0`,
`goodCount (ZMod 6) 3 = 1728 ≠ 0`. The good-world mass profile (exhaustive):

```
Z/6:  d=0 1.000   d=1 1.000   d=2 0.960   d=3 0.720   d=4 0.000
      ∏(1−k²/(N−k)²): 1.000    1.000       0.960       0.720       0.000
```

so at `d = 3, N = 6` the monitored condition survives with probability 0.72 and eq. (4.38)
holds there over `6³ = 216` distinct transcripts with `goodCount = 1728` pairs each. The
theorem is **not** only true in the degenerate `2k ≥ N` regime.

Also worth recording for the neighbouring `mass-layer-and-epsilon` slice: `card_good / (N!)²`
equals `∏_{k<d}(1 − k²/(N−k)²)` **exactly** (verified N = 4, 5, 6, all `d`). The counting leaf
is *tight*, not slack; the only slack introduced downstream is Weierstrass (product → sum).

---

## 2. Per-node findings

### 2.1 `canonSubset` layer (`RandomSystems/PermFreshCounting.lean`)

* **`Counting.canonSubset` (:42) — CLEAN.** `#print` gives
  `fun {α} s m => if h : m ≤ s.card then ⋯.choose else s`. `Exists.choose` on
  `Finset.exists_subset_card_eq : n ≤ s.card → ∃ t ⊆ s, t.card = n` (statement verified).
  It is a genuine *function* of `(s, m)` — `Exists.choose` depends on the proof term, but
  proof irrelevance makes that a function of the Prop, so `canonSubset s m` is well-defined
  and deterministic. No `DecidableEq`/`Fintype` needed; universe-polymorphic in `α`. ✔
* **`canonSubset_subset` (:45) — CLEAN.** Holds in *both* branches (the `else` branch returns
  `s`, and `s ⊆ s`). Statement is unconditional, and correctly so.
* **`canonSubset_card` (:52) — CLEAN.** Hypothesis `m ≤ s.card` is present, load-bearing
  (the `else` branch gives `s.card ≠ m`), and satisfiable. ✔

### 2.2 The fibre (`SumOfPermutationsTight.lean`)

* **`freshFiber` (:99) — CLEAN.** `(univ \ U).filter (fun u => y − u ∉ V)`. Docstring "the
  values available to `π₁ x` that give answer `y` without repeating a used value" is exact:
  `u` is `π₁ x`, `y − u` is `π₂ x`.
* **`mem_freshFiber` (:103) — CLEAN.** `u ∈ freshFiber U V y ↔ u ∉ U ∧ y − u ∉ V`. Both
  conjuncts present, no strengthening. Instance args coherent (`DecidableEq G` for both the
  `\` and the `∉ V`).
* **`card_freshFiber_ge` (:110) — CLEAN, and tight enough.**
  `N − (|U| + |V|) ≤ |freshFiber U V y|`. Math: `|freshFiber| = N − |U ∪ (y−V)| =
  N − |U| − |V| + r(y)` with `r(y) = #{(a,b) ∈ U×V : a+b=y}`, so `≥ N−|U|−|V|` with equality
  iff `r(y)=0`. That is exactly the inequality `card_freshKeep` needs, and it is achieved
  (some `y` has `r(y) = 0` whenever `k² < N`), so it is not over-conservative. Truncated
  `ℕ` subtraction only makes the LHS `0`, i.e. weaker, never false. The `omega` closes
  from `A + B = N − |U|`, `B ≤ |V|`, `|freshFiber| = A` — all three correct. ✔
* **`freshKeep` (:128) — CLEAN as a definition** (see MINOR-1 / MINOR-2 for the docstring and
  the asymmetry). `canonSubset (freshFiber U V y) (Fintype.card G − 2 * U.card)`.
* **`freshKeep_subset` (:132) — CLEAN.** Unconditional; correct in both `canonSubset` branches.
* **`card_freshKeep` (:136) — CLEAN.** `U.card = V.card → (freshKeep U V y).card = N − 2|U|`.
  I confirmed `hUV` is **genuinely load-bearing, not decoration**: brute force over `Z/5`
  found **575** counterexamples to the `|U| ≠ |V|` version of the answer-count, and e.g.
  `U = ∅, V = {0}, y = 0` gives `|freshKeep| = 4 ≠ 5 = N − 2|U|` (the `else` branch of
  `canonSubset` fires). Both call sites discharge `hUV` via
  `Finset.card_image_of_injective _ p.i.injective` (`himgcard`, lines 337–341 and 427–431). ✔
* **`sopFresh` (:142) — CLEAN.** `u ∈ freshKeep U V (u + v)`. Note it *implies* `u ∉ U` and
  `v ∉ V` (via `freshKeep_subset` + `mem_freshFiber`, since `(u+v) − u = v`), so the monitor
  subsumes freshness without adding a constraint that a permutation pair could violate —
  confirmed empirically: `P[good] = 1` at `d = 1` for every N tested.
* **`sopFresh_decidable` (:145) — CLEAN.** `Classical.dec`, `noncomputable instance`. Head is
  specific to `sopFresh`, so no instance diamond. `Finset.filter` under a classical instance is
  still the extensionally correct finset (`Finset.filter_congr_decidable`), and card is
  instance-independent, so this cannot change any statement's meaning.

### 2.3 The balance identity

* **`card_avail_fresh_answer` (:156) — CLEAN. This is the load-bearing node and I checked it
  hardest.**
  Statement (elaborated): `U.card = V.card → ∀ c, {uv ∈ availPairs U V | uv.1 + uv.2 = c ∧
  sopFresh U V uv.1 uv.2}.card = Fintype.card G − 2 * U.card`.
  - The bijection is `u ↦ (u, c − u)` from `freshKeep U V c`. **Onto**: given
    `uv` available with `uv.1 + uv.2 = c` and `sopFresh`, `sopFresh` unfolds to
    `uv.1 ∈ freshKeep U V (uv.1+uv.2) = freshKeep U V c`, and `(uv.1, c − uv.1) = uv` by
    `add_sub_cancel_left`. **Into**: `u ∈ freshKeep U V c ⊆ freshFiber U V c` gives `u ∉ U`
    and `c − u ∉ V`, i.e. availability, and `u + (c−u) = c` re-establishes `sopFresh`.
    **Injective** on the first coordinate. All three legs are in the proof and correct.
  - Independence of `c` is real: `card_freshKeep` gives the same size for every `c`, and
    the choice made by `canonSubset` per `c` is independent — which is fine, because the
    images `{(u, c−u)}` over distinct `c` are disjoint.
  - Exhaustively verified for every `U, V` with `|U| = |V|` and every `c` in `Z/3, Z/4,
    (Z/2)², Z/5` and `k ≤ 3` in `Z/6`, under three selection rules.
* **`card_avail_fresh` (:190) — CLEAN.** `N * (N − 2|U|)`. Fibre-wise over `uv.1 + uv.2`
  with `t = univ`; the `Finset.filter_filter` + `and_comm` re-ordering is correct.
  Sanity: `(N−k)² − N(N−2k) = k²` = `Σ_y r(y) = |U||V|` — exactly the "discarded excess"
  the module docstring claims. Verified numerically. ✔

### 2.4 The monitored condition

* **`sopTightBad` (:218) — CLEAN.** `∃ pre x, pre ++ [x] <+: l ∧ x ∉ pre ∧ ¬sopFresh
  (image p.1 pre.toFinset) (image p.2 pre.toFinset) (p.1 x) (p.2 x)`.
  `pre ++ [x] <+: l` pins `pre` to be *exactly* the elements of `l` before that occurrence, so
  `x ∉ pre` is precisely "first occurrence". Uses `pre.toFinset`, so repeats inside `pre` do
  not inflate `U` — checked against interleaved-repeat lists like `[0,1,0,1]`, `[2,2,3,3,1,0]`
  in the brute force. Depends only on `(p, l)`: a legitimate *seeded* condition.
* **`sopTightBad_decidable` (:222) — CLEAN.** As `sopFresh_decidable`.
* **`sopTightBad_monotone` (:226) — CLEAN.** `l₁ <+: l₂ → bad l₁ → bad l₂` by
  `IsPrefix.trans`. Exactly the direction the game framework needs (an MBO can only go up).
* **`sopTightBad_concat` (:234) — CLEAN, and really is an iff.**
  Forward uses `List.prefix_concat_iff : l₁ <+: l₂ ++ [a] ↔ l₁ = l₂ ++ [a] ∨ l₁ <+: l₂`
  (statement verified against Mathlib) plus `List.append_inj'` to split `pre = l, y = x`;
  in that branch `hy : y ∉ pre` becomes exactly the `x ∉ l` of the RHS. Backward uses
  monotonicity and `List.prefix_rfl`. "A repeat cannot fire it" is genuinely captured — the
  `x ∉ l` conjunct is in the RHS, and it is what both inductions use in the repeat branch.
* **`sopTightBad_congr` (:251) — CLEAN.** Hypotheses are agreement on `l.toFinset` for
  *both* components, and both `Finset.image_congr` rewrites are present (lines 260–263) plus
  the two point rewrites `← h₁ x hxl`, `← h₂ x hxl`. `pre ⊆ l` and `x ∈ l` are derived from
  `hp.subset`, so the hypotheses cover everything the conclusion mentions. Stated one-way;
  both call sites supply `.symm` correctly (I checked the direction at both `hP` arguments).

### 2.5 The count and the two inductions

* **`goodCount` (:275) — CLEAN.** `(N−d)!² · ∏_{k<d}(N − 2k)`. Docstring matches.
* **`goodCount_step` (:279) — CLEAN, no off-by-one.** With `N − d = j+1` and
  `N − (d+1) = j`: LHS `= (j+1)²·j!²·P·(N−2d)`, RHS `= (N−2d)·((j+1)·j!)²·P`. Equal. The
  `N − 2d` factor is the *same* truncated `ℕ` expression on both sides, so truncation cannot
  create a false identity. `hd : d < Fintype.card G` is needed (for `∃ j, N − d = j + 1`) and
  is satisfiable. Verified numerically against `goodCount` for N = 4,5,6, all d.
* **`card_goodAgree` (:291) — CLEAN.** No hypothesis on `a` and none needed: the count is
  `goodCount G l.toFinset.card` for **every** `a : G → G`, which I verified by *full*
  enumeration of `a` (not sampling) for N = 3, 4 and both groups of order 4.
  Proof audit:
  - `hlt : l.toFinset.card < Fintype.card G` is **derived** (`Finset.ssubset_univ_iff` from
    `hxQ : x ∉ l.toFinset`), not assumed. `hpos` follows by `omega`. ✔
  - `hP` (restriction-invariance) is discharged via `sopTightBad_congr` with the right
    direction, and via `sopFunction` unfolding for the agreement conjunct.
  - `hm` instantiates `card_avail_fresh_answer` at `U = l.toFinset.image p.1`,
    `V = l.toFinset.image p.2`, `c = a x`, and reduces `2 * (image p.1 l.toFinset).card` to
    `2 * l.toFinset.card` by `card_image_of_injective` — so `m` really is the *same*
    constant for all `p`, which is what `card_fresh_pair_refine` demands and what the
    balanced set exists to provide.
  - `hfilter` is an honest iff; the backward direction's `by_contra hnf; exact hb (Or.inr ⟨hx, hnf⟩)`
    uses `hx : x ∉ l` from the `by_cases` branch, so it is only applied where valid.
  - the `(N−d)²` cancellation via `Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hpos)` is
    correct and its positivity side condition is discharged, not assumed.
* **`card_good` (:391) — CLEAN.** `N^d · goodCount d`, same shape, same audit; the extra
  `hexp`/`hkey` `pow_succ` bookkeeping is routine `ring`. Two independent internal
  cross-checks pass: (i) `card_good = N^d · card_goodAgree` is exactly the statement that
  the `N^d` transcripts partition the good world, which is what `mass_agree_and_good`
  consumes; (ii) `card_good / (N!)² = ∏(1−k²/(N−k)²)` numerically.
  Note it holds with no `Nonempty G`, and is correct even for `G` empty (`1 = 0^0 · 0!² · 1`).

### 2.6 Elaborator-generated nodes (12)

I read the elaborated type of every one; none carries independent content, and each is a
true `ℕ`/`simp` fact:

| node | type | verdict |
|---|---|---|
| `goodCount.eq_1` | definitional unfolding | CLEAN |
| `sopFresh.eq_1` | `sopFresh U V u v = (u ∈ freshKeep U V (u+v))` | CLEAN |
| `sopFunction.eq_1` | `sopFunction p x = p.1 x + p.2 x` | CLEAN |
| `card_avail_fresh_answer._simp_1_1` | `Finset.mem_filter` as `=` of Props | CLEAN |
| `._simp_1_2` | `Finset.mem_image` | CLEAN |
| `._simp_1_3` | `Counting.mem_availPairs` | CLEAN |
| `card_freshFiber_ge._proof_1_1` | the `omega`: `A+B = N−\|U\|`, `B ≤ \|V\|`, `ff = A` ⟹ `N−(\|U\|+\|V\|) ≤ ff` | CLEAN, true in `ℕ` |
| `card_freshKeep._proof_1_1` | `\|U\|=\|V\| → N−2\|U\| = N−(\|U\|+\|V\|)` | CLEAN |
| `card_good._proof_1_3`, `card_goodAgree._proof_1_4` | `d < N → 0 < N − d` | CLEAN |
| `goodCount_step._proof_1_1` | `d < N → N−d = (N−d−1)+1` | CLEAN |
| `goodCount_step._proof_1_2` | `d < N → N−d = j+1 → N−(d+1) = j` | CLEAN |

---

## 3. MINOR notes (no node fails on these)

**MINOR-1 — `freshKeep`'s docstring states an unconditional property that is false without
`U.card = V.card`.** `SumOfPermutationsTight.lean:127`: *"The **balanced** fresh set: exactly
`N − 2|U|` available values, whatever `y` is."* The theorem that establishes this
(`card_freshKeep`, :136) requires `hUV : U.card = V.card`, and without it the claim is simply
false — `G = Z/5`, `U = ∅`, `V = {0}`, `y = 0` gives `|freshKeep| = 4`, not `5`. Not a proof
defect (both call sites discharge `hUV`); it is a docstring that would mislead a reuser.
Same remark, milder, for `card_avail_fresh_answer`'s *"exactly `N − 2k`"*, which is
`ℕ`-truncated and therefore reads "exactly 0" once `2k ≥ N` (the module docstring does call
this out explicitly at lines 57–60, so it is disclosed).

**MINOR-2 — `freshKeep` sizes by `U.card` alone, and the `canonSubset` `else` branch fails
open.** `freshKeep U V y = canonSubset (freshFiber U V y) (N − 2 * U.card)` never mentions
`V.card`. Off the `|U| = |V|` diagonal the requested size can exceed `|freshFiber|`, at which
point `canonSubset` silently returns *all* of `freshFiber` — i.e. `sopFresh` becomes **weaker**
(more pairs pass the monitor) rather than erroring or being empty. In this development that
branch is unreachable (`U`, `V` are images of one finset under two injections, so
`|U| = |V|` always, and `card_freshFiber_ge` then guarantees `m ≤ |freshFiber|`), so it is not
a defect here — but `sopFresh` is a public definition and a fail-open degenerate branch in a
*monitored condition* is the kind of thing that becomes a real bug on reuse. Worth a comment
or a `|U| = |V|` bundling.

**MINOR-3 — the "eq. (4.38)" citation is loose (stronger, not weaker).** I checked CR18
visually: `papers/CR18_LN.pdf`, PDF page 60 = printed page 108, §4.11.1, Definition 4.19,
equation **(4.38)** reads
`p^S_{Y_i, A_i=0 | X^i} = p^S_{A_i=0 | X^i} · p^T_{Y_i | X^i}` — a *per-step* factorisation.
`card_goodAgree` + `card_good` deliver the *cumulative* (whole-prefix) version: the joint
mass of "transcript `= a` on `l` and no-bad" is `goodCount d` for every `a`, and the no-bad
mass is `N^d · goodCount d`. That is strictly stronger than (4.38) (it also shows
`p^S_{A_i=0|X^i}` does not depend on `y^{i−1}` — I checked the telescoping:
`goodCount(d+1)/goodCount(d) · N = 1 − d²/(N−d)²`, independent of the answers). So the
docstring under-describes rather than over-describes what is proved. Recording it because a
reader chasing the citation will not find this exact statement at (4.38).

---

## 4. Explicitly NOT checked (out of slice, or trusted)

I did **not** audit the proofs of, and make no claim about:

* `RandomSystems.CR18.Counting.card_fresh_pair_refine`, `card_fresh_pair_fiber`,
  `card_permPair_restrict`, `restrict_perm_injective`, `availPairs`, `mem_availPairs`
  (slice `perm-fresh-refinement`). I checked only that `card_fresh_pair_refine`'s **statement**
  is instantiated correctly at both call sites (`P`, `hP`, `R`, `m`, `hm` all line up, and `m`
  is genuinely `p`-independent), and my exhaustive enumeration independently confirms the
  *conclusions* of `card_good`/`card_goodAgree`, which is the only way this lemma is used here.
* `mass_agree_and_good`, `mass_good_eq_prod`, `mass_sopTightBad_le`, `sopEps`,
  `sopEps_nonneg`, `sopEps_ge_one_of_large` (slice `mass-layer-and-epsilon`). I did record
  one datum for that slice: `card_good/(N!)² = ∏(1−k²/(N−k)²)` holds *exactly*, so
  `mass_good_eq_prod` should be an equality with no slack.
* `sopReal`, `sopIdeal`, `sopFunction` (the def itself), `sopTightGame`,
  `sopTightGame_ignoreMBO`, `sopTight_condEquiv`, `maxAdvantage`, `filterQueries`,
  `seededConditionCGame`, `Dist`, `Dist.mass`, `Dist.uniform`, and the whole blind-game
  endpoint. Whether the counting in this slice is *plugged into* a correct notion of
  distinguishing advantage is not something this slice can settle.
* Mathlib/core lemmas, treated as trusted. I did print and read the statements of the
  load-bearing ones: `List.prefix_concat_iff`, `List.append_inj'`,
  `Finset.exists_subset_card_eq`, `Finset.card_filter_add_card_filter_not`,
  `Finset.card_univ_diff`, `Nat.eq_of_mul_eq_mul_left`.
* I did not attempt Lean-level mutation testing (deleting `hUV` and re-running the proof)
  because the rules forbid modifying the proof files; hypothesis load-bearingness was
  established semantically instead (575 explicit counterexamples for `hUV`).

## 5. Coverage

**34 of 34 slice nodes checked** — 22 named declarations (both (a) and (b) passes) and all 12
elaborator-generated nodes (type read, truth confirmed). None skipped.
