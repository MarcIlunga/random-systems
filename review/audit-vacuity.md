# Audit — slice `vacuity`

Target: `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight`
(`RandomSystems/SumOfPermutationsTight.lean:769`).

Mandate: assume the proof was written to pass a checker, not to be true. Try to break it.

**Bottom line.** I could not break it. The theorem is true, is about the objects its names
claim, and its `ε` is not below the exact truth on any of the 55 concrete `(N, q)` instances I
computed independently. Every one of the six named suspicions is settled below; two of them
(1 and 2) are *real* — the conditional equivalence really is vacuous past `N/2` distinct
queries, and the `min 1` cap really does make the first conjunct content-free past
`≈1.442·N^{2/3}` — but both are compensated exactly, and nothing false is derived. The one
thing I would push back on is the **statement's certificate strength**: the floor conjunct,
the only clause that is supposed to guarantee the bound is worth anything, is discharged by
`ε ≤ 1` alone throughout the entire beyond-birthday regime the file is about (94% of the
`1 < q < N` domain), and would be *false* without the cap on 34% of it.

Read-only. No proof file was touched. Lean probes and Python scripts were written to `/tmp`
and are reproduced inline below.

---

## 0. What was checked, and what was not

| | |
|---|---|
| repo nodes in the DAG (`review/sop-dag.md` §1) | 500 |
| nodes I inspected (statement read, or proof read, or exercised) | 88 |
| — all hand-written decls of `SumOfPermutationsTight.lean` (840 lines, read in full) | 34 |
| — all hand-written decls of `PermFreshCounting.lean` (385 lines, read in full) | 9 |
| — LIB nodes read (definitions + statements; proofs where load-bearing) | 45 |
| Mathlib frontier | not walked (trusted) |

Not checked, and I make no claim about them:

* the interior of `blind-game-endpoint` (308 nodes). I read the **CE consumption path only**:
  `maxAdvantage_filterQueries_seededConditionCGame_le` →
  `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` →
  `advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo` →
  `advantage_le_absorbedWinnerProb_of_condEquiv_of_totalUpTo` →
  `Theorem417.massYAfalse_gameEnhance_eq_of_totalUpTo` (proof read in full — it is where the
  vacuous CE instances land). The winner-absorption half (`winProb_absorption_of_totalUpTo`,
  `absorbedWinnerDist`, `blindMaxWinProb_filterQueries_monitored_le`) I did **not** verify.
* `Lemma415`, `RelateGameDistinguishing`, `GameOf`, `WinProb`/`MaxWinProb` interiors.
* the arithmetic proofs inside `mass_sopTightBad_le` / the floor branch beyond re-deriving
  their claims numerically (they are `nlinarith`/`linarith` chains that the kernel checked).

Axioms re-confirmed: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no
`Lean.ofReduceBool`. This proves nothing about meaning and is not offered as evidence.

---

## 1. Independent falsification: exact truth vs the claimed bound

The strongest attack available is not to read the proof but to compute the thing it bounds.

`Δ(⌈q⌉ S, ⌈q⌉ T)` is *not* a degenerate sup: `RandomSystems/RandomSystem.lean:1271`
proves `adv_eq_maxAdvantage_swap : Adv S T = Δ(T, S)`, where `Adv` (thesis Def 2.26,
`RandomSystem.lean:704`) is `sup` over **deterministic environments and prefix lengths** of the
one-sided transcript excess `δ`. The accept-set distinguisher is *constructed* there
(`PFunDDS.DDD.ofDDE e n A`), so the distinguisher class is rich enough to attain the transcript
distance. Hence for probability systems

> `Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal)` = the total-variation distance between the law of
> `(f(x₁),…,f(x_q))` under XoP and the uniform law on `G^q`, over the best adaptive schedule.

For `G = ℤ/N` that TV is exactly computable: the answer-vector law is the self-convolution of
the indicator of injective `q`-tuples, so an `FFT` over `(ℤ/N)^q` gives it in closed form.
Adaptivity buys nothing (the law depends only on the queries being distinct), so this *is* the
quantity the first conjunct bounds.

```python
A = indicator of injective q-tuples over (Z_N)^q         # numpy
C = ifftn(fftn(A)**2).real                               # C[y] = #{u inj : y-u inj}
TV = 0.5 * abs(C/C.sum()... - 1/N**q).sum()
```

Result — all `2 ≤ N ≤ 15`, `1 ≤ q ≤ min(N,5)`, 55 instances, **zero violations**:

| N | q | exact TV | `sopEps N q` | ε/TV |
|---|---|---|---|---|
| 4 | 2 | 0.0833333 | 0.1111111 | 1.333 |
| 5 | 2 | 0.0500000 | 0.0625000 | 1.250 |
| 8 | 2 | 0.0178571 | 0.0204082 | 1.143 |
| 15 | 2 | 0.0047619 | 0.0051020 | 1.071 |
| 8 | 3 | 0.0372024 | 0.1315193 | 3.54 |
| 12 | 3 | 0.0184343 | 0.0482645 | 2.62 |
| 15 | 4 | 0.0191525 | 0.0912707 | 4.77 |
| 15 | 5 | 0.0229517 | 0.2235021 | 9.74 |

At `q = 2` the exact TV is `1/(N(N−1))` and the bound is `1/(N−1)²` — ratio exactly `N/(N−1)`,
i.e. the docstring's tightness claim is correct and the bound is **within 7% of exact at
N = 15**. That is decisive against "the bound is vacuously large" and against "the bound is
secretly below the truth".

Sanity in the other direction: the sibling `sop_randomness_expander_optimal`
(`SumOfPermutationsOptimal.lean:149`, a different route via `SoP/` coupling) exhibits
`q(q−1)(2q−1)/(3N²) ≈ 2q³/3N²`, i.e. exactly **twice** this file's `Σ_{k<q} k²/N² = q³/3N²`
leading term. Two independent routes landing on the same order, a factor 2 apart, with the
tighter one still above the exact TV, is a consistent picture.

---

## 2. Suspicion 1 — is the conditional equivalence vacuous, and does anything false follow?

**The vacuity is real, and I have a kernel receipt for it.**
`freshKeep U V y = canonSubset (freshFiber U V y) (N − 2|U|)`; `ℕ`-truncated subtraction makes
the target cardinality `0` once `2|U| ≥ N`, so `freshKeep = ∅`, `sopFresh` is unsatisfiable,
and the monitor fires with certainty at the `(⌈N/2⌉+1)`-th **distinct** query. Verified in
Lean at `G = ZMod 4`, history `[0,1,2]` (checked by `lake env lean`, file below):

```lean
theorem goodCount_zmod4_three : goodCount (ZMod 4) 3 = 0 := by
  simp [goodCount, Finset.prod_range_succ]

theorem good_world_empty :
    (Finset.univ.filter (fun p : Equiv.Perm (ZMod 4) × Equiv.Perm (ZMod 4) =>
      ¬ sopTightBad p [0,1,2])).card = 0 := by
  rw [card_good]; rw [show ([0,1,2] : List (ZMod 4)).toFinset.card = 3 from by decide,
    goodCount_zmod4_three, Nat.mul_zero]

theorem massAfalse_zero :                       -- the CE normalizer is 0 at that history
    CondEquiv.massAfalse (sopTightGame (G := ZMod 4)) [0,1,2] = 0 := …
```

`CondEquiv.CondEquiv` (`CondEquiv.lean:118`) is guarded:

```
∀ i xs ys, massAfalse Ŝ xs ≠ 0 → massDom T xs ≠ 0 → massYAfalse Ŝ i ys xs * massDom T xs = …
```

so at `[0,1,2]` over `ZMod 4` the obligation is discharged **by the guard**, not by the
balanced-fiber argument. (Even unguarded it would be `0 = massY · 0`.) `sopTight_condEquiv` is
a `∀`-statement over all histories that carries content only on histories with at most `N/2`
distinct queries. Its docstring says so; the name does not.

**Nothing false follows.** The exact path, traced:

1. The CE is consumed once, at `Theorem417.massYAfalse_gameEnhance_eq_of_totalUpTo:219`, which
   *case-splits on exactly this*: `by_cases hA : massAfalse Shat xs.toList = 0`. In the `0`
   branch it proves the needed equality without `hCE` at all
   (`massYAfalse ≤ massAllFalse = massAfalse = 0`). So the vacuous instances are never *used*;
   the framework already knew it would not get anything there.
2. In that regime the leaf obligation is forced to be `≥ 1`: `mass(bad) = 1`. The proof pays
   it — `mass_sopTightBad_le` branches on
   `hbig : ∃ k < l.toFinset.card, Fintype.card G ≤ 2*k` and uses `sopEps_ge_one_of_large` to
   show the RHS sum is `≥ 1`, i.e. **`sopEps N q = 1` whenever a vacuous history is reachable
   within `q` queries**. (Vacuity needs `d ≥ ⌈N/2⌉+1` and `d ≤ q`, so `k = ⌈N/2⌉ < q` is in the
   sum, with term `k²/(N−k)² ≥ 1`.)
3. So the conclusion drawn in the vacuous regime is `Δ ≤ 1`, which is free (§3).

**Verdict: sound.** The vacuity region is strictly contained in the already-trivial region.
The `min 1` in `sopEps` and the `hbig` branch in `mass_sopTightBad_le` exist precisely to pay
for it, and they are not decoration — remove either and the file does not compile.

---

## 3. Suspicion 2 — does `min 1` make the bound trivially true where it should speak?

`Δ ≤ 1` is free for any pair of probability systems. Six-line proof, checked:

```lean
theorem maxAdvantage_le_one (S T : PFunPDS X Y) (hT : T.isProbDist) : Δ(S, T) ≤ 1 := by
  refine maxAdvantage_le_of_forall_advantage_le (fun D hD => ?_)
  have h1 : verdictProb D T ≤ T.weight := GamePerf.winProb_le_weight PFunDDS.verdict D T hD
  …
```

(the tree already has this — `SumOfPermutationsOptimal.lean:177` uses it by that name.)

So the first conjunct says **nothing at all** wherever `sopEps N q = 1`. That is
`Σ_{k<q} k²/(N−k)² ≥ 1`, i.e. `q ≳ 3^{1/3} N^{2/3} ≈ 1.442 N^{2/3}`:

| N | last `q` with `ε < 1` | `√N` | `q_max / N^{2/3}` |
|---|---|---|---|
| 256 | 52 | 16 | 1.290 |
| 4096 | 353 | 64 | 1.379 |
| 2⁶⁴ | 3.81e6·… | 2³² | 1.4422 |

**The claim survives**: `1.442 N^{2/3} > √N` for every `N ≥ 2`, so there is a genuine
beyond-birthday band `√N < q < 1.442 N^{2/3}` in which the first conjunct is a real, non-free
statement — and, per §1, a nearly tight one at the bottom of that band. But the theorem's
substance is confined to that band; for `q` past `1.44 N^{2/3}` (and in particular anywhere
near the `q ≈ N` regime where XoP is actually believed secure) the headline is `Δ ≤ 1`.

---

## 4. Suspicion 3 — the floor clause, boundaries included

`∀ N q, 1 < q → q < N → sopEps N q < q²/N`. Exhaustive check for all `2 ≤ q < N ≤ 400`
(19 701 pairs): **no violation**, including the named boundaries `q = 2`, `q = N−1`, tiny `N`.
`q = N` is excluded by hypothesis; the `q = N` term would be junk (see §7).

Three things the clause does *not* do, which the phrase "strictly better than birthday"
invites a reader to assume:

1. **It is discharged by `ε ≤ 1` alone on 94% of its domain** (74 651 / 79 401 pairs with
   `2 ≤ q < N ≤ 400`): whenever `q² > N`, i.e. **for every `q` past the birthday barrier**,
   `min 1 (…) ≤ 1 < q²/N` holds for *any* candidate `ε ≤ 1`. The entire beyond-birthday
   regime — the point of the file — is exactly where the floor certifies nothing.
   In the Lean proof this is the branch `by_cases hcase : N < q ^ 2 · refine lt_of_le_of_lt
   (min_le_left _ _) …` (line 795–799): the `min` is the whole argument there.
2. **The cap is load-bearing for the clause's truth.** Without `min 1` the raw sum *exceeds*
   `q²/N` on 34% of the same domain — first counterexample `N = 6, q = 5`: raw sum `5.29` vs
   `q²/N = 4.17`. The raw estimate stops beating birthday at `q ≈ 0.66 N`.
3. **It is satisfiable by a constant-factor improvement of the birthday bound.**
   `ε' N q := min 1 (q²/(2N))` satisfies both `ε' < q²/N` on `1 < q < N` and (presumably)
   provability. So the conjunct excludes *restating* `q²/N` — it does not certify anything
   beyond birthday. The docstring is honest about this ("a floor that merely excludes
   restating the birthday bound"); the theorem name (`…_tight`) and the abstract are less so.

Because `ε` is `∃`-bound, a consumer of the public statement gets **only** these two facts:
"some bound exists, and it is everywhere strictly under `q²/N`". The actual achievement —
`min 1 Σ k²/(N−k)²`, tight to `N/(N−1)` at `q = 2` — lives in `sopEps` + `mass_sopTightBad_le`
+ the `calc` chain, not in the headline. That is a property of the statement shape (shared with
`sop_randomness_expander_optimal`), not a defect of this proof.

---

## 5. Suspicion 4 — does anything depend on *which* subset `canonSubset` picks?

**No.** Three independent arguments:

* **Syntactic.** `freshKeep` is used through exactly two facts, `freshKeep_subset`
  (`canonSubset_subset`) and `card_freshKeep` (`canonSubset_card`), plus abstract membership
  in the `hset` step of `card_avail_fresh_answer`. `grep` confirms `canonSubset` occurs
  nowhere else in the repository outside `PermFreshCounting.lean` and these sites.
* **Proof-irrelevance.** `canonSubset s m = if h : m ≤ s.card then (Finset.exists_subset_card_eq h).choose else s`.
  `Exists.choose` is a function of the proposition, and `Prop` proof irrelevance makes the
  bound `h` immaterial, so the `dite` cannot leak the proof term.
* **Empirical.** I re-implemented the whole monitored count over `ℤ/4` and `ℤ/5` with **three
  different selection rules** (`first-m`, `last-m`, seeded-shuffle) and brute-forced all
  `(24²=576)` resp. `(120²=14400)` permutation pairs. `#{p : ¬bad p l}` and
  `#{p : ¬bad ∧ agree with a}` are **identical across all three rules** and match
  `N^d·goodCount d` resp. `goodCount d` for every list tried, including lists with repeats
  (`[0,1,0,2]`) and every one of the `N^d` assignments `a`.

That last run doubles as an independent check of `card_good` and `card_goodAgree` themselves
(the uniformity of the count over `a` is the entire content of the conditional equivalence):

```
N=5 l=(0,1,2)   #good=7500 = 5³·60 ✓   #good&agree ∈ {60} for all 125 assignments ✓
                mass_good = 0.520833 = ∏_{k<3}(1−k²/(5−k)²) ✓
N=5 l=(0,1,2,3) #good=0 ✓ (vacuity)     ∏(1−k²/(5−k)²) = −0.651 ✗  → the `hsmall`
                hypothesis of `mass_good_eq_prod` is genuinely load-bearing, and present.
```

---

## 6. Suspicion 5 — instance diamonds

No diamond found; I could not construct one.

* Every declaration in the two NEW files takes `[Fintype G] [DecidableEq G] [AddCommGroup G]`
  (and sometimes `[Nonempty G]`) as **section variables**, so a single instance term flows
  through each statement. Elaborated signatures printed and inspected (all 34 decls) — no
  stray `Classical.decEq`, no duplicated instance argument.
* `canonSubset` needs no `DecidableEq` at all (`{α : Type*}`), so the one choice-based object
  in the development is instance-free.
* The two `Classical.dec` instances (`sopFresh_decidable`, `sopTightBad_decidable`) are the
  *unique* instances for their predicates; nothing else in the tree can supply a competitor.
* `Dist.uniform` is already known to be `Fintype`-instance-independent
  (`Dist.uniform_eq_of_fintype_instances`, `Dist.lean:443`; and
  `fTransform_uniform_fintypeIrrel`, `SumOfPermutationsOptimal.lean:92`), so the `Perm G × Perm G`
  and `G → G` uniforms in the statement do not depend on which `DecidableEq H` a consumer
  supplies.
* A mismatched `Finset.filter` decidability instance between a lemma's statement and its use
  makes the corresponding `rw` fail; the file compiles, and every `rw [card_good …]` /
  `rw [card_goodAgree …]` site succeeds, so the instances did unify. I did **not** re-elaborate
  the file against an adversarial second `Fintype`/`DecidableEq` instance — that is the one
  experiment I did not run.

---

## 7. Suspicion 6 — universe and quantifier scope

`#print` output, verbatim:

```
theorem …sop_randomness_expander_tight.{u} : ∃ ε,
  (∀ (H : Type u) [inst : Fintype H] [inst_1 : DecidableEq H] [inst_2 : Nonempty H]
      [inst_3 : AddCommGroup H] (q : ℕ),
      maxAdvantage (filterQueries q sopReal) (filterQueries q sopIdeal) ≤ ε (Fintype.card H) q)
  ∧ ∀ (N q : ℕ), 1 < q → q < N → ε N q < ↑q ^ 2 / ↑N
```

`ε : ℕ → ℕ → ℝ` is bound outside the `∀ H`, the theorem is universe-polymorphic in `u`, and
`Fintype.card H` is the only channel from the group to `ε`. The degenerate instantiation the
docstring worries about ("ε := the advantage itself") is not even expressible. `ε :≡ 1` is
excluded by the floor at `q² ≤ N`. Nothing hides in the instance binders: `Fintype H` forces
`Fintype.card H` to be the true cardinality, and `[Nonempty H]` is redundant (implied by
`AddCommGroup H`) but harmless.

**`omit` audit.** Every `omit` in the file (`omit [Nonempty G]`, `omit [AddCommGroup G]`) only
*removes* an instance from a statement, which strictly strengthens it; none can hide a needed
hypothesis (the proof would not close). Printed signatures confirm: `mass_sopTightBad_le`,
`card_good`, `card_goodAgree` carry **no** side conditions at all, and `card_freshKeep`,
`card_avail_fresh_answer`, `mass_good_eq_prod`, `goodCount_step`, `sopEps_ge_one_of_large`
carry exactly the ones §5 shows to be load-bearing.

---

## 8. Junk arithmetic in `sopEps` (minor, not exploitable as used)

`sopEps N q = min 1 (Σ_{k<q} k²/((N:ℝ)−k)²)` divides by zero at `k = N`, and Lean's `x/0 = 0`
silently **drops that term**. Exhaustive search over `N ≤ 60`, `q ≤ N+5`: the only `(N,q)` where
a sub-`1` value depends on the convention is `(N,q) = (1,2)`, giving `sopEps 1 2 = 0` and hence
the claim `Δ(⌈2⌉ sopReal, ⌈2⌉ sopIdeal) ≤ 0` for the one-element group. That claim is **true**
(over a one-element group `sopReal` and `sopIdeal` are literally the same `Dist`), and the
proof establishes it honestly rather than through the junk: at `N = 1` there is only one
possible query, so `d ≤ 1`, the `hsmall` branch applies, and `mass(bad) = 0` is derived from
`mass_good_eq_prod`. For every `N ≥ 2` the sum already exceeds `1` long before `k` reaches `N`.

Flagged only because the formula is not robust to reuse: any future statement quantifying `q`
past `N` inherits a silently-dropped term.

---

## 9. Things I tried that did not break it

* Instantiate at the trivial group (`N = 1`) — bound `0`, systems identical, no contradiction.
* Instantiate at `ℤ/2, q = 2`, where XoP is maximally broken (`f(0) = f(1)` always, advantage
  `1/2`) — bound is `1`. No contradiction.
* Push the exact-TV computation to every `(N,q)` reachable by FFT — no violation (§1).
* Look for a lemma that is false without its hypothesis and applied without it —
  `card_freshKeep` (false for `|U| ≠ |V|`: take `U = ∅, V = univ`), `mass_good_eq_prod` (false
  without `hsmall`: the product goes negative at `N=5, d=4`), `sopEps_ge_one_of_large`
  (false without `k < N`). All three carry their hypothesis and all three discharge sites
  supply it correctly.
* Check the hinge `ignoreMBO sopTightGame = sopReal` — `ignoreMBO` is the `Prod.fst`
  pushforward (`SystemMBO.lean:29,45`), so the bound really is about the monitor-free system.
  Its proof routes through `seededConditionCGame_ignoreMBO`, an **uncommitted, never-reviewed**
  addition to `SwitchingLemma.lean:1864` (flagged in `sop-dag.md` §2); I read it, it is a
  `funext`/`rfl` strip identity, and it is correct.
* Check whether `Δ` could be a degenerate sup over an impoverished distinguisher class —
  no (`adv_eq_maxAdvantage_swap`, §1).

## 10. Reproduction

```
lake -KverificationBuildDir=.lake/verify-rs-prover-d0 env lean /tmp/vac_probe3.lean   # §2,§3 receipts
uv run --with numpy python3 /tmp/vac/tv.py       # §1 exact TV vs bound
uv run python3 /tmp/vac/count.py                 # §5 brute-force counting, 3 selection rules
uv run python3 /tmp/vac/eps.py /tmp/vac/floor.py # §3,§4,§8 saturation / floor / junk analysis
```
