# Slice review — `sop-statement-and-semantics` (81 nodes: 16 NEW / 65 LIB)

Reviewer: adversarial pass, read-only. No proof or framework file was modified. All three
reproducible probes live next to this report under `review/`:

| probe | reproduce with |
|---|---|
| `slice-sop-statement-and-semantics.probe-vacuity.lean` | `lake env lean review/slice-sop-statement-and-semantics.probe-vacuity.lean` |
| `slice-sop-statement-and-semantics.probe-semantics.lean` | `lake env lean review/slice-sop-statement-and-semantics.probe-semantics.lean` |
| `slice-sop-statement-and-semantics.exact-advantage.py` | `uv run python3 review/slice-sop-statement-and-semantics.exact-advantage.py` |

All three were re-run from those paths and pass.

**Headline.** The theorem is true, sorry-free and axiom-clean, and every object in it means what
its name says — `sopReal` really is `x ↦ π₁x + π₂x` under two independent uniform permutations,
`sopIdeal` is *definitionally* the library's `PFunPDS.URF`, `⌈q⌉` caps the interaction at exactly
`q` answered queries, and `Δ` is a supremum over a demonstrably inhabited class containing every
deterministic adaptive distinguisher. **One MAJOR defect**: the *statement* does not certify what
its docstring says it certifies. I proved the verbatim statement of
`sop_randomness_expander_tight`, axiom-clean, from the **already-committed birthday theorem**
`RandomSystems.SumOfPermutations` alone. The "strictly better than birthday" conjunct does not
exclude restating the birthday bound.

---

## Coverage

All 81 nodes were examined. Breakdown:

* **16 NEW** — all read in source; the 7 elaborator-generated ones (`_proof_*`, `.eq_1`,
  `._simp_*`) were `#print`ed and inspected.
* **65 LIB** — the 54 substantive ones had their *source statement* read (not just the type);
  the 11 elaborator-generated ones (`.match_1`, `.match_3`, `._proof_1/2`, `.eq_1`) carry no
  independent claim and were accepted as Lean-generated equation/validity artifacts.

Nothing in the slice was skipped. What I did **not** do is verify the *proofs* of the LIB nodes
(they are library-level and exercised by other published bounds); I verified their **statements**
and, where a statement encodes semantics I depend on (`filterQueries`, `maxAdvantage`,
`functionEvaluator`, `fullyDefined`/`keptPrefix`, `stripMBO`), I re-derived the semantics
independently in Lean.

---

## FINDING 1 — MAJOR — `sop_randomness_expander_tight`: the statement certifies nothing beyond birthday

### The claim under review

Docstring (lines 755–768):

> Exhibit a bound `ε N q` … **together with a proof that it strictly improves on the birthday
> bound `q²/N` in the range where `q²/N` says anything.**
> … The improvement clause is a floor that **merely excludes restating the birthday bound**.

### The defect

The second conjunct is
```
∀ N q : ℕ, 1 < q → q < N → ε N q < (q:ℝ)^2 / (N:ℝ)
```
It excludes `ε = q²/N` **uncapped and with exactly that constant**. It does *not* exclude the
birthday bound: `Δ ≤ 1` is free for probability systems (`maxAdvantage_le_one`), so

```
ε N q := min 1 ((1/2) * q² / N)
```

satisfies **both** conjuncts, using only the already-committed
`RandomSystems.CR18.SoP` birthday argument. Conjunct 2 because `min 1 x ≤ x < 2x = q²/N`
for `x = q²/2N > 0`; conjunct 1 because `Δ ≤ 1` and `Δ ≤ pairCollisionUnionBound ≤ q²/2N`.

### Machine-checked evidence

`slice-sop-statement-and-semantics.probe-vacuity.lean` proves the **verbatim** statement (same `∃ ε`, same `∀ H` block,
same `SoPTight.sopReal` / `SoPTight.sopIdeal`) from `SumOfPermutations` alone:

```
'ReviewProbe.sop_randomness_expander_tight_FROM_BIRTHDAY' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The probe also contains, as `rfl`, the two identifications that make it a fair comparison:

```lean
theorem tight_real_eq  : SoPTight.sopReal  (G := G) = SoP.sopReal  (G := G) := rfl
theorem tight_ideal_eq : SoPTight.sopIdeal (G := G) = SoP.sopIdeal (G := G) := rfl
```

### How weak is the statement, exactly?

Because `Δ ≤ 1` always and `ε` is bounded, one may take `ε N q := sSup {r | ∃ H : Type u, …,
Fintype.card H = N ∧ r = Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal)}` — a legitimate closed `ℕ → ℕ → ℝ`.
Conjunct 1 then closes by `le_csSup`. So the whole theorem is **logically equivalent** to

> for all `1 < q < N`, the maximal `q`-query advantage of XoP over *every* abelian group of
> order `N` is **strictly less than `q²/N`**

— i.e. strictly weaker than the birthday bound `q²/2N` the repo already proves. The vacuity gate
on `ε` (which *is* correctly placed — see node check below) removes only the trivial `le_refl`
cheat; it does not make the statement say "beyond birthday".

### Two subsidiary inaccuracies in the same docstring

* "*in the range where `q²/N` says anything*" — `q²/N` says something only for `q < √N`, but the
  conjunct's range is `1 < q < N`. On the bulk of that range (`√N < q < N`) the conjunct is
  discharged by the cap alone: the proof's own first branch is
  `hcase : N < q^2 ⊢ min_le_left … ; 1 < q²/N`. So the conjunct has content only on `q ≤ √N`,
  which is *precisely* the range where the birthday bound is already good.
* `q < N` is a further needless weakening: for `N ≤ q` one has `q²/N ≥ q ≥ 2 > 1 ≥ ε`, so the
  hypothesis could be dropped. Its presence makes the clause look narrower/sharper than it is.

### What the file actually proves (and does not expose)

The real content is `Δ ≤ sopEps (card H) q` with `sopEps N q = min 1 (Σ_{k<q} k²/(N−k)²) ≈ q³/3N²`
— genuinely beyond birthday: non-trivial out to `q ≈ 1.44·N^{2/3}` versus `N^{1/2}`. I extracted
it as a standalone theorem (`…probe-semantics.lean`, `explicit_bound`, axioms
`[propext, Classical.choice, Quot.sound]`) by replaying the file's own calc. **But this statement
appears nowhere as a named declaration** — it exists only inside the `∃`-proof, and `Exists` is a
`Prop`, so no downstream consumer can recover `sopEps` from `sop_randomness_expander_tight`. The
theorem as published is strictly less useful than the proof that backs it.

**Recommended fix (not applied — read-only):** export the explicit bound as a named theorem, and
either drop the `∃ ε` packaging or replace the floor clause with one that bites, e.g.
`∀ N q, 1 < q → q^3 ≤ N^2 → ε N q < (q:ℝ)^2 / (2*N)` (the sharper form the repo already proves for
birthday), or an asymptotic clause `ε N q ≤ C·q³/N²`.

---

## FINDING 2 — MINOR — `sop_randomness_expander_tight` / `maxAdvantage`: prob-dist side conditions are unstated

`Δ(S,T) := sSup {advantage D S T | D.isProbDist}` with `advantage D S T = Pr^{DT}(1) − Pr^{DS}(1)`
is a *signed* sup. It equals the statistical distance, is symmetric, and is `≤ 1` **only when
`S` and `T` are probability distributions** — see `maxAdvantage_comm` / `maxAdvantage_le_one`
(`CompatibleMetric.lean:1405,1470`), both of which take `isProbDist` hypotheses; the repo's own
`AttainmentCounterexample` documents that the unnormalised carrier is where this breaks.

`⌈q⌉ sopReal` and `⌈q⌉ sopIdeal` *are* probability distributions (I closed both with `cr18_prob`
in the vacuity probe), so the reading is sound. But the theorem statement records
neither fact, and — unlike `SumOfPermutations.lean`, which has `sopReal_isProbDist` —
`SumOfPermutationsTight.lean` provides **no** `sopReal_isProbDist`. A reader of the statement
alone cannot tell that `Δ` here is an advantage rather than a signed sup on the unnormalised
carrier. Not a soundness defect; a statement-hygiene defect.

---

## FINDING 3 — MINOR (cross-slice note) — `sopEps` is not the displayed formula for `q > N`

`sopEps N q = min 1 (∑ k ∈ range q, (k:ℝ)^2 / ((N:ℝ) - k)^2)`. At `k = N` the denominator is `0`
and Lean's `x/0 = 0`, so that term silently vanishes; for `k > N` the term is `k²/(k−N)²`, which
the "`Σ_{k<q} k²/(N−k)²`" prose does not suggest. This is **harmless here** — for `q > N ≥ 2` the
`k = N−1` term is already `(N−1)² ≥ 1`, so `sopEps = 1` and the bound is trivially true — but the
definition is not the mathematical object its docstring displays outside `q ≤ N`. (`sopEps` is
owned by the `mass-layer-and-epsilon` slice; flagged here because it is the `ε` this theorem
exhibits.)

---

## Node-by-node results

### NEW (16) — all checked

| node | (a) Lean | (b) math | verdict |
|---|---|---|---|
| `sop_randomness_expander_tight` | see Findings 1–3 | statement is **true** (verified) but under-specified | **MAJOR** |
| `sopReal` | CLEAN | CLEAN | CLEAN |
| `sopIdeal` | CLEAN | CLEAN | CLEAN |
| `sopFunction` | CLEAN | CLEAN | CLEAN |
| `sopTightGame` | CLEAN | CLEAN | CLEAN |
| `sopTightGame_ignoreMBO` | CLEAN | CLEAN | CLEAN |
| `sopIdeal_isProbDist` | CLEAN | CLEAN | CLEAN |
| `sopIdeal_totalOnNonempty` | CLEAN | CLEAN | CLEAN |
| `seededConditionCGame_ignoreMBO` | CLEAN | CLEAN | CLEAN |
| `sopReal._proof_1` | `Nonempty (Perm G × Perm G)` — instance side-goal | — | CLEAN |
| `sopIdeal._proof_1` | `Nonempty (G → G)` — instance side-goal | — | CLEAN |
| `sopTightGame.eq_1` | `@[defeq]` equation lemma, `Eq.refl` | — | CLEAN |
| `sop_randomness_expander_tight._proof_1_1` | `omega` term: `1 < q → ¬0 < q → False` | — | CLEAN |
| `sop_randomness_expander_tight._proof_1_2` | `omega` term: `¬N < q² → ¬q² ≤ N → False` | — | CLEAN |
| `sopIdeal_isProbDist._simp_1_1` | `propext (isProbDist_fTransform …)` | — | CLEAN |
| `sopIdeal_isProbDist._simp_1_7` | `eq_true uniform_isProbDist` | — | CLEAN |

**What I actually checked, in detail:**

* **`sopReal` = independent uniform permutations, applied as `x ↦ π₁x + π₂x`.**
  Signature is `{G} [Fintype G] [DecidableEq G] [AddCommGroup G] → PFunPDS G G` (no spurious
  `Nonempty` binder). I confirmed in Lean that
  `Dist.uniform (Equiv.Perm G × Equiv.Perm G) = Dist.prod (Dist.uniform (Perm G)) (Dist.uniform (Perm G))`
  — the uniform law on the product *is* the independent product, not assumed
  (probe-semantics.lean, item 3b). Also confirmed
  `sopReal = PFunPDS.ofFunDist (Dist.fTransform sopFunction (Dist.uniform (Perm G × Perm G)))`,
  i.e. the system is exactly "sample the pair, answer with the induced function"; `fTransform`
  correctly collapses pairs inducing the same function and sums their mass.
  `sopFunction p x = p.1 x + p.2 x` uses the `AddCommGroup` `+`. ✔
* **`sopIdeal` = URF.** `SoPTight.sopIdeal (G := G) = PFunPDS.URF` closes by **`rfl`**, and
  `PFunPDS.IsRandomFunction sopIdeal` (CR18 Def 3.15) by `ofFunDist_isRandomFunction`. ✔
* **`sopTightGame_ignoreMBO : ignoreMBO sopTightGame = sopReal`** — the hinge. Semantics checked
  independently: `stripMBO ∘ (a ↦ historyEvaluator (l,h ↦ (F a (l.getLast h), decide (bad a l))))
  = (a ↦ functionEvaluator (F a))` (this is `historyEvaluator_getLast_eq_functionEvaluator`,
  `rfl`), then `fTransform_comp` collapses the two pushforwards. Same seed law and same
  `sopFunction` as `sopReal` — no substitution slipped in. ✔
* **`seededConditionCGame_ignoreMBO`** (the uncommitted one, `SwitchingLemma.lean:1864`). I read
  the full uncommitted diff. It is the **generalisation of an already-committed lemma**: the same
  proof script previously sat inline in `seededHashThenURFGame_ignoreMBO`, and the diff *replaces*
  that proof with `seededConditionCGame_ignoreMBO _ _ _`. So the new lemma re-proves a result that
  was already reviewed and is already load-bearing for the CBC/NMAC bounds. Statement is
  mathematically correct (pushforward composition). Axiom-clean. ✔ The DAG's "uncommitted,
  never-reviewed" flag is a real provenance fact but not a defect.
* **Vacuity gate on `ε`.** `#check` confirms `ε` is `∃`-bound **outside** the `∀ H` block:
  `∃ ε, (∀ (H : Type u_1) [Fintype H] … , 〈⌈q⌉sopReal | ⌈q⌉sopIdeal〉 ≤ ε (Fintype.card H) q) ∧ …`.
  `sopEps : ℕ → ℕ → ℝ` has **no** instance arguments — it is genuinely closed. `Fintype.card H` is
  the only channel from the group to `ε`, and it is taken w.r.t. the same `Fintype H` binder used
  by `sopReal`/`sopIdeal`. The gate works as documented; it is just weaker than the docstring
  claims (Finding 1).
* **Non-vacuity of the `∀ H` binder.** Instantiated at `ZMod 5` in Lean
  (probe-semantics.lean, item 3b): all four instance binders are satisfiable simultaneously, and
  the specialised statement `Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ sopEps 5 q` type-checks.
* **`sopIdeal_isProbDist` / `sopIdeal_totalOnNonempty`.** Both correctly `omit [AddCommGroup G]`
  (neither needs it); `TotalOnNonempty` unfolds to "every support atom is defined on every
  nonempty history", which is exactly right for a `functionEvaluator` pushforward. ✔

### LIB — substantive (54) — all statements read

**Distinguishing / advantage (`Distinguishing.lean`, `MaxWinProb.lean`, `PDS.lean`) — CLEAN**

* `maxAdvantage S T = sSup {advantage D S T | D.isProbDist}`, `advantage D S T =
  Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`, `verdictProb = GamePerf.winProb PFunDDS.verdict`,
  `winProb win W G = Σ_{w,g} W(w)·G(g)·⟦win w g⟧`.
* **The class is inhabited** — `advantage_image_nonempty` exhibits `rejectDistinguisher` (the
  point mass on `rejectDDD`), and `bddAbove_advantage_image` bounds the set by `T.weight`. So
  `sSup` is a genuine supremum, **not** the `sSup ∅ = 0` junk value. This was the main vacuity
  risk in the slice and it does not fire.
* **The class is rich enough.** `DDD X Y = {d : List (Option Y) → X ⊕ Bool // StopFinal d}` is
  every deterministic adaptive distinguisher with a final verdict; `Dist (DDD X Y)` with
  `isProbDist` gives every finitely-randomised one. The point mass on any deterministic `d` is
  admissible, so `Δ` dominates every adaptive strategy.
* **Signed sup = statistical distance.** For probability systems, `max_E (T(E) − S(E)) =
  TV(S,T)` because complementing `E` flips the sign; a deterministic `D` that queries a fixed
  schedule and outputs `1` on `E` realises it. So the one-sided-looking `Δ(sopReal, sopIdeal)`
  is the full two-sided advantage. (`maxAdvantage_comm` in `CompatibleMetric.lean:1405` is the
  library's own statement of this, with the necessary `isProbDist` hypotheses.)
* `PFunDDS.verdict d s := ∃ n, d.val ((transcript s (ddToDDE d) n)↓ᵧ) = Sum.inr true` — reads the
  verdict off the generic transcript; non-termination defaults to `0`. `StopFinal` makes it
  well-defined. `ddToDDE` forgets the verdict so the interaction is the generic one. ✔

**Query filter (`PDS.lean:120`, `PFunDDS.lean:336,360`, `keptPrefix`, `fullyDefined`) — CLEAN**

The slice question was: does `⌈q⌉` really cap at `q`, and is it `≤ q` or `< q`? I proved four
statements in Lean (probe-semantics.lean §Cap, compiles clean):

1. `l ∈ dom (filterQueries q (functionEvaluator f)) ↔ (l ≠ [] ∧ l.length ≤ q)` — **`≤ q`**, so
   `q` queries are answered, not `q−1`.
2. inside the budget the answer is the honest `f x`.
3. `(keptPrefix (filterQueries q (functionEvaluator f)) m).length = min q m.length` — the kept
   prefix saturates at exactly `q`.
4. hence in the `fullyDefined` completion that `transcript` actually uses: query `q+1` **and
   every later query** returns `none` (⊥), and every query up to the `q`-th returns
   `some (f (l.getLast _))`.

So the cap is exactly `q` — neither more (soundness) nor fewer (strength). Note it counts
*repeats* too, which is conservative. Both sides of `Δ` are filtered identically, so ⊥ carries no
signal. `PrefixClosed (fun l => l.length ≤ q)` is correct and is what `filterDom` requires.

**MBO stripping (`SystemMBO.lean`, `RelateGameDistinguishing.lean:190`) — CLEAN**

`PFunDDS.stripMBO s = ⟨fun l => (s.1 l).map Prod.fst, s.2⟩` — post-composition with `Prod.fst`,
domain-preserving (validity is inherited *definitionally*, `stripMBO._proof_1` is `s.2`).
`PFunPDS.stripMBO = fTransform PFunDDS.stripMBO`; `ignoreMBO` is a compatibility `abbrev` for it,
not a second implementation. This is CR18 Def 4.18 correctly rendered. ✔

**`Dist` layer (`Dist.lean`) — CLEAN, with the unnormalised caveat handled**

`Dist A = A →₀ NNReal` is explicitly **not** normalised (docstring says so). Every probability
claim on the path carries an `isProbDist`:
`uniform_isProbDist` (via `weight_uniform`, `weight_eq_sum`, `uniform_apply = 1/card A`),
`isProbDist_fTransform` (iff, via `weight_fTransform`), `sopIdeal_isProbDist`. `Dist.mass` is
support-summed `if P a then w else 0` — correct. `fTransform` is the discrete pushforward and
`fTransform_comp : fTransform g (fTransform f X) = fTransform (g ∘ f) X` is the true functoriality
law (used twice, both times correctly). `mem_support_fTransform` is the correct support-witness
statement. ✔

**Deterministic-system layer (`PFunDDS.lean`) — CLEAN**

`Raw = List X →. Y`; `Valid S := [] ∉ dom S ∧ nonempty-prefix-closed` — Maurer's Def 3.2 / thesis
Def 2.9 exactly. `DDS` is the subtype. `functionEvaluator f` answers `f (l.getLast)` on every
nonempty history (`dom_functionEvaluator` confirms `dom = {l | l ≠ []}`), i.e. it *is* a stateless
function — no hidden statefulness. `historyEvaluator` generalises it, and
`historyEvaluator (fun l h => f (l.getLast h)) = functionEvaluator f` by `rfl` (this is what makes
the `ignoreMBO` hinge a `rfl`). `DDE = List (Option Y) → Option X`, `transcript` is CR18 Def 3.7's
recurrence through `s⊥`. `transcriptInputs/Outputs` are the `↓ₓ`/`↓ᵧ` projections. ✔

**Miscellaneous LIB — CLEAN**

* `Counting.three_sum_sq_le_cube : 3 * Σ_{k<q} (k:ℝ)² ≤ q³`. True: `3·(q−1)q(2q−1)/6 =
  q³ − 1.5q² + 0.5q ≤ q³` for `q ≥ 0`. Statement matches name and use site. ✔
* `PFunPDS.ofFunDist_totalOnNonempty` — correct, and it is exactly what `sopIdeal_totalOnNonempty`
  needs (`sopIdeal` is `ofFunDist (uniform (G→G))` definitionally). ✔
* `IsBlind w := ∀ l₁ l₂, l₁.length = l₂.length → w l₁ = w l₂` — a winner that ignores outputs.
  Correct notion; its *use* (the blind reduction) belongs to `blind-game-endpoint`. ✔
* `seededConditionCGame D F bad = fTransform (a ↦ historyEvaluator (l,h ↦ (F a (l.getLast h),
  decide (bad a l)))) D` — the MBO bit is a function of the *full* history, which is what makes
  prefix-monotonicity meaningful. ✔

### LIB — elaborator-generated (11) — no independent claim

`PFunDDS.ddToDDE.match_1`, `PFunPDS.ofFunDist.eq_1`, `PFunDDS.filterDom._proof_1`,
`PFunDDS.filterDom._proof_2`, `PFunDDS.fullyDefined._proof_1`,
`PFunDDS.functionEvaluator._proof_1`, `PFunDDS.historyEvaluator._proof_1`,
`PFunDDS.transcript._proof_1`, `PFunDDS.transcript.match_1`, `PFunDDS.transcript.match_3`,
`PFunDDS.stripMBO._proof_1`.

These are match-arm splitters, equation lemmas, and the `Valid`-side-goals of the constructions
above. They assert nothing the parent definition does not; I inspected the parent definitions.

---

## MATH CHECK — is the bound actually true?

**Exact computation, not a spot check.** `sopReal` and `sopIdeal` are both invariant under
arbitrary relabelling of the query inputs (`(π₁∘σ, π₂∘σ)` is uniform for any bijection `σ`), so
the law of the answer vector depends only on the repeat-pattern of the query list. Repeated
queries return the same answer on both sides and carry no information. Hence **the optimal
distinguisher is non-adaptive on `q` distinct inputs**, and the total-variation distance between
the two answer-vector laws *is* the exact maximal advantage.

`slice-sop-statement-and-semantics.exact-advantage.py` computes that exactly (rational arithmetic, full enumeration of injective
tuples):

| N | q | exact max advantage | `sopEps N q` | ratio |
|---|---|---|---|---|
| 2 | 2 | 1/2 = 0.500000 | 1.000000 | 2.00 |
| 3 | 2 | 1/6 = 0.166667 | 0.250000 | 1.50 |
| 4 | 2 | 1/12 = 0.083333 | 0.111111 | 1.33 |
| 5 | 2 | 1/20 = 0.050000 | 0.062500 | 1.25 |
| 6 | 2 | 1/30 = 0.033333 | 0.040000 | 1.20 |
| 7 | 2 | 1/42 = 0.023810 | 0.027778 | 1.17 |
| 8 | 2 | 1/56 = 0.017857 | 0.020408 | 1.14 |
| 5 | 3 | 0.063333 | 0.506944 | 8.00 |
| 6 | 3 | 0.055556 | 0.290000 | 5.22 |
| 7 | 3 | 0.045578 | 0.187778 | 4.12 |
| 8 | 3 | 0.037202 | 0.131519 | 3.53 |
| 7 | 4 | 0.048188 | 0.750278 | 15.6 |
| 8 | 4 | 0.043354 | 0.491519 | 11.3 |

The bound holds in every case. **The module docstring's tightness claims are confirmed exactly:**
at `q = 2` the true distance is `1/(N(N−1))` and `sopEps N 2 = 1/(N−1)²`, ratio exactly `N/(N−1)`.

Asymptotically `sopEps N q ≈ q³/3N²`, non-trivial (`< 1`) out to `q ≈ 1.44·N^{2/3}` versus the
birthday `N^{1/2}` — a real and substantial improvement. **The mathematics is sound; only the
packaging of the statement is not.** I would sign the underlying result off in a paper; I would
not sign off the theorem statement as written, because a referee reading only the statement learns
strictly less than the birthday bound already gives.

---

## Cross-slice notes (not findings on my nodes)

* The whole existential/floor packaging is reused by `RandomSystems/SumOfPermutationsOptimal.lean`
  (`sop_randomness_expander_optimal`, `sop_randomness_expander_mirror`) with the same
  `∀ N q, 1 < q → q < N → ε N q < q²/N` clause. Finding 1 applies verbatim to those statements too;
  whoever owns them should check them against the same probe.
* `SumOfPermutationsTight.lean` and `SumOfPermutations.lean` are both **untracked** in git
  (`?? RandomSystems/SumOfPermutationsTight.lean`). `SwitchingLemma.lean` carries a 100-line
  uncommitted diff, of which `seededConditionCGame_ignoreMBO` is 17 lines.
