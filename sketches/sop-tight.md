# Sketch — `sop_randomness_expander_tight` (beyond-birthday SoP by conditional equivalence)

**STATUS: FORMALIZED, axiom-clean** (`propext, Classical.choice, Quot.sound`; no `sorry`).
`ε N q = min 1 (Σ_{k<q} k²/(N−k)²)` = `sopEps`, in `RandomSystems/SumOfPermutationsTight.lean`.
Generic infrastructure added public: `RandomSystems/PermFreshCounting.lean` (`canonSubset`,
`card_permPair_restrict`, `availPairs`, `card_fresh_pair_fiber`, `card_fresh_pair_refine`).
The plan below was followed as written; §4 was retracted and rewritten.

Target (statement fixed, must not change):

```
∃ ε : ℕ → ℕ → ℝ,
  (∀ H [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H] (q : ℕ),
      Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ ε (card H) q) ∧
  (∀ N q, 1 < q → q < N → ε N q < q^2 / N)
```

Prescribed technique: **conditional equivalence, CR18 Thm 4.17.** Not coupling, not the
H-technique, no bridge to `adaptiveTranscriptAdvantage`.

---

## 0. The object of the search

`cond` (the MBO) is the free parameter and it sets the constant. So the whole of stage 1 is:

> **what is the collision MBO charging for that it does not need to?**

Incumbent (`RandomSystems/SumOfPermutations.lean`): MBO = *a collision of the sampled
function*, bound `q²/N`. Read probabilistically, that MBO insists the **internal** value
`v_i = π₂(x_i)` be *fresh* — it charges the full birthday cost of "π₂ is not a random
function". But the distinguisher never sees `v_i`; it sees `u_i + v_i`. A repeat of `v_i`
is **completely invisible** as long as the *sum* can still be handed a uniform value. The
collision MBO throws away the masking by `π₁`. Concretely it charges `2k/N` at step `k+1`
(the two chances of hitting a used image) where the honest charge is `k²/N²`.

That factor `N/k` per step is the whole prize: `q²/N → q³/3N²`.

---

## 1. The mathematics

Fix a blind (non-adaptive) query list `x₁ … x_q`; WLOG distinct — repeats cost nothing,
both worlds answer a repeat deterministically with the earlier answer.

Lazy-sample the two permutations. After `k` distinct queries let

```
U_k = {π₁ x₁, …, π₁ x_k},  V_k = {π₂ x₁, …, π₂ x_k},   |U_k| = |V_k| = k.
```

Given the state, `(u,v) := (π₁ x_{k+1}, π₂ x_{k+1})` is uniform on `Ū_k × V̄_k`
(complements, each of size `N−k`), the two coordinates independent. Hence the next answer
`y = u+v` has fiber count

```
c_k(y) = #{(u,v) ∈ Ū_k × V̄_k : u+v = y} = |Ū_k ∩ (y − V̄_k)| = |complement of (U_k ∪ (y−V_k))|
       = N − 2k + r_k(y),        r_k(y) := #{(a,b) ∈ U_k × V_k : a+b = y},  Σ_y r_k(y) = k².
```

So the real system's next answer is **not** uniform: it is biased *upward* exactly on the
`y` that are representable as `used₁ + used₂`, and in particular `r_k(y_j) ≥ 1` for every
previous answer `y_j` (witness `(u_j, v_j)`). That is the entire non-uniformity, and it is
second order: `Σ_y c_k(y) = (N−k)²`, and `N·(N−2k) = (N−k)² − k²`, so the **relative**
deficiency of the flat level below the average is only `k²/(N−k)²`.

### The MBO

> **`bad` fires at step `k+1` when the freshly sampled pair `(u,v)` falls outside a
> *balanced* subset of `Ū_k × V̄_k`.**

Balanced = every fiber of `(u,v) ↦ u+v` retains exactly `N − 2k` elements. Such a subset
exists because every fiber has `c_k(y) = N−2k+r_k(y) ≥ N−2k` elements; take any canonical
`N−2k` of them (e.g. the `N−2k` smallest under the order pulled back from
`Fintype.equivFin H` — the *choice does not matter*, only the cardinality does).

Prefix-monotone by construction: once fired, stays fired.

### Conditional equivalence (exact, no slack)

Condition on `bad` not set through step `k+1`. For each surviving state, the retained
fiber over every `y ∈ H` has exactly `N−2k` pairs, so

```
Pr[Y_{k+1} = y, ¬bad_{k+1} | y¹…y^k, ¬bad_k] = Σ_states w_state · (N−2k)/(N−k)²
```

which is **constant in `y`** ⟹ conditioned on `¬bad`, `Y_{k+1}` is uniform on `H` ⟹ the
game is conditionally equivalent to the URF. Note this is *exact*, and note it holds
however the `N−2k` retained elements were chosen: only the count enters. A repeated query
is answered deterministically in both worlds, so it is exempt.

The counting form of `hCE` (what Lean will actually see): for every query list
`x₁…x_{k+1}` and every `y`,

```
#{(π₁,π₂) : ¬bad, π₁x_j+π₂x_j = y_j (j ≤ k), π₁x_{k+1}+π₂x_{k+1} = y}
  = ((N−k−1)!)² · #{good k-prefixes for y¹…y^k} · (N−2k)
```

— the `y`-dependence has vanished. The extension count `((N−k−1)!)²` is constant because
"pair of permutations with prescribed values on `k+1` points" always has the same number of
completions.

### The charge

Per step, conditionally on the state and on `¬bad_k`:

```
Pr[bad fires at step k+1] = 1 − N(N−2k)/(N−k)² = k²/(N−k)²      (and ≥ that is impossible:
                                                                 the flat level is capped by
                                                                 min_y c_k(y))
```

so, telescoping / union bound over steps,

```
ε(N,q) = Σ_{k=0}^{q-1} k²/(N−k)²   ≈ q³/(3N²).
```

Degenerate arm: when `2k ≥ N` the balanced subset is empty, `bad` fires with probability 1,
and `k²/(N−k)² ≥ 1` — the bound still holds. This is the "one-cell" arm of the analysis.

### Calibration (why this is the sharp form)

* `q = 2`: bound `1/(N−1)²`. Exact real law: `H(y₁,y₂) = N(N−2)` for `y₁ ≠ y₂`, so
  `P/Q = N(N−2)/(N−1)² = 1 − 1/(N−1)²`, and the true `Δ = 1/(N(N−1))`. The MBO is
  **exactly** the worst-case pointwise deficiency; the bound is off by `N/(N−1)`.
* `q³/N²` (H-technique, `HTechnique/SoP/LawAdvantage.lean:163`): 8× worse at `q=2`.
* `2q³/3N²` (coupling, `SoP/SoP2.lean` Cor 9): 5.3× worse at `q=2`, 2× worse asymptotically.
* Published `(q/N)^{3/2}` (Dai–Hoang–Tessaro) is better for `q > N^{1/3}` and is **not
  reachable by CE** — see §4.

---

## 2. Technique, and the doors rejected

* **Conditional equivalence, Door 1** (`maxAdvantage_filterQueries_seededConditionCGame_le`):
  the real system *is* a seed-indexed last-query evaluator — seed `(π₁,π₂)`,
  `F (π₁,π₂) x = π₁ x + π₂ x` — so Door 1 applies and I do not own `Γᵇ`.
* **Door 2 (raw 4.17)** rejected: nothing about this system fails the seeded-evaluator test,
  so owning `Γᵇ` by hand buys nothing.
* **Family I (exact equality)** rejected: `Δ > 0` genuinely (the real law over-weights
  repeated answers by `1 + C(y)/N`), so no behavioural-quotient collapse.
* **Family II hybrid** rejected *as the main route*: the hybrid `π₁+π₂ → π₁+f → f`
  (with `f` a URF, and `π₁+f` **exactly** a URF) reduces to the switching lemma and gives
  `q²/2N` — birthday, and it loses precisely the masking effect that §1 exploits. It is the
  incumbent's route in disguise.
* **H-technique / coupling / winnability**: excluded by the task, and (H) already benchmarked
  at `q³/N²`.

---

## 3. Obligation DAG

```
sop_randomness_expander_tight
└── ε := fun N q => min 1 (Σ_{k<q} k²/(N−k)²)     [choice of ε]
    ├── clause (a): ∀ H q, Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ ε N q
    │   ├── [LIB]      Δ ≤ 1 arm (the `min 1` branch)
    │   ├── [LIB]      sopReal = ignoreMBO (seededConditionCGame D F bad)
    │   ├── [LIB]      Door 1 endpoint  maxAdvantage_filterQueries_seededConditionCGame_le
    │   ├── [ROUTINE]  hmono (prefix monotone), hD, hT (isProbDist), hTtot
    │   ├── [CREATIVE 1] hCE : balanced fibers ⟹ conditioned law = URF law
    │   │   ├── balanced-subset selection with card = N−2k                  [needs infra]
    │   │   ├── extension count of a pair of partial injections is y-free   [needs infra]
    │   │   └── fiber count identity c_k(y) = N−2k+r_k(y)                   [ROUTINE-ish]
    │   └── [CREATIVE 2] hleaf : seed mass of bad on a FIXED list ≤ Σ k²/(N−k)²
    │       ├── per-step conditional charge = 1 − N(N−2k)/(N−k)²
    │       └── telescoping over steps
    └── clause (b): ε N q < q²/N for 1 < q < N
        ├── case N < q²   : min ≤ 1 < q²/N
        └── case q² ≤ N   : Σ_{k<q} k²/(N−k)² ≤ q³/(3(N−q)²) < q²/N   [cr18_arith-ish]
```

## 4. Where the remaining slack is — a gap in THIS MBO, not in the technique

**SETTLED — there is no CE ceiling.** An earlier version claimed `Θ(q³/N²)` is a *ceiling*
for conditional equivalence, on the grounds that CE is a pointwise/L^∞ argument that cannot
express L²/χ² cancellation. That is **false**, but not for the reason first given here: an
intermediate version "refuted" it with Lanzenberger Thm 2.37 + Thm 2.31, which are
**coupling/representative-side** attainment and do not yield a tight MBO.

The correct citation is **Maurer–Pietrzak–Renner, CRYPTO 2007, Lemma 5**
(`papers/MaPiRe07.pdf`, p. 140): for *any* two systems `S`, `T` there exist `Ŝ`, `T̂` with
MBOs such that `Ŝ⁻ ≡ S`, `T̂⁻ ≡ T`, `Ŝ⊣ ≡ T̂⊣`, and `δ_k^D(S,T) = ν_k^D(Ŝ)` for **all** `D`.
That is conditional equivalence with the distance *equal* to the winning probability. MPR07
§1.4 notes it settles an open problem from MP04 and is tight.

**The caveat that applies to this proof.** Lemma 5's MBO lives on `Ŝ`, a system *equivalent*
to `S`, built by the `min(P,Q)` split — it **redistributes** mass. The balanced-fiber event
here is a deletion on the *given* representative, and deletion cannot move surplus on one
transcript to cover a deficit on another. So any floor this MBO hits is a fact about this
representative, not about CE. The two routes onward are: refine the condition, or change the
representative.

The slack in *this* MBO is identifiable and is described below.

So the gap between `q³/3N²` and `(q/N)^{3/2}` is a gap in the *balanced-fiber event*. What
it over-charges for, precisely: it flattens each step to `min_y c_k(y) = N − 2k`, discarding
the entire excess `Σ_y r_k(y) = k²` — and `k²/(N−k)²` *is* exactly that discarded excess.
But the excess is not deficiency: a transcript that lands on `y` with `r_k(y) > 0` has
**surplus** real mass (`P/Q ≈ 1 + C(y)/N`), and the true distance `Δ = Σ_y (Q−P)⁺` averages
deficiency over transcripts rather than taking a per-step worst case. A sharper monitored
condition would have to fire with a rate depending on the *realized* fiber profile
`r_k(y_k)` — flattening to the average rather than to the minimum, paying for a lucky step
out of an earlier surplus. That is not expressible by a per-step Markovian deletion on the
state, but `bad a l` sees the whole query list, so it is not excluded either.
