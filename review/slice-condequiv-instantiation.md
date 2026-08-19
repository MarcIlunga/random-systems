# Slice review — `condequiv-instantiation` (38 nodes: 1 NEW, 37 LIB)

Reviewer: adversarial pass, read-only. No proof file was modified. All experiments in
`/tmp/sopreview/` (deleted after the run); nothing written outside `review/`.

**Verdict: no defect found. 38 / 38 nodes checked. 2 MINOR observations, both about the
generality of `CondEquiv` and about where the statement stops having content — neither
invalidates `sopTight_condEquiv` nor the root theorem.**

---

## 0. What was established, in one paragraph

`|≡` (`RandomSystems/CondEquiv.lean:118`) is CR18 Definition 4.19 eq. (4.38), read at the
unnormalized-mass level, in the *cross-multiplied* form the paper itself gives, with the guard
that is footnote 29 verbatim. I proved in Lean (scratch, kernel-checked) that the guard is
**vacuous** — the guarded definition is equivalent to the unguarded identity — so nothing was
weakened by it. The four obligations of `condEquiv_of_transcript_mass_reductions` are each matched
by the argument the lemma asks for; I read the *elaborated* goals at the two `by simp` steps and
they are exactly `decide P = false ↔ ¬P` with syntactically identical side conjuncts, so the
decide/Prop bridge is sound. The conditioning event is **non-empty** in the regime the bound cares
about — I proved `massAfalse (sopTightGame (G := ZMod 5)) [0,1,2] ≠ 0` in Lean — and it is
**empty exactly where the file's docstring says it is** (`massAfalse (sopTightGame (G := ZMod 3))
[0,1,2] = 0`, also Lean-proved). An independent brute force over `Z/2, Z/3, Z/4, Z/5, Z/6,
Z/2×Z/2` confirms the mathematical content: conditioned on the monitor, the transcript law is
*exactly* uniform, while the unconditioned real law is not.

---

## 1. Paper check — is `|≡` CR18 Def 4.19 / Maurer13b Def 13?

Both PDFs read **visually** (`Read` with `pages`, no text extraction).

**Maurer13b p. 4 (art. p. 3153), Definition 13.** For an (X, Y×{0,1})-system **S** with MBO
A₀,A₁,…, let 𝒜 be "the game is not won" (A_i = 0). For an (X,Y)-system **T**, `S|𝒜 ≡ T` iff for
i ≥ 1, `p^S_{Y^i|X^i,A_i=0} = p^T_{Y^i|X^i}`; "the above condition is equivalent to
`p^S_{Y^i,A_i=0|X^i} = p^S_{A_i=0|X^i} · p^T_{Y^i|X^i}`". Footnote 9: equality is required only
"for all arguments for which they are both defined (here one considers only x^i for which A_i has
non-zero probability)".

**CR18_LN p. 108, Definition 4.19 / eq. (4.38)** — identical statement, identical footnote (29).
p. 110, Theorem 4.17: `Ŝ |≡ T ⟹ ⟨S|T⟩ ≤ b Ŝ ∘ ρT̃`, in particular `Δ(S,T) ≤ Γ(bŜ)`, where
`Ŝ⁻ = S`. So the game must sit over the system on the **left** of `Δ`.

**Lean rendering** (`CondEquiv.lean:118`):

```
massYAfalse Ŝ i ys xs * massDom T xs.toList = massY T i ys xs * massAfalse Ŝ xs.toList
```
guarded by `massAfalse Ŝ xs.toList ≠ 0` and `massDom T xs.toList ≠ 0`, for all `i : ℕ`,
`xs ys : Vector _ (i+1)`.

* `massYAfalse` = `p^Ŝ_{Y^i, A_i=0|X^i}` (unnormalized). ✓
* `massAfalse` = `p^Ŝ_{A_i=0|X^i}` (unnormalized). ✓
* `massY` = `PFunPDS.cumulativeBehavior` = CR18 Def 3.20 `p^T_{Y^i|X^i}` (unnormalized). ✓
* `massDom` = the `T`-side normalizer; `= 1` for a total probability system
  (`massDom_eq_one_of_totalOnNonempty`). ✓
* `i : ℕ` with vectors of length `i+1` ⇒ paper's `i ≥ 1`. ✓
* Guard = footnote 29/9 verbatim. ✓
* Cross-multiplied form is **scale-invariant** in both `Ŝ` and `T` (degree 1 on each side in each),
  so it is genuinely "the two conditional distributions agree" and does not silently assume that
  `Dist` is normalized — which matters, because `Dist` in this repo is *not* normalized by
  construction.

**Direction.** `sopTight_condEquiv : sopTightGame |≡ sopIdeal` with
`sopTightGame_ignoreMBO : ignoreMBO sopTightGame = sopReal`, and the endpoint concludes
`Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ ε`. That is Theorem 4.17 with `S = sopReal`, `T = sopIdeal`,
`Ŝ = sopTightGame`. Direction is correct.

---

## 2. The guard is not a weakening (Lean-proved)

Concern: the Lean definition only demands (4.38) where `massAfalse ≠ 0 ∧ massDom ≠ 0`, whereas a
consumer proof may need the unguarded identity. I proved in a scratch file (compiles clean under
`lake env lean`, no `sorry`):

```
theorem massYAfalse_le_massAfalse : massYAfalse S i ys xs ≤ massAfalse S xs.toList
theorem massY_le_massDom          : massY T i ys xs   ≤ massDom T xs.toList
theorem condEquiv_iff_unguarded (S T) :
    (S |≡ T) ↔ ∀ i xs ys, massYAfalse S i ys xs * massDom T xs.toList
                        = massY T i ys xs * massAfalse S xs.toList
```

(The `≤`s hold because instantiating the `∀ k` at `k = i` gives `xs.toList.take (i+1) = xs.toList`,
i.e. the numerator event implies the normalizer event.) So the guards can never hide a gap: where
they fail, both sides are `0`. **No finding.**

---

## 3. The four obligations of `condEquiv_of_transcript_mass_reductions`

Elaborated signature (from `#check @…`, so no reading-comprehension risk):

| # | obligation | supplied in `sopTight_condEquiv` | verdict |
|---|---|---|---|
| hAf | `∀ {xs}, xs ≠ [] → massAfalse Ŝ xs = D₁.mass (E · xs)` | `fun {xs} hne => …` (unfold + `massAfalse_fTransform_historyEvaluator` + decide-bridge) | ✓ |
| hY | `∀ {i} ys xs, massY T i ys xs = D₂.mass (∀k, outT g (xs.get k) = ys.get k)` | `massY_fTransform_lastQuery _ _ ys xs` | ✓ |
| hYAf | `∀ {i} ys xs, massYAfalse Ŝ i ys xs = D₁.mass ((∀k, out f (xs.get k)=ys.get k) ∧ E f xs.toList)` | `massYAfalse_fTransform_lastQuery … hmono ys xs` + decide-bridge | ✓ |
| hprod | per-assignment factorization on `↥xs.toList.toFinset` | `mass_agree_and_good xs.toList.toFinset a xs.toList (fun x => List.mem_toFinset.symm)` | ✓ |

with `D₁ = uniform (Perm G × Perm G)`, `D₂ = uniform (G → G)`, `out = sopFunction`,
`outT = fun g => g`, `E = fun p l => ¬ sopTightBad p l`, `hT := sopIdeal_isProbDist`,
`hTot := sopIdeal_totalOnNonempty`. Notes:

* **hY is discharged by a `functionEvaluator`/`historyEvaluator` defeq.** `sopIdeal = fTransform
  functionEvaluator (uniform (G→G))` unifies with the lemma's
  `fTransform (fun a => historyEvaluator fun l h => F a (l.getLast h))` because
  `historyEvaluator_getLast_eq_functionEvaluator` is `rfl`. Checked: this forces `F := fun g => g`,
  which is exactly the `outT` supplied — so hY cannot be satisfied with a *different* evaluator than
  the one the CE conclusion talks about.
* **hAf really needs `xs ≠ []`, and only that.** At `xs = []` the obligation is *false*
  (`massAfalse Ŝ [] = 0` since `[] ∉ dom s`, while `D₁.mass (¬ sopTightBad p []) = 1`). The template
  uses it only at `(Vector _ (i+1)).toList`, where `hne` is discharged by `simp`. Hypothesis is
  exactly as strong as needed, not silently weakened.
* **hprod is quantified over *all* `a : ↥xs.toList.toFinset → Out`**, i.e. stronger than the
  template strictly needs (it applies it only at `tupleAssignmentOn`). `mass_agree_and_good` does
  prove it for all `a`. No mismatch.
* `hT`/`hTot` are `autoParam`s (`_auto_1`, `_auto_3` = the `cr18_standing` tactic syntax) but are
  **overridden by named arguments** here, so no tactic ran. Confirmed by `#print`.
* Template proof audited line by line: `massDom → 1`, `mul_one`, three rewrites, then a case split
  on `tupleConsistent`; consistent branch quotients both agreement events by
  `tuple_agree_iff_assignmentOn` (`and_congr_left'` keeps `E` untouched) and applies `hprod`;
  inconsistent branch zeroes both sides. The guards `hA`/`hD` are introduced and never used — the
  template proves the *unguarded* identity, i.e. strictly more. ✓

---

## 4. The decide-vs-Prop bridge — the two `by simp` steps

I re-elaborated the proof in a scratch copy with `trace_state` inserted. The **actual** goals are:

```
-- hAf branch
⊢ decide (sopTightBad p xs) = false ↔ (fun p l => ¬sopTightBad p l) p xs

-- hYAf branch
⊢ (∀ k : Fin (i+1), sopFunction p (xs.get k) = ys.get k) ∧ decide (sopTightBad p xs.toList) = false
  ↔ (∀ k : Fin (i+1), sopFunction p (xs.get k) = ys.get k) ∧ (fun p l => ¬sopTightBad p l) p xs.toList
```

Both are `decide_eq_false_iff_not` with a **syntactically identical** side conjunct on the two
sides — `simp` cannot be smuggling anything in, and it cannot be closing the goal by collapsing
both sides to `False`, because the two sides differ only in the `decide`/`¬` spelling. The lemma
`decide P = false ↔ ¬P` is instance-independent (`Decidable` is a subsingleton), so the fact that
`sopTightBad_decidable` is `Classical.dec` is irrelevant. **Sound. No finding.**

Ancillary: `massYAfalse_fTransform_lastQuery`'s monotonicity side condition is supplied as
`fun p l₁ l₂ hpre hb => by simpa using sopTightBad_monotone p hpre (by simpa using hb)` — the same
decide-bridge in both directions, over the genuinely-proved `sopTightBad_monotone`
(`IsPrefix.trans`). ✓

---

## 5. Is the conditioning event non-empty? (the vacuity question)

**Answer: yes where it matters, and provably empty exactly where the docstring says.**
Kernel-checked in scratch (both compile clean):

```
theorem massAfalse_ne_zero (l : List G) (hne : l ≠ [])
    (hsmall : ∀ k < l.toFinset.card, 2 * k < Fintype.card G) :
    CondEquiv.massAfalse (sopTightGame (G := G)) l ≠ 0            -- general

example : CondEquiv.massAfalse (sopTightGame (G := ZMod 5)) [0,1,2] ≠ 0   -- witness
example : CondEquiv.massAfalse (sopTightGame (G := ZMod 3)) [0,1,2] = 0   -- boundary
```

So `sopTight_condEquiv` is **not** a vacuous statement: for every history whose distinct-query
count `d` satisfies `2(d−1) < N` the good world has positive mass and (4.38) is a real constraint.
Past that boundary `freshKeep` is empty, `massAfalse = 0`, and (4.38) holds as `0 = 0` — which is
harmless because `sopEps_ge_one_of_large` caps the final bound at `1` there.

**Independent brute force** (`/tmp/sopreview/brute*.py`, exhaustive over all `(π₁,π₂)`), replicating
the monitor from the definitions but with an *arbitrary* canonical-subset choice (both ascending
and descending, to confirm choice-independence):

| G | query list | d | #good | per-transcript count | `goodCount d` |
|---|---|---|---|---|---|
| Z/2 | [0] | 1 | 4 | 2 (all 2) | 2 |
| **Z/2** | **[0,1]** | **2** | **0** | 0 | 0 |
| Z/3 | [0,1] | 2 | 27 | 3 (all 9) | 3 |
| Z/3 | [0,1,0] | 2 | 27 | 3 | 3 |
| **Z/3** | **[0,1,2]** | **3** | **0** | 0 | 0 |
| Z/4 | [0,1] | 2 | 512 | 32 (all 16) | 32 |
| Z/2×Z/2 | [0,1] | 2 | 512 | 32 (all 16) | 32 |
| **Z/2×Z/2** | **[0,1,2]** | **3** | **0** | 0 | 0 |
| Z/5 | [0,1] | 2 | 13500 | 540 (all 25) | 540 |
| Z/5 | [0,1,2] | 3 | 7500 | 60 (all 125) | 60 |
| Z/6 | [0,1] | 2 | 497664 | 13824 (all 36) | 13824 |

In every non-degenerate row the good count is **exactly constant across all transcripts** — which
*is* eq. (4.38). The `Z/2` row is the decisive one for the direction argument in the file's
docstring: in `Z/2` two distinct queries always produce equal answers, so no conditioning can make
the real law uniform — and indeed the good world is empty there, so the CE is true only vacuously,
exactly as claimed. Repeat queries (`[0,1,0]`) leave everything unchanged, as the monitor's
first-occurrence guard requires.

**Non-triviality.** The unconditioned real law on `Z/5`, queries `[0,1]`, is
`720` on the diagonal `y₀=y₁` vs `540` off it (uniform would be `576`). So the CE statement is not
true "for free": the monitor is doing real work, discarding exactly the diagonal excess. And
`1 − 13500/14400 = 0.0625 = Σ_{k<2} k²/(5−k)²`, i.e. the counting leaf's bound is met with
equality here.

---

## 6. Node-by-node coverage (38 / 38)

### 6.1 The NEW node

* **`SoPTight.sopTight_condEquiv`** (`SumOfPermutationsTight.lean:572`) — **CLEAN**.
  (a) Statement is `sopTightGame |≡ sopIdeal` with the notation resolving to
  `CondEquiv.CondEquiv` (confirmed against `#check`). All four obligations supplied in the right
  slots (§3); the two `simp` goals inspected (§4); `hT`/`hTot` explicit. Instances coherent
  (`Fintype/DecidableEq/Nonempty/AddCommGroup G`; `Nonempty` is genuinely needed for
  `Dist.uniform (Perm G × Perm G)`). Not vacuous (§5).
  (b) Mathematically true: verified exhaustively for six groups (§5), including a non-cyclic one.

### 6.2 LIB definitions — read against the paper

* `CondEquiv.massYAfalse` (61) — **CLEAN**. All-prefix `Y`-match ∧ all-prefix MBO `false`. Equals
  `p^Ŝ_{Y^i,A_i=0|X^i}` for a monotone MBO. Indexing (`take (k+1)`, `k : Fin ysl.length`) checked.
* `CondEquiv.massAfalse` (73) — **CLEAN**. `∃ h : xs ∈ dom s, (output …).2 = false` — the paper's
  `A_i = 0` at the *final* history. See MINOR-1.
* `CondEquiv.massY` (81) — **CLEAN**. Literally `PFunPDS.cumulativeBehavior` (Def 3.20).
* `CondEquiv.massDom` (88) — **CLEAN**. `mass (xs ∈ dom t)`; the `T`-side normalizer.
* `CondEquiv.TotalOnNonempty` (96) — **CLEAN**. `∀ t ∈ T.support, ∀ xs ≠ [], xs ∈ dom t`. Correct
  rendering of "defined on the histories under discussion"; quantified over `support` (not all of
  the type), which is what `massDom_eq_weight_of_totalOnNonempty` needs and all it needs.
  Satisfiable and satisfied: `sopIdeal = PFunPDS.ofFunDist (uniform (G→G))` definitionally, whose
  realizations are `functionEvaluator`s with `dom = {l ≠ []}`.
* `CondEquiv.CondEquiv` (118) — **CLEAN** (with MINOR-1). §1, §2.
* `PFunPDS.CumulativeBehavior` (PDS:459) / `cumulativeBehavior` (465) — **CLEAN**. Def 3.20; index
  `i` = paper length `i+1`; argument order `(ys, xs)` matches `p^S_{Y^i|X^i}(y^i,x^i)`.
* `tupleConsistent` (SwitchingLemma:359) — **CLEAN**. `∀ i j, xs i = xs j → ys i = ys j`.
* `tupleAssignmentOn` (540) + `._proof_1` — **CLEAN**. Choice-based representative on a finset
  targeted by `hS`; no default value, so no silent junk.

### 6.3 LIB theorems — statement + proof read

* `massDom_eq_weight_of_totalOnNonempty` (131) — **CLEAN**. `Finsupp.sum_congr` over support +
  `if_pos`; needs exactly `TotalOnNonempty` and `xs ≠ []`.
* `massDom_eq_one_of_totalOnNonempty` (141) — **CLEAN**. Adds `isProbDist`.
* `take_succ_ne_nil` (249) + `._proof_1_1` — **CLEAN**. `l ≠ [] → l.take (k+1) ≠ []`.
* `massAfalse_fTransform_historyEvaluator` (256) — **CLEAN**. `= D.mass (bit a xs = false)`;
  `xs ≠ []` is load-bearing (false without it, see §3).
* `massY_fTransform_historyEvaluator` (270) — **CLEAN**.
* `massYAfalse_fTransform_historyEvaluator` (288) — **CLEAN**. The `hmono` hypothesis is genuinely
  used (backward direction: bit false at the full history ⇒ false at every prefix). Forward
  direction instantiates `k = i` and uses `take (i+1) = toList`. Correct.
* `Dist.mass_congr` (Dist:196) — **CLEAN**. `(∀ a, P a ↔ Q a) → mass P = mass Q`.
* `Dist.mass_fTransform` (Dist:572) — **CLEAN**. `(fTransform f X).mass P = X.mass (P ∘ f)` —
  correct even though `fTransform` is `Finsupp.mapDomain` and **merges** distinct permutation pairs
  that induce the same DDS. This is the one place a pushforward could have silently lost mass; it
  does not.
* `getLast_take_succ` (Lemma415:332) + `._proof_1_1` — **CLEAN**. `(l.take (m+1)).getLast = l.get m`.
* `PFunDDS.dom_historyEvaluator` (142) / `historyEvaluator_output` (148) — **CLEAN**; `dom = {l ≠ []}`,
  output is the callback. (Cross-read `historyEvaluator_getLast_eq_functionEvaluator`, which is
  `rfl` and is what makes hY typecheck.)
* `mass_tuple_agree_eq_zero_of_not_consistent` (373) — **CLEAN**.
* `mass_tuple_agree_and_event_eq_zero_of_not_consistent` (395) — **CLEAN**; the side event `E` is
  arbitrary, which is what the template needs.
* `vector_toList_toFinset_eq_image_get` (416) — **CLEAN**.
* `forall_toList_iff` (438) — **CLEAN**; list-index ↔ vector-index transport, both directions.
* `massY_fTransform_lastQuery` (457) — **CLEAN**.
* `massYAfalse_fTransform_lastQuery` (473) — **CLEAN**; monotonicity stated on the `Bool` bit
  (`bit a l₁ = true → bit a l₂ = true`), matching what the instantiation proves.
* `tuple_agree_iff_assignmentOn` (546) — **CLEAN**; `hcons` used in the ← direction, as required.
* `condEquiv_of_transcript_mass_reductions` (576) — **CLEAN**. §3.

### 6.4 Elaborator-generated (no content; signatures printed and inspected)

`massAfalse_fTransform_historyEvaluator.match_1_1`, `massY_fTransform_historyEvaluator.match_1_1`,
`take_succ_ne_nil._proof_1_1`, `getLast_take_succ._proof_1_1`, `PFunDDS.output.congr_simp`,
`tupleAssignmentOn._proof_1`, `condEquiv_of_transcript_mass_reductions._auto_1` and `._auto_3`
(= `cr18_standing` syntax, not invoked here). All **CLEAN**.

Axiom check re-run: `sopTight_condEquiv`, `condEquiv_of_transcript_mass_reductions`,
`massYAfalse_fTransform_historyEvaluator` each depend on exactly
`[propext, Classical.choice, Quot.sound]`.

---

## 7. Findings

### MINOR-1 — `CondEquiv` conditions on two *different* events, reconciled only by monotonicity

`massAfalse Ŝ xs` requires the MBO bit to be `false` **at `xs` only**; `massYAfalse Ŝ i ys xs`
requires it to be `false` **at every prefix** of `xs`. For a monotone MBO these are the same event
(and both equal the paper's `A_i = 0`). `CondEquiv` (`CondEquiv.lean:118`) carries **no**
monotonicity hypothesis, so for a general `(X, Y × Bool)`-system `|≡` is a hybrid that is neither
CR18 Def 4.19 (which presupposes an MBO, CR18 Def 3.22) nor internally coherent.

*Impact here: none.* `sopTightBad_monotone` is proved and used, and the consuming endpoint
`maxAdvantage_filterQueries_seededConditionCGame_le` separately requires `MonotoneMBO`. But the
definition alone does not encode the paper's standing assumption, so a future instantiation with a
non-monotone bit could produce a `|≡` that reads like Def 4.19 and is not. Recommend documenting
(or adding) the monotonicity side condition. **No change to the theorem under review.**

### MINOR-2 — the conditional equivalence has content only below `N/2` distinct queries

Lean-proved boundary: `massAfalse (sopTightGame (G := ZMod 3)) [0,1,2] = 0`, and in general
`freshKeep` is empty once `2k ≥ N`, so every history with `2(d−1) ≥ N` distinct queries satisfies
(4.38) as `0 = 0`. This is *not* a defect — it is stated openly in the file docstring, it is forced
(in `Z/2` the real law is not full, so no non-vacuous CE with the URF can exist), and the final
bound survives it because `sopEps = min 1 (…)` and `sopEps_ge_one_of_large` pushes the bound to `1`
in exactly that regime. Recorded so that no reader treats `sopTight_condEquiv` as a statement
about all `q`. **No change to the theorem under review.**

---

## 8. What I did NOT check (out of slice)

* `mass_agree_and_good`, `card_goodAgree`, `card_good`, `goodCount`, `goodCount_step`,
  `card_avail_fresh*`, `freshFiber`/`freshKeep`/`sopFresh`, `Counting.canonSubset*`,
  `Counting.card_fresh_pair_refine` — the counting slice. I did **not** read their proofs. I did
  independently validate the *conclusion* they feed into hprod (transcript-independence of the good
  count) by exhaustive brute force over six groups (§5), which is evidence, not verification.
* `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`, `blindMaxWinProb_*`,
  `IsBlind`, `blindQueryList`, and everything else in `blind-game-endpoint`. In particular I did
  **not** verify that `|≡` + `MonotoneMBO` actually yields the advantage bound (CR18 Thm 4.17); my
  slice only establishes that `|≡` *means* eq. (4.38).
* `sopTightGame_ignoreMBO`, `sopEps*`, `mass_sopTightBad_le`, `sop_randomness_expander_tight` —
  root/endpoint slices. I read their statements only.
* `sopIdeal_isProbDist`, `sopIdeal_totalOnNonempty` — not slice nodes. I checked their elaborated
  statements and that `sopIdeal` is definitionally `PFunPDS.ofFunDist (uniform (G→G))`, but did not
  audit `cr18_prob` / `ofFunDist_totalOnNonempty`.
* `Dist.mass_mono`, `Dist.uniform_mass_eq_card_filter` — used only inside my own scratch proofs;
  statements read, proofs not.
* `condEquiv_filterDom` / `condEquiv_filterQueries` (`CondEquiv.lean:203/237`) — not slice nodes,
  but I read them while checking the surrounding file; statements and proofs look correct.
  They are the bridge the endpoint needs to go from the unfiltered CE proved here to the
  `⌈q⌉`-filtered advantage; whether the endpoint actually uses them is the endpoint slice's call.
