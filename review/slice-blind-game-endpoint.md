# Adversarial review — DAG slice `blind-game-endpoint` (308 nodes, 0 NEW)

Reviewer: subagent, read-only. No proof file was modified. Scratch: `/tmp/rsrev/Chk.lean` (a
`#check`/`#print axioms` probe), deleted at the end.

Root declarations reviewed:

| # | decl | file:line |
|---|---|---|
| R1 | `RandomSystems.CR18.blindQueryList` | `RandomSystems/SwitchingLemma.lean:811` |
| R2 | `RandomSystems.CR18.blindQueryList_length_le` | `RandomSystems/SwitchingLemma.lean:814` |
| R3 | `RandomSystems.CR18.blindMaxWinProb_filterQueries_monitored_le` | `RandomSystems/SwitchingLemma.lean:1778` |
| R4 | `RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le` | `RandomSystems/SwitchingLemma.lean:1881` |
| R5 | `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` | `RandomSystems/GameOf.lean:1432` |

**Bottom line: no soundness defect found in this slice.** The `IsBlind` / `blindQueryList`
adaptive→non-adaptive reduction is legitimate, and it is legitimate for the reason Maurer gives:
blindness is *derived* by absorbing the copying converter `T̃` into the distinguisher, not assumed of
the distinguisher. Five MINOR findings below, all about statement strength, hygiene, or a factual
error in the DAG's own slice note — none of them changes the truth of the endpoint or of the SoP
root theorem.

---

## 0. The claim this slice has to support

`R5` is Maurer CR18 Theorem 4.17 in filtered form:

```
[Nonempty X] (q) (Shat : PFunPDS X (Y × Bool)) {S T : PFunPDS X Y}
  (hCE : Shat |≡ T) (hstrip : Shat.ignoreMBO = S) (hmono : MonotoneMBO Shat)
  (hS : Shat.isProbDist) (hT : T.isProbDist)
  (hStot : TotalOnNonempty Shat) (hTtot : TotalOnNonempty T)
  : (Δ(⌈q⌉ S, ⌈q⌉ T) : ℝ) ≤ (Γᵇ (⌈q⌉ Shat) : ℝ)
```

Statement elaborated and confirmed verbatim by `#check` (see §6). Note the shape: **there is no `D`
in the statement.** `Δ` is `sSup` over *all* probability distinguishers
(`Distinguishing.lean:136-137`), with no blindness, no query-count and no other restriction. So this
theorem does bound the adaptive advantage. The blindness lives only on the *game-winner* side of
the inequality. That is exactly the right place, and it is where the review has to be sharp.

---

## 1. Is `IsBlind` the right restriction? (the slice's key question)

`RandomSystems/BlindConverter.lean:51`:

```lean
def IsBlind (w : PFunDDS.Winner X Y) : Prop :=
  ∀ l₁ l₂ : List (Option Y), l₁.length = l₂.length → w l₁ = w l₂
```

with `Winner X Y = DDE X Y = List (Option Y) → Option X` (`PDS.lean:3068`), and
`IsBlindDist W := ∀ w ∈ W.support, IsBlind w` (`BlindConverter.lean:57`), and

```lean
Γᵇ Shat := sSup ((fun W => winProb W Shat) '' {W | IsBlindDist W ∧ W.isProbDist})
```

**LEAN CHECK — pass.** `IsBlind` says the winner's *entire* behaviour (which query, and whether to
stop) is a function of the round number only, never of the reply values. `winnerView`
(`PDS.lean:3104`) feeds a winner `h.map (Option.map Prod.fst)`, which is length-preserving, so
blindness at the `Winner` level is blindness against the game. `IsBlindDist` is per-realization, so a
blind *randomized* winner is a distribution over fixed schedules — Maurer's `p^W_{Xᵢ|Xⁱ⁻¹}` rather
than `p^W_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}` (Def 4.20 / eq. 4.35). Not vacuous: constant winners are blind, and
`bddAbove_blindWinProb_image` shows the sup is a genuine lub, not junk `sSup`.

**The direction-of-danger analysis.** `Γᵇ` appears on the *large* side of `Δ ≤ Γᵇ`. Making `IsBlind`
too **strong** would shrink the index set, shrink `Γᵇ`, and make `R5` an unsound claim. It is
therefore not enough that `IsBlind` be a *sound* over-approximation; the absorbed winner really has
to satisfy it. It does, and this is proved, not assumed:

* `absorbedWinner d t l := ddToDDE d (transcriptOutputs (transcript t (ddToDDE d) l.length))`
  (`BlindAbsorption.lean:130`) — replays `d` against a **fixed sampled realization `t ← T`**, so it
  reads only `l.length` from the live game. `isBlind_absorbedWinner` (`:135`) is one `simp only`.
* `absorbedWinnerDist D T := fTransform (fun p => absorbedWinner p.1 p.2) (Dist.prod D T)`
  (`:167`), blind-supported by `isBlindDist_absorbedWinnerDist` (`:185`).
* `advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo` (`:728`) has **no `hblind` hypothesis on
  `D`**; blindness is obtained from the construction. This is the load-bearing improvement over the
  earlier `advantage_le_blindMaxWinProb_of_condEquiv_of_blind` (`BlindConverter.lean:183`), which is
  retained only as a documented non-endpoint helper.

**MATH CHECK — pass, and this is the crux.** The reduction is sound because the replayed reply
process is `T`'s (the *ideal*), sampled independently of `Ŝ`, not `Ŝ`'s. That is exactly Maurer's
eq. (4.40) "absorbing `T̃` into the winner". The Lean discharges the substantive step, not a
paraphrase of it:

* `winnerFactor_absorbedWinnerDist_eq` (`:346`) — the absorbed winner's schedule probability is the
  `T`-marginal `∑_{yⁱ} winnerFactor(D-as-winner)(xⁱ,yⁱ)·p^T_{Yⁱ|Xⁱ}(yⁱ,xⁱ)`. Proved by fiber
  decomposition (`mass_eq_tsum_of_unique`) with existence (`absorbed_fiber_hex`, `:284`, via
  `run_to_matches` + `winnerMatches_inj_xs`) and uniqueness (`absorbed_fiber_huniq`, `:322`, via
  `run_proj`), on the never-winning game `tagFalse t` whose `Y`-process is `t`
  (`ignoreMBO_tagFalse`, `not_winsDDS_tagFalse`).
* `massYAfalse (gameEnhance T Ŝ) = massY T · massAllFalse Ŝ` (`Theorem417.lean:81`), a genuine
  rectangle split through `Dist.mass_prod_and` (`Dist.lean:1461`, checked: it really is the
  independent-product factorization, proved from `prod_apply`), and
  `massAllFalse = massAfalse` under `MonotoneMBO` (`Theorem417.lean:176`, via
  `outputBit_false_of_isGame`, which is derived from Def 3.22 `IsMBO`, not posited).
* `tsum_massYAfalse_eq_massAfalse` (`BlindAbsorption.lean:378`) marginalizes the game's visible
  output on the other side. Both inner sums then collapse to the same `Gx · massAfalse Ŝ xⁱ`
  (`notWonProbBehavior_absorption`, `:541`).

I would sign this off in a paper. It is Maurer's argument, with the two marginalizations that the
paper does in one line each actually carried out.

**Verdict: CLEAN.**

---

## 2. R1/R2 — `blindQueryList`, `blindQueryList_length_le`

```lean
def blindQueryVector (w) (q) : Fin q → Option X := fun i => w (List.replicate i.1 none)
def blindQueryList  (w) (q) : List X := ((List.finRange q).map (blindQueryVector w q)).reduceOption
theorem blindQueryList_length_le : (blindQueryList w q).length ≤ q
```

**LEAN CHECK — pass.** For a blind `w`, `w l = w (replicate l.length none)`, so `blindQueryVector`
really is *the* schedule and it depends on `w` and `q` only — no game, no seed, no replies. That is
precisely what turns the adaptive adversary into a fixed schedule, and it is why the endpoint's leaf
`∀ w, IsBlind w → D.mass (fun a => bad a (blindQueryList w q)) ≤ ε` is a statement about a
*non-adaptive* query list. `blindQueryList_length_le` = `reduceOption_length_le` ∘ `length_finRange`;
axioms `[propext, Quot.sound]` only. Correct.

**MATH CHECK — pass, with one semantic caveat (see MINOR-1).** `List.reduceOption = filterMap id`
drops **every** `none`, not just a trailing run (verified by `#eval`: `[some 1, none, some 2, none,
some 3].reduceOption = [1,2,3]`). Meanwhile the interaction *freezes* at the first stop
(`transcript_succ_stall` / `transcript_freeze`), so a winner that returns `none` at round `m` never
issues anything at rounds `> m`. Consequently `blindQueryList w q` can contain queries the winner
never issues. The link back to the actual run is `isPrefix_blindQueryList`
(`SwitchingLemma.lean:822`), which is stated in the safe direction:

```
xs.length ≤ q → (∀ k, blindQueryVector w q ⟨k,_⟩ = some (xs.get k)) → xs <+: blindQueryList w q
```

so the real query list is a **prefix**, and monotone `bad` transports `bad xs → bad (blindQueryList
w q)`. The over-approximation therefore only makes the caller's obligation harder. Sound.

**Verdict: CLEAN** (see MINOR-1 for the caveat).

---

## 3. R3 — `blindMaxWinProb_filterQueries_monitored_le`

```
(hmono : ∀ a, l₁ <+: l₂ → bad a l₁ → bad a l₂) (q) (ε : NNReal)
(hleaf : ∀ w, IsBlind w → D.mass (fun a => bad a (blindQueryList w q)) ≤ ε)
  : Γᵇ (⌈q⌉ fTransform (fun a => historyEvaluator fun l h => (F a (l.getLast h), decide (bad a l))) D) ≤ ε
```

**LEAN CHECK — pass.** Four things to get wrong here; none is:

1. `hbridge` — `filterQueries q (historyEvaluator (F a ·, bad a ·)) = gameOfDDS (bad a ∘ map fst)
   (filterQueries q (functionEvaluator (F a)))`. Domains agree by `Iff.rfl`
   (`dom_historyEvaluator = dom_functionEvaluator = {l ≠ []}`, and `gameOfDDS` does not change the
   domain: `dom_gameOfDDS`); outputs agree by `ioTranscript_map_fst`. Correct.
2. `unfold PFunPDS.filterQueries; rw [Dist.fTransform_comp]` reassociates the `[q]`-pushforward so
   `blindMaxWinProb_fTransform_le` applies; that lemma (`BlindConverter.lean:103`) correctly consumes
   `hleaf` at exactly `hblind w hw` for `w ∈ W.support` of a blind `W`, and uses `hWprob` to collapse
   `(W.sum fun _ wp => wp) = 1`. The quantifier alignment is exact — no winner outside the blind
   support is fed to `hleaf`, and none inside is skipped.
3. `winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list`
   (`SwitchingLemma.lean:1124`) is the operational core and I read it in full. Two details that
   matter and are right: (a) `hraw_lt_q : raw.length < q` is *derived* from the winning history being
   in the filtered domain (`hdom.2 : xs.length ≤ q`), so a win at round `q+1` is impossible — the
   `[q]` filter really does block it; (b) each raw query is identified with
   `blindQueryVector w q k` by `transcript_input_get?_eq_env` plus `hblind` applied to a
   *length-matched* view (`hlen_view`), i.e. blindness is used exactly once, correctly, to replace
   the observed reply history by `replicate k none`.
4. Direction of the final inequality: `mass_mono` sends `winsDDS` ⊆ `bad ∘ blindQueryList`, then
   `hleaf`. Win event bounded by leaf event, not the reverse. Correct.

**MATH CHECK — pass.** This is Step 2 of a CR18 MBO-game proof done honestly: a blind winner against
a `[q]`-filtered monitored evaluator can only trigger `bad` on a prefix of its own fixed schedule, so
the win probability is bounded by the seed probability of `bad` on that schedule. Nothing is
smuggled: `bad` is a *seed* predicate on the query list, so the leaf really is a statement about the
scheme, not about the adversary.

**Verdict: CLEAN.**

---

## 4. R4 — `maxAdvantage_filterQueries_seededConditionCGame_le`, and its use by the SoP root

```
Δ(⌈q⌉ (seededConditionCGame D F bad).ignoreMBO, ⌈q⌉ T) ≤ (ε : ℝ)
```
from `hmono`, `hCE : seededConditionCGame D F bad |≡ T`, `hD`, `hT`, `hTtot`, `hleaf`.

**LEAN CHECK — pass.** The two calc legs are `R5` and `R3`. All six `autoParam` slots of `R5` are
supplied **explicitly and in the right positions** (`q`, `Shat`, `hCE`, `rfl`, `monotoneMBO`,
`isProbDist`, `hT`, `totalOnNonempty`, `hTtot`) — I checked the order against the elaborated
signature. `hstrip := rfl` pins the implicit `S` to `ignoreMBO (seededConditionCGame D F bad)`, which
is what the conclusion quantifies over, so nothing is left ambiguous. `hS`/`hStot`/`hmono` are
*discharged* from `hD`/`hmono`, not assumed (`seededConditionCGame_isProbDist` / `_totalOnNonempty` /
`_monotoneMBO`); the last routes through `historyEvaluator_pair_isGame_of_monotone`, i.e. through
Def 3.22, not through a fresh monotonicity axiom.

Non-vacuity check: the hypothesis set is jointly satisfiable — take `bad ≡ False`,
`T = ofFunDist (fTransform F D)`, `ε = 0`; then `hCE` holds (all masses coincide) and `hleaf` is
`0 ≤ 0`, and the conclusion reduces to `Δ(A,A) ≤ 0`, consistent with `maxAdvantage_self_le_zero`.
So the theorem is not true-because-unsatisfiable.

**Application check (`SumOfPermutationsTight.lean:781-787`).** The instantiation is
`D := uniform (Perm H × Perm H)`, `F := sopFunction`, `bad := sopTightBad`,
`T := sopIdeal`, `ε := _` (unified to `Real.toNNReal (sopEps (card H) q)`), and the leaf is

```lean
(fun w _ => ?_)   -- the IsBlind hypothesis is DISCARDED
… exact (Real.le_toNNReal_iff_coe_le (sopEps_nonneg _ _)).mpr
    (mass_sopTightBad_le (blindQueryList w q) q (blindQueryList_length_le w q))
```

i.e. the SoP proof proves the leaf **for an arbitrary list of length ≤ q**, using nothing about
blindness. That is the strongest possible discharge and it removes any residual worry that `IsBlind`
is calibrated to make this particular leaf easy. Good practice, worth keeping.

The `NNReal`/`ℝ` boundary flagged in the DAG note is handled correctly: `Real.toNNReal` would clamp a
negative `ε` to `0` and thereby *strengthen* the claim, but `sopEps_nonneg` (`:603`,
`le_min zero_le_one (sum_nonneg …)`, trivially correct) rules that out, and the final
`Real.coe_toNNReal _ (sopEps_nonneg _ _)` converts back with no slack.

**MATH CHECK — pass.**

**Verdict: CLEAN.**

---

## 5. R5 — `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`

**LEAN CHECK — pass.** Structure:

* `q = 0` branch: `verdictProb_eq_of_queriesExactly_zero` makes both verdict probabilities equal
  (a 0-query distinguisher's verdict is `d.val []`, system-independent given equal weights), so the
  advantage is `0 ≤ Γᵇ`. Correct, and the weight hypothesis is supplied.
* `q = n+1` branch: rewrites `⌈q⌉ ignoreMBO Shat = ignoreMBO (⌈q⌉ Shat)`
  (`PFunPDS.ignoreMBO_filterQueries`, itself `ignoreMBO_filterDom` — both are deterministic
  pushforwards whose DDS maps commute; correct), then applies the absorbed Theorem 4.17 with
  `condEquiv_filterQueries`, `monotoneMBO_filterQueries`, `totalUpTo_filterQueries`.
  - `condEquiv_filterQueries` (`CondEquiv.lean:237`) is correct: on `length ≤ q` all four masses are
    unchanged (`P` is downward-closed, `prefixClosed_length_le`); off it, `massAfalse` of the
    filtered game is `0`, contradicting the guard `hA`. So no CE obligation is silently dropped.
  - `TotalUpTo` (`Lemma415.lean:259`) is the *weaker*, filtered-friendly totality; using it here
    (rather than `TotalOnNonempty`, which a filtered game genuinely fails) is the right call.
* The `Δ`-side `sSup` is discharged by
  `maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact` +
  `deltaFilteredFiniteQueryNormalization_of_totalOnNonempty`. This is the §4.10.1 WLOG and it is the
  one step where a hand-wave would be invisible; it is **not** hand-waved.

**MATH CHECK of the §4.10.1 padding — pass, and this deserves the space.** `padDDD dummy q d`
(`GameOf.lean:492`) issues `d`'s query while `d` queries, substitutes `dummy` once `d` has stopped,
and at reply-history length `≥ q` stops with verdict
`decide (∃ n, d.val (h.take q ++ replicate n none) = Sum.inr true)`. This is the correct verdict
because:
* against `⌈q⌉S`, once `q` queries are consumed the `fullyDefined` completion answers `none` forever
  and `keptPrefix` freezes at `q` (`keptPrefix_filterQueries_eq_take_of_total`), so `d`'s own run
  continues on exactly the history `h ++ none^n` — matched by
  `verdict_filterQueries_iff_tail_of_total` (`:412`);
* if `d` stopped early with bit `b`, `StopFinal` (`PDS.lean:3080`) forces `d.val` to be `inr b` on
  every extension, so the padded verdict agrees;
* the padded and original runs coincide on the prefix where `d` is still querying
  (`transcript_padDDD_filterQueries_eq_of_all_query_before`).

Hence `verdict_padDDD_filterQueries_iff_of_total` (`:688`) is an **iff**, not an inequality, so
`advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty` (`:937`) is an **equality**. Padding is
therefore lossless, which is what makes `QueriesExactly q` a genuine WLOG rather than a restriction
on the adversary. This is the step I most expected to be weakened, and it is not.

`Δ` itself is `sSup` over *finitely supported* probability distributions on `DDD X Y`. That loses
nothing: `advantage` is affine in `D`, so the sup over finitely-supported `D` equals the sup over
point masses, i.e. over deterministic distinguishers. No adversary is excluded.

**Verdict: CLEAN.**

---

## 6. Findings

### MINOR-1 — `blindQueryList` over-approximates the winner's issued queries

`blindQueryList` uses `List.reduceOption`, which drops **interior** `none`s. Because the transcript
freezes at the first stop (`transcript_freeze`), a blind winner that returns `none` at round `m` and
`some x` at some round `k > m` never issues `x`, yet `x` appears in `blindQueryList w q`. Concretely
`w := fun l => if l.length = 0 then none else some x` is `IsBlind`, issues nothing at all, and yet
`blindQueryList w q = replicate (q-1) x`.

Direction of error is **safe**: the leaf obligation
`∀ w, IsBlind w → D.mass (fun a => bad a (blindQueryList w q)) ≤ ε` is strictly *stronger* than
Maurer's ("bad on the queries actually asked"), and `isPrefix_blindQueryList` only ever needs the
real query list to be a prefix — which it is. So the endpoint is sound; the caller merely proves
slightly more than necessary. In the SoP application this costs nothing (`mass_sopTightBad_le` is
proved for every list of length ≤ q). Worth a sentence in the `blindQueryList` docstring, because a
future caller who tries to exploit "the winner stopped, so it asked fewer queries" will find the
statement does not give that.

`severity: MINOR` — documentation / statement-tightness, not correctness.

### MINOR-2 — the DAG's slice note misstates the `autoParam` situation

`review/sop-dag.md` §5 says *"Two `autoParam` slots in
`maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` (`_auto_1`, `_auto_3`) are discharged by
tactic. Confirm what they proved."* Two corrections:

1. There are **six**, not two (`_auto_1,3,5,7,9,11` — `hstrip`, `hmono`, `hS`, `hT`, `hStot`,
   `hTtot`), and all six are listed in the slice's own membership table.
2. They proved **nothing**. `_auto_N` is Lean's auxiliary *syntax* object for a signature-level
   `:= by tac`; `#print` shows `meta def foo._auto_1 : Lean.Syntax := …`. It carries the tactic
   script, not a proof term. The obligations are discharged at each *call site*, not once inside the
   theorem.
3. On the path under review, all six are supplied **explicitly** by
   `maxAdvantage_filterQueries_seededConditionCGame_le`; `cr18_standing` never runs. So there is
   nothing hidden in the SoP chain.

`severity: MINOR` — a correction to the review scaffolding, not to the proof.

### MINOR-3 — `cr18_standing` is a globally mutable simp set feeding six `autoParam`s

`cr18_standing` (`CR18TacticsCore.lean:121`) is `simp only [cr18_standing] <;> cr18_prob` over a
`register_simp_attr` set that any downstream file can extend (`CBCMAC.lean:220`,
`CBCStructureGraph.lean:285`, …). For callers of `R5` that *omit* an argument, what those six slots
elaborate to therefore depends on which modules are imported. This cannot produce an unsound proof
(the tactic must still produce a term of the stated type), but it does mean the meaning of an
application — in particular which `S` the implicit `hstrip : ignoreMBO Shat = S` unifies with, when
`S` is not already pinned by the goal — is import-context-dependent. Not exercised here (SoP pins
`S` from the goal *and* passes `rfl`), but it is a real hazard for the CBC-MAC/SequenceHash callers,
which do rely on `cr18_standing`.

`severity: MINOR` — hygiene.

### MINOR-4 — `Δ` is a one-sided signed supremum; two-sidedness is never cited

`advantage D S T := (verdictProb D T : ℝ) - (verdictProb D S : ℝ)` and
`Δ(S,T) := sSup {advantage D S T | D.isProbDist}` (`Distinguishing.lean:130-137`). So the SoP root's
`Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ ε` literally bounds `sup_D (Pr_ideal[1] − Pr_real[1])` — one
direction only, and with the *ideal* in the positive position, which reads backwards relative to the
usual convention.

This is not a hole: `maxAdvantage_comm` (`CompatibleMetric.lean:1405`) proves `Δ(S,T) = Δ(T,S)` for
probability systems, and both filtered systems here are probability systems. But `maxAdvantage_comm`
appears **nowhere** in the proof DAG of `sop_randomness_expander_tight`, so a reader who takes the
root statement at face value gets only the one-sided bound. Recommend either citing symmetry in the
root theorem's docstring or stating the root with `|·|`.

`severity: MINOR` — statement readability / claim strength as literally written.

### MINOR-5 — `R5` demands full `TotalOnNonempty`, stronger than the filtered claim needs

`R5` takes `hStot : TotalOnNonempty Shat` and `hTtot : TotalOnNonempty T` (total on *every* nonempty
history), whereas everything downstream of the normalization only uses `TotalUpTo · (q+1)`. The
strong form is needed solely because `verdict_padDDD_filterQueries_iff_of_total` /
`deltaFilteredFiniteQueryNormalization_of_totalOnNonempty` are stated for total base systems. Extra
hypotheses weaken the theorem, so this is safe; but it means `R5` cannot be applied to an already
filtered `Shat`, and it is the reason the SoP chain has to keep an unfiltered game around. Noted for
the record, since the file's own comments claim `TotalUpTo` as "the tight assumption".

`severity: MINOR` — hypothesis strength, safe direction.

---

## 7. Verification receipts

`/tmp/rsrev/Chk.lean`, run with `lake env lean` (project oleans built from HEAD; `git diff` on
`RandomSystems/SwitchingLemma.lean` touches only proof bodies and adds four new declarations — none
of the five roots' *statements* is modified, so the olean statements are current):

* All five root signatures printed and match the source reading above (§0, §2, §3, §4).
* `#print axioms`:
  * `maxAdvantage_filterQueries_seededConditionCGame_le` → `[propext, Classical.choice, Quot.sound]`
  * `blindMaxWinProb_filterQueries_monitored_le` → `[propext, Classical.choice, Quot.sound]`
  * `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` → `[propext, Classical.choice, Quot.sound]`
  * `blindQueryList_length_le` → `[propext, Quot.sound]`
* `#print foo._auto_1` on a synthetic example confirms `meta def _ : Lean.Syntax` (MINOR-2).
* `#eval [some 1, none, some 2, none, some 3].reduceOption = [1,2,3]` confirms MINOR-1.

Scratch file deleted.

---

## 8. Coverage — what I actually checked, and what I did not

The slice is 308 nodes, of which ~90 are elaborator artifacts (`._proof_*`, `._simp_*`, `.eq_1`,
`.match_*`) that carry no independent statement. I inspected **≈150 nodes at statement level**, of
which **≈60 with the proof read**. The 90 artifacts I did not inspect individually.

**Read in full (file-level):** `RandomSystems/BlindConverter.lean` (all 12 decls),
`RandomSystems/BlindAbsorption.lean` (all 28 hand-written decls).

**Read statement + proof:** `blindQueryVector`, `blindQueryList`, `blindQueryList_length_le`,
`isPrefix_blindQueryList`, `transcript_input_get?_eq_env`,
`true_output_mem_gameOfDDS_exists_query_cond_true`,
`winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list`,
`blindMaxWinProb_filterQueries_monitored_le`, `seededConditionCGame_{monotoneMBO,totalOnNonempty,isProbDist}`,
`maxAdvantage_filterQueries_seededConditionCGame_le`, `padDDD` + its 8 companions,
`queriesExactly_ddToDDE_padDDD`, `verdict_filterQueries_iff_tail_of_total`,
`verdict_padDDD_filterQueries_iff_of_total` (most), `padDDDDist{,_isProbDist,_queriesExactly_support}`,
`verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty`,
`advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty`, `DeltaFilteredFiniteQueryNormalization`
+ its 2 constructors, `maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact`,
`totalOnNonempty_ignoreMBO`, `isProbDist_ignoreMBO`,
`maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`, `gameOfDDS` + `dom/keptPrefix/output/outputBit_gameOfDDS`,
`run_proj`, `notWonProb_eq_behavior`, `winProb_eq_behavior`, `massYAfalse_gameEnhance`,
`massAllFalse_eq_massAfalse`, `massYAfalse_le_massAllFalse`,
`massYAfalse_gameEnhance_eq_of_totalUpTo`, `outputBit_false_of_isGame`,
`condEquiv_filterDom`, `condEquiv_filterQueries` + the four `mass*_filterQueries`,
`monotoneMBO_fTransform_historyEvaluator`, `totalOnNonempty_fTransform_historyEvaluator`,
`PFunPDS.ignoreMBO_filterDom/filterQueries`, `mass_split`, `mass_mono`, `Dist.mass_prod_and`,
`Dist.prod_apply`, `historyEvaluator_pair_isGame_of_monotone`, `monotoneMBO_filterDom/filterQueries`,
`isGame_filterDom`.

**Read statement only (definitions/API I relied on but whose proofs I did not open):**
`Dist`, `Dist.weight/mass/mass_true/mass_congr/mass_add_compl/mass_eq_zero_of_forall_not/prod/
prod_isProbDist/weight_prod/weight_eq_weight_of_isProbDist/weight_eq_finsupp_sum/fTransform_isProbDist/
mem_support_fTransform/mass_prod_eq_double_sum`, `PFunDDS.Raw/Valid/DDS/dom/output/output_congr/
functionEvaluator/historyEvaluator/keptPrefix/fullyDefined/output_fullyDefined/filterQueries/
mem_dom_filterQueries/ioTranscript/ioTranscript_map_fst`, `PFunDDS.IsMBO/outputHistory/DDS.IsGame/
Winner/winnerView/ddToDDE/DDD/StopFinal`, `MonotoneMBO`, `winnerMatches`, `gameMatches`,
`massYAfalse_eq_mass_gameMatches`, `winnerFactor`, `notWonProbBehavior`, `winProbBehavior`,
`QueriesExactly`, `TotalUpTo`, `TotalUpTo_of_totalOnNonempty`, `massDom_eq_{weight,one}_of_totalUpTo`,
`totalUpTo_filterQueries`, `take_succ_get'`, `run_to_matches`, `combineSys`/`output_combineSys`,
`gameEnhance`, `massAllFalse`, `mass_congr_support`, `MassYAfalseEqAt` + `.symm`,
`distNotWonZ1_congr_mass_at`, `winProbBehavior_congr_mass_at`,
`advantage_le_winProb_of_massYAfalseEqAt`, `advantage_le_winProb_assemble`,
`CondEquiv.{massYAfalse,massAfalse,massY,massDom,TotalOnNonempty,CondEquiv,massDom_eq_weight_of_totalOnNonempty,
massAfalse_fTransform_historyEvaluator}`, `winsDDS`, `winProb`, `notWonProb`,
`winProb_add_notWonProb`, `keptPrefix_gameOfDDS_filterQueries_functionEvaluator`,
`PFunPDS.filterDom/filterQueries/isProbDist_filterQueries_iff`, `maxAdvantage`, `advantage`,
`verdictProb`, `verdictProb_eq_of_queriesExactly_zero`.

### NOT checked at all (named individually, as required)

Hand-written LIB nodes in the slice that I did not open:

* `GameOf.lean`: `foldl_keepUntil_length_eq_take`, `PFunDDS.keptPrefix_eq_of_dom_iff`,
  `PFunDDS.keptPrefix_filterQueries_eq_take_of_total`,
  `PFunDDS.keptPrefix_filterQueries_functionEvaluator`,
  `PFunDDS.output_fullyDefined_filterQueries_of_total_ge`,
  `PFunDDS.transcript_length_eq_of_fire` (statement only, proof unread),
  `PFunDDS.transcript_outputs_filterQueries_tail_of_total`,
  `PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total`,
  `PFunDDS.ddToDDE_padDDD_of_ge` (statement only),
  `PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before`,
  `PFunDDS.verdict_padDDD_iff_tail` (first half only),
  `PFunDDS.padDDD_true_iff_of_length_eq` (statement only),
  `deltaFilteredFiniteQueryNormalization_of_padDDDDist_advantage` (proof only, statement read).
* `Lemma415.lean`: `mass_prod_eq_double_sum`, `winProb_eq_prod_mass`, `transcript_zero`,
  `transcript_succ_stall`, `transcript_succ_fire`, `transcriptInputs_append`,
  `transcriptOutputs_append`, `transcriptInputs_length`, `transcriptOutputs_length`,
  `transcript_length_eq`, `transcript_take`, `transcript_freeze`, `mass_eq_tsum_of_unique`,
  `notWonProb_eq_fiber`, `run_to_matches` (proof), `winProb_eq_behavior` (only the 3-line derivation
  read).
* `Theorem417.lean`: `mass_singleton'`, `fTransform_fst_prod`, `gameEnhance_isProbDist`,
  `gameEnhance_totalUpTo`, `PFunDDS.verdict_iff_at_exact`,
  `PFunDDS.output_fullyDefined_ignoreMBO_combineSys_eq_of_totalUpTo`,
  `PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo`,
  `PFunDDS.verdict_ignoreMBO_combineSys_iff_of_totalUpTo`,
  `verdictProb_ignoreMBO_gameEnhance_eq_of_totalUpTo`, `massAllFalse_eq_massAfalse` (proof read;
  `mass_congr_support` proof not).
* `RelateGameDistinguishing.lean`: `PFunDDS.ignoreMBO`, `output_ignoreMBO`, `keptPrefix_ignoreMBO`,
  `output_fullyDefined_ignoreMBO`, `projT`, `projT_append`, `projT_inputs`, `projT_outputs`,
  `transcript_ignoreMBO`, `verdict_ignoreMBO`, `winProb_fTransform`, `winProb_fTransform_game`,
  `winProb_ddToDDE`, `verdictMatches`, `distNotWonZ1`, `PFunPDS.ignoreMBO_filterDom` (proof only),
  `projT_run_outputs`, `verdict_iff_verdictMatches`, `verdictNotWon_eq_distNotWonZ1`,
  `advantage_le_winProb_assemble` (proof).
* `PFunDDS.lean`: `output_congr` (proof), `dom_fullyDefined`, `keptPrefix_foldl_eq_append_of_mem`,
  `keptPrefix_eq_self_of_mem`, `keptPrefix_eq_self_of_mem_or_empty`,
  `output_fullyDefined_append_of_mem`, `mem_dom_filterQueries` (proof).
* `PDS.lean`: `PFunPDS.filterDom` output lemmas, `PFunPDS.isProbDist_filterQueries_iff` (proof),
  `PFunDDS.outputHistory` proofs.
* `PFunConverter.lean`: `PFunConverter.queryLimitApply`, `PFunConverter.queryLimitApply_dom` — **not
  read at all**; they enter the DAG through the `[q]` converter realization and I did not determine
  where.
* `MaxWinProb.lean`: `GamePerf.winProb_le_weight`, `GamePerf.winProb_add_compl` — statements inferred
  from use sites only.
* `Dist.lean`: `mem_support_fTransform`, `fTransform_isProbDist`, `prod_isProbDist`, `weight_prod`,
  `weight_eq_weight_of_isProbDist`, `mass_prod_eq_double_sum` — proofs unread.
* All ~90 `._proof_*` / `._simp_*` / `.eq_1` / `.match_*` / `._auto_*` elaborator artifacts, except
  `._auto_1` whose *kind* I confirmed synthetically.

### What a defect in the unchecked set would look like

The unchecked nodes are overwhelmingly transcript-algebra plumbing (`transcript_*`, `projT_*`,
`keptPrefix_*`). A defect there would most plausibly be a mis-stated `transcript_freeze` or
`transcript_take`, which would break `run_proj`/`run_to_matches` and hence the (4.35) rectangle. I
did read `run_proj` in full and it is internally consistent with the step lemmas as named, which is
partial evidence but not proof. The single node I would prioritize next is
`Lemma415.notWonProb_eq_fiber` (`:567`) — the file's own comment calls it "the isolated interaction
unfolding", i.e. the one genuinely operational kernel under `notWonProb_eq_behavior`, and I did not
open it.
