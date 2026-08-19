# Eval for the `random-systems-proofs` skill

A skill that has never been run is a hypothesis. This measures whether the skill
changes behaviour, and in which direction.

## What is graded, and why not the obvious thing

**Not "did the proof close."** Most of the skill's value is in the three stages
*before* Lean, Lean proofs are slow, and completion is a noisy signal dominated by
how hard the mathematics happens to be.

**Graded instead:**

| signal | how | why it cannot be faked |
|---|---|---|
| **routing** | `#uses_constant` walks the elaborated proof term's dependencies | grades what the proof *did*, not what the transcript *said* |
| **wrong door** | `FORBID_DEP` — the same check, negated | catches the specific rabbit hole the skill claims to prevent |
| **re-derivation** | new-declaration count against a snapshot baseline | a helper minted next to the proof is visible in the diff |
| **hygiene** | no `private` introduced | the repo's standing rule |
| **process** | a sketch exists, names a technique, carries `REUSE`/`ADAPT`/`NEW` verdicts, and is **not newer** than the Lean | the ordering check is what catches a sketch written afterwards to justify the work |
| **axioms** | `#assert_axiom_clean` | transitive, so a `sorry` in a helper is caught |

An LLM grader is left only the judgment calls — is the adaptation table
substantive, is the rejected-technique reason real. Everything above is a shell
exit code.

## Running a case

```sh
# 1. materialize the fixture and snapshot the grading baseline
bash eval/cases/case1-cbc-ce-routing/setup.sh

# 2. run the agent on eval/cases/<case>/TASK.md  (the arm under test)

# 3. grade
bash eval/assert/check.sh eval/cases/case1-cbc-ce-routing
```

**Ablation** — the number that matters — is just the skill's presence:

```sh
mv .claude/skills/random-systems-proofs /tmp/skill-off     # baseline arm
mv /tmp/skill-off .claude/skills/random-systems-proofs     # treatment arm
```

If the skill is ever packaged as a plugin, `CLAUDE_CODE_WALNUT_SPIRE=1 claude
plugin eval plugins/<name> --ablation with-without` does the same thing with
reporting attached.

## The cases

### case1 — CBC-MAC: does it take the packaged CE door?

The CBC-MAC model is present; the two headline theorems are stripped to `sorry`.
The task is a **compiling skeleton**, so creative leaves may stay open.

- **expect** `maxAdvantage_filterQueries_seededConditionCGame_le` — the packaged
  endpoint, which has already converted the adaptive bad-event bound into a
  fixed-schedule one.
- **forbid** `maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization` —
  the raw Theorem 4.17. Taking it means the run inherited `Γᵇ` and owns the
  adaptive reduction itself.

**Two arms.** With `EVAL_HOLD_OUT_RECIPE=1`, `setup.sh` also removes
`CHEATSHEET.md`'s condition-C and CBC sections.

- **1a (recipe present)** measures *did it consult the index* — realistic, but the
  cheatsheet literally says "Read this as the template for a new MBO-game proof",
  so a passing run may have found a recipe rather than routed.
- **1b (recipe held out)** measures *did it route from the model's structure*.
  **1b is the arm that predicts performance on new work** (sponge, sequence-hash),
  so weight it higher.

### case2 — chain bound: reuse or hand-roll?

Given per-hop bounds on a trace of `n + 1` systems, bound the endpoints.

- **expect** `maxAdvantage_le_adjacent_sum`. Ground truth is the one-liner
  `AdjacentMaxAdvantageBounded.traceBound hstep`, verified against the tree.
- **forbid** `maxAdvantage_triangle` — where a hand-rolled induction bottoms out.
- **budget** 0 new declarations. The reference solution adds nothing.

`sequence-hash/PLAN.md` §3b names this exact lemma as one people re-mint instead
of reusing, which is why it is the reuse case.

## Known confounds — read before believing a result

1. **`cbcGame` is *defined* as a `seededConditionCGame`.** Even in arm 1b the
   model's shape signposts the endpoint. That is arguably the fair test — "is the
   real system a seed-indexed evaluator?" is the skill's own routing question —
   but it is easier than routing for a scheme whose model you wrote yourself.
2. **CBC is well-trodden.** A model may recall the CR18 argument independently of
   both the skill and the tree. Arm 1b reduces but does not remove this.
3. **Only two cases.** These cover routing and reuse. They do **not** cover
   family-I/II omission, the most-special-variant rule, or the negative case where
   the skill should stay out of the way — all proposed but not built.
4. **The process assertions are shallow.** They check that a sketch exists, names
   a technique, and precedes the Lean. They cannot tell a good sketch from a
   ritualistic one; that is the LLM grader's job.

## What would falsify the skill

Decide this before seeing numbers.

- **case1 routes correctly without the skill** ⟹ the flagship CE content is doing
  nothing; shrink it to a pointer at `CHEATSHEET.md` §5.
- **case2 reuses only when the lemma is in `CHEATSHEET.md`** ⟹ grow the cheatsheet,
  not the skill.
- **the skill wins on 1a but not 1b** ⟹ it teaches index-lookup, not routing. Still
  useful, but say so honestly and stop claiming the latter.
- **a negative case regresses** ⟹ the gates need a documented cheap path.

## The held-out reference, and the cheat channels

`RandomSystems/CBCMAC.lean` has been **physically removed** from the tree. The
pristine file lives at `~/Documents/tob/research/eval-reference/CBCMAC.lean`,
verified byte-identical (sha256 `8e68e3ce…`, 1905 lines, 96187 bytes) to the
committed blob. Its build artifacts are in `build-artifacts/` beside it.

Three ways the answer can leak. Two are closed:

| channel | status |
|---|---|
| the source file | **closed** — physically moved out |
| the stale `.olean` | **closed** — `setup.sh` deletes it; otherwise `import RandomSystems.CBCMAC` loads the *compiled* reference proof and `#print` reveals it |
| **git history** | **OPEN** — `git show HEAD:RandomSystems/CBCMAC.lean` still returns the full proof |

Closing the third would mean rewriting history, which is not worth it. Instead:
run the eval in a **copy without history** (`git archive HEAD \| tar -x -C /tmp/eval-run`),
or grep the run's transcript for `git show`/`git log` against that path and
discard the run if it appears. `RandomSystems/Legacy/Applications/CBCMAC.lean`
remains in the tree; it names neither the endpoint nor the theorem, so it is a
distractor rather than a spoiler.

## Restoring the tree

```sh
git checkout RandomSystems/CBCMAC.lean      # restore the real proof
git checkout CHEATSHEET.md                  # if arm 1b was run
lake build                                  # regenerate build artifacts
```

Six modules import `CBCMAC` — `CBCStructureGraph`, `BonehShoup/Converters`,
`BonehShoup/Ch6MAC`, `RandomSystemsCC/CBC`, `RandomSystemsCC/CBCModel`, and
sequence-hash's `SequenceMACPRF` — so with the file absent they do not build.
That is expected and accepted: restoring is one command. Running
`case1-cbc-ce-routing/setup.sh` puts the fixture (full model, two proofs opened)
back in place, which those six modules *do* elaborate against.
