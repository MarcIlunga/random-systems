# Counting — discharging the probability

## Contents

- The six doors into combinatorics
- The split that matters
- Skeleton, statement-first
- Fixed schedules, and why that matters
- Normalisations that carry no new mathematics
- Getting to a headline form
- Heavier engines
- Traps

---

Every family-III proof ends here. This is the one stage where budget *should* go: it is
where the genuinely new combinatorics lives. Everything above it is routing.

The goal on entry is always of the form `probBad D Bad ≤ ε` or `D.mass P ≤ ε`.

## The six doors into combinatorics

| door | lemma | shape |
|---|---|---|
| **union bound** | `probBad_iUnion_le` (`RandomSystems/StatDist.lean:294`) | cover `∀ a, Bad a → ∃ i, P i a`, then `∑ᵢ D.evalPred (P i) ≤ ε` |
| **union bound (mass)** | `mass_biUnion_le` (`RandomSystems/SwitchingLemma.lean:55`) | the switching-lemma form of the same step |
| **ratio trick** | `probBad_le_of_ratio` (`RandomSystems/HTechnique/Derivation.lean:3499`) | ideal never hits `Bad`, densities within `(1-δ)` off it ⟹ `P.mass Bad ≤ δ` |
| **structure graphs** | `RandomSystems/CBCStructureGraph.lean` (Jha–Nandi) | CBC-MAC's `𝒪(q²ℓ/2ⁿ)`; accident extraction, single-charge leaf, cover |
| **orbit / partition counting** | `RandomSystems/SoP/`, `CompatibleCount.lean` | sum-of-permutations |
| **collision / birthday** | `RandomSystems/SwitchingLemma.lean`, `Instances.URFfunEval` | the standard tail |

**The union bound is the door.** Nearly every proof in the library ends through it.

## The split that matters

The union bound separates two very different kinds of work, and getting to the second one is
the point of everything above it:

```lean
refine le_trans (RandomSystems.probBad_iUnion_le D Bad P ?bad_event_cover) ?bad_event_leaf_sum
case bad_event_cover    => sorry   -- ∀ a, Bad a → ∃ i, P i a    — pure logic, usually short
case bad_event_leaf_sum => sorry   -- ∑ i, D.evalPred (P i) ≤ ε  — pure counting, usually long
```

Both are stage-2 DAG nodes; use exactly these names.

Get to `bad_event_leaf_sum` before doing any real thinking. Everything before it is plumbing.

**The choice of descriptor family `P` is the creative act.** It is what turns "some bad thing
happened" into "one of these `|ι|` named, individually-countable things happened". Choose
`P` so that each `D.evalPred (P i)` has a closed form — usually `1/|X|` or `1/(|X| - k)` —
and the sum is `|ι|` times that.

## Skeleton, statement-first

```lean
theorem mass_my_bad_le (…) : probBad D Bad ≤ ε := by
  refine le_trans
    (RandomSystems.probBad_iUnion_le D Bad
      (fun (p : ι) a => …)                        -- name the descriptor family
      ?bad_event_cover)
    ?bad_event_leaf_sum
  case bad_event_cover    => sorry
  case bad_event_leaf_sum => sorry
```

Compile it. A skeleton that fails here usually means `ι` is not a `Fintype` or `P i` is not
decidable — fix the descriptor, not the proof.

## Fixed schedules, and why that matters

If you arrived here from **conditional equivalence** via the packaged endpoint, the query
schedule is already **fixed** — `blindQueryList w q` is a list, not an adaptive process. The
blind reduction did that for you.

If you arrived from the **H-technique**, the obligation is universally quantified over
environments (`∀ E : QQueryEnvironment X Y q, …`), so you must bound uniformly, but the
transcript law inside is still at a fixed query vector after `htechnique_compress`.

**Either way: you are counting over a fixed schedule.** If your argument involves an
adversary choosing its next query in response to an answer, you have skipped a reduction.
Go back.

## Normalisations that carry no new mathematics

Mathematically these are free. **Mechanically they are only free when the tactic's rewrite
set matches your shape** — off it, the same normalisation is hand work (an H-technique leaf
for CBC-MAC cost ~60 lines doing query compression by hand). Budget accordingly.

| do this first | why |
|---|---|
| `htechnique_compress` / `compressedQuery_bound` | replaces an arbitrary query vector by the canonical injective vector of its **distinct** entries. Counting over a vector with repeats is a self-inflicted difficulty |
| `cr18_filter` | normalises the `⌈q⌉` filter so lengths are literal |
| `cr18_mass_expand`, `cr18_sum_swap x`, `cr18_ite_collapse` | mass/sum bookkeeping (`RandomSystems/CR18TacticsCore.lean:49,55,61`) |
| `cr18_card` | cardinality arithmetic (`:88`) |
| `cr18_arith`, `cr18_arith!`, `cr18_algebra` | the final ℝ/NNReal tail (`:68,74,98`) |

Finish with `cr18_close`, the omnibus finisher: `grind`, then arithmetic, then a
normalise-and-grind pass.

## Getting to a headline form

The last step is usually a named arithmetic lemma, not a hand computation. Grep for one
before writing one:

- `pairCollisionUnionBound_le_birthday` — `q(q-1)/2 · 1/|X| ≤ ½q²/|X|`
- the switching-lemma tail in `RandomSystems/SwitchingLemma.lean`
- `RandomSystems/Counting.lean`, `RandomSystems/CompatibleCount.lean`

## Heavier engines, and when to reach for them

**Structure graphs** (`RandomSystems/CBCStructureGraph.lean`, 1400+ lines). The Jha–Nandi
route for CBC-family MACs. Contains a proven tolerant-CE bridge and a full counting engine:
single-charge leaf, `1/N²` double slice, accident extraction, cover. Reach for it when a
plain pair-collision union bound is too lossy — it is what gets `𝒪(q²ℓ/2ⁿ)` rather than
`(qL)²/2ⁿ`. Expensive; do not start here.

**Sum-of-permutations** (`RandomSystems/SoP/`, `HTechnique/SoP/`). Orbit and partition
counting for XoP-style constructions. `RandomSystems/SoP/SoP.md`, `SoP1.md`, `SoP2.md` carry
the written-out mathematics — read those before the Lean.

**ANOVA / Mayer expansion** (`Legacy/Applications/XoP*.lean`). The analytic route. Rarely
the right first move.

## Traps

**Do not re-prove a union bound.** `probBad_iUnion_le` and `mass_biUnion_le` are `[LIB]`.
If you are manipulating `Finset.sum` over a filtered support to establish a union bound,
stop.

**Do not count over a query vector with repeats.** Compress first.

**Bound uniformly when the obligation says `∀ E`.** A bound that depends on the environment
does not discharge a universally quantified goal, and the mismatch may not surface until the
outer `calc` fails.

**A slack cover costs you the bound, not the proof.** If `∑ᵢ D.evalPred (P i)` comes out too
big, the descriptor family is too coarse — refine `P`, do not look for a cleverer sum bound.

**Check for an existing arithmetic lemma before doing casts by hand.** `NNReal` → `ℝ`
casting in this tree has established idioms; `cr18_arith!` and `cr18_algebra` know them.
