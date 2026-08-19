# Proof DAG — `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight`

Generated 2026-07-31 by a Lean environment walk (`Expr.getUsedConstants` over each
declaration's **value and type**), recursing through repo declarations and stopping at the
`Mathlib` / `Init` / `Std` / `Lean` / `Batteries` / `Aesop` boundary. Read-only: no proof file was
touched. Raw adjacency is in `review/sop-dag.tsv` (`NODE` / `VDEP` / `TDEP` rows).

## 0. Coverage statement — read this first

* The walk is **complete** down to the Mathlib boundary: every repo constant reachable from
  the root is listed. Nothing was sampled.
* The walk **stops at Mathlib**. The 1348 Mathlib/core constants below are the *frontier*, not
  the Mathlib closure (~200k). They are tagged MATHLIB and treated as trusted; §6 flags the
  ones used in a load-bearing or unusual way.
* Tags were assigned from module provenance + `git log` + working-tree status, not from
  guesswork; the evidence is in §2.
* I have **read in full**: `RandomSystems/SumOfPermutationsTight.lean` (840 lines) and
  `RandomSystems/PermFreshCounting.lean` (385 lines) — i.e. both NEW files — plus the
  endpoint region of `RandomSystems/SwitchingLemma.lean` (1857–1935) and the complete
  uncommitted diff of that file. I read **statements only** (via the elaborated types) for
  the 44 LIB frontier nodes in §4.3, and **nothing at all** of the 386 LIB interior nodes
  in §4.4 — the `blind-game-endpoint` slice exists precisely so a reviewer does.
* Slice notes in §5 are review *prompts* derived from reading the two NEW files. They are
  hypotheses about where a defect could hide, not findings. I found no defect and did not
  look for one; that is the next stage.
* Axiom check re-run here: `sop_randomness_expander_tight`, `sopTight_condEquiv`,
  `mass_sopTightBad_le`, `card_fresh_pair_refine` each depend on exactly
  `[propext, Classical.choice, Quot.sound]`. Confirmed, and it proves nothing about meaning.

## 1. Numbers

| | count |
|---|---|
| distinct nodes in the DAG (repo + Mathlib frontier) | **1848** |
| repo nodes (walked through) | 500 |
| — NEW | 70 (44 hand-written + 26 elaborator-generated) |
| — LIB | 430 |
| Mathlib/core frontier constants (trusted, not walked) | 1348 |
| fully-duplicated tree nodes (NEW expanded, LIB as leaves) | 796 |

Repo nodes by module:

| module | nodes | tag |
|---|---|---|
| `RandomSystems.GameOf` | 70 | LIB |
| `RandomSystems.SumOfPermutationsTight` | 54 | NEW |
| `RandomSystems.Lemma415` | 53 | LIB |
| `RandomSystems.PFunDDS` | 45 | LIB |
| `RandomSystems.BlindAbsorption` | 38 | LIB |
| `RandomSystems.Dist` | 37 | LIB |
| `RandomSystems.SwitchingLemma` | 36 | LIB (1 NEW decl, see §2) |
| `RandomSystems.Theorem417` | 36 | LIB |
| `RandomSystems.CondEquiv` | 30 | LIB |
| `RandomSystems.PDS` | 25 | LIB |
| `RandomSystems.RelateGameDistinguishing` | 25 | LIB |
| `RandomSystems.PermFreshCounting` | 15 | NEW |
| `RandomSystems.Counting` | 14 | LIB |
| `RandomSystems.BlindConverter` | 6 | LIB |
| `RandomSystems.Distinguishing` | 4 | LIB |
| `RandomSystems.WinProb` | 4 | LIB |
| `RandomSystems.MaxWinProb` | 3 | LIB |
| `RandomSystems.SystemMBO` | 3 | LIB |
| `RandomSystems.PFunConverter` | 2 | LIB |

## 2. Tagging — provenance evidence

**NEW** = written for this proof (untracked, or added in the uncommitted working tree).

| file | evidence | verdict |
|---|---|---|
| `RandomSystems/SumOfPermutationsTight.lean` | untracked (`git ls-files` empty), mtime 2026-07-31 09:38 | NEW — 54 nodes |
| `RandomSystems/PermFreshCounting.lean` | untracked, mtime 2026-07-31 09:11 | NEW — 15 nodes |
| `RandomSystems/SwitchingLemma.lean` | tracked (HEAD 2026-07-25) but ` M` dirty; `git diff` adds 4 decls, of which **`seededConditionCGame_ignoreMBO`** is in this DAG | LIB file, **1 NEW node** |
| `RandomSystems/Counting.lean` | tracked, clean, HEAD 2026-07-25 | LIB — 14 nodes |
| `RandomSystems/Dist.lean` | tracked, clean, HEAD 2026-07-27 | LIB — 37 nodes |
| `RandomSystems/PDS.lean`, `PFunDDS.lean` | tracked, clean, HEAD 2026-07-27 | LIB |
| `GameOf`, `Lemma415`, `Theorem417`, `BlindAbsorption`, `CondEquiv`, `RelateGameDistinguishing`, `BlindConverter`, `Distinguishing`, `WinProb`, `MaxWinProb` | tracked, clean, HEAD 2026-07-25 | LIB |
| `SystemMBO.lean` (2026-07-02), `PFunConverter.lean` (2026-07-04) | tracked, clean | LIB |

Two provenance traps worth naming up front:

1. **The namespace `RandomSystems.CR18.Counting` spans two files.**
   `canonSubset`, `availPairs`, `card_fresh_pair_fiber`, `card_fresh_pair_refine`,
   `card_permPair_restrict`, `restrict_perm_injective`, `mem_availPairs`, `canonSubset_*` are
   **NEW** (`PermFreshCounting.lean`); `chain_product_lower_bound`, `three_sum_sq_le_cube`,
   `card_function_fiber_finset`, `card_perm_fiber_finset` are **LIB** (`Counting.lean`).
   A name-based tagger would get all eight wrong.
2. **`SwitchingLemma.lean` is dirty.** The packaged endpoint
   `maxAdvantage_filterQueries_seededConditionCGame_le` itself is *unchanged* by the diff
   (verified line-by-line), but `seededConditionCGame_ignoreMBO`, which
   `sopTightGame_ignoreMBO` calls, was **added in the working tree** and has never been
   committed or reviewed. It is tagged NEW.

## 3. The tree

Shared nodes are **duplicated**, not shared: every arrow is a distinct *use* and is printed
with its own subtree, in its own context.

* `[N file:line]` NEW, `[L file:line ↳n §slice]` LIB — `↳n` is the size of that LIB node's own
  repo sub-DAG, and `§slice` names the slice that owns it. LIB nodes are leaves here.
* MATHLIB deps are not drawn (1348 of them); see §4.5 and §6.
* Names are shown with `RandomSystems.CR18.SoPTight.` / `RandomSystems.` prefixes stripped;
  §4 has them in full.
* `(2nd use, same node)` = the *same* declaration appears twice in one parent's dependency
  list (e.g. once in the value, once in the type). The arrow is shown; the subtree is not
  repeated within a single parent.

### 3.1 NEW region — expanded in full, LIB and MATHLIB as annotated leaves

```
sop_randomness_expander_tight  [N SumOfPermutationsTight:769]
├─ maxAdvantage  [L Distinguishing:136 ↳28 §sop-statement-and-semantics]
├─ PFunPDS.filterQueries  [L PDS:120 ↳17 §sop-statement-and-semantics]
├─ sopReal  [N SumOfPermutationsTight:82]
│  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
├─ sopIdeal  [N SumOfPermutationsTight:88]
│  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
├─ sopEps  [N SumOfPermutationsTight:600]
├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10 §sop-statement-and-semantics]
├─ sopTightGame  [N SumOfPermutationsTight:504]
│  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
├─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
├─ sopTightGame_ignoreMBO  [N SumOfPermutationsTight:508]
│  ├─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10 §sop-statement-and-semantics]
│  ├─ sopTightGame  [N SumOfPermutationsTight:504]
│  │  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  ├─ sopReal  [N SumOfPermutationsTight:82]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ sopTightGame.eq_1  [N SumOfPermutationsTight:?]
│  │  ├─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  │  ├─ sopTightGame  [N SumOfPermutationsTight:504]
│  │  │  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  │  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  │  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  │  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  │  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  └─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │     └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │        └─ sopFresh  [N SumOfPermutationsTight:142]
│  │           └─ freshKeep  [N SumOfPermutationsTight:128]
│  │              ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │              └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ PFunPDS.ofFunDist  [L PDS:144 ↳9 §sop-statement-and-semantics]
│  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  ├─ seededConditionCGame_ignoreMBO  [N SwitchingLemma:1864]
│  │  ├─ Dist  [L Dist:50 §sop-statement-and-semantics]
│  │  ├─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  │  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10 §sop-statement-and-semantics]
│  │  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  │  ├─ PFunPDS.ofFunDist  [L PDS:144 ↳9 §sop-statement-and-semantics]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  ├─ PFunPDS.stripMBO  [L SystemMBO:45 ↳9 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.stripMBO  [L SystemMBO:29 ↳5 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │  └─ Dist.fTransform_comp  [L Dist:1572 ↳3 §sop-statement-and-semantics]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  ├─ PFunPDS.ofFunDist.eq_1  [L PDS:? ↳10 §sop-statement-and-semantics]
│  ├─ Dist  [L Dist:50 §sop-statement-and-semantics]
│  └─ Dist.fTransform_comp  [L Dist:1572 ↳3 §sop-statement-and-semantics]
├─ maxAdvantage_filterQueries_seededConditionCGame_le  [L SwitchingLemma:1881 ↳375 §blind-game-endpoint]
├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
├─ sopFunction  [N SumOfPermutationsTight:77]
├─ sopTightBad  [N SumOfPermutationsTight:218]
│  └─ sopFresh  [N SumOfPermutationsTight:142]
│     └─ freshKeep  [N SumOfPermutationsTight:128]
│        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│        └─ freshFiber  [N SumOfPermutationsTight:99]
├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  └─ sopTightBad  [N SumOfPermutationsTight:218]
│     └─ sopFresh  [N SumOfPermutationsTight:142]
│        └─ freshKeep  [N SumOfPermutationsTight:128]
│           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│           └─ freshFiber  [N SumOfPermutationsTight:99]
├─ sopTightBad_monotone  [N SumOfPermutationsTight:226]
│  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  └─ sopFresh  [N SumOfPermutationsTight:142]
│     └─ freshKeep  [N SumOfPermutationsTight:128]
│        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│        └─ freshFiber  [N SumOfPermutationsTight:99]
├─ sopTight_condEquiv  [N SumOfPermutationsTight:572]
│  ├─ condEquiv_of_transcript_mass_reductions  [L SwitchingLemma:576 ↳31 §condequiv-instantiation]
│  ├─ sopTightGame  [N SumOfPermutationsTight:504]
│  │  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  ├─ sopIdeal  [N SumOfPermutationsTight:88]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ CondEquiv.massAfalse  [L CondEquiv:73 ↳9 §condequiv-instantiation]
│  ├─ Dist.mass  [L Dist:150 ↳2 §sop-statement-and-semantics]
│  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9 §sop-statement-and-semantics]
│  ├─ sopReal._proof_1  [N SumOfPermutationsTight:?]
│  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5 §sop-statement-and-semantics]
│  ├─ CondEquiv.massAfalse_fTransform_historyEvaluator  [L CondEquiv:256 ↳18 §condequiv-instantiation]
│  ├─ Dist.mass_congr  [L Dist:196 ↳3 §condequiv-instantiation]
│  ├─ massY_fTransform_lastQuery  [L SwitchingLemma:457 ↳25 §condequiv-instantiation]
│  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  ├─ CondEquiv.massYAfalse  [L CondEquiv:61 ↳9 §condequiv-instantiation]
│  ├─ massYAfalse_fTransform_lastQuery  [L SwitchingLemma:473 ↳23 §condequiv-instantiation]
│  ├─ sopTightBad_monotone  [N SumOfPermutationsTight:226]
│  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ mass_agree_and_good  [N SumOfPermutationsTight:520]
│  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  ├─ Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq  [L Dist:1317 ↳8 §mass-layer-and-epsilon]
│  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  ├─ goodCount  [N SumOfPermutationsTight:275]
│  │  ├─ card_goodAgree  [N SumOfPermutationsTight:291]
│  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ goodCount  [N SumOfPermutationsTight:275]
│  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopTightBad_concat  [N SumOfPermutationsTight:234]
│  │  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  └─ sopTightBad_monotone  [N SumOfPermutationsTight:226]
│  │  │  │     ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ Counting.card_fresh_pair_refine  [N PermFreshCounting:295]
│  │  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │  ├─ Counting.card_fresh_pair_refine._simp_1_1  [N PermFreshCounting:?]
│  │  │  │  ├─ Counting.card_fresh_pair_refine._simp_1_2  [N PermFreshCounting:?]
│  │  │  │  └─ Counting.card_fresh_pair_fiber  [N PermFreshCounting:104]
│  │  │  │     ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     ├─ Counting.card_permPair_restrict  [N PermFreshCounting:70]
│  │  │  │     │  └─ Counting.card_perm_fiber_finset  [L Counting:623 ↳7 §perm-fresh-refinement]
│  │  │  │     ├─ Counting.restrict_perm_injective  [N PermFreshCounting:64]
│  │  │  │     ├─ Counting.card_fresh_pair_fiber._simp_1_1  [N PermFreshCounting:?]
│  │  │  │     ├─ Counting.card_fresh_pair_fiber._simp_1_2  [N PermFreshCounting:?]
│  │  │  │     ├─ Counting.mem_availPairs  [N PermFreshCounting:96]
│  │  │  │     │  └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     ├─ Counting.card_fresh_pair_fiber._proof_1_3  [N PermFreshCounting:?]
│  │  │  │     │  └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     └─ Counting.card_fresh_pair_fiber._proof_1_4  [N PermFreshCounting:?]
│  │  │  │        └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  ├─ sopTightBad_congr  [N SumOfPermutationsTight:251]
│  │  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopFunction.eq_1  [N SumOfPermutationsTight:?]
│  │  │  │  └─ sopFunction  [N SumOfPermutationsTight:77]
│  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  ├─ card_avail_fresh_answer  [N SumOfPermutationsTight:156]
│  │  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │  ├─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │  ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │  └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ card_avail_fresh_answer._simp_1_1  [N SumOfPermutationsTight:?]
│  │  │  │  ├─ card_avail_fresh_answer._simp_1_3  [N SumOfPermutationsTight:?]
│  │  │  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │  │  └─ Counting.mem_availPairs  [N PermFreshCounting:96]
│  │  │  │  │     └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │  ├─ card_avail_fresh_answer._simp_1_2  [N SumOfPermutationsTight:?]
│  │  │  │  ├─ sopFresh.eq_1  [N SumOfPermutationsTight:?]
│  │  │  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ freshKeep_subset  [N SumOfPermutationsTight:132]
│  │  │  │  │  ├─ Counting.canonSubset_subset  [N PermFreshCounting:45]
│  │  │  │  │  │  └─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ mem_freshFiber  [N SumOfPermutationsTight:103]
│  │  │  │  │  └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  └─ card_freshKeep  [N SumOfPermutationsTight:136]
│  │  │  │     ├─ Counting.canonSubset_card  [N PermFreshCounting:52]
│  │  │  │     │  └─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ card_freshKeep._proof_1_1  [N SumOfPermutationsTight:?]
│  │  │  │     ├─ card_freshFiber_ge  [N SumOfPermutationsTight:110]
│  │  │  │     │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     │  └─ card_freshFiber_ge._proof_1_1  [N SumOfPermutationsTight:?]
│  │  │  │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ card_goodAgree._proof_1_4  [N SumOfPermutationsTight:?]
│  │  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ sopFunction  [N SumOfPermutationsTight:77]
│  │  │  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  └─ goodCount  [N SumOfPermutationsTight:275]
│  │  │  └─ goodCount_step  [N SumOfPermutationsTight:279]
│  │  │     ├─ goodCount  [N SumOfPermutationsTight:275]
│  │  │     ├─ goodCount_step._proof_1_1  [N SumOfPermutationsTight:?]
│  │  │     ├─ goodCount_step._proof_1_2  [N SumOfPermutationsTight:?]
│  │  │     └─ goodCount.eq_1  [N SumOfPermutationsTight:?]
│  │  │        └─ goodCount  [N SumOfPermutationsTight:275]
│  │  ├─ card_good  [N SumOfPermutationsTight:391]
│  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ goodCount  [N SumOfPermutationsTight:275]
│  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopTightBad_concat  [N SumOfPermutationsTight:234]
│  │  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  └─ sopTightBad_monotone  [N SumOfPermutationsTight:226]
│  │  │  │     ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ Counting.card_fresh_pair_refine  [N PermFreshCounting:295]
│  │  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │  ├─ Counting.card_fresh_pair_refine._simp_1_1  [N PermFreshCounting:?]
│  │  │  │  ├─ Counting.card_fresh_pair_refine._simp_1_2  [N PermFreshCounting:?]
│  │  │  │  └─ Counting.card_fresh_pair_fiber  [N PermFreshCounting:104]
│  │  │  │     ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     ├─ Counting.card_permPair_restrict  [N PermFreshCounting:70]
│  │  │  │     │  └─ Counting.card_perm_fiber_finset  [L Counting:623 ↳7 §perm-fresh-refinement]
│  │  │  │     ├─ Counting.restrict_perm_injective  [N PermFreshCounting:64]
│  │  │  │     ├─ Counting.card_fresh_pair_fiber._simp_1_1  [N PermFreshCounting:?]
│  │  │  │     ├─ Counting.card_fresh_pair_fiber._simp_1_2  [N PermFreshCounting:?]
│  │  │  │     ├─ Counting.mem_availPairs  [N PermFreshCounting:96]
│  │  │  │     │  └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     ├─ Counting.card_fresh_pair_fiber._proof_1_3  [N PermFreshCounting:?]
│  │  │  │     │  └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     └─ Counting.card_fresh_pair_fiber._proof_1_4  [N PermFreshCounting:?]
│  │  │  │        └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  ├─ sopTightBad_congr  [N SumOfPermutationsTight:251]
│  │  │  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  ├─ card_avail_fresh  [N SumOfPermutationsTight:190]
│  │  │  │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │  │  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │  └─ card_avail_fresh_answer  [N SumOfPermutationsTight:156]
│  │  │  │     ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │  │  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     ├─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │  ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │  └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ card_avail_fresh_answer._simp_1_1  [N SumOfPermutationsTight:?]
│  │  │  │     ├─ card_avail_fresh_answer._simp_1_3  [N SumOfPermutationsTight:?]
│  │  │  │     │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     │  └─ Counting.mem_availPairs  [N PermFreshCounting:96]
│  │  │  │     │     └─ Counting.availPairs  [N PermFreshCounting:93]
│  │  │  │     ├─ card_avail_fresh_answer._simp_1_2  [N SumOfPermutationsTight:?]
│  │  │  │     ├─ sopFresh.eq_1  [N SumOfPermutationsTight:?]
│  │  │  │     │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │  │     │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ freshKeep_subset  [N SumOfPermutationsTight:132]
│  │  │  │     │  ├─ Counting.canonSubset_subset  [N PermFreshCounting:45]
│  │  │  │     │  │  └─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     ├─ mem_freshFiber  [N SumOfPermutationsTight:103]
│  │  │  │     │  └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │     └─ card_freshKeep  [N SumOfPermutationsTight:136]
│  │  │  │        ├─ Counting.canonSubset_card  [N PermFreshCounting:52]
│  │  │  │        │  └─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │        ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │        ├─ card_freshKeep._proof_1_1  [N SumOfPermutationsTight:?]
│  │  │  │        ├─ card_freshFiber_ge  [N SumOfPermutationsTight:110]
│  │  │  │        │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │        │  └─ card_freshFiber_ge._proof_1_1  [N SumOfPermutationsTight:?]
│  │  │  │        │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │  ├─ goodCount_step  [N SumOfPermutationsTight:279]
│  │  │  │  ├─ goodCount  [N SumOfPermutationsTight:275]
│  │  │  │  ├─ goodCount_step._proof_1_1  [N SumOfPermutationsTight:?]
│  │  │  │  ├─ goodCount_step._proof_1_2  [N SumOfPermutationsTight:?]
│  │  │  │  └─ goodCount.eq_1  [N SumOfPermutationsTight:?]
│  │  │  │     └─ goodCount  [N SumOfPermutationsTight:275]
│  │  │  └─ card_good._proof_1_3  [N SumOfPermutationsTight:?]
│  │  │     ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │     ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │     │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │     │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │     │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │     │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  │     └─ goodCount  [N SumOfPermutationsTight:275]
│  │  ├─ Counting.card_function_fiber_finset  [L Counting:345 ↳4 §mass-layer-and-epsilon]
│  │  ├─ Dist.mass  [L Dist:150 ↳2 §sop-statement-and-semantics]
│  │  └─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopIdeal_isProbDist  [N SumOfPermutationsTight:492]
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │  ├─ sopIdeal  [N SumOfPermutationsTight:88]
│  │  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │  │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  │  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  │  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  │  ├─ sopIdeal_isProbDist._simp_1_1  [N SumOfPermutationsTight:?]
│  │  │  ├─ Dist  [L Dist:50 §sop-statement-and-semantics]
│  │  │  ├─ Dist.isProbDist  [L Dist:111 ↳3 §sop-statement-and-semantics]
│  │  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  │  └─ Dist.isProbDist_fTransform  [L Dist:598 ↳6 §sop-statement-and-semantics]
│  │  └─ sopIdeal_isProbDist._simp_1_7  [N SumOfPermutationsTight:?]
│  │     ├─ Dist.isProbDist  [L Dist:111 ↳3 §sop-statement-and-semantics]
│  │     ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │     └─ Dist.uniform_isProbDist  [L Dist:485 ↳8 §sop-statement-and-semantics]
│  ├─ sopIdeal_totalOnNonempty  [N SumOfPermutationsTight:497]
│  │  ├─ PFunPDS.ofFunDist_totalOnNonempty  [L GameOf:949 ↳14 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7 §condequiv-instantiation]
│  │  └─ sopIdeal  [N SumOfPermutationsTight:88]
│  │     ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │     ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │     ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │     ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  │     └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  └─ CondEquiv.CondEquiv  [L CondEquiv:118 ↳15 §condequiv-instantiation]
├─ Dist.uniform_isProbDist  [L Dist:485 ↳8 §sop-statement-and-semantics]
├─ sopIdeal_isProbDist  [N SumOfPermutationsTight:492]
│  ├─ Dist.isProbDist  [L Dist:111 ↳3 §sop-statement-and-semantics]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  ├─ sopIdeal  [N SumOfPermutationsTight:88]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│  │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  │  └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
│  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│  ├─ sopIdeal_isProbDist._simp_1_1  [N SumOfPermutationsTight:?]
│  │  ├─ Dist  [L Dist:50 §sop-statement-and-semantics]
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3 §sop-statement-and-semantics]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│  │  └─ Dist.isProbDist_fTransform  [L Dist:598 ↳6 §sop-statement-and-semantics]
│  └─ sopIdeal_isProbDist._simp_1_7  [N SumOfPermutationsTight:?]
│     ├─ Dist.isProbDist  [L Dist:111 ↳3 §sop-statement-and-semantics]
│     ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│     └─ Dist.uniform_isProbDist  [L Dist:485 ↳8 §sop-statement-and-semantics]
├─ sopIdeal_totalOnNonempty  [N SumOfPermutationsTight:497]
│  ├─ PFunPDS.ofFunDist_totalOnNonempty  [L GameOf:949 ↳14 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7 §condequiv-instantiation]
│  └─ sopIdeal  [N SumOfPermutationsTight:88]
│     ├─ Dist.fTransform  [L Dist:523 ↳2 §sop-statement-and-semantics]
│     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3 §sop-statement-and-semantics]
│     ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5 §sop-statement-and-semantics]
│     ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│     ├─ sopIdeal._proof_1  [N SumOfPermutationsTight:?]
│     └─ PFunPDS  [L PDS:68 ↳5 §sop-statement-and-semantics]
├─ PFunDDS.Winner  [L PDS:3070 ↳2 §sop-statement-and-semantics]
├─ IsBlind  [L BlindConverter:51 ↳3 §sop-statement-and-semantics]
├─ Dist.mass  [L Dist:150 ↳2 §sop-statement-and-semantics]
├─ blindQueryList  [L SwitchingLemma:811 ↳4 §blind-game-endpoint]
├─ sopEps_nonneg  [N SumOfPermutationsTight:603]
│  └─ sopEps  [N SumOfPermutationsTight:600]
├─ mass_sopTightBad_le  [N SumOfPermutationsTight:699]
│  ├─ Dist.mass  [L Dist:150 ↳2 §sop-statement-and-semantics]
│  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  ├─ Dist.mass_le_one  [L Dist:312 ↳7 §mass-layer-and-epsilon]
│  ├─ Dist.uniform_isProbDist  [L Dist:485 ↳8 §sop-statement-and-semantics]
│  ├─ sopEps_ge_one_of_large  [N SumOfPermutationsTight:680]
│  ├─ mass_sopTightBad_le._proof_1_2  [N SumOfPermutationsTight:?]
│  ├─ Dist.weight  [L Dist:71 ↳2 §sop-statement-and-semantics]
│  ├─ Dist.mass_add_compl  [L Dist:205 ↳4 §mass-layer-and-epsilon]
│  ├─ mass_good_eq_prod  [N SumOfPermutationsTight:610]
│  │  ├─ goodCount  [N SumOfPermutationsTight:275]
│  │  ├─ goodCount.eq_1  [N SumOfPermutationsTight:?]
│  │  │  └─ goodCount  [N SumOfPermutationsTight:275]
│  │  ├─ Dist.mass  [L Dist:150 ↳2 §sop-statement-and-semantics]
│  │  ├─ Dist.uniform  [L Dist:431 ↳2 §sop-statement-and-semantics]
│  │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │  │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │  │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │  │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │  │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │  │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │  ├─ Dist.uniform_mass_eq_card_filter  [L Dist:1306 ↳7 §mass-layer-and-epsilon]
│  │  └─ card_good  [N SumOfPermutationsTight:391]
│  │     ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │     │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ goodCount  [N SumOfPermutationsTight:275]
│  │     ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ sopTightBad_concat  [N SumOfPermutationsTight:234]
│  │     │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │  └─ sopTightBad_monotone  [N SumOfPermutationsTight:226]
│  │     │     ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ Counting.card_fresh_pair_refine  [N PermFreshCounting:295]
│  │     │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │  ├─ Counting.card_fresh_pair_refine._simp_1_1  [N PermFreshCounting:?]
│  │     │  ├─ Counting.card_fresh_pair_refine._simp_1_2  [N PermFreshCounting:?]
│  │     │  └─ Counting.card_fresh_pair_fiber  [N PermFreshCounting:104]
│  │     │     ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │     ├─ Counting.card_permPair_restrict  [N PermFreshCounting:70]
│  │     │     │  └─ Counting.card_perm_fiber_finset  [L Counting:623 ↳7 §perm-fresh-refinement]
│  │     │     ├─ Counting.restrict_perm_injective  [N PermFreshCounting:64]
│  │     │     ├─ Counting.card_fresh_pair_fiber._simp_1_1  [N PermFreshCounting:?]
│  │     │     ├─ Counting.card_fresh_pair_fiber._simp_1_2  [N PermFreshCounting:?]
│  │     │     ├─ Counting.mem_availPairs  [N PermFreshCounting:96]
│  │     │     │  └─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │     ├─ Counting.card_fresh_pair_fiber._proof_1_3  [N PermFreshCounting:?]
│  │     │     │  └─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │     └─ Counting.card_fresh_pair_fiber._proof_1_4  [N PermFreshCounting:?]
│  │     │        └─ Counting.availPairs  [N PermFreshCounting:93]
│  │     ├─ sopTightBad_congr  [N SumOfPermutationsTight:251]
│  │     │  ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │     │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │     ├─ card_avail_fresh  [N SumOfPermutationsTight:190]
│  │     │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │  ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │     │  │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │  │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │  │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │  │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │  └─ card_avail_fresh_answer  [N SumOfPermutationsTight:156]
│  │     │     ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     ├─ sopFresh_decidable  [N SumOfPermutationsTight:145]
│  │     │     │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │     ├─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │  ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │  └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     ├─ card_avail_fresh_answer._simp_1_1  [N SumOfPermutationsTight:?]
│  │     │     ├─ card_avail_fresh_answer._simp_1_3  [N SumOfPermutationsTight:?]
│  │     │     │  ├─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │     │  └─ Counting.mem_availPairs  [N PermFreshCounting:96]
│  │     │     │     └─ Counting.availPairs  [N PermFreshCounting:93]
│  │     │     ├─ card_avail_fresh_answer._simp_1_2  [N SumOfPermutationsTight:?]
│  │     │     ├─ sopFresh.eq_1  [N SumOfPermutationsTight:?]
│  │     │     │  ├─ sopFresh  [N SumOfPermutationsTight:142]
│  │     │     │  │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │  │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │  │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     ├─ freshKeep_subset  [N SumOfPermutationsTight:132]
│  │     │     │  ├─ Counting.canonSubset_subset  [N PermFreshCounting:45]
│  │     │     │  │  └─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     │  └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │     │     ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │     │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     ├─ mem_freshFiber  [N SumOfPermutationsTight:103]
│  │     │     │  └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │     └─ card_freshKeep  [N SumOfPermutationsTight:136]
│  │     │        ├─ Counting.canonSubset_card  [N PermFreshCounting:52]
│  │     │        │  └─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │        ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │        ├─ card_freshKeep._proof_1_1  [N SumOfPermutationsTight:?]
│  │     │        ├─ card_freshFiber_ge  [N SumOfPermutationsTight:110]
│  │     │        │  ├─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │        │  └─ card_freshFiber_ge._proof_1_1  [N SumOfPermutationsTight:?]
│  │     │        │     └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │     │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │     │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │     ├─ goodCount_step  [N SumOfPermutationsTight:279]
│  │     │  ├─ goodCount  [N SumOfPermutationsTight:275]
│  │     │  ├─ goodCount_step._proof_1_1  [N SumOfPermutationsTight:?]
│  │     │  ├─ goodCount_step._proof_1_2  [N SumOfPermutationsTight:?]
│  │     │  └─ goodCount.eq_1  [N SumOfPermutationsTight:?]
│  │     │     └─ goodCount  [N SumOfPermutationsTight:275]
│  │     └─ card_good._proof_1_3  [N SumOfPermutationsTight:?]
│  │        ├─ sopTightBad  [N SumOfPermutationsTight:218]
│  │        │  └─ sopFresh  [N SumOfPermutationsTight:142]
│  │        │     └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        │        ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        │        └─ freshFiber  [N SumOfPermutationsTight:99]
│  │        ├─ sopTightBad_decidable  [N SumOfPermutationsTight:222]
│  │        │  └─ sopTightBad  [N SumOfPermutationsTight:218]
│  │        │     └─ sopFresh  [N SumOfPermutationsTight:142]
│  │        │        └─ freshKeep  [N SumOfPermutationsTight:128]
│  │        │           ├─ Counting.canonSubset  [N PermFreshCounting:42]
│  │        │           └─ freshFiber  [N SumOfPermutationsTight:99]
│  │        └─ goodCount  [N SumOfPermutationsTight:275]
│  ├─ Counting.chain_product_lower_bound  [L Counting:43 ↳2 §mass-layer-and-epsilon]
│  └─ sopEps  [N SumOfPermutationsTight:600]
├─ blindQueryList_length_le  [L SwitchingLemma:814 ↳5 §blind-game-endpoint]
├─ sop_randomness_expander_tight._proof_1_1  [N SumOfPermutationsTight:?]
├─ sop_randomness_expander_tight._proof_1_2  [N SumOfPermutationsTight:?]
└─ Counting.three_sum_sq_le_cube  [L Counting:257 §sop-statement-and-semantics]
```

### 3.2 LIB spine — the packaged endpoint, expanded 3 deep

The 308-node `blind-game-endpoint` slice bottoms out here. Printed to depth 3; the full
membership is in §4.4 and the slice file.

```
maxAdvantage_filterQueries_seededConditionCGame_le  [L SwitchingLemma:1881 ↳375]
├─ Dist  [L Dist:50]
├─ PFunPDS  [L PDS:68 ↳5]
│  ├─ Dist  [L Dist:50]
│  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│     ├─ PFunDDS.Raw  [L PFunDDS:50]
│     └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│        └─ … 1 repo deps, sub-DAG 2 nodes
├─ CondEquiv.CondEquiv  [L CondEquiv:118 ↳15]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ CondEquiv.massAfalse  [L CondEquiv:73 ↳9]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.mass  [L Dist:150 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │  │  └─ … 3 repo deps, sub-DAG 4 nodes
│  │  └─ PFunDDS.output  [L PFunDDS:85 ↳5]
│  │     └─ … 4 repo deps, sub-DAG 5 nodes
│  ├─ CondEquiv.massDom  [L CondEquiv:88 ↳8]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.mass  [L Dist:150 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │     └─ … 3 repo deps, sub-DAG 4 nodes
│  ├─ CondEquiv.massYAfalse  [L CondEquiv:61 ↳9]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.mass  [L Dist:150 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │  │  └─ … 3 repo deps, sub-DAG 4 nodes
│  │  └─ PFunDDS.output  [L PFunDDS:85 ↳5]
│  │     └─ … 4 repo deps, sub-DAG 5 nodes
│  └─ CondEquiv.massY  [L CondEquiv:81 ↳11]
│     ├─ PFunPDS  [L PDS:68 ↳5]
│     │  └─ … 2 repo deps, sub-DAG 5 nodes
│     └─ PFunPDS.cumulativeBehavior  [L PDS:465 ↳10]
│        └─ … 6 repo deps, sub-DAG 10 nodes
├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9]
│  ├─ Dist  [L Dist:50]
│  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  └─ Dist  [L Dist:50]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.historyEvaluator._proof_1  [L PFunDDS:?]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  └─ PFunPDS  [L PDS:68 ↳5]
│     ├─ Dist  [L Dist:50]
│     └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│        └─ … 2 repo deps, sub-DAG 3 nodes
├─ Dist.isProbDist  [L Dist:111 ↳3]
│  ├─ Dist  [L Dist:50]
│  └─ Dist.weight  [L Dist:71 ↳2]
│     └─ Dist  [L Dist:50]
├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│     └─ PFunDDS.Raw  [L PFunDDS:50]
├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  └─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│     │  └─ … 2 repo deps, sub-DAG 3 nodes
│     ├─ PFunDDS.Raw  [L PFunDDS:50]
│     └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│        └─ … 1 repo deps, sub-DAG 2 nodes
├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  └─ PFunDDS.DDE  [L PFunDDS:947]
├─ IsBlind  [L BlindConverter:51 ↳3]
│  └─ PFunDDS.Winner  [L PDS:3070 ↳2]
│     └─ PFunDDS.DDE  [L PFunDDS:947]
├─ Dist.mass  [L Dist:150 ↳2]
│  └─ Dist  [L Dist:50]
├─ blindQueryList  [L SwitchingLemma:811 ↳4]
│  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │  └─ PFunDDS.DDE  [L PFunDDS:947]
│  └─ blindQueryVector  [L SwitchingLemma:795 ↳3]
│     └─ PFunDDS.Winner  [L PDS:3070 ↳2]
│        └─ … 1 repo deps, sub-DAG 2 nodes
├─ maxAdvantage  [L Distinguishing:136 ↳28]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ Dist  [L Dist:50]
│  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  └─ PFunDDS.StopFinal  [L PDS:3082]
│  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  └─ verdictProb  [L Distinguishing:107 ↳24]
│  │     └─ … 6 repo deps, sub-DAG 24 nodes
│  └─ Dist.isProbDist  [L Dist:111 ↳3]
│     ├─ Dist  [L Dist:50]
│     └─ Dist.weight  [L Dist:71 ↳2]
│        └─ … 1 repo deps, sub-DAG 2 nodes
├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  └─ Dist  [L Dist:50]
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  └─ PFunDDS.filterQueries  [L PFunDDS:360 ↳13]
│     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│     │  └─ … 2 repo deps, sub-DAG 3 nodes
│     ├─ PFunDDS.filterDom  [L PFunDDS:336 ↳11]
│     │  └─ … 6 repo deps, sub-DAG 11 nodes
│     └─ prefixClosed_length_le  [L PFunDDS:39 ↳2]
│        └─ … 1 repo deps, sub-DAG 2 nodes
├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  └─ PFunPDS.stripMBO  [L SystemMBO:45 ↳9]
│     ├─ PFunPDS  [L PDS:68 ↳5]
│     │  └─ … 2 repo deps, sub-DAG 5 nodes
│     ├─ Dist.fTransform  [L Dist:523 ↳2]
│     │  └─ … 1 repo deps, sub-DAG 2 nodes
│     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│     │  └─ … 2 repo deps, sub-DAG 3 nodes
│     └─ PFunDDS.stripMBO  [L SystemMBO:29 ↳5]
│        └─ … 4 repo deps, sub-DAG 5 nodes
├─ blindMaxWinProb  [L BlindConverter:67 ↳27]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ Dist  [L Dist:50]
│  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │  └─ PFunDDS.DDE  [L PFunDDS:947]
│  ├─ winProb  [L WinProb:38 ↳22]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ GamePerf.winProb  [L MaxWinProb:37 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ winsDDS  [L WinProb:32 ↳18]
│  │     └─ … 5 repo deps, sub-DAG 18 nodes
│  ├─ IsBlindDist  [L BlindConverter:57 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  └─ IsBlind  [L BlindConverter:51 ↳3]
│  │     └─ … 1 repo deps, sub-DAG 3 nodes
│  └─ Dist.isProbDist  [L Dist:111 ↳3]
│     ├─ Dist  [L Dist:50]
│     └─ Dist.weight  [L Dist:71 ↳2]
│        └─ … 1 repo deps, sub-DAG 2 nodes
├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv  [L GameOf:1432 ↳333]
│  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ CondEquiv.CondEquiv  [L CondEquiv:118 ↳15]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ CondEquiv.massAfalse  [L CondEquiv:73 ↳9]
│  │  │  └─ … 5 repo deps, sub-DAG 9 nodes
│  │  ├─ CondEquiv.massDom  [L CondEquiv:88 ↳8]
│  │  │  └─ … 4 repo deps, sub-DAG 8 nodes
│  │  ├─ CondEquiv.massYAfalse  [L CondEquiv:61 ↳9]
│  │  │  └─ … 5 repo deps, sub-DAG 9 nodes
│  │  └─ CondEquiv.massY  [L CondEquiv:81 ↳11]
│  │     └─ … 2 repo deps, sub-DAG 11 nodes
│  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  └─ PFunPDS.stripMBO  [L SystemMBO:45 ↳9]
│  │     └─ … 4 repo deps, sub-DAG 9 nodes
│  ├─ MonotoneMBO  [L PDS:2995 ↳15]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.DDS.IsGame  [L PDS:2954 ↳12]
│  │     └─ … 4 repo deps, sub-DAG 12 nodes
│  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ Dist.weight  [L Dist:71 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │     └─ … 3 repo deps, sub-DAG 4 nodes
│  ├─ maxAdvantage  [L Distinguishing:136 ↳28]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  │  └─ … 4 repo deps, sub-DAG 25 nodes
│  │  └─ Dist.isProbDist  [L Dist:111 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.filterQueries  [L PFunDDS:360 ↳13]
│  │     └─ … 3 repo deps, sub-DAG 13 nodes
│  ├─ blindMaxWinProb  [L BlindConverter:67 ↳27]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ winProb  [L WinProb:38 ↳22]
│  │  │  └─ … 6 repo deps, sub-DAG 22 nodes
│  │  ├─ IsBlindDist  [L BlindConverter:57 ↳5]
│  │  │  └─ … 3 repo deps, sub-DAG 5 nodes
│  │  └─ Dist.isProbDist  [L Dist:111 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact  [L GameOf:1232 ↳43]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ DeltaFilteredFiniteQueryNormalization  [L GameOf:1176 ↳41]
│  │  │  └─ … 8 repo deps, sub-DAG 41 nodes
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ QueriesExactly  [L Lemma415:249 ↳3]
│  │  │  └─ … 1 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.ddToDDE  [L PDS:3117 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  │  └─ … 4 repo deps, sub-DAG 25 nodes
│  │  ├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │  │  └─ … 4 repo deps, sub-DAG 17 nodes
│  │  └─ maxAdvantage  [L Distinguishing:136 ↳28]
│  │     └─ … 5 repo deps, sub-DAG 28 nodes
│  ├─ deltaFilteredFiniteQueryNormalization_of_totalOnNonempty  [L GameOf:1204 ↳112]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  │  │  └─ … 3 repo deps, sub-DAG 7 nodes
│  │  ├─ deltaFilteredFiniteQueryNormalization_of_padDDDDist_advantage  [L GameOf:1187 ↳54]
│  │  │  └─ … 12 repo deps, sub-DAG 54 nodes
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  │  └─ … 4 repo deps, sub-DAG 25 nodes
│  │  ├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │  │  └─ … 4 repo deps, sub-DAG 17 nodes
│  │  ├─ PFunDDS.padDDDDist  [L GameOf:889 ↳8]
│  │  │  └─ … 4 repo deps, sub-DAG 8 nodes
│  │  ├─ advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty  [L GameOf:937 ↳102]
│  │  │  └─ … 9 repo deps, sub-DAG 102 nodes
│  │  └─ DeltaFilteredFiniteQueryNormalization  [L GameOf:1176 ↳41]
│  │     └─ … 8 repo deps, sub-DAG 41 nodes
│  ├─ totalOnNonempty_ignoreMBO  [L GameOf:1403 ↳14]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  │  │  └─ … 3 repo deps, sub-DAG 7 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10]
│  │  │  └─ … 2 repo deps, sub-DAG 10 nodes
│  │  ├─ PFunDDS.stripMBO  [L SystemMBO:29 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │  │  └─ … 3 repo deps, sub-DAG 4 nodes
│  │  └─ Dist.mem_support_fTransform  [L Dist:565 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ Dist  [L Dist:50]
│  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  └─ PFunDDS.StopFinal  [L PDS:3082]
│  ├─ QueriesExactly  [L Lemma415:249 ↳3]
│  │  └─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ PFunDDS.ddToDDE  [L PDS:3117 ↳5]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.ddToDDE.match_1  [L PDS:?]
│  │  ├─ PFunDDS.StopFinal  [L PDS:3082]
│  │  └─ PFunDDS.DDE  [L PFunDDS:947]
│  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  └─ verdictProb  [L Distinguishing:107 ↳24]
│  │     └─ … 6 repo deps, sub-DAG 24 nodes
│  ├─ verdictProb  [L Distinguishing:107 ↳24]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ GamePerf.winProb  [L MaxWinProb:37 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.verdict  [L PDS:3143 ↳20]
│  │     └─ … 6 repo deps, sub-DAG 20 nodes
│  ├─ advantage.eq_1  [L Distinguishing:? ↳26]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  │  └─ … 4 repo deps, sub-DAG 25 nodes
│  │  └─ verdictProb  [L Distinguishing:107 ↳24]
│  │     └─ … 6 repo deps, sub-DAG 24 nodes
│  ├─ verdictProb_eq_of_queriesExactly_zero  [L GameOf:1274 ↳39]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ QueriesExactly  [L Lemma415:249 ↳3]
│  │  │  └─ … 1 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.ddToDDE  [L PDS:3117 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.weight  [L Dist:71 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ verdictProb  [L Distinguishing:107 ↳24]
│  │  │  └─ … 6 repo deps, sub-DAG 24 nodes
│  │  ├─ GamePerf.winProb  [L MaxWinProb:37 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.verdict  [L PDS:3143 ↳20]
│  │  │  └─ … 6 repo deps, sub-DAG 20 nodes
│  │  ├─ PFunDDS.StopFinal  [L PDS:3082]
│  │  ├─ PFunDDS.transcriptOutputs  [L PFunDDS:959]
│  │  ├─ PFunDDS.transcript  [L PFunDDS:984 ↳15]
│  │  │  └─ … 9 repo deps, sub-DAG 15 nodes
│  │  ├─ PFunDDS.verdict_iff_at_exact  [L Theorem417:501 ↳32]
│  │  │  └─ … 12 repo deps, sub-DAG 32 nodes
│  │  └─ Dist.weight_eq_finsupp_sum  [L Dist:1545 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  ├─ Dist.weight_eq_weight_of_isProbDist  [L Dist:1301 ↳4]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ Dist.weight  [L Dist:71 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._simp_1_6  [L GameOf:? ↳24]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │  │  └─ … 4 repo deps, sub-DAG 17 nodes
│  │  └─ PFunPDS.isProbDist_filterQueries_iff  [L PDS:130 ↳23]
│  │     └─ … 7 repo deps, sub-DAG 23 nodes
│  ├─ isProbDist_ignoreMBO  [L GameOf:1411 ↳16]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10]
│  │  │  └─ … 2 repo deps, sub-DAG 10 nodes
│  │  ├─ PFunPDS.stripMBO  [L SystemMBO:45 ↳9]
│  │  │  └─ … 4 repo deps, sub-DAG 9 nodes
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.stripMBO  [L SystemMBO:29 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  └─ isProbDist_ignoreMBO._simp_1_1  [L GameOf:? ↳7]
│  │     └─ … 4 repo deps, sub-DAG 7 nodes
│  ├─ PFunPDS.ignoreMBO_filterQueries  [L RelateGameDistinguishing:205 ↳25]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunPDS.ignoreMBO_filterDom  [L RelateGameDistinguishing:195 ↳21]
│  │  │  └─ … 11 repo deps, sub-DAG 21 nodes
│  │  ├─ prefixClosed_length_le  [L PFunDDS:39 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10]
│  │  │  └─ … 2 repo deps, sub-DAG 10 nodes
│  │  └─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │     └─ … 4 repo deps, sub-DAG 17 nodes
│  ├─ advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo  [L BlindAbsorption:728 ↳232]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDD  [L PDS:3091 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ CondEquiv.CondEquiv  [L CondEquiv:118 ↳15]
│  │  │  └─ … 5 repo deps, sub-DAG 15 nodes
│  │  ├─ MonotoneMBO  [L PDS:2995 ↳15]
│  │  │  └─ … 3 repo deps, sub-DAG 15 nodes
│  │  ├─ TotalUpTo  [L Lemma415:259 ↳7]
│  │  │  └─ … 3 repo deps, sub-DAG 7 nodes
│  │  ├─ QueriesExactly  [L Lemma415:249 ↳3]
│  │  │  └─ … 1 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.ddToDDE  [L PDS:3117 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  ├─ advantage  [L Distinguishing:113 ↳25]
│  │  │  └─ … 4 repo deps, sub-DAG 25 nodes
│  │  ├─ PFunPDS.ignoreMBO  [L RelateGameDistinguishing:190 ↳10]
│  │  │  └─ … 2 repo deps, sub-DAG 10 nodes
│  │  ├─ winProb  [L WinProb:38 ↳22]
│  │  │  └─ … 6 repo deps, sub-DAG 22 nodes
│  │  ├─ absorbedWinnerDist  [L BlindAbsorption:167 ↳26]
│  │  │  └─ … 8 repo deps, sub-DAG 26 nodes
│  │  ├─ blindMaxWinProb  [L BlindConverter:67 ↳27]
│  │  │  └─ … 6 repo deps, sub-DAG 27 nodes
│  │  ├─ advantage_le_absorbedWinnerProb_of_condEquiv_of_totalUpTo  [L BlindAbsorption:642 ↳223]
│  │  │  └─ … 33 repo deps, sub-DAG 223 nodes
│  │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ absorbedWinnerDist_isProbDist  [L BlindAbsorption:175 ↳36]
│  │  │  └─ … 11 repo deps, sub-DAG 36 nodes
│  │  ├─ winProb_le_blindMaxWinProb  [L BlindConverter:84 ↳31]
│  │  │  └─ … 8 repo deps, sub-DAG 31 nodes
│  │  └─ isBlindDist_absorbedWinnerDist  [L BlindAbsorption:185 ↳31]
│  │     └─ … 12 repo deps, sub-DAG 31 nodes
│  ├─ CondEquiv.condEquiv_filterQueries  [L CondEquiv:237 ↳43]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ CondEquiv.CondEquiv  [L CondEquiv:118 ↳15]
│  │  │  └─ … 5 repo deps, sub-DAG 15 nodes
│  │  ├─ CondEquiv.condEquiv_filterDom  [L CondEquiv:203 ↳39]
│  │  │  └─ … 13 repo deps, sub-DAG 39 nodes
│  │  ├─ prefixClosed_length_le  [L PFunDDS:39 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  └─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │     └─ … 4 repo deps, sub-DAG 17 nodes
│  ├─ monotoneMBO_filterQueries  [L PDS:3022 ↳29]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ MonotoneMBO  [L PDS:2995 ↳15]
│  │  │  └─ … 3 repo deps, sub-DAG 15 nodes
│  │  ├─ monotoneMBO_filterDom  [L PDS:3006 ↳25]
│  │  │  └─ … 9 repo deps, sub-DAG 25 nodes
│  │  ├─ prefixClosed_length_le  [L PFunDDS:39 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  └─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │     └─ … 4 repo deps, sub-DAG 17 nodes
│  ├─ totalUpTo_filterQueries  [L Lemma415:304 ↳22]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  │  │  └─ … 3 repo deps, sub-DAG 7 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
│  │  │  └─ … 4 repo deps, sub-DAG 17 nodes
│  │  ├─ PFunDDS.filterQueries  [L PFunDDS:360 ↳13]
│  │  │  └─ … 3 repo deps, sub-DAG 13 nodes
│  │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │  │  └─ … 3 repo deps, sub-DAG 4 nodes
│  │  ├─ mem_support_fTransform  [L Lemma415:290 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.mem_dom_filterQueries  [L PFunDDS:367 ↳14]
│  │  │  └─ … 3 repo deps, sub-DAG 14 nodes
│  │  └─ TotalUpTo  [L Lemma415:259 ↳7]
│  │     └─ … 3 repo deps, sub-DAG 7 nodes
│  ├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_1  [L GameOf:?]
│  ├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_3  [L GameOf:?]
│  ├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_5  [L GameOf:?]
│  ├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_7  [L GameOf:?]
│  ├─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_9  [L GameOf:?]
│  └─ maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_11  [L GameOf:?]
├─ seededConditionCGame_monotoneMBO  [L SwitchingLemma:1833 ↳23]
│  ├─ Dist  [L Dist:50]
│  ├─ CondEquiv.monotoneMBO_fTransform_historyEvaluator  [L CondEquiv:328 ↳21]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.DDS.IsGame  [L PDS:2954 ↳12]
│  │  │  └─ … 4 repo deps, sub-DAG 12 nodes
│  │  ├─ Dist.mem_support_fTransform  [L Dist:565 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.historyEvaluator_pair_isGame_of_monotone  [L PDS:2964 ↳15]
│  │  │  └─ … 11 repo deps, sub-DAG 15 nodes
│  │  └─ MonotoneMBO  [L PDS:2995 ↳15]
│  │     └─ … 3 repo deps, sub-DAG 15 nodes
│  ├─ MonotoneMBO  [L PDS:2995 ↳15]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.DDS.IsGame  [L PDS:2954 ↳12]
│  │     └─ … 4 repo deps, sub-DAG 12 nodes
│  └─ seededConditionCGame  [L SwitchingLemma:1824 ↳9]
│     ├─ Dist  [L Dist:50]
│     ├─ Dist.fTransform  [L Dist:523 ↳2]
│     │  └─ … 1 repo deps, sub-DAG 2 nodes
│     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│     │  └─ … 2 repo deps, sub-DAG 3 nodes
│     ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│     │  └─ … 4 repo deps, sub-DAG 5 nodes
│     └─ PFunPDS  [L PDS:68 ↳5]
│        └─ … 2 repo deps, sub-DAG 5 nodes
├─ seededConditionCGame_isProbDist  [L SwitchingLemma:1852 ↳15]
│  ├─ Dist  [L Dist:50]
│  ├─ Dist.isProbDist  [L Dist:111 ↳3]
│  │  ├─ Dist  [L Dist:50]
│  │  └─ Dist.weight  [L Dist:71 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │     └─ … 1 repo deps, sub-DAG 2 nodes
│  ├─ seededConditionCGame  [L SwitchingLemma:1824 ↳9]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  └─ PFunPDS  [L PDS:68 ↳5]
│  │     └─ … 2 repo deps, sub-DAG 5 nodes
│  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  └─ Dist  [L Dist:50]
│  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│  │  ├─ PFunDDS.Raw  [L PFunDDS:50]
│  │  ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.historyEvaluator._proof_1  [L PFunDDS:?]
│  │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │     └─ … 2 repo deps, sub-DAG 3 nodes
│  └─ seededConditionCGame_isProbDist._simp_1_1  [L SwitchingLemma:? ↳7]
│     ├─ Dist  [L Dist:50]
│     ├─ Dist.isProbDist  [L Dist:111 ↳3]
│     │  └─ … 2 repo deps, sub-DAG 3 nodes
│     ├─ Dist.fTransform  [L Dist:523 ↳2]
│     │  └─ … 1 repo deps, sub-DAG 2 nodes
│     └─ Dist.isProbDist_fTransform  [L Dist:598 ↳6]
│        └─ … 5 repo deps, sub-DAG 6 nodes
├─ seededConditionCGame_totalOnNonempty  [L SwitchingLemma:1844 ↳14]
│  ├─ Dist  [L Dist:50]
│  ├─ CondEquiv.totalOnNonempty_fTransform_historyEvaluator  [L CondEquiv:340 ↳12]
│  │  ├─ Dist  [L Dist:50]
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  ├─ Dist.fTransform  [L Dist:523 ↳2]
│  │  │  └─ … 1 repo deps, sub-DAG 2 nodes
│  │  ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│  │  │  └─ … 4 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │  │  └─ … 3 repo deps, sub-DAG 4 nodes
│  │  ├─ Dist.mem_support_fTransform  [L Dist:565 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  │     └─ … 3 repo deps, sub-DAG 7 nodes
│  ├─ CondEquiv.TotalOnNonempty  [L CondEquiv:96 ↳7]
│  │  ├─ PFunPDS  [L PDS:68 ↳5]
│  │  │  └─ … 2 repo deps, sub-DAG 5 nodes
│  │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│  │  │  └─ … 2 repo deps, sub-DAG 3 nodes
│  │  └─ PFunDDS.dom  [L PFunDDS:77 ↳4]
│  │     └─ … 3 repo deps, sub-DAG 4 nodes
│  └─ seededConditionCGame  [L SwitchingLemma:1824 ↳9]
│     ├─ Dist  [L Dist:50]
│     ├─ Dist.fTransform  [L Dist:523 ↳2]
│     │  └─ … 1 repo deps, sub-DAG 2 nodes
│     ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
│     │  └─ … 2 repo deps, sub-DAG 3 nodes
│     ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
│     │  └─ … 4 repo deps, sub-DAG 5 nodes
│     └─ PFunPDS  [L PDS:68 ↳5]
│        └─ … 2 repo deps, sub-DAG 5 nodes
└─ blindMaxWinProb_filterQueries_monitored_le  [L SwitchingLemma:1778 ↳93]
   ├─ Dist  [L Dist:50]
   ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │  └─ PFunDDS.DDE  [L PFunDDS:947]
   ├─ IsBlind  [L BlindConverter:51 ↳3]
   │  └─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │     └─ … 1 repo deps, sub-DAG 2 nodes
   ├─ Dist.mass  [L Dist:150 ↳2]
   │  └─ Dist  [L Dist:50]
   ├─ blindQueryList  [L SwitchingLemma:811 ↳4]
   │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  └─ blindQueryVector  [L SwitchingLemma:795 ↳3]
   │     └─ … 1 repo deps, sub-DAG 3 nodes
   ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  ├─ PFunDDS.Raw  [L PFunDDS:50]
   │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │     └─ … 1 repo deps, sub-DAG 2 nodes
   ├─ PFunDDS.filterQueries  [L PFunDDS:360 ↳13]
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.filterDom  [L PFunDDS:336 ↳11]
   │  │  └─ … 6 repo deps, sub-DAG 11 nodes
   │  └─ prefixClosed_length_le  [L PFunDDS:39 ↳2]
   │     └─ … 1 repo deps, sub-DAG 2 nodes
   ├─ PFunDDS.historyEvaluator  [L PFunDDS:134 ↳5]
   │  ├─ PFunDDS.Raw  [L PFunDDS:50]
   │  ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ PFunDDS.historyEvaluator._proof_1  [L PFunDDS:?]
   │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │     └─ … 2 repo deps, sub-DAG 3 nodes
   ├─ PFunDDS.gameOfDDS  [L GameOf:230 ↳13]
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.Raw  [L PFunDDS:50]
   │  ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ PFunDDS.ioTranscript  [L PFunDDS:387 ↳10]
   │  │  └─ … 4 repo deps, sub-DAG 10 nodes
   │  └─ PFunDDS.gameOfDDS._proof_1  [L GameOf:? ↳12]
   │     └─ … 6 repo deps, sub-DAG 12 nodes
   ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5]
   │  ├─ PFunDDS.Raw  [L PFunDDS:50]
   │  ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ PFunDDS.functionEvaluator._proof_1  [L PFunDDS:?]
   │  └─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │     └─ … 2 repo deps, sub-DAG 3 nodes
   ├─ PFunDDS.Raw  [L PFunDDS:50]
   ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │  └─ PFunDDS.Raw  [L PFunDDS:50]
   ├─ PFunDDS.ioTranscript  [L PFunDDS:387 ↳10]
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
   │  │  └─ … 3 repo deps, sub-DAG 4 nodes
   │  ├─ PFunDDS.output  [L PFunDDS:85 ↳5]
   │  │  └─ … 4 repo deps, sub-DAG 5 nodes
   │  └─ PFunDDS.ioTranscript._proof_2  [L PFunDDS:? ↳8]
   │     └─ … 4 repo deps, sub-DAG 8 nodes
   ├─ PFunDDS.ioTranscript_map_fst  [L PFunDDS:399 ↳11]
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
   │  │  └─ … 3 repo deps, sub-DAG 4 nodes
   │  ├─ PFunDDS.ioTranscript  [L PFunDDS:387 ↳10]
   │  │  └─ … 4 repo deps, sub-DAG 10 nodes
   │  ├─ PFunDDS.output  [L PFunDDS:85 ↳5]
   │  │  └─ … 4 repo deps, sub-DAG 5 nodes
   │  └─ PFunDDS.ioTranscript._proof_2  [L PFunDDS:? ↳8]
   │     └─ … 4 repo deps, sub-DAG 8 nodes
   ├─ blindMaxWinProb  [L BlindConverter:67 ↳27]
   │  ├─ PFunPDS  [L PDS:68 ↳5]
   │  │  └─ … 2 repo deps, sub-DAG 5 nodes
   │  ├─ Dist  [L Dist:50]
   │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ winProb  [L WinProb:38 ↳22]
   │  │  └─ … 6 repo deps, sub-DAG 22 nodes
   │  ├─ IsBlindDist  [L BlindConverter:57 ↳5]
   │  │  └─ … 3 repo deps, sub-DAG 5 nodes
   │  └─ Dist.isProbDist  [L Dist:111 ↳3]
   │     └─ … 2 repo deps, sub-DAG 3 nodes
   ├─ PFunPDS.filterQueries  [L PDS:120 ↳17]
   │  ├─ PFunPDS  [L PDS:68 ↳5]
   │  │  └─ … 2 repo deps, sub-DAG 5 nodes
   │  ├─ Dist.fTransform  [L Dist:523 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  └─ PFunDDS.filterQueries  [L PFunDDS:360 ↳13]
   │     └─ … 3 repo deps, sub-DAG 13 nodes
   ├─ Dist.fTransform  [L Dist:523 ↳2]
   │  └─ Dist  [L Dist:50]
   ├─ Dist.fTransform_comp  [L Dist:1572 ↳3]
   │  ├─ Dist  [L Dist:50]
   │  └─ Dist.fTransform  [L Dist:523 ↳2]
   │     └─ … 1 repo deps, sub-DAG 2 nodes
   ├─ blindMaxWinProb_fTransform_le  [L BlindConverter:103 ↳33]
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ Dist  [L Dist:50]
   │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ IsBlind  [L BlindConverter:51 ↳3]
   │  │  └─ … 1 repo deps, sub-DAG 3 nodes
   │  ├─ Dist.mass  [L Dist:150 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ winsDDS  [L WinProb:32 ↳18]
   │  │  └─ … 5 repo deps, sub-DAG 18 nodes
   │  ├─ blindMaxWinProb  [L BlindConverter:67 ↳27]
   │  │  └─ … 6 repo deps, sub-DAG 27 nodes
   │  ├─ Dist.fTransform  [L Dist:523 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ winProb  [L WinProb:38 ↳22]
   │  │  └─ … 6 repo deps, sub-DAG 22 nodes
   │  ├─ IsBlindDist  [L BlindConverter:57 ↳5]
   │  │  └─ … 3 repo deps, sub-DAG 5 nodes
   │  ├─ Dist.isProbDist  [L Dist:111 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ GamePerf.winProb  [L MaxWinProb:37 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ winProb_fTransform_game  [L RelateGameDistinguishing:132 ↳4]
   │  │  └─ … 3 repo deps, sub-DAG 4 nodes
   │  ├─ Dist.mass.eq_1  [L Dist:? ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ Dist.weight  [L Dist:71 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  └─ Dist.weight_eq_finsupp_sum  [L Dist:1545 ↳3]
   │     └─ … 2 repo deps, sub-DAG 3 nodes
   ├─ winsDDS  [L WinProb:32 ↳18]
   │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.transcriptOutputs  [L PFunDDS:959]
   │  ├─ PFunDDS.transcript  [L PFunDDS:984 ↳15]
   │  │  └─ … 9 repo deps, sub-DAG 15 nodes
   │  └─ PFunDDS.winnerView  [L PDS:3104 ↳3]
   │     └─ … 2 repo deps, sub-DAG 3 nodes
   ├─ mass_mono  [L RelateGameDistinguishing:222 ↳4]
   │  ├─ Dist  [L Dist:50]
   │  ├─ Dist.mass  [L Dist:150 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  └─ Dist.mass.eq_1  [L Dist:? ↳3]
   │     └─ … 2 repo deps, sub-DAG 3 nodes
   ├─ blindQueryVector  [L SwitchingLemma:795 ↳3]
   │  └─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │     └─ … 1 repo deps, sub-DAG 2 nodes
   ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.Raw  [L PFunDDS:50]
   │  └─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │     └─ … 1 repo deps, sub-DAG 2 nodes
   ├─ winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list  [L SwitchingLemma:1124 ↳70]
   │  ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ IsBlind  [L BlindConverter:51 ↳3]
   │  │  └─ … 1 repo deps, sub-DAG 3 nodes
   │  ├─ winsDDS  [L WinProb:32 ↳18]
   │  │  └─ … 5 repo deps, sub-DAG 18 nodes
   │  ├─ PFunDDS.gameOfDDS  [L GameOf:230 ↳13]
   │  │  └─ … 5 repo deps, sub-DAG 13 nodes
   │  ├─ PFunDDS.filterQueries  [L PFunDDS:360 ↳13]
   │  │  └─ … 3 repo deps, sub-DAG 13 nodes
   │  ├─ PFunDDS.functionEvaluator  [L PFunDDS:112 ↳5]
   │  │  └─ … 4 repo deps, sub-DAG 5 nodes
   │  ├─ PFunDDS.DDS  [L PFunDDS:64 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.transcriptOutputs  [L PFunDDS:959]
   │  ├─ PFunDDS.transcript  [L PFunDDS:984 ↳15]
   │  │  └─ … 9 repo deps, sub-DAG 15 nodes
   │  ├─ PFunDDS.winnerView  [L PDS:3104 ↳3]
   │  │  └─ … 2 repo deps, sub-DAG 3 nodes
   │  ├─ blindQueryVector  [L SwitchingLemma:795 ↳3]
   │  │  └─ … 1 repo deps, sub-DAG 3 nodes
   │  ├─ PFunDDS.dom  [L PFunDDS:77 ↳4]
   │  │  └─ … 3 repo deps, sub-DAG 4 nodes
   │  ├─ PFunDDS.ioTranscript  [L PFunDDS:387 ↳10]
   │  │  └─ … 4 repo deps, sub-DAG 10 nodes
   │  ├─ PFunDDS.keptPrefix  [L PFunDDS:163 ↳5]
   │  │  └─ … 2 repo deps, sub-DAG 5 nodes
   │  ├─ PFunDDS.transcriptInputs  [L PFunDDS:954]
   │  ├─ PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true  [L SwitchingLemma:1075 ↳35]
   │  │  └─ … 22 repo deps, sub-DAG 35 nodes
   │  ├─ keptPrefix_gameOfDDS_filterQueries_functionEvaluator  [L SwitchingLemma:892 ↳35]
   │  │  └─ … 6 repo deps, sub-DAG 35 nodes
   │  ├─ PFunDDS.Raw  [L PFunDDS:50]
   │  ├─ PFunDDS.Valid  [L PFunDDS:58 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_1  [L SwitchingLemma:? ↳34]
   │  │  └─ … 8 repo deps, sub-DAG 34 nodes
   │  ├─ winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_2  [L SwitchingLemma:? ↳34]
   │  │  └─ … 8 repo deps, sub-DAG 34 nodes
   │  ├─ PFunDDS.transcript_input_get?_eq_env  [L SwitchingLemma:1030 ↳23]
   │  │  └─ … 18 repo deps, sub-DAG 23 nodes
   │  ├─ transcriptInputs_length  [L Lemma415:99 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ transcriptOutputs_length  [L Lemma415:102 ↳2]
   │  │  └─ … 1 repo deps, sub-DAG 2 nodes
   │  ├─ winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_3  [L SwitchingLemma:? ↳34]
   │  │  └─ … 8 repo deps, sub-DAG 34 nodes
   │  └─ winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_4  [L SwitchingLemma:? ↳34]
   │     └─ … 8 repo deps, sub-DAG 34 nodes
   └─ isPrefix_blindQueryList  [L SwitchingLemma:822 ↳5]
      ├─ PFunDDS.Winner  [L PDS:3070 ↳2]
      │  └─ … 1 repo deps, sub-DAG 2 nodes
      ├─ blindQueryVector  [L SwitchingLemma:795 ↳3]
      │  └─ … 1 repo deps, sub-DAG 3 nodes
      └─ blindQueryList  [L SwitchingLemma:811 ↳4]
         └─ … 2 repo deps, sub-DAG 4 nodes
```

## 4. Flat table

### 4.1 NEW — hand-written (44)

| declaration | tag | file:line | statement |
|---|---|---|---|
| `RandomSystems.CR18.Counting.canonSubset` | NEW (def) | `RandomSystems/PermFreshCounting.lean:42` | {α : Type u_1} → Finset α → ℕ → Finset α |
| `RandomSystems.CR18.Counting.canonSubset_subset` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:45` | ∀ {α : Type u_1} (s : Finset α) (m : ℕ), RandomSystems.CR18.Counting.canonSubset s m ⊆ s |
| `RandomSystems.CR18.Counting.canonSubset_card` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:52` | ∀ {α : Type u_1} (s : Finset α) {m : ℕ}, m ≤ s.card → (RandomSystems.CR18.Counting.canonSubset s m).card = m |
| `RandomSystems.CR18.Counting.restrict_perm_injective` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:64` | ∀ {X : Type u_2} (Q : Finset X) (π : Equiv.Perm X), Function.Injective fun z => π ↑z |
| `RandomSystems.CR18.Counting.card_permPair_restrict` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:70` | ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] (Q : Finset X) (f g : ↥Q → X), Function.Injective f → Function.Injective g → {p / (∀ (z : ↥Q), p.1 ↑z = f z) ∧ ∀ (z : ↥Q), p.2 ↑z = g z}.c… |
| `RandomSystems.CR18.Counting.availPairs` | NEW (def) | `RandomSystems/PermFreshCounting.lean:93` | {X : Type u_2} → [Fintype X] → [DecidableEq X] → Finset X → Finset X → Finset (X × X) |
| `RandomSystems.CR18.Counting.mem_availPairs` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:96` | ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] {U V : Finset X} {uv : X × X}, uv ∈ RandomSystems.CR18.Counting.availPairs U V ↔ uv.1 ∉ U ∧ uv.2 ∉ V |
| `RandomSystems.CR18.Counting.card_fresh_pair_fiber` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:104` | ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] (Q : Finset X), ∀ x ∉ Q, Q.card < Fintype.card X → ∀ (p₀ : Equiv.Perm X × Equiv.Perm X) (R : X → X → Prop) [inst_2 : (u v : X) → Decidable… |
| `RandomSystems.CR18.Counting.card_fresh_pair_refine` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:295` | ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] (Q : Finset X), ∀ x ∉ Q, ∀ (P : Equiv.Perm X × Equiv.Perm X → Prop) [inst_2 : DecidablePred P], (∀ (p p' : Equiv.Perm X × Equiv.Perm X), (… |
| `RandomSystems.CR18.SoPTight.sopFunction` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:77` | {G : Type u} → [AddCommGroup G] → Equiv.Perm G × Equiv.Perm G → G → G |
| `RandomSystems.CR18.SoPTight.sopReal` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:82` | {G : Type u} → [Fintype G] → [DecidableEq G] → [AddCommGroup G] → RandomSystems.CR18.PFunPDS G G |
| `RandomSystems.CR18.SoPTight.sopIdeal` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:88` | {G : Type u} → [Fintype G] → [DecidableEq G] → [Nonempty G] → RandomSystems.CR18.PFunPDS G G |
| `RandomSystems.CR18.SoPTight.freshFiber` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:99` | {G : Type u} → [Fintype G] → [DecidableEq G] → [AddCommGroup G] → Finset G → Finset G → G → Finset G |
| `RandomSystems.CR18.SoPTight.mem_freshFiber` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:103` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] {U V : Finset G} {y u : G}, u ∈ RandomSystems.CR18.SoPTight.freshFiber U V y ↔ u ∉ U ∧ y - u ∉ V |
| `RandomSystems.CR18.SoPTight.card_freshFiber_ge` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:110` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G) (y : G), Fintype.card G - (U.card + V.card) ≤ (RandomSystems.CR18.SoPTight.freshFiber U V y).card |
| `RandomSystems.CR18.SoPTight.freshKeep` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:128` | {G : Type u} → [Fintype G] → [DecidableEq G] → [AddCommGroup G] → Finset G → Finset G → G → Finset G |
| `RandomSystems.CR18.SoPTight.freshKeep_subset` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:132` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G) (y : G), RandomSystems.CR18.SoPTight.freshKeep U V y ⊆ RandomSystems.CR18.SoPTight.freshFiber U V… |
| `RandomSystems.CR18.SoPTight.card_freshKeep` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:136` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G), U.card = V.card → ∀ (y : G), (RandomSystems.CR18.SoPTight.freshKeep U V y).card = Fintype.card G… |
| `RandomSystems.CR18.SoPTight.sopFresh` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:142` | {G : Type u} → [Fintype G] → [DecidableEq G] → [AddCommGroup G] → Finset G → Finset G → G → G → Prop |
| `RandomSystems.CR18.SoPTight.sopFresh_decidable` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:145` | {G : Type u} → [inst : Fintype G] → [inst_1 : DecidableEq G] → [inst_2 : AddCommGroup G] → (U V : Finset G) → (u v : G) → Decidable (RandomSystems.CR18.SoPTight.sopFresh U V u v) |
| `RandomSystems.CR18.SoPTight.card_avail_fresh_answer` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:156` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G), U.card = V.card → ∀ (c : G), {uv ∈ RandomSystems.CR18.Counting.availPairs U V / uv.1 + uv.2 = c … |
| `RandomSystems.CR18.SoPTight.card_avail_fresh` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:190` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G), U.card = V.card → {uv ∈ RandomSystems.CR18.Counting.availPairs U V / RandomSystems.CR18.SoPTight… |
| `RandomSystems.CR18.SoPTight.sopTightBad` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:218` | {G : Type u} → [Fintype G] → [DecidableEq G] → [AddCommGroup G] → Equiv.Perm G × Equiv.Perm G → List G → Prop |
| `RandomSystems.CR18.SoPTight.sopTightBad_decidable` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:222` | {G : Type u} → [inst : Fintype G] → [inst_1 : DecidableEq G] → [inst_2 : AddCommGroup G] → (p : Equiv.Perm G × Equiv.Perm G) → (l : List G) → Decidable (RandomSystems.CR18.SoPTight.sopTightBad p l) |
| `RandomSystems.CR18.SoPTight.sopTightBad_monotone` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:226` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (p : Equiv.Perm G × Equiv.Perm G) {l₁ l₂ : List G}, l₁ <+: l₂ → RandomSystems.CR18.SoPTight.sopTightBad p l₁ → Ran… |
| `RandomSystems.CR18.SoPTight.sopTightBad_concat` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:234` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (p : Equiv.Perm G × Equiv.Perm G) (l : List G) (x : G), RandomSystems.CR18.SoPTight.sopTightBad p (l ++ [x]) ↔ Ran… |
| `RandomSystems.CR18.SoPTight.sopTightBad_congr` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:251` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] {p p' : Equiv.Perm G × Equiv.Perm G} (l : List G), (∀ z ∈ l.toFinset, p.1 z = p'.1 z) → (∀ z ∈ l.toFinset, p.2 z =… |
| `RandomSystems.CR18.SoPTight.goodCount` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:275` | (G : Type u) → [Fintype G] → ℕ → ℕ |
| `RandomSystems.CR18.SoPTight.goodCount_step` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:279` | ∀ (G : Type u) [inst : Fintype G] {d : ℕ}, d < Fintype.card G → (Fintype.card G - d) * (Fintype.card G - d) * RandomSystems.CR18.SoPTight.goodCount G (d + 1) = (Fintype.card G - 2 * d) * RandomSystem… |
| `RandomSystems.CR18.SoPTight.card_goodAgree` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:291` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (l : List G) (a : G → G), {p / ¬RandomSystems.CR18.SoPTight.sopTightBad p l ∧ ∀ x ∈ l, RandomSystems.CR18.SoPTight… |
| `RandomSystems.CR18.SoPTight.card_good` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:391` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (l : List G), {p / ¬RandomSystems.CR18.SoPTight.sopTightBad p l}.card = Fintype.card G ^ l.toFinset.card * RandomS… |
| `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:492` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : Nonempty G], RandomSystems.Dist.isProbDist RandomSystems.CR18.SoPTight.sopIdeal |
| `RandomSystems.CR18.SoPTight.sopIdeal_totalOnNonempty` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:497` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : Nonempty G], RandomSystems.CR18.CondEquiv.TotalOnNonempty RandomSystems.CR18.SoPTight.sopIdeal |
| `RandomSystems.CR18.SoPTight.sopTightGame` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:504` | {G : Type u} → [Fintype G] → [DecidableEq G] → [AddCommGroup G] → RandomSystems.CR18.PFunPDS G (G × Bool) |
| `RandomSystems.CR18.SoPTight.sopTightGame_ignoreMBO` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:508` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G], RandomSystems.CR18.SoPTight.sopTightGame.ignoreMBO = RandomSystems.CR18.SoPTight.sopReal |
| `RandomSystems.CR18.SoPTight.mass_agree_and_good` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:520` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : Nonempty G] [inst_3 : AddCommGroup G] (S : Finset G) (a : ↥S → G) (l : List G), (∀ (x : G), x ∈ l ↔ x ∈ S) → ((RandomSystems.Dist.… |
| `RandomSystems.CR18.SoPTight.sopTight_condEquiv` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:572` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : Nonempty G] [inst_3 : AddCommGroup G], RandomSystems.CR18.CondEquiv.CondEquiv RandomSystems.CR18.SoPTight.sopTightGame RandomSyste… |
| `RandomSystems.CR18.SoPTight.sopEps` | NEW (def) | `RandomSystems/SumOfPermutationsTight.lean:600` | ℕ → ℕ → ℝ |
| `RandomSystems.CR18.SoPTight.sopEps_nonneg` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:603` | ∀ (N q : ℕ), 0 ≤ RandomSystems.CR18.SoPTight.sopEps N q |
| `RandomSystems.CR18.SoPTight.mass_good_eq_prod` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:610` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (l : List G), (∀ k < l.toFinset.card, 2 * k < Fintype.card G) → ↑((RandomSystems.Dist.uniform (Equiv.Perm G × Equi… |
| `RandomSystems.CR18.SoPTight.sopEps_ge_one_of_large` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:680` | ∀ {N q k : ℕ}, k < q → k < N → N ≤ 2 * k → 1 ≤ ∑ j ∈ Finset.range q, ↑j ^ 2 / (↑N - ↑j) ^ 2 |
| `RandomSystems.CR18.SoPTight.mass_sopTightBad_le` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:699` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (l : List G) (q : ℕ), l.length ≤ q → ↑((RandomSystems.Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass fun p => Ra… |
| `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:769` | ∃ ε, (∀ (H : Type u) [inst : Fintype H] [inst_1 : DecidableEq H] [inst_2 : Nonempty H] [inst_3 : AddCommGroup H] (q : ℕ), RandomSystems.CR18.maxAdvantage (RandomSystems.CR18.PFunPDS.filterQueries q R… |
| `RandomSystems.CR18.seededConditionCGame_ignoreMBO` | NEW (thm) | `RandomSystems/SwitchingLemma.lean:1864` | ∀ {A : Type u_1} {I : Type u_2} {O : Type u_3} (D : RandomSystems.Dist A) (F : A → I → O) (bad : A → List I → Prop) [inst : (a : A) → (l : List I) → Decidable (bad a l)], (RandomSystems.CR18.seededCo… |

### 4.2 NEW — elaborator-generated (26)

Equation lemmas, `_proof_`/`_simp_` splits and decidability shims produced while elaborating
the declarations above. They carry no independent content, but they *are* distinct nodes and
a `_proof_` node can hide a nontrivial side goal (e.g. an `omega` on truncated `Nat`).

| declaration | tag | file:line | statement |
|---|---|---|---|
| `RandomSystems.CR18.Counting.card_fresh_pair_fiber._proof_1_3` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:?` | ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (Q : Finset X) (x : X) (p₀ : Equiv.Perm X × Equiv.Perm X) (R : X → X → Prop) [(u v : X) → Decidabl… |
| `RandomSystems.CR18.Counting.card_fresh_pair_fiber._proof_1_4` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:?` | ∀ {X : Type u_1} [inst : Fintype X] [DecidableEq X] (Q : Finset X) (x : X) (p₀ : Equiv.Perm X × Equiv.Perm X) (R : X → X → Prop) [(u v : X) → Decidable (R u v)… |
| `RandomSystems.CR18.Counting.card_fresh_pair_fiber._simp_1_1` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:?` | ∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a) |
| `RandomSystems.CR18.Counting.card_fresh_pair_fiber._simp_1_2` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:?` | ∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True |
| `RandomSystems.CR18.Counting.card_fresh_pair_refine._simp_1_1` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:?` | ∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a) |
| `RandomSystems.CR18.Counting.card_fresh_pair_refine._simp_1_2` | NEW (thm) | `RandomSystems/PermFreshCounting.lean:?` | ∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True |
| `RandomSystems.CR18.SoPTight.card_avail_fresh_answer._simp_1_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a) |
| `RandomSystems.CR18.SoPTight.card_avail_fresh_answer._simp_1_2` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {f : α → β} {s : Finset α} {b : β}, (b ∈ Finset.image f s) = ∃ a ∈ s, f a = b |
| `RandomSystems.CR18.SoPTight.card_avail_fresh_answer._simp_1_3` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] {U V : Finset X} {uv : X × X}, (uv ∈ RandomSystems.CR18.Counting.availPairs U V) = (uv.1 ∉ U ∧ uv.… |
| `RandomSystems.CR18.SoPTight.card_freshFiber_ge._proof_1_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G) (y : G), (RandomSystems.CR18.SoPTight.freshFiber U V y)… |
| `RandomSystems.CR18.SoPTight.card_freshKeep._proof_1_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1} [inst : Fintype G] (U V : Finset G), U.card = V.card → ¬Fintype.card G - 2 * U.card = Fintype.card G - (U.card + V.card) → False |
| `RandomSystems.CR18.SoPTight.card_good._proof_1_3` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1} [inst : Fintype G] [inst_1 : DecidableEq G] [AddCommGroup G] (l : List G) (x : G), l.toFinset.card < Fintype.card G → ¬0 < Fintype.card G - l.… |
| `RandomSystems.CR18.SoPTight.card_goodAgree._proof_1_4` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1} [inst : Fintype G] [inst_1 : DecidableEq G] [AddCommGroup G] (a : G → G) (l : List G) (x : G), l.toFinset.card < Fintype.card G → ¬0 < Fintype… |
| `RandomSystems.CR18.SoPTight.goodCount.eq_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ (G : Type u) [inst : Fintype G] (d : ℕ), RandomSystems.CR18.SoPTight.goodCount G d = (Fintype.card G - d).factorial * (Fintype.card G - d).factorial * ∏ k ∈ … |
| `RandomSystems.CR18.SoPTight.goodCount_step._proof_1_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ (G : Type u_1) [inst : Fintype G] {d : ℕ}, d < Fintype.card G → ¬Fintype.card G - d = Fintype.card G - d - 1 + 1 → False |
| `RandomSystems.CR18.SoPTight.goodCount_step._proof_1_2` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ (G : Type u_1) [inst : Fintype G] {d : ℕ}, d < Fintype.card G → ∀ (j : ℕ), Fintype.card G - d = j + 1 → ¬Fintype.card G - (d + 1) = j → False |
| `RandomSystems.CR18.SoPTight.mass_sopTightBad_le._proof_1_2` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1} [inst : Fintype G] [DecidableEq G] (l : List G) (q k : ℕ), ¬2 * k < Fintype.card G → ¬Fintype.card G ≤ 2 * k → False |
| `RandomSystems.CR18.SoPTight.sopFresh.eq_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G] (U V : Finset G) (u v : G), RandomSystems.CR18.SoPTight.sopFresh U V u v =… |
| `RandomSystems.CR18.SoPTight.sopFunction.eq_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u} [inst : AddCommGroup G] (p : Equiv.Perm G × Equiv.Perm G) (x : G), RandomSystems.CR18.SoPTight.sopFunction p x = p.1 x + p.2 x |
| `RandomSystems.CR18.SoPTight.sopIdeal._proof_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1} [Nonempty G], Nonempty (G → G) |
| `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist._simp_1_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {A : Type u_5} {B : Type u_6} (f : A → B) (X : RandomSystems.Dist A), (RandomSystems.Dist.fTransform f X).isProbDist = X.isProbDist |
| `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist._simp_1_7` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {A : Type u_1} [inst : Fintype A] [inst_1 : Nonempty A], (RandomSystems.Dist.uniform A).isProbDist = True |
| `RandomSystems.CR18.SoPTight.sopReal._proof_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u_1}, Nonempty (Equiv.Perm G × Equiv.Perm G) |
| `RandomSystems.CR18.SoPTight.sopTightGame.eq_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ {G : Type u} [inst : Fintype G] [inst_1 : DecidableEq G] [inst_2 : AddCommGroup G], RandomSystems.CR18.SoPTight.sopTightGame = RandomSystems.CR18.seededCondi… |
| `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight._proof_1_1` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ (N q : ℕ), 1 < q → ¬0 < q → False |
| `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight._proof_1_2` | NEW (thm) | `RandomSystems/SumOfPermutationsTight.lean:?` | ∀ (N q : ℕ), ¬N < q ^ 2 → ¬q ^ 2 ≤ N → False |

### 4.3 LIB frontier — the 44 library nodes a NEW node calls directly

These are the load-bearing library nodes: every one of them is an interface the new proof
leans on. If any of these means something other than what its name suggests, the theorem
means something other than what it says.

| declaration | tag | file:line | statement | slice |
|---|---|---|---|---|
| `RandomSystems.CR18.IsBlind` | LIB (def) | `RandomSystems/BlindConverter.lean:51` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunDDS.Winner X Y → Prop | `sop-statement-and-semantics` |
| `RandomSystems.CR18.CondEquiv.massYAfalse` | LIB (def) | `RandomSystems/CondEquiv.lean:61` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X (Y × Bool) → (i : ℕ) → Vector Y (i + 1) → Vector X (i + 1) → NNReal | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massAfalse` | LIB (def) | `RandomSystems/CondEquiv.lean:73` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X (Y × Bool) → List X → NNReal | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.TotalOnNonempty` | LIB (def) | `RandomSystems/CondEquiv.lean:96` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X Y → Prop | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.CondEquiv` | LIB (def) | `RandomSystems/CondEquiv.lean:118` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X (Y × Bool) → RandomSystems.CR18.PFunPDS X Y → Prop | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massAfalse_fTransform_historyEvaluator` | LIB (thm) | `RandomSystems/CondEquiv.lean:256` | ∀ {X : Type u} {Y : Type v} {A : Type u_1} (D : RandomSystems.Dist A) (out : A → (l : List X) → l ≠ [] → Y) (bit : A → List X → Bool) {xs : List X}, xs ≠ [] → RandomSystems.CR18.CondEquiv.massAfalse … | `condequiv-instantiation` |
| `RandomSystems.CR18.Counting.chain_product_lower_bound` | LIB (thm) | `RandomSystems/Counting.lean:43` | ∀ {q : ℕ} (f : ℕ → ℝ), (∀ k < q, 0 ≤ f k) → (∀ k < q, f k ≤ 1) → ∏ k ∈ Finset.range q, (1 - f k) ≥ 1 - ∑ k ∈ Finset.range q, f k | `mass-layer-and-epsilon` |
| `RandomSystems.CR18.Counting.three_sum_sq_le_cube` | LIB (thm) | `RandomSystems/Counting.lean:257` | ∀ (q : ℕ), 3 * ∑ k ∈ Finset.range q, ↑k ^ 2 ≤ ↑q ^ 3 | `sop-statement-and-semantics` |
| `RandomSystems.CR18.Counting.card_function_fiber_finset` | LIB (thm) | `RandomSystems/Counting.lean:345` | ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] [inst_2 : Fintype Y] [inst_3 : DecidableEq Y] (S : Finset X) (g : ↥S → Y), {f / ∀ (x : ↥S), f ↑x = g x}.card = Fintype.card… | `mass-layer-and-epsilon` |
| `RandomSystems.CR18.Counting.card_perm_fiber_finset` | LIB (thm) | `RandomSystems/Counting.lean:623` | ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (S : Finset X) (g : ↥S ↪ X), {π / ∀ (x : ↥S), π ↑x = g x}.card = (Fintype.card X - S.card).factorial | `perm-fresh-refinement` |
| `RandomSystems.Dist` | LIB (def) | `RandomSystems/Dist.lean:50` | Type u_1 → Type (max 0 u_1) | `sop-statement-and-semantics` |
| `RandomSystems.Dist.weight` | LIB (def) | `RandomSystems/Dist.lean:71` | {A : Type u_1} → RandomSystems.Dist A → NNReal | `sop-statement-and-semantics` |
| `RandomSystems.Dist.isProbDist` | LIB (def) | `RandomSystems/Dist.lean:111` | {A : Type u_1} → RandomSystems.Dist A → Prop | `sop-statement-and-semantics` |
| `RandomSystems.Dist.mass` | LIB (def) | `RandomSystems/Dist.lean:150` | {A : Type u_1} → RandomSystems.Dist A → (A → Prop) → NNReal | `sop-statement-and-semantics` |
| `RandomSystems.Dist.mass_congr` | LIB (thm) | `RandomSystems/Dist.lean:196` | ∀ {A : Type u_5} (X : RandomSystems.Dist A) {P Q : A → Prop}, (∀ (a : A), P a ↔ Q a) → X.mass P = X.mass Q | `condequiv-instantiation` |
| `RandomSystems.Dist.mass_add_compl` | LIB (thm) | `RandomSystems/Dist.lean:205` | ∀ {A : Type u_5} (X : RandomSystems.Dist A) (P : A → Prop), (X.mass P + X.mass fun a => ¬P a) = X.weight | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.mass_le_one` | LIB (thm) | `RandomSystems/Dist.lean:312` | ∀ {A : Type u_5} {X : RandomSystems.Dist A}, X.isProbDist → ∀ (P : A → Prop), X.mass P ≤ 1 | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.uniform` | LIB (def) | `RandomSystems/Dist.lean:431` | (A : Type u_5) → [Fintype A] → [Nonempty A] → RandomSystems.Dist A | `sop-statement-and-semantics` |
| `RandomSystems.Dist.uniform_isProbDist` | LIB (thm) | `RandomSystems/Dist.lean:485` | ∀ {A : Type u_1} [inst : Fintype A] [inst_1 : Nonempty A], (RandomSystems.Dist.uniform A).isProbDist | `sop-statement-and-semantics` |
| `RandomSystems.Dist.fTransform` | LIB (def) | `RandomSystems/Dist.lean:523` | {A : Type u_1} → {B : Type u_2} → (A → B) → RandomSystems.Dist A → RandomSystems.Dist B | `sop-statement-and-semantics` |
| `RandomSystems.Dist.isProbDist_fTransform` | LIB (thm) | `RandomSystems/Dist.lean:598` | ∀ {A : Type u_5} {B : Type u_6} (f : A → B) (X : RandomSystems.Dist A), (RandomSystems.Dist.fTransform f X).isProbDist ↔ X.isProbDist | `sop-statement-and-semantics` |
| `RandomSystems.Dist.uniform_mass_eq_card_filter` | LIB (thm) | `RandomSystems/Dist.lean:1306` | ∀ {A : Type u_1} [inst : Fintype A] [inst_1 : Nonempty A] (P : A → Prop) [inst_2 : DecidablePred P], (RandomSystems.Dist.uniform A).mass P = ↑(Finset.filter P Finset.univ).card / ↑(Fintype.card A) | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq` | LIB (thm) | `RandomSystems/Dist.lean:1317` | ∀ {A : Type u_5} {B : Type u_6} [inst : Fintype A] [inst_1 : Nonempty A] [inst_2 : Fintype B] [inst_3 : Nonempty B] (P E : A → Prop) (Q : B → Prop) [inst_4 : DecidablePred P] [inst_5 : DecidablePred … | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.fTransform_comp` | LIB (thm) | `RandomSystems/Dist.lean:1572` | ∀ {A : Type u_1} {B : Type u_2} {C : Type u_4} (g : B → C) (f : A → B) (X : RandomSystems.Dist A), RandomSystems.Dist.fTransform g (RandomSystems.Dist.fTransform f X) = RandomSystems.Dist.fTransform … | `sop-statement-and-semantics` |
| `RandomSystems.CR18.maxAdvantage` | LIB (def) | `RandomSystems/Distinguishing.lean:136` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X Y → RandomSystems.CR18.PFunPDS X Y → ℝ | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS.ofFunDist_totalOnNonempty` | LIB (thm) | `RandomSystems/GameOf.lean:949` | ∀ {X : Type u} {Y : Type v} (Df : RandomSystems.Dist (X → Y)), RandomSystems.CR18.CondEquiv.TotalOnNonempty (RandomSystems.CR18.PFunPDS.ofFunDist Df) | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS` | LIB (def) | `RandomSystems/PDS.lean:68` | Type u → Type v → Type (max u v) | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS.filterQueries` | LIB (def) | `RandomSystems/PDS.lean:120` | {X : Type u} → {Y : Type v} → ℕ → RandomSystems.CR18.PFunPDS X Y → RandomSystems.CR18.PFunPDS X Y | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS.ofFunDist` | LIB (def) | `RandomSystems/PDS.lean:144` | {X : Type u} → {Y : Type v} → RandomSystems.Dist (X → Y) → RandomSystems.CR18.PFunPDS X Y | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.Winner` | LIB (def) | `RandomSystems/PDS.lean:3070` | Type u → Type v → Type (max u v) | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS.ofFunDist.eq_1` | LIB (thm) | `RandomSystems/PDS.lean:?` | ∀ {X : Type u} {Y : Type v} (Df : RandomSystems.Dist (X → Y)), RandomSystems.CR18.PFunPDS.ofFunDist Df = RandomSystems.Dist.fTransform RandomSystems.CR18.PFunDDS.functionEvaluator Df | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.DDS` | LIB (def) | `RandomSystems/PFunDDS.lean:64` | Type u → Type v → Type (max u v) | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.functionEvaluator` | LIB (def) | `RandomSystems/PFunDDS.lean:112` | {X : Type u} → {Y : Type v} → (X → Y) → RandomSystems.CR18.PFunDDS.DDS X Y | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.historyEvaluator` | LIB (def) | `RandomSystems/PFunDDS.lean:134` | {X : Type u} → {Y : Type v} → ((l : List X) → l ≠ [] → Y) → RandomSystems.CR18.PFunDDS.DDS X Y | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS.ignoreMBO` | LIB (def) | `RandomSystems/RelateGameDistinguishing.lean:190` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X (Y × Bool) → RandomSystems.CR18.PFunPDS X Y | `sop-statement-and-semantics` |
| `RandomSystems.CR18.massY_fTransform_lastQuery` | LIB (thm) | `RandomSystems/SwitchingLemma.lean:457` | ∀ {A : Type u_1} {I : Type u_2} {O : Type u_3} (D : RandomSystems.Dist A) (F : A → I → O) {i : ℕ} (ys : Vector O (i + 1)) (xs : Vector I (i + 1)), RandomSystems.CR18.CondEquiv.massY (RandomSystems.Di… | `condequiv-instantiation` |
| `RandomSystems.CR18.massYAfalse_fTransform_lastQuery` | LIB (thm) | `RandomSystems/SwitchingLemma.lean:473` | ∀ {A : Type u_1} {I : Type u_2} {O : Type u_3} (D : RandomSystems.Dist A) (F : A → I → O) (bit : A → List I → Bool), (∀ (a : A) {l₁ l₂ : List I}, l₁ <+: l₂ → bit a l₁ = true → bit a l₂ = true) → ∀ {i… | `condequiv-instantiation` |
| `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions` | LIB (thm) | `RandomSystems/SwitchingLemma.lean:576` | ∀ {In : Type u_1} {Out : Type u_2} {F : Type u_3} {A : Type u_4} [inst : DecidableEq In] (Shat : RandomSystems.CR18.PFunPDS In (Out × Bool)) (T : RandomSystems.CR18.PFunPDS In Out) (D₁ : RandomSystem… | `condequiv-instantiation` |
| `RandomSystems.CR18.blindQueryList` | LIB (def) | `RandomSystems/SwitchingLemma.lean:811` | {X : Type u_1} → {Y : Type u_2} → RandomSystems.CR18.PFunDDS.Winner X Y → ℕ → List X | `blind-game-endpoint` |
| `RandomSystems.CR18.blindQueryList_length_le` | LIB (thm) | `RandomSystems/SwitchingLemma.lean:814` | ∀ {X : Type u_1} {Y : Type u_2} (w : RandomSystems.CR18.PFunDDS.Winner X Y) (q : ℕ), (RandomSystems.CR18.blindQueryList w q).length ≤ q | `blind-game-endpoint` |
| `RandomSystems.CR18.seededConditionCGame` | LIB (def) | `RandomSystems/SwitchingLemma.lean:1824` | {A : Type u_1} → {I : Type u_2} → {O : Type u_3} → RandomSystems.Dist A → (A → I → O) → (bad : A → List I → Prop) → [(a : A) → (l : List I) → Decidable (bad a l)] → RandomSystems.CR18.PFunPDS I (O × … | `sop-statement-and-semantics` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le` | LIB (thm) | `RandomSystems/SwitchingLemma.lean:1881` | ∀ {A : Type u_1} {I : Type u_2} {O : Type u_3} [Nonempty I] (D : RandomSystems.Dist A) (F : A → I → O) (bad : A → List I → Prop) [inst : (a : A) → (l : List I) → Decidable (bad a l)], (∀ (a : A) {l₁ … | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.stripMBO` | LIB (def) | `RandomSystems/SystemMBO.lean:29` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunDDS.DDS X (Y × Bool) → RandomSystems.CR18.PFunDDS.DDS X Y | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunPDS.stripMBO` | LIB (def) | `RandomSystems/SystemMBO.lean:45` | {X : Type u} → {Y : Type v} → RandomSystems.CR18.PFunPDS X (Y × Bool) → RandomSystems.CR18.PFunPDS X Y | `sop-statement-and-semantics` |

### 4.4 LIB interior — the remaining 386 library nodes

Reached only through the frontier. Listed name / kind / location / slice; statements are in
the source and in `review/sop-dag.tsv`.

| declaration | kind | file:line | slice |
|---|---|---|---|
| `RandomSystems.CR18.PFunDDS.tagFalse` | def | `RandomSystems/BlindAbsorption.lean:65` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.mem_dom_tagFalse` | thm | `RandomSystems/BlindAbsorption.lean:73` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_tagFalse` | thm | `RandomSystems/BlindAbsorption.lean:78` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ignoreMBO_tagFalse` | thm | `RandomSystems/BlindAbsorption.lean:82` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcriptOutputs_tagFalse_false` | thm | `RandomSystems/BlindAbsorption.lean:90` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.not_winsDDS_tagFalse` | thm | `RandomSystems/BlindAbsorption.lean:115` | `blind-game-endpoint` |
| `RandomSystems.CR18.absorbedWinner` | def | `RandomSystems/BlindAbsorption.lean:130` | `blind-game-endpoint` |
| `RandomSystems.CR18.isBlind_absorbedWinner` | thm | `RandomSystems/BlindAbsorption.lean:135` | `blind-game-endpoint` |
| `RandomSystems.CR18.queriesExactly_absorbedWinner` | thm | `RandomSystems/BlindAbsorption.lean:145` | `blind-game-endpoint` |
| `RandomSystems.CR18.absorbedWinnerDist` | def | `RandomSystems/BlindAbsorption.lean:167` | `blind-game-endpoint` |
| `RandomSystems.CR18.absorbedWinnerDist_isProbDist` | thm | `RandomSystems/BlindAbsorption.lean:175` | `blind-game-endpoint` |
| `RandomSystems.CR18.isBlindDist_absorbedWinnerDist` | thm | `RandomSystems/BlindAbsorption.lean:185` | `blind-game-endpoint` |
| `RandomSystems.CR18.absorbed_run_eq` | thm | `RandomSystems/BlindAbsorption.lean:204` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerMatches_absorbedWinner_of_matches` | thm | `RandomSystems/BlindAbsorption.lean:223` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerMatches_inj_xs` | thm | `RandomSystems/BlindAbsorption.lean:242` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_gameMatches_tagFalse` | thm | `RandomSystems/BlindAbsorption.lean:261` | `blind-game-endpoint` |
| `RandomSystems.CR18.absorbed_fiber_hex` | thm | `RandomSystems/BlindAbsorption.lean:284` | `blind-game-endpoint` |
| `RandomSystems.CR18.absorbed_fiber_huniq` | thm | `RandomSystems/BlindAbsorption.lean:322` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerFactor_absorbedWinnerDist_eq` | thm | `RandomSystems/BlindAbsorption.lean:346` | `blind-game-endpoint` |
| `RandomSystems.CR18.tsum_massYAfalse_eq_massAfalse` | thm | `RandomSystems/BlindAbsorption.lean:378` | `blind-game-endpoint` |
| `RandomSystems.CR18.summable_mass_of_unique` | thm | `RandomSystems/BlindAbsorption.lean:439` | `blind-game-endpoint` |
| `RandomSystems.CR18.term_eq_rect_mass` | thm | `RandomSystems/BlindAbsorption.lean:457` | `blind-game-endpoint` |
| `RandomSystems.CR18.summable_notWonTerm` | thm | `RandomSystems/BlindAbsorption.lean:469` | `blind-game-endpoint` |
| `RandomSystems.CR18.summable_notWonTerm_inner` | thm | `RandomSystems/BlindAbsorption.lean:500` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProbBehavior_eq_tsum_tsum` | thm | `RandomSystems/BlindAbsorption.lean:523` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProbBehavior_absorption` | thm | `RandomSystems/BlindAbsorption.lean:541` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_absorption_of_totalUpTo` | thm | `RandomSystems/BlindAbsorption.lean:584` | `blind-game-endpoint` |
| `RandomSystems.CR18.advantage_le_absorbedWinnerProb_of_condEquiv_of_totalUpTo` | thm | `RandomSystems/BlindAbsorption.lean:642` | `blind-game-endpoint` |
| `RandomSystems.CR18.advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo` | thm | `RandomSystems/BlindAbsorption.lean:728` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProbBehavior.eq_1` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.tagFalse._proof_1` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcriptOutputs_tagFalse_false._simp_1_1` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcriptOutputs_tagFalse_false._simp_1_2` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerMatches_absorbedWinner_of_matches._proof_1_1` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerMatches_absorbedWinner_of_matches._proof_1_2` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massAfalse.eq_1` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.tsum_massYAfalse_eq_massAfalse._proof_1_2` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.tsum_massYAfalse_eq_massAfalse._simp_1_3` | thm | `RandomSystems/BlindAbsorption.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.IsBlindDist` | def | `RandomSystems/BlindConverter.lean:57` | `blind-game-endpoint` |
| `RandomSystems.CR18.blindMaxWinProb` | def | `RandomSystems/BlindConverter.lean:67` | `blind-game-endpoint` |
| `RandomSystems.CR18.bddAbove_blindWinProb_image` | thm | `RandomSystems/BlindConverter.lean:75` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_le_blindMaxWinProb` | thm | `RandomSystems/BlindConverter.lean:84` | `blind-game-endpoint` |
| `RandomSystems.CR18.blindMaxWinProb_fTransform_le` | thm | `RandomSystems/BlindConverter.lean:103` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massY` | def | `RandomSystems/CondEquiv.lean:81` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massDom` | def | `RandomSystems/CondEquiv.lean:88` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massDom_eq_weight_of_totalOnNonempty` | thm | `RandomSystems/CondEquiv.lean:131` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massDom_eq_one_of_totalOnNonempty` | thm | `RandomSystems/CondEquiv.lean:141` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massAfalse_filterDom` | thm | `RandomSystems/CondEquiv.lean:152` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massAfalse_filterDom_eq_zero` | thm | `RandomSystems/CondEquiv.lean:161` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massDom_filterDom` | thm | `RandomSystems/CondEquiv.lean:171` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massY_filterDom` | thm | `RandomSystems/CondEquiv.lean:179` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massYAfalse_filterDom` | thm | `RandomSystems/CondEquiv.lean:190` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.condEquiv_filterDom` | thm | `RandomSystems/CondEquiv.lean:203` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.condEquiv_filterQueries` | thm | `RandomSystems/CondEquiv.lean:237` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.take_succ_ne_nil` | thm | `RandomSystems/CondEquiv.lean:249` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massY_fTransform_historyEvaluator` | thm | `RandomSystems/CondEquiv.lean:270` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massYAfalse_fTransform_historyEvaluator` | thm | `RandomSystems/CondEquiv.lean:288` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.monotoneMBO_fTransform_historyEvaluator` | thm | `RandomSystems/CondEquiv.lean:328` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.totalOnNonempty_fTransform_historyEvaluator` | thm | `RandomSystems/CondEquiv.lean:340` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massYAfalse_filterDom.match_1_1` | def | `RandomSystems/CondEquiv.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massYAfalse_filterDom.match_1_3` | def | `RandomSystems/CondEquiv.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massY_filterDom.match_1_1` | def | `RandomSystems/CondEquiv.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massY_filterDom.match_1_3` | def | `RandomSystems/CondEquiv.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massAfalse_filterDom.match_1_1` | def | `RandomSystems/CondEquiv.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massAfalse_filterDom.match_1_3` | def | `RandomSystems/CondEquiv.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.CondEquiv.massAfalse_fTransform_historyEvaluator.match_1_1` | def | `RandomSystems/CondEquiv.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.take_succ_ne_nil._proof_1_1` | thm | `RandomSystems/CondEquiv.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.CondEquiv.massY_fTransform_historyEvaluator.match_1_1` | def | `RandomSystems/CondEquiv.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.Counting.prod_one_sub_ge_one_sub_sum` | thm | `RandomSystems/Counting.lean:27` | `mass-layer-and-epsilon` |
| `RandomSystems.CR18.Counting.card_perm_fiber` | thm | `RandomSystems/Counting.lean:539` | `perm-fresh-refinement` |
| `RandomSystems.CR18.Counting.card_perm_fiber._simp_1_1` | thm | `RandomSystems/Counting.lean:?` | `perm-fresh-refinement` |
| `RandomSystems.CR18.Counting.card_perm_fiber._simp_1_2` | thm | `RandomSystems/Counting.lean:?` | `perm-fresh-refinement` |
| `RandomSystems.CR18.Counting.card_perm_fiber._simp_1_3` | thm | `RandomSystems/Counting.lean:?` | `perm-fresh-refinement` |
| `RandomSystems.CR18.Counting.card_perm_fiber_finset._simp_1_1` | thm | `RandomSystems/Counting.lean:?` | `perm-fresh-refinement` |
| `RandomSystems.CR18.Counting.card_perm_fiber_finset._simp_1_2` | thm | `RandomSystems/Counting.lean:?` | `perm-fresh-refinement` |
| `RandomSystems.CR18.Counting.card_function_fiber_finset.match_1_1` | def | `RandomSystems/Counting.lean:?` | `mass-layer-and-epsilon` |
| `RandomSystems.CR18.Counting.card_function_fiber_finset._simp_1_3` | thm | `RandomSystems/Counting.lean:?` | `mass-layer-and-epsilon` |
| `RandomSystems.CR18.Counting.card_function_fiber_finset._simp_1_4` | thm | `RandomSystems/Counting.lean:?` | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.weight_eq_sum` | thm | `RandomSystems/Dist.lean:77` | `sop-statement-and-semantics` |
| `RandomSystems.Dist.mass_true` | thm | `RandomSystems/Dist.lean:178` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass_eq_zero_of_forall_not` | thm | `RandomSystems/Dist.lean:184` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass_le_weight` | thm | `RandomSystems/Dist.lean:212` | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.uniform_apply` | thm | `RandomSystems/Dist.lean:437` | `sop-statement-and-semantics` |
| `RandomSystems.Dist.weight_uniform` | thm | `RandomSystems/Dist.lean:475` | `sop-statement-and-semantics` |
| `RandomSystems.Dist.mem_support_fTransform` | thm | `RandomSystems/Dist.lean:565` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass_fTransform` | thm | `RandomSystems/Dist.lean:572` | `condequiv-instantiation` |
| `RandomSystems.Dist.weight_fTransform` | thm | `RandomSystems/Dist.lean:583` | `sop-statement-and-semantics` |
| `RandomSystems.Dist.fTransform_isProbDist` | thm | `RandomSystems/Dist.lean:591` | `blind-game-endpoint` |
| `RandomSystems.Dist.prod` | def | `RandomSystems/Dist.lean:1107` | `blind-game-endpoint` |
| `RandomSystems.Dist.prod_apply` | thm | `RandomSystems/Dist.lean:1116` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass_prod_eq_double_sum` | thm | `RandomSystems/Dist.lean:1149` | `blind-game-endpoint` |
| `RandomSystems.Dist.weight_prod` | thm | `RandomSystems/Dist.lean:1185` | `blind-game-endpoint` |
| `RandomSystems.Dist.prod_isProbDist` | thm | `RandomSystems/Dist.lean:1205` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass_eq_sum` | thm | `RandomSystems/Dist.lean:1281` | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.weight_eq_weight_of_isProbDist` | thm | `RandomSystems/Dist.lean:1301` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass_prod_and` | thm | `RandomSystems/Dist.lean:1461` | `blind-game-endpoint` |
| `RandomSystems.Dist.weight_eq_finsupp_sum` | thm | `RandomSystems/Dist.lean:1545` | `blind-game-endpoint` |
| `RandomSystems.Dist.isProbDist_fTransform._simp_1` | thm | `RandomSystems/Dist.lean:?` | `blind-game-endpoint` |
| `RandomSystems.Dist.mass.eq_1` | thm | `RandomSystems/Dist.lean:?` | `mass-layer-and-epsilon` |
| `RandomSystems.Dist.isProbDist.eq_1` | thm | `RandomSystems/Dist.lean:?` | `blind-game-endpoint` |
| `RandomSystems.Dist.weight.eq_1` | thm | `RandomSystems/Dist.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdictProb` | def | `RandomSystems/Distinguishing.lean:107` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.advantage` | def | `RandomSystems/Distinguishing.lean:113` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.advantage.eq_1` | thm | `RandomSystems/Distinguishing.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.foldl_keepUntil_length_eq_take` | thm | `RandomSystems/GameOf.lean:51` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_eq_of_dom_iff` | thm | `RandomSystems/GameOf.lean:101` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_filterQueries_eq_take_of_total` | thm | `RandomSystems/GameOf.lean:134` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_filterQueries_functionEvaluator` | thm | `RandomSystems/GameOf.lean:177` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_fullyDefined_filterQueries_of_total_ge` | thm | `RandomSystems/GameOf.lean:188` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.gameOfDDS` | def | `RandomSystems/GameOf.lean:230` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.dom_gameOfDDS` | thm | `RandomSystems/GameOf.lean:234` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_gameOfDDS` | thm | `RandomSystems/GameOf.lean:241` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_gameOfDDS` | thm | `RandomSystems/GameOf.lean:255` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputBit_gameOfDDS` | thm | `RandomSystems/GameOf.lean:261` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_length_eq_of_fire` | thm | `RandomSystems/GameOf.lean:291` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_outputs_filterQueries_tail_of_total` | thm | `RandomSystems/GameOf.lean:313` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total` | thm | `RandomSystems/GameOf.lean:357` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_filterQueries_iff_tail_of_total` | thm | `RandomSystems/GameOf.lean:412` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD` | def | `RandomSystems/GameOf.lean:492` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ddToDDE_padDDD_of_lt` | thm | `RandomSystems/GameOf.lean:519` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD_val_of_lt` | thm | `RandomSystems/GameOf.lean:529` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ddToDDE_padDDD_of_ge` | thm | `RandomSystems/GameOf.lean:537` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD_val_of_ge` | thm | `RandomSystems/GameOf.lean:545` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_ge` | thm | `RandomSystems/GameOf.lean:556` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_length_eq` | thm | `RandomSystems/GameOf.lean:569` | `blind-game-endpoint` |
| `RandomSystems.CR18.queriesExactly_ddToDDE_padDDD` | thm | `RandomSystems/GameOf.lean:577` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_padDDD_iff_tail` | thm | `RandomSystems/GameOf.lean:590` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before` | thm | `RandomSystems/GameOf.lean:635` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_padDDD_filterQueries_iff_of_total` | thm | `RandomSystems/GameOf.lean:688` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDDDist` | def | `RandomSystems/GameOf.lean:889` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDDDist_isProbDist` | thm | `RandomSystems/GameOf.lean:894` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDDDist_queriesExactly_support` | thm | `RandomSystems/GameOf.lean:902` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty` | thm | `RandomSystems/GameOf.lean:914` | `blind-game-endpoint` |
| `RandomSystems.CR18.advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty` | thm | `RandomSystems/GameOf.lean:937` | `blind-game-endpoint` |
| `RandomSystems.CR18.DeltaFilteredFiniteQueryNormalization` | def | `RandomSystems/GameOf.lean:1176` | `blind-game-endpoint` |
| `RandomSystems.CR18.deltaFilteredFiniteQueryNormalization_of_padDDDDist_advantage` | thm | `RandomSystems/GameOf.lean:1187` | `blind-game-endpoint` |
| `RandomSystems.CR18.deltaFilteredFiniteQueryNormalization_of_totalOnNonempty` | thm | `RandomSystems/GameOf.lean:1204` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact` | thm | `RandomSystems/GameOf.lean:1232` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdictProb_eq_of_queriesExactly_zero` | thm | `RandomSystems/GameOf.lean:1274` | `blind-game-endpoint` |
| `RandomSystems.CR18.totalOnNonempty_ignoreMBO` | thm | `RandomSystems/GameOf.lean:1403` | `blind-game-endpoint` |
| `RandomSystems.CR18.isProbDist_ignoreMBO` | thm | `RandomSystems/GameOf.lean:1411` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` | thm | `RandomSystems/GameOf.lean:1432` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD.match_1` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD._proof_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_length_eq._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_length_eq._proof_1_2` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_2` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_3` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_4` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_fullyDefined_filterQueries_of_total_ge._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_outputs_filterQueries_tail_of_total._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_filterQueries_iff_tail_of_total.match_1_1` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_2` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total.match_1_3` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_5` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_6` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_2` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_3` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_4` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_padDDD_filterQueries_iff_of_total._proof_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_padDDD_filterQueries_iff_of_total._proof_1_2` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._simp_1_6` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.isProbDist_ignoreMBO._simp_1_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_1` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_3` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_5` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_7` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_9` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_11` | def | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.gameOfDDS._proof_1` | thm | `RandomSystems/GameOf.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_prod_eq_double_sum` | thm | `RandomSystems/Lemma415.lean:50` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_eq_prod_mass` | thm | `RandomSystems/Lemma415.lean:59` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_zero` | thm | `RandomSystems/Lemma415.lean:77` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_succ_stall` | thm | `RandomSystems/Lemma415.lean:80` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_succ_fire` | thm | `RandomSystems/Lemma415.lean:85` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcriptInputs_append` | thm | `RandomSystems/Lemma415.lean:91` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcriptOutputs_append` | thm | `RandomSystems/Lemma415.lean:95` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcriptInputs_length` | thm | `RandomSystems/Lemma415.lean:99` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcriptOutputs_length` | thm | `RandomSystems/Lemma415.lean:102` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_length_eq` | thm | `RandomSystems/Lemma415.lean:124` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_take` | thm | `RandomSystems/Lemma415.lean:142` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_freeze` | thm | `RandomSystems/Lemma415.lean:163` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerMatches` | def | `RandomSystems/Lemma415.lean:195` | `blind-game-endpoint` |
| `RandomSystems.CR18.gameMatches` | def | `RandomSystems/Lemma415.lean:204` | `blind-game-endpoint` |
| `RandomSystems.CR18.massYAfalse_eq_mass_gameMatches` | thm | `RandomSystems/Lemma415.lean:213` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerFactor` | def | `RandomSystems/Lemma415.lean:221` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProbBehavior` | def | `RandomSystems/Lemma415.lean:231` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProbBehavior` | def | `RandomSystems/Lemma415.lean:239` | `blind-game-endpoint` |
| `RandomSystems.CR18.QueriesExactly` | def | `RandomSystems/Lemma415.lean:249` | `blind-game-endpoint` |
| `RandomSystems.CR18.TotalUpTo` | def | `RandomSystems/Lemma415.lean:259` | `blind-game-endpoint` |
| `RandomSystems.CR18.massDom_eq_weight_of_totalUpTo` | thm | `RandomSystems/Lemma415.lean:272` | `blind-game-endpoint` |
| `RandomSystems.CR18.massDom_eq_one_of_totalUpTo` | thm | `RandomSystems/Lemma415.lean:281` | `blind-game-endpoint` |
| `RandomSystems.CR18.mem_support_fTransform` | thm | `RandomSystems/Lemma415.lean:290` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.totalUpTo_filterQueries` | thm | `RandomSystems/Lemma415.lean:304` | `blind-game-endpoint` |
| `RandomSystems.CR18.take_succ_get'` | thm | `RandomSystems/Lemma415.lean:315` | `blind-game-endpoint` |
| `RandomSystems.CR18.getLast_take_succ` | thm | `RandomSystems/Lemma415.lean:332` | `condequiv-instantiation` |
| `RandomSystems.CR18.run_proj` | thm | `RandomSystems/Lemma415.lean:351` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches` | thm | `RandomSystems/Lemma415.lean:414` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_eq_tsum_of_unique` | thm | `RandomSystems/Lemma415.lean:515` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProb_eq_fiber` | thm | `RandomSystems/Lemma415.lean:567` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProb_eq_behavior` | thm | `RandomSystems/Lemma415.lean:638` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_eq_behavior` | thm | `RandomSystems/Lemma415.lean:652` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_length_eq._proof_1_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_length_eq._proof_1_3` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_length_eq._proof_1_2` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.transcript_take._proof_1_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_2` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._simp_1_3` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._simp_1_4` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_5` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_6` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_7` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_8` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_9` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_to_matches._proof_1_10` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_proj._proof_1_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_proj._proof_1_2` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.run_proj._proof_1_3` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.GamePerf.winProb.eq_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProb.eq_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProbBehavior.eq_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winnerFactor.eq_1` | thm | `RandomSystems/Lemma415.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.getLast_take_succ._proof_1_1` | thm | `RandomSystems/Lemma415.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.GamePerf.winProb` | def | `RandomSystems/MaxWinProb.lean:37` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.GamePerf.winProb_le_weight` | thm | `RandomSystems/MaxWinProb.lean:42` | `blind-game-endpoint` |
| `RandomSystems.CR18.GamePerf.winProb_add_compl` | thm | `RandomSystems/MaxWinProb.lean:62` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunPDS.filterDom` | def | `RandomSystems/PDS.lean:105` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunPDS.isProbDist_filterQueries_iff` | thm | `RandomSystems/PDS.lean:130` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunPDS.CumulativeBehavior` | def | `RandomSystems/PDS.lean:459` | `condequiv-instantiation` |
| `RandomSystems.CR18.PFunPDS.cumulativeBehavior` | def | `RandomSystems/PDS.lean:465` | `condequiv-instantiation` |
| `RandomSystems.CR18.PFunDDS.IsMBO` | def | `RandomSystems/PDS.lean:2939` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputHistory` | def | `RandomSystems/PDS.lean:2945` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.DDS.IsGame` | def | `RandomSystems/PDS.lean:2954` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.historyEvaluator_pair_isGame_of_monotone` | thm | `RandomSystems/PDS.lean:2964` | `blind-game-endpoint` |
| `RandomSystems.CR18.MonotoneMBO` | def | `RandomSystems/PDS.lean:2995` | `blind-game-endpoint` |
| `RandomSystems.CR18.isGame_filterDom` | thm | `RandomSystems/PDS.lean:2999` | `blind-game-endpoint` |
| `RandomSystems.CR18.monotoneMBO_filterDom` | thm | `RandomSystems/PDS.lean:3006` | `blind-game-endpoint` |
| `RandomSystems.CR18.monotoneMBO_filterQueries` | thm | `RandomSystems/PDS.lean:3022` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.StopFinal` | def | `RandomSystems/PDS.lean:3082` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.DDD` | def | `RandomSystems/PDS.lean:3091` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.winnerView` | def | `RandomSystems/PDS.lean:3104` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ddToDDE` | def | `RandomSystems/PDS.lean:3117` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.verdict` | def | `RandomSystems/PDS.lean:3143` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.ddToDDE.match_1` | def | `RandomSystems/PDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.outputHistory._proof_2` | thm | `RandomSystems/PDS.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputHistory._proof_1` | thm | `RandomSystems/PDS.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunConverter.queryLimitApply` | def | `RandomSystems/PFunConverter.lean:763` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunConverter.queryLimitApply_dom` | thm | `RandomSystems/PFunConverter.lean:818` | `blind-game-endpoint` |
| `RandomSystems.CR18.PrefixClosed` | def | `RandomSystems/PFunDDS.lean:25` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.prefixClosed_length_le` | thm | `RandomSystems/PFunDDS.lean:39` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.Raw` | def | `RandomSystems/PFunDDS.lean:50` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.Valid` | def | `RandomSystems/PFunDDS.lean:58` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.dom` | def | `RandomSystems/PFunDDS.lean:77` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.output` | def | `RandomSystems/PFunDDS.lean:85` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.output_congr` | thm | `RandomSystems/PFunDDS.lean:90` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.valid` | thm | `RandomSystems/PFunDDS.lean:97` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.empty_not_mem` | thm | `RandomSystems/PFunDDS.lean:100` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.prefix_closed` | thm | `RandomSystems/PFunDDS.lean:103` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.dom_functionEvaluator` | thm | `RandomSystems/PFunDDS.lean:120` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.dom_historyEvaluator` | thm | `RandomSystems/PFunDDS.lean:142` | `condequiv-instantiation` |
| `RandomSystems.CR18.PFunDDS.historyEvaluator_output` | thm | `RandomSystems/PFunDDS.lean:148` | `condequiv-instantiation` |
| `RandomSystems.CR18.PFunDDS.keptPrefix` | def | `RandomSystems/PFunDDS.lean:163` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.fullyDefined` | def | `RandomSystems/PFunDDS.lean:171` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.dom_fullyDefined` | thm | `RandomSystems/PFunDDS.lean:185` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_fullyDefined` | thm | `RandomSystems/PFunDDS.lean:191` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_foldl_eq_append_of_mem` | thm | `RandomSystems/PFunDDS.lean:259` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_eq_self_of_mem` | thm | `RandomSystems/PFunDDS.lean:277` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_eq_self_of_mem_or_empty` | thm | `RandomSystems/PFunDDS.lean:281` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_fullyDefined_append_of_mem` | thm | `RandomSystems/PFunDDS.lean:300` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.filterDom` | def | `RandomSystems/PFunDDS.lean:336` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.filterQueries` | def | `RandomSystems/PFunDDS.lean:360` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.mem_dom_filterQueries` | thm | `RandomSystems/PFunDDS.lean:367` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ioTranscript` | def | `RandomSystems/PFunDDS.lean:387` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ioTranscript_map_fst` | thm | `RandomSystems/PFunDDS.lean:399` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.DDE` | def | `RandomSystems/PFunDDS.lean:947` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcriptInputs` | def | `RandomSystems/PFunDDS.lean:954` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcriptOutputs` | def | `RandomSystems/PFunDDS.lean:959` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcript` | def | `RandomSystems/PFunDDS.lean:984` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcript.match_3` | def | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcript.match_1` | def | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.fullyDefined._proof_1` | thm | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcript._proof_1` | thm | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.filterDom._proof_1` | thm | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.filterDom._proof_2` | thm | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.functionEvaluator._proof_1` | thm | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.historyEvaluator._proof_1` | thm | `RandomSystems/PFunDDS.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.transcript._proof_2` | thm | `RandomSystems/PFunDDS.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output.congr_simp` | thm | `RandomSystems/PFunDDS.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.PFunDDS.ioTranscript._proof_2` | thm | `RandomSystems/PFunDDS.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ioTranscript._proof_1` | thm | `RandomSystems/PFunDDS.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.ignoreMBO` | def | `RandomSystems/RelateGameDistinguishing.lean:39` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_ignoreMBO` | thm | `RandomSystems/RelateGameDistinguishing.lean:46` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.keptPrefix_ignoreMBO` | thm | `RandomSystems/RelateGameDistinguishing.lean:49` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_fullyDefined_ignoreMBO` | thm | `RandomSystems/RelateGameDistinguishing.lean:54` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.projT` | def | `RandomSystems/RelateGameDistinguishing.lean:67` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.projT_append` | thm | `RandomSystems/RelateGameDistinguishing.lean:72` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.projT_inputs` | thm | `RandomSystems/RelateGameDistinguishing.lean:75` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.projT_outputs` | thm | `RandomSystems/RelateGameDistinguishing.lean:78` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO` | thm | `RandomSystems/RelateGameDistinguishing.lean:85` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_ignoreMBO` | thm | `RandomSystems/RelateGameDistinguishing.lean:103` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_fTransform` | thm | `RandomSystems/RelateGameDistinguishing.lean:117` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_fTransform_game` | thm | `RandomSystems/RelateGameDistinguishing.lean:132` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_ddToDDE` | thm | `RandomSystems/RelateGameDistinguishing.lean:146` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdictMatches` | def | `RandomSystems/RelateGameDistinguishing.lean:156` | `blind-game-endpoint` |
| `RandomSystems.CR18.distNotWonZ1` | def | `RandomSystems/RelateGameDistinguishing.lean:162` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunPDS.ignoreMBO_filterDom` | thm | `RandomSystems/RelateGameDistinguishing.lean:195` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunPDS.ignoreMBO_filterQueries` | thm | `RandomSystems/RelateGameDistinguishing.lean:205` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_split` | thm | `RandomSystems/RelateGameDistinguishing.lean:214` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_mono` | thm | `RandomSystems/RelateGameDistinguishing.lean:222` | `blind-game-endpoint` |
| `RandomSystems.CR18.advantage_le_winProb_assemble` | thm | `RandomSystems/RelateGameDistinguishing.lean:250` | `blind-game-endpoint` |
| `RandomSystems.CR18.projT_run_outputs` | thm | `RandomSystems/RelateGameDistinguishing.lean:301` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdict_iff_verdictMatches` | thm | `RandomSystems/RelateGameDistinguishing.lean:318` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdictNotWon_eq_distNotWonZ1` | thm | `RandomSystems/RelateGameDistinguishing.lean:335` | `blind-game-endpoint` |
| `RandomSystems.CR18.distNotWonZ1.eq_1` | thm | `RandomSystems/RelateGameDistinguishing.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.tupleConsistent` | def | `RandomSystems/SwitchingLemma.lean:359` | `condequiv-instantiation` |
| `RandomSystems.CR18.mass_tuple_agree_eq_zero_of_not_consistent` | thm | `RandomSystems/SwitchingLemma.lean:373` | `condequiv-instantiation` |
| `RandomSystems.CR18.mass_tuple_agree_and_event_eq_zero_of_not_consistent` | thm | `RandomSystems/SwitchingLemma.lean:395` | `condequiv-instantiation` |
| `RandomSystems.CR18.vector_toList_toFinset_eq_image_get` | thm | `RandomSystems/SwitchingLemma.lean:416` | `condequiv-instantiation` |
| `RandomSystems.CR18.forall_toList_iff` | thm | `RandomSystems/SwitchingLemma.lean:438` | `condequiv-instantiation` |
| `RandomSystems.CR18.tupleAssignmentOn` | def | `RandomSystems/SwitchingLemma.lean:540` | `condequiv-instantiation` |
| `RandomSystems.CR18.tuple_agree_iff_assignmentOn` | thm | `RandomSystems/SwitchingLemma.lean:546` | `condequiv-instantiation` |
| `RandomSystems.CR18.blindQueryVector` | def | `RandomSystems/SwitchingLemma.lean:795` | `blind-game-endpoint` |
| `RandomSystems.CR18.isPrefix_blindQueryList` | thm | `RandomSystems/SwitchingLemma.lean:822` | `blind-game-endpoint` |
| `RandomSystems.CR18.keptPrefix_gameOfDDS_filterQueries_functionEvaluator` | thm | `RandomSystems/SwitchingLemma.lean:892` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_input_get?_eq_env` | thm | `RandomSystems/SwitchingLemma.lean:1030` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true` | thm | `RandomSystems/SwitchingLemma.lean:1075` | `blind-game-endpoint` |
| `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list` | thm | `RandomSystems/SwitchingLemma.lean:1124` | `blind-game-endpoint` |
| `RandomSystems.CR18.blindMaxWinProb_filterQueries_monitored_le` | thm | `RandomSystems/SwitchingLemma.lean:1778` | `blind-game-endpoint` |
| `RandomSystems.CR18.seededConditionCGame_monotoneMBO` | thm | `RandomSystems/SwitchingLemma.lean:1833` | `blind-game-endpoint` |
| `RandomSystems.CR18.seededConditionCGame_totalOnNonempty` | thm | `RandomSystems/SwitchingLemma.lean:1844` | `blind-game-endpoint` |
| `RandomSystems.CR18.seededConditionCGame_isProbDist` | thm | `RandomSystems/SwitchingLemma.lean:1852` | `blind-game-endpoint` |
| `RandomSystems.CR18.seededConditionCGame_isProbDist._simp_1_1` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true._simp_1_1` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true._simp_1_2` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_1` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_2` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_input_get?_eq_env._proof_1_1` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_3` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_4` | thm | `RandomSystems/SwitchingLemma.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.tupleAssignmentOn._proof_1` | thm | `RandomSystems/SwitchingLemma.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions._auto_1` | def | `RandomSystems/SwitchingLemma.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions._auto_3` | def | `RandomSystems/SwitchingLemma.lean:?` | `condequiv-instantiation` |
| `RandomSystems.CR18.PFunDDS.stripMBO._proof_1` | thm | `RandomSystems/SystemMBO.lean:?` | `sop-statement-and-semantics` |
| `RandomSystems.CR18.PFunDDS.combineSys` | def | `RandomSystems/Theorem417.lean:34` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_combineSys` | thm | `RandomSystems/Theorem417.lean:43` | `blind-game-endpoint` |
| `RandomSystems.CR18.gameEnhance` | def | `RandomSystems/Theorem417.lean:52` | `blind-game-endpoint` |
| `RandomSystems.CR18.massAllFalse` | def | `RandomSystems/Theorem417.lean:70` | `blind-game-endpoint` |
| `RandomSystems.CR18.massYAfalse_gameEnhance` | thm | `RandomSystems/Theorem417.lean:81` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_congr_support` | thm | `RandomSystems/Theorem417.lean:127` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame` | thm | `RandomSystems/Theorem417.lean:142` | `blind-game-endpoint` |
| `RandomSystems.CR18.massAllFalse_eq_massAfalse` | thm | `RandomSystems/Theorem417.lean:176` | `blind-game-endpoint` |
| `RandomSystems.CR18.massYAfalse_le_massAllFalse` | thm | `RandomSystems/Theorem417.lean:201` | `blind-game-endpoint` |
| `RandomSystems.CR18.massYAfalse_gameEnhance_eq_of_totalUpTo` | thm | `RandomSystems/Theorem417.lean:212` | `blind-game-endpoint` |
| `RandomSystems.CR18.MassYAfalseEqAt` | def | `RandomSystems/Theorem417.lean:269` | `blind-game-endpoint` |
| `RandomSystems.CR18.MassYAfalseEqAt.symm` | thm | `RandomSystems/Theorem417.lean:276` | `blind-game-endpoint` |
| `RandomSystems.CR18.distNotWonZ1_congr_mass_at` | thm | `RandomSystems/Theorem417.lean:287` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProbBehavior_congr_mass_at` | thm | `RandomSystems/Theorem417.lean:301` | `blind-game-endpoint` |
| `RandomSystems.CR18.advantage_le_winProb_of_massYAfalseEqAt` | thm | `RandomSystems/Theorem417.lean:325` | `blind-game-endpoint` |
| `RandomSystems.CR18.mass_singleton'` | thm | `RandomSystems/Theorem417.lean:422` | `blind-game-endpoint` |
| `RandomSystems.CR18.fTransform_fst_prod` | thm | `RandomSystems/Theorem417.lean:431` | `blind-game-endpoint` |
| `RandomSystems.CR18.gameEnhance_isProbDist` | thm | `RandomSystems/Theorem417.lean:472` | `blind-game-endpoint` |
| `RandomSystems.CR18.gameEnhance_totalUpTo` | thm | `RandomSystems/Theorem417.lean:478` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_iff_at_exact` | thm | `RandomSystems/Theorem417.lean:501` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.output_fullyDefined_ignoreMBO_combineSys_eq_of_totalUpTo` | thm | `RandomSystems/Theorem417.lean:541` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo` | thm | `RandomSystems/Theorem417.lean:601` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.verdict_ignoreMBO_combineSys_iff_of_totalUpTo` | thm | `RandomSystems/Theorem417.lean:653` | `blind-game-endpoint` |
| `RandomSystems.CR18.verdictProb_ignoreMBO_gameEnhance_eq_of_totalUpTo` | thm | `RandomSystems/Theorem417.lean:669` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.combineSys._proof_1` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.combineSys._proof_2` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.combineSys._proof_3` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.gameEnhance.eq_1` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.massAllFalse_eq_massAfalse._proof_1_1` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._proof_1_1` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._proof_1_2` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._simp_1_3` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._proof_1_4` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo._proof_1_1` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo._proof_1_2` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo._proof_1_3` | thm | `RandomSystems/Theorem417.lean:?` | `blind-game-endpoint` |
| `RandomSystems.CR18.winsDDS` | def | `RandomSystems/WinProb.lean:32` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb` | def | `RandomSystems/WinProb.lean:38` | `blind-game-endpoint` |
| `RandomSystems.CR18.notWonProb` | def | `RandomSystems/WinProb.lean:46` | `blind-game-endpoint` |
| `RandomSystems.CR18.winProb_add_notWonProb` | thm | `RandomSystems/WinProb.lean:51` | `blind-game-endpoint` |

### 4.5 MATHLIB frontier — 1348 constants (trusted, not expanded)

Not tabulated in full; the complete list with per-node use counts is in
`review/sop-dag.tsv`. The 30 most-used:

| constant | direct uses |
|---|---|
| `Eq` | 365 |
| `Nat` | 267 |
| `List` | 255 |
| `id` | 242 |
| `OfNat.ofNat` | 240 |
| `Bool` | 232 |
| `Membership.mem` | 231 |
| `Prod` | 220 |
| `Eq.refl` | 204 |
| `congrArg` | 201 |
| `Not` | 188 |
| `instOfNatNat` | 184 |
| `HAdd.hAdd` | 184 |
| `instHAdd` | 184 |
| `Eq.trans` | 180 |
| `Eq.mpr` | 169 |
| `List.nil` | 167 |
| `And` | 163 |
| `NNReal` | 151 |
| `instAddNat` | 146 |
| `LE.le` | 139 |
| `Eq.symm` | 138 |
| `List.length` | 137 |
| `Set` | 127 |
| `Set.instMembership` | 125 |
| `Finset` | 119 |
| `LT.lt` | 113 |
| `False` | 113 |
| `True` | 112 |
| `instLTNat` | 110 |

## 5. Slices

Six **disjoint** slices covering all 500 repo nodes (NEW and LIB). Every repo node has exactly
one owner; the union is the whole repo DAG. Cross-slice edges exist and are shown in §3.

Node counts are a poor proxy for review effort here and I have not pretended otherwise:
`sop-counting-core` is 34 nodes but ~300 lines of dense induction; `blind-game-endpoint` is
308 nodes but 5 statements to read plus a judgement about a framework already exercised by
two other published bounds. The slices are sized by *coherence*, not by node count.

| slice | nodes | NEW | LIB | roots |
|---|---|---|---|---|
| `sop-statement-and-semantics` | 81 | 16 | 65 | 15 |
| `perm-fresh-refinement` | 19 | 12 | 7 | 7 |
| `sop-counting-core` | 34 | 34 | 0 | 22 |
| `mass-layer-and-epsilon` | 20 | 7 | 13 | 8 |
| `condequiv-instantiation` | 38 | 1 | 37 | 9 |
| `blind-game-endpoint` | 308 | 0 | 308 | 5 |

### `sop-statement-and-semantics` — 81 nodes (16 NEW, 65 LIB)

**Does the statement say what the abstract claims, over objects that mean what their names say?**

Roots:

* `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight` — `RandomSystems/SumOfPermutationsTight.lean:769` [NEW]
* `RandomSystems.CR18.SoPTight.sopReal` — `RandomSystems/SumOfPermutationsTight.lean:82` [NEW]
* `RandomSystems.CR18.SoPTight.sopIdeal` — `RandomSystems/SumOfPermutationsTight.lean:88` [NEW]
* `RandomSystems.CR18.SoPTight.sopFunction` — `RandomSystems/SumOfPermutationsTight.lean:77` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightGame` — `RandomSystems/SumOfPermutationsTight.lean:504` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightGame_ignoreMBO` — `RandomSystems/SumOfPermutationsTight.lean:508` [NEW]
* `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist` — `RandomSystems/SumOfPermutationsTight.lean:492` [NEW]
* `RandomSystems.CR18.SoPTight.sopIdeal_totalOnNonempty` — `RandomSystems/SumOfPermutationsTight.lean:497` [NEW]
* `RandomSystems.CR18.maxAdvantage` — `RandomSystems/Distinguishing.lean:136` [LIB]
* `RandomSystems.CR18.PFunPDS.filterQueries` — `RandomSystems/PDS.lean:120` [LIB]
* `RandomSystems.CR18.PFunPDS.ignoreMBO` — `RandomSystems/RelateGameDistinguishing.lean:190` [LIB]
* `RandomSystems.CR18.seededConditionCGame` — `RandomSystems/SwitchingLemma.lean:1824` [LIB]
* `RandomSystems.CR18.seededConditionCGame_ignoreMBO` — `RandomSystems/SwitchingLemma.lean:1864` [NEW]
* `RandomSystems.CR18.Counting.three_sum_sq_le_cube` — `RandomSystems/Counting.lean:257` [LIB]
* `RandomSystems.CR18.PFunPDS.ofFunDist_totalOnNonempty` — `RandomSystems/GameOf.lean:949` [LIB]

What the reviewer must establish:

* The **vacuity gate**: `ε` is `∃`-quantified *outside* the `∀ H` — check it really is (`sopEps` is a closed `ℕ → ℕ → ℝ`), and that `Fintype.card H` is the only channel from the group to `ε`.
* Does `sopReal` compute `x ↦ π₁ x + π₂ x` under *independent uniform* `π₁,π₂`? `Dist.uniform (Equiv.Perm G × Equiv.Perm G)` is uniform on the **product**, which is independence — confirm, do not assume.
* Does `sopIdeal` = URF? `Dist.fTransform PFunDDS.functionEvaluator (Dist.uniform (G → G))`.
* `Dist` is **not normalised** (arbitrary `NNReal` weights). Every "probability" claim needs `isProbDist` somewhere. Check `Dist.uniform_isProbDist`, `Dist.weight`, `Dist.mass ≤ weight` and where the proof relies on weight = 1.
* `maxAdvantage` (= `Δ(·,·)`): is it a sup over *all* distinguishers, and is the sup over an inhabited class? An empty distinguisher class makes `Δ = 0` and the theorem vacuous. Trace `advantage`, `verdictProb`, `GamePerf.winProb`, `PFunDDS.Winner`, `PFunDDS.verdict`.
* `PFunPDS.filterQueries q`: does `⌈q⌉` really cap the interaction at `q` queries (and is it `≤ q` or `< q`)? Trace `PFunDDS.filterDom`, `keptPrefix`, `PrefixClosed`, `prefixClosed_length_le`.
* `sopTightGame_ignoreMBO : ignoreMBO sopTightGame = sopReal` — this is the hinge that makes the bound about `sopReal`. Its proof calls the **uncommitted, never-reviewed** `seededConditionCGame_ignoreMBO`.
* The second conjunct (`ε N q < q²/N` for `1 < q < N`) is a floor only; check it is not accidentally *stronger* than the first conjunct can support, and that the `hcase : N < q²` branch is not where all the content hides.

<details><summary>full membership (81)</summary>

* `RandomSystems.CR18.IsBlind` — LIB — `RandomSystems/BlindConverter.lean:51`
* `RandomSystems.CR18.Counting.three_sum_sq_le_cube` — LIB — `RandomSystems/Counting.lean:257`
* `RandomSystems.Dist` — LIB — `RandomSystems/Dist.lean:50`
* `RandomSystems.Dist.weight` — LIB — `RandomSystems/Dist.lean:71`
* `RandomSystems.Dist.weight_eq_sum` — LIB — `RandomSystems/Dist.lean:77`
* `RandomSystems.Dist.isProbDist` — LIB — `RandomSystems/Dist.lean:111`
* `RandomSystems.Dist.mass` — LIB — `RandomSystems/Dist.lean:150`
* `RandomSystems.Dist.uniform` — LIB — `RandomSystems/Dist.lean:431`
* `RandomSystems.Dist.uniform_apply` — LIB — `RandomSystems/Dist.lean:437`
* `RandomSystems.Dist.weight_uniform` — LIB — `RandomSystems/Dist.lean:475`
* `RandomSystems.Dist.uniform_isProbDist` — LIB — `RandomSystems/Dist.lean:485`
* `RandomSystems.Dist.fTransform` — LIB — `RandomSystems/Dist.lean:523`
* `RandomSystems.Dist.weight_fTransform` — LIB — `RandomSystems/Dist.lean:583`
* `RandomSystems.Dist.isProbDist_fTransform` — LIB — `RandomSystems/Dist.lean:598`
* `RandomSystems.Dist.fTransform_comp` — LIB — `RandomSystems/Dist.lean:1572`
* `RandomSystems.CR18.verdictProb` — LIB — `RandomSystems/Distinguishing.lean:107`
* `RandomSystems.CR18.advantage` — LIB — `RandomSystems/Distinguishing.lean:113`
* `RandomSystems.CR18.maxAdvantage` — LIB — `RandomSystems/Distinguishing.lean:136`
* `RandomSystems.CR18.PFunPDS.ofFunDist_totalOnNonempty` — LIB — `RandomSystems/GameOf.lean:949`
* `RandomSystems.CR18.mem_support_fTransform` — LIB — `RandomSystems/Lemma415.lean:290`
* `RandomSystems.CR18.GamePerf.winProb` — LIB — `RandomSystems/MaxWinProb.lean:37`
* `RandomSystems.CR18.PFunPDS` — LIB — `RandomSystems/PDS.lean:68`
* `RandomSystems.CR18.PFunPDS.filterQueries` — LIB — `RandomSystems/PDS.lean:120`
* `RandomSystems.CR18.PFunPDS.ofFunDist` — LIB — `RandomSystems/PDS.lean:144`
* `RandomSystems.CR18.PFunDDS.Winner` — LIB — `RandomSystems/PDS.lean:3070`
* `RandomSystems.CR18.PFunDDS.StopFinal` — LIB — `RandomSystems/PDS.lean:3082`
* `RandomSystems.CR18.PFunDDS.DDD` — LIB — `RandomSystems/PDS.lean:3091`
* `RandomSystems.CR18.PFunDDS.ddToDDE` — LIB — `RandomSystems/PDS.lean:3117`
* `RandomSystems.CR18.PFunDDS.verdict` — LIB — `RandomSystems/PDS.lean:3143`
* `RandomSystems.CR18.PFunDDS.ddToDDE.match_1` — LIB — `RandomSystems/PDS.lean:?`
* `RandomSystems.CR18.PFunPDS.ofFunDist.eq_1` — LIB — `RandomSystems/PDS.lean:?`
* `RandomSystems.CR18.PrefixClosed` — LIB — `RandomSystems/PFunDDS.lean:25`
* `RandomSystems.CR18.prefixClosed_length_le` — LIB — `RandomSystems/PFunDDS.lean:39`
* `RandomSystems.CR18.PFunDDS.Raw` — LIB — `RandomSystems/PFunDDS.lean:50`
* `RandomSystems.CR18.PFunDDS.Valid` — LIB — `RandomSystems/PFunDDS.lean:58`
* `RandomSystems.CR18.PFunDDS.DDS` — LIB — `RandomSystems/PFunDDS.lean:64`
* `RandomSystems.CR18.PFunDDS.dom` — LIB — `RandomSystems/PFunDDS.lean:77`
* `RandomSystems.CR18.PFunDDS.output` — LIB — `RandomSystems/PFunDDS.lean:85`
* `RandomSystems.CR18.PFunDDS.valid` — LIB — `RandomSystems/PFunDDS.lean:97`
* `RandomSystems.CR18.PFunDDS.empty_not_mem` — LIB — `RandomSystems/PFunDDS.lean:100`
* `RandomSystems.CR18.PFunDDS.prefix_closed` — LIB — `RandomSystems/PFunDDS.lean:103`
* `RandomSystems.CR18.PFunDDS.functionEvaluator` — LIB — `RandomSystems/PFunDDS.lean:112`
* `RandomSystems.CR18.PFunDDS.dom_functionEvaluator` — LIB — `RandomSystems/PFunDDS.lean:120`
* `RandomSystems.CR18.PFunDDS.historyEvaluator` — LIB — `RandomSystems/PFunDDS.lean:134`
* `RandomSystems.CR18.PFunDDS.keptPrefix` — LIB — `RandomSystems/PFunDDS.lean:163`
* `RandomSystems.CR18.PFunDDS.fullyDefined` — LIB — `RandomSystems/PFunDDS.lean:171`
* `RandomSystems.CR18.PFunDDS.filterDom` — LIB — `RandomSystems/PFunDDS.lean:336`
* `RandomSystems.CR18.PFunDDS.filterQueries` — LIB — `RandomSystems/PFunDDS.lean:360`
* `RandomSystems.CR18.PFunDDS.DDE` — LIB — `RandomSystems/PFunDDS.lean:947`
* `RandomSystems.CR18.PFunDDS.transcriptInputs` — LIB — `RandomSystems/PFunDDS.lean:954`
* `RandomSystems.CR18.PFunDDS.transcriptOutputs` — LIB — `RandomSystems/PFunDDS.lean:959`
* `RandomSystems.CR18.PFunDDS.transcript` — LIB — `RandomSystems/PFunDDS.lean:984`
* `RandomSystems.CR18.PFunDDS.filterDom._proof_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.filterDom._proof_2` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.fullyDefined._proof_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.functionEvaluator._proof_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.historyEvaluator._proof_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript._proof_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript.match_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript.match_3` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunPDS.ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:190`
* `RandomSystems.CR18.SoPTight.sopFunction` — NEW — `RandomSystems/SumOfPermutationsTight.lean:77`
* `RandomSystems.CR18.SoPTight.sopReal` — NEW — `RandomSystems/SumOfPermutationsTight.lean:82`
* `RandomSystems.CR18.SoPTight.sopIdeal` — NEW — `RandomSystems/SumOfPermutationsTight.lean:88`
* `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist` — NEW — `RandomSystems/SumOfPermutationsTight.lean:492`
* `RandomSystems.CR18.SoPTight.sopIdeal_totalOnNonempty` — NEW — `RandomSystems/SumOfPermutationsTight.lean:497`
* `RandomSystems.CR18.SoPTight.sopTightGame` — NEW — `RandomSystems/SumOfPermutationsTight.lean:504`
* `RandomSystems.CR18.SoPTight.sopTightGame_ignoreMBO` — NEW — `RandomSystems/SumOfPermutationsTight.lean:508`
* `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight` — NEW — `RandomSystems/SumOfPermutationsTight.lean:769`
* `RandomSystems.CR18.SoPTight.sopIdeal._proof_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist._simp_1_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sopIdeal_isProbDist._simp_1_7` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sopReal._proof_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sopTightGame.eq_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight._proof_1_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight._proof_1_2` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.seededConditionCGame` — LIB — `RandomSystems/SwitchingLemma.lean:1824`
* `RandomSystems.CR18.seededConditionCGame_ignoreMBO` — NEW — `RandomSystems/SwitchingLemma.lean:1864`
* `RandomSystems.CR18.PFunDDS.stripMBO` — LIB — `RandomSystems/SystemMBO.lean:29`
* `RandomSystems.CR18.PFunPDS.stripMBO` — LIB — `RandomSystems/SystemMBO.lean:45`
* `RandomSystems.CR18.PFunDDS.stripMBO._proof_1` — LIB — `RandomSystems/SystemMBO.lean:?`

</details>

### `perm-fresh-refinement` — 19 nodes (12 NEW, 7 LIB)

**The lazy-sampling counting kernel in `PermFreshCounting.lean`: is the fresh pair really uniform on the unused product?**

Roots:

* `RandomSystems.CR18.Counting.card_fresh_pair_refine` — `RandomSystems/PermFreshCounting.lean:295` [NEW]
* `RandomSystems.CR18.Counting.card_fresh_pair_fiber` — `RandomSystems/PermFreshCounting.lean:104` [NEW]
* `RandomSystems.CR18.Counting.card_permPair_restrict` — `RandomSystems/PermFreshCounting.lean:70` [NEW]
* `RandomSystems.CR18.Counting.restrict_perm_injective` — `RandomSystems/PermFreshCounting.lean:64` [NEW]
* `RandomSystems.CR18.Counting.availPairs` — `RandomSystems/PermFreshCounting.lean:93` [NEW]
* `RandomSystems.CR18.Counting.mem_availPairs` — `RandomSystems/PermFreshCounting.lean:96` [NEW]
* `RandomSystems.CR18.Counting.card_perm_fiber_finset` — `RandomSystems/Counting.lean:623` [LIB]

What the reviewer must establish:

* `card_fresh_pair_refine` is the single load-bearing counting lemma of the whole proof: `(N−|Q|)² · #{p | P p ∧ R … (p.1 x) (p.2 x)} = m · #{p | P p}`. Its hypothesis `hm` is quantified over **every** `p : Perm X × Perm X` (not just over one representative per fiber) — the proof uses only `hm p₀`, so `hm` is stronger than needed here, but at the call sites it must still be discharged for arbitrary `p`. Check both call sites (`card_goodAgree`, `card_good`) supply it for arbitrary `p`, via `himgcard p` from `Finset.card_image_of_injective`.
* Is `hP` (restriction-invariance of `P`) actually needed and actually satisfied? It is the formal content of "the past is determined by the restriction to `Q`".
* `card_fresh_pair_fiber` assembles `(n−k)·(n−k)·((n−k−1)!)² = ((n−k)!)²` under truncated `Nat` subtraction. Its guard is `hkn : Q.card < Fintype.card X`, which `card_fresh_pair_refine` derives internally from `hx : x ∉ Q` via `Finset.ssubset_univ_iff` — so the guard is *not* a caller obligation. Verify that derivation, because it is the only thing preventing the `n − k = 0` degenerate case.
* Two different `R` types: `card_fresh_pair_fiber` takes `R : X → X → Prop`, `card_fresh_pair_refine` takes `R : Finset X → Finset X → X → X → Prop` and applies it at `Q.image p.1, Q.image p.2` — i.e. the used sets are read off *the same `p`* being tested. The fiber argument (`himage`) is what makes that constant along a fiber. Check `himage`.
* `card_permPair_restrict` splits the pair fiber as a product — verify the two permutations are genuinely independent in the count (`Finset.card_product` on a `×ˢ`), which is where "independent permutations" enters the combinatorics.
* `restrict_perm_injective` is stated for `fun z : ↥Q => π z.1`. Confirm `card_perm_fiber_finset` (LIB) needs exactly that and is itself correct.

<details><summary>full membership (19)</summary>

* `RandomSystems.CR18.Counting.card_perm_fiber` — LIB — `RandomSystems/Counting.lean:539`
* `RandomSystems.CR18.Counting.card_perm_fiber_finset` — LIB — `RandomSystems/Counting.lean:623`
* `RandomSystems.CR18.Counting.card_perm_fiber._simp_1_1` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.card_perm_fiber._simp_1_2` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.card_perm_fiber._simp_1_3` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.card_perm_fiber_finset._simp_1_1` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.card_perm_fiber_finset._simp_1_2` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.restrict_perm_injective` — NEW — `RandomSystems/PermFreshCounting.lean:64`
* `RandomSystems.CR18.Counting.card_permPair_restrict` — NEW — `RandomSystems/PermFreshCounting.lean:70`
* `RandomSystems.CR18.Counting.availPairs` — NEW — `RandomSystems/PermFreshCounting.lean:93`
* `RandomSystems.CR18.Counting.mem_availPairs` — NEW — `RandomSystems/PermFreshCounting.lean:96`
* `RandomSystems.CR18.Counting.card_fresh_pair_fiber` — NEW — `RandomSystems/PermFreshCounting.lean:104`
* `RandomSystems.CR18.Counting.card_fresh_pair_refine` — NEW — `RandomSystems/PermFreshCounting.lean:295`
* `RandomSystems.CR18.Counting.card_fresh_pair_fiber._proof_1_3` — NEW — `RandomSystems/PermFreshCounting.lean:?`
* `RandomSystems.CR18.Counting.card_fresh_pair_fiber._proof_1_4` — NEW — `RandomSystems/PermFreshCounting.lean:?`
* `RandomSystems.CR18.Counting.card_fresh_pair_fiber._simp_1_1` — NEW — `RandomSystems/PermFreshCounting.lean:?`
* `RandomSystems.CR18.Counting.card_fresh_pair_fiber._simp_1_2` — NEW — `RandomSystems/PermFreshCounting.lean:?`
* `RandomSystems.CR18.Counting.card_fresh_pair_refine._simp_1_1` — NEW — `RandomSystems/PermFreshCounting.lean:?`
* `RandomSystems.CR18.Counting.card_fresh_pair_refine._simp_1_2` — NEW — `RandomSystems/PermFreshCounting.lean:?`

</details>

### `sop-counting-core` — 34 nodes (34 NEW, 0 LIB)

**The balanced fresh set, the monitored condition, and the `goodCount` induction — the new mathematics.**

Roots:

* `RandomSystems.CR18.SoPTight.card_good` — `RandomSystems/SumOfPermutationsTight.lean:391` [NEW]
* `RandomSystems.CR18.SoPTight.card_goodAgree` — `RandomSystems/SumOfPermutationsTight.lean:291` [NEW]
* `RandomSystems.CR18.SoPTight.goodCount` — `RandomSystems/SumOfPermutationsTight.lean:275` [NEW]
* `RandomSystems.CR18.SoPTight.goodCount_step` — `RandomSystems/SumOfPermutationsTight.lean:279` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightBad` — `RandomSystems/SumOfPermutationsTight.lean:218` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightBad_decidable` — `RandomSystems/SumOfPermutationsTight.lean:222` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightBad_monotone` — `RandomSystems/SumOfPermutationsTight.lean:226` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightBad_concat` — `RandomSystems/SumOfPermutationsTight.lean:234` [NEW]
* `RandomSystems.CR18.SoPTight.sopTightBad_congr` — `RandomSystems/SumOfPermutationsTight.lean:251` [NEW]
* `RandomSystems.CR18.SoPTight.card_avail_fresh` — `RandomSystems/SumOfPermutationsTight.lean:190` [NEW]
* `RandomSystems.CR18.SoPTight.card_avail_fresh_answer` — `RandomSystems/SumOfPermutationsTight.lean:156` [NEW]
* `RandomSystems.CR18.SoPTight.freshKeep` — `RandomSystems/SumOfPermutationsTight.lean:128` [NEW]
* `RandomSystems.CR18.SoPTight.freshKeep_subset` — `RandomSystems/SumOfPermutationsTight.lean:132` [NEW]
* `RandomSystems.CR18.SoPTight.card_freshKeep` — `RandomSystems/SumOfPermutationsTight.lean:136` [NEW]
* `RandomSystems.CR18.SoPTight.freshFiber` — `RandomSystems/SumOfPermutationsTight.lean:99` [NEW]
* `RandomSystems.CR18.SoPTight.mem_freshFiber` — `RandomSystems/SumOfPermutationsTight.lean:103` [NEW]
* `RandomSystems.CR18.SoPTight.card_freshFiber_ge` — `RandomSystems/SumOfPermutationsTight.lean:110` [NEW]
* `RandomSystems.CR18.SoPTight.sopFresh` — `RandomSystems/SumOfPermutationsTight.lean:142` [NEW]
* `RandomSystems.CR18.SoPTight.sopFresh_decidable` — `RandomSystems/SumOfPermutationsTight.lean:145` [NEW]
* `RandomSystems.CR18.Counting.canonSubset` — `RandomSystems/PermFreshCounting.lean:42` [NEW]
* `RandomSystems.CR18.Counting.canonSubset_subset` — `RandomSystems/PermFreshCounting.lean:45` [NEW]
* `RandomSystems.CR18.Counting.canonSubset_card` — `RandomSystems/PermFreshCounting.lean:52` [NEW]

What the reviewer must establish:

* **The uniformity claim.** `card_avail_fresh_answer`: for every prescribed answer `c`, exactly `N − 2k` available-and-surviving pairs. This is eq. (4.38). Check the bijection `freshKeep U V c → {(u, c−u)}` really is onto the filtered set and that `card_freshKeep` needs `hUV : U.card = V.card` (it does — check that hypothesis is discharged at every call site, via `Finset.card_image_of_injective`).
* **`Nat` truncation.** `card_freshKeep` states `card = Fintype.card G − 2 * U.card` in `ℕ`. Once `2|U| ≥ N` this is `0`, `freshKeep` is empty, `sopFresh` is always false, `sopTightBad` always fires, and the good world is empty. Confirm the theorem is not *only* true because of this degenerate regime — i.e. that `mass_sopTightBad_le` genuinely covers `2k < N` with content.
* `card_freshFiber_ge` closes by `omega` over truncated subtraction. Check `Fintype.card G − (U.card + V.card) ≤ |freshFiber|` is the inequality actually needed, and that the inclusion–exclusion step (`Finset.card_image_le` on `v ↦ y − v`) is tight enough.
* **The monitored condition.** `sopTightBad p l` quantifies over `pre ++ [x] <+: l` with `x ∉ pre`. Check it fires at *first* occurrences only, that it is prefix-monotone (`sopTightBad_monotone`), and that `sopTightBad_concat` really is an iff (a repeat cannot fire it).
* `sopTightBad_congr`: the condition depends only on values at queried points. This is what lets `card_fresh_pair_refine`'s `hP` apply. Check the two `Finset.image_congr` rewrites cover both permutations.
* **The induction.** `card_goodAgree` (prescribed transcript) and `card_good` (no transcript) are two `List.reverseRecOn` inductions with the same shape. Both cancel `(N−d)²` by `Nat.eq_of_mul_eq_mul_left`; check the positivity side conditions and that `hlt : l.toFinset.card < Fintype.card G` is derived, not assumed.
* `goodCount_step` is a pure `Nat` identity with a `⟨j, hj⟩ : ∃ j, N − d = j + 1` destructuring. Check it for off-by-one.
* `canonSubset` is defined by `Exists.choose` — see §6. Confirm no argument depends on *which* subset is chosen.

<details><summary>full membership (34)</summary>

* `RandomSystems.CR18.Counting.canonSubset` — NEW — `RandomSystems/PermFreshCounting.lean:42`
* `RandomSystems.CR18.Counting.canonSubset_subset` — NEW — `RandomSystems/PermFreshCounting.lean:45`
* `RandomSystems.CR18.Counting.canonSubset_card` — NEW — `RandomSystems/PermFreshCounting.lean:52`
* `RandomSystems.CR18.SoPTight.freshFiber` — NEW — `RandomSystems/SumOfPermutationsTight.lean:99`
* `RandomSystems.CR18.SoPTight.mem_freshFiber` — NEW — `RandomSystems/SumOfPermutationsTight.lean:103`
* `RandomSystems.CR18.SoPTight.card_freshFiber_ge` — NEW — `RandomSystems/SumOfPermutationsTight.lean:110`
* `RandomSystems.CR18.SoPTight.freshKeep` — NEW — `RandomSystems/SumOfPermutationsTight.lean:128`
* `RandomSystems.CR18.SoPTight.freshKeep_subset` — NEW — `RandomSystems/SumOfPermutationsTight.lean:132`
* `RandomSystems.CR18.SoPTight.card_freshKeep` — NEW — `RandomSystems/SumOfPermutationsTight.lean:136`
* `RandomSystems.CR18.SoPTight.sopFresh` — NEW — `RandomSystems/SumOfPermutationsTight.lean:142`
* `RandomSystems.CR18.SoPTight.sopFresh_decidable` — NEW — `RandomSystems/SumOfPermutationsTight.lean:145`
* `RandomSystems.CR18.SoPTight.card_avail_fresh_answer` — NEW — `RandomSystems/SumOfPermutationsTight.lean:156`
* `RandomSystems.CR18.SoPTight.card_avail_fresh` — NEW — `RandomSystems/SumOfPermutationsTight.lean:190`
* `RandomSystems.CR18.SoPTight.sopTightBad` — NEW — `RandomSystems/SumOfPermutationsTight.lean:218`
* `RandomSystems.CR18.SoPTight.sopTightBad_decidable` — NEW — `RandomSystems/SumOfPermutationsTight.lean:222`
* `RandomSystems.CR18.SoPTight.sopTightBad_monotone` — NEW — `RandomSystems/SumOfPermutationsTight.lean:226`
* `RandomSystems.CR18.SoPTight.sopTightBad_concat` — NEW — `RandomSystems/SumOfPermutationsTight.lean:234`
* `RandomSystems.CR18.SoPTight.sopTightBad_congr` — NEW — `RandomSystems/SumOfPermutationsTight.lean:251`
* `RandomSystems.CR18.SoPTight.goodCount` — NEW — `RandomSystems/SumOfPermutationsTight.lean:275`
* `RandomSystems.CR18.SoPTight.goodCount_step` — NEW — `RandomSystems/SumOfPermutationsTight.lean:279`
* `RandomSystems.CR18.SoPTight.card_goodAgree` — NEW — `RandomSystems/SumOfPermutationsTight.lean:291`
* `RandomSystems.CR18.SoPTight.card_good` — NEW — `RandomSystems/SumOfPermutationsTight.lean:391`
* `RandomSystems.CR18.SoPTight.card_avail_fresh_answer._simp_1_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.card_avail_fresh_answer._simp_1_2` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.card_avail_fresh_answer._simp_1_3` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.card_freshFiber_ge._proof_1_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.card_freshKeep._proof_1_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.card_good._proof_1_3` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.card_goodAgree._proof_1_4` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.goodCount.eq_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.goodCount_step._proof_1_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.goodCount_step._proof_1_2` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sopFresh.eq_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`
* `RandomSystems.CR18.SoPTight.sopFunction.eq_1` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`

</details>

### `mass-layer-and-epsilon` — 20 nodes (7 NEW, 13 LIB)

**From cardinalities to a real number: does the counting actually become a probability bound, and is `ε` what the docstring says?**

Roots:

* `RandomSystems.CR18.SoPTight.mass_agree_and_good` — `RandomSystems/SumOfPermutationsTight.lean:520` [NEW]
* `RandomSystems.CR18.SoPTight.mass_good_eq_prod` — `RandomSystems/SumOfPermutationsTight.lean:610` [NEW]
* `RandomSystems.CR18.SoPTight.mass_sopTightBad_le` — `RandomSystems/SumOfPermutationsTight.lean:699` [NEW]
* `RandomSystems.CR18.SoPTight.sopEps` — `RandomSystems/SumOfPermutationsTight.lean:600` [NEW]
* `RandomSystems.CR18.SoPTight.sopEps_nonneg` — `RandomSystems/SumOfPermutationsTight.lean:603` [NEW]
* `RandomSystems.CR18.SoPTight.sopEps_ge_one_of_large` — `RandomSystems/SumOfPermutationsTight.lean:680` [NEW]
* `RandomSystems.CR18.Counting.chain_product_lower_bound` — `RandomSystems/Counting.lean:43` [LIB]
* `RandomSystems.CR18.Counting.card_function_fiber_finset` — `RandomSystems/Counting.lean:345` [LIB]

What the reviewer must establish:

* `mass_agree_and_good` is the product law: seed-mass of (realizes `a` ∧ good) = URF-mass of (realizes `a`) × seed-mass of (good). It routes through `Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq`, a **cardinality** hypothesis. Verify the cardinality identity supplied really is `|P| · |B| = |Q| · |E|` in the right order — a transposition here silently changes the claim.
* The `ã` total extension (`if h : z ∈ S then a ⟨z,h⟩ else 0`) must make "realizes `a` on `S`" and "realizes `ã` on `l`" the *same* event. Check `hagree` in both directions.
* `mass_good_eq_prod` casts `ℕ → ℝ` under truncated subtraction; every factor needs `2k < N` (`hsmall`). Check `hprod2` termwise casting and `hfac` (`N! = (N−d)!·∏(N−k)`).
* `mass_sopTightBad_le` splits on `∃ k < d, N ≤ 2k`. In that branch the bound is proved by `mass ≤ 1 ≤ Σ` (`sopEps_ge_one_of_large`) — i.e. **the bound is vacuous there**. Check the other branch is not also vacuous.
* `Counting.chain_product_lower_bound` (Weierstrass, LIB) requires `0 ≤ f k ≤ 1`; check `hle1` supplies it for `k²/(N−k)²` and that the direction of the inequality survives `linarith`.
* Is `sopEps N q = min 1 (Σ_{k<q} k²/(N−k)²)` the ≈ q³/3N² the docstring claims, and is `min 1` doing more work than advertised? At `q ≥ N/2` the sum exceeds 1 and `ε = 1` — a trivial bound.

<details><summary>full membership (20)</summary>

* `RandomSystems.CR18.Counting.prod_one_sub_ge_one_sub_sum` — LIB — `RandomSystems/Counting.lean:27`
* `RandomSystems.CR18.Counting.chain_product_lower_bound` — LIB — `RandomSystems/Counting.lean:43`
* `RandomSystems.CR18.Counting.card_function_fiber_finset` — LIB — `RandomSystems/Counting.lean:345`
* `RandomSystems.CR18.Counting.card_function_fiber_finset._simp_1_3` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.card_function_fiber_finset._simp_1_4` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.CR18.Counting.card_function_fiber_finset.match_1_1` — LIB — `RandomSystems/Counting.lean:?`
* `RandomSystems.Dist.mass_add_compl` — LIB — `RandomSystems/Dist.lean:205`
* `RandomSystems.Dist.mass_le_weight` — LIB — `RandomSystems/Dist.lean:212`
* `RandomSystems.Dist.mass_le_one` — LIB — `RandomSystems/Dist.lean:312`
* `RandomSystems.Dist.mass_eq_sum` — LIB — `RandomSystems/Dist.lean:1281`
* `RandomSystems.Dist.uniform_mass_eq_card_filter` — LIB — `RandomSystems/Dist.lean:1306`
* `RandomSystems.Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq` — LIB — `RandomSystems/Dist.lean:1317`
* `RandomSystems.Dist.mass.eq_1` — LIB — `RandomSystems/Dist.lean:?`
* `RandomSystems.CR18.SoPTight.mass_agree_and_good` — NEW — `RandomSystems/SumOfPermutationsTight.lean:520`
* `RandomSystems.CR18.SoPTight.sopEps` — NEW — `RandomSystems/SumOfPermutationsTight.lean:600`
* `RandomSystems.CR18.SoPTight.sopEps_nonneg` — NEW — `RandomSystems/SumOfPermutationsTight.lean:603`
* `RandomSystems.CR18.SoPTight.mass_good_eq_prod` — NEW — `RandomSystems/SumOfPermutationsTight.lean:610`
* `RandomSystems.CR18.SoPTight.sopEps_ge_one_of_large` — NEW — `RandomSystems/SumOfPermutationsTight.lean:680`
* `RandomSystems.CR18.SoPTight.mass_sopTightBad_le` — NEW — `RandomSystems/SumOfPermutationsTight.lean:699`
* `RandomSystems.CR18.SoPTight.mass_sopTightBad_le._proof_1_2` — NEW — `RandomSystems/SumOfPermutationsTight.lean:?`

</details>

### `condequiv-instantiation` — 38 nodes (1 NEW, 37 LIB)

**Is `sopTightGame |≡ sopIdeal` the conditional equivalence of Maurer13b / CR18, and is the reduction lemma instantiated correctly?**

Roots:

* `RandomSystems.CR18.SoPTight.sopTight_condEquiv` — `RandomSystems/SumOfPermutationsTight.lean:572` [NEW]
* `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions` — `RandomSystems/SwitchingLemma.lean:576` [LIB]
* `RandomSystems.CR18.massY_fTransform_lastQuery` — `RandomSystems/SwitchingLemma.lean:457` [LIB]
* `RandomSystems.CR18.massYAfalse_fTransform_lastQuery` — `RandomSystems/SwitchingLemma.lean:473` [LIB]
* `RandomSystems.CR18.CondEquiv.massAfalse_fTransform_historyEvaluator` — `RandomSystems/CondEquiv.lean:256` [LIB]
* `RandomSystems.CR18.CondEquiv.CondEquiv` — `RandomSystems/CondEquiv.lean:118` [LIB]
* `RandomSystems.CR18.CondEquiv.massAfalse` — `RandomSystems/CondEquiv.lean:73` [LIB]
* `RandomSystems.CR18.CondEquiv.massYAfalse` — `RandomSystems/CondEquiv.lean:61` [LIB]
* `RandomSystems.CR18.CondEquiv.TotalOnNonempty` — `RandomSystems/CondEquiv.lean:96` [LIB]

What the reviewer must establish:

* Read `CondEquiv.CondEquiv`, `massAfalse`, `massYAfalse`, `massY`, `massDom` against Maurer13b (read the PDF **visually**). Does `|≡` mean "the two systems have the same conditional distribution given the monitor has not fired", or something weaker?
* `condEquiv_of_transcript_mass_reductions` takes four obligations. Check each supplied argument is the obligation the lemma asks for and not a neighbouring one: (i) `massAfalse` reduction, (ii) `massY` reduction, (iii) `massYAfalse` reduction, (iv) the per-transcript mass factorization.
* The `decide`/`Prop` boundary: the game carries `decide (sopTightBad p l)` while the mass lemmas talk about `¬ sopTightBad p l`. Two `Dist.mass_congr _ fun p => by simp` steps bridge them. Confirm `simp` closed the right goal — this is exactly where a `decide`-vs-`Prop` mismatch would hide.
* `TotalOnNonempty` for the ideal system: is the ideal side really total, and does the lemma need it for the reason it says?
* **Direction.** The docstring argues at length that the game must be on the *real* side here (`SumOfPermutations` puts it on the ideal side). Check the claim that `freshKeep` is empty for `2k ≥ N` and that eq. (4.38) then holds as `0 = 0` — a conditional equivalence with an empty conditioning event is not an equivalence, it is a vacuity.

<details><summary>full membership (38)</summary>

* `RandomSystems.CR18.CondEquiv.massYAfalse` — LIB — `RandomSystems/CondEquiv.lean:61`
* `RandomSystems.CR18.CondEquiv.massAfalse` — LIB — `RandomSystems/CondEquiv.lean:73`
* `RandomSystems.CR18.CondEquiv.massY` — LIB — `RandomSystems/CondEquiv.lean:81`
* `RandomSystems.CR18.CondEquiv.massDom` — LIB — `RandomSystems/CondEquiv.lean:88`
* `RandomSystems.CR18.CondEquiv.TotalOnNonempty` — LIB — `RandomSystems/CondEquiv.lean:96`
* `RandomSystems.CR18.CondEquiv.CondEquiv` — LIB — `RandomSystems/CondEquiv.lean:118`
* `RandomSystems.CR18.CondEquiv.massDom_eq_weight_of_totalOnNonempty` — LIB — `RandomSystems/CondEquiv.lean:131`
* `RandomSystems.CR18.CondEquiv.massDom_eq_one_of_totalOnNonempty` — LIB — `RandomSystems/CondEquiv.lean:141`
* `RandomSystems.CR18.CondEquiv.take_succ_ne_nil` — LIB — `RandomSystems/CondEquiv.lean:249`
* `RandomSystems.CR18.CondEquiv.massAfalse_fTransform_historyEvaluator` — LIB — `RandomSystems/CondEquiv.lean:256`
* `RandomSystems.CR18.CondEquiv.massY_fTransform_historyEvaluator` — LIB — `RandomSystems/CondEquiv.lean:270`
* `RandomSystems.CR18.CondEquiv.massYAfalse_fTransform_historyEvaluator` — LIB — `RandomSystems/CondEquiv.lean:288`
* `RandomSystems.CR18.CondEquiv.massAfalse_fTransform_historyEvaluator.match_1_1` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.massY_fTransform_historyEvaluator.match_1_1` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.take_succ_ne_nil._proof_1_1` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.Dist.mass_congr` — LIB — `RandomSystems/Dist.lean:196`
* `RandomSystems.Dist.mass_fTransform` — LIB — `RandomSystems/Dist.lean:572`
* `RandomSystems.CR18.getLast_take_succ` — LIB — `RandomSystems/Lemma415.lean:332`
* `RandomSystems.CR18.getLast_take_succ._proof_1_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.PFunPDS.CumulativeBehavior` — LIB — `RandomSystems/PDS.lean:459`
* `RandomSystems.CR18.PFunPDS.cumulativeBehavior` — LIB — `RandomSystems/PDS.lean:465`
* `RandomSystems.CR18.PFunDDS.dom_historyEvaluator` — LIB — `RandomSystems/PFunDDS.lean:142`
* `RandomSystems.CR18.PFunDDS.historyEvaluator_output` — LIB — `RandomSystems/PFunDDS.lean:148`
* `RandomSystems.CR18.PFunDDS.output.congr_simp` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.SoPTight.sopTight_condEquiv` — NEW — `RandomSystems/SumOfPermutationsTight.lean:572`
* `RandomSystems.CR18.tupleConsistent` — LIB — `RandomSystems/SwitchingLemma.lean:359`
* `RandomSystems.CR18.mass_tuple_agree_eq_zero_of_not_consistent` — LIB — `RandomSystems/SwitchingLemma.lean:373`
* `RandomSystems.CR18.mass_tuple_agree_and_event_eq_zero_of_not_consistent` — LIB — `RandomSystems/SwitchingLemma.lean:395`
* `RandomSystems.CR18.vector_toList_toFinset_eq_image_get` — LIB — `RandomSystems/SwitchingLemma.lean:416`
* `RandomSystems.CR18.forall_toList_iff` — LIB — `RandomSystems/SwitchingLemma.lean:438`
* `RandomSystems.CR18.massY_fTransform_lastQuery` — LIB — `RandomSystems/SwitchingLemma.lean:457`
* `RandomSystems.CR18.massYAfalse_fTransform_lastQuery` — LIB — `RandomSystems/SwitchingLemma.lean:473`
* `RandomSystems.CR18.tupleAssignmentOn` — LIB — `RandomSystems/SwitchingLemma.lean:540`
* `RandomSystems.CR18.tuple_agree_iff_assignmentOn` — LIB — `RandomSystems/SwitchingLemma.lean:546`
* `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions` — LIB — `RandomSystems/SwitchingLemma.lean:576`
* `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions._auto_1` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.condEquiv_of_transcript_mass_reductions._auto_3` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.tupleAssignmentOn._proof_1` — LIB — `RandomSystems/SwitchingLemma.lean:?`

</details>

### `blind-game-endpoint` — 308 nodes (0 NEW, 308 LIB)

**The pre-existing CR18 spine: does the packaged endpoint deliver the advantage bound it promises, and is it applied with the right arguments?**

Roots:

* `RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le` — `RandomSystems/SwitchingLemma.lean:1881` [LIB]
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` — `RandomSystems/GameOf.lean:1432` [LIB]
* `RandomSystems.CR18.blindMaxWinProb_filterQueries_monitored_le` — `RandomSystems/SwitchingLemma.lean:1778` [LIB]
* `RandomSystems.CR18.blindQueryList` — `RandomSystems/SwitchingLemma.lean:811` [LIB]
* `RandomSystems.CR18.blindQueryList_length_le` — `RandomSystems/SwitchingLemma.lean:814` [LIB]

What the reviewer must establish:

* **Nothing in this slice is NEW.** 308 pre-existing nodes from `GameOf` (69), `Lemma415` (50), `BlindAbsorption` (38), `Theorem417` (36), `PFunDDS` (32), `RelateGameDistinguishing` (25), `SwitchingLemma` (21), `PDS` (20), `Dist` (16), `CondEquiv` (15) and six smaller modules. It is by far the largest slice by node count and by far the smallest by *new* content.
* The review here is **statement-level and application-level**, not line-level. Read exactly these five statements: `maxAdvantage_filterQueries_seededConditionCGame_le` (SwitchingLemma:1877), `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` (GameOf:1417), `blindMaxWinProb_filterQueries_monitored_le` (SwitchingLemma:1770), `blindQueryList` / `blindQueryList_length_le` (SwitchingLemma:810/814).
* The endpoint's leaf obligation is `∀ w, IsBlind w → D.mass (fun a => bad a (blindQueryList w q)) ≤ ε`. **`blindQueryList w q` is a fixed list depending only on the blind winner `w`** — this is what turns an adaptive adversary into a non-adaptive schedule. Check `IsBlind` really means "receives no answers" and that `blindQueryList` is the schedule such a winner asks; if `IsBlind` is too strong, the blind reduction quantifies over too few adversaries.
* Two `autoParam` slots in `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` (`_auto_1`, `_auto_3`) are discharged by tactic. Confirm what they proved.
* Cross-check: the same endpoint is used by `RandomSystems/CBCMAC.lean:1083` and `RandomSystems/SumOfPermutations.lean:254`. Prior exercise is evidence, not proof; but a defect here would be a defect in three published bounds, which raises the stakes and the prior probability that it is right.
* The `NNReal`/`ℝ` boundary at the very top: the endpoint yields `≤ (ε : ℝ)` for `ε : NNReal`, and the root theorem lands it via `Real.toNNReal (sopEps …)` + `Real.coe_toNNReal _ (sopEps_nonneg _ _)`. A negative `ε` would be silently clamped to `0`; `sopEps_nonneg` is what rules that out. Check it.

<details><summary>full membership (308)</summary>

* `RandomSystems.CR18.PFunDDS.tagFalse` — LIB — `RandomSystems/BlindAbsorption.lean:65`
* `RandomSystems.CR18.PFunDDS.mem_dom_tagFalse` — LIB — `RandomSystems/BlindAbsorption.lean:73`
* `RandomSystems.CR18.PFunDDS.output_tagFalse` — LIB — `RandomSystems/BlindAbsorption.lean:78`
* `RandomSystems.CR18.PFunDDS.ignoreMBO_tagFalse` — LIB — `RandomSystems/BlindAbsorption.lean:82`
* `RandomSystems.CR18.PFunDDS.transcriptOutputs_tagFalse_false` — LIB — `RandomSystems/BlindAbsorption.lean:90`
* `RandomSystems.CR18.PFunDDS.not_winsDDS_tagFalse` — LIB — `RandomSystems/BlindAbsorption.lean:115`
* `RandomSystems.CR18.absorbedWinner` — LIB — `RandomSystems/BlindAbsorption.lean:130`
* `RandomSystems.CR18.isBlind_absorbedWinner` — LIB — `RandomSystems/BlindAbsorption.lean:135`
* `RandomSystems.CR18.queriesExactly_absorbedWinner` — LIB — `RandomSystems/BlindAbsorption.lean:145`
* `RandomSystems.CR18.absorbedWinnerDist` — LIB — `RandomSystems/BlindAbsorption.lean:167`
* `RandomSystems.CR18.absorbedWinnerDist_isProbDist` — LIB — `RandomSystems/BlindAbsorption.lean:175`
* `RandomSystems.CR18.isBlindDist_absorbedWinnerDist` — LIB — `RandomSystems/BlindAbsorption.lean:185`
* `RandomSystems.CR18.absorbed_run_eq` — LIB — `RandomSystems/BlindAbsorption.lean:204`
* `RandomSystems.CR18.winnerMatches_absorbedWinner_of_matches` — LIB — `RandomSystems/BlindAbsorption.lean:223`
* `RandomSystems.CR18.winnerMatches_inj_xs` — LIB — `RandomSystems/BlindAbsorption.lean:242`
* `RandomSystems.CR18.mass_gameMatches_tagFalse` — LIB — `RandomSystems/BlindAbsorption.lean:261`
* `RandomSystems.CR18.absorbed_fiber_hex` — LIB — `RandomSystems/BlindAbsorption.lean:284`
* `RandomSystems.CR18.absorbed_fiber_huniq` — LIB — `RandomSystems/BlindAbsorption.lean:322`
* `RandomSystems.CR18.winnerFactor_absorbedWinnerDist_eq` — LIB — `RandomSystems/BlindAbsorption.lean:346`
* `RandomSystems.CR18.tsum_massYAfalse_eq_massAfalse` — LIB — `RandomSystems/BlindAbsorption.lean:378`
* `RandomSystems.CR18.summable_mass_of_unique` — LIB — `RandomSystems/BlindAbsorption.lean:439`
* `RandomSystems.CR18.term_eq_rect_mass` — LIB — `RandomSystems/BlindAbsorption.lean:457`
* `RandomSystems.CR18.summable_notWonTerm` — LIB — `RandomSystems/BlindAbsorption.lean:469`
* `RandomSystems.CR18.summable_notWonTerm_inner` — LIB — `RandomSystems/BlindAbsorption.lean:500`
* `RandomSystems.CR18.notWonProbBehavior_eq_tsum_tsum` — LIB — `RandomSystems/BlindAbsorption.lean:523`
* `RandomSystems.CR18.notWonProbBehavior_absorption` — LIB — `RandomSystems/BlindAbsorption.lean:541`
* `RandomSystems.CR18.winProb_absorption_of_totalUpTo` — LIB — `RandomSystems/BlindAbsorption.lean:584`
* `RandomSystems.CR18.advantage_le_absorbedWinnerProb_of_condEquiv_of_totalUpTo` — LIB — `RandomSystems/BlindAbsorption.lean:642`
* `RandomSystems.CR18.advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo` — LIB — `RandomSystems/BlindAbsorption.lean:728`
* `RandomSystems.CR18.CondEquiv.massAfalse.eq_1` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.PFunDDS.tagFalse._proof_1` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.PFunDDS.transcriptOutputs_tagFalse_false._simp_1_1` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.PFunDDS.transcriptOutputs_tagFalse_false._simp_1_2` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.tsum_massYAfalse_eq_massAfalse._proof_1_2` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.tsum_massYAfalse_eq_massAfalse._simp_1_3` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.winProbBehavior.eq_1` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.winnerMatches_absorbedWinner_of_matches._proof_1_1` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.winnerMatches_absorbedWinner_of_matches._proof_1_2` — LIB — `RandomSystems/BlindAbsorption.lean:?`
* `RandomSystems.CR18.IsBlindDist` — LIB — `RandomSystems/BlindConverter.lean:57`
* `RandomSystems.CR18.blindMaxWinProb` — LIB — `RandomSystems/BlindConverter.lean:67`
* `RandomSystems.CR18.bddAbove_blindWinProb_image` — LIB — `RandomSystems/BlindConverter.lean:75`
* `RandomSystems.CR18.winProb_le_blindMaxWinProb` — LIB — `RandomSystems/BlindConverter.lean:84`
* `RandomSystems.CR18.blindMaxWinProb_fTransform_le` — LIB — `RandomSystems/BlindConverter.lean:103`
* `RandomSystems.CR18.CondEquiv.massAfalse_filterDom` — LIB — `RandomSystems/CondEquiv.lean:152`
* `RandomSystems.CR18.CondEquiv.massAfalse_filterDom_eq_zero` — LIB — `RandomSystems/CondEquiv.lean:161`
* `RandomSystems.CR18.CondEquiv.massDom_filterDom` — LIB — `RandomSystems/CondEquiv.lean:171`
* `RandomSystems.CR18.CondEquiv.massY_filterDom` — LIB — `RandomSystems/CondEquiv.lean:179`
* `RandomSystems.CR18.CondEquiv.massYAfalse_filterDom` — LIB — `RandomSystems/CondEquiv.lean:190`
* `RandomSystems.CR18.CondEquiv.condEquiv_filterDom` — LIB — `RandomSystems/CondEquiv.lean:203`
* `RandomSystems.CR18.CondEquiv.condEquiv_filterQueries` — LIB — `RandomSystems/CondEquiv.lean:237`
* `RandomSystems.CR18.CondEquiv.monotoneMBO_fTransform_historyEvaluator` — LIB — `RandomSystems/CondEquiv.lean:328`
* `RandomSystems.CR18.CondEquiv.totalOnNonempty_fTransform_historyEvaluator` — LIB — `RandomSystems/CondEquiv.lean:340`
* `RandomSystems.CR18.CondEquiv.massAfalse_filterDom.match_1_1` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.massAfalse_filterDom.match_1_3` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.massYAfalse_filterDom.match_1_1` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.massYAfalse_filterDom.match_1_3` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.massY_filterDom.match_1_1` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.CR18.CondEquiv.massY_filterDom.match_1_3` — LIB — `RandomSystems/CondEquiv.lean:?`
* `RandomSystems.Dist.mass_true` — LIB — `RandomSystems/Dist.lean:178`
* `RandomSystems.Dist.mass_eq_zero_of_forall_not` — LIB — `RandomSystems/Dist.lean:184`
* `RandomSystems.Dist.mem_support_fTransform` — LIB — `RandomSystems/Dist.lean:565`
* `RandomSystems.Dist.fTransform_isProbDist` — LIB — `RandomSystems/Dist.lean:591`
* `RandomSystems.Dist.prod` — LIB — `RandomSystems/Dist.lean:1107`
* `RandomSystems.Dist.prod_apply` — LIB — `RandomSystems/Dist.lean:1116`
* `RandomSystems.Dist.mass_prod_eq_double_sum` — LIB — `RandomSystems/Dist.lean:1149`
* `RandomSystems.Dist.weight_prod` — LIB — `RandomSystems/Dist.lean:1185`
* `RandomSystems.Dist.prod_isProbDist` — LIB — `RandomSystems/Dist.lean:1205`
* `RandomSystems.Dist.weight_eq_weight_of_isProbDist` — LIB — `RandomSystems/Dist.lean:1301`
* `RandomSystems.Dist.mass_prod_and` — LIB — `RandomSystems/Dist.lean:1461`
* `RandomSystems.Dist.weight_eq_finsupp_sum` — LIB — `RandomSystems/Dist.lean:1545`
* `RandomSystems.Dist.isProbDist.eq_1` — LIB — `RandomSystems/Dist.lean:?`
* `RandomSystems.Dist.isProbDist_fTransform._simp_1` — LIB — `RandomSystems/Dist.lean:?`
* `RandomSystems.Dist.weight.eq_1` — LIB — `RandomSystems/Dist.lean:?`
* `RandomSystems.CR18.advantage.eq_1` — LIB — `RandomSystems/Distinguishing.lean:?`
* `RandomSystems.CR18.foldl_keepUntil_length_eq_take` — LIB — `RandomSystems/GameOf.lean:51`
* `RandomSystems.CR18.PFunDDS.keptPrefix_eq_of_dom_iff` — LIB — `RandomSystems/GameOf.lean:101`
* `RandomSystems.CR18.PFunDDS.keptPrefix_filterQueries_eq_take_of_total` — LIB — `RandomSystems/GameOf.lean:134`
* `RandomSystems.CR18.PFunDDS.keptPrefix_filterQueries_functionEvaluator` — LIB — `RandomSystems/GameOf.lean:177`
* `RandomSystems.CR18.PFunDDS.output_fullyDefined_filterQueries_of_total_ge` — LIB — `RandomSystems/GameOf.lean:188`
* `RandomSystems.CR18.PFunDDS.gameOfDDS` — LIB — `RandomSystems/GameOf.lean:230`
* `RandomSystems.CR18.PFunDDS.dom_gameOfDDS` — LIB — `RandomSystems/GameOf.lean:234`
* `RandomSystems.CR18.PFunDDS.keptPrefix_gameOfDDS` — LIB — `RandomSystems/GameOf.lean:241`
* `RandomSystems.CR18.PFunDDS.output_gameOfDDS` — LIB — `RandomSystems/GameOf.lean:255`
* `RandomSystems.CR18.PFunDDS.outputBit_gameOfDDS` — LIB — `RandomSystems/GameOf.lean:261`
* `RandomSystems.CR18.PFunDDS.transcript_length_eq_of_fire` — LIB — `RandomSystems/GameOf.lean:291`
* `RandomSystems.CR18.PFunDDS.transcript_outputs_filterQueries_tail_of_total` — LIB — `RandomSystems/GameOf.lean:313`
* `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total` — LIB — `RandomSystems/GameOf.lean:357`
* `RandomSystems.CR18.PFunDDS.verdict_filterQueries_iff_tail_of_total` — LIB — `RandomSystems/GameOf.lean:412`
* `RandomSystems.CR18.PFunDDS.padDDD` — LIB — `RandomSystems/GameOf.lean:492`
* `RandomSystems.CR18.PFunDDS.ddToDDE_padDDD_of_lt` — LIB — `RandomSystems/GameOf.lean:519`
* `RandomSystems.CR18.PFunDDS.padDDD_val_of_lt` — LIB — `RandomSystems/GameOf.lean:529`
* `RandomSystems.CR18.PFunDDS.ddToDDE_padDDD_of_ge` — LIB — `RandomSystems/GameOf.lean:537`
* `RandomSystems.CR18.PFunDDS.padDDD_val_of_ge` — LIB — `RandomSystems/GameOf.lean:545`
* `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_ge` — LIB — `RandomSystems/GameOf.lean:556`
* `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_length_eq` — LIB — `RandomSystems/GameOf.lean:569`
* `RandomSystems.CR18.queriesExactly_ddToDDE_padDDD` — LIB — `RandomSystems/GameOf.lean:577`
* `RandomSystems.CR18.PFunDDS.verdict_padDDD_iff_tail` — LIB — `RandomSystems/GameOf.lean:590`
* `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before` — LIB — `RandomSystems/GameOf.lean:635`
* `RandomSystems.CR18.PFunDDS.verdict_padDDD_filterQueries_iff_of_total` — LIB — `RandomSystems/GameOf.lean:688`
* `RandomSystems.CR18.PFunDDS.padDDDDist` — LIB — `RandomSystems/GameOf.lean:889`
* `RandomSystems.CR18.PFunDDS.padDDDDist_isProbDist` — LIB — `RandomSystems/GameOf.lean:894`
* `RandomSystems.CR18.PFunDDS.padDDDDist_queriesExactly_support` — LIB — `RandomSystems/GameOf.lean:902`
* `RandomSystems.CR18.verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty` — LIB — `RandomSystems/GameOf.lean:914`
* `RandomSystems.CR18.advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty` — LIB — `RandomSystems/GameOf.lean:937`
* `RandomSystems.CR18.DeltaFilteredFiniteQueryNormalization` — LIB — `RandomSystems/GameOf.lean:1176`
* `RandomSystems.CR18.deltaFilteredFiniteQueryNormalization_of_padDDDDist_advantage` — LIB — `RandomSystems/GameOf.lean:1187`
* `RandomSystems.CR18.deltaFilteredFiniteQueryNormalization_of_totalOnNonempty` — LIB — `RandomSystems/GameOf.lean:1204`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact` — LIB — `RandomSystems/GameOf.lean:1232`
* `RandomSystems.CR18.verdictProb_eq_of_queriesExactly_zero` — LIB — `RandomSystems/GameOf.lean:1274`
* `RandomSystems.CR18.totalOnNonempty_ignoreMBO` — LIB — `RandomSystems/GameOf.lean:1403`
* `RandomSystems.CR18.isProbDist_ignoreMBO` — LIB — `RandomSystems/GameOf.lean:1411`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` — LIB — `RandomSystems/GameOf.lean:1432`
* `RandomSystems.CR18.PFunDDS.gameOfDDS._proof_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.output_fullyDefined_filterQueries_of_total_ge._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.padDDD._proof_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.padDDD.match_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_length_eq._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.padDDD_true_iff_of_length_eq._proof_1_2` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_2` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_5` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total._proof_1_6` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total.match_1_3` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_outputs_filterQueries_tail_of_total._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_2` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_3` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before._proof_1_4` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.verdict_filterQueries_iff_tail_of_total.match_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.verdict_padDDD_filterQueries_iff_of_total._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.PFunDDS.verdict_padDDD_filterQueries_iff_of_total._proof_1_2` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_2` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_3` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.foldl_keepUntil_length_eq_take._proof_1_4` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.isProbDist_ignoreMBO._simp_1_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_1` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_11` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_3` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_5` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_7` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._auto_9` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv._simp_1_6` — LIB — `RandomSystems/GameOf.lean:?`
* `RandomSystems.CR18.mass_prod_eq_double_sum` — LIB — `RandomSystems/Lemma415.lean:50`
* `RandomSystems.CR18.winProb_eq_prod_mass` — LIB — `RandomSystems/Lemma415.lean:59`
* `RandomSystems.CR18.transcript_zero` — LIB — `RandomSystems/Lemma415.lean:77`
* `RandomSystems.CR18.transcript_succ_stall` — LIB — `RandomSystems/Lemma415.lean:80`
* `RandomSystems.CR18.transcript_succ_fire` — LIB — `RandomSystems/Lemma415.lean:85`
* `RandomSystems.CR18.transcriptInputs_append` — LIB — `RandomSystems/Lemma415.lean:91`
* `RandomSystems.CR18.transcriptOutputs_append` — LIB — `RandomSystems/Lemma415.lean:95`
* `RandomSystems.CR18.transcriptInputs_length` — LIB — `RandomSystems/Lemma415.lean:99`
* `RandomSystems.CR18.transcriptOutputs_length` — LIB — `RandomSystems/Lemma415.lean:102`
* `RandomSystems.CR18.transcript_length_eq` — LIB — `RandomSystems/Lemma415.lean:124`
* `RandomSystems.CR18.transcript_take` — LIB — `RandomSystems/Lemma415.lean:142`
* `RandomSystems.CR18.transcript_freeze` — LIB — `RandomSystems/Lemma415.lean:163`
* `RandomSystems.CR18.winnerMatches` — LIB — `RandomSystems/Lemma415.lean:195`
* `RandomSystems.CR18.gameMatches` — LIB — `RandomSystems/Lemma415.lean:204`
* `RandomSystems.CR18.massYAfalse_eq_mass_gameMatches` — LIB — `RandomSystems/Lemma415.lean:213`
* `RandomSystems.CR18.winnerFactor` — LIB — `RandomSystems/Lemma415.lean:221`
* `RandomSystems.CR18.notWonProbBehavior` — LIB — `RandomSystems/Lemma415.lean:231`
* `RandomSystems.CR18.winProbBehavior` — LIB — `RandomSystems/Lemma415.lean:239`
* `RandomSystems.CR18.QueriesExactly` — LIB — `RandomSystems/Lemma415.lean:249`
* `RandomSystems.CR18.TotalUpTo` — LIB — `RandomSystems/Lemma415.lean:259`
* `RandomSystems.CR18.massDom_eq_weight_of_totalUpTo` — LIB — `RandomSystems/Lemma415.lean:272`
* `RandomSystems.CR18.massDom_eq_one_of_totalUpTo` — LIB — `RandomSystems/Lemma415.lean:281`
* `RandomSystems.CR18.totalUpTo_filterQueries` — LIB — `RandomSystems/Lemma415.lean:304`
* `RandomSystems.CR18.take_succ_get'` — LIB — `RandomSystems/Lemma415.lean:315`
* `RandomSystems.CR18.run_proj` — LIB — `RandomSystems/Lemma415.lean:351`
* `RandomSystems.CR18.run_to_matches` — LIB — `RandomSystems/Lemma415.lean:414`
* `RandomSystems.CR18.mass_eq_tsum_of_unique` — LIB — `RandomSystems/Lemma415.lean:515`
* `RandomSystems.CR18.notWonProb_eq_fiber` — LIB — `RandomSystems/Lemma415.lean:567`
* `RandomSystems.CR18.notWonProb_eq_behavior` — LIB — `RandomSystems/Lemma415.lean:638`
* `RandomSystems.CR18.winProb_eq_behavior` — LIB — `RandomSystems/Lemma415.lean:652`
* `RandomSystems.CR18.GamePerf.winProb.eq_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.notWonProb.eq_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.notWonProbBehavior.eq_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_proj._proof_1_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_proj._proof_1_2` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_proj._proof_1_3` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_10` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_2` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_5` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_6` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_7` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_8` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._proof_1_9` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._simp_1_3` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.run_to_matches._simp_1_4` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.transcript_length_eq._proof_1_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.transcript_length_eq._proof_1_2` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.transcript_length_eq._proof_1_3` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.transcript_take._proof_1_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.winnerFactor.eq_1` — LIB — `RandomSystems/Lemma415.lean:?`
* `RandomSystems.CR18.GamePerf.winProb_le_weight` — LIB — `RandomSystems/MaxWinProb.lean:42`
* `RandomSystems.CR18.GamePerf.winProb_add_compl` — LIB — `RandomSystems/MaxWinProb.lean:62`
* `RandomSystems.CR18.PFunPDS.filterDom` — LIB — `RandomSystems/PDS.lean:105`
* `RandomSystems.CR18.PFunPDS.isProbDist_filterQueries_iff` — LIB — `RandomSystems/PDS.lean:130`
* `RandomSystems.CR18.PFunDDS.IsMBO` — LIB — `RandomSystems/PDS.lean:2939`
* `RandomSystems.CR18.PFunDDS.outputHistory` — LIB — `RandomSystems/PDS.lean:2945`
* `RandomSystems.CR18.PFunDDS.DDS.IsGame` — LIB — `RandomSystems/PDS.lean:2954`
* `RandomSystems.CR18.PFunDDS.historyEvaluator_pair_isGame_of_monotone` — LIB — `RandomSystems/PDS.lean:2964`
* `RandomSystems.CR18.MonotoneMBO` — LIB — `RandomSystems/PDS.lean:2995`
* `RandomSystems.CR18.isGame_filterDom` — LIB — `RandomSystems/PDS.lean:2999`
* `RandomSystems.CR18.monotoneMBO_filterDom` — LIB — `RandomSystems/PDS.lean:3006`
* `RandomSystems.CR18.monotoneMBO_filterQueries` — LIB — `RandomSystems/PDS.lean:3022`
* `RandomSystems.CR18.PFunDDS.winnerView` — LIB — `RandomSystems/PDS.lean:3104`
* `RandomSystems.CR18.PFunDDS.outputHistory._proof_1` — LIB — `RandomSystems/PDS.lean:?`
* `RandomSystems.CR18.PFunDDS.outputHistory._proof_2` — LIB — `RandomSystems/PDS.lean:?`
* `RandomSystems.CR18.PFunConverter.queryLimitApply` — LIB — `RandomSystems/PFunConverter.lean:763`
* `RandomSystems.CR18.PFunConverter.queryLimitApply_dom` — LIB — `RandomSystems/PFunConverter.lean:818`
* `RandomSystems.CR18.PFunDDS.output_congr` — LIB — `RandomSystems/PFunDDS.lean:90`
* `RandomSystems.CR18.PFunDDS.dom_fullyDefined` — LIB — `RandomSystems/PFunDDS.lean:185`
* `RandomSystems.CR18.PFunDDS.output_fullyDefined` — LIB — `RandomSystems/PFunDDS.lean:191`
* `RandomSystems.CR18.PFunDDS.keptPrefix_foldl_eq_append_of_mem` — LIB — `RandomSystems/PFunDDS.lean:259`
* `RandomSystems.CR18.PFunDDS.keptPrefix_eq_self_of_mem` — LIB — `RandomSystems/PFunDDS.lean:277`
* `RandomSystems.CR18.PFunDDS.keptPrefix_eq_self_of_mem_or_empty` — LIB — `RandomSystems/PFunDDS.lean:281`
* `RandomSystems.CR18.PFunDDS.output_fullyDefined_append_of_mem` — LIB — `RandomSystems/PFunDDS.lean:300`
* `RandomSystems.CR18.PFunDDS.mem_dom_filterQueries` — LIB — `RandomSystems/PFunDDS.lean:367`
* `RandomSystems.CR18.PFunDDS.ioTranscript` — LIB — `RandomSystems/PFunDDS.lean:387`
* `RandomSystems.CR18.PFunDDS.ioTranscript_map_fst` — LIB — `RandomSystems/PFunDDS.lean:399`
* `RandomSystems.CR18.PFunDDS.ioTranscript._proof_1` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.ioTranscript._proof_2` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript._proof_2` — LIB — `RandomSystems/PFunDDS.lean:?`
* `RandomSystems.CR18.PFunDDS.ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:39`
* `RandomSystems.CR18.PFunDDS.output_ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:46`
* `RandomSystems.CR18.PFunDDS.keptPrefix_ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:49`
* `RandomSystems.CR18.PFunDDS.output_fullyDefined_ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:54`
* `RandomSystems.CR18.PFunDDS.projT` — LIB — `RandomSystems/RelateGameDistinguishing.lean:67`
* `RandomSystems.CR18.PFunDDS.projT_append` — LIB — `RandomSystems/RelateGameDistinguishing.lean:72`
* `RandomSystems.CR18.PFunDDS.projT_inputs` — LIB — `RandomSystems/RelateGameDistinguishing.lean:75`
* `RandomSystems.CR18.PFunDDS.projT_outputs` — LIB — `RandomSystems/RelateGameDistinguishing.lean:78`
* `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:85`
* `RandomSystems.CR18.PFunDDS.verdict_ignoreMBO` — LIB — `RandomSystems/RelateGameDistinguishing.lean:103`
* `RandomSystems.CR18.winProb_fTransform` — LIB — `RandomSystems/RelateGameDistinguishing.lean:117`
* `RandomSystems.CR18.winProb_fTransform_game` — LIB — `RandomSystems/RelateGameDistinguishing.lean:132`
* `RandomSystems.CR18.winProb_ddToDDE` — LIB — `RandomSystems/RelateGameDistinguishing.lean:146`
* `RandomSystems.CR18.verdictMatches` — LIB — `RandomSystems/RelateGameDistinguishing.lean:156`
* `RandomSystems.CR18.distNotWonZ1` — LIB — `RandomSystems/RelateGameDistinguishing.lean:162`
* `RandomSystems.CR18.PFunPDS.ignoreMBO_filterDom` — LIB — `RandomSystems/RelateGameDistinguishing.lean:195`
* `RandomSystems.CR18.PFunPDS.ignoreMBO_filterQueries` — LIB — `RandomSystems/RelateGameDistinguishing.lean:205`
* `RandomSystems.CR18.mass_split` — LIB — `RandomSystems/RelateGameDistinguishing.lean:214`
* `RandomSystems.CR18.mass_mono` — LIB — `RandomSystems/RelateGameDistinguishing.lean:222`
* `RandomSystems.CR18.advantage_le_winProb_assemble` — LIB — `RandomSystems/RelateGameDistinguishing.lean:250`
* `RandomSystems.CR18.projT_run_outputs` — LIB — `RandomSystems/RelateGameDistinguishing.lean:301`
* `RandomSystems.CR18.verdict_iff_verdictMatches` — LIB — `RandomSystems/RelateGameDistinguishing.lean:318`
* `RandomSystems.CR18.verdictNotWon_eq_distNotWonZ1` — LIB — `RandomSystems/RelateGameDistinguishing.lean:335`
* `RandomSystems.CR18.distNotWonZ1.eq_1` — LIB — `RandomSystems/RelateGameDistinguishing.lean:?`
* `RandomSystems.CR18.blindQueryVector` — LIB — `RandomSystems/SwitchingLemma.lean:795`
* `RandomSystems.CR18.blindQueryList` — LIB — `RandomSystems/SwitchingLemma.lean:811`
* `RandomSystems.CR18.blindQueryList_length_le` — LIB — `RandomSystems/SwitchingLemma.lean:814`
* `RandomSystems.CR18.isPrefix_blindQueryList` — LIB — `RandomSystems/SwitchingLemma.lean:822`
* `RandomSystems.CR18.keptPrefix_gameOfDDS_filterQueries_functionEvaluator` — LIB — `RandomSystems/SwitchingLemma.lean:892`
* `RandomSystems.CR18.PFunDDS.transcript_input_get?_eq_env` — LIB — `RandomSystems/SwitchingLemma.lean:1030`
* `RandomSystems.CR18.PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true` — LIB — `RandomSystems/SwitchingLemma.lean:1075`
* `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list` — LIB — `RandomSystems/SwitchingLemma.lean:1124`
* `RandomSystems.CR18.blindMaxWinProb_filterQueries_monitored_le` — LIB — `RandomSystems/SwitchingLemma.lean:1778`
* `RandomSystems.CR18.seededConditionCGame_monotoneMBO` — LIB — `RandomSystems/SwitchingLemma.lean:1833`
* `RandomSystems.CR18.seededConditionCGame_totalOnNonempty` — LIB — `RandomSystems/SwitchingLemma.lean:1844`
* `RandomSystems.CR18.seededConditionCGame_isProbDist` — LIB — `RandomSystems/SwitchingLemma.lean:1852`
* `RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le` — LIB — `RandomSystems/SwitchingLemma.lean:1881`
* `RandomSystems.CR18.PFunDDS.transcript_input_get?_eq_env._proof_1_1` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true._simp_1_1` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true._simp_1_2` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.seededConditionCGame_isProbDist._simp_1_1` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_1` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_2` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_3` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list._proof_1_4` — LIB — `RandomSystems/SwitchingLemma.lean:?`
* `RandomSystems.CR18.PFunDDS.combineSys` — LIB — `RandomSystems/Theorem417.lean:34`
* `RandomSystems.CR18.PFunDDS.output_combineSys` — LIB — `RandomSystems/Theorem417.lean:43`
* `RandomSystems.CR18.gameEnhance` — LIB — `RandomSystems/Theorem417.lean:52`
* `RandomSystems.CR18.massAllFalse` — LIB — `RandomSystems/Theorem417.lean:70`
* `RandomSystems.CR18.massYAfalse_gameEnhance` — LIB — `RandomSystems/Theorem417.lean:81`
* `RandomSystems.CR18.mass_congr_support` — LIB — `RandomSystems/Theorem417.lean:127`
* `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame` — LIB — `RandomSystems/Theorem417.lean:142`
* `RandomSystems.CR18.massAllFalse_eq_massAfalse` — LIB — `RandomSystems/Theorem417.lean:176`
* `RandomSystems.CR18.massYAfalse_le_massAllFalse` — LIB — `RandomSystems/Theorem417.lean:201`
* `RandomSystems.CR18.massYAfalse_gameEnhance_eq_of_totalUpTo` — LIB — `RandomSystems/Theorem417.lean:212`
* `RandomSystems.CR18.MassYAfalseEqAt` — LIB — `RandomSystems/Theorem417.lean:269`
* `RandomSystems.CR18.MassYAfalseEqAt.symm` — LIB — `RandomSystems/Theorem417.lean:276`
* `RandomSystems.CR18.distNotWonZ1_congr_mass_at` — LIB — `RandomSystems/Theorem417.lean:287`
* `RandomSystems.CR18.winProbBehavior_congr_mass_at` — LIB — `RandomSystems/Theorem417.lean:301`
* `RandomSystems.CR18.advantage_le_winProb_of_massYAfalseEqAt` — LIB — `RandomSystems/Theorem417.lean:325`
* `RandomSystems.CR18.mass_singleton'` — LIB — `RandomSystems/Theorem417.lean:422`
* `RandomSystems.CR18.fTransform_fst_prod` — LIB — `RandomSystems/Theorem417.lean:431`
* `RandomSystems.CR18.gameEnhance_isProbDist` — LIB — `RandomSystems/Theorem417.lean:472`
* `RandomSystems.CR18.gameEnhance_totalUpTo` — LIB — `RandomSystems/Theorem417.lean:478`
* `RandomSystems.CR18.PFunDDS.verdict_iff_at_exact` — LIB — `RandomSystems/Theorem417.lean:501`
* `RandomSystems.CR18.PFunDDS.output_fullyDefined_ignoreMBO_combineSys_eq_of_totalUpTo` — LIB — `RandomSystems/Theorem417.lean:541`
* `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo` — LIB — `RandomSystems/Theorem417.lean:601`
* `RandomSystems.CR18.PFunDDS.verdict_ignoreMBO_combineSys_iff_of_totalUpTo` — LIB — `RandomSystems/Theorem417.lean:653`
* `RandomSystems.CR18.verdictProb_ignoreMBO_gameEnhance_eq_of_totalUpTo` — LIB — `RandomSystems/Theorem417.lean:669`
* `RandomSystems.CR18.PFunDDS.combineSys._proof_1` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.combineSys._proof_2` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.combineSys._proof_3` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._proof_1_1` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._proof_1_2` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._proof_1_4` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.outputBit_false_of_isGame._simp_1_3` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo._proof_1_1` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo._proof_1_2` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo._proof_1_3` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.gameEnhance.eq_1` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.massAllFalse_eq_massAfalse._proof_1_1` — LIB — `RandomSystems/Theorem417.lean:?`
* `RandomSystems.CR18.winsDDS` — LIB — `RandomSystems/WinProb.lean:32`
* `RandomSystems.CR18.winProb` — LIB — `RandomSystems/WinProb.lean:38`
* `RandomSystems.CR18.notWonProb` — LIB — `RandomSystems/WinProb.lean:46`
* `RandomSystems.CR18.winProb_add_notWonProb` — LIB — `RandomSystems/WinProb.lean:51`

</details>

## 6. MATHLIB — trusted, with flags

The 1348 Mathlib/core constants on the frontier are taken as correct. That is a real
assumption but not an interesting one. What matters is Mathlib lemmas whose *hypotheses* or
*conventions* carry the argument. These are the ones I would not wave through:

| Mathlib constant | used by | why it is load-bearing |
|---|---|---|
| `Finset.exists_subset_card_eq` + `Exists.choose` / `Exists.choose_spec` | `Counting.canonSubset`, `canonSubset_subset`, `canonSubset_card` | **`freshKeep` — and therefore the monitored condition `sopTightBad`, and therefore the whole bound — is defined by an unspecified choice.** The file says the choice is irrelevant "to every argument that only needs the count". Verify that: `card_avail_fresh_answer` uses only `canonSubset_card` and `canonSubset_subset`, but a reviewer should confirm no later step needs the choice to be *consistent across `y`*, since `freshKeep U V y` makes an independent choice for each answer `y`. |
| `Nat` truncated subtraction (`Fintype.card G - 2 * U.card`, `Fintype.card G - d`) with `omega` | `card_freshKeep`, `card_freshFiber_ge`, `goodCount`, `goodCount_step`, `card_good`, `card_goodAgree` | Every one of these is `0` in the degenerate regime `2k ≥ N` / `d ≥ N`, and `omega` will happily prove a truncated identity that is *not* the intended arithmetic identity. This is the single most likely place for a vacuously-true statement. |
| `Nat.eq_of_mul_eq_mul_left` | `card_goodAgree`, `card_good` | Both inductions *cancel* `(N−d)²` from an identity. The cancellation is only valid because `0 < N − d`, supplied by `omega` from `hlt`. If `hlt` were ever discharged from a false hypothesis the cancellation would license anything. |
| `List.reverseRecOn` | `card_goodAgree`, `card_good` | Induction on the query list *from the right*. The step case must correspond to appending a query; check the `nil` base case actually says "no queries, all `(N!)²` pairs survive" (it goes through `Fintype.card_prod` + `Fintype.card_perm`). |
| `Finset.card_eq_sum_card_fiberwise` | `card_avail_fresh` | Turns the total count into a sum over answers. The `t = univ` and `f = (uv ↦ uv.1 + uv.2)` choices are what make "`N` answers, `N−2k` each" come out; a wrong fiber map would still typecheck. |
| `Nat.factorial_mul_descFactorial`, `Nat.descFactorial_eq_prod_range` | `mass_good_eq_prod` | The `N! = (N−d)! · ∏_{k<d}(N−k)` identity that converts the counting into the product form the Weierstrass step consumes. Mathlib's `descFactorial` convention (`N.descFactorial d = N(N−1)…(N−d+1)`) must match the intended product. |
| `Real.toNNReal`, `Real.coe_toNNReal`, `Real.le_toNNReal_iff_coe_le` | `sop_randomness_expander_tight` | The `ℝ`-valued `sopEps` is pushed through an `NNReal`-valued endpoint. `Real.toNNReal` **clamps negatives to 0**; only `sopEps_nonneg` makes the round trip an identity. |
| `Classical.dec` | `sopFresh_decidable`, `sopTightBad_decidable` | The game `seededConditionCGame` emits `decide (bad a l)`. With a `Classical.dec` instance the emitted bit is still the right Prop, but nothing *computes*; and any `simp` step that normalises `decide` must be checked against the instance actually in scope, since a second, different `Decidable` instance would make `decide` a different function. `sopTight_condEquiv` has two `by simp` steps on exactly this boundary. |
| `Fintype.card_perm`, `Fintype.card_prod`, `Fintype.card_fun` | `card_goodAgree`/`card_good` base cases, `mass_agree_and_good` | `|Perm G| = N!`, `|G → G| = N^N`. These fix the *normalisation* of both uniform distributions. A mismatch here would rescale the whole bound. |
| `Finset.card_image_of_injective` (with `p.1.injective`) | `card_goodAgree`, `card_good`, `card_fresh_pair_fiber` | Supplies `|U| = |V| = k`, the hypothesis `card_freshKeep` needs. Without injectivity the balance identity is false. |
| `Finset.filter_congr` (6 uses) | the two inductions, `mass_agree_and_good` | Every one is an event-rewriting step. A `filter_congr` that rewrites to a *different but equinumerous* event is invisible to the kernel and fatal to the meaning. |

Everything else on the frontier is ordinary `Finset`/`List`/`Nat`/`Real` plumbing
(`Finset.mem_filter`, `List.mem_toFinset`, `positivity`/`nlinarith` byproducts, instance
resolution). Full list with use counts in `review/sop-dag.tsv`.

## 7. What this document does *not* establish

It is a map, not a verdict. In particular it does not check that:

* `Dist`, `mass`, `maxAdvantage`, `filterQueries`, `CondEquiv` mean what CR18 / MaPiRe07 /
  Maurer13b mean by those words — that is slices 1, 5 and 6;
* the balance identity is true — that is slice 3;
* the bound is non-vacuous in the regime it claims (`q` past `√N`) — that is slices 3 and 4;
* the `ε` exhibited is the `≈ q³/3N²` the docstring advertises — that is slice 4.

