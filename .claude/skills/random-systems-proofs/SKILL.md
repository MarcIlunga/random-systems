---
name: random-systems-proofs
description: "Routes and structures Random Systems / Constructive Cryptography proofs in Lean 4. Use when proving, finishing, or repairing ANY theorem in the RandomSystems or RandomSystemsCC libraries — an advantage bound (Δ(S,T) ≤ ε), a PRF/PRP/MAC/indifferentiability claim, a lemma that will not close, a `sorry` to discharge, or a proof broken by a refactor. Also use when asked to prove a named theorem in a RandomSystems file, or to formalize a security proof from a paper. Picks the technique (H-technique, conditional equivalence, coupling, winnability, counting), names the obligations it leaves, points at the reuse index before you write anything new, and says what shape the finished proof should read as."
---

# Random Systems proof workflows

Every security statement in this library is an advantage bound, and the library proves them
with a **closed set of seven technique families**. The shape of a proof is knowable before it
is attempted — so most of the work is knowing *what you owe* and *what already exists*, not
writing tactics.

**Seven stages, four of them before Lean.** Each has a required artifact and a gate. Do not
skip a gate; the gates are the whole mechanism.

Copy this checklist into your first response and tick items as you go:

```
- [ ] 1. SKETCH        mathematics only. NO Lean, NO library search.
- [ ] 2. DAG           obligations from the technique; class each [LIB]/[ROUTINE]/[CREATIVE]
- [ ] 3. REUSE SEARCH  per node: CHEATSHEET → grep → local search → mathlib
- [ ] 4. AUDIT         per definition: QUOTE the source · SUM it · check the number
- [ ] 5. SKELETON      apply the endpoint, `sorry` every creative leaf, COMPILE
- [ ] 6. FILL LEAVES   in DAG order, leaves first
- [ ] 7. RECEIPTS      axiom audit · no sorry · report reused vs. generalized
```

### Stage 4 exists because typechecking cannot see a wrong definition

**A definition that misreads the source still typechecks, still composes, and still lets the
skeleton build green.** The signal that would catch it — a leaf that will not close — arrives
only when someone attacks that leaf, by which time it has dependents. This is the single most
expensive failure mode in this repo, measured: in one formalization of a 3-page proof, **four
separate definitions/statements were false against the source**, each surviving until a proof
attempt or a review question forced a re-read.

So before proving anything against a definition that claims to be the source's, do both:

1. **Quote the source in the docstring.** Not a paraphrase — the sentence. To write the quote
   you must find it, and *that is the check*. Three of the four measured errors were content
   sitting in a different modality from where the eye was: the multiset was displayed but its
   index was defined in a sentence three paragraphs earlier; the figure was a complete-looking
   table but the caveat that halves a term was in the prose beneath it.
2. **Sum it and compare the number.** Aggregate your definition the way the source aggregates
   it and check you get the source's constant. This is ~30 seconds and it tests exactly the
   property types cannot. The measured catch: an un-gated cost table summed to `4σ` where the
   paper had `2σ` — found *before* the proof, unlike the other three.

Corollaries worth stating separately:

- **Generality in a definition is free; in an obligation's conclusion it is fatal.** Quantifying
  a bound over an arbitrary distribution, or dropping a side condition from a table, *strengthens*
  the claim past truth. Two of the four measured errors were exactly this, and both felt like
  good engineering when written. If the source's `Pr` is one specific distribution, yours is too.
- **Never write the Lean from your summary of the source.** Transcribe with the page open, one
  declaration at a time. Consulting the source only when something breaks is what produced all
  four.

### Stage 1 is Lean-free. This is the rule agents break most.

**Do not open a Lean file, grep the library, or look up a lemma name until the mathematical
sketch exists.** Measured failure: agents burn most of their opening context surveying Lean
before they know what they are proving.

The cost is not just tokens. Searching first **anchors you to what the library has instead
of what is true**. You start assembling the proof the existing lemmas suggest, rather than
working out the argument and then asking what would implement it. That is how you inherit a
loose bound: the first endpoint you find becomes the ceiling.

Library search is **stage 3**, and it is deliberately after the DAG, so that you search for
things you have already decided you need.

**Missing infrastructure is expected, not a constraint.** You may add definitions, lemmas,
and general framework facts freely — public, in the right module (see stage 3). Never let
the absence of a lemma decide the mathematics. If the argument needs an object the library
does not have, build it; the sketch decides, not the tree.

### How much freedom at each stage

| stage | freedom | why |
|---|---|---|
| 1 SKETCH | **high** — open field | many routes are valid; this is where the creativity lives |
| 2–3 DAG, reuse | medium | the node set follows from the technique; the search order is fixed |
| 4 SKELETON | **low** — narrow bridge | one endpoint, exact arguments, must compile |
| 5–6 fill, receipts | medium | leaves-first order is fixed, tactics are yours |

Do not import stage-4 caution into stage 1. A sketch that only considers what is already
formalized is not a sketch.

Stages 1–3 are in [sketch-and-plan.md](references/sketch-and-plan.md) — **read it before
starting a proof.**

**Nothing enforces any of this.** No goal-shape tactic, no typeclass, no hook. That is a
deliberate choice, and it has a measured consequence: in a two-dispatch run of 67 tool calls,
an agent that had read `sketch-and-plan.md` produced **zero** sketch files and went straight
from grepping to editing Lean. The gates are prose a confident model will skip.

So treat the sketch as **your first deliverable, not a gate you pass** — write
`sketches/<result>.md` and keep it updated as the proof moves. Its value is not compliance:
it is the only artifact that makes your routing decision reviewable afterwards. A proof
whose reasoning exists only in a transcript cannot be checked, corrected, or reused.

## When to Use

- Proving a new bound `Δ(⌈q⌉ Real, ⌈q⌉ Ideal) ≤ ε` in `RandomSystems` / `RandomSystemsCC`.
- Repairing a `sorry`, a proof broken by a refactor, or a bound that will not close.
- Deciding which technique a paper's argument corresponds to before formalising it.
- Reviewing a proof for silent slack (loose metric form, wrong H variant, unpackaged CE).

## When NOT to Use

- Pure Mathlib goals with no RS content (`ring`, `omega`, `Finset` algebra) — just prove them.
- Defining systems, converters, resources, or protocols with no bound attached — that is
  the `cc-constructions` skill's territory (it also decides what each RS leaf must SAY
  before handing it here).
- Layer questions above Random Systems (CC composition, AC, resource lifting) — use
  `cc-constructions`.
- The creative combinatorics itself once you are inside a named counting node. Get there with
  this skill, then think freely — that node is where budget *should* go.

## Routing — stage 1's central question

```
0. Is the distance ZERO?        → family I. CHECK FIRST. δ = 0 beats every δ ≤ ε.
1. Can Δ be split or stripped?  → family II reshape (hybrid / DPI / restriction).
2. What is the "bad thing"?     → family III — THE choice point:
     a bad TRANSCRIPT           → H-technique              (references/h-technique.md)
     a CONDITION the adversary triggers, adaptive/stateful
                                → conditional equivalence  (references/conditional-equivalence.md)
     DISAGREEMENT under shared randomness
                                → coupling                 (references/reshape-and-exact.md)
     the adversary WINNING a given game
                                → winnability              (references/reshape-and-exact.md)
3. Discharge the probability    → family VI counting       (references/counting.md)
4. Arithmetic                   → cr18_arith / cr18_algebra / cr18_close
```

Two omissions to pre-empt, both common:

- **Family I gets skipped in favour of a bound.** Behavioural quotient, relabelling
  invariance, non-adaptive sufficiency — check for exact equality first.
- **Family II is the step most often omitted.** Attacking `Δ(Real, Ideal)` head-on when a
  hybrid through an intermediate system splits it into two easy halves is the single most
  common self-inflicted difficulty in this repo.

State the technique **and the alternative you rejected, with a reason**. A sketch that cannot
say why the other door is wrong has not chosen a door.

### Before you commit: which route is this module already on?

**Read `CHEATSHEET.md` §9's route warning as part of ROUTING, not just reuse.** It says:

> *"This layer is a SEPARATE proof route, used for R4 only. It is **not** the Gaži/CBC
> pure-`Δ` (condition-equivalence) route of sections 1–5. **Do not mix the two**: a proof is
> either a `Δ`/blind-game proof or an H-technique/transcript-distance proof."*

A module is architected for one route. Proving a CE-architected theorem by the H-technique
*can* succeed — it was done, axiom-clean — and still cost ~90 lines of glue producing zero
new mathematics, because every non-citation line was an artifact of the transcript surface.

So the routing question is not only "which technique fits the mathematics" but **"which
route is this file already built for"**. Check the module's existing endpoints and the §9
warning before committing. Going against the grain is occasionally right; doing it by
accident never is.

## The obligation ledger

Every endpoint's hypotheses fall into exactly three classes. Classify at stage 2.

| tag | meaning | what you do |
|---|---|---|
| `[LIB]` | a named library theorem supplies it | cite the name. **Never re-prove.** |
| `[ROUTINE]` | a named tactic closes it | run the tactic. **If it fails, fix the model, not the proof.** |
| `[CREATIVE]` | genuinely new mathematics | this is the work |

If every node is `[CREATIVE]`, the routing is wrong — go find the packaged endpoint.

### The `[ROUTINE]` tactics

| tactic | discharges | lives in |
|---|---|---|
| `cr18_total`, `htechnique_total` | `KStepTotal S q`, `TotalOnNonempty S` | `TotalityTactics`, `HTechnique/Tactics` |
| `cr18_prob` | `isProbDist` | `CR18TacticsCore` |
| `cr18_routine` | standing side conditions | `CR18TacticsCore` |
| `cr18_filter` / `cr18_game` / `cr18_transcript` | `⌈q⌉` filter, `gameOf`/MBO, transcript shape | `CR18Tactics` |
| `htechnique_compress` | repeated queries → canonical injective tuple | `HTechnique/Tactics` |
| `htechnique_adv_le` | `advPRF/advPRP/Adv ≤ ε` shell → pointwise bound | `HTechnique/Tactics` |
| `cr18_arith`, `cr18_algebra`, `cr18_close` | the arithmetic tail | `CR18Tactics{,Core}` |
| `inferInstance` | `FiniteTranscriptSpace`, `DiscreteTranscriptSpace` | — |

**Check the target file imports the tactic's module.** These are not globally available:
`CBCMAC.lean` imports none of the tactic modules, so `cr18_total` is simply unavailable
there and its obligations must be discharged by hand or by adding the import. A tactic that
does not resolve is an import problem, not a licence to hand-roll everything.

**When the tactic IS available and fails, that is a modelling bug, not a proof to write.**
`cr18_total` fails ⇒ the system carries partiality it should not. `cr18_prob` fails ⇒ the
weight is not normalised. Instance search fails ⇒ the carrier is wrong. Hand-proving around
any of these buries the bug inside a proof where nobody will find it.

## Stage 4 — the skeleton

Apply the endpoint with a named hole at every creative obligation, `sorry` each, **compile**.

```lean
theorem my_bound … : Δ(⌈q⌉ Real, ⌈q⌉ Ideal) ≤ ε := by
  refine RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good
    Real Ideal Bad δ (by cr18_total) (by cr18_total)
    ?good_transcript_equality ?ideal_bad_probability
  case good_transcript_equality => sorry
  case ideal_bad_probability    => sorry
```

Named metavariables give you `case` labels. **Nothing checks the obligation count** — that is
what your stage-2 DAG is for. If the goals that appear do not match the DAG, stop: either the
endpoint is not the one you planned, or the plan was wrong.

Do this even for single-obligation proofs. A skeleton that does not compile means the bound
is wrong as stated, the endpoint is wrong, or a routine hypothesis is unavailable — all cheap
now, expensive in two hours.

The one measured exception: when every node triaged `[LIB]`, there is no intermediate
skeleton state — you write the finished `calc` directly. If your DAG has no `[CREATIVE]`
node, skip to writing the proof.

## Proof shape — the proof must LOOK like the argument

A cryptographer's proof is a **chain of hops**: a sequence of quantities, each step
justified. A Lean proof that closes the goal but hides that chain is a worse artifact than
a paper proof, and this is where machine proofs most often fail their readers.

Measured failure: an H-technique proof of the CBC-MAC bound closed correctly but buried its
chain in nested `refine le_trans (…) ?_`. The quantities never appeared as a sequence, and
nothing in it revealed which of the five H analyses was running. Same mathematics, unreadable.

**1. The top level is a `calc`, one line per hop.** Nested `le_trans` is the same
mathematics with the quantities deleted.

```lean
calc (Δ(⌈q⌉ Real, ⌈q⌉ Ideal) : ℝ)
    ≤ Adv[q](R, I)              := ⟨the Δ → Adv bridge⟩
  _ ≤ (badMassBound : ℝ)        := ⟨the H endpoint, fed good_ratio and bad_probability⟩
  _ ≤ ⟨the headline bound⟩      := ⟨the arithmetic lemma⟩
```

The reader now sees the hops — `Δ → Adv → bad mass → headline` — with a citation on each.
Four quantities, three justified steps. That is what a paper displays, and it is what a
reviewer checks.

**2. Creative obligations are named `have`s stated BEFORE the `calc`.** Ingredients first,
then assembly. Use the ledger names — `good_ratio`, `bad_probability`, `pointwise_ratio`,
`conditional_equivalence`, `bad_event_cover`. Never inline a forty-line `case` inside a hop.

**3. The bad event gets a name.** `set Bad := …`, or a top-level `def` when it is reused.
Never an anonymous lambda buried in an argument position — a reader must be able to point
at it and a later proof must be able to cite it.

**4. Make the variant visible.** State in one line which analysis is running and why —
especially the degenerate cases. "`Bad = ∅`, so the ratio is uniform and this is the
one-cell variant" is the difference between a reader following you and reverse-engineering
you.

**5. Hoist routine plumbing.** `isProbDist`, `TotalOnNonempty`, `KStepTotal`, normalization
receipts go in a block at the top, or are discharged by tactic. They must never sit between
two mathematical hops.

`RandomSystemsCC/ControlledNaturalLanguage.lean` renders this shape as paper prose for
H-coefficient proofs — structure sentences that leave `?good_ratio` / `?bad_probability` as
named goals. Read it for the target shape even if you do not adopt the syntax; `DESIGN.md`'s
stated aim for it is "proofs read like pen-and-paper".

## Discovering the surface

Read the library from the environment, never from memory:

| where | for |
|---|---|
| **`CHEATSHEET.md`** (repo root) | the curated reuse index, organized by goal. **Always first.** |
| **`RandomSystems/LanzenbergerChain.lean`** | **thesis-item → declaration name table.** One row per numbered item of the thesis's Ch. 2, plus the source errata it found. Read this *before* concluding a thesis result is missing — measured failure: an agent twice asserted "no theorem says `Adv` depends only on the behavior" when `behavior_equivalent_iff_transcript_equivalent` was in the tree. Caveat: the file does not currently compile (unfinished `dist-real` migration), so items behind `BoundedAttainment` are written but not auditable. |
| `grep` over `RandomSystems/`, `RandomSystemsCC/`, `../abstract-crypto/` | names and idioms |
| `lean_local_search` | fast local declaration search — **before guessing a name** |
| `lean_state_search` | goal → closing lemmas |
| `lean_loogle` / `lean_leansearch` / `lean_leanfinder` | mathlib by type / language / concept |
| `#print axioms`, `lean_verify` | the stage-6 receipt |

**Dev loop:** iterate with the **`lean-lsp` MCP** — `lean_goal` gives the actual proof state,
which is the whole game. Fall back to `lake env lean <file>`. `lake build` only for stale
oleans or a final gate. Put this in any subagent brief.

## Modelling rules that keep the obligation count down

Each of these was learned by getting it wrong first.

**The transcript law is a pushforward.** `transcriptDist S e m = fTransform (fun s
=> transcript s e m) S`. Once you see that, DPI (`δ_fTransform_le`, thesis Lemma
2.7) is the single tool behind three separate-looking steps:

| push along | gives |
|---|---|
| `tr(·,e)` | `Adv ≤ Δ` — Thm 2.31's easy half is *one* DPI application |
| `verdict` | `maxAdvantage ≤ Adv` — why the verdict can be dropped from the model |
| a forgetful projection | any "give the adversary extra information" step |

**To give the adversary more information, refine the observation — never build a
new system.** A second system with a wider alphabet forces a *simulation*
obligation relating two systems' transcripts. Pushing the *same* PDS (or its key
distribution) forward along a finer map, and recovering the plain law by
`Prod.fst`, makes the whole step one `δ_fTransform_le`. Corollary: information
recorded in the observation is invisible to the environment (whose queries are
functions of *responses*), so "revealed after all queries" is structural rather
than a side condition on the environment.

**Orientation is inherited from `δ`, which is asymmetric at unequal weight**
(thesis Def 2.4's own remark). `Adv S T` is the excess of `S` over `T`, i.e.
`Δ(T, S)`. The naive `Adv S T = Δ(S, T)` is *refutable* at sub-distribution
weight. **Ideal system first.**

**`NonNeg` side conditions are Def 2.4 content, not bookkeeping.** `δ` sums over
`supp μ`; that equals Def 2.4's sum over the whole carrier only when the second
argument is non-negative. Omit it and partition-additivity is false, not merely
unprovable.

**A `Fintype` requirement on an H lemma is about `statDist`, not about H.**
Symmetrising needs equal weights and `Finset.univ`; the one-sided `δ` needs
neither. If the carrier is infinite (e.g. `List (X × Option Y)`), state the
`δ`-native version — it has *strictly weaker* hypotheses.

**Dependent-type friction is a modelling smell.** Totality and width-polymorphism
at layer 1 (`sub` reads zeros past the end; `blocks` accepts any width) let
predicates on malformed inputs be *garbage rather than ill-typed*, which is
exactly what a total `Bad` needs. When casts do threaten, name the stuck
intermediate rather than casting around it.

**CR18 numbering in a docstring is not evidence of thesis conformance.**
Declarations are named after CR18; only some carry a "Lanzenberger Def 2.x is this
plus…" note. Check the thesis before treating a CR18 number as the model.

## Rationalizations to Reject

Each is a real failure mode in this codebase, with the tell.

**"I'll start in Lean and work out the math as I go."**
No. The sketch is stage 1 because Lean does not tell you what you are proving — it tells you
whether what you wrote type-checks. Bounds that were never provable as stated survive a
surprising amount of tactic work before failing.

**"I'll search for existing lemmas when I hit a wall."**
Too late. By then you have written the specialized copy. Search at stage 3, per node, before
any Lean.

**"This helper doesn't exist, I'll write it."**
Did you check `CHEATSHEET.md`, then grep, then `lean_local_search`, then loogle? A `NEW`
verdict with no search record is not a verdict. The library is ~6,000 declarations with 189
notations; a near-duplicate is worse than the detour because it splits future maintenance.

**"The general version is in the tree but it's stated for the wrong type."**
**Generalize it in place, public.** Do not write a specialized copy, do not write `private`,
do not mint a local `myscheme_*` helper for a scheme-agnostic fact.

**"The library doesn't have this thesis result."**
Did you read `RandomSystems/LanzenbergerChain.lean`? It is a name table for every
numbered item of the thesis's Chapter 2. A `MISSING` verdict without a hit in that
file is not a verdict. Measured failure: the same non-existent gap asserted twice
in one session.

**"I'll model the extra information as another system / another query."**
Then you owe a simulation, and — if the information is meant to be revealed late —
a spurious ordering condition on the environment, plus a strictly stronger
adversary than your bad-event analysis can support. Refine the observation map
instead. See the modelling rules above.

**"The augmented object can appear in the statement."**
No. A statement must not mention proof devices. Stating the bound about the
augmented worlds *hides* the augmentation-soundness obligation; making the
statement honest is what surfaces it.

**"I read the paper carefully, so my definition matches it."**
Then quote it. If you cannot produce the sentence your definition encodes, you are working from
a summary — see stage 4. Figures and displays are the *least* reliable thing to transcribe from,
because their qualifications live in the surrounding prose.

**"This definition is more general, which can only help."**
It cannot. A generic parameter in a bound's *conclusion* asserts the bound for instances the
source never claimed, and those instances are usually counterexamples. Ask what the source's
quantity actually ranges over and match it exactly.

**"It typechecks and the skeleton composes, so the modelling is right."**
Composition is preserved by false leaves — that is what makes this failure expensive. `A → B`
being checked says nothing about `A`. Run stage 4's sum.

**"The paper states this bound, so I'll formalize that bound."**
The paper is a **template, not the answer**. For every bound term and every bad event, say in
the adaptation table whether a known specificity of *this* construction kills / shrinks /
leaves it, and why. Inherited-but-vacuous terms are invisible later — they still prove, just
loosely.

**"I'll reason about what an adaptive distinguisher can do here."**
You took the wrong door. Every packaged endpoint has already performed that reduction —
conditional equivalence's blind reduction hands you a **fixed** query schedule. Go back.

**"I'll just manipulate the statistical distance directly."**
You skipped family II. Hybrid, data processing, query restriction — check those first.

**"`cr18_total` isn't closing it, I'll prove totality by hand."**
No. The system is defined wrong. Fix the definition.

**"The partition variant is more general, I'll use that to be safe."**
Generality costs obligations. Take the **most special** variant that applies. Reaching for
`partition` when `eq_on_good` holds manufactures two extra creative goals.

**"The ratio direction probably doesn't matter."**
It does. Ideal on the left, real on the right: `(1 - ε) * ideal ≤ real`. Reversed, it
type-checks against nothing.

**"The `≤` metric form is fine."**
Only if you checked. `maxEDist ≤ ofReal Δ` holds unconditionally, but **equality** holds on
every shared-domain object. Accepting `≤` where `=` is available is silent slack in a
headline bound.

**"This fix didn't work, let me try a variant."**
After the *second* failed fix of the same goal, stop patching and restate. The difficulty is
usually self-inflicted: wrong statement shape, or hand-rolled infrastructure duplicating
something already in the tree.

**"I proved a lemma that makes the goal go through."**
Axiom-audit it. A declaration whose own text is `sorry`-free can still rest on `sorryAx`
through a helper.

**"It compiles and it's axiom-clean, so it's done."**
Not if the argument is invisible. A nested `refine le_trans (…) ?_` stack proves the same
theorem as a `calc` and communicates nothing — no sequence of quantities, no indication of
which analysis is running. Compiling is the floor, not the deliverable. See **Proof shape**.

**"The technique closed the goal, so it was the right technique."**
Closing proves viability, not fit. The H-technique closed a CE-architected bound axiom-clean
and still cost ~90 lines of glue for zero new mathematics. Check `CHEATSHEET.md` §9 for which
route the module is on *before* committing, not after.

## References

- [sketch-and-plan.md](references/sketch-and-plan.md) — **stages 1–3.** Sketch template,
  adaptation table, the obligation DAG, the reuse-search order and verdict format.
- [creative-search.md](references/creative-search.md) — **when stage 1 is the hard part.**
  Parallel exploration: when to fan out, the six angles, how to brief a scout, effort
  scaling, synthesis. Read this whenever the bound is unknown or must beat a published one.
- [h-technique.md](references/h-technique.md) — the three axes, the five analyses, the exact
  creative nodes per variant.
- [conditional-equivalence.md](references/conditional-equivalence.md) — packaged vs. raw door,
  the CBC-MAC worked example.
- [counting.md](references/counting.md) — the six doors into combinatorics, structure graphs,
  sum-of-permutations, birthday tails.
- [reshape-and-exact.md](references/reshape-and-exact.md) — families I, II, IV, V; coupling;
  winnability; the metric receipt.

Full derivation, with per-technique graphs and the deferred Lean-enforcement design:
`skills/PROOF-WORKFLOWS.md`.
