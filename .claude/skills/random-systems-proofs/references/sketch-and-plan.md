# Stages 1–3: sketch, plan, reuse

## Contents

- Stage 1 — the sketch (Lean-free)
- Stage 2 — the obligation DAG
- Stage 3 — the reuse search
- What you carry into Lean

---

The three stages before Lean. They exist because Lean does not tell you what you are proving
— it tells you whether what you wrote type-checks. A bound that was never provable as stated
survives a surprising amount of tactic work before it fails.

In-repo precedent: `sequence-hash/sketches/*.md` and `sequence-hash/PLAN.md` §0.5, where this
discipline is enforced by a dispatch script that **fails loudly** if the sketch-adaptation
rule is missing. This reference generalizes it to any RS proof.

---

## Stage 1 — the sketch

**Artifact:** a markdown file. Prose and LaTeX. **No Lean.**

Put it next to the work — `sketches/<result>.md` beside the target module, or in the scratch
directory for a one-off. It is a working document, not a deliverable; it is allowed to be
wrong, and it is much cheaper to be wrong here.

### Template

```markdown
# <result name> — pen-and-paper sketch

<One paragraph: what is being proved and by what route. State the technique
 in the first three sentences.>

## (a) Objects

- `X`, `Y`, … — the carriers, with the existing library type each maps to.
- Real system  : <definition>   ⟵ existing object, or new (say which)
- Ideal system : <definition>   ⟵ existing object, or new
- Parameters   : q (queries), L (blocks), ε, …

## (b) The claim

    Δ(⌈q⌉ Real, ⌈q⌉ Ideal) ≤ <exact bound>

Every parameter bound. No "up to constants".

## (c) The argument

<Prose. What is the bad thing? Why do the two worlds coincide off it?
 Where does the loss come from? This is the part a reader of the paper
 would recognize.>

## (d) Technique, and the one rejected

Technique: <family + variant>, entering at <endpoint name>.
Rejected:  <the other plausible door>, because <reason>.

## (e) Adaptation table            [required when the argument comes from a paper]

| term / bad event in the source | kills / shrinks / leaves | why |
|---|---|---|
| … | leaves | cascade-inherent; our separation does not touch it |
| … | kills  | domain separation makes this event vacuous (⟨lemma⟩) |
| … | shrinks| our L bounds the range to … |
```

### The rule this enforces

**The source paper is a template, not the answer.** Blunt transcription of a paper's bound
and bad-event list is the most common way a formalization inherits terms that this
construction's own structure makes vacuous — and it is invisible afterwards, because the
extra terms still prove, just loosely.

`PLAN.md` §3c states it for SequenceHash and the shape generalizes: for **every** bound term
and **every** bad event, say whether a known specificity **kills / shrinks / leaves** it, and
why. Be honest about what remains — separation typically kills bookkeeping and aliasing
events, not the construction's inherent loss.

Naming a rejected technique is not a formality. `sequence-hash/sketches/A2` opens by stating
that the proof is *not* an H-technique proof and that no H-coefficient object belongs in it —
which is what stopped the formalization from drifting into the wrong layer.

### Reading the source

**Papers are read visually.** Do not grep or extract a PDF's text layer — extraction fails
silently in this repo's paper set, returning zero hits for terms that are plainly in the
document. Open the pages.

**Verify the passed-forward premise.** If the argument rests on a "design decision" attributed
to a source, check the source actually poses it before building on it.

### Gate

The sketch names the technique and the exact bound. If it cannot, the mathematics is not
understood yet — and Lean will not help you understand it.

---

## Stage 2 — the obligation DAG

**Artifact:** a node list with dependencies. Half a page.

The node set is **not invented** — it is *determined* by the technique you chose. The
technique references give it per endpoint:

| technique | nodes |
|---|---|
| H, `eq_on_good` | `good_transcript_equality`, `ideal_bad_probability` |
| H, `ratio_of_good` | `good_transcript_ratio`, `ideal_bad_probability` |
| H, `partition` | `cell_defect_ratio`, `weighted_cell_bound` |
| CE, packaged | `conditional_equivalence`, `blind_schedule_bad_mass` |
| coupling | `coupling_marginals`, `disagreement_bound` |
| union bound | `bad_event_cover`, `bad_event_leaf_sum` |

Additional nodes come from your sketch's own intermediate lemmas.

### Node format

```
<name>
  statement : <mathematics, not Lean>
  class     : [LIB] | [ROUTINE] | [CREATIVE]
  depends   : <other node names>
  verdict   : <filled at stage 3>
```

### Why the DAG and not a list

**Fill order is leaves-first.** A creative node proved before its dependencies is a node
proved against assumptions you have not fixed yet, and that is exactly where statements
silently drift — you end up with a true lemma that does not compose.

A typical CE proof:

```
  bound
   ├── conditional_equivalence        [CREATIVE]
   │    ├── fiber_balance             [CREATIVE]   ← the real content
   │    └── shift_preserves_good      [CREATIVE]
   ├── blind_schedule_bad_mass        [CREATIVE]
   │    ├── bad_event_cover           [CREATIVE]
   │    └── bad_event_leaf_sum        [CREATIVE]   ← the counting
   ├── bad_monotone                   [ROUTINE]
   └── isProbDist ×2, TotalOnNonempty [ROUTINE]
```

Two leaves carry the whole proof. Everything else is plumbing or citation — and you know that
before writing a line of Lean.

### Gate

Every node has a statement and a class. **If every node is `[CREATIVE]`, the routing is
wrong** — you are about to hand-build something the library packages. Go back to the routing
questions and find the packaged endpoint.

---

## Stage 3 — the reuse search

**Artifact:** exactly one verdict per node.

- **REUSE `Name`** — exists and applies as-is. Cite it; do not restate it.
- **ADAPT `Name`** — exists but is too specific. **Generalize it in place, public.**
- **NEW** — genuinely absent, *with a one-line record of what you searched*.

### Search order

Cheapest and highest-yield first. Stop at the first hit.

| # | tool | for |
|---|---|---|
| 1 | **`CHEATSHEET.md`** (repo root) | the curated index — "By goal — what are you trying to do?" and "REUSE THIS — do NOT re-derive". Covers `Δ` algebra, carriers and ideal objects, converters/DPI, switching and birthday, condition-equivalence and the blind game, `Dist` facts, the tactic families, AC indifferentiability, H-technique endpoints |
| 2 | `grep` over `RandomSystems/`, `RandomSystemsCC/`, `../abstract-crypto/` | names and idioms; also finds the *worked example* you should be copying |
| 3 | `lean_local_search` | fast local declaration search — **before guessing a name** |
| 4 | `lean_state_search` | goal → closing lemmas |
| 5 | `lean_loogle` | mathlib by type pattern |
| 6 | `lean_leansearch` / `lean_leanfinder` | mathlib by natural language / concept |
| 7 | `lean_hammer_premise` | premise selection when you cannot name the shape |

Steps 5–7 matter more than they look: a good share of `[CREATIVE]` counting nodes bottom out
in a mathlib fact about `Finset` cardinalities, `Nat.choose`, or products of `NNReal` — and
mathlib is not searched by grepping this repo.

### The two sharp rules

**Generalize in place; never a specialized copy.** If the fact you need is not specific to
your scheme, do not prove a narrow version next to your proof. Widen the existing lemma where
it lives, keep it public, and let both callers use it. A near-duplicate is worse than the
detour, because it splits the lemma's future maintenance and the next person finds the wrong
one.

**Never `private`, never a local generic helper.** If a general fact is genuinely missing, add
it *public to the framework*, not to the scheme file. A `private` lemma that someone later
needs forces a re-derivation around it.

### Gate

Every node has a verdict. **A `NEW` with no search record is not a verdict** — it is the
default answer of an agent that did not look, and it is how the library grows duplicates.

---

## What you carry into Lean

After stage 3 you have: the exact bound, the endpoint name, the obligation names, a fill
order, and for each obligation either a lemma to cite or a statement to prove. Stage 4 is then
mechanical — write the `refine`, `sorry` the creative leaves, compile.

If stage 4's goals do not match your DAG, **stop**. Either the endpoint is not the one you
planned, or the plan was wrong. Nothing in Lean will warn you about this; the DAG is the only
check there is.
