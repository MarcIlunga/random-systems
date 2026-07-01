# Can these be used as slides to present a Lean proof, with show-hidden-details?

The question driving the whole design. Short answer:

> **Qualified YES** — as an **interactive proof browser** ("living slides") for
> small-to-medium proofs, with a bounded default depth. The *show-hidden-detail*
> and *goal-state-on-hover* features are the genuine strength and map directly
> onto presentation use. **Qualified NO** to the stronger reading "auto-generate
> a narrated presentation": symbolic informalization cannot synthesize a thesis,
> motivation, or "the key idea." Those remain the author's to add.

This answer survived two contrarian rounds (see `CONTRARIAN_LOG.md`, finding 7),
which is why it is *qualified*, not an unconditional yes.

## 1. Why YES — the talk's own demo is exactly this

The source talk *demonstrates* the feature on slides 23–24 and 27:
- **Slide 24**: "Imagine clicking a `⊕` and seeing further proof. To go
  arbitrarily deep, we need a formalized proof!" — a collapsible structured proof.
- **Slides 22/24**: a "Current proof state" box (context + goal) shown for a step
  — proof-state-on-hover.
- **Slide 27**: a full natural-language structured proof with inline `⊕`/`⊖`
  expanders that "could answer any question you have about the proof."

These are presentation affordances. Our design realizes them as first-class
`Explanation` nodes:

| Presentation need | `Explanation` primitive (§5) | UX (§8) |
|---|---|---|
| Show only the top-level argument | `detail summary expanded`, collapsed | the default slide view |
| Reveal a sub-proof on demand | `detail`, expand on `⊕` click | drill-down, arbitrarily deep |
| Show the context behind a step | `goalState` in a `tooltip` | hover reveals the proof state |
| Reveal a definition | `clickable label reveal` | click a term → its definition |
| Display an equation | `displayMath` | centered multiline math |

Because the proof is *formalized*, every `⊕` has real content to show — there is
no "…and the rest is routine" dead end. That is precisely what a textbook proof
*cannot* offer (slide 23: "Textbooks show only one level of detail").

## 2. Why the naive YES fails — and how the design fixes it

Three concrete failure modes (contrarian finding 7), each answered by a design
mechanism:

1. **Expansion explosion.** A decompiled `exact` can synthesize a whole subtree
   (the Laziness Principle, §1.5). Expanding a real proof a few levels could dump
   hundreds of nodes — unreadable.
   → **Expansion budget** (§8): curated default depth `d₀`, a per-view node
   budget `N`, and salience-ordered BFS (`pivotal` before `routine`, §7). A click
   never dumps an unbounded subtree; "expand subtree" is an explicit opt-in.

2. **Raw goal-state dumps are anti-narrative.** A verbatim local context (dozens
   of machine-named hypotheses, instances) reproduces the IDE the talk wanted to
   *escape*.
   → **Summarized goal states** (§8): changed hypotheses highlighted, the rest
   folded; full context is itself behind a `detail`.

3. **No narrative flow.** GOFAI describes each step faithfully but cannot say
   "the crux is the pigeonhole step." A slide deck needs a thesis.
   → We **do not pretend otherwise**. The output is a faithful, navigable proof;
   *narration is the presenter's layer on top*. The tool gives the presenter a
   reliable scaffold whose every claim is provenance-checked (§3.2), not a
   finished talk.

## 3. The presentation workflow we actually support

1. Informalize a Lean module → `index.html` (offline, zero-dep, §9).
2. Open at default depth: the **statement** in natural prose + the **top-level
   proof outline**. This *is* the opening slide.
3. Present top-down. When the audience asks "why does that step hold?", click
   `⊕` to reveal exactly the sub-argument — **live, to arbitrary depth**, with
   the goal state one hover away. No slide-switching, no "trust me."
4. The presenter supplies motivation in speech; the tool supplies *correct,
   drillable detail on demand*. The two compose.

This is strictly more than static slides for a proof: it is a proof you can
*interrogate* in front of an audience, with a guarantee (provenance) that what is
shown is what was proved.

## 4. Honest limits (so the YES is not oversold)

- Best for **small-to-medium** proofs; very large mathlib proofs need curation
  beyond the automatic salience heuristic.
- **Tier-2 naturalness is bounded by noun-lexicon coverage** (§3.1); uncovered
  concepts degrade gracefully to Tier-1 (typeset terms) or Tier-0 (fallback
  sentence), always marked, never wrong.
- **Article guesses can be wrong** ("a/an"); they are advisory and flagged (§6.1).
- The tool **does not** write your talk's narrative — by design, not omission.

**Verdict.** Yes for an interactive, drill-down *proof browser* used as living
slides, with the show-hidden-detail feature as its core value; no for a
push-button narrated presentation. The design (§5, §8, §9) implements the former
and is explicit about not attempting the latter.
