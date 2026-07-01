# Informalization

The **missing arrow**: Lean proof → interactive, controlled-natural-language
document. A companion (not inverse) to the *verbose layer* and *cnl-rs*, which go
the other way (prose → Lean).

Reverse-engineered and gap-filled from Kyle Miller's talk *To formalized
mathematics and back* (`ucsc_cse_talk.pdf`), then designed against two rounds of
contrarian review and implemented as a self-contained `import Lean`-only package.

## The question this answers

> *Can these be used as slides to present a Lean proof, with features such as
> showing the hidden details?*

**Qualified yes** — as an interactive *proof browser* ("living slides") with
show-hidden-detail (`⊕`/`⊖`) and goal-state-on-hover, for small/medium proofs at
a bounded default depth. **No** to push-button narrated presentation (symbolic
generation cannot synthesize a thesis). Full answer: `design/SLIDES_ANSWER.md`.

## Layout

```
design/        DESIGN.md (v2), CONTRARIAN_LOG.md (2 rounds), SLIDES_ANSWER.md,
               REUSE_SURVEY.md
Informalization/
  Explanation.lean   the structured-document ADT (7 features) + provenance leaves
  Grammar.lean       GF-RGL feature realization + Reiter–Dale aggregation (proven)
  ExprLatex.lean     real Expr→LaTeX over a core fragment (credits LeanTeX)
  Ontology.lean      Entity/Noun/Adjective/Accessory + handler registry (slide 51)
  FTL.lean           Formal Theory Language ADTs + realizer → Explanation
  Serialize.lean     Explanation → JSON (the renderer's schema)
  Provenance.lean    the provenance invariant + checker
  Frontend.lean      REAL InfoTree → ProofTree (core Lean), example: inj_comp
  Describe.lean      tactic describers, fallback, decompiler seam, salience
examples/      InjComp.lean (real, end-to-end), Reduction.lean (hand-built)
web/           index.html + render.js + style.css  ("the slides")
UPSTREAM_TO_CNL_RS.md   grammar ideas to upstream (cnl-rs's weak spot)
```

## Design pillars

- **"Not wrong" via provenance** (not free English): every typeset-math leaf is
  traceable to a kernel-checked term; `checkProvenance` is the buildable oracle.
  Semantic faithfulness of the *English* is never claimed (undecidable).
- **Grammar grounded in theory**: GF / Resource Grammar Library (Ranta),
  Reiter–Dale microplanning, ForTheL — not bespoke rules. Articles are *lexical
  features*; merging is *aggregation* with proven content/truth preservation.
- **Security in our own code** (deps like KaTeX are fine, pinned): the renderer
  builds DOM with `createTextNode`/`textContent` only — no `innerHTML`/`eval`,
  JSON is `JSON.parse`d, KaTeX runs with `trust:false`.
- **Honest scope**: one *real* path (`inj_comp`: real InfoTree + real Expr→LaTeX);
  general mathlib coverage and a ForTheL parser are documented seams/future work.

## Build

```sh
cd random-systems/informalization
lake build
```
Toolchain `v4.29.0` (matches random-systems). No mathlib / VCVio dependency.

## View "the slides"

Open `web/index.html` in a browser (no server needed). Drop a pinned KaTeX into
`web/vendor/` for typeset math (optional — math degrades to readable text
without it). Replace the inline JSON payload with the output of
`Explanation.toJsonString` from a generated example.
