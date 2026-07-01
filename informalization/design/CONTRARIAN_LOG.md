# Design debate log (proposer ↔ contrarian)

Per project policy, design review is an *iterated debate*, not a single pass.

## Round 1 — contrarian attack on DESIGN v0

An independent contrarian reviewed v0 against the talk, `cnl_grammar.ebnf`, the
cnl-rs idiom doc, and CR18 house style. Verdicts:

| # | Claim attacked | Verdict | Core of the attack |
|---|---|---|---|
| 1 | Round-trip oracle | **BROKEN** | Can't run (no buildable parser; cnl-rs is *deleting* its frame parser); wrong equality (defeq hole inherited from cnl-rs round-2); circular (Tier-1 *defined as* "round-trips"); a verbatim-term informalizer round-trips perfectly → oracle rewards non-natural output. |
| 2 | FTL decision | **WEAK→BROKEN** | `cnl_grammar.ebnf` punts all math to Lean's term parser, so "re-parseable" *forces* Lean-plumbing leaks — the opposite of natural. Tier-1 (re-parseable) and Tier-2 (natural) conflict; Tier-2 forfeits the round-trip. "FTL like ForTheL" overclaims: the cnl-rs shell is not a self-contained CNL. |
| 3 | Scope honesty | **WEAK** | The two stubbed seams (true-tree recovery, Expr→LaTeX) are exactly the semantically load-bearing ones; the "end-to-end" example is entirely hand-fed → rigged demo proving plumbing, not the thesis. |
| 4 | `faithful` invariant | **BROKEN** | Semantic faithfulness is undecidable without elaborating the prose; only a *syntactic* provenance check is provable; "not wrong" cannot be a typed invariant. |
| 5 | Grammar engine | **WEAK** | a/an depends on *pronunciation* (reader-dependent: "an `ℝ`-module", "a `1`-form", "an `8`-cube") — total only by guessing; override table permanently incomplete. Merge content-preservation is true but the lemma that *matters* (truth under cross-references) is unstated. |
| 6 | Security | **WEAK** | "zero-dependency" and "vendored KaTeX" are contradictory; KaTeX has injection/DoS CVE history and its threat model assumes trusted LaTeX, but ours is generated from adversary-controllable Lean modules. |
| 7 | Slides question | **WEAK (dodged)** | Expansion explosion ("arbitrarily deep" is the problem); raw goal-state dumps are anti-narrative (reproduce the IDE we fled); GOFAI cannot synthesize a *narrative*. It's a proof browser, not slides. |
| 8 | "strict inverse of cnl-rs" | **BROKEN** | cnl-rs abandoned its parser (combinators + comments — not a language); scope is disjoint (cnl-rs = linear order-algebra; we must handle induction/calc/case-split); honesty asymmetry is structural (cnl-rs output is kernel-elaborated, our prose is never elaborated). |

## Round 1 — proposer adjudication

**Accepted (wholesale): 1, 3, 4, 6, 7, 8.** These are correct and make the design
honest and buildable. Resulting changes (folded into v1):

- **1 + 4 → provenance invariant.** Drop the round-trip *as the oracle*. The
  real, buildable, provable invariant is **provenance**: every `Explanation`
  leaf carries the source `Expr`/`MVarId` it was generated from; a total checker
  asserts each LaTeX leaf equals `exprToLatex` of *that* term. Theorem:
  `render` is provenance-preserving. Market it as "every claim is traceable to a
  kernel-checked term," **not** "not wrong." The round-trip survives only as an
  *aspirational regression test on a closed statement corpus*, never as the
  guarantee.
- **3 → one real path.** Commit to a **genuine** `Frontend` path: ingest a real
  InfoTree from a real in-package theorem (core-Lean only, no mathlib) and a
  **real** (small-fragment) `Expr→LaTeX`. Chosen example: `inj_comp`
  (composition of injective functions is injective) — from the talk, uses only
  core `Function.Injective`. The hand-fed example is kept too, but it is no
  longer the *only* path.
- **6 → true zero-dep.** Drop KaTeX entirely. Ship an explicit **escaping
  mini-typesetter** for the closed LaTeX fragment we actually emit (sub/superscript,
  fractions, named symbols, binary operators). User text via `textContent`;
  structure via a whitelist of created elements; no `innerHTML`, no `eval`, no
  network. Now "zero-dependency" is literally true.
- **7 → proof browser, qualified yes.** Reframe deliverable as an **interactive
  proof browser** ("living proof", not auto-generated narrative). Add an explicit
  **expansion budget** and **curated default depth**. `SLIDES_ANSWER.md` gives a
  *qualified* yes (small/medium proofs, bounded default depth, show-hidden-detail
  is the genuine strength) and states plainly what GOFAI cannot do (synthesize a
  thesis/motivation).
- **8 → companion, not inverse.** Drop "strict inverse." Position as an
  *independent* Lean→prose proof browser that **shares the grammar engine and
  vocabulary** with cnl-rs (the genuinely reusable asset) but **not** a
  round-trippable grammar or an honesty mechanism.

**Accepted with synthesis (not capitulation): 2 and 5.**

- **2 (FTL).** The contrarian is right that the *cnl-rs shell* is not a real FTL
  and that re-parseability of *that shell* fights naturalness. But the user
  explicitly requires "consider a Formal Theory Language for the CNL part," and
  the right reading of that requirement is the **ForTheL stance**: a CNL in which
  *the mathematics is expressed in the controlled language itself* (noun-notation
  like "ρ is a τ-reduction of q to p"), **not** punted to a raw term parser.
  Synthesis: target a **genuine FTL with first-class noun-notation** as the
  *natural* (Tier-2) surface. Concede that this genuine FTL is **not** what
  current cnl-rs parses, so round-tripping to *today's* cnl-rs is unavailable —
  and turn that into the headline **upstream suggestion**: grow cnl-rs a real
  noun-notation FTL parser. This honours the user's FTL requirement, absorbs the
  critique, and feeds `UPSTREAM_TO_CNL_RS.md`. The three tiers are re-cut as
  *fidelity of phrasing*, decoupled from re-parseability.
- **5 (grammar).** Accept both fixes. `indefiniteArticle` returns
  `Article × ArticleSource` (heuristic | overridden | unknown) — **advisory**,
  surfaced to the author, never claimed correct. State and prove the merge lemma
  that matters: `Mergeable a b → ¬ crossRef a b` as a precondition, and prove
  merge preserves each introduction's content in isolation.

**Convergence:** no contested findings remain after adjudication; all are
accepted or synthesized. v1 written. A focused Round-2 check follows on whether
the v1 revisions actually discharge findings 1–8.

## Round 2 — focused contrarian verification of v1

Verdicts on the v1 revisions: findings **1, 4, 5, 6, 7, 8 → DISCHARGED**;
**2, 3 → PARTIAL** (ambition relocated, not retired). Four new clarifications
raised (A–D); three were blocking statement-level fixes.

## Round 2 — proposer adjudication → v2 (all accepted)

- **A (FTL scope).** Pinned in §3.1: FTL is **emit-only** — typed ADTs + a total
  realizer + a *finite advisory* noun lexicon. **No ForTheL parser/grammar** is
  built (nothing in Lean→prose needs to parse). Tier-2 is bounded by lexicon
  coverage (honest, logged), not by an unbounded grammar.
- **B (provenance teeth).** Pinned in §3.2: the invariant is a **post-pipeline
  preservation** property (`exprToLatex` pure; checked after grammar/merge/
  serialize). It catches leaf `(latex, e)` swap/drop/dup/rewrite — not the
  tautological "renders its own e".
- **C (real tree vs stub).** Resolved in §7: re-parenting is **real for the
  closed tactic set the examples use**, so the `inj_comp` path recovers the true
  tree; only general mathlib-wide tactic coverage is the seam. §4(A)/§9 "real
  path" and §7 no longer contradict.
- **D (salience).** Concrete in §7/§8: `salience : pivotal | routine` is a
  `ProofStep` field set by the describer; renderer does salience-ordered BFS
  truncated at node budget `N`.

**Convergence reached.** Two rounds, all findings discharged or pinned; v2 is the
implementation baseline. (Residual PARTIALs on 2/3 are *honest scope limits*
now stated in the design, not unresolved disputes.)

## Post-design user directives folded into implementation

1. **Reuse survey (wary of deviations).** Before/while coding, survey existing
   Lean presentation/informalization implementations to reuse rather than build
   from scratch — specifically **Kyle Miller's own informalizer prototype**,
   **Verso** (Lean doc-authoring), **LeanTeX** (Expr→LaTeX, named in the talk),
   and Verbose's English print layer. Treat any reuse as a *helper*: vet for
   buildability against our pinned toolchain and for design deviations before
   adopting. → tracked as a task; results in `design/REUSE_SURVEY.md`.
2. **cnl-rs is less mature than assumed**, weak at natural/readable grammar →
   the grammar engine is the prize to upstream (`UPSTREAM_TO_CNL_RS.md`).
