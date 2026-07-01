# Informalization — Design

Status: **v2 — IMPLEMENTED** (post-contrarian Rounds 1–2 + user directives; see
`CONTRARIAN_LOG.md`). All modules build green on v4.29.0; 57 `#guard` tests pass;
grammar theorems are `sorryAx`-free; two worked examples (`inj_comp` real path,
`reduction` describer path) render in `web/`.
Scope: everything under `random-systems/informalization/`.
Companion to: the **verbose layer** (`verbose-lean/Verbose`) and **cnl-rs** (`cnl-rs/`)
— a *shared grammar engine and vocabulary*, **not** a shared round-trippable grammar
(see §0.1 and finding 8).

---

## 0. Position: the missing arrow

The source talk (Kyle Miller, *To formalized mathematics and back*, UCSC CSE
Colloquium 2024-01-24, `ucsc_cse_talk.pdf`) frames the field as a square:

```
            formalization
   English  ───────────────▶  Lean
      ▲                         │
      └─────────────────────────┘
            informalization          (slide 20: "We realized this arrow was missing!")
```

- **Formalization** (English → Lean) is what humans do by hand.
- **cnl-rs** and **Verbose Lean** are the *authoring* side of that arrow: a human
  writes controlled prose, the system *parses* it down to Lean tactics/terms.
  (`Since … we get …`, `By … we have …`, `Let X be …`.) They go **prose → Lean**.
- **Informalization** (Lean → English) is the missing arrow. Given a *finished*
  Lean module (statements + proofs), produce a human-readable, interactive
  document that explains it.

**This project implements the missing arrow as an *independent* Lean → prose
proof browser.** It is a *companion* to cnl-rs/Verbose, not their strict inverse.

### 0.1 What "companion" means (and what it does not)

Round-1 contrarian finding 8 is accepted: cnl-rs and informalization are **not
inverses**.
- cnl-rs's mature design ships *named combinators + comments*, not a re-parseable
  proof grammar — there is no live `parse : CNL → Lean` arrow to invert.
- Their math domains are nearly disjoint: cnl-rs is scoped to linear
  order-algebra reduction proofs and cedes induction / `calc` / case-splits to
  native Lean; informalization must describe *exactly* those proof shapes.
- The honesty mechanisms sit on opposite sides of the trust boundary: cnl-rs
  output is *elaborated by Lean* (kernel-checked); informalization output is
  *prose that is never elaborated*. So informalization cannot inherit cnl-rs's
  honesty, and has its own central problem (faithfulness without elaboration).

What is genuinely shared, and the basis of "companion": **the grammar engine and
the mathematical vocabulary** — articles, plurality, the subjunctive,
entity-merging, and a noun-notation lexicon ("ρ is a τ-reduction of q to p").
This is the reusable jewel and the subject of `UPSTREAM_TO_CNL_RS.md`. The
aspiration that `Lean → CNL → Lean` is identity is retained only as a
*long-term regression goal on statements*, contingent on cnl-rs growing a real
FTL parser (an upstream item) — **never** as this project's correctness oracle.
The real oracle is *provenance* (§3, §9).

---

## 1. What the talk actually specifies (faithful extraction)

These are load-bearing and are reproduced, not reinvented.

### 1.1 Guiding principle — "output that is not wrong"
`Right ⊂ Not-wrong ⊂ Wrong`. The informalizer is **symbolic GOFAI**, not an LLM:
- We may produce text that is *ambiguous, terse, or omits steps* (bugs), but we
  must **never** produce text that is *mathematically wrong*.
- Because it is symbolic, every output has a precise provenance and is fixable.
- The talk explicitly contrasts this with LLMs ("output is not generally not
  wrong"; consecutive ChatGPT runs all differed). **No LLM is in the trusted path.**

### 1.2 Architecture (slide 45)
```
Lean `print_proof` frontend  ──▶  Explanation webapp (JS renderer)
        │
        ▼
   Theorem explainer
        │
        ├── TacticTree inference
        ├── Tactic explainers (describers)
        ├── Proof-term decompilers
        ├── Entity explainers
        ├── Proposition explainers
        └── Expr → LaTeX  (LeanTeX)
```

### 1.3 The ontology (slides 48–53)
An **ontology** = concepts, properties, relations + a *mapping* Lean-4 ontology →
English ontology. "The better the ontology, the more natural the output."

| Concept | Fields (from slides 50–51) |
|---|---|
| `Entity` | `id`/`fvarid`, `name`, `noun : Option Noun`, `provides`, `adjectives`, `accessories` |
| `Noun` | `kind : Name`, `article`, `text`, `pluralText`, `inlineText`, `inlinePluralText`, `typePayload : Option NounTypePayload` |
| `NounTypePayload` | `type`, `text`, `pluralText` |
| `Adjective` | `kind : Name`, `expr : Expr`, `article`, `text` |
| `Accessory` | `kind : Name`, `expr : Expr`, `text` |

**Entity construction** (slides 53–54): for each local variable, run a *handler*
keyed by the head constant (`@[english_param const.TopologicalSpace]`). The
handler decides *what the variable is about* (`(T : Type)` is about `T`;
`(h : U ∈ Nhd x)` is about `U`), then creates/updates the relevant `Entity`,
attaching a `Noun`, `Adjective`, or `Accessory` and respecting dependencies.

### 1.4 Grammatical construction (slides 55–58)
Two core templates:
- **Defining**:  `Let <name> [: <noun.type>] be <article> <adjectives> <noun.text> with <accessories>.`
- **Quantifying**: `For all <adjectives> <noun.inlineText> with <accessories>, …`

Plus:
- **Merging**: consecutive entities with compatible data collapse into one
  sentence ("Let α, β and γ be types.").
- **Agreement**: plurality (verb is/are, noun function/functions), articles
  (a/an by phonetics), and the subjunctive ("Let n *be*…" vs "Suppose n *is*…").

### 1.5 Proof description (slides 59–67)
- Recover the **true proof tree** from Lean **InfoTrees**. Tactics are
  *semi-hierarchical*: many produce **side goals** solved later, so a flat tactic
  list must be re-parented (`getSideGoalsFor`).
- A **tactic describer** is `TacticTree → DescriberM ProofStep`; it may
  `throwInapplicableDescriber` to decline a node.
- **Proof-term decompiler**: for `exact`/`apply`/`refine`/…, decompile the
  generated *term* into an equivalent sequence of simpler tactics, then describe
  *that*. Rationale (the "Laziness Principle"): a Lean author writes to be
  understood by the *computer*; the human reader wants different granularity.
  `Local context + expected type + proof term → synthesized tactic trees (with
  synthesized intermediate goal states) → Explanations.`

### 1.6 The `Explanation` document type (slide 64)
A structured document supporting exactly:
1. block indentation, 2. paragraph breaks, 3. **text with (+)/(–) that replaces
text with other text** (show/hide detail), 4. clickable words that reveal extra
text, 5. tooltips, 6. **goal states**, 7. multiline equations.
Rendered by a **JavaScript webapp**.

---

## 2. Gaps in the talk, and how we fill them

The talk is a prototype report; it leaves these underspecified. Our fills:

| # | Gap | Fill (this design) |
|---|---|---|
| G1 | Output is *free English* — not re-parseable, no correctness oracle. | Target a **genuine Formal Theory Language** (FTL, ForTheL-stance: math expressed *in* the CNL via noun-notation, not punted to a term parser) as the *natural* surface. This is **not** today's cnl-rs shell and does **not** round-trip to it (finding 2); re-parseability is a future, not the oracle. |
| G2 | `Explanation` features listed but not given a type. | A strongly-typed, total ADT `Explanation` with an explicit `Detail` (show/hide) node and `GoalState` node (§5). |
| G3 | Handlers "crafted by hand"; no story for coverage/failure. | Handlers are a **typed registry** returning `Option`/`Except`; an explicit **fallback describer** guarantees *totality* (every node yields *some* not-wrong text, possibly a verbatim fallback). No silent gaps (§6, §7). |
| G4 | "not wrong" stated as a principle, never enforced. | Replaced by an enforceable, *syntactic* **provenance invariant** (finding 1+4): every `Explanation` leaf carries the source `Expr`/`MVarId`; a total checker asserts each LaTeX leaf is `exprToLatex` of *that* term; `render` is provenance-preserving. "Traceable to a kernel-checked term," **not** "semantically not-wrong" (which is undecidable without elaborating the prose). |
| G5 | Plurality/articles/subjunctive sketched. | A complete, unit-tested **grammatical engine** (`Informalization.Grammar`) — pure, total functions; the article function is **advisory** (returns its source tag), never claimed correct. (The piece cnl-rs most lacks; see `UPSTREAM_TO_CNL_RS.md`.) |
| G6 | No security/trust boundary. | Third-party deps (**KaTeX**, a hover lib) are **acceptable** — pinned to current, non-severely-vulnerable versions. The security work is in **our own code**: every user/term string reaches the DOM via `textContent` (never `innerHTML`); our JSON is `JSON.parse`d, never `eval`'d; KaTeX runs with a safe config (`trust:false`, `throwOnError:false`, bounded `maxExpand`). Lean side emits inert JSON. Trust boundary explicit (§9). |
| G7 | Merging "if compatible" — undefined. | A precise `Mergeable` relation **with a `¬ crossRef` precondition** (finding 5) + a confluent merge fold; content-preservation proven (§6.3). |

---

## 3. The FTL target and the provenance oracle

Two decisions, kept strictly separate (Round-1 finding 2 showed that conflating
them — "re-parseable ⇒ natural via one grammar" — is false).

### 3.1 FTL is the *phrasing target*, not the correctness mechanism

**Decision: the natural output surface is a *genuine Formal Theory Language*
(FTL), in the ForTheL / Naproche-SAD sense — a CNL in which the *mathematics is
expressed in the controlled language itself* via noun-notation ("ρ is a
τ-reduction of q to p"), not punted to a raw term parser.**

This is deliberately **not** today's cnl-rs/`cnl_grammar.ebnf` shell, which keeps
"CNL only for the outer shell" and parses `goal`/`prop`/`term` with Lean's term
parser. That shell *forces* Lean-plumbing leaks (`⇑r`, typeclass binders) into
any "re-parseable" output — the opposite of natural. A real FTL has productions
for the nouns themselves, so the math need never appear as raw Lean.

Consequence (accepted, not hidden): our richest output is **not** parseable by
current cnl-rs. Round-tripping becomes a *future* property, contingent on cnl-rs
acquiring a real noun-notation FTL parser — which is the headline item in
`UPSTREAM_TO_CNL_RS.md`. We do **not** claim a round-trip oracle here.

**Scope of "FTL" in THIS project (Round-2 issue A — pinned).** We build FTL
*emit-only*: (i) the typed ADTs `FTL.Statement` / `FTL.ProofStep` / `FTL.Document`;
(ii) a total **realizer** `FTL → Explanation` (the grammar engine, §6); and
(iii) a **finite, advisory noun lexicon** (`kind : Name ↦ noun-notation`) that
grows on demand exactly like Miller's hand-crafted `@[english_param]` handlers.
We do **not** build a ForTheL-style *parser* or a complete grammar — nothing in
the Lean→prose direction needs to parse. Tier-2 quality is therefore bounded by
lexicon coverage (an honest, advisory limit, logged per §3.3), not by a grammar
we must complete. This keeps the build `import Lean`-only and finite.

FTL has two strata matching Miller's split:
- **Statement FTL** ↔ Entity/Proposition explainers (Let / For-all / iff / …).
- **Proof FTL** ↔ tactic describers + decompiler (Since / By / It-suffices / …).

### 3.2 Provenance is the correctness oracle

The buildable, provable guarantee (replacing v0's round-trip, findings 1 & 4):

> **Provenance invariant.** Every leaf of an `Explanation` that asserts
> mathematical content carries the source term `e : Expr` (and, for steps, the
> `MVarId` goal) it was generated from. A total checker `checkProvenance`
> asserts that each math/`displayMath` leaf's LaTeX **equals `exprToLatex e`**
> for its recorded `e`. Theorem: `render` and the FTL→Explanation realizer are
> **provenance-preserving** (no leaf loses or fabricates its source term).

This is *syntactic* and decidable; it is the honest reading of "output that is
not wrong": **every displayed claim is traceable to a kernel-checked Lean term,
and the typeset math is exactly that term.** It does *not* assert the surrounding
English sentence is semantically equivalent to the term — that is undecidable
without elaborating the prose (which we never do), so we never claim it.

**Where the teeth are (Round-2 issue B — pinned).** At the *point of
construction* a leaf built as `math (exprToLatex e)` and recorded with that same
`e` satisfies the check tautologically. The invariant earns its keep as a
**post-pipeline preservation property**: `checkProvenance` runs *after* the
grammar realizer (§6), merging (§6.3), and serialization (§4G), and
`exprToLatex` is **pure/deterministic**. So what it actually catches is any pass
that **swaps, drops, duplicates, or rewrites** a leaf's `(latex, e)` pairing —
e.g. a merge that re-attaches the wrong source term, or a serializer that
transposes two leaves. That is a real, non-vacuous class of bugs; "this leaf
renders its own `e`" is not the claim.

### 3.3 Fidelity tiers (phrasing quality, decoupled from re-parseability)

Refining `Right ⊂ Not-wrong ⊂ Wrong`, now a *phrasing-fidelity* ladder — every
tier satisfies the provenance invariant:
- **Tier 0 — Fallback**: stock carrier sentence + `exprToLatex` of the term
  ("By a proof term `…`, the goal follows."). Always available.
- **Tier 1 — Structured**: a real FTL sentence frame (Let/For-all/Since/By) with
  math still shown as typeset terms.
- **Tier 2 — Natural**: Tier-1 plus ontology-driven noun-notation, articles,
  plurality, merging. Reads like a textbook; uses the genuine FTL lexicon.

Every node is annotated with the tier achieved. The pipeline **never drops below
Tier 0** and **logs** any node below Tier 2 (no silent caps, per project policy).
The optional `Roundtrip` regression test applies only to Tier-1 *statement*
output and only when a parser seam is wired; it is a test, not the guarantee.

---

## 4. Architecture (typed, this project)

```
                    ┌─────────────────────────────────────────────┐
   Lean module ───▶ │  (A) Frontend: InfoTree / Expr ingestion      │   [Lean, import Lean]
                    └─────────────────────────────────────────────┘
                                      │  TheoremData (typed)
                                      ▼
                    ┌─────────────────────────────────────────────┐
                    │  (B) Ontology builder                         │
                    │      Entity / Noun / Adjective / Accessory    │
                    │      + @[english_param] handler registry      │
                    └─────────────────────────────────────────────┘
                                      │  Context : Array Entity
                                      ▼
                    ┌─────────────────────────────────────────────┐
                    │  (C) Statement informalizer  → FTL.Statement  │
                    │  (D) Proof informalizer:                      │
                    │        TacticTree inference (true tree)       │
                    │        describers + proof-term decompiler     │
                    │        → FTL.ProofStep tree                   │
                    └─────────────────────────────────────────────┘
                                      │  FTL.Document
                       ┌──────────────┴───────────────┐
                       ▼                               ▼
        ┌──────────────────────────┐    ┌────────────────────────────┐
        │ (E) Grammar engine        │    │ (F) Provenance checker      │
        │  FTL → Explanation        │    │  every math leaf's LaTeX ≟  │
        │  (article/plural/merge)   │    │  exprToLatex(its src Expr)  │
        └──────────────────────────┘    └────────────────────────────┘
                       │ Explanation (+ Expr→LaTeX via LeanTeX-style)
                       ▼
        ┌──────────────────────────┐
        │ (G) Serializer → JSON      │   [Lean → data only]
        └──────────────────────────┘
                       │ explanation.json
                       ▼
        ┌──────────────────────────┐
        │ (H) Web renderer (offline) │   [HTML+JS, zero-dep, no eval/network]
        │  collapsible +/-, hover    │   ← "the slides"
        │  goal-states, tooltips     │
        └──────────────────────────┘
```

**Implementation reality (honest scope, revised per finding 3).** `Expr→LaTeX`
for *arbitrary* mathlib terms is large and toolchain-fragile (Verbose is
*unbuildable* against the pinned mathlib — `Mathlib.Tactic.CC` was removed; see
cnl-rs findings). So we draw the line at **core Lean**, not at "abstract":

- **(A) Frontend — ONE REAL PATH.** Using only core `Lean.Elab`/`InfoTree` APIs
  (no mathlib), we elaborate a real in-package theorem from source, walk its
  `InfoTree`, and recover a `ProofTree`. Example: **`inj_comp`** (composition of
  injective functions is injective) — from the talk, core `Function.Injective`
  only. This is a genuine `Expr`-to-prose path, not hand-fed.
- **(E) `Expr→LaTeX` — REAL, closed fragment.** A genuine recursive
  `exprToLatex` over the closed fragment the example needs (application,
  `∀`/`→`, `fun`, projections, `=`, named consts with a notation table). Total;
  unknown nodes fall back to a fully-escaped `toString` (still provenance-valid).
- The `(B)`–`(G)` **algebra** is implemented as strongly-typed total functions and
  also exercised by a second, hand-built example (to show domain nouns/merging
  that the core example does not reach). (H) is fully real and standalone.

This keeps the package `import Lean`-only and green, while the *two semantically
load-bearing pieces* (true-tree recovery and term rendering) are **real** on at
least one path — so the demo proves the thesis, not just plumbing.

---

## 5. The `Explanation` document type

```lean
inductive Explanation where
  | text     (s : String)                                   -- plain run
  | math     (latex : String)                               -- inline LaTeX
  | concat   (xs : Array Explanation)                       -- in-line sequence
  | paragraph (xs : Array Explanation)                      -- paragraph break (2)
  | indent   (body : Explanation)                           -- block indentation (1)
  | detail   (summary : Explanation) (expanded : Explanation) -- (+)/(-) replace (3)
  | clickable (label : Explanation) (reveal : Explanation)  -- click → extra text (4)
  | tooltip  (anchor : Explanation) (hint : Explanation)    -- tooltip (5)
  | goalState (g : GoalState)                               -- goal state (6)
  | displayMath (latex : String)                            -- multiline equation (7)
```
Totality and a `render : Explanation → Html` (pure) give a **decidable, finite**
document. `detail` is the show-hidden-details primitive; `goalState` is the
proof-context primitive. Both are first-class, not annotations.

`GoalState` mirrors the talk's "Current proof state" box:
```lean
structure Hyp where name : String; type : String /- LaTeX -/
structure GoalState where hyps : Array Hyp; goal : String /- LaTeX -/
```

---

## 6. The grammatical engine (strong; cnl-rs's weak spot)

Pure, total, unit-tested. No metaprogramming. This is the reusable jewel.

### 6.0 Theoretical foundation (not invented here)

Per project direction, the grammar must rest on an *established* linguistic
framework, followed as closely as possible — not bespoke rules that "sort of"
read naturally. We adopt three:

1. **Grammatical Framework (GF) and its Resource Grammar Library (RGL)** — Aarne
   Ranta. GF's defining move is the split between an **abstract syntax**
   (language-independent meaning) and **concrete syntaxes** (language-specific
   realization via *feature structures*). This is *exactly* the talk's "Lean-4
   ontology → English ontology" mapping (slide 49), and GF is the principled
   version of it. We follow GF in three concrete ways:
   - **Agreement is by features, not guessing.** Number/determiner agreement is
     computed from a feature record threaded through realization (GF's
     parameter/table model), never inferred ad hoc.
   - **The article is a *lexical feature*.** In GF's `ParadigmsEng`, a noun's
     indefinite-article allomorph (a/an) is a property *stored on the lexical
     entry*, with a written-form heuristic only as the default seeder,
     overridable per word. This is why the talk's `Noun` already carries an
     `article` field — and it is the principled fix to Round-1 finding 5: the
     article is data on the noun, the spelling heuristic only *seeds* the
     lexicon (advisory), it is never the source of truth at realization time.
   - GF is itself grounded in Martin-Löf type theory — congenial to a Lean host.
   - Precedent for *mathematics*: WebALT (Caprotti 2006) and **MathNat**
     (Humayoun & Raffalli) realize mathematical text via GF.
2. **Reiter & Dale, *Building Natural Language Generation Systems* (2000)** — the
   standard NLG pipeline: document planning → **microplanning** (lexicalisation,
   **aggregation**, referring-expression generation) → surface realization. Our
   components map onto their named operations exactly:
   - entity **merging** *is* **aggregation** (combining simple phrase specs into
     one complex sentence) — so `mergeGroups` is `aggregate`;
   - choosing "a/an", "the", names *is* **referring-expression generation**;
   - the `Let …`/`For all …` templates are **surface realization**.
   Using the standard names (and the standard soundness obligations — e.g.
   aggregation must not change truth conditions, our `isolation` lemma) keeps the
   engine honest and recognizable rather than bespoke.
3. **ForTheL** (Naproche-SAD's *Formal Theory Language*) — the CNL target (§3),
   the math-bearing controlled grammar our FTL ADT abstracts.

Grammar.lean is written as a small, faithful Lean rendering of GF-RGL feature
realization + Reiter–Dale aggregation; every primitive cites the framework
operation it implements.

### 6.1 Articles (advisory, not authoritative)
Finding 5 is accepted: a/an depends on how a symbol is *read aloud*
(reader-dependent: "an `ℝ`-module", "a `1`-form", "an `8`-cube"), so no spelling
function can be *correct*. We therefore make it explicitly advisory:
```lean
inductive Article | a | an
inductive ArticleSource | overridden | heuristic | unknown
def indefiniteArticle : String → Article × ArticleSource
```
An explicit override table handles known math words; otherwise a leading-sound
heuristic with `source := heuristic`; genuinely ambiguous → `unknown` (defaults
to "a", flagged). The `ArticleSource` is surfaced to the author (and as a faint
tier mark in the UI), so a wrong guess is *visible and fixable*, never silent.
Total; never throws.

### 6.2 Plurality & agreement
`Number = singular | plural`. Functions:
`verbToBe : Number → Subjunctive → String` ("is"/"are"/"be"),
`pluralize : Noun → Number → String` (uses `pluralText`, not naive +s),
`agree : Determiner → Number → …`. A `Phrase` carries its own `Number` so
agreement is computed, not guessed.

### 6.3 Merging (with the cross-reference precondition)
```lean
def crossRef   (a b : EntityIntro) : Bool   -- a's text/type mentions b's name, or vice-versa
def Mergeable  (a b : EntityIntro) : Bool   -- same noun+adjectives+accessories+"be" AND ¬ crossRef a b
def mergeRun   : Array EntityIntro → Array SentencePlan
```
"Let α be a type. Let β be a type. Let γ be a type." → "Let α, β and γ be types."
But "Let α be a type. Let β be an α-module." does **not** merge (`crossRef` holds:
β's noun mentions α). The fold is confluent (order within a run preserved;
Oxford-comma list join). Two proven lemmas (finding 5):
1. **content-preservation**: `mergeRun` preserves the multiset of introduced
   entities (none lost or duplicated);
2. **isolation**: merging fires only between non-cross-referencing intros, so each
   merged conjunct is well-formed standalone (the merge cannot create a sentence
   asserting a dependency that the unmerged form did not).

### 6.4 Sentence templates (the FTL surface)
Realize `FTL.Statement` / `FTL.ProofStep` into `Explanation` via the two
templates (§1.4) plus the proof frames shared with cnl-rs (`Since/By/We
conclude/It suffices/Assume/Fix`). Each realization is a pure function with the
agreement engine threaded through.

---

## 7. Proof description (scoped)

- `ProofTree` is a typed input: a true, re-parented tree with side goals attached
  to their parent. **Re-parenting is REAL for the closed tactic set the examples
  use** (`intro`, `exact`, `apply`, `refine`, `constructor`, term mode) — i.e. the
  `inj_comp` real path recovers its *true* tree, not a flat list, discharging
  Round-2 issue C. General mathlib-wide tactic coverage (every exotic tactic's
  side-goal discipline) is the seam; the *algebra over the tree* is fully
  implemented regardless.
- Each `ProofStep` carries `salience : Salience` (`pivotal | routine`, default
  `routine`), set by its describer (issue D). The renderer's expansion budget
  (§8) does a salience-ordered BFS truncated at the node budget `N`: all
  `pivotal` first, then `routine`, never exceeding `N` without an explicit
  "expand subtree".
- `Describer := ProofTree → DescriberM (Option ProofStep)` (returns `none` ⇒
  inapplicable; mirrors `throwInapplicableDescriber`). A registry tries
  describers in priority order; the **fallback describer** (Tier 0) is total.
- **Decompiler seam**: `decompile : Term → Option (Array TacticStep)` for the
  `exact/apply/refine` family. Implemented for a small closed grammar of terms
  (application, `fun`, projection, named lemma) — enough for the example; growable.

---

## 8. Expected output, interaction, UX

**What it is (finding 7).** Not an auto-generated *narrative presentation* —
symbolic GOFAI cannot synthesize a thesis or "the key idea." It is an
**interactive proof browser** ("living slides"): a faithful, collapsible,
provenance-checked rendering of a real proof, whose strength is *show-hidden-
detail* and *goal-state-on-hover*. See `SLIDES_ANSWER.md` for the qualified yes.

**Expected output.** One self-contained `index.html` (+ `explanation.json`) per
informalized module. Opens to a **theorem statement** in natural prose, then the
proof as an **indented, collapsible outline at a bounded default depth** (the
*expansion budget*, below). Every claim has a **Tier mark** (● natural, ○
structured, · fallback) and an **article-source mark** when a/an was guessed, so
reader/author always know provenance.

**Expansion budget (finding 7).** "Arbitrarily deep because formalized" is a
hazard, not a feature: decompiling one `exact` can synthesize a subtree of steps.
So the document ships with:
- a **default depth** `d₀` (curated per describer: routine steps collapsed,
  pivotal steps shown); nodes carry a `salience` so the budget shows the useful
  ones first;
- a per-view **node budget** `N`; expanding beyond it requires an explicit
  "expand subtree" so a click can never dump hundreds of synthesized nodes;
- goal states are **summarized by default** (changed hypotheses highlighted, the
  rest folded) — never a raw verbatim context dump (which would just reproduce
  the IDE the talk wanted to escape).

**Interaction.**
- **Hover** any introduced entity or step ⇒ tooltip with its **goal state**
  (the "Current proof state" box from slides 22/24).
- **Click `⊕`** on any step ⇒ expands the hidden sub-proof one level (slide 24's
  "Imagine clicking a ⊕ and seeing further proof"); `⊖` collapses. Arbitrarily
  deep, because the proof is formalized.
- **Click a defined term** ⇒ reveals its definition inline (clickable-word node).

**UX principles (consistent with the user's widget-minimalism preference).**
- The canvas is **paper-like and minimal**: prose only, no chrome. Detail,
  tooltips, goal-states, tiers live in **hover/expand**, never on the surface.
- Keyboard: `+`/`-` expand/collapse focused step; `g` toggles all goal states.
- Fully offline; print-to-PDF gives a clean static paper (details expanded or
  collapsed per a print toggle).

---

## 9. Scope, non-goals, security, typing, correctness

**In scope (buildable):** §5–§8 algebra + grammar + renderer + one end-to-end
worked example, all `import Lean`-only, green, axiom-light.

**Seam (typed stub + 1 example):** live InfoTree ingestion; full `Expr→LaTeX`.

**Non-goals:** training-data generation (slide 35), knots (the speaker's research),
a general InfoTree decompiler for all of mathlib, LLM anything.

**Security / trust boundary (revised per user direction).** We are *not*
extremely conservative: **third-party dependencies are acceptable** —
specifically **KaTeX** for math typesetting and a small positioned-tooltip lib
for hover, vendored at current, non-severely-vulnerable versions (the same stack
Verso uses). The bar is "no outdated dep with a known severe vuln," not "no dep."

**The real security work is in our own implementation**, where the actual risk
lives (a malicious/odd Lean module can influence every string in the JSON):
1. **No injection through our glue.** Every user-/term-derived string reaches the
   DOM via `document.createTextNode` / `.textContent` — **never** `innerHTML`,
   `insertAdjacentHTML`, or template-string HTML. Structure is built with
   `createElement`; only a fixed whitelist of tags is ever created.
2. **No code execution of our data.** `explanation.json` is parsed with
   `JSON.parse`, never `eval`/`new Function`; no field is ever used as a tag
   name, attribute name, URL, or event-handler string.
3. **Safe KaTeX config.** `renderToString` with `trust:false` (disables
   `\href`/`\url`/raw-HTML commands), `throwOnError:false`, and a bounded
   `maxExpand`/`maxSize` to prevent macro-expansion DoS from adversarial LaTeX.
   KaTeX output is inserted into a node we created, not merged into untrusted
   markup.
4. **No network at view time** (assets vendored), so no exfiltration/CDN-tamper
   surface — a convenience, not the core control.

Threat model: a malicious Lean module can produce *weird prose and weird math*
but **cannot execute script in the viewer**, because the injection-prone sinks
are closed in *our* code regardless of what the dependencies do. That is where
the user directed the security effort, and where it belongs.

**Typing discipline.** Follow the CR18 PFun house style: lightest faithful type
(predicate → product → subtype), `abbrev`s, `@[simp]` normal forms, no `Bool`
where a `Prop`+`Decidable` is clearer, Apache headers. The ontology structures
are records exactly as in slide 51.

**Correctness.** Three levels: (i) total functions (no partiality in the algebra);
(ii) content-preservation + isolation lemmas (merging loses/duplicates nothing
and never fabricates a dependency; rendering is structure-preserving); (iii) the
**provenance invariant** (§3.2): every math leaf's LaTeX equals `exprToLatex` of
its recorded source term, checked by a total `checkProvenance` and preserved by
`render`. The round-trip is a *regression test* on Tier-1 statements only, not a
guarantee.

---

## 10. Module map (proposed)

```
informalization/
  lakefile.lean              -- import Lean only
  lean-toolchain             -- v4.29.0 (matches random-systems)
  Informalization.lean       -- root import
  Informalization/
    Explanation.lean         -- §5 ADT + render to Html data
    Ontology.lean            -- §1.3 Entity/Noun/Adjective/Accessory + registry
    Grammar.lean             -- §6 article/plural/subjunctive/merge (pure, tested)
    FTL.lean                 -- §3 Statement/ProofStep/Document grammar + tiers
    Describe.lean            -- §7 ProofTree, Describer, fallback, decompiler seam
    ExprLatex.lean           -- §4(E) REAL exprToLatex over the core fragment
    Frontend.lean            -- §4(A) REAL InfoTree → ProofTree (core Lean) + hand feeder
    Provenance.lean          -- §3.2 provenance invariant + checkProvenance + render-preservation
    Serialize.lean           -- §4(G) Explanation/FTL → JSON
    Test.lean                -- grammar + provenance unit tests via #guard
  examples/
    InjComp.lean             -- REAL end-to-end: elaborate inj_comp → InfoTree → prose → JSON
    Reduction.lean           -- hand-built: domain nouns + merging (CR18-flavoured)
    *.json                   -- generated artifacts
  web/
    index.html               -- §4(H) renderer ("the slides"): KaTeX math + safe JSON→DOM glue
    render.js                -- JSON.parse → createElement/textContent only (no innerHTML/eval)
    style.css
    vendor/                  -- pinned KaTeX (+ optional tippy), current non-vuln versions
  design/
    DESIGN.md  CONTRARIAN_LOG.md  SLIDES_ANSWER.md
  UPSTREAM_TO_CNL_RS.md
  README.md
```
```
```
