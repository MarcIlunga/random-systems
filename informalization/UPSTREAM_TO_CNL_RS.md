# Ideas to upstream to cnl-rs (focus: natural, readable grammar)

cnl-rs is less mature than it looks, and its **weakest point is achieving
natural, readable grammar** (the user's assessment, confirmed by its own design
notes: `cnl_rs_idiom_layer_design.md §0` lists "a citation in costume", "Lean
plumbing leaks", "hypotheses are raw inequalities, not nouns"). Informalization
had to build exactly the missing layer — a grammar engine grounded in real
linguistic theory — and that layer is **the shared asset** between the two
projects (DESIGN §0.1). This document proposes what to lift across, why, and how.

The unifying message: **cnl-rs currently invents grammar ad hoc; it should adopt
an established framework.** Everything below follows GF / its Resource Grammar
Library (Ranta), Reiter–Dale microplanning, and ForTheL — not bespoke rules.

---

## 1. The core port: the grammar engine (`Informalization.Grammar`)

`Grammar.lean` is **pure, `import Lean`-free, theory-grounded, and proven**. It
is directly liftable into cnl-rs as `CnlRs.Grammar` with zero dependency cost.
What it gives cnl-rs that it lacks today:

| cnl-rs gap (its own §0) | Grammar.lean primitive | Framework basis |
|---|---|---|
| article never agrees ("a injective") | `seedArticle` + lexical `Article` feature; `realizeNounPhrase` reads the article from the noun, never from spelling | GF `ParadigmsEng`: article is a *lexical feature*, heuristic only seeds it |
| multiple intros listed one-per-line | `aggregate` (= `mergeGroups`) collapses "Let α be a type. Let β be a type." → "Let α, β and γ be types." | Reiter–Dale **aggregation** |
| number never agrees ("α, β is types") | `Features.number` threaded through `realizeNounPhrase`/`verbToBe` | GF feature/parameter model |
| no Oxford-comma list realization | `joinAnd` | surface realization |
| no provable safety on the above | `mergeGroups_flatten` (content preservation), `mergeGroups_isolation` (truth preservation) | Reiter–Dale aggregation soundness obligation |

**How to adopt.** cnl-rs `Statements`/`Lets` already build noun-notation; route
their *introduction* sentences through `Grammar.realizeIntros` instead of
emitting one `Let` per binder. Concretely, where cnl-rs renders
`Given: {R Sr Ωr : Type*}` it should build three `Grammar.Intro`s (one per type
variable) and call `realizeIntros` → "Let R, Sr and Ωr be types." This single
change kills both the plumbing leak (`Type*`) and the one-per-line awkwardness.

---

## 2. Articles as a lexical feature, not a spelling rule

cnl-rs (and most homegrown CNLs) compute "a/an" from the first letter and get
math wrong ("a ε-net", "a injective function", "an unique map"). The principled
fix, straight from GF's English RGL:

> The indefinite article is a **property stored on each lexical entry**; a
> written-form heuristic supplies the default, overridable per noun.

In cnl-rs terms: every noun-notation `def` (e.g. `def reduction … `,
`def converges_to …`) should carry an `article : Article` field (or a metadata
attribute), seeded once by `Grammar.seedArticle` and corrected by hand where the
seeder is `unknown`/`heuristic`. The realizer then *reads* it. This makes "an
ε-net" and "a unique factorization" correct by construction and **localizes** the
only place a human must check (the lexicon entry), instead of hoping a global
heuristic is right everywhere.

`seedArticle` already returns an `ArticleSource` (`overridden | heuristic |
unknown`) precisely so cnl-rs can surface "please confirm this article" at
lexicon-definition time.

---

## 3. Reasoning frames as ForTheL/Reiter–Dale, not single-phrase hops

cnl-rs's original surface bound one English noun phrase to one lemma
(`reductions compose` ⇒ `exact reduction_comp`), which its own review calls "a
citation in costume" — the *argument* is discarded. The informalization FTL layer
(`FTL.lean`) models the **reasoning moves themselves** as a typed `Frame` ADT
(`since`, `byApplied`, `weConclude`, `itSuffices`, `assume`, `fix`, `fallback`),
each a ForTheL/Verbose sentence form. cnl-rs should converge its frames onto the
**same `Frame` vocabulary** so that:
- a proof reads as sentences with subjects and verbs ("Since ρ is a τ-reduction
  and reductions compose, we get …"), not bare citations;
- the two projects share one surface, so an informalized proof and a
  hand-authored cnl-rs proof are *the same language* (the companion relation,
  DESIGN §0.1).

This is the place to **grow cnl-rs toward a real ForTheL parser** (DESIGN §3.1):
once the frames are first-class data on both sides, cnl-rs can parse them and
informalization can emit them, and the `Lean → CNL → Lean` round-trip becomes a
*future* reality rather than a slogan.

---

## 4. Nouns for hypotheses, via the ontology bridge

cnl-rs renders hypotheses as raw inequalities (`(p_red : τ ∘ p̄ ≤ q̄ ∘ ρ)`) where
the paper says "ρ is a τ-reduction of q to p". Informalization's
`Ontology.Entity`/`Noun` + `Entity.toIntro` is exactly the machinery to turn a
typed hypothesis into a noun phrase. cnl-rs should adopt the `Entity`/`Noun`
ontology (slide-51 shape) and an `@[english_param]`-style handler registry so
that a hypothesis of type `τ-reduction …` realizes as the *noun* "a τ-reduction
of q to p", not the inequality. The handler registry's **fallback totality**
(an identity handler) means coverage can grow incrementally without ever
crashing — uncovered hypotheses degrade to the typeset term, marked, never wrong.

---

## 5. A shared, theory-cited test corpus

Port `Grammar.lean`'s `#guard` suite (article seeding, aggregation, end-to-end
realization) into cnl-rs as a regression corpus, and grow it with CR18 sentences
("Let p, q and r be problems.", "ρ is a τ-reduction of q to p."). Because the
engine is pure and the lemmas are proven, this corpus is cheap to maintain and
pins natural-reading output against regressions — the thing cnl-rs most needs and
currently has no guard for.

---

## 6. Suggested sequencing for cnl-rs maintainers

1. **Lift `Grammar.lean`** verbatim as `CnlRs.Grammar` (pure, no new deps).
2. **Add `article` to noun-notation lexicon entries**, seeded by `seedArticle`.
3. **Route `Given:`/`Let` rendering through `realizeIntros`** (aggregation +
   agreement) — immediate, visible naturalness win.
4. **Adopt the `Frame` ADT** for proof steps; retire single-phrase hops.
5. **Adopt the `Entity`/`Noun` ontology** for hypotheses-as-nouns.
6. **Share the test corpus**; later, build the ForTheL parser to close the
   round-trip.

Items 1–3 are small and give most of the readability gain. Items 4–6 are the
path to cnl-rs and informalization genuinely being one language in two
directions.

---

### References (the frameworks, so this is not bespoke)
- A. Ranta, *Grammatical Framework: Programming with Multilingual Grammars* (CSLI,
  2011); the GF **Resource Grammar Library** (LiLT) — abstract/concrete syntax,
  feature-based agreement, `ParadigmsEng` article allomorphy.
- E. Reiter & R. Dale, *Building Natural Language Generation Systems* (CUP, 2000)
  — microplanning: lexicalisation, **aggregation**, referring-expression
  generation, surface realization.
- **ForTheL** / Naproche-SAD — the Formal Theory Language (CNL for mathematics).
- M. Humayoun & C. Raffalli, *MathNat* — mathematical text in a CNL via GF
  (precedent for GF-based mathematics realization).
