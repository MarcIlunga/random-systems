# Reuse survey — existing implementations to build on

Per user directive: *reuse existing work as helpers rather than starting from the
ground up, but be wary of deviations*; specifically check **Kyle Miller's own
implementation**, **Verso**, and other Lean presentation tooling.

Method: `gh` inspection of licenses, toolchains, and scope. Verdicts are
**ADOPT** (depend on it), **MIRROR** (copy the design/patterns, not the code),
**MINE** (extract data/vocabulary), or **AVOID** (with reason).

## Summary table

| Asset | What it is | License | Toolchain | Verdict |
|---|---|---|---|---|
| **Kyle Miller's informalizer** | the prototype from the talk | — | — | **AVOID (unavailable)** — not a public repo (checked all `kmill` repos via `gh`). Only LeanTeX is published. The talk is the spec; the code can't be reused. |
| **kmill/LeanTeX** | Expr→LaTeX pretty-printer (the talk's "LeanTeX" box) | Apache-2.0 | v4.18.0-rc1 | **MIRROR** — port its precedence/parenthesization patterns into our `ExprLatex.lean`; don't depend (toolchain gap 4.18→4.29; pulls its own deps). |
| **kmill/LeanTeX-mathlib** | mathlib LaTeX printers | Apache-2.0 | (tracks LeanTeX) | **AVOID** — needs mathlib, which we deliberately exclude. |
| **leanprover/verso** | Lean doc-authoring; HTML w/ **proof-state-annotated** code (Alectryon-style) | Apache-2.0 | **v4.29.0 tag (exact match)** | **MIRROR now, ADOPT-later** — see §1. |
| **Verbose English layer** (in-repo) | prose→Lean English tactic vocabulary | — | unbuildable here (CC removed) | **MINE** — extract its English phrase tables as a vocabulary source; don't import. |
| arXiv 2509.09726 "Informalization of Proof Steps + recursive summarization" | LLM-based informalizer | — | — | **AVOID** — LLM paradigm; violates the "not wrong / no LLM in trusted path" principle. Related work, not reuse. |

## 1. Verso — the most important find, and the deviation it carries

Verso is the official Lean documentation tool. Crucially (and exactly on point):
*"tactic proofs are annotated with their proof states, so the proof can be
understood without having to open the file in a full Lean environment"* — the
proof-state-on-hover UX our design calls for (§8), already built, battle-tested,
HTML output, **and tagged v4.29.0 to match our toolchain**.

**Why not just ADOPT it as the renderer?** Two deviations:
1. **Wrong genre.** Verso renders **Lean *code*** with proof-state annotations.
   It does **not** informalize — no ontology, no Entity/Noun, no English
   *generation*. It would give us the *display* half (annotated HTML, hover proof
   states, collapsibles) but none of the Lean→prose half, which is the project.
2. **Heavy, compiler-coupled dependency.** Verso "tracks the Lean compiler
   closely"; adopting it pulls a large library into a package whose whole
   buildability strategy (per cnl-rs findings) is to stay **`import Lean`-only**
   and dodge mathlib/VCVio/heavy-dep build hell. That is exactly the deviation
   the user warns about.

**Concrete code inspection (via `gh`, `leanprover/verso@main`).** The proof-state
hover lives in `src/verso/Verso/Code/Highlighted/WebAssets.lean`, which ships the
UX by `include_str`-vendoring `popper.min.js`, `tippy-bundle.umd.min.js`,
`marked.umd.min.js`, plus KaTeX (`Verso/Output/Html/KaTeX.lean`); a typed HTML
builder is in `Verso/Output/Html.lean` and the highlighter in
`Verso/Code/Highlighted.lean`. So Verso's hover is **tippy + popper**, its math is
**KaTeX**, and `marked` is a markdown→HTML parser.

**Per user direction, third-party JS deps are acceptable** (pin to current,
non-severely-vulnerable versions; the real security work is in *our* code — see
DESIGN §9). So the earlier "we refuse this stack" objection is withdrawn: we will
**directly reuse KaTeX** for math (as Verso does), and **may reuse tippy** for
hover. We do **not** use `marked` (we emit structured JSON, not markdown — so no
markdown→HTML parser is in the path; that is a *design* choice, not a security
veto).

**Decision on Verso itself: MIRROR now, ADOPT-later** — and the reason is **no
longer the dependencies**. It is (a) **genre mismatch**: Verso renders Lean
*code* with proof-state annotations; it does not *informalize* (no ontology, no
English generation) — so it can supply the *display* half but none of the
Lean→prose half that is this project; and (b) **compiler-coupling**: Verso tracks
the Lean compiler closely and is large, which is a heavy dependency for a package
whose buildability strategy is `import Lean`-only.
- *Now*: mirror Verso's **proven UX and data model** — the
  highlighted-token-with-hover-proof-state interaction (inspired by **Alectryon**,
  Clément Pit-Claudel), goal-states-as-data-alongside-spans, and
  HTML-with-rich-annotations as output. Reuse **KaTeX** (and optionally tippy)
  directly rather than reimplementing them.
- *Later*: a **Verso output genre** — emit our `Explanation` as Verso markup so
  informalized proofs slot into Lean manuals (future work; avoids the heavy dep
  until the core is proven).

## 2. LeanTeX — mirror the precedence logic, don't depend

LeanTeX is the talk's `Expr→LaTeX` component (the `#latex 1+(2+3)`,
`#latex s.sum (λ x => x+1)` examples on the LeanTeX slide *are* its output). It is
Apache-2.0 — same license as our house headers — so its *patterns* are clean to
adapt with attribution.

Deviations: (a) v4.18.0-rc1 vs our v4.29.0 — `Lean.Expr`/`PrettyPrinter` APIs
drift across 11 minor versions, so it is not drop-in buildable; (b) the
genuinely valuable part for arbitrary math is **LeanTeX-mathlib**, which needs
mathlib (excluded).

**Decision: MIRROR.** Our `ExprLatex.lean` implements a *small closed fragment*
(application, `∀`/`→`, `fun`, `=`, projections, named consts w/ a notation table)
and reuses LeanTeX's **core idea**: precedence-driven parenthesization
(`1+(2+3)` vs `(1+2)+3` → `1+2+3`; `2^2^2` vs `(2^2)^2`). We credit LeanTeX in the
module header. We do *not* attempt LeanTeX-mathlib's coverage — out of scope, and
its mathlib dependency is the deviation we refuse.

## 3. Verbose English layer (in-repo) — mine the vocabulary

`verbose-lean/Verbose/English/*` already encodes a prose vocabulary for tactics
(`Since`, `By … we have`, `It suffices`, `We conclude`). It is the *forward*
(prose→Lean) direction, and it is **unbuildable here** (depends on
`Mathlib.Tactic.CC`, removed). But its phrase tables are reusable *data*.

**Decision: MINE.** Extract the tactic→English phrasings into our FTL proof-frame
lexicon (so informalization and Verbose speak the *same* surface vocabulary — the
"companion" relationship of §0.1, realized at the lexicon level, not by import).

## 4. Net effect on the design

- `ExprLatex.lean` — header credits **LeanTeX**; mirrors its precedence logic;
  closed fragment only.
- `web/` renderer — mirrors **Verso/Alectryon** proof-state-hover UX and
  HTML-with-annotations data model; **reuses KaTeX** for math (safe config, §9)
  and may reuse tippy for hover. Security work is in our own JSON→DOM glue, not
  in avoiding deps.
- `FTL.lean` proof-frame lexicon — seeded from **Verbose English** phrasings.
- **Future work** (documented, not built): a Verso output genre; tracking
  LeanTeX-mathlib if/when a mathlib-bearing build is wanted.

Nothing is taken as a hard dependency. Every reuse is a *helper pattern or data
table*, vetted against (i) buildability on our pinned v4.29.0 `import Lean`-only
package and (ii) the zero-dep security boundary — exactly the "wary of
deviations" bar the user set.

## UPDATE — Verso ADOPTED for the presentation layer (decision reversal)

The earlier "MIRROR-not-ADOPT" verdict applied to the *core renderer*. Per user
direction, the **presentation media now reuses Verso directly** via
`leanprover/verso-slides` (the reveal.js genre behind de Moura's ETAPS 2026 deck):
clickable Lean with proof-state panels, vendored offline assets. This lives in
`slides/` — a SEPARATE project on Verso's toolchain (v4.32.0-rc1), pulling Verso
via Lake, so the `import Lean`-only core (v4.29.0) is untouched. The two connect
through `Informalization/VersoEmit.lean` (`Explanation → Verso markup`, pure).
Verified: `slides/` builds and generates a self-contained `_slides/index.html`;
`#informalizeVerso` auto-emits slide-ready markup from a Lean theorem. The
zero-dep standalone renderer (`web/`) remains as a lightweight alternative.
