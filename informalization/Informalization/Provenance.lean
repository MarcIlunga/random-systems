/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Explanation

/-!
# Provenance — the correctness oracle

The honest, *syntactic* reading of the talk's "output that is not wrong"
(DESIGN §3.2): every `Explanation` leaf that asserts mathematical content carries
the source term `e : Expr` (here an opaque `Prov` id) it was generated from, and
a total checker asserts each math/`displayMath` leaf's LaTeX **equals
`exprToLatex e`** for its recorded `e`.

## What the check actually catches (DESIGN §3.2, Round-2 finding B)

This is a **post-pipeline preservation property**, not a construction-time
tautology. At the *point of construction* a leaf built as `math (exprToLatex e)`
and recorded with that same `e` satisfies the check trivially. The teeth are
that `checkProvenance` runs *after* the grammar realizer, merging, and
serialization, and the `oracle` (`exprToLatex ∘ resolve`) is **pure /
deterministic**. So a re-run of the oracle on each recorded source term must
still reproduce the *displayed* LaTeX. What this detects is therefore any pass
that **swaps, drops, duplicates, or rewrites** a leaf's `(latex, prov)` pairing —
e.g. a merge that re-attaches the wrong source term, or a serializer that
transposes two leaves. "This leaf renders its own term" is *not* the claim.

The `oracle` is kept abstract (`Prov → Option String`) so this module stays
`Explanation`-only: the caller supplies `exprToLatex ∘ resolve`. Leaves with
`prov = none` are Tier-0 / text and are **skipped** (they assert no checkable
mathematical content).

## Structural determinacy of the leaf set

`provLeaves` is structurally determined: the leaf list of a composite node is
the concatenation of its children's leaf lists, in document order. The
`#guard`-style examples below pin this down on concrete inputs — no pass can
fabricate or hide a leaf without it showing up in `provLeaves`. (They are stated
as `example`s rather than `theorem … := by rfl` because `provLeaves` is a
`partial def` in `Explanation.lean`, whose equations the kernel does not unfold
definitionally; an `example`/`#guard` on concrete data exercises the actual
compiled function.)
-/

namespace Informalization

/-- A typed view of one provenance leaf: the displayed LaTeX and its optional
source-term id. Mirrors the pairs produced by `Explanation.provLeaves`. -/
structure ProvEntry where
  latex : String
  prov : Option Prov
  deriving Repr, BEq, Inhabited

/-- The provenance table of a document: every math/`displayMath` leaf, in
document order, as typed `ProvEntry`s. A thin typed re-exposure of the raw
`Explanation.provLeaves` pairs. -/
def Explanation.provTable (e : Explanation) : Array ProvEntry :=
  e.provLeaves.map (fun (l, p) => { latex := l, prov := p })

/-- The provenance check (DESIGN §3.2). For every math/`displayMath` leaf that
**carries** a `prov` tag, re-render the recorded source term through `oracle`
and assert it reproduces the displayed LaTeX (`oracle prov = some latex`).
Leaves with `prov = none` (Tier-0 / text) are skipped. Returns `true` iff every
tagged leaf matches.

`oracle` is `exprToLatex ∘ resolve`, supplied by the caller; keeping it abstract
keeps this module `Explanation`-only and makes explicit that the oracle is a pure
function re-run after the pipeline (see the module doc). -/
def checkProvenance (e : Explanation) (oracle : Prov → Option String) : Bool :=
  e.provLeaves.all fun (latex, prov?) =>
    match prov? with
    | none      => true
    | some prov => oracle prov == some latex

/-! ## Structural determinacy of the leaf set

These pin down that `provLeaves` is a pure structural concatenation: a composite
node's leaves are exactly its children's leaves, in document order.

**Downgraded from `theorem … := by rfl` to `#guard`s on concrete inputs.**
`Explanation.provLeaves` is a `partial def` in `Explanation.lean`; the kernel
does not unfold a `partial` definition's equations definitionally, so the
abstract `(Explanation.concat xs).provLeaves = xs.foldl …` lemma is **not**
provable by `rfl` (it fails with a metavariable type-mismatch). The structural
property is instead exercised on concrete documents, which run the actual
compiled function. The determinacy claim — composite leaves = concatenation of
children's leaves — holds for these witnesses; the abstract theorem would need a
non-`partial` reformulation of `provLeaves` to discharge. -/

-- A pair of distinct leaves used as building blocks below.
private def lf0 : Explanation := .math "x = y" (some "e0")
private def lf1 : Explanation := .displayMath "a + b" (some "e1")

-- `concat`: the leaf list is the children's leaves concatenated, in order.
#guard (Explanation.concat #[lf0, .text "t", lf1]).provLeaves
  = lf0.provLeaves ++ (Explanation.text "t").provLeaves ++ lf1.provLeaves

-- `paragraph`: same structural concatenation as `concat`.
#guard (Explanation.paragraph #[lf0, lf1]).provLeaves
  = lf0.provLeaves ++ lf1.provLeaves

-- `indent`: transparent — the body's leaves, unchanged.
#guard (Explanation.indent lf0).provLeaves = lf0.provLeaves

-- `detail`: summary leaves followed by expanded leaves (the `salient` flag is
-- irrelevant to provenance).
#guard (Explanation.detail lf0 lf1 true).provLeaves = lf0.provLeaves ++ lf1.provLeaves

/-! ## Tests -/

-- A toy oracle: a fixed lookup table mapping source-term ids to their LaTeX.
private def toyOracle : Prov → Option String
  | "e0" => some "x = y"
  | "e1" => some "a + b"
  | _    => none

-- PASS: every tagged leaf renders to exactly what the oracle says; the untagged
-- `text` leaf is skipped.
#guard checkProvenance
  (.concat #[.math "x = y" (some "e0"), .text "and", .displayMath "a + b" (some "e1")])
  toyOracle = true

-- PASS (vacuous): no leaf carries a `prov`, so nothing is checked.
#guard checkProvenance (.concat #[.math "anything" none, .text "."]) toyOracle = true

-- FAIL: the displayed LaTeX `"x = z"` does not match the oracle's `"x = y"` for
-- source term `e0` — exactly the swap/rewrite class of bug the check catches.
#guard checkProvenance (.math "x = z" (some "e0")) toyOracle = false

end Informalization
