/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# `Explanation` — the structured document type

A strongly-typed, total model of the interactive document the informalizer
produces (DESIGN §5). It realizes exactly the seven features the source talk
lists for its `Explanation` type (slide 64):

1. block indentation        → `indent`
2. paragraph breaks         → `paragraph`
3. (+)/(-) replaceable text → `detail`     (the *show hidden detail* primitive)
4. clickable reveal         → `clickable`
5. tooltips                 → `tooltip`
6. goal states              → `goalState`  (the *proof context* primitive)
7. multiline equations      → `displayMath`

The Lean side only ever emits **data** (`Lean.Json`); the actual rendering to
DOM happens in the zero-dependency web renderer (`web/`). This keeps the trust
boundary clean (DESIGN §9): Lean produces inert JSON, never executable markup.
-/

namespace Informalization

/-- A hypothesis line in a goal-state box: a name and its type (already LaTeX).
`changed := true` marks a hypothesis the current step introduced or altered, so
the renderer can highlight it and fold the rest (the summarized goal state of
DESIGN §8). -/
structure Hyp where
  name : String
  type : String
  changed : Bool := false
  deriving Repr, BEq, Inhabited

/-- A proof goal-state, mirroring the talk's "Current proof state" box: a list of
hypotheses and the goal, both as LaTeX. -/
structure GoalState where
  hyps : Array Hyp := #[]
  goal : String
  deriving Repr, BEq, Inhabited

/-- Provenance tag: an opaque identifier linking a typeset-math leaf back to the
kernel-checked term it was generated from (DESIGN §3.2). The id resolves, in the
describer layer, to a concrete `Lean.Expr`; keeping it a `String` here keeps
`Explanation` dependency-light and JSON-serializable. -/
abbrev Prov := String

/-- The fidelity tier a node achieved (DESIGN §3.3), purely advisory metadata
surfaced as a faint mark in the UI. Decoupled from re-parseability. -/
inductive Tier where
  | fallback    -- Tier 0: stock carrier sentence + raw term
  | structured  -- Tier 1: a real FTL frame, math shown as typeset terms
  | natural     -- Tier 2: ontology-driven noun-notation, articles, merging
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The structured-document type. Total and finite. -/
inductive Explanation where
  /-- A plain text run. Rendered via `textContent` (never markup). -/
  | text (s : String)
  /-- Inline typeset math (LaTeX fragment), with optional provenance. -/
  | math (latex : String) (prov : Option Prov := none)
  /-- In-line concatenation of fragments. -/
  | concat (xs : Array Explanation)
  /-- A paragraph break around its children. -/
  | paragraph (xs : Array Explanation)
  /-- Block indentation of a body. -/
  | indent (body : Explanation)
  /-- Show-hidden-detail: `summary` is shown collapsed; clicking `⊕` swaps in
  `expanded`. The `salient` flag drives the expansion budget (DESIGN §8). -/
  | detail (summary : Explanation) (expanded : Explanation) (salient : Bool := false)
  /-- A clickable label that reveals extra text (e.g. a definition) in place. -/
  | clickable (label : Explanation) (reveal : Explanation)
  /-- An anchor with a hover tooltip. -/
  | tooltip (anchor : Explanation) (hint : Explanation)
  /-- A goal-state box. -/
  | goalState (g : GoalState)
  /-- A centered multiline equation. -/
  | displayMath (latex : String) (prov : Option Prov := none)
  deriving Inhabited

namespace Explanation

/-- Smart constructor: an empty document. -/
def empty : Explanation := .concat #[]

/-- Collect every `(latex, prov)` pair appearing at a math/`displayMath` leaf, in
left-to-right document order. This is the basis of the provenance checker
(`Provenance.lean`): the invariant is a property of exactly this list. -/
partial def provLeaves : Explanation → Array (String × Option Prov)
  | .text _              => #[]
  | .math l p            => #[(l, p)]
  | .displayMath l p     => #[(l, p)]
  | .goalState _         => #[]
  | .indent b            => provLeaves b
  | .detail s e _        => provLeaves s ++ provLeaves e
  | .clickable a b       => provLeaves a ++ provLeaves b
  | .tooltip a b         => provLeaves a ++ provLeaves b
  | .concat xs           => xs.foldl (fun acc x => acc ++ provLeaves x) #[]
  | .paragraph xs        => xs.foldl (fun acc x => acc ++ provLeaves x) #[]

/-- Count the leaves of a document (used for the node budget / tests). -/
partial def size : Explanation → Nat
  | .text _              => 1
  | .math _ _            => 1
  | .displayMath _ _     => 1
  | .goalState _         => 1
  | .indent b            => 1 + size b
  | .detail s e _        => 1 + size s + size e
  | .clickable a b       => 1 + size a + size b
  | .tooltip a b         => 1 + size a + size b
  | .concat xs           => xs.foldl (fun acc x => acc + size x) 1
  | .paragraph xs        => xs.foldl (fun acc x => acc + size x) 1

end Explanation

end Informalization
