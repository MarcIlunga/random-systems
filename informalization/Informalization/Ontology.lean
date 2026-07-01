/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Grammar

/-!
# `Ontology` — the Lean-4 ↦ English ontology (slide 51)

A strongly-typed reproduction of the talk's ontology (DESIGN §1.3, slides 48–53):
`Entity`s carry a `Noun`, a set of `Adjective`s, and `Accessory`s, with a
`NounTypePayload` for "the type-of" phrasing. An **ontology** is "concepts,
properties, relations + a *mapping* Lean-4 ontology → English ontology — the
better the ontology, the more natural the output."

Entity construction (slides 53–54) runs a **handler** keyed by the head constant
(`@[english_param const.TopologicalSpace]`). We model handlers as a plain typed
**registry** rather than a real Lean attribute (DESIGN §6/§G3): this keeps the
module buildable and decidable, and lets `applyHandlers` provide the project's
**totality / fallback guarantee** — there is *always* a result, the fallback
being identity (no silent gaps).

Deviations from slide 51, all to keep the ontology decidable and serializable:
* `Adjective.expr : Expr` and `Accessory.expr : Expr` become `exprStr : String`.
  An `Expr` is neither `BEq`- nor `Repr`-friendly and would force `import`-heavy,
  non-serializable structures; the provenance link (DESIGN §3.2) lives in the
  `Explanation` leaf, not here. The head constant `kind : Name` is retained.

`Entity.toIntro` bridges the ontology to the grammar merge layer (`Grammar.Intro`),
so this module *feeds* the grammar engine (DESIGN §4, builder (B) → engine (E)).
-/

namespace Informalization.Ontology

open Lean

/-! ## The ontology structures (slide 51) -/

/-- The "type-of" payload of a noun, for phrasing like "a type-`τ` reduction":
the type text it specializes and its singular/plural surface forms. -/
structure NounTypePayload where
  type : String
  text : String
  pluralText : String
  deriving Repr, BEq, Inhabited

/-- A noun in the ontology, keyed by the head constant `kind` it realizes. Carries
the article, the block-level singular/plural text and the inline singular/plural
text (slide 51), plus an optional `typePayload`.

`Name` derives `Repr`/`Inhabited` cleanly, so no derive is dropped here. -/
structure Noun where
  kind : Name
  article : Grammar.Article
  text : String
  pluralText : String
  inlineText : String
  inlinePluralText : String
  typePayload : Option NounTypePayload := none
  deriving Repr, Inhabited

/-- An adjective in the ontology ("open", "dense", "continuous"), keyed by its
head constant. DEVIATION (see header): the talk's `expr : Expr` is modeled as
`exprStr : String` to keep the ontology decidable/serializable. -/
structure Adjective where
  kind : Name
  article : Grammar.Article
  text : String
  exprStr : String := ""
  deriving Repr, Inhabited

/-- An accessory — a "with …" clause attached to an entity ("with basis `B`"),
keyed by its head constant. DEVIATION: `expr : Expr` → `exprStr : String`. -/
structure Accessory where
  kind : Name
  text : String
  exprStr : String := ""
  deriving Repr, Inhabited

/-- An entity: a local variable's English shape. `mentions` are the names this
entity's text/type refers to (feeding `Grammar.crossRef` at merge time). -/
structure Entity where
  name : String
  noun : Option Noun := none
  adjectives : Array Adjective := #[]
  accessories : Array Accessory := #[]
  mentions : List String := []
  deriving Inhabited

/-! ## The context and its update helpers -/

/-- The ontology builder's working state: the entities seen so far (DESIGN §4,
builder (B) output `Context : Array Entity`). -/
abbrev Context := Array Entity

/-- Find the entity with the given name, if any. -/
def findEntity (ctx : Context) (name : String) : Option Entity :=
  ctx.find? (·.name == name)

/-- Append a fresh entity. -/
def pushEntity (ctx : Context) (e : Entity) : Context :=
  ctx.push e

/-- Replace the first entity named `name` via `f`, leaving the rest untouched. If
no such entity exists the context is returned unchanged. -/
private def updateEntity (ctx : Context) (name : String) (f : Entity → Entity) : Context :=
  ctx.map (fun e => if e.name == name then f e else e)

/-- Attach an adjective to the named entity (no-op if it does not exist). -/
def pushAdjective (ctx : Context) (name : String) (a : Adjective) : Context :=
  updateEntity ctx name (fun e => { e with adjectives := e.adjectives.push a })

/-- Attach an accessory to the named entity (no-op if it does not exist). -/
def pushAccessory (ctx : Context) (name : String) (a : Accessory) : Context :=
  updateEntity ctx name (fun e => { e with accessories := e.accessories.push a })

/-- Set (or replace) the noun of the named entity (no-op if it does not exist). -/
def setNoun (ctx : Context) (name : String) (n : Noun) : Context :=
  updateEntity ctx name (fun e => { e with noun := some n })

/-! ## Handlers — the `@[english_param]` registry (DESIGN §6, §G3) -/

/-- A handler transforms an entity, given that its head constant matched `kind`.
This is the typed stand-in for `@[english_param const.X]` (slide 53). -/
structure Handler where
  kind : Name
  run : Entity → Entity

/-- A registry is just an ordered array of handlers; first match wins. -/
def Registry := Array Handler

/-- Run the FIRST handler whose `kind` matches; otherwise return `e` unchanged.

**Totality / fallback guarantee (DESIGN §G3).** There is *always* a result: the
fallback is the identity on `e`. Handler coverage is therefore never a source of
partiality or a silent gap — an unhandled constant yields the entity verbatim,
which the downstream Tier-0 fallback can still phrase. -/
def applyHandlers (reg : Registry) (kind : Name) (e : Entity) : Entity :=
  match reg.find? (·.kind == kind) with
  | some h => h.run e
  | none   => e

/-- An example registry mirroring the talk's `@[english_param]` handlers. Each
handler adds the relevant ontology data and uses `Grammar.indefiniteArticle` to
pick the article (advisory; DESIGN §6.1). -/
def topologyRegistry : Registry := #[
  -- `(T : TopologicalSpace X)` is about a "topological space".
  { kind := `TopologicalSpace,
    run := fun e =>
      let n : Noun :=
        { kind := `TopologicalSpace,
          article := (Grammar.indefiniteArticle "topological space").1,
          text := "topological space",
          pluralText := "topological spaces",
          inlineText := "topological space",
          inlinePluralText := "topological spaces" }
      { e with noun := some n } },
  -- `(h : IsOpen U)` makes `U` "open".
  { kind := `IsOpen,
    run := fun e =>
      let a : Adjective :=
        { kind := `IsOpen,
          article := (Grammar.indefiniteArticle "open").1,
          text := "open" }
      { e with adjectives := e.adjectives.push a } },
  -- `(h : Dense s)` makes `s` "dense".
  { kind := `Dense,
    run := fun e =>
      let a : Adjective :=
        { kind := `Dense,
          article := (Grammar.indefiniteArticle "dense").1,
          text := "dense" }
      { e with adjectives := e.adjectives.push a } }
]

/-! ## Bridge to the grammar engine -/

/-- Convert an `Entity` into a `Grammar.Intro` (DESIGN §4, (B) → (E)). The noun's
block-level text fills singular/plural (defaulting to "object"/"objects" when the
entity has no noun yet — the not-wrong fallback); adjectives and accessories
become their surface texts; `mentions` carries cross-reference information through
to `Grammar.crossRef`. -/
def Entity.toIntro (e : Entity) : Grammar.Intro :=
  let nounSingular := match e.noun with | some n => n.text       | none => "object"
  let nounPlural   := match e.noun with | some n => n.pluralText | none => "objects"
  { name := e.name
    nounSingular := nounSingular
    nounPlural := nounPlural
    adjectives := (e.adjectives.map (·.text)).toList
    accessories := (e.accessories.map (·.text)).toList
    mentions := e.mentions }

/-! ## Tests -/

-- Building an entity and attaching ontology data through the context helpers.
private def demoCtx : Context :=
  let c := pushEntity #[] { name := "X" }
  let c := setNoun c "X"
    { kind := `TopologicalSpace, article := .a
      text := "topological space", pluralText := "topological spaces"
      inlineText := "topological space", inlinePluralText := "topological spaces" }
  pushAdjective c "X" { kind := `IsOpen, article := .a, text := "open" }

#guard (findEntity demoCtx "X").isSome
#guard (findEntity demoCtx "Y").isNone
#guard ((findEntity demoCtx "X").map (·.adjectives.size)) == some 1

-- Applying a handler: `IsOpen` adds the "open" adjective.
#guard ((applyHandlers topologyRegistry `IsOpen { name := "U" }).adjectives.map (·.text))
        == #["open"]

-- Applying a handler: `TopologicalSpace` sets the noun.
#guard ((applyHandlers topologyRegistry `TopologicalSpace { name := "T" }).noun.map (·.text))
        == some "topological space"

-- Totality / fallback: an unhandled constant returns the entity unchanged.
#guard (applyHandlers topologyRegistry `NoSuchClass { name := "Z" }).name == "Z"
#guard (applyHandlers topologyRegistry `NoSuchClass { name := "Z" }).noun.isNone

-- Bridging to the grammar `Intro`: noun + adjective surface in the merge layer.
#guard ((findEntity demoCtx "X").map (fun e => e.toIntro.nounSingular))
        == some "topological space"
#guard ((findEntity demoCtx "X").map (fun e => e.toIntro.adjectives))
        == some ["open"]

-- No-noun entity falls back to "object"/"objects".
#guard (Entity.toIntro { name := "a" }).nounSingular == "object"
#guard (Entity.toIntro { name := "a" }).nounPlural == "objects"

end Informalization.Ontology
