/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Informalization.Explanation

/-!
# Serializer — `Explanation → Lean.Json`

Stage (G) of the architecture (DESIGN §4): the Lean side emits **inert data**
only (`Lean.Json`), never executable markup, keeping the trust boundary clean
(DESIGN §9). The zero-dependency web renderer (`web/render.js`) consumes exactly
the schema below via `JSON.parse` + `createElement`/`textContent`.

The schema is a load-bearing contract with the renderer — every node serializes
to an object with a `"kind"` discriminator. Do not deviate without updating the
renderer in lockstep.

The `Document` wrapper (theorem metadata + body) is owned by the FTL layer; this
module is the `Explanation`-only serializer.
-/

namespace Informalization

/-- Serialize a `Hyp` line: name, type (LaTeX), and the `changed` highlight flag. -/
def Hyp.toJson (h : Hyp) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", .str h.name)
    , ("type", .str h.type)
    , ("changed", .bool h.changed) ]

/-- Serialize a `GoalState` box: its hypothesis lines and the goal (LaTeX). -/
def GoalState.toJson (g : GoalState) : Lean.Json :=
  Lean.Json.mkObj
    [ ("hyps", Lean.Json.arr (g.hyps.map Hyp.toJson))
    , ("goal", .str g.goal) ]

/-- Serialize an optional provenance tag: the source-term id as a string, or
`null` for a leaf that carries no provenance (Tier-0 / text). -/
def provJson : Option Prov → Lean.Json
  | none   => .null
  | some p => .str p

/-- Serialize an `Explanation` to the renderer's JSON schema (DESIGN §4G). Every
node becomes an object discriminated by its `"kind"` field. Total. -/
def Explanation.toJson : Explanation → Lean.Json
  | .text s          => Lean.Json.mkObj [("kind", .str "text"), ("s", .str s)]
  | .math l p        =>
      Lean.Json.mkObj [("kind", .str "math"), ("latex", .str l), ("prov", provJson p)]
  | .concat xs       =>
      Lean.Json.mkObj [("kind", .str "concat"), ("xs", Lean.Json.arr (xs.map Explanation.toJson))]
  | .paragraph xs    =>
      Lean.Json.mkObj [("kind", .str "paragraph"), ("xs", Lean.Json.arr (xs.map Explanation.toJson))]
  | .indent b        =>
      Lean.Json.mkObj [("kind", .str "indent"), ("body", Explanation.toJson b)]
  | .detail s e sal  =>
      Lean.Json.mkObj
        [ ("kind", .str "detail")
        , ("summary", Explanation.toJson s)
        , ("expanded", Explanation.toJson e)
        , ("salient", .bool sal) ]
  | .clickable a b   =>
      Lean.Json.mkObj
        [ ("kind", .str "clickable")
        , ("label", Explanation.toJson a)
        , ("reveal", Explanation.toJson b) ]
  | .tooltip a b     =>
      Lean.Json.mkObj
        [ ("kind", .str "tooltip")
        , ("anchor", Explanation.toJson a)
        , ("hint", Explanation.toJson b) ]
  | .goalState g     =>
      Lean.Json.mkObj [("kind", .str "goalState"), ("hyps", (g.hyps.map Hyp.toJson) |> Lean.Json.arr), ("goal", .str g.goal)]
  | .displayMath l p =>
      Lean.Json.mkObj [("kind", .str "displayMath"), ("latex", .str l), ("prov", provJson p)]

/-- The compact (no-whitespace) JSON string emitted to `explanation.json`. -/
def Explanation.toJsonString (e : Explanation) : String := e.toJson.compress

/-! ## Tests -/

-- A plain text run.
#guard (Explanation.text "hello").toJson.compress
  = "{\"kind\":\"text\",\"s\":\"hello\"}"

-- Inline math with a provenance tag.
#guard (Explanation.math "x = y" (some "e0")).toJson.compress
  = "{\"kind\":\"math\",\"latex\":\"x = y\",\"prov\":\"e0\"}"

-- Display math with no provenance serializes `prov` as `null`, and a concat of
-- two children round-trips its `xs` array in document order.
#guard (Explanation.concat #[.displayMath "a + b" none, .text "."]).toJson.compress
  = "{\"kind\":\"concat\",\"xs\":[{\"kind\":\"displayMath\",\"latex\":\"a + b\",\"prov\":null},{\"kind\":\"text\",\"s\":\".\"}]}"

end Informalization
