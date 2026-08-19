/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.HtmlDisplay

/-!
# THROWAWAY SPIKE — Penrose vs. our hand-computed emitter, same CC figure

**This file is not part of the library.**  It is imported by nothing
(`RandomSystems.lean` and every aggregator deliberately do not mention it),
it defines no mathematics, and it should be deleted once the renderer
question is settled.  It exists for exactly one purpose: to put the SAME
Constructive-Cryptography figure on the screen twice — once through
`#cc_diagram`'s positioned-`div` emitter, once through
`ProofWidgets.Penrose.PenroseDiagram` — so that the two can be compared by
eye and by cost.

## The figure

`decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR))`
(`RandomSystems.CC.CarrierDemo.constructedShape`), which the gallery draws
as *"two connections, the eq.-(1) shape (item 28)"* — Jost Fig. 2.1's
π_ε^A / π_ε^B over `[KEY, AUT]`.  Two resource rows in a `∥`; a connection
on each flank, each FORKED onto one interface of each row; one outer wire
per connection crossing the dashed specification boundary.

Sizes are DESIGN.md §12's own tokens (resource 120×44, pill 76×34 radius
17, row gap 10, boundary pad 12, wire `#555`, converter `#1E8449`, assumed
resource `#2563C4`, fork pitch 22, connection lead 34, lead-in 16) so the
two pictures are dimensionally comparable rather than merely similar.

## What this file CANNOT tell you

The Penrose output cannot be rendered outside the Lean infoview on this
machine: `penroseDisplay.js` is a 2.8 MB widget module that wants the
infoview's React runtime, and there is no `node`/`npm` here to drive
`@penrose/core` standalone.  `lake env lean` therefore checks that the
props typecheck and that the three programs are embedded as strings —
**nothing about the picture**.  The trio below has never been rendered.

## How to look at it

Open this file in VS Code and put the cursor on the `#html` command at the
bottom (`spikeWithLabels` / `spikeBare`).  The diagram appears in the
infoview under the command.  A small refresh glyph in the diagram's
top-right corner re-rolls Penrose's random `variation`; see the notes on
determinism at the bottom of this file.
-/

namespace RandomSystems.CC.PenroseSpike

open Lean ProofWidgets

/-! ## The domain program (`dsl`)

Vocabulary from DESIGN.md §12: resources and converters (item 13), the
interfaces a CONNECTION reaches (item 28), the box that OWNS the interface
a branch names (item 31), the `∥` row order (item 30(a)), the
specification boundary (item 3), and Maurer11's roles (item 5). -/

def ccDsl : String := r#"-- Constructive Cryptography, as much of DESIGN.md §12 as a Penrose domain
-- can carry.  Throwaway spike.

type Object
type Resource <: Object
type Converter <: Object
type Interface
type Boundary

-- §12 item 30(a): the `∥` row order.  `above` is the row printed first.
predicate StackedAbove(Resource above, Resource below)

-- §12 item 2: which flank a spine converter takes (the n = 2 geography).
predicate LeftFlank(Converter c)
predicate RightFlank(Converter c)

-- §12 item 28: Jost's γ — the interfaces `α ••[γ] R` reaches at once.
predicate Reaches(Converter c, Interface i)

-- §12 item 31: the box that OWNS the interface a branch names.  This is
-- `Diagram.reachAt`, i.e. `Connection.untouched` descended to the base
-- resource — computed in Lean, asserted here.
predicate Owns(Resource r, Interface i)

-- Jost's I_out: the single outer interface a connection PRODUCES.
predicate Produces(Converter c, Interface o)

-- §12 item 3: inside the dashed specification boundary.
predicate Inside(Object o, Boundary b)

-- §12 item 5: Maurer11's role palette.
predicate Assumed(Object o)
predicate Protocol(Object o)
"#

/-! ## The substance program (`sub`)

One declaration per node of the term.  Every `Owns` line is a fact the
Lean side already computes (`Diagram.descendInterface`); Penrose is told
it, it does not discover it. -/

def ccSub : String := r#"-- decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR))
-- = RandomSystems.CC.CarrierDemo.constructedShape

Resource keyRow
Resource autRow
StackedAbove(keyRow, autRow)
Assumed(keyRow)
Assumed(autRow)

Converter encA
Converter decB
Protocol(encA)
Protocol(decB)
LeftFlank(encA)
RightFlank(decB)

-- γ^A reaches interface `u` of BOTH rows (Jost: "interface A of Key" and
-- "interface A of AuthChan").
Interface encAkey
Interface encAaut
Reaches(encA, encAkey)
Reaches(encA, encAaut)
Owns(keyRow, encAkey)
Owns(autRow, encAaut)

-- γ^B reaches interface `v` of both rows.
Interface decBkey
Interface decBaut
Reaches(decB, decBkey)
Reaches(decB, decBaut)
Owns(keyRow, decBkey)
Owns(autRow, decBaut)

-- The two outer wires that cross the boundary.
Interface outA
Interface outB
Produces(encA, outA)
Produces(decB, outB)

Boundary spec
Inside(keyRow, spec)
Inside(autRow, spec)
Inside(encA, spec)
Inside(decB, spec)
"#

/-! ## The style program (`sty`)

Written against the vendored Penrose (`@penrose/core ~3.2.0`), checked
against `widget/penrose/venn.sty` and `euclidean.sty` rather than against
the current online docs.

Two conventions are borrowed from the vendored `penroseCanvas.tsx`: every
object that carries an `embeds` entry must have a `.textBox : Rectangle`
(whose width/height the widget then overrides to the measured HTML size),
and per-object literals are set through backtick-quoted selectors, which
is the idiom the widget's own `compileWithSizes` emits. -/

def ccSty : String := r#"-- CC connection diagram, DESIGN.md §12 geometry.  Throwaway spike.
-- Penrose's canvas is y-UP, so "above" means a larger y.

Colors {
  wire      = #555555
  converter = #1e8449
  assumed   = #2563c4
  boundary  = #888888
  clear     = none()
}

-- §12 item 1: the fixed grid.  Every number here is a §12 token.
const {
  resW      = 120
  resH      = 44
  pillW     = 76
  pillH     = 34
  pillR     = 17
  rowGap    = 10
  padX      = 12
  forkPitch = 22
  connLead  = 34
  leadIn    = 16
  stub      = 30
  stroke    = 2
  tagRise   = 9
}

-- §12 item 5: role palette, colour reinforcing shape (item 13).
forall Object o {
  o.color = Colors.wire
}

forall Object o
where Assumed(o) {
  o.color = Colors.assumed
}

forall Object o
where Protocol(o) {
  o.color = Colors.converter
}

-- §12 item 13: a resource is a RECTANGLE at item 1's fixed grid size.
forall Resource r {
  r.center = (?, ?)

  r.icon = Rectangle {
    center         : r.center
    width          : const.resW
    height         : const.resH
    cornerRadius   : 2
    fillColor      : Colors.clear
    strokeColor    : r.color
    strokeWidth    : const.stroke
    ensureOnCanvas : false
  }

  r.textBox = Rectangle {
    center         : r.center
    width          : 1
    height         : 1
    fillColor      : Colors.clear
    strokeColor    : Colors.clear
    ensureOnCanvas : false
  }
}

-- §12 items 13 + 28: a converter is a ROUNDED pill, grown by one
-- `forkPitch` per EXTRA branch of the connection it carries.  The `+ 1 *`
-- is baked in: a plain `forall` block cannot count the matches of
-- `Reaches(c, _)`.  (Penrose 3.2 does ship `collect ... into ... foreach`
-- and `numberof`, so `c.arity = numberof reached` would express it; it is
-- not used here because this spike cannot be run to test the syntax.)
forall Converter c {
  c.center = (?, ?)

  c.icon = Rectangle {
    center         : c.center
    width          : const.pillW
    height         : const.pillH + const.forkPitch
    cornerRadius   : const.pillR
    fillColor      : Colors.clear
    strokeColor    : c.color
    strokeWidth    : const.stroke
    ensureOnCanvas : false
  }

  c.textBox = Rectangle {
    center         : c.center
    width          : 1
    height         : 1
    fillColor      : Colors.clear
    strokeColor    : Colors.clear
    ensureOnCanvas : false
  }
}

-- §12 item 29: a wire is a two-bend orthogonal route.  THREE STRAIGHT
-- SEGMENTS here: Penrose has no orthogonal router and no quarter-arc
-- corner primitive, so `radius.bend` = 6 has no counterpart and the
-- corners are sharp.
forall Interface i {
  i.from  = (?, ?)
  i.to    = (?, ?)
  i.turnX = ?

  i.bend1 = (i.turnX, i.from[1])
  i.bend2 = (i.turnX, i.to[1])

  i.lead = Line {
    start       : i.from
    end         : i.bend1
    strokeColor : Colors.wire
    strokeWidth : const.stroke
    style       : "solid"
  }

  i.jog = Line {
    start       : i.bend1
    end         : i.bend2
    strokeColor : Colors.wire
    strokeWidth : const.stroke
    style       : "solid"
  }

  i.entry = Line {
    start       : i.bend2
    end         : i.to
    strokeColor : Colors.wire
    strokeWidth : const.stroke
    style       : "solid"
  }

  -- §12 item 31(g): the label rides the segment that ARRIVES.
  i.tag = Text {
    center    : (?, ?)
    string    : "?"
    fontSize  : "11px"
    fillColor : Colors.wire
  }

  ensure i.tag.center[0] == (i.bend2[0] + i.to[0]) / 2
  ensure i.tag.center[1] == i.to[1] + const.tagRise
}

-- §12 item 30(a): the `∥` stack is a column, one `rowGap` apart.
forall Resource r; Resource s
where StackedAbove(r, s) {
  ensure r.center[0] == s.center[0]
  ensure r.center[1] == s.center[1] + const.resH + const.rowGap
}

-- §12 item 31(c): a fork is centred on the MEAN of the axes of the rows
-- its branches land on.
forall Converter c; Interface i; Interface j; Resource r; Resource s
where Reaches(c, i); Reaches(c, j); Owns(r, i); Owns(s, j) {
  ensure c.center[1] == (r.center[1] + s.center[1]) / 2
}

-- §12 item 28(iv), THE FORK, as a placement constraint rather than a
-- post-hoc measurement: one rung per interface reached, symmetric about
-- the pill's axis, at exactly `forkPitch`.  (Squared, to avoid `abs`.)
forall Converter c; Interface i; Interface j
where Reaches(c, i); Reaches(c, j) {
  ensure i.from[1] + j.from[1] == 2 * c.center[1]
  ensure (i.from[1] - j.from[1]) * (i.from[1] - j.from[1])
           == const.forkPitch * const.forkPitch
}

-- §12 item 30(c), TARGET ORDER: the rung order follows the row order, so
-- the two branches of one fork cannot cross.
forall Converter c; Interface i; Interface j; Resource r; Resource s
where Reaches(c, i); Reaches(c, j); Owns(r, i); Owns(s, j);
      StackedAbove(r, s) {
  ensure i.from[1] > j.from[1]
}

-- The branch leaves the pill's CORE-facing edge, then gets `leadIn` of
-- straight wire before it may turn (§12 items 28, 31(g)).
forall Converter c; Interface i
where LeftFlank(c); Reaches(c, i) {
  ensure i.from[0] == c.center[0] + const.pillW / 2
  ensure i.turnX  == i.from[0] + const.leadIn
}

forall Converter c; Interface i
where RightFlank(c); Reaches(c, i) {
  ensure i.from[0] == c.center[0] - const.pillW / 2
  ensure i.turnX  == i.from[0] - const.leadIn
}

-- ★ §12 item 31(e), THE TARGET INVARIANT — the `wrong-target` check that
-- our renderer can only make as a post-hoc measurement in the browser.
-- Here it is a PLACEMENT CONSTRAINT: the branch's landing point lies on
-- the perimeter of the box that owns the interface it names, on that
-- box's own port axis (§12 item 11(a)).  Nothing pins its x: the side is
-- bracketed and `signedDistance == 0` supplies the edge.
forall Interface i; Resource r
where Owns(r, i) {
  ensure signedDistance(r.icon, i.to) == 0
  ensure i.to[1] == r.center[1]
}

forall Converter c; Interface i; Resource r
where LeftFlank(c); Reaches(c, i); Owns(r, i) {
  ensure i.to[0] < r.center[0]
  ensure i.to[0] > r.center[0] - const.resW
}

forall Converter c; Interface i; Resource r
where RightFlank(c); Reaches(c, i); Owns(r, i) {
  ensure i.to[0] > r.center[0]
  ensure i.to[0] < r.center[0] + const.resW
}

-- The outer wire: one lead on the pill's own axis, crossing the dashed
-- boundary (§12 items 3, 4, 28).  It is level, so `turnX` sits on the
-- start and the two bends degenerate.
forall Converter c; Interface o
where LeftFlank(c); Produces(c, o) {
  ensure o.from[0] == c.center[0] - const.pillW / 2
  ensure o.from[1] == c.center[1]
  ensure o.turnX   == o.from[0]
  ensure o.to[1]   == o.from[1]
  ensure o.to[0]   == o.from[0] - const.stub
}

forall Converter c; Interface o
where RightFlank(c); Produces(c, o) {
  ensure o.from[0] == c.center[0] + const.pillW / 2
  ensure o.from[1] == c.center[1]
  ensure o.turnX   == o.from[0]
  ensure o.to[1]   == o.from[1]
  ensure o.to[0]   == o.from[0] + const.stub
}

-- §12 item 3: DASHED = the specification boundary.  Item 11(b) wants the
-- pad EXACT and PER AXIS (12, 14); `contains` gives a one-sided isotropic
-- `>=`, so the tightest Penrose statement available is "contain with at
-- least `padX`, and be as small as possible".  The 14 is unreachable.
forall Boundary b {
  b.icon = Rectangle {
    center       : (?, ?)
    width        : ?
    height       : ?
    cornerRadius : 4
    fillColor    : Colors.clear
    strokeColor  : Colors.boundary
    strokeWidth  : const.stroke
    strokeStyle  : "dashed"
  }

  encourage minimal(b.icon.width)
  encourage minimal(b.icon.height)
}

forall Boundary b; Object o
where Inside(o, b) {
  ensure contains(b.icon, o.icon, const.padX)
}

-- Per-object wire labels.  §12 item 31(d): both rows print `toyR`, so the
-- name addresses nothing and the row POSITION is used instead.  One block
-- per object is the only way to attach a literal to a single substance
-- object; this is the idiom `penroseCanvas.tsx` itself emits.
forall Interface `encAkey` {
  override `encAkey`.tag.string = "1.u"
}

forall Interface `encAaut` {
  override `encAaut`.tag.string = "2.u"
}

forall Interface `decBkey` {
  override `decBkey`.tag.string = "1.v"
}

forall Interface `decBaut` {
  override `decBaut`.tag.string = "2.v"
}

forall Interface `outA` {
  override `outA`.tag.string = "gammaU"
}

forall Interface `outB` {
  override `outB`.tag.string = "gammaV"
}
"#

/-! ## The embeds

`embeds` is the ONE addressable surface Penrose output has: each entry is
arbitrary `Html` (hence any `ProofWidgets.Component`, `MakeEditLink`
included) mounted as a React child, absolutely positioned over the
`x.textBox` rectangle of the named substance object.  Everything Penrose
itself draws is an opaque SVG appended by raw DOM manipulation — see the
notes at the bottom.

The `title` attributes below stand in for the hover text `#cc_diagram`
puts on every box. -/

private def boxLabel (text color tip : String) : Html :=
  .element "span"
    #[("title", tip),
      ("style", Json.mkObj [
        ("fontFamily", "'JetBrains Mono', ui-monospace, monospace"),
        ("fontSize", "13px"),
        ("color", color),
        ("whiteSpace", "nowrap"),
        ("padding", "0 4px")])]
    #[.text text]

/-- The four box labels, keyed by their substance names.  Each name must
exist in `ccSub` and must have a `.textBox : Rectangle` in `ccSty`. -/
def spikeEmbeds : Array (String × Html) := #[
  ("keyRow", boxLabel "toyR" "#2563c4"
    "row 1 of `toyR ∥ toyR` — Jost Fig. 2.3's Key"),
  ("autRow", boxLabel "toyR" "#2563c4"
    "row 2 of `toyR ∥ toyR` — Jost Fig. 2.3's AuthChan"),
  ("encA", boxLabel "encA" "#1e8449"
    "encA ••[gammaU] — Jost Fig. 2.1's π_ε^A, reaching u of both rows"),
  ("decB", boxLabel "decB" "#1e8449"
    "decB ••[gammaV] — Jost Fig. 2.1's π_ε^B, reaching v of both rows")]

/-! ## The two renders

`maxOptSteps` is raised from the default 500 because every §12 rule above
is a hard equality and the optimizer pays for each one.  Non-convergence
is reported only as a `console.warn` in the widget; there is no way to
read it back from Lean. -/

/-- The spike as intended: Penrose geometry, HTML labels through `embeds`. -/
def spikeWithLabels : Html :=
  .ofComponent Penrose.Diagram
    { embeds := spikeEmbeds, dsl := ccDsl, sty := ccSty, sub := ccSub,
      maxOptSteps := 2000 } #[]

/-- The same trio with no embeds at all — the fallback if the embed name
lookup (a `textContent` regex in `penroseCanvas.tsx`) fails.  The boxes
render unlabelled; the geometry is the same. -/
def spikeBare : Html :=
  .ofComponent Penrose.Diagram
    { embeds := #[], dsl := ccDsl, sty := ccSty, sub := ccSub,
      maxOptSteps := 2000 } #[]

-- ▼ PUT THE CURSOR ON THE NEXT LINE to see the Penrose render in the infoview.
#html spikeWithLabels

-- ▼ …and on this one for the no-embeds fallback.
#html spikeBare

/-! ## Findings, recorded here so the file is self-contained

**1. What §12 becomes.**  Almost all of the *relational* grammar states
cleanly as `ensure`/`encourage`, and the statements read like the spec:

* item 30(a), the `∥` order — `ensure r.center[1] == s.center[1] + resH +
  rowGap`;
* item 28(iv), the fork — symmetry about the pill axis plus a squared
  pitch equality, which is exactly the `cc-conn-<n>` audit check;
* item 30(c), target order — `ensure i.from[1] > j.from[1]` under
  `StackedAbove(r, s)`;
* item 31(c), mean-of-axes fork centring — one line;
* **item 31(e), the `wrong-target` invariant** — `ensure
  signedDistance(r.icon, i.to) == 0` under `Owns(r, i)`.  It IS expressible
  as a placement constraint.  Two qualifications: Penrose's `ensure` is a
  penalty term in an optimization, so this is a *target*, not a gate — a
  non-converged run draws the wrong picture and says so only in the browser
  console; and the *claim* `Owns(r, i)` still has to be computed in Lean by
  `Diagram.descendInterface`, exactly as DESIGN §12 item 31(i)(d) already
  says of our own audit.

**2. What does not state.**  (a) Exact anisotropic frame pads (item
11(b)): `contains(a, b, pad)` is one-sided and isotropic, so 12/14 is out
of reach; `encourage minimal(...)` only approximates the tight fit.
(b) The quarter-arc bend (item 29, `radius.bend` = 6): no orthogonal
router, no corner primitive; the routes above are three straight `Line`s
with sharp corners.  (c) Fork arity from the term — a plain `forall`
cannot count `Reaches(c, _)` matches, so the pill height is hard-coded for
two branches.  Penrose 3.2 *does* have `collect … into … foreach`,
`numberof`, `listof`, `maxList`/`minList`, which would express both this
and the exact frame pad; untested here.  (d) Planarity (item 30(b)) as
stated: `disjoint` on two wires forbids T-junctions too, and Penrose has no
"relative interior" notion.  (e) The medium: §12 item 10 makes diagrams
live DOM divs and bans SVG; Penrose emits SVG only.

**3. Determinism.**  Penrose's RNG seed is the `variation` string.
`penroseCanvas.tsx` starts it at `undefined` and passes `''` to the
compiler, so a first draw of a fixed trio is reproducible — but the seed is
NOT exposed through `DiagramProps`: the only way to change it is the
refresh glyph, which sets `Math.random().toString()`.  Two real
non-determinisms remain.  The style program is post-fixed with `canvas {
width = max(400, containerWidth); height = <the same> }`, so **the layout
is a function of the infoview's width**; and `embeds` feed their *measured*
pixel sizes back into the style.  Results are memoized by a SHA-1 of
dsl+sty+sub+embed sizes, and that digest is computed over a buffer whose
offsets are miscomputed (`data.subarray(written2)` should be
`subarray(written + written2)`), so the hash is not injective — distinct
trios can in principle collide onto a cached SVG.

**4. Addressability.**  `penrose.toSVG` names each shape only by an SVG
`<title>` child holding its style path (`` `encA`.icon ``); `id` is used
only for markers, filters and clip paths, and there are no classes and no
`data-*`.  The SVG is inserted with `ref.appendChild`, i.e. outside React,
so no `MakeEditLink` (or any component) can be attached to a Penrose-drawn
shape.  The single addressable surface is `embeds`: those are React
children of the canvas, positioned over `x.textBox`, and they take
arbitrary `Html` — so the D4 interaction model would survive only by
routing every clickable node through an embed, one per object, with the
embed's measured size feeding back into the layout.  Wires, forks and the
boundary could not be made clickable at all.

**5. Line count, same figure.**  dsl 33, sub 44, sty 289 — 366 lines of
Penrose (254 once comments and blanks are dropped) for ONE figure.  Our
side emits that figure as 34 positioned `div`s (4 boxes, 1 boundary, 14
wires, 8 bends, 6 tags, 1 container) out of a 2607-line general emitter
that covers all 43 gallery figures, i.e. ~61 emitter lines per figure
amortized — but 44 of the Penrose lines are the substance, which is the
only part that would be generated per term; the other 322 are the grammar,
written once.  So the honest reading is that Penrose is cheap per *rule*
and expensive per *figure*, and buys the target invariant as a constraint
at the cost of the DOM medium, exact pads, bends, and per-node
addressability.
-/

end RandomSystems.CC.PenroseSpike
