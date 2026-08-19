/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceWidgets

/-!
# The visual test corpus and gallery generator (DESIGN §12 item 8)

The §12 design system demands that every rendering case be LOOKED AT:
"Gallery generated as HTML from the widget's own Html tree and inspected
in a browser against the source figures."  This module delivers that
loop:

* the **corpus** — one named term per §12-item-8 case: single, `∥`×2,
  `∥`×3, attach at one/both parties, full construction with simulator
  (real and ideal side), blocked, nested, long-label stress, deep-chain
  stress, the glyph channels, and the MaRuTa12-Fig.-1 layout target;
  plus one per sourced-grammar convention (§12 items 13–18): the
  n-party ladder at three unrecognised interfaces, two simulators at
  distinct interfaces, a filtered party and a filtered adversary
  interface, a free interface above, and the one genuinely unnameable
  interface that still falls back;
* a plain-HTML **serializer** for `ProofWidgets.Html` — the gallery page
  shows *exactly* the tree the infoview panel shows (React's Json style
  objects are re-emitted as CSS strings, camelCase → kebab-case);
* the `#cc_gallery "path" [ "name" => term, … ]` command, which renders
  every case (a term whose TYPE is an equality or `≈[ε]` statement
  renders as the §12-item-6 figure pair) next to its ASCII structure
  receipt and writes one self-contained page.

Serializer limitation (documented, not hit): an `Html.component` node
carries lazily-encoded React props that cannot be evaluated outside the
infoview, so it serializes as a bare `<div data-component="opaque">`
around its children.  `Diagram.html` emits only `element`/`text` nodes,
so the gallery is exact for everything the diagram renderer draws.

The corpus terms deliberately include semantically-idle attachments
(e.g. re-attaching at an already-converted interface): the gallery tests
the RENDERER, and shape discovery is syntactic.  One consequence is worth
knowing, because it is visible on the page: D2 named-subterm recognition
is *semantic*, so it sees through an idle attachment — `enc₂^a (KEY ∥ AUT)`
is definitionally `NET` at this layout (a converter whose inner side is a
PAIRED service misses a single interface's base one), and the collapsed
compound is therefore labelled `NET` rather than left anonymous.  That is the feature
working, not a mislabel; the anonymous-compound case next to it is the
one that exercises the corner label.  The Fig.-1 target uses
a homogeneous `KEY ∥ AUT` stand-in — the heterogeneous
`•══• ∥ •—→` composite is the open padding-transport ledger item
(STATUS), not a rendering question.
-/

namespace RandomSystems.CC.Gallery

open RandomSystems.CR18.TypedResource
open Lean Elab Command Meta ProofWidgets
open CarrierDemo AlgebraDemo Channels
open scoped Converter ResourceSystem

/-! ## The corpus development: a three-party twin of the carrier demo -/

/-- The carrier-demo services laid out over the three parties of
`AlgebraDemo.Party3` (`a`, `b`, `e`) — the geography needs a genuine
A/B/E boundary. -/
abbrev plainLayoutG : demoServices.Layout Party3 := fun _ => .base .plain

/-- A toy deterministic box at the all-plain three-party layout. -/
def galleryBox : Machine demoServices.sig plainLayoutG where
  State := Unit
  init := ()
  step _ _query := some ((), (false : Bool))

noncomputable def toyG : ResourceSystem demoServices Party3 :=
  ResourceSystem.ofLayout
    (DependentRandomSystem.ofProb
      ⟨Finsupp.single galleryBox.toDDS 1, RandomSystems.Dist.isProbDist_single _⟩)

/-- The Fig.-2.2 key, as a display-named stand-in. -/
@[cc_display "KEY", cc_role assumed]
noncomputable def keyG : ResourceSystem demoServices Party3 := toyG

/-- The Fig.-2.2 authenticated channel, as a display-named stand-in. -/
@[cc_display "AUT", cc_role assumed]
noncomputable def autG : ResourceSystem demoServices Party3 := toyG

/-- The constructed resource of the ideal side. -/
@[cc_display "SEC", cc_role constructed]
noncomputable def secG : ResourceSystem demoServices Party3 := toyG

/-- The named network `KEY ∥ AUT` — the D1/D2 target: `unfold NET` opens
it into its stack, and `fold KEY ∥ AUT` (no `as`) closes the stack back
under THIS name, found by definitional recognition. -/
@[cc_display "NET", cc_role assumed]
noncomputable def netG : ResourceSystem demoServices (Party3 ⊕ Party3) :=
  keyG ∥ autG

@[cc_display "enc", cc_role converter]
noncomputable def encG : Converter demoServices (.base .plain) (.base .masked) :=
  Converter.ofMaps id (fun b => !b)

@[cc_display "dec", cc_role converter]
noncomputable def decG : Converter demoServices (.base .plain) (.base .masked) :=
  Converter.ofMaps id (fun b => !b)

@[cc_display "sim", cc_role simulator]
noncomputable def simG : Converter demoServices (.base .plain) (.base .masked) :=
  Converter.ofMaps id id

/-- A converter whose inner side is the PAIRED service of two interfaces —
Jost Fig. 2.3's shape.  Attached at a SINGLE interface of a `∥` it is idle
(that interface provides a base service, not a paired one), which is what
makes the D2-recognition case below honest: `enc₂^a (KEY ∥ AUT)` really is
`NET`. -/
@[cc_display "enc₂", cc_role converter]
noncomputable def encPairG :
    Converter demoServices
      (.sum (.base .plain) (.base .plain)) (.base .masked) :=
  Converter.ofMaps Sum.inl (Sum.elim id id)

/-- The long-label stress case: 66 codepoints of display name against a
12-codepoint box budget. -/
@[cc_display "TheAbsurdlyLongResourceNameThatUsedToStretchTheEntireDiagramWidth",
  cc_role assumed]
noncomputable def longNameG : ResourceSystem demoServices Party3 := toyG

/-- The deep-chain stress case: six spine converters, parties
alternating, the simulator innermost. -/
noncomputable def chainG : ResourceSystem demoServices Party3 :=
  encG •[Party3.a] (decG •[Party3.b] (encG •[Party3.a]
    (decG •[Party3.b] (encG •[Party3.a] (simG •[Party3.e] toyG)))))

/-- The MaRuTa12-Fig.-1 layout target: `enc` on the A flank, `dec` on
the B flank, `sim` below, `KEY` stacked over `AUT` in the dashed box. -/
noncomputable def fig1G : ResourceSystem demoServices (Party3 ⊕ Party3) :=
  simG •[Sum.inl Party3.e] (decG •[Sum.inl Party3.b]
    (encG •[Sum.inl Party3.a] (keyG ∥ autG)))

/-- The `≈[ε]` face of the pair renderer, on the corpus toys. -/
theorem toyG_close : toyG ≈[(0 : ℝ)] toyG :=
  (ResourceSystem.close_zero_iff _ _).mpr rfl

/-- The game-role case: §2.2.6's CPA game as a display-named stand-in —
exercises the grey palette entry and the small-caps non-color signal. -/
@[cc_display "CPA₀", cc_role game]
noncomputable def cpa0G : ResourceSystem demoServices Party3 := toyG

/-! ## The n-party development (§12 items 14–18)

`Party3`'s `a`/`b`/`e` are exactly the paper letters, so it can only ever
exercise item 2's n = 2 geography.  This second party type carries none of
them among its parties: `p1 p2 p3` are unrecognised names and must take
NUMBERED SLOTS on the party flank (item 14), `m2` is BBM18's per-party
intruder interface, `e` the adversary, and `f` Jost's free interface
(item 18: the one other stroke, dotted). -/

inductive PartyN | p1 | p2 | p3 | e | m2 | f
  deriving DecidableEq

abbrev plainLayoutN : demoServices.Layout PartyN := fun _ => .base .plain

def galleryBoxN : Machine demoServices.sig plainLayoutN where
  State := Unit
  init := ()
  step _ _query := some ((), (false : Bool))

noncomputable def toyN : ResourceSystem demoServices PartyN :=
  ResourceSystem.ofLayout
    (DependentRandomSystem.ofProb
      ⟨Finsupp.single galleryBoxN.toDDS 1, RandomSystems.Dist.isProbDist_single _⟩)

/-- An interface named by a COMPUTATION, not a name: `partyOf 0` prints
with a space, so it cannot key a slot in the item-14 ladder.  This is the
one genuine `data-geography="fallback"` — the corpus has to contain it or
the fallback branch is untested folklore. -/
def partyOf : Nat → PartyN
  | 0 => .p1
  | 1 => .p2
  | _ => .p3

/-! ## Connections (§12 item 28, Jost Fig. 2.1)

Two corpus cases, because a connection reaches two interfaces and there are
exactly two ways for those to sit: **across a `∥`** (Jost's own γ^A — int. A
of `Key` and int. A of `AuthChan`, which is `CarrierDemo.gammaU` over
`toyR ∥ toyR`), and **inside ONE resource** (two interfaces of a single box,
which lands both branches on one edge as a two-rung port ladder).  The
second has no counterpart in the carrier demo, so it is defined here. -/

/-- **A connection reaching two interfaces of ONE resource**: `a` and `b` of
a three-party box, leaving `e` untouched.  Jost Fig. 2.1 only draws the
across-a-`∥` case; this is the same γ with both feet on one box, and the
picture must put two rungs on that box's edge rather than two buses into two
rows. -/
def gammaAB : Connection Party3 Unit where
  split :=
    { toFun := fun
        | .a => .inr (.inl ())
        | .b => .inr (.inr ())
        | .e => .inl ()
      invFun := fun
        | .inr (.inl ()) => .a
        | .inr (.inr ()) => .b
        | .inl () => .e
      left_inv := by rintro (_ | _ | _) <;> rfl
      right_inv := by rintro (⟨⟩ | ⟨⟩ | ⟨⟩) <;> rfl }

/-! ## The serializer: the widget's own Html tree, as plain HTML -/

def escapeHtml (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | c => acc.push c) ""

/-- React style keys are camelCase; CSS wants kebab-case. -/
def cssKey (s : String) : String :=
  s.foldl (fun acc c =>
    if c.isUpper then (acc.push '-').push c.toLower else acc.push c) ""

def jsonScalar : Json → String
  | .str s => s
  | .num n => toString n
  | j => j.compress

/-- A React Json style object as a CSS declaration string. -/
def styleString : Json → String
  | .obj kvs =>
      kvs.foldl (fun acc k v => acc ++ s!"{cssKey k}: {jsonScalar v}; ") ""
  | _ => ""

def attrString : String × Json → String
  | ("style", v) => s!" style=\"{escapeHtml (styleString v)}\""
  | (k, v) => s!" {k}=\"{escapeHtml (jsonScalar v)}\""

/-- Serialize the widget tree.  `component` nodes cannot be evaluated
outside the infoview and become a marked `div` around their children —
`Diagram.html` never emits one. -/
partial def htmlString : Html → String
  | .element tag attrs children =>
      let attrsStr := String.join (attrs.toList.map attrString)
      let childrenStr := String.join (children.toList.map htmlString)
      s!"<{tag}{attrsStr}>{childrenStr}</{tag}>"
  | .text s => escapeHtml s
  | .component _ _ _ children =>
      s!"<div data-component=\"opaque\">{String.join
        (children.toList.map htmlString)}</div>"

def sectionHtml (name diagram ascii : String) : String :=
  "<section><h2>" ++ escapeHtml name ++ "</h2><div class=\"case\">" ++
    "<div class=\"diagram\">" ++ diagram ++ "</div>" ++
    "<pre class=\"ascii\">" ++ escapeHtml ascii ++ "</pre></div></section>"

def pageCss : String :=
  "body { font-family: -apple-system, 'Segoe UI', sans-serif; margin: 24px; " ++
    "max-width: 1200px; color: #222; } " ++
  "h1 { font-size: 20px; } " ++
  "p.note { color: #666; font-size: 13px; } " ++
  "section { border-bottom: 1px solid #ddd; padding: 10px 0 18px; } " ++
  "h2 { font-family: monospace; font-size: 14px; color: #333; } " ++
  ".case { display: flex; flex-direction: row; gap: 32px; " ++
    "flex-wrap: wrap; align-items: flex-start; } " ++
  -- a diagram is a fixed-geometry object (§12 item 10): it may SCROLL in a
  -- narrow page, it may never be reflowed or shrunk
  ".diagram { max-width: 100%; overflow: auto; } " ++
  "#geometry-audit { max-width: 100%; overflow: auto; } " ++
  ".ascii { background: #f7f7f7; padding: 8px 12px; font-size: 12px; " ++
    "border-radius: 4px; margin: 0; max-width: 100%; overflow: auto; " ++
    "box-sizing: border-box; }"

/-- The geometry self-audit: dependency-free JS that measures the
RENDERED page (§12 item 11).  Four checks, tolerance 0.75px:

* **floating endpoint** — every non-open wire endpoint lies on some box
  perimeter or on another wire;
* **label clipped** — every box label fits (`scrollWidth ≤ clientWidth`,
  the div-native check), i.e. the budgeted middle-ellipsis really did its
  job;
* **port ladder** (item 11a, restated by item 14) — the wires meeting
  one EDGE of a box form a LADDER SYMMETRIC ABOUT THE BOX CENTRE: every
  rung `d` is paired with a rung whose MIDPOINT with it is the centre.
  A single-port box is the special case `d + d = 0`, i.e. exactly the
  old wire-axis rule, so "an attached pill shares its resource's port
  axis" stays machine-checked; a MULTI-PARTY box has off-centre ports by
  construction (BBM18 Fig. 4's braid — n parties, n rungs) and the axis
  rule as stated would forbid the picture item 14 requires.  Symmetry is
  the honest generalization: it still pins every port to a fixed offset
  from the centre and still fails a wire that merely lands somewhere on
  the edge;
* **frame pad** (item 11b) — every dashed boundary is EXACTLY its
  content union inflated by `(padX, padY)` per side, the pads read from
  the emitter itself (`Diagram.framePad`).  Content is everything of the
  diagram contained in the frame; `cc-deck` and `cc-corner` are UI
  chrome and exempt — a transient overlay must never resize a semantic
  specification boundary (§12 item 12);
* **connection fork** (item 28) — a converter marked `cc-conn-<n>` is the
  converter of a CONNECTION reaching `n` interfaces, and some ONE edge of
  it must carry exactly `n` rungs, at exactly the emitter's fork ladder
  (`Diagram.forkPitch`, read from the emitter for the same reason the pads
  are).  This is strictly stronger than the port-ladder check on that box:
  symmetry alone would accept one wire, or three, or a pair at the wrong
  pitch.  It is what makes "the connection is visible" machine-checked
  rather than eyeballed.
* **TARGET CORRECTNESS** (item 28/30(a)) — a lead's last segment carries
  `data-target="k"`, the emitter's own claim about WHICH core row owns the
  interface that wire names, and that row's box carries `cc-row-k`.  The
  claim is checked against the drawing: one of the segment's endpoints must
  lie on that box's perimeter.  Nothing else in this audit can see this.
  A branch landing on the wrong but perfectly LEGAL box — the right kind of
  wire, on a box edge, at a symmetric rung, inside a planar drawing —
  violates no measurement, which is exactly how the eq.-(1) shape drew both
  of a fork's branches onto one resource and reported zero violations.  An
  unstamped wire makes no claim and is not checked (a row drawn as a region
  has no single box to name); a stamped wire whose row box is missing is
  itself the violation (`target-missing`).
* **BRANCH LABELS ARE DISTINCT** (item 28) — the labels of one connection's
  branches (`data-fork` = the converter's D4 address) must be pairwise
  distinct.  `γ.split` is an equivalence, so `γ.first ≠ γ.second` ALWAYS:
  two branches drawn with the same label can only mean the picture dropped
  what tells them apart, and no correct drawing can trip it.
* **PLANARITY** (item 30) — the drawing is a plane graph: no two wire
  segments meet except at shared endpoints.  Concretely three kinds.
  `wire-crossing`: a horizontal and a vertical segment meeting in the
  RELATIVE INTERIOR of both — a T-junction (an endpoint on another wire's
  interior) is the legitimate fan-out and stays legal, which is why the
  test is interior-vs-interior and not "any intersection".
  `wire-overlap`: two collinear segments sharing more than a point, which
  merges two distinct interfaces into one drawn line.  `wire-through-box`:
  a segment cutting a box's interior — Jost routes the free wire behind
  `Key` (item 28's closing note) and we do not have that grammar element,
  so a wire through a box is always a defect here.  BENDS take part: a
  `cc-bend` is a wire's quarter turn, so it contributes its two arc ends as
  endpoints (which is also how the floating-endpoint check accepts a
  routed wire) and its sharp-corner L as two segments — a conservative
  over-approximation of the arc, so the check can only ever be too strict.

Bounds containment alone is not an audit.  The JSON report lands in
`<pre id="geometry-audit">`; an empty `violations` array is the gate. -/
def auditScript : String := String.intercalate "\n" [
  "<pre id=\"geometry-audit\"></pre>",
  "<script>",
  "(function(){",
  " const tol = 0.75;",
  s!" const padX = {Diagram.framePad.1}, padY = {Diagram.framePad.2};",
  s!" const forkPitch = {Diagram.forkPitch};",
  " const chrome = function(e){ return e.classList.contains('cc-deck')",
  "   || e.classList.contains('cc-corner'); };",
  " const dedupe = function(xs){",
  "  const ds = [];",
  "  xs.forEach(function(d){",
  "   if (!ds.some(function(x){ return Math.abs(x-d) <= tol; })) ds.push(d);",
  "  });",
  "  return ds;",
  " };",
  " const report = {cases: [], violations: [], summary: {}};",
  " let totW = 0, totB = 0, totL = 0, totA = 0, totF = 0, totR = 0, totD = 0;",
  " let totC = 0, totX = 0, totN = 0, totT = 0, totG = 0;",
  -- a bend is a wire's quarter turn: its two arc ends are wire endpoints,
  -- its sharp-corner L is the conservative segment approximation (§12 item 29)
  " const bendEnds = function(e){",
  "  const r = e.getBoundingClientRect(); const c = e.dataset.corner;",
  "  if (c === 'tr') return [[r.left, r.top+1], [r.right-1, r.bottom],",
  "                          [r.right-1, r.top+1]];",
  "  if (c === 'br') return [[r.left, r.bottom-1], [r.right-1, r.top],",
  "                          [r.right-1, r.bottom-1]];",
  "  if (c === 'tl') return [[r.right, r.top+1], [r.left+1, r.bottom],",
  "                          [r.left+1, r.top+1]];",
  "  return [[r.right, r.bottom-1], [r.left+1, r.top], [r.left+1, r.bottom-1]];",
  " };",
  " document.querySelectorAll('.cc-diagram').forEach(function(diag){",
  "  const sec = diag.closest('section');",
  "  const name = sec ? sec.querySelector('h2').textContent : '?';",
  "  const boxes = Array.from(diag.querySelectorAll('.cc-box, .cc-boundary'))",
  "    .map(function(b){ return b.getBoundingClientRect(); });",
  "  const portEls = Array.from(diag.querySelectorAll('.cc-box'));",
  "  const ports = portEls.map(function(b){",
  "    return b.getBoundingClientRect(); });",
  "  const frames = Array.from(diag.querySelectorAll('.cc-boundary'));",
  "  const content = Array.from(diag.querySelectorAll(",
  "    '.cc-box, .cc-boundary, .cc-wire, .cc-tag'));",
  "  const wires = Array.from(diag.querySelectorAll('.cc-wire')).map(function(w){",
  "   const r = w.getBoundingClientRect();",
  "   if (w.dataset.axis === 'h')",
  "    return {x1:r.left, y1:r.top+r.height/2, x2:r.right, y2:r.top+r.height/2,",
  "            axis:'h', open:w.dataset.open||''};",
  "   return {x1:r.left+r.width/2, y1:r.top, x2:r.left+r.width/2, y2:r.bottom,",
  "           axis:'v', open:w.dataset.open||''};",
  "  });",
  "  const bends = Array.from(diag.querySelectorAll('.cc-bend')).map(bendEnds);",
  "  totB += boxes.length; totW += wires.length; totN += bends.length;",
  "  function onBend(px, py){",
  "   return bends.some(function(b){",
  "    return Math.hypot(px-b[0][0], py-b[0][1]) <= tol",
  "        || Math.hypot(px-b[1][0], py-b[1][1]) <= tol; });",
  "  }",
  "  function onBox(px, py){",
  "   return boxes.some(function(r){",
  "    const onV = (Math.abs(px-r.left)<=tol || Math.abs(px-r.right)<=tol)",
  "      && py >= r.top-tol && py <= r.bottom+tol;",
  "    const onH = (Math.abs(py-r.top)<=tol || Math.abs(py-r.bottom)<=tol)",
  "      && px >= r.left-tol && px <= r.right+tol;",
  "    return onV || onH;",
  "   });",
  "  }",
  "  function onWire(px, py, self){",
  "   return wires.some(function(l){",
  "    if (l === self) return false;",
  "    const dx = l.x2-l.x1, dy = l.y2-l.y1;",
  "    const len2 = dx*dx+dy*dy;",
  "    if (!len2) return false;",
  "    let t = ((px-l.x1)*dx+(py-l.y1)*dy)/len2;",
  "    t = Math.max(0, Math.min(1, t));",
  "    return Math.hypot(px-(l.x1+t*dx), py-(l.y1+t*dy)) <= tol;",
  "   });",
  "  }",
  "  const rungs = ports.map(function(){",
  "   return {left:[], right:[], top:[], bottom:[]}; });",
  "  wires.forEach(function(l){",
  "   [['1',l.x1,l.y1],['2',l.x2,l.y2]].forEach(function(e){",
  "    if (l.open.indexOf(e[0]) >= 0) return;",
  "    if (!onBox(e[1],e[2]) && !onWire(e[1],e[2],l) && !onBend(e[1],e[2]))",
  "     report.violations.push({case:name, kind:'floating-endpoint',",
  "       at:[Math.round(e[1]),Math.round(e[2])]});",
  "    ports.forEach(function(r, i){",
  "     const cx = (r.left+r.right)/2, cy = (r.top+r.bottom)/2;",
  "     const atL = Math.abs(e[1]-r.left)<=tol, atR = Math.abs(e[1]-r.right)<=tol;",
  "     const atT = Math.abs(e[2]-r.top)<=tol, atB = Math.abs(e[2]-r.bottom)<=tol;",
  "     const onSide = (atL || atR) && e[2] >= r.top-tol && e[2] <= r.bottom+tol;",
  "     const onCap = (atT || atB) && e[1] >= r.left-tol && e[1] <= r.right+tol;",
  "     if (l.axis === 'h' && onSide) {",
  "      totA++; rungs[i][atL ? 'left' : 'right'].push(l.y1-cy);",
  "     }",
  "     if (l.axis === 'v' && onCap) {",
  "      totA++; rungs[i][atT ? 'top' : 'bottom'].push(l.x1-cx);",
  "     }",
  "    });",
  "   });",
  "  });",
  "  rungs.forEach(function(edges, i){",
  "   const conn = Array.from(portEls[i].classList).find(function(c){",
  "    return c.indexOf('cc-conn-') === 0; });",
  "   if (conn) {",
  "    totC++;",
  "    const n = parseInt(conn.slice(8), 10);",
  "    const want = [];",
  "    for (let j = 0; j < n; j++) want.push((j - (n-1)/2) * forkPitch);",
  "    const got = {};",
  "    const ok = ['left','right','top','bottom'].some(function(side){",
  "     const ds = dedupe(edges[side]);",
  "     got[side] = ds.map(function(x){ return Math.round(x*10)/10; });",
  "     return ds.length === n && want.every(function(w){",
  "      return ds.some(function(d){ return Math.abs(d-w) <= tol; }); });",
  "    });",
  "    if (!ok) report.violations.push({case:name, kind:'connection-fork',",
  "      reaches:n, want:want, got:got});",
  "   }",
  "   ['left','right','top','bottom'].forEach(function(side){",
  "    const ds = dedupe(edges[side]);",
  "    if (ds.length > 1) totR++;",
  "    ds.forEach(function(d){",
  "     if (!ds.some(function(x){ return Math.abs((x+d)/2) <= tol; }))",
  "      report.violations.push({case:name, kind:'port-ladder-asymmetric',",
  "        side:side, offset:Math.round(d*10)/10,",
  "        rungs:ds.map(function(x){ return Math.round(x*10)/10; })});",
  "    });",
  "   });",
  "  });",
  -- §12 item 28/30(a): the wire lands on the box that OWNS the interface it
  -- names.  `data-target` is the emitter's intent, `cc-row-<k>` the box; the
  -- audit reads the intent back and checks the geometry against it.
  "  const onPerimeter = function(b, px, py){",
  "   const onV = (Math.abs(px-b.left)<=tol || Math.abs(px-b.right)<=tol)",
  "     && py >= b.top-tol && py <= b.bottom+tol;",
  "   const onH = (Math.abs(py-b.top)<=tol || Math.abs(py-b.bottom)<=tol)",
  "     && px >= b.left-tol && px <= b.right+tol;",
  "   return onV || onH;",
  "  };",
  "  Array.from(diag.querySelectorAll('.cc-wire[data-target]')).forEach(",
  "   function(w){",
  "    totT++;",
  "    const k = w.dataset.target;",
  "    const box = diag.querySelector('.cc-row-' + k);",
  "    if (!box) {",
  "     report.violations.push({case:name, kind:'target-missing', target:k});",
  "     return;",
  "    }",
  "    const r = w.getBoundingClientRect();",
  "    const ends = (w.dataset.axis === 'h')",
  "     ? [[r.left, r.top+r.height/2], [r.right, r.top+r.height/2]]",
  "     : [[r.left+r.width/2, r.top], [r.left+r.width/2, r.bottom]];",
  "    const b = box.getBoundingClientRect();",
  "    if (ends.some(function(e){ return onPerimeter(b, e[0], e[1]); })) return;",
  "    const landed = Array.from(diag.querySelectorAll('.cc-box'))",
  "     .filter(function(o){",
  "      const ob = o.getBoundingClientRect();",
  "      return ends.some(function(e){ return onPerimeter(ob, e[0], e[1]); });",
  "     }).map(function(o){ return o.textContent || o.className; });",
  "    report.violations.push({case:name, kind:'wrong-target', target:k,",
  "      wanted:(box.textContent || box.className), landedOn:landed,",
  "      at:[Math.round(ends[1][0]), Math.round(ends[1][1])]});",
  "   });",
  -- §12 item 28: `γ.first ≠ γ.second`, so one node's branch labels must differ
  "  const forks = {};",
  "  Array.from(diag.querySelectorAll('.cc-tag[data-fork]')).forEach(",
  "   function(t){",
  "    const f = t.dataset.fork;",
  "    (forks[f] = forks[f] || []).push(t.textContent);",
  "   });",
  "  Object.keys(forks).forEach(function(f){",
  "   totG++;",
  "   const ls = forks[f];",
  "   ls.forEach(function(l, i){",
  "    if (ls.indexOf(l) !== i)",
  "     report.violations.push({case:name, kind:'duplicate-branch-label',",
  "       fork:f, label:l, labels:ls});",
  "   });",
  "  });",
  "  frames.forEach(function(f){",
  "   const fr = f.getBoundingClientRect();",
  "   let u = null;",
  "   content.forEach(function(c){",
  "    if (c === f || chrome(c)) return;",
  "    const r = c.getBoundingClientRect();",
  "    if (r.left < fr.left-tol || r.right > fr.right+tol",
  "     || r.top < fr.top-tol || r.bottom > fr.bottom+tol) return;",
  "    u = (u === null) ? {l:r.left, t:r.top, r:r.right, b:r.bottom}",
  "      : {l:Math.min(u.l,r.left), t:Math.min(u.t,r.top),",
  "         r:Math.max(u.r,r.right), b:Math.max(u.b,r.bottom)};",
  "   });",
  "   totF++;",
  "   if (u === null) {",
  "    report.violations.push({case:name, kind:'empty-frame'});",
  "    return;",
  "   }",
  "   const got = [u.l-fr.left, fr.right-u.r, u.t-fr.top, fr.bottom-u.b];",
  "   const want = [padX, padX, padY, padY];",
  "   ['left','right','top','bottom'].forEach(function(side, i){",
  "    if (Math.abs(got[i]-want[i]) > tol)",
  "     report.violations.push({case:name, kind:'frame-pad', side:side,",
  "       got:Math.round(got[i]*10)/10, want:want[i]});",
  "   });",
  "  });",
  -- §12 item 30: the drawing is a PLANE GRAPH.  Segments = the wires plus
  -- each bend's sharp-corner L; a crossing is interior-vs-interior, so the
  -- T-junctions a fan-out is made of stay legal.
  "  const segs = wires.map(function(l){",
  "   return {x1:Math.min(l.x1,l.x2), x2:Math.max(l.x1,l.x2),",
  "           y1:Math.min(l.y1,l.y2), y2:Math.max(l.y1,l.y2), a:l.axis}; });",
  "  bends.forEach(function(b){",
  "   segs.push({x1:Math.min(b[0][0],b[2][0]), x2:Math.max(b[0][0],b[2][0]),",
  "              y1:b[0][1], y2:b[0][1], a:'h'});",
  "   segs.push({x1:b[1][0], x2:b[1][0], a:'v',",
  "              y1:Math.min(b[1][1],b[2][1]), y2:Math.max(b[1][1],b[2][1])});",
  "  });",
  "  totX += segs.length;",
  "  for (let i = 0; i < segs.length; i++)",
  "   for (let j = i+1; j < segs.length; j++) {",
  "    const p = segs[i], q = segs[j];",
  "    if (p.a !== q.a) {",
  "     const h = (p.a === 'h') ? p : q, v = (p.a === 'h') ? q : p;",
  "     if (v.x1 > h.x1+tol && v.x1 < h.x2-tol",
  "      && h.y1 > v.y1+tol && h.y1 < v.y2-tol)",
  "      report.violations.push({case:name, kind:'wire-crossing',",
  "        at:[Math.round(v.x1), Math.round(h.y1)]});",
  "    } else if (p.a === 'h') {",
  "     if (Math.abs(p.y1-q.y1) <= tol",
  "      && Math.min(p.x2,q.x2) - Math.max(p.x1,q.x1) > tol)",
  "      report.violations.push({case:name, kind:'wire-overlap', axis:'h',",
  "        at:[Math.round(Math.max(p.x1,q.x1)), Math.round(p.y1)]});",
  "    } else {",
  "     if (Math.abs(p.x1-q.x1) <= tol",
  "      && Math.min(p.y2,q.y2) - Math.max(p.y1,q.y1) > tol)",
  "      report.violations.push({case:name, kind:'wire-overlap', axis:'v',",
  "        at:[Math.round(p.x1), Math.round(Math.max(p.y1,q.y1))]});",
  "    }",
  "   }",
  "  const solids = Array.from(diag.querySelectorAll('.cc-box')).map(function(b){",
  "    return b.getBoundingClientRect(); });",
  "  segs.forEach(function(s){ solids.forEach(function(r){",
  "   if (Math.min(s.x2,r.right) - Math.max(s.x1,r.left) > tol",
  "    && Math.min(s.y2,r.bottom) - Math.max(s.y1,r.top) > tol)",
  "    report.violations.push({case:name, kind:'wire-through-box',",
  "      at:[Math.round(s.x1), Math.round(s.y1)]});",
  "  }); });",
  "  Array.from(diag.querySelectorAll('.cc-box')).forEach(function(b){",
  "   totL++;",
  "   if (b.scrollWidth > b.clientWidth + 1)",
  "    report.violations.push({case:name, kind:'label-clipped',",
  "      label:b.textContent, scrollWidth:b.scrollWidth,",
  "      clientWidth:b.clientWidth});",
  "  });",
  "  totD += diag.querySelectorAll('.cc-wire[data-stroke=\\'dotted\\']').length;",
  "  report.cases.push({case:name, boxes:boxes.length, wires:wires.length,",
  "    frames:frames.length});",
  " });",
  " report.summary = {diagrams: report.cases.length, boxes: totB,",
  "  wires: totW, dottedWires: totD, bends: totN, labels: totL,",
  "  portChecks: totA, multiPortLadders: totR, connectionForks: totC,",
  "  targetedLeads: totT, labelledForks: totG,",
  "  frames: totF, planarSegments: totX,",
  "  violations: report.violations.length};",
  " document.getElementById('geometry-audit').textContent =",
  "  JSON.stringify(report, null, 1);",
  "})();",
  "</script>"]

/-! ## The mutation receipt for the planarity check (§12 item 30)

A check nobody has seen FAIL is folklore.  This page is the deliberate
mutant: two hand-written figures whose only difference is which of two
leads turns first, i.e. exactly the track-order decision `Diagram`'s
channel makes.  Every wire is marked `data-open="12"`, so the
floating-endpoint rule is silent by construction and cannot be confused
with the crossing rule; there are no boxes, frames or labels, so no other
check can speak either.  The CONTROL turns the upper lead first and is
planar; the MUTANT swaps the two tracks and its leads cross once.  The
page runs the gallery's own `auditScript`, unmodified, and is written on
every build to `.lake/cc_planarity_mutation.html` — a green gallery and a
red mutant are the two halves of the same receipt. -/

private def mutantWire (x y w h : Nat) : String :=
  s!"<div class=\"cc-wire\" data-axis=\"{if h == 0 then "h" else "v"}\" " ++
  s!"data-open=\"12\" style=\"position:absolute; left:{x}px; top:{y}px; " ++
  s!"width:{if h == 0 then toString w else "2"}px; " ++
  s!"height:{if h == 0 then "2" else toString h}px; background:#555\"></div>"

/-- Two order-preserving leads: `A` from `y = 20` to `y = 95`, `B` from
`y = 80` to `y = 110`.  `A` travels DOWN PAST `B`'s entry, which is exactly
the situation the channel's track order exists to resolve — `A` must turn
FURTHER from the flank than `B`.  `t1`/`t2` are their tracks, and they are
the only difference between the two figures. -/
private def mutantFigure (name : String) (t1 t2 : Nat) : String :=
  "<section><h2>" ++ escapeHtml name ++ "</h2><div class=\"case\">" ++
  "<div class=\"diagram\"><div class=\"cc-diagram\" " ++
  "style=\"position:relative; width:180px; height:130px\">" ++
  mutantWire 10 20 (t1 - 10) 0 ++ mutantWire t1 20 0 75 ++
  mutantWire t1 95 (150 - t1) 0 ++
  mutantWire 10 80 (t2 - 10) 0 ++ mutantWire t2 80 0 30 ++
  mutantWire t2 110 (150 - t2) 0 ++
  "</div></div></div></section>"

def mutationPage : String :=
  "<!doctype html><html><head><meta charset=\"utf-8\">" ++
  "<title>Planarity check — mutation receipt (DESIGN §12 item 30)</title>" ++
  "<style>" ++ pageCss ++ "</style></head><body>" ++
  "<h1>Planarity check: the mutation receipt</h1>" ++
  "<p class=\"note\">Same two leads, same endpoints, same audit script as " ++
  "the gallery. Only the CHANNEL TRACK ORDER differs. Expected report: " ++
  "zero violations on the control, one <code>wire-crossing</code> on the " ++
  "mutant. Every wire is <code>data-open=\"12\"</code> and there are no " ++
  "boxes or frames, so no other check can fire.</p>" ++
  mutantFigure "CONTROL — the deeper lead turns later (planar)" 90 40 ++
  mutantFigure "MUTANT — tracks swapped (the leads cross twice)" 40 90 ++
  auditScript ++ "</body></html>"

#eval do
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/cc_planarity_mutation.html" mutationPage

/-! ## The mutation receipt for the TARGET check (§12 item 28/30(a))

The same discipline for the check that had to be invented: a branch landing
on the wrong box is a SEMANTIC error and every geometric measurement is happy
with it, so the mutant here is a drawing that no other check can fault.  Two
stacked resource boxes, `cc-row-0` and `cc-row-1`, and one lead stamped
`data-target="0"`.  The CONTROL lands it on row 0 and is clean; the MUTANT
draws the very same wire onto row 1 — same length, same axis, still on a box
edge, still at that box's centre, still planar, still nothing through a box —
and only the target check can tell them apart.  The third and fourth figures
do the same for branch labels: two tags of one fork, distinct then equal.
Every wire is `data-open="12"`, so the floating-endpoint rule is silent and
cannot be confused with either. -/

private def mutantBox (x y w h : Nat) (cls label : String) : String :=
  s!"<div class=\"cc-box {cls}\" style=\"position:absolute; left:{x}px; " ++
  s!"top:{y}px; width:{w}px; height:{h}px; box-sizing:border-box; " ++
  s!"border:2px solid #555; display:flex; align-items:center; " ++
  s!"justify-content:center; font-family:monospace; font-size:13px\">" ++
  escapeHtml label ++ "</div>"

private def mutantLead (x w y : Nat) (target : String) : String :=
  s!"<div class=\"cc-wire\" data-axis=\"h\" data-open=\"12\" " ++
  s!"data-target=\"{target}\" style=\"position:absolute; left:{x}px; " ++
  s!"top:{y}px; width:{w}px; height:2px; background:#555\"></div>"

/-- `row` is the box the single stamped lead is DRAWN to; the stamp always
says row 0.  `row = 0` is the control, `row = 1` the mutant. -/
private def targetFigure (name : String) (row : Nat) : String :=
  "<section><h2>" ++ escapeHtml name ++ "</h2><div class=\"case\">" ++
  "<div class=\"diagram\"><div class=\"cc-diagram\" " ++
  "style=\"position:relative; width:260px; height:130px\">" ++
  mutantBox 120 10 120 44 "cc-row-0" "toyR" ++
  mutantBox 120 64 120 44 "cc-row-1" "toyR" ++
  mutantLead 10 110 (if row == 0 then 31 else 85) "0" ++
  "</div></div></div></section>"

/-- **The drawing that shipped**, rebuilt by hand at the coordinates the old
emitter printed: two rows, an item-30(c) stack BRACKET (one rail, one spur per
row), and the two branches of a fork ending on the rail instead of on the rows
they name.  It is a perfectly legal picture — planar, no wire through a box,
every endpoint on another wire — and every check that existed before this one
passes it.  The two branches are stamped with the rows their interfaces name,
which is what the emitter now says, so the target check reports both. -/
private def regressionFigure : String :=
  "<section><h2>" ++
  escapeHtml "REGRESSION — the eq.-(1) drawing that shipped (both branches \
    on the shared bracket)" ++
  "</h2><div class=\"case\">" ++
  "<div class=\"diagram\"><div class=\"cc-diagram\" " ++
  "style=\"position:relative; width:260px; height:130px\">" ++
  mutantBox 120 10 120 44 "cc-row-0" "toyR" ++
  mutantBox 120 64 120 44 "cc-row-1" "toyR" ++
  mutantWire 108 20 0 78 ++                 -- the bracket rail
  mutantWire 109 31 11 0 ++ mutantWire 109 85 11 0 ++   -- its two spurs
  mutantLead 10 99 20 "0" ++ mutantLead 10 99 96 "1" ++
  "</div></div></div></section>"

private def mutantTag (x y : Nat) (fork label : String) : String :=
  s!"<div class=\"cc-tag\" data-fork=\"{fork}\" style=\"position:absolute; " ++
  s!"left:{x}px; top:{y}px; font-family:monospace; font-size:11px; " ++
  s!"color:#555\">" ++ escapeHtml label ++ "</div>"

/-- Two branch labels of ONE fork.  The control names two interfaces, the
mutant names one twice — which is what dropping the `Sum.inl`/`Sum.inr`
qualifier did to the eq.-(1) shape. -/
private def labelFigure (name : String) (second : String) : String :=
  "<section><h2>" ++ escapeHtml name ++ "</h2><div class=\"case\">" ++
  "<div class=\"diagram\"><div class=\"cc-diagram\" " ++
  "style=\"position:relative; width:200px; height:60px\">" ++
  mutantTag 20 10 "R" "1.u" ++ mutantTag 20 34 "R" second ++
  "</div></div></div></section>"

def targetMutationPage : String :=
  "<!doctype html><html><head><meta charset=\"utf-8\">" ++
  "<title>Target check — mutation receipt (DESIGN §12 item 28)</title>" ++
  "<style>" ++ pageCss ++ "</style></head><body>" ++
  "<h1>Target correctness and branch labels: the mutation receipt</h1>" ++
  "<p class=\"note\">Same audit script as the gallery. Expected report: " ++
  "zero violations on the two controls, one <code>wrong-target</code> on " ++
  "the target mutant, two on the regression figure, and one " ++
  "<code>duplicate-branch-label</code> on the label mutant. The target " ++
  "mutant differs from its control ONLY in which box the lead is drawn to — " ++
  "same axis, same length, both endpoints on a box edge at that box's " ++
  "centre, nothing through a box, nothing crossing. No other check can see " ++
  "it.</p>" ++
  targetFigure "CONTROL — the lead lands on the row it names" 0 ++
  targetFigure "MUTANT — the same lead, drawn to the other row" 1 ++
  regressionFigure ++
  labelFigure "CONTROL — one fork, two distinct branch labels" "2.u" ++
  labelFigure "MUTANT — the qualifier dropped, both branches read `1.u`"
    "1.u" ++
  auditScript ++ "</body></html>"

#eval do
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/cc_target_mutation.html" targetMutationPage

def pageHtml (sections : Array String) : String :=
  "<!doctype html><html><head><meta charset=\"utf-8\">" ++
  "<title>CC diagram gallery (DESIGN §12 corpus)</title>" ++
  "<style>" ++ pageCss ++ "</style></head><body>" ++
  "<h1>CC diagram visual test corpus — DESIGN §12 item 8</h1>" ++
  "<p class=\"note\">Left: the widget's own Html tree, serialized. " ++
  "Right: the pinnable ASCII structure receipt (deliberately a tree, " ++
  "not a picture — §12 item 7). Hover any box for the full label. " ++
  "The geometry audit report is at the bottom of the page.</p>" ++
  String.join sections.toList ++ auditScript ++ "</body></html>"

/-! ## The command -/

syntax ccGalleryItem := str " => " term (" with " "[" ccViewDir,* "]")?

/-- `#cc_gallery "path" [ "name" => t, … ]`: render every corpus case —
diagram beside ASCII receipt — into one self-contained HTML page at
`path` (parent directories are created).  A term whose *type* is an
equality or `≈[ε]` statement renders as the figure pair of its sides
(§12 item 6); anything else renders as its own composition diagram.
A case may carry the `#cc_diagram` view clause (`… with [fold enc]`) —
the D1 view states are corpus cases like any other and must be looked
at in the browser too. -/
syntax (name := ccGalleryCmd) "#cc_gallery " str " [" ccGalleryItem,* "]" :
  command

@[command_elab ccGalleryCmd] def elabCcGallery : CommandElab := fun stx => do
  let some path := stx[1].isStrLit?
    | throwError "#cc_gallery expects a path string"
  let items := stx[3].getSepArgs
  let mut sections : Array String := #[]
  for item in items do
    let some name := item[0].isStrLit?
      | throwError "#cc_gallery case expects a name string"
    let t : TSyntax `term := ⟨item[2]⟩
    let dirs ←
      if item[3].isNone then pure []
      else item[3][2].getSepArgs.toList.mapM Diagram.parseViewDir
    let sec ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      match ← Diagram.ofStatement? ty dirs with
      | some (l, rel, r) =>
          return sectionHtml name
            (htmlString (Diagram.pairHtml (Diagram.html l) rel (Diagram.html r)))
            s!"{Diagram.ascii l}\n{rel}\n{Diagram.ascii r}"
      | none =>
          let shape ← Diagram.shapeWithDirs e dirs
          return sectionHtml name (htmlString (Diagram.html shape))
            (Diagram.ascii shape)
    sections := sections.push sec
  let page := pageHtml sections
  if let some dir := (System.FilePath.mk path).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path page
  logInfo s!"#cc_gallery: {items.size} cases → {path}"

/-! ## The §12-item-8 corpus, rendered

Every case class the renderer can meet, in one page.  Regenerated on
every compile of this file; the critique loop (§12: "inspected in a
browser against the source figures") reads the output page. -/

#cc_gallery ".lake/cc_gallery.html" [
  "single resource" => toyG,
  "parallel of two" => (toyG ∥ toyG),
  "parallel of three" => (toyG ∥ toyG ∥ toyG),
  "attach at one party" => (encG •[Party3.a] toyG),
  "attach at both parties" => (decG •[Party3.b] (encG •[Party3.a] toyG)),
  "construction, real side" =>
    (decG •[Sum.inl Party3.b] (encG •[Sum.inl Party3.a] (keyG ∥ autG))),
  "construction, ideal side (simulator)" => (simG •[Party3.e] secG),
  "MaRuTa12 Fig. 1 layout target" => fig1G,
  -- §12 item 15: absence of output IS the filter's rendering.  The E
  -- wire leaves the core and STOPS inside the boundary; the party
  -- interfaces cross it live, exactly BBM18 Fig. 4's live-vs-filtered
  -- reading.  No pill, no `⊣` symbol, no corruption ring.
  "filtered adversary interface (item 15)" => (⊣[Party3.e] toy3),
  "filtered party interface (item 15)" => (⊣[Party3.b] toy3),
  -- §12 item 14: three UNRECOGNISED party interfaces take numbered
  -- slots, one converter box each, stacked vertically on the party
  -- flank, each with its own bus into every row of the resource stack
  -- (BBM18 Fig. 4).  `data-geography="indexed"`, never "fallback".
  "n-party ladder, 3 parties (item 14)" =>
    (encG •[Sum.inl PartyN.p3] (decG •[Sum.inl PartyN.p2]
      (encG •[Sum.inl PartyN.p1] (toyN ∥ toyN)))),
  "n-party ladder over one resource (item 14)" =>
    (encG •[PartyN.p3] (decG •[PartyN.p2] (encG •[PartyN.p1] toyN))),
  -- §12 item 16: one simulator per dishonest interface, each in series
  -- on its OWN wire; the honest party interface bypasses both.
  "two simulators, distinct interfaces (item 16)" =>
    (simG •[PartyN.e] (simG •[PartyN.m2] (encG •[PartyN.p1] toyN))),
  -- §12 item 18: DOTTED = a free interface, accessed directly by the
  -- distinguisher (Jost Fig. 2.1's F at top).  No third stroke.
  "free interface, dotted above (item 18)" =>
    (encG •[PartyN.f] (encG •[PartyN.p1] toyN)),
  "free and adversary interfaces together" =>
    (simG •[PartyN.e] (encG •[PartyN.f] (encG •[PartyN.p1] toyN))),
  -- §12 item 28: a CONNECTION (`α ••[γ] R`, Jost's γ) is one converter
  -- FORKED onto the interfaces it reaches — Jost Fig. 2.1's π_ε^A, whose
  -- tall box carries one inner wire per reach.  Across a `∥` the two
  -- branches take two buses into the stack; on ONE resource they land as
  -- two rungs of that box's own port ladder.
  "connection across a ∥ (item 28, Jost Fig. 2.1)" =>
    (encA ••[gammaU] (toyR ∥ toyR)),
  "connection into one resource (item 28)" => (encPairG ••[gammaAB] toyG),
  "two connections, the eq.-(1) shape (item 28)" =>
    CarrierDemo.constructedShape,
  -- a connection sharing a flank with an ordinary attachment: the fork's
  -- two branches and the plain row's single lead take three buses into one
  -- resource, i.e. a three-rung port ladder on its edge
  "connection beside a plain attachment (item 28)" =>
    (encPairG ••[gammaAB] (encG •[Party3.a] toyG)),
  -- the ONE genuine fallback: an interface printed as a computation
  "geography fallback (unnameable interface)" =>
    (encG •[partyOf 0] toyN),
  "game resource (small-caps grey)" => cpa0G,
  "reduction attached to the game" => (encG •[Party3.a] cpa0G),
  "nested construction in parallel" => ((encG •[Party3.a] toyG) ∥ toyG),
  -- the corner-label migration, with NO directives: an ANONYMOUS
  -- collapsed compound is a dashed region and carries its summary at the
  -- TOP-LEFT corner, never centered (§12 item 12)
  "deep nesting collapses (corner label)" =>
    (decG •[Sum.inl Party3.b] ((encG •[Party3.a] toyG) ∥ toyG)),
  -- the same collapse when the subterm HAS a name: D2 recognizes it
  -- definitionally and the compound becomes that named object's solid
  -- box + deck.  (Here honestly so: a PAIRED-source converter attached at a
  -- single interface of a `∥` is idle, so `enc₂^a (KEY ∥ AUT)` really IS
  -- `NET`.)
  "deep nesting collapses (D2-recognized name)" =>
    (decG •[Sum.inl (Sum.inl Party3.b)]
      ((encPairG •[Sum.inl Party3.a] (keyG ∥ autG)) ∥ toyG)),
  "long display name" => longNameG,
  "long anonymous converter" =>
    ((Converter.ofMaps id (fun b => !b) :
        Converter demoServices (.base .plain) (.base .masked))
      •[Party3.a] toyG),
  "deep converter chain" => chainG,
  "glyph: insecure channel" => (insecureChannel Bool),
  "glyph: authenticated channel" => (authenticatedChannel Bool),
  "glyph: confidential channel" => (confidentialChannel (fun _ : Bool => (0 : Nat))),
  "glyph: secure channel" => (secureChannel (fun _ : Bool => (0 : Nat))),
  "glyph: shared key" => (sharedKey Bool),
  "glyphs in parallel" => (authenticatedChannel Bool ∥ authenticatedChannel Bool),
  "equation pair (theorem)" => GrammarTests.counter_eq_twin,
  "closeness pair (theorem)" => toyG_close,
  -- `CtrIface.user` is not a paper letter but IS a name, so under
  -- item 14 it takes slot 0 on the party flank rather than degrading the
  -- spine: `data-geography="indexed"`
  "unrecognised interface takes a slot (item 14)" => WidgetTests.attached,
  -- D1/D2 view states (§12 item 12): folded elements carry the deck
  -- outline and otherwise look exactly like ordinary boxes
  "fold: serial run to one pill" => chainG with [fold enc],
  "fold: stack under a given name" =>
    (decG •[Sum.inl Party3.b] (encG •[Sum.inl Party3.a] (keyG ∥ autG)))
      with [fold KEY ∥ AUT as "NET"],
  "fold: stack under the RECOGNIZED name (D2)" =>
    (encPairG •[Sum.inl Party3.a] (keyG ∥ autG)) with [fold KEY ∥ AUT],
  "unfold: named leaf into a corner-labelled region" =>
    (encG •[Sum.inl Party3.a] netG) with [unfold NET]
]

/-! ## Receipts: the corpus shapes are pinned -/

/-- info: ◠ sim @ Sum.inl Party3.e
  ◠ dec @ Sum.inl Party3.b
    ◠ enc @ Sum.inl Party3.a
      ∥
        □ KEY
        □ AUT -/
#guard_msgs in
#cc_diagram fig1G

/-- info: ◠ enc @ Party3.a
  ◠ dec @ Party3.b
    ◠ enc @ Party3.a
      ◠ dec @ Party3.b
        ◠ enc @ Party3.a
          ◠ sim @ Party3.e
            □ toyG -/
#guard_msgs in
#cc_diagram chainG

/-- info: □ TheAbsurdlyLongResourceNameThatUsedToStretchTheEntireDiagramWidth -/
#guard_msgs in
#cc_diagram longNameG

/-! ### The sourced-grammar cases (§12 items 14–18)

The ASCII twin is the STRUCTURE receipt (§12 item 7), so it is blind to
the flank a node lands on — deliberately: that is what lets the layout
evolve under a stable pin.  What the receipts below pin is the SPINE the
layout is handed; the geography itself is pinned by
`Diagram.geography`'s own receipts. -/

-- Three unrecognised party interfaces over a two-row stack: item 14's
-- numbered ladder, one converter box per party.
/-- info: ◠ enc @ Sum.inl PartyN.p3
  ◠ dec @ Sum.inl PartyN.p2
    ◠ enc @ Sum.inl PartyN.p1
      ∥
        □ toyN
        □ toyN -/
#guard_msgs in
#cc_diagram (encG •[Sum.inl PartyN.p3] (decG •[Sum.inl PartyN.p2]
  (encG •[Sum.inl PartyN.p1] (toyN ∥ toyN))))

-- Two simulators at DISTINCT interfaces (item 16): two below columns,
-- each in series on its own wire; `p1` bypasses both.
/-- info: ◠ sim @ PartyN.e
  ◠ sim @ PartyN.m2
    ◠ enc @ PartyN.p1
      □ toyN -/
#guard_msgs in
#cc_diagram (simG •[PartyN.e] (simG •[PartyN.m2] (encG •[PartyN.p1] toyN)))

-- The free interface (item 18): above the core, drawn dotted.
/-- info: ◠ enc @ PartyN.f
  ◠ enc @ PartyN.p1
    □ toyN -/
#guard_msgs in
#cc_diagram (encG •[PartyN.f] (encG •[PartyN.p1] toyN))

-- Filtering (item 15): the structure tree still records the blocking
-- attach — it IS one — while the picture draws its EFFECT and no box.
/-- info: ◠ ⊣ @ Party3.b
  □ toy3 -/
#guard_msgs in
#cc_diagram (⊣[Party3.b] toy3)

-- The one genuine fallback: `partyOf 0` prints as a computation, not a
-- name, so it cannot key a slot.
/-- info: ◠ enc @ partyOf 0
  □ toyN -/
#guard_msgs in
#cc_diagram (encG •[partyOf 0] toyN)

/-! ### Connections (§12 item 28)

The reach is TERM structure — `γ.first` and `γ.second`, reduced — so the
structure receipt prints it in `⟨…⟩` and pins it.  The picture's own
invariant (one fork rung per reach, at the emitter's pitch) is pinned by the
gallery's `connection-fork` audit check, not by these. -/

-- Jost's own γ^A: interface `u` of the LEFT copy and interface `u` of the
-- RIGHT one — Fig. 2.1's "int. A of Key" and "int. A of AuthChan".
/-- info: ◠ encA @ gammaU ⟨Sum.inl Party.u, Sum.inr Party.u⟩
  ∥
    □ toyR
    □ toyR -/
#guard_msgs in
#cc_diagram (encA ••[gammaU] (toyR ∥ toyR))

-- The same γ with both feet on ONE resource: two interfaces of a single
-- box, which the picture lands as two rungs of that box's own port ladder.
/-- info: ◠ enc₂ @ gammaAB ⟨Party3.a, Party3.b⟩
  □ toyG -/
#guard_msgs in
#cc_diagram (encPairG ••[gammaAB] toyG)

/-- A spine node with only its interface and role — the geography's whole
input. -/
private def spineAt (interface : String)
    (role : Option RandomSystems.CC.Names.Role := none) : Diagram.SpineNode :=
  { converter := "c", interface := interface, role := role, decl := none }

/-- The geography split, in flank order `left | right | above | below`. -/
private def geographyLine (spine : List Diagram.SpineNode) : String :=
  let names := fun (l : List Diagram.SpineNode) =>
    l.map (fun nd => Diagram.lastComponent nd.interface)
  let g := Diagram.geography spine
  s!"{g.mode}: {names g.left} {names g.right} {names g.above} {names g.below}"

-- p1/p2/p3 take the party flank in spine order under `indexed`; a/b keep
-- item 2's flanks under `classified`; `f` goes above and a simulator
-- below whatever its interface; only `partyOf 0` — a computation, not a
-- name — is `fallback`, and then the spine alternates as before.
/-- info: indexed: [p1, p2, p3] [] [] []
classified: [a] [b] [] [e]
classified: [] [] [f] [m2]
fallback: [p3, f2 0] [p2] [] [] -/
#guard_msgs in
#eval do
  IO.println (geographyLine [spineAt "PartyN.p1", spineAt "PartyN.p2",
    spineAt "PartyN.p3"])
  IO.println (geographyLine [spineAt "Party3.a", spineAt "Party3.b",
    spineAt "Party3.e"])
  IO.println (geographyLine [spineAt "PartyN.f",
    spineAt "PartyN.m2" (some .simulator)])
  IO.println (geographyLine [spineAt "PartyN.p3", spineAt "PartyN.p2",
    spineAt "PartyN.f2 0"])

/-! ### The D1 view states (§12 item 12) -/

-- `fold enc` collapses `enc`'s MAXIMAL same-interface serial run — all
-- three `a`-side `enc`s — into one node under the composed name.  The
-- receipt keeps the composition whole (`enc∘enc∘enc`); only the pill
-- middle-ellipsizes it (`enc∘…enc`), and never to a count form.  The
-- untouched `dec`s stay two separate nodes: a fold is per-converter.
/-- info: ▸ enc∘enc∘enc @ Party3.a
  ◠ dec @ Party3.b
    ◠ dec @ Party3.b
      ◠ sim @ Party3.e
        □ toyG -/
#guard_msgs in
#cc_diagram chainG with [fold enc]

-- `fold A ∥ B as "N"` collapses the stack to ONE resource box; the
-- receipt records what the abstraction stands for.
/-- info: ◠ dec @ Sum.inl Party3.b
  ◠ enc @ Sum.inl Party3.a
    ▸ NET = KEY ∥ AUT -/
#guard_msgs in
#cc_diagram (decG •[Sum.inl Party3.b] (encG •[Sum.inl Party3.a] (keyG ∥ autG)))
  with [fold KEY ∥ AUT as "NET"]

-- D2: WITHOUT `as`, the collapsed subterm is checked definitionally
-- against the registered `cc_display` constants and takes the name (and
-- role) of the one it equals — here `netG`, declared `NET`.
/-- info: ◠ enc₂ @ Sum.inl Party3.a
  ▸ NET = KEY ∥ AUT -/
#guard_msgs in
#cc_diagram (encPairG •[Sum.inl Party3.a] (keyG ∥ autG)) with [fold KEY ∥ AUT]

-- `unfold` is the inverse: `ofExpr` stops at a display-named head, and
-- the directive overrides that for THAT leaf, re-discovering structure.
/-- info: ◠ enc @ Sum.inl Party3.a
  ◈ NET
    ∥
      □ KEY
      □ AUT -/
#guard_msgs in
#cc_diagram (encG •[Sum.inl Party3.a] netG) with [unfold NET]

-- The no-directive regression: nothing about the collapse changed, only
-- WHERE the compound's name is drawn (top-left corner, in HTML).  The
-- ASCII twin is the full structure tree either way — that is precisely
-- why pins bind to it and not to the picture (§12 item 7).
/-- info: ◠ dec @ Sum.inl Party3.b
  ∥
    ◠ enc @ Party3.a
      □ toyG
    □ toyG -/
#guard_msgs in
#cc_diagram (decG •[Sum.inl Party3.b] ((encG •[Party3.a] toyG) ∥ toyG))

end RandomSystems.CC.Gallery
