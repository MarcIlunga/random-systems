# Visual scenarios for the CC diagram renderer — the matrix and its policy

*Draft for folding into `DESIGN.md` §12.  Written 2026-08-08 against
`RandomSystems/Jost/SurfaceWidgets.lean` (the emitter), `SurfacePanel.lean`
(the D4/D5 chrome) and `SurfaceGallery.lean` (the page + geometry audit).
Every number below was measured in headless Chrome, not asserted; the
measurement harness and the raw JSON are described in §6.*

---

## 0. Three corrections to the framing, before the matrix

**(a) The panels ARE dynamic; the LAYOUT is deliberately not.**  Every
click in `#cc_panel` is a real `MakeEditLink` document edit, a real
re-elaboration and a real `Kernel.check` (§12 item 26).  What does not
adapt is the *geometry*, and that is item 10 on purpose: engine-owned
layout is banned inside a diagram because it is exactly what made wires
miss their boxes in v3.  So the fix is **a container policy around the
diagram**, never a responsive emitter.  Reading the defect as "make the
renderer responsive" would trade a measurable geometry gate for a
plausible-looking picture.

**(b) "Labels are too small" is really "labels are hard-coded pixels".**
Measured: box labels 13px, wire tags 11px, corner names 10px — all
literals in `Prim.toHtml`.  The infoview inherits the reader's editor
font; the diagram ignores it completely.  A reader at an 18px editor font
gets 11px interface tags.  A floor alone does not fix that; a floor **and**
a reader-relative scale **and** a cap does (§2, R1′).

**(c) "Magnifier-style pseudocode" is the opposite of what §12 froze.**
Item 20 is explicit: *"Inspecting a leaf is SEMANTIC ZOOM, not
magnification: the lens swaps the REPRESENTATION, since pseudocode is a
different rendering of the same object, not a larger picture of it."*  The
frozen treatment is a peek view / magic lens — overlay, anchored over its
object, context dimmed beneath, opaque 1px panel, drawn cross.  Built that
way (§7).  Nothing in the shipped lens magnifies anything.

**(d) There is no pseudocode to show.**  `resource … where`
(`SurfaceGrammar.lean`) compiles its block away; no attribute stores the
source text.  What the lens can show today is the other representation the
library actually has — the item-7 structure twin and the term.  A true
pseudocode lens needs a `cc_pseudocode` store first (§7, request 4).

---

## 1. The axes, corrected

### 1.1 Shapes — the diagram grammar (22 rows, not 17)

Two of the seventeen are removed and eight are added.

**Removed from this axis** (they are *chrome*, §1.3): the pseudocode
overlay and the ε-rail.  §12 item 12 already rules that UI chrome is
exempt from frame-content in the geometry audit; putting chrome on the
shape axis manufactures nonsense cells (`ε-rail × folded`).

| # | shape | source | measured natural size |
|---|---|---|---|
| S1 | base resource | Jost Fig 2.1 | 196×60 |
| S2 | 2-row `∥` stack | item 9a | 196×114 |
| S3 | n-row `∥` stack | MaRuTa12 Fig 1 | 196×(54n+6) |
| S4 | attachment at one interface | item 9 | 326×88 |
| S5 | serial converter chain at one interface | item 9 | **684×160** (deep chain) |
| S6 | attachments on opposite flanks | item 9 | 432×88 |
| S7 | nested attachments on one flank | item 9 | 386×142 |
| S8 | connection fork, two interfaces of one resource | item 28 | 339×142 |
| S9 | connection fork reaching across a stack | item 28(i) | 377×164 |
| S10 | fork beside a plain attachment on one flank | item 28 | 364×142 |
| S11 | fork on a **perpendicular** flank (single lead) | item 28(ii) | — *unbuilt* |
| S12 | blocked interface `⊣` | item 18 / MauRen16 §3.4 | 220×88 |
| S13 | simulator on a perpendicular flank | item 16 | 350×178 |
| S14 | free interface (dotted, top) | item 18 | 330×88 |
| S15 | dashed specification frame | item 18 | 432×142 |
| S16 | dashed frame + **corner name** | item 12 | 436×170 |
| S17 | folded deck | item 12 | 516×160 |
| S18 | n-party ladder (BBM18 Fig 4) | item 14 | 432×214 |
| S19 | **equation pair** (`≡` / `≈[ε]` between two figures) | item 6 | **787×186** (toy) |
| S20 | **indexed family with ellipsis members** `F₁ F₂ ⋯ Fₙ` | item 17 | — *unbuilt* |
| S21 | **intruder stub vs live intruder crossing** | item 15 | — *unbuilt* |
| S22 | **no-effect gap** (`size.gap.noEffect`) | item 15 / BMT18 Fig 6 | — *unbuilt* |

Also named by §12 but out of this matrix on purpose: the ε corner badge
(item 24's one narrow exception), the hybrid corner badge (item 23), the
proof chain of picture-equalities (item 23), the wide joint-action box
(item 17).  Each is a shape and each needs a row once it exists; three of
them are *wider than anything we render today*, which is why they are
called out rather than silently omitted.

Why the additions matter for policy, not just for completeness:

* **S19 is the widest object the renderer emits** and it is the first
  thing that breaks: 787px natural against a 375px medium.
* **S20 is the corpus's own folding device.**  The deck (S17) is *ours*.
  A rule that folds an indexed family to a deck when the literature folds
  it to `F₁ F₂ ⋯ Fₙ` is a departure that must be argued, not defaulted to.
* **S21 and S22 are the two shapes a folding rule must never touch**: for
  them the *absence* is the semantics (item 15: "Absence of output IS the
  filter's rendering").  Folding a stack containing a filtered interface
  deletes the only rendering of the filter.

### 1.2 Media — six, and one of them is not a viewport

| code | medium | width × height | why it is distinct |
|---|---|---|---|
| **N** | infoview, narrow | 250–600 × tall | the default; user-resizable down to ~250px, lower than the brief's 380 |
| **W** | infoview, wide | 600–1000 × tall | the comfortable case |
| **B** | infoview, **bottom-docked** | ≥1000 × **≤250** | *missing from the brief*, and the one that breaks first vertically |
| **G** | gallery / browser page | ≥1200 × tall | many figures stacked; page-level vs per-figure overflow is decided here |
| **M** | mobile | ~375 × tall | below the atom width — a regime, not a size (see §5) |
| **X** | static export (LaTeX, print) | — | **not a viewport of this renderer** |

Two corrections:

* **The height axis is real and was missing.**  A bottom-docked infoview
  is ~180–250px tall.  The tallest figure we render today is 232px, and a
  two-row move menu adds 64px more.  Every vertical policy below is about
  **B**, and B is where R4's fixed fold order is provably wrong (§4).
* **X is a different renderer.**  `#cc_latex` (`SurfaceLatex.lean`) is a
  separate emitter with its own grammar; §12 item 20(f) already concedes
  that a lensed view "degrades to item 19's paired figures".  So X is not
  a column of *this* matrix: the only cross-cutting requirement is that
  every interactive state have a static equivalent, and §3.3 records
  which do.

### 1.3 Chrome layers — the third axis the brief folded into "shapes"

| code | layer | owner | hangs |
|---|---|---|---|
| C1 | hit layer (click targets, hover outline) | `SurfacePanel` | over the boxes |
| C2 | move menu | `SurfacePanel` | **below** the selected box |
| C3 | pseudocode lens | `SurfacePanel` | **below**, from the box's top-left |
| C4 | the rail (`calc` / ε-rail + buttons) | `SurfacePanel` | **beside** the stage |
| C5 | deck outline | emitter (item 12) | +3px behind an element |
| C6 | corner name on a dashed region | emitter (item 12) | at the region's top-left |

C2 and C3 hang **below** the diagram, and that single fact is what makes
R3 insufficient on its own (§4, R3-fail-1).

### 1.4 States — six, with two corrections and two additions

| state | note |
|---|---|
| default | — |
| hover | **only exists where a hit layer exists.**  Item 26(c): the outline is drawn by the chrome, not the box, because the hit sits above the box and `.cc-box:hover` never fires.  So hover is empty in `#cc_diagram`, in the gallery and in export. |
| folded | **a view directive (D1), not a state**, and per item 27 it is *incompatible with D4 addressing*: `#cc_panel` accepts no view clause and a fold-collapsed box is stamped unaddressable.  So `folded × {selected, panel open, lens open}` is empty **by construction**. |
| selected | one node at a time; drives C2 and C3 |
| panel open (C2 visible) | — |
| lens open (C3 visible) | — |
| **unaddressable** *(new)* | a node that is drawn and offers nothing — a fold-collapsed box (item 27) or one `Move.decode?` cannot read (`ResourceAt.attach`).  Today it is *visually indistinguishable* from an addressable node: it simply does not respond.  A real gap (§5). |
| **refused** *(new)* | `#cc_panel t with [commute]` on a term that does not license it is an **error and no diagram at all**.  "The picture is not drawn" is a state a media policy has to admit. |

---

## 2. The rules, as amended

Marc's four, corrected by the matrix.  Changes are marked ▲.

> **R1′ — legibility floor *and cap*, reader-relative between them.**  A
> label never renders below its floor.  ▲ It also never renders above its
> **cap**, because §12 item 1 fixes the box at 120px and the label budget
> at 12 codepoints: the middle-ellipsis is computed in *codepoints at
> authoring time*, so a label too wide in *pixels* is clipped by
> `overflow: hidden` with no ellipsis at all.  Between floor and cap the
> size follows the reader's own font (`em`).  ▲ The floor applies to
> chrome type too (menu, rail, tab), which is the smallest type on the
> screen at 10–11px.
> Values: box 13–14, tag 12–13, corner 11–12 px.

> **R2′ — orientation is semantic *inside a `.cc-diagram`*.**  Party
> flanks left/right, free above, adversary below, distinguisher beside
> (item 22) is grammar; no medium may rotate or reflow it.  ▲ The scope
> qualifier is load-bearing: without it R2 forbids the only workable
> narrow layout, since the *rail* must be allowed to move below the stage.
> ▲ And R2 does **not** govern the equation pair's `≡` axis: the relation
> symbol is a relation, not an interface geography.

> **R3′ — overflow, not scale.**  Natural size inside
> `overflow: auto; max-width: 100%`.  Nothing is ever scaled, so every
> audited pixel survives.  ▲ Companion clause, which R3 needs to be
> implementable: **chrome that hangs below a diagram reserves its own room
> in the scroll container**, because `overflow-x: auto` forces
> `overflow-y` to `auto` too (CSS Overflow 3 §3.3) and an unreserved menu
> would need a second scroll to read.

> **R4′ — fold along the axis that is short.**  ▲ *Not* a fixed order.
> Measured: folding a serial chain takes the widest figure from 684px to
> 516px — **168px of width, no height**; folding a `∥` stack to a deck
> takes height and *no width at all* (`stackRows` centres rows in the max
> width).  So: a narrow medium folds serial chains and never the stack; a
> short medium (B) folds the stack and never the chain.
> ▲ Step 2 splits by shape: an **indexed family** folds to the sourced
> ellipsis member (item 17, S20), a heterogeneous stack to the deck (S17).
> ▲ Step 3 — "labels to initials with a tooltip" — is **deleted**: item 1
> already spends both budgets (the label is already middle-ellipsized and
> the `title` already carries the full name), and initials would be a new
> unsourced encoding.
> ▲ Hard exclusion: a fold may never remove an intruder stub (S21) or a
> no-effect gap (S22).
> ▲ Scope: **R4 cannot fire in `#cc_panel` at all** (item 27).

▲ **R5 (new) — hanging chrome reserves, and the reserve is measured.**
The room C2/C3 need is a function of two *counts* (menu rows, lens lines),
never of a coordinate.  The browser gate checks the foot of each layer
lands inside the stage (`menu-below-the-fold`, `lens-below-the-fold`), so
the reserve is a checked property rather than a guess.

▲ **R6 (new) — every interactive state has a static equivalent, or is
declared chrome-only.**  Item 20(f) sets the precedent.  §3.3 tabulates
which layers have one.

---

## 3. The matrix

Policy codes:

| code | meaning |
|---|---|
| `=` | renders as-is |
| `PAN` | natural size; the *stage* scrolls (R3′) |
| `WRAP` | chrome wraps below the stage |
| `FOLD-S` | fold serial converter chains (width) |
| `FOLD-⋯` | fold an indexed family to ellipsis members (item 17) |
| `FOLD-DECK` | fold `∥` rows to a deck (height) |
| `PAIR-V` | stack the two sides of an equation pair vertically |
| `∅` | empty by construction |
| `✗` | unsupportable — state it, do not pretend |
| `!` | needs a change in a file this pass may not edit (named) |

### 3.1 Shapes × media

| shape | N (250–600) | W (600–1000) | B (short) | G (≥1200) | M (375) | X (export) |
|---|---|---|---|---|---|---|
| S1 base resource | `=` | `=` | `=` | `=` | `=` | `=` |
| S2 2-row stack | `=` | `=` | `=` | `=` | `=` | `=` |
| S3 n-row stack | `=` | `=` | `FOLD-DECK` n≥3 `!` | `=` | `=` | `FOLD-DECK` |
| S4 attach ×1 | `=` | `=` | `=` | `=` | `PAN` | `=` |
| S5 serial chain | `PAN`, `FOLD-S` outside the panel | `=` | `=` | `=` | `PAN` | `FOLD-S` |
| S6 opposite flanks | `PAN` <600 | `=` | `=` | `=` | `PAN` | `=` |
| S7 nested one flank | `PAN` <400 | `=` | `=` | `=` | `PAN` | `=` |
| S8 fork, one resource | `PAN` <350 | `=` | `=` | `=` | `PAN` | `=` |
| S9 fork across a stack | `PAN` <390 | `=` | `FOLD-DECK` `!` | `=` | `PAN` | `=` |
| S10 fork + attach | `PAN` <380 | `=` | `=` | `=` | `PAN` | `=` |
| S11 fork, perpendicular | *unbuilt* | *unbuilt* | *unbuilt* | *unbuilt* | *unbuilt* | *unbuilt* |
| S12 blocked | `=` | `=` | `=` | `=` | `=` | `=` |
| S13 simulator below | `PAN` <360 | `=` | ✗ (the drop is vertical grammar; R2′ bars moving it) | `=` | `PAN` | `=` |
| S14 free interface | `=` | `=` | ✗ (same, upward) | `=` | `PAN` | `=` |
| S15 dashed frame | `PAN` <450 | `=` | `=` | `=` | `PAN` | `=` |
| S16 frame + corner name | `PAN` <450 | `=` | `=` | `=` | `PAN` | `=` |
| S17 folded deck | `PAN` <530 | `=` | `=` | `=` | `PAN` | `=` |
| S18 n-party ladder | `PAN` | `=` | ✗ for n≥4 (parties stack **vertically** on the flank, item 14 — they cost height) | `=` | `PAN` | `=` |
| S19 **equation pair** | `PAN` (783px content in a 375 stage — measured) — wants `PAIR-V` `!` | `PAN` <800 | `=` | `=` | `PAN`, wants `PAIR-V` `!` | `=` |
| S20 indexed family | *unbuilt*; policy: `FOLD-⋯` is the shape, not a fold | | | | | |
| S21 intruder stub | `=`, never folded | `=` | `=` | `=` | `=` | `=` |
| S22 no-effect gap | `=`, never folded | `=` | `=` | `=` | `=` | `=` |

Reading the table: **the only genuinely width-constrained media are N
below ~450px and M**, and for both the answer is `PAN` — because R4 is
unavailable in the panel (item 27) and the gallery has the room.  Height
(B) is where structural folding is actually required, and that is exactly
where the current fold machinery cannot be invoked.

### 3.2 Chrome × media

| layer | N | W | B | G | M | X |
|---|---|---|---|---|---|---|
| C1 hit layer | `=` (scrolls with the stage) | `=` | `=` | ∅ (no panel on the gallery page) | `=` | ∅ |
| C2 move menu | `=` + R5 reserve; may exceed the medium's width and pan (measured 331px in a 375 medium) | `=` | ✗ — a 64–124px menu under a ≤250px medium leaves nothing of the figure | ∅ | `=` + pan | ∅ |
| C3 lens | `=` + R5 reserve; body capped at `--cc-lens-maxw/maxh`, scrolls internally | `=` | ✗ — same reason | ∅ | `=` | ∅ → paired figures (item 19) |
| C4 rail | `WRAP` below the stage | `WRAP` (measured: the single figure still wraps at 600, since 431+16+290 = 737 > 600) | `WRAP`, and then the medium is all rail | `=` beside (measured: the pair sits beside at 1200, 894+16+290 = 1200) | `WRAP` | ∅ → `write calc below` writes the chain into the file |
| C5 deck outline | `=` | `=` | `=` | `=` | `=` | `=` |
| C6 corner name | `=` | `=` | `=` | `=` | `=` | `=` |

### 3.3 States × media, and R6's static equivalents

| state | N/W | B | G | M | X | static equivalent |
|---|---|---|---|---|---|---|
| default | `=` | `=` | `=` | `=` | `=` | — |
| hover | `=` | `=` | ∅ | `=` (touch: no hover) | ∅ | none needed |
| folded | ∅ in the panel (item 27); `=` in `#cc_diagram` | | `=` | | `=` | the composed name (item 12) |
| selected | `=` | `=` | ∅ | `=` | ∅ | none needed |
| panel open | `=` | ✗ | ∅ | `=` | ∅ | **none — declared chrome-only** |
| lens open | `=` | ✗ | ∅ | `=` | ∅ | item 19's paired figures |
| unaddressable | `=` but **indistinguishable from addressable** — gap | | | | | the node table prints `—` (item 7) |
| refused | no diagram; the error is the output | | | | | the error message |

---

## 4. Where the four rules fail

### R1 (legibility floor)

1. **A floor without a cap is unimplementable against item 1.**  The
   emitter's middle-ellipsis is computed in codepoints at authoring time;
   the box is `overflow: hidden; white-space: nowrap`.  So a label that is
   within budget in *codepoints* but over budget in *pixels* is cut with
   no ellipsis and no signal.  Measured widths in the fallback monospace:
   a 12-codepoint resource label is ≈101px at 14px and ≈108px at 15px
   against a 116px inner width; the 8-codepoint converter budget is 67px
   at 14px and **72px at 15px against a 72px inner width** — exactly at
   the edge.  **14px is the cap, and it is arithmetic, not taste.**
2. **The floor breaks the emitter's own bounds estimate.**  `Prim.bounds`
   sizes a tag at 6.2px/char, calibrated for 11px type.  Raising tags to
   12–13px makes that estimate wrong, and the estimate is what the dashed
   frame's pad-symmetry audit (item 11b) is computed from.  Measured: no
   tag collisions in the panel corpus at 13px — but that is the corpus's
   luck, not a guarantee.  **This is why the floor must be a token inside
   `SurfaceWidgets.lean` and not a stylesheet override** (§7, request 1).
3. **R1's escape hatch does not exist where R1 bites.**  "If it does not
   fit, the diagram folds or scrolls" — folding is barred in the panel
   (item 27), so in the panel the hatch is *scroll only*.
4. **R1 is silent about chrome**, which is the smallest type on screen
   (menu 11px, caption/buttons 10px).  Fixing only the diagram fixes half
   the complaint.  → R1′ extends the floor to chrome.

### R2 (orientation is semantic)

1. **Unscoped, R2 forbids the only workable narrow layout.**  The rail is
   not grammar; at a 375px medium it *must* move below the stage.  R2 has
   to say "inside a `.cc-diagram`".
2. **R2 wrongly captures the equation pair.**  Item 25 says EquationPair
   is "horizontal per PorRen22 Fig 5", but the `≡` axis carries a
   *relation*, not an interface geography, and item 23's proof chain
   already sets the step number *over* the symbol.  Two 400px figures do
   not fit side by side in 375px, and stacking them is not a lie about
   roles.  **`PAIR-V` is legitimate and unavailable**: `Diagram.pairHtml`
   is a non-wrapping `inline-flex` row in `SurfaceWidgets.lean` (§7,
   request 3).
3. **R2 does correctly bar** moving the adversary drop (S13) or the free
   interface (S14) for a short medium — which is what makes those cells
   genuinely unsupportable rather than merely unimplemented.

### R3 (overflow, not scale)

1. **`overflow` is axis-coupled, so R3 alone does not work.**  `overflow-x:
   auto` forces `overflow-y: visible` to compute to `auto`.  Everything
   that hangs below a diagram — the move menu, the open lens, the
   adversary dangle — then needs a second, vertical scroll to read.  R3
   needs R5.  Measured after implementing R5: reserve slack 62px (menu)
   and 110px (lens), down from 116px/199px with a static reserve.
2. **R3 provides no affordance.**  A clipped diagram in a scroll container
   looks like a *broken* diagram; overlay scrollbars are invisible until
   you scroll.  The corpus offers nothing, and item 20(d) bans gradients,
   so a fade is out.  A 1px rule at the pannable edge plus
   `scrollbar-gutter: stable` is line work and therefore paper-legal — but
   it is **ours**, and item 24's discipline says it must be labelled as an
   extension.  **Open, and honestly a gap.**
3. **R3 cannot be applied where it is most needed.**  The gallery page
   overflows at the *document* level: at a 500px window
   `document.scrollWidth` is 960px and 3 of 43 figures cross the viewport
   edge (widest figure 684px, median 326px).  The fix is one rule in
   `SurfaceGallery.lean`'s `pageCss` (§7, request 2).
4. **R3 says nothing vertical.**  An 8-row stack is ~500px tall and a
   bottom-docked infoview is ~180px.  There is no scroll answer that keeps
   the flanks visible, because the flanks *span* the stack.

### R4 (fold to fit, in a fixed order)

1. **R4 cannot fire in `#cc_panel`.**  Item 27: no view clause, and a
   fold-collapsed box is unaddressable.  R4 is a `#cc_diagram`/gallery
   rule and the panel is the medium with the width problem.
2. **The fixed order is wrong for the stated problem.**  Measured: serial
   fold 684→516px (168px of width, no height); `∥`→deck buys height and
   **zero** width.  R4 orders width-saving before height-saving
   unconditionally; the axis that is short should decide.
3. **Step 3 is already spent.**  Item 1 middle-ellipsizes the label and
   puts the full name in `title`.  There is no second truncation, and
   "initials" would be a new unsourced encoding.  Delete the step.
4. **Step 2 has a sourced alternative R4 does not mention.**  Item 17's
   ellipsis member `F₁ F₂ ⋯ Fₙ` is the corpus's folding device; the deck
   is ours.  For an indexed family the sourced device should win.
5. **R4 has no exclusion list, and needs one.**  Folding a stack that
   contains a filtered intruder interface (S21) or a no-effect gap (S22)
   deletes the only rendering of the filter — item 15's "absence of output
   IS the filter's rendering".

---

## 5. Cells that are genuinely unsupportable

Stated rather than papered over.

1. **B (bottom-docked, ≤250px tall) × any panel state.**  The move menu is
   64–124px and the lens body up to 220px; both hang below the selected
   box.  Reserving room (R5) is what stops them overlapping, and in a
   250px medium the reserve *is* the medium.  There is no layout that
   shows a figure and its menu in 250px of height, and R2′ forbids moving
   the menu sideways into the flank geography.
2. **B × S13/S14 (adversary below, free above).**  The vertical drop and
   the dotted top wire are geography (item 2).  A short medium cannot show
   them without either scaling (banned by R3′) or moving them (banned by
   R2′).
3. **B × S18 with n≥4 parties.**  Item 14 stacks one converter box per
   party *vertically* on the flank, so parties cost **height**: the
   measured n-party target is 432×214 and each further party adds a pill
   plus `flankGapF`.  A ≤250px medium cannot hold four, and folding
   parties would delete the interface set the picture exists to show.  (M
   is *not* the failing medium here — width-wise the ladder pans like
   anything else.  The width floor is instead the atom: a bare resource
   measures **196px** = 120px box + 2×30px stubs + 2×8px diagram margin,
   so nothing at all folds below ~200px.)
4. **X × {hover, selected, panel open}.**  No hit layer exists in a static
   export.  Item 20(f) already concedes the point for the lens; the move
   *menu* is declared chrome-only and needs no static form, because its
   static form is the file the click writes.
5. **`folded` × {selected, panel open, lens open}.**  Barred by item 27 —
   an address through a collapsed node names the wrong subterm.
6. **The `unaddressable` state has no rendering.**  A drawn node that
   offers nothing looks exactly like one that does; the reader discovers
   it by clicking and getting nothing.  A non-colour signal is available
   (item 5 requires one anyway) and none is spent — but any candidate is
   *ours*, so it needs the item-24 argument before it ships.  Left open
   deliberately.

---

## 6. Measured evidence

Harness: headless Chrome
(`--headless --disable-gpu --virtual-time-budget=6000 --dump-dom`), with
the page's own self-audit writing JSON into a `<pre>`, the same discipline
as §12 item 11.  **A medium is modelled as a fixed-width `div`, not as a
window** — an infoview *is* a fixed-width panel, and headless Chrome
refuses to open a window narrower than 500px (a `--window-size=375,800`
run reports `innerWidth` 500), so a 375px window cannot be measured but a
375px medium can.

### Gallery, 43 figures (`.lake/cc_gallery.html` as of the start of this pass; the in-flight emitter rewrite has since taken it to 41)

| | |
|---|---|
| figure widths | 196 – **684** px, median 326 |
| widest | "deep converter chain" 684×160 |
| its folded twin | "fold: serial run to one pill" 516×160 → **serial folding saves 168px of width** |
| tallest | 232px ("nested construction"), 214px (MaRuTa12 Fig 1) |
| at a 500px window | `document.scrollWidth` 960, **3 figures past the viewport edge** |
| at 600 | 1 past the edge |
| at 1200 | 0 |
| label sizes | 13px box / 11px tag / 10px corner — all hard-coded |

### Panel, before

Measured on the previous `.lake/cc_panel_chrome.html` inside fixed-width
frames:

| medium | `.cc-panel` client / scroll | overflow | rail ∩ diagram |
|---|---|---|---|
| 375 | 327 / **737** (single), **1021** (pair) | 410px, 694px | 1 |
| 480 | 432 / 737, 1021 | 305px, 589px | 1 |
| 600 | 552 / 737, 1021 | 185px, 469px | 1 |
| 900 | 852 / 852, **1021** | 169px (pair) | 1 |
| 1200 | 1152 / 1152 | 0 | 0 |

`document.scrollWidth` reached **2748px** against a 375px medium.  At 900
the stage measured 715px wide with 783px of content and
`overflow: visible` — i.e. **68px of diagram painted on top of the rail**,
which is the reported "things overlap".

### Panel, after (`.lake/cc_panel_chrome.html`, 5 media, **0 violations**)

Two readings, because the emitter moved underneath this work (another
session is redesigning wire routing in `SurfaceWidgets.lean`, and the
gallery went from 43 cases to 41 mid-pass).  The before/after overflow
comparison above and the first reading below are both against the *old*
emitter, so they are apples to apples; the second reading is the final
state and is what reproduces today.  Both are 0 violations — which is the
point of expressing the reserve as a checked property rather than a
constant: it re-verifies against whatever geometry the emitter emits.

| case | medium | panel overflow | stage w / content | pans | fonts (box/tag) | reserve slack (menu/lens) |
|---|---|---|---|---|---|---|
| D4 single, narrow | 375 | **0** | 375 / 431 | yes | 14 / 13 | 62 → 89 / — |
| D4 single, wide | 600 | 0 | 600 / 600 | no | 14 / 13 | 62 → 89 / — |
| D4 single, lens open | 600 | 0 | 600 / 600 | no | 14 / 13 | 119 → 146 / 110 → 137 |
| D5 pair, narrow | 375 | **0** | 375 / 783 | yes | 14 / 13 | 62 → 89 / — |
| D5 pair, wide | 1200 | 0 | 894 / 894 | no | 14 / 13 | 62 → 89 / — |

Lens: closed → body measures **0×0**; open → **358×112**, left edge
aligned to the box's own left edge within 0.51px, opaque, and the diagram
beneath at computed opacity **0.45** (item 20c, fired by `:has()`, with
`decorateLast`'s own dimming switched *off* in that case so the `:has()`
path is what is being measured).  Lens tab: 297px before naming the box
rather than the subtree, **155px** after.

Checks in the gate, all at 0 violations: `hit-off-box`,
`link-does-not-fill`, `menu-not-left-aligned`, `menu-not-anchored-under`,
`menu-not-opaque`, `context-not-dimmed`, `panel-overflows-medium`,
`stage-not-a-scroll-container`, `rail-painted-over-diagram`,
`menu-below-the-fold`, `lens-below-the-fold`, `label-below-floor`,
`label-clipped-by-box`, `tags-collide`, `closed-lens-draws`,
`lens-tab-not-drawn`, `open-lens-empty`, `lens-not-anchored-on-object`,
`lens-not-opaque`, `lens-context-not-dimmed`.

---

## 7. What is implemented, and the four changes that need another file

Implemented in `RandomSystems/Jost/SurfacePanel.lean` (§6's "after"):

* **R3′ + R5** — `.cc-panel` is a wrapping flex row at `max-width: 100%`;
  `.cc-stage` is the scroll container (`flex: 1 1 auto; min-width: 0;
  max-width: 100%; overflow: auto`); hanging chrome reserves room through
  `:has()`, sized from the menu's row count and the lens's line count
  (`Panel.reserveStyle`), with the reserve *checked* in the browser.
  Degradation without `:has()` is safe: a scrollbar instead of a reserve,
  never an overlap.
* **R1′** — `Panel.fontScale` = `[(box, 13, 14), (tag, 12, 13),
  (corner, 11, 12)]` drives both the CSS `clamp(floor, k·em, cap)` custom
  properties and the browser gate's floors, so rule and gate cannot drift.
* **The lens (C3)** — a `details`/`summary` overlay: absolutely
  positioned (no reflow, item 20a), anchored at its object's top-left
  (20b), context dimmed not hidden (20c), 1px opaque panel at token radius
  (20d), and the `summary` is simultaneously item 21's grey identity tab
  and item 20(e)/26(b)'s drawn cross + re-click toggle.

**Why `details`/`summary` and not a hidden checkbox.**  Both are pure
CSS/HTML and both satisfy the `mk_rpc_widget%` constraint.  `details` wins
on four counts: (i) it needs **no `id`**, and a checkbox + `~` sibling
selector needs a document-unique one — several panels share one infoview,
so the ids would collide; (ii) the `summary` is natively focusable and
keyboard-operable, so the tab is a real control rather than a styled
`label`; (iii) one element is *both* the open affordance and the dismissal,
which is literally what item 26(b) substitutes for click-outside/Esc; (iv)
with a wrapping `label`, clicking inside the panel body would toggle it —
you could not select the code you came to read.  The cost, stated: the
open state is DOM state, so any command edit re-elaborates and the lens
returns closed.  That is correct — a peek is transient (item 20), and real
state belongs in the file (item 26).  The considered alternative was to
make the lens a command clause (`#cc_panel … show code`), which *would*
put it in the file and, unlike `fold`, would invalidate no address; it was
rejected only because it costs an LSP round trip and a file edit per look.

### Changes needed in files this pass may not edit

1. **`SurfaceWidgets.lean` — make the three font sizes tokens.**  In
   `Prim.toHtml`, replace the literals
   `("fontSize", "13px")` (box), `("fontSize", "11px")` (tag),
   `("fontSize", "10px")` (corner)
   with
   `("fontSize", "var(--cc-font-box, 13px)")`,
   `("fontSize", "var(--cc-font-tag, 11px)")`,
   `("fontSize", "var(--cc-font-corner, 10px)")`.
   That is the whole change.  It (a) lets the panel's three `!important`
   declarations be deleted unchanged, (b) extends R1 to the **gallery and
   `#cc_diagram`**, which the panel's scoped stylesheet cannot reach, and
   (c) keeps `Prim.bounds`' 6.2px/char estimate and the rendered type in
   one place, which is the correctness argument in §4/R1-fail-2.  Ratified
   token names to record in §12 item 25: `font.label.box` 13–14,
   `font.label.tag` 12–13, `font.label.corner` 11–12, each
   `clamp(floor, k·em, cap)`.
2. **`SurfaceGallery.lean` — one rule in `pageCss`.**
   `.diagram { max-width: 100%; overflow: auto; }`
   This is R3 for the gallery; measured need: 3 of 43 figures cross a
   500px viewport today and the page scrolls horizontally as a whole
   rather than per figure.
3. **`SurfaceWidgets.lean` — `Diagram.pairHtml` needs a vertical form.**
   It is `display: inline-flex; flex-direction: row` with no wrap, so an
   equation pair is 787px minimum.  Either `flex-wrap: wrap` with the
   relation symbol allowed to sit on its own line, or an explicit
   `PAIR-V` variant.  §4/R2-fail-2 argues this is not an R2 violation.
4. **`SurfaceGrammar.lean` (or `SurfaceNames.lean`) — a `cc_pseudocode`
   store**, so the lens can show the real thing.  Today the `resource …
   where` block is compiled away and nothing keeps its text; the lens
   therefore shows the item-7 structure twin and the term.  A parametric
   attribute carrying the block's source (or its declaration range, read
   back through the file map) is enough.

### Not done, and why

* **An affordance for a pannable edge** (§4/R3-fail-2).  Every candidate
  is unsourced; item 24's discipline says it must be argued and labelled
  as ours before it ships.
* **A rendering for the `unaddressable` state** (§5.6).  Same reason.
* **`FOLD-⋯`, the ellipsis member (S20)** — sourced (item 17) and unbuilt;
  it is the correct fold for an indexed family and it lives in the
  emitter.
* **R4′ itself.**  It is a `#cc_diagram` rule (item 27 bars it from the
  panel) and every one of its steps lives in the emitter's view
  directives, which this pass may not touch.
