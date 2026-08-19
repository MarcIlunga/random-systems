# Status — Random Systems in Lean 4

Single tracking document.  Design rationale lives in `DESIGN.md`.  This file
consolidates and supersedes the former `PROOF_GAPS.md`, `MIGRATION_STATUS.md`,
`DOWNSTREAM.md`, the checklist/roadmap files, and `attic/README.md`
(2026-07-02 consolidation; full historical detail is in git history).

## Signed-PDS pen-and-paper research program (2026-08-04)

[FOUNDATIONS.md](FOUNDATIONS.md) is the notation and presentation authority
for this program. It follows the Maurer--Lanzenberger order through
distributions, systems, games, advantage, and coupling, and then separately
defines the virtual signed extension and the common transcript, gain-graph,
and collision notation.

The next mathematical targets are organized in
`sketches/signed-pds-research-program.md`.  This is a research charter, not a
Lean-status claim.  It separates closed identities, complete pen-and-paper
derivations, open analytic obligations, and conjectural benchmark improvements.

The three detailed branches are:

- `sketches/sop2-general-groups.md`: universal collision proxy for the product
  of two random permutations over an arbitrary finite group, a basis-free
  partition-Mobius remainder certificate, and the still-open sharp scalar tail
  summation;
- `sketches/sop1-general-groups.md`: the exact ordered-product SoP1 model,
  square-root-profile obstruction, finite-abelian binomial proxy, and the open
  connected-pair remainder;
- `sketches/signed-pds-symmetric-benchmarks.md`: fifteen source-audited
  symmetric-cryptography targets, ranked by the likelihood of obtaining a
  genuinely simpler or tighter theorem.

The first dedicated benchmark follow-up is
`sketches/hctr2-representative-study.md`. It separates the native tagged
multi-user random-system game from Definition 2.27's several-system distance,
derives the honest workload-profile coupling bound, gives exact one-block and
long-stream matching attacks, and quarantines the still-open signed-rook
remainder estimate.

No Lean work is authorized by these notes yet.  The immediate proof order is
truncated permutations, the general-group SoP2 tail sum, finite-abelian SoP1,
key-alternating complete links, cascaded-LRW2 gain cycles, and only then
CBC-MAC/OMAC hidden-path cancellation.

## SequenceHash and SequenceMAC v1.0.0 pen-and-paper program (2026-08-04)

The stable C2SP v1.0.0 text and the earlier v0.1.0 draft are preserved
byte-for-byte under `sequence-hash/specs/`; the existing Lean development and
root compatibility specification remain pinned to v0.1.0. Version-scoped
research indexes live under `sequence-hash/research/`.

The paper-facing chapters separate the security goals:

- `papers/notes/SEQUENCEHASH_CE_INDIFFERENTIABILITY.md` gives the fixed-tag,
  short-customization random-oracle analysis by conditional equivalence. The
  exact profile law, local distance, finite bound, and two-query attack are
  closed; the causal common-carrier theorem is derived. Simultaneous public
  tags and arbitrary long customizers remain open in that model.
- `papers/notes/SEQUENCEMAC_PRF_SECURITY.md` states three distinct routes:
  standard-model PRF security through a trace-preserving NMAC schedule bridge;
  direct ideal-compression PRF security through the H-technique; and a modular
  keyed-indifferentiability corollary. The published Backendal and Shen
  endpoints and the data-processing corollary are checked. The two literal
  v1.0.0 schedule embeddings, their key-entropy terms, and attack-preserving
  transfers remain open.

The direct ideal-compression follow-up is
`papers/notes/SEQUENCEHASH_MD_SMART_SIMULATOR.md`.  For fixed public
customization of at most one block it replaces the DRST HMAC router by one
typed compression graph.  The stable v1 `0x55`/`0xaa` first blocks remove the
allowed-key parser and colored-oracle hop; an exact occupied-link carrier
handles outer prequeries before the graph-join count.  The derived finite
bound is

$$
\min\!\left\{
1,
\frac{\binom{\sigma-a+1}{2}+q(\sigma-a)}{N}
+\frac{qa(N-1)}{N^2}
\right\}
\le
\min\!\left\{1,\frac{2\sigma^2}{N}\right\}.
$$

The abstract-grammar Lean formalization is now in progress.  The following
pieces compile under strict implicit-argument settings, contain no admissions,
and have accepted `#print axioms` footprints:

- `SequenceHashSimulator.lean`: executable two-interface simulator whose
  correctness tree eliminates the actual table/parser/endpoint observations;
- `SequenceHashGraphInvariant.lean`: certified live paths and typed inner
  endpoints, preserved through every generated executor leaf;
- `SequenceHashRepresentative.lean`: exact bisimulation between the ordinary
  real construction and the same simulator driven by correlated tapes;
- `DeferredSampling.lean` and `MDDeferredSampling.lean`: exact adaptive fresh
  fibre counting for hidden MD paths;
- `OccupiedLink.lean`, `OccupiedLinkProfile.lean`, and
  `OccupiedLinkGame.lean`: the exact `c(N-1)/N^2` carrier, its causal product
  bound, and its direct pre-winning-equivalence/distinguishing endpoint; and
- `SequenceHashJoinBound.lean`: the static IV/live/live-root join count.

The history-condition boundary now also compiles.  Generic infrastructure in
`RandomSystems/HistoryConditionC.lean` proves once for every seed-indexed,
prefix-monotone history predicate that the attached bit is an MBO, that the
game is normalized, and that erasing the bit recovers the underlying history
system.  `SequenceHashConditionGame.lean` therefore contains no specialized
game or `ignoreMBO` wrapper: it proves only the scheme-specific fact
`simulatorJoinAudit_prefix`.  That proof follows every generated simulator
branch and preserves visible words, hidden construction assignments, loose
roots, and the fired join flag.

The proof is not yet an end-to-end v1 theorem.  The remaining mathematical
bridge is to assemble the deferred path, occupied-link games, and join event
over the full stateful query transcript.  The stable-v1 byte codec/parser
realization and arbitrary long customization also remain open.  The existing
Lean `sequenceFunctionInnerInput` and outer schedule still use the v0.1 order
`header || derived key`; stable v1 uses `derived key || header`, so the old
schedule is deliberately not reused as a realization of this theorem.

Coupling and signed-representative alternatives occur only in the final
appendices. No v1.0.0 Lean theorem is claimed.

## `∥` migrated to Jost's disjoint interface sets (2026-08-08)

`Jost/SurfacePar.lean`'s `∥` was the MERGED operation — same interfaces, each
now providing the tagged sum of both components' services.  It is now Jost's
own (§2.2.2, printed p. 17): resources with **disjoint** interface sets, side
by side, on the union.

- `ResourceSystem.par : ResourceSystem S I → ResourceSystem S J →
  ResourceSystem S (I ⊕ J)` over `Resource.tensor` (`TypedTensor.lean`), with
  `close_par` (eq. (3)), `close_par_left`, `layoutAt_par_inl/inr`; same at the
  layout-indexed quotient (`ResourceAt.par` at `Sum.elim layoutL layoutR`) and
  for single-world resources (`Resource.par`, which no longer needs the
  free-closure embedding at all).  `Φ` becomes a FAMILY indexed by interface
  sets; Maurer11 Def. 1 is untouched, because fn. 9's "again a resource with
  the same interface set" constrains ATTACHMENT, still an endo-operation.
- **Jost Prop. 2.2.3 (2)** `Converter.attachAt_par_left` — a plain `=`, TOTAL
  (no `provides` side condition), coding-free.  This retires the `par_distrib`
  obligation `SurfaceAlgebra` used to scope, and it makes
  `RandomSystems/OneSidedConverter.lean` dead: that module existed only to
  express "γ lands in R" as a one-sided converter lift inside the merged
  model.  **Deleted.**
- **Jost Thm 2.2.5 (2)** `Converter.close_par_attachAt_left`: a construction
  statement for `R` yields one for `[R, T]` at the same ε.
- **Jost's γ, exposed.**  `Connection K rest` is the two-interface connection
  function; `α ••[γ] R` (`Converter.attachAlong`) is `π^γ R`, landing at
  `rest ⊕ Unit` = `(I_P \ img γ) ∪ I_out`.  Merge-then-attach underneath:
  bijective re-indexing along γ, `DependentRandomSystem.mergeTwo`, then the
  ordinary `•[Sum.inr ()]`.  The merge is an isometry
  (`ResourceSystem.close_mergeAlong`), so eq. (4) survives verbatim
  (`Converter.close_attachAlong`).  Merge is used FORWARD only — it is
  injective and isometric but not invertible (`not_surjective_mergeBlock`).
- **`Services.free` / `SumService` / `HasSumCode` change role, not content**:
  from the coding `∥` was built from, to the coding a MERGE lands in.  A
  development declares over `S.free` exactly when its converters reach more
  than one interface at a time.
- Flagship re-authored: `CarrierDemo.constructedShape =
  decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR)) :
  ResourceSystem demoServices (Unit ⊕ Unit)` — two independent copies of the
  toy, each converter reaching one interface of each, and the constructed
  system has exactly Fig. 2.3's two interfaces.  `encA`/`decB` are UNCHANGED:
  their paired inner side is now the service the connection faces.
  `idleShape` keeps the contrast at the same connections with a base-source
  converter, and `#cc_moves` now separates them as `—` vs `drop_idle`
  (`Converter.attachAlong_of_not_provides`).
- Renderers taught `Converter.attachAlong`: `Diagram.ofExpr` draws it as
  **DESIGN §12 item 28's CONNECTION FORK** — Jost Fig. 2.1's π_ε^A read
  first-hand: one converter pill spanning its reach, one labelled branch per
  interface γ reaches on its core-facing edge, the connection's own name on
  the outer crossing (Jost's `I_out`), and the merge still never drawn (it is
  the isometry `close_mergeAlong`, not an object).  The reach comes from
  reducing `γ.first`/`γ.second` under a heartbeat budget and prints in the
  ASCII receipt as `⟨…⟩`.  New audit check `connection-fork` (a `cc-conn-<n>`
  box must carry `n` rungs at the emitter's own `Diagram.forkPitch` on one
  edge) — mutation-tested as strictly stronger than the item-11a symmetry
  check; gallery 43 diagrams / 0 violations.  `Move.decode?` gains a
  `.attachAlong` head, for which `lift`/`merge`/`commute`/`drop_id` are
  honestly unavailable.
  - CLOSED 2026-08-08 by **DESIGN §12 items 29–30**, and the parked question
    turned out to be load-bearing: item 9a's bus was not imprecise but FALSE
    under disjoint `∥` (`Sum.inl a` is `KEY`'s interface and nothing else),
    and `n` buses into `m` rows is `K_{n,m}` — non-planar as an abstract
    graph at `n = m = 3`, so no routing could have rescued it.  Amended: a
    `•[i]` wire lands on the ONE row `i` names, read off the interface's own
    `Sum` prefix (which is `flattenParAt`'s path); a node an inner
    `attachAlong` has re-indexed falls back to the STACK BRACKET, per flank.
    Rows nothing names keep their interfaces as straight boundary crossings.
    Routing: two-bend orthogonal routes at a constant `radius.bend`, one
    channel track per bending wire ordered by a strict partial order, all
    inside per-row BANDS.  New audit checks `wire-crossing` /
    `wire-overlap` / `wire-through-box` with a mutation receipt at
    `.lake/cc_planarity_mutation.html` (control 0, mutant 2); gallery 43
    diagrams / 0 violations, and the old corpus measured 13 crossings.
    STILL OPEN, and now precisely stated (§12 item 30(e)): planarity holds
    iff a flank's reach sets are non-crossing INTERVALS of the row order.
    `α ••[γ] (enc •[i] R)` over `A ∥ B ∥ C` with γ reaching rows 0 and 2 and
    `i` naming row 1 is constructible and draws one crossing — a TERM
    property no router can fix, which is why the check is a gate and not a
    guarantee.
  - Field-order trap recorded at `Diagram.Shape.attach`: Lean applies
    constructor DEFAULTS INSIDE PATTERNS, so a `match` arm that omits a
    trailing defaulted argument silently becomes a constraint that the field
    equals its default — with a catch-all arm present it does not even warn.
    `folded` is therefore the last field (the only one false on every node
    `ofExpr` discovers).  Every consumer that does not need the trailing
    fields now matches `.attach conv ifc ..` (arity-proof); the four that do
    spell all ten.
  - **CLOSED 2026-08-08 by DESIGN §12 item 31**, and it was a SEMANTIC defect
    a green audit shipped: the eq.-(1) shape drew both connections on one
    flank with all four branches on the stack bracket, and labelled both of
    `enc^{γᴬ}`'s branches `u`.  Cause: item 28's scope (i) refused to read a
    re-indexed reach at all, and item 30(d)'s per-flank granularity then
    demoted the INNER connection with it.  The refusal was unnecessary —
    `Diagram.descendInterface` pushes an index into `rest` back through the
    inner `Connection.untouched`, so `γᴮ` resolves to `Sum.inl Party.v`,
    `Sum.inr Party.v` and item 28's scope (i) is closed for connections (it
    stands for plain attachments).  A connection is now placed by the
    interfaces it REACHES, so the picture is Jost Fig. 2.1 exactly: π^A left,
    π^B right, each forking to both rows.  Branch labels are qualified by the
    row (Jost printed p. 27, "interface A of AuthChan"), falling back to the
    row's POSITION when two rows share a name — `1.u`/`2.u`.  New audit
    checks `wrong-target` (a lead's `data-target` row must be the box it
    lands on) and `duplicate-branch-label`, with a mutation receipt at
    `.lake/cc_target_mutation.html`: control 0, mutant 1, the shipped
    drawing rebuilt by hand 2, label mutant 1.  Gallery 43 diagrams /
    42 targeted leads / 5 labelled forks / 0 violations.  Residual, recorded
    not hidden (§12 item 31(h)): `connection beside a plain attachment` still
    draws one lead with sharp corners — 10px of drop where two `radius.bend`
    arcs need 12, and item 29 forbids shrinking the radius.

Open, and now much cheaper than before: `par_comm`/`par_assoc` are no longer
blocked by a re-CODING (the merged `∥` needed one; `SumService.sum` is
injective).  They are `Equiv.sumComm` / `Equiv.sumAssoc` re-indexings, which
the kernel already has together with their isometry
(`DependentRandomSystem.reindex`, `edist_reindex`); only the surface
`ResourceSystem.reindex` and the two instances are missing.

Gates: full `lake build` green; surface audit **70 → 89 clean**, 5 bridges, 4
demoted (unchanged); gallery **0 violations / 39 diagrams / 204 port checks /
4 multi-port ladders** (identical to the pre-migration record — no renderer
change); every headline axiom-clean.

## CC DSL interaction ladder D1–D5 (2026-08-06; D1+D2 shipped, D3–D5 designed)

The ladder (from the "visual proving" question): D1 view folds · D2 named
fold recognition · D3 algebraic moves as kernel-backed rewrites · D4 the
interactive panel · D5 the ε-mode rail.  The insight that fixes the
dependency order: the pictures reachable by folding/unfolding/rearranging
a diagram ARE the term's equivalence class under the CC algebra, so
"nicer visuals" and "visually performing the algebraic laws" are the view
layer and the proof layer of one mechanism.

**D1+D2 shipped** (`68a2345`, design frozen in DESIGN §12 item 12):
`#cc_diagram t with [fold enc]` / `[fold KEY ∥ AUT as "NET"]` /
`[unfold NET]`, also on `thm` pairs (directives apply to both sides).
`with` is load-bearing: `#cc_diagram t [fold α]` ALREADY parses as an
application to a list literal (because `fold` must stay an ordinary
identifier), and the view category needs `behavior := both` so a leading
ident consults the token index.  Folded elements carry the deck outline;
a folded serial run is one pill labelled by the composed name
(`enc∘…enc`, never a count); every dashed region names itself at the
top-left corner (Maurer's convention, migrated from centred summaries).
D2 recognition is DEFINITIONAL (heartbeat-bounded, type gate first), so
`as` overrides only the name while the recognized role still colours the
box — and it sees through semantically-idle attachments
(`enc^a (KEY ∥ AUT) = NET` by rfl at the demo layout), which split the
old collapse case into anonymous (corner label) and recognized (named).
`Shape` now carries its sub-`Expr`: the D3 data path, no moves yet.
Gates: 30 cases → 32 diagrams, extended audit 0 violations (149 axis
checks, 18 frames), 24/24 pre-existing corpus cases byte-identical, 32
pins green, surface audit unchanged 59/5/4.

**Audit extensions** (DESIGN §12 item 11, from Marc's centring critique):
wire-AXIS centring and frame-pad SYMMETRY — bounds containment alone is
not an audit.  A mutation run confirms they bite: a 5px box nudge trips
the axis check but NOT the old floating-endpoint check.

**Renderer conformance to the sourced grammar** (`7ac3570`): the emitter
now obeys §12 items 13–18 — the n-party party ladder (`Flank` carries an
index; a classifier emits a SLOT and a geography pass numbers it, since
per-interface classification cannot know spine order), `block` drawn as
a wire that stops INSIDE the boundary (absence of output is how the
papers render a filter — our `⊣` got a sourced picture), one simulator
COLUMN per interface (they were previously stacked in series on one
wire, i.e. drawn as composed — a latent bug the grammar exposed), dotted
free-interface wires, and `kindShape` so a folded leaf keeps its kind.
Deferred with reasons: indexed families (no family object — `par` is
binary) and hybrid sequences (one theorem yields one relation).
DESIGN amended on five implementer objections, incl. item 11(a) restated
as PORT-LADDER SYMMETRY (the old "centre of every box it touches" is
contradicted by item 14's off-centre ports) and items 18/23's stroke
collision resolved to a corner badge.  Gallery 37 cases / 39 diagrams,
0 violations, 204 port checks, 4 multi-port ladders.

**D3 SHIPPED** (`d48df68`, `Jost/SurfaceMoves.lean`): `#cc_moves` lists
the moves applicable at a node; `#cc_rewrite t with [lift, merge, …]`
emits the rewritten term AND a `calc` chain citing one lemma per step —
an equational proof authored by pointing at a diagram.  Moves: `lift`
(`word_smul`), `merge` (`mul_smul`), `drop_id` (`one_smul`), `commute`
(`attachAt_comm` / `block_smul_of_ne` / `smul_comm_of_ne`), `drop_idle`
(`attachAt_of_not_provides`).  Applicability decided by the TERM
(`isDefEq`, `mkDecideProof` — no `native_decide`); depth transported by
`mkCongrArg`.  The composite is checked by `Lean.Kernel.check` INSIDE
the command, metavariables refused; a mutation returning the unswapped
term is kernel-rejected.  Four theorems pasted verbatim from the
Try-this output compile, `#print axioms` pinned at the standard three.

Three findings from D3 that are about the MATHEMATICS, not the tooling:
* `par_comm` is FALSE here as a plain `=` — `(R ∥ Q).layoutAt i =
  .sum (R.layoutAt i) (Q.layoutAt i)` and `SumService.sum` is injective,
  so the two systems provide different services.  The padding-ledger
  item is now a named missing lemma: a swap-recoding transport.
* The demo carrier is DEGENERATE and the matcher proves it: on
  `CarrierDemo`, `dec^B enc^A (KEY ∥ AUT)` offers `drop_idle` at both
  depths, because a `∥` stack provides `.sum plain plain` ≠ `mask`'s
  source.  Both converters are attachment-identities.  This is the hole
  `Converter.par` + `attachAt_par` would fill.
* `⊣` is NOT an element of the converter monoid (its converter is
  layout-dependent), which is the single root of three unimplemented
  moves.  If blocking should participate in the algebra it wants a
  service-agnostic `⊥ ∈ Σ`, not the indexed family.

**D4–D5 remain**: the interactive panel (hover-to-select, move menu,
calc rail) and the ε-rail.  D3 flags that its `Nat` depth addressing
should become the PATH that hover-to-select naturally yields, and that
`merge` should compose with a D1 view directive so the merged pill
re-labels as `enc∘enc` instead of `word * word`.

**Parked — structure graphs are NOT a CC diagram** (Marc, 2026-08-06):
the BPR05/BDPV08 structure-graph vocabulary was surveyed and then REMOVED
from DESIGN §12.  A collision graph's nodes are not systems and its edges
are not interfaces; it is a combinatorial proof artifact needing a
graph-layout renderer, not the box-and-wire composition language
`#cc_diagram` speaks.  If `CBCStructureGraph.lean` ever wants figures,
the survey is recoverable from git (`3d9b4cd`, reverted here): BPR05 is
internally inconsistent across three idioms; the root is NOT marked; bold
border = a caption-declared vertex SET (Fig 9's is the accident index
set I⁻, not rootedness); collapse is invisible (vertices absent, indices
gapped); accidents/collisions are never drawn — the count lives in the
caption; BPR05 indexes by TIME where BDPV08 indexes by PATH.

**Open (awaiting Marc)**: Penpot design round 2 (Jost pseudocode boxes +
MPC) is built and audited but its conventions are under revision — the
pseudocode-unfold LEADER is deleted (a wire denotes composition, so no
wire-like connector may join an object to a DESCRIPTION of it; the
replacement is a semantic-zoom lens, focus+context, anchored over its
object with the context dimmed).  A corpus-wide AC/CC/RS figure survey
is running to settle the n-party conventions — the earlier "the
literature has no multi-party wiring diagram" finding was an artifact of
a thesis-only brief (LiuMau20 and the other multi-party papers were
never opened; see the memory note on surveying the corpus, not one
source).

## CC diagram visual design pass (2026-08-06, V1–V3 complete)

Marc's directive: no overarching visual design, untested cases, labels
stretching layout — "start from an actual design, visually critique
against papers".  Executed as spec → implementation → closed-loop visual
critique:

- V1: DESIGN.md §12 — the visual design system (fixed-grid geometry,
  label budgets w/ middle-ellipsis + title attr, interface geography,
  dashed = specification boundary, role palette with non-color twins,
  figure pairs for equations, 12-class visual corpus).  Amended after
  critique with items 9–11: wiring rules (fan-out bus to every stacked
  resource, protruding party crossings, no floating boxes, horizontal
  same-interface chains, no dangling endpoints), the rendering-medium
  decision (Marc: diagrams are DYNAMIC HTML OBJECTS, no SVG; precision
  is emitter-owned — absolutely-positioned divs at Lean-computed px on
  an orthogonal grid; flexbox banned inside diagrams), and the
  machine-checked geometry gate.
- V2 (`SurfaceWidgets.lean` renderer v4 + `SurfaceGallery.lean`): pure
  Lean layout engine (`Prim` box/hwire/vwire/tag) emitting positioned
  divs; 23-case corpus gallery + `Html → String` serializer +
  `#cc_gallery` writing `.lake/cc_gallery.html` on every build; embedded
  vanilla-JS geometry self-audit (`<pre id="geometry-audit">`: every
  wire endpoint on a box perimeter/bus within 0.75px, no clipped
  labels).
- V3 (closed loop, headless Chrome): render → audit JSON → zoomed
  screenshot critique vs MaRuTa12 Fig 1 / Maurer11 Figs 3–4 / Jost
  Figs 2.1–2.4 → fix round → re-render.  Two rounds to golden: round 1
  killed the five geometry defects (KEY floating unwired, no party
  crossings, floating bare resources, vertical same-interface stacks
  with dangling stubs, `enc^a … AUT)` unbalanced collapse label);
  round 2 pruned interface tags to exactly one per interface at the
  outermost crossing.  Final: **0 violations over 25 diagrams / 64
  boxes / 120 wires / 53 labels**, Fig-1 target visually matches the
  paper; audit unchanged at 59 clean / 5 bridges / 4 demoted;
  `SurfaceGallery` import compile-gates the corpus in the umbrella.

Tooling note: Penpot's hosted MCP registered at local scope (healthy,
`✔ Connected`); tools become available in the NEXT session (tool surface
is fixed per session and inherited by subagents — verified empirically).
Planned use: CC design-system file in Penpot, design tokens synced back
into the emitter constants; figures stay Lean-compiled.

Penpot design system LIVE + first sync (2026-08-06 afternoon): file holds
the `cc-diagram` token set (22 tokens = the §12 constants), 12 components
(masters are fixed-size flex boards with a nested auto-hugging `Label`
component — Marc-confirmed centered on canvas after the stale-context
incident; channel glyphs are DRAWN vectors, not font glyphs), and the
Fig-1 mockup rebuilt from component instances (24/24 wire endpoints
audit-clean).  First token sync applied to `SurfaceWidgets.lean`:
JetBrains Mono font stack, game `#6b7280`, boundary `#888888`, tag 11px,
boundary pad (12,14), double border 1px/−4px inset per the master.
Gallery regenerated: 0 violations / 25 diagrams.  Session traps (stale
plugin context = 1×1 text layout; export renders server state vs client
context; canvas is arbiter) recorded in memory `penpot-cc-design-system`.

## The Maurer pass (2026-08-06, M1–M5, gates A–C: 236fbcd, feec196, cb79a3a)

The design criterion "what would Maurer have wanted" (minimality +
usability; grounded in visual reads of Maurer11 pp. 40–47, MauRen16
pp. 3–8, MaRuTa12 pp. 2–7, JosMau20 pp. 4–9), executed as gated waves:

- M1 `SurfaceCarrier`: `ResourceSystem` on the bundled heterogeneous
  carrier — attachment `α •[i] R` TOTAL (identity on mismatch, §10.9's
  contract), Prop 2.2.3 a bare `=`, `≈[ε]` with `≈[0] ↔ =` (Maurer's ≡ IS
  our =), eq. (3)/(4) as `close_par`/`close_attachAt`; coherence receipt
  to the layout-indexed layer.
- M2 `SurfaceAlgebra`: Def 1 completed — `Σ` at an interface IS the
  kernel converter monoid (`id•R=R` = `one_smul`, `∘` = `mul_smul`, word
  embedding coheres with `•[i]` by rfl); NEW: `⊣[i]` blocking with
  type-level unqueryability, MaRuTa12 Def-2 two-condition `Constructs` +
  Thm-1 sequential composition, `Protocol` + `smul_perm` (JosMau20
  Prop 1).  `ψ‖φ` typed law honestly scoped (obligation stated).
- M3a `SurfaceChannels` + display consumption: the channel calculus
  (`—→ •—→ —→• •—→• •══•` per MaRuTa12 §1.3, reusing authChan/secChan);
  `cc_display` names render in goals/diagrams; Maurer11 role palette.
- M3b: grammar reservation-free (only `resource`/`converter` command
  heads reserved; certified from an importer), display/latex/role
  clauses, doc-comments.
- M4: the linter ENFORCES the Maurer standard (HEq/Function.update/edist
  = violations; demoted-with-successor ledger, third audit counter);
  `Realization.presents` closed the toDDS vocabulary gap; audit
  59 clean / 5 bridges / 4 demoted.
- M5: Fig-1 dashed-box diagrams (simulator below, adversary wire);
  `#cc_latex` paper-equation export from checked terms (glyphs,
  superscripts, `\equiv`); `#simulate`'s `on` de-reserved.

Open ledger: heterogeneous key-beside-channel `∥` (padding quotient
transport — now the top want, it blocks MaRuTa12 Fig 1 verbatim); typed
`ψ‖φ` law; full §2.2.6 in-grammar re-render; machine_step attribute;
Protocol `•` LaTeX form.

## CC DSL push: grammar, tactics, linter, widgets (2026-08-05/06, waves 1–3b)

Design in the 2026-08-05 session transcript + `.claude/skills/cc-constructions`;
staged with validation gates, all committed (07dd9d0, 593f0e5, f591d28):

- `Jost/SurfaceLint.lean` — `@[cc_surface]`/`@[cc_surface_bridge]` +
  `#cc_surface_audit`; §10.11 is now a BUILD GATE (standing audit in
  `Jost.lean`: 25 statements clean, 6 bridges).  Open vocabulary gap it
  found: the coupling bridges' fibre hypotheses still show `Machine.toDDS`.
- `Jost/SurfaceTactics.lean` — `bisim_cases rel` (congruence + per-interface
  split + machine_step bundle with the measured trap discipline) and
  `couple using j`; counter refactor and coin coupling are ONE line each.
- `Jost/SurfaceBridge.lean` — rfl `Interfaces↪Services`; free-closure embed
  proven an isometry; `∥` on plain `Resource`s; padding scoped to
  machine+law (quotient transport = a padded analogue of TypedParallel's
  defining equation, stated in the docstring).
- `Jost/SurfaceGrammar.lean` — `cc_resource … where` (interface/input/state/
  on/sample/require/reject) elaborating to pure `ofState`/`sampleInit`;
  autoparams killed the normalization plumbing (zero call-site fixes);
  `Dist.forall_support_fTransform` + pre-substituted coupling bridge.
  **PENDING Marc's veto: reserved keywords vs indentation combinators.**
- `Jost/SurfaceDelab.lean` — goal display in surface vocabulary
  (`Resource F`, `sampleInit`, `i ! x`), toggleable, guard-pinned.
- `Jost/SurfaceWidgets.lean` — `#simulate` (computable step, ⊥-blocking
  shown live) and `#cc_diagram` (ASCII pinned + ProofWidgets HTML panel).

Veto resolved (ship v1, rework queued).  W3a landed (9b00e73):
`cc_converter` with the Def-2.2.2 judgment SYNTHESIZED — arity-indexed
`RoundN` scripts make the discipline structural, one generic
`step_inl_iff` + packaged `Converter.ofScript`, zero bespoke proof
obligations, axiom-clean; π_A re-authored as the two-call receipt;
`cc_resource` now emits `Name.machine`.  Gate-3 receipts: F2/F3/F4/F5
PASS (tactics-shrunk leaves; linter as build gate; diagrams post
React-#62 fix; three domain-language staged errors); F1 demonstrated on
representative shapes — the FULL in-grammar §2.2.6 re-render is queued,
not claimed.  Polish queue (task ledger): reservation-free grammar
(the `input` token bit the converter module's own binders — concrete
motivation), Function.update display sugar, `!x` spacing, a surface
name for the toDDS fibre hypotheses, machine_step as real attribute,
padding quotient transport, full §2.2.6 in-grammar.

## CC authoring surface over the contextual quotient (2026-08-04, second round)

`RandomSystems/Jost/Surface*.lean` + `SecureChannel.lean`: thesis-vocabulary
surface (audit verdict + layer map in `RandomSystems/Jost.lean` and
`sketches/jost-2-2-6.md`).  `Resource F` = the existing contextual quotient,
so plain `=` is behavioral identity; constructors `ofState`/`sampleInit`;
`Services`/`Converter.ofRounds`/`ResourceAt.attach` (+ non-expansion +
quotient-level `attach_comm` = Prop 2.2.3); `∥` over `TypedParallel` via the
free sum-closure `Services.free` (+ Maurer11 eq. (3) re-export);
Prop 2.2.17 restated at the quotient (`CC.SecureChannel.construction`),
leaves reused from the machine-level bisimulations.  Machine combinators
demoted to family-authoring devices (no coherence receipt owed by shipped
statements).  Kernel names confined to bodies plus one marked bridge
section (§10.11 discipline).  All surface theorems axiom-clean.
Unblocking repairs to the in-flight dist-real migration landed in
`RandomSystemQuotient`, `StrictRelabel`, `RandomSystemParallel`,
`StrictParallel` (mixture block rewritten for ℝ masses), `TypedParallel`;
`delta_eq_zero_iff_le` gained its Def-2.4 `NonNeg` side condition.
The OTP demonstrator is COMPLETE (`Jost/OTP.lean`, 2026-08-04):
`otp_real_eq_ideal` — a resource identity that is NOT a law equality
(disjoint supports; coupling provably cannot close it), proved via the
four-worlds transcript invariant `otp_transcript` and
`strict_equivalent_of_equivalent`, entering the surface through
`sampleInit_eq_of_flatten_equivalent`; axiom-clean, zero sorries.
Migration candidates minted there: `flatten_output_concat`,
`output_fullyDefined_of_total`.

## Jost §2.2.6 at the package level — pseudocode DSL integration test (complete, 2026-08-04)

`RandomSystems/Jost/` reproduces the thesis's worked example (Prop. 2.2.17,
confidential channel from `[AuthChan, Key]` via symmetric encryption) entirely
at the `Machine` level; layer map and scope boundaries in the module docstring
of `RandomSystems/Jost.lean`, sketch + routing in `sketches/jost-2-2-6.md`.
All headline declarations axiom-clean, zero sorries.

- New DSL infrastructure: `Machine.par` and `Prog`/`Converter.attach` (the
  `call` keyword) in `Jost/Combinators.lean`; `Dist.fTransform_congr`,
  `Dist.fTransform_eq_of_coupling`, `Machine.lawOf_congr`,
  `Machine.lawOf_eq_of_coupling` in `Jost/LawCoupling.lean` (the "couple on
  the key, compare transcripts" principle; per-fibre discharge is
  `toDDS_eq_of_bisim`).
- Both Prop.-2.2.17 leaves proved as LAW EQUALITIES (family I) under the
  identity coupling of the `(key, tape)` seed; `dec_enc` consumed exactly
  once (Bob's clause of leaf 1).  Headline `construction`: every functional
  Φ of (real, ideal) equals Φ of (`c CPA_0`, `c CPA_1`) — the ε(D) transport
  with zero metric slack.
- Deferred bridge receipt (documented, not claimed): machine-level
  `par`/`attach` vs PFun-layer attachment.
- Completed 2026-08-04 (second pass): bad-set Δ-face
  `Machine.lawOf_lawStatDist_le_of_coupling` (via new
  `HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne`) — the
  package-level conditional-equivalence entry point; general lemmas migrated
  in place (`Dist.fTransform_congr`, `Dist.fTransform_eq_of_coupling`,
  `Dist.mass_mono_on_support` → `Dist.lean`; `logLookup_map` →
  `JostFigure22`).

## XOR SoP complement regime: full-deck tail closed (2026-08-04)

`RandomSystems/SoP/XORComplement.lean` now compiles the exact full-deck core
needed to investigate every query depth above `N/2`.  It proves that the
zero-XOR checksum density is normalized and has exact distance `1 - 1/N`
from uniform.  It also defines the checksum-conditioned collision proxy and
proves pointwise nonnegativity, total mass one, and the same exact full-deck
distance for `N = 2^n`, `n >= 2`.

The signed-representative quotient has been pushed into the exact Fourier
algebra.  Adding one character to every row changes a full-injection
coefficient only by a sign, so its square, and hence the exact two-permutation
convolution coefficient, is invariant.  Constant checksum modes and every
global translate of a pair-collision mode can therefore be removed together
before taking an `L1` or `L2` norm.  The supporting orthogonality calculation
also proves that checksum conditioning leaves the centered collision kernel's
mean equal to zero.  The exact convolution and its signed residual are
supported on the checksum slice, of uniform probability `1/N`; the compiled
support-aware Cauchy theorem converts full residual energy `E` to half-`L1`
at most `sqrt(E/N)/2`.

`XORComplementSpectrum.lean`, `XORComplementMultiplicity.lean`, and
`XORComplementSparse.lean` now carry this further.  The residual energy is
exactly an anchored injection fourth moment, translated pair modes are deleted
with no loss, and profiles with a row value occurring more than `3N/4` times
are bounded by the explicit level-three term plus `(580/3)/N^2`.

`XORComplementProfiles.lean` compiles the remaining profile bookkeeping: row
permutation and global-shift invariance, the exact factor `N` between full and
anchored sums, and exact vanishing whenever the XOR of the mask rows is
nonzero.  Its finite Walsh second-moment identity gives every separated
profile a hyperplane cut with

```text
N^2 <= 16*m*(N-m).
```

`XORComplementSquareRoot.lean` and `XORComplementEntropy.lean` now close the
two estimates which were previously only source obligations.  The first file
uses a finite torus, exact histogram/permutation double counting, and a sharp
multinomial-mode inequality to prove the per-profile square-root estimate

```text
countPerms(s) * coefficient(s)^2
  <= choose(N + support(s) - 1, support(s) - 1).
```

The second file aggregates this exact envelope without asymptotic notation.
It quarter-splits every separated histogram, lower-bounds its multinomial
orbit, counts profiles by support, and sums the resulting eighth-power
exponential series.  For `n >= 63`, `N = 2^n`, the compiled endpoints are

```text
highEntropyProfileCubicEnvelope <= 2*N^2 / 3^(N/16) <= 1/N
separatedAnchoredCubicMass      <= 1/N^2
fullResidualAdvantage           <= 7/N.
```

The focused gates for `XORComplementEntropy`, `XORComplementMarginal`, and
`XORComplementBoundary` pass.  The endpoints have no admissions or custom
axioms; their only reported axioms are the standard quotient/classical/
propositional-extensionality axioms used by the finite library.

`XORComplementMarginal.lean` now closes the signed marginal bridge.  It proves
by zero-padding Walsh masks that, whenever `N-q >= 3`, marginalizing the full
checksum-conditioned proxy gives exactly the ordinary collision proxy.  The
full signed residual therefore marginalizes exactly to the visible
`remainderDensity`, and finite signed data processing gives the compiled
operational endpoint

```text
|adaptiveAdvantage(q,N) - collisionAdvantage(q,N)| <= 7/N,
    n >= 63, q <= N, N-q >= 3.
```

`XORComplementBoundary.lean` closes the final two strict-prefix cases.  With
two hidden rows, the extra centered-checksum correction has exact half-`L1`
cost `1/(N*(N-1))`.  With one hidden row, the extra co-singleton Walsh modes
have half-`L1` cost at most `1/(2*(N-1))`.  The unified compiled endpoint is

```text
|adaptiveAdvantage(q,N) - collisionAdvantage(q,N)|
  <= 7/N + 1/(2*(N-1))
  <= 8/N,                         n >= 63, q < N.
```

This now covers every pre-saturation query depth, including all points above
`N/2`.  The same module defines `preSaturationRemainderBound`: below half the
deck it retains the minimum of this complement estimate and the sharper
existing sparse Fourier remainder; above half it uses the complement
estimate.  The concrete collision-threshold distinguisher is formally within
twice that best certified residual of the optimal adaptive advantage.  At
`q=N`, the already-formal checksum attack gives the separate saturation
behavior `1-1/N`.

## Signed/virtual PDS norm layer (compiled and exact, 2026-08-03)

`RandomSystems/VirtualPDS.lean` now packages the general linear extension that
was previously only in `sketches/signed-virtual-pds.md`.  No duplicate carrier
was introduced: current source already defines `Dist A = A →₀ ℝ`, so raw
`PFunPDS` is the virtual carrier and `Dist.NonNeg` marks the honest cone.

The module proves:

```text
virtualL1(push f mu) <= virtualL1(mu)

Adv(S,T) <= 1/2 * virtualL1(S' - T')
```

whenever `S'` and `T'` have the same transcript pushforwards as honest,
equal-weight `S` and `T`.  It defines the infimum over all signed equivalent
representatives and proves that the infimum equals `Adv` whenever an honest
equivalent pair attains `Adv`.  The signed-`Real` migration of
`BoundedAttainment.lean` is now complete, including explicit nonnegativity of
the source laws and the attaining representatives.  Consequently
`virtualClassDistance_eq_advantage_of_finite_common_domain_and_bounded` is the
unconditional source theorem: for finite query alphabets, a common support
domain, and a uniform query bound, the signed representative infimum is
exactly operational advantage.  Its bundled probability-system form is also
exported.

`RandomSystems/SoP/XORVirtualRepresentative.lean` instantiates the norm layer
on fixed visible XOR tapes.  It packages the exact likelihood error, retained
Fourier truncation, and tail as signed `Dist` values; proves the exact vector
identity

```text
exact error = retained error + tail;
```

identifies all three old half-uniform-`L1` quantities with the new generic
`virtualDistance`; proves that the retained visible representative has total
mass one; and restates the existing reverse-triangle theorem entirely as a
virtual-representative certificate.  This bridge is deliberately a fixed
visible-transcript representative, not a claim that the truncation alone is a
full PDS representative for every adaptive environment.

The focused source files and the `RandomSystems.VirtualPDS` target compile.
Axiom audits of pushforward contraction, operational soundness, unconditional
exactness, and the XOR bridge report only `propext`, `Classical.choice`, and
`Quot.sound`.

## XOR degree four, threshold test, and collision asymptotics (2026-08-03)

`SoP/XORSignedDegreeFour.lean` classifies the exact four-row Fourier
coefficient.  Besides the all-equal and two-pair cases, the all-distinct
coefficient is nonzero precisely on XOR affine parallelograms; this is the
first point where equality partitions alone stop determining the answer.  The
module retains level four and proves its certified tail bound is no larger
than the degree-three tail bound.

`SoP/XORCollisionThreshold.lean` gives a concrete Boolean distinguisher that
accepts exactly when the visible collision count exceeds its ideal mean.  Its
gap is the collision-proxy advantage plus the exact higher-order remainder on
that event, so the same explicit attack works on both sides of the birthday
transition.

`SoP/XORCollisionAsymptotics.lean` proves the exact analytic targets:

```text
Poisson MAD(lambda) = 2*lambda*Pr[Poisson(lambda)=floor(lambda)]
standard Gaussian MAD = sqrt(2/pi)
```

and factors the finite collision advantage into its dense scale times the
standardized collision MAD.  The former approximation placeholder is now
closed by three compiled modules:

- `SoP/CollisionStein.lean` proves the finite local-dependence Stein transfer;
- `SoP/CollisionSteinAnalytic.lean` constructs the absolute-value normal Stein
  certificate with target `sqrt(2/pi)`;
- `SoP/CollisionCountNormal.lean` counts all local terms, including the signed
  triangle cancellation, and proves the explicit finite error
  `(sqrt(2/pi) + 2 + 20*q/N)/sigma`, together with normal convergence whenever
  `N` and the collision-count standard deviation tend to infinity.

`SoP/CollisionCountPoisson.lean` supplies the sparse and birthday side.  It
proves the exact identity `MAD = 2*lambda*Pr[K=0]` below collision rate one,
identifies `Pr[K=0]` with the birthday product, proves its elementary Poisson
limit, and obtains the sharp sparse ratio.  This covers every limiting rate
strictly below one, in particular `q ~ sqrt(N)` with rate `1/2`.  It also
proves the dense proxy ratio tends to `sqrt(2/pi)` and the resulting leading
constant is `1/(2*sqrt(pi))`.

`SoP/CollisionCountPoissonFixed.lean` now closes the complete fixed-rate
interpolation, including every rate at or above one, without importing an
external Poisson approximation theorem.  Planting one collision edge gives
the exact size-biased collision law.  Its effect differs from adding one
collision only through edges touching a planted endpoint, yielding an
atomwise approximate Poisson recurrence.  Induction from the exact birthday
zero atom proves convergence of every fixed collision-count atom.  A finite
lower-tail identity at `floor(lambda)` then gives

```text
N * finite collision-proxy advantage
  -> lambda * Pr[Poisson(lambda) = floor(lambda)]
```

for every fixed nonnegative `lambda`.

`collision_advantage_eq_birthday_collision_target` in
`SoP/XORCollisionAsymptotics.lean` identifies that finite birthday formula
with the collision proxy used in the SoP development, and
`abs_advantage_sub_birthday_collision_target_le` transfers it to the true
adaptive advantage with exactly `remainderErrorBound`.

Finally,
`abs_advantage_sub_normal_collision_target_le_finiteStein` in
`SoP/XORCollisionAsymptotics.lean` connects the explicit finite Stein error to
the true adaptive SoP advantage, adding only `remainderErrorBound`.  The
same module proves that `N * remainderErrorBound` tends to zero in every fixed
birthday-rate window.  Consequently
`tendsto_card_mul_adaptiveTranscriptAdvantage_fixedPoisson` transfers the
displayed constant to the true adaptive XOR SoP advantage, while
`tendsto_card_mul_collisionThresholdTestGap_fixedPoisson` proves that the
explicit centered-collision threshold test attains it.  For every positive
fixed rate,
`tendsto_collisionThresholdTestGap_div_adaptiveAdvantage_fixedPoisson`
strengthens this to the literal ratio `attack gap / optimal advantage -> 1`.
Thus the sharp asymptotic and matching attack are both formal at every fixed
positive rate (in particular every rate at or above one).  At rate zero the
scaled quantities both tend to zero, which is not by itself a matching-order
claim.  The focused modules, targeted builds, and endpoint axiom audits pass.

## XOR SoP signed degree-three improvement (complete, 2026-08-03)

`RandomSystems.SoP.XORSignedDegreeThree` now formalizes the first strictly
cancellation-aware member of the signed-truncation hierarchy.  Instead of
taking the absolute value of the degree-two collision proxy and charging the
whole degree-three layer afterward, it combines levels two and three
pointwise first.  In the transparent sparse range

```text
10 <= n,
2 <= q,
2*q <= N,
2*choose(q,2) <= N,
N = 2^n,
```

the combined density is negative exactly on collision-free tapes and
nonnegative on tapes with a collision.  Its half-L1 norm is therefore exactly

```text
(N)_q / N^q *
  (choose(q,2)/(N-1)^2
    - 8*choose(q,3)/((N-1)^2*(N-2)^2)).
```

The terminal operational theorem
`adaptive_transcript_advantage_le_signed_degree_three_main_add_error_sparse` adds
only `signedDegreeThreeError n q` (exactly `signedTailErrorBound n q 4`), the
certified level-four-and-higher tail:

```text
1/2 * sqrt((1152/7)*q^4/N^6 + 8*q^4/N^8).
```

`SoP/SignedLocalRepair.lean` packages this calculation as an especially
simple representative proof.  Averaging one coordinate over all recolorings
is a local mass repair; subtracting that average has total mass zero.  Keeping
the pair and triple repair cores produces the density
`1 + signedTruncationDensity n q 4`, and the sparse sign lemma proves this
density is nonnegative and normalized.  Its exact distance from uniform is
the displayed main term.

`abs_advantage_sub_signed_degree_three_main_le_error_sparse` proves the matching
two-sided statement: the absolute difference between the true adaptive
advantage and the displayed main term is at most that same tail.

The comparison with the previous collision-proxy/gain-graph endpoint is also
formal, not merely numerical.  Throughout the same range,
`signed_degree_three_bound_le_min_sparse_dense_add_remainder_sparse` proves

```text
new main + new tail
  <= min(old sparse branch, old dense branch) + old remainder.
```

For `3 <= q`,
`signed_degree_three_bound_lt_min_sparse_dense_add_remainder_sparse` proves the
inequality is strict.  The dense-branch comparison uses the new elementary
finite estimate

```text
(N)_q / N^q <= N / (N + choose(q,2)).
```

Thus the signed representative is never worse over its complete proved range
and is genuinely smaller as soon as triples exist, rather than merely giving a
different proof of the old formula.

`RandomSystems.SoP.XORCollisionAttack` now packages the matching elementary
attack.  It makes a fixed fresh query schedule and returns `real` exactly when
the visible answer tuple is non-injective.  Lean identifies its signed
acceptance gap with the corresponding real-minus-ideal event mass and proves

```text
Main - Error <= collision-test gap <= adaptive advantage,
|collision-test gap - Main| <= Error.
```

Hence the leading term is witnessed by a concrete nonadaptive distinguisher;
it is not only an upper-bound artifact.

The proof is elementary after the exact three-row character cancellation.  A
closed three-row card evaluates to `2` when its three visible answers are
distinct, `-(N-2)` when exactly one pair agrees, and `(N-1)(N-2)` when all
three agree.  This gives the collision-free value and a uniform lower bound;
the two sparse inequalities above settle the sign.  Centering then turns the
half-L1 norm into collision-free probability times one constant.  No mirror
theory or conditioning argument is used.

The module also exposes the more general theorem with the two exact finite
sign inequalities as hypotheses.  The new lane contains no `sorry`, `admit`,
declared axiom, `sorryAx`, or `native_decide`, and its focused source compile
is clean.  `RandomSystemsApplications.lean` imports the terminal module.

## XOR SoP gain-graph/collision-proxy theorem (complete, 2026-08-03)

The representative-first broken-cycle proof for the XOR of two independent
uniform permutations is complete.  For `N = 2^n`, `10 <= n`, `2 <= q`, and
`2*q <= N`,
`RandomSystems.SoP.XORGainGraph.adaptiveTranscriptAdvantage_le_explicit_gainGraph`
proves the minimum of the exact sparse collision term and dense square-root
term, plus a certified higher-level remainder.  The tight squared remainder is

```text
16 * choose(q,3) / ((N-1)^3 * (N-2)^3)
  + (1152/7) * q^4/N^6
  + 8 * q^4/N^8.
```

The companion rounded theorem retains the simpler `200` and `16` constants.
`SoP/GainGraphCancellation.lean` now proves the generic finite
Dohmen--Trinks/Whitney least-pivot involution, specializes it to balanced
collision gain cycles, proves that the two-edge hidden/shifted cycle is
balanced exactly at a visible answer collision, and derives the exact
broken-circuit-restricted compatible-count formula.  `SoP/XORGainGraph.lean`
normalizes that graph sum, proves pointwise equality with the real SoP
likelihood, identifies the graph residual with the certified
level-three-and-higher remainder, and exposes the tight endpoint above.  The
last orthogonal core-pair estimate remains the finite Walsh/checkerboard proof;
the theorem is complete, while a spectral-free general gain-graph tail theorem
remains open.

The full lane consists of `SoP/XORCollisionProxy.lean`, `XORFourier.lean`,
`XORInjection.lean`, `XORCore.lean`, `XORTail.lean`, `XORCoefficient.lean`,
`XORPascal.lean`, `XORBounds.lean`, `GainGraphCancellation.lean`, and
`XORGainGraph.lean`, plus `XORSignedTruncation.lean` and
`XORSignedDegreeThree.lean`.  Each focused file compiles; the lane contains no `sorry`,
`admit`, declared axiom, `sorryAx`, or `native_decide`.  Axiom audits of the
evaluated graph formula, pair-cycle theorem, graph-residual energy bound, and
expanded endpoint report only `propext`, `Classical.choice`, and `Quot.sound`.
`RandomSystemsApplications.lean` imports the terminal gain-graph module.  The
focused endpoint and its generated olean pass against the repository's
compatible build cache.  The older SoP aggregate chain has now been migrated
through `Partition.lean`, `XoPModel.lean`, `XoPAnalytic.lean`, `SoP2.lean`, and
`SmallQ.lean`; every focused source/build check in that lane passes.  A clean
`RandomSystemsApplications` build proceeds beyond that chain and currently
stops in unrelated signed-carrier migrations in `HTechnique`, `Complexity`,
`BonehShoup`, and `SwitchingLemma`.  The new endpoints do not depend on those
modules.  Their `#print axioms` audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

The source audit and mathematical design remain recorded in
`sketches/signed-virtual-pds.md`.  The general half-`L1` contraction,
operational soundness, signed-class infimum, and unconditional finite/common-
domain/bounded exactness now live in `VirtualPDS.lean`; the fixed-visible XOR
instantiation lives in `XORVirtualRepresentative.lean`.  Ordinary probability,
conditioning, and coupling remain in the positive layer.

## Deterministic causal RS → AC completion program (complete, 2026-07-21)

Success means that one canonical import supplies the exact current indexed
AC contract for the full deterministic, stateful, typed `IsDDC` converter
class, with randomness carried by resources and with no `Emulable` or
`FrameCompatible` field in `Gamma`.  The selected semantics distinguishes a
committed rejection (an ordinary dependent output) from divergence
(`Part.none`, with no continuation); it does not expose CR18's transactional
`s ↦ s⊥` deletion/retry behavior at the AC boundary.

The implementation checklist was binding.  CBC, HCTR2, FROST, and historical
bridge modules were not used as evidence for completion: this receipt concerns
the generic RS carrier, converter family, action, metric, and AC/CC/CC.MPC
integration surface.

- [x] Land the strict contextual observation kernel over normalized PDSs:
  finite deterministic tests, acceptance mass, contextual equivalence,
  quotient, pseudo-emetric, and zero-kernel theorem.
- [x] Prove strict context absorption for every stateful `IsDDC`
  `ProtocolFn`, including distribution-level factorization, quotient
  congruence, and metric data processing.  Keep `probeFn` as the permanent
  regression proving that no `Emulable` restriction has slipped back in.
- [x] Make typed primitive `DeterministicConverter` exactly
  `ProtocolFn + IsDDC` and delete its `Emulable` field.  Keep identity and
  serial composition in the extensional AC converter monoid; do not introduce
  an unproved second raw typed monoid.
- [x] Define boundary-indexed typed experiments and contextual behavior over
  the native shared-state `DependentPDS` carrier.  Tests range over all finite
  converter contexts followed by a strict deterministic observation, so
  attachment closure is structural rather than an extra certificate.
- [x] Build the canonical all-interface frame for every stateful typed
  converter and prove that native attachment flattens exactly to strict
  framed application. Compile every finite typed experiment through that
  theorem and prove arbitrary-interface metric full abstraction.
- [x] Replace the old typed behavioral quotient and metric by that contextual
  quotient.  Use the existing dependent answer fibres; do not introduce one
  common output alphabet.
- [x] Lift arbitrary typed attachment through normalized laws and the new
  quotient; prove representative independence, metric non-expansion, and exact
  distinct-interface commutation.  Same-interface serial action is the
  extensional endomorphism multiplication used to define `Gamma`.
- [x] Make a primitive at interface `i` contain every typed deterministic
  `IsDDC` converter and no framed-compatibility field.  Its total action must
  update only boundary component `i` and remain stable under changes at other
  interfaces.
- [x] Rebuild `Gamma i` as the extensional generated submonoid of those local
  semantic actions, then install
  `[forall i, Monoid (Gamma i)]`,
  `[MulAction (forall i, Gamma i) Phi]`,
  `[PseudoEMetricSpace Phi]`, and
  `[IsNonexpandingSMul (forall i, Gamma i) Phi]`.
- [x] Provide ergonomic constructors for ordinary one-query functions and
  arbitrary history functions, and prove that semantic serial composition is
  exactly multiplication and AC action notation (right factor first).
- [x] Add generic gates for dependent signature change, two interfaces,
  hidden converter state, committed rejection followed by continuation,
  divergence after a successful internal call, `probeFn`, serial coherence,
  distinct-interface commutation, all four inferred AC instances, and a
  generic `Constructs`, ordinary-CC, and indexed `CC.MPC` receipt.
- [x] Remove the operational/metric split and its rejected converter-action
  renderings from the tree.  Keep observable `s⊥` and `Emulable` only where
  they state or test pure CR18 source semantics; neither is transitive through
  the selected `RandomSystemsCC` root.
- [x] Update `DESIGN.md`, the public roots, and the source/accounting audit;
  run the focused generic gates, `lake build RandomSystems`,
  `lake build RandomSystemsCC`, both H-technique gates, the surface audit,
  and admission/axiom/name audits.
- [x] Perform a requirement-by-requirement completion audit.  Do not mark the
  RS instantiation complete merely because the four typeclasses infer in an
  isolated homogeneous scratch model.

### Completion receipt

The selected `RandomSystemsCC` import satisfies each item in Section 9 of the
live AC library guide:

1. For every fixed boundary `sigma`, `DependentRandomSystem U sigma` is the
   normalized contextual-behavior quotient; `Resource I U` is the dependent
   sum of those fibres.
2. `Gamma I U i` is the extensional submonoid of non-expanding resource
   endomorphisms generated by every typed deterministic `IsDDC` primitive at
   interface `i`.  Raw programs with identical action are the same public
   converter, and the inherited monoid laws are exact.
3. The indexed tuple action is total.  A primitive attaches on its advertised
   source boundary and is the identity outside that domain.
4. `Primitive.act_of_matches` exposes the source-applicability premise and the
   resulting target boundary.  A concrete construction must discharge that
   premise; heterogeneous typing plus the mismatch branch is not treated as a
   substitute.
5. Fixed fibres and the heterogeneous carrier have contextual
   `PseudoEMetricSpace` instances, with zero distance iff quotient equality;
   unequal boundary vectors have infinite distance.
6. Every primitive action is non-expanding, closure stays inside
   `nonexpandingEnd`, and the indexed tuple action has
   `IsNonexpandingSMul`.
7. This instance makes no homogeneous `Par` claim.  Native typed routing and
   exact distinct-interface attachment commutation are proved because they
   are required to assemble the indexed action; optional AC parallel
   composition remains a separate mixin.
8. This is an information-theoretic instance and makes no computational
   feasibility claim, so no feasible subcarrier or cost-closure instance is
   advertised.

The completion gates passed and were revalidated after landing generic
all-interface framing on 2026-07-21: the combined `RandomSystems`,
`RandomSystemsCC`, and `RandomSystemsCC.TypedFiniteChecks` build (8,370 jobs),
both H-technique builds (8,315 and 8,336 jobs), and
`htechniqueSurfaceAudit`. The Lean LSP reports no errors in the framing,
metric, source-advantage, or CBC modules. The selected path contains no `sorry`, `admit`,
`sorryAx`, or declared axioms; its public endpoint axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The import audit finds one
production path and no rejected converter-action rendering, the theorem-leaf
name audit finds no uppercase declarations, and `git diff --check` passes.

The source audit was made from rendered PDFs: CR18 Definition 3.3 and
Definitions 3.8/3.13 establish the transactional partial-system semantics
that remain available for CR18 source theorems, while Maurer--Renner
Definitions 14 and 16 supply the converter/action/interchange obligations at
the composable-cryptography boundary.  The selected strict causal carrier is
an explicit model choice, not an attribution of blocking divergence to CR18.

Raw typed protocol composition may later receive a representation-coherence
theorem.  It is not part of the public converter identity: AC multiplication
is already exact semantic serial composition.  Paper-vocabulary renaming and
application bridges such as CBC are likewise subsequent consumers, not
missing instantiation obligations.

The broad paper-vocabulary rename (`PFun`, `ProtocolFn`, and theorem/function
names) is deliberately a subsequent migration.  It must not create a second
semantic layer or delay validation of this one.

## Current correction program (2026-07-21)

- The original CR18, Lanzenberger--Maurer, and thesis PDFs were checked at the
  cited definitions and proofs. `Equivalent` is the canonical transcript
  setoid, and `ObservableBehaviorEq` is its partial-system behavior
  characterization through the observable `s ↦ s⊥` view.
- The AC-boundary choice was checked again against rendered source pages, not
  inferred from extracted text.  CR18 PDF page 35 (Definition 3.3) explicitly
  gives invalid-input deletion and continuation; pages 37--38 (Definitions
  3.8 and 3.13) give general DDCs and attachment through `s⊥`.  Maurer--Renner
  PDF pages 13--14 (Definitions 14 and 16) require converter attachment,
  neutral/serial laws, distinct-interface commutation, equivalence congruence,
  and compatibility of the *distinguisher class*.  They do not require a
  per-converter `FrameCompatible` certificate.  The production strict causal
  carrier is therefore an intentional model extension, not a claim that CR18
  already uses blocking divergence.
- The unrestricted varying-domain class-distance/advantage equality is false.
  Its admitted endpoint and dependent coupling corollaries were removed from
  `RandomSystem.lean`; that module now builds without `sorry`. The replacement
  finite/common-domain/bounded attainment theorem and its normalized coupling
  corollary are complete as an independent RS theorem lane.
  `RandomSystems/AttainmentCounterexample.lean` is the permanent negative gate:
  for the normalized four-pattern partial pair it proves `Adv = 1/2`, every
  equivalent representative pair has static distance one, and the class
  distance is one.
- The rejected heterogeneous `RandomSystemsCC.DiscreteSystems` prototype, its
  admitted CBC-MAC bundled wrapper, and the sibling repository's four raw
  compatibility modules/targets were deleted. Thirteen empty historical bridge
  shells were also removed. The proved CBC-MAC RS/converter core remains and
  has only pure-RS dependencies.
- The transactional metric/action attempt has been superseded.  Its
  `Emulable` and `FrameCompatible` certificates were consequences of exposing
  `s ↦ s⊥` rejection-and-retry behavior at the AC boundary, not restrictions
  on deterministic converters in the mathematical AC model.
- `RandomSystems/StrictContext.lean` now supplies strict tests, exact context
  absorption, the normalized contextual quotient and pseudo-emetric, zero
  kernel, data processing, and exact serial coherence for every stateful
  `IsDDC` protocol. `Part.none` blocks the interaction; an explicit rejection
  is an ordinary proper output and remains in the causal history.
- `TypedResource.lean` retains the native dependent shared-state PDS carrier
  and tag-faithful flattening only. `TypedAttachment.lean` defines
  `DeterministicConverter` as exactly `ProtocolFn + IsDDC`, supplies
  one-query and arbitrary-history constructors, proves typed attachment and
  exact distinct-interface interchange, and contains no `Emulable` field.
- `TypedAction.lean` defines finite boundary-indexed experiments recursively
  from arbitrary typed attachment followed by a strict terminal test.  The
  resulting contextual quotient is closed under every deterministic
  converter by construction; its metric is non-expanding without a separate
  compatibility certificate.  The heterogeneous carrier has infinite
  distance only across different boundary vectors.
- `TypedFraming.lean` proves the previously missing arbitrary-interface
  coherence theorem for the full `ProtocolFn + IsDDC` converter class. Other
  interfaces pass through, selected-interface state is retained, and
  completion-level `none` cannot be followed by another successful event
  because of `AnswersInY`. `TypedFramingMetric.lean` then compiles every
  finite experiment to one strict test on the flattened global law and proves
  exact contextual/strict metric equality. Neither theorem assumes a finite
  interface type, total resources, or a converter subclass.
- `RandomSystemsCC/TypedFinite.lean` is the sole selected AC instance:
  `Phi := TypedResource.Resource I U`; each `Gamma i` is the extensional
  submonoid of `nonexpandingEnd Phi` generated by every local deterministic
  primitive; commuting inclusions install the exact indexed `MulAction` and
  `IsNonexpandingSMul`.  `Model` packages finiteness and decidable equality
  once so downstream statements do not repeat monoid/action/metric headers.
- `RandomSystemsCC/TypedFiniteChecks.lean` is the permanent adversarial gate.
  It uses a genuinely dependent `Fin 2` universe and checks all four AC
  instances, signature change, a history-sensitive query limit, a converter
  with hidden state, committed rejection followed by continuation, divergence
  after a successful inner answer, the formally non-`Emulable` `probeFn`,
  serial AC multiplication, distinct-interface commutation, and generic
  `Constructs`, ordinary-CC, and `CC.MPC` notation. The focused target builds.
- `RandomSystems/TypedUnitMetric.lean` proves full abstraction at every
  one-interface dependent boundary: arbitrary finite typed experiments
  compile to one strict local test and contextual distance equals strict
  local-view distance. `RandomSystemsCC/TypedUnitAdvantage.lean` then gives
  the source-facing bound by CR18 maximal advantage. The reverse equality is
  deliberately conditional: `StrictContextTotal.lean` proves it under
  support totality and records the rejected-query/continue counterexample to
  an unrestricted equality.
- `RandomSystemsCC/TypedFramingAdvantage.lean` generalizes the source-facing
  metric bridge to arbitrary dependent boundaries: normalized typed distance
  is bounded by CR18 maximal advantage on the flattened global laws, with the
  reverse equality stated only under support totality. The one-interface
  bridge remains available for strict-carrier applications.
- `RandomSystemsCC/ResourceLift.lean` is the source-facing CR18 rendering.
  Bundled DDCs compose and act directly with `*` on raw PDSs and heterogeneous
  resources; typed intermediate alphabets and the internal operational
  embedding are inferred.  A bundled DDC reassociates law application without
  exposing its `AnswersInY` projection.
  **SUPERSEDED 2026-07-25 (§11.3 C1) —** the paragraph above originally
  continued: "same-signature distance is definitionally `ENNReal.ofReal Δ`" and
  "the separate `CompatibleProtocol` submonoid requires `Emulable` and alone
  receives the global `IsNonexpandingSMul` instance."  Neither is true now.
  The fibre is the separated strict quotient `StrictContext.System`; `Δ`
  survives only as the sound `≤` (`edist_liftProb_le_advantage`), with no
  `edist = ofReal Δ` lemma; and `Protocol` — the whole `IsDDC` class — carries
  `IsNonexpandingSMul`, because absorption is structural on that quotient.  The
  compatible subclass is deleted.  The refusal to infer compatibility from
  Definition 3.8 alone still stands as mathematics
  (`not_emulable_probeFn`); it is simply a fact about `Δ` rather than a
  constraint on this carrier.  See DESIGN §10.10 for the full account.
- `RandomSystemsCC/CBC.lean` now uses that exact-`Δ` carrier.  It packages
  `theta_r`, CBC, and `[r]` as ordinary DDCs and displays their literal
  operational product `theta_r * CBC * [r]`.  `R` and `V_n` are named
  normalized PDSs, visibly cast to the CBC resource carrier only in the
  construction statement.  Equation (6.1) rewrites the typed product;
  `cr18_construct` then specializes the general
  `constructs_liftProb_of_advantage` boundary (one-way since C1) at the shared
  outer restriction, exposing the real-valued `Δ` goal without `Protocol`,
  `edist`, interface witnesses, or `ENNReal` plumbing.  The bundled
  `CBC R = cbcReal` equation leaves exactly the paper's MBO strip, Theorem
  4.17, collision bound, and birthday bound.  The former CBC-specific metric
  bridge and `congrArg` transport are deleted.  The focused modules elaborate
  at default heartbeats with no admissions.
- The rejected `ConverterAction`/`ConverterAlgebra`/`LocalizedConverter`,
  fixed-signature, typed-signature probe, exact-operational, and memoryless
  scratch renderings were deleted, as was their superseded standalone roadmap.
  There is one production RS-to-AC path. CBC and other applications are
  deliberately not used as evidence for completion of the generic instance.
- `RandomSystems/BoundedAttainment.lean` records the directly checked
  Lanzenberger--Maurer/thesis source boundary and completes the arbitrary-weight
  cross-query induction. It returns equivalent representatives with separate
  left/right masses and `δ = Adv`, then derives the class-distance equality.
  `RandomSystems/RandomSystemCoupling.lean` consumes that theorem only at the
  normalized boundary and returns a `Dist.ProbDist` joint with both marginals
  and disagreement probability `= Adv`. Focused and cumulative pure-RS builds,
  an independent PDF/statement review, dependency checks, and naming/admission/
  axiom audits pass; the public endpoints use only `propext`,
  `Classical.choice`, and `Quot.sound`.

## 1. Current state (2026-07-02)

- **Surface flip executed (Option B).**  The former `NextGen` tree is the
  main `RandomSystems` lib; the H-technique layer is promoted to
  `RandomSystems/HTechnique` (namespace `RandomSystems.HTechnique`); the
  pre-migration bounded API and applications live under
  `RandomSystems.Legacy.*` (module names only — declaration namespaces
  unchanged).
- **The selected roots build**: `lake build RandomSystems RandomSystemsCC`
  completed 8,348 jobs on 2026-07-20. The public roots deliberately exclude the
  broad historical `RandomSystemsLegacy` target and unfinished bridge modules.
  Three still-used foundational compatibility modules remain transitive through
  `Transcript` and the URP/URF instances; the rest of legacy is available only
  through the explicit target.
- **Converter realization + resource view landed** (2026-07-02, `DESIGN.md`
  §10): `StepConverter.lean` — `DDC.ofStep` (protocol converters as Def 3.8
  objects), realization theorem
  `apply_ofStep : (ofStep step) ·ᶜ S = CausalApply.applyG step S.1`
  (Def 3.9 = function composition; certifies the HCTR2 `CausalApply` surface),
  simple-converter recovery `simple_apply` (`(simple c d) S = map d ∘ S ∘
  map c`, domains included) and the interactive `feedback` examples; and
  `ResourceView.lean` — `fullyDefined_inj` (systems embed into their resource
  view `s⊥`), `unitResourceEquiv : DDS X Y ≃ Resource Unit X Y` (Def 3.5,
  single interface), law-level `PFunPDS.applyDDC` / `PFunPDC.apply`
  (Def 3.17) with mass preservation.  Both `sorry`-free.
- **Protocol-function layer landed** (2026-07-02, `DESIGN.md` §10.5–10.6):
  `ProtocolFn.lean` — the converter as a single history-function
  `ν : List U × List Y →. X ⊕ V` (no state carriers; the earlier σ-machine
  design was rejected as operational), its trace tree `Reach`, the identity
  discipline (`JunkFree`, `normalize` + stability/idempotence,
  `TraceEquiv`), the canonical Def 3.8 object `toDDC` with
  `toDDC_normalize`/`toDDC_congr`, and stress tests: closed-form trace
  trees for `simpleFn`/`queryLimitFn` (`[q]` as a round counter, breach
  pair reachable-and-undefined = Def 3.10), junk detection and
  junk-invisibility (`simpleFnJunk`: `¬JunkFree`, raw-distinct, yet
  `TraceEquiv` → same `toDDC`).  Stress testing caught a real junk bug in a
  first draft of `queryLimitFn`.  Event-algebra source (GegMau26,
  2026/1071) recorded in `DESIGN.md` §1/§10.6; Lean adoption scoped to
  DDC + applications only.
- **ν-realization + honest converter equations landed** (2026-07-02, second
  pass; `DESIGN.md` §10.5): `ProtocolRealization.lean` — transcript-equation
  driver `applyNu` and the ν-level realization theorem `apply_toDDC :
  DDC.apply (toDDC ν) S = applyNu ν S.1` (arbitrary converters, cross-round
  memory included), with the `[q]` instance (`applyNu_queryLimitFn`,
  `apply_toDDC_queryLimitFn`, `queryLimit_apply_eq_toDDC` — the two `[q]`
  representatives are apply-equal; bespoke trace proofs retire as
  instances); `CascadeRealization.lean` — the honest cascade equation
  `apply_cascadeStep : DDC.apply (ofStep cascadeStep) (cascadeAccess S T)
  = S ⊲ₚ T` (CR18 Def 3.11 via Def 3.9, replacing the vacuous `rfl`).
  Both `sorry`-free.
- **Converter DPI landed** (2026-07-02, third pass; `DESIGN.md` §10.7):
  `AbsorbDPI.lean` — the absorbed distinguisher `absorb d step : DDD X Y`
  (choice-based replay, `StopFinal` unconditional), the verdict
  correspondence `verdict_absorb_iff : verdict (absorb d step) s ↔
  verdict d (applyG step s.1)` (joint-run bisimulation `AbsRun`, both
  Def 3.7 transcript alignments), the law-level lift `verdictProb_absorb` /
  `advantage_absorb` (winProb pushforward transports), and the endpoint
  **`maxAdvantage_applyDDC_le : Δ(applyDDC (ofStep step) S, applyDDC
  (ofStep step) T) ≤ Δ(S, T)`** — converters are 1-Lipschitz for
  distinguishing advantage.  Hypotheses: Def 3.8 round bound +
  `TotalOnNonempty` (resource view), both necessary.  `sorry`-free.
- **Converter algebra completion** (2026-07-03, fourth pass): `StepConverter.lean`
  gains the monoid-action laws `simple_id_id_apply : simple id id ·ᶜ S = S`
  (unit) and `simple_simple_apply : simple c' d' ·ᶜ (simple c d ·ᶜ S) =
  simple (c ∘ c') (d' ∘ d) ·ᶜ S` (memoryless action law, five tactic lines
  from `simple_apply`).  `CombineRealization.lean` — the honest CR18 Def 3.12
  equation `apply_combineStep : DDC.apply (ofStep (combineStep op))
  [Combine.pair S T]ₚ = S ⋆ₚ[op] T` (arity-2 rounds against the parallel
  access system; mirrors `CascadeRealization`), with the `rfl`-by-definition
  `cascadeViaConverter_eq_cascade`/`combineViaConverter_eq_combine` docstrings
  now pointing at the honest equations.  `ProtocolRealization.lean` gains
  `toNu` (a DDC read back as a protocol function via its canonical trace
  `DDCTrace`) and the round-trip **`toNu_toDDC : toNu (toDDC ν) = normalize ν`**
  (+ `toNu_toDDC_of_junkFree`): the ν-world is exactly the junk-free quotient
  of the DDC-world, completing the §10.5 identity discipline.  All
  `sorry`-free.
- **Serial ν-composition landed** (2026-07-03, fifth pass;
  `ComposeRealization.lean`): the composite converter `compNu ν₂ ν₁` (flat
  replay `compGo` of the two-converter stack, fuel + `eventual`) and the
  **action law** `applyNu_compNu` / `apply_toDDC_compNu` — applying the
  serial composite equals composing the applications, *unconditionally*.
  Three-level joint-run `CompRun` with replay/reverse/extraction, middle
  certification (`compRun_middle`, `compRun_middle_value`), outer
  certification (`compRun_outer`), and both direction simulations.  With
  the unit law (`simple_id_id_apply`) and the identity discipline
  (`toNu_toDDC`), converters now form a monoid acting on systems — the
  ⟨Φ, Σ, ≈⟩ data of MauRen11 Def 14 at Level 2, ready for the
  ../abstract-crypto instantiation.  `sorry`-free.
- **Surface audit green**: `python3 RandomSystems/HTechnique/audit_surface.py`
  (or `lake run htechniqueSurfaceAudit`).
- The new surface (everything outside `Legacy/`) is `sorry`/`admit`/`axiom`-free.

## 2. Gates

| Gate | Command |
|---|---|
| Everything | `lake build RandomSystems` |
| H-technique surface (legacy-free) | `lake build RandomSystems.HTechnique.All` |
| Legacy gates + representative layer + pins | `lake build RandomSystems.HTechnique.LegacyChecks` |
| Surface audit (headers, imports, coverage, legacy-free `All`) | `lake run htechniqueSurfaceAudit` |
| Audit + surface build | `lake run htechniqueCheck` |

Anti-drift pins (must stay green until `Legacy` is deleted; a pin failure
means a refactor changed the mathematics):
`HTechnique/SoP/LegacyVisibleEquiv` (migrated SoP visible law = legacy
`Transcript`/`TV` objects, all `rfl`) and `HTechnique/SoP/XoPLegacyBridge`
(legacy adaptive XoP advantage = migrated `visibleStatDist`).

## 3. Public surface

Curated API: `HTechnique.Surface` = `SecurityDefs` + `SoPBoundary` +
`HashThenPRF` + `StrongPRP` (+ `Tactics` via `All`).  Canonical law-level
spellings (`ProbPDS`, `ProbPDE`, `TranscriptPrefix`, `FiniteTranscriptSpace`,
`DiscreteTranscriptSpace`) are owned by core `RandomSystems.CR18Names`.

Frozen source-facing endpoint names (application gate, frozen 2026-07-02):
`advPRF`, `advNPRF`, `advPRP`, `advNPRP`, `advSPRP`, `advTPRP`, `advTSPRP`,
`advNPRF_le_advPRF`, `advNPRP_le_advPRP`, `sop_prf_advantage`,
`sop_statDist_rfDist_le`, `sopFixedQueryAdvantage(_le)`, `sop_advPRF_le`,
`sop_filteredDelta_le`, `hashThenPRF_security`; single support alias
HashThenPRF `badPred`.  The old carriers (`sopDist`, `urfDist`, `rfDist`,
`sopFunctionDist`, `sopPDS`, `sop_ratio_lower_bound`) are support-only, **no
aliases** — reopening requires evidence of a concrete downstream caller.
Note (post-flip): endpoint names live directly in `RandomSystems.HTechnique`
(there is no inner `StrongPRP` namespace; e.g. `RandomSystems.HTechnique.advSPRP`).

## 4. Quarantine / legacy retirement map

`All` is legacy-free (audit-enforced).  Behind `LegacyChecks`:

| Module | Kind | Removal condition |
|---|---|---|
| `TranscriptLaw`, `FixedQuery`, `AdaptiveBridge`, `AdaptiveTranscriptAdvantage`, `SoP.CompressionLegacy`, `SoP.AdaptiveAdvantage` | representative layer | retire with `RandomSystems.Legacy` |
| `LegacyBoundary`, `LegacyBoundedTranscript`, `LegacyStatelessBridge`, `SoPLegacyBoundary` | legacy gates | retire when downstream callers finish migrating (Phase 6) |
| `FixedQueryCompatibility` | source-name sample-space wrappers | retire when no proof script uses `fixedQueryTranscriptDist_functionEvaluator` by source name |
| `SoP.LegacyVisibleEquiv`, `SoP.XoPLegacyBridge` | anti-drift pins | die with the `Legacy` tree itself |
| `Density`, `TranscriptLawPublic` aliases | source-name facades | retire at final H-technique deprecation |

Retired at the flip (deleted): the `AdaptiveLawBridge`/`FunctionEvaluator`/
`BoundedEnvironment` name shims.

## 5. Known gaps and parked files

Legacy sorries (**2** after the 2026-07-28 drop; pre-dating the migration;
tracked, not scheduled):

1. `Legacy/FundamentalTheorem.lean` — Theorem 1 (Δ = Adv) inductive step;
2. `Legacy/Amplification.lean` — amplification for general `k`.

*(The third, an adaptive cascade scaffold, went with the Boneh–Shoup cascade
files in the drop — see §11.25.)*

**`attic/` is deleted** (2026-07-28).  It sat outside every `lean_lib`, so
nothing ever built it, and its four files existed only to hold material
referencing the retired `Legacy/CR18/*` core — one of them never compiled at all,
carrying a genuine duplicate declaration across two imports.  The restore-or-delete
decision recorded here as pending is now decided: deleted.

### 5.1 `RV.law` ↔ constructor bridge (planned scaffold, 2026-07-09)

From the PDS "internal sampled randomness" survey. A PDS has two wired
presentations: the **law** form `PFunPDS X Y = Dist (DDS X Y)` (distribution
over deterministic systems, `PDS.lean:61`) and the **RV/coins** form
`PFunPDS.RV Ω X Y = Ω → DDS X Y` with ambient `p : ProbDist Ω`, the forgetful
map being `PFunPDS.RV.law p S := Dist.fTransform S p.val` (`PDS.lean:594`). `Ω`
is the internal randomness/key space; the keyed-function model (a PRF as
`F : Key → X → Y` + `keyDist`, `Complexity/PRF.lean:36`) is the RV form, and its
law is the distribution-over-functions view via `ofFunDist` (`PDS.lean:118`).

**The gap:** the RV→constructor identities are ad hoc — the *only* proven
`law = ofFunDist/pure/ofPermDist` instance is `urfRV_law` (`PDS.lean:1008`), and
the PRF `real = ofFunDist (…)` step is inlined inside `PRF.endpoints`
(`PRF.lean:99–103`) rather than named. There is no systematic bridge API.

The whole bridge is pushforward functoriality: `Dist.fTransform_comp`
(`Dist.lean:1391`) + `fTransform_id` (`Dist.lean:1401`), plus one genuinely
missing helper `fTransform_const`. Statements below type-check modulo `sorry`
(signatures verified against the live defs); each carries its closer. Not built
(documented here only, per the sorry-free default-glob convention); promote to
an isolated non-default `lean_lib` (RandomSystemsCC-style) when scheduled.

```lean
-- Prerequisite (missing from Dist.lean).  Closer: Finsupp.mapDomain of a
-- constant is `single b (X.sum fun _ w => w) = single b X.weight`.
theorem Dist.fTransform_const {A B : Type*} (b : B) (X : Dist A) :
    Dist.fTransform (fun _ => b) X = Finsupp.single b X.weight := by
  sorry

-- Bridge 1 — the general urfRV_law (subsumes PRF.lean:99–103).
-- Closer: both sides are `fTransform (functionEvaluator ∘ F) p.val`, fTransform_comp.
theorem PFunPDS.RV.law_functionEvaluatorRV {Ω : Type w}
    (p : Dist.ProbDist Ω) (F : Ω → (X → Y)) :
    PFunPDS.RV.law p (functionEvaluatorRV F)
      = PFunPDS.ofFunDist (Dist.fTransform F p.val) := by
  sorry

-- Bridge 2 — degenerate law = point mass.
-- Closer: fTransform_const + p.property (isProbDist ⇒ weight = 1) ⇒ single s 1 = pure s.
theorem PFunPDS.RV.law_const {Ω : Type w}
    (p : Dist.ProbDist Ω) (s : PFunDDS.DDS X Y) :
    PFunPDS.RV.law p (fun _ => s) = PFunPDS.pure s := by
  sorry

-- Bridge 3 — permutation form.
-- Closer: both sides `fTransform ((fun σ => functionEvaluator σ.toFun) ∘ Σ) p.val`, fTransform_comp.
theorem PFunPDS.RV.law_permEvaluatorRV {Ω : Type w}
    (p : Dist.ProbDist Ω) (Σ : Ω → Equiv.Perm X) :
    PFunPDS.RV.law p (fun ω => PFunDDS.functionEvaluator (Σ ω).toFun)
      = PFunPDS.ofPermDist X (Dist.fTransform Σ p.val) := by
  sorry

-- Bridge 4 — existing urfRV_law as a one-line corollary of Bridge 1.
-- Closer: urfRV = functionEvaluatorRV id; law_functionEvaluatorRV; fTransform_id.
example [Fintype (X → Y)] [Nonempty (X → Y)] :
    PFunPDS.RV.law uniformP (urfRV : PFunPDS.RV (X → Y) X Y) = PFunPDS.URF := by
  sorry

-- Bridge 5 — PRF real world = distribution-of-functions view, named (now inline
-- at PRF.lean:99–103).  Stated over Dist (no ProbDist), matching sub-distributions.
-- Closer: fTransform_comp on functionEvaluator ∘ F.
theorem PRF.real_eq_ofFunDist {Key : Type u} (F : Key → X → Y) (keyDist : Dist Key) :
    PRF.real F keyDist = PFunPDS.ofFunDist (Dist.fTransform F keyDist) := by
  sorry

-- Payoff — same induced function-law ⇒ behaviorally identical, across different
-- key spaces Ω, Ω'.  This is why the bridge matters: swap keyed ↔ distribution
-- inside any observable.  Closer: behaviorB_eq_of_law_eq (PDS.lean:878), its
-- PMF-equality hypothesis discharged by law_functionEvaluatorRV + h.  (Adapt the
-- hypothesis to behaviorB_eq_of_law_eq's exact PMF/law spelling.)
theorem behaviorB_eq_of_functionEvaluator_law_eq {Ω Ω' : Type w}
    (p : Dist.ProbDist Ω) (p' : Dist.ProbDist Ω')
    (F : Ω → X → Y) (G : Ω' → X → Y)
    (h : Dist.fTransform F p.val = Dist.fTransform G p'.val)
    (α : List X) (yᵢ : Part Y) (yprev : List (Part Y)) :
    behaviorB p (functionEvaluatorRV F) α yᵢ yprev
      = behaviorB p' (functionEvaluatorRV G) α yᵢ yprev := by
  sorry
```

## 6. Downstream / external (updated independently, per owner)

Import rename cheat-sheet for the external `fv/` workspace (declaration names
and namespaces are unchanged; only module paths moved):

- `import NextGen.Migration.HTechnique.X` → `import RandomSystems.HTechnique.X`
- `import NextGen.X` → `import RandomSystems.X`
- old bounded-API imports gain the `RandomSystems.Legacy.` prefix.

Per-project plan (from the frozen downstream audit): **ChaChaPoly** is a pure
re-export layer — repoint HashThenPRF names to `HTechnique.HashThenPRF`
(incl. `badPred`), `advNPRF/advPRF/advNPRP/advPRP` to `SecurityDefs`,
`advSPRP` to the law-level endpoint (callers adopt the concrete
`QueryDir × X` input shape).  **SequenceHash** `HTechniqueScaffold` is not a
name swap — restate on the CR18 law-level surface or park behind an explicit
legacy adapter.  **HCTR2** already has a law-level `advSPRP` cut and no
external `HTechnique.*` imports in its concrete proofs; next step there is
migrating its real systems to the `QueryDir × X` / `T × X` law-level input
shapes.  **/h-technique** gets thin aliases, then deprecation, after the
two callers move.  (The former `design/CR18_API_CHANGES.md` pin-marker
protocol for hctr2 is superseded by this section.)

## 7. Automation inventory (drained 2026-07-02)

All O-items from the pen-and-paper drive are drained or closed; the standing
rules live in `DESIGN.md` §4–5.  Residuals worth picking up opportunistically:

- benchmark `grind` on the switching-ratio/birthday family when touching it;
- sweep `cr18_total`/`htechnique_total`/`htechnique_adv_le` across remaining
  endpoint proofs as files are touched (only the demonstrator sites were
  converted);
- `CascadeCircle.lean:331`'s TODO can proceed (the shared
  `eval_nonces_uniform` it asks for now exists in general form);
- mass bundle (`cr18_mass_expand`/`cr18_sum_swap`/`cr18_ite_collapse`) and
  `@[grind =]` instrumentation landed (`DESIGN.md` §5.x); annotate new
  equation lemmas with `@[grind =]` at birth;
- v4.29 tactic radar surveyed and partially adopted — `grw`, `bound`,
  `grind only` minimization in use; `order`/`fun_induction`/`plausible`/
  `peel`/`lift` on the radar (`DESIGN.md` §5.y);
- protocol-converter automation (`DESIGN.md` §10.4): once a *third* protocol
  converter appears, collect the `run`-parser snoc lemmas and the
  `driveG`/`driveOuter` closed-form unfoldings into a `cr18_protocol` simp
  set, and absorb the `n + 1 + 1` fuel-literal idiom into a `driveG_unfold`
  tactic — not before.
- machine-bisim automation (2026-08-04, from `RandomSystems/Jost/`): the
  per-query case proofs all run the same simp bundle
  (`Converter.attach_step`, `Machine.runProg`, `Machine.par`, the concrete
  boxes, `Option.map`, `Option.bind`) then `injection`+`subst`+rebuild — on a
  *second* DSL construction proof, package it as a `machine_step` simp set /
  tactic.  Two traps it must encode: (a) simp's `Option.map_some` /
  `Option.some.injEq` do NOT fire when the `some`'s type ascriptions are
  defeq-but-not-syntactic (composite-machine `.State` projections vs reduced
  literals) — unfold `Option.map`/`Option.bind` instead and use `injection`,
  which matches at default transparency; (b) rcases/rintro `-` patterns clear
  every hypothesis DEPENDING on the dropped fvar — a `-` on a Unit state
  component silently deleted 4 of 6 bisim-relation components; name the
  variable instead.

### 7.1 HCTR2 M3.5 automation pass (2026-07-05)

Route-or-demote verdict on the HCTR2 attribute packs (method: strip every
attribute, full-file diagnostics + `lake build`, restore only what breaks):

- **Kept, firing sites cited**: `Dfull/Rfull_inr_zero/succ` `@[grind =]`
  (the two `grind` block-constraint sites in `hctr_real_ge` fail without
  them — verified by strip); `finTail_val` `@[simp]` (~18 omega/indicator
  sites across the DCell/RCell cover+count block); `capRank_inl_false/true`
  `@[simp]` (rank-order side goal in `rCell_card_hbarL`; their `grind =`
  halves dropped — no `grind` call exists after the cap packs).
- **Demoted to plain named lemmas (21)**: `hctrMsgL_card`, `getD_ofFn_fin`,
  `hctrPlain/hctrCipher_fwd/inv`, `Dfull/Rfull_inl_*`, `capRank_inr`,
  `capValid_inl/inr`, `DfullFix_*` ×4, `RfullFix_*` ×4.  All surviving uses
  are named `rw`/`simp only`; pack header comments rewritten to match
  (they claimed simp/grind sweeping that never fired).
- **Routed**: the two double-`rw` `*Fix_inr_zero` chains now go through
  conditional `simp only [<name>, hi, hj]`; the `_pos` (`≠ 0`) variants do
  not discharge their side condition conditionally — left as `rw`.
- **Estate sweep (adopted/rejected)**: `htechnique_fixed_query_pds` 0/2 —
  it unfolds `ProbPDS.fixedQueryTranscriptDist` but §LP sits at
  `PFunPDS.Prob` level (corrects §7b's claim that the estate "covers real
  hand-rolled rewriting in §LP"); the twice-pasted `show … from rfl` cast
  blocks were instead collapsed by `unfold lpUrf lpTweakableStrongURP` +
  the owner rewrite (18 → 6 lines).  `htechnique_mass_congr` 0/2 (in
  scope, but no shrink over `apply Dist.mass_congr`);
  `htechnique_dist`/`dist_simp` and `*_fixed_query_base/core`: no matching
  sites in HCTR2.  `char2`/`char2_norm`/`char2_iff` remain the local
  workhorses (28 sites); no manual `ring_nf`+`CharTwo` incantation
  survives outside them.
- **Minted**: `pairMass_le_of_reveal` (lemma, not macro) — the
  `mass_mono` + `revealCollapse_le` reveal-lift; deduplicates 9
  `pairD_*`/`pairR_*` leaf proofs (the 2 direction-split senc/sdec
  variants stay on `revealCollapse_le` directly).
- **Left, threshold not met**: bare `dsimp only` beta-normalizer (18
  sites, already one line; Mathlib `beta_reduce` is no shorter);
  counting-block `push_cast`/`zify` (9 sites, no two identical); the
  `mass_eq_zero_of_forall`-then-`zero_le _` branch shape (2 identical
  sites).

### 7.2 P1-count automation lessons (2026-07-09)

- **`ring` inside `first`/`<;>` combinators is a trap**: on failure it falls
  back to `ring_nf`, *succeeds* with the goal left open, and the combinator
  commits — every downstream alternative is silently skipped.  Use `ring1`
  in closers (standing rule; three sites in the P1 count hit this).
- **`simp`/`simp_all` with hypothesis-flags is non-confluent**: an equality
  flag (`h3 : ↑p.1 = 0`) rewrites inside the *other* conditions before they
  can match their own flags, and the default set normalizes `¬(a < b)`/
  val-lt into forms the flags no longer match.  For decidable case grids,
  prefer atomic `by_cases` flags + `simp only [flags, if/and lemmas]` (no
  default set), with `split_ifs <;> first | rfl | (push_cast; ring1) |
  (exfalso; omega)` as the residual closer.  `omega` does not split `∧`/`¬∧`
  hypotheses — feed it atomic flags.
- New generic counting layer (reusable): `Counting.sq_sum_eq_sum_sq_add_two_
  mul_sorted`, `Counting.sum_sorted_add`, `Counting.sum_prod_trichotomy`/
  `sum_sorted_swap`, `Counting.mul_pred_add`; `Derivation.sum_fin_gate`/
  `_prod`/`_sorted` + `card_filter_fin_pos_lt`, `Derivation.sum_sorted_capSplit`
  (sorted-pair block split over a `Bool ⊕ instance × slot` cap, abstract rank).
  These + `mass_sorted_pair_le_of_embed` + the `expectW` engine are the full
  generic spine of a σ-accounted sorted-pair union bound; only the charge
  tables and the two scalar slack lemmas are application-specific.

### 7.3 Controlled-language sentence layer (2026-07-21)

`RandomSystemsCC/ControlledNaturalLanguage.lean` — the `rs.` sentence
vocabulary anticipated by AC's CNL header, organized as **proof styles**:
condition C (`rs.condition_c.*`: Maurer's 4.17/4.18 transitions + endpoint
summary) and H coefficients (`rs.h_coefficient.*`: good/bad,
equality-on-good, and perfect skeletons over
`adv_le_of_fixedQuery_ratio(_of_good/_eq_on_good)`; leg sentences closing
`?good_ratio`/`?good_equality`/`?bad_probability`/`?pointwise_ratio`; a
`defect ≤ 1` WLOG guard; endpoint summaries).  Structure sentences leave
exactly the mathematical legs as named goals; what they hide is strictly
non-argument (`cr18_total`, `NNReal` `δ + 0` casts, the degenerate
`defect > 1` branch).  Wording is real H-coefficient paper prose, per the
module's documented writing standard: complete clauses with predicative
parameters (“the bad event is ⟨B⟩”), citations as trailing “, by ⟨ref⟩” or
instrumental “using ⟨ref⟩”, hypotheses named via “; call this assumption
⟨h⟩”.  No proof search — citations are explicit `cryptoCnlReference`s with
optional prose annotations.  `urp_KStepTotal` is
tagged into `Cr18Total` from this module (move next to the lemma at the
next `Derivation.lean` rebuild).  Demo: `RandomSystemsSwitchingDemo.lean`,
five presentations of the switching lemma (plain calc; condition-C
sentences; structured perfect-H; structured good/bad-H at
`Bad := Collision`; one-line summaries).  Token trap for future sentences:
syntax atoms (e.g. `"bad"`) register as global tokens, so a *later* macro
parameter with that name no longer parses as an ident — rename the
parameter (cf. `badEvent`).

## 7a. HCTR2 formalization (started 2026-07-03)

`RandomSystems/HTechnique/HCTR2.lean` — self-contained formalization of
ePrint 2021/1441 (Crowley–Huckleberry–Biggers), **goal: formalize the
existing proof**.

**STATE 2026-07-04 (end of rebuild session): the file is SORRY-FREE and in
the `All`/`Surface` gate; the audit exemption is removed.**  Both headline
theorems are proven with clean axiom checks (`propext`, `Classical.choice`,
`Quot.sound`):
- `hctr2_securityL` — the paper's §3.5 bound for the paper's adversary class
  (no pointless queries, the `hctrNP` filter = the paper's §3.4 standing
  assumption);
- `hctr2_securityL_unrestricted` — the reduction from *unrestricted*
  adversaries (beyond the paper), via the proven `hctr_pointless_wlog`:
  a simulating environment that self-answers checkably-pointless queries
  with the determined value (`hctrDeterminedAnswer` + oracle coherence),
  pads with head-fresh queries (hence the mild `q ≤ |F|` hypothesis), and
  transfers the distinguishing advantage through the transcript-law
  pushforward (`deterministicTranscriptDist_functionEvaluator_eq_fTransform`)
  and the statistical-distance DPI.

**Soundness-of-meaning fix (gap #7, pre-existing)**: `lpNPV` compared
`facIO`'s `Classical.arbitrary` junk branch across length-mismatched
responses, making `EnvRespects hctrNP` provably false for any environment
asking two distinct same-class queries — every filtered theorem (including
the PRP-RND birthday lemma) quantified over a near-empty adversary class.
`lpNPV` now guards on length-match; two proof sites repaired; all filtered
statements unchanged but now meaningful.

Session highlights (details in the file header and the lemma docstrings):
- **Soundness fix**: the previous direction split ("both-fwd/some-inv") of
  the MM–MM/UU–UU/Y–UU cells contradicted the paper's Figs 4/5 ("direction of
  the *later* query"); three sorried leaves were false as stated (explicit
  countermodel: decrypt-then-interpolate adversary beats `1/N` via a d-root
  POLYVAL polynomial).  Tables, dispatch (now merged, sorted-pair-only via
  `capRank_lt_inr_inr`) and budget arithmetic redone against the paper; the
  budget also needs `1 ≤ Hf.d` (false at `d = 0`), now threaded.
- **Counterfactual pointless exclusion**: `EnvRespects` is possibilistic, so
  per-transcript plaintext/ciphertext-share exclusion needs response surgery
  (`envReplay` machinery + `hctr_queries_eq_of_shares`); `revealCollapse_le`
  now passes `hctrAdmissible` (filter ∧ consistency ∧ length-match).
- **Response-pin engine** (the paper's p.11 conditioning sentence as a
  theorem): `uniform_pi_selfloc_le` (self-locating-coordinate counting; no
  conditional probability needed), `envRun` run machinery +
  `envRun_prefix_congr` (adaptivity), `hctr_omega_slice_le` (transcript law =
  pushforward of uniform ω), `hctrOmegaEquiv` block reindex, capstone
  `hctr_respPin_le` with a *query-dependent* pin index (same-query UU–Y pins
  block 0 for enc but block j for dec, paper p.12).  All five response leaves
  proven with it.
- **Budget summation** `hctr_pairBound_sum_le`: quadrant decomposition with
  exact cell counts matching `hctr_pairBound_numeric` (proven, exact
  Δ-certificate).

Landed: field-based block model (`F` a char-2 finite field, `⊕ = +`),
`BinEnc`, `HashFamily` (paper §3.2 Properties 1–3 as fields), `xctr`,
`hctr2Enc`/`hctr2Dec` (Figs 2–3) with the correctness lemma
`hctr2Dec_hctr2Enc` (proved), the two-directional `hctr2Fun`, worlds
`hctr2Real` (X = HCTR2[Perm]) / `pmRnd` (Y = ±rnd = URF) /
`idealTweakablePerm` (±p̃rp), and `sigmaBlocks`.

Roadmap (full 6-phase plan is in the file header).  **Phase 1 + 2a DONE**
(reusable, sorry-free):
- `Derivation.lean`: `pow_inv_le_descFactorial_inv` (`N^{-k} ≤ 1/(N)_k`),
  `uniform_perm_consistent_mass_ge` (perm-consistency good-ratio engine,
  reusing `card_perm_fiber`), `adaptiveTranscriptAdvantage_triangle` (lifts
  `statDist_triangle`), and `uniform_pi_eval_mass` (the general tweak-product
  factorization: `Pr_f[∀i, P i (f(idx i))] = ∏_τ Pr_a[…]`, via
  `Fintype.card_piFinset`).
- `HCTR2.lean`: `permConstraint` (direction-aware per-query perm constraint),
  `tweakableStrongPermFunction_eq_iff`, and `tweakableStrongURP_output_mass_prod`
  (the `±p̃rp` output mass factors over tweaks — the good-ratio heart).  Custom
  tactic `hctr2_dir` (grind-based `QueryDir` case split) + `@[grind]`
  instrumentation.
Audit carries a WIP allowlist (`HCTR2.lean`) so the sorry-bearing file stays
out of the sorry-free `All` gate while remaining tracked.

**NonPointless filter added** (2026-07-03).  Discovered while proving Phase 2:
the ±rnd-comparison lemmas are FALSE over all environments — a pointless
inverse query distinguishes a permutation from the memoryless URF with
advantage ≈1 (this is exactly why the paper §3.4 forbids pointless queries;
it is NOT WLOG against ±rnd, only against another permutation).  So:
- `Derivation.lean` gains the general filtered-adversary machinery:
  `EnvRespects`, `filteredAdaptiveTranscriptAdvantage`, its
  `_le_of_pointwise`, and the endpoint
  `adv_le_of_fixedQuery_ratio_of_good_filtered` (good ratio needed only on
  `Filt` transcripts; bad bound only over respecting environments).
- `HCTR2.lean` gains `NonPointless` (distinct queries ⟹ distinct
  tweak-perm constraints; repeats free) and restates `tweakableStrongURP_rnd`
  and `hctr2_main_lemma` over the `NonPointless`-filtered advantage (now
  TRUE).
- `hctr2_security` reverts to a documented sorry: it now needs the WLOG step
  (`Adv[q] = filteredAdv NonPointless` for the permutation-vs-permutation
  pair) + a filtered triangle — the correct consequence of the filter.
3 sorries: the two restricted intermediates + security-via-WLOG.  **Phase 2 assembly infra — all landed and verified** (sorry-free, in
`Derivation.lean`): `uniform_perm_consistent_mass_ge_finset` (partial-injection
perm mass, repeats allowed), `card_image_le_of_factors` (`|image φ| ≤ |image ψ|`
when φ factors through ψ — the `Σdτ ≤ c` counting engine), the tweak
factorization `uniform_pi_eval_mass` + `tweakableStrongURP_output_mass_prod`,
and the filter endpoint `adv_le_of_fixedQuery_ratio_of_good_filtered`.

Remaining for `tweakableStrongURP_rnd`: the ~250-line combination —
(a) **good ratio** `tr(urf,t) ≤ tr(±p̃rp,t)` on `NonPointless ∧ ¬Bad`:
reduce to output masses, `urf = N^{-c}` (`uniformFunction_eval_apply`),
`±p̃rp = ∏_τ perm_mass_τ ≥ ∏_τ N^{-dτ} = N^{-Σdτ} ≥ N^{-c}` with `Σdτ ≤ c`
from `card_image_le_of_factors` on `¬Bad`; (b) **bad bound** via the ratio
trick (`Pr_{±p̃rp}[Bad]=0`, switching ratio `(1-δ)·tr(±p̃rp) ≤ tr(urf)` needing
`Σdτ = c` from `NonPointless`, per-tweak `switching_ratio_le`).  Both hinge on
a fibered per-tweak sum `Σ_τ dτ = |image(tweak,pInp)|` — the one remaining
combinatorial step.

## Variable BLOCK-length migration (Option A) — ✅ COMPLETE (2026-07-03)

Decision: migrate to variable-length messages, **capped** at `L`, length-
preserving ideals.  **Block-aligned assumption** (documented, NOT proven): the
fibers `F × (Fin ℓ → F)` are whole `F`-blocks, so lengths are multiples of `n`
— a strict restriction of the paper's arbitrary-bit-length `M = ⋃_{i ≤ n+2ⁿ−1}`
(under which the leftover `Dˢ` is empty).  True bit-level (`BitVec` fibers + the
`Dˢ` machinery) is a deferred future migration.
Strategy (per Marc): parallel implementation in the SAME file, validate,
then delete the fixed-length statements/types and promote the new ones.

**DONE — fixed-length fully deleted, faithful model promoted (full build 8431
jobs green).**  The construction now lives over `TotMsg (hctrMsgL F) =
Σ ℓ : Fin L, F × (Fin ℓ → F)`:
- **Construction** (`§Faithful`): `hctrMsgL`, length-polymorphic `HashFamilyL`
  (single degree bound `d` uniform over lengths), `xctrL`/`hctr2EncCoreL`/
  `hctr2DecCoreL`/`hctr2FunL`, `hctr2RealL` (one `π ∈ Perm F` across lengths),
  `sigmaBlocksL`.  Correctness `hctr2DecCoreL_hctr2EncCoreL` proven.
- **Statements** (`§Faithful.Statements`): `hctr2_main_lemmaL` (sorry),
  `hctr2_securityL` (sorry), and **`tweakableStrongURP_rndL` PROVEN** — the
  `N_min = |F| = 2ⁿ` instance of `lpTweakableStrongURP_rnd`, with `N_min`
  realized by the shortest one-block class via `F ↪ F × (Fin ℓ → F)`.
- **Deleted** (~450 lines): `Msg`, `HashFamily`, `xctr`/`hctr2Enc`/`hctr2Dec`/
  `hctr2Fun`/`hctr2Real`, `pmRnd`, `idealTweakablePerm`, `sigmaBlocks`, the
  whole `PRPRND` + `PRPRNDProof` engine (`permConstraint`/`Bad`/`NonPointless`/
  `good_ratio_transcript`/`switch_ratio_transcript`/`tsURP_no_bad`/`bad_bound`)
  and the three fixed-length statements.  `NonPointless`→`lpNonPointless`
  resolved the entanglement.  Only two `sorry`s remain (Phases 3-5 + Phase 6),
  now stated faithfully over the length-preserving objects.

**De-risk COMPLETE (no HEq tar pit):**
- length-preserving perm over `Σ ℓ, MsgL ℓ` is HEq-free (`Sigma.ext rfl`);
- `uniform` over the dependent family `∀ (t,ℓ), Perm(MsgL ℓ)` works;
- `uniform_dpi_eval_mass` (dependent factorization, per-index codomain via
  `h ▸ a`) — **proven and landed in `Derivation.lean`**;
- the Sigma-*output* equality (which introduces `HEq` via `Sigma.mk.injEq`)
  collapses to a clean transported `Eq` by casing on the length-match
  `v.1 = ℓ` (`cases v; cases hv; simp`).

**Landed (parallel objects, green, in `HCTR2.lean` §LengthPreserving):**
`TotMsg`, `lpStrongPermFunction`, `lpTweakableStrongURP` (±p̃rp, perm per
`(tweak,length)`), `lpUrfFunction`, `lpUrf` (±rnd, uniform per length), and
both `_KStepTotal`.

**Landed (all green, `HCTR2.lean §LengthPreserving`):** the full transport
core — `idxOf`, `lpConstr` + `DecidablePred`, `lpStrongPermFunction_eq_iff`,
`lpTweakableStrongURP_output_mass_prod` (dependent `(tweak,length)`
factorization), `lpIO`, `lpConstr_iff`, `lpConstr_transport`, `facIO`,
`lp_factor_mass_eq` (factor mass = perm-consistency over `MsgL p.2`), and
`lp_perm_factor_ge` (**per-factor good bound** via
`uniform_perm_consistent_mass_ge_finset`).  The transport template is nailed:
destructure `v i` first → `Sigma.mk.injEq`/`heq_eq_eq`/`grind[Equiv.symm_apply_eq]`;
factor transport via `subst h`; length-view via `k.2.symm ▸` + `Subsingleton.elim`.

**Also landed (green):** `lpUrfConstr` + `lpUrfFunction_eq_iff`,
`lpUrf_output_mass_prod` (±rnd factors over the query alphabet),
`lpUrf_factor_le` (per-query factor ≤ N_ℓ⁻¹ on hit), `lpUrf_output_le`
(±rnd mass ≤ ∏_{Q∈image} N_ℓ⁻¹).  So both sides of the good ratio are now
bounded: `±p̃rp ≥ ∏_{(t,ℓ)} N_ℓ^{−d}` (via `lp_perm_factor_ge`) and
`±rnd ≤ ∏_{Q∈image} N_ℓ⁻¹`.

**GOOD-RATIO DIRECTION COMPLETE (2026-07-03, all green):** landed
`lpBadV`, `facIO_eq`, `transp_content_eq`, `lp_facIO_fst_eq` (facIO.1 factors
through query ⟹ d≤cq), `lp_filter_eq_subtype_card`, `lp_perm_factor_ge_cq`
(N^{−cq}≤factor), and **`lp_good_output_ratio`** (`±rnd ≤ ±p̃rp` on `¬lpBadV`,
via `prod_fiberwise` regroup + `gcongr` + mismatch⟹`±rnd=0`).  Custom pattern:
destructure-`v`-first + `Sigma.ext_iff`/`cast_heq` + `subst h` for transports.

### LP PRP-RND COMPLETE (2026-07-03, all green — faithful Phase 2 done)

The entire length-preserving PRP-RND is landed and verified, sorry-free:
- **Good direction:** `lp_good_output_ratio` → `lp_good_ratio_transcript`
  (`±rnd ≤ ±p̃rp` on `¬lpBad`).
- **Switch direction:** `lp_perm_factor_switch` (`switching_ratio_le` +
  NonPointless `cq=d`), `lp_sum_bday_le` (`Σcq(cq−1)≤q(q−1)`),
  `lp_switch_output_ratio` → `lp_switch_ratio_transcript`
  (`(1−C(q,2)/N_min)·±p̃rp ≤ ±rnd`).
- **No-bad + bad bound:** `sysFactor_lpTweakableStrongURP`,
  `lp_factor_zero_of_bad` (perm can't map one input to two outputs / two to
  one — partial-injection violation ⟹ factor 0), `lpTsURP_no_bad`
  (matched/non-matched split via `lpConstr_iff`), `lp_bad_bound`
  (ratio trick `probBad_le_of_ratio`).
- **Assembly:** `lpTweakableStrongURP_rnd` — via
  `adv_le_of_fixedQuery_ratio_of_good_filtered` with the `lpNonPointless`
  filter:

      filteredAdaptiveTranscriptAdvantage lpNonPointless (±p̃rp) (±rnd)
        ≤ C(q,2) / N_min          (N_min ≤ |MsgL ℓ| for all ℓ)

Honest re-derivation over the dependent `(tweak,length)` index, NOT a rename:
every content/output touch carried the dependent transport, collapsed via the
extracted atoms `lp_transp_eq_iff` / `lp_content_heq`.

**PROMOTION (swap) — remaining:** the fixed-length Phase-2 engine
(`section PRPRNDProof`, lines ~369–793: `Bad`, `NonPointless`,
`good_ratio_transcript`, `switch_ratio_transcript`, `sysFactor_tweakableStrongURP`,
`tsURP_no_bad`, `bad_bound`) and its concrete instantiation
`tweakableStrongURP_rnd` are now fully superseded by the LP versions.  They are
referenced by nothing compiled (only a comment inside the `sorry`-stubbed
`hctr2_security`).  Full deletion + promotion is entangled with the *construction*
migration (Phases 3–5: `hctr2Real`/`Msg`/`pmRnd`/`idealTweakablePerm` are still
fixed-length), which is deferred.  `pmRnd`/`idealTweakablePerm` (lines 288/295)
must stay — used by the deferred `hctr2_main_lemma`/`hctr2_security`.

## HCTR2 main lemma `hctr2_main_lemmaL` (Phases 3-5, §3.4) — plan + infra map

The bulk. Faithful statement (green sorry) at `HCTR2.lean`:
`filteredAdaptiveTranscriptAdvantage lpNonPointless (hctr2RealL) (lpUrf) ≤
(3σ²+2qσ+7σ+2)/(2·|F|)`.  Paper §3.4 fully digested (papers/2021-1441.pdf
p.8-16; `pdftotext … | sed -n '420,1010p'`).

**Reduction chain** (H-technique, ε=0): `Adv ≤ Pr[Y∈T_bad] ≤ 2·C(σ_m,2)/N + c`,
`N=|F|=2ⁿ`, `σ_m = 2 + Σ_s m_s ≤ σ+2`, `c = c_b(−1)+c_f(≤2σ)+c_w(≤0)+
c_a(≤(q−1)σ+C(σ,2))`.  Final arithmetic **VERIFIED** (`scratchpad/arith.lean`:
`nlinarith`+`Nat.choose_two_right`; the `c_b=−1` is load-bearing — dropping it
overshoots by `1/N`).

**LANDED — the architectural unblocker (green, `Derivation.lean`):**
`adv_le_of_extFixedQueryRep_ratio_of_good_filtered` (+ generic
`adv_le_of_extended_ratio_of_good_filtered`).  The main lemma needs BOTH the
representative extension (world-X = falling factorial) AND the pointless filter
(HCTR2[π] is a perm).  Insight: on `¬Bad` the good ratio holds *unconditionally*
(a pointless query forces `MMʳ=MMˢ` ⟹ D-collision ⟹ Bad), so the filter enters
ONLY on the bad-bound side — the filtered endpoint = unfiltered rep endpoint
with the sup restricted to `Filt`-respecting E.

**The 22 cases collapse to 4 shape-lemmas** (systematization — no argument
written twice; each Fig 4/5 box is one instance):
- **S1 uniform** (`= 1/N`): event ⟺ `(V = rhs)`, `V∈{L,h̄,Uˢ,Mˢ}` uniform &
  independent given the conditioning.  14 grey boxes + every green-on-decryption.
  Tool: `uniform_function_pair_eq_mass` / `iid_uniform_pair_eq_mass` (=1/N).
- **S2 impossible** (`= 0`): `bin(0)=bin(1)`, `Sⁱˢ=Sⱼˢ ⟺ bin(i)=bin(j)`.
- **S3 hash-1/3** (`≤ d/N`): event ⟺ `H_h̄(t,m)=g` / `H+h̄=g` — `HashFamilyL.prop1`/
  `prop3` DIRECTLY.  Cases `bin=MMˢ`, `h̄=UUˢ`, `Yⁱʳ=UUˢ`.
- **S4 hash-XOR** (`≤ max(dʳ,dˢ)/N`): event ⟺ `H(t₁,m₁)⊕H(t₂,m₂)=g`, `(t,·)`
  distinct — `HashFamilyL.prop2`.  Cases `MMʳ=MMˢ`, `UUʳ=UUˢ`.

**KEY FINDINGS (2026-07-03):**
- **Block-aligned ⟹ NO leftover `Dˢ`**: `hctrMsgL ℓ = F × (Fin ℓ → F)` uses
  whole `F`-blocks, so `|Pˢ|` is always a multiple of `n` — no partial block.
  The reveal collapses to `Z = F × F` (just `h̄, L`) and `Yⱼˢ = Nⱼˢ ⊕ Vⱼˢ`.
- **Char-2 has a reuse after all**: `linear_combination h` closes every XOR
  rearrangement (both iff directions) in a char-2 field — no custom tactic
  needed for the collision-equation ⟺ `V = rhs` steps.
- **Inferred `MMˢ,UUˢ,Sˢ,Sⱼˢ` are SCALARS in `F`** (only tail vectors are
  length-indexed) ⟹ definable with no dependent transport; tails handled by
  total `ℕ → F` 0-extensions (`tailN`/`tailV`).

**Build order (each layer green-independent):**
1. **Reveal + inferred blocks** (defs). ✅ **L1 DONE (green, `HCTR2.lean`
   §MainLemmaSetup)**.  L1a: `hctrPlain`/`hctrCipher`/`hctrTweak` (direction-aware
   extraction), scalar `MMv`/`UUv`/`Sv`/`Sjv`, `tailN`/`tailV`/`Yjv`, `mBlocks`.
   L1b: `DRIdx` (`Bool ⊕ Σ s, Fin (mBlocks t s)`), `Dfull`/`Rfull` entry families,
   `hctrTBad := ∃ two distinct entries equal` (D or R), representatives
   `hctrRealP/F` (Perm F, `aug = (π(bin0),π(bin1))`), `hctrIdealP/F`
   (dummy `(h̄,L)` × lpUrf coins, `aug = dummy`).  NOTES: file convention needs
   explicit `hctrMsgL (L := L) F` (L not inferrable); concrete per-fiber instances
   `hctrMsgL_{fintype,decEq,nonempty}` are declared so the Sigma/Pi builders
   resolve the URF coin space `Fintype` (abstractly assumed inside `lpUrf`).
   **L1-glue ✅ DONE (green)**: `pmf_hctrReal_eq` (`= hctr2RealL`, `rfl` since
   `functionEvaluator p F = Dist.PMF p (functionEvaluatorRV F)`) and
   `pmf_hctrIdeal_eq` (`= lpUrf`, dummy sums out; mirrors `pmf_dummyKey_eq_urf`
   via `mass_prod_snd_pred`).
2. **S1-S4 shape lemmas** ✅ **DONE (green)**.  `uniformSingleton_mass` (S1
   `= 1/N`); the char-2 collision reductions `MMv_eq_iff`/`UUv_eq_iff` (→ S4
   `prop2`), `Sjv_eq_MMv_iff` (→ S1, isolates `L`), `hbar_eq_UUv_iff` (→ S3
   `prop3`), all closed by
   `linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h`
   (plain `ring` leaves a `2·x=0` residue — the char-2 normalizer is the reusable
   pattern; a `macro`/`syntax` wrapper does NOT work inside `norm :=`, so it is
   inlined).  S3/S4 upper bounds ARE `HashFamilyL.prop1/2/3` directly; S2
   (`bin(i)=bin(j)` impossible) still to add (needs `bin` injectivity on the
   block range).  More reductions (the remaining ~18 case dispatches) added as
   Layer 4 consumes them.
3. **Good ratio** (σ⁺).  ✅ **DONE (green, 2026-07-03)** — whole layer, incl. the
   inference CRUX.  Landed:
   - `sigmaM = 2 + Σₛ mˢ`, `card_DRIdx : |DRIdx t| = sigmaM t`.
   - **Inference / reconstruction** (`hctr_reconstruct`): the direction we need
     (consistent-`π` ⟹ realizes transcript+reveal).  Built cleanly by mirroring
     the *correctness* proof shape — a `dite`-free per-query core lemma
     `enc_reconstruct`/`dec_reconstruct` on `hctr2EncCoreL`/`DecCoreL` (fixed `k`,
     `F × (Fin k → F)`, no `Sigma`/direction/`dite`), then `cases dir; obtain
     query/response; dsimp; subst; Sigma.ext; exact enc/dec_reconstruct`.  KEY
     UNBLOCK: `tailN`/`tailV` were re-defined `dite`-free as
     `(List.ofFn …).getD j 0` — the old `dite`'s dependent proof term
     (`⟨j,h⟩`) had blocked every `cases`/`generalize`/`set`.  See memory
     `automation-first-lean-proofs`.
   - `hctr_query_inj` (¬Bad ⟹ query vector injective; MMˢ/UUˢ block-0 collision).
   - `hctr_real_ge` (real σ⁺ `≥ N^{−σ_m}` on good+len via
     `uniform_perm_consistent_mass_ge_finset` + `card_DRIdx` + `mass_mono`).
   - `hctr_ideal_le` (ideal σ⁺ `≤ N^{−σ_m}`: `mass_prod_and` dummy×URF,
     `lpUrf_output_le`, `Finset.prod_image` over the injective query vector,
     fiber card `N^{ℓ+1}`), and `hctr_ideal_zero` (len-mismatch ⟹ 0).
   - **Deliverable `hctr_sigma_ratio`**: the ε=0 σ⁺ ratio
     `ideal ≤ real` on any ¬Bad tz (branch on length-consistency:
     `ideal ≤ N^{−σ_m} ≤ real`, else `ideal = 0`) — exactly the `h_ratio`
     hypothesis of `adv_le_of_extFixedQueryRep_ratio_of_good_filtered`.
4. **Bad bound** (`h_bad`; **refined 2026-07-03**, in-file docstring on
   `hctr_bad_bound`).  **KEY INSIGHT — reveal-factoring**: `extSysFactorRep ideal
   (t,z)` is INDEPENDENT of the reveal `z` (URF factor ignores the dummy), so
   `extendedTranscriptDistRep ideal E (t,z) = N⁻²·tr(lpUrf,E)(t)` and
   `Pr[Bad ∣ ext ideal E] = Σ_t tr(lpUrf,E)(t)·Pr_{z∼unif(F×F)}[Bad(t,z)]`.
   ⇒ the collision analysis is over a **fixed transcript `t`** (`DRIdx t` a fixed
   `Fintype` ⇒ `probBad_iUnion_le` applies) with only `(h̄,L)` random.  Then:
   (a) prove the reveal-factoring (`mass_prod_and`, like `hctr_ideal_le`'s `hfact`
       but WITHOUT fixing `z`);
   (b) per-`t` union bound over `DRIdx t`-pairs → 22 cases → 4 shapes (S1
       `uniform_pt_mass`, S2 `bin i≠bin j`, S3 `prop1/3`, S4 `prop2`) — each
       `char2`/`grind`-dispatched via the algebraic reductions
       `MMv_eq_iff`/`UUv_eq_iff`/`Sjv_eq_MMv_iff`/`hbar_eq_UUv_iff`;
   (c) ✅ **DONE (green)** `σ_m(t) ≤ σ+2`: `sigmaM_le Hf hLd t : sigmaM t ≤
       sigmaBlocksL Hf q + 2`, from `mBlocks_le_d Hf hLd t s : mBlocks t s ≤ Hf.d`
       (`mˢ = ℓˢ+1 ≤ L ≤ d`, `ℓˢ : Fin L`).  MODELING decision: the blocks-per-
       query ≤ hash-degree fact enters as a **threaded hypothesis `hLd : L ≤ Hf.d`**
       (NOT a `HashFamilyL` struct field — zero construction sites, but `L` is not a
       structure parameter; the paper's `d = 1+⌈|T|/n⌉+⌈|P|/n⌉ ≥ L` supplies it).
       `hctr_bad_bound`/`hctr2_main_lemmaL`/`hctr2_securityL` gain `hLd`;
   (d) `Σ_t tr(lpUrf,E)(t)·B(σ_m(t)) ≤ hctrBadBudget` via
       `Σ_t tr(lpUrf,E)(t)=1` + summation (`cr18_arith!`, `Nat.choose_two_right`).

   **EXACT paper analysis (2026-07-03, read `papers/2021-1441.pdf` §3.4.2–3,
   Figs 4/5) — for the faithful build:**
   `Pr[Bad] ≤ 2·C(σ_m,2)/2ⁿ + c/2ⁿ`, `c = c_b+c_f+c_w+c_a`:
   `c_b=−1` (`bin0≠bin1`); `c_f ≤ Σ_s 2(d_s−1) ≤ 2σ` (fwd: `bin0=MMˢ`,`bin1=MMˢ`
   at `d_s/2ⁿ`; inv: `h̄=UUˢ` at `d_s/2ⁿ`); `c_w ≤ 0` (`Sᵢˢ=Sⱼˢ` impossible);
   `c_a ≤ Σ_{r<s}(d_r+d_s−1+(m_r−1)(d_s−1)) ≤ (q−1)σ+C(σ,2)`.  Arithmetic (with
   `σ_m ≤ σ+2`) closes to `(3σ²+2qσ+7σ+2)/2ⁿ⁺¹` — VERIFIED.  22 cases: 14 at
   `1/2ⁿ`, 2 impossible (`0`), 6 at `d/2ⁿ` or `max(d_r,d_s)/2ⁿ`.
   **CLEAN DECOMPOSITION (2026-07-03, revised by building it): `Bad = RevealBad ∨
   ResponseBad`.**  `ResponseBad` = EXACTLY the `Yᵢʳ=Yⱼˢ` pairs (both `Yⱼˢ=Nⱼˢ⊕Vⱼˢ`
   reveal-independent — need a URF response block).  Everything else (incl.
   `UUˢ=Yⱼˢ` via `prop1`, `Sᵢʳ=Sⱼˢ` via `h̄` after `L` cancels — my earlier
   "these need responses" note was WRONG) is `RevealBad`, bounded over the uniform
   reveal `(h̄,L)`.  Then `Pr[Bad] ≤ Pr[RevealBad] + Pr[ResponseBad]`:
   `Pr[RevealBad] = Σ_t tr(ideal,E)(t)·Pr_reveal[…]` (collapse SOUND here), and
   `Pr[ResponseBad] = Pr_ideal[∃ Y-collision]` = a birthday bound over URF
   responses (≈ `probBad_urf_collision_le`).  `DRIdx t`-dependence dissolved by
   over-approximating `Fin (mBlocks t s)` with the fixed cap `Fin L`.
   **UNION-BOUND REDUCTION GREEN (2026-07-03, no heartbeat bumps):**
   `hctr_bad_bound` → `mass_or_le` → `hctr_col_bound` → `mass_witness_iUnion_le`
   (NEW generic Finsupp-level union-bound atoms; `evalPred`/`probBad_iUnion_le`
   drag transcript-carrier `Fintype`+decidability and time out `whnf`) fed by
   `Dcol_witness`/`Rcol_witness` over the fixed cap `Bool ⊕ Fin q × Fin L`
   (`capValid` decidable in-range predicate, `DfullFix`/`RfullFix` total
   extensions) → **`hctr_pair_bound` = THE remaining Layer-4 sorry** (per-pair
   §3.4.2 routing + §3.4.3 summation).  LESSON (now standing rule): CR18 proofs
   at `mass` level, HO predicate args as `_` (explicit lambdas ⇒ whnf blowup).
   STATUS: **plan + case table + arithmetic LOCKED; reveal-shape library COMPLETE
   (green).**  Green reveal per-shape bounds over `Dist.uniform (F×F)` (all ~5-line,
   modeling vindicated): `revealMMv_collision_le`/`revealUUv_collision_le` (S4,
   `prop2`), `revealhbar_UUv_le`/`revealUUv_Yjv_le`/`revealMMv_const_le` (S3,
   `prop1`/`prop3`), `revealSjvMMv_le`/`revealSjv_const_le`/`revealhbar_Yjv_le`/
   `revealL_Yjv_le` (S1, via `uniform_prod_snd_functional`/`mass_prod_fst/snd` +
   `uniformSingleton_mass`), with iff helpers `MMv_eq_const_iff`/`UUv_eq_const_iff`/
   `Sjv_eq_const_iff`.  Plus `mBlocks_le_d`/`sigmaM_le` (counting) and
   `hctr_bad_summation` (arithmetic).  REMAINING (the `hctr_bad_bound` sorry, all
   volume/assembly — modeling cleared): (i) block-block D `Sⱼˢ=Sₖʳ` shape (`c_a`,
   `L` cancels → `h̄`-equation); (ii) `Pr[ResponseBad]` birthday bound over URF
   responses (adapt `probBad_urf_collision_le`/`uniform_function_pair_eq_mass` to
   the derived `Yⱼˢ`); (iii) per-`t` union bound over the fixed-`Fin L` index +
   reveal-collapse; (iv) counting glue → `hctr_bad_summation`.
5. **Assembly** ✅ **DONE (green)**: `hctr2_main_lemmaL` =
   `adv_le_of_extFixedQueryRep_ratio_of_good_filtered` (eps=0) fed
   `hctr_sigma_ratio` (L3) + `hctr_bad_bound` (L4), `Dist.PMF` marginals rewritten
   via `pmf_hctrReal_eq`/`pmf_hctrIdeal_eq`; faithful-space `Fintype`/`DecidableEq`
   transcript instances added.  Only `hctr_bad_bound` remains sorried.

**Key reusable endpoints** (from 2026-07-03 infra survey; namespaces
`CR18.HTechniqueDerivation` / `RandomSystems` / `CR18` / `CR18.Counting`):
rep machinery `extendedTranscriptDistRep`(:1100) `extFixedQueryTranscriptDistRep`
(:1155) `extFixedQueryTranscriptDistRep_self`(:1163)
`extended_ratio_of_extFixedQueryRep_ratio_of_good`(:1173)
`fTransform_fst_extendedTranscriptDistRep`(:1127); bad toolkit
`probBad_iUnion_le`(StatDist:273) `mass_biUnion_le`(SwitchingLemma:54)
`uniform_function_pair_eq_mass`(SwitchingLemma:168)
`iid_uniform_pair_eq_mass`(:143) `queryPairSet`(:670) `card_pair_eq_type` (the `Fin t` copy `card_pair_eq` was deleted 2026-08-07 as a verbatim duplicate)
worked template `uniform_mass_blindQueryCollision_le_pairCollisionUnionBound`
(:978); AXU templates `hashCollision_prob_le`(HashThenPRF:188)
`uniformK_hashBadAt_le`(Derivation:3252); counting
`nnreal_one_sub_sum_le_prod`(:2394) `pow_inv_le_descFactorial_inv`(:2263)
`uniform_perm_consistent_mass_ge_finset`(:2301); triangle
`adaptiveTranscriptAdvantage_triangle`(:2433); tactics `cr18_simp`/`cr18_grind`/
`cr18_mass_expand`/`cr18_sum_swap`, `htechnique_*`.

Scoped out (this file): computational `HCTR2[E]` vs `HCTR2[Perm]` substitution.
`hctr2_securityL` (Phase 6) = WLOG (both perms) + filtered triangle composing
`hctr2_main_lemmaL` + the proven `tweakableStrongURP_rndL`.

## 7b. HCTR2 proof audit (2026-07-04) — improvement inventory + migration plan

Five-section audit of the completed proof (tree-down; correctness NOT in
question — quality only).  Headline: the file is ~6.2k lines of which an
estimated **35–45% is avoidable glue** (target after migration: ~3.9k lines
in HCTR2.lean + ~700 new generic lines in Derivation that serve every future
H-technique proof).  The worst section (dispatch/counting) is 78% glue.

### Root causes (ranked)

1. **Hand-instantiated union bound** — witness maps, sorted-guard if-wrapper,
   per-pair dispatch and quadrant summation are five bespoke layers around
   what should be ONE generic rank-filtered sorted-pair lemma
   (`mass_sorted_pair_le_of_embed`) plus a paper-literal cell classifier
   (`inductive DCell`, one constructor per Fig-4/5 color, fiberwise sum).
2. **Symmetric proofs paid twice** — plain/cipher, MM/UU, Enc/Dec, D/R-Fix,
   fwd/inv, and the pin engine's raw two-transcript interface (all six
   consumers prove `e1` AND `e1'`).  Fixes: `hashBlk` extractor
   parametrization (audited: BEATS the dirFlip involution, which breaks on
   environments and on the real D/R asymmetry); merged
   `hctr_io_share_false`; `hctrSides` normalizer; a solved-form
   `hctr_respPin_solved_le` (block = rhs(z,t) + rhs-congruence ⟹ engine
   derives the two-transcript pin internally).
3. **Third hand-rolled replay engine** — §PointlessWlog duplicates
   `absorbGo` (AbsorbDPI) and `driveNu` (ProtocolRealization) at concrete
   types; ~70% of its 1050 lines are a generic `SelfAnswerFilter`/`attachEnv`
   + transcript-law-absorption theorem.  Also: fuel-with-absorbing-states is
   the wrong recursion; a structural advance/consume split deletes the
   extension/monotonicity lemmas and ~12 copies of match-unfold boilerplate.
4. **Length-mismatch drag** (the gap-#7 root): `hmatch` ×46, `facIO` junk
   branch, three inline mismatch-zero proofs, `hctrAdmissible`'s third
   conjunct, 80 lines of HEq for "URF answers repeats consistently" (a fact
   the paper does not even state).  In-framework fix for §LP: quantify over
   the fiber `w : ∀ i, MsgL (xs i).2.2.1` + one range-adapter lemma.  Full
   fix (dependent-fiber transcripts, `Y : X → Type`) is a next-build
   architecture decision — recorded as debt, NOT part of this migration.
5. **Statement noise** — the environment type + `EnvRespects` spelled 26×,
   `extendedTranscriptDistRep …` 29×, a 4-line filter-card expression ~20×,
   10-line mass predicates ×19, `(hq)(hd)(hLd)(hbin)` threaded through 6
   theorems.  Fixes: `pairMassD/R`, `cq`, type abbrevs, `hbin` becomes a
   `BinEnc` field.
6. **Stale/dead/bypassed** — `revealIndep_eq` (dead, documents an abandoned
   route), `card_sorted_inr_le` (41 lines, zero uses), unused `hLd` in both
   dispatchers, `hctr_omega_slice_le` re-proves the since-promoted
   `deterministicTranscriptDist_functionEvaluator_eq_fTransform` inline,
   `char2_norm` unused at its own six `_eq_iff` call sites, ReductionPack
   `grind` attributes that never fire, twice-pasted 40-line transcript
   dance in §LP (generalize `fixedInputLiftDist_ratio_at`).

### Tactic/automation inventory (feeds §7)

- `char2_iff` macro (`constructor <;> intro h <;> linear_combination
  (norm := char2_norm) h`) — 7 `_eq_iff` proofs become one-liners.
- `sigma_transport` macro (eqRec_eq_cast/cast_heq/Sigma.ext normalizer) —
  kills the ≥5 remaining Σ-extraction dances; pairs with one helper
  `totMsg_ext_of_hash_input`.
- Cell-classifier `match` beats any table-dispatch macro (typecheckable,
  paper-legible); pin-leaf dedup via a lemma family (`RespPinCtx`), NOT a
  macro (macros bake in hypothesis names and fail opaquely).
- Existing `htechnique_fixed_query_pds`/`cr18_fixed_query_pds`/`dist_simp`
  are entirely unused in HCTR2 and cover real hand-rolled rewriting in §LP.
- Route-or-demote: CapReductionPack/ReductionPack `@[simp, grind =]`
  halves that no proof exercises.

### Migration plan — ✅ EXECUTED IN FULL (2026-07-05, commits b246680,
0df6dc5, 41aea2a, cdba720, 0ea4859, a182108, e3354e6; M4's items remain
recorded-only by design).  Outcome: HCTR2.lean 6255 → 5156 lines (−1099);
Derivation.lean +~930 generic lines (sorted-pair union bound, product
factorization, SelfAnswerFilter/attachEnv, TranscriptPrefix.pairs) now
LARGER than the application file; headline statements byte-identical
except two strict strengthenings (hbin absorbed into BinEnc.bin_inj,
hqF dropped from hctr2_securityL_unrestricted via vacuity); axiom
checks clean on both endpoints; every phase committed green.  Original
plan follows for the record.

- **M0 Hygiene** (~½ session, −150 lines, zero risk): delete
  `revealIndep_eq`, `card_sorted_inr_le`, unused `hLd`/`_hL`; route
  `char2_norm`'s own call sites + add `char2_iff`;
  `two_mul_choose_two_int` once (kills 4 hand-rolled ℤ-casts); re-prove
  `hctr_bad_summation` as the tight affine bound (`Nat.choose_le_choose`,
  no certificate); 3-line `cast_mul_inv_le_div`; `cq` abbreviation; hoist
  `lpIO_fst_heq_plain`/`lpIO_snd_heq_cipher`; `dec_reconstruct` from
  `enc_reconstruct` + correctness; `Enc∘Dec` via
  `LeftInverse.rightInverse_of_surjective`; `capRank` via `pairRank`;
  one-clause `totBlock`.
- **M1 Statement surface** (−250): `pairMassD/R` + `pairBadEvent` defs;
  `hbin` moves into `BinEnc`; local type abbrevs; `lp_good_iff`;
  `sum_mul_pred_le` to Counting.
- **M2 Generic engines → Derivation** (the big win; three independent
  sub-commits):
  - **M2a** `mass_sorted_pair_le(_of_embed)` + `DCell`/`RCell` classifiers
    + fiberwise summation → dispatch/counting rebuilt (~1000 lines touched,
    −400).
  - **M2b** `extendedTranscriptDistRep_indep` + fiber-Fubini corollaries →
    both collapse lemmas become ≤10-line corollaries;
    `hctr_respPin_solved_le` + `RespPinCtx` family → six pin consumers
    halve (−350 combined).
  - **M2c** `SelfAnswerFilter`/`attachEnv` (advance/consume recursion) +
    `TranscriptPrefix.pairs` generic → §PointlessWlog reduced to ~300
    instance lines (−730 local, +600 generic); drop `hqF` from
    `hctr2_securityL_unrestricted` via the vacuity case-split (statement
    STRENGTHENS).
- **M3 Mirror merges** (−300): `hashBlk` parametrization of
  MMv/UUv-family; `hctr_io_share_false`; `hctrSides`;
  `hctrConstraints_sound`; §LP `lpUrf_factor_eq` (≤/≥ merge) +
  `lp_prod_image_fiber_eq` + `fixedInputLiftDist_ratio_at`;
  fiber-quantified `w` restatement of §LP internals; `sigma_transport`.
- **M4 Recorded, deliberately NOT executed here**: dependent-fiber
  transcript layer (next-build architecture, eliminates the junk-response
  class by construction); converter-monoid factorization of HCTR2 itself
  (enables `HCTR2[E]` via `maxAdvantage_applyDDC_le`); bit-level messages.

Anti-drift rule for the whole migration: `hctr2_securityL`,
`hctr2_main_lemmaL`, `lpTweakableStrongURP_rnd` statements are pinned;
`hctr2_securityL_unrestricted` may only lose hypotheses.

## 7c. M4 program executed (2026-07-05)

All items recorded as "deliberately NOT executed" in §7b are now DONE
(commits 34eebb7, cc8c724, 6b19a4d, 4631cc1, 952ee01, 146ee93, 9c874b9,
24284ab, ecf42ef).  The original HCTR2 caveat list is fully discharged:

- **HCTR2Computational.lean** (sorry-free): HCTR2 as a step converter over
  the two-sided cipher resource, realization equation, substitution DPI
  Δ(HCTR2[E], HCTR2[Perm]) ≤ Δ(±E, ±Perm), composed paper-p.17 headline
  hctr2_security_computational; also proves the previously-missing CR18
  §4.10.1 links maxAdvantage_triangle + maxAdvantage_filterQueries_le.
- **HCTR2Instance.lean** (sorry-free): GaloisField 2 n + explicit
  polynomial hash at honest degree d = L+τ+2, concrete headline
  hctr2_security_GF with 2ⁿ denominators.  **Soundness-of-meaning gap #8
  found and fixed en route**: HashFamilyL's properties quantified over all
  tail lengths, provably forcing d ≥ |F| for every instance
  (hashFamilyL_card_le_d, kept as record) — now k ≤ L guarded, with
  HashFamilyL taking (L) like BinEnc.
- **§LP fiber quantification** (HCTR2.lean): internals over
  w : ∀ i, MsgL (xs i).2.2.1; hmatch 46→17, junk branch confined to the
  pinned boundary def.
- **DependentTranscript.lean** (sorry-free): the typed transcript layer —
  DTranscriptPrefix, flatten/Coherent/unflatten, comapDomain law
  transport, fiber-respecting oracles' laws supported on coherent
  transcripts, depTranscriptDist endpoint.  E2 (dependent
  envRun/SelfAnswerFilter, HCTR2 retrofit) is a consumer-driven roadmap
  in the file header.
- **HCTR2Bit.lean** (5,692 lines, sorry-free, clean axioms): the paper's
  TRUE arbitrary-bit-length message space — BitVec partial last blocks,
  the leftover reveal (full-last-keystream-block form, fixed reveal
  type), hybrid ideal reveal (a design flaw in the naive dummy reveal
  was caught BY PROOF: the unconditional good ratio is false there),
  bit-level pin engines (dependent-codomain selfloc + fused product
  pin), the full 22+-cell dispatch with the new lastB column, and both
  headlines: hctr2Bit_securityL (filtered) and
  hctr2Bit_securityL_unrestricted (no hqF) at
  (20σ² + qσ + 38σ + 16)/2ⁿ + C(q,2)/2ⁿ — same shape/order as the
  paper, constants documented against the deliberate over-counting
  conventions (always-call, ordered pairs, rank-one charges).

Remaining recorded-only: none from the M-program.  Next candidates live
in the module headers (DependentTranscript E2; HCTR2Bit constant
tightening; upstreaming the UPSTREAM-CANDIDATE atoms).

## 7d. Paper-parity program (P-phases, 2026-07-05) — ✅ COMPLETE (2026-07-09)

**PROGRAM DONE.**  The headline: `HCTR2Paper.hctr2_paper_theorem`
(`RandomSystems/HTechnique/HCTR2Paper.lean`, in the `All` gate, axioms clean)
— the paper p.17 display over the paper's own objects:
`Δ(⌈q⌉ HCTR2[E], ⌈q⌉ ±p̃rp) ≤ Δ(⌈2+q(L+1)⌉ ±E, ⌈2+q(L+1)⌉ ±Perm) +
(3σ² + 2qσ + q² + 7σ + 2)/2¹²⁹` at `σ = q(L+τ+1)`, over
`GF(2¹²⁸) = F₂[x]/(x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1)` with the RFC-8452 POLYVAL hash at
`u = x⁻¹²⁸` — cipher term at `≤ σ+2` queries, `C(q,2)` merged as `q²`;
`t/t′` out of scope (cost model).  Final session (2026-07-08/09, commits
802778f, 0f26703, +P5):

- **P1 C2 (the formerly-STUCK count) PROVEN** (802778f): the P1b4g
  "template-less interlocked unit" verdict was wrong — the per-transcript
  single-charge count `bit_cellWeight_sum_le` decomposes as nine shape
  classes (generic `sum_sorted_capSplit` block split + gated-sum evaluators
  `sum_fin_gate`/`_prod`/`_sorted`) closed by an EXACT slack identity
  `2·(budget − count) = Σ_s DIAG(s) + Σ_{r<s} CROSS(r,s)` with two scalar
  lemmas (`bit_count_diag`, `bit_count_cross`; the cross case is where
  `mʳ ≤ dʳ` pays for the degree asymmetry `|dʳ−dˢ| ≤ (dʳ−aʳ)dˢ + aʳ` that
  defeats separable bounds).  Machine-cross-checked on 20k random configs
  before formalization.  Generic layer: `Counting.lean` gains
  `sq_sum_eq_sum_sq_add_two_mul_sorted`, `sum_sorted_add`,
  `sum_prod_trichotomy`, `sum_sorted_swap`, `mul_pred_add`;
  `Derivation.lean` gains the gated-sum evaluators + `sum_sorted_capSplit`.
  The count needs the length-match on the cipher-degree side (supplied on
  the ideal support via `bitIdeal_zero`).
- **P1 C3 + headline swap** (0f26703): σ-budgeted `bit_col_bound`/
  `bit_bad_bound` (dispatch twins → `expectW` sum-swap → count on support →
  `bitW_le`); `hctr2Bit_main_lemmaL`/`hctr2Bit_securityL[_unrestricted]`
  RESTATED over the `bitNPB` filter at the paper constants
  `(3σB²+2qσB+7σB+2)/(2·|F|) [+ C(q,2)/|F|]`; `hd`/`hLd` hypotheses gone.
  The pre-P1 uniform-cap `20σ²` stack (~800 lines: `bitDBound`/`bitRBound`
  rank-one tables, unconditional dispatches, all-pairs counting) and the
  superseded P1b4c double-charge R table are DELETED.
- **P5** (`HCTR2Paper.lean`): composed from
  `hctr2_security_computational_sigma` (P4) at `F := GF128` (P3),
  `specHashFamily uPolyval` (P2a), + the `C(q,2) → q²` merge; helper
  `specBin_ne_zero` discharges the `hlen` side condition (in-range positive
  indices are nonzero).  Beyond-paper note: the TRUE bit-length theorem at
  the same constants is `hctr2Bit_securityL` (P1); its computational
  composition needs a bit-level converter realization (recorded as future
  work in the file header).

Original program record follows.

Target: ONE theorem identical to paper p.17 over the concrete field.  Gaps
and phases (each: Opus agent, guarded spec, paper-argument-only mandate):

- **P2a (Spec file)**: reconcile specH against paper p.6–7 EXACTLY (trailing
  0ⁿ block, poly() exponent convention, pad(T)) — fix if drifted; variable-
  length tweaks (bin(2|T|+2/3) over any |T|, pad(T)) with Appendix-A
  injectivity formalized AS THE PAPER PROVES IT.
- **P3 (new field file)**: concrete GF(2¹²⁸) = F₂[X]/(x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1)
  via Nat-encoded carry-less arithmetic + Rabin criterion (kernel-computable
  squarings; decide on Nat, never on Polynomial); pin u = x⁻¹²⁸; kill the
  1 ≤ τ hypothesis via the paper's xⁿ ≠ x argument (min-poly degree).
- **P4 (Computational file)**: repeat-cache/dedup lemma (repeats are free
  against function-backed systems), distinct-call count 2 + Σ mˢ for
  hctrStep, RHS filtered at the σₘ-shaped budget; t/t′ declared out of
  scope (header note).
- **P2b (Bit file, after P2a)**: rewire Bit's hash inputs from tweak-slot
  domain separation to the spec's H (first-block length encoding + pad);
  define per-query dˢ = mˢ + tweak blocks.
- **P1 (Bit, after P2b — the hard one)**: σ-accounting.  New filter conjunct
  Σ dˢ ≤ σ; upgrade cell bounds to conditional form mass(E_p) ≤ bound·
  mass(valid_p) (reveal side free via the collapse structure; pin side =
  validity-preserving injection); per-transcript Finset count ≤ paper's
  C(σₘ,2)-shaped table; port M2a exact sorted-pair counting → paper
  constants (3σ²+2qσ+7σ+2)/2ⁿ⁺¹ at the bit level.
- **P5 (composition)**: hctr2_paper_theorem = P1+P2+P3+P4 assembled; paper
  p.17 display with C(q,2) merged as q²/2ⁿ⁺¹.

Waves: 1 = P2a ∥ P3 ∥ P4 (disjoint files); 2 = P2b; 3 = P1; 4 = P5.
Guardrails per agent: verbatim acceptance statements; formalize the PAPER's
argument (ALT-PROOF marker required + discouraged if deviating); DO-NOT
lists (no refactors, no generalization, no upstreaming, no new tactics);
SPEC DEVIATION / STUCK protocol; mechanical evaluator gates.

### 7d.1 CC-linkage integration verdict (2026-07-06, studied post-L3b)

> **Superseded linkage status (2026-07-20).** This section's
> `CarrierPackage`/`probCarrierPackage` landing claim and queued
> `edistD`/`ResPT` integration work describe the deleted typed-carrier
> generation and are non-operative. The warning below not to replace a
> one-directional `Δ` theorem by a symmetric metric statement remains relevant,
> but it is not a carrier receipt. The later heterogeneous
> `RandomSystemsCC.DiscreteSystems` experiment and its bundled compatibility
> dependency were deleted on 2026-07-20. The fixed-signature behavioral
> quotient and selected indexed action remain the live RS-to-AC plan.

The bridge lane (RandomSystemsCC/, other session) has L0–L3b + the L5 CRS
leaf landed sorry-free: a real `CarrierPackage` term (`probCarrierPackage`,
metric axioms inherited with ZERO RS-side proofs), the cumBehav-Equiv
carrier (deliberate deviation from ≡ᵇ, documented), and the exact
translation `edistD = ofReal (max Δ(R,S) Δ(S,R))`.

**Binding decisions for the HCTR2 lane:**
1. **Do NOT consume the inherited triangle in P4/P4c/P5.**  `edistD` is
   symmetric ℝ≥0∞; the paper p.17 display is the signed one-directional Δ.
   Rerouting through the inheritance would CHANGE the pinned statement.
   `maxAdvantage_triangle` stays hand-proved in RS (and
   `maxAdvantage_filterQueries_le` is L4-designated carrier-specific).
2. **P5 is orthogonal to CC vocabulary** — the paper theorem is NOT
   restated through gameSpec/Constructs.
3. Env-side attachment (SelfAnswerFilter) has NO CC counterpart yet —
   the earlier contract-field recommendation stands as linkage-lane work.

**Queued integration items:** post-P5 additive corollary exposing the
HCTR2 headline as an `edistD`/property-transfer statement via the
translation lemma (Fin 1 signature embedding + ResPT membership of the
filtered systems); handoff notes to the linkage lane — add a
`lake build RandomSystemsCC` gate (build health currently ungated) and
consider promoting `verdictProb_congr_cumBehav` into RS core (owner
review; touches Distinguishing/Lemma415 territory).

## 7e. HCTR2 single-file consolidation (2026-07-10) — block-aligned COMPLETE

Marc's consolidation mandate: the paper's H-technique proof (NO CE, NO coupling), ONE
file, CBC-MAC-style minimalism, block-aligned theorem first then bit-level, no scratch
files.  **Part 1 is done**: `RandomSystems/HCTR2.lean` (namespace
`RandomSystems.CR18.HCTR2`, 4,312 lines, 0 sorries, endpoints verify with
`[propext, Classical.choice, Quot.sound]`) replaces the forward-only CE-flavored
scaffold and re-proves, self-contained over the generic `HTechnique/Derivation.lean`
spine:

- `hctr2_security` — filtered (`NP`) advantage vs `±p̃rp` ≤
  `(3σ²+2qσ+7σ+2)/2N + C(q,2)/N`, `σ = q·d` (statement matches the pinned
  `hctr2_securityL` constants);
- `hctr2_security_unrestricted` — same RHS over plain `Adv[q]` (no extra hypotheses);
- `tprp_rnd` — the in-file PRP-RND leg (§3.5/[HR03]), concretized (the old abstract
  §LengthPreserving layer is not replicated);
- `hctr2_main_lemma` — §3.4 via `adv_le_of_extFixedQueryRep_ratio_of_good_filtered`
  at ε = 0 (Layer-3 σ⁺ ratio + Layer-4 sorted-pair bad bound, 22 cells → 4 shapes).

Modeling changes vs the old file (math identical): the non-pointless filter is
`pinnedIO`-based (pinned (plaintext, ciphertext) packaged as Sigma values) — kills the
`facIO`/`lpIO` HEq-transport machinery at three sites (shares_eq 38→6 lines, PRP-RND
filter bridge, WLOG freshness hand-off); fiber-quantified responses (`embV`) replace the
junk-`dite` `facIO`; `hctr_bad_summation` and six dead oracle lemmas not ported.
Compression: PRP-RND 662 vs ~805, Layer-4a 845 vs ~995, WLOG ~371 vs ~469, Layer-4b
1,679 vs ~1,730.  New Lean trap recorded: section `variable`s typed via a
`local notation` silently kill downstream theorems (spell the carrier out).

The old `HTechnique/HCTR2*.lean` estate is UNTOUCHED (it feeds
`HCTR2Computational/Instance/Paper`); retirement decision pending — requires either
migrating those consumers to the new file or keeping both.

**Part 2 (bit-level, same file) — ✅ COMPLETE (2026-07-10, same day).**
`RandomSystems/HCTR2.lean` is now 12,390 lines, **ZERO sorries file-wide**; all seven
endpoints verify with `[propext, Classical.choice, Quot.sound]`:
`hctr2_security(_unrestricted)`, `tprp_rnd`, `hctr2_main_lemma` (block-aligned) and
`hctr2Bit_main_lemma`, `hctr2Bit_security(_unrestricted)` (bit level, at the paper's
σ-accounted constants `(3σB²+2qσB+7σB+2)/2N + C(q,2)/N` under the `bitNPB` filter,
plus the beyond-paper unrestricted form under a universal σ-budget).  One-engine
outcome: generic PRP-RND leg (`Leg.tprp_rnd`) + generic reveal-collapse spine
(`Leg.revealCollapseZ_le`/`pairMassZ_le_of_reveal`/`omegaSliceZ_le`, reveal-type
generic) instantiated by both parts; Part 1's rank plumbing reused at `L+2`;
`bit_shares_eq`/`bit_input_fresh_NP` replace the oracle's `facIO`/HEq transports
(the `pinnedIO` filter redesign pays off at six sites total across both parts).
Genuinely bit-specific and faithfully transplanted from `HCTR2Bit.lean` with
per-lemma oracle citations (zero STUCK across five transplant phases): the hybrid
ideal reveal, the `lastB` column, the fused/virtual pin engines, and the σ-budgeted
nine-class count.  Deferred polish items: (i) re-derive the block-aligned headlines
from the general engine at `r = 0` (carrier-equivalence transport for `BitVec 0`)
and delete Part 1's concrete Layer-3/4 twins; (ii) basename-shadowing sweep
(`NP` vs `Leg.NP` etc.); (iii) old-estate retirement (needs the
`HCTR2Computational/Instance/Paper` consumers migrated or kept).

*(Original in-progress plan follows for the record.)*
No black-box bit→block reduction exists (leftover reveal is load-bearing; the ideals
don't align), so the bit math is proven — but as ONE engine, not a parallel stack:
the bit development over `bitMsg F ℓ r = F × (Fin ℓ → F) × BitVec r` IS the general
case (`r = 0` = block-aligned shadow).  Done so far: the PRP-RND leg re-generalized
in place (`Leg.tprp_rnd` over any fiber family; endpoints byte-identical; +143
lines) and B1 (bit model, `BlockBits`/`HashFamilyS`/`bitNPB` filter over the generic
`Leg.NP`, construction + correctness, pinned headline statements at the oracle's
σ-accounted constants; `hctr2Bit_security` PROVEN from the sorried main lemma +
the free `bit_tprp_rnd` leg instantiation).  Remaining: bit engine port (extraction
+ hybrid-ideal reveal + Layer 3; shapes/pins; σ-accounted dispatch + count; main
lemma; WLOG) — oracle `HCTR2Bit.lean` :1465 onward — then optionally re-derive the
block-aligned headlines from the general engine at `r = 0` (needs a small
carrier-equivalence transport; until then Part 1's concrete layers stay).

## 7f. HCTR2 elegance pass (2026-07-11) — dead-code purge, one-engine, upstreaming

Executed against the 12,390-line consolidated file; every phase built green.

- **Dead-code purge (−1,939 lines, two verified sweeps).**  A whole orphaned
  generation of plain bit leaves (`bit_pairD/R_*`, `bit_lastB_*` at the old
  9256–10038) plus its transitively-dead engines (`bit_respPin_le`,
  `bit_virtualPin_le`, `_solved` forms, `uniform_pi_selfloc_dep_le`,
  `uniform_pi_prod_selfloc_fused_le`), the `revealLastB_*` family, superseded
  reveal bounds with their `_sharp` orphans, and second-order orphans (the
  uniform-multiplicity `of_no_share`/`collision`/`const` chain, non-`wexp`
  collapse adapters, `mass_le_of_fiber_snd_cond`).  Method: declaration-block
  parser + zero-reference verification (comments stripped), iterated to
  convergence, then a roots-based reachability sweep (endpoints + attributed
  decls + instances as roots).  Deliberately kept: `HashFamilyS.uniform_prop1/2/3`
  (the "sharp honestly refines uniform" consistency theorem, unreferenced).
- **One-engine for real.**  Part 1's reveal-collapse spine (`idealTr_vanish`,
  `revealCollapse_le`, `pairMass_le_of_reveal`, `omega_slice_le`, `admissible`)
  was a verbatim copy of the generic `Leg` spine; now five one-line
  instantiations at `Z := F × F`, exactly like the bit level.
- **Twin-family parameterizations.**  (a) The bit no-share reveal bound is one
  parameterized lemma `revealBitHashBlk_of_no_share_le` (mass-0 diagonal proven
  once; the sharp bound is a 2-line instance).  (b) The `_ks_le` σ-cell leaves
  lost their repeated `expectW_indicator_const` + `bitIdealExtH_mass`
  slice-transport preamble to two wrapper engines `bit_virtualPin_ks_le` /
  `bit_respPin_ks_le` (`expectW`-form conclusions; 10 call sites).  (c) The
  senc/sdec arms inlined in `bit_cell_D_cond_le`/`bit_cell_R_cond_le'` are now
  named leaves (`bit_pairD_MM_MM_{senc,sdec}_cond_le`,
  `bit_pairR_UU_UU_sdec_cond_le`), symmetric with the already-named senc leaf.
  REJECTED with cause: merging Part 1's four senc/sdec pair twins over a
  direction `Bool` (each mirrors a distinct quoted paper sentence; the bundle
  abstraction costs ≈ its savings and hides the Fig-4/5 correspondence);
  merging `uniform_pi_selfloc_slice_le` with the fused engine (different
  theorems — per-fiber `c ≤ card` injection vs fixed-`V` equiv tiling; a merge
  needs `c ∣ card`, unavailable).
- **Upstreaming (−1,364 lines from the leaf).**  The generic tweakable-PRP leg
  (worlds, `pinnedIO` filter, `Leg.tprp_rnd`, reveal-collapse spine, 803 lines)
  → new `HTechnique/TweakablePRP.lean` (namespace `RandomSystems.CR18`,
  inner `TweakablePRP` — renamed from the jargon `Leg` 2026-07-11; 40 internals stay `private`, now enforced by the module
  boundary; API = `NP`/`pinnedIO`/worlds/`tprp_rnd`/`BadTr`/
  `good_ratio_transcript`/`prp_rnd_bad_bound` + the `Z`-generic collapse
  spine).  The uniform pin/self-locating engines, `expectW` functional,
  conditional fiber bounds, indicator algebra, and `Fin` counting helpers
  (20 decls, 533 lines) → `Derivation.lean` §MassToolbox.  BitVec
  `Fintype`/cardinality/`setWidth` facts → new `RandomSystems/BitVecFacts.lean`
  (mathlib-PR candidates; `bitVecEquivFin` deleted in favor of mathlib's
  `BitVec.equivFin`).  `QueryDir.eq_inv_of_ne_fwd` → `StrongPRP.lean`.
- **Automation verdicts (§7 protocol).**  Minted `hctr2_ite_arith` (the §7.2
  blessed case-grid closer; 3 sites).  Mathlib reuse: `sigma_mk_injective`
  replaces `eq_of_heq (Sigma.mk.inj h).2` at 2 of 4 sites (the other 2 have
  explicit-`have`-type elaboration that mis-infers the index family — left
  explicit).  LEFT with cause: the 51 `dCellOf`/`rCellOf` grid sites (each
  fires branch-specific `if_pos`/`if_neg` flags — the §7.2-blessed explicit
  style; a uniform tactic would re-split settled cases); the 4
  direction-split one-liners (already minimal); the membership normalizer
  (pattern extinct after the purge); sweeping bare `ring`/`omega` onto
  `cr18_algebra`/`cr18_arith!` (single-word closers — zero elegance gain).
- **Net effect (pre-estate-retirement):** `HCTR2.lean` 12,390 → ~9,070 lines
  with ~1,400 of the removed lines now reusable upstream; headline endpoints
  and constants unchanged.

### 7f.1 Old-estate retirement — ✅ COMPLETE (2026-07-11)

The §7e deferred item (iii) is done: `HTechnique/HCTR2.lean` (5,159) and
`HCTR2Bit.lean` (9,374) are **deleted**; all four consumers migrated onto the
consolidated file (import `RandomSystems.HCTR2`, drop the `…L` suffixes,
`lpTweakableStrongURP → tprp` / `lpUrf → rnd` / `lpNonPointless → NP`,
`TotMsg (hctrMsgL F) → Sigma (Msg F)`).  Per-consumer notes:

- `HCTR2Computational` — pure renames; the ideal world in
  `hctr2_security_computational[_sigma]` is respelled `tprp` (definitionally
  the same construction; MIGRATION NOTE in its header).  Constants unchanged.
- `HCTR2Instance` — renames + a `badBudget/sigmaBlocks` unfold in the
  `hctr2_security_GF` tail; statement unchanged (`σ = q·(L+τ+2)`).
- `HCTR2Spec` — `HashFamilyLS → HashFamilyS` (field-shape identical);
  its duplicated `padBlockBits` block (~48 lines) deleted in favor of the
  consolidated exports; local 2-line `bitVecEquivFin` kept (the `gBits`
  `BitVec.ofFin` defeq; mathlib's `BitVec.equivFin` has a different shape).
- `HCTR2Paper` — renames only; **`hctr2_paper_theorem` at the exact p.17
  constants over GF(2¹²⁸)**.
- `All.lean` drops the old import; `audit_surface.py` updated (traverses the
  `RandomSystems.HCTR2` hub; `wip_exempt` allowlist now EMPTY;
  `TweakablePRP.lean` exempted from the no-private scan as consolidated-core
  support, rationale in-file).

Gates: `lake build RandomSystems` green (8,440 jobs), `HTechnique.All` green,
`htechniqueSurfaceAudit` passes, and all endpoints (`hctr2_security[_unrestricted]`,
`hctr2Bit_security[_unrestricted]`, `hctr2_security_computational[_sigma]`,
`hctr2_security_GF`, `hctr2_security_spec`, `hctr2_paper_theorem`) verify with
`[propext, Classical.choice, Quot.sound]`.  **Net repo delta ≈ −16,400 Lean
lines** for the whole elegance pass; everything remains uncommitted by request.

### 7f.2 One model, one paper file, paper-1:1 theorem surface (2026-07-11)

Marc's fluff hunt ("why several files? why so many theorems?") executed:

- **`Leg` renamed `TweakablePRP`** (namespace + module file, ~250 refs; the
  jargon never had sign-off).  `TweakablePRP.lean`/`BitVecFacts.lean` ruled
  KEEP as separate infrastructure (Marc, 2026-07-11).
- **One paper file.**  `HCTR2Computational/Instance/Spec/Paper` merged into a
  single `HTechnique/HCTR2Paper.lean` (2,220 lines, four namespace parts);
  intermediate security theorems privatized; POLYVAL ε-AXU lemmas stay public
  (reusable library).  The three source files deleted.
- **The chain moved to the bit model** (the paper's true message space).  New
  bit converter accounting: per query of class `(ℓ, r)` the construction makes
  `4 + ℓ` cipher calls (incl. the always-issued partial-block XCTR call at
  `r = 0`), distinct-call cap **unchanged at `2 + q(L+1)`**; σ **= `q(L+τ+1)`,
  paper-exact**; side condition `2(τ·128)+3 < 2¹²⁸`.
  `hctr2_paper_theorem` is now stated over `bitMsgL` at GF(2¹²⁸)+POLYVAL.

- **PAPER-EXACT HASH MODEL + σ (DONE 2026-07-11, "real model for injectivity").**
  Replaced the invented `bitLenBlock` encoding: the abstract `HashFamily`/`HashFamilyS`
  now hash the paper's **structured** tail `BitTailS := Σ ℓ, (Fin ℓ → F) × Option F`
  (the `ℓ` full blocks and, only when unaligned, one `10*`-padded partial block —
  `hashTailB`/`msgHashTail` repackaged, `none`/`some` = the alignment), with `prop1'/2'/3'`
  over DISTINCT `(tweak, tail)` pairs and honest `degB t mˢ = mˢ + ⌈|T|/n⌉ = dˢ`
  (`bitMsgDeg`, `bitTailDegLen`, `mˢ = 1 + ℓ + (r≠0 ? 1 : 0)`).  Deleted: `bitLenBlock`,
  the old flat `hashTailB`/`msgHashTail` (`Fin (ℓ+2) → F`), the `polyvalHf` flat inhabitant.
  Reproved: the reveal diagonal (`revealBitHashBlk_of_no_share_le` over `T × BitTailS`),
  `hashTailB_sigma_inj` (via `padBlock_r_inj`), the 5 sharp reveal bounds, and the whole
  spec realization (`specBlockV`/`specHashFamilyV`/`VS`) via the ALREADY-proven App.-A
  `specH_input_inj` mode-block/parity injectivity — new `specBlockV_sigma_inj`,
  `specBlockV_head_ne` (needs the `bin(2|T|+3) ≠ 0` twin `hlenV3`, discharged by
  `specBin_ne_zero`).  Two ledgers stay separate: the reveal's fork-free cipher count
  `mBlocksBit = ℓ + 2 ≥ 2` (density σₘ, `bit_count_core`'s `2 ≤ mˢ` minimum) is UNTOUCHED;
  only the hash-degree ledger (`bitMsgDeg` green cells, `twBlocks = τ`, `bitD`, `bitNPB`)
  moved to `dˢ`.  `hctr2_paper_theorem` now at σ = `q(L+τ+1)` with per-query `dˢ` at every
  `r > 0` query; the `r = 0` budget stays `dˢ + 1` because the fork-free reveal keeps
  `mˢ = ℓ + 2` (the honest `mˢ = ℓ + 1` there would give a 1-block message with `mˢ = 1`,
  which `bit_count_core`'s `2 ≤ mˢ` forbids — the ONE remaining margin, structural not
  invented).  0 sorries; `hctr2Bit_security_unrestricted` + `hctr2_paper_theorem` axiom-clean
  `[propext, Classical.choice, Quot.sound]`; surface audit passes.
- **Part 1 (block-aligned) DELETED** — the shadow model's four endpoints,
  worlds, and concrete Layer-3/4 (~3,400 lines; two script sweeps + a
  closure-based shell rewrite).  What survives of it is the shared interface:
  `BinEnc`, `HashFamily`, `capRank` rank plumbing (used by the bit dispatch at
  cap `L+2`), `pickFresh`.  `HCTR2.lean` is now **5,684 lines** (was 12,390),
  bit model only; script lesson recorded: one-line `@[attr] theorem` blocks
  and anonymous instances dodge the block parser — closure-verify plus manual
  shell pass needed at the end.
- **Theorem surface now paper-1:1** (public): `hctr2Bit_main_lemma` (§3.4),
  `TweakablePRP.tprp_rnd`/`bit_tprp_rnd` (§3.5), `hctr2Bit_security` (the
  paper's statement under its §3.4 standing assumption),
  `hctr2Bit_security_unrestricted` (assumption discharged, beyond paper),
  `hctr2_paper_theorem` (p. 17).  Gates: full build 8,440 jobs green, audit
  passes, both headline endpoints `[propext, Classical.choice, Quot.sound]`.
  HCTR2 estate total: 5,684 + 2,220 + 848 + 48 ≈ **8,800 lines** (was
  ≈ 29,600 at session start).  Uncommitted (Marc commits).

## 8. Open work

> **Scope note (2026-07-27).**  This section predates the RS↔AC bridge program
> and covers the *pure random-systems* surface only.  For bridge, AC/CC and
> source-layer work read **§11** — it is the live ledger, and where §8 and §11
> disagree §11 wins.  Item 5 below ("everything is uncommitted") is obsolete:
> the tree is committed on local `main` and nothing is pushed.

1. **System-views unification U1–U5** (`DESIGN.md` §3) — designed, not
   implemented; U2 (behavior ↔ observational) is the only substantial proof.
1b. **H-technique re-derivation + extended transcripts** (`DESIGN.md` §9) —
   IMPLEMENTED in `RandomSystems/HTechnique/Derivation.lean` (namespace
   `RandomSystems.CR18.HTechniqueDerivation`, in the `All` gate):
   good-transcript factorization transfer, weight side condition, the
   adaptive H-technique in ratio / equality-on-good / expectation / perfect
   forms, extension-as-data extended-transcript forms, the (★) identity
   (`statDist_deterministicTranscriptDist_eq_sum_fixedQuery_gap`, with named
   `sysFactor`/`envFactor`), and the σ⁺ fixed-query refinement
   (`extSysFactor`, `extendedDeterministicTranscriptDist` — event-mass
   construction, no pushforward needed — projection/weight laws,
   `envFactor_fixedQueryDDE` indicator, extended Layer-B transfer,
   `adv_le_of_extFixedQuery_ratio_of_good`), the fundamental-theorem lower
   bound (Layer F: `lawStatDist`, transcript DPI, `Adv ≤ Δ_q`
   `adaptiveTranscriptAdvantage_le_lawDelta`, coupling bound
   `adaptiveTranscriptAdvantage_le_mass_ne`), and the generalized
   partition H-lemma (Layer D′: `hTechnique_partition`,
   `adv_le_of_fixedQuery_partition`, good/bad recovered as the two-cell
   case via `hTechnique_ratio_via_partition`), and stress-test applications
   (Layer G): the adaptive PRF/PRP switching lemma both directions
   (`urf_urp_switching` via the perfect no-bad form + new `urp` bridges
   `urp_eq_functionEvaluator`/`urp_KStepTotal`/`perm_eval_ratio`;
   `urp_urf_switching` via `adaptiveTranscriptAdvantage_symm`), the
   fixed-query switching bound, and hash-then-PRF composed with it
   (`hashThenPRF_vs_urp`).  The PRP/PRF direction is proved **directly**
   with bad transcripts (`Collision`, `sysFactor_urp_eq_zero_of_collision`,
   good-ratio `urf_le_urp_fixedQuery_of_good` at ε = 0, and the **adaptive
   birthday bound** `probBad_urf_collision_le` — obtained from the
   switching ratio itself via `Pr_urp[Collision] = 0`, no freshness
   recursion); the symmetry route remains as a remark. The Thm 2.31
   attainment direction is now complete separately in
   `RandomSystems/BoundedAttainment.lean` (see 1e). Note: the first switching lemma on the
   adaptive-advantage surface — SecurityDefs `advPRF`/`advPRP` corollaries
   are now one-liners when wanted.
1c. **Environment duality chart** (`DESIGN.md` §3a) — IMPLEMENTED in
   `Derivation.lean` (Layer A′): `chooser`/`ofChooser`, round-trip
   `chooser_ofChooser`, agreement `ofChooser_chooser_agree`, transcript-law
   transport `deterministicTranscriptLaw_congr_of_agree` (chooser = complete
   invariant), and
   `adaptiveTranscriptAdvantage_eq_boundedAdaptiveTranscriptAdvantage`
   (environment supremum = chooser supremum, upgrading the old one-way
   comparison to equality).  Optional `X × dual-system` split not done.
1e. **Thm 2.31 attainment direction** (`DESIGN.md` §9 plan) -- COMPLETE
   on the current CR18 surface: law-level successors, finite-answer
   reassembly, the Lemma 2.33 cross-query joint, the bounded common-domain
   induction, class-distance equality, and normalized coupling are proved.
   The unrelated pre-migration `Legacy.FundamentalTheorem` admission remains
   quarantined and has no role in the selected surface.
1d. **Converter algebra follow-ups** (`DESIGN.md` §10.4–10.7).
   DONE 2026-07-02 second pass: the ν-level realization theorem
   (`ProtocolRealization.lean`: `apply_toDDC`, the `[q]` instance
   `applyNu_queryLimitFn`/`apply_toDDC_queryLimitFn`, and
   `queryLimit_apply_eq_toDDC` retiring bespoke `[q]` trace proofs) and the
   honest cascade equation (`CascadeRealization.lean`: `apply_cascadeStep :
   DDC.apply (ofStep cascadeStep) (cascadeAccess S T) = S ⊲ₚ T`).
   Remaining: (i) DONE fourth pass (`toNu_toDDC : toNu (toDDC ν) =
   normalize ν`); fixed-arity ν's for `simple`/`feedback` as `apply_toDDC`
   instances still open; (ii) DONE fourth pass (`apply_combineStep`,
   CombineRealization.lean; the `rfl` equations kept with docstrings
   pointing at the honest theorems); (ii-b) DONE fifth pass: serial
   ν-composition (`ComposeRealization.lean`, 1016 lines, `sorry`-free):
   `compNu ν₂ ν₁` + **`applyNu_compNu : applyNu (compNu ν₂ ν₁) S = applyNu
   ν₂ (applyNu ν₁ S).1`** and its Def 3.9 surface form `apply_toDDC_compNu`
   — the monoid action law, unconditional (strict semantics needs no
   totality/bound hypotheses); three-level `CompRun` bisimulation per
   DESIGN §10.7 closing note; (iii) DONE third pass: converter DPI via
   absorption (`AbsorbDPI.lean`, `maxAdvantage_applyDDC_le`; ν-general
   version over `applyNu` when a cross-round-memory application needs it);
   (iv) the
   consistency-indicator factorization on the H-technique surface;
   (v) `attachAt () = DDC.apply` under `unitResourceEquiv`; (vi) a lenient
   (`Option Y`) ν variant — only when an application needs it.
2. **Legacy retirement** — per the map in §4, gated on downstream (Phase 6,
   external) and on U4 for the final mathematical justification.
3. **attic/ decision** — restore-and-repair or delete (owner's call).
4. **Legacy sorries** (§5) — fix or explicitly wontfix before any claim that
   the *legacy* tree is complete (the new surface does not depend on them).
5. ~~**Everything is uncommitted**~~ — OBSOLETE (2026-07-27).  The tree is
   committed on local `main`; nothing is pushed.  Workflow: commit freely to
   local `main`, squash into a clean commit before anything goes out.

## 9. Consolidation record

2026-07-02: this file and `DESIGN.md` replaced `BLUEPRINT.md`,
`PROOF_GAPS.md`, `LITERATURE_CASCADE_PRF.md`, `LEMMA_SEARCH_RESULTS.md`,
`design/` (5 files + `next-gen/` 4 files), `RandomSystems/HTechnique/`
ledgers (7 files), and `attic/README.md`.  Proof expositions moved to
`papers/notes/` (`LM20_ORBIT_PROOF.md`, `CBCMAC_{STRUCTURE,ANALYSIS,VERIFICATION}.md`).
All removed content is recoverable from git history.

## 10. CC-first symmetric-construction exercise program (2026-07-23)

The binding design is `DESIGN.md` §11.  This program replaces the rejected
distribution-first attempt in the sibling `ccprover/Examples` tree.  That
attempt is not a construction surface and is not evidence for completion; it
has been left untouched pending the object-and-statement replacement.

The execution order is strict.  At most one item below is active.  Every
object-and-statement gate must pass before any proof task begins.  As requested,
all occurrences of “PRF” in this program are modeled by an ideal URF resource;
there is no computational PRF layer.

- [x] D0: check the source PDFs and current `TypedFinite`, AC, CC, adaptive
  H-technique, metric, and CBC application surfaces; freeze `DESIGN.md` §11.
- [x] S1: define the common channel model and all OTP objects; elaborate the
  final `otp_securely_constructs` header with an honestly incomplete proof.
- [x] S1b: define the indexed fresh-pad OTP source and target over abstract
  finite `X`, with a shared uniform table `X → G`, partial one-submission-per-
  index domains, genuine converters, and the final
  `fresh_otp_securely_constructs` header.
- [x] S2: define the affine one-time MAC objects; elaborate the final
  `affine_one_time_mac_securely_constructs` header.
- [x] S3: define the bounded URF-MAC objects; elaborate the final
  `bounded_urf_mac_securely_constructs` header.
- [x] S4: define the generic UHF/short-URF and polynomial-UHF objects;
  elaborate both long-URF construction headers.
- [x] S5: define the staged UHF/URF/MAC objects; elaborate the generic and
  polynomial-UHF bounded-MAC construction headers.
- [x] S6: define the shared MAC-to-OTP staged objects; elaborate the generic
  and concrete secure-channel composition headers.
- [x] G0: validate the complete statement surface for all six exercises and
  the indexed fresh-pad extension:
  symbolic parameters only, named endpoints, explicit budgets, source
  accounting, no embedding plumbing, no standalone security endpoints, no
  speculative helpers, and no non-foundational axioms.
### Proof-obligation ledger

This is the binding leaf-task list for the 13 admitted construction endpoints.
A theorem checkbox closes only when every child is closed and its focused
build, admission scan, and endpoint axiom audit pass.

Proof-layer rule: each endpoint uses the smallest RS behavioral receipt and
immediately upcasts it to `Phi`.  Availability, simulation, composition, and
error accounting are discharged in AC/CC.  Unfolding the general attachment
driver inside an endpoint or rebuilding an end-to-end RS game is a wrong-layer
implementation.

> **STALE — do not plan against the E01 tree below.**  E01 is **CLOSED**
> (2026-07-26; see §11.3 A2).  When A1 landed the generic action calculus it
> silently closed leaves 2b.3b.iv/v, 2c, 2d, 3, 4 and 5; only 3c and 3d were
> genuinely open, and both are now proved.  The tree is retained as a record of
> the decomposition, which E02–E04 follow.  **Read the live goal with
> `lean_goal` before trusting any leaf list in this file** — that is the lesson,
> not a remark about this one tree.

- [x] E01 `otp_securely_constructs` — **CLOSED**
  - [x] E01.1 establish the minimal typed-action/upcast coherence receipts for
    `otpProtocol`, `bottom`, and `simulatorProtocol`;
  - [ ] E01.2 prove the simulated-security equality directly in `Phi`; its
    sole RS kernel is the uniform additive reindexing for the complete
    one-message behavior, including pre-submission Bob/Eve queries;
    - [x] E01.2a use the typed action receipts to put both sides in the same
      post-protocol boundary fibre;
    - [ ] E01.2b discharge the one deterministic converter-coherence fact
      for the two-query encrypt/decrypt path and the one-query simulator;
      - [x] E01.2b.1 establish the exact typed `ofFunctions` attachment
        coherence seam locally and file its reusable promotion as U01.  The
        receipt is necessarily stated after application to a tag-faithful
        typed resource: raw trace equality with a global `simpleFn` is false
        on malformed, wrong-tag answers;
      - [x] E01.2b.2 instantiate that receipt for `simulator` as
        `simulator_attach_eq`;
      - [ ] E01.2b.3 use `apply_ofStep_eq_applyG` for the two-query
        `encrypt`/`decrypt` path and identify the resulting post-protocol DDS;
        - [x] E01.2b.3a define only the fixed-key intermediate post-decryption
          DDS and the exact honest-boundary final DDS required by the action;
        - [ ] E01.2b.3b normalize the Bob frame after application to
          `(realDDS key).flatten`, using the resource-aware U07 shape and
          `apply_ofStep_eq_applyG decryptStep`;
          - [x] E01.2b.3b.i prove the exact one-round `decrypt_driveG_eq`
            receipt for Alice, Bob, Eve, admitted, and rejected histories;
          - [x] E01.2b.3b.ii lift the receipt to fixed-fuel whole histories
            (`decrypt_driveOuter_eq`) and file the missing generic fuel
            normalization as U09;
          - [x] E01.2b.3b.iii hide fuel and identify the global step
            application exactly with `(postDecryptDDS key).flatten`
            (`decrypt_applyG_eq`);
          - [ ] E01.2b.3b.iv prove the resource-aware framed/global
            application equality (the construction-local U07 instance);
          - [ ] E01.2b.3b.v conclude `decrypt_attach_eq` through
            `flatten_attach_eq_apply_framed`;
        - [ ] E01.2b.3c normalize the Alice frame on that intermediate DDS,
          using `apply_ofStep_eq_applyG encryptStep`, and identify the final
          DDS with `realSecurityDDS key` across
          `security_boundaries_agree`;
        - [ ] E01.2b.3d lift the pointwise deterministic receipt through
          `Dist.fTransform`/the uniform law to discharge the sole remaining
          local `honestLaw` obligation in `otp_securely_constructs`;
    - [x] E01.2c prove equality for every strict observation by the
      observation-dependent uniform translation; before Alice submits the
      translation is the identity, and after submission it is
      `key ↦ message + key`;
    - [x] E01.2d upcast that strict behavioral equality through the typed
      quotient to the displayed equality in `Phi`;
  - [x] E01.3 derive availability from E01.2 in `Phi`, using honest/Eve
    commutation and the simulator-then-`blockRealEve` definition of `bottom`;
    no second end-to-end RS proof is permitted;
  - [x] E01.4 exhibit `simulatorProtocol` and prove
    `simulatorProtocol ∈ otpSimulators`;
  - [x] E01.5 assemble the two `CC.SecurelyConstructs` clauses at error zero
    from the `Phi` equalities;
  - [ ] E01.6 run the focused build and remove the endpoint `sorry`;
  - [ ] E01.7 run the admission scan and endpoint axiom audit.
- [ ] E02 `fresh_otp_securely_constructs`
  - [ ] E02.1 normalize indexed encryption/decryption against the partial
    one-submission-per-index real domain;
  - [ ] E02.2 normalize the indexed simulator and both Eve blockers;
  - [ ] E02.3 prove availability;
  - [ ] E02.4 prove `simulatorProtocol ∈ freshOtpSimulators`;
  - [ ] E02.5 reindex the uniform real pad table pointwise by the unique
    submitted message at each index and prove complete behavioral equality;
  - [ ] E02.6 assemble the zero-error CC judgment;
  - [ ] E02.7 run the focused build, admission scan, and axiom audit.
- [ ] E03 `affine_one_time_mac_securely_constructs`
  - [ ] E03.1 normalize signing, verification, simulator, and blocker
    attachments against their partial one-message resources;
  - [ ] E03.2 prove availability and
    `simulatorProtocol ∈ affineMacSimulators`;
  - [ ] E03.3 couple the honest `(message, tag)` transcript exactly;
  - [ ] E03.4 show a fresh replacement is accepted only under the unique
    affine-key constraint and bound it by `1 / Fintype.card F`;
  - [ ] E03.5 assemble the CC clauses and run the endpoint gates.
- [ ] E04 `bounded_urf_mac_securely_constructs`
  - [ ] E04.1 normalize signing, verification, simulator, and blockers for
    the `q`-delivery/one-replacement domains;
  - [ ] E04.2 prove availability and
    `simulatorProtocol ∈ boundedUrfMacSimulators`;
  - [ ] E04.3 couple every admitted honest signing delivery;
  - [ ] E04.4 isolate the fresh URF value at the sole replacement attempt
    and prove the `1 / Fintype.card T` bound;
  - [ ] E04.5 assemble the CC clauses and run the endpoint gates.
- [ ] E05 `uhf_then_urf_constructs_long_urf`
  - [ ] E05.1 normalize the hash-then-oracle converter action on the typed
    `Q`-bounded source;
  - [ ] E05.2 identify the resulting adaptive transcript with the existing
    H-technique real object and the target with its long-URF object;
  - [ ] E05.3 transport `Hf.eps` through the adaptive collision bound to
    `Nat.choose Q 2 * Hf.eps`;
  - [ ] E05.4 close the `ApproximatelyConstructs` metric obligation and run
    the endpoint gates.
- [ ] E06 `polynomial_hash_then_urf_constructs_long_urf`
  - [ ] E06.1 instantiate E05 with `polynomialHash`;
  - [ ] E06.2 prove the length-separated polynomial collision bound
    `ell / Fintype.card F` over the abstract finite field;
  - [ ] E06.3 rewrite the inherited construction radius to the displayed
    endpoint and run the endpoint gates.
- [ ] E07 `uhf_urf_mac_securely_constructs`
  - [ ] E07.1 prove the shared-carrier boundary/resource identification
    between E05's long URF target and E04's MAC source;
  - [ ] E07.2 prove the honest/adversarial converter commutations required by
    `CC.SecurelyConstructs.trans`;
  - [ ] E07.3 compose E05 and E04 and normalize protocol multiplication;
  - [ ] E07.4 rewrite the additive radius and run the endpoint gates.
- [ ] E08 `polynomial_uhf_urf_mac_securely_constructs`
  - [ ] E08.1 instantiate E07 using E06's polynomial receipt;
  - [ ] E08.2 normalize the displayed polynomial protocol and resource names;
  - [ ] E08.3 rewrite the inherited radius and run the endpoint gates.
- [ ] E09 `mac_then_otp_securely_constructs`
  - [ ] E09.1 prove the zero-error OTP-stage construction from
    `authenticatedWithOtpKeyResource` to `secureChannelResource`;
  - [ ] E09.2 prove the distinct-interface commutations required by
    `CC.SecurelyConstructs.trans`;
  - [ ] E09.3 compose the supplied `hmac` with E09.1;
  - [ ] E09.4 normalize `macThenOtpProtocol`, simplify `εmac + 0`, and run the
    endpoint gates.
- [ ] E10 `affine_mac_with_otp_key_securely_constructs`
  - [ ] E10.1 transport E03's affine proof to the shared staged carrier while
    preserving the independent OTP-pad capability;
  - [ ] E10.2 identify the source/target names and protocols exactly;
  - [ ] E10.3 run the endpoint gates.
- [ ] E11 `affine_mac_then_otp_securely_constructs`
  - [ ] E11.1 instantiate E09 with E10;
  - [ ] E11.2 normalize the one-message resources, protocol, and radius;
  - [ ] E11.3 run the endpoint gates.
- [ ] E12 `polynomial_urf_mac_with_otp_key_securely_constructs`
  - [ ] E12.1 transport E08's polynomial MAC proof to the shared staged
    carrier while preserving all `q` independent pads;
  - [ ] E12.2 identify the source/target names, protocol, and displayed bound;
  - [ ] E12.3 run the endpoint gates.
- [ ] E13 `polynomial_urf_mac_then_otp_securely_constructs`
  - [ ] E13.1 instantiate E09 with E12;
  - [ ] E13.2 normalize the `q`-message resources, protocol, and radius;
  - [ ] E13.3 run the endpoint gates.

Global completion additionally requires the cumulative symmetric build, zero
remaining admissions in `RandomSystemsCC/Symmetric`, the statement-surface
audit, and axiom-clean verification of all 13 endpoints.

### Upstream helper candidates exposed by the proof program

**Status 2026-07-26 (A1): U01–U04 and U06–U09 are PROMOTED and the private OTP
originals deleted.  U05 alone remains — its obstruction is structural, not
mathematical; see §11.3 item #20.**  Where a description below disagrees with
the promoted theorem, the theorem wins; these paragraphs are the design intent
that produced it, not its specification.

- [x] U01 typed simple-attachment coherence: when a
  `DeterministicConverter.ofFunctions query answer` is attached at one
  interface, expose its native domain/output equation (equivalently, identify
  the canonical framed application with the global one-query simple
  converter *after application to a flattened tag-faithful dependent DDS*).
  Do not state this as raw `ProtocolFn.TraceEquiv`: the frame rejects
  wrong-tag answers while an unguarded global `simpleFn` accepts them.
  `OTP.lean` now carries the exact private target
  `simulator_attach_eq`; its proof should instantiate this reusable receipt
  once it is prepared for `TypedAttachment`/`TypedFraming`.  The same helper
  is consumed by the OTP, fresh-OTP, affine MAC, bounded-URF-MAC,
  UHF/URF-MAC, and MAC-to-OTP simulators and blockers.
- [x] U02 successful-driver reachability: promote the construction-independent
  private theorem `OTP.drive_result_reachable` to `ProtocolRealization`.  From an
  initial `PFunConverter.Reach protocol (queries, answers)` and a successful
  `drive protocol system ...` result, expose both reachability of
  `(queries, result.2.2)` and membership of `Sum.inr result.1` at that final
  state.  The OTP-specific tag invariant must remain outside this theorem.
- [x] U03 invariant-indexed application congruence: add a generic
  `ProtocolRealization` induction principle for two protocol functions that
  agree on reachable states satisfying an invariant, where resource
  completions preserve that invariant.  Its conclusion should be equality
  only after application to the resource, not raw `TraceEquiv`.  The private
  OTP chain `simulator_drive_mem_iff` /
  `simulator_driveOuter_mem_iff` / `simulator_apply_eq_framed` is the concrete
  witness and fixes the required hypotheses.
- [x] U04 strict-flattened equivalence upcast: promote the private
  `OTP.ofProb_eq_of_flatten_equivalent` to `TypedFramingMetric`.  If two
  normalized dependent laws have `StrictContext.Equivalent` flattened laws,
  their `DependentRandomSystem.ofProb` classes are equal.  The proof is the
  direct `Experiment.accept_mass_eq_to_flatten_test` quotient lift; callers
  should not repeat that quotient plumbing.
- [ ] U05 CR18-to-strict equivalence bridge: promote the private
  `OTP.strict_equivalent_of_equivalent` beside `StrictContextAdvantage`.
  For normalized laws, CR18 transcript `Equivalent` implies
  `StrictContext.Equivalent`; the proof completes each strict test with
  rejection and uses the existing maximal-advantage comparison at zero.
- [x] U06 kept-prefix monotonicity: promote the private
  `OTP.keptPrefix_mono` to `PFunDDS`.  If `left <+: right`, then scanning CR18
  completion inputs preserves
  `keptPrefix system left <+: keptPrefix system right`.  The proof is the
  generic append/fold invariant and is independent of OTP.
- [x] U07 framed `ofStep` application coherence: for a typed converter whose
  local protocol is `ProtocolFn.ofStep step count`, expose the corresponding
  all-interface step application after applying the canonical frame to a
  tag-faithful flattened dependent DDS.  As with U01, this must be a
  resource-aware theorem, not raw trace equivalence.  E01.2b.3 needs its
  two-call instances for `encryptStep` and `decryptStep`; E02 and E05 consume
  the same theorem for their bounded step converters.
- [x] U08 admitted dependent-flatten evaluation: promote the private
  `OTP.flatten_apply_eq_some` to `TypedResource`.  Evaluating
  `system.flatten` on `history ∈ system.domain` should expose the tagged
  dependent `system.output` directly, with the active interface obtained from
  `history.getLast`.  Converter receipts should not repeatedly descend through
  proof-dependent `Part.get` terms merely to recover the native resource
  answer.
- [x] U09 bounded causal-driver fuel normalization: promote the private
  `OTP.driveG_mem_at_count_succ` and
  `OTP.driveOuter_mem_at_uniform_count_succ` to `CausalApply` (or the
  step-realization layer).  If `step` issues an inner query exactly while
  `answers.length < count query`, every terminating round already terminates
  at fuel `count query + 1`; a uniform bound on `count` gives the analogous
  whole-history result.  This is the missing bridge from a fixed-fuel
  construction receipt to fuel-free `applyG`, and is independent of OTP.

S1 is complete: `RandomSystemsCC/Symmetric/{ChannelModel,OTPModel,OTP}.lean`
defines the typed ports, staged resources, genuine two-query converters,
protocol, availability filter, Eve-supported simulator class, and the final
zero-error construction header.  During E01 proof integration the focused
build passes with two tracked admissions: the construction-local U07
framed/global application seam and the final construction proof.  The
pre-integration statement baseline had only the latter, whose axiom audit was
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.  No standalone OTP
ciphertext-law theorem or auxiliary probability/equality lemma was added.
The first P1 proof reduction found an S1 semantic bug: the supposed
one-message source and target were total history evaluators, so they admitted
multiple Alice submissions and retained the latest one.  Both resources now
have genuinely partial `[1]` domains: key reads and Bob/Eve observations do
not consume the budget, while a history containing a second Alice submission
is undefined.  Nothing is committed or silently ignored.  The ideal DDS
again samples a manifestly message-independent ciphertext; the eventual
endpoint proof must obtain real/ideal equality by uniform additive
reindexing.  The focused OTP and full symmetric umbrella were revalidated
after this domain correction and remain green.  The remaining P1 kernel is
the explicit typed-attachment normalization in P1.1 above; protocol
restriction and Eve-supported simulator membership have already been checked
to reduce without additional mathematical assumptions.
S1b is complete:
`RandomSystemsCC/Symmetric/{FreshOTPModel,FreshOTP}.lean` defines an indexed
authenticated-channel source with a shared URF-style pad table `X → G`, the
matching indexed secure target, actual encryption/decryption converters, the
Eve simulator, availability, and the final zero-error construction header.
Each index admits at most one Alice submission; a second submission at the
same index is outside the partial domain, while pad reads and observations
remain available.  Uniform sampling of the whole table gives independent
uniform outputs at distinct fresh indices and consistent output on repeats.
The focused build passes; the only local admission is the deliberately
deferred final construction proof.
S2 is complete:
`RandomSystemsCC/Symmetric/{AffineOneTimeMACModel,AffineOneTimeMAC}.lean`
models a uniform affine key over an arbitrary finite field, one honest
message/tag payload, one Eve replacement attempt, the authenticated target,
the real signing/verification converters, and the final `1 / |F|` CC
construction header.  Its focused build passes and its only admission is that
final proof, with the same expected foundational-plus-`sorryAx` audit.
S3 is complete:
`RandomSystemsCC/Symmetric/{BoundedURFMACModel,BoundedURFMAC}.lean`
models abstract finite nonempty message/tag spaces, a source-owned uniform
function, the first `q` honest payloads, one replacement attempt, matching
authenticated target and simulator transcript, and the final `1 / |T|`
construction header.  Its focused build and admission/axiom audits pass.
S4 is complete:
`RandomSystemsCC/Symmetric/{UHFThenURFModel,UHFThenURF}.lean` defines a
single bundled key/short-oracle source port, the genuine two-query
hash-then-oracle converter, `Q`-bounded source and long-URF target resources,
and the generic `choose(Q,2)·ε` endpoint.  It also fixes a length-indexed
bounded-vector message type and terminal-coefficient polynomial encoding over
an arbitrary finite field, with the unconditional
`choose(Q,2)·ell/|F|` endpoint.  Both headers elaborate as
`ApproximatelyConstructs`; the only local admissions are their two deferred
final proofs, and both axiom audits have the expected footprint.
S5 is complete:
`RandomSystemsCC/Symmetric/{UHFURFMACModel,UHFURFMAC}.lean` supplies the
required common staged carrier (short keyed oracle, long oracle, authenticated
channel), actual Alice/Bob hash converters, signing/verification converters,
all three named resources, availability/simulator objects, and serial protocol.
The generic bound is `choose(q+1,2)·ε + 1/|T|`; the unconditional polynomial
bound is `choose(q+1,2)·ell/|F| + 1/|T|`.  Both final CC headers build, are the
only local admissions, and pass the expected axiom/source-surface audit.
S6 is complete:
`RandomSystemsCC/Symmetric/{MACThenOTPModel,MACThenOTP}.lean` defines the
insecure/authenticated/secure staged boundaries, preserves a MAC secret and
independent OTP pads, and bundles the MAC, OTP, simulator, and availability
protocols.  It states the generic composition receipt plus assumption-free
affine and polynomial-UHF/URF MAC-stage and end-to-end secure-channel
receipts.  The affine endpoint is one-time; the `q`-message polynomial endpoint
uses independent pads rather than reusing one OTP key.  All five S6
construction headers elaborate; they are the only local admissions and the
audited end-to-end endpoints have the expected axiom footprint.
G0 is complete.  `RandomSystemsCC/Symmetric/All.lean` exports the suite and
`lake build RandomSystemsCC.Symmetric.All` passes.  The frozen statement
surface has exactly 13 public construction theorem declarations.  Before E01
proof integration it had exactly 13 deliberately deferred final construction
proofs; the current E01 work-in-progress temporarily adds the separately
tracked U07 seam above, with zero `admit` or declared `axiom` occurrences.
Extracted theorem headers contain no `Pi.mulSingle`, `Gamma.ofPrimitive`,
`protocolOfPrimitive`, raw `.act`, `statDist`, `Adv`, `Delta`, concrete small
field, or `ZMod` plumbing.  Every endpoint audit reports only `propext`,
`Classical.choice`, `Quot.sound`, and the expected temporary `sorryAx`.
The broader `lake build RandomSystemsCC` currently stops at the pre-existing
user worktree error in `RandomSystems/HTechnique/Derivation.lean:317`; the
focused symmetric gate is green and that unrelated file was not changed here.
Standalone forger-mass, fixed-query transcript, and concrete-small-field
theorems are not accepted deliverables for this program.

## 11. RS ↔ AC bridge audit program (2026-07-25)

Audit of `AbstractCrypto`/`CC` and `RandomSystemsCC` against the sources and
against AC's own integration receipts (`../abstract-crypto/LIBRARY_GUIDE.md`
§9).  Verdict: the abstract layers are sound, cited, and admission-free; the
**bridge** is where every gap is.  The gaps are overwhelmingly *wiring* gaps —
the mathematics they need is already proved in this repository and is simply
not installed as an instance.

### 11.0 Measured baseline (re-measure before claiming progress)

**Current, 2026-07-27** — `lake build RandomSystems` green (8337 jobs);
`RandomSystemsCC` green; `htechniqueSurfaceAudit`, `ccSurfaceAudit` and
`ccCheck` all exit 0; bridge admissions **13** (down from 15), 39 derived
public endpoints.  **Fourteen of the twenty-six ledger lines below are
closed** (G1 is split into a landed phase 1 and an open phase 2).  Receipt 7 (parallel) is met on `ResourceLift`; receipt 8 is
partially met with its missing theorem named.  The open architectural item is
§11.4: the converter monoid should be syntactic, not extensional.  The three that change what the library can *do*: approximate
constructions compose (C1/C2), a construction can be stated without descending
through fuel and framing (A1), and a security *guarantee* crosses rather than
only a distance (D3).

*Session-start snapshot, kept because it is what the gaps were measured
against:*

* ~~`lake build RandomSystems` **FAILS** at `HTechnique/Derivation.lean:317`~~
  — **FIXED 2026-07-25 (B1).**  The step was `simpa [transcriptDist] using h`
  after `rw [← transcriptDist_ofDDE, ← transcriptDist_ofDDE]`; because
  `transcriptDist_ofDDE` is a *global* `@[simp]` lemma (`PDS.lean:2755`) the
  `simp` re-applied it and undid both rewrites.  The goal was already the
  hypothesis, so the fix is `exact h`.  Recorded as `DESIGN.md` §4 item 10.
* ~~`lake run htechniqueSurfaceAudit` **FAILS**~~ — **FIXED 2026-07-25 (B1).**
  A second red gate, independent of the build and not previously recorded:
  `audit_surface.py`'s `BRIDGE_STATEMENT_FILES` allow-list named four modules
  (`Instantiated.lean`, `FixedSignature/{Serial,TwoInterface}.lean`,
  `FrostInstantiation.lean`) that the bridge consolidation deleted, so the gate
  had been failing — and therefore going unread — since §10.9's restructuring,
  while `AGENTS.md` still advertised it.  The list is now the live consumers
  (`LiftingExample.lean`, `Frost.lean`, `Frost/{Instantiation,EndToEnd,Reduction}.lean`)
  and the audit now **fails loudly if a sanctioned entry stops existing**, so it
  cannot rot silently again.  Lesson for every gate in this repo: an allow-list
  keyed on paths needs an existence check, or it decays into noise.
* `RandomSystemsCC.Symmetric` builds with **14 admissions** over 13 public
  endpoints (all of §10's E01–E13) plus the tracked U07 seam.
  → now 13; the U07 seam and E01 are closed (A1, A2).
* `AbstractCrypto`, `CC`, `CC.MPC`: zero `sorry`, zero declared `axiom`.
  → still true, and now also of `AbstractCrypto/ChoiceSettings.lean` (X2).
* `AbstractCrypto.Par` has **no instance on any concrete carrier** in either
  repository.  → STILL TRUE; P1 is open, and is now cheaper than estimated
  because its one open item is moot on the strict carrier.
* `AbstractCrypto.DistinguisherClass` is **never constructed** — it occurs
  only as a `variable`.  → FIXED (D1), and now consumed by property transfer
  (D3).
* `ResourceLift`'s `CompatibleConverter`/`CompatiblePrimitive`/
  `CompatibleProtocol` have **no instances**, so the only non-expanding
  protocol monoid on that carrier is unreachable.  → RESOLVED by deletion
  (C1): non-expansion is structural on the strict quotient.
* `.lake/build` is entirely stale against the working tree.  → rebuilt.

### 11.1 Receipt scoreboard (LIBRARY_GUIDE §9)

Updated 2026-07-26; changes from the session-start audit in **bold**.

| # | Receipt | `TypedFinite` | `ResourceLift` |
|---|---|---|---|
| 1 | fixed-signature behavioral quotient | yes (`TypedAction.lean:393`) | **yes** — fibre is `StrictContext.System` (C1) |
| 2 | converter quotient, exact monoid laws | yes (extensional `Gamma`) | partial (`DDConverter` + `PFunConverter.comp`) |
| 3 | total action on the quotient | yes | yes |
| 4 | applicability + output-signature preservation | **yes at word level** — `outCode` / `WellPlaced` (C3b) | **yes** — placement named by `liftProbAt`, overlap pinned (C3a) |
| 5 | pseudo-emetric + zero-distance policy | yes, separated (`:601`) | **yes, separated** (C1) |
| 6 | action non-expansion | yes (`TypedFinite.lean:157`) | **yes, for the full `IsDDC` class** (C1) |
| 7 | typed parallel routing / congruence / non-expansion | **no `Par` — and the recorded reason is STALE (see §11.10)** | yes — `Par`, `IsNonexpandingPar`, `SMulParClass` (P1), **used by nothing** |
| 8 | feasible subcarriers + cost closure | no (D2 open) | no |
| — | lifting instances (guide §9 addendum) | exact only (N1 open) | **AC-native**; the bespoke notation is gone |
| — | distinguisher class | **built + non-vacuous** (D1) | n/a |
| — | property transfer | **worked end-to-end** (D3) | n/a |

Receipt 6 is what unblocked ε-composition: `Constructs.eball_trans` now applies
on `ResourceLift`, and `cbc_urp_randomness_expander` is the receipt that it
does.  Receipt 7 remains the largest single gap.

### 11.2 Standing acceptance gates (every task below)

A task closes only when **all** of these pass and the diff has been read:

1. focused `lake build` of the touched modules **and** the downstream gate
   (`RandomSystems`, `RandomSystemsCC.Symmetric.All`, or `RandomSystemsCC.CBC`
   as applicable) is green;
2. `sorry`/`admit`/declared-`axiom` count strictly decreases or is unchanged,
   with every remaining one named and justified in this file;
3. `#print axioms` on each touched public endpoint reports only `propext`,
   `Classical.choice`, `Quot.sound`;
4. no new `maxHeartbeats`, `maxRecDepth`, or `native_decide`; no widening of a
   global `simp` set; no proof witness added to typeclass search;
5. statement surface: no `Pi.mulSingle`, `Gamma.ofPrimitive`,
   `protocolOfPrimitive`, raw `.act`, `statDist`, `Adv`, `Delta`, or `ZMod`
   plumbing in a public header; §1 theorem-naming rule respected;
6. **non-vacuity**: a new definition or instance is accompanied by a witness
   that it is not degenerate (an empty distinguisher-test set, an identity
   action on a mismatched code, or a `⊤` radius all make downstream theorems
   true and worthless);
7. any claim attributed to a source is checked in the original PDF, not in
   `papers/notes/` or an OCR text;
8. no new top-level document — this file, `DESIGN.md`, and `README.md` only.
9. **update these docs in the same change that makes them wrong.**  A stale doc
   is worse than a missing one: it silently misdirects the next reader.  Two
   real costs this program has already paid — `audit_surface.py`'s allow-list
   named four modules the bridge consolidation had deleted, so that gate sat
   red and unread for weeks; and §10's E01 leaf tree was planned against after
   A1 had already closed six of its leaves.  When a claim here is superseded,
   strike it and say what replaced it rather than deleting it silently: the
   superseded reasoning is usually why the current design is what it is (see
   DESIGN §10.10's retained account of the Δ-carrier).  Before planning against
   any leaf list in this file, read the live goal with `lean_goal`.

### 11.3 Ledger

Task ids are the session task list.  Ordering is by dependency, not priority.

- [x] **B1** (#1) fixed `Derivation.lean:317` (`exact h`), fixed the stale
  `audit_surface.py` bridge allow-list and made a missing sanctioned entry a
  loud failure, and recorded the policy as `DESIGN.md` §4 item 10.  Gates run:
  `lake build RandomSystems` (8336 jobs), `RandomSystems.HTechnique.All`
  (8324), `RandomSystems.HTechnique.LegacyChecks` (8342) — all green;
  `htechniqueSurfaceAudit` green and verified to still reject an injected
  token; no new admissions.
- [x] **B2** (#2) `RandomSystemsCC/audit_surface.py` + `audit_baseline.json`,
  driven by `lake run ccSurfaceAudit` (syntactic, no build) and
  `lake run ccCheck` (focused builds + per-endpoint `#print axioms`).  Add both
  to `AGENTS.md`'s quick-gates line.  Five gates: admissions (with enclosing
  declaration and `private` flag), §11.2-rule-5 statement surface, performance
  escapes, endpoint axiom footprints, JSON summary; exit 1 on regression, exit 2
  on "no regression but incomplete" (an unavailable axiom audit is explicitly
  *not* a pass).  Two design points worth keeping: baseline keys are
  `module::declaration::token`, never `file:line`, so the baseline survives
  reformatting and still catches a `sorry` that moved to a different theorem;
  and the scanner strips comments/strings first, without which `Frost/Group.lean`'s
  prose mentions of "axiom"/"sorry" read as admissions.  Endpoints are *derived*
  (a public theorem whose statement mentions a construction judgment), not
  hand-listed.  Regression detection verified independently on the real tree.
  Corrections to §11.0's baseline, from the tool: total admissions are **15**
  (14 `sorry` + the allow-listed `secp256k1_q_prime`), and 0 `admit`; the 14
  line numbers first recorded here were the enclosing *declaration* lines (what
  the build warning reports), not the `sorry` lines — the tool prints both;
  `OTP.lean:2570` is the **private** U07 seam, so the count is 13 public
  endpoints + 1 private seam; `secp256k1_q_prime` appears in **no** endpoint
  footprint (it is reachable only through a `Fact` instance no endpoint
  consumes); and there are **29** public construction endpoints under
  `RandomSystemsCC`, of which **16 are already axiom-clean** — now a
  machine-checked fact rather than an assumption.
  One defect found in review and fixed: `SURFACE_EXEMPT_FILES` had no existence
  check, i.e. the same rot that had killed the sibling H-technique gate (and #6
  will plausibly rename `TypedFinite.lean`).  A missing exempt module is now its
  own labelled failure; verified it fires and that the gate returns to green.
- [x] **C1** (#3) fibre moved to `StrictContext.System`; `IsNonexpandingSMul`
  installed for the full `IsDDC` class; the `Δ` bridge kept as the **sound `≤`
  only** (`edist_liftProb_le_advantage`) — there is deliberately no
  `edist = ofReal Δ` lemma, and the two-way iffs became one-way
  `constructs_*_of_advantage`, whose converse is false here and which nothing
  consumed.  Compatible subclass DELETED (zero instances anywhere; its purpose
  is now filled structurally).  **The cheap alternative was ruled out on
  mathematical grounds**: non-expansion on the Δ-carrier needs
  `maxAdvantage_apply_le` without `Emulable`, and `not_emulable_probeFn`
  refutes that.  Second root cause found beyond the original diagnosis: two
  defeq-but-syntactically-different `SMul ↥(Protocol U)` paths (bespoke
  `MulAction.compHom` vs mathlib's `Submonoid.smul`), invisible without
  `pp.explicit` — see DESIGN §10.10's trap note.
- [x] **C2** (#4) `cbc_urp_randomness_expander` —
  `P —[θ_r * (CBC * [r]); r²/(2|X|) + r²/(2|X|)]→ θ_r * Vₙ`, i.e. CBC-MAC over
  a uniform random **permutation** at Theorem 6.1's own protocol, by
  `Constructs.eball_trans` from two named legs.  Proof body has **zero**
  transcript or probability reasoning — that is the standing wrong-layer test.
- [x] **C3** (#5) both halves landed.  *(b)* the silent-identity mismatch action
  (`c09c419`): `ConverterTerm.outCode` / `WellPlaced` make placement a syntactic
  judgment on **words**, with `boundary_eval_of_outCode` and six regressions
  pinning word-level dropout.  *(a)* the `HasResourceCode` overlap —
  **and here the "diamond bug" premise did not survive checking.**
  - Deleting the `priority := 1100` instance is not available: a `DDConverter`
    action recovers its source and target codes *through* these instances, so
    deletion kills the whole `θ * …` / `CBC * …` converter algebra, not merely
    the coercion.  Tried it; three CBC sites failed on
    `HMul (DDConverter M X M X) (Resource X M)`.
  - Measured (not argued) what the overlap actually does: at `M = X` the head
    `HasResourceCode (interfaces Bool Bool) Bool Bool` resolves to
    `variableInputFunction`, and resolution is deterministic and cached per
    head — so **every** occurrence collapses together.  The statement is the
    same mathematics under the other of two labels for one signature, **not a
    false statement**.  Sound, but silently relabelling.
  - Landed instead: `liftProbAt` (reducible alias for `liftProb` at an explicit
    instance, so all `liftProb` simp lemmas still fire), `CBCMAC.liftVIF`, the
    three `cbc_*_randomness_expander` statement boundaries switched to explicit
    placement, and two regressions — `liftProbAt_roundFunction_ne_liftVIF`
    (placement is *observable*, which is why it must be pinned) and
    `overlap_resolves_to_variableInputFunction` (a priority change is now a
    compile error, not a silent move).  Rule recorded as DESIGN §4 item 13.
- [ ] **C4** (#6) unify the two carriers; `TypedUnitMetric.lean` has the
  charts.  `ResourceLift.Resource` has no interface index, so no CC judgment
  can ever live there — that asymmetry is the reason the estate has two.
- [x] **P1** (#7) installed on `ResourceLift`: `Par (Resource U)`,
  `IsNonexpandingPar`, `ParProtocol U` (syntactic), `SMulParClass`, plus
  `HasSumCode` (with `sumCode_inj` — required, not decoration) and
  `RandomSystems/StrictParallel.lean` (~2750 lines).  Worked example applies
  `Constructs.eball_par_resource` on the carrier.
  **My premise "this is wiring, not research" was WRONG, in three ways that
  matter more than the code:**
  1. after C1 moved the fibre, eq. (3) for `Δ` **does not transfer** — the
     strict metric satisfies only `maxEDist ≤ ofReal Δ`, one-way — and CR18
     transcript congruence does not descend to the coarser strict quotient.
     Strict par-non-expansion and par-congruence were genuinely NEW theorems.
  2. **`IsDDC (PFunConverter.par α β)` is FALSE in general.**  The tagged par
     converter drops untagged `⊥`s and mis-tagged answers in its `filterMap`
     projections, so a component re-issues its query forever at reachable junk
     pairs and `AnswersWithin` fails for *every* bound.  Any design routing the
     parallel action through the raw par converter is dead on arrival.  The
     honest replacement is "parallel with a fixed deterministic component" as
     genuine `IsDDC` converters, with realization theorems.
  3. **`Par` on an EXTENSIONAL converter monoid is ill-posed in principle** —
     see §11.4.  `Emulable (par α β)` was indeed moot on the strict carrier, as
     predicted.
- [ ] **P2** (#8) **premise check DONE — E09 never needed `Par`; my scoping was
  wrong.**  Verified: `macThenOtpProtocol tag = otpProtocol * macProtocol tag`
  (`MACThenOTP.lean:255`), so the endpoint is pure serial composition via
  `SecurelyConstructs.trans` over the extensional `Gamma` we already have.  P1
  was never a blocker.  What actually remains: the OTP-stage leg at error zero
  on the *staged* carrier (a real construction proof, but the same shape as
  A2's landed encrypt/decrypt U07 instantiations plus the ambient-chart
  boundary transport), the `trans` commutation premise (Eve-supported
  simulators versus honest-supported protocol), and `εmac + 0`.  If the four
  downstream endpoints in the same file then follow, admissions go 13 → 8.
  §11.1 rule 2 still stands for `TypedFinite` models until #21 lands.
- [x] **D1** (#9) `RandomSystemsCC/TypedDistinguisher.lean` — `strictTestClass`
  over the RS strict observations, plus `boundedStrictTestClass q` via
  `truncDDD`.  States the honest relations rather than an assumed equality:
  `edistD ≤ edist`, equality on a fixed boundary, and **strict** inequality
  across boundaries (distinct boundaries sit at `⊤`, which no `[0,1]`-valued
  test can see).  Non-vacuity PROVED in `TypedDistinguisherChecks.lean`:
  `edistD = 1` exactly, for the full class and the `q = 2` subclass.
- [x] **D2** (#10) `RandomSystemsCC/TypedFeasibility.lean` — cost-bounded test
  subcarrier (`callsTo`, `CallsWithin`, `costBoundedTests`,
  `costBoundedStrictTestClass`), the budget/asymptotic boundary
  (`reductionRelaxation` membership, `PolyBoundedCost` + `Negligible`), and a
  tightness receipt.  Non-vacuity is two-sided: the D1 probe is certified at an
  explicit budget, and a **starved-interface coupling** exhibits a test that is
  in `strictTests` but in NO class with `calls c 1 = 0`.
  **Honest negative, and the more valuable half:** graded cost closure is
  provable only for the NEUTRAL converter.  The general case needs a *counting*
  version of context absorption — re-presenting `absorb (testOfTruncDDD q d) γ`
  as a truncated reader with composed per-interface counts.  The estate has
  absorption without counting at three layers and a streak bound published
  ∃-only.  Receipt 8 is therefore **partially met**, and the missing piece is
  one named theorem rather than a vague gap.  Also confirmed: the RS cost layer
  is machine-model-free by design, so the only cost coordinates definable for a
  strict test are query-based — consistent with LIBRARY_GUIDE §4's refusal to
  supply a machine model.
- [x] **D3** (#11) `RandomSystemsCC/TypedPropertyTransfer.lean` —
  `unforgeability_transfer : edistD real ideal ≤ ε → ∀ t ∈ unforgeabilityTests,
  1 - ε ≤ t real`, plus the `gameSpec`/`GateHierarchy` route.  The real content
  is `forgery_win_test_eq_win_prob` / `unforgeability_test_eq_not_won_prob`: an
  RS game-winning probability **is** an admitted AC test value.  Non-vacuity is
  two-sided — a concrete forger, the ideal satisfying the defining test, and a
  degenerate forgeable resource failing it at value exactly 1.
- [x] **A1** (#12) eight of the nine §10 helpers promoted: U08
  `flatten_apply_eq_some`; U01 `flatten_attach_ofFunctions`; U07
  `flatten_attach_ofStep` (+ the `apply_framed_*` forms); U09 the fuel-free
  `applyG` bridge; U02/U03 in `ProtocolRealization`; U06 `keptPrefix_mono`;
  U04 in `TypedFramingMetric`.  **The tracked U07 seam is closed** and
  `OTP.lean` fell 3075 → 1768 lines as the private originals were deleted and
  rewired.  U01/U07 are stated as equalities **after application to a
  tag-faithful resource**, never as raw `TraceEquiv` — the four branch
  hypotheses are exactly what makes them true, which is why the earlier
  trace-level attempts were wrong.  U05 not promoted; see #20.
- [x] **A2** (#13) `otp_securely_constructs` — the first fully-proven CC
  construction on this carrier, at error **zero**, both worlds named.  Two
  shapes E02–E04 reuse: the encrypt-side U07 instantiation (asymmetric to
  decrypt — the *second* inner query carries the submission weight, so the key
  read can be admitted while the send is rejected) and the ambient-chart
  boundary transport for the propositional boundary equality.
- [ ] **N1** (#14) notation: approximate-construction lifting for bare
  converters, `Prob → Phi` coercion, the `—[·; ·]→` glyph collision between
  `ResourceLift.lean:760` and `Relaxations.lean:590`, and specification-level
  (not just resource-level) construction statements.
- [x] **N2** (#15) `rs_construct`/`rs_compose`/`rs_simulator`/`rs_availability`
  and the `rs.construction.*` controlled sentences, in
  `RandomSystemsCC/TypedConstruct.lean` with the usability gate
  `RandomSystemsCC/TypedConstructChecks.lean`.  The CNL layer now expresses
  construction assembly as well as the proof technique; see §11.34.
- [x] **X1** (#16) `ConstructiveCrypto/*` assessed.  **Correction to the
  audit's first reading:** the tree is not silently duplicated dead weight — it
  is *already retired*, explicitly and reversibly (every import in
  `ConstructiveCrypto.lean` commented out since 2026-07-18 under a RETIRED
  header, the `ResourceTheory/` subtree deleted, and its `lean_lib` globs only
  the theory-free root, so the target builds no theory).  Verified directly.
  What survives is a real gap, now task #18: `CCAlgebra.theorem2Full` is a
  *faithful* MauRen11 Theorem 2 — the Def 8–11/18 choice-setting, actual choice
  domains and complete-factorizable-relation layer, plus the p.16 proof objects
  — and the selected surface has only the choice-free specialization, so no
  concrete carrier can reach Theorem 2.  Do not retire the tree until #18 lands.
  `LIBRARY_GUIDE.md` §3 now records this status; the stale
  `ConstructiveCrypto/ResourceTheory/*` links in
  `sequence-hash/sketches/A4-indiff-prf.md` are repointed or marked historical.
- [x] **X2** (#18) MauRen11 Theorem 2 ported to the selected contract and
  **proved** (`AbstractCrypto/ChoiceSettings.lean`, axiom-clean).  Statement-first:
  the statements were reviewed before any proof, and the review found a simpler
  proof than the sketch — factoring both tuples through a common *leftmost* γ
  removes the commutation step the choice-free version needs, so
  `patternAttach_mul`, `commute_patternAttach_supportedOn` and `supportedOn`
  appear nowhere.  Promoted `patternAttach_apply_of_mem`/`_of_notMem` to
  `CryptographicAlgebra` on the way.  Wired and instantiated by X3.
- [x] **U2** (#17) CR18 §3.6 behavior/transcript characterization — **it was
  already proven; this entry was stale.**
  `RandomSystems.CR18.behavior_equivalent_iff_transcript_equivalent`
  (`RandomSystem.lean:640`) gives `ObservableBehaviorEq ↔ Equivalent` for
  normalized PDS, axiom-clean and already in the root gate via
  `BoundedAttainment`.  The CR18-vs-Lanzenberger discrepancy is documented at
  the definition: CR18 Def 3.18/3.20 makes behavior a sequence of *normalized
  conditional* distributions, partial at probability-zero conditioning events,
  where the Lean rendering uses **unnormalized cumulative masses on the `s⊥`
  view** — total, same information, and the docstring exhibits a two-mixture
  counterexample showing the successful-history kernel alone is insufficient
  for partial systems.  CR18 also omits Lemma 3.2's proof; our converse is a
  reconstruction via the fixed-query environment.  Per the standing decision
  the chain rests on Lanzenberger Def 2.17 / Lemma 2.18, not on the lecture
  note's phrasing.
- [x] **X3** (#19) Theorem 2 wired into the AC root and **instantiated at
  `TypedFinite`** (`RandomSystemsCC/ChoiceSettingsExample.lean`) with the
  premise **discharged from a real behavioral fact** — `flip • flip • R = R`,
  double output negation is trace-invisible — not assumed.  Non-vacuity: the
  concrete real/ideal pair is *provably distinct* by a one-query strict test,
  so the abstraction is not reflexivity in disguise.  LIBRARY_GUIDE §1/§2/§3
  and `abstract-crypto/AGENTS.md` corrected; `ConstructiveCrypto/*` retired
  after an audit, with `IndexedResourceAlgebra` and `CCAlgebra.OutBound`
  recorded as out-of-scope with git-history pointers.
  Carrier finding worth keeping: the receipt uses a one-code signature so all
  boundaries are DEFINITIONALLY equal; on a multi-code signature the same
  premise additionally needs propositional boundary transport (`HEq`), as OTP
  paid.  That is friction in `replaceBoundary`'s typing — see §11.4.
- [x] **G1** (#21 phase 1) **`TypedFinite.Gamma` de-quotiented** — now
  `Quotient (ConverterTerm.setoid i)`, converter words modulo the SERIAL laws
  only, i.e. MauRen11's syntactic Γ.  `mrange_gammaInclusion_eq_generatedConverterMonoid`
  proves the interpretation's range is exactly the old extensional monoid, so
  nothing was lost.  Scope held exactly as measured: three files, one 2-line
  proof repair; `Symmetric/**` and `Frost/**` never edited, so the 13 endpoint
  statements are unchanged *by construction*.  The probe's key null result:
  **zero genuine action-vs-equality conflations existed downstream** — the
  quotient was never buying anything.
- [x] **G1b** (#21 phase 2) **`ResourceLift.Protocol` de-quotiented** — now
  `Quotient (ConverterTerm.setoid U)`, converter words modulo the SERIAL laws
  only, interpreted by `protocolInclusion` into `nonexpandingEnd (Resource U)`.
  `mrange_protocolInclusion_eq_generatedConverterMonoid` proves the range is
  exactly the old extensional monoid (kept as `generatedConverterMonoid`), so
  nothing was lost.  **Zero downstream repairs**: two files edited, no proof in
  the tree changed, `CBC.lean` never opened; the four CBC endpoints' elaborated
  types and axiom footprints are byte-identical before/after.  `ParProtocol`
  was **not** folded in and still claims no non-expansion (§11.5: par-act
  non-expansion is false); the estate's only `SMulParClass` is untouched
  (§11.29).  No extensional converter monoid remains in the estate.
- [x] **TA** (#22) totalization/quotient audit done — six rows, **no new tasks**,
  and two results worth more than the table.  (1) Row 4, totalized attachment,
  is **refuted as a defect with a reason**: its guard is code-determined and
  unequal codes sit at `⊤`, so the default branch is constant on every
  finite-radius ball — yielding the general **criterion** now in §11.4, which
  turns DESIGN §4 item 11 from a prohibition into a test.  (2) A **new and worse
  defect**: `ConverterTerm.mul` constrains nothing, so a word can silently drop
  a factor and produce a substantive theorem with a **lying protocol label** —
  folded into C3 (#5), whose fix must now operate on words.  No sixth
  totalization exists; the only one open is the `s⊥` completion (#28).
- [ ] **DOC** (#23) promote `papers/ThesisJost.pdf` to a PRIMARY source in
  `DESIGN.md` §1 (it is newer and more rigorous than CR18 on exactly the points
  we keep deciding), and record two trap notes: MauRen11 fn. 23 versus any
  extensional Γ, and `IsDDC (par α β)` being false.
- [ ] **R1b** (#24) resources-as-packages: promote `scratchpad/ResourceMachine.lean`
  (ready, green, zero admissions), add `domain_eq_of_invariant` and
  **`toDDS_eq_of_bisim`** (the state-coupling lemma — the one piece here that
  touches the *proof* side, natural in the machine presentation and impossible
  to state in the fold presentation), then the `resource` macro.  Acceptance is
  the content:generated ratio (§11.8), and the macro must **error on
  non-exhaustive clauses, never default** — a default would be the fifth
  totalization.
- [ ] **CODE** (#25) evaluate collapsing the `Code`/`Boundary` indirection:
  default `Code := Iface` with the identity boundary, exposing the
  code-changing form only where a converter changes a signature.  Motivated
  independently by the DSL prelude (§11.8) and by the `HEq`/`sumCode` tax
  (§11.4) — the same defect seen from two directions.  Assess against §11.4's
  four totalization rows *before* building on it; this is a carrier change, not
  a syntax change.
- [ ] **S1** (#26) **replace the single-simulator `CC.SecurelyConstructs`** with
  the general specification form.  Three of the five sources point the same
  way: LiuMau20 p. 8 calls the single-simulator type "too restrictive" and
  attributes it to "the early version of CC", citing Jost–Maurer 2020 for
  impossibilities the general view circumvents; MR16 §8 says "simulators should
  probably only appear in proofs, not in definitions"; MauRen11 App. C.1 notes
  UC's single simulator makes it "in a strict sense a special case" for n ≥ 3,
  its own Theorem 2 using *local* per-interface simulators.  We already have the
  general form (`Relaxation.star` + `constructs_of_simulator`), so this is a
  change of which form is primary.  Measure the blast radius first (13 Symmetric
  endpoints + FROST) and verify the cited impossibility bites for *our* carrier.
- [ ] **SY1** (#27) **synchrony**: LiuMau20's Def 4 resources consume a complete
  input list per invocation, which silently forbids rushing; its r.a/r.b
  semi-round split restores it.  Our `DependentDDS` answers one query at a time
  over an interleaved history — neither forbidding rushing nor modelling rounds.
  Decide: no issue (our MPC layer is generic and assumes no synchrony), a
  soundness issue (something implicitly assumes round structure — **check this
  first, it is the only defect case**), or a missing capability.  Either way
  §11.6 must state plainly which model we are in; `Q3`/`ConstructsForAll`
  currently float free of the paper motivating them.
- [x] **BOT** (#28) **settled — artifact, but of the ADVANTAGE side; see §11.9.**
  My stakes paragraph was inverted: the strict quotient is *vindicated*, and it
  is `maxAdvantage` that over-counts, by the free domain probing the deletion
  rule grants.
  No migration.  Also found a documentation defect: `maxEDist = 0` was asserted
  in three places (including a live docstring) but is **not kernel-checked** —
  all three corrected.  Superseded framing below, retained for the reasoning:
- [ ] ~~**BOT** (#28) is the strict/Δ gap genuine or an artifact of CR18's
  `s⊥` completion?~~  Lanzenberger has no `⊥` channel: partial domains plus
  *compatible* environments, with equal domains required — in that setting our
  `AttainmentCounterexample` cannot arise as stated (that file proves
  `Adv = ½` and attainment failure; it does **not** contain a `maxEDist`
  statement — see §11.9).  The
  completion is itself a totalization, which would make it the fifth instance in
  §11.4–11.5.  Stakes are high: if artifact, the strict quotient may be
  unnecessary and `edist = ofReal Δ` recoverable, simplifying the bridge and
  removing the ≤-only discipline.  Verdict before any code.  *CR18 is lecture
  notes; where a better treatment exists, use it.*
- [ ] **I1** (#29) **Phase II — make the indexed ε-relaxation primary.**  Jost
  Def 2.2.9 / Thm 2.2.11: ε is a *function on distinguishers*, transported by
  reindexing (`ε_π(D) := ε(Dπ(·))`, `ε_S(D) := sup_S ε(D[·,S])`), with no metric
  anywhere.  AC's `parRightBudget` IS Jost's `ε_S`; D2 built the RS subcarrier.
  Keep scalar `eball` as the constant-ε specialization it already documents
  itself to be.  This is the principled route to chaining parallel
  constructions, which §11.5 closed off via non-expansion.
- [ ] **M1** (#30) **Phase III.1 — `⊣`, right-outbound, `R[[`, first
  impossibility.**  MR16 §3.4/§5.  We have zero impossibility results and this
  theory's famous results are impossibilities.  MR16's Lemmas 3–4 are stated
  **without proof**, so this is a contribution, not a port.  Acceptance test:
  Lemma 6, `PRᵏ ↛ (PRᵏ⁺¹)[[^ε`, with its concrete distinguisher.
- [ ] **EV1** (#31) **Phase III.2 — events** (Jost Ch. 3).  He calls it "an
  alternative instantiation of CC's higher-level axioms", so it slots into our
  architecture.  It is the principled alternative to DESIGN §11.1 rule 2's
  capability-multiplexing, and it generalizes MPR07's MBOs — which we already
  have — so check what carries over before building fresh.  Reconcile with
  DESIGN §10.6's GegMau26 event algebras rather than inventing a third notion.
- [ ] **CR1/IW1** (#32) **Phase III.3–4 — context-restricted constructions and
  interval-wise guarantees** (Jost Ch. 4–5).  Blocked by #31.  CR1's composition
  theorem is an **iff** — do not weaken it.  IW1's until/from relaxations are
  defined by *equality of projected systems*, and their non-commutation with ε
  is the whole reason for the sandwich definition; whether the relaxations
  themselves commute is an **open question in the source** (p. 101).
- [x] **U05** (#20) **the premise was false — there was no obstruction, only a
  misfiling.**  `StrictContextAdvantage.lean` imported only
  `RandomSystems.{CompatibleMetric,StrictContext}`; `StrictContextTotal.lean`
  only its sibling; *zero* references to `AbstractCrypto` or any
  `RandomSystemsCC.*` in either.  Pure RS content living in the CC tree.  Both
  moved to `RandomSystems/**`, namespaces renamed; every consumer already
  `open`s `RandomSystems.CR18`, so only import lines changed.  A 22-line shim
  remains at the old CC path solely for the untouchable `Symmetric/OTP.lean`.
  The helper A1 could not promote is now
  `StrictContextAdvantage.strict_equivalent_of_equivalent`.  The entry had
  stood as "structural, not mathematical" — it was neither.

### 11.10 The parallel axis is installed on the carrier with no cryptography on it (2026-07-27)

P2's pad bug was a symptom.  The defect it points at is structural, and it is
the largest one open.  Four facts, each checked against the tree rather than
recalled:

1. **Every CC endpoint lives on `TypedFinite.Phi`.**  All six `SecurelyConstructs`
   files — `OTP`, `AffineOneTimeMAC`, `BoundedURFMAC`, `FreshOTP`, `UHFURFMAC`,
   `MACThenOTP` — are stated on `Phi`.  `ResourceLift.Resource` carries **no CC
   judgment at all**: not one `SecurelyConstructs`, not one `Constructs`.
2. **`Par`, `IsNonexpandingPar` and `SMulParClass` exist only on
   `ResourceLift.Resource`** (`ResourceParallel.lean`, plus
   `RandomSystems/StrictParallel.lean`).
3. **`CC.SecurelyConstructs.par` has zero uses in the estate.**  We ported
   MauRen11 Theorem 1(ii) and proved it; its only mention anywhere is a comment
   in `MACThenOTP` saying it is unavailable.
4. So the parallel axis and the cryptography sit on **disjoint carriers**, and
   the canonical CC statement — `AUT ∥ KEY  ⟶  SEC`, MauRen16 §5 / Jost §2.3 —
   **cannot currently be written** in this estate.

**Two ledger entries were wrong and are corrected here.**

* *P1's headline* — "install the whole parallel-composition axis" — is true of
  the code and false of the estate.  The axis is real (`Par`,
  `IsNonexpandingPar`, `SMulParClass`, `ParProtocol`, ~2750 lines of
  `StrictParallel`) and it is installed where **nothing can consume it**.  P1
  is not withdrawn; its *scope claim* is.
* *Receipt row 7's reason* — "`Par` ill-posed on extensional Γ" — is **stale on
  both counts**.  (i) `Gamma` is no longer extensional: G1 made it
  `Quotient (ConverterTerm.setoid …)`, i.e. syntactic, quotiented by the monoid
  laws only.  (ii) More decisively, **P1 never put `Par` on the protocol monoid
  in the first place** — it introduced a *separate* free `{1, ∘, ‖}`-algebra
  (`ProtocolTerm`) whose `par` acts componentwise on `‖`-shaped resources and
  as the identity elsewhere, which is exactly MauRen11 fn. 23's freedom used
  correctly.  The obstruction that row 7 cites was designed around a year of
  work ago.

**What `Par` on `Phi` actually needs**, and why it is easier there, not harder:
`Phi I U = ⟨boundary : I → U.Code, system⟩` already indexes by interface, so
the resource-side parallel is *per-interface*: `(R ∥ R').boundary i` is the sum
code of `(R.boundary i, R'.boundary i)`.  That is `ResourceLift`'s
`HasSumCode` / `sumCode_inj` closure condition, indexed by `I` — and the
interface index, which is exactly what `ResourceLift` lacks and what makes CC
judgments statable, is what makes the routing canonical here.  The protocol
side is P1's `ProtocolTerm` construction transplanted.

**Consequences, in the order they bite.**  This is task **P3**, and it belongs
at the top of the program, ahead of the E09 pad repair:

* E09's pad bug **dissolves** rather than gets patched: hand-multiplexing two
  independent capabilities over one shared history is what invented `padAt`,
  its per-interface counters, and its `% (q+1)` totalization wrap.  With a
  `Par`-carried pad store there are no counters to desynchronize.
* Most of `MACThenOTP.lean` deletes — the four private history-scanning helpers
  per resource, across three resources, exist only to demultiplex by hand.
* `SecurelyConstructs.par` acquires its first consumer, and MauRen11
  Theorem 1(ii) stops being a theorem we proved and never used.
* C4 (#6, "unify the two carriers") is **re-scoped**: the two carriers each hold
  half of what CC needs — `Phi` has the interface index and no `Par`,
  `Resource` has `Par` and no interface index.  Unification is not a tidiness
  task; it is this.

#### 11.10.1 P3's scope, corrected before building it (2026-07-27)

My first P3 sketch was to add a `par` constructor to `ConverterTerm`, on the
grounds that `Phi`'s `Gamma` is syntactic and can host it where `ResourceLift`'s
extensional `Protocol U` could not.  **That is wrong, and §11.5 already
forbids it.**  `ConverterTerm.eval` lands in `nonexpandingEnd (Phi I U)`, and
the parallel action is **not** non-expanding — §11.5's counterexample (mix a
product law with a correlating one at weight `δ`; the mixture does not
decompose, so the action pins it while moving the product) drives expansion to
`1 − δ` from a starting distance of `δ`.  Adding `par` to `ConverterTerm` would
assert something false, and would break `IsNonexpandingSMul` — hence
`SecurelyConstructs.trans` — for every existing endpoint.  It would have been
the fourth repetition of the totalize-a-partial-operation disease, in the very
task filed to fix the third.

**The correction shrinks P3 rather than growing it.**  Look at what the target
statement actually needs.  E09 is

> `π • (AUT ∥ KEY)  ≈  SEC`

and the `∥` is on the **resource** — `π` is a serial protocol (encrypt at
Alice, decrypt at Bob) acting on an already-parallel resource.  So P3 needs:

* `Par (Phi I U)` — so `AUT ∥ KEY` can be *written* at all;
* `IsNonexpandingPar (Phi I U)` — MauRen11 eq. (3), the **resource-side**
  claim, which is what `Constructs.eball_par` / `par_left` consume;
* **nothing whatsoever on `Gamma`** — so `IsNonexpandingSMul` and
  `SecurelyConstructs.trans` survive untouched for all existing endpoints.

Protocol-side par (`Par (∀ i, Γ i)`, `SMulParClass`, and therefore
`SecurelyConstructs.par` itself) stays **deferred**, per §11.5's standing
decision: if serial chaining of parallel constructions is ever wanted, restrict
the action to the decomposable sub-carrier rather than totalizing with an
identity branch.  It has no consumer today, and E09 is not one.

**Revised checkpoints.**  P3a `System.relabel` along alphabet equivalences with
`edist` preserved (the one new general lemma; C4 will want it too) → P3b the
boundary equivalence `Query U (σ ⊞ σ') ≃ Query U σ ⊕ Query U σ'`, which is
`HasSumCode.input_eq` under `Equiv.sigmaCongrRight` followed by mathlib's
`Equiv.sigmaSumDistrib` → P3c `DependentRandomSystem.parallel` with
`parallel_inj` and `edist_parallel_le`, obtained by flattening, applying P1's
existing `System.parallel`, and transporting back — **not** by rebuilding
`StrictParallel`'s ~2500 lines for the dependent case → P3d the two instances
→ P3f restate E09 with the pad store as a genuine parallel component.

### 11.11 The CBC counting constant is not provable as written (RS-1, 2026-07-27)

The last admission in the live `RandomSystems/**` tree, `mass_cbcGraphBad_le`,
is **still open** — but the attempt returned something better than a proof
would have been at this stage: the stated bound is wrong, and one step of the
cover is unsound for the headline.

**Proven and landed** (axiom-clean): `mass_cbcGraphBad_le_terminal_add_pairs`
(the cover in mass form), and the **entire `E₁` terminal leg at exactly the
stated constant** — `terminalEventPool`, `card_terminalEventPool_le` (`≤ 2q²L`,
the terminal side's level pinned to its message's last block, so `q·qL` pairs
per side, not `(qL)²`), `mass_terminal_chargedEvent_le : E₁ ≤ 2q²L/|X|`.  The
`E₂` generic case is complete too: `card_two_chargedEvents_strictTop_mul_le`
generalizes the double slice from pair/pair to all four descriptor shapes, and
`mass_two_chargedEvents_strictTop_le` gives `≤ 1/|X|²` per pair whenever
`D₁.top < D₂.top`.

**Finding 1 — the second constant is wrong.**  `(qL)⁴/|X|²` is **not provable
as written** by the only proof shape this file's ingredients support (a
descriptor-pair union bound).  The valid pool holds `q²L(L+1) + q(L−1)`
descriptors — *two* constants per sorted site pair, since `c = 0` input
collisions and `c = blockdiff` lifted-vertex collisions genuinely occur at the
same sites — which exceeds `(qL)²`, the square root of the stated budget, for
every `L ≥ 1`.  Provably `|pool| ≤ 2(qL)²`, so the honest reachable statement
is `2q²L/|X| + **4**(qL)⁴/|X|²`.  The statement was left unchanged because the
constant propagates into `blindMaxWinProb_cbcGraphGame_le` and
`cbc_mac_beyond_birthday` in the same file; **all three must be restated
together** when the kernel cases land.

**Finding 2 — correctness-critical, and it would have been silent.**  The
current cover emits *forced-twin* pairs, where `D₂`'s equation is
deterministically implied by `D₁`'s through shared take-prefixes at both site
pairs.  A twin pair's joint event costs `1/|X|`, **not** `1/|X|²`; summed, the
twins contribute `≈ q²L²/|X|` and **destroy the `L`-linear headline** — the
whole point of the beyond-birthday route.  They are excludable: forced twins
have equal `predInputs` fingerprints and `two_chargedEvents_of_accidents`
already supplies a fingerprint-*distinct* pair, so a second-minimal extraction
over "not forced-equivalent to `D₁`" exists.  The uniqueness guard then weakens
to "= `D₁` ∨ forced-equivalent to `D₁`", and the avoid engine must also kill
forced copies of revisit events.

**Finding 3 (2026-07-27, and it supersedes the other two): the stated bound
reproduces NO source.  PARKED — foundations before applications.**

Checked against the primary sources rather than against our own docstring:

| | first term | second term |
|---|---|---|
| BPR05 (`papers/cbc-improved.pdf`, Fig. 1) | `12·ℓq²/2ⁿ` | `64·ℓ⁴q²/2^{2n}` |
| JN16 (ePrint 2016/161 — the source we *cite*) | `≈ σq/2ⁿ`, **conditional on `ℓ < 2^{n/3}`** | none — folded into the side condition |
| our Lean | `2·q²L/2ⁿ` | `q⁴L⁴/2^{2n}` |

* our second term carries **`q⁴` where BPR05 has `q²`** — a different quantity,
  not a constant discrepancy;
* our first term claims a constant **6× tighter than the published bound**,
  with nothing justifying it;
* JN16 has no second term at all: it buys the beyond-birthday result with a
  **side condition** our statement does not carry;
* **ePrint 2016/161 is not in `papers/`.**  The constants were written without
  the cited source in hand.

So Finding 1's "honest reachable `4(qL)⁴`" answers the wrong question — what
*this union bound* can prove, not what the paper proves.  And the gap is
structural, not cosmetic: BPR05's `q²ℓ⁴` is far smaller than the `q⁴ℓ⁴` a
descriptor-pair union yields, and getting `q²` is exactly what Lemma 10 — the
lemma JN16 corrects — is *for*.  The union-over-all-pairs shape cannot reach
the real bound in principle, which is Finding 2's message arriving from the
other side.  (Unresolved caveat: our ideal is a uniform random **function**
where BPR05 uses a **permutation**, so some divergence is legitimate — not 6×
in the leading constant with no argument.)

**Decision: this is an APPLICATION, and the thesis draws that line itself** —
§2.3 "Definition of the Basic Objects" and §2.4 "Elementary Results" are
foundations, §2.5 is titled "Applications", and CBC/BPR05/JN16 is not in the
thesis at all.  Work stops here until the RS *foundations* are finished.  When
it resumes: fetch ePrint 2016/161, read the corrected Lemma 10, restate to a
source shape (preferably JN16's σ-budgeted form with its side condition — the
estate already does σ-budgeting correctly in the HCTR2 work, `0f26703`
"headlines at the PAPER's constants"; the CBC statement is the outlier from our
own practice), and only then resume counting.

**What remains**, in increasing difficulty: (a) equal-top *cold* — a mechanical
clone of the strict-top engine, where the `hblock` side condition is *free*;
(b) equal-top *hot* and pred-revisit — the genuine corrected-BPR05-Lemma-10
kernel, needing an arbitrary-constant two-site slice lemma plus a peeling
induction on the top level; (c) the cover sharpening of Finding 2; (d) the `E₂`
union assembly.

### 11.12 Re-assessment: CR18's partiality model is a CHOICE, not a defect (2026-07-27)

The "rewind oracle" misreading was not an isolated slip.  It was **load-bearing
for an entire interpretive layer**, and every conclusion that leaned on it has
to be re-examined.  This section separates what is kernel-checked (unaffected)
from what was narrative (withdrawn or downgraded).

**The deletion rule does not even strain prefix-freeness — it is what
prefix-freeness is *for*.**  Def 3.2 makes domains prefix-closed.  Given that,
the accepted-subsequence `(z₁,…,z_m)` of any history is automatically in the
domain, so `s(z₁,…,z_m)` is always defined and `s⊥` is the canonical total
extension agreeing with `s` on `s`'s own domain.  There is no pathology here,
and CR18 chose it deliberately (fn. 5: an environment *"need not necessarily
'know' in advance whether a certain input is defined"*).

**So "maxAdvantage over-counts" was a pejorative for "measures something
else".**  `Δ`'s distinguisher can observe a refusal and branch on it; a strict
test cannot — it simply diverges.  Those are two different notions of
observation, and **it is not obvious that the strict one is the right one**: a
real adversary interacting with a real system *can* notice that it got no reply
and try something else.  On that reading `maxEDist` **under**-counts relative to
an operational adversary, and `Δ` is the faithful notion.  The framing that had
`Δ` as inflated and `maxEDist` as correct was never argued — it was inherited
from the rewind misreading.

**What stands (kernel-checked, unaffected):**

* `maxEDist ≤ ENNReal.ofReal Δ` — proven, unconditional.
* `maxEDist = ENNReal.ofReal Δ` on the shared-domain subcarrier (RP) and under
  totality.  **RP is more interesting under the corrected reading, not less**:
  it is a clean scoping theorem — the two notions of observation coincide
  exactly when domains carry no information — and it never depended on any
  pejorative.
* LOOSE's CBC receipts (zero metric slack) — a computation, unaffected.
* `AttainmentCounterexample`'s arithmetic: `Adv = ½`, class-distance `1`.
* `not_emulable_probeFn` — a genuine theorem about the `Δ` metric.

**What is withdrawn or downgraded (interpretation, not arithmetic):**

* **BOT (#28)'s headline conclusion** — "the strict/`Δ` gap is an *artifact* of
  CR18's `⊥`-completion" — is **withdrawn**.  The gap is a difference between
  two defensible models of what an environment observes.  Neither side is an
  artifact.
* **§11.9's "THE INVERSION"** — that the artifact sits on the advantage side and
  "Lanzenberger vindicates C1's fibre choice" — is **downgraded to a
  description**.  C1's strict quotient really *is* the machine form of
  compatible-environment semantics; what is gone is the *argument* that this
  vindicates it, since that argument presupposed CR18 was defective.  **C1 now
  needs an honest justification or an honest statement of its trade-off.**
* **`AttainmentCounterexample`'s reading** — "the objects are ill-formed under
  the sources' discipline" — is **suspect**.  They are ill-formed under
  Lanzenberger Def 2.14, which is a *scope restriction*; they are perfectly
  well-formed CR18 objects.  The example may simply show that
  domain-distinguishing is real distinguishing power.
* **DOC/#23's "promoting the thesis removes the complication at its source"** —
  **weakened**.  It does not remove a complication; it **restricts scope** to
  objects where domains carry no information.  That is a legitimate and probably
  correct choice, but it is a different argument and must be made on its merits
  (cleanliness, better foundations, the coupling theorem) rather than by calling
  CR18 broken.
* The `probeFn` **"pathology"** framing — downgraded.  The theorem stands; that
  `Δ`-non-expansion fails for some `IsDDC` converters is a fact whose badness
  depends entirely on whether one wanted that composition property.

**Method lesson, recorded because it cost eleven documents.**  The misreading
survived because it was *convenient*: it made a modeling choice we had already
made look forced.  Every subsequent finding was then read through it.  The
`.txt` extraction dropping the operative paragraph is the proximate cause; the
real cause is that no one re-opened the PDF once the phrase was in our own docs.
**Prefer the PDF for anything load-bearing, and treat our own STATUS as a
secondary source.**

### 11.13 The documentation staleness gate (2026-07-27)

Docs drifting is not an occasional lapse here; it is the single most frequent
defect this program has found.  In one day: `U2` sat open after being proven,
`DESIGN` §9.0 named three declarations that do not exist, receipt row 7 gave a
reason obsoleted by `G1`, `P1`'s scope claim was true of the code and false of
the estate, and the rewind misreading propagated into eleven places.  Every one
was caught by a human noticing, which does not scale and did not work.

`doc_audit.py` (`lake run docAudit`) is the analogue of the two Lean gates, and
it checks the three shapes drift actually takes:

* **phantom declarations** — a backticked Lean name in `README`/`DESIGN`/`STATUS`
  that is declared nowhere in this repo, `abstract-crypto`, mathlib or batteries;
* **phantom paths** — a cited file that no longer exists at that path or basename;
* **withdrawn claims** — a regex list of phrasings we have retired, each with the
  reason attached, because a bare blocklist decays into noise nobody can
  adjudicate.

Two design decisions worth keeping:

1. **Baseline-driven**, like `ccSurfaceAudit`.  The 233 pre-existing stale
   references are recorded in `doc_audit_baseline.json`; the gate fails only on
   **new** drift, and reports baseline entries that have become correct so the
   backlog shrinks rather than rots.  A gate that fails on day one is a gate
   that gets disabled.
2. **Withdrawn claims are never baselineable**, but a line that *retracts* a
   claim may quote it (`is_retraction`).  Otherwise correcting a claim in prose
   would itself fail the gate, and the only way to pass would be to delete the
   record of the correction — precisely the amnesia the gate exists to prevent.

Self-tested: injecting a fabricated declaration name and a withdrawn phrase both
fail the gate; removing them restores it.  It caught a real defect on its first
run — `cbc_advantage`, a theorem that exists only in docstrings, which an agent
named in its report and I copied into this file the same day.  Fixed to
`cbc_mac_randomness_expander` here and in `RandomSystems/CBCMAC.lean`.

The 233 baselined entries are a real backlog, not absolution.  They are mostly
legacy `DESIGN` prose from before the three-document rule.  Shrink opportunistically;
never silence one without reading what it points at.

### 11.14 The game half of the thesis is done — and the system half's audit was overstated (2026-07-27)

**The foundations of Chapter 2 are now complete and named.**  `§2.3.3` and
`§2.4.3` — the half that had no Lean names and whose carriers were all labelled
from *CR18 the lecture note* — are in `RandomSystems/GameWinnability.lean` (885
lines, 38 new theorems, axiom-clean) with the thesis-shaped statements aliased
in `LanzenbergerChain.lean`.

**Theorem 2.37, the Winnability Theorem**, is the substantive result and the
game analogue of the coupling theorem:

```
supWinProb G = infWinnability G ∧
  ∃ G', Equivalent G' G ∧ G'.mass PFunDDS.Winnable = supWinProb G
```

— a game with maximal winning probability `δ` has a representative that is
*statically* winnable with probability exactly `δ`, decided before any
interaction.  Hypotheses are exactly Theorem 2.31's (`Fintype X`, fixed atom
domain, depth bound) with **no** probability-distribution hypothesis, so it runs
at arbitrary Def 2.1 weight.  Proved via the thesis's own "Alternative Proof"
(printed p. 26), reusing the existing 2.31 attainment against a never-won twin
rather than redoing an ~1100-line induction.

**Four thesis-vs-CR18 discrepancies, each now a named distinction rather than a
silent conflation:**

1. **Game model.**  Thesis game = a pair `(s, A : X* → {0,1})` with the monotone
   condition revealed only at the end (Def 2.21); CR18/our tree carries the bit
   in the output alphabet `Y × Bool`, observable every round.  Bridged by
   `gameOfDDS`/`winnerView`; `gameEquivalent_of_equivalent` proves the
   refinement direction, and the converse **fails** — that is Remark 2.23.
2. **CR18's `≡ᵍ` (Def 4.16) is NOT thesis Def 2.22.**  Pre-winning-behavior
   equality versus `(t, A(t'))`-law equality.  Both now exist, under distinct
   names, instead of one standing in for the other.
3. **`maxWinProb` was labelled "CR18 Def 4.17" and had no stated relation to
   thesis Def 2.25 `ν`** — different quantifiers.  Now reconciled by a
   *theorem*, `maxWinProb_eq_supWinProb` (Γ = ν), not by assertion.
4. **Monotonicity of the MC is not needed** for any §2.4.3 result — the winning
   event "some answered bit is 1" is monotone by itself.  Our statements omit
   the hypothesis and are therefore strictly more general than the thesis's.

**And a correction to §11.6/the chain header.**  RS-3's audit was integrated
here as "every numbered step of the chain has a name".  **That was too strong.**
`Def 2.27`, `Thm 2.29` and `Lemma 2.30` — the multi-system distance `Δ(𝒮)` —
have **no** Lean declaration.  The overstatement is the same failure the
`docAudit` gate exists for and which that gate cannot catch: the names an audit
*claims* are all real, so nothing is phantom; what was wrong was the claim of
*completeness*.  Recorded as an explicit gap note in the chain header.

**Remaining Chapter 2 gap after this:** `Def 2.27 / Thm 2.29 / Lemma 2.30`
(multi-system distance).  Everything else in §2.2–§2.4 is named.  §2.5
(Applications) remains parked by the owner's foundations-first directive.

### 11.15 CR18 ↔ thesis reconciliation: settled by proof, not by convention (2026-07-27)

`RandomSystems/ThesisModel.lean` (951 lines, zero admissions, axiom-clean) makes
the thesis's own objects first-class — `PartialDDE` (Def 2.11, a *partial*
`Y* →. X`), `thesisTranscript` (Def 2.12, no `Option` anywhere), `Compatible`,
`ThesisEquivalent` (Def 2.17), `ThesisAdv` (Def 2.26) — and then proves the two
models **coincide exactly on the objects the thesis admits**:

* `equivalent_iff_thesisEquivalent` — our `Equivalent` **is** thesis Def 2.17,
* `adv_eq_thesisAdv` — our `Adv` **is** thesis Def 2.26,

both under `HasFixedDomain _ D` on each side, i.e. exactly Def 2.14's clause.  The
embedding direction needs *no* domain hypothesis at all
(`transcript_toDDE_eq_someMap_thesisTranscript`: a CR18 interaction against `s⊥`
driven by a compatible thesis environment **never exercises the `⊥` channel**).
The converse is rejection-pruning, reusing `StrictContextSharedDomain`'s replay
machine — ~150 lines of glue, no new machinery.  This closes the open item
recorded in `papers/notes/RS_SOURCE_CONTRACT.md` TH-A.

**It is NOT our bug — kernel-checked on CR18's own worked example.**
`Footnote6.output_fullyDefined_footnote6_accepts` / `_rejects` reproduce fn. 6
verbatim: `s⊥(0,2,1,2,1) = s(0,1,1)` with the retained history pinned to
`[0,1,1]`, and `s⊥(0,2,1,2,1,2) = ⊥`.  Our `keptPrefix`/`fullyDefined`
implements Def 3.3 **exactly, nothing stronger**.  The divergence from the
thesis is a genuine modelling difference, not a defect we introduced.

**My stated belief about the gap mechanism was REFUTED.**  I had written that the
operative mechanism is *bare observability* of rejection, with costlessness
merely amplifying it.  Checked against `AttainmentCounterexample.lean` rather
than against our docs: its sole device is `queryThenOtherAfterRejection`
(line 247) — ask `a`, then **after an observed `⊥`, ask `b`** — and the proof's
pivot is `successor_of_not_mem`, i.e. the rejected query left the system
unchanged.  Under *observable-but-terminal* refusal the advantage on that pair
is `0`; under *observable-and-continuing-but-state-advancing* refusal it is also
`0`; under CR18's full semantics it is `½`.  So the gap needs the **whole free
probe — observe **and** continue **and** no state change**; no single component
produces it.  Bare observability is not sufficient: strict tests already
"observe" refusal as acceptance-mass collapse, and a point-empty/point-total
pair gives `maxEDist = 1` with no gap at all.  *(The three-way comparison is
hand-derived, not kernel-checked; the `½` is kernel-checked as
`four_pattern_optimal_advantage_eq_one_half`.)*

**`AttainmentCounterexample` is not pathological, and that resolves §11.12's
open reading.**  It is a legitimate CR18 object exhibiting genuine distinguishing
power through *secret-dependent domains*.  What it certifies is that Def 2.14 is
**mathematically substantive rather than cosmetic**: public availability is what
makes the static-representative theory (class distance, coupling, attainment)
true at all.

**The structural finding: the thesis has NO converter notion.**  Def 2.41's
"construction" is a distribution over abstract functions respecting `≡`,
explicitly *"ignoring the details of the interfaces and messages"*.  It cannot
express converter application, cascades, or interface attachment — and CR18
Def 3.8's converter alphabet **includes `⊥`**.  So every converter-level theorem
in our tree is necessarily CR18-based, and that layer is owned by CR18/AC, not
by the thesis.  This is why "the thesis wins" cannot mean "replace CR18".

**Verdict — and the framing above was wrong, corrected 2026-07-27 on the
owner's reading.**  "Statement layer vs carrier layer" implies a competition,
and there is none.

**The thesis is a theory of RESOURCES, and that is the whole of the RS
instantiation.**  Its subject matter is: what a random system *is* (Def 2.9,
2.14), when two are the same (Def 2.17), how far apart they are (Def 2.26/2.28,
Thm 2.31/2.32), and what a game on one is worth (Def 2.25/2.36, Thm 2.37).  It
never discusses converters, protocols, or constructions on *interfaces* —
Def 2.41's "construction" is deliberately a distribution over abstract functions
respecting `≡`, *"ignoring the details of the interfaces and messages"*.

So the earlier finding — "the thesis has no converter notion" — is **not a
deficiency to route around; it is the scope boundary, by design.**  Read
correctly:

* **The thesis IS our RS layer.**  Everything it defines about resources, our
  `RandomSystems/**` should say the thesis's way; where CR18 and it differ on a
  *resource* notion, the thesis wins outright.
* **Converters, protocols and constructions live one layer up** — MauRen11 /
  MR16 / Jost, with CR18 as the lecture-note rendering we happen to have built
  against.  CR18 is not "winning" there; it is simply the only source in hand
  that descends to that level of detail, and it is a *lecture note*, so it holds
  that slot provisionally.
* CR18's extra generality at the resource level (mixed-domain laws;
  unconstrained environments) is then not a virtue of a rival theory but **extra
  room in our carrier that the thesis does not use** — which is exactly what the
  coincidence theorems say, and why it costs nothing to keep.
* The excluded region is real cryptography — adaptive refusals, aborts, error
  oracles, where *availability itself is secret-dependent*.  It is re-encodable
  in the thesis model by enlarging `Y` with an explicit error symbol and keeping
  the domain total; what that loses is only the *free-ness* of the probe.  Since
  an unmetered probe is operationally dubious, **priced probing** is arguably
  more faithful than either source's default, and our tree can express all
  three.

**Inert for results, live only at the model boundary.**  Audited: every crypto
endpoint (HCTR2, CBC-MAC, switching chains) lives on total laws or `filterDom`
images of them, hence shared-domain by `sharedDomainOn_filterDom` — so for
everything that matters the two models provably coincide.

**The "do not migrate" list — provenance, and what each item actually rests
on.**  *This was RS-5's recommendation, integrated by me.  It is not a decision
the owner made, and it was originally published here in the register of policy,
which was wrong.  It is a recommendation awaiting a decision, and each item is
graded below by the strength of its evidence rather than presented as settled.*

| Item | Rests on | Grade |
|---|---|---|
| Keep the `⊥`-completion | `Footnote6.*` reproduces CR18 fn. 6 exactly | **kernel-checked** |
| Don't swap the `DDE` carrier *for correctness reasons* | `equivalent_iff_thesisEquivalent`, `adv_eq_thesisAdv` — thesis semantics on thesis scope come for free | **kernel-checked** |
| …blast radius if we did | **38 files** reference `DDE` directly, 52 mention it (measured 2026-07-27; "~40" was an estimate until now) | **measured** |
| …and the converter layer needs it | CR18 Def 3.8's converter alphabet includes `⊥` (read in the PDF) | **source-verified** |
| Nothing to migrate converters *to* | Def 2.41 explicitly ignores interfaces and messages | **source-verified** |
| Don't restrict `PFunPDS` to shared-domain at the type level | *"it would break the sub-normalized successor internals that Notation 2.34 requires"* | **ARGUMENT ONLY — not proven, not tested.  Downgraded to an open question.** |

The last row is the one to distrust: it is plausible (the attainment induction
does run through sub-normalized successors, and `weight_successorTransform` is
the receipt) but nobody has tried the restriction and watched it fail.  Treat it
as a hypothesis, not a finding.

None of this forecloses the owner's call.  The strongest *positive* reason to
leave the carrier alone is the second row — the migration would buy no theorem
we do not already have.

**Done (RS-6):** `PFunPDS.HasFixedDomain` and `SharedDomainOn` were proven the
same predicate and are now one definition, `HasFixedDomain S D`, moved upstream
to `RandomSystem.lean`.  The name renders thesis Def 2.14's clause
(*"all DDS in the support have the same domain, denoted `dom(S)`"*) subject-first
and was already the hypothesis spelling of all three thesis-parity endpoints.
The `SharedDomainOn` alias has since been **deleted** — it was kept alive only
because this file cited it, which is backwards; documentation follows code.
And the remaining Chapter 2 gaps: Def 2.27 / Thm 2.29 (multi-system
distance), a named theorem that CR18 Def 3.18's successful-kernel equality
agrees with `Equivalent` on *total* systems (the partial-system counterexample
is currently only a docstring sketch), and Def 2.41–2.45 if amplification ever
becomes a target.

### 11.16 CR18's resource-level behavior notion is REFUTED, not merely dispreferred (2026-07-27)

The sweep asked which resource notions our tree still states CR18's way where the
thesis differs.  The answer is short, because most of the ~700 `CR18 Def/Lemma/§`
citations under `RandomSystems/**` are **converter/interface/problem-level** —
Def 3.5, 3.8–3.13, 3.17, all of ch. 4's distinguisher/reduction/H-technique
apparatus, all of ch. 6 — and the thesis's Chapter 2 has no distinguisher object,
no conditional equivalence and no reductions at all.  There is nothing to migrate
*to*; that layer is CR18's by scope, exactly as §11.15 says.

**The headline: `behaviorEq_not_equivalent_counterexample`.**

```
∃ S T : PFunPDS Bool PUnit,
  S.weight = 1 ∧ T.weight = 1 ∧ PFunPDS.BehaviorEq S T ∧ ¬ Equivalent S T
```

Two **weight-1** laws — genuine probability distributions, not sub-normalized
curiosities — with *identical CR18 Def 3.18/3.19 behavior kernels at every round
and argument*, which a compatible environment nonetheless separates at `δ = ½`.
So CR18's Def 3.18/3.19 resource-level equivalence is **strictly coarser than
the truth on partial systems**: it identifies systems that are genuinely
distinguishable.  This is no longer a preference between two defensible
readings — at the resource level thesis Def 2.17 is *right* and Def 3.18/3.19 is
*wrong*, and that is now kernel-checked rather than sketched in a docstring.

The witnesses are the four self-destructing atoms already in
`AttainmentCounterexample.lean` — the same objects §11.12 was unsure how to
read.  They now have a third job, and it is the decisive one.  Note the
distinction that had gone stale and must not be reconflated: Def 3.20's
*cumulative* behavior on `s⊥` **does** match transcript equivalence
(`behavior_equivalent_iff_transcript_equivalent`); it is Def 3.18/3.19's
*successful-history conditional kernel* that fails.

**Everything else at the resource level is IDENT or already reconciled.**
Relabelled thesis-first after verifying both sides in the PDFs: CR18 Def 3.2 =
thesis Def 2.9 (DDS), Def 3.4 = Def 2.13 (parallel composition), Def 3.16 =
Def 2.15 (PDE).  Both distance renderings (`δ`, `statDist`) already state the
thesis's one-sided Def 2.4 — **no CR18 half-sum residue anywhere at the resource
level**, which was worth checking rather than assuming.  Defs 3.3/3.6/3.7 vs
2.11/2.12 stay as a documented model choice, already reconciled kernel-checked
by `ThesisModel`.

**CR18 owns, and the thesis has no counterpart:** Def 3.1 (sources), Def 3.15
(URF/URP as resources), Def 3.21 (environment behavior), Lemma 3.2 (transcript
factorization — CR18 omits the proof, Lean supplies it), Defs 3.22/3.23 (MBO
games, where the thesis uses the MC-pair model instead).

**Def 2.27 stated, Thm 2.29's LOWER bound proven, the rest honestly refused.**
Read from the source (printed p. 19 = PDF 29), Theorem 2.29 is a **two-sided
sandwich**:

```
min_{i≠j} Δ(Sᵢ,Sⱼ)  ≤  Δ(𝒮)  ≤  (min(n,ℓ) − 1) · min_{i≠j} Δ(Sᵢ,Sⱼ)
```

with `ℓ := |⋃ᵢ ⋃_{Sᵢ∈𝐒ᵢ} supp(Sᵢ)|` — **the number of distinct deterministic
systems across the supports, NOT the alphabet size**, so the factor is bounded
by representation size rather than by `|𝒳|`.

`multiSystemDistance` renders Def 2.27 (**corrected** — see §11.18; the printed
inner `inf` is an erratum), and `multiSystemDistance_pair_le` proves the
**lower** bound *per pair* (taking `min` on the left recovers the
thesis's form; per-pair implies it, not conversely).

**Two gaps, not one** — the second was omitted when this was first written here:
1. the upper bound (Lemma 2.30's matrix partition + an n-ary product joint the
   tree lacks, ≥700 lines), and
2. **the left-hand side is `multiSystemDistance` at `n = 2`, i.e. Def 2.27
   specialized — not the repo's `Δ(S,T)`.**  Def 2.28 gives *two displays*
   (`inf δ(S,T)` and `1 − inf sup Pr(S=T)`) and asserts they agree; our `Δ` is
   the first, Def 2.27-at-2 is the second, and identifying them is the classical
   coupling lemma at representative level.  So the result currently lives
   entirely inside the coupling formulation.

*Source detail that reinforces §11.15:* **Defs 2.26, 2.27 and 2.28 all say "with
the same domain".**  The common-domain clause is not a hypothesis the thesis
adds to its theorems — it is built into the **definition of advantage itself**.
On the thesis's own terms, advantage between different-domain systems is not a
quantity one may write down.  And the remark under Def 2.28 gives the reason for
the `inf` over representatives: equivalent PDS can have `δ(S,S') = 1` (V₀ and
V_{1/2}, Ex. 2.16) — the same phenomenon our `four_pattern_class_distance_eq_one`
exhibits.  The upper bound is **not** cheap
and was not forced: it needs Lemma 2.30's matrix-partition argument (new
combinatorics including a WLOG row-reordering) plus an n-ary product joint the
tree does not have, estimated ≥700 lines.  Recorded as an obstruction, not
attempted.

*Lean trap worth keeping:* the first attempt died on a whnf heartbeat timeout
whose root cause was `![·,·]` — Matrix vector notation elaborates its length as
`(Nat.succ 0).succ`, which fights `Fin 2` literals through every `sSup`/`sInf`
unification.  Replacing it with an explicit if-based selector fixed it with **no**
heartbeat increase.

### 11.17 What the build actually gates — and the applications/foundation line (2026-07-27)

`lean_lib RandomSystems` declares **no globs**, so the default build compiles
exactly what `RandomSystems.lean` transitively imports.  Measured: **194 live
modules, 145 reachable, 49 orphaned (19,642 lines)**.  They have **not rotted** —
`RandomSystems.HTechnique.All` and `RandomSystems.Complexity.All` both build
green on demand — they are simply not covered.

**The owner's classification, which corrects the framing this was first written
with.**  My initial reading treated all 49 as wiring debt.  That is wrong:

| class | modules | lines | verdict |
|---|---|---|---|
| `application` | 35 | 16,892 | **deliberately out.**  HCTR2 (ePrint 2021/1441), CBC-MAC beyond-birthday, the Boneh–Shoup game layer (`Complexity.PRG`/`PRF`/`CPA`/game-hops/cost models), sum-of-permutations, the H-technique application machinery.  These are applications and examples built **on** the foundation, not part of it, and may become their own project. |
| `legacy-bridge` | 8 | 969 | compatibility bridges to the quarantined `Legacy` tree |
| `foundation-unwired` | 6 | 1,781 | **real debt** |

So the orphan list is not a defect list, and the gate does not exist to drive it
to zero.  It exists to keep the *classification* honest: every orphan carries a
`class` and a `reason`, and a module that falls out of reach without one is a new
finding.

**The residue that is genuine debt**, now named rather than buried in a 19.6k
line aggregate:

* `RandomSystemMetric` (111) — **the clearest**: it installs an actual
  `MetricSpace` on the behavioral quotient (not merely a pseudometric), and the
  *reachable* `RandomSystemQuotient` explicitly names it as its downstream
  installer while **nothing imports it**.  The root docstring advertises
  "maximal distinguishing advantage as its metric"; the module that supplies it
  is outside the build.
* `CascadeRealization` (654) — CR18 Def 3.11 cascade equation, converter foundation
* `CombineRealization` (522) — CR18 Def 3.12 output-combine equation
* `DependentTranscript` (368) — dependent-fibre transcripts
* `ReductionByConverter` (93) / `ReductionByInstantiation` (33) — CR18 §4.7.2/§4.7.3

**Two consequences that stand regardless of classification:**
1. regressions anywhere in those 19,642 lines are not caught by `lake build`;
2. the RS admission count is **grep-based**, and the default build never
   compiles `CBCStructureGraph` — the file holding the only live RS `sorry`.

*The tell that some of this is drift rather than design:* `HTechnique.All` and
`Complexity.All` are **aggregator** modules, written to be imported by a root,
that nothing imports.

**Closed 2026-07-28.** Coverage is now complete without blurring the line:

* **`RandomSystemsApplications`** — a new non-default `lean_lib` whose root
  imports the 35 application modules explicitly (grouped: Boneh–Shoup game
  layer, HCTR2, CBC-MAC, H-technique/SoP), so dropping any one import strands it
  and fails the gate.  **Nothing imports this root** (grep-verified, zero hits):
  the dependency arrow keeps pointing applications → foundation, never back.
  `CBCStructureGraph` is included **deliberately** — the only live `sorry` under
  `RandomSystems/**` now surfaces as a compiler warning on every build of that
  target instead of hiding in an uncompiled file.
* **`RandomSystemsLegacyBridge`** — the 7 bridges that actually reach the
  quarantined tree get their own target.  Measured nuance: `SoP.AdaptiveAdvantage`
  imports `SoP.CompressionLegacy`, but that module does **not** import
  `RandomSystems.Legacy.*`, so it compiles inside the applications target as an
  ordinary dependency.
* **All 6 `foundation-unwired` modules wired.**  `RandomSystemMetric` in
  particular went in cleanly: its `instMetricSpace : MetricSpace (RandomSystem X Y)`
  is the **only** metric-class instance on that carrier — the other
  pseudo-emetrics live on `System X Y`, `DependentRandomSystem` and
  `Resource I U`, i.e. different carriers — so the feared instance clash does not
  exist.  The debt was drift, not a hidden reason.

**The gate's meaning changed with it**: "orphan" now means *reachable from no
declared `lean_lib` at all*, it prints the foundation / application-layer /
legacy-bridge split so the classification survives an empty backlog, it fails if
a `lean_lib` exists that the audit does not know about, and a baselined orphan
becoming reachable is now a **failure** rather than a note — the backlog must
shrink.  Current state: **196 live modules, 196 covered, 0 orphaned, backlog
empty, foundation-unwired debt none.**  Self-tested both ways.

Two consequences from §11.17 that this **removes**: regressions in those 19,642
lines are now caught, and `CBCStructureGraph` is compiled rather than merely
grepped.

### 11.18 Theorem 2.29 is finished — and the thesis has two errata here (2026-07-28)

Both were found by re-deriving the section before formalizing it, and **both are
confirmed by my own independent check, not merely by the agent's**.

**Erratum 1 — Def 2.27/2.28's inner `inf` should be `sup`.**  Def 2.28 prints
`Δ(S,T) := inf_{S,T} δ(S,T) = 1 − inf_{(S,T)} sup_ℰ Pr^ℰ(S=T)`.  But maximal
coupling gives `sup_ℰ Pr^ℰ(S=T) = 1 − δ(S,T)` per representative pair, so
`1 − inf_reps sup_ℰ Pr = 1 − inf_reps(1−δ) = **sup**_reps δ` — not the `inf_reps δ`
the first display asserts.  The two agree only if `δ` is constant across
representatives, which the thesis's own V₀ / V_{1/2} remark (Ex. 2.16) explicitly
denies.  Corroboration: the **published** LanMau20 (ePrint 2020/1187, Def. 12)
prints only the first display, and the whole multi-system section exists nowhere
in the published paper — this is thesis-only, less-reviewed material.
Our `multiSystemDistance` had faithfully rendered the printed `sInf`, which made
Part A **false as I stated the task**; it is now `1 - sSup …`, documented at the
definition.

**KERNEL-CHECKED 2026-07-28 — it is no longer hand algebra.**  `Example216.lean`
builds thesis Example 2.16's family and evaluates *both* printed displays at the
class `[V]`, with `printedMultiSystemDistance` rendering display 2 **verbatim**
(`1 − sInf …`):

| Def 2.28 | value | declaration |
|---|---|---|
| display 1, `inf_reps δ` (= repo `Δ`) | `0` | `class_distance_V0` |
| display 2 **as printed** | `1` | `printedMultiSystemDistance_V0` |
| display 2 **corrected** (inner `sup`) | `0` | `corrected_display_agrees_at_V` |

hence `definition_2_28_printed_displays_disagree`.  The witness is exactly the
pair the thesis itself names — `(V₀, V_{1/2})` as two representatives of one
class — and `corrected_display_agrees_at_V` pins the discrepancy to **the
quantifier and nothing else**.

**Erratum 2 — Thm 2.29's upper bound is false as printed.**  The printed
`(min(n,ℓ)−1) · min_{i≠j} Δ(Sᵢ,Sⱼ)` should be `max`, because Lemma 2.30 bounds
the *smallest* pairwise overlap `Σ_k min(A_ik,A_jk) = δ_multi − δ_ij`, i.e. it
controls `δ_multi` by the **largest** pairwise distance.  Kernel-checked
refutation, `printed_min_form_counterexample`, and I recomputed it by hand:
`X₁ = δ₀`, `X₂ = ¾δ₀ + ¼δ₁`, `X₃ = δ₂`, so `ℓ = 3` and the factor is `2`; the
true multi-distance is **1** while the printed right-hand side is
`2 · min(¼,1,1) = ½`.  The corrected max form gives `2 · 1 = 2 ≥ 1`. ✓

**What landed** (all axiom-clean, zero admissions):
* `definition_2_28_pair_distance_eq_class_distance` — Part A, and with **weaker
  hypotheses than I predicted**: my hint to route through Thm 2.31 + 2.32 was an
  over-route, since the identity never mentions `Adv`.  Applying the classical
  coupling lemma *inside* the sup over representative tuples needs probability
  hypotheses only — no `Fintype X`, no common domain, no depth bound.
* `theorem_2_29_lower_bound` / `_min_form` — the thesis's `min_{i≠j}` display.
* `lemma_2_30_zero_column_matrix_bound` — and the zero-row-selector route worked:
  the "WLOG reorder the rows" was indeed presentation, not content.  Better, the
  thesis's Case-2 exact-value analysis turned out **unnecessary** — both cases
  collapse to one dichotomy, with the `l = 1` and `total = 0` degeneracies
  falling out of the same contradiction.
* `theorem_2_29_distribution_upper_bound` and the class-level
  `theorem_2_29_upper_bound`, quantified over representative tuples with a
  per-tuple `ℓ` — **smaller** than the thesis's all-representatives `ℓ`, hence
  stronger at every tuple.
* Reusable infrastructure the tree lacked: `Dist.pi` (finite product with
  `marginalAt_pi`) and the n-ary maximal coupling
  `supAgreement_eq_weight_overlapDist` — `supAgreement laws = Σ_a minᵢ lawsᵢ(a)`.

**Argument-only, documented and not formalized:** that the class-level *printed*
min statement is likewise false (needs transcript-semantics work), and that the
corrected max form cannot be transferred to the pairwise `Δ` without simultaneous
attainment of all pairwise infima by one tuple, which the thesis does not supply.

### 11.19 `Par` is installed where the cryptography is (2026-07-28)

§11.10's finding is closed: the parallel axis existed only on a carrier with no
CC judgment on it, so `AUT ∥ KEY ⟶ SEC` could not be *written*.  It can now.

`RandomSystemsCC/TypedParallel.lean` gives `Par (Phi I U)` and
`IsNonexpandingPar (Phi I U)` — MauRen11 eq. (3), the **resource-side** claim
that `Constructs.eball_par` / `par_left` actually consume — built on a behavior
tower in `RandomSystems/TypedParallel.lean`.  Zero admissions, all fifteen key
declarations `[propext, Classical.choice, Quot.sound]`.

**The route was the cheap one, as designed.**  No part of `StrictParallel`'s
~2500 lines was rebuilt for the dependent case: flatten → P1's `PFunDDS.par` →
relabel back along `queryEquiv`/`answerEquiv` → `unflatten`.  Three pieces
carried it, each already proven: full abstraction
(`contextual_edist_eq_max_edist_flatten`), P3a's relabel **isometry**
(`maxEDist_relabel`), and P1's `maxEDist_par_le`.  P3b's index-compatibility
lemmas discharged exactly the obligation they were written for —
`tag_faithful_relabel_par`, the `unflatten` side condition.  `parallel_inj`
comes from `sumBoundary_inj` plus strict cancellation, and `par_ne_left` is the
non-vacuity receipt that `∥` genuinely remembers both components.

**State the limit precisely, because it is easy to overclaim.**  What is proven
in the acceptance test is the *reflexive* CC judgment on a parallel resource
(`par_resource_in_cc_judgment := SecurelyConstructs.refl …`).  The
`AUT ∥ KEY ⟶ SEC` shape appears as an `example` that **elaborates** — i.e. the
statement is now well-formed and writable — not as a proved construction.  No
attach/parallel interchange law (`π • (A ∥ B) = …`) is claimed.  Non-vacuity is
separately checked: a one-query strict test behaviorally separates the
components on the quotiented carrier, and `demoAut ∥ demoKey ≠ demoKey ∥ demoKey`.

**Still deferred, unchanged:** `CC.SecurelyConstructs.par` / `par_left`
themselves need the **protocol-side** `Par (∀ i, Γ i)` + `SMulParClass`, which
§11.5 forbids on this carrier (the parallel *action* is not non-expanding).  What
P3 unblocked is the resource-side `∥` **under serial protocols** — which is
exactly what E09 needs, since there `π` is encrypt-at-Alice / decrypt-at-Bob.

**CORRECTION (§11.29, 2026-07-28): "the asymmetry is now gone" was wrong.**  P3
installed the **resource-side half**.  AC's parallel calculus needs *four*
classes — `Par Φ`, `IsNonexpandingPar Φ`, `Par M`, `SMulParClass M Φ` — and
`SMulParClass` has **exactly one instance in the estate**, on `Resource U`.

**Consequence for E09**: the pad-selector desync (§11.11 Findings 1–2) can now be
*dissolved* rather than patched — a `Par`-carried pad store has no per-interface
counters to desynchronize, and `otp_stage_securely_constructs` stops being a
false statement in the tree.

### 11.20 E09: the false statement is gone — the model was repaired, not patched (2026-07-28)

`otp_stage_securely_constructs` was a `sorry`'d theorem that was **false for
every `q`**, with three endpoints marked retracted beneath it.  It is now an
honest admission of a statement assessed **true**, and the falsity is gone from
the tree.

**The chosen repair was (a) explicit index addressing, NOT the `Par`
restatement — and the reasoning corrects my own recommendation.**  I had said
`Par` would dissolve this.  The agent evaluated both and showed (b) buys nothing
here, source-verified:

* `CC.SecurelyConstructs.par` requires **protocol-side** `Par (∀ i, Γ i)` and
  `SMulParClass`, which `RandomSystemsCC/TypedParallel.lean` deliberately does
  **not** install (§11.5, the parallel action is not non-expanding).
  `Par (Phi I U)` alone cannot feed `.par`.
* The OTP protocol is **serial across both components** — encrypt reads the pad
  *and* writes the channel — so even with every class present the stage proof
  would not decompose.  The one genuine obligation is the same size either way.
* (b) would also have needed a `HasSumCode` instance on this bespoke universe
  and would have restated the two admitted MAC receipts — blast radius into
  statements that were explicitly out of scope.

Since (b) requires (a) anyway, (a) alone removes everything that made the
statement false.  The honesty payload of (b) was banked *inside* (a): in the
repaired model the pad table's answers depend only on the sample and never on
history, so it is a genuinely separable `KEY` component and a later `∥`
restatement is a refactor rather than a redesign.

**A constraint shaped the design — but it is OUR constraint, not the theory's.**
*(Misattribution corrected 2026-07-28; see §11.21.)*  The design was driven by
"Alice cannot count her own sends", credited to `ProtocolFn.ofStep` **and CR18
Def 3.8**.  The Def 3.8 half is wrong: `IsDDC` is `AnswersInY ∧ ∃ B,
AnswersWithin ν B`, and neither clause forbids memory — `ProtocolFn` takes the
**full outer input list**.  The memorylessness is entirely `ofStep`'s, a
convenience constructor whose own docstring calls it *"the outer-memoryless step
converter"*.  With a history-aware constructor Alice **can** count her own sends.
The E09 design stands on its merits (an explicit address is better than an
implicit one), but it was a *choice*, not a forced move.  "Ask for pad `j`" therefore requires
the *channel* to name `j`: encrypt now performs three inner queries —
`.nextIndex`, `.otpKey j`, `.sendCipher` — and `.receiveCipher` delivers the
ciphertext **with its position**, so decrypt reads the pad at the delivered
index.  The pad address travels with the ciphertext; sender and receiver cannot
disagree.  The minimal-diff variant (channel answers an indexless `.otpKey` at
Alice's send count) was **rejected on principle** — it keeps the address
implicit, which is the disease.

**Deleted, tree-wide, zero occurrences remaining:** `padAt`,
`authAliceOtpCount`, `authBobOtpCount`, `sourceAliceOtpCount`,
`sourceBobOtpCount`, and — same disease, separately spotted — `simulatedCipherAt`
with its own `% (q+1)`.  Sample spaces shrank `Fin (q+1) → G` to `Fin q → G`:
**the `+1` existed only to totalize the mod selector.**  Indexed reads now
answer `Option G` and return `none` past the table, per DESIGN §4 item 11 —
explicit partiality instead of an invented value.

**The three counterexample theorems are deleted.**  They forced this repair and
are gone with the model they refuted.  In their place a `PadSynchronization`
section replays the *same three attack patterns* against the new model as
`rfl`-checked receipts: after two sends `.receiveCipher` delivers `(1, c₂)`;
`.otpKey 1` returns the pad `c₂` was made with; at `q = 1` Bob's second receive
re-delivers `(0, c₀)` — there is no receiver-side counter left to advance.

**Endpoint status:** the three downstream endpoints compile through the
surviving `SecurelyConstructs.trans` + `commute_honest_simulators` proof
unchanged, and their docstrings now state honest conditionality on an admitted
**true** lemma instead of retraction.  Admissions 11 → 11.

**Flagged for later, argument-only and pre-existing:** the polynomial MAC
receipt at `q > 1` may be optimistic — Eve replaying an *older* authentic
payload verifies at `macBob`, while the auth ideal admits replacement only equal
to the *latest*.  Whether the claimed `C(q+1,2)·ℓ/|F| + 1/|T|` budget covers
replay deserves checking **before** anyone attempts that admission.

### 11.21 Every converter in the estate is memoryless — and nothing requires that (2026-07-28)

Raised by the owner on reading E09's design rationale, and confirmed by
measurement.

**The theory supports stateful converters.**
`ProtocolFn U V X Y := List U × List (Option Y) →. X ⊕ V` — the **full** list of
outer inputs together with the cumulative inner answers.  Its own docstring:
*"given the outer inputs and the (cumulative) inner answers so far, the next
move."*  And CR18 Def 3.8, our `IsDDC`, is just `AnswersInY ν ∧ ∃ B,
AnswersWithin ν B` — never move past a `⊥`, and a finite bound on consecutive
inner queries.  **Neither clause mentions state.**

**We built the whole estate through the one constructor that forbids it.**
`StepRealization.ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ)` passes `step`
only `p.1.getLast` — the *current* outer message — plus that round's answer
segment.  Its docstring names the restriction outright: *"The outer-memoryless
step converter"*.  Measured: **`ofStep` is the only `ProtocolFn` constructor in
the tree, with 83 uses across 19 files.**  The only code touching a raw
history-dependent `ProtocolFn` is `StrictRelabel.pullbackFn`, and that is a
*transport*, not a constructor.

**Why it matters beyond tidiness.**  A converter that cannot remember anything
across outer invocations cannot hold a counter, a sequence number, a nonce, or
any handshake or session state — i.e. it cannot express most real protocols.
E09 is the first place this bit: it forced the authenticated channel to *name*
the pad index because Alice could not count her own sends, and the constraint
was then misattributed to CR18 Def 3.8 (corrected in §11.20).  It will bite
harder in the MPC/FROST direction, where session state is unavoidable.

**Done 2026-07-28 — `ofHistoryStep`, additive and pure-insertion.**

```lean
def ofHistoryStep (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ) : ProtocolFn U V X Y
```

line-for-line `ofStep` except at the two places memory lives: `step` sees the
whole history `p.1`, and `(p.1.dropLast.map cnt).sum` becomes
`roundOffset cnt p.1`.  **`ofStep` is byte-identical** — the diff has 321
insertions and **zero deletions**, so all ~367 existing uses are untouched — and
`ofStep_eq_ofHistoryStep` exhibits it as the history-ignoring special case by
*raw function equality*, not merely `TraceEquiv`.

`isDDC_ofHistoryStep` requires the query-count bound to be **uniform over
histories**, and says so: `AnswersWithin` demands a single `B` good at every pair
of the trace tree, so a per-history bound cannot close that clause.  That is an
honest hypothesis, not a convenience.

**The acceptance test is the receipt that this is real.**  `counterFn` runs over
the **silent** outer alphabet `U = Unit` — the caller supplies nothing, so every
difference between invocations is the converter's own memory.  On its `n`-th call
it queries the resource for item `n`: `counterFn ([()], []) = inl 1` and
`counterFn ([(), ()], [some 7]) = inl 2`, both `rfl`, both on the trace tree
(`reach_counterFn_*`, so the difference is environment-reachable and not junk).
`isDDC_counterFn` puts it **inside** CR18 Def 3.8 — memory is not an escape from
the class.  And `not_traceEquiv_ofStep_counterFn` proves that for **every**
`step`/`cnt` satisfying the boundary condition, no `ofStep` converter is
trace-equivalent to it: `step () [] = inl 1` forces `0 < cnt ()`, so at the second
invocation the single available answer is entirely consumed by round 1's budget
and `ofStep` must repeat `inl 1`.  The separation is at the project's working
converter identity, not at raw terms.

*Left on the table — and CORRECTED 2026-07-28, because I overstated it.*  The
agent's note, which I repeated, said a stateful converter could not be **applied**
inside a construction proof until a coherence theorem existed.  **That is false.**
`ProtocolRealization.apply` (`:258`) is defined on an *arbitrary* `ProtocolFn` —
its own docstring calls it *"the ν-level **generalization** of
`CausalApply.applyG`"* — with **no step-shape hypothesis**, and it carries a full
computation surface (`mem_applyRaw`, `mem_applyRawAt_iff`, `@[simp]
apply_toPFun`, `apply_eq_of_reachable_invariant`).  `ofHistoryStep` *is* a
`ProtocolFn`, so stateful converters are applicable **today**.

**The fast path is now built too (2026-07-28).**  `CausalApply.applyGH` is the
history-aware drive — `driveOuterH` threads the consumed prefix so the `cons`
case calls `step (done ++ [u])` — with
`apply_ofHistoryStep_eq_applyGH : PFunConverter.apply (ofHistoryStep step cnt) S
= CausalApply.applyGH step S.1`.  Both files are **pure insertion**
(`CausalApply` +291/−0, `StepRealization` +293/−0), so `applyG` and its ~40
consumers are provably untouched, and `driveOuter_eq_driveOuterH` recovers the
memoryless drive as the specialization — one mechanism, not two.  The old
`apply_ofStep_eq_applyG` is re-derived in four lines from the new coherence as
`apply_ofStep_eq_applyG_of_hist`, non-circularly.

*The `roundOffset` reconciliation — the part I flagged as the real content — went
cleanly*, on the invariant `∀ u, roundOffset cnt (usPre ++ [u]) = ys.length`
("everything delivered so far is exactly what the completed rounds consumed").
The `∀ u` is a device to avoid a new total-offset definition, since that
`roundOffset` sums over proper nonempty prefixes of `usPre` and so does not
depend on `u`.  It initialises from `roundOffset_of_length_le_one` and
re-establishes from `roundOffset_concat`.

*My acceptance-test premise was wrong, and the agent measured it rather than
working around it:* a `Part`-valued run does **not** close by `rfl` —
`Part.bind`'s domain `∃ h : o.Dom, (f (o.get h)).Dom` is not defeq to the
continuation's — so the test mirrors the file's own `Option`-valued `causalDrive`
at the outer level and *proves* it is the applied system
(`applyRawAtH_functionEvaluator`).  Payoff, against a pad table `n ↦ 10n`:
`causalApply_counter_{first,second}` compute `10` and `20` **by `rfl` with axiom
footprint `[propext]` alone**, and `apply_counterFn_ne` transports it — the
*applied system* answers differently on the first and second outer call although
both histories carry only the silent message `()`.  A converter's own memory is
now observable through application, kernel-decided.

This is also the converter-side analogue of the resource-side `Machine` design
queued as R1b (#24).

### 11.22 Legacy triage: the XoP/SoP development is KEPT (2026-07-28)

The `Legacy/` tree is 72 modules / ~75,900 lines, of which 53 modules / 64,202
lines are reached by nothing outside the tree.  Triaged rather than dropped
wholesale, because it turns out to contain two very different things.

**Genuinely new mathematics, with no live counterpart — KEPT (owner's decision).**
The XoP/SoP development: **40,642 lines, 1,544 theorems, zero `sorry`s.**  The
live tree carries roughly **116** theorems of XoP/SoP content, all in thin bridge
modules — so about **93% of this mathematics exists only here.**  Measured
reachability from anything live:

| module | lines | thms | reached by live? |
|---|---|---|---|
| `SoP/SmallQ` — small-query exact values | 15,488 | 516 | **no** |
| `XoPRank` — rank / codimension | 8,846 | 329 | **no** |
| `XoPMayer` — pair-Mayer expansion | 5,785 | 242 | **no** |
| `XoPANOVA` | 1,895 | 87 | **no** |
| `SoP/Affine` — affine invariance | 1,163 | 45 | **no** |
| `SoP/Basic`, `SoP/Partition`, `XoP`, `XoPModel`, … | — | — | yes |

The five unreached modules alone are **~33,000 lines and 1,219 proved theorems** —
Patarin mirror-theory territory (Mayer expansion, rank/codimension, ANOVA,
affine invariance, exact small-query values).  **Directly relevant to the SoP
work now in flight under `RandomSystems/SoP/`**: re-deriving any of it would be
waste.

*Honest caveat:* several titles say **"Scaffold"** (`XoPRank`, `XoPMayer`,
`XoPANOVA`, `SoP/Basic`, `XoP`).  Zero admissions means the content is *proved*;
"scaffold" suggests it was infrastructure toward a target rather than a finished
result.  Worth reading before assuming it is a completed development.

**Superseded duplicates — verified droppable, awaiting go/no-go.**
`Legacy/CR18/*` (23 modules) duplicates the live formalization and is uniformly
*smaller* than it: `PFunDDS` 1,041 vs 1,115, `PFunConverter` 2,103 vs 2,574,
`PDS` 2,570 vs 3,149; `Behavior`, `DDS`, `DDE`, `Game`, `Indist`, `CausalApply`
are all superseded by `RandomSystem.lean`, `PFunDDS.lean`, the game chain,
`Theorem417` and the live `CausalApply.lean`.  Plus two abandoned scaffolds:
`BonehShoupCascade` (1,987 lines, **2** theorems) and `CascadeCircle` (826 lines,
**1** theorem, titled *"# Intended theorem (to be proved)"*).

**Measured, not assumed: that drop set is 25 modules / 25,214 lines and NOTHING
live reaches any of it — zero clashes with `RandomSystemsLegacyBridge`.**  Not
deleted; the decision is the owner's.

### 11.23 Example 2.16 lands, and the RS foundations are closed (2026-07-28)

**No third erratum** — the thesis's ascribed properties hold.  Ex. 2.16 (printed
p. 15) defines a *family*, not the two systems directly:
`V_α := {(zero,α),(one,α),(id,½−α),(flip,½−α)}` over the four **single-query**
DDS of Fig. 2.1, with `[V] = {V_α | α ∈ [0,½]}`; so `V₀` and `V_{1/2}` are its
endpoints.  Both claims proved: `equivalent_V0_Vhalf` and
`delta_V0_Vhalf : δ (V 0) (V (1/2)) = 1`.

**Single-query is load-bearing, and this is the finding worth keeping.**  The
four atoms had to be built with domain exactly `X¹` rather than reusing the
existing total `PFunDDS.functionEvaluator`.  On a *total* evaluator, asking `0`
then `1` reads both coordinates of one sample, and `{id, flip}` is visibly
correlated where `{zero, one}` is not — the equivalence would fail.  So Example
2.16 is precisely a statement of the thesis's *"a system can only be executed
once"* (the remark under Def 2.15), and `raw_fullyDefined_singleQuery_of_two_le`
records it: every query after the first is `⊥`.  That motivating separation is
graded **argument-only**; only the positive side is kernel-checked.

**Item 2 — the positive direction, completing the Def 3.18 picture.**
`behaviorEq_iff_equivalent_of_total`: on total systems CR18 Def 3.18's kernel
equality **does** agree with `Equivalent`.  With the counterexample
(§11.16) this brackets the notion exactly — right where domains carry no
information, wrong exactly where they do.

The hypothesis was *chosen with a proof rather than a preference*:
`totalOnNonempty_iff_hasFixedDomain` shows the two candidates coincide (`Valid`
already forces `[] ∉ dom`, so the fixed-domain form adds nothing), and
`TotalOnNonempty` is kept as the form the tree already uses.  Two receipts guard
against vacuity: `totalOnNonempty_single_functionEvaluator` (the hypothesis is
satisfiable) and `four_pattern_not_both_totalOnNonempty` — the counterexample's
laws **cannot both be total**, derived *for free* from the new theorem plus
`four_pattern_not_equivalent`.  The hypothesis is exactly what the counterexample
violates.

Also fixed: `behaviorEq_not_equivalent_counterexample`'s docstring had claimed
the total-system agreement followed from `behavior_equivalent_iff_transcript_equivalent`
— the Def 3.18 / Def 3.20 conflation this program has now corrected twice.

**With this, thesis §2.2–§2.4 is complete**: every numbered item Def 2.1 → Thm
2.37 is instantiated and named, the two errata are recorded and one is now
kernel-checked, and the remaining thesis work (§2.5 Applications, Chapter 3) is
parked by the foundations-first directive.

### 11.24 `IsDDC`'s query bound is over-strong: a quantifier-order slip (2026-07-28)

Raised by the owner: *"I always read that as per-invocation."*  He is right, and
this relocates a hypothesis I had defended as "honest rather than convenient".

**What we encoded:**
```lean
def AnswersWithin (ν) (B : ℕ) : Prop := ∀ p, Reach ν p → … no streak of B …
def IsDDC (ν) : Prop := AnswersInY ν ∧ ∃ B, AnswersWithin ν B      -- ∃B ∀p
```
**What CR18 Def 3.8 intends:** the same body with `∃ B` **inside** the `∀ p` —
`∀p ∃B`, i.e. *no infinite query streak*, "the converter invokes the system a
finite number of times" per invocation.

It is a **quantifier-order slip — the same shape as the thesis's Erratum 1**
(`inf`/`sup` under `1 − x`).  This project has now found the pattern three times.

**Evidence that per-invocation is the intended reading**, beyond the owner's:
* CR18's own informal paragraph for the same object says *"the converter invokes
  the system **a finite number of times** (zero times is allowed) and then
  returns an output `v ∈ 𝒱`"* — per invocation, not uniform.
* Def 3.8's formal clause — *"There is a finite upper bound on the number of
  consecutive outputs of the form `(in, x)`"* — reads uniform in isolation, and
  contradicts the prose above it.
* CR18 **never discharges the obligation the bound exists for**: after Def 3.9 it
  says *"We do not give a completely formal definition of the application of a
  converter to a system. Formally, one would have to show that the described
  object `αs` is indeed a `(𝒰,𝒱)`-DDS.  **Intuitively, this is obvious.**"*  A
  finiteness condition chosen to support an unproven claim is exactly where
  over-strengthening hides — and **we** discharged that obligation
  (`EmulateRealization.lean`), so we are in a position to tell which strength is
  actually needed, where CR18 was not.

**Everything proved so far is sound.**  `∃B ∀p → ∀p ∃B` is trivial, so every
existing `IsDDC` witness remains a witness for the intended class.  The defect is
that our converter class is **strictly too small**: it excludes converters whose
work grows with invocation count — e.g. one that re-scans its own history each
round.  `counterFn` and `ofHistoryStep` are unaffected (one inner query per call,
uniform `B = 1`), so the stateful-converter work is not blocked.

**Blast radius, measured:** `IsDDC` — 67 mentions across 17 files; `AnswersWithin`
— 57 non-comment occurrences across 15 files; 14 `isDDC_*` producer lemmas.  The
producers are free (their uniform witnesses still qualify).  The real work is the
**consumers that destructure a uniform `B`** — principally `EmulateRealization`'s
fuel simulation (`emuRun_streak` / `_round` / `_terminal` and the application
theorems), plus `StrictParallel`, `ComposeRealization`, `CausalApply`,
`TypedFraming`, `AbsorbDPI`, `StepConverter`.

**CHECKED 2026-07-28 — and the answer is neither of the two I posed.  My
hypothesis that uniformity is slack is REFUTED; so is the framing that this is a
binary choice.**  See §11.26.

### 11.25 The superseded Legacy core is deleted (2026-07-28)

Owner's decision after the §11.22 triage.  Dropped: **29 modules, ~26,800
lines** —

* `Legacy/CR18/*` (23 modules) — a pre-migration duplicate of the live
  formalization, uniformly *smaller* than it (`PFunDDS` 1,041 vs 1,115,
  `PFunConverter` 2,103 vs 2,574, `PDS` 2,570 vs 3,149; `Behavior`, `DDS`, `DDE`,
  `Game`, `Indist`, `CausalApply` all superseded by `RandomSystem.lean`,
  `PFunDDS.lean`, the game chain, `Theorem417` and the live `CausalApply.lean`);
* the Boneh–Shoup cascade files — `BonehShoupCascade` (1,987 lines, **2**
  theorems), `BonehShoupCascadeAdaptive` (89 lines, and one of the three legacy
  `sorry`s), and `CascadeCircle` (826 lines, **1** theorem, titled *"# Intended
  theorem (to be proved)"*);
* **`attic/`** (4 files) — outside every `lean_lib`, so nothing ever built it,
  and it existed only to hold material referencing the retired core.  One of its
  files never compiled at all: a genuine duplicate declaration across two
  imports.

**Re-verified immediately before deleting, and the check earned its keep.**  The
first pass measured "reached by nothing *live*", which missed two things the
second pass caught: `BonehShoupCascadeAdaptive` imports the cascade scaffold (so
dropping one without the other breaks `RandomSystemsLegacy`), and three `attic/`
files import `Legacy/CR18/*`.  The criterion that matters is *"reached by nothing
**kept**"*, not "nothing live".

Legacy is now **46 modules / 50,598 lines**, down from 72 / 75,901 — and what
remains is overwhelmingly the XoP/SoP development kept in §11.22.  All five
targets build clean; all four gates green; admissions unchanged at 11.

`docAudit` caught **8 references to the deleted files** across `STATUS.md` and
`DESIGN.md` — including a Maurer-deviation note in DESIGN §6 whose marker lived
in the now-deleted `Legacy/CR18/Game.lean`.  That deviation still stands (the live bit-guessing
development is `RandomSystems/Complexity/BitGuessing.lean`); only the pointer was
stale.  This is the gate doing exactly the job it was built for: a deliberate
deletion is the commonest way documentation goes stale, and it was caught in the
same minute.

### 11.26 The `IsDDC` bound: uniformity is load-bearing, but not where CR18 puts it (2026-07-28)

The check ran.  **My hypothesis — "those are per-round fuel arguments, so
pointwise suffices and uniformity is slack" — is refuted**, and the binary framing
was wrong too.  There are **three** classes, and the gaps between them are
kernel-checked, not argued:

```lean
AnswersWithinAt ν p B            -- the pointwise witness (factored out)
AnswersEventually ν  := ∀ p, Reach ν p → ∃ B, AnswersWithinAt ν p B   -- CR18's PROSE
AnswersWithinDepth ν F := ∀ p, Reach ν p → AnswersWithinAt ν p (F p.1.length)
AnswersWithin ν B                -- our uniform clause, Def 3.8 as FORMALIZED
IsDDC.isDDCEventually            -- the receipt: axiom-FREE, so all 18 producers still witness
```

**Both separations are strict and kernel-checked:**
* `roundGrowthFn` — `k²` inner queries after `k` outer rounds, all alphabets
  `Unit` so the growth is in the round index alone:
  `isDDCEventually_roundGrowthFn` ∧ `not_isDDC_roundGrowthFn`.  So `IsDDC` really
  is strictly smaller than the prose class.
* `answerGrowthFn` — queries once, reads the answer `m`, then issues `m` more:
  `isDDCEventually_answerGrowthFn` ∧ `not_answersWithinDepth_answerGrowthFn`.  So
  the prose class is strictly larger even than depth-indexed uniformity.

**Where uniformity is genuinely required — and it is NOT what CR18 claims.**
CR18's own undischarged obligation (*"one would have to show that `αs` is indeed
a DDS … intuitively, this is obvious"*) **holds for the prose class**; only our
proof route happens to use uniform fuel (`applyRaw_dom`, graded argument-only).
What actually needs it is the layer CR18 never states: **MauRen11 Def 15/16
environment emulation**, because

```lean
Emulable α := ∀ e n, ∃ e' m g, ∀ s, …
```

fixes the inner fuel `m` **before `s` is quantified**, and the inner answers *are*
`s`'s output.  `answerGrowthFn` admits no bound as a function of the round count,
so a pointwise class cannot be turned into fuel at all.  This is not an artifact:
`CompatibleMetric.maxAdvantage_apply_le` (MauRen11 eq. (4), non-expansion) and
`equivalent_apply` destructure exactly that `⟨e', m, g, hg⟩`, and a finite `m` is
what makes the absorbed distinguisher *bounded*.

**And even there, uniformity over *rounds* is slack — what is load-bearing is
uniformity over *answers*.**  `AnswersWithinDepth` is precisely that boundary:
fuel becomes `∑_{i<n} F i` instead of `n · B`.  So if this is ever migrated, the
target is `AnswersWithinDepth`, **not** `AnswersEventually`.

**Per-consumer verdict** (65 occurrences / 15 files, measured): producers
unaffected (they prove the stronger property); all four *transporters*
(`StrictRelabel`, `TypedAttachment`, `TypedFraming`, `StrictContextAdvantage`)
need only a pointwise bound, each applying its hypothesis at exactly one computed
source pair; `emuRun_round` pointwise — my hypothesis *was* right there;
`emuRun_streak` needs cross-round uniformity (its anchor **moves**, and the
conclusion multiplies a single numeral by the round count);
`ComposeRealization.serial_composition_has_finite_query_bound` needs uniformity
**in the answers** (its anchors differ by `ysPre`).

**My caveat was wrong on its facts.**  I guessed `Complexity/**` would want the
global bound for cost analysis.  *Measured*: **zero** occurrences of `IsDDC`,
`AnswersWithin` or `Emulable` in that directory.  Not a stakeholder.

**Decision: keep `IsDDC` uniform; `IsDDCEventually` is added as the faithful
reading of the prose, not as a replacement.**  Migration would be *wrong*, not
merely expensive — the core consumers need answer-uniformity, `transcript_apply`
carries `B` **in its statement**, and `IsDDC` is baked into subtypes and structure
fields across `StrictContext`, `TypedAttachment`, `TypedResource`, `TypedAction`,
`TypedUnitMetric`, `TypedFraming`, `StrictParallel`.

*Argument-only, with an explicit witness:* `IsDDCEventually` is **not closed under
serial composition** (compose `answerGrowthFn` with a relay; the composite's root
streak is `ext[0] + 1`, unbounded in the extension itself).  If that holds, the
prose class is not a usable converter class at all — which would retro-justify
CR18's formal clause over its own prose.  Worth formalizing before anyone
proposes the migration again.

Two docstrings corrected on the way, one of which asserted the opposite of this
finding: `StepRealization`'s claim that "the uniformity is not slack introduced by
the history indexing" was true of `AnswersWithin` but implied `ofHistoryStep`'s
uniform hypothesis is necessary — it is not.

### 11.26.1 The uniform bound is not a CR18 artifact — Jost states it verbatim (2026-07-28)

Asked whether we were "trying too hard to do CR18", and whether the other
sources help.  **Fair hit — I had not checked, and both are text-extractable, so
it was a grep rather than a visual read.**  Checked now, and the answer is that
they do not help, for a decisive reason.

**Jost, Definition 2.2.2** (`papers/ThesisJost.pdf`), verbatim:

> *"There is a **finite upper bound on the number of consecutive outputs** of the
> form `(y, I′) ∈ 𝒳 × I_in`."*

**CR18, Definition 3.8**, verbatim:

> *"There is a **finite upper bound on the number of consecutive outputs** of the
> form `(in, x)`."*

Word for word.  The newer, longer, more careful source states the **identical
uniform clause** — so `∃B ∀p` is not a lecture-note artifact and not something we
imported carelessly.  Both sources also carry the same looser prose above the
definition (Jost: *"a **bounded** number of queries … before returning a value"*;
CR18: *"invokes the system **a finite number of times**"*), so the
prose/definition tension is in the literature, not in our reading of it.

Two further findings from the same check:
* **Jost explicitly sidesteps the question.**  Immediately before Def 2.2.2:
  *"In this work, we mainly avoid the delicate task of choosing the class of
  converters under consideration by making all converters explicit."*  So the
  best-founded source in our stack declines to pin down the converter class.
* **`PorRen22` does not address it.**  Its only converter-plus-finiteness
  sentence concerns *computational efficiency* (*"one usually only considers
  protocols whose converters are computationally efficient"*), not query counts.

**Consequence.**  On this point the standing "prefer Jost/MR16/Lanzenberger over
CR18" rule yields *no change*: Jost agrees with CR18 verbatim, and Lanzenberger
has no converter notion at all (§11.15).  Our §11.26 analysis therefore stands as
the **best available account** — it is the only place that says *what the uniform
bound is for* (emulation; and specifically uniformity in the **answers**, not in
the round count), backed by two kernel-checked separations.  CR18 waves the
obligation away as "intuitively obvious"; Jost declines to fix the class; we
measured it.

### 11.26.2 The algebraic-theory paper explains WHY the loose reading fails (2026-07-28)

Owner asked whether the Matt et al. / Portmann "algebraic theory of systems" and
"causal boxes" line had been checked.  It had not — **`papers/MMPRT18.pdf`,
"Toward an Algebraic Theory of Systems" (Matt, Maurer, Portmann, Renner,
Tackmann), has been sitting in the repo unread.**  It bears directly, though not
where I would have looked.

**The corroboration.**  Discussing which sequence sets yield a valid
composition-order-invariant system algebra, MMPRT18 says:

> *"it is **not possible in this model to allow arbitrarily many but only
> finitely many** inputs and outputs, because this does not yield an ω-CPO: The
> supremum of an ω-chain `C₀ ⊑ C₁ ⊑ C₂ ⊑ …`, where `Cₙ` contains `n` elements,
> is infinite."*

That is **our `∀p ∃B` versus `∃B ∀p` problem in another guise**.  "Arbitrarily
many but only finitely many" *is* the per-invocation class, and the failure mode
is the one we hit: **the supremum escapes the class.**  So the structural reason
the prose reading misbehaves is already in the literature — it is a
domain-theoretic closure failure, not an accident of our formalization.  It is
also independent evidence for §11.26's argument-only corollary that
`IsDDCEventually` is not closed under serial composition.

**Causal boxes is the paper for the open question, and we do not have it.**
MMPRT18 cites `[PMM+17]` — Portmann, Matt, Maurer, Renner, Tackmann, *"Causal
boxes: Quantum information-processing systems **closed under composition**"*,
IEEE Trans. Inf. Theory 63(5), 2017 — whose entire premise is closure under
composition.  **Not in `papers/`.**  It is the obvious next read before anyone
revisits the converter class.

**Also unread in `papers/` and worth noting** while the list is being taken:
`2105.05949v3` (Broadbent–Karvonen, *Categorical composable cryptography*),
`BMT18`, `BBM18`, `CoMaTa13`, `MaRuTa12`, `2021-156` (Barbosa et al., mechanized
adversarial complexity for UC), `2026-1071` (Gegier–Maurer, event algebras).

**Standing lesson, third time today.**  The answer to "is this difficulty real?"
kept turning on a source we had but had not opened — CR18's dropped paragraph,
Jost's Def 2.2.2, and now MMPRT18's ω-CPO remark.  **Check the shelf before
re-deriving.**

### 11.26.3 Causal boxes: how the literature actually admits unbounded-but-finite (2026-07-28)

`papers/PMMRT17_CausalBoxes.pdf` fetched (arXiv 1512.02240v3, 68pp) — Portmann,
Matt, Maurer, Renner, Tackmann, *"Causal Boxes: Quantum Information-Processing
Systems **Closed under Composition**"*.  It answers the question §11.26 left
open, and the answer is a *technique*, not a verdict.

**The problem is theirs too, and they name it.**  §4.1:

> *"instead of defining it as a map `Φ : T(F_X^T) → T(F_Y^T)`, a causal box is
> given by a set of mutually consistent maps `Φ = {Φ^{≤t} : T(F_X^T) →
> T(F_Y^{≤t})}_{t∈T}` … This allows systems to be included that **produce an
> unbounded number of messages** on the entire set `T`.  For example, let
> `T = ℕ` and consider a beacon system that outputs a state `|0⟩` at every point
> `t ∈ ℕ`.  This is well-defined on every subset `{1,…,t}`, but the limit
> behaviour …"*

**The fix is a projective family, not a bound.**  Rather than demand a global
object (which is what MMPRT18's ω-CPO argument shows cannot exist for
"arbitrarily many but only finitely many"), they *define the system as its
consistent family of bounded restrictions* and never take the limit as an object
of the class.  Appendix C, "Finite causal boxes", then carves out the subset that
*is* a single map on all of `T` — i.e. our `AnswersWithin`, as a distinguished
sub-class rather than the definition.

**What this means for us, stated carefully.**  It does **not** overturn §11.26:
`IsDDC` stays uniform, because our `Emulable` needs one finite fuel chosen before
the system is quantified, and that is a genuine requirement of the metric layer
(a test with no finite length is not a test).  What causal boxes supplies is the
**route** if the per-invocation class is ever wanted: present a converter as a
consistent family `{α^{≤n}}` of fuel-bounded approximations, prove the family
coherent, and let the distinguisher pick the cutoff — instead of asking for a
single unbounded-fuel object.  That is the shape `AnswersWithinDepth` was already
groping toward (fuel `∑_{i<n} F i` rather than `n·B`).

**Also corrected:** `PorRen22` does *not* develop causal boxes; it cites them
(*"e.g., the Quantum Combs of Chiribella et al. or the Causal Boxes of Portmann
et al."*) and works with an abstract notion of system.  So the primary source
genuinely was missing from the shelf, and now is not.

### 11.27 The Code/Boundary indirection is NOT ceremony — it is what makes real-vs-ideal comparable (2026-07-28)

R1b landed; CODE (#25) was **refuted by census**, and the refutation is the more
valuable half.

**`Code := Iface` does not hold, and the reason is structural.**  A census of all
51 `Boundary` sites found **zero** carriers in the tree using an identity
boundary.  Every multi-interface universe is the *opposite* shape — e.g.
`MACThenOTPModel` (measured): **10 codes, 3 interfaces, four boundaries over the
one universe** (`sourceBoundary` / `authBoundary` / `secureBoundary` /
`availableBoundary`).  Same pattern in `OTPModel` (3 boundaries),
`UHFURFMACModel` (4), `BoundedURFMACModel`, `AffineOneTimeMACModel`,
`FreshOTPModel` (3 each).

The reason: **in CC the real and ideal resources sit at the *same* interfaces and
must inhabit *one* universe to be comparable.**  The *code* is exactly what keeps
them at incomparable signatures (`Resource.boundaryEDist = ⊤` across distinct
codes) and the *boundary* is the **world selector**.  `Code := I` would force one
alphabet per interface globally and **collapse real into ideal**.  So the
indirection I had filed as ceremony is load-bearing, and `ofInterfaces` is a
**convenience for the single-world case**, not a replacement — scope documented
at the declaration, with `MACThenOTPModel.signatures` named as the
counterexample.

**My premise was false on both counts, and this is the fifth relayed claim to
invert on checking.**  I asserted "CBC's `interfaces X M` has 2 codes for 3
interfaces".  Measured: `Interface` has exactly **2** constructors, `Code :=
Interface` — so CBC is *already* `Code = I` — and `CBCModel.lean` / `CBC.lean`
contain **no `Boundary` at all**; CBC rides the single-code
`RandomSystemsCC.CR18.Resource U` carrier, not the `DependentDDS U sigma` path.

**What did land.**  The Machine core is promoted to
`RandomSystems/ResourceMachine.lean` (652 lines, gated, namespaced — it had been
polluting the root namespace).  `SignatureUniverse.ofInterfaces` +
`Boundary.ofInterfaces` (**axiom-free**) cut the Fig. 2.2 signature block from
**19 code lines to 10**: the code layer and the interface→code map vanish, leaving
two per-interface alphabet families that read directly off the figure.  Existing
files touched **+35 / −0, pure insertion**.

**Bisimulation, kernel-checked** — `Machine.toDDS_eq_of_bisim`, `[propext,
Quot.sound]`: a relation on states, preserved by `step` with equal answers,
forces equal denoted resources.  Worked example: `authChan` (pointwise
`ℕ → Option M` plus a counter) versus `authChanLog` (a `List M`, no counter) —
visibly different data, same resource, and the three Fig. 2.2 regressions transfer
without restatement.  **Resource state is now refactorable without reproving
anything downstream** — which is precisely what the E09 pad-index repair needed
and did not have.

**The macro layer was refused, with a reason.**  After `ofInterfaces` the residual
ceremony is 10 lines of two pattern-matching `def`s that mirror Jost's figure
line-for-line; a macro would trade readable, greppable Lean for opaque generated
names and would still need the interface enum hand-written.  The ~40-line problem
it was sized against no longer exists.

### 11.27.1 Process defect: `lake env lean` is not a green signal

**`lake env lean <file>` does not apply the package's `leanOptions`.**  The
promoted file was clean under `lake env lean` and then failed `lake build` with
nine `autoImplicit` errors.  The scratchpad prototype had been "compiling green"
for weeks *only because nothing ever built it with `autoImplicit false`.*

This invalidates part of our standing dev-loop instruction, which tells agents to
use `lake env lean <file>` as the fallback iteration signal.  It is fine for
iterating on *goal state*, but **a file is not green until `lake build` has seen
it under the library's own options.**  Every brief from here should say so.

### 11.28 I1: the indexed relaxation was already first-class — the gap was the bridge (2026-07-28)

**My premise was wrong, and it came from this file.**  §11.7 Phase II said "make
the indexed ε-relaxation primary, not the scalar `eball`", and I briefed from it.
Measured against `git HEAD` (not the worktree): `reductionRelaxation` appears
**22 times in the committed** `AbstractCrypto/Relaxations.lean`, and Thm 2.2.10
plus **both halves** of Thm 2.2.11 — `attachBudget` (protocol) and
`parRightBudget` (parallel) — are already proven, with a live consumer in
`RandomSystemsCC/TypedFeasibility.lean`.  It sits under the **JM20 citation
numbering**, not the thesis numbering: thesis Def 2.2.9 = JM20 Def 3, Thm 2.2.11
= JM20 Thm 3.  That is why a search for the thesis numbers found nothing.

**Sixth relayed or assumed claim to invert on checking this session.**

**Confirmed: Thm 2.2.11 needs no metric.**  `reductionRelaxation_par_subset`
assumes only `[Par Φ]` and `IsClosedUnderPar`.

**But one nuance corrects §11.5's framing.**  `IsNonexpandingPar` *is* derivable
for a class-derived metric (`DistinguisherClass.isNonexpandingPar`, from the same
`IsClosedUnderPar`), so the metric route is **not** blocked for class metrics.
The indexed route's real advantages are narrower and better stated:
1. the budget transports **exactly** — `ε_𝒮(D) := sup_{S∈𝒮} ε(D[·,S])` — instead
   of collapsing to a single radius;
2. it is **independent of which metric a carrier installs**, which is decisive on
   `Phi I U`, where `edistD ≤ edist` is strict across boundaries.

**The actual gap, found by grep: ZERO connection between `eball` and
`reductionRelaxation`.**  Now bridged (`+278/−0`, no new `@[simp]`/`@[ext]`):
`reductionRelaxation_const_eq_eball` — `eball ε` **is** the indexed relaxation at
the constant budget, by raw equality; `eball_subset_reductionRelaxation_const`
(the sound direction under a merely *dominating* metric, matching our
`edist ≠ ofReal Δ` finding); `reductionRelaxation_subset_eball_iSup` (best scalar
over-approximation); and **`reductionRelaxation_singleton_ne_eball`** — a
criterion under which an indexed budget equals **no scalar ball at any radius**,
witnessed concretely by 3 states and 2 tests where two states sit at *identical*
class distance 1 from the centre and only one is admitted.

**Bonus, and it is the composition win:** `Constructs.reductionRelaxation_trans`
/ `_par` / `_par_right` — Cor 2.2.13 at indexed budgets, carrying **neither**
`IsNonexpandingSMul` **nor** `IsNonexpandingPar`, where the scalar counterparts
carry both.  Also `parLeftBudget` + `reductionRelaxation_par_left_subset`, which
finally consumes `IsClosedUnderPar.test_par_left` — a field the file's own comment
had flagged as dead.

**Source-verified typo in Jost, p. 23:** the parallel chain prints
`ε(D[·,V])` where it must be `ε(D[·,S])` — the last step is legal only because
`S ∈ 𝒮`, and `V ∈ ℛ^ε` is not in `𝒮` at all.  The Lean proof uses the correct
reading.  (Third defect found in a source this session, after the thesis's two
errata.)

### 11.29 C4: keep both carriers — and P3 closed only half the asymmetry (2026-07-28)

**Decision: keep `RandomSystemsCC.CR18.Resource U`, with its role recorded** —
outcome 2 of the three the task allowed.  Docstring-only, `+60/−0`, **zero
declarations added**.  And the task's premise, which I wrote, is partly refuted.

**The decisive measurement.**  AC's parallel calculus — `Constructs.par_left`,
`par_left_resource`, `simulator_par`, `Constructs.eball_par`,
`CC.SecurelyConstructs.par`/`par_left` — each require **four** classes:
`Par Φ`, `IsNonexpandingPar Φ`, `Par M`, **`SMulParClass M Φ`**.  Measured:
`SMulParClass` has **exactly one instance in the whole estate**
(`ResourceParallel.lean:297`, on `Resource U`).  So `Resource U` is the **only**
carrier where any of those five theorems can fire, and
`ParallelChecks.extract_constructs_par` is the kernel-checked receipt that one
does.  **Retiring it would delete the estate's only executable instance of AC's
parallel construction calculus.**

**So my post-P3 framing was wrong.**  I recorded that P3 removed the asymmetry
justifying two carriers.  It removed the *resource-side* half: `Phi` now has
`Par` and `IsNonexpandingPar`, but still has **no `Par (∀ i, Γ i)` and no
`SMulParClass`** — and §11.5/§11.10.1 explain why it cannot simply copy them
(a `par` on `ConverterTerm`, which interprets into `nonexpandingEnd (Phi I U)`,
would break `IsNonexpandingSMul` and hence `SecurelyConstructs.trans` for every
endpoint).  `ParProtocol` escapes exactly by interpreting into plain
`Function.End` and asserting no metric law.  Porting it is **deferred for want of
a consumer**, not unavailable — and the agent correctly declined to build an
unconsumed monoid against a standing decision.

**Three further reasons the carriers are not duplicates:**
* **CBC's shape is not CC's shape.**  CBC is a randomness expander whose
  `Primitive.act` *changes the resource's signature* (`U(X,X) → M → X`), with no
  honest/dishonest split and no simulator.  `Phi`'s `boundary` is the world
  selector across a *fixed* interface set (§11.27); CBC has nothing to put in it.
* **Option 3's mathematics already exists and its packaging has no consumer.**
  `TypedUnitMetric.lean:414` `contextualEDist_eq_maxEDist_singleView` is metric
  full abstraction at one interface — the `Phi` fibre metric at `I = Unit` **is**
  `Resource U`'s fibre metric.  A bundled embedding is packaging; the reverse
  chart does not exist, and Par-preservation would have to chase `flatten` vs
  `singleView` through `HEq` transport.
* **Option 1 is a re-implementation, not a migration.**  Of `ResourceLift.lean`'s
  838 lines only ~115 are carrier+metric; the rest is the surface CBC consumes —
  `HasResourceCode`, `liftProb`/`liftProbAt`, `DDConverter` with three-way `HMul`
  dispatch, `Primitive`, the `—[π;ε]→` notation, `cr18_construct`, the three
  `Δ`-bridge lemmas.  `Phi` has none of these under any name.

**Census**: `Resource U` has exactly **one** downstream model (`CBCMAC`, 2 hits in
`CBCModel.lean`), 4 `ApproximatelyConstructs` endpoints in `CBC.lean` + 3 in
`ParallelChecks`, and **zero** `SecurelyConstructs`.  `Phi` carries everything
else — all 45 audited endpoints, every `SecurelyConstructs`, `Symmetric/**` (7
files) and `Frost/**` (6).

### 11.30 S1: the general specification form is primary on OTP — and it is a strict gain (2026-07-28)

`RandomSystemsCC/AdversaryStructure.lean` (**new**, 355 lines: 207 code, 148
prose, endpoint-independent) + `Symmetric/OTP.lean` (`+117/−61`).  All seven new
declarations `[propext, Classical.choice, Quot.sound]` — **verified by
`#print axioms`, no `sorryAx`**.

**What changed.**  `otp_constructs_for_adversary_structure` — a LiuMau20
specification-family statement over the adversary structure
`singleDishonest .eve` — is now **primary**, proved from the resource-level
leaves.  The old fixed-`Z` `otp_securely_constructs` is **derived from it, with
its statement text byte-identical** (`git diff` shows the signature lines as
context, not as `+`/`-`; the only removed line is the old `unfold`).

**Why it is a gain and not a lateral move — two independent reasons, both
checked.**
1. **The exact form is metric-free.**  `constructsForAdversaryStructure_of_exact_leaves`
   takes **no metric class at all** (verified: its `#check` signature mentions no
   `PseudoEMetricSpace`/`EDist`).  OTP's proof produces literal *equalities*, and
   the specification form states them as exact set containment.  On a **pseudo**-emetric
   carrier `eball 0 X ⊇ X` can be **strict** — `edist y x = 0` does not force
   `y = x` — so the old `ε = 0` phrasing was *strictly weaker* than what the
   proof establishes.  `ε` is now an optional, separate weakening
   (`constructsForAdversaryStructure_eball_of_exact`), which is JM20 §2.3's point.
2. **The assumed side is `∗Z`-relaxed.**  It reads
   `zStar tupleGamma Z {otpAssumedResource}`, not `{otpAssumedResource}` — the
   statement now covers *every* dishonest-Eve pre-processing of the assumed
   resource.  The previous bridge gave only the bare singleton.

**MauRen11 Def 3's two clauses are the two rungs of the family.**  Reading `⊥` as
the honest-Eve converter and folding it into the tuple `π = protocol * bottom`,
for `𝒵 = {∅, {eve}}`: at `Z = ∅` the ideal is `{⊥ • S}` (relaxation collapses) =
**availability**; at `Z = {eve}` the `⊥` vanishes and the ideal is
`{σ • S | σ ∈ zSub}` = **security**.  Availability is not a second notion, it is
the no-corruption rung, and `zStar tupleGamma Z {patternAttach Zᶜ bottom • S}`
produces both **uniformly, with no `if`**.

**A real ceiling on the adversary-structure axis, and it is Def 3's fault not the
translation's.**  `AdversaryStructure` is monotone, so the smallest structure
containing `Z` is its full downward closure, and a fixed-`Z` judgment says
**nothing** at `∅ ⊊ Z' ⊊ Z`.  A fixed-`Z` endpoint can therefore be lifted only
when `|Z| ≤ 1`.  Fine here — all ten `Symmetric/**` endpoints use `Z = {.eve}` —
but it means *"quantify over an adversary structure"* is **not obtainable by
rewriting existing endpoints** for any genuinely multi-party construction.  Those
need per-`Z` leaves in LiuMau20's quantifier order, which `AbstractCrypto.mpc_step`
and `leaf_of_shared_simulator` already supply, and `Multiparty.lean`'s closing
`example` proves per-pattern ⇏ shared.  **This is quantifier order again** — the
fifth instance this program has hit (§11.17).

**Marginal cost for endpoints #2–#10: ≈23 lines each, zero new mathematics.**
The generic bridge leaves three obligations, all `simp`-closable, and the other
six `Symmetric/*` files define `simulators`, `protocol` and `bottom` **verbatim
character-identically** to OTP's.

**Recommendation adopted: do not rewrite the other nine now.**
`constructsForAdversaryStructure_of_securelyConstructs` lifts an *existing*
`SecurelyConstructs` in ~13 lines with **no reproof**, so the nine
admission-carrying endpoints get their specification form for free the moment
their admissions close.  Make the *exact* form primary only where the leaves are
literal equalities (perfect constructions), which is where it buys real strength.

**Two reasoned refusals, both correct.**
* **`ConstructiveCryptography.lean` left untouched** although the task assigned
  it: `ConstructsForAdversaryStructure`/`zStar`/`tupleGamma` live in
  `AbstractCrypto/Multiparty.lean`, which `AbstractCrypto.lean:92` and the
  `CCMPC` lib declare to be owned by **`CC.MPC`, a layer *above* `CC`**.  Importing
  it into `ConstructiveCryptography.lean` would invert that documented layering.
  The bridge went RS-side, where `import CC.MPC` is already established.
* **CBC left untouched**: `cbc_randomness_expander` is *already* in the general
  form (`Constructs π {R} (eball ε {S})` via `—[π; ε]→`), and the adversary-structure
  axis is not merely unnecessary there but **untypeable** — CBC's acting monoid is
  a flat `Submonoid (nonexpandingEnd (Resource U))` with no interface-indexed
  tuple structure, so `patternAttach`/`tupleGamma` cannot apply.  A randomness
  expander has a distinguisher, not a corruption pattern.  (Same conclusion as
  §11.29 reached from the carrier side.)

**Gate regression I caused and fixed.**  §11.29's docstring tripped
`htechniqueSurfaceAudit`: the bare token `Constructs` is forbidden outside
`BRIDGE_STATEMENT_FILES`, and that rule says *"comments included is acceptable"* —
policing prose is deliberate.  The fix was to my prose, **not** to the gate:
sanctioning `TypedParallel.lean` would have contradicted the rule's own
"carrier/action support modules remain excluded".  Note the gate independently
encodes §11.29's finding — `ResourceParallel.lean` **is** sanctioned because it
owns `extract_constructs_par`; `TypedParallel.lean` is not, because it owns no
construction statement.

**`moduleAudit` baselined `RandomSystems.SoP.SoP`** (661 lines) as
`owner-reserved` rather than wiring it, since a concurrent session owns that tree
under a hands-off instruction.  A permanently-red gate is an unread gate — which
is this audit's own account of why the H-technique gate went unread for weeks.

### 11.31 SY1: verdict (a) — no synchrony *defect*, now with a kernel-checked receipt (2026-07-28)

**Answer: (a) gap, not bug — and (b) is refuted by proof, not by argument.**  All
new declarations axiom-clean (`propext`, `Quot.sound`; **no `sorryAx`, no
`Classical.choice`**); admissions unchanged at 11, endpoints 45, 0 regressions.

**Why (b) was the only candidate defect, and how it is settled.**  Our model can
only be *unsound* if it **forbids** an adversarial interleaving — proving security
against too small a set of distinguishers.  It has exactly one mechanism for
that: `DependentDDS` carries a prefix-closed `domain`, so a resource *can* refuse
a query.  The question is therefore entirely concrete: **do any live domains
depend on query order?**

Enumerated every `domain :=` in the live tree.  All are one of two shapes:
* `{history | history ≠ []}` — total, constrains nothing (`TypedParallelChecks`,
  `TypedFeasibility`, and the RS base);
* `{history | history ≠ [] ∧ countWith w history ≤ 1}` — the OTP/FreshOTP
  one-message budget (5 resources).

`countWith` sums a weight over the history, so it is **permutation-invariant**:
these domains restrict *multiplicity* ("Alice may submit at most once" — the
one-time pad), never *scheduling*.  That is now proved rather than asserted:

| declaration | content |
|---|---|
| `DependentDDS.ScheduleAgnostic` | domain membership depends only on which queries were asked |
| `scheduleAgnostic_of_perm_invariant` | the criterion for the `countWith`-budget shape |
| `scheduleAgnostic_of_total` | total domains constrain nothing |
| **`rushing_not_excluded`** | `honest ++ adversarial ∈ dom → adversarial ++ honest ∈ dom` |
| `scheduleAgnostic_ofAmbient` | **attachment preserves it** |
| `realDDS_/idealDDS_/postDecryptDDS_scheduleAgnostic`, `realDDS_rushing` | the five live receipts |

`rushing_not_excluded` is the formal content of "we do not forbid rushing": the
adversary may act **first** on the same query multiset.  `scheduleAgnostic_ofAmbient`
is what makes the argument reach the endpoints at all — without it the receipts
would cover only bare `R` and `S`, not the `π • R` a distinguisher actually
drives; `ofAmbient` pulls its domain back along `List.map encodeQuery`, and `map`
preserves permutations.

**So our model is strictly *more* permissive than LiuMau20's.**  Its Def 4
resource consumes a complete input list per invocation and thereby silently
forbids rushing (p. 12: "any (dishonest) party's input depends solely on the
previous outputs seen by the party.  In practice this assumption is often not
justified"); the r.a/r.b semi-round split of Fig. 4 is its remedy, and footnote 1
notes the literature's rushing adversary is a special case.  We have no rounds,
so nothing can be withheld within one.  Proving security against a superset of
adversaries is sound, so **no existing statement is weakened**.

**The genuine (c) gap, stated precisely.**  Def 4's resource sees *all* round-`r`
inputs before producing *any* round-`r` output.  A sequential model must
serialize: some party's answer is computed without the others' round-`r` inputs.
So a synchronous functionality delivering `f(x₁,…,xₙ)` simultaneously is not
directly expressible, and **LiuMau20's theorems cannot be stated verbatim**.
What we do have is the standard encoding — a *submit* port and a *read* port
(`.sendCipher` then `.receiveCipher`) — which is the semi-round discipline
imposed at **port granularity instead of round granularity**.  Every construction
in the estate already uses it.  Building Def 4's list-valued invocation is
therefore a capability we lack, not a correction we owe.

**One honest caveat, recorded in the source.**  `Machine.toDDS`'s domain is
`{h | h ≠ [] ∧ (m.run h).isSome}`, and `m.run` folds the history through the
state machine — so `isSome` *may* depend on order.  The `Machine` constructor is
expressive enough to encode a scheduling constraint and is **not**
`ScheduleAgnostic` in general.  Its docstring now says so and points here; any
machine whose statement should admit a rushing adversary owes its own receipt.

**Still open (documentation, not soundness):** our `Q3` quantifies over all of
`I`, whereas LiuMau20 Theorem 1 uses **Q³([n−1], 𝒵)** — party `n` is only the
instruction source.  Ours is the textbook Hirt–Maurer form; instantiating their
theorem needs the restricted variant.

**Process note.**  `lake env lean` reported both receipt files clean while
`lake build` found `Unknown identifier G` — the receipts had landed *after* the
anonymous `section`'s `end`, and `lake env lean` does not apply the package's
`autoImplicit false`, so `G` was silently auto-bound.  This is §11.27.1's lesson
recurring verbatim: **`lake env lean` is not a green signal.**  Section-variable
scope is also the same trap as the local-notation one — a declaration placed past
an `end` loses its instances without any syntactic marker.

### 11.32 M1: MauRen16 §3.4 machinery landed — and eq. (2) over-claims (2026-07-28)

`../abstract-crypto` commit `045baec`, `AbstractCrypto/Relaxations.lean`,
namespace `Relaxation`.  **Lemmas 3 and 4 are stated *without proof* in the
source** ("The following lemmas are stated without proofs", p. 11), so proving
them is a contribution, not a transcription.  `constructs_star`,
`constructs_outboundHull` and `subset_outboundHull` depend on **no axioms at
all**; the other three on `propext`(`, Quot.sound`).

| declaration | MauRen16 |
|---|---|
| `RightOutbound H blk S` | `S*⊣ = S⊣`, no signalling right-to-left (§3.4) |
| `outboundHull H blk R` | `ℛ⟦` (p. 9) |
| `outboundHull_idem` | eq. (2) idempotence — **unconditional** |
| `subset_outboundHull` | eq. (2) containment — **conditional**, see below |
| `constructs_star` | **Lemma 3** (unproved in source) |
| `constructs_outboundHull` | **Lemma 4** (unproved in source) |
| `outboundHull_eq_empty_of_top` | the counterexample forcing the precondition |

**Design: no second action was needed.**  MauRen16 pictures Alice on the left
and Eve on the right and *requires* the two to commute — `(αR)β = α(Rβ)` (p. 8),
"which justifies to write `αRβ`".  In our interface-indexed setting both are
elements of the **same** converter monoid with **disjoint support**, so that
commutation is a *consequence* of the tuple monoid being a product rather than an
extra axiom.  It appears as an explicit hypothesis (`π * β = β * π`) so a carrier
lacking it is excluded rather than silently assumed.  This also means
`Constructs π R S := π • R ⊆ S` **is** MauRen16 Definition 1 verbatim — the
construction notion needed no adjustment.

**FINDING — eq. (2)'s `ℛ ⊆ ℛ⟦` is not a theorem as printed.**  `ℛ⟦` contains
*only* right-outbound resources by construction, so a specification with a
signalling member cannot be contained in its own hull.  The missing precondition
is that every member of `ℛ` be right-outbound.  `outboundHull_eq_empty_of_top`
makes this kernel-checked: over `Function.End Bool` with `⊣ = 1` and Eve allowed
every endofunction, right-outboundness reads `∀ β, β S = S`, refuted for every
`S` by the constant `fun _ => !S` — so the hull is **empty**.

Severity: **pedagogical, not structural.**  Every resource the paper applies it
to is right-outbound (public randomness `PRᵏ`; a random oracle hiding Alice's
queries from Eve), so Corollary 1's appeal to eq. (2) stands.  It is the general
statement that over-claims.  Note the idempotence half needs no hypothesis in
*either* direction: `⊆` because any `S ∈ ℛ⟦` is itself right-outbound and so
contributes its own `S⊣` to `(ℛ⟦)⊣`, and `⊇` because `(ℛ⟦)⊣ ⊆ ℛ⊣`.

**Still open — Lemma 6, the acceptance test.**  `PRᵏ ↛ (PRᵏ⁺¹)⟦^ε` for `ε < ¼`
needs a **conditional min-entropy layer and its chain rule**, and there is
**none anywhere in either package** (`minEntropy`/`H_min`/`Hmin`: zero hits
outside `.lake`).  It also has a statement shape unlike anything else in the
estate — a *negation of an existential over all constructors*, with the
distinguisher `D₁` exhibited concretely.  Dispatched separately.

### 11.33 N1: notation layer — two real defects, one dissolved, one already done (2026-07-28)

New permanent gate `RandomSystemsCC/NotationChecks.lean`, wired into
`RandomSystemsCC.lean`.  Build green, all four audits pass, admissions unchanged
at 11, endpoints 45, 0 regressions.  **Two of the card's four defects were not
what it said**, so each was measured before being fixed.

**(a) Approximate lifting for bare converters — REAL, fixed, and the difficulty
was self-inflicted.**  `AbstractCrypto.ApproximatelyConstructs` demanded
`[Monoid M] [MulAction M Φ]`, but its body uses only `HasReduction.Red` — a bare
relation `Ω → Γ → Ω → Prop` — and `Relaxation.eball`, which needs the metric on
`Φ` alone.  The monoid came from the **ambient `variable` line**, nothing else.
Consequence: `TypedFinite` supplies `HasReduction (Set (Phi I U)) (Primitive …)`,
so the *exact* form `⟪R⟫ —[flip]→ ⟪S⟫` accepted a bare `Primitive` while the
*approximate* form failed with `failed to synthesize Monoid (Primitive …)` — a
`Primitive` is not a monoid and has no reason to be — which is why every metric
endpoint spelled an explicit `Pi.mulSingle` tuple.  Fixed by taking
`[HasReduction (Set Φ) M]`, the hypothesis actually used
(`../abstract-crypto` `7bdcd5c`).  Strictly more general: existing call sites
still resolve through `instance : HasReduction (Set Φ) M`, and all 45 endpoints
build unchanged.

**(b) Packing coercion — REAL, fixed.**  `⟨boundary, ofProb S⟩` was hand-written
at **60+ sites across ten modules** although the boundary is already determined
by the law's type.  `Resource.instCoeTCProbResource` recovers it, with
`coe_prob_boundary`/`coe_prob_system` as `@[simp]` transparency receipts.

**(c) Glyph collision — NOT a defect; the card's claim is refuted.**  The card
said `CBC.lean` "avoids the clash only by not opening `scoped AbstractCrypto`".
**Measured by opening that scope in `CBC.lean` and building: it compiles
clean.**  The two notations do share a glyph and a precedence, but they are not
ambiguous, because they take different argument types (`Resource U`/`ℝ`/
`DDConverter` versus `Set Φ`/`ℝ≥0∞`/`M`), so at most one elaborates for any term.
The card's further claim that `ResourceLift.constructs` introduces a second
construction notion is also wrong — it already delegates to
`AbstractCrypto.ApproximatelyConstructs`.  What *is* true is that `constructs`
takes bare resources and wraps singletons, so no set-level specification is
expressible on that carrier; per §11.29 that carrier's one model is CBC, a
randomness expander with no simulator, so this gap has **no consumer**.  No
change made.

**(d) `⇂` unused — REAL but nearly done already.**  S1's `AdversaryStructure.lean`
had adopted it; exactly **one** fully-qualified `AbstractCrypto.patternAttach`
remained (`Symmetric/MACThenOTP.lean`), now converted.  Zero remain.

**Method note.**  All four line numbers in the card had drifted, and two of its
four claims inverted on measurement.  The card was written before this session's
work and read afterwards as a receipt — the precise failure mode `doc_audit.py`
exists to catch in the three documents, but task cards are not covered by it.

### 11.34 EV1 step 1: Jost's events are NOT a third notion (2026-07-28)

`RandomSystemsCC/EventHistory.lean` (new, wired into `RandomSystemsCC.lean`).
Build green, four audits pass, admissions unchanged at 11, axiom-clean.

**The first obligation was reconciliation, not construction.**  The estate
already carried two event-flavoured notions — GegMau26's
`AbstractCrypto.EventAlgebra` (`CoheytingAlgebra` + linear-occurrence E5,
`DESIGN.md` §10.6, its own `lean_lib`, **imported by nothing**) and the
monotone-binary-output machinery (`SystemMBO`, `GameOf`, CR18 Thm 4.17) — and
Jost states outright (p. 33) that events *generalize* MPR07's MBOs.  Building a
third would have been the error the task card warned about.

**They are not a third notion, and the fit is exact:**
* Jost's composite events are the **monotone predicates** on histories (§3.2.2,
  "an event is essentially just a named monotone condition");
* monotone predicates for the extension order are the **`LowerSet`s of its
  dual**;
* GegMau26 Def 9 asks every **principal up-set** to be a chain.  The extension
  order **fails** this — `[a]` extends to both `[a,b]` and `[a,c]`, which are
  incomparable — but its **dual satisfies it**, because the prefixes of a fixed
  history are totally ordered.  That is `forestOrder`, and getting the direction
  right is the whole content: undualized, the instance is simply false.
* GegMau26's existing `EventAlgebra (LowerSet P)` for a forest `P` then applies,
  giving `compositeEventAlgebra` **by `inferInstance`, with no new axioms**.

Consequence: the `⊓`/`⊔`/`\` calculus on composite events and E5 are
**inherited rather than re-proved**, and the GegMau26 axis stops being
orthogonal — it now has its first consumer.

Also landed: `EventHistory` (Def 3.2.1, duplicate-free name list), `Occurred`,
`cons` (`ℰ ⁺← ℰₙ`, idempotent so occurrence stays monotone), `occurred_cons`
(occurrence is never retracted), the extension `PartialOrder`, `Precedes`
(Def 3.2.2) and `atom`.

**`Precedes` keeps Jost's deliberate asymmetry** — `ℰₙ₁ ≺ ℰₙ₂` holds when only
`n₁` has occurred so far — with `precedes_of_not_occurred` isolating that clause
and the docstring recording his p. 34 justification ("if we express the
condition that a message is secure if the key has been securely erased before
the memory leaked, then we do not need to insist that the memory actually
leaked").  It is not to be "fixed".

**Remaining for EV1**: event-aware resources (Def 3.2.3) over the `X × 2^ℰ`
alphabet with the definedness restriction; the compatible-distinguisher
relaxation (Def 3.3.1); composition-order invariance re-established; renaming
with Prop 3.3.3 (noting an event mapping is **not** a relaxation, p. 37); and a
worked cross-resource dependency that plain CC cannot express.

### 11.35 M1 complete: the estate's first impossibility result (2026-07-29)

`RandomSystemsCC/MauRen16Impossibility.lean` (new, 752 lines, 61 declarations,
**zero `sorry`/`admit`/`axiom`**).  Every named declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.  Endpoints 45 → 52.

```lean
theorem lemma6 (k : ℕ) {ε : ℝ≥0∞} (hε : ε < 1 / 4) (f g : Converter ℕ) :
    ¬ Constructs (honestPair k f g) ({PR k} : Set (PMF (Boundary k)))
      (Relaxation.eball ε
        (Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k}))
```

The statement lands **inside** the abstract vocabulary — `Constructs`, `eball`
and §11.32's `outboundHull` — rather than in a bespoke predicate, so the
impossibility is expressed in the same calculus as the possibility results.

**A sharpness receipt makes the content unmistakable.**
`constructs_of_correlated_honest_pair`: a single converter that samples one
`(k+1)`-bit string and hands it to *both* honest interfaces constructs
`PRᵏ⁺¹⟦` **exactly, at `ε = 0`**.  So Lemma 6 is about `π` being a *pair of
converters with independent randomness*, not about how much randomness the
system contains.  `PRsucc_mem_outboundHull` is the non-vacuity receipt.

**TWO DISCREPANCIES WITH THE PAPER, both checked by hand.**

1. **The displayed real-side identity on p. 14 does not hold.**  The paper
   bounds `Pr[Z_A = Z_A' ≠ Z_E]` by `Pr[Z_A = Z_A']·Pr[Z_E ≠ Z_A']` and then
   equates `Pr[Z_E = Z_A']` with `Pr[Z_A = Z_A']`.  With `q` the law of `πᴬ`
   and `p` that of `πᴬ'` (which `Z_E` shares), those are `∑ₐ p(a)²` and
   `∑ₐ q(a)p(a)` — equal only when `p = q`.  Conditioning on `Z_A' = a` gives
   the true value `∑ₐ q(a)·p(a)·(1 − p(a))`.  **The `¼` survives**, but
   `x(1−x) ≤ ¼` must be applied *inside* the sum.  `real_probZero` proves the
   corrected form; `mul_le_quarter_of_add_eq_one` is the maximization step in a
   subtraction-free shape.
2. **`D₁` is universal only because `π'` reads at most `k` bits, which the
   paper never says.**  Counterexample: `k = 1`, `πᴬ = πᴬ' =` "read twice,
   output `w₁w₂`", with `ℛ`'s right interface answering the `i`-th read with
   the `i`-th bit of `Z_A`.  All three readings then coincide on both sides and
   `D₁`'s advantage is `0`.  That `π` is still ruled out — its `Z_A` lives in
   `{00,11}` while `ℛ`'s is uniform on four values — but only by a
   `π`-*dependent* test, and the elegance of MauRen16's argument is precisely
   that `D₁` is universal.  **Lemma 6 is not false**; its proof is incomplete
   for multi-read converters, and the one-shot carrier is what restores it.

**Min-entropy: built minimally, since none existed.**  `guessProb` (`2^{-H_min(X|Y)}`
as a supremum over *randomized* guessing strategies — same number as the paper's
function form, and the form the proof needs since the guesser is the
probabilistic `π'`), `minEntropy`, `condMinEntropy`,
`econdGuessProb_le_card_mul_iSup` (eq. (11) exponentiated, edge-case-free, and what
the proof actually consumes) and `minEntropy_marginal_sub_logb_card_le_condMinEntropy` (eq. (11) as printed, its two
positivity side conditions **discharged**, not assumed).  Nothing else.

**§11.32's precondition is discharged here, not assumed**: `rightOutbound_all`
proves every resource on a read-only boundary is right-outbound, so
`subset_outboundHull` applies.

**Accepted cost, recorded as debt.**  The file owns a *purpose-built one-shot
carrier* (`Boundary k := ℕ × ℕ × Fin (2^k)`) rather than reusing
`TypedFinite`'s, because that carrier's converter primitives are deterministic
by its own docstring and randomized `πᴬ'` is load-bearing — with deterministic
converters the real-side event has probability 0 and the sharpness receipt
becomes invisible.  Eve's alphabet `Fin (2^k)` is **forced, not chosen**:
`d(πPRᵏ, ℛ)` compares two resources through one distinguisher, so `ℛ` must
offer `πPRᵏ`'s right interface, which is `PRᵏ`'s.  That turns the paper's
unstated "`π'` takes as input only a `k`-bit string" into a **typing fact**, and
it is where the `2ᵏ` in the chain rule comes from.  This is a third carrier in
the bridge (cf. §11.29) and should be revisited if `TypedFinite` ever gains
randomized primitives.

### 11.36 N2: construction assembly on the carrier that holds the endpoints (2026-07-29)

New module `RandomSystemsCC/TypedConstruct.lean` with the permanent usability
gate `RandomSystemsCC/TypedConstructChecks.lean`, both wired into
`RandomSystemsCC.lean`.  Build green (`lake build RandomSystems
RandomSystemsCC`), all four audits pass, admissions unchanged at **11**,
endpoints 45 → **52**, surface violations 0, performance escapes unchanged at
1, 0 regressions.  Everything new is axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`).

**The premise that was wrong.**  The task card said there was "exactly ONE"
RS-side tactic and listed four AC assemblers (`ac_compose`, `ac_simulator`,
`ac_context_left`, `ac_transfer_property`) as non-existent; a re-measurement
supplied a ten-name correction.  Both are wrong.  `AbstractCrypto/
ProofAutomation.lean` defines **sixteen** commands plus the `ac?` diagnostic,
including all four the card called missing.  The real finding is the one
neither list states: **not a single `ac_*` command was used anywhere under
`RandomSystemsCC/`** before this task.  The gap was never a missing AC
assembler; it was that `cr18_construct` serves `CR18.Resource U` (one
downstream model, CBC) while every `CC.SecurelyConstructs` judgment,
`Symmetric/**` and `Frost/**` live on `TypedFinite.Phi I U`, which had no
construction tactic at all.

**`rs_construct`** is the `Phi` analogue of `cr18_construct` and discharges
the same four things: typed composition, the converter action
(`primitive_smul_coe_prob`), boundary alignment (`edist_coe_prob` — off the
diagonal the heterogeneous carrier answers `⊤`, so a distance goal is only
informative inside one fibre) and the `ℝ`/`ℝ≥0∞` boundary
(`edist_coe_prob_le_advantage`, the sound direction only, as on the
fixed-signature carrier).  It leaves the paper's leaf: the CR18 advantage `Δ`
when the radius is displayed as `ENNReal.ofReal`, the native
`DependentPDS.contextualEDist` otherwise.

*Tactic-engineering finding worth keeping.*  The radius shape test must run
`with_reducible`.  At full transparency the unifier tries to decide whether an
opaque `ε : ℝ≥0∞` is an `ENNReal.ofReal`, and that search alone exhausts
`maxHeartbeats` — measured, not guessed.  Reducible transparency makes the
test syntactic and the whole ladder cheap.

**Three assembly facts** were being re-derived inside models and are now
stated with the model removed: `availability_of_security` (MauRen11 Definition
3's availability clause from its security clause, given simulator idleness on
the assumed resource and honest/filter commutation — this is
`OTP.availability_eq_of_security_eq`), `commute_honest_of_supported` (Theorem
1(i)'s commutation premise from simulator support — this is
`MACThenOTP.commute_honest_simulators`, which is now *proved by it*, the only
model rewiring in this task), and `mem_zSub_of_supported` (LiuMau20 admission,
inline in `OTP.otpSimulators_eq_zSub`).

**Wrapped vs. skipped AC assemblers** — the full table with reasons is the
header of `TypedConstructChecks.lean`.  Wrapped where this carrier owns a leaf
the AC command cannot reach: `ac_commute using` → `rs_commute` (the admitted
class is `supportedOn Z ⊤`, the premise is at `Zᶜ`; the double complement must
be normalized), `ac_triangle via` → `rs_triangle` (the goal is a construction
judgment, not a distance), `ac_nonexpand` → `rs_nonexpand` (there is no
`IsNonexpandingSMul (Primitive …) (Phi …)`, so the bare-converter form falls to
`Primitive.edist_act_le`), `ac_compose` → `rs_compose` (the endpoints are
`CC.SecurelyConstructs`, whose composition carries the extra commutation
premise).  **`ac_simulator` deliberately not wrapped**: it targets
`Relaxation.star simulators` while this estate's leaf is LiuMau20's
`zSub tupleGamma Z` existential, so reusing it would silently change which
ideal specification the statement is about; `rs_simulator` targets the leaf
that is actually there.  `ac_parallel`/`ac_context_left`/`ac_context_right`/
`ac_compose_simulators` need protocol-side `Par`/`SMulParClass`, refuted for
this carrier by §11.5 and §11.10.1 — a wrapper would be unusable by
construction.  `ac_relax`/`ac_filtered`/`ac_transfer_property` have no consumer
here.  `ac_construct`/`ac_normalize`/`ac_routine`/`ac_transport` fire unchanged
and are pinned by receipts rather than aliased.

**Token trap: measured, and worse than expected.**  The new sentences add
exactly **two** parser atoms, `availability` and `composition`, each verified
to have zero code occurrences in either repository; every other content word is
parsed as an `ident` and validated by `expectWord`, so `construction`,
`simulator`, `protocol`, `honest`, `filter`, `advantage`, `coupling`,
`distinguishing`, `secure`, `admitted`, `commutes` and `idle` all remain usable
as Lean identifiers — which the gate compiles as binders.

The measurement also surfaced a **pre-existing** collision that predates this
task: the Condition-C and H-coefficient sentences already atomized the articles
and common nouns `the`, `a`, `is`, `in`, `of`, `to`, `at`, `on`, `no`, `one`,
`most`, `least`, `it`, `this`, `real`, `ideal`, `bound`, `event`, `game`,
`ratio`, `defect`, `probability`, `good`, `bad`, `equal` and `world(s)`.  None
of these can be a Lean identifier in any file downstream of
`RandomSystemsCC.ControlledNaturalLanguage`.  Two consequences, both verified
by compilation: (i) that import cannot reach `Symmetric/OTP.lean`, which binds
`ideal`-adjacent names, without renaming; (ii) three AC sentences —
`cnlReplaceProtocol`, `cnlUseSimulator`, `cnlParallelContext` — parse the
article `the` as an `ident` and therefore **cannot parse at all** once the RS
controlled language is imported, since an atom always beats `ident`.  The fix
is AC-side (atomize the articles there too, as this module does) and was left
out of scope; `TypedConstructChecks.lean` records the measurement and pins the
AC sentence that still works (`The construction follows from ⟨fact⟩`).

**A correction I owe.**  When briefing this work I told the agent the card's AC
tactic list (`ac_compose`, `ac_simulator`, `ac_context_left`,
`ac_transfer_property`) named commands that *do not exist*, having grepped for
them.  **They all exist.**  `AbstractCrypto/ProofAutomation.lean` declares
nineteen atoms; the seven I missed are exactly those whose atom carries a
**trailing space inside the string literal** (`"ac_compose "`), which my pattern
`"ac_[a-z_]*"` could not match.  The card was right and my correction was wrong —
and the same bug sat in `doc_audit.py`'s `TACTIC` regex, which is why those
commands were invisible to the staleness gate too.  Both regexes are fixed.

### 11.37 Does GegMau26 already settle Jost's open questions? No — but it names one (2026-07-29)

Asked because it is the right question to ask before spending effort on an
"open" problem: `papers/2026-1071.pdf` (Gegier–Maurer, *Event Algebras and
Applications to Cryptography*) is in the repo and `DESIGN.md` §10.6 already
adopts it, so it is a natural candidate to have resolved Jost Ch. 5's open
question of whether the from- and until-**relaxations** commute.

**It does not, and the reason is a difference of objects.**  GegMau26
axiomatizes the algebra of *events themselves* — a bounded distributive lattice
with co-implication `(E; ≼, ∧, ∨, ∸, ⊤, ⊥)` — and its theorems are **universal
event inequalities**, statements like `e ≼ f ∨ g` holding in every event
algebra.  Jost's question is about **relaxation operators on specifications of
systems**, which are *indexed* by events but are not event-algebra terms, and
are defined by *equality of projected systems*.  The paper says as much in §1.4:
its contributions are "a priori incomparable to the abstract theory of systems
of [Maurer]; the two theories are compatible on a more concrete level".

**But it explicitly names Jost Ch. 5's subject as future work** (p. 5): "more
advanced guarantees (e.g., **commitment-type guarantees**) can be captured by a
more complex type of event-algebraic theorems, which state that (at least) one
of several inequalities is satisfied."  Commitment-type guarantees are exactly
what Ch. 5 exists to solve, and the suggested shape — *disjunctions* of
inequalities rather than single ones — is a concrete lead for CR1/IW1 (§#32).
Named, sketched, not done.

**Where the two papers genuinely meet is §11.34**, and that is already banked:
Jost's composite events *are* GegMau26 event algebras, so the `⊓`/`⊔`/`\`
calculus and E5 were inherited rather than rebuilt.

Method note: a text extraction of that PDF returned zero hits for *every* probe
term including "event", i.e. it was decoding garbage rather than reporting
absence.  It was discarded and the pages read visually.  A zero-hit search is
evidence only once the extractor is shown to work on a control term.

### 11.38 EV1 complete: event-aware systems, composition, renaming, worked example (2026-07-29)

Three new modules wired into `RandomSystemsCC.lean` — `EventAware.lean` (578),
`EventComposition.lean` (615), `EventChannelExample.lean` (410).  Build green
(8435 jobs), four audits pass, admissions 11, endpoints 52, 0 regressions.  Every
new public result `[propext, Classical.choice, Quot.sound]` or a strict subset;
`queryMapBase_comm_queryMapEvents` depends on **no axioms**.

**On the main carrier** (`DependentDDS`): `withEvents U N` realizes Jost's
`𝒳' := 𝒳 × 2^ℰ` as an ordinary `SignatureUniverse` with codes unchanged, so
`Boundary`/`Query`/`Resource`/`Primitive` transfer *definitionally*.
`IsEventAware` is Def 3.2.3 verbatim — both clauses instances of one relation
`ExtendsWithin`, the resource's at `𝒩_R`, the environment's at `𝒩_Rᶜ`.
`IsEventAware.disciplined` ⟷ `isEventAware_of_disciplined` proves the carrier
predicate and the trace predicate are the *same* condition, in both directions.
`act_comm_withEvents` is Prop 2.2.3 discharged by the estate's existing
`Primitive.act_comm` **instantiated** — that it is literally the old theorem is
Jost's own claim that event-awareness does not affect composition-order
invariance.  `chanResource_isEventAware` witnesses `IsEventAware` on a real
resource, so the predicate is not vacuous.

**PREMISE CORRECTION (the brief's, and a naive reading of p. 34).**  The
composite of two event-aware resources is **not** event-aware "because each
component is" — that direction is false.  Taking `[R,S]`'s domain to be "both
projections legal in their components" yields a system whose *global* clause 2
at `𝒩_R ∪ 𝒩_S` is **strictly stronger** than the conjunction of the components'
clause 2; the counterexample is an `R`-step then an `S`-step where the
environment hands `S` a history not extending `R`'s last output.  The
load-bearing statement is the **converse**: every globally legal interaction
*projects* to a legal one per component, and that is exactly what disjoint
event-sets buy — the other component's appends land in `𝒩_Rᶜ`.
`ParDisciplined.proj` is that theorem; `proj_fails_without_disjoint` is the
sharpness receipt; Def 3.3.1 compatibility closes the loop (`disciplined_run`).

**Renaming (§3.3.2)**: `renameHist` reuses step 1's idempotent `cons`, so
"duplicates dropped" is free.  `queryMapBase_comm_queryMapEvents` is **Prop 3.3.3
first equation**, `proj_renameTagged` the **second**, and
`renameSpec_not_inflationary` is the explicit **non-theorem** that an event
mapping is not a relaxation (Def 2.2.6 needs `R ∈ φ(R)`; a one-name rename
breaks it, so none of Prop 2.2.7 is available).

**Two smaller findings.**  `Precedes` is **monotone** (`precedes_mono` — both of
Jost's disjuncts survive an extension), which is what makes `precedesEvent` a
legitimate `CompositeEvent`.  And step 1's deliberate asymmetry earns its keep in
`chanLeak_of_leaked_first`: memory leaked, message not yet sent ⇒ already
compromised — the cross-resource dependency plain CC cannot express without
multiplexing (`DESIGN.md` §11.1 rule 2).

**Honestly not connected, four items.**  (1) `[R,S]` is *not* a second
`DependentDDS` combinator: the estate's `parallel` composes at a `sumBoundary`
under `HasSumCode`, one interface set carrying sum codes, while Jost's `[R,S]`
joins *disjoint* interface sets around a *shared* event component —
Only the event-axis content is proved.

  **Corrected 2026-07-29** (the original wording, "which is false", was an
  unverified assertion I propagated): `HasSumCode (withEvents U N)` is **not
  false** and is **not proved either way** anywhere in the tree.  What is true,
  and checked, is that it is **not inherited** from `HasSumCode U`.  Taking
  `U`'s own `sumCode`, `input_eq` would require
  `(X ⊕ Y) × ℰ = (X × ℰ) ⊕ (Y × ℰ)` — which *is* a genuine equivalence
  (`Equiv.sumProdDistrib`, verified to typecheck) but **not a type equality**
  (`rfl` fails, verified).  The obstruction is therefore that `HasSumCode` is
  stated with `=` on types where only an `Equiv` holds.  That makes the fix
  concrete — relax the class to an equivalence, or supply the transport — rather
  than a wall, and it is the decision CR1's parallel rule turns on.  (2) "the ε-relaxation quantifies
only over compatible distinguishers" is **documented, not wired** — no
`DistinguisherClass` is constructed.  (3) Prop 3.3.3's first equation is proved
at the alphabet/query level, which is what Jost's one-line proof asserts, but is
not an equation between two attached resources.  (4) Renaming's "undo" uses
`injOn` + freshness rather than Jost's recalled modification list.

### 11.39 Jost's open question: a CLAIMED affirmative resolution (2026-07-29)

**Status: claimed, not established.**  Recorded here because the argument
survived my own check of its two load-bearing steps; it is *not* banked until
formalized (task #43).

**The question** (Jost thesis p. 101, also open in the CRYPTO 2020 full version,
ePrint 2020/092): the from- and until-*projections* commute — does the same hold
for the two *relaxations*?

**Claimed answer: yes**, and in the strong three-way form
`(R^{[P₁})^{P₂]} = R^{[P₁,P₂]} = (R^{P₂]})^{[P₁}`, for every event-aware resource
and **arbitrary** predicates `P₁, P₂` — monotonicity *not* required.
Equivalently the two kernels permute, with join the kernel of the composite.

**The proof, which I checked at the combinatorial level.**  At a position after
`i` queries let `W` = "`P₁` held at every query so far" — exactly the
sub-transcripts `from` forwards — and `V` = "`P₂` held at none", what `until`
forwards.  Both are prefix-closed **by construction**, which is precisely why no
monotonicity is needed.  Glue: `T := R` on `W`, `T := S` on `V \ W` (disjoint).
On a `W`-sequence every prefix lies in `W`, so `T = R` throughout.  On a
`V`-sequence prefix-closure of `W` splits it as `1..m` in `W ∧ V` then the rest
in `V \ W`, so `T` emits `R|≤m · S|>m` against `S`'s `S|≤m · S|>m` — equal
exactly by the hypothesis that `R` and `S` agree on `W ∧ V`.  `T` is canonical:
witnesses can differ only on `¬W ∧ ¬V`, which no projection observes.

**Necessity is the interesting half, and I checked it too.**  Event-awareness
(Def 3.2.3) is indispensable; history-blind the statement is **false**.  Take
`P₁ = P₂` = "`a` occurred", resource event-set empty, `R ≡ 0`, `S ≡ 1`.  The
window `W ∧ V` is empty, so the hypothesis holds *vacuously*; but the
`from`-wrapper forwards everything on the all-`a` history, forcing `T` to answer
`000`, while the `until`-wrapper forwards everything on the empty history,
forcing `111`.  A history-blind `T` receives the identical query sequence in both
— and for randomized `T` too, these being distinct point masses.  So the
affirmative answer holds **because of Jost's own Chapter 3**: global events are
exactly what let one resource occupy two otherwise incompatible roles.

**Provenance and caution.**  The agent **self-corrected twice**, having claimed
first that `P₁`-monotonicity and then that the drop semantics of `from` were
load-bearing; both turned out to be properties of its construction, not of the
theorem.  That is the adversarial process working, but it also means earlier
write-ups were wrong, so everything not re-derived here is *claimed*.
**Unchecked**: that Thm 5.3.12 is non-tight (the union over `n` collapsing at
`n = 2`); that the outer relaxation in B.1.1 Claim 1 is redundant; the finite
model runs; and the literature check reporting no prior resolution.

**Scope unchanged**: nothing touches the ε-relaxation.  Thms 5.3.5 and 5.3.10
(non-commutation with ε) stand, and Def 5.3.15/Thm 5.3.16 are unaffected —
which matters, since those are what justify the sandwich definition.

**A structural point worth keeping**: the abstract layer could never have decided
this.  Commuting idempotent retractions need not have permuting kernels (a
3-element counterexample is claimed), so the answer comes from the system algebra
supplying surjectivity onto the pullback, not from the retraction calculus.

### 11.40 HasSumCode relaxed to an equivalence — the event carrier gains parallel composition (2026-07-29)

Build green (8435 jobs), four audits at baseline (admissions 11, endpoints 52, 0
regressions), `ccSurfaceAudit --axioms` 52/52 audited.  **`CBC.lean` shows no
diff at all.**  Also green: `RandomSystemsApplications`,
`RandomSystemsLegacyBridge`, `RandomSystemsSwitchingDemo`.

**The defect was a class demanding more than it used.**  `HasSumCode` stated its
alphabet laws as *type equalities*
(`U.input (sumCode a b) = U.input a ⊕ U.input b`).  Its two `TypedParallel`
consumers immediately did `Equiv.cast` on that field, so equality was strictly
surplus — and the surplus is exactly what excluded any signature whose alphabets
distribute only up to isomorphism.  `withEvents U N` is such a signature:
`(X ⊕ Y) × ℰ` and `(X × ℰ) ⊕ (Y × ℰ)` are `Equiv.sumProdDistrib`-equivalent but
**not equal** (both halves verified: the equiv typechecks, `rfl` fails).  Since
`Resource.instPar` needs `[HasSumCode U]`, the whole event carrier had **no
parallel composition at all** — which is what blocked Jost's `[R,S]` (§11.38's
deferred item 1) and CR1's parallel composition rule.

The class now carries `inputEquiv`/`outputEquiv`.  **Payoff, verified by
`inferInstance`:** `Par (Phi I (withEvents U N))` and
`IsNonexpandingPar (Phi I (withEvents U N))` both resolve, the latter being the
metric premise of `CC.SecurelyConstructs.par`/`par_left`.  §11.38's item 1 is
therefore **withdrawn**: `[R,S]` on the event carrier is not obstructed.

**The transports were the real work, and the tool already existed.**  Nine
consumers, not the two an early truncated grep suggested — eight in
`ResourceParallel.lean` transporting a whole `System` along the equalities via
the since-deleted `System.castEq`.  `RandomSystems.StrictRelabel` (built for
the strict layer) supplies `System.relabel` along equivalences plus
`edist_relabel` — relabelling is an **isometry**, the exact analogue of
the deleted `edist_castEq` — and it composed as that transport did, so nothing had to be
restated.  Only the `System`-level inverse/injectivity was missing
(`relabel_symm_relabel`, `relabel_relabel_symm`, `relabel_inj`, `relabelEquiv`);
the `DDS`/`PFunPDS` levels already had them.

**One genuine behavioural difference, worth keeping in mind.**  The
deleted lemma `castEq_rfl` held *definitionally*, so the transport at reflexivity reduced to
`⟨sum, s⟩` and a proof in `ParallelChecks` was a bare `show`.  `relabel` at the
identity equivalence is only *propositionally* the identity — it goes through
`Quotient.liftOn` — so that proof needed one `congrArg … (System.relabel_refl _)`
step.  That is the sole cost of the generalization.

**The equality-only transport was deleted as dead code.**  `System.castEq` no
longer exists, and `castEq_rfl`, `edist_castEq`, `castEq_inj` are deleted too.
Verified zero consumers across this repo, the sibling package and
`sequence-hash/`; its own docstring had also gone stale, asserting a consumer it
no longer had.  A note stands in its place explaining why an equality-only
transport was strictly weaker.

**A false positive worth recording**: grepping `input_eq`/`output_eq` also hits
`CBCModel.lean:56,57,74,75`, but those are fields of `HasResourceCode`, a
different class.  No change was needed there.

### 11.41 Jost's open question RESOLVED on the deterministic event carrier (2026-07-30)

`RandomSystemsCC/RelaxationFibre.lean` (new, 225) + `IntervalRelaxation.lean`
(new, 1000), wired into the root.  Build green (8437 jobs), four audits at
baseline, admissions 11, endpoints 52, 0 regressions.  All 21 new public theorems
`[propext, Classical.choice, Quot.sound]`; the pure-`Set` ones only
`[propext, Quot.sound]`.  No `sorry`, no `native_decide`, no heartbeat bumps.

**The result.**  `fromThenUntil_eq_intervalRelax` and
`untilThenFrom_eq_intervalRelax` give
`(R^{[P₁})^{P₂]} = R^{[P₁,P₂]} = (R^{P₂]})^{[P₁}`, and
`intervalRelax_union_collapse` shows **Thm 5.3.12's union over `n` collapses at
`n = 2`** — its outer relaxation is redundant.  Specification level:
`spec_untilRelax_specFromRelax` / `spec_fromRelax_specUntilRelax` (obligation 2
discharged, not assumed).  Def 5.3.11's `until ∘ from` orientation is kept
verbatim.  This refutes the p. 101 hedge that the combined relaxation
"apparently neither corresponds to" either two-fold composite.

**SCOPE — the honest limit.**  This is the **deterministic** event carrier
(`DependentDDS (withEvents U N) σ`).  The estate's `Resource I U` is
`Quotient (DependentPDS.Prob.contextualSetoid …)` over `Dist`, and Jost's
resources are probabilistic, so **#43 is not closed for the probabilistic
setting.**  The remaining gap is stated precisely and is *not about the
relaxations*: it needs a finite-support **measure-gluing lemma** — the fibrewise
product coupling of two laws over a common pushforward has those laws as its
marginals — plus a check that `untilP`/`fromP` respect `contextualSetoid`.  The
recipe and the already-proved ingredients are recorded in the module.

**(A) The abstract layer, and a sharper fact than I asked for.**  I briefed
"permute ⟺ composite transitive ⟺ join"; that was never needed.
`fibreComp_swap_of_eq_fibre` shows the collapse in *one* order **forces** the
other, from symmetry of a fibre relation alone — no idempotence, no commutation,
heterogeneous codomains.  That halved (B): only Jost's printed orientation had to
be proved.

**The abstract layer provably cannot decide the question.**
`Blocked.fibreComp_ne_fibre` / `fibreComp_ne_swap`: two **idempotent, commuting**
retractions on three elements whose fibre relations **fail to permute**
(`by decide`).  Since Jost proves the *projections* commute, no retraction
calculus could have settled the *relaxations* — the answer must come from the
system algebra.

**(C) Event-awareness is necessary.**  `Necessity.historyBlind_collapse_fails`:
the collapse **fails** for history-blind resources, with `not_mem_fromRelax` /
`not_mem_untilRelax` as non-vacuity (each factor separately separates the pair
that `intervalRelax` identifies, so the composite is strictly coarser).  The
affirmative answer holds *because of* Jost's Ch. 3 extension.

**Two premises of my brief were wrong, both correcting the model.**
1. **`⊥` cannot be modelled by leaving `DependentDDS.domain`.**  `until_P(R)`'s
   defined region is prefix-closed, but **`from_P(R)`'s is not** — it rejects
   early queries and accepts later ones — while `domain` is prefix-closed *by
   fiat*.  So the projections are `Option`-valued total answer maps
   (`none = ⊥`), paid for with two faithfulness receipts: `answers_injective`
   (the flat reading determines the resource, so nothing is coarsened) and
   `getLast?_accepted` (the interface tag is not lost).
2. **The drop-vs-mask fork had to be settled from the page.**  Figures 5.2/5.3
   (`require X` then "[rest as in SecChDg]") show a rejected query returns `⊥`
   **and the state update is skipped** — queries are *dropped*, not masked.  This
   matters: under masking the theorem is nearly trivial (observed regions are
   pointwise, gluing needs no prefix-closure); under dropping the reindexing is
   real and the window argument is doing work.

**Monotonicity: unused in the proof, load-bearing for faithfulness.**
`holdsAt_mono` is stated and **never used** (verified by grep — only its
declaration and a docstring mention).  The windows are the `∀`-forms, and they
coincide with Jost's *local* phrasing because Def 3.2.3 clause 2 forces
`ℰ_{X₁} ≤ ℰ_{Y₁} ≤ ℰ_{X₂} ≤ …` to be a chain, on which monotone `P` makes "held
earlier" equal "holds now"; transcripts breaking that chain are outside every
event-aware resource's domain and contribute `⊥` on both sides.  So the
*statement* is Jost's and the *proof* generalizes.

**`moduleAudit`**: a new `RandomSystems/BonehShoup/` tree (2 modules) appeared
from a concurrent session and is marked `owner-reserved` — reported every run,
not gating, same treatment as `RandomSystems/SoP/**`.

### 11.42 CR1: context-restricted constructions — and Thm 4.2.6's iff is not proved in the source (2026-07-30)

`../abstract-crypto` commit `3b14ff0`: `AbstractCrypto/ContextRestricted.lean`
(903) + its test lib (190).  **Deliberately placed in the sibling package**, so
`htechniqueSurfaceAudit`'s `Constructs` token rule never applies and
`BRIDGE_STATEMENT_FILES` stays untouched — a cleaner answer than sanctioning a
new file.  Every declaration `[propext, Classical.choice, Quot.sound]` or less;
`subset_closure` and `mem_closure_paperForm` depend on **no axioms**.  No
`sorry`/`admit`/`axiom`/`native_decide`/`set_option` in either file.

Def 4.2.1/4.2.2 as printed, stated against **`reductionRelaxation`** (the
distinguisher-indexed ε, JM20 Def 3) rather than the scalar `eball` — Jost's
`ε_C` maps distinguishers to `[0,1]`, so this is the faithful reading.  Prop
4.2.5 both directions; Thm 4.2.6 both rules, each a genuine `iff` **on the
rule**, with `R S T` quantified *inside* the left-hand side (they must be: the
side condition never mentions them, so no fixed triple could characterize it);
Prop 4.2.7 including `closure_contextId_eq_univ`.

**FINDING — Thm 4.2.6's `iff` is not actually proved in the source.**  The
"reverse direction" paragraph (pp. 50–51) assumes the rule fails and derives that
some `𝒞₂`-context lies outside `𝒞̄₁` — i.e. it argues `¬rule ⟹ ¬condition`,
which is the **contrapositive of the soundness half it had just proved**, not the
converse.  Genuine necessity needs a separating pair of specifications for every
context outside `𝒞̄₁`.  That is isolated as `ContextSet.ClosureComplete`, and its
converse `dominates_of_mem_closure` is proved **unconditionally** (it is Prop
4.2.5 read semantically), so `ClosureComplete` is precisely the missing half.
Necessity is otherwise proved outright, with `constructsRestrictedAsym_smul_self`
(`ℛ ⊢[π,𝒞]→ π•ℛ` always, at `σ = 1`, `ε = 0`) as the separating instance.

**One place the source was narrowed, flagged in the docstring.**  Thm 4.2.6's
parallel side condition prints `⊆`, not `∈`, because `𝒰` is a *specification*, so
`(f, [𝒰,P])` denotes a set.  But Def 4.2.2 grants **one** simulator per context
and the conclusion lives at the single context `(f,P)`; for non-singleton `𝒰` the
simulator would have to be uniform over `𝒰`, which the definition does not
supply.  Stated for a single auxiliary resource — which is what Fig. 4.3's `U`
box and §4.2.4's `[HK,DH]` application actually use.

**Def 4.2.4's printed one-clause set does not contain `𝒞` in this algebra.**  The
paper's "trivial" `𝒞 ⊆ 𝒞̄` takes `h = id` *and* `U = □`, and the second choice
silently collapses the neutral-slot extension — whereas MauRen11 fn. 23, quoted
in `Constructions.lean`, states `α ∥ 1 ≠ α`.  So `𝒞̄` is rendered as the set
*generated* by the clause's two moves; `mem_closure_paperForm` recovers the
displayed shape and `closure_closure` gives idempotence.

**Two laws Chapter 4 needs that this algebra deliberately withholds are opt-in,
not assumed**: parallel associativity as a mixin `IsAssociativePar` with **no
global instance** (`AGENTS.md` forbids assuming it; Jost's `n`-ary tuple former
satisfies it), and `1 ∥ 1 = 1` plus two-sided neutrality of the neutral resource
as explicit hypotheses — the idiom `Constructions.lean` already uses.

**Admissions accounting.**  The RS-side count moved 11 → 13 and endpoints 52 → 55
*during* this work, and none of it is CR1's: traced to another session's commits
`1540a3b`/`6c32a9c` (sponge indifferentiability, a new `Symmetric` module) and
`e5d9a40` (a third `UHFURFMAC` admission).  CR1 edited nothing under
`random-systems/`, and the audit's own regression counter stayed 0.

Applications (§4.3 UCE, §4.4 psPR/psPRP, §4.5 split security, §4.6
Merkle–Damgård) are noted and deliberately not built; §4.2.4's Diffie–Hellman
example would be the natural first consumer.

### 11.43 The probabilistic lift: closed at law level, conditional at the quotient — and the gap is a known ledger item (2026-07-30)

`RandomSystems/DistCoupling.lean` (new, 221) + `RandomSystemsCC/IntervalRelaxationProb.lean`
(new, 460).  Build green (8441 jobs), four audits pass, admissions **13 → 13**
and endpoints **55 → 55** — this work adds neither.  Every new declaration
`[propext, Classical.choice, Quot.sound]`; the two abstract descent lemmas only
`[propext, Quot.sound]`.  No `sorry`, no `native_decide`, no heartbeat bumps.

**(1) The measure-gluing lemma, closed.**  `Dist.exists_coupling_of_fTransform_eq`:
two finite-support laws with a common pushforward admit a coupling supported on
the diagonal of that pushforward, with the two laws as marginals.  The division
is harmless because `apply_le_fTransform_apply` (`X a ≤ fTransform f X (f a)`)
makes the divisor vanish only on fibres null on *both* sides, where `NNReal`'s
`x / 0 = 0` is the correct value.  Landed in a new leaf module rather than
`Dist.lean` to avoid a full-tree rebuild.

**(2) The lift, closed at both pre-quotient levels.**
`probFromThenUntil_eq_probIntervalRelax`, `probUntilThenFrom_eq_probIntervalRelax`,
`probIntervalRelax_union_collapse`, and the normalized twins — on
`DependentPDS (withEvents U N) σ` *and* on `DependentPDS.Prob …`, with the
specification level and the notation receipts.  One ingredient the recipe was
missing: **`untilP_fromP_untilP`**, the interval projection factoring through
`untilP` as well as `fromP`.  Pushforward functoriality is the only tool once the
samples are hidden inside a law, so the `⊆` direction needs *both*
factorizations.  It holds because `from_{P₁}` reads its argument at a **sublist**
and the until-window is sublist-closed — again no monotonicity.

**(3) The quotient descent is CONDITIONAL, and the condition is named in Lean.**
`untilP`/`fromP` are **not** provably compatible with
`DependentPDS.Prob.contextualSetoid`, and this is not a technicality:
`lawUntilP` is equality of *laws over projected behaviours*, while contextual
equivalence compares only **acceptance masses of deterministic tests**.  Rather
than force it, the descent is proved abstractly
(`fibreComp_quotient_eq_fibre`) and the missing input is an explicit **hypothesis**
of `exists_randomSystem_collapse_of_faithful` — verified to be a hypothesis in
the signature, not an axiom.

The exact remaining claim: *for finite-support laws over deterministic partial
systems, `StrictContext.Equivalent left right → left = right`* — strict
deterministic tests separate such laws.  Via the existing
`DependentPDS.contextually_equivalent_iff_flatten_equivalent` and
`DependentDDS.flatten_injective` this is **equivalent** to the faithfulness
hypothesis.  Proving it means *constructing* the separating tests, which is
precisely the **missing action calculus (U01–U09)** already on the §11 bridge
ledger.  So this open question is not blocked on anything about relaxations; it
is blocked on a debt we had already identified.

**The obstruction is generic, which is the useful part.**  *No* projection of a
law finer than acceptance mass descends to this quotient without that
faithfulness result — the interval relaxations are not a special case.  Anyone
later trying to push a law-level construction through `contextualSetoid` will hit
the same wall, and now there is a named lemma to discharge.

**Refactor**: `spec_untilRelax_specFromRelax` / `spec_fromRelax_specUntilRelax`
now delegate to the new abstract `specFibre_specFibre_of_collapse` — statements
byte-identical (verified: no `+`/`-` on any statement line), ~20 lines of
duplicated union-moving argument deleted rather than duplicated for the law
level.

### 11.7 Replanned program (2026-07-27, after the full source reading)

**Phase I — bank the bridge.**  C3 (#5) ✅, TA (#22) ✅; **P2 (#8) partly banked
— its question is answered and its wiring is done; one honest obligation left.**

*P2's question, answered:* **E09 does not need `Par` — it cannot have it.**
E09 lives on the `TypedFinite` `Phi` carrier, which has no `Par` instance:
parallel composition is ill-posed on that converter monoid (§11.4), and P1
installed `Par` on the *other* carrier (`ResourceLift.Resource`).  So
`CC.SecurelyConstructs.par` is unavailable and the MAC secret and OTP pads
cannot be `authChannel ∥ otpKeys`; they are carried by one DDS with both
capabilities (hence `authDDS` still answering `.otpKey`).  Composition is
therefore serial, via `CC.SecurelyConstructs.trans`.

*Banked:* `mac_then_otp_securely_constructs` proven from `trans` plus
`commute_honest_simulators` (simulators supported at Eve, honest converters at
Eveᶜ — `commute_patternAttach_supportedOn`), and both composite endpoints
(`affine_mac_then_otp_*`, `polynomial_urf_mac_then_otp_*`) derived from it.
Admissions **13 → 11**.

*P2's second finding — the stage lemma is FALSE, and the file's bulk and its
falsity have one cause.*  `padAt q pads count = pads[(count-1) % (q+1)]` indexes
the pad by a **per-interface call count** (`authAliceOtpCount` /
`authBobOtpCount`).  Nothing ties the two counters to each other or to the
position of the ciphertext in flight, while `.receiveCipher` always returns the
*latest* ciphertext.  Three kernel-checked (`rfl`) counterexamples now sit in
the file: after two sends Bob's first `.otpKey` returned pad `0` while the
ciphertext he was handed had been made with pad `1`, so Bob returned
`m₂+pad₁-pad₀` against the ideal's `m₂` — off by a uniform group element, not
by `0`.  And **no `q` rescued it**: at `q = 1` Bob's *second* receive already
desynced.  So `otp_stage_securely_constructs` had to be **repaired**, not
proven — index the pad by the ciphertext's position, not by a call count.

**Repaired 2026-07-28; see §11.20.**  Those three counterexample theorems are
**deleted** — they described a model that no longer exists, and keeping
artifacts of a deleted model is how documentation rots.  Their names are
therefore no longer in the tree, which is why this paragraph now describes them
rather than citing them.

*Diagnosis — this is the `Par` gap billed twice.*  With no `Par`, two
independent capabilities (auth channel, pad store) must be multiplexed by hand
over one shared history.  That is what generates the file's bulk (four private
history-scanning helpers per resource, three resources) *and* what forced the
invention of `padAt` — a bespoke selector with a `% (q+1)` wrap added purely to
make it total, in direct violation of DESIGN §4 item 11.  A `Par`-carried pad
store would have no counters and no wrap, and the OTP stage would be
`OTP.otp_securely_constructs` composed with `refl` on the pad component.  The
verbosity was the visible symptom; the bug was the invisible one.

*The price of no `Par`, still named:* `otp_stage_securely_constructs` — the
perfect OTP construction has to be **re-established on the pad-carrying
resource**, since `Symmetric.OTP.otp_securely_constructs` lives on
`signatures G` without the pads.  With `Par` this would have been
`OTP.otp_securely_constructs` composed with `refl` on the pad component.  That
is the concrete cost of §11.4, and it is now one named lemma rather than five
scattered `sorry`s.  Remaining in this file: that lemma plus the two MAC-stage
receipts (`affine_mac_with_otp_key_*`, `polynomial_urf_mac_with_otp_key_*`).  Small, finishes what is open, and C3 was the principle's test case —
it earned its keep by *refuting* its own premise (see the C3 ledger line: the
overlap is sound, and the instance could not be deleted).  Leaving a program 60%
done is how estates rot; this phase is the discipline that keeps the rest
honest.

**Phase II — move ε from scalar to indexed.**  Now the top item, and
over-determined: it is Jost's actual definition (Def 2.2.9, Thm 2.2.11), it is
what MauRen11 never proved for parallel (§11.6), it is the route *around* the
false par-non-expansion (§11.5), and D2 already built the RS-side feasible-test
subcarrier and proved `reductionRelaxation` membership.  AC's `parRightBudget`
**is** Jost's `ε_S`.  Deliverable: make the indexed relaxation the primary error
notion, with scalar `eball` retained as the MR16 specialization it is.

**Phase III — fill L2's missing content**, in order:
1. `⊣` / right-outbound / `R[[` plus **the first impossibility theorem**
   (MR16 §3.4, §5).  We have *zero* impossibility results, and that is where
   this theory's famous results live.  Note MR16's Lemmas 3–4 are **stated
   without proof**, so formalizing them is a contribution, not a port.
   Acceptance test: `PRᵏ ↛ ROᵐ→¹`.
2. **Events** (Jost §3) — and his own framing licenses the drop-in: *"an
   alternative instantiation of Constructive Cryptography's higher-level
   axioms"*, so *"results proven at those abstraction levels directly translate
   over"*.  Prerequisite for anything adaptive or stateful.
3. Context-restricted constructions (Jost §4); interval-wise guarantees (§5).
   Note §5's until/from relaxations are defined by **equality of projected
   systems**, not indistinguishability, and neither commutes with the
   ε-relaxation — that non-commutation is the whole reason for the sandwich
   definition, and is an easy thing for a formalization to gloss.

**Dropped.**  The `⊑π` ↔ `πR ⊆ S` bridge: unbuilt in the literature (§11.6) and
needed by nobody.  `ChoiceSettings` stays as the faithful L1 §7 rendering —
live surface, not extended.  Also dropped: the `ParProtocol` fold into a monoid
claiming non-expansion (§11.5), and U2 (paper-fidelity debt with no consumer).

**Reprioritized in.**  R1 (#24), the resource DSL — see below; its `Machine`
core is built and green, and it is the only item that reduces the cost of
*writing* models rather than proving about them.

### 11.8 Resources as packages: the `Machine` core (2026-07-27)

Jost and the CC literature write resources as stateful pseudocode packages
(Fig. 2.2); we write `DependentDDS` records with a declarative `domain`, an
`empty_not_mem` proof, a `prefix_closed` proof, and — the real cost — **every
piece of mutable state re-encoded as a hand-written fold over the whole
history**.  Measured on `Symmetric/FreshOTP.lean`: 126 lines, of which ≈22 are
figure-equivalent content; **≈5× overhead**, concentrated in the error-prone
part.  A latent hazard found while measuring: fold *direction* is a silent
semantic choice — `OTP.realCiphertext?` is last-write-wins while
`MACThenOTP.sourceReplacement?` is first-write-wins, and nothing but care
distinguishes them.

The asymmetry is worse than posed: converters have `ProtocolFn.ofStep`;
**resources have no state-machine constructor at all**, only `historyEvaluator`
(raw history function) and `functionEvaluator` (memoryless).

Prototype at `scratchpad/ResourceMachine.lean` (399 lines, compiles, zero
admissions, not in any lake target): a `Machine` with `State`/`init`/`step`,
`runFrom`/`run` folds with **one** generic append lemma, and `toDDS` whose
`domain := {h | h ≠ [] ∧ (run h).isSome}` discharges `empty_not_mem` and
`prefix_closed` **once, generically, for every package** (prefix-closure is
structural for a fold).  Jost's Fig. 2.2 `AuthChan` is reproduced at **14
content lines against the figure's 14**, with zero per-model proofs; `Key`'s
`Initialization k ←$ K` becomes `lawOf … (Dist.uniform K)`.  Machine-built
resources are ordinary `DependentDDS`, so `TypedAttachment`/`TypedFraming`/
`Phi` consume them unchanged.

**The partiality answer, which is load-bearing.**  Jost's §2.1.2 defines
`require` explicitly as *returning ⊥*, i.e. rejection-as-**value** with the
interaction continuing — **every** ⊥ in every figure is a value, and blocking
divergence never occurs in his pseudocode.  Our `Part.none` (blocking, no
continuation) has **no counterpart in the source at all**, yet our models
genuinely use it (OTP's one-message budget).  So the DSL needs **two verbs
where the notation has one**: `require`-style rejection → a value in the answer
fibre; `undefined` → `step … = none`.  It must therefore **error on
non-exhaustive clauses rather than defaulting** — inserting any default would
be the fifth totalization (§11.4–11.5, DESIGN §4 item 11).

**The target model and the acceptance metric (added 2026-07-27).**  The
motivating comparison is **Lanyon.AI** (Jonathan Gorard): an LLM proposes a
formal specification in a condensed DSL, and *"purely symbolic algorithms expand
that specification into code and proofs simultaneously"* — *"Lanyon reasons at
the level of tens of lines of formal DSL, but these lines are then automatically
and instantaneously expanded into tens of thousands of lines of code and
proof."*  So the acceptance criterion is not "is the syntax nicer" but the
**ratio of author-written content lines to generated lines**, and **prelude
counts against the numerator**.  Any macro must report that ratio.

**The prelude is NOT yet minimal, and the excess is diagnostic.**  The Fig. 2.2
prototype needs ~50 lines before any cryptography: `Iface`, four input
inductives, two output inductives, `Code`, `sigU`, `chanBoundary`, `ChanState`.
Sorting them: `Iface`, the per-interface I/O types and `ChanState` are *content*
(the last is literally Jost's Initialization block), and several bespoke
inductives are avoidable (`Ok` is `Unit`, `ReceiverIn` is `Unit`, `EveOut`
collapses to `Option M`).  But **`Code`, `sigU` and `chanBoundary` are pure
indirection**: `Code` is in bijection with `Iface`, and the other two write that
bijection out.  Lean cannot infer an inductive from nothing, so no coercion
fixes this — the macro must generate them.

**Why that matters beyond ergonomics — this is §11.4 again.**  `Code` exists as
a type separate from `Iface` *only* because `replaceBoundary` lets a converter
mutate the code at an interface.  For a resource **definition** the boundary is
fixed and `Code ≅ Iface`, so the indirection is dead weight.  Mutable
per-interface codes are exactly the unattested invention §11.4 identifies as the
origin of the `HEq` boundary-transport tax and of `sumCode`.  **The DSL
verbosity complaint and the carrier-shape question are one issue surfacing
twice.**

*Consequent proposal, to be evaluated as its own item (§11.3, ledger entry
"CODE"):* default to `Code := Iface` with the identity boundary, and expose the
general code-changing form **only** where a converter genuinely changes a
signature.  This shrinks the prelude *and* reduces dependence on machinery we
already suspect.  It is a candidate simplification of the carrier, not merely of
the syntax, and should be assessed against the four totalization rows in §11.4
before anything is built on top of it.

Honest limit: this makes resources cheap to **write** (including by AI, since
the package form is the form the literature uses); it does **not** make
constructions cheap to **prove**.  The highest-leverage follow-on is
`toDDS_eq_of_bisim` — a state-coupling lemma the machine presentation makes
natural and the fold presentation makes impossible to state.  Prior art:
SSProve's state-separating packages (free monad + `valid_code` discharged by
typeclass inference) landed on the same shape independently, which is
corroboration.  Not covered by v1: event-parameterized resources (needs the
event layer, Phase III item 2) and adaptive mid-protocol sampling, which the
DSL should reject rather than simulate.

Out of scope for this program, and deliberately so: `Par` associativity /
commutativity / unit laws, an AC-level machine/asymptotic model, and event
algebras.  (MauRen11 Def 18 choice settings/CFR **was** out of scope; X3 has
since brought it in.)

### 11.4 Carrier-shape finding (2026-07-27) — the sigma is exonerated; the quotients are not

A design review asked whether the signature/boundary machinery is worth its
weight, given that AC's own contract is five lines (`Φ`, `Γ : I → Type`,
monoids, a `MulAction`, a pseudo-emetric, non-expansion) and mentions no
signatures at all.  The answer, from sources and from three tasks' evidence:

**Per-interface typing is faithful to what the sources DO.**  Jost's
Definition 2.2.1 (`papers/ThesisJost.pdf`, p. 16) types a resource as
`(X, P, ⟨I_P⟩)` with a *single* alphabet and the interface address encoded in
the input — the same shape as CR18's `Resource I A B := DDS (I × A) B`.  But
his own examples (Fig. 2.2) give each interface a genuinely different type:
`(send, m) ∈ E.C` at Alice, a bare `receive` at Bob, `(leak, i) ∈ N` at Eve,
`k ∈ E.K` from `Key`.  **The single `X` is an erasure**: the real typing lives
in the pseudo-code and is never reconciled with the definition, because nobody
machine-checks a paper.  So a flat `I × X` carrier would be faithful to what
the source *writes*, and ours is faithful to what it *does*; the transport cost
is the price of closing a gap the paper leaves open.  Extensionally the two are
the same object — `Σ i, Xᵢ ≅ {(i,x) ∈ I × X | x ∈ Xᵢ}` — and we have both
presentations already (`flatten`, `flatten_injective`, `TagFaithful`).  The
difference is only where well-typedness lives: intrinsic typing charges on
every signature change, extrinsic charges once per definition.

**Every structural defect found in this program traces instead to a place we
made something TOTAL or QUOTIENTED it, beyond the source.**

* **extensional Γ** — MauRen11 never quotients its constructor set; Γ is a set
  of *programs* closed under `∘` and `|`.  We quotiented by action-equality
  (DESIGN §10.9) to avoid needing a representation theorem.  **MauRen11 fn. 23
  is the incompatibility notice we quotiented past**: the values of `α ∥ β` off
  `‖`-shaped resources are deliberately junk, while action-equality quantifies
  over *all* resources, junk included — so action-equal words need not have
  action-equal parallels and no representation-independent `Par` exists on the
  quotient.  Extensionality is sound for serial composition (action determines
  it) and unsound for parallel.  **AC never asked for it**: its contract admits
  any monoid with an action, which the paper's syntactic Γ satisfies directly.
  → task #21.
* **silent-identity action** — a converter at a mismatched code becomes the
  identity, so a misplaced converter yields a construction theorem that is TRUE
  AND EMPTY, and `smul_par` breaks.  → task #5, promoted from hygiene.
* **totalized attachment** and **inferred `HasResourceCode`** — no defect
  observed yet for the first, which is why it deserves the look.  → task #22.

**Method lesson.** The extensional-Γ rationale read as principled and was
documented; the failure was that it was never tested against the operations it
had to support, and it was not tested because `Par` was uninstantiated — and
`Par` was uninstantiated because §11.1 rule 2 told authors to work around it.
**The workaround hid the defect that made the workaround necessary.**  An
uninstantiated feature cannot refute a design decision, which is an argument
for building the receipt early even when nothing consumes it yet.

**The audit's verdict (TA, #22, 2026-07-27) — and the criterion it produced.**
Row 4, **totalized attachment**, was the one convenience never examined, and the
prior that it hid a defect is **refuted with a reason** rather than by absence of
evidence: the applicability guard `code = primitive.source` is
**code-determined**, and `boundaryEDist` separates unequal codes at `⊤`, so the
identity-default branch is **constant on every finite-radius metric ball** — it
can never pin one point while moving a δ-close one, which is all non-expansion
breakage needs.  `edist_act_le` is proven unconditionally.  Contrast the
parallel action (§11.5), whose guard `∃ R S, R ∥ S = A` is *not* code-determined:
decomposable and correlated resources coexist at one sum code at distance δ,
which is exactly the counterexample.  **Rows 3 and 4 differ by precisely that
property.**  Jost Def 2.2.2's inner-query partiality was moreover handled by the
sanctioned move — *restriction* (`IsDDC` carries `AnswersWithin`) — not by
totalizing.  Verdict: keep, no new task.

So DESIGN §4 item 11 sharpens from a blanket prohibition into a test:

> **A totalizing default is metrically safe iff its guard is code-determined;
> and totalize toward rejection (`⊤`/`none`/`false`), never toward acceptance
> (identity).**

`boundaryEDist … else ⊤` is the polarity exemplar — it makes malformed
cross-code claims *false and unprovable* rather than true, and is what
neutralizes the attachment default metrically.  The audit found **no sixth
instance**; the only one still open is the CR18 `s⊥` completion (task #28).

**A new and worse defect, found inside row 2's blast radius.**
`ConverterTerm.mul` imposes **no source/target compatibility between factors**
(`TypedFinite.lean:86`, verified).  So for `w = p₂ ∘ p₁` with `p₁ : A→B` genuine
on `R` and `p₂ : C→D`, `C ≠ B`, the guard fails after `p₁` and `p₂` acts as the
identity: `w • R = p₁ • R`.  The provable theorem `{R} —[w]→ {p₁ • R}` is **not
vacuous** — it is a substantive construction claim **whose protocol label lies**.
That is strictly worse than the single-primitive vacuity already booked, and it
means C3's fix must operate on **words**: a syntactic well-typedness judgment on
`ConverterTerm`, which only became definable once G1 made Γ syntactic.  G1
therefore enabled the fix for a defect it did not cause.  Note also that the
attachment row's residual cost is *entirely* this statement-level hazard — the
fix is a well-placedness obligation at the statement boundary, **not** a change
to the metric or to `MulAction` totality.

**Status of the fix (2026-07-27).**  `TypedFinite.Gamma` is now syntactic
(commit `4f1f482`, task #21 phase 1), and the migration cost exactly what was
measured: one file, one 2-line proof repair, endpoint statements untouched at
the character level.  The probe's most reassuring finding: **zero genuine
action-versus-equality conflations exist downstream** — converter equality
became strictly finer and no proof in the tree noticed, because every endpoint
protocol equality is between structurally identical words.  So the quotient was
never buying anything; it was only costing.

**Phase 2 landed the same way (2026-07-29, task #21 phase 2).**
`ResourceLift.Protocol` was the last extensional converter monoid; it is now
`Quotient (ConverterTerm.setoid U)`, with `protocolInclusion` interpreting into
`nonexpandingEnd (Resource U)` and
`mrange_protocolInclusion_eq_generatedConverterMonoid` proving its range is the
old `Submonoid.closure (primitiveRange)` — kept under the name
`generatedConverterMonoid`.  **The migration cost was zero repairs**: two files
edited (`ResourceLift.lean`, `ResourceParallel.lean` — the latter docstring
only), no proof anywhere in the tree changed, and `CBC.lean` was never opened.
Phase 1's null result held on the second carrier as well; the elaborated types
*and* the `#print axioms` footprints of all four CBC endpoints are byte-identical
before and after.

The remaining item on this thread is not a defect of the same kind:

* Unifying `TypedFinite.Gamma` with `ResourceLift.Protocol` is blocked by C4
  (typed `Phi I U` versus flat `Resource U`) and by the absence of `Par` on
  `Phi I U`, not by extensionality.  The two protocol monoids on `Resource U`
  (`Protocol`, `ParProtocol`) are now both syntactic and differ only in the
  *codomain of their interpretation*: `Protocol` lands in `nonexpandingEnd` and
  therefore asserts MauRen16 Definition 2 for every element, `ParProtocol` acts
  into plain functions and asserts no metric law.  That is not the fn. 23
  defect recurring; it is §11.5 (par-act non-expansion is FALSE) forcing the
  two claims apart, and merging them would reintroduce a false claim.

### 11.9 The strict/Δ gap: an artifact — but of the ADVANTAGE, not the strict metric (BOT, #28, settled 2026-07-27)

**Verdict (a): the gap is an artifact of CR18's `s → s⊥` completion-with-deletion,
used as the public observation rule on objects the source discipline rejects.**
But **the stakes as I framed them were inverted**, and the correction is the
point of this section.

**Lanzenberger Def 2.14 is stronger than we had recorded**: a PDS is a
distribution over DDS *all of which have the same domain*.  Equal domains are
required **inside every single object**, not merely across a compared pair — a
mixture of atoms with differing domains is not a PDS at all.  His stated reason
(Def 2.15/Ex. 2.16, p. 15): a PDS carries the information of a system that could
be *rewound and re-queried on the same randomness*, and *"we consider the
standard setting in which a system can only be executed once."*

**CR18's deletion rule makes rejection observable and costless.**  *(Corrected
2026-07-27: this paragraph previously said "is a rewind oracle".  That name was
wrong and had propagated into six places here, five docstrings and memory.  The
`.txt` extraction of CR18 drops the operative paragraph; read the PDF, p. 57–58
= PDF page 35.)*  CR18 p. 57, immediately before Def 3.3, verbatim:

> *"If an input outside of the (currently) allowed domain is given, the system
> does not 'see' this, i.e., **it does not change its state**.  Consequently, if
> later an allowed input is given, it will reply as if no undefined input had
> been given.  An environment interacting with a system 'sees' that a system
> gives no reply and can, for example, **ask a different query**."*

and footnote 5: *"an environment need not necessarily 'know' in advance whether
a certain input is defined."*

So the capability is precisely: **rejection does not advance the state, the
environment observes it, and may retry** — a free, unlimited domain-membership
probe.  It is **not** rewinding: nothing advances on a refusal, so there is no
earlier state to return to, and an *accepted* query can never be un-asked nor an
observed answer undone.  Calling it a rewind overstates it and invites the wrong
model.  What Lanzenberger excludes is the multi-execution access of Def 2.15/Ex.
2.16; free domain probing is a *weaker* capability than that, and the table
below should be read accordingly.

Bounding it further, the same page notes that Def 3.2's prefix-freeness
*"assures that a system can not be undefined for a certain input sequence
`(x₁,…,x_k)` but defined for an extension"* — domains are prefix-closed trees,
so probing explores a tree it can never re-enter, not an arbitrary oracle.

**Our counterexample's objects are ill-formed under that discipline**, and the
file proves it itself: `four_pattern_pair_has_no_common_support_domain`.  The
whole ½ is carried by one step — continuing at answer-history `[none]` — which
`IsDDC`'s `AnswersInY` makes type-level unreachable.  The pathology needs *both*
ingredients: unequal-domain mixtures **and** deletion semantics.

**THE INVERSION.**  I wrote that if the gap were an artifact, "the strict
quotient may be unnecessary".  That is backwards.  The artifact is on the
**advantage** side: the strict-test metric *is* Lanzenberger's
compatible-environment semantics in operational form (a test that would leave
the domain diverges = the experiment is inadmissible), and it is `maxAdvantage`
that **over-counts**, by precisely the domain information the costless
rejection grants.  **Lanzenberger vindicates C1's fibre choice.**  What is recoverable is
the *equality* on source-conformant objects — already kernel-checked under
totality (`maxEDist_eq_ofReal_maxAdvantage_of_total`), and extensible on paper
to the shared-domain subcarrier via rejection-pruning.

**The crux — `probeFn`.**  The theorem is genuine and stays; the *phenomenon* is
the deletion-rule probe one level up (the erased probe is CR18 p. 58's "the
system does not see this", applied to the composite).  Under Lanzenberger the
composite is not an object of the theory (atom-dependent domains violate
Def 2.14 — MauRen11 fn. 21's partial action), and under our own AC contract
(DESIGN §10.8: `Part.none` blocks with no continuation, continuable rejections
are ordinary values) the probe/reset run cannot occur at all.  So **C1's fibre
choice acquires a positive foundation** — thesis Def 2.12/2.14/2.17, the strict
quotient as the machine form of "compatible environments" — replacing the
negative one ("`probeFn` forced us off the raw-`Δ` fibre").  `not_emulable_probeFn`
should be cited as the boundary theorem *of the `Δ` metric*, not as the
foundation of the carrier.

**Recommendation: NO MIGRATION.**  Keep the carrier, the strict quotient,
`edist_liftProb_le_advantage`, and the `≤`-only rule.  Compatibility is a
*joint* condition on (experiment, object), so a migrated carrier would thread a
`CommonDomain` invariant through every mixture and restrict the converter monoid
to domain-transparent converters — MauRen11 fn. 21 reborn as an obligation on
every composition, paid everywhere, to buy an equality nothing currently
consumes.  What is lost by not migrating is only Thm 2.31-style attainment on
the *unrestricted* carrier — correctly lost, since `AttainmentCounterexample`
proves it false there, and `BoundedAttainment.lean` recovers it under the source
hypotheses.

**Actionable outcome.**  Nothing to migrate — the AC-facing carrier is already
conformant, so the deliverable was the re-attribution itself.  Three follow-ons:

* **RP (#33) — DONE, and it is the theorem, not the counterexample.**
  `StrictContextSharedDomain.maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain`
  (991-line new module): for normalized laws whose support atoms all share one
  domain — `HasFixedDomain _ D`, exactly Lanzenberger Def 2.14's objects —
  `maxEDist = ENNReal.ofReal Δ`.  Non-vacuous and strictly stronger than the
  old hypothesis: `sharedDomainOn_of_totalOnNonempty` subsumes the total case.
  Mechanism is rejection pruning as conjectured — a fuel-bounded replay machine
  (`pruneStep`/`pruneRun`) simulates the optimal environment against the public
  domain, synthesizes every `⊥` answer itself, and forwards only accepted
  queries; `properInteraction_truncDDD_prunedDDD` gets `ProperInteraction` with
  **no totality anywhere**.  The rule is now scoped, not mysterious: **`≤` on
  the unrestricted carrier, `=` on every object the sources admit.**
  **The memory claim "common domain does NOT rescue the reverse" is REFUTED,
  kernel-checked**; memory corrected.
* **LOOSE (#34) — DONE: NOT loose.  The stalling is invisible to the metric
  here, and that is now a receipt rather than an assumption.**  `θ_r`'s stall
  pattern is a *public block-count predicate*, so CR18's costless rejection buys a
  distinguisher nothing on these objects.  Generally,
  `sharedDomainOn_filterDom` + `maxEDist_filterDom_eq_ofReal_maxAdvantage`: a
  same-predicate `filterDom` restriction of a total law lands on the
  shared-domain subcarrier, where RP gives equality.  Concretely, in
  `CBCMAC.lean`, `maxEDist_theta_cbcReal_Vn_eq_ofReal_maxAdvantage` (Theorem
  6.1's own `θ_r` pair) and `maxEDist_filterQueries_cbcReal_Vn_eq_ofReal_maxAdvantage`
  (`cbc_mac_randomness_expander`'s `⌈q⌉` pair): **zero metric slack** — the birthday radii
  bound the strict metric exactly as they bound `Δ`.  Any residual looseness in
  CBC is combinatorial, not metric.
* **DOC (#23), reframed** — promoting Lanzenberger/Jost/MR16 over CR18 is no
  longer bibliography.  CR18's costless observable rejection *is* the
  complication; the later sources
  do not have it (Lanzenberger has no `⊥` channel; Jost's `require` returns a
  value).  Promoting them removes the complication at its source, and "which
  partiality discipline are we in" is the shared premise of the DSL's two-verb
  design (#24), the `Code` collapse (#25), and C3's well-placedness (#5).

**Documentation defect found and fixed.**  `maxEDist = 0` was asserted in three
places — a docstring in `ResourceLift.lean`, `DESIGN.md` §10.10, and this file —
as the justification for a design decision.  **It is not kernel-checked**:
`AttainmentCounterexample.lean` contains no `maxEDist` statement; it proves
`Adv = ½` and class-distance `1` (attainment failure).  The checked guardrail
for strict blindness is the separate pair `acceptAfterRejectedQuery_verdict_empty`
/ `_not_strictly_accepted` (`StrictContextTotal.lean:489ff`).  All three sites
corrected.  Two further items for the deviations register: CR18 Def 3.8/3.9 are
internally ambiguous about whether a converter may observe inner `⊥` (Def 3.8
says the input alphabet is `𝒴`, Def 3.9 says `𝒴 ∪ {⊥}`), and Def 3.9 is
explicitly informal — the repo silently resolved this via `AnswersInY`.

### 11.6 The source layer map (all five documents read visually, 2026-07-27)

Read cover to cover, by page rendering rather than text extraction — twice in
this program a conclusion drawn from `pdftotext` output turned out to be wrong,
so **extraction is not reading** for these papers.

**MauRen11 defines the hierarchy itself** (§1.5, p. 4) and states which rung it
occupies (p. 5: *"This paper deals with level 1"*):

| rung | content | filled by |
|---|---|---|
| **L1** | general systems + composition, algebraic axioms | **MauRen11** |
| **L2** | *discrete* systems — in 2011 an explicit hole: *"an extension of Maurer's random system framework [Mau02] … to multiple interfaces (**work in progress**)"* | **MauRen16**, then **Jost 2020**; **LiuMau20** instantiates it |
| **L3** | implementation / efficiency | nobody (Jost's asymptotic §2.2.5 aside) |
| substrate | what a random system *is* — **and the whole RS instantiation**: equivalence, distance, coupling, games/winnability.  **Resources only**; converters and constructions are deliberately out of scope (Def 2.41 *"ignoring the details of the interfaces and messages"*) | **Lanzenberger 2023** ← Maurer02 |

The glue is MauRen11 p. 4: *"definitions and theorems are inherited by the lower
levels, **provided** the lower levels satisfy the postulated properties or axioms
of the higher levels."*  That is the architecture we already have —
`Specifications.lean` instantiates L1's `IsSeriallyComposable` /
`IsContextInsensitive` / `IsGenerallyComposable` from L2's `⊆`, which is
Jost Thm 2.2.5 and MR16 Lemma 1.  **Our layering is the papers' layering.**

Three things the reading settles that inference did not:

1. **L1 is not one layer.**  MauRen11 §3–5 (reduction/specification calculus)
   is fully proved; **§6 (system algebra) contains zero theorems** — it is
   purely definitional; §7 couples them and proves Theorem 2.  And §1.4 says
   the choice-setting concept *"is independent of the reduction concept"*: the
   ordering is presentational.  A faithful formalization is three modules plus
   a bridge, which is what we have.
2. **The L2 hole was filled by a different formalism.**  MauRen11's slot
   expected multi-interface random systems; MR16 filled it with `πR ⊆ S` and
   never used `⊑π` again, and **Jost's 228 pages contain no "choice setting"
   and no "factorizable relation" at all**.  So `⊑π` and `⊆` are adjacent-slot
   formalisms that **nobody has ever bridged**.  The connection earlier logged
   here as open is *unbuilt in the literature*, not merely unbuilt by us —
   drop it (see §11.7).
3. **Lanzenberger is its own universe that ALSO instantiates CC.**  It cites no
   CC work — which is *what a lower layer looks like*, not evidence of
   disconnection.  (An earlier draft of this section called it "a separate
   tower whose connection upward is ours to build".  That was wrong on both
   counts.)  **Jost Def 2.2.1 gives the bridge shape explicitly**: *"a resource
   is a special type of a random system [Mau02], where the interface address is
   encoded as part of the inputs"* — which is exactly our
   `flatten : DependentDDS U σ → PFunDDS (Query U σ) (FlatAnswer U σ)` with
   `Query = Σ i, input (σ i)`.  We already implement it.  The practical payoff
   of the layer being self-sufficient is that **pure symmetric-crypto results
   need no CC machinery at all**, and CBC is the evidence in our own tree: its
   CC layer is thin *by design*, with the substance in RS.  Its foundations match ours exactly on
   the two make-or-break points: one-sided asymmetric `δ` (our `statDist` via
   `NNReal` truncated subtraction) and **arbitrary-weight distributions with
   normalization as a separate predicate** — the Thm 2.31 induction runs through
   sub-normalized successors, and *"a formalization that hard-codes weight-1
   PMFs will not reproduce these proofs as written."*  We did not.

**The finding that reshapes the plan.**  MauRen11's Def. 3 (`‖`-non-expanding)
is **dead code in its own paper** — defined, never invoked in any proof — and
MauRen11 states **no ε-parallel theorem at all**: Lemma 3 + Remark 1 cover
*serial* chaining only, while §1.2's claim that Theorem 1 covers "approximate
abstraction" is unmatched by anything in the body.  MR16 likewise has no parallel-ε lemma
(its Lemmas 2–4 are the converter, `*` and `[[` cases).  **But Jost Thm 2.2.11
does prove the parallel statement** — `[R^ε, S] ⊆ [R,S]^{ε_S}` with
`ε_S(D) := sup_{S∈S} ε(D[·,S])` — by pure distinguisher reindexing, **with no
metric anywhere**.  So the accurate claim is about the *route*, not the
theorem: the statement exists and is attested; what no paper proves is the
version routed through a metric non-expansion property, and §11.5 shows that
route is unavailable to us because the converter-side property is false.
(An earlier draft here said "no paper proves it", which checked only
MauRen11 — an overreach.)

Formalization landmines named outright by the sources, all of which we hit
blind: MauRen11 fn. 21 — **the converter action may be partial**; fn. 22 — the
neutral converter is deliberately *not* a system; fn. 23 — `(α∥β)^i T` is
undefined off parallel-form resources and `α∥1 ≠ α`; and §7.3 defines the
protocol map `αψᵢ ↦ απᵢφᵢ` **on syntactic representatives, with
well-definedness under the quotient never discussed** — which is exactly G1.
Jost Def 2.2.2 requires a finite bound on consecutive inner queries (our
`AnswersWithin`), and his Δ^D carries **no absolute value** (it enters only at
the ε-relaxation).

Per-document notes worth keeping: **LiuMau20** is an instantiation (synchrony
lives in the choice of Φ/Σ, not in the construction notion) plus a Z-indexed
statement shape that our `ConstructsForAll` matches exactly; its resources take
a *complete input list per invocation*, which silently forbids rushing unless
the r.a/r.b semi-round discipline is added — our one-query-at-a-time
`DependentDDS` is **not** in that model, so `Q3`/`mpc_step` currently float free
of the paper motivating them.  It also calls the single-simulator specification
type *"too restrictive"*, attributing it to *"the early version of CC"* — and
our `CC.SecurelyConstructs` is that shape (we do also have the general
`star`-relaxation form).

### 11.5 Par-act non-expansion is FALSE (settled 2026-07-27)

The question left open by P1 — is the parallel converter action 1-Lipschitz? —
is answered **no**, and the reason is instructive.

**Closure is not enough.**  That `α ∥ β` is a converter and `R ∥ S` a resource
gives nothing; non-expansion would need every resource at the sum code to *be*
a parallel composition, and **`∥` is not surjective**.  At `sumCode a b` a
resource sees the whole interleaved history and may answer a right-component
query differently depending on what was asked on the left; `par s t`
structurally cannot, since each component sees only its own projection.  So
correlated resources live at the sum code and outside the image of `∥`.  P1
proved decomposition is *unique* (`parallel_inj`); it is not *total*.

**Counterexample.**  The action is `(α ∥ β) • T = if T decomposes then
componentwise else T` — identity off the image, the freedom fn. 23 grants.
Take `R ∥ S`, and `M_δ` = that law with probability `1 − δ` mixed with a
correlating behavior with probability `δ`; a mixture of a product and a
non-product is not a product, so `M_δ` does not decompose.  Then
`edist (R∥S) M_δ = δ`, while `(α∥β)` sends the first to `αR ∥ βS` and the
second to itself; choosing `α` to flip the left output gives
`edist ((α∥β)•(R∥S)) ((α∥β)•M_δ) ≳ 1 − δ`.  **Before `δ`, after `1 − δ`** —
expansion unbounded as `δ → 0`.  The converter moves one point and pins the
other; that is all expansion needs.

**What is actually lost is narrow.**  `Constructs.eball_par` requires
`[Par Φ] [Par M] [SMulParClass M Φ] [IsNonexpandingPar Φ]` — a statement about
*resources*, which is Maurer11 eq. (3) and which P1 **proved**
(`System.edist_parallel_le`).  It does **not** require `IsNonexpandingSMul` for
the parallel protocol.  Only `Constructs.eball_trans` does.  So parallel
constructions work; what fails is **serially chaining them on `ParProtocol`**.
P1's `ParProtocol` already makes no non-expansion claim and does not interpret
into `nonexpandingEnd`, so nothing false is asserted today.

**Decision.**  Do not chase the proof.  If serial chaining of parallel
constructions is ever needed, restrict the parallel action to the decomposable
sub-carrier — its natural domain — where non-expansion holds, rather than
totalizing with an identity branch.  Until then the honest state is: `Par` on
`ResourceLift`, no `IsNonexpandingSMul` on `ParProtocol`, documented.

**This is the same disease a fourth time.**  fn. 23's "junk" is the paper
declining to define the action off `‖`-shaped resources, and Jost never applies
`α ∥ β` to an arbitrary resource either — he applies it to `[AuthChan, Key]`, a
resource he *built* as a composition.  The parallel action is naturally
**partial**; we totalized it, and non-expansion broke.  Fourth confirmed row for
the totalization audit (#22), after extensional Γ, the silent-identity action,
and totalized attachment.

**Corollary for review discipline.** The non-vacuity witness demanded of every
task in this program (D1's separating test, D3's forgeable resource that fails
the property, D2's excluded test, X3's provably distinct pair) is Maurer's
criterion — *a good theory should not let you even state the malformed claim* —
enforced by hand as a proof obligation.  Each caught something types did not.
Keep demanding it.


### 11.32 The UHF/URF MAC composite is now DERIVED, and the model passed the composition test (2026-07-30)

`uhf_urf_mac_securely_constructs` was a single unproved endpoint asserting the
whole chain.  It is now a **term**, obtained from two layer statements by
`securelyConstructs_trans_of_supported`:

```text
[short URF, key, InsecCh] --hashThenOracleProtocol--> [long URF, InsecCh]   C(q+1,2)·ε
[long URF, InsecCh]       --boundedUrfMacProtocol--->  AuthChan             1/|T|
```

The point is what did **not** have to change.  CC serial composition applies
only if the two layers share the intermediate resource, the simulator class
and the availability filter, and if the protocol labels multiply in the right
order.  `boundedLongMacResource` was already "the common intermediate
resource"; `uhfUrfMacProtocol` was already *defined* as
`boundedUrfMacProtocol * hashThenOracleProtocol`; the admitted class was
already `supportedOn {.eve} ⊤`, so the side condition discharges by `le_rfl`;
and the stated error was already the sum of the two layer errors.  The
composition therefore went through with no adjustment to any object.  That is
the load-bearing evidence that the decomposition is the right one — a wrong
factoring would have shown up as a mismatched intermediate resource or an
error that did not add.

Ledger effect: one monolithic admission became two strictly smaller,
independently provable leaves (`uhf_hash_layer_securely_constructs`, the
ε-almost-universal collision cost; `urf_mac_layer_securely_constructs`, the
one-guess forgery cost) plus a proved composition.  `audit_baseline.json` was
regenerated with `--axioms` for exactly this reason: the audit itself reported
`uhf_urf_mac_securely_constructs::sorry` as "recorded in the baseline but gone
(good — re-baseline)".

Not claimed: neither leaf is proved.  `OTP.lean` remains the only fully proved
symmetric CC endpoint.

### 11.33 Indifferentiability is instantiated at the RS carrier (2026-07-30)

`AbstractCrypto.Relaxations.Indifferentiable` (MauRen11 Definition 23 /
MauRen16 §4.2 Lemma 5) and its `.construct`/`.trans` were already proved, and
`Applications.Sponge.sponge_indifferentiable` wrapped `.construct`.  What that
wrapper's docstring deferred — "the concrete `RPerm`/`RO` ... are the
instantiation layer's obligation" — now exists:
`RandomSystemsCC/Symmetric/SpongeIndifferentiability.lean`.

The content is the **two-interface** setting the notion actually requires.
Indifferentiability is not a one-port statement: the distinguisher must reach
the construction *and* the primitive, so `permResource` answers permutation
queries at both `.honest` and `.adversary`, and `oracleResource` answers hash
queries at both (`.adversary` being the simulator's oracle access).  Attaching
the protocol at `.honest` and the simulator at `.adversary` sends both worlds
to `indifferentiabilityBoundary` — hash outside, permutation to the adversary
— which is what makes the two sides comparable at all.

`perm_constructs_random_oracle` is **derived** from the datum by
`Indifferentiable.construct`; nothing is re-proved.  One leaf is admitted,
`sponge_indifferentiability_datum`, and it is honestly weaker than it should
be: `Indifferentiable` existentially quantifies the protocol, so the leaf does
not yet pin `π` to the sponge.  Pinning it to the converter
`RandomSystems.BonehShoup.spongeOver` builds, with `ε` the BDPV capacity
bound, is the next step — that requires a `Primitive.ofHistory` witness for
`spongeStep` together with its Definition 3.8 round bound.

Scope, as directed: basic notion only.  No context restrictions (Jost
Chapter 4's RO-CRI is deliberately unused), no events, no interval-wise
relaxation.

`audit_baseline.json` regenerated with `--axioms`: one new admission (the
leaf) and one new endpoint (the derived construction).

### 11.34 The sponge converter is pinned; the simulator is not available (2026-07-30)

`sponge_indifferentiability_datum` no longer leaves the protocol existential.
`spongeProtocol` is a real CR18 Definition 3.8 converter at `.honest`, built
through `Primitive.ofHistory` from `spongeStep`, and its **round-bound
obligation is discharged**: `isDDC_ofStep` demands that a query be issued
*iff* `ys.length < cnt m`, and `spongeStep_query_iff` proves exactly that in
one line.  `sponge_indifferentiable` and `perm_constructs_random_oracle` are
both derived from the single remaining leaf.

Why the count is exact: the converter absorbs only.  For `v ≤ r` the squeezing
stage is a read of the absorbing stage's final state, so the round count is
the block count with no squeeze rounds — which is what makes `cnt` exact
rather than an upper bound, and hence what makes the Definition 3.8 obligation
provable at all.  A general-output sponge would need the squeeze rounds in
`cnt` and a correspondingly weaker interface.

**Correction to a working assumption.**  The BDPV simulator is *not* already
available anywhere in either repository.  `SPONGE_PROOF_PLAN.md` lists it
under open work — "Define the BDPV simulator as a legal probabilistic reactive
converter", plus its graph/table invariants and the bad-event bound — and
records the modeling direction that it is **probabilistic**, its capacity
coins being internal simulator randomness.  `Primitive` is the *deterministic*
converter layer, so the simulator cannot be built with the constructor used
for `spongeProtocol`; a probabilistic converter carrier (CR18 Definition 3.17,
`PFunPDC`) is needed first.  That, not the sponge converter, is the real
remaining obstacle.

**Superseded — the last two sentences are wrong; see §11.35.**  No
probabilistic carrier is needed: the coins belong in the ideal *resource*, and
with them in hand the simulator is an ordinary `Primitive.ofHistory`.
`simulatorPrimitive` is built and its Definition 3.8 obligation discharged.

### 11.35 The simulator is a deterministic converter; §11.34's obstacle was not one (2026-07-30)

**Correction to §11.34.**  Its closing claim — "a probabilistic converter
carrier (CR18 Definition 3.17, `PFunPDC`) is needed first.  That, not the
sponge converter, is the real remaining obstacle" — is **wrong**, and
`simulatorPrimitive` now refutes it in the kernel.  The simulator's coins are
not a property of the converter layer; they are a *resource*.  Moving them into
the ideal resource (`.hashCoins`, a second port at the adversary interface
offering the random oracle **and** a uniform `X → X`) makes the simulator a
deterministic function of its history, so it is an ordinary
`Primitive.ofHistory` — the same constructor `spongeProtocol` uses.  A local
randomness resource reachable only at the dishonest interface, and only through
`σ`, is what "probabilistic simulator" *means* in a deterministic-converter
framework.  Nothing is assumed by it; no new carrier is needed.

The same section's earlier framing — that the two interfaces demand a technique
the one-interface constructions do not have — is also wrong, and the file
docstring now says why.  `TypedConstruct.edist_coe_prob_le_advantage` sends the
typed distance to `Δ(DependentPDS.flatten …, DependentPDS.flatten …)`, an
ordinary `PFunPDS` advantage over the flat alphabet `Query U σ`, where the
interfaces are mere query tags `⟨.honest, m⟩` / `⟨.adversary, x⟩` and a flat
distinguisher interleaves them freely — which *is* the indifferentiability
adversary.  The leaf has `CBCMAC`'s shape; the two interfaces only make the
alphabet bigger.

**What landed, kernel-checked and axiom-clean** (`propext`, `Quot.sound` only):

* `oracleCoinsResource` — the ideal resource, oracle and coins drawn
  independently, coins reachable only at `.adversary`.  The coins arrive in
  **one** query (`output .hashCoins = D ⊕ (X → X)`); that is not cosmetic, it
  makes the simulator's round count the constant `ms.length + 1`, and
  `isDDC_ofStep` demands an *exact* count — the same knife-edge that made
  `spongeStep_query_iff` provable.  `simulatorStep_query_iff` discharges it by
  arithmetic.
* `simulatorPrimitive` / `simulatorProtocol`, with
  `simulatorProtocol_mem_simulators` admitting it into `supportedOn {.adversary} ⊤`.
* **The simulator reads rootedness off the seed, not off a table**
  (`simChain`, `simLci`, `simAns`).  Holding its coins it can, and two things
  follow: `simChain` is a plain structural recursion on the block index with no
  fixpoint (prefix-freeness of `pad` means a proper prefix of `pad m` is never
  some `pad m'`, so the oracle branch fires only at the last block); and the
  lazy/eager gap disappears, taking one of BDPV's two bad events with it.  The
  adversary can no longer reach a chain input the simulator fails to recognize,
  so **the capacity collision is the whole MBO**.
* `capacityBad` + `capacityBad_monotone` — Maurer's MBO shape exactly, measured
  in the capacity, with the call sites ranging over *both* ports (the chaining's
  inputs for every honest query, and the adversary's own points).  That port
  union is the only genuine difference from `cbcBad`.
* **The coupling** (`spongeChain_simAns_eq_simChain`,
  `squeeze_spongeChain_simAns`, `realDDS_simAns_eq_idealDDS`): driven by the
  simulator's own answer function, the real system **is** the ideal system —
  honest queries answer `g`, adversarial queries answer the simulator.  An
  equality of deterministic systems, not an indistinguishability.  This is the
  conditional-equivalence content at the realization level, and it is the fact
  the whole design rests on, so it is proved first.  Everything it needs from
  "no capacity collision" is isolated into two hypotheses — `lciInj` (distinct
  messages have distinct last chain inputs) and `interiorFresh` (no interior
  chain input hits a last one) — which keeps the coupling free of the counting
  argument.

**What is admitted, and it is now three *named* leaves rather than one opaque
`sorry`.**  A worse admission count, a better statement of what is missing:

* `spongeProtocol_smul_permResource`, `simulatorProtocol_smul_oracleCoinsResource`
  — the two normalization equations.  Not mathematics: `primitive_smul_coe_prob`
  followed by a `Primitive.ofHistory`/`ofStep` realization equation.  The route
  is `DependentDDS.flatten_attach_ofStep` (`TypedFraming`, which already
  packages the `ofStep` frame and its six obligations) composed with
  `PFunConverter.DDC.apply_ofStep_functionEvaluator_of_round` (`StepConverter`),
  exactly as `apply_cbc_to_uniform_random_function_eq_real_system` does on the
  flat carrier.  Both worlds are memoryless evaluators, which is the shape that
  lemma wants.
* `maxAdvantage_realLaw_idealLaw_le` — the paper's leaf, and the only
  mathematical one.  Route, in order: switch the primitive from `𝖯 X` to `𝖱 X`
  (`urf_urp_switching` under the converter DPI — the fiber counting is over
  `X → X`, not over `Equiv.Perm X`); then
  `condEquiv_of_transcript_mass_reductions`, whose three mass reductions are the
  packaged `massAfalse_fTransform_historyEvaluator` /
  `massY_fTransform_lastQuery` / `massYAfalse_fTransform_lastQuery` as in
  `cbc_condEquiv`, leaving `hprod`; then CR18 Theorem 4.17 and the birthday
  count on `capacityBad`.

Why `hprod` should be a bijection rather than a `cbc_fiber_card`-style count:
under the split laws `squeeze (mk d y) = d` and `mk (squeeze y) y = y`,
`simAns g T` is exactly `|D|^|M|`-to-one onto the good primitives.  Off the
`simLci` points the coins are pinned to `f`; at `simLci m` the oracle value
`g m = squeeze (f x)` and the coin capacity are pinned while the coin's outer
part stays free.  That constant fiber is the whole content of the ideal
factor.

Not claimed: the datum is derived, not proved — `sponge_indifferentiability_datum`,
`sponge_indifferentiable` and `perm_constructs_random_oracle` are all
kernel-checked *given* the three leaves.  `OTP.lean` remains the only fully
proved symmetric CC endpoint.

Statement change to note: the ideal specification of
`perm_constructs_random_oracle` now names the oracle **with the simulator's
local randomness alongside it**, and the radius is displayed as
`ENNReal.ofReal ε` so the leaf is the paper's real-valued `Δ`.

### 11.36 BDPV read; the sponge architecture of §11.35 is not their proof (2026-07-30)

`papers/BDPV08_SpongeIndifferentiability.pdf` (EUROCRYPT 2008) fetched and read.
It was not in `papers/` and had not been consulted: §11.35's table-based
simulator was written from memory, and the memory was wrong in the one place that
carries the proof.

**The mechanism I missed.**  Algorithm 2 draws the answer's capacity `t_c`
uniformly from `C \ (R ∪ O)` — the supernodes that are neither rooted nor already
have an outgoing edge.  BDPV therefore *prevent* capacity collisions by
construction; the rooted supernodes form a tree (Lemma 1, at most one path per
node) and the simulator is **exactly** sponge-consistent (Lemma 2).  **There is
no capacity-collision bad event in their proof.**  What can fail instead is
*saturation*, `R ∪ O = C`, and since `R ∪ O` grows by at most one per query it
cannot occur before `2^c` queries — so it is a hypothesis `N < 2^c`, not an event
to bound.  `capacityBad` and `capacityBad_monotone` are therefore off BDPV's
critical path entirely.

**Three further structural facts, each of which changes this file's shape.**

* **Rootedness lives on supernodes, i.e. on capacities** (§3.2): `R ⊆ C`, and a
  node is rooted iff its capacity is.  Both simulators here carry full states.
* **The two interfaces collapse to one** (Lemma 3).  The sponge is public, so a
  distinguisher answers its own `H` queries from `F¹` queries at no greater cost,
  and every `Q⁰` sequence is replaced by an at-least-as-informative `Q¹` one.  The
  leaf is a **one-port** advantage.  §11.33's "indifferentiability is not a
  one-port statement" is right about the *setting* and wrong as a claim about the
  *proof*: the setting has two interfaces, the reduction removes one.  In this
  development Lemma 3 is a converter/DPI step, not a two-port conditional
  equivalence — so the `condEquiv_of_transcript_mass_reductions` plan of §11.35 is
  solving a harder problem than BDPV solve.
* **The leaf is a switching lemma, not a birthday count** (Lemma 4): the
  advantage is the variational distance between uniform node answers and answers
  whose capacities are drawn *without replacement*,
  `f_T(N) = 1 - ∏_{i=1}^{N}(1 - i/2^c) ≈ N(N+1)/2^{c+1}`.  That is
  with- versus without-replacement on the capacity — the shape
  `urf_urp_switching` already has here.

**Permutation case** (Algorithm 3, Theorem 2): additionally `t` must have no
incoming edge, and the `F⁻¹` interface draws `t_c` from `C \ R` among nodes with
no outgoing edge, so an inverse query can never create a rooted node.  Bound
`f_P(N) = 1 - ∏_{i=0}^{N-1} (1 - (i+1)/2^c)/(1 - i/(2^r 2^c))`.  My earlier worry
that the reconstruction "cannot simulate a permutation" was right, and this is how
they handle it.  `N` throughout is BDPV's *cost* — total `F`/`F⁻¹` calls, direct or
via the sponge (§3.5) — not a query count.

**What survives.**  `unpad` (Algorithm 2 line 6 is literally an unpad test); the
block being an `A`-part difference (Lemma 1's closing sentence), so `unabsorb` was
right; `Memory`'s table and its consistency-first lookup; and — untouched by any
of this — `simulatorPrimitive`'s refutation of §11.34, since "coins in the ideal
resource" is orthogonal to which simulator is being built.

**What does not.**  `bdpvAns`'s sampling rule, and with it `length_bdpvOracleNeeds_le`
as an account of BDPV's cost.  Both are marked superseded in the file rather than
deleted, since their parts are reusable.

**Modelling note for the rewrite.**  `t_c` uniform on `C \ (R ∪ O)` is not a draw
from a fixed set, so a coin resource of type `X → X` cannot supply it.  A uniform
`Equiv.Perm C` can: take the first capacity in that order avoiding `R ∪ O`.  The
"randomness lives in resources, converters are deterministic" discipline survives.

Two prose claims corrected elsewhere: our own simulator is not BDPV's (`66c73e4`),
and `ofHistoryStep`, not the carrier, is what hid the converter's memory —
`ProtocolFn` is `List U × List (Option Y) →. X ⊕ V`, the whole transcript, so the
`O(q²)` replay of §11.35 was self-inflicted by a constructor choice.

### 11.37 BDPV Algorithm 2 built from the paper, with Lemma 1's invariant (2026-07-30)

`RandomSystemsCC/Symmetric/SpongeBDPV.lean`, new, **zero sorries**, transcribed
from `papers/BDPV08_SpongeIndifferentiability.pdf` rather than reconstructed.

The graph is §3.2's: nodes `A × C`, **supernodes `C`**.  `R` and `O` are *derived*
(`Graph.R` = the capacities carrying a path, `Graph.O` = the capacities with an
outgoing edge) rather than stored fields, so the "rooted set = capacities with a
path" invariant holds by construction instead of by maintenance — this is where
§11.35's reconstruction went wrong (it carried full states).

`answer` is Algorithm 2 line by line: existing outgoing edge answers from the
graph (lines 2, 18); a rooted `s` at an unsaturated graph takes its bitrate part
from the oracle when the stripped path unpads and its capacity **from
`C \ (R ∪ O)`** (lines 3–12), becoming a new rooted node; anything else is
uniform (line 14).  Two modelling choices worth naming:

* **Saturation is `freshCapacity = none`.**  That merges Algorithm 2's two guards
  — "`s` is rooted AND `R ∪ O ≠ C`" — into one match, and needs no `Fintype C`
  for decidability.
* **`t_c` uniform on `C \ (R ∪ O)` is supplied by a uniform `Equiv.Perm C` per
  query**, taking the first capacity in that order avoiding `R ∪ O`.  A coin
  resource of type `X → X` cannot deliver a draw from a varying set; a permutation
  can, and the "randomness lives in resources, converters are deterministic"
  discipline survives intact.
* The appended block is `s.1 - entry.1.1`, an `A`-part difference.  Algorithm 2
  line 4's "append `s_a`" is shorthand; Lemma 1's closing sentence ("since `A` is
  a group, each `r`-bit block of the path is uniquely determined by the transitions
  on the `A`-part") fixes the difference.

**Proved, axiom-clean:**

* `freshCapacity_notMem` — a fresh capacity is neither rooted nor outgoing.  One
  line, and everything rests on it.
* `answer_R_nodup` — **Lemma 1's invariant**: at most one path per supernode,
  hence per node.  Precisely what drawing from `C \ (R ∪ O)` buys, and the reason
  BDPV need no capacity-collision event.
* `card_rootedOrOutgoing_answer_le` — **the saturation count**: `R ∪ O` grows by
  at most one per query.  The rooted branch adds `s.2` to `O` and `fresh` to `R`,
  but `s` is rooted there so `s.2 ∈ R` already: only `fresh` is new.  This is what
  turns saturation into the hypothesis `N < 2^c`.

Scope: random *transformation* only.  Algorithm 3 (permutation) additionally
requires `t` to have no incoming edge and draws `F⁻¹` answers' capacities from
`C \ R` among nodes with no outgoing edge, so an inverse query never creates a
rooted node — not modelled.  The oracle returns `Fin outBlocks → A`, the same
finite truncation `Vn` uses.

Next, in dependency order: fold `answer` over a query history; the `ProtocolFn`
converter (**not** `ofHistoryStep` — it discards prior rounds' answers, which is
what forced §11.35's replay; the general `ProtocolFn` is
`List U × List (Option Y) →. X ⊕ V`, the whole transcript) with `IsDDC` by hand;
Lemma 2 (exact sponge consistency, no conditioning); Lemma 3 (the honest port is
distinguisher-simulable — a converter/DPI step that collapses the two interfaces
to one); Lemma 4 (with- versus without-replacement variational distance on the
capacity, `urf_urp_switching`'s shape).

### 11.38 BDPV Lemma 1 and Lemma 2 proved; saturation bounded (2026-07-30)

`SpongeBDPV.lean` extended, still **zero sorries**, all axiom-clean.  `A` is now
`AddCommGroup` rather than `AddGroup`: the block recovery `(s_a + b) - s_a = b`
needs commutativity, and BDPV's `A = Z₂^r` has it.

**The run.**  `run` folds `answer` over the adversary's queries and `ans` reads
off an answer.  The graph is genuine state — nothing replays, because the
converter this will carry uses the general `PFunConverter.ProtocolFn`
(`List U × List (Option Y) →. X ⊕ V`, the whole transcript).  `run_R_nodup` lifts
Lemma 1 to a whole run.

**Saturation is unreachable below `|C|` queries** — BDPV's `N < 2^c`, and the
reason their proof needs no bad event:

* `card_rootedOrOutgoing_run_le` — `R ∪ O` after `N` queries has at most `N + 1`
  capacities;
* `exists_notMem_of_card_lt` — below `|C|` some capacity is free;
* `freshCapacity_isSome` — and `freshCapacity` finds it, given that `capacities`
  enumerates `C` (the coin permutation is a bijection, so its image still covers);
* `freshCapacity_run_isSome` — the three composed.

**Lemma 2 (sponge consistency) as an invariant.**  `Graph.Consistent`: every path
in the graph carries the oracle block it names — strip the trailing zero blocks,
unpad the rest, and the node's bitrate part is that message's block at the
stripped index.  `init_consistent` / `answer_consistent` / `run_consistent`.  No
conditioning and no bad event anywhere, which is the whole point of the
`C \ (R ∪ O)` draw.

`init_consistent` needs `unpad [] = none`, which is BDPV's own restriction rather
than a convenience: "the all-zero path does not correspond to a block that can be
output by the sponge construction", and Definition 2 requires `|p| > 0` with last
block `≠ 0^r`.

**Lemma 2's payoff, at a chain step.**  The invariant is about paths; what the
proof consumes is that walking the sponge chain *extends* the path by the absorbed
block:

* `pathAt_eq_of_mem` — Lemma 1 in usable form: a supernode carrying a path carries
  exactly one, so `pathAt` returns it (`List.inj_on_of_nodup_map` on `R.Nodup`);
* `answer_rooted_step` — absorbing `b` at a rooted node with path `w` yields a
  node rooted by `w ++ [b]`.  The appended block comes out as
  `(s.1 + b) - s.1 = b` *only* because `pathAt` found the unique entry — Lemma 1
  and the group law are both load-bearing here.  Its two hypotheses are exactly
  Algorithm 2's guards: the query carries no outgoing edge yet, and the graph is
  unsaturated;
* `answer_bitrate_eq_oracle` — consistency and the rooted step composed: the node
  the chain reaches has the bitrate part the oracle dictates for its own path.

**Not proved, stated with routes in the file's closing section.**  Lemma 3 (the
two interfaces collapse: the sponge is public, so the distinguisher walks the
chain itself — a converter/DPI step, not a conditional equivalence, and the step
that makes `SpongeIndifferentiability.lean`'s two-port architecture unnecessary);
Lemma 4 (the leaf: `Δ(F, P[RO]) ≤ 1 - ∏(1 - i/2^c)`, sampling with versus without
replacement **on the capacity only** — `urf_urp_switching`'s shape one level up,
but partial injectivity on a projection, so it needs its own count); and the
converter itself (general `ProtocolFn`, `IsDDC` by hand, round bound 1 oracle
query plus the coin draw since `answer` consults the oracle at most once).

### 11.39 Lemma 3's content proved; Lemma 4 split, and BDPV assert its hard half (2026-07-30)

`SpongeBDPV.lean` extended, still **zero sorries**, axiom-clean.

**Lemma 3 — the mathematics is done.**  Lemma 3 says a distinguisher can replace
honest-interface queries by permutation queries at no greater cost, because the
sponge is public and it can walk the chain itself.  The content is that the walk
*works*:

* `walk` — absorb each block into the current node's bitrate part and query the
  simulator;
* `WalkFresh` — Algorithm 2's two guards at *every* step.  They are conditions on
  the intermediate graphs, so they cannot be hoisted; carrying them recursively is
  the honest formulation;
* `walk_rooted` — absorbing `bs` from a node rooted by `w` ends on a node rooted by
  `w ++ bs`.  Lemma 1 is re-established at each step (`answer_R_nodup`) so the next
  step can use it;
* `walk_consistent` — consistency survives a walk, unconditionally;
* `walk_bitrate_eq_oracle` — the walk's final node has the bitrate part the oracle
  dictates.  So a distinguisher walking the chain reads exactly the honest
  interface's answer.

What is left of Lemma 3 carries no mathematics: the reduction on distinguishers is
a converter/DPI step (the sponge simulation *is* a converter; dropping the honest
port is advantage monotonicity under it).  It cannot be written until the two-port
resources exist on this file's side.

**Lemma 4, split in two.**  `idealSystem` now exists — Algorithm 2 as a `PFunPDS`
over a uniform seed `(oracle, coinA, coinC)`, with `idealSystem_isProbDist` — so
the target is statable: `Δ(𝖱 (Node A C), idealSystem) ≤ fT |C| N` at `N < |C|`.

*Arithmetic half — done.*  `fT` is BDPV's `f_T(N) = 1 - ∏(1 - i/2^c)`;
`one_sub_sum_le_prod_one_sub` is the union bound `1 - ∏(1 - aᵢ) ≤ ∑ aᵢ`; and
`fT_le` gives the headline `N(N+1)/(2|C|)`.  BDPV reach eq. (4) through
`1 - x ≈ e^{-x}`; `fT_le` proves it outright, so nothing on our side is
approximate.

*Probabilistic half — open, and **not a transcription job**.*  BDPV's proof of
Lemma 4 says "To obtain the greatest possible variational distance, the optimum
strategy consists in creating `N` rooted nodes" and computes the distance for that
strategy.  **The optimality is asserted, not proved**, and it is asserted at exactly
the point a formal proof cannot skip: the variational distance must be bounded for
*every* distinguisher, not for one claimed to be worst-case.  So finishing Lemma 4
means supplying an argument the paper does not give.

The natural one here avoids the optimality claim entirely: a hybrid over the `N`
queries, where at step `i` the forbidden capacity set has size `≤ i`, giving
`∑ i/|C|` — which is the bound `fT_le` already delivers.  That is the route to take,
and it is a different proof from BDPV's, not a formalisation of it.

Also on the record: `N` throughout is BDPV's *cost* (total `F` calls, direct or via
the sponge, §3.5), not a query count.

### 11.40 The counting leaf, without BDPV's optimality assertion (2026-07-30)

`SpongeBDPV.lean`, still **zero sorries**.  The number in Lemma 4 is now proved,
and by a route that does not use the step BDPV assert.

**Why we can skip their assertion.**  Their Lemma 4 computes the variational
distance for the all-rooted strategy and asserts it is worst-case.  That is not
innocuous: `R ∪ O` grows on *every* query, so a strategy that first enlarges `O`
meets a bigger forbidden set at each later rooted query, and whether that trades
favourably against having fewer rooted queries is exactly the unproved claim.
Instead we use `card_rootedOrOutgoing_run_le`, which holds for *every* query list
and hence every strategy: the forbidden set at step `i` has size `≤ i`, so the
deviation is a capacity collision against at most `i` earlier capacities, and a
union bound over query pairs gives `(N choose 2)/|C|`.

**Proved:**

* `fTransform_capacity_uniform` — reading only the capacity of a uniform
  transformation is a uniform random function into `C`.  Every fibre of the
  projection has one preimage per choice of bitrate parts, so
  `Dist.fTransform_uniform_eq_uniform_of_card_fiber_mul` applies; the fibre
  bijection is with `Node A C → A`.
* `uniform_capacity_pair_eq_mass` — two distinct points get equal-capacity
  answers with probability exactly `1/|C|`, by pushing forward and citing
  `uniform_function_pair_eq_mass_of_codomain` (which is already heterogeneous, so
  the projection is the only new content).
* `mass_capacityCollision_le` — **the projected birthday bound**:
  `≤ (N choose 2)/|C|`, via `mass_le_pairCollisionUnionBound_of_cover`, the repo's
  generic birthday-cover engine.  This is where the security parameter becomes the
  *capacity* rather than the whole state.

Needed a new import, `RandomSystems.SwitchingLemma`, for the birthday engine.

**What is still open, and it is one thing.**  The conditional equivalence
`𝖱 (Node A C)` -with-capacity-collision-MBO `|≡ idealSystem`, plus the Theorem
4.17 wiring.  Everything else on the path exists.

Note for that step: the `condEquiv_of_transcript_mass_reductions` template does
**not** apply — it wants `outT : A → In → Out`, a function of the query alone, and
`idealSystem` is history-dependent by construction (the graph is its state).  Two
routes, and the second looks cheaper:

1. prove `CondEquiv` from the mass definitions directly — the ideal side's
   transcript law needs the rooted/non-rooted pattern to be transcript-determined,
   the bitrate parts to be uniform and fresh (which is Lemma 1: unique paths mean
   each oracle position is read once), and the capacities uniform on the
   complement;
2. **a coupling** between the two seed spaces that agrees off the bad set — the
   same shape as the `Φ`-fibre argument already proved for the eager simulator in
   `SpongeIndifferentiability.lean` (`realDDS_simAns_eq_idealDDS`), which suggests
   the machinery in `RandomSystems.Coupling` / `DistCoupling` fits better than the
   condition-C templates do.

Beyond that, the two-port statement still needs the converter and Lemma 3's DPI
step, neither of which is mathematics.

### 11.41 HCTR2 symmetric common-part proof on a common carrier (2026-08-04, corrected 2026-08-06)

`papers/notes/HCTR2_CE_RAW_TAPE.md` now gives a complete pen-and-paper
**symmetric common-part game-equivalence** proof of HCTR2 on the positive
i.i.d. carrier

$$
\Omega=(h^*,l^*)\times W\times R_G\times R_F.
$$

The real and ideal representatives receive the same prefix-monotone condition:
the first same-side collision among raw inferred permutation sites. Before the
condition fires, their complete output prefixes agree for every carrier point.
The common-carrier lemma therefore gives equal pre-winning transcript
subdistributions for the two monitored games. Their residual laws have the
same mass, so total variation is bounded directly by that mass. CR18 Theorem
4.17 does not apply to this two-monitor identity and is not needed.

The ideal visible kernel preserves the prior product law of the current raw
cell, mask key, hash key, unread suffixes, and future rankings. The exhaustive
first-failure inventory reduces every collision to an impossible slot, an
$l^*$ pin, a POLYVAL-root bound, or an i.i.d. raw-cell pin. Consequently,

$$
\Delta(\mathbf{HCTR2}[\operatorname{Perm}(n)],\widetilde{\mathbf T})
\le
\min\!\left\{
1,
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\},
$$

and the tagged multi-user lift is

$$
\min\!\left\{
1,
\frac{
3\sum_i\sigma_i^2+2\sum_iq_i\sigma_i+7\sum_i\sigma_i+2a
}{2N}
\right\}.
$$

This removes the published proof's external $q^2/(2N)$ PRP–RND switching term.

The note also closes a classification question. A direct strict CR18
certificate is impossible at the desired scale in either orientation:
real-to-ideal has a one-query support mismatch and forces survival zero;
ideal-to-real uses the one-block output with probabilities $1/N$ and $2/N$
and forces survival at most $1/2$. Visible pushforward shows that terminal
reveal or other output augmentation does not evade either obstruction.

**Paper status:** **DERIVED.** Exact marginals, adaptive common-part identity,
posterior constancy, collision inventory, single-user bound, multi-user bound,
and the direct strict-CE obstruction are complete. **Lean status:** **OPEN.**
The existing HCTR2 formalization remains an H-technique proof. A formal
common-part certificate still needs the common seed, both deterministic games,
the seed-aware monotone condition, stripped marginal theorems, and the
pre-winning mass identity.

### 11.41.1 HCTR2 blind strict CE: balancing works, fixed-fibre loss exposed (2026-08-06)

`papers/notes/HCTR2_CE_BALANCED.md` gives the CR18-style chain requested after
the common-part proof: two game-equivalent monitored representatives, a local
balancing rejection, strict conditional equivalence to the normalized good
kernel `J`, absorption into a blind winner, and a fixed-list winning bound.

The clean-write-up audit found that the earlier completed-response appendix
did not justify its claimed `alpha_q` bound. The factor
`N/(N-q+1)` controls a newly sampled response pin, but after a completed
response is fixed, a collision such as `S_(r,i)=S_(s,j)` is a polynomial
condition on the persistent POLYVAL key and can exclude up to
`max(d_r,d_s)` keys. Equality of the real and ideal pre-winning masses is also
two-game equivalence, not one-sided strict CE.

The corrected note introduces an exhaustive fixed-completion fibre count
`Phi_i`. With `P_i` the paper's first-collision count, it derives the profile
bound

```text
Adv(HCTR2[Perm(n)], ideal tweakable permutation)
  <= min(1, P_q/(N-Phi_q))
```

and the simple envelope, when `sigma*(sigma+1)*(sigma+2) < N`,

```text
(3*sigma^2 + 2*q*sigma + 7*sigma + 2)
  / (2*(N-sigma*(sigma+1)*(sigma+2))).
```

There is no switching hybrid, but this conservative strict-CE theorem is only
useful below the cubic-fibre threshold. Recovering the common-part proof's
alpha-free birthday-range bound with a blind strict-CE certificate remains
**OPEN**. The new note is **DERIVED** at paper level and **OPEN** in Lean.

## 12. Common mathematical foundations — probability and information theory (2026-08-05)

**This section is a plan, not a receipt.**  Nothing below is claimed to exist
unless it is backticked.  Proposed declaration names are written in plain text
precisely because `doc_audit.py` treats a backticked identifier that resolves
nowhere as a *phantom declaration* — the exact drift this section would
otherwise introduce on the day it was written.  Promote a name into backticks
only once it compiles.

### 12.1 Scope

The goal is a reusable layer of **common mathematical foundations**: facts about
distributions, random variables, and events that a textbook would state the same
way, and that a downstream proof can use without having heard of the paper the
fact came from.

*Centre of gravity: Maurer.*  `papers/Maurer02.pdf`, `papers/MaPiRe07.pdf`,
`papers/MauPie04.pdf`, `papers/LanMau20.pdf`, `papers/CR18_LN.pdf`,
`papers/thesis (1).pdf` (Lanzenberger), `papers/2026-1071.pdf` (Gegier–Maurer).

*Other papers contribute facts, not programs.*  A result from
`papers/PorRen22.pdf`, `papers/BonehShoup.pdf` or `papers/cbc-improved.pdf` is
in scope when the result itself is reusable mathematics; the surrounding
framework is not.

**Explicitly out of scope**, and not tracked here: composability apparatus
(simulators, converters, resource specifications, composition theorems),
negligibility and asymptotics, and system models as such.  Those belong to §10
and §11 and to the CC layer.  This section does not attempt to formalize any
paper end to end.

### 12.1a Where each item may live

`DESIGN.md` §12 fixes the tower (L0 signed `Dist` → L1 expectation and the
one-way transport into mathlib → L2 the information theory mathlib lacks → L3
the Maurer superstructure) and the rule that a probabilistic fact is defined at
its tower level, never inside the application that first wants it.  Every entry
below is placed by that rule.  The layer measurements behind it — which
statement is true at signed, at `NonNeg`, at `isProbDist`, each with a proved
counterexample one layer down — are in `scratch/TransportProbe.lean`.

### 12.2 Naming

Mathlib conventions, without local dialect: `lowerCamelCase` for definitions,
namespaced so they read as `Dist.<name>`; snake-case theorem names that spell
the conclusion out left to right in mathlib's vocabulary for each symbol (`add`,
`sub`, `mul`, `smul`, `sq`, `abs`, `inv`, `min`, `le`, `eq`); the paper cited in
the docstring and never in the identifier.  Generic results carry the
`UPSTREAM-CANDIDATE` marker already used across the tree.

### 12.3 Absent — no formalization anywhere

| Item | Source |
|---|---|
| Shannon `H(X)`, `H(XY)`, binary entropy, `0 ≤ H ≤ log₂ card`, sub-additivity and monotonicity with equality conditions | CR18_LN App. A.2, Defs A.7 / Thms A.1–A.2 |
| Conditional entropy, mutual information, conditional mutual information, chain rule, non-negativity with equality conditions | CR18_LN App. A.2, Defs A.8–A.9 / Thm A.3 |
| Entropy chain rule as used to characterise uniformity of a scalar product | Maurer02 App., Lemma 11 |
| Key-agreement entropy bound and its perfect-case corollary | CR18_LN Thm 7.3, Cor 7.4 |
| Max-probability, collision probability, Rényi/collision entropy, distance from uniform; `1/card ≤ p_coll ≤ p_max`; `d ≤ ½√(card·p_coll − 1)` | CR18_LN §7.2.3, Lemmas 7.6–7.7 |
| 2-universal hash classes; leftover hash / privacy amplification | CR18_LN Def. 7.2, Lemma 7.8, Thm 7.9 |
| Relative entropy and Pinsker | PorRen22 App. A, Lemma 14 |
| χ² method | Dai–Hoang–Tessaro, cited LanMau20 §1.6; blocks the `(q/N)^{3/2}` route noted in `RandomSystems/SumOfPermutationsOptimal.lean` |
| Continuity of entropy in statistical distance (Fannes / Alicki–Fannes) | PorRen22 Thm 12, Cor 13 |
| Expectation and variance as a first-class `Dist` API; linearity, `E[f(X)]`, variance of a sum under *pairwise* independence | CR18_LN App. A.1.3; MauPie04 Lemmas 4–5 |
| Markov, Chebyshev, Cauchy–Schwarz on `Dist` | ibid. |
| Sub-martingales, running maximum, `E[max V] ≤ E[V_n](1 − ln E[V_n])` | MauPie04 Def. 9, Lemmas 7–8 — gates MauPie04 Thms 1–2 |
| Chernoff, Hoeffding | BonehShoup Thm B.3 |
| Statistical distance in min form and in half-L1 form | LanMau20 Def. 3; MPR07 eq. (3); PorRen22 eq. (A1) |
| Optimal guessing probability `½ + ½δ`; advantage as a guessing bias; half-way mixture | MPR07 Lemmas 2–3; PorRen22 Thm 8 |
| Guessing probability bounded by uniform plus distance from uniform | PorRen22 Lemma 11 |
| ~~A probability measure out of an event algebra~~ — **corrected 2026-08-06, this is a wiring job, not a gap**: `LatticeValuation` (`AbstractCrypto/EventAlgebra.lean:708`) already encodes monotone-plus-finite-sub-additive and proves the transfer, but has **zero** uses outside its defining file, and `EventAlgebra` appears in exactly one RS file (`RandomSystemsCC/EventHistory.lean`). What is missing is the `Dist` instance, needing `mass_mono` + `mass_or_le`, both gated on `NonNeg` | GegMau26 §1.3, p. 26/38 |
| Conditional independence; pairwise, k-wise, and adaptively almost-k-wise independence | CR18_LN §6.1.2; Maurer02 Def. 13 / Lemma 12; MauPie04 Def. 11 |
| Bayes, law of total probability, and the transcript chain rule on `Dist.cond` | MPR07 eq. (1); MauPie04 §2.1 |
| Birthday: lower bound, two-sided form, non-uniform i.i.d. case, uniform-minimises-collision | BonehShoup Thm B.1, Cor B.2 |
| Adversary-free collision quantities (`CP`, `FCP`) and the game-playing bound | cbc-improved §2–3 |
| Bernoulli and Binomial as named distribution objects over a two-point carrier (notably ±1) | Lanzenberger thesis §3.2, p.47 |
| Binomial falling-moment identity: expectation of a binomial coefficient of a `Bin(n,ε)` variable is `C(n,m)·ε^m` | Lanzenberger thesis p.37; LanMau20 Cor. 1 |
| Concavity/convexity of a real function as a usable hypothesis, and the concave slicing lemma | Lanzenberger thesis Lemma 3.1, p.47 |
| Blinded-system advantage: distance to a blinded mixture scales by the blind's zero-mass | LanMau20 App. A Lemma 9; thesis Lemma A.1, p.88; = MPR07 Lemma 3 |
| Blinding lemma and the (k,n)-combiner amplification bound with its ξ coefficients | LanMau20 Lemmas 7–8, Thm 3, Cor. 1; thesis Lemmas 2.44/2.47, Thm 2.45, Cor. 2.46 |
| Winnability of a ψ-parallel composition of games as a Bernoulli-vector probability | LanMau20/thesis Def. 2.48, Cor. 2.49 |
| Exact bit-XOR amplification identity for distance from uniform | thesis §2.5.1, p.27 |
| Direct-product hardness amplification (thesis ch. 3 as a whole), Levin/XOR-lemma reductions, and the special-function layer they need (Gordon's Γ-bounds, Lambert W) | Lanzenberger thesis Thms 3.2–3.25 |

### 12.4 Present but specialized — generalize in place, do not re-add

| What exists | Where | Defect |
|---|---|---|
| A genuine `Dist` expectation, `NNReal`-weighted, with two lemmas | `expectW`, `RandomSystems/HTechnique/Derivation.lean` | Buried in a 6k-line derivation file; should be the library's expectation. Also single-distribution and non-negative-weight only: no product/joint expectation, and no signed integrand, both of which the amplification chapter needs |
| Jensen's inequality, ad-hoc and pointwise | `RandomSystems/Legacy/Applications/XoPANOVA.lean`, `RandomSystems/SoP/XORComplementMarginal.lean` | Two independent finite pointwise versions; no `Dist`-level statement for a concave function |
| Almost-XOR-universal hashing | `RandomSystems/HCTR2.lean`, `RandomSystems/HCTR2_FINAL.lean` | Hard-coded to HCTR2; no general k-universal family and no k-wise independence notion |
| Combiners | `IsCombiner`, `IsThresholdCombiner`, `RandomSystems/Legacy/Combiner.lean`; `amplification_theorem`, `RandomSystems/Legacy/Amplification.lean` | Threshold case only, on the quarantined Legacy q-bounded carrier, and proved from an *assumed* per-coordinate reduction rather than from the coupling/blinding route |
| `expect`, `guessProb`, `minEntropy`, `condMinEntropy`, `minEntropy_marginal_sub_logb_card_le_condMinEntropy`, `testDist` | `RandomSystemsCC/MauRen16Impossibility.lean` | The tree's **only** entropy, stranded on mathlib `PMF`/`ℝ≥0∞` inside one CC impossibility file, disconnected from `Dist` and `statDist` |
| Mean, variance, σ, standardization, moments, Cauchy–Schwarz, Stein/Berry–Esseen machinery | `RandomSystems/SoP/CollisionCountNormal.lean` and siblings, e.g. `collisionVariance`, `uniformAverage_abs_le_sqrt_uniformAverage_sq` | An entire moment calculus hard-coded to uniform-on-`Fintype` and to the collision-count observable |
| ε-universal hashing with a scalar ε | `EpsUniversalHash`, `RandomSystems/HTechnique/HashThenPRF.lean` | CR18_LN Def. 6.2 needs a *length-dependent* δ; 2-universal should fall out as a special case |
| A second, weaker hash notion: carrier only, security "not declared here" | `UHF`, `RandomSystems/BonehShoup/Ch7UHF.lean` | Two notions of the same object in one tree |
| Two independent birthday bounds | `pcoll_le_birthday` in `RandomSystems/SwitchingLemma.lean`; `birthday_bound` in `RandomSystems/Counting.lean` | One should be canonical |
| A one-off almost-universal collision game | `seededHashCollision`, `RandomSystems/SwitchingLemma.lean` | Should be stated once against the hash predicate |
| Convexity of distance in mixtures | `acceptMass_par_right_mixture`, `RandomSystems/StrictParallel.lean` | Trapped in the parallel-composition setting; the general `statDist` statement is what MPR07 Lemma 3 needs |
| Independence of random variables | `IndepRV`, `iIndepRV`, `RandomSystems/Dist.lean` | No conditional, pairwise, or k-wise variant |

### 12.5 Build order

Each step unlocks the next; the partition is by file, so steps at the same level
can run concurrently without collision.

1. Expectation, variance, moments, Markov / Chebyshev / Cauchy–Schwarz, and the
   collision-probability quantities — new module.  Folds `expectW` in.
2. Statistical-distance alternate forms and the distribution-level guessing
   identity — `RandomSystems/StatDist.lean`.
3. Min-entropy and guessing probability promoted off `PMF` onto `Dist` and
   connected to `statDist`.
4. Shannon calculus — new module.  Needs step 1.
5. Probability measure on an event algebra.  Small, and cashes out every
   universal event inequality at once.

Not scheduled, and honest about why: martingales (step 5+ of MauPie04's route,
which MPR07 deliberately supersedes), χ², and the Fannes-type continuity bounds.

### 12.6 Audit provenance, and what has landed

The inventory above comes from a paper-by-paper read (2026-08-05) of Maurer02,
MaPiRe07, MauPie04, LanMau20, CR18_LN, PorRen22 App. A, cbc-improved,
BonehShoup App. B, and the Lanzenberger dissertation.  Two qualifications a
reader should carry:

- **Lanzenberger chapter 2 is already formalized end to end.**  Definitions
  2.1–2.8, Lemma 2.18, Theorems 2.29/2.31/2.32, Lemma 2.30, Lemma 2.33 and the
  Winnability Theorem all have general counterparts in the tree
  (`RandomSystems/StatDist.lean`, `RandomSystems/Coupling.lean`,
  `RandomSystems/MultiSystemCoupling.lean`, `RandomSystems/RandomSystemCoupling.lean`,
  `RandomSystems/GameWinnability.lean`, `RandomSystems/LanzenbergerChain.lean`).
  The gap in that dissertation is concentrated in **chapter 3** (amplification)
  and in §2.5 (combiners), not in the coupling theory.
- The CR18_LN and GegMau26 rows of the underlying audit were produced by
  sub-delegation and one of the two sub-reports was not recovered.  Treat those
  two papers' rows as **provisional** until re-read directly.

Landed so far, in `RandomSystems/StatDist.lean`, compiled and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only): `statDist_eq_weight_sub_sum_min`,
`statDist_eq_one_sub_sum_min`, `statDist_eq_half_sum_abs_of_weight_eq`,
`guessProb`, `avgSuccessProb_eq_mass_sub_mass_add_weight_div_two`,
`avgSuccessProb_le_half_add_half_statDist`,
`avgSuccessProb_eq_half_add_half_statDist_of_forall_eq_true_iff_lt`,
`sSup_avgSuccessProb_eq_half_add_half_statDist`.  That is step 2 of §12.5; step 1 is
not started.

### 12.7 Landed 2026-08-05/06 — the L0/L1 foundation

**Two modules, split so the expectation layer stays free of measure theory.**
Both compile at exit 0 with zero `sorry`/`axiom`; spot-checked results depend
only on `propext`, `Classical.choice`, `Quot.sound`.

`RandomSystems/DistExpect.lean` (imports `RandomSystems.Dist` plus pure
analysis only — no measure theory): `Dist.expect` and `Dist.variance`, with
each result carrying the weakest layer at which it is true.  Signed:
`expect_add_left`, `expect_smul_left`, `expect_sub_left`, `expect_add_right`,
`expect_const_mul`, `expect_smul_right`, `expect_const`, `expect_finset_sum`,
`expect_indicator`.  `NonNeg`: `expect_nonneg`, `expect_mono`,
`expect_le_mul_weight`, `mass_ge_le_expect_div` (Markov),
`expect_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz), `expect_sub_sq_nonneg`,
`variance_nonneg`.  `isProbDist`: `variance_eq_expect_sq_sub_sq_expect`,
`expect_sq_sub_sq_expect_nonneg`, and Jensen in both directions
(`ConcaveOn.le_map_expect`, `ConvexOn.map_expect_le`).

`RandomSystems/DistMeasure.lean` (the one-way transport): `Dist.toPMF`,
`Dist.toMeasure` with its `IsFiniteMeasure` instance, `Dist.toSignedMeasure`
and `Dist.jordanDecomposition`; the integral bridge
`integral_toPMF_eq_expect`; the mass/measure correspondence
(`toMeasure_apply_massSet`, `toMeasure_univ`, `toPMF_toMeasure_apply`);
a transported Chebyshev (`mass_ge_le_variance_div_sq`); and
`statDist_eq_toReal_posPart_univ`.

Two design receipts worth keeping.  First, the transported Chebyshev's binders
are measure-free — the `MeasurableSpace` is introduced by `letI ... := ⊤` at the
proof site, per `DESIGN.md` §12 point 3, with the instance-carrying form kept
private as `mass_ge_le_variance_div_sq_aux`.  The Jordan characterization is the
deliberate exception: its *statement* is about a signed measure, so mathlib
vocabulary is the point of it.  Second, `expectW` is gone from
`RandomSystems/HTechnique/Derivation.lean`, which still compiles; the surviving
mentions in `RandomSystems/HCTR2.lean` are prose in doc comments.

### 12.8 Transport probes — measured, not assumed

Both probes live in `scratch/` (excluded from every build target and from
`module_audit.py`), and both are receipts rather than library code.

`scratch/TransportProbe.lean` (398 lines, exit 0, axiom-clean): the transport is
cheap — ~180 lines and 9 distinct `ENNReal` lemmas; the integral bridge is 4
lines; Chebyshev's side conditions (`MemLp`, `AEMeasurable`, `IsFiniteMeasure`)
are all discharged by discrete automation.  It also fixes the layer table of
§12.7 by proving, for each statement, a counterexample one layer down.

`scratch/IndepProbe.lean` (493 lines, exit 0, axiom-clean): independence
transports too, and more cheaply — **3** distinct `ENNReal` lemmas for eight
transported theorems.  `Dist.IndepRV`/`iIndepRV` map to mathlib's
`IndepFun`/`iIndepFun` because mathlib states independence as an equation
between measures and a discrete measure is determined by its singletons.
Variance additivity under independence, Hoeffding via the sub-Gaussian mgf, and
**KL divergence** all came through with usable `Dist`-side statements.

**Still unmeasured, and not to be assumed a third time: filtration-shaped
theorems (Azuma, martingales).**  Their entry obligations are sub-σ-algebras on
the sample space, which the discrete-carrier argument does not kill.

Upstream note: mathlib lacks a `MeasurableSingletonClass` instance for a finite
index product; the probe hand-rolls it in five lines.

### 12.9 Composability corpus — audited, near-zero yield

Read visually and in full: BMT18 (46 pp.), MaRuTa12 (21 pp.), CoMaTa13 (20 pp.),
2021-156 (33 pp.), 2105.05949v3 (23 pp.), XTS_comments (10 pp.); PMMRT17 read at
preliminaries and Appendix G.  Under the "reusable mathematical facts only"
scope this corpus contributed **four** items, three of them from one paper:

- MaRuTa12 Sect. 3.1 Example 2 — one-time-pad perfect secrecy stated as a
  worked example rather than a numbered lemma.
- XTS_comments Sect. 3.1.1 — the `(ε,γ,ρ)`-uniform function definition, and the
  fact that powers of a primitive element of `GF(2ⁿ)` give a
  `(2⁻ⁿ,2⁻ⁿ,2⁻ⁿ)`-uniform family (with `j = 0` necessarily excluded).
- XTS_comments Sect. 3.3 — a uniform random permutation composed with those
  multipliers is almost-XOR-universal.  **The paper's printed constant `2⁻ⁿ` is
  marginally too strong**: for `i ≠ i'`, `j = j'`, `δ ≠ 0` the exact value is
  `1/(2ⁿ − 1)`.  Use `1/(2ⁿ − 1)` if this is ever formalized.

BMT18, CoMaTa13, PMMRT17, 2021-156 and 2105.05949v3 contributed nothing
separable — their probability content is distinguishing-advantage arithmetic,
hybrid factors, and system-model structure, all out of scope by §12.1.

**Not yet done**: the direct re-read of CR18_LN (its sub-report was lost, so the
CR18 rows stay provisional per §12.6), and JosMau20 / BBM18 / MauRen11 /
MauRen16 / MMPRT18 / BDPV08 / Maurer11 / Maurer13a / Maurer13b / LiuMau20 /
cbc-improved §6–8.

### 12.10 Maurer-adjacent slice — audited, stopped early by design

Read visually and in full: MauRen16 (22 pp.), MauRen11 (21 pp.), BDPV08 sponge
(17 pp.); MMPRT18 preliminaries (pp. 6–11); cbc-improved §6–8 incl. appendices
(pp. 10–24).  **Deliberately not read**: JosMau20, BBM18, Maurer11, Maurer13a,
Maurer13b, LiuMau20 — two of the five papers above yielded exactly nothing, and
those six are the same genre.  MauRen11 is nil (relations, pseudo-metrics,
framework throughout).  MMPRT18 is nil and says so itself on p. 6: the paper is
deterministic-only, probabilistic systems are future work.

New items, all verified to exist or not exist at the cited locations:

- **The composing chain-rule INEQUALITY is missing** (cbc-improved Lemma 8, App.
  B p. 23).  The generic content: if each conditional step satisfies
  `mass(⋀_{k<j+1}Aₖ)/mass(⋀_{k<j}Aₖ) ≤ pⱼ`, then `mass(⋀_{k<i}Aₖ) ≤ ∏_{j<i} pⱼ`.
  The **equality** is present and general (`mass_biForall_lt_eq_prod`,
  `RandomSystems/Dist.lean:1028`) and the single-step counting bound too
  (`mass_le_of_fiber_bound`, `RandomSystems/Dist.lean:1470`), but nothing
  composes them; confirmed by search — no `mass_*_le_prod` of any spelling
  exists.

  **CORRECTION, 2026-08-06.**  The sentence originally here — "CBC, SoP and
  HCTR2 each open-code a variant" — was **false**, and it was the whole
  justification for the item.  It came from a grep for files containing
  `prod_le_prod`, which says nothing about what those products range over.
  Checked properly: `RandomSystems/CBCStructureGraph.lean` contains **zero**
  occurrences of `∏`/`Finset.prod` and **zero** `induction`;
  `RandomSystems/SoP/XORComplementSquareRoot.lean` mentions neither `Dist` nor
  `mass` (its products are Fourier/character products).  The tree took the other
  route deliberately — CBC and HCTR2 both bound bad-event mass by a *fiber count
  on a single uniform law* (`CBCStructureGraph.lean:760 mass_chargedEvent_le`;
  `HCTR2_FINAL.lean:3621` and `:4113`, which say so in prose) and never
  condition step by step.  The nearest genuine sibling,
  `RandomSystems/SoP/SoP2.lean:4437 online_state_law_agreement_ge_product`, is
  the mirror inequality over a *dependent family* of laws and cannot be reached
  by a `ProbDist Ω`-shaped lemma.  **There is no call site, so the item was cut
  rather than landed.**  If a caller ever appears, the designed statement is
  mass_biForall_lt_le_prod (name proposed, not yet written) with a multiplicative
  (equivalent under `NonNeg` plus event nesting, and it dodges division by zero).

  **Real duplication found in its place**: the Weierstrass inequality
  `1 − ∑aᵢ ≤ ∏(1−aᵢ)` exists in **four** independent copies —
  `RandomSystems/Counting.lean:27`, `RandomSystems/HTechnique/Derivation.lean:5029`,
  `RandomSystems/Legacy/Applications/XoPANOVA.lean:153`, and
  `RandomSystemsCC/Symmetric/SpongeBDPV.lean:731`.  That is the generalize-in-place
  item this row was reaching for.
- **Geometric tail in usable packaging** (cbc-improved Lemma 9, p. 12):
  `Σ_{i≥2} xⁱ = x²/(1−x) ≤ 2x²` for `0 ≤ x ≤ 1/2`, used to collapse a
  counter-stratified bad event onto its first stratum.  No geometric-series
  result exists under `RandomSystems/`, and mathlib's has no bridge to masses.
- **Min-entropy sampling** (MauRen16 App. Prop. 1 / Cor. 2, p. 20).  **Caveat
  recorded deliberately: MauRen16 does not prove Prop. 1**, it cites
  Wullschleger TQC 2011 Thm 1.  Formalizing means going to that source, not to
  MauRen16 — do not treat the citing paper as the proof.
- Falling-factorial permutation/transformation ratio (BDPV08 Lemma 5, p. 15) —
  genuinely absent, but no caller currently wants it.
- `Pr[E](1−Pr[E]) ≤ 1/4` (MauRen16 p. 14) — trivial, recorded only because it is
  the source of the impossibility constant `1/4`.

Confirmed already present and general, so do not re-derive: the optimal
distinguisher / half-`L¹` identity (BDPV08 eq. (2)) at
`RandomSystems/StatDist.lean:225` and `:377`; the birthday product engine
(BDPV08 Lemma 4) at `RandomSystems/Counting.lean:43`, which is *more general*
than the paper's instance; the union bound (cbc-improved App. A) at
`RandomSystems/Dist.lean:294` and `:327`.

The min-entropy cluster in `RandomSystemsCC/MauRen16Impossibility.lean` is
re-confirmed as bucket (b) and specialized three ways: carrier is mathlib
`PMF (α × γ)` rather than `Dist`, conditioning is hard-wired to the second
component of a pair, and it sits inside the application that first needed it.
That is the L2 promotion already scheduled in §12.5.

### 12.11 CR18_LN re-read — the provisional rows of §12.6 are retired

Read visually this session: PDF 7–55 (printed 1–98) and 64–68 (printed
115–124) — chapters 1–3, §4.1–4.9.2, §5.2.1–5.5, §6.1.  The 2-up offset was
established from content pages and cross-checked against all four previously
read anchors rather than assumed.  Combined with the earlier direct reads
(App. A, §4.9.3–4.11, §6.2–7.3), CR18_LN is now covered end to end and its
rows are no longer provisional.

New absent items, beyond what §12.3 already lists:

- **Exercise 4.4, p. 83 — the missing bridge between the distance layer and the
  expectation layer.**  Perturbing a distribution by `d` in statistical distance
  moves any bounded functional by at most `(sup f − inf f)·d`; the tree has only
  the indicator case (`mass_sub_mass_le_statDist`, `RandomSystems/StatDist.lean:284`).
  Now that `Dist.expect` has landed this is the natural next lemma, and it is
  what makes the two layers compose.
- **Exercise 2.2, p. 18** — a uniform group element absorbs: `U ⋆ X` is uniform
  and independent of `X` *whatever* `X`'s law.  The fact behind every one-time
  pad, mask and re-randomisation step.  Nearest existing is a fiber-count
  criterion with no independence content
  (`fTransform_uniform_eq_uniform_of_card_fiber_mul`, `RandomSystems/Dist.lean:1149`),
  plus a hand-rolled special case at `RandomSystems/Counting.lean:686`.
- **Lemmas 2.3 and 2.4, pp. 26–27** — bit-guessing ↔ distinction *for systems*.
  Both sides exist (`guessProb` at `RandomSystems/StatDist.lean:323`, `advantage`
  at `RandomSystems/Distinguishing.lean:112`); nothing joins them.  This is the
  system-level half of the §12.3 guessing row, which the earlier work
  deliberately did only at the distribution level.
- **Def. 4.11 and Lemma 4.8, p. 95** — the amplification analysis pair
  `ψ_q(x) = 1−(1−x)^q`, `χ_q = ψ_q⁻¹`, with `ψ_q(x) ≥ 1−e^{−xq}`; and
  "win at least one of `q` independent copies" resting on
  `Pr[⋁Aᵢ] = 1−∏(1−pᵢ)` for independent events.  Carrier is ready
  (`Dist.iidPow`).
- Exercise 4.5 (`δ(Unif J, Unif H) ≤ 1 − |J|/|H|`); §3.6.1 Chapman–Kolmogorov
  for plain conditional distributions; §4.3.6 majority-vote amplification (same
  gap as the Chernoff row, and `scratch/IndepProbe.lean` shows Hoeffding
  transports).
- §6.1.2, p. 124 supplies the **witnessing construction** for k-wise
  independence (polynomial evaluation over `GF(2^m)`) that the existing §12.3
  k-wise row lacked.

New specialized items:

- **Derandomisation of distinguishers** (Def. 2.7 remark, p. 25).
  `maxAdvantage` (`RandomSystems/Distinguishing.lean:136`) sups over
  *probabilistic* distinguishers only; that this equals the deterministic sup is
  unproved, and cheap — `advantage` is affine in `D`.
- **Multi-game union bound** (§4.5.1, Def. 4.6, pp. 90–91).  The event-level
  union bound is general (`RandomSystems/Dist.lean:294`), but there is no
  sub-additivity for `winProb`/`winningMass` and no multi-game object.

### 12.12 GegMau26 verification — notes confirmed, headline claim sharpened

Nine pages spot-checked visually (6, 26, 27, 28, 37, 38, 41–43).  **Every claim
checked was confirmed, several verbatim; nothing was found wrong**, and all 17
cited `AbstractCrypto/EventAlgebra.lean` anchors resolve.  One line drift in the
old notes: `mass_le_one` is at `RandomSystems/Dist.lean:410`, not `:380`.

The important refinement: **the paper does not axiomatise probability on event
algebras at all** — no probability assignment, no extension theorem, no
realization theorem; generalising probability *to* event algebras is explicitly
future work (p. 28).  The connection is purely forgetful: a σ-algebra is
Boolean hence an event algebra, so an order inequality reads inside whatever
measure already exists.  A second imprecision worth carrying: the paper
justifies the transfer "by the additivity of `Pr`", but it is really
*monotonicity* followed by *finite sub-additivity*.  §12.3's event-algebra row
is corrected accordingly.

Not verified, so still the prior agent's word: Lemma 1 p. 8, Lemma 2 p. 9,
Thms. 1–2 p. 7, the §§3–4 UEI content, Appendices D/E, and the App. F.3 listing.

### 12.13 Landed 2026-08-06 — the four foundation items (one cut)

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, and
purely additive: no signature, name or import was removed anywhere.

**The distance/expectation bridge** (CR18 Exercise 4.4, printed p. 83) — this is
what makes `RandomSystems/DistExpect.lean` and `RandomSystems/StatDist.lean`
compose, and `StatDist.lean` now imports `DistExpect` (acyclic; `DistExpect`
imports only `RandomSystems.Dist`).  The exercise's own footnote 12 settles the
constant question: the sharp factor is the **range** `M − m`, not `2·sup|f|`.
- `StatDist.lean:311` `expect_sub_expect_le_statDist` — **bare signed layer**, no
  weight hypothesis and no `Fintype`; strictly generalizes
  `mass_sub_mass_le_statDist` from an indicator to any `[0,1]` observable.
- `StatDist.lean:333` `expect_sub_expect_le_mul_statDist` — signed plus
  `|X| = |Y|`.
- `StatDist.lean:359` `abs_expect_sub_expect_le_mul_statDist`.

Equal weight is load-bearing and was checked, not assumed: at `X = single a 1`,
`Y = 0`, `f ≡ 5` the left side is `5` while `(M−m)·δ = 0`.  `NonNeg` is *not*
needed — the proof is recentring plus a pointwise `max` — so requiring it would
have been strictly stronger than the mathematics.

**Probability on an event algebra**, split by tower level so the mathematics
lands at L0 and only the wiring sits in the bridge:
- `Dist.lean:317` `mass_or_add_mass_and` — modularity, **signed layer**, since it
  is a pointwise indicator identity.  This was the missing ingredient; the
  sub-additivity guessed in §12.3 is its strictly weaker consequence.
- `RandomSystemsCC/EventValuation.lean:71` `massValuation` — the
  `AbstractCrypto.LatticeValuation` instance, `NonNeg` layer, with exactly one
  field (`mono`) responsible for that hypothesis.  No normalization: the
  abstract structure has no `m ⊤ = 1` field, so sub-distributions qualify.
- `:94 mass_le_add_of_le_sup`, `:110 mass_le_sum_of_le_finsetSup` — the GegMau26
  transfers in `Dist.mass` vocabulary.  These differ from the native
  `Dist.mass_exists_le` by taking a **lattice-order** hypothesis rather than a
  pointwise existential, which is exactly what lets an abstractly-proved event
  inequality be consumed.

**Derandomisation of distinguishers** (CR18 remark after Def. 2.7, printed
p. 25).  `maxAdvantage` can express it with no new definition:
- `MaxWinProb.lean:147` `winProb_eq_expect_single`, `Distinguishing.lean:189`
  `advantage_eq_expect_single`, `Distinguishing.lean:205`
  `maxAdvantage_eq_sSup_deterministic` — all **bare signed layer**; `isProbDist`
  enters only through `maxAdvantage`'s own definition, never as an added
  assumption.
- `DistExpect.lean:143` `Dist.expect_sub_right` — the function-side mirror of
  `expect_sub_left`, genuinely missing and needed by the above.

**Cut**: the composing chain-rule inequality, because its premise was false.  See
the correction in §12.10.

Gate note: `lake build RandomSystems` remains red-pre-existing at **eight**
targets, a strict subset of the nine recorded earlier —
`RandomSystems.Jost.SurfaceWidgets` now builds.  Independent evidence the rest
predate this work: `ReductionByConverter.lean:83` cites
`Dist.fTransform_finsuppSum`, which exists neither in the worktree nor at HEAD.
`moduleAudit` and `docAudit` are both red on pre-existing entries only.

### 12.14 Adaptive-query collision bounds — the fresh-coordinate lemma (queued)

Added 2026-08-07, from the HCTR2 §3.4 work.  That proof's hard part was not the
counting but the *adaptive* collision fibres: choosing a genuinely independent
coordinate without conditioning on future queries.  The paper's sequential
argument ("once the prefix is fixed, the current response is still fresh and
uniform") is valid but suppresses four things Lean forces into the open — which
prefix is fixed, which query shapes depend on earlier answers, which coordinate
remains independent, and why later transcript information is not conditioned on.
That gap is generic, not HCTR2-specific: it recurs for random functions, random
permutations, lazy sampling, oracle games, and every adaptive collision argument.

**Proposed reusable statement — a fresh-coordinate lemma.**  Informally: if an
adaptively selected coordinate, and the bad event's dependence on it, are both
unchanged when that coordinate is resampled, then a fibre count at the selected
coordinate bounds the probability.  The selection function must not see the coin
it is about to flip, and *that* is the hypothesis to make explicit — a resampling
operator together with an invariance condition on the selector.

Placement and existing anchors:

- The **non-adaptive** case is already present and general:
  `Dist.mass_le_of_fiber_bound`, `RandomSystems/Dist.lean:1470` — a fixed
  coordinate with a solution count.  The queued lemma is its adaptive
  generalization and belongs beside it, at **L1**.
- The **system-level** counterpart already exists as theory: Maurer02 Theorem 2
  and its CR18 condition-C form say adaptive strategies are no better than
  non-adaptive ones under a stated condition, and the tree carries that
  machinery (`RandomSystems/HistoryConditionC.lean`, `RandomSystems/FixedQuery.lean`).
  The queued lemma is the *distribution-level* fact those rest on; the two should
  be connected once it exists, not developed independently.
- `scratch/IndepProbe.lean` showed independence transports into mathlib, so a
  filtration-flavoured formulation is reachable — but filtration-shaped mathlib
  theorems remain the one class the transport probes never measured (§12.8), so
  do not assume that route is cheap.

Status: **design not yet fixed.**  Write the statement and check it against the
HCTR2 §3.4 fibre theorem (`RandomSystems/HCTR2_FINAL.lean`) as the first
consumer before generalizing — a fresh-coordinate lemma with no call site would
repeat the mistake corrected in §12.10.

### 12.15 L2 opened — `RandomSystems/Entropy.lean` (2026-08-07)

550 lines, no `sorry`, no `axiom`; all 45 public declarations across this and the
touched files verify to `propext`, `Classical.choice`, `Quot.sound`.  §12.5 step 3
is done, and the §12.4 min-entropy row is **resolved**.

**Naming, per mathlib's live prefix conventions** (`condVar`/`condExp` for
conditional, `variance`/`evariance` for `ℝ≥0∞`):
- `Dist.guessProb` / `Dist.condGuessProb` — the IT notion, matching
  `minEntropy` / `condMinEntropy`.  CR18's p_max is *this* number, so it has
  one identifier and the paper glyph lives in the docstring.
- `avgSuccessProb` in `RandomSystems/StatDist.lean` — the former `guessProb`
  there, renamed with every caller updated and no alias left.  It is
  prior-averaged over a *given* rule, which is mathlib's `avgRisk` register;
  the Bayes-optimal statement is the supremum, so
  `sSup_avgSuccessProb_eq_half_add_half_statDist` is `1 − bayesRisk`, i.e.
  `bayesRisk = ½ − ½·δ(X,Y)`.
- `econdGuessProb` in `RandomSystemsCC/MauRen16Impossibility.lean` — the
  `ℝ≥0∞`/`PMF` instance.

**Carrier decision**: the `Dist` statements are ℝ-valued with layer hypotheses
and do **not** route through `RandomSystems/DistMeasure.lean`.  Every fact here is
an order/algebra fact about finitely supported real masses; the transport would
have forced `[Fintype]` into signatures (`toPMF` needs it) and pulled measure
theory into an L2 leaf.  `Entropy.lean` does not import `DistMeasure`.

**Layer findings worth keeping**, each the weakest that works:
`collProb_nonneg` is **signed** — it is a sum of squares, the one order fact in
the file needing no hypothesis.  `distFromUniform_eq_statDist_uniform` needs only
`weight = 1`, and is the bridge to the `statDist` calculus.  Lemma 7.6 splits:
`one_div_card_le_collProb` needs `weight = 1`, `collProb_le_guessProb` needs full
`isProbDist` (non-negativity for `P² ≤ P·p_max`, normalization to collapse
`p_max·|𝒳|`).  Lemma 7.7 consumes 7.6 for its radicand.  Both were left as
exercises in the source and are now proved.

**Deleted from `MauRen16Impossibility.lean`**: `minEntropy`, `condMinEntropy`,
chain_rule (the name is retired) and three `ℝ≥0∞` side-condition lemmas — all dead there, so the tree
now has exactly one min-entropy and one chain rule, at L2.

**One judgement call to audit.**  `econdGuessProb` *stays* in the CC file rather
than becoming a wrapper.  It is not a second copy: MauRen16's alphabet is `ℕ`
(infinite) and its strategy is an arbitrary `Converter ℕ = ℕ → PMF ℕ`, neither
expressible by finitely supported `Dist`.  Making the call site consume the L2
lemma would need a "randomized ≤ deterministic sup" argument plus a `toPMF`
bridge, and would drag `DistMeasure` into a CC file for one inequality.  The two
are related by the `e`-prefix naming and by cross-references in both directions;
a *proved* `Dist ↔ PMF` bridge was deliberately not attempted.

**Staged, not yet relocated**: six `Dist`-level helpers and a private
"expectation under uniform is the average" lemma sit in `Entropy.lean` §0 but
belong at L0/L1 (`Dist.lean` / `DistExpect.lean`).  They were left in place to
avoid invalidating every olean while the carrier migration was being repaired
concurrently; move them once that settles.

### 12.16 Lifting operators — `RandomSystems/DistLift.lean` (2026-08-07)

439 lines, no `sorry`, no `axiom`.  All 42 public declarations are
`[propext, Classical.choice, Quot.sound]` except two order-lemmas that need only
`[propext, Quot.sound]`.

**The finding that shaped the module: no `Dist.posPart` was written, because
mathlib already has it.**  `Mathlib.Data.Finsupp.Order` gives `A →₀ ℝ` a
`Lattice`, so `Mathlib.Algebra.Order.Group.PosPart`'s `X⁺`/`X⁻` *are* the Jordan
parts of a signed `Dist`, with `posPart_sub_negPart`,
coprimality of the two parts and `posPart_nonneg` supplied upstream.  Writing a
bespoke operator would have left two (`DESIGN.md` §12 point 4) and forced an
unfold at every mathlib interaction.  The module supplies the *`Dist` face*
instead.  That import was genuinely new to this cone.

**The unlock is one lemma**: `nonNeg_iff_zero_le : X.NonNeg ↔ 0 ≤ X`.  It is what
lets every mathlib ordered-group fact reach a `NonNeg` hypothesis.

**Transport laws are all at the signed layer with no hypothesis** — `expect`,
`weight` and `mass` are linear in the distribution, so the Jordan split costs
nothing: `expect_posPart_sub_expect_negPart`, `weight_posPart_sub_weight_negPart`,
`mass_posPart_sub_mass_negPart`.  Also `statDist_eq_weight_posPart :
statDist X Y = ((X - Y)⁺).weight`, with no layer hypothesis and no `Fintype`.
Normalization: `weight_normalize` needs **only** `weight ≠ 0` (non-negativity
plays no part in the weight computation); `isProbDist_normalize` needs `NonNeg`
as well.

**Three lifted corollaries, each stated so it cannot be misread** as the original
inequality holding one layer down:
- `ConcaveOn.le_map_expect_of_nonNeg` — Jensen at `NonNeg`, with the weight
  factor `|X| · φ(𝔼_X[f]/|X|)`.  It collapses to the `isProbDist` form at
  `|X| = 1`, and on the counterexample witness in `scratch/TransportProbe.lean`
  it holds with equality — that weight factor is precisely what the
  counterexample measures.
- `weight_sq_mul_variance_normalize` — the `𝔼[f²] − 𝔼[f]²` variance form below
  `weight = 1`.  An *identity*, so no hypothesis-weakening reaches it.
- `mass_ge_le_expect_posPart_div` — Markov for a **signed** distribution, with
  the expectation taken under `X⁺`.  The docstring states outright that this is
  not Markov for `X` and that the signed counterexample stays true.

**Jordan identified with mathlib's**: `toJordanDecomposition_posPart` /
`_negPart` prove that mathlib's Jordan decomposition of `toSignedMeasure X` is
literally the pair of transported `Dist`-level parts, so §12.7's
`statDist_eq_toReal_posPart_univ` is now a specialization rather than a
coincidence.

**`RandomSystems/Coupling.lean`**: all three private ℝ-level helpers deleted and
their nine call sites repointed; the file compiles.

**Two duplication items this surfaced, both needing follow-up under §12 point 4:**
1. `eq_zero_of_nonNeg_of_weight_eq_zero` in `DistLift` is a **third** copy of a
   fact also at `RandomSystems/RandomSystem.lean:2898` and
   `RandomSystems/BoundedAttainment.lean:163`.  Both sit *below* `DistLift` in
   the import graph, so neither is reachable from it, and deleting the
   `BoundedAttainment` one is blocked by a consumer in
   `RandomSystems/MultiSystemCoupling.lean`.  Recorded, not resolved.
2. Latent name collision: `Dist.weight_add` and `Dist.weight_sub` are each
   declared **twice** — `RandomSystems/VirtualPDS.lean:85,90` and
   `RandomSystems/MultiSystemCoupling.lean:177`.  Harmless only while the two
   never meet in one import cone.

**Boundary note**: the agent also edited `RandomSystems/DistMeasure.lean`, which
was neither owned nor forbidden, to keep `DistLift` measure-free — `Coupling`
imports `DistLift` and sits upstream of most of the tree, so pulling
mathlib measure theory into that cone would have been the regression §12 warns
about.  The rationale is sound and the edit is confined to one added import and
one section.

### 12.17 Consolidation pass (2026-08-07) — five independent proofs eliminated

Net **−5 deleted, +19 added**; of the additions, 15 are new mathematics and the
rest absorb inline copies.  All 25 results `[propext, Classical.choice, Quot.sound]`.

**Weierstrass, four copies → one.**  Three were the same real-valued fact at
different index types; the fourth (`NNReal`) was genuinely different, because
truncating subtraction discharges `aᵢ ≤ 1` from the statement itself, so it is
*not* a specialization and needs a case split on `∑ aᵢ ≤ 1`.  It was **derived**
from the real form rather than kept as a second proof.  mathlib carries the exact
expansion but not the inequality, so nothing could be imported.  Canonical form is
now `one_sub_sum_le_prod_one_sub` in `RandomSystems/Counting.lean`, with the
counterexample for why `f i ≤ 1` cannot be dropped recorded in its docstring.
Seven call sites moved; a spurious `[LinearOrder ι]` was shed.

**The two birthday bounds, merged by proving the missing link.**  They bounded
provably equal quantities but neither was stated in terms of the other, and
neither was uniformly stronger — `Counting.birthday_bound` was arithmetic with
the sharper `q(q−1)` but needed `q ≤ N`; `pcoll_le_birthday` was probabilistic
with `q²` and no hypothesis.  The missing link, never stated in the tree, is that
`pcoll` *is* `1 − (t)_q/t^q`; it is now `pcoll_eq_one_sub_descFactorial_div`.
`birthday_bound` is canonical, `pcoll_le_birthday_tight` is unconditional, and the
old union-bound proof is gone.

**First collision LOWER bounds in the tree** (Boneh–Shoup Thm B.1, read visually
at PDF 1115–1118): `one_sub_exp_le_pcoll` and `min_le_pcoll`, both unconditional,
plus the upper `pcoll_le_one_sub_exp` under a genuine `2q ≤ t` side condition.
This matters because every existing collision bound proves *security*; a lower
bound is what an attack argument needs, and there was none.

**Third verbatim duplicate found**: the `SwitchingLemma` copy was
character-for-character `card_pair_eq_type` at `α := Fin t`.  Deleted.

**Cut, with reason**: general-`k` Corollary B.2 (uniformity minimizes collision
probability).  Formalized it is Maclaurin's inequality on elementary symmetric
polynomials, which mathlib does not carry; building it would have been the whole
task.  The `k = 2` case landed as `inv_card_le_iidPow_two_mass_collides`, and the
gap is recorded at both `inv_card_le_*` docstrings.

### 12.18 Universal hashing unified — `RandomSystems/UniversalHash.lean` (2026-08-07)

299 lines, no `sorry`; all eighteen results `[propext, Classical.choice, Quot.sound]`.
Three unrelated notions became one.

The definition quantifies a **relation** `Φ` on digests rather than hard-wiring
equality, and takes `δ : ℕ → NNReal` at the max of two message lengths — verbatim
CR18 Definition 6.2, whose own footnote says it is more general than the
literature's scalar form.  Both choices are load-bearing: the length-dependent `δ`
is what makes Corollary 6.4 sayable at all, and `Φ` folds in almost-XOR-universality
**without requiring any algebraic structure** on the digest type.

Four specializations, all `abbrev` so they are reducibly defeq — no second notion
is created: `IsAlmostUniversal` (CR18 Def 6.2), `IsEpsUniversal` (Boneh–Shoup Def
7.4), `Is2Universal` (CR18 Def 7.2, which the source itself calls a special case
of δ-AUH), `IsAlmostXorUniversal` (HCTR2 §3.2 Property 2).

`UHF` in `RandomSystems/BonehShoup/Ch7UHF.lean` is **deleted** — it was a bare
carrier whose docstring apologized for holding no security content — and its eight
use sites repointed.  `EpsUniversalHash` survives as the *bundle*, but its
`universal` field is now the general notion, `rfl`-equal to the old spelled-out
proposition, so no downstream statement moved.  `hashCollision_prob_le` went from
75 lines of bespoke counting to a 9-line corollary of the general union bound.

**Not repointed, with costs measured**: `SwitchingLemma.lean`'s
`seededHashCollision` (zero proof edits — just move three declarations, the
definition is `rfl`-equal); `HCTR2_FINAL.lean` (~half a day, and it touches the
§3.4 accounting, so it should wait); `HCTR2.lean` (needs a subtype for its domain
guard); `UHFThenURF.lean` (deliberately untouched — changing it would alter the
statements sitting under existing `sorry`s).

Correction to the record: `UHFThenURF.lean` has **three** `sorry`s, not the two
previously noted.  None was added or altered; only how one goal *displays* changed,
and the two spellings are `rfl`-equal, so the obligation did not weaken.

### 12.19 The `NNReal → ℝ` carrier migration, finished (2026-08-07)

Commit `df9ded9` (2026-08-01) moved `Dist A` from `A →₀ ℝ≥0` to `A →₀ ℝ`, turning
non-negativity from a structural property into the predicate `Dist.NonNeg`.  Ten
modules predated it and were never migrated; `lake build RandomSystems` had been
red on them.  All ten are now done.  My earlier diagnosis of this — "one root
cause plus downstream" — was wrong: they were ten **independent** failures with a
common origin.

Migrated: `MultiSystemCoupling`, `ReductionByConverter`, `RandomSystemMetric`,
`AttainmentCounterexample`, `GameWinnability`, `TranscriptHybrid`,
`HTechnique/SoP/VisibleLaw`, `ThesisModel`, and (in progress) `LanzenbergerChain`,
`HTechnique/SoP/TranscriptPrefix`.

**The house pattern**: restore the hypothesis at the **weakest layer that works**
— `NonNeg` sufficed almost everywhere, `isProbDist` only where normalization is
genuinely used — and never change what a theorem *says*.  Where a `NonNeg`
witness was already to hand it was used rather than adding a hypothesis; a
`PFunPDS.Prob` carries `isProbDist` by definition, so `S.property.1` supplies it.

**Three places where truncated `NNReal` subtraction had been silently doing
mathematical work**, each restored to the faithful reading rather than the
convenient one:
- `TranscriptHybrid`: the weight defect `S.weight − T.weight` is now
  `max (S.weight − T.weight) 0`.  The untruncated version is **false** — at
  `n = 0` the bound is smaller than `δ` whenever `|T| > |S|`.
- `HTechnique/SoP/VisibleLaw`: `visibleStatDist_eq_sum`'s right-hand side is now
  `∑ max (real y − ideal y) 0`, which is exactly what the `NNReal` spelling
  denoted.
- `GameWinnability`: `infWinnability`'s index set gained `H.NonNeg`.  Without it a
  signed `H` with the same observable behaviour drives the infimum to `−∞`, since
  `Real.sInf` of an unbounded-below set is junk.

**Two conclusions were strengthened, not weakened.**  `winnability_theorem_…`'s
existential now also yields `G'.NonNeg` (Theorem 2.31's attainment already
provided it), restoring the docstring's claim that `G'` is a distribution over
deterministic games.  Every headline in `AttainmentCounterexample` — the
`Adv = 1/2` and `Δ = 1` witnesses and the refutation built on them — has a
byte-identical statement.

**The one decision this surfaced.**  `theorem_2_37_winnability_theorem`
(`LanzenbergerChain.lean:283`) needed `G.NonNeg`, and it is *not* derivable at the
wrapper.  Ruling: add it.  Lanzenberger's Definition 2.36 takes `ω(S^A)` as an
infimum over representatives `S^A ∈ 𝐒^A`, and those representatives are PDS —
probability distributions over deterministic systems — so non-negativity is part
of what membership in the class means, not a new assumption.  The `NNReal` carrier
supplied it structurally; the ℝ carrier must state it.  This is a restoration of a
lost hypothesis, not a change to the thesis statement.

### 12.20 Conditional probability and independence (2026-08-07)

Three modules, 972 lines, no `sorry`; all 46 public declarations
`[propext, Classical.choice, Quot.sound]`.  `RandomSystems/DistCond.lean` imports
`RandomSystems.Dist` only — no measure theory, mirroring the `DistExpect` split —
with `RandomSystems/DistIndepMeasure.lean` carrying the transport half and
`RandomSystems/KWiseIndepPoly.lean` the CR18 §6.1.2 construction.

**The design move that unlocked it: a total `Dist.condProb`.**  `Dist.cond` is
`Part`-valued, and a `Part` cannot sit under a `∏` — a `Finset.prod` body cannot
depend on the membership proof discharging its domain.  That is exactly why the
existing `mass_biForall_lt_eq_prod` spells raw quotients and pays a positivity
hypothesis on every prefix.  `condProb X P Q = X(P∧Q)/X(Q)`, junk `0` on a null
event (matching mathlib's total `ProbabilityTheory.cond`), with
`condProb_eq_cond_get` identifying the two so no convention is forked.  At the
**`NonNeg`** layer `X(P∧Q) = 0` whenever `X(Q) = 0`, so the multiplication rule
and *both* chain rules hold with **no positivity side conditions** — strictly
stronger than what was there.

**A correction to §12.3's transcript-chain-rule row.**  MPR07 eq. (1),
`p_{Y^n|X^n} = ∏_j p_{Y_j|X^j Y^{j−1}}`, is **not unconditional** in a general
random experiment.  Dividing the transcript chain rule by the input chain rule
cancels the input factors only under a causality hypothesis — the *j*-th input
chosen without feedback from past outputs — otherwise the distinguisher's own
conditionals do not cancel.  `condProb_biForall_lt_eq_prod_condProb` therefore
carries `hfree`, and that is precisely the regime in which Maurer's
`p^S_{Y^i|X^i}` is a property of the system alone.  Listing it as a flat missing
identity was an oversimplification on my part.

**Verdict on `iIndepRV`, resolving the asymmetry `scratch/IndepProbe.lean` found
against mathlib's `iIndepFun`**: it is not a defect of the definition.  Under
`[Fintype ι]` plus a `ProbDist`, the tree's full-tuple `iIndepRV` is *equivalent*
to the subset-closed form at `k = |ι|` (`kIndepRV_card_iff_iIndepRV`); what was
missing was the marginalization theorem, now proved.  But `k`-wise independence
has no full-tuple statement to grade, so the `Finset`-indexed `iIndepRVOn` must be
primitive there.  `iIndepRV` stays as the mutual notion, `iIndepRVOn` is primitive
for the graded ones, and the bridge is proven both ways.

**A structural limit of the transport, worth recording against §12.8's optimism.**
Independence subset-closure was proved **natively, deliberately**: `Dist.toPMF`
requires `[Fintype Ω]`, and the tree's main carriers must *not* be `Fintype` — see
the comment on `Dist.mass_prod_and`, which drops `[Fintype Ω]` precisely so it
applies to the DDS/DDE carriers.  A foundational independence lemma carrying
`[Fintype Ω]` would be unusable there.  So the transport is the right tool for
ℝ-valued analytic facts (variance did go through it, using mathlib's
`IndepFun.variance_sum`) and the wrong tool for foundational lemmas on the main
carriers.

**CR18 §6.1.2 landed rather than cut**: polynomial evaluation over an arbitrary
finite field gives a `k`-wise independent family (`kIndepRV_polyEval`), with
`k ≤ |F|` as the source's implicit `k ≤ 2^m`.  Non-vacuity was checked
out-of-tree over `ZMod 2`.

### 12.21 Build green, and a gate that was not measuring what its name says

**All four gates verified at exit 0** (captured directly, not through a pipe):
`lake build RandomSystems`, `RandomSystems.HTechnique.All`,
`RandomSystems.HTechnique.LegacyChecks`, `RandomSystemsLegacyBridge`.  The
`NNReal → ℝ` carrier migration is complete across **27** modules.

**The structural finding, which matters more than the migration.**
`lake build RandomSystems` does *not* build everything.  `RandomSystems.lean`
imports only `HTechnique.Surface`, and `lean_lib RandomSystems` declares no globs,
so `HTechnique/{Density,TranscriptLaw,AdaptiveBridge,LegacyBoundedTranscript}`
and the entire `Legacy` subtree behind `LegacyChecks` are outside its closure.
**Nine of the thirteen files repaired in the final rounds were invisible to the
nominal gate** and would have stayed silently broken behind a green build.
`AGENTS.md` described this gate as "everything"; that line is corrected.

The aggregators themselves had no defect — they failed only on imports.

**The unmask chain went eight rounds.**  Each round's failing set was accurate
when measured; a build simply never attempts a module whose imports are red, so
depth is invisible until the layer above clears.  Rounds 1–3 cleared the
`RandomSystems` closure; rounds 4–8 were entirely modules the default gate does
not reach.  Worth remembering the next time a failing-target count looks like
progress: it is a lower bound, not a remaining-work estimate.

**Zero not-derivable cases across all 27 modules.**  Every hypothesis added was a
restoration the `ℝ≥0` carrier had supplied structurally, at the weakest layer
that works, and every one was derivable at its call sites.  The migration
surfaced no mathematical gaps — only typing chores, plus the three places where
truncated subtraction had been doing silent work (recorded in §12.19).

One module is worth flagging as dead rather than migrated: `HTechnique/Density.lean`
is a pure alias module with **zero consumers**, so the `NonNeg` hypotheses it
gained are vacuously derivable.  It is a candidate for deletion under §12 point 4
rather than maintenance.

## 13. Jost Prop. 2.2.3, second clause — the one-sided pass-through (2026-08-07)

Sketch: `sketches/jost-2-2-3-passthrough.md`.  Target: the clause the library
never formalized, and the reason parallel composability (Jost Thm 2.2.5 (2)) is
missing.

### 13.1 What the source says, and what our encoding makes of it

Prop. 2.2.3 (thesis printed p. 18) has **two** clauses.  Clause 1 —
`π_P^{γ_P} π_Q^{γ_Q} R = π_Q^{γ_Q} π_P^{γ_P} R` — is `Converter.attachAt_comm`.
Clause 2 — *if the interface sets of `R` and `S` are disjoint then
`π_P^{γ_P}[R,S] = [π_P^{γ_P}R, S]`* — was never stated here, and Jost proves
Thm 2.2.5 (2) directly from it (`π[R,T] = [πR,T] ⊆ [S,T]`).

Dictionary: our `i : I` is Jost's **party** and our service is that party's whole
interface-set alphabet, so `∥`'s tagged sum **is** Jost's union of disjoint
interface sets, and `R ∥ R` is his `[R,R']` with the tagging performing the
renaming his disjointness demands.  Jost's connection function `γ_P : I_in ↪ I_P`
becomes tag dispatch inside the converter; "γ_P lands in `R`" becomes "the
converter is the one-sided lift of a converter for `R`".  This settles the open
question of whether the positional sum-coding is Jost-faithful: it is, and
`SurfacePar.lean`'s hedge ("TypedParallel's own reading of AC's `∥`") is too
modest.

### 13.2 Three findings, in the order they were forced

**(a) There is no `Converter.par`.**  `PFunConverter.par α β`
(`EmulateRealization.lean:3048`) routes by `filterMap` on tags, so at a pair whose
recorded answers are all mis-tagged the left component sees an *empty* answer
list and queries again — forever.  Unbounded query streaks on its own trace tree,
hence not `AnswersWithin`, hence not CR18 Def. 3.8.  `StrictParallel.lean`'s
header records exactly this and says it is why that module built the
count-attributing fixed-component converters.  (Documented assessment, not a
theorem — there is no `not_isDDC_par` in the tree.)  The deliverable is therefore
the **count-attributed one-sided lift**, not a symmetric `Converter.par`; the
task's original title was unachievable as stated.

**(b) Count attribution forces silence.**  With positional attribution the open
round's segment may carry an answer from the wrong component, and there is no
total `Out s ⊕ Out u → Out t ⊕ Out u` (it would need `Out s → Out t`).  So the
converter must decline — which `ofRounds` cannot express, its `step` being total.
CR18 §3.4.3 permits silence and `ProtocolFn` carries it, so the constructor was
generalized rather than a junk element invented.

**(c) The §6.2 law cannot evaluate any Def-3.8 converter on a partial system.**
Found while building, not in the sketch.  `PFunConverter.par` feeds its component
the tag-*filtered* answer history, which drops a `⊥`; so it moves past one, which
`AnswersInY` forbids for every legal converter.  At a drive-reachable pair
carrying a `⊥` the lift (silent, as Def. 3.8 requires) and `par αFn idFn`
(moving) therefore disagree, and the drive congruence does not apply.  Way out:
a **totality** hypothesis on the components — true of every resource (Jost
Def. 2.2.1 is a sequence of conditional distributions) and this library's
standard hypothesis class (`KStepTotal`, `TotalOnNonempty`, `cr18_total`) — under
which `(par s t)⊥` never returns `none`.  The alternative is a direct realization
proof in the shape of `apply_parFixedRightFn` (~700 lines, no totality needed).

### 13.3 Landed (build green, 8405 jobs; axiom-clean; no `sorry`)

| where | content |
|---|---|
| `ProtocolFn.lean` | `mapM_length`, promoted out of `TypedAttachment`'s `private` section to the lowest module both users see |
| `StepRealization.lean` | `ofHistoryStepPartial` + `mem_/reach_/answersInY_/answersWithin_/isDDC_` and `ofHistoryStep_eq_ofHistoryStepPartial` — the silence-permitting Def-3.8 constructor.  Boundary condition weakens from an equivalence to *whenever it moves, it queries exactly while its budget lasts*; that is still both Def-3.8 clauses' worth (`AnswersWithin` needs the forward half, `AnswersInY` the backward half so a round never closes early and `roundOffset` stays aligned) |
| `ProtocolRealization.lean` | `sysAnswer`/`sysAnswers`, `DriveReach`, `drive_congr_of_driveReach`, `driveOuter_congr_of_driveReach`, `apply_congr_of_driveReach` — **application is a drive invariant**: protocols agreeing at every pair one application visits apply identically, `TraceEquiv` or not.  The trace tree quantifies over every answer; a single application only over the system's |
| `OneSidedConverter.lean` (new) | `leftOuter`, `inLeftCount`, `inLeftStep`, `inLeftFn`, `isDDC_inLeftFn` — the lift, and its Def-3.8 membership |

Name collision settled: `PFunConverter.drive_congr` / `driveOuter_congr` already
exist in `CompatibleMetric.lean` with the weaker outer-history-only hypothesis,
so the drive-reachability versions carry the `_of_driveReach` suffix.

### 13.4 Open, with sizes

`apply_inLeftFn` (tag faithfulness of `(par s t)⊥`, the drive invariant, the
alignment equation, assembly under totality) ≈ 450 lines; `inRightFn` ≈ 250; the
typed transport through `flatten_attach_eq_apply_framed` / `flatten_parallel`
≈ 300; the surface (`Converter.Rounds`, `inLeft`/`inRight`, Thm 2.2.5 (2) as a
`close` corollary, the `#cc_moves` pin, a `lift_par` rewrite) ≈ 250.

## 14. Closed-form converter application (2026-08-08)

`RandomSystems/ClosedApplication.lean`, 641 lines, axiom-clean, no `sorry`.

**The question.** Application in this library is fuel-indexed at every layer —
`drive` → `driveOuter` → `applyRawAt fuel` → `applyRaw = eventual …`, and the
same shape in `CausalApply` — so no theorem computes a general application and
every law about one is re-derived by a fuel induction.  The single closed form
was the *non-interactive* case, `PFunConverter.DDC.simple_apply`:
`(simple c d ·ᶜ S).1 us = (S.1 (us.map c)).map d`, i.e. `d ∘ S ∘ map c`.

**The result.** It generalizes.  For a converter authored by `ofHistoryStep` /
`ofHistoryStepPartial`, a round is *structural recursion on the budget* `cnt us`
and the outer level is a *fold* threading the inner history — no fuel, no
`eventual`, no fixed point.  Application is literally `cnt us`-many copies of
`S⊥` with the step maps interleaved:

    roundRun  : ℕ → List X → List Y → Option (List X × List Y)   -- one round
    roundOut  : the round's outer answer
    outerRun  : the fold over the outer history
    closedAnswer

    apply_ofHistoryStep_val :
      (PFunConverter.apply (ofHistoryStep step cnt) S).1 us
        = Part.ofOption (closedAnswer (fun us hne ys => some (step us hne ys)) cnt S us)

**Receipt, not assertion**: `simple_apply_of_closedAnswer` re-derives
`simple_apply`'s statement from the general theorem, routing
`simple → ofStep → ofHistoryStep → ofHistoryStepPartial` and evaluating the
closed form — its proof never mentions `simple_apply`.  So the general form
really does recover `d ∘ S ∘ map c`, which is the non-vacuity check.

### Three things that corrected the plan

1. **The right target is `ofHistoryStepPartial`, not `ofHistoryStep`.**  Silence
   and an `S⊥`-`⊥` are the *same* failure mode in the closed form — both are
   `none` in the same `Option` — so covering the silent-capable class costs
   nothing and the total one falls out through
   `ofHistoryStep_eq_ofHistoryStepPartial`.
2. **No totality hypothesis, and none was needed.**  `Part.ofOption` carries the
   partiality exactly, so the equation is unconditional and strictly more
   informative than a totality-gated one.  (Also settled: the library has *no*
   totality class on `PFunDDS.DDS` at all — `KStepTotal` and `TotalOnNonempty`
   live on the probabilistic carrier.)  This retires the totality hypothesis
   §13.2 (c) had planned for.
3. **No uniform bound on `cnt`.**  The needed fuel is per-history —
   `(us.inits.map cnt).sum + 1` — so the closed form applies to converters that
   `isDDC_ofHistoryStep` cannot even certify as DDCs, since Def 3.8 membership
   demands `∃ L, ∀ us, cnt us ≤ L`.  `applyRaw_dom` was checked and gives nothing
   usable here: it routes through `EmuRun` and produces a *membership* whose fuel
   never surfaces.

`hcnt` is the one load-bearing hypothesis, and in a sharper way than "the round
takes `cnt` steps": `ofHistoryStepPartial` locates the open round's segment by
the *arithmetic* offset `roundOffset cnt us`, computed from `cnt` alone and never
from the run.  `hcnt` is what makes the actual query count agree with `cnt us`,
hence what makes that offset point at the round's own answers — both directions
are used (no early `inr`, no over-spend `inl`).  Without it the fuel recursion is
**not** replaceable by structural recursion at all.

## 15. `⊗` at disjoint interface sets: Jost's clause 2, and merge is not invertible (2026-08-08)

`RandomSystems/TypedTensor.lean`, 2890 lines, axiom-clean, no `sorry`.  This is
the decision of §6a of `sketches/jost-2-2-3-passthrough.md` carried out.

### 15.1 Clause 2 holds, for an arbitrary unmodified converter

`attach_tensor_inl` at all four levels (`DependentDDS`, `DependentPDS`, `Prob`,
`DependentRandomSystem`): attaching a converter at `Sum.inl i` of `R ⊗ T` is
attaching it to `R`, with `T` untouched.  The converter is an arbitrary
`DeterministicConverter U source target` — **not modified, wrapped or lifted**.
Only the boundary is transported, and only because `Function.update` at
`Sum.inl i` on `I ⊕ J` and at `i` on `I` are propositionally rather than
definitionally equal, so the statement is heterogeneous exactly as
`ResourceAt.attach_comm` is.

So the whole `inLeft` apparatus of §13 — the count-attributed lift, the silence
constructor's *use*, the alignment arithmetic — is unnecessary in this model.
Also delivered: `edist_tensor_le` (eq. (3)) and `tensor_inj` (the cancellation
mirror of `parallel_inj`), plus a general interface `reindex` calculus.

### 15.2 The reason I gave for expecting it was wrong

I predicted clause 2 would fall out of `TypedFraming`'s `passStep` /
`passAnswerStep`.  It does not, and the file says so.  Those clauses state that
the all-interface frame forwards a query at a *non-selected* interface unchanged
**to the same resource**.  What clause 2 needs is different: that forwarding it
to `R ⊗ T` is the same as letting `T` answer it alone, and that the converter's
own inner queries never reach `T`.  That is a **routing** property of the
composition, not a property of the frame, and it is proved where the routing
lives (`PFunConverter.General.attachAt_routedPar_left`, uniform chart).

Two supporting facts worth keeping: `PFunDDS.fullyDefined` is invoked only for
the converter's own inner queries (all tagged `Sum.inl i`), so there is exactly
one `⊥`-level transparency lemma and no right-query mirror; and `routedPar`'s two
domain guards are consumed *asymmetrically* — a left-tagged last entry consumes
the right guard, a right-tagged last entry consumes the left — so dropping either
breaks one of the two membership inclusions.

### 15.3 Merge is an isometric embedding, NOT a relabelling — proved

The load-bearing claim of §6a was that merging a block of interfaces into one is
a pure re-indexing, hence invertible.  **It is false**, and the falsification is
a theorem, not an assessment:

* `not_tagCompatible_mergeBlock_symm` — the inverse pair is never tag-compatible
  once the block has two distinct interfaces that can carry a query and an
  answer.  The obstruction is explicit: tag faithfulness demands the answer carry
  the *query's* block interface, but a merged answer decodes through `outputCode`
  to whatever interface *it* names.
* `tagCompatible_not_symmetric` — so `reindex` is not invertible in general; the
  merge exhibits both halves at once (forward compatible, inverse not).
* `not_surjective_mergeBlock` — the merge map on resources is therefore not
  surjective.  Its image is exactly the merged-boundary resources whose decoded
  answer sits at the same block interface as the decoded query, and the merged
  boundary imposes no such constraint.

What survives, and is what n-ary attachment actually needs: merge is **injective**
(`mergeBlock_injective`) and an **isometry** (`edist_mergeBlock`), at every level
up to the contextual quotient.  Both are forward-only facts, and `n-ary attach =
merge ; attach` uses only the forward direction, so the construction stands.

**Structural consequence.**  The merged-service model is a proper *sub*-model of
the disjoint one, isometrically embedded — the two encodings are not equivalent,
and the merged one is strictly smaller.  That is a fact about the two designs,
not a bookkeeping detail.

### 15.4 One prediction that did hold

`HasSumCode` / `Services.free` / `SumService` survive and change role: the binary
corollary (`twoBlockInputCode` / `twoBlockOutputCode`) shows the alphabet coding
`HasSumCode` supplies **is** a block coding of the two-interface block.  It stops
being the coding for parallel composition and becomes the coding for *merge*.
