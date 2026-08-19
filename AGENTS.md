# Agent notes

All design rationale, modeling discipline (CR18 PFun rules, statement/proof
policies, automation stack) lives in **`DESIGN.md`**; current state, build
gates, quarantine map, and open work live in **`STATUS.md`**.  Read both
before modeling or proving anything.

All pen-and-paper mathematics shall follow
[FOUNDATIONS.md](FOUNDATIONS.md). Read it before drafting or revising a
research note. Use its notation, object order, theorem style, status labels,
and required section structure. In particular, keep the
Maurer--Lanzenberger positive theory separate from the repository's signed
extension, and do not call a signed joint a coupling without qualification.

**Development loop — do not iterate with `lake build`.**  Use the `lean-lsp`
MCP (`.mcp.json`) to read the *goal state* at a position; if it is unavailable,
run `lake env lean <file>` on the single file, which reuses existing oleans.  A
full build is thousands of jobs and only prints an error string, while most
friction in this codebase is implicit-argument or instance misdirection that
cannot be diagnosed without the goal.  Probe a doubtful lemma in a scratch file
with `lake env lean` before editing the real one.  Reserve `lake build` for
stale oleans and for the gates below.

Quick gates: `lake build RandomSystems` — **not** everything, despite the name.
`RandomSystems.lean` imports only `HTechnique.Surface`, and `lean_lib
RandomSystems` declares no globs, so `HTechnique.{Density,TranscriptLaw,
AdaptiveBridge,LegacyBoundedTranscript}` and the whole `Legacy` subtree are
invisible to it.  In the 2026-08-07 carrier migration nine of thirteen broken
files were reachable only through the two aggregators below, and a green
`lake build RandomSystems` said nothing about them.  Run all three;
`lake build RandomSystems.HTechnique.All` + `lake run htechniqueSurfaceAudit`
(curated surface); `lake build RandomSystems.HTechnique.LegacyChecks`
(legacy gates + anti-drift pins — a pin failure means a refactor changed the
mathematics); `lake run ccSurfaceAudit` (RS→AC bridge: admissions, endpoint
statement surface, performance escapes — syntactic, no build) and
`lake run ccCheck` (adds the focused bridge builds and the per-endpoint
`#print axioms` audit).

**When a proof fights back, question the difficulty.**  Most of it here is
self-inflicted by an earlier attempt — a hand-rolled definition where
infrastructure already exists, or a statement in the wrong shape — not hard
mathematics.  After the second failed fix, stop patching: grep for existing
infrastructure and consider restating the lemma.  `DESIGN.md` §4 records the
traps that have actually cost time.
