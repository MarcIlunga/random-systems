# SequenceHash formalization — plan, operating model, task board

> **Version scope.** This task board records the v0.1.0 draft development and
> is retained as its historical plan. C2SP released the materially revised
> stable v1.0.0 specification on 2026-08-03. See
> [`specs/README.md`](specs/README.md) for both immutable snapshots and their
> semantic differences. New v1.0.0 research is tracked separately and must not
> reinterpret the completed v0.1.0 milestones.

Living planning document for the SequenceHash security proofs. It holds the
pen-and-paper mathematics **before** any Lean, the manager/worker operating
model, and the exact task board.

Spec pinned in [`sequencehash.md`](sequencehash.md); adapted papers in this
directory (see the ladder in §2).

---

## Supervisor goal (my charter)

**Mission.** As supervisor/manager, drive the machine-checked Lean 4
formalization of C2SP SequenceHash's security (ladder R1–R6, §2) to completion by
**copying and adapting existing proofs**, with **Codex sol** as the worker. I do
**not** do the mathematics — I own the statements/guardrails, dispatch, review,
and integration; Codex writes the sketches, definitions, and proofs.

**Definition of done (per result Rn).** A named theorem faithful to its source
paper, `sorry`/`admit`-free, axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`), building green, stated on the RandomSystems PDS surface.

**Non-negotiables I enforce on every dispatch and review:**
1. **PDS, pure CR18 idiom — not games, not H-technique.** Systems are `PFunPDS`
   built as converter-on-resource (`applyDDC (ofStep …) 𝖱`, like `cbcReal`);
   security is the pure distinguishing advantage `Δ(⌈q⌉ real, ⌈q⌉ URF)`
   (`maxAdvantage` + `filterQueries`), mirroring `cbc_mac_randomness_expander`;
   reductions are `Δ` inequalities via the framework lemmas (triangle,
   telescoping, DPI/converter monotonicity, switching). **`advPRF`/`advNPRF`/`Adv`
   are H-technique tools — DO NOT use them for the Gaži (R2) proof.** No
   game/experiment/adversary/oracle objects; `ε_KS`/`ω_S` are `Δ` between PDS
   systems, not game probabilities.
2. **Copy-and-adapt — no guesswork on the model.** Model exactly as the source
   paper defines (read the PDF); never invent a resource/key/proof model. Fidelity
   to the named source; no invented proofs, no bespoke tightening before R6. If a
   paper's structure genuinely can't be rendered faithfully in the pure idiom,
   switch to a cleaner source (e.g. the 2025 paper for the PRF) rather than guess.
3. **Goal-first.** The frozen `-- GUARDRAIL` is always the *goal theorem*, never
   a helper; helpers are discovered by the proof.
4. **Never reprove, and NO `private` declarations — ever.** Reuse existing
   theorems; generalize non-scheme facts in place; no specialized copies, no
   hand-rolled bookkeeping a tactic handles. **`private` is banned** (it blocks
   reuse and forces re-derivation): write everything public; if a needed lemma is
   `private` — even in core `CBCMAC.lean`/framework — make it public (or
   generalize it into a public lemma the original also uses) and REUSE it. Never
   re-derive around a `private` wall.
5. **Persist everything in-repo** (`sketches/`, `dispatch/`, `WORKLOG.md`).
6. **Correct fast.** On owner feedback: kill the run, recard, redispatch.

**My loop.** anchor (place the goal guardrail) → dispatch (`codex exec --yolo`)
→ review (§0.3 gates) → ACCEPT / REDISPATCH / ESCALATE → integrate → journal.

---

## 0. Operating model

**Claude = manager. Codex sol = worker.** Claude does **not** do the
mathematical work — neither the pen-and-paper sketches nor the proofs. Claude
owns only: the Lean statement scaffolding/guardrails (when needed), acceptance
criteria, dispatch, review, and integration. Codex sol produces the pen-and-paper
sketches, the object definitions, and the proofs.

### 0.1 Division of labor

| Manager (Claude) | Worker (Codex sol) |
|---|---|
| Lean **statement scaffolding/guardrails** (`sorry`, may not compile) — only when needed | **Pen-and-paper sketches (§4)**: statement, proof skeleton, infra-map, reuse-vs-new |
| Acceptance criteria per task | Object definitions + proofs; helpers only to close a stated goal |
| Dispatch, review, redispatch, integrate | Make the build green + axiom-clean; report what it did |

The guardrail is load-bearing: **Codex may not change a guardrail statement**,
only prove it. Statement drift is an automatic rejection (see §0.3). This is how
the statement-first discipline is enforced across an agent that would otherwise
drift into helpers-first.

### 0.2 Dispatch mechanics

Worker = `gpt-5.6-sol` at high reasoning. The project is a trusted Codex
workspace; lean-lsp is available to the worker. One task = one `codex exec`,
run **`--yolo`** (all permissions, no sandbox, no approval prompts — required
for an autonomous worker that builds Lean and reaches the cached deps):

```bash
codex exec \
  -C /Users/marcilunga/Documents/tob/research/random-systems \
  -m gpt-5.6-sol \
  -c model_reasoning_effort="high" \
  --yolo \
  -o dispatch/<task-id>-output.md \
  "$(cat dispatch/<task-id>-card.txt)"
```

- Every task-card prompt begins with the **standing preamble (§0.5)**, then the
  card body (§0.4): guardrail file(s), exact target theorem(s), source section,
  acceptance bar, and the hard rule *"do not alter any `-- GUARDRAIL` statement;
  fill only the `sorry`s."*
- **Anchor-first**: manager creates the target file with scaffolding statements
  on disk **before** dispatch — even rough / not-yet-compiling — so the worker
  has a concrete target to fill rather than a blank slate. (E.g. `MDHash.lean`
  was placed with the MD objects + `mdIterate_append` guardrail before the S2
  sketch even returns.)
- **Persist everything in the repo, never only the scratchpad.** The card lives
  at `dispatch/<task-id>-card.txt`, the captured output at
  `dispatch/<task-id>-output.md` (a full sketch also copied to
  `sketches/<name>.md`), and every dispatch + review verdict is journaled in
  [`WORKLOG.md`](WORKLOG.md).
- `-o` captures Codex's final message; run long tasks in the background and
  review on completion.
- `--yolo` gives full access, so no dep pre-warming is needed.

### 0.5 Standing preamble — prepended verbatim to EVERY task card

**Enforced mechanically.** The canonical machine copy is
[`dispatch/PREAMBLE.txt`](dispatch/PREAMBLE.txt); ALL dispatches go through
[`dispatch/codex-dispatch.sh`](dispatch/codex-dispatch.sh) `<card> <out>` (NEVER
`codex exec` directly), which prepends it and FAILS LOUDLY if the strict
sketch-adaptation discipline (§3c) is missing — so the strictness cannot be forgotten,
even after context compaction. Keep this section and `PREAMBLE.txt` in sync.

This is the first thing Codex must act on, before writing a single proof. It is
non-negotiable and repeated on every dispatch (Codex has no memory across runs):

> **STEP 0 — before proving anything.**
> 1. **Know the framework.** RandomSystems is an *algebraic* random-systems
>    framework that **instantiates `AbstractCrypto`** (`../abstract-crypto`, a
>    lakefile dependency). It already has the high-level theorems — resource
>    algebra, distinguishing advantage, the H-technique layer, converters, DPI.
>    Read the relevant surface before you build; do not re-derive framework-level
>    facts inside this scheme. **PDS, pure CR18 idiom — not games, not
>    H-technique:** systems are `PFunPDS` (converter-on-resource, like `cbcReal`);
>    security is `Δ(⌈q⌉ real, ⌈q⌉ URF)` (`maxAdvantage` + `filterQueries`),
>    mirroring `cbc_mac_randomness_expander`. **`advPRF`/`advNPRF`/`Adv` are
>    H-technique — DO NOT use them (Gaži/R2).** Never introduce
>    game/adversary/oracle objects; `ε_KS`/`ω_S` are `Δ` between PDS systems.
> 2. **Never reprove; NO `private` — ever; START FROM `SequenceFunction`.** Before
>    proving any lemma, **consult [`CHEATSHEET.md`](../CHEATSHEET.md) at the repo
>    root FIRST** — it catalogs the reusable theorems/constructions/tactics/
>    notations (advantage `Δ`/`⌈q⌉`, converters/DPI, switching/birthday, the
>    condEquiv blind game, `Dist` facts, `cr18_*` tactics, indiff). If what you
>    need is there, **reuse it by name**. Then also `grep` the
>    RandomSystems/AbstractCrypto trees, `lean_local_search`, `loogle`,
>    `leansearch`, `#check`. If it exists, **reuse it**. If the fact you need is not SequenceHash-specific, do **not**
>    prove a specialized copy — **generalize it in place**. **Do NOT write
>    `private`**; make a needed `private` lemma public (or generalize it public)
>    and reuse it — never re-derive around it. **NEW modeling of the C2SP
>    construction MUST build on the canonical general `SequenceFunction(H,K,S,F;M)`
>    (params `K`,`F`) — never re-spell the inner/outer inputs or the converter
>    step. SequenceHash = `SequenceFunction(∅,F=2)`, SequenceMAC =
>    `SequenceFunction(K,F=1)` are instances.** (Consolidating the already-proven
>    R1/R2 files onto it is the deferred end-of-project migration; new work starts
>    from it directly.)
> 3. **Automation first — MATCH CBC's density, not the old Gaži engine's.** Prefer
>    `grind` and the `cr18_*` family (CBC uses `grind` ~10×, `cr18_*` ~6×; the old
>    Gaži engine used 0/1 and paid with 107 `simp` + 148 `have` — that debt is
>    deferred cleanup, do NOT add to it). Use the repo's custom tactics (`cr18_*`,
>    `htechnique_*`, mass/`grind` bundles, `char2`) + `bound`/`gcongr`/`omega`. Do
>    NOT hand-write `simp`/`have`/`calc` chains for bookkeeping a tactic handles.
>    Every NEW proof must read tidy/pen-and-paper.
> 3b. **Reuse generic facts — do NOT bury them in the proof.** Any scheme-agnostic
>    fact (adjacent-sum, uniform-restriction along an embedding, `Dist` prod-map,
>    statDist manipulations) lives in `Dist`/`Distinguishing`/`AdvantageSeq` and
>    usually ALREADY EXISTS — grep/`loogle`/`lean_local_search` the framework FIRST
>    and reuse (e.g. `maxAdvantage_le_adjacent_sum`). Never mint a local `gazi_*`
>    generic helper; if a general fact is genuinely missing, add it PUBLIC to the
>    framework, not to the scheme file.
> 3c. **SKETCH TASKS — REALLY ADAPT, NEVER TRANSCRIBE.** For a sketch of a source
>    paper (Gaži / Shen / DRST / Backendal), the paper is a **template, not the
>    answer**. NO blunt copy-paste of its bound or bad-event list. For **every**
>    bound term and bad event, state in a TABLE whether a KNOWN SequenceHash
>    specificity **kills / shrinks / leaves** it, and why. Known simplifiers (reuse,
>    do not re-derive): **FIELD** domain separation (R1 `encodeItems_injective` /
>    `sequenceHash_collision_of_distinct_inputs` ⇒ no ambiguity/prefix-free events);
>    **INNER/OUTER** domain separation (R2/A2 `HeaderI ≠ HeaderO` ⇒ NMAC-like
>    independent effective keys, **NOT HMAC-like** ⇒ related-ipad/opad terms don't
>    apply); **CROSS-ROLE** domain separation (`Derive(K)`/`Derive(S)`/inner/outer/key
>    inputs pairwise disjoint ⇒ cross-role bad events drop, bad-event partition
>    collapses); the extra `Derive` long-key/customization cost is a small
>    **accountable** term (name it). Deliver a SequenceHash-**specific** bound, and be
>    HONEST that dominant **cascade-inherent** terms (functional-graph, internal
>    collision) likely REMAIN — separation kills bookkeeping/aliasing, not the
>    cascade's inherent loss. Start from `SequenceFunction`.
> 4. Only after 1–3: fill the `sorry`s under the frozen `-- GUARDRAIL`
>    statements. Report which existing theorems you reused and anything you
>    generalized.

### 0.3 Review protocol (manager, on every return)

1. `lake build <task target>` — must be green.
2. Axiom check the target theorem(s) (`lean_verify` / `#print axioms`): only
   `propext`, `Classical.choice`, `Quot.sound` allowed. No new `axiom`.
3. `grep -rn 'sorry\|admit'` over the touched files — must be empty (unless the
   task explicitly leaves a downstream `sorry`).
4. **Statement-drift check**: diff the `-- GUARDRAIL` lines against what the
   manager placed. Any change to a statement = reject.
5. No-fluff / **reuse / automation** check (repo rule + §0.5 items 2,3,3b): no new
   docs; no helper that duplicates an existing RandomSystems/AbstractCrypto
   theorem; no scheme-specialized copy of a general fact (should have been
   generalized in place); **no local `gazi_*`-style generic helper** (adjacent-sum,
   uniform-restriction, prod-map — must be framework-hoisted/reused); **no
   hand-written `simp`/`have`/`calc` sprawl** where `grind`/`cr18_*` applies.
   **REDISPATCH if the proof re-derives or re-spells anything catalogued in
   `CHEATSHEET.md`** (the reuse index — check the new proof's helpers against it).
   REDISPATCH if a NEW proof re-accretes the old engine's manual/duplicate debt.
6. **Verdict**: `ACCEPT` → mark done, next task · `REDISPATCH` → same card +
   specific defect (drift / residual sorry / axiom leak / reproved-existing /
   should-generalize / fluff) · `ESCALATE` → the guardrail statement itself was
   wrong; manager revises §4 + the stub, then re-cards.

### 0.4 Task-card template

```
[§0.5 STANDING PREAMBLE prepended here verbatim — know the framework, never
 reprove/generalize-in-place, automation first — THEN:]
TASK T<id> — <title>
Result R<n>. Depends: <ids|—>.
GOAL: <one sentence>.
SOURCE: <paper> §<x> — copy and adapt; do not invent a new proof.
GUARDRAIL FILE(S): <path(s)> — statements marked `-- GUARDRAIL` are FROZEN;
  fill only the `sorry`s, add helpers as needed, reuse RandomSystems infra.
DELIVERABLE: <what to prove>.
ACCEPTANCE: `lake build <target>` green; target axiom-clean
  {propext, Classical.choice, Quot.sound}; no residual sorry/admit; guardrail
  statements byte-identical; no new docs.
```

---

## 1. The construction (C2SP SequenceHash v0.1.0)

`SequenceHash(H, S; M)` for `H : List Byte → HashOutput L`, block size `b`,
customization `S`, item sequence `M = (M₁,…,Mₙ)`:

```
inner   = H( headerI(b, F=2, ∅) ‖ pad(∅, b) ‖ encodeItems(M) )
derive  = if |S| ≤ b then pad(S, b) else pad(H(S), b)
outer   = H( headerO(b, F=2, S, ∅) ‖ derive ‖ pad(∅, b)
             ‖ MSBF(|M|) ‖ MSBF(L) ‖ inner )
output  = outer
```

- `headerI = pad("SEQHSH_I" ‖ MSBF(F) ‖ MSBF(|K|), b)`, `K = ∅`.
- `headerO = pad("SEQHSH_O" ‖ MSBF(F) ‖ MSBF(|S|) ‖ MSBF(|K|), b)`, `K = ∅`.
- `MSBF` = 16-byte big-endian length encoding (injective, fixed width).
- `encodeItems(M) = ‖ᵢ (MSBF(|Mᵢ|) ‖ Mᵢ)` — unambiguous item framing.

Domain-separated double hash: distinct indicators keep inner/outer in separate
domains; inner commits the sequence; outer binds `S`, count `n`, length `L`.
**SequenceMAC** = keyed sister (`K ≠ ∅`, `|K| ≥ 32`); the key rides in headers.

---

## 2. Result ladder

Every result copies one existing proof; order is dependency order.

| # | Result | Copy & adapt from | State |
|---|---|---|---|
| **R1** | Encoding non-ambiguity — distinct inputs ⇒ real `H`-collision | C2SP spec (deterministic) | **✅ proven** |
| **R2** | SequenceMAC PRF, MD-style `H`, keyed compression | Gaži–Pietrzak–Rybár 2014 (`2014-578`) | **✅ done** (axiom-clean) |
| **R3** | SequenceMAC PRF assuming `H` indiff. from RO | modular composition (R5 notion as hypothesis) | **✅ done 2026-07-15** — `sequenceMAC_prf_bound_indiff`, cond. on `h_indiff` (role-separated ideal); axiom-clean, pure PDS |
| **R4** | Tight *generic* PRF (H-technique) | Shen–Zhang–Wang–Gu 2025 (`2025-2260`) | 🔄 sketch done (`B_SEQ`, adapted); **structural in-flight** (facade + named bad-mass) |
| **R5** | Indifferentiability from a RO (HMAC approach) | Dodis et al. 2013 (`2013-382`) | 🔶 **structural done 2026-07-15** — `sequenceMAC_md_prf_bound_indiff` wires R1→R5 (axiom-clean) conditional on the named DRST bound `h_drst`; **P5.deep** = formalize the simulator to prove `h_drst` |
| **R6** | Close Gaži's tightness loss | Backendal et al. 2023 (`2023-861`) | 🔶 **strong-MU cascade proven 2026-07-15** — `nmac_prf_bound_strong_mu` removes the row hybrid and proves the exact `(ℓ+2)·epsCompMU + pairCollisionUnionBound` core; `sequenceFunction_prf_bound_strong_mu` is now conditional only on `hSchedule` (C2SP safe-schedule normalization) |

**Decisions (settled):** PRF subject = SequenceMAC over Merkle–Damgård `H=MD[f]`
with `f` keyed as the PRF/URF (⇒ R2 pulls an MD model into scope; `FixedHash` is
opaque today). R5 copies the DRST HMAC simulator. Bound fidelity = whatever the
adapted approach yields; no bespoke tightening before R6.

---

## 3. Phases

Per-result flow:

- **S — sketch** (Codex → `sketches/<name>.md`): pen-and-paper from the source
  paper — statement, proof skeleton mapped to the paper's sections, infra-map
  onto RandomSystems/AbstractCrypto, "reuse vs. new". Codex writes the **full**
  sketch to `sketches/<name>.md`; the manager reviews it and folds a **condensed**
  version into §4. Math uses `$$…$$` / `$…$` (GitHub-renderable), never
  `\[…\]` / `\(…\)`.
- **G — guardrail** (manager, *if needed*): freeze the Lean statement(s) +
  minimal object scaffolding from the accepted sketch, marked `-- GUARDRAIL`.
  May not compile.
- **P — proof/defs** (Codex): fill object definitions + discharge sorries
  top-down.
- **R — review** (manager, §0.3).
- **D — R6** (tightness).

Each `S*` is a Codex sketch; each `T*` is a manager guardrail (G) then a Codex
proof (P) on the same file.

---

## 4. Phase A sketches

Sketches are **Codex deliverables** (dispatched as `S*` tasks). The **full**
sketch is saved in [`sketches/`](sketches/); the manager folds a **condensed**
version into this section. A1 below is retrospective (R1 was already proven);
A2–A5 are produced by Codex.

### A1 — Encoding non-ambiguity (R1) — DONE (retrospective)

**Statement** (`sequenceHash_collision_of_distinct_inputs`). For `(S,M)≠(T,N)`,
equal `sequenceHash` outputs give one of: (i) outer `HashCollision`, (ii) inner
`HashCollision`, (iii) `b<|S| ∧ b<|T| ∧ HashCollision H S T` (both long ⇒ the two
`derive` calls collide).

**Skeleton (proven).** Case on outer-input equality. Unequal + equal output ⇒
(i). Equal: peel outer framing (`MSBF` fixed-width injective ⇒ `|M|=|N|`, `L`,
`derive`, `inner` equal); equal inner ⇒ `encodeItems_injective` forces `M=N` then
`S=T` (contradiction) or inner collision (ii); equal `derive` both-long ⇒ (iii),
short side ⇒ `pad` recovers `S=T`. Distinct `headerI`/`headerO` indicators give
the domain separation.

**RO reading.** Deterministic backbone: the map `(S,M) ↦` bytes fed to `H` is
injective modulo the call graph, so the encoding adds no collisions; under `H=RO`
branches (i)–(iii) are exactly RO-collision events. This is R5's collision half
and why R4 reduces cleanly to `H`.

**Proven:** `encodeItems_injective`, `encodeMSBF_injective`, the collision
theorem. **New only on demand:** a packaged effective-input injectivity lemma —
written only when R5's statement needs it (rule 3). R1 is closed.

### A2 — SequenceMAC PRF (R2) — sketch ACCEPTED (Codex S2, Gaži 2014)

Full sketch: [`sketches/A2-sequencemac-prf.md`](sketches/A2-sequencemac-prf.md).

**Key structural insight (corrected, S2r).** SequenceMAC is single-key, but its
key derivation is **better than HMAC**: a single `K' = Derive(K)` is processed
from two **distinct domain-separated run-ups** (`HeaderI` vs `HeaderO`,
guaranteed different by the leading 8 bytes; spec line 218/237), so the inner key
`k_I` and outer key `k_O` are the compression cascade at *distinct* inputs →
**independently keyed under ordinary (data-input) PRF security of `f`** — no
related-key assumption. (HMAC's `K⊕ipad`/`K⊕opad` are *related* keys and need
RKA; SequenceMAC deliberately avoids that.) So Hop 1 is a clean
domain-separation/independence hop and `ε_KS` is the ordinary-PRF cost of the
key-derivation run-up, **not** an HMAC→NMAC RKA loss.

**R2 is NOT an H-technique proof.** Gaži 2014 is classical game-hop/hybrid
reductions (Appendix A Lemmas 5–6, birthday bounds), not Maurer's H-coefficient
method. R2 uses the plain distinguishing-advantage/reduction infra; the
H-technique endpoints are reserved for R4 (Shen et al. 2025).

**Objects.** MD: `f : C → B → C` (chaining input = key, Gaži §2.2),
`Casc f k = List.foldl f k`, `MD[f] x = Casc f IV (blockify x)`; built directly
on `mdIterate` (= `List.foldl`), block-append law = `List.foldl_append`. (The
legacy Boneh–Shoup cascade is not relevant here.)
SequenceMAC reuses Spec's `pad`/`derive`/`headerI`/`headerO` + Encoding's
`encodeItems`, `F = 1`, fixed key length κ≥32 sampled uniformly. Systems as
`PFunPDS.Prob.functionEvaluator`; advantages via `advPRF`/`advNPRF`. `N = |C|`.

**Final theorem** (frozen in `SequenceMACPRF.lean`):

    advPRF_q(SequenceMAC_{f,S}) ≤ ε_KS + ε_ad + (ℓ+1)·q·ε_na + q²/N + δ_S

with `ε_ad = advPRF(Comp_f)`, `ε_na = advNPRF(Comp_f)`, `δ_S = 0` if `|S| ≤ b`
else `ω_S(q)`. The middle three terms are Gaži Thm 1 §3.1 (`bday` weakened to
`q²/N` to match the paper). **`ω_S(q)` has no unconditional bound** — a long `S`
can force derivation overlap; it needs a syntactic restriction on `S` or a
separate assumption.

**Proof skeleton (8 hops, each mapped to Gaži).** 0 realize the concrete call
schedule (adapt `sequenceHashSystem_realization`; split MD folds by
`List.foldl_append`) · 1 single-key→independent framed-NMAC via the
distinct-run-up domain separation (independent `k_I,k_O` under ordinary
compression PRF; **no RKA** — better than HMAC), loss `ε_KS` · 2 outer
compression PRF→random function, loss `ε_ad` (§3.1 T₁) · 3 random outer = URF
until inner collision `Bad` (§3.1 cond. C; classical hybrid/collision argument,
**not** the H-technique reveal-key representative) · 4 adaptive `Bad` →
nonadaptive cascade collision (§3.1 `A_na`, classical hybrid) · 5 make frozen
queries prefix-free via a fresh block · 6 collision-tester distinguisher,
`+ q²/N` URF-collision · 7 Gaži Prop. 1 (Appendix A, Lemmas 5–6): NA-PF cascade
adv `≤ (ℓ+1)·q·ε_na`.

**Reuse vs. new (classical infra — NOT H-technique).** Reuse (existence
verified): `advantage_telescope`, `maxAdvantage_le_adjacent_sum`,
`statDist_triangle`, `advPRF`/`advNPRF`, `bday`/`bday_mono`,
`IsCostedReduction(.comp)`, `PrefixFree`, `List.foldl_append`,
`encodeItems_injective`/`encodeMSBF_injective`. NEW (generic where possible):
public MD model; `cascade_na_pf_adv_le` (Gaži Prop. 1, generic over `B,C,f`);
`prefixFree_append_fresh` + fresh-block-exists; the SequenceMAC→framed-NMAC
domain-separation bridge (`ε_KS`, ordinary-PRF, construction-specific);
`outerTag` framing + long-case `OverlapS`. Do **not** reuse the H-technique
endpoints (`adv_le_of_extFixedQueryRep_eq_on_good`, the reveal-key
representative) — those are R4. AbstractCrypto indifferentiability is R3/R5, not
R2. Full sketch: `sketches/A2-sequencemac-prf.md`.

### A3 — PRF assuming `H` indiff. from RO (R3) — TODO

Composition: `H≈RO` ⇒ SequenceMAC[`H`] PRF, via the indiff. composition theorem
(R5's predicate as hypothesis).

### A4 — Tight generic PRF via H-technique (R4) — TODO

Adapt Shen 2025; map their lemmas onto `RandomSystems.HTechnique`; decide what of
`RectHashThenPRF.lean` survives as a real sub-goal.

### A5 — Indifferentiability from a RO (R5) — TODO

Adapt the DRST HMAC simulator on the direct PDS/`Δ` surface for canonical
`sequenceFunction` over `MD[f]`, discharging `sequenceMAC_md_h_indiff`'s `h_drst`
premise; reuse A1's collision backbone. Selected `AbstractCrypto.Indifferentiable`
packaging is a later conditional corollary after a faithful carrier/action seam.

---

## 5. Task board

Legend: ☐ not dispatched · ▶ dispatched · ✔ accepted · ↻ redispatch. R1/R2 are
carded exactly; R3–R6 are staged and decomposed when their A-sketch lands.

### R1 — encoding

| Task | Owner step | Status | Notes |
|---|---|---|---|
| T1.1 verify & seal | manager review only | ☐ | axiom-check `sequenceHash_collision_of_distinct_inputs` + `encodeItems_injective`; confirm no Codex work |
| T1.2 sound-encoding corollary | guardrail (mgr) → proof (Codex) | ✔ | **pipeline smoke test — PASSED.** `SoundEncoding.lean`: `sequenceHash_pair_injective` (collision-free `H` ⇒ SequenceHash injective on `(S,M)`). Codex closed it by reusing `sequenceHash_collision_of_distinct_inputs`; build green, axioms {propext, Classical.choice, Quot.sound}, no drift, Spec untouched |

### R2 — SequenceMAC PRF (Gaži)

> **IDIOM CORRECTION (2026-07-14):** R2 is stated in the **CBCMAC idiom** —
> `PFunPDS` converter-on-resource systems + `Δ(⌈q⌉ real, ⌈q⌉ URF)` (pure
> `maxAdvantage`/`filterQueries`), mirroring `cbc_mac_randomness_expander`. The
> earlier `ProbPDS`/`advPRF` goal + systems (`G2`/`P2.obj`/`P2.sys` rows below)
> are **superseded** by `P2.reshape` (✔ done — goal re-frozen in CBCMAC idiom,
> green, no `advPRF`/`advNPRF`/`Adv`). Systems now: `compReal`=`ofFunDist`,
> `compIdeal`/`macIdeal`=`PFunPDS.URF`, `sequenceMACReal`=`applyDDC (ofStep
> macStep) compReal`, `ε_KS`=filtered `Δ`. Remaining `sorry`: `macStep` (Hop 0
> realize), `omegaS`, proof. `P2.new` was killed (built on `advNPRF`); it returns
> as a pure-`Δ` cascade bound.

| Task | Guardrail the manager places | Codex deliverable | Status |
|---|---|---|---|
| S2 sketch (A2) | — | pen-and-paper → §4 A2 | ✔ **accepted (S2r revision)**: key-derivation better than HMAC (no RKA) + H-technique dropped (Gaži classical; that's R4) |
| G2 goal | ✅ `SequenceMACPRF.lean` — `sequenceMAC_prf_bound` `-- GUARDRAIL` (compiles; systems/terms are stubs) | — (statement only) | ✔ **frozen** |
| P2.obj objects (pt 1) | frozen goal | MD model (direct on `mdIterate`/`List.foldl_append`; no Boneh–Shoup) + real `compSystem` | ✔ **accepted**: `MDCodec`+`mdHash`+`mdIterate_append`(via `foldl_append`), `compSystem` real (`functionEvaluator`→`ProbPDS`); green, axiom-clean, goal frozen |
| P2.sys objects (pt 2) | frozen goal (refined: output `C`, +`κ`/`hκ`, +`codec`/`iv`, +`digestBytes`/`hκU128`) | ✔ **accepted**: `sequenceMACSystem`/`framedNMACSystem` real (`functionEvaluator`, reuse Spec/MDHash), `epsKS` = `Adv` between them; green, axiom-clean, PDS. `omegaS`→P2.long |
| P2.new generic | — | `cascade_na_pf_adv_le` (Gaži Prop. 1), public & generic in `CascadeNAPF.lean`; two-hybrid proof (App. A Lemmas 5–6) | ▶ **running** |
| P2.bridge `ε_KS` | — | `sequenceMAC_to_framedNMAC` (single→two-key; data-input/RKA assumptions) | ☐ |
| P2.hops assemble | — | hops 0,2–7 by reuse + *generalizing* RectHashThenPRF's reveal pattern → prove the short-case bound | ☐ |
| P2.long `ω_S` | — | `OverlapS` + `longDerive_eq_shortIdeal_on_noOverlap`; long-case term (needs an `S` restriction) | ☐ |
| T2.2 statement | `RandomSystems/SequenceMACPRF.lean`: SequenceMAC over MD + `theorem sequenceMAC_prf_bound … := by sorry` (`-- GUARDRAIL`) | — (statement only; manager) | ☐ |
| T2.3 short case | sorried game-hop lemmas in T2.2 file | prove short-customization reduction | ☐ |
| T2.4 long case | sorried overlap-term lemma | prove `derive=H(S)` overlap accounting | ☐ |
| T2.5 assemble | — | combine T2.3+T2.4 into `sequenceMAC_prf_bound` | ☐ |

### R3 — PRF given `H≈RO`  ·  R4 — tight H-technique  ·  R5 — indiff (DRST)  ·  R6 — tightness (Backendal)

Staged. Each opens with its A-sketch (manager), then a T-task list mirroring
R2's shape (objects → guardrail statement → proof tasks). Decomposed when
reached, since their task shapes depend on upstream results.

---

## 6. Immediate next actions (manager)

1. ✔ S2 sketch accepted (§4 A2); ✔ R2 goal frozen in `SequenceMACPRF.lean`.
2. Dispatch **P2.obj** (real objects: MD model by generalizing legacy
   `mdIterate`/`List.foldl`; the three systems + `blockify`, replacing the G2 stubs) and
   **P2.new** (the standalone generic `cascade_na_pf_adv_le` = Gaži Prop. 1) —
   independent, can run in parallel.
3. Then **P2.bridge** (`ε_KS`) and **P2.hops** assembly; **P2.long** last.
4. T1.1 axiom-seal (cheap manager check).

---

## 7. Current code state (2026-07-13)

`lake build SequenceHash` green (8299 jobs, warnings only, no
`sorry`/`admit`/`axiom`).

- `Encoding.lean` (164 L) · `Spec.lean` (271 L) — **R1 done.**
- `RandomSystems/Converter.lean` (104 L) — CR18 converter + realization. Support.
- `RandomSystems/Finite.lean` (61 L) — instances. Support.
- `RandomSystems/RectHashThenPRF.lean` (446 L) — generic tight Hash-then-PRF,
  **unwired to `sequenceHash`**; re-subordinated under R4/T4.

---

## Deferred (END-of-project) — `SequenceFunction` consolidation

**Problem (owner-flagged 2026-07-14):** the C2SP spec has ONE construction,
`SequenceFunction(H,K,S,F;M)`; our Lean spells it out 3× — `Spec.sequenceHash*`
(unkeyed K=∅,F=2), `Realization.sequenceMAC*` (keyed K,F=1), and two converter
copies (`Converter.sequenceHashStep` vs `Realization.sequenceMACStep`).
`sequenceMACInnerInput` ≡ `sequenceHashInnerInput` with `(F,K)` param'd. Root
cause: `Spec.lean` encodes the unkeyed instance, not the general `SequenceFunction`.

**Migration plan (RISK-FREE, parallel implementation — do LAST, after R3–R6):**
1. In **ghost/temp files** build the canonical general `sequenceFunctionInnerInput`
   /`OuterInput`/`sequenceFunction` (params `F`,`K`) + a general
   `sequenceFunctionStep`, matching spec §SequenceFunction exactly.
2. Prove `sequenceHash = sequenceFunction … fSeqHsh ∅` and
   `sequenceMAC = sequenceFunction … fSeqMac K` (definitional `rfl`), and the
   converter-step instances, so the new model is provably equivalent.
3. Only once the ghost model is fully green + the equivalences proven, SWAP:
   reduce `Spec`/`Converter`/`Realization` to instances of the general one and
   re-verify R1/R2 stay axiom-clean. Delete the ghost files.

Do NOT touch the proven R1/R2 files until the ghost model is validated.

## Deferred (END) — SequenceMAC proof tidy + automation pass

**Problem (owner-flagged):** the Gaži engine (`SequenceMACPRF.lean`, 1572 L) is far
less elegant than CBC (1006 L) / the CR18 ideal. Evidence: `grind` 0 vs 10,
`cr18_*` 1 vs 6, `simp` 107 vs 22, `have` 148 vs 60 — hand-driven, under-automated
(dispatch-driven "close the sorry", never a tidy pass).

**Fix (do with the SequenceFunction consolidation, at the end):**
1. Automation sweep: manual `simp`/`have` chains → `grind`/`cr18_*` (match CBC).
2. Hoist the generic `gazi_*` helpers (`gazi_uniform_restrict`,
   `gazi_eval_prod_uniform`, `gazi_prod_map_right`) into `Dist`/`Distinguishing`;
   **delete `gazi_statDist_le_adjacent_sum` — reuse `maxAdvantage_le_adjacent_sum`**
   (generalize to statDist if needed). Grep the framework first: several of the 35
   local helpers likely already exist.
3. Mint a `gazi_*`/`nmac_*` tactic family for the recurring hybrid/uniform/
   product-disintegration bookkeeping (the CR18-family analogue).
4. Dedicated consolidation/tidy review.

**Meta-rule for R3–R6:** budget a "tidy + automate" dispatch per result (prefer
`grind`/`cr18_*`; grep framework before adding a helper) so the same debt doesn't
re-accrue.

## Deferred (follow-up) — R4 via condEquiv, the CBC-parallel Maurer route

**Owner decision (2026-07-16):** R4 lands FIRST on the H-technique packaging
(equality-on-good + named `h_badmass`, `adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter`).
As a LATER follow-up, ALSO prove R4 via **conditional equivalence** — the
Maurer-native route that both CBC files actually use.

**Why both are worth having:** for sequence, fresh compression outputs are
*exactly* uniform = the ideal URF, so the H-technique ratio term `ε_ratio` collapses
to 0 — which is precisely the regime where condEquiv (one error term, `Δ ≤ Γᵇ`)
applies. The equality-on-good already PROVEN
(`sequenceFunctionIC_r4_equality_on_good`) IS the condEquiv condition, re-read at
the `massYAfalse` level. So this is a re-packaging, not a re-derivation.

**Shape (mirror `cbcGraphGame_condEquiv` / `cbc_mac_beyond_birthday`, NOT CBC's H-technique — CBC has none):**
1. Define `sequenceFunctionGraphGame : PFunPDS _ (_ × Bool)` — an MBO game whose bit
   watches `Bad_SEQ` over the seed (the compression-value collision), exactly as
   `cbcGraphGame`'s bit watches the chaining collision (`CBCStructureGraph.lean:317`).
2. Prove `sequenceFunctionGraphGame |≡ sequenceFunctionIdeal` via
   `condEquiv_of_transcript_mass_reductions` — the three mass reductions come from the
   already-proven equality-on-good content.
3. `Δ(⌈q⌉ real, ⌈q⌉ ideal) ≤ Γᵇ(⌈q⌉ graphGame)` via
   `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`.
4. Bound `Γᵇ` by the counting (= `h_badmass` re-expressed as a `blindMaxWinProb`
   bound, structurally identical to `blindMaxWinProb_cbcGraphGame_le`) — this is where
   the CBC counting engine is reused end-to-end, unlike the H-technique route.

**Payoff:** kills the last condEquiv-free security rung; makes R4 reuse the CBC
condEquiv+counting spine; documents that sequence's exact-equality is what lets the
single-error-term Maurer statement suffice. Do AFTER R4-structural + `h_badmass`
land on H-technique.
