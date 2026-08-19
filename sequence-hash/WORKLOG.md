# SequenceHash work log — durable record of all work

Everything the SequenceHash effort produces is saved **in this repo** (never only
in a scratchpad). This file is the hub: a journal of every Codex dispatch and its
review verdict, plus the map of where each artifact lives.

## ✅ R2 DONE (2026-07-14) — SequenceMAC PRF on the literal C2SP construction

`sequenceMAC_prf_bound_concrete` (`SequenceMACRealization.lean`) — literal C2SP
SequenceMAC over `InputSequence`, output `HashOutput L` — **axiom-clean**
`{propext, Classical.choice, Quot.sound}` (fresh-LSP verified). Chain: concrete →
block-level `sequenceMAC_prf_bound` → `nmac_prf_bound` (Gaži Thm 1) → Prop.1
hybrids + outer PRF hop + condition-C/birthday, every link axiom-clean. Pure
`Δ`/`PFunPDS`, no advPRF/H-technique/`private`/game; CBC machinery
generalized+reused; dead `blockify_prefixFree` removed. Next: R3 (PRF assuming H
indiff. from RO).

## R3 — SequenceMAC PRF assuming H indiff. from RO · ▶ in progress

- **S4 sketch ✔ ACCEPTED** ([`sketches/A4-indiff-prf.md`](sketches/A4-indiff-prf.md)):
  composition route — bound `Δ(⌈q⌉ SM_H, ⌈q⌉ URF) ≤ ε_ind(4q) + ε_enc(q)`
  (indiff advantage of H at the per-query call budget + encoding-collision term;
  `2q` for short keys). Reuses R1 parsing + header/F separation + abstract-crypto
  `ProtocolIndifferentiable`/`.constructs` (exists, axiom-clean). New: the
  PFunPDC/PDS bridge, finite active-call-domain wrapper, prob-converter DPI,
  keyed collision generalization, adaptive-RO scheduling.
- **T4.obj ✔** — guardrail placed; two obligations taken as named hypotheses
  (`ProtocolIndifferentiableSequenceMACBridge`, `SequenceMACEncodingBound`), no
  fake composition. **T4.assembly ✔** (after an orphaned-codex hang → killed all
  codex + redispatched fresh): the **conditional** `sequenceMAC_prf_bound_indiff`
  is sorry-free + **axiom-clean** given its two hypotheses.
- **T5.enc ▶ running** — discharge the encoding obligation: `SM_RO ≈ URF` via the
  SAME `seededHashThenURF` blind-game endpoint as R2's collision (reuse, not
  reprove) + R1 unambiguity + `pairCollisionUnionBound`. First dispatch under the
  tightened automation/reuse discipline.
- **T5.enc ✔ ACCEPTED** (encoding obligation): `sequenceMAC_encoding_bound` proves
  `SequenceMACEncodingBound` — **axiom-clean** (fresh-LSP). Reused the shared
  `maxAdvantage_filterQueries_seededHashThenURF_le` blind-game endpoint +
  `uniform_fixedQuery_collision_le` (R2 birthday leaf) + `encodeItems_injective`
  (R1); NO condition-C reproof, no local generic helper, no `private`/advPRF/sprawl.
  Honest residual `ε_sched` (R3 analog of `ε_C2SP`; zeroable under an A4 freshness
  premise). First dispatch under the tightened discipline + cheatsheet — clean.
- **T6.bridge ▶ running** (last R3 obligation): discharge
  `ProtocolIndifferentiableSequenceMACBridge` by REUSING
  `RandomSystemsCC/ProbMetric.edistD_le_maxAdvantage` (metric↔`maxAdvantage`
  transport — the "missing bridge" EXISTS) + the `Sponge.lean` worked pattern +
  abstract-crypto `.constructs`. Closes R3 to unconditional (also adds
  `sequenceMAC_prf_bound_indiff_unconditional`). Escalates if the abstract-`A`
  statement needs fixing `A` := ProbAlgebra.

## Where the work lives

| Kind | Location |
|---|---|
| Plan, operating model, task board, condensed sketches | [`PLAN.md`](PLAN.md) |
| Full pen-and-paper sketches (Codex `S*` deliverables) | [`sketches/`](sketches/) |
| Dispatch cards + raw Codex outputs (every `codex exec`) | [`dispatch/`](dispatch/) |
| Lean sources (objects, guardrails, proofs) | `SequenceHash/**` |
| This dispatch/review journal | this file |

## Dispatch journal

Newest last. Each entry: what was dispatched, the artifacts, and the manager's
§0.3 review verdict.

### T1.2 — sound-encoding corollary (R1) · ✔ ACCEPTED

- **Card:** [`dispatch/T1.2-card.txt`](dispatch/T1.2-card.txt)
- **Codex output:** [`dispatch/T1.2-codex-output.md`](dispatch/T1.2-codex-output.md)
- **Guardrail / result:** `SequenceHash/SoundEncoding.lean` —
  `sequenceHash_pair_injective` (collision-free `H` ⇒ SequenceHash injective on
  `(S,M)` pairs).
- **Review:** build green; axioms `{propext, Classical.choice, Quot.sound}`; no
  residual `sorry`; guardrail statement byte-identical; `Spec.lean` untouched;
  closed by reusing `sequenceHash_collision_of_distinct_inputs` (no reproof).
- **Purpose:** pipeline smoke test — validated guardrail → `--yolo` dispatch →
  review end-to-end.

### S2 — SequenceMAC PRF pen-and-paper sketch (R2, Gaži 2014) · ✔ ACCEPTED

- **Card:** [`dispatch/S2-card.txt`](dispatch/S2-card.txt)
- **Codex output = the sketch:** [`sketches/A2-sequencemac-prf.md`](sketches/A2-sequencemac-prf.md)
- **Review:** faithful to Gaži (hops mapped to §2.1/§3.1/App. A/Prop. 1/Thm 1);
  caught the single-key vs two-key gap → mandatory `ε_KS` bridge term; ~40 cited
  `REUSE:` theorems spot-checked to exist; correctly scopes AbstractCrypto
  indifferentiability out of R2. Condensed into `PLAN.md` §4 A2.
- **Follow-on (manager):** froze the R2 goal guardrail
  `SequenceHash/RandomSystems/SequenceMACPRF.lean :: sequenceMAC_prf_bound`
  (compiles; systems/terms are stubs for Codex Phase-P). `MDHash.lean` reduced to
  support objects (the mis-placed `mdIterate_append` helper-as-guardrail removed).
- **Two corrections found on owner review (→ S2r):** (1) SequenceMAC's key
  derivation is *better* than HMAC — distinct domain-separated run-ups give
  independent inner/outer keys under ordinary compression PRF, so Hop 1 needs no
  HMAC→NMAC related-key bridge; (2) Gaži is NOT an H-technique proof (classical
  game-hop/hybrid), so R2 must not route through the H-technique endpoints (those
  are R4). v1 snapshot: `dispatch/A2-sketch-v1-preRevision.md`.

### S2r — revise the R2 sketch (Fix 1 key derivation, Fix 2 no H-technique) · ✔ ACCEPTED

- **Card:** [`dispatch/S2r-card.txt`](dispatch/S2r-card.txt) · **summary:** `dispatch/S2r-output.md`
- **Output:** overwrote [`sketches/A2-sequencemac-prf.md`](sketches/A2-sequencemac-prf.md).
- **Review (both fixes verified by grep):** Fix 1 — RKA/`ipad`/`opad` appear only
  as the HMAC contrast; Hop 1 is now an ordinary data-input PRF hop over the two
  distinct run-ups, `ε_KS` has "no RKA component". Fix 2 — H-technique endpoints
  explicitly excluded and reserved for R4; surviving `fixedQueryAdv` is the plain
  nonadaptive notion. Math delimiters clean. Goal guardrail unaffected. PLAN §4 A2
  matches the corrected sketch.

### P2.obj — MD model + `compSystem` (R2 objects, part 1) · ✔ ACCEPTED

- **Review:** build green; `mdIterate_append` axiom-clean `{propext, Quot.sound}`,
  proven by `List.foldl_append` (no reproof, no cascade dep); `MDCodec`+`mdHash`
  added; `compSystem` real via `functionEvaluator` → `ProbPDS` (PDS, not game);
  goal statement frozen; the four other stubs untouched. No Boneh–Shoup.


- **Card:** [`dispatch/P2.obj-card.txt`](dispatch/P2.obj-card.txt) · output → `dispatch/P2.obj-output.md`
- **Deliverable:** MD model in `MDHash.lean` (built directly on `mdIterate` =
  `List.foldl`; block-append law = `List.foldl_append`; **not** the legacy
  Boneh–Shoup cascade — owner: irrelevant) + real `compSystem` in
  `SequenceMACPRF.lean`, replacing that stub. Goal theorem frozen.
- **Recarded** after killing the first dispatch (its card wrongly said to
  generalize `cascadeEval`); Boneh–Shoup scrubbed from card, sketch, and plan.

### Goal refinement (manager edit to the frozen R2 goal, before P2.sys)

To make the systems compose I refined `sequenceMAC_prf_bound` (all green): output
type `HashOutput L → C` (the SequenceMAC digest *is* the shared compression
output type `C`, so `advPRF (sequenceMACSystem …)` and `advPRF (compSystem f)`
share `C`); added key-length `κ` + `hκ : 32 ≤ κ` (spec line 273); added the MD
`codec`/`iv` that `mdHash` needs. `ε_KS`/`ω_S` documented as `Adv` between PDS
systems (not game probabilities). This is the frozen contract for P2.sys onward.

### P2.sys — SequenceMAC + framed-NMAC systems + `ε_KS` · ▶ running (2nd dispatch)

- **Card:** [`dispatch/P2.sys-card.txt`](dispatch/P2.sys-card.txt) · output → `dispatch/P2.sys-output.md`
- **Deliverable:** real `sequenceMACSystem`/`framedNMACSystem` (via
  `functionEvaluator`, mirroring `RectHashThenPRF.realF`), `epsKS` = `Adv` between
  them; reuse Spec/Encoding/MDHash/Converter.
- **1st dispatch → ESCALATED (guardrail worked):** Codex stopped without editing
  and reported three needs — `digestBytes : C ↪ HashOutput L` and
  `hκU128 : κ < u128Modulus` (goal params), and an `MDCodec` block-boundary
  decomposition gap. Manager added the two params to the frozen goal (green) and
  re-carded permitting an `MDCodec` model extension; redispatched.
- **2nd dispatch → ✔ ACCEPTED:** `sequenceMACSystem` (uniform length-`κ` key,
  reusing `headerI`/`headerO`/`derive`/`encodeItems`/`mdHash` + `digestBytes`
  readout) and `framedNMACSystem` (independent uniform `k_I,k_O` via
  `prodProbDist`, `mdIterate` cascades) both real & axiom-clean; no `MDCodec`
  extension needed. Codex again escalated on `epsKS` (implicit-`q` inference in
  the frozen call); manager pinned `epsKS := Adv (q:=q) sequenceMACSystem
  framedNMACSystem` (its forced meaning) and fixed the call to `epsKS (q:=q) …`.
  Build green; `epsKS` axiom-clean `{propext, Classical.choice, Quot.sound}`; PDS,
  no game objects. Remaining `sorry`: `omegaS` (P2.long) + the goal proof.

### IDIOM CORRECTION → P2.reshape (2026-07-14, owner) · ✔ ACCEPTED

Owner: `advPRF`/`advNPRF`/`Adv` are H-technique tools; the Gaži proof is fully
random-system, so R2 must have the **CBCMAC shape** `Δ(⌈q⌉ real, ⌈q⌉ URF)` over
`PFunPDS` converter-on-resource systems (mirroring `cbc_mac_randomness_expander`).
- **P2.new killed** (it built the cascade bound on `advNPRF`); partial
  `CascadeNAPF.lean` deleted. Returns after reshape as a pure-`Δ` bound.
- **P2.reshape** (card `dispatch/P2.reshape-card.txt`, output
  `dispatch/P2.reshape-output.md`) rewrites `SequenceMACPRF.lean`: `PFunPDS`
  systems (`sequenceMACReal = applyDDC (ofStep macStep) compReal`, reusing
  `Converter.sequenceHashStep`), ideal `PFunPDS.URF`, `ε_KS = Δ(⌈q⌉ real,
  ⌈q⌉ framed)`, goal `Δ(⌈q⌉ real, ⌈q⌉ URF) ≤ …`. The `ProbPDS`/`advPRF` version
  is snapshotted at `dispatch/SequenceMACPRF-advPRF-superseded.lean`.
- **✔ ACCEPTED:** build green + full `lake build RandomSystems`/`HTechnique.All`/
  `LegacyChecks`/surface audit all pass; grep confirms no
  `advPRF`/`advNPRF`/`Adv`/`ProbPDS`/game objects. `compReal`=`ofFunDist(uniform
  key)`, `compIdeal`/`macIdeal`=`PFunPDS.URF`, `sequenceMACReal`=converter on
  `compReal`, `epsKS`=filtered `Δ`. **Budget decision:** one compression `Δ` at
  `q*(ℓ+1)` (`R=ℓ+1`, converter-DPI `q*R`), replacing Gaži's ε_ad/(ℓ+1)q·ε_na
  split — the CBCMAC-idiom adaptation. Frozen as the corrected R2 goal. Remaining
  `sorry`: `macStep` (Hop 0 realize), `omegaS` (P2.long), the proof.

### P2.paper-model — faithful Gaži 2014 model · ✔ ACCEPTED

- **Card/output:** `dispatch/P2.paper-model-{card.txt,output.md}`. Followed Gaži
  2014 exactly (no 2025 fallback). Key resolution of the blocker: `f : C→B→C`
  (first arg = key, §2.2); `compReal : PFunPDS B C` = `f_K` (sample `K`, expose
  `f_K:B→C`) vs `compIdeal = r` (§2.1 URF `B→C`); the **cascade uses `f` directly**
  (`mdIterate`), so the compression PRF is an *assumption term* `Δ(⌈q⌉ f_K,⌈q⌉ r)`,
  NOT a resource the cascade queries. `nmac` per §2.2; `CompNASecure` = the NA-PRF
  term (no game object). Goal = **Gaži Eq. (1)**:
  `Δ(⌈q⌉ SequenceMAC, ⌈q⌉ URF) ≤ ε_KS + Δ(⌈q⌉ f_K, ⌈q⌉ r) + (ℓ+1)q·ε_na + q²/|C|`.
- **Review:** build green (+ full `RandomSystems`/`HTechnique.All`/audit per Codex);
  no `advPRF`/`advNPRF`/`Adv`/game objects (one grep hit = a comment). Two `sorry`:
  `nmac_prf_bound` (Prop 1/Thm 1 hybrids), `sequenceMAC_prf_bound` (final triangle).
- **Noted:** messages are `BlockString B ℓ` (Gaži's block abstraction); the
  concrete `InputSequence`→blocks encoding (R1 + a realization) connects it to the
  literal SequenceMAC — a later step.

### P2.nmac — Gaži Theorem 1 proof scaffold · ✔ ACCEPTED (partial, tracked)

- **Card/output:** `dispatch/P2.nmac-{card.txt,output.md}`. `nmac_prf_bound` now
  closes via a two-hop `Δ` trace (`maxAdvantage_le_adjacent_sum`); Prop. 1
  composes length-position + row-index → `ℓ·q·ε_na`. Reused PFunPDS/fixed-query
  laws/`CBCMAC.PrefixFree`/`Dist.prod`/telescoping. Build green, no advPRF/game,
  statements frozen.
- **4 atomic residual `sorry`s** (the deepest Gaži steps, each a named lemma):
  `gazi_lemma5_depth_hybrid` (App. A Lemma 5 / Eq. 9), `gazi_lemma6_row_hybrid`
  (Lemma 6 / Eq. 10), `gazi_outer_prf_hop` (§3.1 outer `f_K₂→r` DPI),
  `gazi_outer_random_collision_bound` (§3.1 cond. C / Eq. 2 / birthday). Plus the
  final `sequenceMAC_prf_bound` triangle (untouched).

### P2.prop1 — Gaži Proposition 1 (both hybrids) · ✔ ACCEPTED

- `gazi_lemma5_depth_hybrid` (Eq. 9, factor `ℓ`, prefix-freeness + `mdIterate_append`)
  and `gazi_lemma6_row_hybrid` (Eq. 10, factor `q`, row product-laws + `CompNASecure`)
  both PROVEN, **verified axiom-clean** `{propext, Classical.choice, Quot.sound}`,
  no `sorryAx`. Build green, pure `Δ`. **Proposition 1 is fully proven.** Sorries 5→3.

### P2.outer — Gaži Theorem 1 outer PRF hop + collision · ✔ ACCEPTED (partial)

- `gazi_outer_prf_hop` PROVEN (§3.1 `f_{K₂}→r`, one-query converter DPI via
  `maxAdvantage_filterQueries_applyDDC_le`, budget `q`), **verified axiom-clean**.
  `gazi_outer_random_collision_bound` remains the sole Theorem-1 `sorry`. Sorries 3→2.
- **Finding:** the condition-C / first-collision machinery exists but is PRIVATE +
  CBC-specific in `CBCMAC.lean`; no reusable generic seed-indexed hash-then-URF
  condition-C theorem yet. → generalize it (never reprove).

### P2.collision — Gaži §3.1 cond. C + birthday · ✔ ACCEPTED → **Gaži Theorem 1 PROVEN**

- Closed `gazi_outer_random_collision_bound`; `nmac_prf_bound` **axiom-clean**
  `{propext, Classical.choice, Quot.sound}` (verified), no game/advPRF.
- **Reuse-not-rederive done right:** generalized CBC's condition-C machinery into
  PUBLIC lemmas in `SwitchingLemma.lean` (`seededConditionCGame`,
  `seededHashThenURF_condEquiv`, `maxAdvantage_filterQueries_seededHashThenURF_le`,
  all axiom-clean); refactored CBC to reuse them; made CBC's needed lemmas public.
  `cbc_mac_randomness_expander` still clean (no regression). **Zero new `private`.**
- **Review lesson:** `lean_verify` initially reported `sorryAx` on nmac/gazi — a
  STALE lean-lsp cache (Codex edited the file outside the LSP's view; imports load
  fresh but the file's own decls showed the pre-edit sorried state). Forcing a
  reload (`lean_diagnostic_messages`) then re-verifying showed clean. **Always
  force an LSP reload before `lean_verify` after an external (Codex) edit.**
- **Remaining R2 `sorry`:** only `sequenceMAC_prf_bound` (line 1545) — the final
  `ε_KS` + Theorem 1 triangle (the SequenceHash-specific hop).

### S3 — SequenceHash realization sketch · ✔ ACCEPTED · T3.obj ▶ running

- Full sketch: [`sketches/A3-sequencehash-realization.md`](sketches/A3-sequencehash-realization.md).
- **Fidelity cleared:** `blockify_prefixFree` is DORMANT (grep: defined in
  `MDHash.lean:41`, used nowhere). The proof discharges prefix-freeness via Gaži's
  fresh-delimiter trick `exists_prefixFree_appendDelimiter` inside the frozen
  theorem — NOT MD strengthening, NOT the encoding. My earlier "MD corner-cut"
  alarm was overblown; the proof is faithful. Dead field to be removed (T3.obj).
- `encodeItems_injective` = unambiguity (R1), NOT prefix-freeness (they differ).
- Concrete target = `sequenceMAC_prf_bound_concrete` over `InputSequence`; C2SP's
  multi-block outer envelope is charged into a bridge `ε_C2SP` (not a definitional
  NMAC equality). **T3.obj** (card `dispatch/T3.obj-card.txt`) places the concrete
  objects + guardrail statement-first + removes the dead field.

### P2.final — `sequenceMAC_prf_bound` triangle · ✔ ACCEPTED → **R2 ENGINE COMPLETE**

- `sequenceMAC_prf_bound` closed via `unfold epsKS` + `maxAdvantage_triangle` +
  `gcongr` + `nmac_prf_bound`. **Verified axiom-clean** (fresh-LSP reload first,
  per the lesson): `{propext, Classical.choice, Quot.sound}`. R2 file: **ZERO
  `sorry`**, no `private`/advPRF/game, green.
- **Honest scope:** this is the **generic Gaži NMAC/cascade PRF theorem over
  abstract `BlockString B ℓ`** — a faithful Gaži adaptation, but NOT yet the
  literal SequenceHash. The file has no `encodeItems`/`headerI`/`derive`/`S`. The
  **SequenceHash connection** (InputSequence → blocks via encoding; discharge
  prefix-free from `encodeItems`+framing NOT `blockify_prefixFree`; `ε_KS` as
  domain separation; envelope→NMAC) is the remaining R2 work → S3 sketch next.

### (old first-dispatch note, superseded) P2.collision · ▶ running

- **Card/output:** `dispatch/P2.collision-{card.txt,output.md}`. Generalize CBC's
  `cbc_condEquiv`/first-collision machinery into a public seed-indexed hash-then-URF
  condition-C lemma (may add to `CBCMAC.lean`; frozen statements untouched), then
  close `gazi_outer_random_collision_bound` → `nmac_prf_bound` fully proven.
- **Status of Gaži Theorem 1:** 3/4 atomic lemmas proven + assembly; this is the last.

### (superseded) P2.realize — Hop 0 · ✖ BLOCKED → resolved by P2.paper-model

- Codex stopped (frozen signatures can't realize it) with two correct blockers:
  (1) `compReal : PFunPDS B C` exposes a fixed `f k : B→C`, but the MD fold needs
  `f` on changing chaining — resource must be `PFunPDS (C×B) C`; (2) the MAC key
  `K` never enters the deterministic `macStep`/`ofStep`.
- Owner: **no guesswork — model exactly like Gaži 2014; if too hard, the 2025
  paper.** → dispatched **P2.paper-model** (card `dispatch/P2.paper-model-card.txt`,
  output `dispatch/P2.paper-model-output.md`): read `2014-578.pdf` precisely
  (§2 compression/cascade/keys, §3 + App. A Prop. 1 / Thm 1 / Lemmas 5–6), model
  its actual definitions in the pure `PFunPDS`/`Δ` idiom, fix the resource domain
  + key handling the paper's way; fall back to `2025-2260.pdf` if Gaži can't be
  rendered faithfully. ▶ running.

- **Card:** [`dispatch/P2.realize-card.txt`](dispatch/P2.realize-card.txt) · output → `dispatch/P2.realize-output.md`
- **Deliverable:** define `macStep` (compression-call-granular SequenceMAC
  schedule; the key `K` lives in the converter, the resource is only `f`) +
  `sequenceMACReal_realizes`, mirroring `Converter.sequenceHashSystem_realization`
  (reuse `mdIterate_append`/`foldl_append`, `applyDDC` realization lemmas).

## Next dispatches (staged, pure-Δ / CBCMAC idiom)

- **P2.bridge** — `ε_KS ≤` ordinary-PRF domain-separation `Δ` term (Hop 1).
- **P2.new** — generic pure-`Δ` cascade bound (Gaži Prop. 1), re-based off `advPRF`.
- **P2.core** — `Δ(⌈q⌉ sequenceMACReal[URF], ⌈q⌉ macIdeal)` info-theoretic part
  (the CBCMAC `randomness_expander` analogue) + `q²/|C|` birthday.
- **P2.long** — `ω_S`. Then final assembly of `sequenceMAC_prf_bound`.

## 2026-07-15 — R3 DONE (indiff → PRF), role-separated ideal

- **Result:** `sequenceMAC_prf_bound_indiff` (SequenceMACIndiff.lean:324) —
  `Δ(⌈q⌉ SM_H, ⌈q⌉ URF) ≤ ε_ind(4q) + pairCollisionUnionBound (HashOutput L) q`,
  conditional on `h_indiff : Δ(⌈q⌉ SM_H, ⌈q⌉ SM_RO_separated) ≤ ε_ind(4q)` (R5 discharges it).
  Axiom-clean {propext, Classical.choice, Quot.sound}; sorry-free; build green (8301 jobs).
- **Manager decision (the fix):** R3's ideal is the ROLE-SEPARATED `SM_RO_separated`,
  not the shared-table `SM_RO`. Codex (T6.simplify) correctly escalated that pure-birthday
  over the shared table is UNSOUND (raw-derivation/inner/outer share one flat URF → cross-role
  collisions; `sequenceMACScheduleError` ε_sched patched it). Role-separation is the faithful
  ideal indifferentiability delivers; cross-role domain separation is R5's simulator's job.
- **DELETED (over-modeling, all local):** the CC apparatus
  (`SequenceMACProtocolIndifferentiable`, `ProtocolIndifferentiableSequenceMACBridge`,
  `MetricResourceAlgebra`/`ProtocolIndifferentiable` use), the shared-table model (`SM_RO`,
  `sequenceMACRODist`, `sequenceMACActiveRO`, `extendSequenceMACActiveHash`), and the
  residual machinery (`sequenceMACScheduleError`, `ε_enc`, `SequenceMACEncodingBound`,
  `sequenceMAC_encoding_bound`).
- **Encoding leg (proven, pure birthday):** `sequenceMAC_separated_encoding_bound` reuses
  `maxAdvantage_filterQueries_seededHashThenURF_le` + `sequenceMACSeparatedSeed_collision_mass_le`;
  R3 = ONE `maxAdvantage_triangle`.
- **Dispatch trail:** T6.simplify (escalated, correct) → T6.sep (`blhbiug9u`, ACCEPTED).
  Root-caused the recurring codex hang: a zombie `uv`/python (lean-lsp) at 11.5 h — reaped.
- **Next:** S4.sketch (`bw0obemcg`) dispatched — R4 tight generic PRF (Shen 2025), H-technique route.

## 2026-07-15 — Domain-separation enabler DONE (additive, axiom-clean)

- **New file** `SequenceHash/DomainSeparation.lean` (171 lines), built via the SequenceHash
  glob, purely additive (no existing proof touched), axiom-clean {propext, Classical.choice,
  Quot.sound}, no private/sorry. Dispatched via the ENFORCED wrapper `codex-dispatch.sh`
  (first live use — preamble embedding verified in the codex process args).
- **inner ≠ outer, UNCONDITIONAL**: `sequenceMACInnerInput_ne_outerInput` (F=1) +
  `sequenceHashInnerInput_ne_outerInput` (F=2) via `headerI_ne_headerO` — "SEQHSH_I" vs
  "SEQHSH_O" differ at byte 7 (73 vs 79); proof = `take 8` exposes the indicator + `decide`.
  This is the structural cascade/outer independence, now machine-checked.
- **within-role**: inner injective (unconditional); outer injective CONDITIONAL on the
  inner-tag function being injective (honest — outer framing carries only |M| + digest).
- **Derive vs framed — verdict (b), CONDITIONAL** on `¬ List.IsPrefix (headerI/O …) deriveInput`
  (raw `K.val`/`S.val`, no role header). Not unconditional. This CONFIRMS the `DeriveCost_SEQ`
  term (S4) and that R5's discharge of R3's `h_indiff` incurs the Derive residual — only the
  inner/outer part of the old `ε_sched` vanishes cleanly.
- **Payoff**: the fact both R3 (via h_indiff) and S4 (B_SEQ) assumed is now proven for the
  main event and precisely characterized for Derive — the "two unverified sketches" gap is
  closed on the load-bearing claim.
- Dispatch: T-domsep (`ba92f2asc`) → ACCEPTED.

## 2026-07-15 — R5 STRUCTURAL done (wires R1→R5), additive + axiom-clean

- **New file** `SequenceHash/RandomSystems/SequenceMACIndiffMD.lean` (additive, axiom-clean
  {propext, Classical.choice, Quot.sound}, no private/sorry/admit/axiom, whole-repo build
  green 8440). Dispatched via the wrapper (`bfs1as4gu`).
- **Sketch A5 corrections honored**: plain MD is NOT indifferentiable → target is the full
  `SequenceFunction` construction; `4q` hash-calls ≠ compression-calls → explicit cost map.
- **Objects (concrete, non-vacuous)**: `mdHashDist` (MD hash law = pushforward of compression
  law); `drstError = 13·Σ²/2^(8L)` (real DRST bound); `sequenceFunctionCompressionCost`
  (hash-call→compression-call map, charges every `blockify` block); `DeriveCost_SEQ =
  DK.mass (DerivePrefixHit_SEQ)` (real prefix-hit mass); `DeriveSafeS_SEQ` (side-condition).
- **Proven bridging** (`sequenceMAC_keyDerive_separated_of_not_prefixHit`,
  `_customizationDerive_separated_of_safe`) connects DeriveCost/DeriveSafe to the proven
  `DomainSeparation` Derive lemmas — the residual is genuinely characterized.
- **`sequenceMAC_md_h_indiff`**: DRST bound `h_drst` (named hypothesis = the deep P5.deep
  follow-up) + `hepsilon` ⟹ R3's exact `h_indiff`. **`sequenceMAC_md_prf_bound_indiff`**:
  applies R3 `sequenceMAC_prf_bound_indiff` at `D_H := mdHashDist` and discharges its
  `h_indiff` ⟹ end-to-end `Δ(⌈q⌉ SM_H over MD, ⌈q⌉ URF) ≤ ε_ind(4q) + birthday`, conditional
  only on `h_drst` + `hepsilon` + `hDK`. **R1→R5 wired.**
- Remaining: **P5.deep** (formalize the DRST simulator → prove `h_drst`); **R4** (Shen B_SEQ);
  **R6** (Backendal). Cleanup D1–D8 still held for owner go.

## 2026-07-15 — R4 structural ESCALATED (clean, no files changed) → 2-dispatch split

- Codex refused to fake the equality-on-good spine: good-transcript equality is NOT a
  facade freebie — it needs an explicit compression-call trace, real/ideal reveal laws,
  `Bad_SEQ`, and a uniform-function fiber-count proof. Hiding it in `hroles` or defining
  badness as unequal masses would be cheating; it declined. (Correct.)
- **Split plan handed back:**
  1. FACADE INFRA: tagged `Prim`/`Eval` accounting + `TaggedBudgetRespects` (total length
     p+q); the generic filtered equality-on-good representative endpoint; typed
     ideal-compression coins, shared-`Prim` real/ideal worlds, canonical `sequenceFunction`
     evaluation, totality + extension/reveal carriers; freeze codec/IV/digest params +
     `SequenceFunctionTraceBound` type; (maybe an `All.lean` import edit / audit exemption).
  2. STRUCTURAL THEOREM: concrete `KeyPointMassBound`, `SequenceFunctionCrossRoleSeparated`,
     compression traces, the five-event `Bad_SEQ`; prove equality of extended fixed-query
     masses off `Bad_SEQ` (reusing DomainSeparation + R5 bridges); define `B_cascade`/
     `B_key`/`deriveCostGeneric`/`B_SEQ` per A4 §5; state `h_badmass` as `∀ E respecting the
     budget, Pr[Bad_SEQ | ideal extension] ≤ B_SEQ`; close with the equality-on-good endpoint.
- **Checkpoint**: facade infra (dispatch 1) builds a NEW ideal-compression H-technique layer
  touching SHARED core (generalizes `EnvRespects`, maybe `All.lean`) — held for owner steer.

## 2026-07-15 — R4 facade infra (dispatch 1) ACCEPTED; theorem (dispatch 2) in-flight

- **New reusable ideal-compression H-technique layer**:
  `RandomSystems/HTechnique/IdealCompression.lean` (generic: `TaggedBudgetRespects`,
  shared-`Prim` real/ideal worlds + representatives + reveal carrier, endpoint
  `adv_le_of_extFixedQueryRep_eq_on_good_filtered`) + `SequenceHash/RandomSystems/
  IdealCompression.lean` (scheme: `SequenceFunctionCompressionModel`,
  `SequenceFunctionTraceBound`, `sequenceFunctionIC{Real,Ideal}`,
  `SequenceFunctionTaggedBudgetRespects`, reveal maps, KStepTotal).
- **Additive-safe verified**: only edit to a tracked shared file = an appended import in
  `HTechnique/All.lean`; `EnvRespects` UNCHANGED and no users rewritten (`TaggedBudgetRespects`
  is parallel). **Whole-repo `lake build` green (8441 jobs)** — nothing downstream broke.
  Axiom-clean {propext, Classical.choice, Quot.sound}; no sorry/admit/axiom/private. Reuses the
  extended-representative/hash-then-PRF spine (no reproved fundamental theorem). Dispatch `bbxi2xlqi`.
- **Dispatch 2 (`b62zpbczd`)**: define `Bad_SEQ` + `B_SEQ` (§5) + `KeyPointMassBound`/
  `CrossRoleSeparated`; prove equality-on-good off `Bad_SEQ`; close `sequenceMAC_generic_prf_tight`
  with the endpoint; Shen mass = named `h_badmass` (R4.deep).

## 2026-07-15 — R6 STRUCTURAL done (Backendal tight, standard-model), additive + axiom-clean

- **New file** `SequenceHash/RandomSystems/SequenceMACTight.lean` (additive, axiom-clean,
  no sorry/private/H-technique, whole-repo green). Dispatched via wrapper (`bvxb662j1`).
- `epsCompMU` (strong multi-user compression Δ) + `SequenceFunctionBodyDepth`/
  `SequenceFunctionSafeScheduleBound` facades over canonical `sequenceFunction`.
- **`sequenceFunction_prf_bound_strong_mu`**: `Δ(⌈q⌉ sequenceFunctionReal, ⌈q⌉ URF) ≤
  epsSchedule + DeriveCost_SEQ + dBody·epsCompMU q q f + pairCollisionUnionBound`, proven by
  ONE `maxAdvantage_triangle` through the normalized NMAC core. Deep parts = named
  hypotheses: `h_nmac_mu` (Backendal Lemma 2/Thm 5 core, = R6.deep) + `hSchedule`
  (safe-schedule normalization). No weakened terms (§7 must-nots honored). Reuses R2
  `nmacReal`/`macIdeal`/`CompressionFamily` + R5 `DeriveCost_SEQ`/`DeriveSafeS_SEQ` + birthday.
- **MILESTONE: Phase A complete EXCEPT R4.** R1/R2/R3+domain-sep full; R5 & R6 structural; R4
  facade done. Remaining: R4-structural (the hard H-coefficient build, 2–3 dispatches, Bad_SEQ
  redesigned to compression-call freshness) + Phase-B deep cores + cleanup D1–D8.

## 2026-07-15 — P6d.nmacmu complete: R6 strong-MU cascade fully proven

- Moved generic `epsCompMU` beside `multiCompReal`/`multiCompIdeal` in
  `SequenceMACPRF.lean`; added the public fixed-query-to-adaptive bridge and the
  one-row converter/DPI restriction used by the outer NMAC call.
- Proved `MACPRF.nmac_prf_bound_strong_mu` with the existing
  `gazi_lemma5_depth_hybrid`: every depth swap is charged directly to one
  `epsCompMU q q f`.  `gazi_lemma6_row_hybrid` is not used, so its factor `q`
  is gone.  The collision leg retains the exact `pairCollisionUnionBound`;
  the original R2 theorem remains source-compatible through its coarse-bound
  wrapper.
- Removed `h_nmac_mu` from `sequenceFunction_prf_bound_strong_mu`; only
  `hSchedule` (C2SP safe-schedule normalization) remains named.
- Verification: focused R2/R6 builds green; whole-repo `lake build` green
  (8441 jobs); H-technique surface audit passed; both the new NMAC theorem and
  R6 headline have axioms exactly `{propext, Classical.choice, Quot.sound}`.

## 2026-07-15 — R6.deep PROVEN (Backendal core) + CORRECTED APPROACH

- **`nmac_prf_bound_strong_mu` is now PROVEN** (`SequenceMACPRF.lean:1645`, axiom-clean,
  whole-repo green). Reused `gazi_lemma5_depth_hybrid` UNCHANGED (already accepts an arbitrary
  per-layer bound); DROPPED `gazi_lemma6_row_hybrid` (kills the factor q — Backendal's exact
  improvement); each depth level charged to `epsCompMU` (= Δ of the existing `multiComp` worlds);
  outer call = one more `epsCompMU`; birthday reused. Upstreamed `ConverterBridge`/`StatDist`
  bridges. R6 headline no longer needs `h_nmac_mu` (only `hSchedule` C2SP-normalization remains).
  Dispatch `bhi26pe7t`.
- **CORRECTED APPROACH (owner pushback, justified):** my "research-grade, can't copy-adapt"
  framing was WRONG (partly context-fatigue laziness). The deep cores REUSE proven machinery:
  CBCStructureGraph.lean has `cbcGraphGame_condEquiv` (PROVEN) = the "fresh ⇒ real=ideal"
  template for R4 step-3/R5 simulator; its counting engine = R4 `h_badmass`; R2's `gazi_lemma5`
  = R6. Sequence's proven domain separation + prefix-freeness SIMPLIFY each. DO the real adapted
  proof, never merely name a hypothesis. R6.deep proved this: 1 dispatch reusing a proven lemma.
- **Now driving (real proofs, not hypotheses):** R4 step 3 (`b1pibaix3`, fiber via CBC
  condEquiv template) → R4 step 4 → R5 `h_drst` (structure-graph simulator) → R4 `h_badmass`
  (CBC counting engine) → cleanup.

## 2026-07-16 — R4 equality-on-good PROVEN (the H-coefficient crux), ~13 sub-dispatches

- **`sequenceFunctionIC_r4_equality_on_good` PROVEN** (axiom-clean) — the full H-technique
  equality-on-good ("fresh ⇒ real=ideal" on `extFixedQueryTranscriptDistRep`), reusing the CBC
  generic counting engine (`cbc_fiber_card` STRUCTURE + `Counting.card_filter_shift_univ` + the new
  `Dist` framework lemma — NOT CBC's condEquiv engine; the H-technique route reuses none of it)
  adapted: freshness (3a) → reveal/reduction (3b) → filtered endpoint (3c) → terminal shift + laws →
  `sequenceFunction_fiber_card` → skeleton shift-invariance → direct representative-mass eq.
- **New REUSABLE framework lemma** `Dist.mass_prod_uniform_coordinate_exchange` (`Dist.lean:1315`,
  axiom-clean) — the honest bottom the grind converged to. Generic, upstreamed.
- R4 step 4 (`sequenceMAC_generic_prf_tight`: `B_SEQ` + eq-on-good + named `h_badmass`) dispatched
  `bfqejn3c2`. After it: R4-structural done; then `h_badmass` (CBC counting = R4.deep), R5 `h_drst`,
  R6 `hSchedule`, cleanup.

## 2026-07-16 — technique clarification + condEquiv follow-up queued

- Verified: BOTH CBC files use **conditional equivalence** (`cbc_condEquiv` CBCMAC:816,
  `cbcGraphGame_condEquiv` CBCStructureGraph:317; via `condEquiv_of_transcript_mass_reductions`,
  bound `Δ ≤ Γᵇ`). Neither touches the H-technique surface — that surface (`IdealCompression.lean`)
  is the sequence R4 stack ONLY. Corrected the eq-on-good entry above (reuses GENERIC counting, not
  the CBC condEquiv engine).
- **Owner decision:** R4 lands first on H-technique (per the AskUserQuestion); condEquiv route is a
  QUEUED follow-up — recorded in `sequence-hash/PLAN.md` "Deferred (follow-up) — R4 via condEquiv"
  and in memory. For sequence, fresh⟹exactly-uniform ⟹ `ε_ratio=0`, so condEquiv (one error term,
  reuses the CBC spine) is the natural second proof; the proven `sequenceFunctionIC_r4_equality_on_good`
  IS its `massYAfalse` condition (re-packaging, not re-derivation).

## 2026-07-16 — MODELING CORRECTION: filter-first / technique-second (owner)

Foundational order-of-operations law established (persisted in memory). Summary:
- **Filter in the RS domain FIRST** (`⌈q⌉ S` = new RS, = S up to q, rejects after), THEN a
  transcript technique. The filter defines the finite game; it is NOT a hardness statement.
  Headlines are always `Δ(⌈q⌉ real, ⌈q⌉ ideal) ≤ …` (CBC shape) — R4/R5/R6 alike.
- **H-method main theorems** are transcript-law facts (`adaptiveTranscriptAdvantage_le_lawStatDist`
  Derivation:1550; `adv_le_of_fixedQuery_eq_on_good` :423; `adv_le_of_extFixedQueryRep_eq_on_good`
  :1230). `filteredAdaptiveTranscriptAdvantage`/representatives = DERIVED PLUMBING, not the method.
- **condEquiv ⇄ H-technique**: same filtered objects, interchangeable, downstream of the filter.
- **ProbPDS = PFunPDS.Prob** (all PFun); `.val` = raw PFunPDS where `⌈q⌉` lives.
- **R4 rework:** `sequenceFunctionIC_r4_equality_on_good` (SequenceMACGenericFiberMass:2201) is
  wrong-order (concludes `filteredAdaptiveTranscriptAdvantage (TaggedBudgetRespects …)`). Corrected:
  `Δ(⌈p+q⌉ …Real.val, ⌈p+q⌉ …Ideal.val) ≤ B_SEQ` via bridge
  `maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage` (AdaptiveLawBridge:547) →
  `adv_le_of_extFixedQueryRep_eq_on_good` (:1230) + named `h_badmass`. KEEP the eq-on-good core
  (`…_extFixedQueryTranscriptDistRep_eq_on_good`, Filt-free) + KStepTotal lemmas; DROP
  `filteredAdaptiveTranscriptAdvantage`/`TaggedBudgetRespects` from the headline; p/q/λ = hypotheses
  + in `Bad_SEQ`. Bridge needs `DeltaFilteredFiniteQueryNormalization` (copy CBC).
- **Dispatch hygiene:** P4n hung 14h on a silent network drop (0.14s CPU) — verify codex alive +
  burning CPU within ~1 min of every dispatch; never wait on a silent block.
- Next task: rewrite P4n.spine card to the corrected chain, re-dispatch (with liveness check).

## 2026-07-16 — filterDom step 1 ACCEPTED (core filter generalized in place)

Dispatch P4-filterdom (b2o9iejfz), owner-approved "generalize filterQueries in place":
- `PrefixClosed` abbrev + `prefixClosed_length_le` (PFunDDS.lean:25/30, mathlib `<+:` reused).
- `@[reducible] filterDom (P) (hP : PrefixClosed P)` at DDS (PFunDDS:287) + PDS (PDS:98) level.
- `filterQueries q := filterDom (length ≤ q) …` DEFINITIONALLY (PFunDDS:311); `filterQueries_eq_filterDom`
  = `rfl`. Reducibility ⟹ old body reproduced ⟹ ZERO downstream proof-body edits.
- VERIFIED independently: whole-repo `lake build RandomSystems RandomSystemsCC SequenceHash` green
  (8500 jobs, rerun clean); filterDom decls axiom-clean; downstream canaries `cbc_condEquiv`,
  `cbc_mac_randomness_expander` still {propext, Classical.choice, Quot.sound}. (The sorryAx on
  cbc_mac_beyond_birthday is the PRE-EXISTING mass_cbcGraphBad_le residual, not from this change.)
- Bridge VALVE-STOPPED with a correct finding: general `Δ(⌈P⌉·,⌈P⌉·) ≤ Adv[q]` is unsound (distinguisher
  can violate P → get none → continue; arbitrary prefix-closed P is not extensible so exact-query
  padding fails). Codex proposed a new `domAdaptiveTranscriptAdvantage` (StopsBy + DomEnvRespects) +
  normalization shell. NEXT: decide bridge target — reuse existing `filteredAdaptiveTranscriptAdvantage`
  (which the R4 endpoint already consumes; R4's budget IS extensible to the fixed p+q length, so
  exactly-q P-respecting envs may suffice) vs. codex's new notion. Investigate :513 bridge first.

## 2026-07-16 — filterDom BRIDGE ACCEPTED (filter-first, reuses proven R4 endpoint)

Dispatch P4-bridge (bzskh9ivx). Owner correction absorbed: no fundamental filter/budget distinction —
all Maurer restrictions are well-defined; my "totality obstruction" was one lemma's over-strong hyp.
- `maxAdvantage_filterDom_le_filteredAdaptiveTranscriptAdvantage` (Derivation:1909):
  `Δ(⌈P⌉ S.val, ⌈P⌉ T.val) ≤ filteredAdaptiveTranscriptAdvantage (liftHist P) S T`, given `KStepTotal S/T q`,
  `PrefixClosed P`, `DeltaFilterDomFiniteQueryNormalization P`. `liftHist P t := P t.1.toList` (:1693).
  Support: `deterministicTranscriptDist_filterDom_eq` (:1759), generic filterDom condEquiv mass
  reductions (CondEquiv:152, count-filter now one-line instances), length-≤q restricted adv = ordinary
  adaptiveTranscriptAdvantage (:1859, count route preserved).
- VERIFIED: full build green (8500 jobs); bridge + `deterministicTranscriptDist_filterDom_eq` axiom-clean
  {propext, Classical.choice, Quot.sound}; count canary `cbc_mac_randomness_expander` clean; no new
  sorry/private; sequence/CBC/R1-R6 bodies untouched.
- Codex SOUNDLY kept `DeltaFilterDomFiniteQueryNormalization P` as a HYPOTHESIS (didn't fake an
  unconditional padDDD — prefix-closure ≠ length-q respecting continuation; e.g. `length≤1` at q=2).
  For the sequence BUDGET it IS extensible (a budget-respecting history under p+q takes one more
  prim-or-eval query within budget) ⟹ dischargeable, scheme-specific.
- NEXT (R4-structural spine): (1) budgetHist predicate + PrefixClosed; (2) discharge
  `DeltaFilterDomFiniteQueryNormalization (budget)` via extensibility (the respecting-completion, the
  substantive piece); (3) `liftHist budgetHist = SequenceFunctionTaggedBudgetRespects`; (4) B_SEQ §5 +
  named h_badmass; (5) headline `Δ(⌈budget⌉ real.val, ⌈budget⌉ ideal.val) ≤ B_SEQ` via bridge + proven
  `sequenceFunctionIC_r4_equality_on_good`.

## 2026-07-16 — R4-STRUCTURAL DONE (filter-first surface) ✅

Dispatch P4n.spine2 (bcnf10kvx). `sequenceMAC_generic_prf_tight` (SequenceMACGeneric.lean:192):
  Δ(filterDom budgetHist real.val, filterDom budgetHist ideal.val) ≤ B_SEQ
- FILTER-FIRST form (RS-domain filter, per owner). Canonical `sequenceFunctionICReal/Ideal`; all five §8
  guardrails (users≤q, KeyPointMassBound, TraceBound, CrossRoleSeparated, OutputCompressionBacked);
  RHS = B_SEQ (§5: B_cascade+B_key+deriveCostGeneric), not B_N.
- `budgetHist` + `budgetHist_prefixClosed`; `liftHist_budgetHist_eq` (= SequenceFunctionTaggedBudgetRespects);
  B_cascade/B_key/deriveCostGeneric/B_SEQ per §5. calc chain: bridge
  `maxAdvantage_filterDom_le_filteredAdaptiveTranscriptAdvantage` (+ KStepTotal + h_norm) → rw liftHist →
  proven `sequenceFunctionIC_r4_equality_on_good` (+ h_badmass). No triangle/NMAC hop.
- TWO NAMED R4-deep cores: `h_norm` (DeltaFilterDomFiniteQueryNormalization budget — budget extensibility)
  + `h_badmass` (the counting, = original R4.deep).
- VERIFIED: full build green (8501 jobs); headline axiom-clean {propext, Classical.choice, Quot.sound},
  NO sorryAx (⟹ bridge + eq-on-good genuinely sorry-free; the two cores are real hyps not sorries);
  additive (only SequenceMACGeneric.lean); no private; R1-R6/facade untouched.
- NEXT R4-deep: (1) h_norm via generic `deltaFilterDomFiniteQueryNormalization_of_extensible`
  (suppress P-violating + pad respecting via QExtensible) + budget QExtensible; (2) h_badmass counting.
  Then R5, R6.

## 2026-07-16 — h_norm Part A ACCEPTED; Part B scoped (6 obligations)

Dispatch P4-norm (b86tcip2b). Part A green + axiom-clean:
- `QExtensible` (PFunDDS:28); generic tag-count facts (IdealCompression:77: `taggedCounts_toList`,
  `primCount_add_evalCount`, prefix monotonicity — GENERALIZED sequence→framework); `nonemptyBlock`;
  `sequenceFunctionICReal/Ideal_totalOnNonempty` (IdealCompression:172); `budgetHist_append_prim/eval` +
  corrected `budgetHist_qExtensible` (SequenceMACGeneric:61).
- FINDING: unconditional extensibility is FALSE — needs `0 < users` (+ TraceBound/backed). Counterexample
  users=0,p=0,q=1. ⟹ the discharged `_norm` headline must ADD `0 < users`.
- Part B (suppress+pad normalization) VALVE-STOPPED — genuinely new construction (padDDD/SelfAnswerFilter/
  Cache don't cover it). 6 obligations: (1) suppression transform (follow d while P holds; at first
  violation compute verdict along deterministic none-tail); (2) its verdict prob = d vs filterDom P S;
  (3) history-dependent respecting padding via QExtensible; (4) padded d makes exactly q + DistinguisherRespects P;
  (5) lift through fTransform, preserve mass, base-system verdict equalities via TotalOnNonempty; (6) combine
  → advantage domination + instantiate. NEXT: dispatch Part B (valve after suppression 1-2).

## 2026-07-16 — h_norm Part B STEP 1 (suppression) ACCEPTED

Dispatch P4-normB (brcknvnop), valve after Step 1. New file `RandomSystems/FilterDomNormalization.lean`
(green, axiom-clean): `keepAdmitted`, `suppressViolating`, `verdict_suppressViolating_iff_filterDom`,
`verdictProb_suppressViolating_eq_filterDom`, `advantage_suppressViolating_eq_filterDom` (suppression
answers rejected queries internally with none + continues). Build green (8502 jobs), no new sorry.
- Two soundness corrections: (1) generic lemma needs `QBounded P q` (P l → length ≤ q), not just
  QExtensible (P:=True,q:=0 counterexample) — budget IS q-bounded; (2) prefix-closure ≠ permanent
  rejection (fullyDefined deletes rejected query; a later one may be admitted) — replay handles it.
- Step 2 remaining: QBounded predicate + budget proof; respecting padding via QExtensible; exact-q +
  DistinguisherRespects + mass/verdict/advantage preservation; corrected normalization lemma
  (QExtensible + QBounded + TotalOnNonempty); discharge `sequenceMAC_generic_prf_tight_norm` (+ 0<users).
- Reuse map: keptPrefix, fullyDefined, absorbGo replay, winProb_fTransform_left/right, winProb_congr_support.

## 2026-07-16 — h_norm Part B STEP 2 (padding) ACCEPTED; domination+discharge remains

Dispatch P4-normC (bjx2kyryp), valve after padding. Green + axiom-clean:
- `QBounded` (PFunDDS:35), `budgetHist_qBounded` + `budgetHist_nil` (SequenceMACGeneric:61).
- `padRespecting` (history-dependent, subtype-state maintains P) (FilterDomNormalization:577),
  `queriesExactly_ddToDDE_padRespecting` (:740), `distinguisherRespects_padRespecting` (Derivation:1707).
- Correction 3: generic lemma false without `P []` (P:=False vacuous); padRespecting requires h0:P[],
  budgetHist_nil supplies it.
- FINAL remaining (codex plan): (1) replay invariant aligning suppress admitted-state with padRespectingState;
  (2) QBounded ⟹ suppressed distinguisher stops by q; (3) verdict equivalence vs total systems via
  winProb_fTransform_left/right + winProb_congr_support; (4) advantage domination + generic lemma
  (PrefixClosed+QExtensible+QBounded+P[]+TotalOnNonempty); (5) instantiate ⟹ discharge `_norm`.

## 2026-07-16 — h_norm CLOSED ✅ (filter-first re-architecture complete)

Dispatch P4-normD (bzjd13ul2). `deltaFilterDomFiniteQueryNormalization_of_extensible` (Derivation:1780,
generic: PrefixClosed+QExtensible+QBounded+P[]+TotalOnNonempty ⟹ the normalization) + the domination
(`advantage_suppressViolating_le_padRespecting` :1060, via replay invariant :852 + stop-by-q :515 + verdict
equivalence through winProb). Discharged `sequenceMAC_generic_prf_tight_norm` (SequenceMACGeneric:330):
FILTER-FIRST headline Δ(filterDom budget real.val, filterDom budget ideal.val) ≤ B_SEQ, h_norm GONE (proven
via the generic lemma + all budget facts), `0<users` added, ONLY `h_badmass` remains.
- VERIFIED: full build green (8502 jobs); `_norm` + generic lemma axiom-clean {propext, Classical.choice,
  Quot.sound}, NO sorryAx; count-filter normalization preserved; no private.
- 3 soundness corrections along the way (0<users, QBounded, P[]) — all honest, all landed.
- ★ R4-STRUCTURAL now rests on a SINGLE named core `h_badmass` (the CBC-counting adaptation). Filter-first
  re-architecture (filterDom + bridge + normalization) COMPLETE + axiom-clean.
- NEXT: h_badmass (real security counting = R4.deep), then R5 (DRST simulator), R6 (hSchedule; R6.deep done).

## 2026-07-16 — h_badmass SKELETON ACCEPTED (decomposition + §3c adaptation)

Dispatch P4-badmass (b8wo54sza), valve after skeleton. New file `SequenceMACGenericCount.lean` (green,
axiom-clean). Genuine §3c table: KILLED (input ambiguity, prefix aliasing, inner/outer related-key,
cross-role input aliasing); REMAINS (compression-call internal collision, primHit pqλ/2^c, single-coll
C(q,2)(λ+2)/2^c, double/equal-top merge=NAMED, raw-key repeats, secret-input guessing, derive).
- Exact Bad_SEQ = PrimHit ∨ ConstructionCollision; cover Bad_SEQ ⊆ CascadeBad ∪ KeyBad ∪ DeriveBad;
  cascade cover ⊆ PrimHit ∪ SingleColl ∪ GraphBad; additive assembly → B_cascade → B_SEQ; PROVEN.
  `sequenceFunction_badmass_of_named_leaves` produces h_badmass from named leaves.
- 5 named leaves: h_primHit, h_singleColl, h_key, h_derive (TRACTABLE, undischarged), `sequenceGraphBad_equalTop`
  (the honest corner). Codex correctly did NOT add `_final` (would falsely imply equalTop is sole residual).
- VERIFIED: full build green, htechniqueSurfaceAudit passed, axiom-clean, no sorry/private.
- NEXT: discharge the 4 tractable leaves (needs digest-card=2^c, codec secret-sites, uniform/counting leaves,
  KeyPointMassBound + TraceBound), then `_final` carries ONLY sequenceGraphBad_equalTop.
