# Sketch — Jost §2.2.6 reproduced top-to-bottom (`RandomSystems/Jost/`)

## 2026-08-04 second-round audit verdict (surface redesign)

Full audit of the existing converter-application/quotient stack before the
CC-pure surface build. **Everything I claimed missing in the critique
exists, at production quality**:

| CC want | exists as | where |
|---|---|---|
| behavioral identity ≈ | `DependentRandomSystem U σ` = Quotient of `Prob` laws by `ContextuallyEquivalent`; `edist_eq_zero_iff_eq` | TypedAction.lean:398/447 |
| per-interface attachment | `DependentDDS.attach` (converter = `ProtocolFn`+`IsDDC` at one code), law + quotient levels, congruence, 1-Lipschitz | TypedAttachment.lean:1728, TypedAction.lean:292/464/505 |
| Prop 2.2.3 order-independence | `DependentDDS.attach_comm` (HEq) / `embed_attach_comm` (exact) / flat `General.attachAt_comm` (CR18 Lemma 3.1) | TypedAttachment.lean:1792/1764, PFunConverter.lean:2506 |
| parallel `∥` | `parallel` at ALL levels (DDS/PDS/Prob/quotient/Resource), non-expansion, cancellation; AC-form: same interfaces, summed alphabets via `HasSumCode` | TypedParallel.lean |
| metric + full abstraction | `contextualEDist` = flat `maxEDist` after flatten; `ofProb_eq_of_flatten_equivalent` | TypedFramingMetric.lean:127/142 |
| construction calculus | `Phi`/`Primitive`/`⟪R⟫—[π]→⟪S⟫`, §10.11 discipline | TypedFinite.lean, LiftingExample.lean |

**Disposition of the first Jost round**: `Machine`/`lawOf`/bisim/coupling =
the AUTHORING + proof-device layer (keep; it generates the "one genuine
behavioral fact" of §10.11). `Jost/Combinators.lean`'s `Converter`/`attach`
and `Machine.par` = reinventions of TypedAttachment/TypedParallel at the
wrong altitude AND (for par) the wrong operation (disjoint-union interfaces
vs AC's fixed-interface alphabet sum) — to be demoted to authoring devices
with coherence receipts, or retired in the re-render.

**Revised phases**: 1) `Interfaces` vocabulary + `Resource F :=
DependentRandomSystem` (plain `=` IS behavioral identity) + constructors
`ofState`/`sampleInit` (= `ofProb ∘ lawOf`) + equality receipts from the
coupling lemmas; 2) converter authoring path step-fn → `ProtocolFn`+`IsDDC`
(audit StepConverter/StepRealization `ofStep`/`ofHistoryStep` first) +
surface attach = TypedAction.attach; 3) surface `∥` = TypedParallel (+
HasSumCode instance for `ofInterfaces` signatures, inert codes for absent
interfaces); 4) Jost re-render (protocol as genuinely per-interface
attachments; reduction c stays a global strict converter) + OTP
≈-demonstrator via `ofProb_eq_of_flatten_equivalent`.

## Second-round completion status (2026-08-04, later session)

Phases 1–3 ✅ COMPLETE and committed (`Jost/Surface.lean`,
`Jost/SurfaceAttach.lean` incl. quotient-level `attach_comm` = Prop 2.2.3,
`Jost/SurfacePar.lean` incl. `Services.free`); dist-real migration repairs
in five kernel files were required and landed with them.  Phase 4's
re-render ✅ (`Jost/SecureChannel.lean` — Prop 2.2.17 as behavioral
identity, leaves reused from `Construction.lean` through
`sampleInit_congr`; the machine combinators demoted to family-authoring
devices, no coherence receipt owed by any shipped statement).

### OTP demonstrator — ✅ COMPLETE (2026-08-04, `RandomSystems/Jost/OTP.lean`)

`otp_real_eq_ideal : real = ideal` proved, axiom-clean, zero sorries.
Route taken = (a) below, with one improvement found during reuse search:
`StrictContextAdvantage.strict_equivalent_of_equivalent` already packages
the whole metric chain (CR18 transcript equivalence → strict contextual
equivalence), so no maxAdvantage manipulation was needed.  The creative
core is `otp_transcript` (the four-worlds transcript invariant: pre-send
all transcripts literally equal; post-send `SR k` pairs with
`SI (m₀ XOR k)`), fed by snoc-history closed forms.  Two generic lemmas
minted (migration candidates → `ResourceMachine.lean`/`PFunDDS.lean`):
`flatten_output_concat` (flattened package answer at `init ++ [q]` from
run + one step — the `getLast` transport done once, via an ∃-repackaging
that makes `rw` motives type-correct) and `output_fullyDefined_of_total`
(⊥-completion of a total system answers `some`).  The final law equality
uses `Dist.fTransform_bijection_uniform` — the library's own "OTP-style
argument" lemma, used for its stated purpose for the first time.
N8 (law-inequality witness) skipped per budget rule; the fibres'
message-dependent vs constant answers make it evident, and it remains a
straightforward Finsupp evaluation if ever wanted.

### Original stage-1 sketch (superseded above)

Boxes (single-world `Interfaces`, alphabets over `Bool`): single-use
channel; A: `send m` (first send stores, later sends answer ⊥-value);
E: `leak` ↦ `Option Bool`.  real = `sampleInit (k : Bool)` with leak
answering `some (m XOR k)`; ideal = `sampleInit (c : Bool)` with leak
answering `some c` (message-independent).

- The claim `real = ideal : Resource F` is NOT a law equality — the two
  laws have disjoint supports over deterministic systems (real's fibres
  answer message-dependently, ideal's constantly).  It enters through the
  bridge `Resource.sampleInit_eq_of_flatten_equivalent` — this example is
  the reason that bridge exists.
- Routing (family I via behavior, alternatives rejected: coupling cannot
  close it — any coupling of the laws has positive disagreement):
  obligation = `StrictContext.Equivalent` of the flattened laws.
  Candidate discharge chains, to be decided at stage 2:
  (a) `maxEDist ≤ ofReal maxAdvantage` (strict-test receipt, kernel-checked
  on shared-domain carriers — both laws here are total) + `maxAdvantage
  = 0` from transcript-law equality for every environment — one
  [CREATIVE] transcript induction on the 2-interface Bool carrier;
  (b) the ratio-1 fixed-query H endpoint (`adv_le_of_fixedQuery_ratio`
  with empty bad set) feeding the same metric chain.
- Deliberately not attempted in this session: it is a fresh
  sketch→DAG→skeleton proof cycle, not wiring; everything it needs is now
  on the surface.


Status: ✅ COMPLETE (2026-08-04). All of `RandomSystems/Jost/` compiles; every headline
declaration is axiom-clean (`propext, Classical.choice, Quot.sound` only, no `sorryAx`).
Deviations from this sketch discovered during the build:
- N4 (bad-set variant) built in a second pass (same day):
  `Machine.lawOf_lawStatDist_le_of_coupling` via the new in-place
  `HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne` and
  `Dist.mass_mono_on_support`; general lemmas migrated in place
  (`Dist.fTransform_congr`/`fTransform_eq_of_coupling` → `Dist.lean`,
  `logLookup_map` → `JostFigure22`).
- Pairing invariants restated `logLookup`-based instead of positional `getElem` (kills
  all index-arithmetic lemma dependencies; every case is a `rw` chain).
- Two tactic traps recorded in STATUS.md §7: rcases `-` clears dependent hypotheses
  (nuked 4 of 6 rel components silently); simp's `Option.map_some`/`some.injEq` fail on
  defeq-but-not-syntactic type indices of composite-machine states — fix is unfolding
  `Option.map`/`Option.bind` in the simp set and `injection` instead of injEq+subst.

## 0. The statement being reproduced

Jost thesis §2.2.6, Prop 2.2.17. Resources AuthChan, Key, SecChan over parties
{A, B, E, F}; protocol pi = (piA, piB) from a symmetric encryption scheme; simulator
sigma at E; reduction system c; CPA_b the left-or-right IND-CPA resources. Claim:

    [AuthChan, Key] —(pi, sigma, eps)→_sim SecChan,   eps(D) := Δ^{Dc}(CPA_0, CPA_1)

Thesis proof: "c CPA_0 = pi [AuthChan, Key] and c CPA_1 = sigma SecChan, where Eve's
output matches by definition and Bob's output matches by correctness."

**Routing (family I).** Both leaves are EXACT identities — and, after derandomizing the
scheme, they are identities of *laws over deterministic systems* (the strongest form),
not merely behavior equivalences: under the identity coupling of the shared seed, the
two machines answer identically at EVERY history. δ = 0; no H-technique, no CE, no
counting. Rejected alternatives: (a) transcript-level equivalence via environments —
strictly weaker conclusion, more machinery, nothing gained since the strong form holds;
(b) H-technique — no bad transcript exists, the identity is unconditional.

**Consequence for the CC layer.** Because the leaves are law *equalities*, the
"distance transport" of Prop 2.2.17 needs NO metric infrastructure: for every function
Φ of two laws, Φ(real, ideal) = Φ(c CPA_0, c CPA_1) by rewriting. The per-distinguisher
eps(D) form is definitional given the equalities. This is the honest Lean form of the
thesis's proof-by-observing.

## 1. Modeling decisions (the adaptation table)

| thesis object | decision here | why |
|---|---|---|
| probabilistic Enc `c ← E.Enc(k,m)` | explicit randomness `enc : K → R → M → C`, tape seed | eager-seed carrier (PDS = Dist over DDS); sampling per query = pre-sampled tape |
| unbounded channel buffer | capacity parameter `cap`, error answer past cap | tape must be `Fin cap → R` for finite seed support (`Dist` is Finsupp) |
| `require` / error ⊥ | error VALUE in the answer fibre; machines stay total (`step` never `none`) | Jost §2.1.2: ⊥ is a returned symbol, continuation allowed; total machines kill all domain reasoning in bisimulations |
| message length `|m|` | abstract `len : M → L`, `zeroOf : L → M`, `len (zeroOf l) = l` | keeps varying-length leakage faithful without indexed vectors |
| party/interface structure | one interface index type per composite; `InterfaceMachine` one-code-per-interface | matches Fig. 2.2's one-box-per-interface reading |
| randomized simulator (own key) | simulator seed folded into the ideal family's seed product | families are functions; composition of seeded objects = product seed before `lawOf` |
| Key "sampled at init" | seed-indexed constant machine under uniform law (`Machine.lawOf`) | already the library's kernel form |

Seed spaces, both leaves: SAME product `K × (Fin cap → R)` on each side (leaf 2 also
works with identity coupling because sigma's "own key" plays CPA_1's key). So the leaves
use the diagonal/pointwise corollary of the coupling lemma; the general coupling form is
still built (ladder item 1) because non-shared-seed examples (single-message OTP) need it.

## 2. The new reasoning principles (the actual mathematics)

Let μ_i : Dist Ω_i, f_i : Ω_i → β. γ : Dist (Ω₁ × Ω₂) a coupling of (μ₁, μ₂).

(i)  **Pushforward congruence along a coupling.**
     If f₁ ω₁ = f₂ ω₂ for all (ω₁,ω₂) ∈ supp γ, then f₁_* μ₁ = f₂_* μ₂.
     Proof: f₁_* μ₁ = f₁_* (fst_* γ) = (f₁∘fst)_* γ = (f₂∘snd)_* γ = f₂_* (snd_* γ) = f₂_* μ₂,
     the middle step by congruence of pushforward on the support.

(ii) **Bad-set variant.** If f₁ = f₂ on supp γ \ Bad, then
     statDist(f₁_* μ₁, f₂_* μ₂) ≤ γ(Bad).  (Coupling bound after pushforward.)

Machine layer (instantiate f_i := toDDS ∘ m_i):

(iii) `lawOf_eq_of_coupling` : coupling of seeds + per-support-pair `toDDS` equality
      (discharged by `toDDS_eq_of_bisim`) ⟹ equal laws.
(iv)  `lawOf_congr` (diagonal corollary): same seed law, pointwise bisimilar machines
      ⟹ equal laws.

These are the Lean forms of "couple on the key, induct on the transcript" — the whole
content of a Prop-2.2.17-style leaf.

## 3. Machine combinators (the DSL's composition layer)

- `par : Machine I₁ → Machine I₂ → Machine (I₁ ⊕ I₂)` — product state, dispatch on the
  address. (Fig. 2.1's `[R, S]`.)
- Converter attachment (the `call` keyword): a converter is a package
  (state; per outer query, a PROGRAM over inner queries returning the outer answer).
  Program = tiny dependent free monad `ret | call (q) (k : Answer q → Prog)`; attachment
  interprets the program against the resource's step, threading both states. Structural
  recursion, no fuel. Total converters over total resources give total composites.
- Scope note: agreement of this machine-level attachment with the PFun-layer
  `ProtocolFn`/attachment theorems is a BRIDGE receipt, deliberately deferred and
  documented in the README (same status as the RS↔AC wiring ledger).

## 4. The systems (all total; alphabets finite)

EncScheme: finite K, R, M, C, L; enc : K → R → M → C; dec : K → C → Option M;
len : M → L; zeroOf : L → M; laws: dec k (enc k r m) = some m; len (zeroOf l) = l.

- Key(k): fetch at A/B ↦ k.
- AuthChan(cap): buffer of ≤ cap ciphertexts; A: send c (error past cap); B: receive ↦
  delivered or ⊥; E: leak i ↦ buffer[i] or ⊥; E,F: deliver i.
- SecChan(cap): same but E: leak i ↦ len of message i (length only).
- CPA_b(k, tape): E-only: (challenge, m₀, m₁) ↦ enc k (tape n) m_b, counter n; length
  guard len m₀ = len m₁ ↦ error.
- piA(k-via-fetch, tape): on (send, m): call fetch; call send (enc k (tape n) m); ok.
  piB: on receive: call receive; call fetch; dec k c (⊥ if none/⊥).
- sigma(k', tape'): on (leak, i): call leakLen i at SecChan; enc k' (tape' i) (zeroOf l).
  on (deliver, i): forward. (Stateless beyond its seed; deliver forwarded.)
- c (reduction, deterministic): plaintext store + ciphertext store; A: (send,m): call
  challenge (m, zeroOf (len m)) at CPA; append both stores; B/E/F as thesis Prop 2.2.17.

real  := lawOf (fun (k, t) => attach (pi k-tape t) (par AuthChan Key(k))) uniform
       — piA's tape = t; Key's seed = k.
ideal := lawOf (fun (k', t') => attach (sigma k' t') SecChan) uniform
game b := lawOf (fun (k, t) => attach c (CPA_b k t)) uniform

## 5. The two leaves (family I, exact)

Leaf 1: real = game 0. Identity coupling on (k, t). Bisimulation relation between
  (converter states × AuthChan buffer) and (c's stores × CPA counter):
  ciphertext buffer = map (fun (i, m) => enc k (t i) m) over c's plaintext store,
  counters equal, delivered index equal. Answer equality per query constructor;
  B-receive uses `dec_enc` correctness (exactly where the thesis says "by correctness").

Leaf 2: ideal = game 1. Identity coupling on (k, t) (sigma's own key ↔ CPA_1's key).
  Relation: c's plaintext store ↔ SecChan buffer (same messages), CPA counter ↔ sigma's
  call count; E-answers both enc k (t i) (zeroOf (len m_i)); B-answers both the
  delivered plaintext. No correctness needed on this side.

Headline (Prop 2.2.17, Lean form):
  real = game 0  ∧  ideal = game 1
  corollary: ∀ Φ : Law → Law → α, Φ real ideal = Φ (game 0) (game 1)  — the eps(D)
  transport with the distinguisher class left abstract, as the thesis's relaxation
  machinery intends.

## 6. Obligation DAG

  N1  [ROUTINE-def] Machine.par                                    (Combinators)
  N2  [CREATIVE-def] Prog + Converter + attach; totality transport (Combinators)
  N3  [CREATIVE] pushforward congruence along coupling (i)         (LawCoupling)
  N4  [LIB?] bad-set variant (ii) — expect `coupling_bound` + pushforward composition
  N5  [ROUTINE-def] EncScheme; Key/AuthChan/SecChan/CPA machines   (Systems)
  N6  [ROUTINE-def] piA/piB/sigma/c as converters; real/ideal/game (Protocol)
  N7  [CREATIVE] leaf 1: real = game 0  — via (iv) + bisim         (Construction)
  N8  [CREATIVE] leaf 2: ideal = game 1 — via (iv) + bisim         (Construction)
  N9  [ROUTINE] transport corollary (rewriting)                    (Construction)
  N10 [DOC] README: scope, layer map, deferred bridges             (README)

Dependencies: N3→N4? (independent), N3,(N1,N2)→(N7,N8); N5,N6 feed N7,N8; N9 from N7,N8.

## 7. Reuse-search targets (stage 3 queries, to be verdict-ed)

- Dist: `fTransform` composition + congruence-on-support; `statDist`; uniform on
  products; `isProbDist` of fTransform/uniform. (Dist.lean / StatDist.lean)
- Coupling: coupling record/marginals; `RandomSystems.coupling_bound`. (Coupling.lean)
- TypedResource: SignatureUniverse.ofInterfaces / Boundary / Query / AnswerAt exact
  shapes; DependentPDS.Prob; anything about products of signatures. (TypedResource.lean)
- ResourceMachine: full remaining API (lines 300–661): lastStep lemmas, bisim exact form.
- LanzenbergerChain.lean: rows for Def 2.14 / coupling attainment — confirm no existing
  lawOf-coupling congruence.
- Existing par/attach at machine level: grep `par`, `attach`, `Prog`, free monad remnants.
