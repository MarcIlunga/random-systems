---
name: cc-constructions
description: "Models and proves Constructive Cryptography constructions in Lean 4 over the RandomSystems tree. Use when DEFINING resources, converters, simulators, or reductions; when stating or proving a construction (real ⊑ ideal-with-simulator, Prop-2.2.17-style statements, composition claims); when deciding WHICH layer (pseudocode surface, machine, law, behavioral quotient, spec/AC) a new object or statement belongs to; or when a CC statement mixes with an indistinguishability bound. Explains the layer tower, the eager-randomness discipline, the identity ladder (law equality vs behavioral equality), and the reduction pattern — with the Jost §2.2.6 and OTP files as worked templates. Every probabilistic leaf (Δ ≤ ε, system equivalence with content) is handed to the random-systems-proofs skill; this skill decides what that leaf must SAY."
---

# Constructive Cryptography: modeling and construction workflows

A CC development in this tree is a **tower**, and almost every failure mode is
working at the wrong floor.  The composition algebra and the quotient already
exist at production quality; a construction proof writes *definitions* plus a
small number of *leaf identities*, then transports.  Most of the work is
knowing which floor each object lives on and what the leaves must say — not
inventing machinery.  (Measured failure, recorded in
`sketches/jost-2-2-6.md`: a full machine-level converter/parallel layer was
built before auditing, and the audit then found `TypedAttachment`,
`TypedAction`, and `TypedParallel` already had all of it, at the right
altitude.  **Audit before building** is this skill's first rule.)

Copy this checklist into your first response when starting a construction:

```
- [ ] 1. MODEL     boxes, converters, seeds — on paper, in thesis vocabulary
- [ ] 2. FLOORS    place every object and every claim on the tower (§ below)
- [ ] 3. AUDIT     what exists: Jost.lean layer map → CHEATSHEET → grep kernel
- [ ] 4. DEFINE    surface constructors only; kernel names never in statements
- [ ] 5. LEAVES    state each RS obligation precisely → random-systems-proofs
- [ ] 6. TRANSPORT construction statement by rewriting/complexity-free algebra
- [ ] 7. RECEIPTS  axiom audit; ScheduleAgnostic caveat; zero-slack check
```

## The tower

| floor | objects | identity | where |
|---|---|---|---|
| L0 pseudocode | Fig.-2.2 boxes, `call` blocks | — (syntax) | the paper |
| L1 realizations | `Machine`/`Realization`: state, init, step; converter = state + `ofRounds` step | bisimulation | `ResourceMachine.lean`, `Jost/Surface*.lean` |
| L2 deterministic systems | `DependentDDS` (typed), `PFunDDS.DDS` (flat, via `flatten`) | function equality | `TypedResource.lean`, `PFunDDS.lean` |
| L3 laws | `Dist` over systems; `sampleInit` = Def 2.2.1's random variable over deterministic systems | Finsupp equality (representation-dependent!) | `PDS.lean`, `Machine.lawOf` |
| L4 **resources** | the contextual quotient; **plain `=` is behavioral identity** | `=` (≙ no separating observation context) | `TypedAction.lean`; surface `CC.Resource`/`ResourceAt` |
| L5 algebra | `attach` (Def 2.2.2/Prop 2.2.3), `∥` (Maurer11 eq. (3)), non-expansion (Thm 2.2.11's engine) | — (laws proven once) | `Jost/SurfaceAttach.lean`, `Jost/SurfacePar.lean`, kernel underneath |
| L6 constructions | specifications (SETS of resources), `⟪R⟫ —[π]→ ⟪S⟫`, relaxations, composition theorem | set inclusion | `TypedFinite.lean`, `LiftingExample.lean`, DESIGN §10.9–10.11 |

**The Maurer-pass surface (2026-08-06) supersedes L5's spellings**: author
against `ResourceSystem` with TOTAL attachment `α •[i] R` (no provides
proofs, no layout in types; Prop 2.2.3 is a bare `=` — `attachAt_comm`),
closeness `R ≈[ε] S` (never `edist` in a statement — the linter now
rejects it, along with `HEq` and `Function.update`), the Def-1 algebra in
`SurfaceAlgebra` (`id`, `∘`, `⊣[i]`, two-condition `Constructs`,
`Protocol`), the channel calculus in `SurfaceChannels` (`—→ •—→ —→•
•—→• •══•`), the reservation-free `resource`/`converter` grammar with
`display/latex/role` clauses, and `#cc_latex`/`#cc_diagram` as the
presentation layer.  The layout-indexed forms below remain as kernel-
facing demoted statements with named successors (`#cc_surface_audit`'s
third counter tracks them).

**The two-intervention rule** (the whole CC/RS division of labor):
probabilistic reasoning enters exactly twice.  *Once per framework*: the
algebra laws (composition-order independence, distinguisher absorption,
quotient congruence) — already proven; you cite, never re-prove.  *Once per
construction, at the leaves*: identities or distances between fully
assembled systems/laws.  Everything between — simulators, reductions,
composition, relaxations — is definitions and rewriting.  A proof that
manipulates probabilities outside a leaf is at the wrong floor.  Corollary:
**never cross a specification boundary** — once a construction statement is
proven, later steps use the constructed resource as an opaque element of
the algebra; reopening its pseudocode in a downstream proof is an error.

## Modeling decisions (each was gotten wrong once; the fix is recorded)

**Vocabulary rule (§10.11).**  Statements read as algebra, in thesis words.
Kernel names (`SignatureUniverse`, codes, `Boundary`, `Dependent*`,
`fTransform`, embeddings) may appear in definition *bodies* and in the one
marked Bridges section of `Jost/Surface.lean` — never in a surface
statement.  Author against `CC.Interfaces`/`Resource`/`Services`/
`Converter`/`∥`, not against the kernel.

**Eager randomness.**  The carrier is a law over *deterministic* systems, so
every sampling step is a seed coordinate: `Initialization x ←$ X` is a
seed-indexed family under `sampleInit`; per-query randomness is a
pre-sampled finite tape (`Fin cap → R`) totalized by `default` past `cap`
(`tapeAt`) — no guards, no caps in machines; `cap` only calibrates how many
queries a game means what it claims.  A converter that "samples its own
key" (a simulator) is a *family* of deterministic converters; compose
families as functions, take one product seed, sample once.

**Totality and rejection.**  Prefer total machines: `step = none` is
blocking divergence (history leaves the domain); a `require`-violation the
caller survives is an ordinary error VALUE in the answer fibre.  Total
machines kill all domain reasoning in bisimulations.  Caveat owed either
way: `Machine`-built domains can be order-sensitive — a rushing-adversary
statement owes its own `ScheduleAgnostic` receipt (STATUS §11.31).

**One world or many.**  A resource that owns its interfaces needs only
`Interfaces` (one signature per interface; no code layer visible).  The
moment a converter *changes* what an interface provides (plaintext-send
outer vs ciphertext-send inner), the development needs `Services` — the
named alphabet pairs the construction ranges over; that is what kernel
codes are for.  Parallel composition over a fixed interface set needs the
free sum-closure `Services.free` (each interface then provides both
components' services — AC's `∥`, NOT a doubled interface set).

**The identity ladder.**  Decide which identity a leaf can have BEFORE
proving; each rung has a packaged discharge:

1. **Law equality** (strongest): the fibres agree pointwise as systems under
   a coupling of the seeds — often the identity coupling of a shared seed.
   Discharge: `Resource.sampleInit_congr` / `sampleInit_eq_of_coupling`,
   per-fibre `toDDS_eq_of_bisim`.  Test: do the coupled fibres answer
   identically at EVERY history, observer-free?  (Jost §2.2.6: yes — both
   leaves.)
2. **Bad-set distance**: fibres agree off a bad seed set → δˡ ≤ joint bad
   mass (`Machine.lawOf_lawStatDist_le_of_coupling`).  E.g. statistical
   instead of perfect correctness.
3. **Behavioral equality only**: the pairing of seeds is observer-dependent
   (OTP: real key `k` pairs with ideal ciphertext `m₀ ⊕ k`, and `m₀` is the
   environment's choice).  Laws differ — *no coupling can close this* — but
   the resource identity holds.  Discharge through the bridge
   `Resource.sampleInit_eq_of_flatten_equivalent`; the obligation becomes a
   transcript/behavior argument — an RS leaf.
   Never state rung 3 as a metric bound when equality holds (zero-slack
   rule), and never claim rung 1 when only rung 3 is true (the OTP laws
   have disjoint supports; `Jost/OTP.lean` is the counterexample template).

**The reduction pattern.**  Build the reduction system `c` so that real and
ideal are *literally* `c` attached to the two game worlds.  Then the
security statement needs NO metric infrastructure: prove the two leaf
identities and the ε(D) transport is `rw` (`Φ (real, ideal) = Φ (c·G₀,
c·G₁)` for every functional Φ) — distinguisher absorption is definitional
because `c` is inside the game laws.  Per-party protocol converters attach
per interface (order-independence = `ResourceAt.attach_comm`); a reduction
or simulator that needs shared state across all interfaces is a *global*
converter (flat strict layer), which is fine — reductions live on the
distinguisher side.

## The leaf handoff (→ random-systems-proofs)

This skill decides *what the leaf says*; the RS skill proves it.  Hand over
a fully assembled, closed object and a target form — never a half-composed
one and never a conclusion-shaped hint:

| leaf form | hand to RS skill as |
|---|---|
| two machine fibres equal as systems | `toDDS` equality; suggest bisimulation (family I) |
| two seeded families equal as laws | seed coupling + per-fibre bisim (family I) |
| δˡ / advantage bound with a bad event | coupling with bad set, or CE/H-technique per the RS routing |
| behavioral equality, observer-dependent pairing | `StrictContext.Equivalent` of the flattened laws — transcript route (`strict_equivalent_of_equivalent` packages transcript-equivalence → strict) or H ratio-1 |
| a named game assumption (IND-CPA, PRF) | nothing — it stays an assumption; the construction transports TO it |

The RS skill's stage-1 rule applies to the leaf, not to the modeling: do
the CC modeling first (this skill), then enter the RS skill at its SKETCH
stage with the leaf statement fixed.

## Rationalizations to reject

**"The kernel lacks X, I'll build it at the machine level."**
Audit first: `RandomSystems/Jost.lean`'s layer map, then `CHEATSHEET.md`,
then grep `Typed*.lean`.  Attachment, order-independence, parallel, the
quotient, the metric, and the construction calculus all exist.  The
machine-level combinators in `Jost/Combinators.lean` are the preserved
cautionary tale: correct, axiom-clean, and demoted — they duplicated the
kernel at the wrong altitude, and their `par` was even the wrong operation
(doubled interfaces vs AC's summed alphabets).

**"Equality of laws is the resource identity."**
Only rung 1 of the ladder.  The OTP identity is unstatable at the law
floor; resources are behaviors (Def 2.2.1), and the quotient is the
identity.  Conversely, when rung 1 holds, USE it — it is strictly stronger
and needs no metric.

**"Converters are programs, give them a monad."**
Def 2.2.2's converter is a system: per outer input, a bounded streak of
inner calls, then an answer.  Author with `Converter.ofRounds`
(whole-history step + per-round call budget; the causality judgment is
discharged inside the constructor).  No do-notation, no free-monad framing
in the surface.

**"I'll put the game/CPA box at a different kind of object."**
A game IS a resource (Fig. 2.4b's own caption).  One interface, challenge
queries, error VALUES for `require` — same constructors as every other box.
That unification is what makes `c · G_b` typecheck against `π · R`.

**"Sampling per query needs a probabilistic step function."**
No — eager seed + tape.  The lazy/monadic denotation is a different
ontology (behaviors, not laws) and owes an adequacy theorem nobody has.

**"I need the composite's pseudocode to prove the next construction."**
Specification boundary violation.  If the downstream proof needs more than
the constructed resource's interface, the ideal resource was mis-specified;
fix the specification, don't reopen the box.

**"HEq/casts in my construction statement."**
Only `attach_comm` carries a transport (two update orders of the same
layout), and it is packaged.  Any other cast in a statement means objects
were placed on the wrong floor — usually a missing `Services` declaration.

**"The statement can mention lawOf/.val/flatten."**
That is the embedding plumbing.  If a hypothesis needs the kernel's
equivalence, it enters through the marked Bridges section
(`sampleInit_eq_iff`, `sampleInit_eq_of_flatten_equivalent`) — cite those,
don't inline their content.

## Worked examples

Both live in the tree, axiom-clean, and are the templates to imitate:

- **`Jost/SecureChannel.lean` + `Systems.lean` + `Construction.lean`** —
  Jost §2.2.6 (Prop 2.2.17): rung-1 leaves, the reduction pattern, the
  Φ-transport.  Full walkthrough with floor tags:
  [references/jost-worked-examples.md](references/jost-worked-examples.md) §1.
- **`Jost/OTP.lean`** — the rung-3 identity: laws with disjoint supports,
  same resource; the four-worlds transcript invariant; the bridge.
  Walkthrough: [references/jost-worked-examples.md](references/jost-worked-examples.md) §2.

Discovery, in order: `RandomSystems/Jost.lean` (layer map + surface table) →
`sketches/jost-2-2-6.md` (the audit verdict and both proof designs, with
dead ends) → `CHEATSHEET.md` → `DESIGN.md` §10.8–10.11 (the kernel contract
and the declare-at-RS/prove-by-lifting method) → `RandomSystemsCC/
LiftingExample.lean` (the ⟪R⟫—[π]→⟪S⟫ pattern for AC-level statements).
