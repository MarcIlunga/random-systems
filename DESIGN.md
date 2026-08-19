# Design — Random Systems in Lean 4

Single design document for the repository.  Tracking (what is done, what is
open) lives in `STATUS.md`.  This file consolidates and supersedes the former
`BLUEPRINT.md`, `design/*` (CR18 API changes, deviations, formalization
checklist, system-views sketch, next-gen modeling notes), and the H-technique
`MIGRATION.md`/`FLIP_PLAN.md`/`AUTOMATION.md`/`COMPONENT_ROADMAP.md`/
`SOURCE.md` (2026-07-02 consolidation; full historical detail is in git
history).

Pen-and-paper notation and exposition are governed by
[FOUNDATIONS.md](FOUNDATIONS.md).

## 1. Sources and scope

**Pen-and-paper convention.** Before defining a research game,
representative, coupling, virtual certificate, or transcript statistic, follow
[FOUNDATIONS.md](FOUNDATIONS.md). That document preserves the
Maurer--Lanzenberger definition order and notation and marks every repository
extension separately.

**Primary-source rule.** Repository notes, OCR, and extracted text are
navigation aids only.  Before attributing a definition, theorem, hypothesis,
or proof step to a source, check the relevant pages in the original PDF,
including the proof and any conventions used elsewhere in the document.  If
the PDF is unavailable, say so and do not present the attribution as verified.

Formalized sources:

- **Maurer 2002**, *Indistinguishability of Random Systems* (EUROCRYPT) —
  behaviors, the original random-systems definition.
- **CR18**: Maurer, *Cryptography Foundations* lecture notes 2018
  (`papers/CR18_LN.pdf`; extracted text is navigation only) — DDS/PDS,
  transcripts, games/MBOs, Theorem 4.17, Lemma 4.19 switching.
- **LanMau20 / Lanzenberger thesis** — systems as transcript-law equivalence
  classes, `Adv` as a supremum over transcript distances, coupling.
- **MPR07** — indistinguishability amplification (legacy tree).
- **GegMau26**: Gegier–Maurer, *Event Algebras and Applications to
  Cryptography* (ePrint 2026/1071, `papers/2026-1071.pdf`) — events as
  monotone predicates on the forest of evolutions of a discrete-step model;
  event algebras (co-Heyting lattice + linear-occurrence axiom E5) capture
  them exactly (Birkhoff duality); universal event inequalities;
  probability as a valuation applied last.  Adopted as a design guide for
  the converter trace-tree layer and the games/bad-event vocabulary
  (§10.6); *not* a replacement for the indistinguishability core (the paper
  itself scopes UEIs away from indistinguishability-style statements).

**Scope rule (CR18).** Only *pure random-systems facts* are in scope:
DDS/PDS/behavior, their algebra (composition, converters, filters), advantage
and statistical distance, games as systems-with-MBO, conditional equivalence
and switching.  Computational problems/reductions (CR18 Ch4 §4.1–4.9),
constructive cryptography (Ch5), and scheme primitives (Ch2) belong to other
libraries and are deliberately absent.

**Theorem naming rule.**  The leaf name of every new `theorem` or `lemma` is
ASCII lowercase `snake_case` (digits and a final apostrophe are allowed when
mathematically meaningful).  Names describe the proposition, almost as a
sentence: use logical words such as `_iff_`, `_eq_`, `_le_`, and `_of_`, and
name the mathematical objects rather than a proof device, source number, or
notation glyph.  Namespace components may retain their type names.  If a
conjunction needs an unwieldy name, expose separate semantic projection
theorems instead of hiding several claims behind a vague name such as
`main_theorem` or `coupling_theorem`.  A public name is frozen before its proof
is integrated, and roadmap modules are audited for uppercase theorem leaves.

## 2. Architecture (post-flip, 2026-07-02)

One glob-built library, `RandomSystems` (lakefile: `.andSubmodules`):

```
RandomSystems/
  Dist, DistSimp(Attr), StatDist, Coupling,           -- probability core
  CompatibleCount, Transcript, Instances/{URF,URFfunEval,URP},
  PDS, PFunDDS, GameOf, …                             -- PFun/CR18 surface (former NextGen)
  CR18Names                                           -- canonical short spellings (ProbPDS, …)
  CR18Tactics, FixedQueryTactics, TotalityTactics, TotalityRuleSet, DistSimp
  Complexity/                                          -- game-based complexity bridges
  HTechnique/                                          -- promoted application layer
    Surface, SecurityDefs, SoPBoundary, HashThenPRF, StrongPRP   -- public API
    All (= Surface + Tactics, legacy-free)                        -- main gate
    LegacyChecks (legacy gates + representative layer + pins)     -- compat gate
  Legacy/                                              -- pre-migration bounded API + apps
attic/                                                 -- never-buildable parked files
```

Public-surface conventions (statement-shape invariant): public H-technique /
security endpoints take **law-level** objects — `ProbPDS`/`ProbPDE`
(canonical spellings in `RandomSystems.CR18Names`), deterministic CR18
environments, fixed-query vectors, concrete application parameters, and named
transcript-space assumptions (`FiniteTranscriptSpace`; `DiscreteTranscriptSpace`
only for finite-sum lemmas).  They must not expose sample spaces, raw RVs,
probability carriers, or representative wrappers.  Enforced by
`RandomSystems/HTechnique/audit_surface.py`: forbidden header tokens, no
`private`, compatibility markers, folder build-coverage from
`All`+`LegacyChecks`, and **`All`'s closure may not import
`RandomSystems.Legacy.*`**.

Lean can't hide imports, so the promotion boundary is convention-based and
audited on theorem headers, endpoint modules, namespaces, and docs.

## 3. One system, four views (the unification design)

Four presentations of a probabilistic `(X,Y)`-system:

| View | Object | Source | In code |
|---|---|---|---|
| V1 representative | `(Ω, p, S : Ω → DDS)` | CR18 Def 3.14 | `PFunPDS.RV`, `PDSRepresentative` (LegacyChecks) |
| V2 law | `μ : Dist (DDS X Y)` weight 1 | pushforward | `PFunPDS.Prob` = `ProbPDS` — the public surface |
| V3 behavior | kernels `p(yᵢ ∣ xⁱ, yⁱ⁻¹)` | Maurer'02; CR18 Def 3.18/3.20 | `BehaviorKernel`, `BehaviorSeq`, `behaviorOf(Law)` |
| V4 observational | transcript-law class | thesis Def 2.17/Lem 2.18; LanMau20 Def 10/Lem 5 | `Prob.transcriptDist`, `adaptiveTranscriptAdvantage`, `BehaviorSeqEquiv` |

V1→V2 forgets the sample space; V2→V3 forgets interaction-invisible
correlations.  CR18 §3.6 characterizes behavior as the complete observable
behavior determined by transcript distributions.  Definition 3.20 and the
conversion following Eq. (3.2) give the cumulative reconstruction, while
Lemma 3.2 gives the transcript factorization.  Independently, thesis
Definition 2.17/Lemma 2.18 defines transcript equivalence, reduces it to
non-adaptive deterministic environments, and then identifies the equivalence
class with Maurer's conditional-distribution random system.  The Lean V3↔V4
theorem reconciles these source presentations in the repository's explicit
`Option`/`s⊥` model.
Categorically: `D` = finite distribution monad; V2 is the co-Yoneda collapse
of V1 (`D(DDS) ≅ ∫^Ω D(Ω) × (Ω → DDS)`); V3/V4 is the final coalgebra of
`F(S) = X → D(Y × S)`, i.e. behavioral equivalence — the automata analogy
(many machines, one language, minimal automaton as canonical representative)
is exact.  The H-technique is V3/V4-invariant, which is why the law-level
surface is its right home.

**Modeling priority (2026-08-01).**  The semantic object for new random-system
arguments is Lanzenberger's V4 object: an observational equivalence class of
PDS laws.  Proof design should start by exploring the class's PDS
representatives and the couplings between them.  A full random table, a lazy
tape, a block-first law, and a recursively branch-coupled law can be different
PDSs representing the same random system.  CR18's partial-function carrier and
namespaces remain useful implementation machinery, especially for partial
systems and transcript factorization, but they are not the canonical model and
must not dictate the representative choice.  At a public theorem boundary,
state the result on random-system behavior or explicitly quantify the chosen
Lanzenberger representatives; mention CR18 only when an implementation detail
or a genuinely stronger partial-system semantic is load-bearing.

Lanzenberger's honest arbitrary-weight distributions remain nonnegative.  They
allow common parts, answer-selected successors, and residual branches whose
weights are not one; they do not themselves license negative PDS mass.  The
canonical linear envelope is nevertheless sound: a **virtual PDS** is a finite
signed combination of DDSs, and virtual equivalence is equality of every
transcript pushforward.  For normalized finite common-domain systems, the
infimum half-`L1` distance over signed equivalent representatives is exactly
the distinguishing advantage.  Pushforward contraction proves the lower
bound, and Lanzenberger's honest attainment theorem proves the reverse bound.
Thus signed gain-graph, Fourier, Möbius, or ANOVA representatives cannot cheat
the operational distance and may be used directly as distance certificates.
This does not make them quantitatively redundant: by delaying absolute values
and exposing cancellations, they may lower the best upper bound we can
currently prove, even though the exact infimum itself remains `Adv`.  Searching
for such a tractable near-optimal certificate is the main reason to enlarge the
representative language.
Combine all coefficients of each atom before taking an `L1` norm.  Pass to
Jordan positive/negative subdistributions only when an honest PDS or literal
coupling is required; signed joints are not operational couplings and general
normalized conditioning fails.  The source audit and full design are in
`sketches/signed-virtual-pds.md`.

**Compiled linear layer (2026-08-03).**  Do not introduce a second
`VirtualDist`: current `Dist A` is already `A →₀ ℝ`.  Use
`Dist.virtualL1`, `Dist.virtualDistance`, and
`CR18.virtualPDSDistance` from `VirtualPDS.lean`.  The theorem
`advantage_le_virtualPDSDistance_of_equivalent` is the non-cheating boundary;
`virtualClassDistance_eq_advantage_of_exists_honest_attainment` isolates the
exactness step supplied by honest attainment.  The signed-`Real` migration of
`BoundedAttainment.lean` is complete, so
`virtualClassDistance_eq_advantage_of_finite_common_domain_and_bounded` now
composes the two layers into the unconditional exact theorem on the source
class (finite query alphabet, one support domain, uniformly bounded depth).
The first concrete visible-law instantiation is
`SoP/XORVirtualRepresentative.lean`.  It must continue to be described as a
fixed-transcript certificate unless a construction proves one signed PDS
representative works for every environment.

**First compiled signed-cancellation instance (2026-08-03).**
`SoP/XORSignedTruncation.lean` partitions the exact XOR SoP likelihood into an
arbitrary signed low-level prefix and an orthogonal tail.  It combines the
prefix pointwise before any absolute value and applies Cauchy--Schwarz only to
the unretained tail.  `SoP/XORSignedDegreeThree.lean` evaluates the first
nontrivial prefix, levels two plus three, exactly in the sparse sign range.
This is the modeling pattern to reuse: retain a tractable signed prefix,
classify its sign regions, compute its L1 norm there, and bound only the later
tail.  The signed prefix is a distance certificate, not a probabilistic
coupling; the final endpoint is nevertheless the ordinary adaptive random-
system advantage.  The module also proves the resulting closed certificate is
below the former `min(sparse,dense) + remainder` endpoint throughout that
range, strictly so for three or more queries; certificate comparisons should
be exported as theorems rather than left as numerical observations.

**Planned unification (not yet implemented):** characteristic-predicate style
first, quotient capstone later.

- U1 `Behavior/Core`: `Prob.behavior : Prob X Y → BehaviorSeq X Y` (from
  `behaviorOfLaw`), `BehaviorEq`, `IsBehaviorOf`.
- U2 `Behavior/Observational` — the heart, theorem **(B)** (the CR18 §3.6
  behavior/transcript characterization in the law-level model):
  `BehaviorEq S T ↔ ∀ q, ∀ q-total deterministic E,
  deterministicTranscriptDist S E q = deterministicTranscriptDist T E q`.
  (⇒) via the Lemma 3.2 factorization (`transcriptLaw_eq_systemFactor_mul_environmentFactor`,
  `transcriptCond_eq_behaviorOf`, needs a law-level restatement); (⇐) by
  reconstructing kernel entries from `fixedQueryDDE` transcript masses — the
  `Part NNReal` fn14 conventions must match the transcript zero conventions;
  a `KStepTotal` proof may be retained as a restricted intermediate result for
  current applications, but CR18's final statement must cover its general
  partial-`DDS`/observable-`⊥` semantics.
- U3 `Behavior/Descent`: `transcriptDist_congr`,
  `adaptiveTranscriptAdvantage_congr`, HTechnique `Adv/advPRF/fixedQueryAdv
  _congr`, `filteredDelta_congr`.  Legacy `advantage_respects_equiv`
  re-derived as a regression pin.
- U4 `Behavior/Atlas` — theorem **(A)** and round-trips:
  `Dist.PMF`/`ofProbPDS` section-retraction, and the presentations theorem
  `BehaviorSeqEquiv p S p' S' ↔ BehaviorEq (PMF p S) (PMF p' S')`
  (`BehaviorSeqEquiv` already crosses sample spaces).
- U5 `System.lean` (optional): `System := Quotient lawBehaviorSetoid`,
  endpoints by `Quotient.lift` over the U3 lemmas; thesis Def 2.17 / LanMau20
  Def 10 becomes a theorem.

Decision rationale: predicate-first avoids `Quotient.lift` boilerplate across
~15 endpoints, `Finsupp` friction, and `PDSRepresentative.Ω : Type w`
universe noise.  U2 is the only real proof work.  Public statements do NOT
change shape — the atlas adds invariance theorems about the existing V2
surface.  After U4, the representative layer and the anti-drift pins are
formally *charts of an explicit atlas*, which is the final justification for
deleting `Legacy`.  Markov-category framing is a design guide only; revisit
if Mathlib's synthetic probability matures.

## 3a. Environment duality (implemented 2026-07-02, `Derivation.lean` Layer A′)

The two formalized sources disagree on the environment carrier, and the Lean
follows CR18:

- **Thesis Def 2.11**: a DDE is `e : Y* ⇀ X`, a partial function with
  prefix-closed domain — a DDS-shaped object on the swapped alphabet.  The
  duality is exact up to one shift: an `(X,Y)`-environment must also answer
  the *empty* history (it moves first), so morally
  `Env(X,Y) ≅ X × DDS(Y,X)` — first query plus a dual system one round
  behind (`xᵢ = e(y^(i−1))`, `yᵢ = s(xⁱ)`).
- **CR18** (implemented; docstring cite at `PFunDDS.lean` `DDE`):
  `e : (Y ∪ {⊥})* → X ∪ {⊣}`, i.e. `DDE X Y = List (Option Y) → Option X` —
  a *total* function on a marked alphabet (`⊥` = system undefined, `⊣` =
  stop).

Why the CR18 carrier was the right engine (do not swap it):

1. no `Valid`-style side-condition bureaucracy on the environment side
   (environments are bare functions);
2. the first query at the empty history is free (a strict dual `DDS(Y,X)`
   cannot answer `ε`; the migration ledger recorded this exact bug);
3. transcript events stay separable under *partial* systems: the `Option Y`
   history entries make the environment event total on one carrier, which is
   what makes the Lemma 3.2 factorization one `mass_prod_and` step instead
   of an induction — the H-technique derivation depends on this.

Reconciling fact: **in the total regime the models coincide.**  Every
H-technique endpoint assumes `KStepTotal`/`DDEKQueryTotal`, under which only
all-`some` histories of length `< q` are consulted; a `q`-query-total DDE is
exactly the positive, dual-shaped chooser data
`choose : (i : Fin q) → (Fin i → Y) → X`, which already exists in the code
as the `boundedDDE`/`boundedEnvironment` family (with
`boundedEnvironment_KQueryTotal` as one direction).

**Planned (duality-as-theorem, another chart in the atlas — not a carrier
refactor):**

- `QQueryEnvironment.equivChooser :
  PFunPDE.QQueryEnvironment X Y q ≃ ((i : Fin q) → (Fin i → Y) → X)` —
  forward map is `boundedDDE`/`boundedEnvironment` + its totality lemma;
  inverse reads the environment on concrete histories (total by `E.2`);
  round-trips are the new content.
- Optional thesis-literal split: peel off `i = 0` to exhibit
  `chooser ≅ X × (bounded (Y,X)-system data)` — "environments are duals of
  systems, one round behind" as a named equivalence.
- A transport lemma expressing `deterministicTranscriptDist S E` through the
  chooser view, so statements can be *written* in the dual vocabulary while
  the CR18 carrier remains the engine.

This slots beside §3 as the environment-side mirror of the views/atlas
program: same philosophy — add the chart, don't rebuild the manifold.

## 4. Statement and proof policies (hard-won; each broke something once)

1. **Decidability policy** (documented at the top of `Dist.lean`): file-wide
   classical instances serve *proofs* only.  Any lemma whose *statement*
   contains a decidability-dependent term (`Finset.filter`, `if`) takes the
   instance as an explicit binder, so the statement instantiates with the
   caller's ambient instance and `rw`/`simp` match in both classical and
   `[DecidableEq]` files.  Violation symptom: rewrite-pattern failures and
   instance-bridging `congr`/`convert` noise (this caused most of the
   post-toolchain-bump rot).
2. **Simp normal form is an API decision.**  Domain vocabulary
   (`vectorOfFunction`, …) is the normal form; Mathlib-direction bridges stay
   named, non-simp.  Tagging bridges `@[simp]` flips goals out of the
   vocabulary statements use.
3. **Alias with `export`, never `abbrev`-wrappers, when deduplicating.**
   Wrappers are new constants and silently break `simp only [old_name]`
   downstream (`SoP/Basic` broke this way).
4. **Side-condition tactics run at reducible transparency** and lemma heads
   must match goal heads syntactically.  Default-transparency `first`-chains
   over large system laws hit whnf heartbeat timeouts.
5. **`first`-chains swallow unknown identifiers** — an unresolvable name in a
   branch is a silent dead branch, not an error (bit `htechnique_total`
   once).  Smoke-test each branch when writing chained tactics.
6. **Name-capture on promotion**: promoting a short name into a parent
   namespace re-resolves unqualified uses in open-namespace files, silently
   and type-compatibly (`RandomSystems.transcriptOutputs` captured the XoP
   one).  Grep unqualified uses before promoting any name.
7. **Section-variable auto-inclusion** (Lean ≥4.29) adds phantom instance
   requirements to lemmas that don't mention them; audit `variable` lines
   when moving declarations (`Coupling.lean` lesson).
8. **New shared "obvious" lemmas are simp-/rule-set-tagged at birth**, and a
   proof repeating a 3+-step rewrite chain from another proof is a bug:
   extract it into the tactic layer.
9. **Attributes must cite a firing site.**  Item 8's tag-at-birth is
   provisional: at each polish pass, strip-test the pack — an attribute no
   `simp`/`grind` call exploits is demoted to a plain named lemma (named
   `rw`/`simp only` uses survive).  HCTR2's M3.5 pass demoted 21 of 28 this
   way; each survivor has a cited consumer (STATUS §7.1).  Corollary: for
   proof-*shape* dedup prefer a lemma (`pairMass_le_of_reveal`) over a
   macro — macros bake in hypothesis names and fail opaquely; macros are
   for goal-normalization only (`char2`, `htechnique_dist`).
10. **Never close a definitional or notation boundary with `simpa [someDef]`.**
    A `simpa`/`simp` carrying a definition also runs the *global* simp set, so
    a `@[simp]` lemma can rewrite the goal straight back across the `rw` that
    just set it up — and the break surfaces only when an unrelated `import` or
    `open scoped` elsewhere in the file changes normalization, hundreds of
    lines from the edit.  `Derivation.lean`'s
    `deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good` broke this
    way: after `rw [← transcriptDist_ofDDE, ← transcriptDist_ofDDE]` the goal
    already *was* the hypothesis, but `simpa [transcriptDist]` re-applied the
    global `@[simp] transcriptDist_ofDDE` and undid both rewrites.  The fix was
    `exact h`.  Prefer `exact`/`exact_mod_cast`, then a named `rw`, then a
    closed `simp only [...]` list; a bare definition name in a simp set at such
    a seam is the smell.  (Same family as items 2 and 6: what breaks is always
    *action at a distance* through a global set or a re-resolved name.)
11. **Do not totalize what the source leaves partial.**  Four defects in the
    RS↔AC bridge trace to exactly this move, and none to anything else
    (`STATUS.md` §11.4–11.5): quotienting the converter monoid by action-
    equality made `Par` ill-posed, because MauRen11 fn. 23 leaves `α ∥ β`
    *junk* off `‖`-shaped resources while action-equality quantifies over all
    resources; a default identity branch for a converter at a mismatched code
    turns a misplaced converter into a **true but vacuous** theorem; and
    totalizing the parallel action the same way makes par-act non-expansion
    outright **false**, since `∥` is not surjective and the identity branch
    moves one point while pinning a nearby one.  When a paper says a value is
    unconstrained, that is a *domain restriction*, not permission to pick one —
    picking one silently extends every theorem to inputs the source never
    considered.  Prefer a partial operation with an explicit applicability
    hypothesis, or restrict the carrier to the operation's natural domain.
12. **`IsDDC (PFunConverter.par α β)` is false in general.**  The tagged
    parallel converter drops untagged `⊥`s and mis-tagged answers in its
    `filterMap` projections, so a component re-issues its query forever at
    reachable junk pairs and `AnswersWithin` fails for *every* bound.  Route a
    parallel action through the fixed-component realization theorems in
    `RandomSystems/StrictParallel.lean`, never through the raw par converter.

13. **A carrier whose `HasResourceCode` heads can unify must pin the winner
    and name its codes.**  `HasResourceCode U X Y` places a law by its
    *alphabets*, so two instances on one carrier can have heads that unify
    under some instantiation of the model's type variables — CBC's
    `(interfaces X M) X X` and `(interfaces X M) M X` collide at `M = X`.
    Question the reflex to call this a diamond bug: resolution is
    deterministic and cached per head, so at the collision *every* occurrence
    collapses to the priority winner **together**.  The statement is therefore
    the same mathematics under the other of two labels for one signature — not
    a false statement (checked empirically, not argued: the overlap resolves to
    `variableInputFunction`).  What it is not is what the author wrote, and
    placement is observable (`Resource.mk` is injective in its code).  So the
    fix is not deletion — the instances are load-bearing, since a
    `DDConverter` action recovers its source and target codes through them, and
    deleting one kills the converter algebra.  It is: (i) a **resolution pin**
    (`CBCMAC.overlap_resolves_to_variableInputFunction`) so a priority change is
    a compile error rather than a silent relabelling, and (ii) `liftProbAt` /
    the carrier's `liftVIF` at every statement boundary whose intent matters.
    `liftProbAt` is a reducible alias for `liftProb` at an explicit instance,
    so every `liftProb` simp lemma still fires through it.

## 5. Automation stack

Simp sets: `dist_simp` (weights, uniform, pushforward events, composition),
`htechnique_dist_simp`.  Tactics:

- `cr18_pushforward / cr18_prob / cr18_filter / cr18_game / cr18_transcript /
  cr18_arith (gcongr-first) / cr18_simp / cr18_grind` (`CR18Tactics`);
- `cr18_fixed_query_*` (`FixedQueryTactics`);
- `cr18_total` (`TotalityTactics`) — totality side conditions for standard
  constructors, extensible via the **`Cr18Total` aesop rule set**
  (`TotalityRuleSet`; rule sets must live in their own module to activate);
  application layers tag their totality lemmas at definition sites;
- `cr18_adv_le` / `htechnique_adv_le` — advantage-supremum shells down to
  pointwise transcript bounds;
- `htechnique_fixed_query / _compress(_once) / _simp / _grind /
  _total / _adv_le` (`HTechnique/Tactics`);
- `rs.` controlled sentences (`RandomSystemsCC/ControlledNaturalLanguage`,
  scope `CryptoControlledNaturalLanguage`) — paper-facing proof *styles*
  over the frozen skeletons: condition C (Maurer 4.17/4.18) and the three
  H-coefficient forms.  Structure sentences expose the mathematical legs as
  named goals (`?good_ratio`, `?bad_probability`, `?pointwise_ratio`) and
  absorb only totality (`cr18_total`) and `NNReal` cast arithmetic; summary
  sentences cite finished endpoints.  No search; explicit citations only.

Goal: proofs read like pen-and-paper; normalization, side conditions, and
mass bookkeeping are absorbed by the stack, never assumed away.

### 5.x Derivation.lean automation audit (2026-07-02)

Drained: paired weight side conditions
(`deterministicTranscriptDist_weight_eq`/`_le_one` replace 4 inline
`rw`-pairs); the singleton-shrink pointwise transfer is now the lemma
`deterministicTranscriptDist_ratio_of_fixedQuery_ratio_at` (used by the
expectation and partition endpoints).

Implemented (2026-07-02, second pass):

- **mass bundle in `CR18Tactics.lean`**: `cr18_mass_expand` (probBad/mass/
  weight/Finsupp.sum → Finset sums), `cr18_sum_swap x` (sum_comm +
  pointwise congr, binder named), `cr18_ite_collapse` (ite-fiber sums).
  Deployed in `Derivation.lean` (σ⁺ partition, partition-lemma regroup,
  mass_mono, mass split); remaining candidate sites (DPI step 3, coupling
  tail) keep bespoke shapes inside calc blocks.
- **RS-specific grind instrumentation**: `@[grind =]` on the Derivation
  equation lemmas (`deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor`,
  `envFactor_eq_indicator`, `envFactor_fixedQueryDDE`,
  `extendedDeterministicTranscriptDist_apply`, weight-one, A.1 identities,
  `lawStatDist_eq_statDist`).  Wins: `deterministicTranscriptDist_weight_eq`,
  `…_weight_le_one`, and `extFixedQueryTranscriptDist_self` are now `by
  grind` (the last replacing a 3-step rw/simp chain).  Annotate new
  equation lemmas at birth.

### 5.y Tactic radar — Lean v4.29 / current Mathlib survey (2026-07-02)

Enumerated via `#help tactic`; tested on live Derivation goals.  Adopted:

- **`grw` / `grewrite`** (generalized rewriting along `≤`): replaces
  `le_trans _ (add_le_add …)` finales — "substitute a bound into an
  inequality" reads like paper.  Deployed at 4 finale sites in
  `Derivation.lean` (`grw [h_ext, h_bad E] at h_proj`).
- **`bound`** (recursive inequality prover: gcongr ∪ positivity ∪
  norm_num): closes NNReal product/sum bounds given the key fact as a
  local `have` (its lemma-argument form cannot elaborate underscored
  side facts).  Deployed in the two-cell special case.
- **`grind?` → `grind only [...]`**: suggestion mode emits minimized
  configurations; the weight side conditions now use
  `grind only [= deterministicTranscriptDist_weight_eq_one]` (faster and
  drift-stable vs bare `grind`).  Use `grind?` during development, commit
  the `only` form.

On the radar (relevant, not yet load-bearing):

- `order` — order-theoretic closer from hypotheses (tested green on NNReal
  antisymmetry); use for ≤/=-shuffles where `le_antisymm`/`le_trans`
  plumbing accumulates.
- `fun_induction` / `fun_cases` — functional induction for recursive defs;
  natural fit for `concreteOutputHistory`/transcript-recurrence proofs in
  the core when next touched.
- `plausible` — property-based counterexample search; run on candidate
  statements before proving (esp. Thm 2.31 attainment intermediate lemmas).
- `peel` — quantifier-matching transfer between hypothesis and goal
  (`h_ratio`-shaped ∀-chains).
- `lift` — carrier lifting (NNReal ↔ ℝ) as an alternative to
  `exact_mod_cast` boundary hops.
- `cutsat` / `lia` — grind's linear integer solver, standalone; Nat/Fin
  index arithmetic only (NNReal out of scope).
- `grobner` — grind's ring solver, standalone; needs (comm) rings, so not
  NNReal, but flag for ℝ-valued advantage algebra.
- `bv_decide` / `bv_omega` — SAT-backed bitvector decision; flag for
  block-cipher-level facts in HCTR2-style applications.
- search/dev tools: `exact?`, `apply?`, `rw_search`, `rw??`, `hint`,
  `try?`, `observe` — exploration only, never committed.

Not applicable to this library: `finiteness` (ENNReal), `polyrith`/
`linear_combination`/`field_simp` (rings/fields), `module`/`match_scalars`,
`mvcgen` (monadic do-programs), category/coherence tactics.

Open / negative results:

- `sum_extSysFactor` is **not e-matchable** (`Z`/`aug` appear only on one
  side each) — no grind attribute; use it by name.
- grind does **not** close NNReal truncated-sub goals (two-cell ratio
  branches, tried 2026-07-02); keep `by_cases … <;> simp` there and do not
  re-try without new grind extensions.
- The adaptive endpoints all open with `adaptiveTranscriptAdvantage_le_of_pointwise
  … ; intro E`; if a third file grows this shape, absorb into `cr18_adv_le`.

## 6. CR18 deviations register

Recorded **only** when the lecture note itself is unsound; implementation
bugs against a correct note are fixed, not recorded.  Each deviation is also
marked in code with `-- DEVIATION FROM CR18 (<id>): …`.

### 4.8 — Bit-guessing performance mis-calibrated (`−1/2` should be `−1`)

- **Maurer says** (Def 4.8, Def 2.9, §2.3.1): `Λ_D(S,B) = 2·Pr[κ(D,S)=B] − 1/2`.
- **Why wrong:** an always-correct guesser gives `Λ = 3/2 > 1`, contradicting
  the same definition's "performance is between −1 and 1" and "1 ⇔ correct
  w.p. 1"; the Lemma 2.3 chain `Λ_D(S_U,U) = Δ_D(S₀,S₁)` only closes with
  constant `1` (perfect distinguisher: `−1/2` formula gives `3/2 ≠ 1`).
- **We do:** `Λ_d(S,B) := 2·Pr[κ(d,S)=B] − 1`, matching the prose anchors and
  Lemma 2.3.  Found by contrarian review, 2026-06-09.  *(The marker lived in the
  retired `Legacy/CR18` core, deleted 2026-07-28; the deviation itself stands —
  the live bit-guessing development is `RandomSystems/Complexity/BitGuessing.lean`.)*

(New entries follow the same format: Maurer says / why wrong / what we do /
marked in / found by.)

## 7. H-technique modeling anchors (retained from the migration ledger)

- CR18 §3.6.5 / Lemma 3.2: transcript-prefix laws factor into system ×
  environment factors; the environment side is a random DDE over optional
  output histories, so the first query is `E() = x₁`.
- CR18 §4.10.2 / Thm 4.17: the game/distinguishing bridge must use the
  filtered or per-winner bounds, never an unfiltered `Γ` shortcut.
- CR18 Lemma 4.19: URF/URP switching routes through filtered Theorem 4.17
  (`SwitchingLemma`), with the numeric step in shared counting
  (`CR18.Counting.switching_ratio_le`).
- LanMau20/SoP: the SoP proof reduces adaptive advantage to a fixed visible
  transcript law, then to the orbit/counting bound (`q³/|G|²`); the shared
  combinatorial core is `RandomSystems.CompatibleCount` (Mathlib-only), with
  the LM20 orbit-proof exposition preserved at
  `papers/notes/LM20_ORBIT_PROOF.md`.

## 8. CR18 PFun modeling discipline (operative rules; formerly AGENTS.md)

- **Stay close to the paper** (`papers/CR18_LN.pdf`; use
  `papers/CR18_LN.txt` only for navigation).  If the Lean proof stops
  resembling Maurer's, the *model* is wrong, not the proof.  A hard
  "constructed object = intended object" bridge is a modeling smell:
  re-model; Maurer's random-variable/sequence views usually make the event
  separable or the equality definitional.
- **Algebraic, not operational.**  Equational definitions and notation over
  helper functions; no simulation loops or fuel-bounded interpreters as
  public models — finite transcripts/histories are private proof witnesses.
- **No speculative scaffolding.**  No helper predicates/wrappers without a
  paper definition and an immediate consumer; delete unused ones.
- **Types carry the math.**  Payloads in products, never payload-carrying
  constructors; match lengths in types; public APIs expose paper objects
  (DDS, DDC, filters, behaviors, transcripts), never implementation devices.
- **Converters**: a DDC is a DDS over converter alphabets; application is the
  DDS-level `DDC.apply` (Def 3.9); filters are converters; paper-facing
  converter equations are extensional DDS equalities against the *actual*
  converter (never redefine the converter side to force `rfl`); if raw-history
  parsing degenerates, add typed canonical prefix descriptions.  Notation
  roles stay distinct (`⊲ₚ`, `·ᶜ`, `cascᶜ[…]`, `⋆ₚ[…]`).
- **§3.6 behavior/transcripts**: behavior and cumulative behavior are
  kernels over DDS samples, length-matched; reuse the `outSeq`/`prevOut` API
  and add new list↔index bridges as NAMED lemmas; telescoping via
  `mass_biForall_lt_eq_prod` (NNReal has no `CommGroup` for
  `prod_range_div`); model the transcript as Maurer's list of RVs
  (`Yᵢ = S(x¹…xⁱ)`, `Xᵢ = E(yⁱ⁻¹)`), not the deterministic recurrence — this
  makes Lemma 3.2 factor in one step via `Dist.mass_prod_and`.
- **Games ride the exclusion chain, no side predicates**:
  `Raw —Valid→ DDS —IsGame→ DDG`, `PDG = RV valued in DDG`; `IsMBO` is a
  property of `List (Y × Bool)` (monotone bit), the system never appears in
  it; a winner IS a `(Y,X)`-environment (`Winner := DDE`); a distinguisher is
  `{d : List (Option Y) → X ⊕ Bool // StopFinal d}` (verdicts are final).
- **Notation**: PDS/PDE uppercase (`S`, `E` — random variables), DDS/DDE
  lowercase (`s`, `e` — deterministic values).

## 9. H-technique re-derivation on the RS surface (implemented 2026-07-02)

Status: implemented in `RandomSystems/HTechnique/Derivation.lean`
(`RandomSystems.CR18.HTechniqueDerivation`, in the `All` gate): Layers B–E as
designed below, plus the (★) identity (named `sysFactor`/`envFactor`), the σ⁺
fixed-query refinement (Layer E′ — event-mass construction
`extendedDeterministicTranscriptDist`, no pushforward needed), the
fundamental-theorem lower bound (Layer F — `lawStatDist` support-based law
distance, transcript DPI `statDist_deterministicTranscriptDist_le_lawStatDist`,
`Adv ≤ Δ_q` via `adaptiveTranscriptAdvantage_le_lawDelta`, coupling reading
`adaptiveTranscriptAdvantage_le_mass_ne`), and the environment-duality chart
(Layer A′, §3a).

**Extension mechanism (final form, 2026-07-03).**  Extensions are
representative-level and transcript-dependent: for a law presented as
`Dist.PMF p F` with representative `(Ω, p, F)`, a reveal is any function
`aug : Ω → TranscriptPrefix → Z`, and

    tr⁺(p,F,aug,E)(t,z) = p{ω : F ω ⊩ t ∧ aug ω t = z} · η_E(t)

(`Derivation.lean` Layer E″: `extSysFactorRep`, endpoints
`adv_le_of_extFixedQueryRep_{ratio,eq}_on_good`).  Design rationale:
(i) sample-level is forced — the hash-then-PRF key is not a function of the
induced oracle; (ii) transcript-dependence is forced — HCTR2's extended
transcripts reveal the internal block-cipher pairs *used in answering the
queries*; (iii) randomized reveals (HCTR2's ideal world samples dummy
internals conditioned on the transcript) are absorbed by enlarging the
representative with coins — `(Ω × C, p ⊗ uniform, F ∘ fst)` presents the
same law.  The event-mass construction handles adaptivity with no
run/pushforward map; extensions are honestly representation-dependent data
(V1), which the theorems tolerate since only existence is needed.

**Completed: Thm 2.31 attainment direction** (2026-07-20).
`RandomSystems/BoundedAttainment.lean` proves the source theorem under the
rendered-PDF hypotheses: finite `X`, one support domain, and a uniform bound
on answered-query depth. It uses law successors `S^{x↓y}`, finite realized
answer reassembly, a Lemma 2.33 cross-query joint preserving distinct common
left/right masses, and an adaptive per-answer witness environment. It returns
equivalent representatives with `δ_law = Adv` and derives class-distance
equality. `RandomSystems/RandomSystemCoupling.lean` then derives the normalized
Theorem 2.32 coupling. No unrestricted varying-domain version is asserted:
`RandomSystems/AttainmentCounterexample.lean` proves that such an equality is
false under CR18 observable-rejection semantics. The pre-migration
`Legacy.FundamentalTheorem` admission remains quarantined rather than serving
as a dependency of this result.

### 9.0 Original design (for reference)

Thesis anchors (Lanzenberger, `papers/thesis (1).pdf`, checked against rendered
original pages; extraction is navigation only):
Def 2.9/2.11/2.12 (DDS/DDE/`tr`), Def 2.14 (PDS = general nonneg
distribution over DDSs, one shared domain), **Def 2.17** (`S ≡ T` iff
`tr(S,e) = tr(T,e)` for all *deterministic* compatible DDEs; probabilistic
environments give the same relation), **Lemma 2.18 + App. A.1**
(*non-adaptive* deterministic environments suffice for ≡; proof: for a fixed
transcript `t̂`, the system-side event `{s : tr(s,e) = t̂}` equals
`{s : ∀ i, s(x̂ⁱ) = ŷᵢ}` — independent of how `e` chose the `x̂ᵢ`),
Def 2.26 (`Adv` = sup over deterministic DDEs of transcript `δ`),
Def 2.28 / Thm 2.31 / Thm 2.32 (`Δ = Adv`, attained; coupling theorem),
Notation 2.34 (successor systems, the induction engine for 2.31).

Derivation chain (each step one lemma family):

0. distinguisher → transcript: verdicts are transcript events, so
   advantage ≤ `Adv`; deterministic WLOG by affinity.
1. **adversary factorization** (deterministic `e`):
   `tr(S,e)(t̂) = 𝟙[e consistent with t̂] · σ_S(x̂ˡ, ŷˡ)` where
   `σ_S(x̂ˡ,ŷˡ) := S{s : ∀ i, s(x̂ⁱ) = ŷᵢ}` is the **system factor**, and
   `σ_S` *is* the non-adaptive (fixed-query) transcript mass.  This is the
   deterministic-`e` specialization of CR18 Lemma 3.2.
2. transcript distance with the adversary factored:
   `δ(tr(S,e),tr(T,e)) = Σ_{t̂ e-consistent} max(0, σ_S(t̂) − σ_T(t̂))` —
   all pointwise hypotheses are therefore *non-adaptively checkable*;
   adaptivity only selects which fixed-query events are summed.
3. H-technique as pure distribution facts on transcript space (bad event
   `B`, equal weights ≤ 1): one-sided `δ ≤ Pr_Q[B] + ε` from
   `(1−ε)·Q ≤ P` off `B`; ratio and expectation variants
   (`δ ≤ Pr_Q[B] + E_Q[ε(·)·𝟙_{¬B}]`).  Lift: hypotheses at σ-level
   (fixed-query), conclusion uniform in `e`, hence a bound on `Adv`.
   Residual per-`e` dependence sits only in `sup_e Pr_{tr(T,e)}[B]`,
   bounded separately (birthday/union arguments on the ideal side).
4. `Δ = Adv` (Thm 2.31, bounded common-domain successor induction), followed
   by the probability-level optimal coupling of Thm 2.32.

Lean mapping (pieces mostly exist; the re-derivation *names the chain*):
step 0 = `AdaptiveLawBridge` verdict/advantage lemmas + `mass_tsub_mass_le_statDist`;
step 1 = `deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor`
+ `sysFactor_eq_fixedQueryTranscriptDist_self`; step 2 =
`statDist_deterministicTranscriptDist_eq_sum_fixedQuery_gap`; step 3 =
`RandomSystems.hTechnique_{ratio,expectation,eq_on_good}` /
`oneSided_hTechnique` (`StatDist.lean`) lifted by the
`adv_le_of_fixedQuery_{ratio,eq_on_good,expectation,partition}` family
(`HTechnique/Derivation.lean`);
**(names corrected 2026-07-27 — the three above were planned names that drifted;
`systemFactor_eq_fixedQueryTranscriptDist` and `oneSided_hTechnique_adaptive`
do not exist.  This paragraph was a plan, and was read for years as a receipt.)** step 4 =
`BoundedAttainment.lean` plus `RandomSystemCoupling.lean`, with
`Coupling.lean` supplying the arbitrary-carrier finite-support coupling
bridge.

**Extended transcripts** (same file of ideas, Patarin/Chen–Steinberger
"reveal the key"): choose per-side extensions `aug_S, aug_T : DDS → Z`
(deterministic aux info; kernel extensions reduce to this by enlarging the
sampled object).  Define
`tr⁺(S,e) := pushforward of S under s ↦ (tr(s,e), aug_S s)` on `T × Z`.
Facts: (i) `fst`-projection recovers `tr(S,e)`; (ii) data processing
(Lemma 2.7 / `statDist_fTransform_le`):
`δ(tr(S,e),tr(T,e)) ≤ δ(tr⁺(S,e),tr⁺(T,e))`; (iii) factorization extends
verbatim with `σ⁺_S(x̂,ŷ,z) = S{s : ∀ i, s(x̂ⁱ)=ŷᵢ ∧ aug_S s = z}`, still
fixed-query; (iv) H-technique on `T × Z` gives
`Adv(S,T) ≤ ε + sup_e Pr_{tr⁺(T,e)}[B⁺]`.  Value: σ⁺-ratios are often
*exactly computable* (conditioning on the revealed key trivializes the real
side), at the price of a slightly larger bad event.  Lean: new core module
`ExtendedTranscript.lean` (`extendedDeterministicTranscriptDist`,
projection, DPI, extended system factor, packaged
`oneSided_hTechnique_extended_adaptive`); `HTechnique/HashThenPRF.lean`
already implements the instance (`realExtDist`/`idealExtDist` over
`(y^q, h)`) and becomes the regression consumer of the general API.

## 10. Converter application as composition; the resource view (2026-07-02)

Design + first execution of the "converters feel unfinished" drive.  The
thesis: *applying a converter creates a random system, so application must be
a partial function `List U →. V` obtained by a (nontrivial) composition of
the converter's function and the system's function* — and the paper-facing
Def 3.9 object must be **computable** for concrete converter classes, not
just well-defined.

### 10.1 What was wrong

`DDC.apply` (Def 3.9) already produces a valid `DDS U V` for *every* `(α, S)`
(no productivity side condition; undefined exactly where the inner loop
diverges), built as `π ∘ fold(round) ∘ lfp(connStep)` — so the thesis holds
*by construction*.  What was missing:

1. **Two unbridged applies.**  `DDC.apply` (transcript fixed point against
   `s⊥`) and `CausalApply.applyG` (function-native finite unrolling of a step
   function against `S.1`, the HCTR2 surface) had no connecting theorem.
2. **Vacuous converter equations.**  `cascadeViaConverter_eq_cascade` and
   `combineViaConverter_eq_combine` are `rfl` because the LHS is *defined* as
   the native operation — the exact "redefine the converter side to force
   `rfl`" smell §8 forbids.  Only `queryLimit` had a genuine apply-level
   theorem (~500 lines of bespoke trace work).
3. **No resource story.**  Def 3.9 reads the system only through Def 3.3's
   `s⊥`, but nothing named that object or proved systems embed into it.

### 10.2 The realization theorem (`StepConverter.lean`)

An **outer-memoryless** converter is presented by a *protocol step function*
`step : U → List Y → X ⊕ V` ("given the outer input and this round's inner
answers so far, issue the next inner query or answer outside") — exactly the
type `CausalApply` consumes.  `DDC.ofStep step` realizes it as an honest
Def 3.8 DDC: domain = protocol traces (parsed left-to-right by a private
`run` parser; strictness: a `⊥` answer kills the trace), value = the move
`step` prescribes at the parsed round state.  The heart is

**`apply_ofStep`:  `(ofStep step) ·ᶜ S = CausalApply.applyG step S.1`.**

Proof = two simulations with the single invariant `xs ∈ dom S ∨ xs = []`
(strictness keeps the recorded inner history live, so `keptPrefix` is the
identity and `s⊥`-answers coincide with raw `S`-answers): inner round by fuel
induction (forward) and `PFun.fixInduction` (backward, with the dead-state
contradiction for `⊥`), outer level by list induction with fuel merging by
monotonicity.  Consequences: Def 3.9 application **is** the composition of
the two component functions; the whole `CausalApply`/HCTR2 surface is
retroactively a faithful instance of Def 3.9; converter equations become
*computations* of `applyG` (list inductions), never transcript arguments.

Computation rules proved on top (all extensional `Part`/DDS equalities,
domains included, against **arbitrary** systems):

- **Simple converters** (Maurer's word, Def 4.20): `simple c d :=
  ofStep (query `c u`, answer `d y`)`;
  `simple_apply : ((simple c d) ·ᶜ S) us = (S (us.map c)).map d` — for
  `d = id` literally `S(c(input))` (`simple_id_apply`); domain form
  `simple_apply_dom`; stateless instance `simple_functionEvaluator :
  simple c d ·ᶜ ⌜f⌝ = ⌜d ∘ f ∘ c⌝`.  Validity of `S` is what collapses the
  per-round domain conditions to the single condition `us.map c ∈ dom S`.
- **Interactive (two adaptive rounds)**: `feedback g := ofStep (query x,
  query g y₁, answer y₂)`;
  `feedback_apply_singleton : (feedback g ·ᶜ S) [x] = S[x] >>= fun y₁ =>
  S[x, g y₁]` on arbitrary *stateful* `S` (the round structure as a bind),
  and `feedback_functionEvaluator : feedback g ·ᶜ ⌜f⌝ = ⌜f ∘ g ∘ f⌝` (full
  DDS equality).

### 10.3 The resource view (`ResourceView.lean`)

What a converter interacts with is `⟦S⟧ := S⊥` — a *fully defined*
`(X, Y∪{⊥})`-system.  Proven:

- `fullyDefined_inj` / `fullyDefined_injective`: `S` is recoverable from
  `S⊥` (reverse-history induction; `dom S` = histories whose nonempty
  prefixes all answer `some`), so systems **embed** into resources and the
  factoring `DDC.apply_congr_resourceView` (`S⊥ = T⊥ → α·ᶜS = α·ᶜT`) is
  exact: the resource view is the whole interaction-relevant content.
- `unitResourceEquiv : DDS X Y ≃ Resource Unit X Y` — a DDS *is* a CR18
  Def 3.5 resource with a single interface (history reindexing).
- Probabilistic lifts (law level, mass-preserving): `PFunPDS.applyDDC`
  (pushforward of the deterministic apply — "applying a converter creates a
  random system"), `PFunPDC.apply` (Def 3.17 composition =
  `fTransform` over `Dist.prod`), and the random-function instance
  `applyDDC_simple_ofFunDist : simple (c,d) ⋆ RF(Df) = RF((d ∘ · ∘ c)_* Df)`.

### 10.4 Design decisions and deferred pieces

- **Strict `ofStep`.**  A `⊥` answer kills the run, making the realization
  target the raw `S` and the domain equalities crisp.  A lenient variant
  (`step` over `Option Y`, realizing `applyG step S⊥`-style application) is a
  wrapper away if an application needs it; no current consumer does.
- **Stateful protocol steps** — SUPERSEDED by §10.5: the general converter
  presentation is the protocol function `ν` on histories (no state carrier);
  memory classes are invariance *predicates* on `ν`, never part of the type.
  (An earlier `(σ, δ, move)`-machine design was rejected as operational — a
  machine is a quotiented-history presentation, i.e. a classification device
  and proof witness, not a mathematical object of the theory.  This is the
  §8 discipline applied to converters.)
- **Cascade/combine converter equations** (fixing 10.1(2)): re-prove
  `cascᶜ ·ᶜ cascadeAccess S T = S ⊲ₚ T` and the `comb⋆` analogue against the
  *actual* converters via a paired-access analogue of the realization
  theorem, then retire the `rfl` definitions.  Tracked in `STATUS.md` §8.
- **`attachAt () = DDC.apply`** under `unitResourceEquiv` (unifying the
  Def 3.13 attachment machinery with Def 3.9 at the single interface): true;
  bisimulation invariant "attach-history = `keptPrefix` of apply-history"
  (attach records only kept queries, `connStep` records all; answers agree
  because `s⊥` applies `keptPrefix` anyway).  Tracked in `STATUS.md` §8.
- **Automation inventory** (per §4–5 policy): `run`-parser snoc lemmas and
  the `driveG`/`driveOuter` closed-form unfoldings are candidates for a
  `cr18_protocol` simp set once a third protocol converter appears; the
  `n + 1 + 1` fuel-literal idiom (equation-lemma matching) should be absorbed
  by a small `driveG_unfold` tactic at that point, not before.

### 10.5 The protocol function ν, its trace tree, and the identity discipline (2026-07-02)

Outcome of the slow re-derivation (memoryless case first, then memory), and
the correction of 10.4's machine design.  Everything is a history-function;
no state carriers anywhere.

**Memoryless anchor.**  A memoryless DDS over a *partial* `s : X →. Y` is
forced by prefix closure to be the **strict evaluator** `⌜s⌝ₚ` (defined at
`x₁…x_k` iff every `s(x_i)` is): *the value forgets the past but the domain
remembers it* — the partiality ratchet is validity's operational content.  A
memoryless DDC is a pair `αU : U → X ⊕ V`, `αY : Y → X ⊕ V`; one round is
the **orbit of a single self-map** `t = s ∘ (query part of αY)` with
first-hit exit, and the expected theorem is `α ·ᶜ ⌜s⌝ = ⌜f⟨α,s⟩⌝ₚ` (round
function = case-split + orbit + first-hit; `simple` is the one-query
subclass, `f = d ∘ s ∘ c`).  `feedback` is the first non-example (needs one
bit of within-round memory), locating the hierarchy.

**The general object.**  A converter is one partial history-function

`ν : List U × List Y →. (X ⊕ V)`

("after outer inputs `u^k` and inner answers `y^l` — cumulative, across
rounds — the next move").  Its own past outputs are recomputable, so nothing
else is data.  Round boundaries are derived from ν recursively.  Memory
classes are *invariance predicates* on ν (the `IsBlind` pattern —
factoring-through, never a carrier): memoryless = factors through the last
symbol; outer-memoryless (= `ofStep`, §10.2) = factors through
`(last u, current-round answers)`; round counters (`[q]`, blind `b`) =
factors through lengths; general = no restriction.  Fixed inner arity `n`
collapses the family to `U^q × (X^{nq} × Y^{nq}) →. V` + consistency — the
fixed-query vocabulary the H-technique surface already speaks.

**The trace tree.**  `Reach(ν)` = least set of pairs with: `([u], [])` ∈;
after a query (`ν = inl x`) every answer extends; after an answer
(`ν = inr v`) every next outer input extends.  Undefinedness *inside* the
tree is honest partiality (non-productive spot); values *off* the tree are
junk.  Reach has triple duty: well-formedness discipline, domain of the
canonical representative, and **the consistency indicator** of the
transcript-law factorization (see below) — one definition, three roles.

**Identity discipline** (chosen; the alternatives and the gap are recorded):

1. carrier = bare ν, **junk-freedom** (`dom ν ⊆ Reach ν`) as a `Prop`
   (constructors produce junk-free values, mirroring how Def 3.8's query
   bound stays a predicate);
2. **normalization** `ν* = ν|Reach(ν)`; stability `Reach(ν*) = Reach(ν)`
   hence idempotence; **trace equality** `ν ≈ ν' :⇔ ν* = ν'*` is the working
   identity — a computable congruence (composition/absorption respect it
   lemma-by-lemma);
3. **apply equality** (`∀ S, νS = ν'S`) is strictly coarser — separated by
   *dead queries* (query, ignore the answer, never consult again in any
   continuation); it is the converter-side analogue of the U5 behavioral
   quotient, flagged but not adopted (no current theorem needs it; any
   paper-facing "converter equality" claim should be read as apply equality
   unless about a specific representative);
4. in the ν presentation **no validity condition remains** (any partial ν is
   a legal converter) — evidence that ν is the right primitive and the
   converter-alphabet DDS is derived.

**Application = transcript equations.**  Against `s`, the interaction is the
unique maximal solution of the mutual recursion `x̂ⱼ = ν(active prefix,
ŷ^{j−1})`, `ŷⱼ = s(x̂^j)` (unique by causality; defined per round iff an
`inr` is reached — productivity witnesses, e.g. ranking functions, stay
private), and `(νs)(u^k) = the round-k inr`.  `PFun.fix` is the private
constructor of this solution.  Because `y^l` is *free* in ν, the composite's
transcript law against any environment factors as
`Σ over Reach-consistent inner transcripts of the system factor` —
simultaneously the converter-side Lemma 3.2, the general form of
Thm 4.17's `T̃`-absorption (environment + converter fuse into a derived
environment: `⟨E, νS⟩ ≡ ⟨νᵀE, S⟩`), and the intended proof engine for the
nonexpansiveness/DPI `Adv(νS, νT) ≤ Adv(S, T)`.

**Lean staging** (scoped to DDC + applications, per owner direction):

- landed: `ProtocolFn.lean` — ν carrier, `Reach`, `JunkFree`, `normalize`
  (+ stability, idempotence), `TraceEquiv`, `toDDC` (junk-free-by-
  construction Def 3.8 object; parse relation `ParsesTo`, deterministic,
  prefix-closed), `toDDC_normalize` and `toDDC_congr` (the identity
  discipline cashed as theorems: trace-equal converters are literally the
  same DDC after normalization).
- landed, stress tests (same file): `simpleFn` and `queryLimitFn` with their
  trace trees characterized in closed form (`reach_simpleFn_iff`,
  `reach_queryLimitFn_iff` — the predicted length lattices, budget-cut for
  `[q]`), junk-freedom for both, the breach fact
  (`queryLimitFn_breach`: the pair "q+1 inputs, q answers" is *reachable
  and undefined* — Def 3.10's "(q+1)-st query undefined" read off the
  tree), a `toDDC` first-move smoke test, and the junk triple for
  `simpleFnJunk` (not junk-free; raw-distinct from `simpleFn`; yet
  `TraceEquiv`, hence the same `toDDC`).  The tests caught a real
  modeling bug: a first draft of `queryLimitFn` omitted the budget check on
  the *answer* branch, silently carrying junk at answered pairs beyond
  round `q` — `JunkFree` failed exactly there.  The discipline is doing its
  job.
- landed (2026-07-02, second pass): `ProtocolRealization.lean` — the
  transcript-equation driver `driveNu`/`driveNuOuter`/`applyNu` (fuel-free
  via `eventual`; the ν-generalization of `CausalApply.applyG`) and **the
  ν-level realization theorem** `apply_toDDC : DDC.apply (toDDC ν) S =
  applyNu ν S.1` — Def 3.9 = the transcript-equation solution for
  *arbitrary* converters, cross-round memory included; plus the first
  cross-round instance `applyNu_queryLimitFn : applyNu (queryLimitFn q) S.1
  = filterQueries q S`, its Def 3.9 corollary `apply_toDDC_queryLimitFn`,
  and `queryLimit_apply_eq_toDDC` (the old operational `[q]ᶠ` DDC and
  `toDDC (queryLimitFn q)` are apply-equal representatives — bespoke
  `queryLimit` trace proofs are retired as instances).
- landed (same pass): `CascadeRealization.lean` — **the honest cascade
  equation** `apply_cascadeStep : DDC.apply (ofStep cascadeStep)
  (cascadeAccess S T) = S ⊲ₚ T` (CR18 Def 3.11 via Def 3.9), replacing the
  `rfl`-by-definition `cascadeViaConverter_eq_cascade`.  Key observation:
  over the paired-access system the cascade converter is *outer-memoryless*
  (fixed arity 2), so it factors through `apply_ofStep`; the proof is a
  `driveG` computation with `cascadeAccess` evaluation lemmas and
  `cascadeMiddle` snoc bookkeeping — no transcripts.
- next: `toNu` + round-trips (junk-free ν ≅ normalized DDC); fixed-arity
  ν's for `simple`/`feedback` as `apply_toDDC` instances; retire the `rfl`
  `cascadeViaConverter`/`combineViaConverter` definitions in favor of the
  honest equations (the `comb⋆` analogue of `apply_cascadeStep` follows the
  same recipe).

### 10.6 Event algebras (GegMau26) — adoption plan

`Reach(ν)`, the interaction tree of `⟨E,S⟩`, the transcript prefix order and
the game tree are all *forests of evolutions* in GegMau26's sense; their
Thm 2 (the forest is recoverable from the algebra of its monotone
predicates) is the "no machines / observables determine the object"
principle as a duality theorem.  Mapping onto this repo:

- **The monotone gadgetry is one structure.**  `IsMBO`, `MonotoneMBO`
  (Thm 4.17), H-technique bad events, strictness death (`⊥`-answer),
  Reach-inconsistency — each is an *event* (monotone predicate) on the
  relevant forest.  Named operations: filtered winning = `win ∸ bad`;
  game hops = the triangle UEI `a∸b ⪯ (a∸c) ∨ (c∸b)`; union bounds =
  valuation of `∨`; "prevent e by preventing f" = `e ⪯ f`
  (`⟺ e ∸ f = ⊥`).
- **Two-layer architecture, named**: UEIs on the interaction forest (pure
  lattice algebra, no probability, no model) + the PDS law as a *valuation*
  (transcript masses of events) evaluating every UEI into a probability
  inequality for **any** law, no independence assumptions.  This is the
  law-level discipline, axiomatized — randomness enters only as a valuation
  at the end.
- **Division of labor**: events handle the bad-event/forgery layer; random
  systems handle indistinguishability (GegMau26 §4.9 scopes UEIs away from
  it); the H-technique (`δ ≤ Pr[B] + ε-on-good`) is the bridge — `B` lives
  in the event algebra, `δ` in the metric world.  Their "lattice valuations"
  future-work direction is where our `Adv`/DPI sits.
- **Lean cost note**: E1–E4 = mathlib `CoheytingAlgebra` (with `\` as `∸`
  and the needed API: `sdiff_le`, `sdiff_le_iff`, `sdiff_triangle`,
  distributivity); E5 = one extra axiom; the forest model = upper sets of
  the prefix order.  GegMau26 App. F.3 reports its own mathlib
  formalization — check for reuse before writing any of this.
- **Adoption scope (owner decision 2026-07-02)**: Lean adoption restricted
  to what touches **DDC and applications** — the Reach/consistency layer of
  §10.5 and, later, absorption/DPI phrased as event pullback along the
  forest map induced by a converter (events pull back, valuations push
  forward).  The games/MBO restatement (`win ∸ bad` forms of the Thm 4.17
  chain) and a standalone `EventAlgebra` core module are recorded here as
  design only, not scheduled.

### 10.7 Converter DPI via absorption (IMPLEMENTED 2026-07-02, `AbsorbDPI.lean`)

The nonexpansiveness theorem `Δ(αS, αT) ≤ Δ(S, T)` (converters are
1-Lipschitz for distinguishing advantage — the categorical content of
"converters are morphisms", DESIGN §10.6).  Statement chain, each step one
lemma family:

1. **Absorption (deterministic core).**  `absorb (α : DDC U V X Y)
   (d : DDD U V) : DDD X Y` — the distinguisher with the converter fused in:
   at an `s`-answer history `h : List (Option Y)`, deterministically replay
   the `d`–`α` interaction consuming `h` answer-by-answer (a `run`-parser
   construction, same recipe as `OfStep.run`/`ParsesTo`); emit `α`'s next
   inner query, or `d`'s verdict once it stops.  `StopFinal` holds because
   the replay stops consuming at `d`'s stop.
2. **Verdict correspondence.**  `verdict (absorb α d) s ↔ verdict d (α ·ᶜ s)`
   for every DDS `s` — a transcript bisimulation between
   `transcript s (ddToDDE (absorb α d))` and
   `transcript (α ·ᶜ s) (ddToDDE d)` (Def 3.7 both sides), through the
   `resolve`/`driveFrom` machinery; the two `∃ n` witnesses are related by
   the round structure (inner steps vs outer rounds).  This is the fourth
   simulation of the realization-theorem family; the invariant is the same
   liveness `xs ∈ dom s ∨ xs = []` plus "replay state = parse of the
   answer history".
3. **Law-level lift.**  `verdictProb (fTransform (absorb α) D) S
   = verdictProb D (applyDDC α S)` (pushforward + the deterministic
   correspondence pointwise under the `winProb` sum), hence
   `advantage D (applyDDC α S) (applyDDC α T)
   = advantage (fTransform (absorb α) D) S T`.
4. **Endpoint.**  `maxAdvantage (applyDDC α S) (applyDDC α T)
   ≤ maxAdvantage S T` — sup over `D`, using `fTransform`
   `isProbDist`-preservation and `advantage_le_maxAdvantage`.

Implementation notes (2026-07-02): all four steps landed in
`AbsorbDPI.lean`, `sorry`-free.  The replay is the fuel-monotone driver
`absorbGo` with the move extracted classically (`absorbFun`); `StopFinal`
holds *unconditionally* (a diverging internal interaction defaults to
verdict `0` on both sides, and divergence is stable under history
extension).  The verdict correspondence `verdict_absorb_iff` is proven via
the joint-run relation `AbsRun t T mode` (base transcript, composite
transcript, round state) with: forward/reverse replay lemmas, a run
extraction lemma, `driveOuter`-certification of the recorded composite
answers (`absRun_driveOuter`), Def 3.7 `Transcript` alignment on both sides,
and round completion under the Def 3.8 bound.  Scope hypotheses (both
paper-faithful, both *necessary* — without them the composite-level and
base-level `keptPrefix` prunings genuinely diverge): the systems'
support-totality `CondEquiv.TotalOnNonempty` (the resource view), and the
converter's round bound (Def 3.8).  Endpoint:
`maxAdvantage_applyDDC_le : Δ(applyDDC (ofStep step) S, applyDDC (ofStep
step) T) ≤ Δ(S, T)`.  The ν-general version (cross-round-memory converters)
follows the same recipe over `applyNu` when needed.

Event-algebra reading (§10.6): `absorb` is the forest map induced by the
converter; step 2 is "events pull back", step 3 "valuations push forward".

Converter-algebra completion (2026-07-03): unit and action law for the
memoryless rung (`simple_id_id_apply`, `simple_simple_apply`), honest
Def 3.12 equation (`apply_combineStep`, CombineRealization.lean), and the
§10.5 round-trip `toNu_toDDC : toNu (toDDC ν) = normalize ν` — the ν-world
is the junk-free quotient of the DDC-world, so `TraceEquiv` classes and
normalized DDCs are interchangeable presentations.  Serial ν-composition (IMPLEMENTED 2026-07-03,
`ComposeRealization.lean`): `compNu ν₂ ν₁` is the flat replay of the
two-converter stack (`compGo`, the `absorb` recipe with the distinguisher
slot generalized; `Part`-partiality absorbs divergent internal chatter, so
the definition needs no round bounds), and the **action law / interaction
associativity**

  `applyNu_compNu : applyNu (compNu ν₂ ν₁) S = applyNu ν₂ (applyNu ν₁ S).1`
  `apply_toDDC_compNu : (toDDC (compNu ν₂ ν₁)) ·ᶜ S = (toDDC ν₂) ·ᶜ ((toDDC ν₁) ·ᶜ S)`

holds *unconditionally* — no totality, no round bounds: the strict/raw
semantics has no `keptPrefix` pruning, so flat and nested replays agree on
the nose.  Proof: three-level joint-run relation `CompRun` (outer `wsAct/zs`,
middle `us/vs`, base `xs/ys`, turn bit) with: flat replay + reverse replay +
extraction (L1, the `AbsRun` recipe over two consumable streams), middle
certification `compRun_middle`/`compRun_middle_value` (the recorded `vs` are
genuine `applyNu ν₁ S` outputs — `driveNuOuter` run + open-round `driveNu`
continuation), outer certification `compRun_outer` (a global anchor +
continuation invariant giving the ν₂-against-middle run), and the two
round/outer simulations in each direction (`lhs_driveNu_sim`/`lhs_to_rhs_outer`,
`segment_lhs`/`rhs_to_lhs_round`/`rhs_to_lhs_outer`).  With
`simple_id_id_apply` as unit and `toNu_toDDC` for identity, the converter
monoid acting on systems is now fully algebraic at Level 2.
The consistency-indicator factorization of the composite transcript law
(`law⟨E, νS⟩ = Σ_{Reach-consistent} σ_S`) is the fixed-query shadow of the
same construction and can be developed on the H-technique surface
independently.

### 10.8 Deterministic causal typed resources and the current AC contract

The production instance has one semantic path.  It is neither the memoryless
`routeAt` experiment nor the CR18 observable-completion quotient.

#### Native mathematical objects

A signature universe contains codes with code-dependent input and output
types.  A boundary is `sigma : I -> Code`; its query alphabet is
`Sigma i, input (sigma i)`, and the answer to a query at `i` lies in
`output (sigma i)`.  A `DependentDDS` sees the complete interleaved history,
so hidden state can be shared across interfaces.  This is one resource with
typed ports, not a product of independent state machines and not a common-
output-alphabet encoding.

A deterministic typed primitive from `source` to `target` is exactly a
history-sensitive `ProtocolFn` plus `IsDDC`.  The `IsDDC` judgment supplies
the causal alphabet discipline and a finite inner-query bound.  There is no
`Emulable`, `FrameCompatible`, memorylessness, or one-query field.  Ordinary
functions use `DeterministicConverter.ofFunctions`; arbitrary stateful
programs use `ofHistory`.  Fixed-signature raw protocol composition remains
the established `PFunConverter.comp`, with its proved `IsDDC` closure and
action law.  The typed AC boundary does not posit a second raw converter
monoid: its identity and serial composition are the word constructors
`ConverterTerm.one` and `ConverterTerm.mul` of `Gamma`, interpreted as
resource endomorphism identity and composition.

Attachment changes only one boundary component and frames every other query
unchanged.  The ambient tagged chart is an implementation device used to
reuse the general stateful driver; its image is proved tag-faithful before
returning to the dependent carrier.  Attachments at distinct interfaces
commute exactly (up to the unique dependent transport) by the generalized
`attachAt_comm` theorem.

#### Rejection and divergence

At the selected AC boundary, `Part.none` means blocking divergence: there is
no answer event and hence no continuation event.  A rejection after which the
caller may continue is an ordinary value in the advertised output type (for
example `Option A`'s `none` inside the outer `Part.some`).  It remains in the
query/answer history just like any other reply.

This deliberately differs from applying CR18's `s -> s_bot` completion as the
public observation rule.  That completion reports `bot`, deletes the rejected
input from the state seen by the underlying DDS, and allows the environment to
continue.  For a multi-query converter, successful inner calls made before a
later stall can then be erased by the outer retry semantics.  The formal
`probeFn` example isolates exactly this probe/reset phenomenon.  CR18
completion remains available for source theorems that state it; it does not
define equality in the AC carrier.

#### Contextual behavior and distance

A terminal strict test is an arbitrary Boolean-returning deterministic
`IsDDC` protocol invoked once.  Testing `alpha S` equals testing `S` with the
serial composite of the test and `alpha`; this is the established interaction
associativity theorem, not a new compatibility assumption.  It yields context
absorption, quotient congruence, data processing, and strict serial coherence
for every deterministic converter.

For dependent resources, an experiment is inductively either a terminal
strict test or attachment of any typed deterministic converter followed by an
experiment at the target boundary.  Equality means equal acceptance mass for
all such finite experiments.  The contextual extended distance is the
supremum of their acceptance-distance.  Converter closure and non-expansion
are structural consequences of prepending one experiment node; no converter
subclass or per-converter quotient certificate is needed.  Probability is a
finite-support law over deterministic resources.  Randomized constructions
may therefore expose randomness as another resource while this first AC
instance keeps converters deterministic.  On a fixed boundary, and again on
the heterogeneous resource carrier, zero contextual distance is exactly
quotient equality; this is the intended information-theoretic zero policy.

### 10.9 The single AC rendering

`Phi` is the dependent sum of normalized contextual behavior fibres over all
boundaries, with fibre distance inside one boundary and infinity across
different boundaries.  A primitive at interface `i` contains any typed
deterministic converter.  On a resource whose local code matches its source it
performs native attachment and changes only component `i`; on a nonmatching
local code its total AC action is the identity.  As required by the selected
AC contract, an application theorem must still prove that its assumed
specification lies in the matching source domain and has the advertised
target boundary.

`Gamma i` is the **syntactic** converter monoid at `i`: words over the
primitive actions modulo the serial monoid laws only (`ConverterTerm`
quotiented by `ConverterTerm.Rel`), interpreted into `nonexpandingEnd Phi` by
`gammaInclusion`, whose range is the extensional monoid it used to be
(`mrange_gammaInclusion_eq_generatedConverterMonoid`).  Multiplication is
serial composition of words, so ordinary `mul_smul` and `primitive_mul_smul`
give the exact paper order (right factor first).  Exact primitive commutation
at distinct interfaces extends through the word structure.  The commuting
inclusions combine with
`MonoidHom.noncommPiCoprod` to install globally

```lean
[forall i, Monoid (Gamma i)]
[MulAction (forall i, Gamma i) Phi]
[PseudoEMetricSpace Phi]
[IsNonexpandingSMul (forall i, Gamma i) Phi]
```

The first two are AC's equality-level contract; the latter two are its metric
refinement.  They are furnished by the same carrier and the same full
deterministic converter class.  The former separate exact-operational instance
is obsolete and is outside the selected import graph.  `TypedFinite.Model`
packages the finite interface type, signature universe, and decidability data
once so downstream theorem headers name only `model.Phi`, `model.Gamma i`, and
`model.Protocol`; the algebraic and metric instances infer globally.

This rendering deliberately makes neither a homogeneous `Par` claim nor a
computational-feasibility claim.  AC treats both as independent mixins.  The
typed routing and distinct-interface commutation proved here are the facts
needed for the indexed tuple action; they do not silently assert a resource
parallel operator.  Likewise, the exact semantic monoid does not depend on a
raw typed-program composition representation theorem.  Such a theorem is a
useful future realization bridge, but it cannot change converter identity or
block the AC instance.

Implementation map (2026-07-21):

* `StrictContext.lean`: strict observation, contextual quotient/metric,
  absorption, serial coherence, and non-expansion;
* `TypedResource.lean`: native dependent DDS/PDS and tag-faithful flattening;
* `TypedAttachment.lean`: every typed `ProtocolFn + IsDDC`, signature-changing
  attachment, embedding coherence, and distinct-interface interchange;
* `TypedAction.lean`: dependent contextual experiments, quotient, metric,
  total primitive action, and commutation;
* `TypedFraming.lean`: the canonical all-interface frame for every typed
  deterministic converter and exact native-attachment/strict-application
  coherence after flattening;
* `TypedFramingMetric.lean`: compilation of every finite boundary-indexed
  experiment to one strict global test and arbitrary-interface metric full
  abstraction;
* `RandomSystemsCC/TypedFinite.lean`: `Phi`, `Gamma`, tuple action,
  non-expansion, ergonomic configured model, and generic `Constructs` receipt;
* `RandomSystemsCC/TypedFiniteChecks.lean`: dependent two-interface,
  rejection/divergence, hidden-state, `probeFn`, serial, commutation, exact AC
  inference, and AC/CC/CC.MPC notation regression gates.

### 10.10 Source-metric bridges and the CBC integration test

The selected contextual metric is not definitionally CR18's observable-
bottom distinguishing advantage. `TypedFraming.lean` supplies the missing
all-interface deterministic coherence theorem: native attachment of any
history-sensitive `ProtocolFn + IsDDC` converter, when flattened, is exactly
strict application of its boundary-wide frame. `TypedFramingMetric.lean`
therefore compiles every finite typed experiment to one strict test on the
flattened global alphabet, preserving acceptance mass exactly. Hence typed
contextual distance equals strict distance after flattening for arbitrary
interface types. No `Fintype`, totality, `Emulable`, `FrameCompatible`,
memorylessness, or one-query premise occurs in this result.

`TypedUnitMetric.lean` remains the useful one-interface specialization: it
removes the vacuous `Unit` tags and identifies the same contextual distance
with strict distance on `singleView`.

`StrictContextAdvantage.lean` completes a diverging strict observer by
returning `false` and absorbs the resulting productive protocol into a CR18
distinguisher.  This proves the direction needed to reuse source bounds:

```lean
typed contextual edist <= ENNReal.ofReal (CR18 maximal advantage).
```

`RandomSystemsCC/TypedFramingAdvantage.lean` exposes this inequality directly
for every normalized dependent boundary, using the flattened global laws;
`TypedUnitAdvantage.lean` is its tag-free one-interface presentation.

The reverse direction is not unconditional.  A CR18 distinguisher may observe
an invalid query as `none`, continue, and later accept, whereas strict
divergence has no continuation. `StrictContextTotal.lean` proves equality
under support totality (more generally, proper interaction) and keeps the
empty-resource counterexample as the semantic guardrail.

`RandomSystemsCC/ResourceLift.lean` supplies the second, source-facing
rendering needed when a theorem is already stated in CR18's own observation
model.  **Its fibre is the separated strict quotient
`StrictContext.System X Y`** (2026-07-25); unequal signatures remain at
distance `⊤`.  Bundled DDCs compose with `*` and act with the same typed
operation on raw PDSs and heterogeneous resources; the right-hand type selects
composition or action and fixes every intermediate alphabet.
`DDConverter.apply_law_comp` carries the converter's DDC evidence through
ordinary reassociation.

`Protocol` is the **syntactic** monoid of converter words over the CR18
`IsDDC` primitives modulo the serial monoid laws only (`ConverterTerm`
quotiented by `ConverterTerm.Rel`) — CR18's Γ as programs, not as behavior.
`protocolInclusion` interprets it into `nonexpandingEnd`, and it carries
`IsNonexpandingSMul` for that **whole** class: non-expansion is structural on
the strict quotient (context absorption), not a per-converter certificate.
Consequently `Constructs.eball_trans` applies and approximate constructions on
this carrier compose — `cbc_urp_randomness_expander` is the receipt.  The
extensional submonoid `Protocol` used to be is retained as
`generatedConverterMonoid`, proved equal to the interpretation's range by
`mrange_protocolInclusion_eq_generatedConverterMonoid`, so the de-quotienting
lost nothing the old presentation could express.

*Superseded design, retained because the reasoning still matters.*  The fibre
was originally the un-quotiented `PFunPDS.Prob` law with `Δ` installed as a
pseudometric, and the rendering separated `Protocol` from a
`CompatibleProtocol` generated only by `Emulable`-certified converters.  That
split was forced by the `not_emulable_probeFn` guardrail — CR18 Definition 3.8
membership alone does **not** make a converter compatible with the full CR18
distinguisher class, which is genuine mathematics and still true.  But the
consequences were fatal in practice: AC requires an already-quotiented carrier
(so exact `Constructs` meant *law* equality, finer than behavioral equality),
`Protocol` had no non-expansion instance and therefore no ε-composition, and
`CompatibleProtocol` was never instantiated anywhere in either repository.
Moving to the strict quotient — where absorption is structural — dissolves the
obstruction rather than working around it, so the compatible subclass is
deleted.  The `Emulable` boundary it encoded is a fact about `Δ` and stays with
`Δ`, in `CompatibleMetric.maxAdvantage_apply_le`.

**The source-metric direction is one-way, and this is load-bearing.**  The
bridge to `Δ` is `edist_liftProb_le_advantage`, the *sound* direction: a CR18
advantage bound on the displayed laws gives an AC distance bound on the
embedded resources.  There is deliberately **no** `edist = ENNReal.ofReal Δ`
lemma on this carrier — the converse is false in general
(`AttainmentCounterexample`: strict tests are type-level blind past `none`, so
`maxAdvantage = ½` with class-distance `1`, i.e. attainment fails; note the
file proves that pair, NOT `maxEDist = 0`).  Construction proofs use the
inequality; a proof that needs the equality is a proof in the wrong place.
Accordingly `constructs_liftProb_iff_advantage` and its siblings are now
one-way `constructs_*_of_advantage`; nothing consumed the reverse direction.

*Instance-path trap (cost real time, 2026-07-25).*  After the fibre move,
composition still failed with `IsNonexpandingSMul` unsynthesizable and the
action `simp` lemmas silently not firing.  The cause was two defeq-but-
syntactically-different `SMul ↥(Protocol U)` paths — a bespoke
`MulAction.compHom` instance versus the mathlib `Submonoid.smul` chain that a
bare `•` elaborates through in *statements* — and it is invisible without
`set_option pp.explicit true`.  Use mathlib's canonical `Submonoid.mulAction`
so one path serves statements, `constructs`, and the AC calculus; the file
pins this with an `example : MulAction … := inferInstance`.

`RandomSystemsCC/CBC.lean` uses this source-facing rendering.  Its three
paper converters remain ordinary bundled DDCs and the displayed protocol is
literally `theta_r * CBC * [r]`; their bundled views are transparent at the
underlying converter projection.  `R` and `V_n` remain named normalized PDSs
and are cast to the CBC resource carrier only in the construction statement.
CR18 equation (6.1) rewrites the typed DDC product directly.  The general
`constructs_liftProb_of_advantage` theorem handles any typed DDC between
embedded PDSs; `cr18_construct` first selects its common-outer specialization
when that preserves the paper's visible context.  It turns

```lean
R —[theta_r * CBC; epsilon]→ theta_r * V_n
```

directly into the real-valued paper goal
`Δ(theta_r · CBC R, theta_r · V_n) ≤ epsilon`.  It owns the operational
protocol embedding, interface witnesses, typed reassociation, and
`ℝ`/`ℝ≥0∞` conversion.  The bundled equation `CBC R = cbcReal` leaves exactly
the paper expression `Δ(theta_r · cbcReal, theta_r · V_n)`.  There is no
CBC-specific metric bridge, `congrArg` transport, or strict-context
transport rung in the construction proof.  `cbc_randomness_expander`'s
statement is unchanged by the fibre move; only its *meaning* changed, from law
equality to behavioral equality, which is the point of the move.

**The composition receipt.**  `cbc_urp_randomness_expander` chains the URP/URF
switching leg with the round-limited expander leg through
`Constructs.eball_trans`, giving CBC-MAC over a uniform random *permutation* at
Theorem 6.1's own protocol and at radius literally `ε₁ + ε₂`.  Its proof body
contains no transcript or probability reasoning — that is the standing test for
whether a composite was assembled at the right layer.  Contrast the RS-level
`rs.cbc.randomness_expander_urp`, which re-derives the bound directly; keeping
both is deliberate, since the bespoke one is the tighter statement and the
composed one is the methodological receipt.

*Known friction:* `cr18_construct`'s `first`-branch unification hits a whnf
timeout against `roundLimit` (unfolding `queryLimitFn` versus `comp`), so the
switching leg applies its lemma directly.  The macro still serves
`cbc_randomness_expander` unchanged.

### 10.11 Declare at RS, prove by lifting to AC (the working method)

This is the discipline every concrete construction on this carrier should
follow, and the reason the RS-to-AC instance exists.

**Declare the objects at the random-systems level; prove the construction
by lifting to Abstract Cryptography.**  A resource is a concrete `Phi`; a
local converter is a concrete `Primitive`.  Because `TypedFinite`
instantiates AC's monoid/action/metric contract (§10.9), AC's construction
*calculus* — `constructs_singleton_iff`, `Constructs.trans`, the metric
relaxations — applies to those concrete objects for free.  You never re-prove
composition; you discharge one behavioral fact at the RS level and wrap it
with an AC lemma.

**Statements must read as algebra, like the papers — never expose the
embedding plumbing.**  The tuple/monoid embedding of a one-interface
converter (`Pi.mulSingle i (Gamma.ofPrimitive ·)`, named `protocolOfPrimitive`)
and the raw action (`Primitive.act`) must not appear in a statement.  The
lifting instances in `TypedFinite.lean` make a bare `Primitive` first-class:

* `SMul (Primitive I U i) (Phi I U)` — the native action, so `flip • R`
  reads as `flip · R` (`primitive_smul_eq_act : flip • R = flip.act R`,
  `rfl`);
* `CoeTC (Primitive I U i) (Protocol I U)` — the converter *is* a protocol;
* `HasReduction (Set (Phi I U)) (Primitive I U i)` — so the construction
  notation `⟪R⟫ —[flip]→ ⟪S⟫` takes a bare `flip` (the coercion cannot fire
  where the reduction's converter type is fixed by `flip`, so this instance
  supplies it);
* `coe_primitive_smul : (protocolOfPrimitive flip) • R = flip • R` — the
  bridge `simp` lemma that discharges an AC construction about the embedded
  protocol from the native RS action.

`RandomSystemsCC/LiftingExample.lean` is the canonical minimal worked
example: a signature, a `flip` converter, and

```lean
theorem flip_apply      : flip • R = flip.act R
theorem flip_constructs : ⟪R⟫ —[flip]→ ⟪flip • R⟫
```

with no `Pi.mulSingle`, `Gamma.ofPrimitive`, `.act`, or `↑` in any
statement.  The division of labor is exact: **RS owns the concrete object
and the one genuine behavioral fact** (for a real scheme, a coupling or
program-equivalence proof); **AC owns the construction predicate and its
calculus**.

**Honest caveat — this is modeling, not notation.**  The lifting instances
remove *plumbing*; they do not remove the need to *name your ideal
resource*.  A meaningful construction is `⟪real⟫ —[π]→ ⟪ideal⟫` with both
endpoints named and `π • real = ideal` a genuine behavioral proof.  For a
generic resource `R` the only available right-hand side is "`π` applied to
`R`", which says nothing; the content lives in defining the ideal and
proving the converter reaches it.  No coercion can supply that.  The FROST
DKG is the live instance: the honest statement is
`⟪coins⟫ —[dkg]→ ⟪keys⟫` (with `keys` the named `keyResource` of
`Frost.Dkg`), and the behavioral equality `dkg • coins = keys` is the real
coupling — which is also where an obstruction such as the Pedersen/GJKR key
bias appears as a genuine proof goal rather than an assumed hypothesis.

## 11. CC-first symmetric-cryptography construction exercises

This section freezes the design of the small symmetric-cryptography
construction suite before any proof work begins.  The source targets are the
OTP construction in CR18 §2.4 (printed pages 27--30), the authenticated and
secure channel models in CR18 §§2.5 and 5.3--5.4, and the PRF-MAC,
PRF(UHF), and one-time PUF-MAC constructions in Boneh--Shoup §§6.3, 7.1,
7.3, and 7.6 (printed pages 223--224, 252--265, and 275--276).

The suite is not a collection of standalone probability or distribution
theorems.  Every exercise starts with named real and ideal resources and
named converters, and its public endpoint is an AC/CC construction judgment.
Probability, interpolation, transcript, coupling, and equality facts may
appear only as proof obligations generated by those final judgments.

### 11.1 Non-negotiable modeling rules

1. **Objects and final statements precede all proofs.**  All resource laws,
   typed boundaries, converters, protocols, simulators, and final construction
   theorem headers for Exercises 1--6 below are implemented and checked
   before the first construction proof is attempted.
2. **Resources carry all relevant capabilities and randomness.**  Channel, key,
   hash-key, and oracle capabilities needed by one construction are multiplexed
   into one dependent typed resource, as in the FROST model, rather than
   represented by an assumed resource product.
   *Status note (2026-07-25):* this rule is a **workaround, not a principle**.
   It exists because the `TypedFinite` carrier has no homogeneous `Par`
   instance — and consequently `Constructs.par_left`, `Constructs.eball_par`,
   `SecurelyConstructs.par`, `IsContextInsensitive`, `IsGenerallyComposable`
   and `ConstructionTree` are all uninstantiated, which is why
   `mac_then_otp_securely_constructs` is an open ledger item instead of two
   lines of composition.  The mathematics for `Par` is already proved
   (Maurer11 Def 2 eq. (3) is `maxAdvantage_par_le`, eq. (4) is
   `maxAdvantage_apply_le`); its one open item, `Emulable (par α β)`, is moot
   on the strict-quotient carrier of §10.10.  When `Par` lands (STATUS §11.3
   P1), keep multiplexing for the existing models but do not impose it on new
   ones.
3. **Converters are the actual protocol algorithms.**  Sender, receiver, MAC,
   verification, hash-then-oracle, and simulator behavior are concrete
   `Primitive`/`Protocol` objects.  Public statements contain no
   `Pi.mulSingle`, `Gamma.ofPrimitive`, `protocolOfPrimitive`, raw `.act`, or
   representative plumbing.
4. **Every endpoint names both worlds.**  No theorem may conclude with
   `⟪π • R⟫`, a transformed distribution, or an unnamed action result.  The
   right-hand side is a separately defined secure channel, authenticated
   channel, or ideal oracle resource.
5. **The channel statements include the adversary interface.**  For the
   Alice--Bob--Eve exercises, the endpoint is
   `CC.SecurelyConstructs {eve} simulators protocol bottom ε real ideal`.
   Thus availability and a simulator-backed security clause are both part of
   the theorem.  A singleton `ApproximatelyConstructs` judgment is used only
   for an oracle-to-oracle construction with no separate adversarial port.
6. **Bounds match the modeled budget.**  A `q`-time MAC resource permits at
   most `q` honest signing deliveries and exactly one fresh forgery attempt,
   matching Boneh--Shoup Attack Game 6.1.  If verification queries are later
   added, they require a new resource and a new bound; they are not silently
   absorbed into the present theorem.
7. **Spaces remain abstract.**  The public parameters are generic finite,
   decidable, nonempty types (`M`, `X`, `T`, and so on) with only the
   algebraic structure used by the construction.  Concrete small moduli such
   as `ZMod 5`, enumerated forgers, and fixed query vectors are forbidden.
   The unconditional algebraic instantiations quantify over an arbitrary
   finite field.
8. **“PRF” means URF in this exercise suite.**  The examples use the ideal
   uniform random-function resource directly.  They do not introduce a
   computational PRF, a feasible distinguisher class, or a PRF-to-URF
   assumption.  A computational instantiation can be a separate future
   construction layer after these information-theoretic receipts exist.
9. **No speculative helper surface.**  No correctness, mass, equality,
   interpolation, or counting lemma is added merely because it looks useful.
   During proof work, an obligation is first discharged locally.  A named
   helper is extracted only if the final construction proof requires it at
   more than one site or if it is itself a source-defined mathematical
   object with an immediate consumer.
10. **Composition is inherited.**  Serial construction proofs use
    `CC.SecurelyConstructs.trans`, `Constructs.trans`, or the corresponding
    relaxation theorem.  Re-proving the end-to-end distance bound after stage
    receipts exist is a wrong-layer bug.
11. **Use the CBC application layout.**  `RandomSystemsCC/CBCModel.lean` is
    the structural template: interface codes, `HasResourceCode` instances,
    and bundled DDC converters live in a model file.  The construction file
    then has an `Objects` section followed immediately by the final AC
    theorem.  Transport or counting lemmas are added later only when that
    theorem's proof exposes the corresponding obligation.  Copy the layout,
    not CBC's source-facing `Δ` carrier: the channel suite remains on
    `TypedFinite` and its strict contextual semantics.
12. **Upcast behavioral facts immediately.**  Follow
    `RandomSystemsCC/LiftingExample.lean`: RS owns only the smallest genuine
    behavioral receipt required by the endpoint; that receipt is lifted to
    equality/distance in `Phi`, and availability, simulation, serial
    composition, and error accounting are then proved with the AC/CC
    calculus.  Endpoint proofs must not unfold the general attachment driver
    or reproduce a construction as a second low-level RS development.

### 11.2 Common typed channel model

The common interface type has exactly three values: `alice`, `bob`, and
`eve`.  Each construction has source and target codes for all three
interfaces.  A boundary is therefore a function from the interface to the
stage-specific code, rather than a single common code pretending that the
three ports have the same query and answer alphabets.

The resource laws are stateful dependent PDSs:

* an insecure channel lets Alice submit a payload, lets Eve read and replace
  it, and lets Bob retrieve the resulting payload;
* an authenticated channel leaks Alice's message to Eve but lets Bob receive
  only Alice's message (subject to the same explicit delivery policy);
* a secure channel leaks only the public length/shape value selected by the
  model and otherwise delivers Alice's message unchanged;
* a key capability returns the same sampled key to Alice and Bob and nothing
  to Eve;
* a keyed-oracle capability is sampled once and answers consistently across
  all permitted calls.

Each resource records its delivery and query budget in its state.  Rejection
that permits a later call is an ordinary `Option`-valued answer; `Part.none`
remains blocking divergence, following §10.8.  The bottom protocol used in
availability exposes the intended honest delivery behavior, and the simulator
submonoid contains only tuples supported at `eve`.

The shared model is justified by the final serial constructions in Exercises
5 and 6.  It is not a convenience abstraction: without a common carrier and
staged boundaries, `CC.SecurelyConstructs.trans` cannot type the intermediate
resource.

### 11.3 Exercise 1 — additive OTP constructs a secure channel

Parameters: an arbitrary finite additive commutative group `G`, used for
messages, keys, and ciphertexts.

Objects:

* `otp_assumed_resource`: an authenticated one-message channel bundled with
  a uniformly sampled shared key;
* `secure_channel_resource`: the one-message ideal secure channel, leaking
  only the fixed public shape carried by the type;
* `otp_encrypt`, `otp_decrypt`, and `otp_protocol`;
* `otp_simulator`: at Eve's ideal interface, samples the ciphertext that Eve
  sees in the real system.

Frozen endpoint:

```lean
theorem otp_securely_constructs :
  CC.SecurelyConstructs {eve} otp_simulators otp_protocol bottom 0
    otp_assumed_resource secure_channel_resource
```

The proof obligation generated by this statement is behavioral equivalence of
the complete real and simulated ideal resources.  “Ciphertext is uniform” is
not a public theorem in this exercise; it is an internal step only if the
resource equivalence proof needs it.

### 11.3.1 Exercise 1b — indexed fresh-pad OTP

The reusable OTP construction makes the randomness capability explicit rather
than reusing the single pad from Exercise 1.  It has an arbitrary finite,
decidable, nonempty index space `X` and an arbitrary finite additive
commutative group `G`.

The assumed resource multiplexes an authenticated indexed channel with a
shared URF-style pad table `pads : X → G`.  Alice and Bob obtain the same pad
at index `x`.  Under the uniform law, values at distinct fresh indices are
independent and uniform, while repeated access to one index is consistent.
This is the finite-table presentation of the usual fresh-input behavior of a
URF; it is not a converter-owned random generator.

The channel domain admits at most one Alice submission at each index.
Attempts to submit a second message at the same index are outside the partial
domain; they are neither overwrites nor silently ignored.  Pad reads and
Bob/Eve observations do not consume this submission budget.  Thus the
construction supports up to `|X|` independently padded messages without
pretending that a finitely supported `Dist` contains an infinite random
stream.

Objects:

* `freshPadAssumedResource`: authenticated indexed channel plus the shared
  uniform pad table;
* `indexedSecureChannelResource`: indexed secure channel with an independent
  uniform simulated-ciphertext table;
* `FreshOTP.encrypt`, `FreshOTP.decrypt`, and `freshOtpProtocol`;
* `simulatorProtocol`: routes Eve's real indexed ciphertext observation to the
  ideal simulated-ciphertext port.

Frozen endpoint:

```lean
theorem fresh_otp_securely_constructs :
  CC.SecurelyConstructs {eve} freshOtpSimulators freshOtpProtocol bottom 0
    freshPadAssumedResource indexedSecureChannelResource
```

As in Exercise 1, the public result is the construction judgment.  Fresh-output
uniformity and additive reindexing are internal obligations only if generated
by its proof.

### 11.4 Exercise 2 — affine one-time MAC constructs authentication

Parameters: an arbitrary finite field `F`.  The one-time MAC key is a
uniform pair `(a,b) : F × F`, and the tag of `m : F` is `a*m+b`.  This is the
abstract-field version of Boneh--Shoup §7.6.2--7.6.3, not a fixed small-field
example.

Objects:

* `affine_mac_assumed_resource`: an insecure one-message channel bundled with
  the shared affine key;
* `one_time_authenticated_resource`: an authenticated channel allowing one
  honest delivery and one fresh injection attempt;
* `affine_sign`, `affine_verify`, and `affine_mac_protocol`;
* `affine_mac_simulator`: simulates the observed tag at Eve and routes the
  original-message case through the ideal channel.

Frozen endpoint:

```lean
theorem affine_one_time_mac_securely_constructs :
  CC.SecurelyConstructs {eve} affine_mac_simulators affine_mac_protocol
    bottom (1 / (Fintype.card F : ℝ≥0∞))
    affine_mac_assumed_resource one_time_authenticated_resource
```

There is no PUF, DUF, universality, or forger-success hypothesis in this
statement.  The interpolation/counting fact is derived only when the
construction's security clause produces that obligation.

### 11.5 Exercise 3 — a bounded URF MAC constructs authentication

Parameters: arbitrary finite nonempty message and tag spaces `M` and `T`, and
a natural signing budget `q`.

Objects:

* `bounded_urf_mac_assumed_resource q`: an insecure channel bundled with one
  uniformly sampled function `M → T`, exposing at most `q` honest signing
  calls and one final verification attempt;
* `q_authenticated_resource q`: the matching ideal authenticated channel;
* `urf_sign`, `urf_verify`, `bounded_urf_mac_protocol`, and
  `bounded_urf_mac_simulator`.

Frozen endpoint:

```lean
theorem bounded_urf_mac_securely_constructs (q : Nat) :
  CC.SecurelyConstructs {eve} bounded_urf_mac_simulators
    (bounded_urf_mac_protocol q) bottom
    (1 / (Fintype.card T : ℝ≥0∞))
    (bounded_urf_mac_assumed_resource q) (q_authenticated_resource q)
```

The bound is independent of the number of signing calls because the single
forgery must use a fresh message and a URF value at a fresh point is uniform.
The resource enforces the freshness and call-budget conditions; they do not
appear as theorem hypotheses about an external forger.

### 11.6 Exercise 4 — UHF then random function constructs a long-input URF

Parameters: abstract finite nonempty types `K`, `M`, `X`, and `T`; an
`ε`-universal family `H : K → M → X`; and a total oracle budget `Q`.

Objects:

* `uhf_short_urf_resource H Q`: a uniformly sampled hash key and short-input
  random function `X → T`, bundled behind one long-message interface;
* `bounded_long_urf_resource Q`: the ideal `Q`-query random function
  `M → T`;
* `hash_then_oracle`: the converter implementing
  `m ↦ rho (H k m)`.

Frozen endpoint:

```lean
theorem uhf_then_urf_constructs_long_urf (Q : Nat) :
  ⟪uhf_short_urf_resource H Q⟫
    —[hash_then_oracle H Q;
      (Nat.choose Q 2 : ℝ≥0∞) * (H.eps : ℝ≥0∞)]→
  ⟪bounded_long_urf_resource Q⟫
```

This endpoint uses the adaptive tight hash-then-random-function theorem; a
fixed vector of queries is not an acceptable substitute.  A second frozen
endpoint instantiates `H` with the polynomial UHF over an arbitrary finite
field and bounded-length field-vector messages, eliminating the universality
premise while retaining the symbolic field cardinality and length bound:

```lean
theorem polynomial_hash_then_urf_constructs_long_urf (Q ell : Nat) :
  ⟪polynomial_hash_short_urf_resource (F := F) Q ell⟫
    —[polynomial_hash_then_oracle (F := F) Q ell;
      (Nat.choose Q 2 : ℝ≥0∞) *
        ((ell : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))]→
  ⟪bounded_long_urf_resource Q⟫
```

The exact encoding of variable-length messages is fixed at object-definition
time and must distinguish different lengths, matching Boneh--Shoup equation
(7.3).  No padding convention may be invented inside the proof.

### 11.7 Exercise 5 — UHF then URF constructs a bounded MAC

The MAC adversary makes `q` signing calls and one fresh forgery attempt, so
the composed long-function construction is budgeted at `Q = q+1`.

The information-theoretic endpoint uses a true short-input random function
and composes Exercises 4 and 3.  Its proof is construction calculus, not a new
transcript argument:

```lean
theorem uhf_urf_mac_securely_constructs (q : Nat) :
  CC.SecurelyConstructs {eve} uhf_urf_mac_simulators
    (bounded_urf_mac_protocol q * hash_then_oracle H (q + 1))
    bottom
    ((Nat.choose (q + 1) 2 : ℝ≥0∞) * (H.eps : ℝ≥0∞) +
      1 / (Fintype.card T : ℝ≥0∞))
    (uhf_mac_assumed_resource H q) (q_authenticated_resource q)
```

The unconditional polynomial-UHF corollary replaces `H.eps` by the
source-derived symbolic bound over an arbitrary finite field.  Both endpoints
use a true short-input URF; there is no computational PRF variant in this
suite.

### 11.8 Exercise 6 — authentication followed by OTP constructs a secure channel

This is the suite's end-to-end composition exercise.  Its common staged model
bundles independent MAC and OTP key capabilities with the insecure channel.
The MAC stage constructs the intermediate authenticated channel while
preserving the OTP key capability; the OTP stage consumes that intermediate
resource and constructs the secure channel.

Frozen generic endpoint:

```lean
theorem mac_then_otp_securely_constructs
    (hmac : CC.SecurelyConstructs {eve} simulators mac_protocol bottom
      εmac insecure_with_keys_resource authenticated_with_otp_key_resource) :
  CC.SecurelyConstructs {eve} simulators
    (otp_protocol * mac_protocol) bottom εmac
    insecure_with_keys_resource secure_channel_resource
```

Its proof is one application of `CC.SecurelyConstructs.trans` to `hmac` and
`otp_securely_constructs`, plus the required honest/dishonest commutation
receipt.  Two concrete corollaries are part of the statement surface:

* affine one-time MAC followed by OTP, fully information-theoretic over an
  arbitrary finite field, with error `1 / |F|`;
* polynomial-UHF/URF MAC followed by OTP for `q` messages, with error
  `choose(q+1,2) * ell/|F| + 1/|T|`.

No end-to-end probability proof is permitted after the stage receipts exist.

### 11.9 Mandatory gate before moving between tasks

Each object-and-statement task must pass all of the following checks before
the next exercise starts:

* the model and theorem header elaborate on the current `TypedFinite` carrier;
* real resource, ideal resource, protocol, bottom behavior, and simulator
  class are named;
* the resource boundaries before and after every converter match, including
  the mismatch-as-identity branch required by §10.9;
* the theorem is a `CC.SecurelyConstructs` or named-resource
  `ApproximatelyConstructs` judgment, never a naked mass, equality,
  `statDist`, `Adv`, or `Delta` endpoint;
* public parameters are symbolic and no concrete small finite type occurs;
* the modeled query/verification budget is explicit and agrees with the
  claimed numerical bound;
* the source page and its assumptions have been checked against the rendered
  PDF;
* no proof helper or theorem unrelated to the final construction obligation
  was introduced;
* the focused file passes Lean elaboration, the admission is honestly marked
  incomplete during the statement-only phase, and no non-foundational axiom
  is introduced;
* a source scan confirms that public statements contain none of the embedding
  plumbing forbidden in §11.1.

Only after the statement gate has passed for all six exercises does proof
work begin, in the same order.  Each proof task then has its own kernel,
axiom-footprint, source-surface, and relevant build gates.  Failure at any
gate keeps that one task active; work does not skip ahead to a later proof.

## 12. The probability tower, and where a probabilistic fact may live

A recurring failure in this tree is a general probabilistic fact proved inside
the one application that first needed it, on whatever carrier was convenient
there.  `minEntropy`, `guessProb` and `condMinEntropy` live on mathlib `PMF`
inside `RandomSystemsCC/MauRen16Impossibility.lean`; an expectation operator
lives on `Dist` inside `RandomSystems/HTechnique/Derivation.lean`; a moment
calculus (mean, variance, σ, Cauchy–Schwarz) lives hard-coded to
uniform-on-`Fintype` inside `RandomSystems/SoP/`.  Each was correct and each is
unreachable from anywhere else, so the next caller reproves it.  The rule below
exists to stop that, and it is the reason the probability/information-theory
program (`STATUS.md` §12) is staged the way it is.

**The tower.**  Four levels; each is built only from the levels below it.

- **L0 — `Dist` itself.**  `Dist A := A →₀ ℝ`, signed and unnormalized.  This is
  the *only* level at which the bilinear calculus is expressible: expectation is
  linear in the distribution here, and that statement cannot even be written on
  the mathlib side, because `PMF` has no `+` and `Measure` has only
  `ℝ≥0∞`-conical `smul`.  The `statDist` calculus also lives here.
- **L1 — expectation, and the one-way transport into mathlib.**  Everything
  generic-probabilistic that mathlib already has is *imported* through the
  transport rather than reproved: variance, Chebyshev, Markov, Cauchy–Schwarz,
  Jensen, Bernoulli/Binomial, conditional expectation, KL.  A native proof at
  this level is a deliberate choice — justified when the statement lives below
  mathlib's reach (the signed layer) or when the proof is two lines and the fact
  is used constantly — never the default.
- **L2 — the information theory mathlib does not have.**  Shannon entropy,
  conditional entropy, mutual information and the chain rule, Pinsker,
  min-entropy, Rényi/collision entropy, guessing probability, distance from
  uniform, universal hashing, leftover hashing.  Built on L1, never on an
  application's local carrier.
- **L3 — the Maurer superstructure.**  Couplings of random systems, blinding,
  combiners, amplification, event-algebra probability.  Built on L2.

**Hypothesis discipline.**  Each statement carries the weakest of the three
distribution layers at which it is true — signed, `NonNeg`, or `isProbDist` —
not the strongest that makes the proof convenient.  Measured, with proofs and
counterexamples both, in `scratch/TransportProbe.lean`: bilinearity and the
`statDist` triangle inequality hold signed; monotonicity, Markov,
Cauchy–Schwarz and the `E[(f−c)²]` form of variance need `NonNeg`; Jensen and
the `E[f²]−E[f]²` form of variance need `weight = 1`.

**Consequences, in the imperative.**

1. A probabilistic or information-theoretic fact is defined at its tower level,
   in a module of that level, and never inside the application that first wants
   it.  If an application needs one, the fix is to add it below, not locally.
2. L2 is written to be *upstreamable*: stated on the general carrier with the
   weakest hypotheses, docstring citing the source, `UPSTREAM-CANDIDATE` marker.
   mathlib has no Shannon entropy today; if it acquires one, we want to align
   with it rather than collide.
3. Measure-theoretic instances (`MeasurableSpace`, `DiscreteMeasurableSpace`)
   are introduced at the proof site, never in a library-facing signature, so the
   transport stays invisible to callers.
4. When a fact already exists in a specialized form, generalize it in place and
   repoint the callers.  Do not leave two.

## 12. CC diagram visual design system (2026-08-06)

Source figures: Maurer11 Figs 3–4, MaRuTa12 Fig 1, Jost Figs 2.1–2.4
(all read visually).  The renderer implements THIS spec; features follow
the spec, never the reverse.

1. Geometry is semantic, never typographic: fixed grid sizes; labels
   middle-ellipsized at per-kind budgets (resource 12, converter 8;
   glyph names exempt), full name via title attr.  A label must never
   stretch layout.
2. Interface geography: honest parties horizontal (A left, B right),
   adversary interface at the BOTTOM (invariant across all source
   figures), FREE interface at the TOP and drawn dotted (Jost Fig 2.1;
   BMT18 p.4 — amended 2026-08-06, this item originally omitted F).
   Layout columns [A-converters | resource stack | B-converters];
   E-wires drop below; simulator below per Maurer11 Fig 3.  This is the
   n=2 SPECIALIZATION: item 14 generalizes it to a party ladder and
   governs whenever the interface set is not recognisably {A,B,E,F}.
3. Dashed border = specification boundary (the constructed system);
   solid = concrete systems.  One dashed nesting level rendered; deeper
   nesting collapses to a compound box.
4. Wires carry interface labels at boundary crossings; boxes stay
   near-empty.
5. Role palette (Maurer11): assumed #2563c4, constructed/ideal #c0392b,
   converter #1e8449, simulator #0e7c7b, game grey — ALWAYS duplicated
   by a non-color signal (border style / sigil) for print and
   accessibility.
6. Equations render as figure pairs: `#cc_diagram thm name` shows both
   sides of an equality with `≡` between (Maurer11 Fig 3 top/bottom).
7. The ASCII twin is a STRUCTURE receipt, deliberately not a picture;
   pins bind to it, layout evolves freely.
8. Visual test corpus (golden gallery, reviewed by eye each change):
   single · ∥×2 · ∥×3 · attach@party · attach@both · full construction
   with simulator (real & ideal) · blocked · nested · long-label stress
   · deep-chain stress · glyph channels · MaRuTa12-Fig-1 target.
   Gallery generated as HTML from the widget's own Html tree and
   inspected in a browser against the source figures.
9. Wiring rules (2026-08-06 critique round 1, from the source figures):
   a party's interface wire reaches EVERY resource in a parallel stack
   (vertical bus, MaRuTa12 Fig 1); the constructed dashed box shows its
   party interfaces protruding through the boundary left/right exactly
   as the adversary wire protrudes below (the dashed box IS a
   resource); bare resources carry short interface stubs — no floating
   boxes; serial converters at ONE interface chain horizontally
   outermost→innermost→resource (the monoid must be visible; cross-
   interface order is free by `attachAt_comm` and renders as flanks).
   No dangling wires: every endpoint lies on a box edge, a bus, or a
   labeled boundary crossing.
10. Rendering medium (2026-08-06, Marc's decision): diagrams are
    DYNAMIC HTML OBJECTS — live DOM divs (title/hover now; click/RPC
    interactivity later).  No SVG, no static pictures.  Precision is
    emitter-owned: the layout is computed in Lean from item 1's grid
    constants and emitted as absolutely-positioned divs inside a
    `position:relative` container; wires are 2px divs on an
    orthogonal-only grid.  Engine-owned layout (flexbox/grid) is
    banned inside a diagram — it is exactly what made wires miss
    their boxes in v3.
11. Machine-checked geometry gate: the gallery embeds a vanilla-JS
    self-audit (every wire endpoint on some box perimeter or wire
    within 0.75px; no label clipped beyond its budgeted ellipsis)
    writing a JSON report into `<pre id="geometry-audit">`; an empty
    violations list is the gate, read via headless Chrome.  Eyeball
    review (item 8) judges paper fidelity; the audit judges precision
    — both run on every renderer change.  EXTENSION (2026-08-06, from
    the Penpot mockup critique): the audit additionally checks
    (a) PORT-LADDER SYMMETRY — the wires meeting one edge of a box are
    deduped into rungs, and each rung's offset `d` from the box centre
    must have a partner `x` with |(d+x)/2| ≤ tol.  For a single port
    this IS the old rule (|d| ≤ tol — an attached pill shares its
    resource's port axis); for n ports it demands a ladder symmetric
    about the centre, which is what a multi-party box has.  A
    generalization, not a loosening: a wire that merely lands somewhere
    on an edge still fails.  (The original phrasing — "a wire's
    centerline equals the vertical center of EVERY box it touches" —
    is literally contradicted by item 14's n-party picture, where ports
    are off-centre by construction; corrected 2026-08-06 on the
    implementer's objection.)  (b) frame-pad SYMMETRY — every dashed
    boundary equals its content union + exactly (padX, padY) each side.
    Bounds containment alone is not an audit.
12. Interaction design (D1–D5, mockups frozen 2026-08-06 on the Penpot
    Page-1 zone; Marc ratified all ★ calls): fold marker = the DECK
    OUTLINE (1px grey rounded outline offset +3px behind the element;
    pure line work; visually disjoint from the constructed inner
    double border); hover highlight = 2px ROLE-COLOR OFFSET OUTLINE,
    never a fill; folded serial chains are labeled by the composed
    name under the budget middle-ellipsis (`enc∘…enc`), never a count
    form; ALL dashed regions (unfolded named regions AND collapsed
    compound boxes) carry their name at the TOP-LEFT CORNER per
    Maurer11 — centered names belong to leaf boxes only.  UI chrome
    (menus, rails, hover outlines) is exempt from frame-content in the
    geometry audit: a transient overlay must never resize a semantic
    specification boundary.  New tokens ratified: space.ui.deckOffset 3,
    color.ui.railBg #FAFAFA, space.ui.railWidth 290,
    color.ui.chromeBorder → {color.boundary}, font.ui.caption 10.

### The sourced grammar (2026-08-06 corpus survey, 27 of 30 papers swept)

Items 13–25 come from a visual sweep of the whole `papers/` corpus across
all three layers.  Provenance discipline: every item carries its citation;
items marked ✓ were verified FIRST-HAND at the page by the author of this
section, the rest are agent reads and are marked ⚠ where resolution-
sensitive.  The survey exists because an earlier thesis-only brief
produced the false negative "the literature has no multi-party wiring
diagram" — a claim about what the papers do NOT do is only valid after a
corpus-wide figure sweep.

13. Shape codes the KIND; colour only reinforces it.  Resource =
    rectangle, converter = rounded box (Jost Fig 2.1 caption p.27: "we
    depict resources using rectangular boxes and converters using
    rounded boxes"; PorRen22 Fig 4 caption p.9, restated Fig 1 p.5).
    These are the only captions in the corpus that STATE a convention
    and they agree, so this outranks the dissent — Maurer11 Figs 3–4
    (all dashed rectangles, colour alone), MaRuTa12/CoMaTa13 (all
    rounded, position alone), MMPRT18, and BBM18 Fig 4 ✓ (all plain
    rectangles: converters, resources and simulators alike).  Colour-only
    coding is exactly the accessibility failure item 5 forbids, so we
    depart from that camp knowingly.  A SIMULATOR IS A CONVERTER
    (PorRen22 §II.D.c p.10) and takes the rounded shape; never an
    ellipse.  Scoped to the CC view: the RS view draws no converters and
    distinguishes by SHADING (Maurer13b Fig 1 p.3154 — grey rounded
    composite over white sharp members), so "rounded" never means two
    things in one picture.
14. n-party layout: one converter box per party, STACKED vertically on
    the party flank, feeding a parallel resource stack inside the
    boundary (BBM18 Fig 4 p.14 ✓ — P₁/P₂/P₃ each into its own `scr_Ψ`,
    braided into the Mem/CA/Net stack).  Item 2's A-left / B-right /
    E-below / F-above geography is the n=2 specialization (Jost Fig 2.1)
    and applies only when the interface set is recognisably {A,B,E,F}.
    `Flank` must therefore carry an INDEX, not a four-way enum; an
    unrecognised interface takes a slot by index and never degrades the
    spine to fallback — "fallback" must mean genuinely unclassifiable
    (an interface with no printable name), never merely n>2.  The index
    cannot come from the per-interface classifier, which cannot know
    spine order: the classifier emits a party SLOT and a later
    geography pass numbers the slots (implementer's clarification,
    2026-08-06).  Alternates if ever needed: horizontal row with
    ellipsis (2021-156 Fig 9 p.9; 2105.05949 Fig 1b), four-sided star
    (LiuMau20 Fig 1 p.6; Maurer11 fn.9 p.44 "star-shaped topology").
15. Corruption is marked by WIRE TOPOLOGY, never by colour or
    decoration — but the marked wire is the INTRUDER interface, not the
    party interface (BBM18 Fig 4 p.14 ✓, caption: "we do not depict the
    filter explicitly, but only indicate their effect, e.g., by not
    giving output at intruder interfaces M₁ and M₃").  Precisely: every
    party interface Pᵢ crosses the boundary — they are the constructed
    resource's own interfaces.  Compromise is modelled by a per-party
    intruder interface Mᵢ, drawn LIVE (an arrow crossing the boundary to
    a labelled external port) when unfiltered, and as a STUB that stops
    without exiting when the filter kills it.  Absence of output IS the
    filter's rendering.  A wire that stops in a visible GAP before a box
    means that interface has no effect (BMT18 Fig 6 p.18, captioned).
    No red corruption ring — unsourced, and the topology already says
    it.  Alternates: box substitution by an arbitrary system (MMPRT18
    Fig 2 p.3); a pseudocode section annotated "(additional)" (Jost
    Fig 5.9).
16. Simulator placement.  DEFAULT: one simulator per dishonest
    interface, each in series on its own wire (BBM18 Fig 4 p.14 ✓ —
    σ_M₂ and σ_E drawn as two separate boxes; 2105.05949 Thm 5 p.17 —
    s_A, s_B, s_C one per party column).  SINGLE-BUNDLE CASE: one pill
    in series on the whole adversarial bundle, which may fan out into
    several outside stubs (CoMaTa13 Fig 1R, E → E.1/E.2) and may span a
    stack of 2–3 resources at ONE interface (Jost Fig 4.3, p.51).  In
    every case HONEST INTERFACES BYPASS THE SIMULATOR ENTIRELY (BBM18
    Fig 4 ✓ — P₁/P₂/P₃ wire straight into SecNT; 2021-156 Fig 9, where
    BACKDOOR is intercepted and IO is not).  A simulator never spans
    parties.
17. Indexed families render as first, second, ellipsis, last with a bus
    fan-out — `F₁ F₂ ⋯ F_{n-1} Fₙ` (Lanzenberger thesis Fig 2.2);
    vertically stacked members use a vertical ellipsis (2026-1071 Fig 9
    p.22).  A WIDE box spanning several wires denotes a JOINT action,
    not a family (2105.05949 Fig 1d, Fig 2a) — never use one to
    abbreviate a family.
18. Line-style vocabulary, fixed and exclusive.  DASHED = the
    specification boundary (MaRuTa12 p.3: "the outer interfaces of enc
    and dec are the interfaces of the constructed (dashed) system";
    CoMaTa13 Fig 1; MMPRT18 Fig 3; BBM18 Fig 4 ✓).  DOTTED = a FREE
    interface, accessed directly by the distinguisher (BMT18 Fig 1 p.2,
    defined p.4; Jost Fig 2.1's F at top).  No third semantic stroke.
    This is deliberately NARROWER than the sources and item 3 should say
    so rather than implying they agree: Jost dashes four distinct things
    (grouping p.49, context p.50, naming shorthand Fig 4.5, replaced
    subsystem Fig 6.5) and reserves dotted for the indistinguishability
    boundary (p.49) with dash-dot for the filter (p.51).  We do not
    adopt dotted-for-indistinguishability: it would collide with F, and
    item 6's equation pair already carries indistinguishability.
19. A wire denotes COMPOSITION.  Therefore no wire-like connector may
    join an object to a DESCRIPTION of that object — pseudocode, a
    legend, an annotation.  A description relates to its object by
    IN-PLACE SUBSTITUTION or SHARED NAME only.  The corpus obeys this
    exactly: Jost draws dashed leaders from pseudocode to a LIFELINE in
    message-sequence charts (where a line is a time axis and cannot
    assert composition) and draws no leader in any of his box-and-wire
    diagrams; elsewhere leaders annotate only bare glyphs (Maurer11
    Fig 1 p.36 "addition modulo 2" → XOR).  Paired figures are the
    papers' device: Jost Fig 2.1 draws the diagram, Fig 2.2 gives its
    pseudocode, joined by name alone.
20. Inspecting a leaf is SEMANTIC ZOOM, not magnification: the lens
    swaps the REPRESENTATION, since pseudocode is a different rendering
    of the same object, not a larger picture of it.  Technique:
    focus+context / magic lens (Bier et al., Toolglass and Magic Lenses;
    survey: Cockburn, Karlson & Bederson), in the PEEK VIEW form (VS
    Code).  (a) OVERLAY, never inline reflow — geometry is emitter-
    computed and machine-audited, and reflow would thrash layout and
    invalidate the item-11 gate on every inspection; an overlay leaves
    coordinates untouched and is chrome, hence exempt from frame-content
    by item 12.  (b) ANCHORED OVER ITS OBJECT — position carries the
    relation, so item 19's category error cannot arise.  (c) CONTEXT
    PRESERVED — the diagram stays visible beneath, dimmed by opacity on
    the diagram layer; never hidden, never a scrim.  (d) PAPER STYLE
    HOLDS — 1px bordered opaque panel at token radius; no shadows,
    gradients, or icons.  (e) DISMISSAL — drawn small cross plus
    click-outside / Esc, in the D4 chrome treatment.  (f) STATIC EXPORT
    — with no hover, a lensed view degrades to item 19's paired figures.
21. Pseudocode panels carry item 13's shape rule: a Resource panel has
    SHARP corners, a Converter or Simulator panel ROUNDED (Jost Fig 2.4
    p.30 places both in one float) ⚠ pixel-level, stated nowhere in the
    text.  Panel identity is a grey rounded tab overlapping the TOP-LEFT
    border carrying the kind keyword then the name (JosMau20, all
    figures; BBM18 Figs 3/5 ✓ — "Resource CAₙ", "Resource Netₙ").
    Solid sub-box = an unfiltered/dishonest extension; dashed sub-box =
    event bookkeeping (JosMau20 Figs 3, 6, 7, 8).
22. RS layer vocabulary.  The distinguisher sits BESIDE the system,
    joined by a labelled query/response ARROW PAIR (Xᵢ in, Yᵢ out), with
    the decision bit Z leaving on the far side; the MBO / game flag
    leaves the TOP of the enclosing box (Maurer13b Fig 1 p.3154).
    OUT OF SCOPE: structure graphs (BPR05, BDPV08).  Their nodes are not
    systems and their edges are not interfaces — a collision graph is a
    combinatorial proof artifact needing a graph-layout renderer, not
    this box-and-wire language.  Surveyed and parked (STATUS).  A
    randomized or
    sampling step is a SQUIGGLY arrow, deterministic a straight one
    (Lanzenberger Fig 3.2).  Cascade is drawn in WRITTEN order
    (MauPie04 Fig 1 p.11).  Transcripts and query ladders are drawn
    NOWHERE in the corpus; if we need one it is ours and must be
    labelled as such.
23. Hybrid and game sequences.  The source distinguishes otherwise-
    identical hybrids by BORDER STYLE (2026-1071 Fig 13: dashed /
    dotted / dash-dot for G1/G2/G3), but WE CANNOT: item 18 spends
    dashed on the specification boundary and dotted on the free
    interface, so a hybrid carrying both has no stroke left.  Use a
    CORNER BADGE instead (the device item 24 already sanctions for ε) —
    still a non-colour signal, so item 5 is satisfied unaided.  Border
    style stays available only for a figure with no boundary and no
    free interface, and never as the primary channel.  (Collision
    found by the implementer, 2026-08-06.)  A
    proof chain is a row of picture-equalities with the step number set
    OVER each relation symbol (2105.05949 Fig 6, whose text states the
    pictures ARE the proof).  Hybrid-only pseudocode lines are boxed,
    solid vs dashed by which hybrid owns them (BBM18 App. C p.36; the
    same device appears in Fig 3 p.13 ✓, where boxed statements mark the
    weaker game variant).
24. What the literature does NOT picture, and our answer.  A
    SPECIFICATION — a set of resources — is drawn NOWHERE in 27 swept
    papers, including the two most committed to the notion: BMT18
    defines specifications as sets (§2.2) and uses them throughout, yet
    draws each with the same plain rectangle as a single resource; Jost
    p.30 writes "we allow ourselves to just write a resource R instead
    of a singleton specification {R}".  DECLINE TO INVENT A SET
    RENDERING.  Draw a specification exactly as its representative
    resource and carry the set-ness in the LABEL and the relation
    symbol, which the ASCII twin already pins losslessly.  Reasons: a
    blob or cloud would be the only element in the system with no
    counterpart in any source and would read as decoration; the set-ness
    is fully carried by the ε superscript and the subset in the
    construction statement; and 27 papers declining the same picture is
    a considered convention, not an oversight.  ONE NARROW EXCEPTION:
    when a figure's subject IS the relaxation, render ε as a superscript
    badge at the box corner — a label, not a new shape, not a halo.
    Also undrawn anywhere, hence ours if we build them: transcripts,
    query ladders, ε-balls.  The AC layer draws NOTHING AT ALL
    (MauRen11 and MauRen16 contain zero figures across 43 pages; MauRen11
    fn.27 p.18 defends the symbolic choice: interface superscripts are
    "necessary to maintain linear expressions ... An alternative would be
    to use formulas that are not linear but make use of the two-
    dimensional plain") — so every AC rendering we ship is ours by
    construction and must be labelled as an extension.
25. New tokens: radius.simulator → {radius.converter};
    size.simulator.w (per-interface pill) and size.simulator.span
    (single-bundle pill); color.role.free; stroke.free → dotted;
    size.party.pitch; size.gap.noEffect (BMT18 Fig 6's dead-end gap);
    space.lensPad; color.ui.lensDim (opacity, not a colour);
    size.lens.maxW / size.lens.maxH; font.ui.stepLabel.  New components:
    Simulator (rounded, dotted border — replacing the ellipse),
    EllipsisMember, Lens, and EquationPair (two diagrams with the
    relation symbol between them, horizontal per PorRen22 Fig 5).
    A STUB IS NOT A COMPONENT — party, intruder and free stubs are
    WIRES carrying an open-end marker and a stroke flag, which is the
    right factoring for a positioned-primitive emitter: a stub is the
    ABSENCE of a crossing, not an object (implementer's correction,
    2026-08-06).  `size.simulator.span` is cosmetic and unimplemented;
    the semantics item 16 requires — one pill, one wire, one interface
    — is what ships.  NO StructureNode component (item 22 — structure
    graphs are out of scope) and NO SpecSet component (item 24).
26. THE PANEL'S STATE LIVES IN THE SOURCE FILE (D4, 2026-08-06).
    ProofWidgets' `mk_rpc_widget%` components cannot hold React state
    and cannot pass closures to children, so "click → menu → click →
    term changes" cannot be a client-side state machine.  It must not
    be one anyway: the state of a PROOF belongs in the file.  Every
    click is a `MakeEditLink` LSP edit that rewrites the `#cc_panel`
    command itself (a node click writes `at [inner, left]`, a move
    click appends to `with [...]`, `undo` drops the last), and the
    panel is a pure function of the command it re-elaborates.  A panel
    that DRAWS is therefore a kernel receipt: every redraw re-runs the
    move's `Kernel.check`.  Consequences, each a named substitute for
    something §12 asked for and the platform forbids:
    (a) item 12's "copy as calc" cannot copy (no clipboard without a
        closure on a DOM node) → `write calc below`, which inserts the
        finished chain into the file; strictly better in an editor.
    (b) item 20(e)'s "click-outside / Esc" needs global handlers →
        ships as the drawn cross plus re-clicking the node as a toggle.
    (c) the hover outline is drawn by the CHROME, not the box: the hit
        target sits above the box so `.cc-box:hover` never fires.  The
        hit copies the box's `color`, so `currentColor` IS the role
        colour and item 12's rule is preserved.
27. D1 VIEW DIRECTIVES AND D4 ADDRESSING ARE INCOMPATIBLE — §12 did not
    anticipate this.  A `fold` collapses several term nodes into one
    box, so every later node's path names the WRONG subterm.  Therefore
    `#cc_panel` accepts no view clause, and the emitter stamps a
    fold-collapsed box as UNADDRESSABLE (no `cc-at-` class): it draws,
    but offers no moves.  The two features compose only in one
    direction — a move may emit a view directive (so a merged pill can
    re-label as `enc∘enc`), never the reverse.
28. A CONNECTION IS DRAWN, AND IT IS A FORK (Jost Fig. 2.1, printed
    p. 27 ✓ — read first-hand at the page, 2026-08-08).  Jost's γ
    (`α ••[γ] R`, `Converter.attachAlong`) is a converter reaching TWO
    interfaces at once, and his own figure draws it as ONE ROUNDED BOX
    SPANNING ITS REACH: π_ε^A is a single tall converter whose vertical
    extent covers the whole `Key`-over-`AuthChan` stack; its INNER edge
    carries one horizontal wire per interface reached (one into `Key`,
    one into `AuthChan`, each on that resource's own axis), and its
    OUTER edge carries exactly one wire, on the box's own axis, labelled
    `A`.  π_ε^B mirrors it.  The two inner wires are UNLABELLED in the
    source: Jost carries the reach topologically, by which boxes the
    wires land on, and the prose supplies the names ("interface A of
    AuthChan", p. 27).  No merge is drawn anywhere — and neither do we
    draw one: merging is the isometry `close_mergeAlong`, not an object.
    (Also seen first-hand and NOT adopted: Jost routes the free `F` wire
    BEHIND the `Key` box, with a jog at each border, to reach `AuthChan`
    underneath.  A wire crossing a box it does not connect to is a
    grammar element we do not have and do not need — item 9a's buses run
    outside the stack — but it is in the source, so it is recorded here
    rather than rediscovered later as a gap.)

    WE DRAW: one converter pill grown by one `size.conn.forkPitch` per
    extra branch (that is the span), a FORK on its core-facing edge —
    one rung per interface reached, symmetric about the pill's axis, so
    item 11(a) holds by construction — and, our one addition to the
    source, EACH BRANCH LABELLED WITH THE INTERFACE IT REACHES.  That is
    not a breach of item 4 ("labels at boundary crossings, boxes
    near-empty"): the interfaces a connection reaches are CONSUMED by the
    converter and never cross the boundary, so the branch IS their
    outermost visible point, which is exactly what item 4 asks for.  We
    add it because the defect this item fixes was precisely that a
    reader could not see WHICH interfaces a connection reached, and
    because our rows are not always distinguishable by name the way
    `Key` and `AuthChan` are.  The OUTER crossing keeps the connection's
    own name: that wire is Jost's `I_out`, the interface the connection
    PRODUCED, and the term offers no other name for it.

    REJECTED: (a) reproducing Jost's box height literally, spanning the
    whole core — it makes a converter's height a function of what it is
    attached to and spends item 1's fixed grid for no information the
    fork does not already carry; (b) drawing the merge as its own box —
    unsourced, and it would put an object where the algebra has an
    isometry; (c) two separate pills — that is two attachments, a
    different term; (d) leaving the branches unlabelled as Jost does —
    it works in a figure whose prose names the interfaces and whose rows
    are `Key` and `AuthChan`, and fails here.

    HONEST SCOPE, stated rather than hidden.  (i) Each branch runs to its
    OWN bus and each bus fans into EVERY row of the stack, per item 9a —
    so the picture says "these two interfaces", not "this one of `Key`
    and that one of `AuthChan`".  Routing each branch to the single row
    it names is only sound when nothing between the connection and the
    core has re-indexed the interface set (it has, in
    `dec^{γ^B} enc^{γ^A} [KEY, AUT]`, for the outer connection), and
    item 9a's bus is ALREADY this imprecise for a plain
    `α •[Sum.inl a] (KEY ∥ AUT)` — so this is an item-9 question, not a
    connection question, and is left open there rather than fixed here
    for one node kind.  (ii) The fork is drawn on the PARTY flanks,
    where Jost draws connections; a connection landing on a
    perpendicular flank (E below, F above — reachable only for a
    simulator-role converter) draws its spanning pill with a single
    lead.  (iii) New tokens: `size.conn.forkPitch` 22,
    `size.conn.lead` 34 (the extra inner lead the branch labels need).
    (iv) New machine check, CONNECTION FORK: a box stamped `cc-conn-<n>`
    must have ONE edge carrying exactly `n` rungs at exactly the
    emitter's own fork ladder (`Diagram.forkPitch`, read from the
    emitter as the pads are).  It is strictly stronger than item 11(a)
    on that box and was mutation-tested against it: item 11(a) stays
    silent both when the fork draws the wrong NUMBER of branches and
    when it draws them symmetric at the wrong PITCH.  (v) The ASCII twin
    prints the reach in `⟨…⟩` — it is term structure (`γ.first`,
    `γ.second`), so item 7's structure receipt owes it a line.

29. A WIRE IS A TWO-BEND ORTHOGONAL ROUTE ON ITS OWN CHANNEL TRACK
    (2026-08-08).  Item 10 fixed the MEDIUM (positioned divs, orthogonal
    grid, no SVG) and item 9 fixed the ENDPOINTS ("no dangling wires"),
    but nothing said what happens between them, and the result looked
    undesigned: leads jogged twice in four pixels, buses braided, and the
    only reason no wire was worse than the next was luck.

    WE DRAW: horizontal → bend → vertical → bend → horizontal.  At most
    TWO bends per wire, and a level wire is ONE straight segment with no
    bend at all — which, after item 30's band discipline, is what most
    wires are (14 bends over the whole 43-diagram corpus).  A BEND is its
    own primitive (`Prim.bend`): a `(r+1) × (r+1)` cell carrying two
    adjacent borders and the matching corner radius, which CSS collapses
    into exactly one quarter arc.  It is a primitive rather than a
    special case of a wire because item 10's rule is that every drawn
    thing is a positioned rectangle the audit can measure — a bend has to
    BE a box, and its two arc ends have to be readable from its rect, so
    it carries `data-corner` and the audit reads its endpoints back.
    `radius.bend` = 6 is a CONSTANT: a route with no room for it falls
    back to SHARP corners rather than to a smaller radius, because a
    radius that shrank when a wire was cramped would encode crowding, and
    item 1 says geometry is semantic, never typographic.

    THE CHANNEL is the strip between a flank's converters and the core.
    It carries one vertical TRACK per bending wire at `space.track` = 10,
    and the track ORDER is the whole design — it is what makes the
    ordering non-crossing rather than accidentally non-crossing.  Wire i
    must turn FURTHER FROM THE FLANK than wire j exactly when j's entry
    lies strictly inside i's vertical span; otherwise i would have to
    dive across j's lead.  On an order-preserving matching (which item 30
    supplies) that relation is a strict partial order — a two-cycle would
    need `tᵢ > eⱼ` and `tⱼ < eᵢ` at once, i.e. `tᵢ > eⱼ > eᵢ > tⱼ > tᵢ` —
    so ANY linear extension serves and the emitter takes the
    longest-chain rank.  The perpendicular flanks use the same discipline
    transposed: the jog from the cap ladder out to a column axis is
    STAGGERED by rank, outermost column first.  At m ≤ 2 every rank is 0
    and nothing moves; at m ≥ 4 the unstaggered form drew two collinear
    jogs on top of each other — a defect found by item 30's check and not
    by any eye, since the corpus has no four-column case.

    PROVENANCE: OURS, and labelled so.  The corpus draws wires but states
    no routing rule anywhere (the figures are hand-drawn; MaRuTa12 Fig. 1,
    BBM18 Fig. 4 ✓ and Jost Figs. 2.1–2.4 all route by eye), so item 24's
    discipline applies — this is an extension, not a reading.  What IS
    sourced is the CONSTRAINT the routing must respect: Jost Fig. 2.1
    routes the free `F` wire BEHIND the `Key` box (recorded in item 28),
    a grammar element we do not have, so our routes must never need one.

    REJECTED: (a) splines or diagonals — item 10's grid is orthogonal and
    a diagonal is not a positioned rectangle, so the audit could not
    measure it; (b) a radius that always shrinks to fit — see above;
    (c) one shared track per flank — collinear verticals merge two
    interfaces into one drawn line, which item 9's "distinct interfaces
    are distinct wires" forbids and item 30's overlap check now catches;
    (d) a bend as a rotated or clipped wire — a CSS transform makes
    `getBoundingClientRect` report the transformed box, so the geometry
    audit would go blind exactly where the geometry is hardest;
    (e) a general routing solver — the shapes this grammar makes are a
    matching in a strip, and a partial order beats a search.
    New tokens: `radius.bend` 6, `space.track` 10.

30. THE DIAGRAM IS A PLANE GRAPH — AND ITEM 9a IS AMENDED TO MAKE IT ONE
    (2026-08-08).

    (a) THE AMENDMENT, stated first because everything else depends on
    it.  Item 9a says a party's interface wire reaches EVERY resource in
    a parallel stack.  Under the algebra as it now stands that is not
    merely imprecise (which is how item 28's honest scope (i) recorded
    it) — it is FALSE.  `∥` is Jost's DISJOINT parallel composition
    (`ResourceSystem.par : … S I → … S J → … S (I ⊕ J)`, migrated
    2026-08), so `Sum.inl a` is an interface of the LEFT component and of
    nothing else.  Item 9a cites MaRuTa12 Fig. 1, and the reading was
    wrong: the wire that reaches both `KEY` and `AUT` in that figure is
    `enc^A`, a CONNECTION — Jost's γ, `Converter.attachAlong` — which is
    a DIFFERENT TERM and already has its own rendering in item 28.  Item
    9a generalized one figure's connection into a rule about every
    attachment.  AMENDED: a `•[i]` wire lands on the ONE row that `i`
    names.  The emitter reads the row off the term, not off a heuristic:
    the `Sum.inl`/`Sum.inr` prefix of the printed interface IS the path
    into the `∥` tree, the same path `flattenParAt` walks.  The
    consequence is a gain, not a loss — a row that no spine node names
    keeps its own interfaces and crosses the boundary at its own axis,
    which is MaRuTa12 Fig. 1's `AUT` line, the very line the bus used to
    braid into everything else.

    (b) THE INVARIANT: no two wire segments meet except at shared
    endpoints.  A T-junction — an endpoint lying in another wire's
    interior — stays legal and is what a fan-out is made of; what is
    banned is an interior meeting an interior, two collinear segments
    sharing more than a point, and a segment cutting a box.

    (c) HOW IT IS OBTAINED, in three moves.  BANDS: the core stack tiles
    into disjoint horizontal strips, one per row, and every pill, lead,
    rung and crossing belonging to a row lives inside that row's band —
    so wires of different rows cannot meet, and the untouched-row stub of
    (a) passes cleanly under every converter.  A band grows to seat its
    flank's converter cluster; that is why three attachments at one
    resource make the picture taller rather than tangled.  TARGET ORDER:
    a flank's rows are ordered by the core row they land on.  This spends
    a freedom item 9 already granted — "cross-interface order is free by
    `attachAt_comm` and renders as flanks" — so the order that was
    arbitrary now buys the matching's monotonicity.  TRACKS: item 29.
    Where a row's entries already form a symmetric ladder that fits its
    edge, they ARE its rungs, so the wires are straight and a
    connection's fork reads exactly as Jost Fig. 2.1 draws it.

    (d) WHERE THE TERM DOES NOT NAME A ROW: the stack BRACKET.
    `attachAlong` lands in `rest ⊕ Unit`, so a node OUTSIDE a connection
    is written against a re-indexed interface set and its `Sum` prefix
    means nothing about the core's rows — the eq.-(1) shape
    `dec^{γᴮ} enc^{γᴬ} [KEY, AUT]` is exactly this case.  Then the flank
    draws the composite's EDGE: one vertical at `space.busLead` from the
    stack, one spur to each row's axis, the entries landing on it.  It is
    not a wire and asserts no composition; it is item 24's move — when
    the picture cannot say which member, draw the composite as one
    object.  Granularity is PER FLANK, never per wire: a bracket spans
    every band a resolved wire would have to cross, so a mixed flank
    cannot be drawn planar.  The same bracket serves the side with no
    converters at all, where "all the rows'" is the true answer.

    (e) WHAT IS TRUE, EXACTLY.  The conjecture this item was built to
    test — "every diagram this grammar can produce is planar by
    construction, because attachment consumes what it reaches and
    produces one interface, so converters at a flank are strictly nested
    by depth and their reach sets are laminar" — is FALSE, in three
    independent places, and the record matters more than the fix.
    (i) `Converter.attachAt` is an ENDO-operation on the interface set
    (`… S I → … S I`); only `attachAlong` consumes.  So an outer
    converter may attach at ANY interface, and nesting-by-depth is not a
    theorem of the grammar.  (ii) Item 9a's bus was not a drawing
    accident: n buses each fanning into m rows is `K_{n,m}` with the
    boxes as solid obstacles, NON-PLANAR AS AN ABSTRACT GRAPH at
    n = m = 3, so no router could ever have fixed it; at n = 3, m = 2 the
    old corpus measured 3 crossings, and 13 across three diagrams.
    (iii) Even with (a) and (c) in place, reach sets are laminar as SETS
    (each interface is consumed at most once, so the reaches form a
    forest) but NOT as INTERVALS of the row order, and the row order is
    term structure, not a rendering choice.  `α ••[γ] (enc •[i] R)` over
    `A ∥ B ∥ C`, with γ reaching rows 0 and 2 and `i` naming row 1, is
    constructible, is drawn with one crossing, and no flank order fixes
    it — the two branches are rigid on one pill, so `{0,2}` straddles
    `{1}` whichever side the plain pill takes.
    THE STATEMENT THAT HOLDS: at each flank, order the spine nodes by the
    core rows they reach; the picture is planar iff those reach sets are
    pairwise NON-CROSSING INTERVALS of the row order.  Sufficient, and
    covering the whole corpus and every source figure: at most one
    connection per flank, every plain attachment naming one row.  This is
    a property of the TERM, so the emitter cannot guarantee it and does
    not pretend to — it is exactly what (f) measures.

    (f) THE MACHINE CHECK, and its mutation receipt.  The gallery audit
    gains `wire-crossing`, `wire-overlap` and `wire-through-box`, over
    the wires plus each bend's sharp-corner L (a conservative
    over-approximation of the arc, so the check can only be too strict).
    A check nobody has seen fail is folklore, so
    `.lake/cc_planarity_mutation.html` is written on every build: two
    hand-made figures differing ONLY in which of two leads turns first,
    every wire `data-open="12"` and no boxes, frames or labels, so no
    other check can speak.  Control 0 violations; mutant 2
    `wire-crossing`.  The interleaved counterexample of (e) reports
    exactly 1.  Gallery: 43 diagrams, 0 violations.

    (g) REJECTED: (a) keeping item 9a and routing around it — impossible,
    see (e)(ii); (b) dropping the untouched rows' stubs instead of
    banding — it leaves a resource in the picture with no wires at all,
    which reads as a rendering failure; (c) per-wire bracket granularity
    — see (d); (d) reordering the `∥` rows to make a reach contiguous —
    `par` is not commutative, the row order is the term's, and a picture
    that silently permutes a stack is worse than one that crosses;
    (e) scoping the planarity check to what the emitter can guarantee —
    a gate with a known exception is not a gate, and (e)'s counterexample
    is precisely the thing a reader must be told about.

31. A CONNECTION'S BRANCH LANDS ON THE BOX THAT OWNS ITS INTERFACE — AND
    THE AUDIT CHECKS THAT IT DOES (2026-08-08).

    THE DEFECT, and it is worth stating precisely because the audit
    reported ZERO violations while it shipped.  The eq.-(1) shape
    `dec^{γᴮ} enc^{γᴬ} [KEY, AUT]` drew both connections stacked on one
    flank, all four branches ending on item 30(d)'s stack BRACKET, so
    every branch asserted a reach into BOTH rows; and the two branches of
    `enc^{γᴬ}` were both labelled `u`, because the label was the printed
    interface's last component and `Sum.inl Party.u`/`Sum.inr Party.u`
    have the same one.  Nothing measured was wrong.  Every wire was on a
    box edge or another wire, every ladder symmetric, every frame pad
    exact, the whole drawing planar.

    (a) THE CAUSE.  Item 28's honest scope (i) and item 30(d) both blamed
    re-indexing: `attachAlong` lands in `rest ⊕ Unit`, so `γᴮ.first =
    Sum.inl Comp.key` carries the MERGE tag, not a step into the `∥`
    tree, and reading a row off it is a category error (it would send
    `Comp.key` and `Comp.aut` to the same row).  True — but the
    conclusion drawn from it was wrong twice over.  First, the emitter
    refused to read the outer connection AT ALL, and item 30(d)'s
    per-flank granularity then demoted the INNER connection with it,
    whose `Sum.inl Party.u`/`Sum.inr Party.u` do name rows.  Second, the
    refusal was unnecessary: an index into `rest` is pushed back into the
    base set by the inner connection's own `Connection.untouched`, which
    is a function the algebra already has.  `Diagram.descendInterface`
    walks the carrier's spine doing exactly that (`attachAlong` peels a
    `Sum.inl` through `γ.untouched`, `Sum.inr ()` names the inner
    converter and reaches no base interface, `•[i]`/`⊣[i]`/scalar `•`
    pass through), and `γᴮ` resolves to `Sum.inl Party.v`, `Sum.inr
    Party.v` — Jost Fig. 2.1's π_ε^B reaching interface B of `Key` and of
    `AuthChan`.  Item 28's scope (i) is CLOSED for connections; it stands
    for plain attachments, whose own index is not descended.

    (b) A CONNECTION IS PLACED BY THE INTERFACES IT REACHES, not by γ's
    printed name.  γ's name is not an interface and classified to a
    numbered slot, which is why both connections stacked on one flank.
    With the descent, `γᴬ` reaches `u` twice and `γᴮ` reaches `v` twice,
    so they take opposite flanks and the picture becomes Fig. 2.1: π^A
    left, π^B right, each forking to both rows, no crossing.  Only when
    every branch agrees on a paper side; a γ with one foot on A and one
    on B (`gammaAB`) belongs to neither and keeps its slot.

    (c) A FORK MAY SPAN ROWS, so item 30(c)'s bands are amended: a
    cluster landing on m rows books an m-th share of each band, and a
    flank group is centred on the MEAN of the axes of the rows it lands
    on rather than on one band's centre.  For a single target that IS the
    band centre, so nothing else moves; for a two-row fork it puts the
    pill between the rows and the two branches leave it symmetrically.

    (d) THE BRANCH LABEL IS A QUALIFIED INTERFACE.  SOURCED, Jost printed
    p. 27 (PDF p. 43): "When considering a composed resource, such as
    [AuthChan, Key], then we address a party's interfaces by referring to
    the corresponding atomic resource's name, e.g., interface A of
    AuthChan" — used again on p. 28 and in Fig. 2.3's pseudo-code ("at
    interface A of Key").  So a branch reads `AUT.a`, not `a`.  Two
    conditions, both from the source: the qualification is for COMPOSED
    resources, so a one-row core keeps the bare letter; and it must
    ADDRESS, so when two rows carry the same name (`toyR ∥ toyR`) the
    name addresses nothing and the row's POSITION is used instead —
    `1.u` and `2.u`.  The `title` carries Jost's sentence itself.
    Budgets are per KIND (item 1), so this gets its own: `budget.branch`
    12.  The same reading fixes the flank crossing of a connection, which
    is tagged with γ's NAME and was metered at the 6-codepoint INTERFACE
    budget — that, not any pixel clipping, is what printed `gam…AB`
    (`.cc-tag` sets no width and no overflow, so a tag is never clipped).
    New: `budget.connection` 10, and a crossing tag is pushed outward
    when centring it on its stub would lay it across the frame.

    (e) THE NEW MACHINE CHECK, TARGET CORRECTNESS, because none of the
    above is visible to a measurement.  A lead's last segment carries
    `data-target="k"` — the emitter's own claim about which core row owns
    the interface that wire names — and that row's box carries
    `cc-row-k`; the audit reads the claim back and requires an endpoint
    of the segment to lie on that box's perimeter.  The stamp is carried
    on the item-30(d) BRACKET path too, deliberately: a branch that names
    a row and is nevertheless drawn onto a rail serving every row is the
    defect itself, and must not go silent because the emitter declined to
    make a claim.  A row with no single box (an unfolded region) is not
    marked and its leads are not stamped — silent rather than wrong.
    Second check, BRANCH LABELS ARE DISTINCT: `γ.split` is an
    equivalence, so `γ.first ≠ γ.second` always, and two branches of one
    `data-fork` sharing a label can only mean the picture dropped what
    tells them apart.  No correct drawing can trip either.

    (f) THE MUTATION RECEIPT, `.lake/cc_target_mutation.html`, written on
    every build.  Control: one lead, stamped and drawn to the row it
    names.  Mutant: the SAME lead drawn to the other row — same axis,
    same length, both endpoints on a box edge at that box's centre,
    nothing through a box, nothing crossing — 1 `wrong-target`.
    REGRESSION: the shipped eq.-(1) drawing rebuilt by hand at the
    coordinates the old emitter printed (rail, two spurs, two stamped
    branches ending on the rail) — 2 `wrong-target`, and every older
    check passes it.  Label control/mutant: 0 and 1
    `duplicate-branch-label`.  Gallery: 43 diagrams, 42 targeted leads,
    5 labelled forks, 0 violations.

    (g) ROUTING, two changes found by LOOKING at the render and not by
    the audit.  `space.leadIn` 16: the first channel track sat one
    `space.track` from the flank and a bend eats `radius.bend`, so a lead
    turned FOUR pixels out of its pill and three leads read as one blob;
    every lead now gets `leadIn - bendR` of straight wire before it may
    turn.  And a branch label now rides the segment that ARRIVES, not the
    one that leaves: at the entry height it floated off its own wire and
    sat next to a neighbour's.  Item 29's tie-break, which is free
    (equal rank = incomparable, any linear extension is planar), is spent
    on the same goal: among equal ranks the SHALLOWEST jog turns first,
    so the corner with the least vertical room sits at the edge of the
    fan rather than between two others.

    (h) HONEST RESIDUAL.  `connection beside a plain attachment` still
    draws one lead with SHARP corners.  Three entries (a 22-pitch fork
    plus one plain lead) meet a 14-pitch three-rung ladder, and the
    middle entry is 10px from the middle rung whatever the pitches are;
    two `radius.bend` = 6 arcs need 12.  Item 29 forbids shrinking the
    radius, so the fallback is correct and the drawing is as good as this
    configuration allows.  Recorded, not hidden.

    (i) REJECTED: (a) per-wire bracket granularity, again — item 30(d)'s
    argument is unchanged, and the fix is to make the wire readable, not
    to mix granularities; (b) making `Shape.reach` hold the descended
    interfaces — the ASCII receipt's `⟨…⟩` is `γ.first`/`γ.second`, term
    structure, and item 7 pins it; the descent is a SECOND field
    (`reachAt`) and the two are documented as different facts;
    (c) labelling every branch `resource.interface` including single-row
    cores — Jost's convention is for composed resources and the
    qualification would be noise; (d) checking the emitter's INTENT — the
    target check verifies the drawing against the claim, and cannot
    verify the claim; what guards the claim is the descent being the
    algebra's own `untouched` rather than string surgery.
