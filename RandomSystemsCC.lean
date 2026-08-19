/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedFinite
import RandomSystemsCC.TypedFramingAdvantage
import RandomSystemsCC.TypedUnitAdvantage
import RandomSystems.StrictContextTotal
import RandomSystemsCC.CBC
import RandomSystemsCC.TypedConstruct
import RandomSystemsCC.TypedConstructChecks
import RandomSystemsCC.ControlledNaturalLanguage
import RandomSystemsCC.CnlCrossLayerChecks
import RandomSystemsCC.LiftingExample
import RandomSystemsCC.ChoiceSettingsExample
import RandomSystemsCC.Symmetric.All
import RandomSystemsCC.TypedPropertyTransfer
import RandomSystemsCC.TypedFeasibility
import RandomSystemsCC.ResourceParallel
import RandomSystemsCC.ParallelChecks
import RandomSystemsCC.NotationChecks
import RandomSystemsCC.EventHistory
import RandomSystemsCC.EventValuation
import RandomSystemsCC.EventAware
import RandomSystemsCC.EventComposition
import RandomSystemsCC.EventChannelExample
import RandomSystemsCC.RelaxationFibre
import RandomSystemsCC.IntervalRelaxation
import RandomSystemsCC.IntervalRelaxationProb
import RandomSystemsCC.TypedParallel
import RandomSystemsCC.TypedParallelChecks
import RandomSystemsCC.MauRen16Impossibility

/-!
# Selected random-systems instantiation of Abstract Cryptography

This root exports the canonical deterministic, typed, finite-interface
RS-to-AC instance:

* `TypedFinite.Phi I U` is the heterogeneous sigma of normalized dependent
  PDS behavior fibres;
* `TypedFinite.Gamma I U i` is the syntactic converter monoid — words over
  every stateful typed `ProtocolFn` satisfying `IsDDC` at interface `i`,
  modulo the serial monoid laws only — interpreted homomorphically into
  non-expanding endomorphisms;
* `TypedFinite.Protocol I U = forall i, Gamma I U i` acts on `Phi I U`;
* the contextual pseudo-emetric is non-expanding under that action.

`Part.none` is blocking divergence.  A rejection that permits continuation
is an ordinary value of the relevant dependent output type.  This
full-converter path does not use observable-completion, `Emulable`, or
`FrameCompatible`.  `RandomSystemsCC.ResourceLift` separately exposes the
source-facing fixed-signature carrier: its fibre is the separated strict
behavioral quotient, every `IsDDC` converter acts non-expandingly on it with
no `Emulable` certificate, and CR18 `Δ` bounds enter through the sound
`maxEDist ≤ ENNReal.ofReal Δ` inequality (never an equality).

`RandomSystemsCC.TypedFiniteChecks` is a separate permanent generic regression
target, not an application or a public-root dependency.  It checks the exact
AC contract, dependent signature change, arbitrary converter state,
rejection/divergence, the historical probe/reset counterexample, serial
multiplication, interface commutation, and construction notation.

`RandomSystemsCC.TypedFramingAdvantage` is the generic source-metric receipt:
for every dependent boundary, the selected contextual distance is bounded by
CR18 maximal distinguishing advantage on the flattened global laws. Equality
is exposed only under support totality, preserving the blocking-divergence
versus observable-completion distinction.

`RandomSystemsCC.CBC` uses that source-facing carrier, so its AC `edist` goal
is discharged by the general `cr18_construct` boundary theorem and becomes
the real-valued CR18 expression `Δ(θr·CBC·R, θr·Vₙ)`.  Its PDSs are cast to
resources only in the construction statement, while typed DDC composition
and action are written directly with `*`.  Because the carrier's protocol
monoid is non-expanding, AC's ε-composition applies: the URP/URF switching
lemma and CR18 Theorem 6.1 chain by `Constructs.eball_trans` into the
two-hop composite `cbc_urp_randomness_expander`, radii adding, with no
transcript reasoning in the composite proof.

`RandomSystemsCC.TypedConstruct` is the construction-assembly layer for the
carrier the CC endpoints actually live on.  `cr18_construct` serves only the
fixed-signature `ResourceLift` carrier; `rs_construct` is its `Phi I U`
analogue, discharging typed composition, the converter action, boundary
alignment and the `ℝ`/`ℝ≥0∞` boundary and leaving the paper's leaf — the CR18
advantage `Δ` when the radius is displayed as `ENNReal.ofReal`, the native
contextual distance otherwise.  Alongside it are the three assembly facts the
`Symmetric/**` endpoints were re-deriving by hand — MauRen11 Definition 3's
availability clause from its security clause (`rs_availability`), the
honest/adversary commutation premise from simulator support (`rs_commute`),
LiuMau20's simulator admission (`rs_simulator`), and Theorem 1(i) serial
composition with the commutation premise discharged (`rs_compose`) — and the
carrier-specific wrappers over the AC assemblers that have a leaf here
(`rs_triangle`, `rs_nonexpand`).  `RandomSystemsCC.TypedConstructChecks` is its permanent
usability regression, in the style of `NotationChecks`: every command fired on
the goal shape a model produces, every leaf closed from a *named* hypothesis
so that a tactic which starts hiding an estimate breaks the build, one
compiled instance of each `rs.construction.*` controlled sentence, and the
token-trap receipt for the two parser atoms the language layer adds.

`RandomSystemsCC.ChoiceSettingsExample` is the reachability regression for
MauRen11 Theorem 2 (`AbstractCrypto.ChoiceSettings`): the typed carrier
discharges the local-simulation premise for a genuine minimal construction —
a resource behind the output-negating `flip` filter is abstracted by the
negated resource, the dishonest simulator being `flip` itself — so the
choice-domain/CFR conclusion `R_φ ⊑^π S_ψ` now lands on concrete
random-systems resources.  The behavioral core is that double output
negation is trace-invisible (`flip • flip • R = R`, for every resource);
non-vacuity is witnessed on the two constant oracles, which the filter
exchanges and a one-query strict test provably separates.

`RandomSystemsCC.Symmetric.All` exports the CC-first symmetric construction
suite: OTP, affine one-time MAC, bounded URF-MAC, UHF/URF expansion and MAC,
and MAC-then-OTP composition.  Its current statement-first proof status is
tracked in `STATUS.md` §10.

`RandomSystemsCC.TypedPropertyTransfer` is the worked AC property-transfer
example over the strict-observation distinguisher class of
`RandomSystemsCC.TypedDistinguisher` (imported transitively together with
its non-vacuity receipts): an unforgeability `propSpec`/`gameSpec` whose
defining tests are CR18 game-winning probabilities — an admitted test value
equals `winProb` against a `gameOf` MBO game — so `one_tsub_le_test_of_close`
and `gameSpec_of_edistD_le` carry the ideal resource's guarantee, in the
paper's `1 - ε` form and as a CR18 winning-probability bound, to every
resource within class distance `ε`.

`RandomSystemsCC.ResourceParallel` installs the parallel-composition axis
on the strict resource carrier: `Par (Resource U)` and `IsNonexpandingPar`
(Maurer11 eq. (3), proved for the **strict** contextual metric — a new
fact, not a transfer of `maxAdvantage_par_le`), plus the syntactic
protocol monoid `ParProtocol U` with `SMulParClass` (the `‖`-routing law,
well-defined by strict cancellation — the uniqueness of a strict
behavior's parallel decomposition).  `RandomSystemsCC.ParallelChecks` is
its permanent regression: `Constructs.eball_par_resource` applied to a
genuine extraction construction on a concrete `⊕`-closed universe, with
one-query-test separation and cancellation as the non-vacuity receipts.

`RandomSystemsCC.TypedParallel` installs the same axis on the carrier the
CC endpoints actually live on: `Par (Phi I U)` and
`IsNonexpandingPar (Phi I U)`, from the typed resource parallel of
`RandomSystems.TypedParallel` (flatten → flat parallel → relabel →
unflatten, every fact transported through metric full abstraction and the
relabelling isometry — nothing re-proved).  The protocol side is
deliberately untouched: the parallel *action* is not non-expanding, and
the canonical statement `AUT ∥ KEY ⟶ SEC` needs only a resource-side `∥`
under a *serial* protocol.  `RandomSystemsCC.TypedParallelChecks` is its
permanent regression: a genuine `π • (A ∥ B)` on a concrete two-party
`⊕`-closed universe with a boundary receipt, a `CC.SecurelyConstructs`
judgment over parallel composites, the `AUT ∥ KEY ⟶ SEC` statement shape
elaborated, and one-query-test separation + `Resource.par_ne_left` as the
non-vacuity receipts.

`RandomSystemsCC.EventAware`, `RandomSystemsCC.EventComposition` and
`RandomSystemsCC.EventChannelExample` complete Jost's *Constructive
Cryptography with Events* (thesis Ch. 3) on top of the object layer settled in
`RandomSystemsCC.EventHistory`.  `Events.withEvents` is Jost's augmented
alphabet `𝒳 × 2^ℰ` as an ordinary `SignatureUniverse`, so an event-aware
resource is an ordinary `DependentDDS` and `Events.IsEventAware` is Definition
3.2.3 as a predicate on it — the route Jost himself points at (p. 35,
"event-aware systems are a special case of the regular ones").  Because the
carrier is unchanged, composition order invariance is the estate's existing
`Primitive.act_comm` instantiated (`Events.act_comm_withEvents`), and the only
new content is the definedness side conditions, which are symmetric
(`Events.eventCompatible_attach_comm`).  On the event axis — Jost's own working
representation, p. 35 — `Events.ParDisciplined.proj` is why parallel
composition demands disjoint event-sets (with `Events.proj_fails_without_disjoint`
as the sharpness receipt), `Events.disciplined_run` is the point of the
compatible-distinguisher restriction of Definition 3.3.1, and
`Events.proj_renameTagged` plus `Events.queryMapBase_comm_queryMapEvents` are
the two equations of Proposition 3.3.3, with
`Events.renameSpec_not_inflationary` recording as an explicit non-theorem that
an event mapping is not a relaxation.  The example file exhibits the
cross-module dependency plain CC cannot express, and its
`chanResource_isEventAware` is the carrier-level witness that `IsEventAware` is
inhabited.

`RandomSystemsCC.RelaxationFibre` and `RandomSystemsCC.IntervalRelaxation` settle
the question Jost leaves open in thesis Ch. 5 §5.3 (p. 101, "it is an interesting
open question whether the two respective relaxations actually commute").  The
first module is the abstract half and its result is negative:
`IntervalWise.Blocked` exhibits two idempotent commuting self-maps of `Fin 3` —
the two properties Jost's from/until projections have — whose fibre relations fail
to permute, so the retraction calculus alone cannot decide the question.  The
second module answers it affirmatively on the event carrier, in the sharp
collapse form `(R^{[P₁})^{P₂]} = R^{[P₁,P₂]} = (R^{P₂]})^{[P₁}`
(`IntervalWise.fromThenUntil_eq_intervalRelax`,
`IntervalWise.untilThenFrom_eq_intervalRelax`), so Theorem 5.3.12's union over
`n ∈ ℕ` collapses at `n = 2` and the outer relaxation of its three-fold
composites is redundant.  The proof is a positionwise gluing over the two
prefix-closed windows the projections forward, the witness is checked against
Definition 3.2.3 (`IntervalWise.glue_isEventAware`), the statement is carried to
Jost's specification level explicitly, and
`IntervalWise.Necessity.historyBlind_collapse_fails` records that event-awareness
is indispensable: with `P₁ = P₂` the hypothesis is vacuous and no history-blind
witness exists, so the affirmative answer holds *because of* the Ch. 3 extension.

`RandomSystemsCC.IntervalRelaxationProb` lifts that answer from the deterministic
carrier to the probabilistic one, where Jost's resources actually live: the same
collapse holds for laws (`IntervalWise.probFromThenUntil_eq_probIntervalRelax`,
`IntervalWise.probUntilThenFrom_eq_probIntervalRelax`) and for normalized laws
(`IntervalWise.normFromThenUntil_eq_normIntervalRelax`), with the union collapse
and the specification level following as before.  One inclusion is functoriality
of the pushforward over `IntervalWise.untilP_fromP_untilP`; the other is a
measure-gluing step, `RandomSystems.Dist.exists_coupling_of_fTransform_eq`, since
two laws with equal interval projection agree only in aggregate and the
deterministic witness needs a *pair* of samples on a common fibre.  On the
contextual quotient the collapse is available conditionally
(`IntervalWise.randomSystem_fromThenUntil_eq_intervalRelax`): the abstract
descent `IntervalWise.fibreComp_quotient_eq_fibre` needs only that the three
projections are defined on classes, and
`IntervalWise.exists_randomSystem_collapse_of_faithful` records that discharging
that is exactly the open claim that the strict-context action on `DependentPDS`
is faithful.

`RandomSystemsCC.TypedFeasibility` connects the RS complexity layer to the
strict-observation distinguisher class (AC integration receipt 8): a strict
test's machine-free cost fills both coordinates of `RandomSystems.Cost` —
round budget as `intrinsic`, per-interface query counts as `calls` — and
`costBoundedTests` is the resulting feasible test subcarrier, monotone in
the `Cost` order and non-vacuous in both directions (an admitted separating
witness at an explicit budget, and a full-class test provably outside every
`calls 1 = 0` class, by the starved-interface transcript coupling).  The
worked computational statement places a noisy resource family inside a
per-test `reductionRelaxation` budget of the ideal with `PolyBoundedCost`
and `Negligible` at the asymptotic boundary, and the budget is proved
tight.  At a fixed cost the class closes under the neutral converter only:
the graded MauRen11 Definition 17 closure needs a counting version of
context absorption that the estate does not yet have — the module header
states precisely what is missing.
-/
