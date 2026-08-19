# Efficient operational layer: approach registry

Status vocabulary: `open`, `candidate`, `component`, `rejected`, `blocked`,
and `selected`. A route is not selected merely because its notation is
convenient.

## R0 — Existing unbounded single-token realization

- **Status:** component.
- **Carrier:** finite typed networks of probabilistic interactive multitape
  Turing machines, with one activation token and persistent private random and
  work tapes.
- **Operations:** renaming, disjoint parallel composition, typed connection,
  strict feedback, and converter-shaped attachment.
- **Denotation:** fixed tapes give a partial macro transition and DDS;
  pushforward gives a law over DDSs; transcript quotient gives a random
  system.
- **Strength:** clean pathwise semantics and explicit partiality.
- **Gap for efficiency:** macro-collapse erases every step, cell, message-copy,
  activation, routing, random-bit, and resource-call cost.
- **Naive extension rejected:** attaching the predicate “PPT” to the resulting
  extensional DDS. Extensionally equal behaviors can have radically different
  implementations and costs, and arbitrary extensional functions have no
  finite program descriptions.

## A — Security-parameter-indexed machine/network families

- **Status:** component.
- **Candidate carrier:** a family `(N_kappa)_{kappa in Nat}` of finitely
  described typed networks, with a cost certificate at every parameter and a
  uniform generator as a separate predicate.
- **Potential advantage:** denotation at each parameter is direct; uniform and
  nonuniform variants can coexist.
- **Naive failure:** if arbitrary families are allowed, one bit of an
  undecidable language can be hard-coded at each parameter, disguising
  nonuniformity as “efficiency.”
- **Resolution:** the primary uniform presentation is one fixed finite network
  template whose machines receive `1^kappa`. A generated-network presentation
  is admitted only with a fixed polynomial-time generator and an aggregate
  size/cost envelope. Polynomial advice is a separately named nonuniform
  variant. An arbitrary indexed family is never called uniform or efficient.

## B — One uniform universal machine

- **Status:** selected secondary presentation.
- **Candidate carrier:** one machine receives unary security parameter,
  network/program encoding, and auxiliary input; it interprets a generated
  network.
- **Potential advantage:** uniformity is internal rather than a metapredicate.
- **Naive failure:** without a prefix-free encoding and a polynomial
  universal-simulation theorem, interpreter and routing overhead are hidden;
  binary security parameters also permit exponential work in the represented
  value while appearing polynomial in input length.
- **Resolution:** every value, port, and program has an effective
  self-delimiting encoding; the security parameter is supplied in unary.  The
  admitted family has one fixed generator, one fixed external boundary, fixed
  program/codec/grade libraries, a polynomial code-length bound, and a
  polynomial aggregate native profile.  A sequential decoder, charged private
  grade evaluator with meter-only unary `1^kappa,1^b` tracks, and interpreter
  use a normalized magnitude envelope that includes the administrative-input
  lengths and unused virtual quotas.  With fixed routine-compilation constants
  they preserve erased transcripts and the virtual native ledger under an
  explicit master-tape coupling. The simulated-event bound includes
  activations and oracle accesses, not only machine work. For each fixed
  stateful oracle dependency, a charged private proxy mirrors its meter-level
  exact commit receipt and next public coordinate into the virtual ledger;
  decoded code receives only the ordinary reply. Their physical profile is
  polynomially transformed and is not claimed equal to the native profile.
  Generated networks are therefore a proved presentation convenience, not a
  new complexity class. Only implementation nodes are generated; fixed named
  specification oracles remain boundary dependencies, and the proxy does not
  create another occurrence.

## C — Graded or costed system algebra

- **Status:** selected.
- **Candidate carrier:** operational terms paired with a vector-valued cost
  transformer; constructors compose grades.
- **Potential advantage:** exact constructor-by-constructor accounting and a
  clean forgetful map.
- **Naive failure:** a single scalar polynomial grade cannot express adaptive
  resource calls or input-dependent message growth, and syntax-sensitive
  grades are not invariant under graph isomorphism.
- **Selected form:** a small-step run has an exact, vector-valued ledger:
  per-component transitions, activations, random bits, and peak live cells;
  per-edge traffic; and per-oracle call and traffic counts. Aggregation is a
  separate monotone map. Component occurrences carry polynomial quota
  transformers in a common ambient workload. Quotas are labels on the final
  network graph, so alpha-renaming and changes of parenthesization do not
  change them.
- **Why exact costs precede grades:** grades are upper bounds and may be loose.
  The exact ledger is needed for concrete reductions, lower bounds, alternative
  hardware weightings, and auditing a claimed certificate.
- **Algebraic carrier:** at every fixed `(kappa,b)`, finite normalized open
  graphs are quotiented by all cost-aware closing contexts.  Bare aliases
  normalize away; explicit physical links remain nodes/edges.  Renaming,
  tensor, connection (including cyclic finite matchings), and converter action
  are well-defined on the contextual quotient.  A second quotient erases
  reports and identifies `Block` and `Exhaust` with semantic nonresponse; the
  quotient map is an operation-preserving homomorphism.  On the route-safe
  subalgebra, a derived canonical-router envelope makes structural routing
  behaviorally transparent while retaining its exact cost; the selected
  standard-Borel partial-random-system embedding is then a proved
  strict-feedback homomorphism.  Only comparison with a differently chosen
  external carrier remains separate.
- **Observer split:** the pointwise quotient may use every measurable
  terminal predicate because it compares complete outcome laws. A
  computational test does not receive that predicate for free: it contains a
  fixed uniform graded scorer whose input processing and report computation
  are charged, with a fixed default on scorer block/exhaust.

## D — Oracle-relative efficient machines

- **Status:** selected.
- **Candidate carrier:** interactive oracle machines with separate local-step,
  call-count, and communication coordinates.
- **Potential advantage:** ideal resources can remain specifications while
  efficient converters access them through charged calls.
- **Naive failure:** treating an oracle call as one ordinary step permits a
  one-bit query to trigger unbounded hidden work and makes reductions appear
  efficient by laundering computation through the oracle.
- **Selected form:** oracle calls have distinct coordinates for call count,
  query bits, response bits, and a declared tariff. The implementation pays
  serialization and the tariff but not the oracle's hidden implementation
  cost. A response cannot create computational budget. An oracle is
  *efficiently accessible* only relative to a polynomial tariff contract; this
  does not assert that the oracle is efficiently implementable.
- **Admission discipline:** for bounded response envelopes, reserve
  call/traffic/tariff capacity from the query and public contract before
  sampling.  A rejected call does not sample or change oracle state.  A
  stateful fixed-chunk contract plus a metered reassembly converter is the
  explicit alternative for genuinely unbounded responses; after hiding the
  chunk interface its loss is the converter-exhaustion tail. Sample-then-reject
  is not treated as an exact admitted call because it can condition the
  successful response law.

## E — Explicit processor, memory, randomness, communication, and clock resources

- **Status:** selected refinement.
- **Candidate carrier:** narrow routers connected to explicit cost resources.
- **Potential advantage:** expresses bounded memory, reset, erasure, leakage,
  and timing claims without pretending erased costs are unavailable.
- **Naive failure:** making every machine step an AC interaction obscures
  ordinary efficient cryptography and creates a cumbersome infinite protocol
  trace unless a macro refinement theorem is supplied.
- **Selected API:** an initialized, program-indexed transition-token
  `PROC[P;T,A,L]`, a
  native-configuration `STORE[S]`, a named persistent `COIN[R]`, and an
  optional one-buffer lossless `SLINK[C,W,S]`.  A stateless generated driver
  only routes fixed tags; connection to `PROC[P;...]`, not data hidden in the
  driver, selects the immutable program.  Program storage, logarithmic
  counters, transaction scratch, and private copies remain in the full
  explicit ledger.  A generic loaded variant additionally requires a charged
  program-image source, atomic initialization policy, and source/destination
  peak; it is not implicit in this API.
- **Resolution:** a two-phase protocol reserves processor, actual-branch coin,
  and store capacity before committing any native coordinate. Linear
  capabilities and a padded eight-phase schedule prevent replay and
  branch-dependent administrative leakage; a well-founded lexicographic rank
  in phase suffix and remaining admitted scan/copy microsteps prevents new
  blocking or livelock. Administrative erasure is pathwise equal to the
  metered machine, and `pi_native` preserves its exact ledger. This discharges
  the macro theorem for the selected sequential APIs.
- **Generated presentation:** compile a generated network to the one fixed
  universal machine first, then reify that universal occurrence.  The
  decoder/interpreter physical profile feeds the explicit-resource profile.
  Nodewise reification in the opposite order would generate ideal resources
  and is rejected without a separately fixed indexed product resource.
- **Boundary:** shared processors, RAM, visible clocks, reset, leakage, secure
  erasure, asynchronous links, and a physical implementation of the ideal
  coin source are different lower resources.  The MauRen16 source supports
  the modeling direction, not the selected transaction protocol.

## F — Two-sorted specifications and implementations

- **Status:** selected.
- **Candidate carrier:** an implementation sort with finite programs and cost
  certificates, and a specification/oracle sort that need only expose an
  admissible efficient interface.
- **Potential advantage:** an ideal random oracle need not be efficiently
  executable to be usable in an efficient experiment.
- **Naive failure:** calling every efficiently accessible ideal resource
  “efficiently implementable” conflates query access with internal execution.
- **Selected form:** implementation objects have finite codes, exact ledgers,
  and quota certificates. Specification objects are abstract random-system
  families equipped only with effective wire encodings and access tariffs.
  The latter may contain a random oracle, an ideal channel, or a noncomputable
  transition law. Converters are implementation objects and may access
  specifications as charged oracles.

## G — Reactive/interactive complexity

- **Status:** evidence incorporated; framework import rejected.
- **Candidate evidence:** UC ITMs, IITMs, RSIM, and reactive polynomial time,
  stripped of their framework-specific adversary/session conventions.
- **Potential advantage:** the literature contains explicit attacks on strict
  total-polynomial and per-activation definitions.
- **Naive failure:** importing an entire framework silently imports its
  addressing, scheduling, corruption, and security quantifiers, none of which
  is forced by the AC lower-realization problem.
- **Evidence retained:** strict lifetime clocks can be killed by a larger
  polynomial environment; per-activation polynomial time permits message
  amplification; polynomial input-shaping is not closed under feedback; and
  “almost bounded” components can activate each other's rare bad cases. These
  are operational facts, not UC security definitions.

## H — Per-activation polynomial time

- **Status:** rejected as the primary notion.
- **Candidate:** each activation of `M` takes at most
  `p_M(kappa + |current-input|)` steps.
- **Failure:** two machines can repeatedly double and return a message. Each
  activation is polynomial in its own input, but after a polynomial number of
  transfers the work and message size are exponential. If feedback is
  unbounded, the run livelocks. Counting only the current input also lets one
  component manufacture a large input that grants another component more
  computation.
- **Residual use:** a local per-activation bound is a useful proof lemma once
  a global traffic/workload invariant has already been established.

## I — Strict lifetime polynomial in the security parameter

- **Status:** rejected as the primary reactive notion.
- **Candidate:** every participant halts after `p_M(kappa)` total steps.
- **Failure:** an environment with a higher-degree polynomial can exhaust an
  otherwise natural service using irrelevant queries. A real implementation
  and its ideal specification may then expose different denial-of-service
  behavior. This is the “killing” problem documented in the reactive-runtime
  literature.
- **Residual use:** it is sound for one-shot games and for a closed experiment
  whose complete workload is fixed in advance.

## J — Polynomially shaped input/output flow

- **Status:** component, with a connection side condition.
- **Candidate:** for every outside system, total output and activations of a
  component collection are polynomial in `kappa` plus total input received
  from outside the collection.
- **Strength:** it captures open-ended reactive services without fixing a
  lifetime query bound and exposes message amplification.
- **Failure:** it is not closed under arbitrary connection. A forwarder and a
  repeater are each polynomially shaped in isolation but can form an infinite
  internal loop. Hofheinz--Mueller-Quade--Unruh give this exact phenomenon.
- **Use here:** a flow certificate can prove that a particular unmetered
  composition is adequately responsive. It is not the generic closure
  mechanism.

## K — Expected or almost polynomial runtime

- **Status:** rejected as the algebraic core.
- **Candidate:** bound expected work, or permit superpolynomial work on a
  negligible set of runs.
- **Failure:** expectation permits inverse-polynomial bad events with very
  large cost. More subtly, two almost-bounded components can generate each
  other's rare hard inputs and cease to be almost bounded; the IITM
  time-lock-puzzle counterexample establishes this under a standard
  assumption.
- **Residual use:** tail bounds may be layered over the strict metered core,
  but composition must carry an explicit hypothesis and union/reduction
  accounting.

## L — Externally visible timeout or error

- **Status:** rejected as an implicit convention.
- **Candidate:** return an ordinary `Err` value when a clock expires.
- **Failure:** this changes the random system. After `Err`, a context may
  continue; after strict nonresponse it cannot. It also exposes the selected
  machine clock at an abstraction layer intended to forget time.
- **Selected form:** budget exhaustion is a lower-layer terminal status
  observable only to the meter. The ordinary random-system erasure maps it to
  nonresponse. A protocol that wants a visible timeout must explicitly include
  it in its interface.

## M — Ambient workload with non-observable component meters

- **Status:** selected closure mechanism.
- **Carrier:** a fixed finite typed machine graph. Each component occurrence
  has a monotone multivariate polynomial quota transformer
  `F_v(kappa, b)` for transitions, space, randomness, traffic, activations,
  and named oracle calls. The environment chooses an ambient workload
  `b = p(kappa + |aux|)` using a fixed polynomial `p`.
- **Execution rule:** programs cannot read their remaining quota. Before a
  primitive action would cross a quota, an external meter terminates the run
  with `Exhaust`. Every microstep costs at least one transition unit. Message
  production, routing, random-bit reads, and oracle traffic are charged.
- **Closure argument:** for a fixed finite graph, a sum, maximum, and
  composition of finitely many polynomial quota transformers is polynomial.
  Connection and feedback may spend the quotas but cannot create more. Thus
  every polynomial-workload closed experiment has polynomial total cost,
  including executions that end by exhaustion.
- **Reactive advantage:** a higher-degree polynomial environment chooses a
  larger ambient workload, so a service is not tied to one universal lifetime
  polynomial. For each fixed environment, the composed experiment still has a
  polynomial bound. This has the useful quantifier order
  `for every efficient context, there exists a bound for the closed
  experiment`.
- **Availability caveat:** metering proves resource boundedness, not that a
  requested response occurs. Construction of a responsive specification needs
  a separate no-exhaustion/productivity certificate on the declared workload
  class.

## N — Polynomial cost transformers for reductions

- **Status:** selected.
- **Carrier:** an efficient converter records a transformer from the budget
  profile of an outer distinguisher to the profile needed after absorbing the
  converter. It includes universal-simulation, routing, message, randomness,
  and oracle-call overhead.
- **Composition:** sequential transformers compose; independent parallel
  transformers combine coordinatewise; error bounds add. Polynomial
  transformers send polynomial budget policies to polynomial budget policies.
- **Consequence:** nonexpansion is budget-reindexed rather than falsely
  same-budget:
  `Delta_b(alpha R, alpha S) <= Delta_{T_alpha(b)}(R,S)`.
  The usual asymptotic nonexpansion follows because `T_alpha(p(kappa))`
  remains polynomial. Concrete security retains the actual transformer.

## O — Dependency-relative feasible algebra

- **Status:** selected after exact MR11 compatibility audit.
- **Carrier:** one fixed finite signature `Gamma` of specification packages.
  Each package fixes the typed oracle interface, initialization, conditional
  kernel, codecs, public coordinate, reservation/tariff evaluators, evaluator
  profiles, and independence convention.  Resource, converter, and test
  networks are all relative to the same `Gamma`.
- **Occurrence discipline:** tensor alpha-renames names apart before forming
  the union.  Distinct occurrences own distinct initial-state and seed
  coordinates; sharing is represented by one occurrence with multiple
  callers.  Absorption retains these exact occurrences and never clones them.
- **Closure argument:** for any feasible converter `alpha` and any feasible
  resource graph `S`, the absorbed tests `D[alpha]` and `D[. || S]` are fixed
  feasible networks.  Their normalized closed graphs are pathwise identical
  to `D(alpha R)` and `D(R || S)`, and fixed polynomial transformers charge
  every retained implementation and oracle coordinate.
- **Boundary:** enlarging `Gamma` changes the computational model.  A
  parameter-dependent number of independent oracle instances must be one
  fixed indexed product-state package with a charged multiplexer and
  aggregate tariff; the generated implementation compiler cannot manufacture
  ideal independence.

## Selected architecture

The paper will use the following stack.

1. The existing unbounded finite-network semantics remains the behavioral
   base.
2. Every run is enriched with an exact local and global cost ledger.
3. Non-observable meters and an ambient workload produce a total,
   budget-indexed operational family. Exhaustion erases to strict
   nonresponse.
4. Uniformity is primarily one fixed template receiving unary `kappa`.
   Generated networks are admitted only through the proved fixed-generator
   compiler and aggregate profile certificate; polynomial advice is a
   separately named nonuniform variant.
5. Abstract specifications form an oracle sort with charged, pre-reserved
   access (or an explicit streaming contract) but no implementability claim.
   The geometric-string instance supplies one complete unbounded-response
   tail and local-profile calculation.
6. The finite cost-aware contextual quotient supplies the complete bounded
   operational algebra. Its erasure homomorphism lands in a behavioral
   operational quotient. On the route-safe subalgebra, canonical routing has
   a derived dominating envelope and the further map into the selected
   standard-Borel partial-random-system carrier is an injective
   strict-feedback homomorphism. Limited links are explicit resources.
7. Workload-relative no-exhaustion, productivity, and behavioral realization
   are separate adequacy judgments. Stop outcomes attribute the first failed
   action to a public owner class, and availability quantifies over completion
   contexts with their own safety and conditional-progress certificates;
   otherwise a self-exhausting or self-blocking context would refute every
   resource. Elementary DAG, solved response-adaptive post-fixed-point, or
   affine-credit certificates establish the tested-side judgment for selected
   compositions; meters alone do not.
8. Fixed graded interaction and terminal-scorer codes, together with
   polynomial quota and reduction transformers, define the efficient
   asymptotic class and concrete loss accounting. Arbitrary measurable
   terminal predicates remain confined to the pointwise quotient.
9. If a cost itself matters to the security statement, its meter is reified as
   an explicit AC resource.  The private sequential
   `PROC/STORE/COIN/SLINK` instance has a proved transactional macro
   refinement; different resource APIs require their own theorem.

This choice does not claim that arbitrary unmetered polynomially shaped
components are closed under feedback. It instead supplies a closed metered
implementation algebra and states no-exhaustion/productivity as the additional
semantic property needed for useful services.
