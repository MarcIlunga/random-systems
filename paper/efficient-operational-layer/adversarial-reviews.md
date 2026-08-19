# Efficient operational layer: adversarial review ledger

Each review was performed against the definitions in
`research-dossier.md`, not merely against the intended conclusion. Severity
uses `critical`, `major`, `moderate`, and `minor`. “Revision” records a change
that must appear in the unified paper; residual risks remain listed even when
the architecture survives.

## Review 1 - complexity theory

### Attacks

1. **Ambient workload may disguise superpolynomial computation.** A component
   quota is polynomial in `b`, while a context chooses `b=p(kappa)`. If `p`
   were allowed to vary with `kappa` rather than being one fixed polynomial
   in the context description, the definition would admit arbitrary runtime.
   **Severity:** critical.
2. **Arbitrary indexed machines disguise advice.** Requiring only that every
   `N_kappa` is small admits the bit of any undecidable language.
   **Severity:** critical.
3. **Generated node bounds can have growing exponents.** A polynomial number
   of generated nodes, each carrying the certificate `b^kappa`, is not
   polynomially bounded by any fixed polynomial. **Severity:** major.
4. **Long-message replay might be unit cost.** If an output register can alias
   a previous input or persistent buffer, a repeater can emit a long string in
   one transition. **Severity:** critical.
5. **Expected runtime does not control tails.** A linear expectation can hide
   inverse-polynomial bad events and bad concrete availability. **Severity:**
   major.
6. **Interpreter overhead is assumed rather than proved.** A universal
   simulation theorem needs a fixed code and routing model. **Severity:**
   moderate.

### Resolution and revisions

- A workload policy is finite syntax in a fixed context code. Its exponents
  and coefficients do not depend on `kappa`.
- The primary uniform object is one fixed graph template receiving
  `1^kappa`. Generated graphs need one fixed generator and a polynomial
  **aggregate** size/quota envelope, not only per-node labels. Polynomial
  advice is a separately named nonuniform mode.
- Output buffers are blank at activation, aliases are forbidden, and the
  canonical router scans or copies a self-delimiting code with charged
  transitions. Re-emitting stored data is at least linear in its encoded
  length.
- Strict grades, not expectation, define the implementation carrier. Tail
  bounds can be a later property.
- The later compiler round fixed a prefix code, validator, aggregate
  certificate, master-tape coupling, and sequential universal interpreter.
  Its polynomial overhead theorem now uses explicit family-independent
  routine-compilation constants; equality of physical cost reports is not
  claimed.

### Residual risk

Polynomial time remains machine-model dependent up to polynomial overhead.
That is intended, but any concrete bound must name the chosen multitape
machine, router, and encoding.

## Review 2 - programming languages and operational semantics

### Attacks

1. **Budget monotonicity fails if code reads its clock.** A larger budget could
   make a program choose a different branch. **Severity:** critical.
2. **Cost-aware observation does not factor through ordinary random
   systems.** The dossier initially let the supervisor distinguish `Block`
   from `Exhaust`, while the random-system erasure maps both to nonresponse.
   **Severity:** critical.
3. **Response-dependent oracle tariff has an ordering ambiguity.** The meter
   cannot know the response length until the oracle samples it. Does a failed
   tariff check roll back oracle state? **Severity:** major.
4. **Connection preservation remains assumed.** A cost ledger does not prove
   that operational feedback matches the target partial fixed point.
   **Severity:** major.
5. **Peak space is not a simple additive grade.** Treating the entire ledger
   as one commutative monoid would state false sequential equations.
   **Severity:** major.
6. **Persistent histories require lifetime meters.** Resetting quotas at each
   query would reintroduce per-activation amplification. **Severity:**
   critical.

### Resolution and revisions

- Meters are external and non-observable. Programs see neither the remaining
  quota nor the exhaustion event.
- The paper now distinguishes two carriers:
  an operational costed carrier whose lower observer may see
  `Success/Block/Exhaust`, and its forgetful ordinary random-system carrier
  where block and exhaustion are both strict nonresponse. Standard behavioral
  security and performance-sensitive security must name which observation
  they use.
- The later oracle round rejected response-dependent sample-then-check as the
  baseline exact-call rule. A public query-only envelope is reserved before a
  fresh named seed is consumed. Rejection samples nothing and changes no
  state. Admission then samples once, commits once, and deducts an exact charge
  dominated by the reservation. Unbounded responses use a stateful chunk
  specification and metered reassembly converter.
- Space remains an exact peak coordinate; only its bound is combined by
  maxima and global live-cell sums.
- Meter state and exact ledgers persist for the complete system lifetime.
- Connection theorems remain explicitly conditional on the strict-feedback
  correspondence and quotient congruence.

### Residual risk

The oracle-relative infinite-lifetime measure still requires a fully selected
standard-Borel or projective carrier. Finite-budget cylinder semantics is not
by itself the complete measure theorem.

## Review 3 - Constructive Cryptography and system algebra

### Attacks

1. **A relay machine is not a cost-neutral identity.** If it consumes quota,
   inserting the purported identity can cause exhaustion and change behavior.
   **Severity:** critical.
2. **Ambient workload appears context dependent.** An AC resource should be
   an object before the distinguisher is chosen. **Severity:** major.
3. **Specification families are not necessarily PPT implementations.** This
   seems to conflict with high-level asymptotic definitions that restrict
   resource families to efficient ones. **Severity:** major.
4. **Cost labels are syntax sensitive.** Parenthesizing a composite
   differently might create different routers or quotas. **Severity:** major.
5. **Metered closure could be mistaken for productive closure.** That would
   invalidate any claim that converters remain responsive after feedback.
   **Severity:** critical.

### Resolution and revisions

- The identity is a bare typed wire and graph normalization fuses consecutive
  bare wires. Physical transport is charged once to the resulting edge or
  communication resource; inserting identity syntax adds no component and no
  extra quota.
- For every fixed `(kappa,b)`, the costed or erased denotation is an ordinary
  object. The context later selects the index `b=p(kappa+|a|)`, exactly as an
  asymptotic test selects `kappa`; the object is not retroactively changed.
- “Efficiently accessible specification” and “efficiently implementable
  resource” are separate predicates. The general AC carrier can contain both.
  A theorem that specifically assumes Jost's `Theta_poly` must use only the
  latter or be restated with charged oracle access.
- Quotas label occurrences in a normalized final graph. Alpha-renaming
  transports them, and construction order does not create administrative
  nodes.
- The paper states two classes throughout: bounded metered implementations,
  closed under wiring; and adequately responsive implementations, requiring a
  flow/rank/credit theorem.

### Residual risk

The later finite-algebra round proves the cost-aware contextual system algebra
and its erasure homomorphism. The remaining risk is narrower: identifying the
behavioral operational quotient with the independently selected lifetime
random-system carrier still needs strict-feedback congruence.

## Review 4 - cryptographic reductions and concrete security

### Attacks

1. **“Same budget” absorption is generally false.** A distinguisher that
   internally simulates a converter needs more time, space, traffic, and
   oracle calls. **Severity:** critical.
2. **Ambient workload and exact resource profile were conflated.** The same
   `b` can remain in the graph while the absorbed distinguisher's aggregate
   profile grows. **Severity:** major.
3. **A parallel ideal resource cannot be emulated for free.** If it is not
   machine implementable, absorbing it requires oracle access and a tariff.
   **Severity:** critical.
4. **Auxiliary input can carry nonuniform advice.** Taking a supremum over all
   polynomial-length `a_kappa` is stronger than pure uniform security.
   **Severity:** major.
5. **Simulator cost was at risk of disappearing in the asymptotic quotient.**
   **Severity:** major.
6. **Negligible runtime overrun cannot simply be union-bounded through
   adaptive, unbounded feedback.** **Severity:** major.

### Resolution and revisions

- Absorption is an exact graph equality, but the certified aggregate cost
  profile is transformed. The ambient workload index may stay `b`; the
  concrete bound becomes `T_alpha(Profile_D(kappa,b))`.
- Nonexpansion is always written with the transformed profile. Same-budget
  notation is used only if a separate domination proof establishes it.
- An absorbed abstract resource remains a named oracle in the reduction and
  contributes its tariff and call profile.
- Three uniformity modes are named:
  pure uniform code with no arbitrary advice; uniform code with
  polynomial-length auxiliary input (auxiliary-input/nonuniform strength);
  and explicit nonuniform advice/circuit families.
- Simulators are graded converter codes. Concrete statements report their
  transformer; explicit-computation statements reify their processor
  resource.
- Strict metering, not almost-boundedness, gives generic feedback closure.
  Any tail-bound refinement carries a separate composition hypothesis.

### Residual risk

The exact numerical overhead of universal simulation and routing is not
available until the concrete machine compiler is fixed. The current result is
a symbolic cost-transformer theorem.

## Review 5 - MR16/RSS11 resource modeling

### Attacks

1. **Explicit memory can be bypassed by hidden work tapes.** **Severity:**
   critical.
2. **An explicit processor may itself contain unaccounted persistent memory
   and randomness.** **Severity:** critical.
3. **Randomness is double counted or silently shared.** A machine random tape
   plus a `RAND` resource violates the intended model. **Severity:** major.
4. **Reset, erasure, and leakage are not determined by a cell-count bound.**
   **Severity:** major.
5. **An oracle tariff might be mistaken for the cost of implementing the
   ideal resource.** **Severity:** major.

### Resolution and revisions

- In an explicit-memory regime, program converters are stateless except for
  finite control and explicit resource handles. Input/output buffers and
  handles are covered by the API.
- The `CPU` contract must say whether it includes working memory and
  randomness. If `MEM` and `RAND` are separate, the processor is a transition
  engine with no hidden persistent storage or random tape.
- Named randomness is exclusive: either a component has a private random tape
  in the free-computation model, or it obtains random bits through `RAND`.
  Shared randomness is always a common resource.
- Capacity, reset, secure erasure, snapshots, leakage, and access pattern are
  separate resource features. `MEM[S]` is only schematic until its API fixes
  them.
- Oracle tariffs price access and serialization only. No internal
  implementation claim follows.

### Residual risk

There is no canonical processor/memory API. The macro-refinement theorem must
be reproved for each resource model of physical interest.

## Review 6 - finite implementability and uniformity

### Attacks

1. **An abstract kernel may be nonmeasurable.** Then the experiment law is not
   defined. **Severity:** critical.
2. **Fair-bit tapes do not realize all abstract real probabilities.**
   **Severity:** major if surjectivity is claimed.
3. **“Uniform with arbitrary auxiliary input” was mislabeled.** An arbitrary
   sequence of polynomial-length auxiliary strings acts as advice.
   **Severity:** major.
4. **Type membership and parsing might be noncomputable.** **Severity:**
   critical at an implementation boundary.
5. **A generated graph can hide initialization and routing work.**
   **Severity:** major.

### Resolution and revisions

- Specification kernels and tariffs are required to be measurable. Finite
  encoded interface validation used by machines is effective and has a
  declared grade.
- The denotation is explicitly an operational image. Abstract resources with
  noncomputable probabilities remain specifications, not implementation
  outputs.
- The paper separates pure uniform, auxiliary-input, and explicit nonuniform
  modes. The default theorem states which is used.
- Code generation, graph validation, initialization, and universal routing
  are ledger coordinates under an aggregate certificate.
- The later compiler round discharges the mathematical generated-to-fixed
  theorem for its selected fixed grammar and aggregate certificate, leaving
  only literal numerical routine-expansion constants symbolic.

### Residual risk

Exact characterization of the samplable random-system image is not attempted.
Even for computable measures, almost-sure versus worst-case sampling
termination requires care.

## Review 7 - exposition and theorem status

### Attacks

1. **The original title and abstract promise only an unbounded layer.** The
   efficient theory would appear as an afterthought. **Severity:** major.
2. **The distinction between UC evidence and a UC translation could be lost.**
   **Severity:** critical relative to the research question.
3. **Too many layers can obscure the simple behavioral map.** **Severity:**
   major.
4. **Conditional connection and measure claims might read as proved
   theorems.** **Severity:** critical.
5. **The metered architecture could be presented as canonical rather than a
   justified proposal.** **Severity:** moderate.
6. **Efficiency, boundedness, and availability could be used
   interchangeably.** **Severity:** critical.

### Resolution and revisions

- The unified paper will be retitled around operational realizations in both
  unbounded and efficient regimes. The abstract and contribution list will
  introduce the exact ledger, meters, oracle sort, and reduction transformer
  at the outset.
- UC/RSIM/IITM appear only in a source-evidence section. No role or security
  quantifier occurs in a definition.
- The exposition is staged:
  behavioral core; exact costs; metering and uniformity; specifications;
  distinguishers/reductions; explicit-resource refinements.
- Statement boxes use distinct labels: `Theorem`, `Conditional claim`,
  `Design proposal`, and `Counterexample`.
- The paper presents the architecture as one conservative instantiation with
  a route registry and states alternative reactive/flow models.
- Every use of “efficient” is qualified as implementation-efficient,
  efficiently accessible, resource bounded, or adequately responsive.

### Residual risk

The unified paper will be longer than MR11/MR18. It must preserve their
gradual style by moving detailed failure examples and proof obligations after
the main construction rather than front-loading every caveat.

## Cross-review verdict

No review found a reason to abandon the two-stage architecture, but four
changes are mandatory:

1. distinguish the costed lower observer from the ordinary random-system
   erasure;
2. make bare-wire normalization, not a relay machine, the graded identity;
3. separate ambient workload from transformed concrete cost profiles;
4. separate pure uniform security from arbitrary auxiliary-input and
   nonuniform variants.

At the end of this first pass, the high-risk seams were strict feedback,
finite oracle semantics, generated-network compilation, and explicit-resource
macro refinement. Later rounds discharged the finite oracle, compiler, and
finite costed-algebra obligations under explicit hypotheses. Strict
feedback/target-carrier identification and explicit-resource macro refinement
remain conditional.

---

## Second pass after the adequacy, compiler, algebra, and oracle proofs

This pass starts from the revised artifacts rather than merely checking that
the first-pass recommendations were copied.  Each perspective attempts to
falsify a stated theorem with a concrete countermodel.  “Closed” below means
that either the attack is ruled out by an explicit premise or the claim was
weakened.  “Residual” means the paper must still present the point as an open
obligation.

## Review 1B - complexity theory

### Attacks

1. **Truncation masquerades as polynomial time.** Every program can be given a
   polynomial meter, including one that always spins to exhaustion.
   **Severity:** critical.
2. **The ambient parameter can encode an arbitrary time bound.** If `b` is an
   arbitrary value selected separately at every `kappa`, polynomiality in `b`
   says nothing. **Severity:** critical.
3. **Compact graph declarations break the interpreter bound.** A length-`L`
   graph can contain `L` node records, each declaring `L` blank tapes with a
   logarithmic count. The claim that there are globally at most `L` virtual
   tapes is false. **Severity:** critical.
4. **An indexed list of session bounds hides nonuniform exponents.** Writing
   `sum_i P_i(kappa,b)` is not uniform if the family `(P_i)` is arbitrary.
   **Severity:** major.
5. **A polynomial number of ideal instances is generated for free.** A
   universal machine compiler can create implementation state, but not new
   independent abstract kernels. **Severity:** critical.
6. **Public tariff evaluation can hide a noncomputable predicate.** Even if
   the kernel is intentionally ideal, a free noncomputable admission test
   turns the meter itself into another oracle. **Severity:** major.
7. **Polynomial auxiliary input is silently treated as pure uniformity.**
   Taking a worst string independently at each parameter has advice strength.
   **Severity:** major.

### Resolution

- The revised efficiency witness requires metered boundedness,
  overwhelming no-exhaustion, productivity on the declared responsive domain,
  and behavioral realization as four separate predicates. `Spin` is bounded
  and inadequate.
- The workload policy is fixed finite syntax in each context. Quantification
  is one fixed context at a time, after which substituting its one polynomial
  into fixed grade transformers yields a polynomial closed profile.
- The compiler now permits up to `L^2` declared tape headers. Over `T` native
  transitions the sum of head movements is at most `LT`; a directory plus
  materialized intervals has size `O(L^2+LT)`, dominated by
  `O((L+T)^2)`. The interpreter constants were enlarged rather than hiding
  this correction.
- Logical sessions use one fixed session code and one fixed profile
  `P_s`; aggregate native work is bounded by
  `A P_s(kappa,b,L_s)`. Sequential lookup pays a factor `q` on every
  activation.
- Generated compilation is restricted to implementation nodes and one fixed
  external boundary. A parameter-dependent ideal array requires a separately
  specified countable product-state oracle and an instance-index tariff.
- Reservation and public-tariff evaluators are effective fixed code with a
  charged or explicitly administrative polynomial profile. Only the hidden
  specification kernel may remain noncomputable.
- Pure uniform, bounded auxiliary-input, and explicitly nonuniform modes have
  different quantifiers and names.

### Verdict

The complexity architecture survives. Attack 3 changed the theorem's
polynomial and attack 4 changed the logical-copy premise; they were not merely
editorial. The main residual is ordinary machine-model dependence through
six fixed routine-compilation constants. Literal numerical universal-machine
constants require printing the transition tables, but polynomial uniformity
does not.

## Review 2B - operational semantics

### Attacks

1. **Erasure loses the prefix before nonresponse.** Mapping every stop to one
   undifferentiated `NoResponse` identifies systems that emitted different
   visible events before stopping. **Severity:** critical.
2. **A terminal supervisor cannot see its own retained state.** A closing
   context may base its default decision on a private coin or an earlier
   reply not recoverable from the final response alone. **Severity:** major.
3. **State-dependent kernel samples cannot simply be “fixed.”** A Markov
   kernel does not arrive with a common sample space or pathwise coupling.
   **Severity:** critical.
4. **Sample-then-check makes successful responses cheap-biased.** Rollback
   conventions also break budget monotonicity. **Severity:** critical.
5. **Streaming changes the visible interface.** Comparing an atomic response
   directly with a sequence of chunks yields different transcripts even when
   every chunk fits. **Severity:** critical.
6. **Regenerating the decoded network at every external query resets lifetime
   state and randomness.** **Severity:** critical.
7. **Released reservation slack might be program-visible.** If so, a larger
   budget can change control flow. **Severity:** major.
8. **A context can refute every no-exhaustion claim by exhausting itself.**
   Quantifying global `Exhaust` over all metered contexts without attribution
   makes the adequacy predicate impossible. **Severity:** critical.

### Resolution

- Terminal outcomes retain the complete finite visible transcript `tau`.
  Behavioral erasure yields `NoResponse(tau,o)`, not a bare stop token.
- A closing test designates a finite observation `o` of its own terminal
  state. The supervisor sees `(tau,o,status,report)` but never hidden state of
  the tested graph.
- Every standard-Borel oracle contract selects a measurable randomization
  `sample(s,q,u)` and a named iid uniform seed sequence. The randomization
  theorem supplies existence; different choices preserve the one-experiment
  law while selecting possibly different cross-experiment couplings.
- Bounded calls reserve a public envelope before reading the fresh seed.
  Rejection does not sample, advance the seed, or change state. Exact
  response-dependent charges may affect later calls, but never select the
  current response.
- An unbounded atomic response is replaced by a stateful fixed-chunk
  specification *and a metered reassembly converter*. The converter retains
  the one token and hides the chunk interface. The comparison is between the
  original oracle and the reassembled external interface.
- The generated universal component initializes once. Decoded component
  state, stacks, meters, random positions, and the master-tape cache persist
  across every later macrostep.
- Reservations and remaining budgets are external non-observable state.
  Budget-monotonicity couples the same seed and exact charge whenever the
  smaller budget admits.
- Stop outcomes label the first blocking/exhausting action by an
  alpha-invariant public owner class. Resource adequacy bounds tested-side
  exhaustion and quantifies over completion contexts carrying their own safety
  certificate; context and shared-infrastructure bounds are then union-bounded
  to obtain the global closed-experiment statement. Arbitrary self-exhausting
  tests remain permitted for behavioral security, but not as availability
  witnesses.

### Verdict

The finite operational semantics survives. Attacks 1, 5, and 8 exposed real
semantic errors and forced changes to the carrier, streaming theorem, and
adequacy quantifiers. The residual is the unbounded
lifetime/strict-feedback map into the independently chosen random-system
carrier; the finite metered terminal kernel itself is proved.

## Review 3B - Constructive Cryptography and system algebra

### Attacks

1. **The identity wire either costs work or erases a real link.**
   **Severity:** critical.
2. **Alias equivalence can encode fanout or mix polarities.** Treating aliases
   as an arbitrary equivalence relation is too permissive for linear typed
   interfaces. **Severity:** critical.
3. **Connection order changes edge names and public ledger coordinates.**
   **Severity:** major.
4. **The contextual quotient may fail congruence under a binary operation.**
   **Severity:** major.
5. **Cyclic connection is called efficient merely because it exhausts.**
   **Severity:** critical.
6. **The costed quotient is silently identified with MR11 random systems.**
   **Severity:** critical.
7. **Pointwise `(kappa,b)` laws do not automatically give asymptotic closure.**
   **Severity:** major.

### Resolution

- A bare identity is an administrative typed boundary-face bijection, not a
  relay and not a physical matching. It composes names and contributes no
  transition or second edge.
- Aliases are bijections between faces after inner-interface polarity is
  transported to a common orientation. They cannot fan out. Alias chains
  normalize by associative function composition, not arbitrary equivalence
  closure.
- Every remaining physical edge receives an administrative name determined
  by its ordered endpoint pair. Public reports are invariant under hidden
  alpha-renaming.
- Cost and behavioral equivalence quantify over all one-hole closing
  contexts. Fixing the other argument of tensor/connection/converter action
  produces such a context, so contextual equivalence is a congruence.
- Arbitrary finite cycles have a bounded lower meaning because a positive
  quota eventually exhausts. Adequate efficiency requires a separate DAG,
  rank, affine-credit, or solved flow/progress certificate.
- Theorems 7.1 and 8.1 establish a finite operational system algebra and
  erasure homomorphism. The further map `J` into the selected lifetime
  random-system carrier is explicitly conditional on operational/strict
  feedback equality and target quotient congruence.
- Asymptotic closure additionally uses fixed polynomial profile transformers,
  fixed context workload policies, triangle inequalities, and negligible
  closure. These are stated outside the pointwise algebra theorem.

### Verdict

The finite costed algebra survives and is no longer merely proposed. Attack 2
changed the normalization definition. The exact remaining AC bridge is
`J`; no theorem in the revised ledger marks it proved.

## Review 4B - concrete reductions

### Attacks

1. **Challenge calls and side-oracle calls are conflated.** A transformer that
   leaves `P.calls` unchanged appears to lose the converter's inner queries.
   **Severity:** critical.
2. **Repeated queries break the parallel profile.** A bound on distinct inputs
   is enough for a collision probability, but not for call, traffic, or work
   accounting. **Severity:** critical.
3. **The wrapper omits routing, response parsing, and peak space.**
   **Severity:** major.
4. **The PRP/PRF hybrid assumes nonadaptive per-instance transcripts.**
   **Severity:** major.
5. **A varying number of parallel ideal instances is treated as a finite
   syntactic tensor.** **Severity:** critical.
6. **Same-budget nonexpansion is restated after all.** **Severity:** critical.
7. **A numerical advantage hides a catastrophic reduction cost.**
   **Severity:** major.

### Resolution

- Profiles have a separate challenge-query bound. `P.calls` denotes named
  side-oracle calls. Absorbing a converter retains every challenge query and
  adds its inner work/routes; no call is erased.
- In the parallel RF/RP calculation, `q_j` now bounds *total calls* to
  instance `j`. Distinct queries are at most `q_j`, so the same value safely
  bounds both switching loss and resource traffic.
- The tagged/truncated wrapper recomputes every phase:

  ```text
  C_seq = 8s + 9n + 3l + 12
  ```

  work per query, two converter activations, `2m` traffic bits, one oracle
  call, `m` query bits, `m` response bits, no random bits, and a conservative
  `4m+8` protocol-space increment (plus the two logical unary parameter tracks
  and heads in the primary uniform presentation).
- Couple all independent RF/RP pairs simultaneously.  Conditional on every
  common joint history, the next within-instance collision probability is at
  most the number of that instance's preceding distinct outputs divided by
  `2^m`.  A union bound over adaptive query positions gives

  ```text
  sum_j q_j(q_j-1)/2^(m+1)
    <= Q(Q-1)/2^(m+1).
  ```

- The parallel theorem is pointwise for fixed finite `h`. A varying
  `h(kappa)` needs a fixed multiplexer and a separate countable product-state
  specification; the implementation compiler cannot create the ideal copies.
- Every metric theorem is profile-reindexed:

  ```text
  d_P(alpha G,alpha H)
    <= d_(T_alpha(P))(G,H).
  ```

  Same-profile notation requires an additional domination proof.
- The numerical instance reports both loss `<2^-209` and wrapper work
  `44,761,612,288` bit-machine steps. The latter is not hidden by the
  asymptotic conclusion.

### Independent arithmetic check

The phase sums, persistent-mask lifetime formula, wrapper constant, numerical
product, generated-code bound (tested for `q=1,...,10000` with an arbitrary
fixed program length), and affine-credit polynomial were recomputed
independently. No discrepancy remained after correcting the generated-code
header and retained-output space.

### Verdict

The concrete reduction survives after total-call and space corrections. Its
switching bound is an upper bound after deterministic tagging/truncation, not
an equality claim. General polynomially many ideal instances remain subject
to the explicit array-specification premise.

## Review 5B - explicit resources and physical accounting

### Attacks

1. **The virtual native ledger is reported as physical universal-machine
   cost.** **Severity:** critical.
2. **The generator's output code is omitted from peak space.** A graph of
   length `Theta(q log q)` cannot be retained in `O(q)` cells.
   **Severity:** critical.
3. **Oracle responses create free local work or memory.** **Severity:**
   critical.
4. **A streaming oracle hides an arbitrarily long buffer in its converter.**
   **Severity:** critical.
5. **Exact ledger coordinates are called CPU/MEM resources without an API.**
   **Severity:** major.
6. **Memory and randomness are both implicit and explicit in the same
   refinement.** **Severity:** major.

### Resolution

- The compiler preserves the *virtual* native ledger as simulation data and
  bounds a separate physical universal ledger. Cost-aware equivalence is not
  asserted; erased transcript law is.
- The generated flip-chain example now uses
  `GenSpace=L_flip+16(q+1)`. The compiler profile also charges decoder tables,
  virtual directories, cache, and scratch space.
- Oracle admission never adds to local work or space. Every response bit is
  charged in the oracle/traffic ledger, and parsing, storage, copying, and
  re-emission consume the caller's unchanged local quotas.
- Streaming comparison includes a metered reassembly converter with chunk,
  work, output, and buffer-space budgets. The loss event includes failure of
  any of those coordinates.
- The ordinary exact ledger remains an accounting presentation. Reifying
  `CPU`, `MEM`, `RAND`, or `COMM` as an AC resource needs an API and a
  macro-erasure theorem; it remains a separate refinement.
- In an explicit-memory/randomness regime, converters lose hidden persistent
  work tapes/random tapes except for the declared finite-control and handles.
  The free-machine and explicit-resource regimes are alternatives.

### Verdict

The accounting layer survives, with attacks 1 and 2 forcing substantive
corrections. No claim currently proves a canonical physical processor/memory
API.

## Review 6B - finite implementability and probability

### Attacks

1. **“Fix every kernel sample” is undefined for a state-dependent kernel.**
   **Severity:** critical.
2. **An almost-sure tariff envelope does not prove strong metered boundedness
   on null seeds.** **Severity:** major.
3. **Graph counts encoded in binary cause exponential decoder allocation.**
   **Severity:** critical.
4. **Alpha-isomorphic graphs are assumed to serialize identically.**
   **Severity:** major.
5. **The universal simulator collapses independent random tapes to one shared
   stream.** **Severity:** critical.
6. **An unbounded response is sampled and rejected retroactively.**
   **Severity:** critical.
7. **The decoder/interpreter constants are fabricated without transition
   tables.** **Severity:** critical for a concrete numerical claim.

### Resolution

- Standard-Borel randomization supplies a measurable seed realization. Every
  occurrence receives an independent uniform sequence; pathwise statements
  fix those sequences.
- The bounded-call contract requires the reservation to dominate the selected
  sampler's output for every seed. An almost-sure envelope is named as a
  weaker variant and is not used for strong boundedness.
- Every decoded count is rejected if it exceeds total code length `L`; the
  decoder never expands an unchecked binary count. Its dense tables are at
  most quadratic.
- List positions are administrative occurrence names. The decoder validates a
  deterministic labeled presentation but performs no graph-canonicalization
  algorithm. Alpha-isomorphic decoded graphs meet only in the later
  operational quotient.
- Cantor's bijection sends master coordinate `pair(i,j)` to virtual node
  bit `(i,j)`. A finite-cylinder proof shows the resulting array has the
  independent product Bernoulli law. The cache changes access order, not
  values.
- Unbounded output uses the stateful streaming/reassembly construction; the
  original sample is committed once and never selected by fit.
- The polynomial and elementary scan coefficients are explicit. Four
  family-independent constants `c_dec,s_dec,c_int,s_int` represent expansion
  of a finite routine library to literal transition records. The theorem
  depends only on their finiteness. It makes no unsupported numerical claim
  that they equal one.

### Verdict

Finite metered probability semantics and generated compilation survive under
their displayed hypotheses. Exact universal-machine constants remain
available only after a literal implementation, correctly outside the current
theory claim.

## Review 7B - theorem status and exposition

### Attacks

1. **The paper still reads as an attempted UC instantiation.** **Severity:**
   critical relative to the user's question.
2. **A finite contextual quotient is advertised as the final random-system
   model.** **Severity:** critical.
3. **“Efficient” continues to mean merely metered.** **Severity:** critical.
4. **Internal notes contain stronger claims than the claims ledger.**
   **Severity:** major.
5. **The source discussion does not separate quotation, paraphrase, and new
   proposal.** **Severity:** major.
6. **The manuscript front-loads every caveat and loses the gradual MR11/MR18
   style.** **Severity:** major.
7. **A stale PDF can conceal that the corrected notes were never integrated.**
   **Severity:** critical for delivery.

### Resolution required for the final synthesis

- UC, IITM, and reactive-simulatability papers appear only as bottom-up design
  evidence about machine and runtime choices. No UC roles, corruption,
  scheduler, or security quantifiers are imported. The object being built is
  a lower realization beneath AC/CC.
- The paper must draw three distinct arrows:

  ```text
  finite costed operational quotient
       --proved erasure-->
  finite behavioral operational quotient
       --conditional J-->
  selected lifetime random-system carrier.
  ```

- Terminology is fixed: metered implementation, adequately efficient
  implementation, efficient realization, and efficient construction witness.
- The claims ledger is the controlling theorem-status source. The compiler,
  oracle, algebra, and adequacy notes have been brought into agreement with
  it; the final Typst source still requires the same update.
- `source-audit.md` records exact source location and labels every use as
  quotation, paraphrase, inference, or new proposal.
- The final paper should present the positive construction first:
  operational machines, exact ledger, metering, uniformity, oracle access,
  algebra, and efficient witness. Counterexamples and residual alternatives
  should follow the definition they motivate rather than dominate the
  introduction.
- The existing 33-page PDF predates the second-pass corrections and is not a
  deliverable. It must be regenerated and every page re-audited after the
  source is rewritten.

### Verdict

The theory notes now support a coherent paper, but the artifact does not yet.
This review remains open until Round 9 completes source integration,
compilation, text/status checks, and page-by-page visual inspection.

## Second-pass verdict matrix

| Obligation | Status after second pass | Exact boundary |
|---|---|---|
| Adequacy predicates and constructor rules | proved under displayed local and context-safety certificates | stop ownership is explicit; response-adaptive size recurrences need a stronger rule |
| Finite metered oracle terminal law | proved | standard-Borel, effective public reservation, finite quotas |
| No-selection and budget monotonicity | proved | pre-sample strong envelope and non-observable meter |
| Streaming comparison | proved generically | fixed one-token reassembler; concrete APIs need tail/profile instantiation |
| Generated-to-fixed compilation | proved at mathematical machine-construction level | fixed boundary/libraries, aggregate profile, symbolic fixed routine constants |
| Finite cost-aware system algebra | proved | finite normalized metered graphs and admitted oracle contracts |
| Erasure to behavioral operational quotient | proved | retains transcript/test observation; stop is semantic |
| Embedding into selected random systems | residual | strict-feedback equality and target quotient congruence |
| Explicit CPU/MEM/RAND/COMM refinement | residual | choose APIs and prove macro-erasure |
| Final academic paper/PDF | open | integrate revised results and repeat full artifact audit |

## Third-pass review - integrated manuscript semantics

This pass attacks the rewritten Typst manuscript rather than the supporting
notes.  It is intentionally independent of the second-pass verdicts: a claim
that is correct in a dossier but misstated in the paper still fails.

### Attack 1: the asymptotic quantifiers silently take a supremum over all PPT
codes

At a fixed parameter, the pointwise supremum over every polynomial-time code
can select a different code, degree, and hard-coded constant at every
parameter.  It is not the usual uniform computational-indistinguishability
quantifier and can destroy a true asymptotic statement.  The draft's phrase
“one negligible envelope for the declared test class” had the same problem.

**Resolution.** The paper now defines pure uniform indistinguishability as

```text
for every fixed code D and fixed polynomial policy p_D,
there exists a negligible nu_D.
```

Bounded auxiliary input places its supremum inside this fixed-`D`
quantifier.  A uniform concrete bound over a profile class is named as a
strictly stronger option, not smuggled into the definition.  The efficient
construction witness uses `epsilon_D` and `delta_C` unless such a concrete
uniform envelope is actually supplied.

**Verdict.** Resolved.  Profile-indexed `Delta_P` remains a pointwise concrete
pseudometric; it is not used to redefine the asymptotic quantifier.

### Attack 2: a context can refute every availability claim by exhausting
itself

The integrated paper originally described a terminal status but did not carry
ownership through every theorem.  A context that deliberately spends its own
quota then makes global no-exhaustion false for any tested resource.

**Resolution.** `Block` and `Exhaust` retain an alpha-invariant public owner;
graph syntax contains owner-library indices; absorption preserves those
labels; completion contexts certify context-side safety; and the global bound
is the union of tested, context, and shared-infrastructure events.  Arbitrary
self-exhausting tests remain valid for behavioral security because they have a
total semantic score after erasure.

**Verdict.** Resolved.  Availability and behavioral-security context classes
are deliberately different.

### Attack 3: the credit rule does not exclude local blocking

A decreasing feedback credit proves only that the number of hidden transfers
is finite.  A component may still block, diverge within an activation, or
exhaust locally before consuming credit.  The earlier theorem therefore did
not prove productivity.

**Resolution.** The affine-credit theorem now assumes that every activation
terminates within the local envelope without blocking or exhaustion and
either emits visibly or makes one credit-consuming hidden transfer.  At zero
credit the next activation is required to emit visibly.

**Verdict.** Resolved under the displayed local premise.  Credit is a
composition certificate, not a substitute for local correctness.

### Attack 4: an unbounded-output oracle is called “atomic” after the bounded
contract has rejected it

If response encodings have unbounded support for one query, the strong
pre-reservation contract cannot admit the one-shot call.  Comparing an
“atomic oracle” with the streamer could misleadingly suggest otherwise.

**Resolution.** The coupling theorem now compares the bounded streaming
implementation with an original *one-shot reference kernel*.  The reference
is a semantic specification used in the comparison, not an admitted bounded
call.  Handles have a fixed public code bound, the reassembler admits one
active handle, and the loss includes chunk calls, response traffic, local
work, output work, and buffer space.

**Verdict.** Resolved.  Neither successful reassembly nor a length cap is
silently conditioned into the original law.

### Attack 5: the explicit-resource figure overstates the target theorem

The last box in the refinement diagram was labeled “random system,” even
though only erasure into the finite behavioral operational quotient is proved.
This contradicted the text's conditional `J`.

**Resolution.** The diagram now ends at the behavioral operational quotient.
The separate map `J` is displayed in the reduction section and remains
conditional exactly on strict-feedback equality and target quotient
congruence.

**Verdict.** Resolved.  The paper presents the two lower quotients and the
target map as three distinct objects.

### Attack 6: generated uniformity has no complete numerical witness

A theorem containing only `poly(L,T)` can hide code size, retained generated
code, routing, interpreter state, or a parameter-dependent routine library.

**Resolution.** The paper now includes the generated flip-chain family.  It
derives a gamma-code length

```text
L_flip <= c_F q + (q-1)(4h_q+8) + 6h_q + 61,
```

charges retained code in generator space, prints native work/activation/
traffic/space bounds, and substitutes them into the fixed decoder/interpreter
profile.  The four remaining routine-expansion constants are fixed once for a
literal finite library and are not assigned invented numerical values.

**Verdict.** Resolved at the mathematical machine-construction level.
Literal transition tables remain an optional mechanization task.

### Attack 7: the reduction hides a practically useless wrapper behind a
negligible loss

The asymptotic switching statement alone omits the cost that motivates the
lower layer.

**Resolution.** The manuscript recomputes the tagged/truncated RF/RP wrapper
phase by phase, carries work, activations, traffic, space, calls, query bits,
response bits, and randomness, proves the adaptive fixed-`h` hybrid, and
reports the numerical pair

```text
loss < 2^-209,
wrapper work = 44,761,612,288 bit-machine steps.
```

The varying-`h(kappa)` case is explicitly outside the fixed-instance theorem
until an indexed product-state specification is supplied.

**Verdict.** Resolved.

### Attack 8: a total decision on nonresponse introduces a hidden timeout

A program cannot observe an infinite run and then output a decision.  Calling
the decision map a distinguisher transition would contradict strict
nonresponse.

**Resolution.** The decision map is now explicitly a meta-level scoring
convention on maximal semantic outcomes.  It never creates a wire response or
a successor round.  Cost-aware scoring may use finite meter status; behavioral
scoring must factor through semantic `NoResponse` and therefore cannot
distinguish blocking from exhaustion with the same visible prefix and closing
observation.

**Verdict.** Resolved at the finite metered layer.  Compatibility of this
semantic scoring convention with the independently selected random-system
observer carrier remains part of `J`.

### Third-pass status

The integrated source now agrees with the claim ledger on every issue above.
The remaining adversarial task is artifact-level: compile, inspect references
and fonts, render every page, and check that equations, tables, theorem boxes,
and page breaks do not visually change the intended claim.

## Fourth-pass review - the random-system bridge

The earlier manuscript left `J` conditional.  This pass asks whether the
remaining bridge can actually be proved for a selected carrier without
silently erasing physical routing or enlarging the computational test class.
The resulting construction is recorded in
`partial-random-system-bridge.md`.

### Attack 1: physical connection can exhaust although strict DDS feedback is
free

The costed graph operation adds a canonical physical matching.  If its router
has an arbitrary finite quota, `connect(G)` can stop even when cost-free
strict feedback of the erased behaviors succeeds.  Thus the unrestricted
behavioral operational quotient cannot map homomorphically to ordinary strict
connection merely by wishing the router away.

**Resolution.** Select the route-safe subalgebra.  Derive the canonical
router envelope from aggregate machine-work, oracle-call, and oracle-traffic
grades.  Blank output buffers and bit-costful emission bound machine event
count and bits by work; tariff reservations bound specification events.
One-token execution bounds live router space by one message.  The derived
envelope therefore dominates every possible canonical routing action.

**Verdict.** Resolved for structural plumbing.  An intentionally limited link
is an explicit resource node and may still exhaust; its failure is then part
of the target behavior rather than an artifact of connection.

### Attack 2: recomputing the routing grade under connection changes the
system

Tensor or connection increases the aggregate envelope.  If programs could
read quotas, or if an earlier valid route-safe router could have exhausted,
this could change behavior and destroy associativity.

**Resolution.** Grades are external and non-observable.  The domination
theorem shows that no valid route-safe router can be first to exhaust under
either envelope.  Every construction order has the same final normalized
graph and aggregate component/oracle grades, hence derives the same canonical
envelope.  Exact routing events and ledgers are unchanged.

**Verdict.** Resolved.

### Attack 3: the space of partial lifetime DDSs is only a hand-written
sigma-algebra

A pushforward law is not enough if the target is not a well-behaved measurable
space.

**Resolution.** For countable `X,Y`, embed partial functions in the countable
product `(Y+undefined)^(X^+)`.  Prefix closure is a Borel condition: its
failure is the countable union of finite-coordinate forbidden cylinders.
The partial-DDS subset is therefore standard Borel, with exactly the
evaluation sigma-algebra used by the operational proof.

**Verdict.** Resolved.

### Attack 4: common-domain transcript equivalence cannot observe random
nonresponse domains

The finite PDS source assumes compatible environments and one common domain.
Metered block/exhaust branches violate that premise.

**Resolution.** The selected extension uses maximal strict transcripts:
infinite interaction, finite environment stop, or finite system stop retaining
the unanswered query.  System stop is semantic and does not create a response
symbol.  On the finite common-domain compatible subcategory, the extra case
disappears and the source presentation embeds exactly.

**Verdict.** Resolved as an explicitly new carrier, not attributed to
Lanzenberger--Maurer.

### Attack 5: observational equivalence may not be a connection congruence

Feedback can make several adaptive hidden calls within one visible
interaction.  Equality of one-shot marginals would not suffice.

**Resolution.** Equality is by every complete transcript law, not marginals.
Given an environment for a connected system, lift it to the unconnected
boundary: after an answer at either connected port, issue the corresponding
hidden query; after another boundary answer, advance the outer environment.
A measurable hiding map removes hidden pairs and turns an infinite hidden
tail into strict outer nonresponse.  Pathwise equality followed by
pushforward proves congruence.  Separately, flattening nested single-edge
evaluators shows that every enumeration of one legal finite matching follows
the same hidden expansion, proving connection-order invariance.

**Verdict.** Resolved.

### Attack 6: finite coded contexts cannot quantify over every mathematical
environment

If operational contextual equivalence is coarser than target transcript
equivalence, `J` is not well-defined on its quotient.

**Resolution.** The proof is pointwise at fixed `(kappa,b)`, not a uniform
implementation theorem for the whole environment.  If two target measures
differ, they differ on a finite maximal-transcript cylinder.  Along that
one cylinder a deterministic environment uses only finitely many finite
queries and expected responses.  A finite lookup context with a sufficiently
large constant grade implements exactly that test.  Conversely, conditioning
a finite behavioral context on its tapes and oracle seeds yields a
deterministic partial environment and semantic score.  Hence operational and
target equivalence coincide pointwise on route-safe graphs.

**Verdict.** Resolved without enlarging asymptotic computational security,
which continues to quantify only over fixed uniform codes.

### Attack 7: oracle kernels destroy the fixed-sample DDS map

State-dependent kernels do not come with canonical samples, and their hidden
states need not be countable.

**Resolution.** The bounded oracle contract already selects a measurable
standard-Borel randomization and one named iid uniform seed sequence per
occurrence.  Fixing tapes, seeds, and initial specification states makes the
lifetime execution deterministic.  Measurable finite-step composition gives
each DDS evaluation event; pushforward gives the target law.

**Verdict.** Resolved under the existing oracle hypotheses.

### Attack 8: the selected carrier is advertised as every existing notion of
random system

Different external theories may identify nonresponse differently or choose a
different feedback fixed point.

**Resolution.** The theorem names its codomain `RS_partial`, proves the finite
common-domain embedding, and states comparison with any differently mandated
carrier as a separate conditional theorem.  What is now complete is a valid
lower AC instantiation, not uniqueness of all random-system presentations.

**Verdict.** Resolved.

### Fourth-pass verdict

The route-safe restriction is mathematically necessary and not cosmetic.  It
turns the former operational/target seam into a theorem while preserving
limited communication as an explicit resource.  The proved chain is now

```text
route-safe costed quotient
  --cost erasure-->
route-safe behavioral operational quotient
  --injective J-->
selected standard-Borel partial random systems.
```

The only carrier-level residual is comparison with a separately imposed
nonresponse or feedback convention.

## Fifth-pass review - quantifier and edge-case audit of the proved bridge

This pass treats the fourth-pass resolution as an adversary would: every
compressed phrase is tested on terminal branches, infinite branches, and the
distinction between a pointwise semantic observer and a uniform efficient
algorithm.

### Attack 1: an arbitrary measurable terminal scorer is free
noncomputable advice

The pointwise costed quotient compares full terminal laws by quantifying over
all measurable bit maps.  Reusing that observer class verbatim in
computational indistinguishability would let a “PPT” test apply an
uncomputable predicate to a finite transcript or exact report without paying
for it.  A finite output does not imply an effectively decidable predicate of
that output.

**Resolution.** Separate the observer classes.  The pointwise quotient keeps
all measurable terminal maps because this is simply equality of complete
outcome laws.  A computational distinguisher instead contains one fixed
uniform graded terminal-scorer program.  Its input reading, report processing,
work, and space are in the test profile; a fixed bit completes the experiment
if the scorer itself blocks or exhausts.  Behavioral scoring receives only
the erased record.  Post-run invocation cannot create a wire response or
restart a stopped interaction.  The cost-aware report projection is also
fixed and effective, with certified polynomial evaluation and output length;
terminal-record length is a profile coordinate and is transformed under
converter absorption.  The report is frozen from the interaction ledger
before scoring starts.  Report/scorer work is charged for admissibility but
is not recursively added to the input being scored.

**Verdict.** Resolved.  Total semantic observation and efficient computation
are no longer conflated.

### Attack 2: the route envelope does not say whether there is one router or
one router per edge

The exact ledger names canonical infrastructure occurrences per physical
edge, whereas the envelope is aggregate.  If the theorem silently assumes one
global router, it changes the cost model; if it assigns only a fraction to
each edge, one edge might exhaust despite the aggregate inequality.

**Resolution.** Each canonical edge may conservatively receive the full
whole-graph envelope.  Since the aggregate use of all canonical edges is
below that envelope, every edge's local use is below it.  An equivalent
implementation may enforce one shared aggregate meter while retaining exact
per-edge ledger coordinates.  Recomputing the same whole-graph envelope after
normalization is independent of construction order.

**Verdict.** Resolved without choosing a privileged routing architecture.

### Attack 3: external queries are absent from the event-count bound

An environment can emit an input before the tested component has spent any
work.  If that input is charged to an internal router but is absent from
`W,C,R`, the first physical route can invalidate the domination theorem.

**Resolution.** Open-boundary delivery is not an ordinary matched edge and
uses no hidden canonical router.  Once a closing context is attached, its
machine must construct and emit the query before it crosses the newly created
matching; blank-output bit cost includes the event and its bits in the
aggregate machine-work bound.  A direct query to a specification is likewise
emitted by the context and the specification reply/block is covered by the
call envelope.

**Verdict.** Resolved under the stated boundary-delivery convention, which is
now explicit.

### Attack 4: tensor congruence ignores an infinite run confined to the fixed
factor

“Condition on the second DDS and absorb its answers” is incomplete if the
joint environment makes infinitely many second-factor queries before it ever
returns to the first factor.  No next query for the derived first-factor DDE
then exists, but replacing that behavior by an ordinary environment stop
would change the maximal transcript.

**Resolution.** Split each simulated block into three cases: it reaches a
first-factor query; it stops finitely; or it continues forever entirely in
the fixed factor.  Only the first case consults the replaced law.  A
deterministic reconstruction map restores the finite stop or infinite
fixed-factor transcript in the other cases.  Finite path events are
evaluation cylinders and the infinite case is their countable limit, so the
conditional kernels are measurable before integration.

**Verdict.** Resolved.

### Attack 5: compatible finite PDS environments do not justify an “exact
subtheory” claim

The source common-domain equivalence tests only compatible environments.  The
partial carrier also tests environments that deliberately query outside the
domain and observes a pending-query `SysStop`.  Merely noting that compatible
runs have no `SysStop` proves only one direction.

**Resolution.** For common domain `D`, truncate any environment immediately
before its first out-of-domain query.  This truncation is compatible.  The
maximal run of the original environment is a deterministic transform of the
ordinary run of the truncation: a genuine environment stop and a
domain-forced truncation are distinguished from `e`, `D`, and the finite
output history, and the latter restores the pending query.  Hence
source-equivalent PDSs agree under all extended environments, while the
converse is immediate from compatible tests.

**Verdict.** Resolved; “embeds exactly” is now proved rather than inferred.

### Attack 6: conditioning a randomized operational context may leave hidden
random initial state

Fixing only machine tapes and oracle seed sequences is insufficient when an
abstract specification occurrence has a random initial standard-Borel state.
The alleged deterministic environment could remain randomized.

**Resolution.** The reverse full-abstraction proof now conditions on initial
specification states as well.  With all three sample families fixed,
single-token execution between boundary calls is deterministic and can be
replayed into a partial DDE.  Integration is over their joint product law
(or the explicitly declared joint law of a shared resource).

**Verdict.** Resolved.

### Fifth-pass verdict

The audit found one genuine computational error—the free arbitrary
terminal-scorer class—and several proof compressions.  The computational
definition now charges scoring, while the pointwise quotient retains its
information-theoretic observer.  The router, tensor, common-domain, and
conditioning arguments now cover their terminal and infinite edge cases
explicitly.

## Sixth-pass review - selected explicit computation resources

This pass treats the new processor--store--coin translation as an
implementation theorem rather than accepting a diagram labeled `CPU || MEM ||
RAND`.  The target is exact administrative erasure for one selected
single-token API, not universality over hardware models.

### Attack 1: sequential debiting changes the failed ledger

If the adapter decrements the processor, consumes a coin, and only then finds
that the store update exceeds capacity, the explicit run has spent resources
which the native external meter never commits.  It may also expose a different
first exhausted subresource.

**Resolution.** Processor, coin, and store operations have a prepare/commit
split.  A reservation locks capacity but changes no native projected
coordinate.  All selected reservations occur before any commit; commits are
infallible.  Every rejecting primary resource has the same public owner `v`.
The state relation is asserted only at transaction boundaries, so the proof is
a stuttering simulation rather than a false one-resource-step bisimulation.

**Verdict.** Resolved for the selected single-owner API.

### Attack 2: worst-case pre-reservation rejects a fitting random branch

Reserving the maximum space of both random successors is safe as an upper
bound but not behaviorally exact.  One branch can exceed `S` while the sampled
branch fits.

**Resolution.** The coin resource supports a non-destructive reservation.  It
returns the actual current bit without advancing the head or committing a read.
The processor computes the actual command and only then does the store test
the prospective footprint.  If that test fails, the run terminates and the
speculatively exposed private bit has no external continuation.

**Verdict.** Resolved.  The theorem would be false for a fresh-bit-only source
without reservation or for a shared coin interface visible during prepare.

### Attack 2b: the random-head move is chosen before seeing the bit

In an ordinary transition table, the current random bit may determine not only
the work-tape update but also whether the random head advances.  An API
`reserveRead(advance?)` called before returning the bit cannot simulate that
transition.

**Resolution.** `reserveMode(use?)` only performs a non-destructive peek and
reserves one read.  After `planCoin` sees the bit, its command contains the
actual advance flag.  `commitRead(cap,advance?)` consumes the read and moves
the head accordingly.  A failed later store reservation commits neither.

**Verdict.** Resolved; the advance decision is now at the correct phase.

### Attack 3: administrative traffic leaks the coin

Even with hidden ports, a cost-aware terminal scorer could infer a secret bit
if the two branches use different numbers or lengths of private messages.  It
could also infer whether the current instruction reads randomness when a
failed native transition commits no `rand` coordinate.

**Resolution.** Every transition follows one padded eight-phase control shape.
The coin source receives either a genuine read mode or a no-read mode with the
same message length.  The latter returns a fixed dummy bit and cannot fail.
Both random branches use fixed-size plan and update-command records.  Native
output, peak space, or exhaustion may still depend on the bit exactly as in
the source machine.  Full physical reports retain program and administrative
costs, but their control-message size is not a new branch side channel.

**Verdict.** Resolved at the declared aggregate report interface.  An API that
publishes private message payloads or reservation types is a leakage resource
and needs a different security theorem.

### Attack 4: the stateless driver secretly retains the continuation

A multi-call orchestration normally remembers whether it is waiting for the
processor, coin, or store and where the eventual output should return.  Keeping
that state in `Drive_P` recreates precisely the hidden memory excluded by the
MR16 refinement.

**Resolution.** Transaction phase, pending native port, frame, and command live
in `STORE` or the unique in-flight record.  Return destinations are fixed
tags carried by that record.  The driver is a generated tag router and
constant-program selector only.  Its ports are all hidden after attachment.

**Verdict.** Resolved by the state invariant.  A hand-written stateful RPC
adapter would not satisfy the theorem.

### Attack 5: an arbitrarily long input is installed atomically for free

`STORE.accept.prepare(input)` appears to hold the whole input before checking
capacity.  This either requires unbounded unreported scratch or copies a
payload which the failed source activation did not copy.

**Resolution.** The validated self-delimiting header exposes the encoded
length while the value remains in the charged original routing buffer.  Store
and activation capacities are reserved from the length.  Only after both fit
does the route-safe adapter make one charged private copy into the reserved
native input region.  The temporary routing buffer and copy work are explicit
administrative coordinates.

**Verdict.** Resolved under the paper's effective self-delimiting codec and
boundary-delivery convention.

### Attack 6: processor and randomness resources hide their own memory

The processor retains a program and counters; the coin source retains a head,
read count, and current bit.  Calling only the mutable work tapes “memory”
would make the explicit physical-space claim false.

**Resolution.** The native projection preserves only the original logical
`peak_v`.  The full explicit report additionally includes program length
`L`, logarithmic processor/coin/meter counters, fixed transaction scratch, and
the in-flight event buffer.  The sampled infinite coin tape is an ideal
randomness resource rather than a claimed finite-memory implementation.

**Verdict.** Resolved by weakening exactness to the named native projection
and reporting the new coordinates.  Implementing the ideal coin source is a
further lower layer.

### Attack 7: transition planning is an unmetered computation oracle

The processor computes `plan(frame)` before its token commits.  A malicious
caller might reserve, query, abort, and repeat to obtain arbitrary free
computation.

**Resolution.** Administrative interfaces are private; only the fixed driver
can reach them.  Reservations return linear capabilities, admit at most one
outstanding transaction under the single-token invariant, and cannot be
replayed.  Planning occurs only after a successful step reservation and has no
second public result.  An abort exists only as terminal exhaustion of the
whole run.

**Verdict.** Resolved for encapsulated resources.  A shared public processor
requires an access-control and scheduling API.

### Attack 8: distributed commit exposes a torn machine state

Coin, processor, and store cannot literally update in one small step.  A
context, clock, reset, or concurrent caller could observe the interval after
one commit and before another.

**Resolution.** There is one token, all administrative ports are private,
commits cannot fail, and no native output is possible until the final store
commit.  The decreasing phase rank makes the interval finite.  The theorem
therefore relates only transaction boundaries and erases the private suffix.

**Verdict.** Resolved in the selected observation model.  Visible clocks,
crash recovery, reset, and concurrent sharing are explicitly outside scope
because they make torn states observable.

### Attack 9: processor tokens do not by themselves imply availability

Finite quotas prevent infinite administrative execution only if every private
call answers and the orchestration does not cycle.  Otherwise an allegedly
equivalent translation can block before its native counterpart.

**Resolution.** Each reservation either answers or produces a terminal lower
stop, commits are total, and every administrative phase strictly decreases a
fixed rank.  This is a local progress certificate, not a conclusion drawn from
the word “metered.”  Exact erased behavior then transfers native productivity
and no-exhaustion once the derived administrative envelope is supplied.

**Verdict.** Resolved.

### Attack 10: `MEM[S]` silently means both tape space and RAM

An address-space bound, number of nonblank tape cells, number of allocated
words, and maximum resident bytes are inequivalent.  A proof for one cannot be
advertised as a proof for all.

**Resolution.** `STORE[S]` tests exactly the native `live_P(c)` of the selected
multitape model and exposes only scanned local frames and constant-locality
updates.  The paper calls random-access memory and another cell metric
different APIs requiring new refinements.

**Verdict.** Resolved by narrowing the theorem.

### Attack 11: `COMM[c]` still hides topology and failure behavior

A bit count does not decide whether messages are copied or ownership is
transferred, queued, reordered, delayed, dropped, or delivered adversarially.

**Resolution.** The proved communication instance is `SLINK_e[C,W,S]`: one
buffer, one token, canonical copying, no clock, and an atomic joint check of
traffic, router work, and buffer capacity.  It either delivers one identical
event or returns owner-labeled exhaustion.  Smaller bounds make it an
intentional fallible node; route-envelope bounds make it transparent.

**Verdict.** Resolved only for this selected lossless sequential link, as the
statement now says.

### Attack 12: a visible clock contradicts administrative erasure

Two native-equivalent programs may expand to different numbers of private
phases.  A clock-reading context distinguishes them even when first visible
outputs agree.

**Resolution.** No visible clock occurs in the refinement theorem.  Time is
either a hidden meter, a coordinate retained in a timed target, or paired with
a restricted clock-insensitive observer class.

**Verdict.** The unrestricted visible-clock refinement is correctly rejected,
not left as an unproved part of the theorem.

### Attack 13: charging the meters creates an infinite regress

If every quota comparison and ledger append must itself call the same
processor and store, the resource account never reaches a bottom layer.

**Resolution.** Token checks, capacity checks, and ledger updates are declared
primitives of this selected layer and their state size is reported.  The
top-down theory permits a later realization of those primitives.  The theorem
does not claim a final physical model.

**Verdict.** Resolved as an explicit abstraction boundary.

### Attack 14: full cost-aware equality is overclaimed

The explicit network necessarily contains initialization, transaction, and
private-copy costs absent from the native ledger.  Equality of full terminal
reports is false.

**Resolution.** The theorem states pathwise behavioral equality after
`erase_admin` and exact ledger equality only after the named projection
`pi_native`.  Full explicit reports retain program storage and administrative
work, traffic, and space.  A test allowed to score those coordinates may
distinguish the presentations.

**Verdict.** Resolved; the new arrow is a cost-report projection
homomorphism, not an isometry of physical ledgers.

### Attack 15: generated programs reintroduce nonuniform constants

The fixed-program administrative constants can depend arbitrarily on
`kappa` if a different transition table and adapter are simply postulated at
each parameter.

**Resolution.** The primary presentation uses one fixed program receiving
unary `kappa`.  The generated presentation requires one fixed
polynomial-time generator, a polynomial code-length bound, and one universal
administrative template whose profile is a fixed polynomial in code length
and the native grade.  Program initialization is charged.

**Verdict.** Resolved under the same uniformity modes as the machine compiler.

### Sixth-pass verdict

The explicit-resource obligation is discharged for one carefully delimited
sequential API.  The proof depends essentially on transactional reservation,
linear capabilities, private administrative ports, padded control traffic,
and the finite phase rank.  None is decorative: removing any one yields a
counterexample above.  The result does not cover shared processors, RAM,
visible timing, reset, leakage, concurrent communication, or a physical
implementation of the ideal coin source.  Those are named lower refinements,
not silently bundled into the theorem.

## Seventh-pass review - response-adaptive acyclic composition

### Attack 1: a DAG does not stop iteration inside one activation

A parent can call the same lower-ranked echo child polynomially many times and
square the preceding reply length before every next call.  The graph has one
acyclic edge, while message length becomes doubly exponential.

**Resolution.** The elementary DAG rule remains explicitly
response-independent.  The stronger rule requires a supplied polynomial
cumulative-response invariant `Z_v` and a proved post-fixed-point inequality.
The repeated-squaring example has no such nonzero polynomial invariant.

**Verdict.** Resolved; graph acyclicity is no longer confused with size
stability.

### Attack 2: the invariant proof is circular

The local `Q_vw(...,Z_v)` and `M_vw(...,Z_v)` bounds are valid only while the
response total is below `Z_v`, which is precisely what the theorem is trying
to prove.

**Resolution.** Use a first-crossing argument.  Before the first response that
would cross `Z_v`, every earlier prefix satisfies the premise, so every issued
query and the number of calls up to and including the crossing call obey the
local bounds.  Child response envelopes then make the total at most the
post-fixed-point left side, contradicting a crossing.

**Verdict.** Resolved without assuming the conclusion.

### Attack 3: a marginal child bound fails under adaptive steering

A parent can choose a rare hard child input after seeing previous replies.
An isolated average or marginal response/work bound does not survive this
selection.

**Resolution.** Local response, work, and failure certificates hold
conditionally and uniformly over every certified adaptive history and input
within the size invariant.  The probabilistic proof union-bounds these
conditional failures and assumes no independence.

**Verdict.** Resolved under the same history-uniform premise as the elementary
DAG theorem.

### Attack 4: the theorem hides the hard part in the word “solve”

Existence of a polynomial post-fixed point for arbitrary monotone polynomial
recurrences is not automatic, and deciding semantic program bounds is not
generally decidable.

**Resolution.** `Z_v` and a proof of the displayed inequality are explicit
certificate data.  The result is a checker theorem: if the certificate is
supplied, adequacy follows.  Automatic synthesis is listed as a separate
research problem.

**Verdict.** Resolved by stating the quantifier honestly.

### Attack 5: local work double-counts or omits child execution

If `t_v` includes child work, adding the recursive sum double-counts it.  If it
does not include response parsing and retained data, the total is too small.

**Resolution.** `t_v(kappa,b,n,z)` is explicitly the parent's own total local
work over the activation, including query construction, parsing, and
continuation, but excluding child occurrence work.  The recursive sum charges
each child activation once.  Routing is a separate term.

**Verdict.** Resolved by the ledger ownership convention.

### Attack 6: peak space is added like time

Summing every child peak across sequential calls can be safe but misleading;
taking only a maximum can omit the suspended parent's retained state.

**Resolution.** The recurrence adds the parent's retained state and fixed
administrative stack to the maximum live child stack.  Cumulative coordinates
sum over calls; peak coordinates use maximum plus retained ancestors.  Fixed
DAG depth keeps the stack polynomial.

**Verdict.** Resolved.

### Attack 7: a different invariant polynomial is hard-coded at each
parameter

Pointwise existence of some finite `Z_(v,kappa)` is vacuous and can conceal
nonuniform exponents.

**Resolution.** Each `Z_v(kappa,b,n)` is one fixed finite polynomial
description in the declared uniform certificate.  Generated presentations
must generate the certificate with the same fixed polynomial profile.

**Verdict.** Resolved.

### Attack 8: the response envelope is known only at the global input bound

A child may be reached with many query lengths, so a single number `R_w(L_w)`
does not justify the parent's functional recurrence.

**Resolution.** Reverse induction first constructs monotone per-input envelope
functions `Resp_w(kappa,b,m)`, `Work_w(kappa,b,m)`, and `Space_w(kappa,b,m)`.
The parent's post-fixed point evaluates those functions at its own adaptive
query bound.  The forward pass later substitutes the global `L_v` and computes
activation multiplicities.

**Verdict.** Resolved by separating functional reverse envelopes from global
forward counts.

### Attack 9: connecting two certified DAGs can create a cycle

Each operand may have a valid post-fixed-point certificate while their new
cross-connection points back to a parent.

**Resolution.** The theorem applies to the final normalized union graph and
requires it to remain a fixed DAG.  Otherwise the composition needs a new
rank, affine-credit, or solved-flow certificate.

**Verdict.** Resolved; adequacy is not claimed closed under arbitrary
connection.

### Attack 10: the stronger rule may still be vacuous for useful adaptive
protocols

If it rejects every response-dependent query, it has only renamed the
elementary restriction.

**Resolution.** When a child reply has public length at most `lambda`
independently of its query and the parent makes at most `q` calls,
`Z_v=q*lambda` is a valid post-fixed point.  The next query may depend on all
prior reply contents and cumulative length, evaluated at that envelope.

**Verdict.** The rule admits genuine response adaptivity while rejecting
uncontrolled size iteration.

### Seventh-pass verdict

The generic response-adaptive DAG obligation is discharged as a certified
post-fixed-point theorem.  What remains open is invariant discovery, not the
soundness of a supplied invariant.  The distinction mirrors the rest of the
paper: grades and progress certificates are evidence checked by the lower
theory, not automatically inferred from arbitrary code.

## Eighth-pass review - concrete unbounded-response streaming

### Attack 1: the advertised code is not self-delimiting

Chunking an arbitrary bitstring without retaining its length does not identify
where one response ends.

**Resolution.** `GeoBits` returns `(L,U)` using `1^L 0 U`.  The first zero
determines `L`, after which exactly `L` payload bits are read.  No codeword is
a prefix of another.

**Verdict.** Resolved.

### Attack 2: the geometric tail has an off-by-one error

With code length `2L+1` and capacity `2*kappa*(b+1)`, the largest fitting
length and the failure event must be computed exactly.

**Resolution.** The largest fitting integer is
`L=kappa*(b+1)-1`; failure is `L>=kappa*(b+1)`.  For
`Pr[L=ell]=2^(-ell-1)`, the latter probability is exactly
`2^(-kappa*(b+1))`.  The threshold was independently checked for
`(kappa,b)=(1,0),(1,7),(2,1),(8,7),(128,0)`.

**Verdict.** Resolved.

### Attack 3: a full final chunk needs an extra empty call

If completion is reported only by a subsequent empty chunk, a response of
exactly `Q*c` bits needs `Q+1` calls and violates the profile.

**Resolution.** The resource knows the retained finite code and tags the last
full *or* partial chunk `done`.  Thus a nonempty fitting code uses exactly
`ceil((2L+1)/c) <= Q` `Next` calls.

**Verdict.** Resolved.

### Attack 4: `Start` retries until it samples a fitting length

Such retrying would replace the geometric law by its short-response
conditioning and invalidate the coupling.

**Resolution.** `Start` samples and commits one response exactly once.  If
reassembly later exhausts, the experiment terminates.  No rollback or retry
interface exists.

**Verdict.** Resolved.

### Attack 5: the oracle hides an unbounded response buffer

The streaming resource retains the sampled code in hidden state, potentially
far beyond the caller's memory bound.

**Resolution.** This is an abstract specification resource.  The theorem
charges access, chunks, and the caller's reassembly memory, but makes no claim
about implementing the oracle's hidden state.  Reifying that storage would be
a different construction problem.

**Verdict.** Resolved by the two-sort boundary, not by calling the hidden
buffer efficient.

### Attack 6: only chunk traffic is funded

Receiving chunks does not pay for parsing, storing, and copying the final
blank output register.

**Resolution.** The profile has separate `Calls`, `ChunkBits`, local `Work`,
`Space`, and `OutputBits` coordinates.  Fixed compiled-copy constants multiply
the full `cQ` payload.  The generic coupling's failure event includes every
one of these coordinates.

**Verdict.** Resolved.

### Attack 7: the chunk size is zero at the security parameter zero

`c(kappa)=2*kappa` provides no progress at `kappa=0`.

**Resolution.** The proposition explicitly assumes `kappa>=1`, as is standard
for asymptotic security tails.  One could instead define `c=2(kappa+1)`
without changing the method.

**Verdict.** Resolved.

### Attack 8: tag and handle bits invalidate the capacity arithmetic

The equation `2L+1<=cQ` covers only response-code payload, not repeated chunk
headers.

**Resolution.** `c` bounds payload per chunk.  The response-bit profile is
`Q(c+h)` with fixed handle/tag overhead `h`; routing and local profiles fund
that value.  The tail threshold concerns only whether the payload code fits in
`Q` chunks.

**Verdict.** Resolved.

### Attack 9: the tail is not negligible uniformly in workload

An adversarial workload could in principle weaken the exponent.

**Resolution.** The workload is a natural number and
`2^(-kappa*(b+1)) <= 2^(-kappa)` for every `b>=0`.  Larger declared workload
only supplies more chunks and decreases failure.

**Verdict.** Resolved.

### Attack 10: the tail is added twice to security error

Exhaustion already appears as nonresponse after erasure; independently adding
it to a total-variation mismatch can double count the same event.

**Resolution.** The streaming proposition uses one common-sample coupling and
states a single disagreement event.  A higher construction may retain the
exhaustion probability as a separate adequacy field or use it in a behavioral
triangle bound, but must not call the two occurrences disjoint without
defining them.

**Verdict.** Resolved consistently with the metered/unmetered coupling rule.

### Eighth-pass verdict

The generic streaming theorem now has one complete nontrivial instance with
unbounded response support, exact tail arithmetic, fixed hidden-handle
semantics, and a full polynomial caller profile.  It remains an
oracle-relative access theorem, not an implementation of the hidden geometric
sampler or response buffer.

## Ninth-pass review - generated implementations versus explicit resources

### Attack 1: nodewise reification manufactures ideal resources

The generated-network compiler is allowed to create implementation records,
not new independent abstract oracles.  Replacing each of
`q(kappa)` decoded machines by its own `PROC/STORE/COIN` bundle would silently
generate `q(kappa)` specification-resource occurrences and independent coin
sources.

**Resolution.** Order the translations:

```text
generated graph
  --fixed generator/decoder/interpreter-->
one fixed universal machine
  --explicit translation-->
one fixed PROC/STORE/COIN bundle.
```

The generated code and virtual configurations are data in the universal
`STORE`; the one universal `COIN` supplies the master tape whose Cantor
coordinates realize the virtual independent tapes.

**Verdict.** Resolved.  Direct nodewise reification is rejected without a
separately defined indexed product-state computer resource.

### Attack 2: the virtual ledger is fed to the physical processor resource

The compiler preserves the decoded graph's native ledger only as virtual
simulation data.  Its actual interpreter cost is much larger.

**Resolution.** The explicit processor/store quotas are obtained from the
compiler's *physical* work, space, and random profile.  The native projection
of the explicit bundle equals that universal physical ledger.  The decoded
virtual ledger remains a further report projection and is never called
physical cost.

**Verdict.** Resolved by composing profiles in the correct direction.

### Attack 3: the explicit processor program still varies with `kappa`

If `PROC` is loaded directly with the generated graph as a new executable at
each parameter, fixed-program administrative constants may become nonuniform.

**Resolution.** The processor's immutable executable is the one fixed
universal decoder/interpreter.  The generated graph code is charged input/data
stored in `STORE`, with length and generation bounded by the existing compiler
certificate.

**Verdict.** Resolved.

### Attack 4: one coin resource loses virtual independence

Putting all simulated components behind one random source might correlate
their tapes.

**Resolution.** The existing compiler theorem uses Cantor's bijection from
`(virtual occurrence,local position)` to master-tape coordinates.  Every
finite collection uses distinct fair coordinates, hence has the independent
Bernoulli product law.  Explicit translation preserves that physical master
tape pathwise.

**Verdict.** Resolved under the compiler's named-tape coupling.

### Attack 5: polynomial closure is asserted without composing the two
profiles

The decoder/interpreter can have a high-degree polynomial, and the
administrative layer adds another transformer.

**Resolution.** First substitute the generated code-length and aggregate
native profile into the displayed decoder/interpreter bounds.  Then substitute
that physical universal profile into the explicit administrative affine
bounds and program/counter space formula.  Finite composition of these fixed
polynomials is polynomial; no same-profile claim is made.

**Verdict.** Resolved.

### Ninth-pass verdict

Generated implementation syntax and explicit resource assumptions do not
commute automatically.  The paper now proves only the valid order—compile to
one fixed universal implementation, then reify it—and names the opposite
order's missing indexed-resource theorem.  This closes a genuine
cross-layer uniformity error.

## Tenth-pass review - representation-level space accounting

### Attack 1: the store hides tape-head coordinates outside native peak space

The native live-cell ledger counts finite tape support and registers.  An
explicit `STORE`, however, must encode the absolute position of every tape
head.  Calling its administrative state constant would therefore omit an
unbounded logarithmic memory term.

**Resolution.** Let `H_P` be the fixed number of ordinary heads.  Under the
selected standard initialization, each ordinary head begins at a designated
origin, the input is contiguous, and a transition moves a head by at most
one.  With native bounds `T` and `S`, every live-cell and head coordinate
therefore has magnitude at most `T+S+1`.  A canonical sparse serialization
has at most `S` cell records.  The full explicit report now includes

```text
O((S+H_P) log(T+S+2))
```

plus the program and logarithmic `T,A,R,S` counters.  The random head is
monotone and advances at most `R` times, so its coordinate is already included
in the `log(R+1)` term.  No equality is claimed between this serialized
representation cost and native `peak`; the primary `STORE[S]` capacity remains
the selected logical live-cell metric.

**Verdict.** Resolved for the standard initialized sequential API.

### Attack 2: a sparse initial tape can place a head at an astronomically
large coordinate

Finite support alone does not bound the bit length of its coordinate labels.
If arbitrary sparse configurations are admitted as uncharged initial states,
`S` need not control the position encoding.

**Resolution.** The explicit theorem is stated for the selected standard
initialization used by the native machine layer: input is installed
contiguously at the origin and ordinary heads start at designated origin
positions.  A theorem for arbitrary supplied initial configurations must add
their serialized representation length (including coordinate labels) to the
input and initial-space profile.  The paper does not silently extend the
current bound to that regime.

**Verdict.** Scope made explicit; the arbitrary-configuration variant remains
a separate charged-input theorem.

### Tenth-pass verdict

The cost projection remains exact only after erasing representation state.
The complete explicit report now charges the sparse tape serialization,
ordinary and random head coordinates, and every variable quota counter, and
explicitly ties the polynomial bound to standard initialization.

## Eleventh-pass review - universal compiler quota representation

### Attack 1: transition count does not bound unused meter state

The compiler originally bounded its virtual tables by `O((L+T)^2)`, where
`T` was aggregate executed work.  A generated graph can execute one step while
carrying a workload-dependent quota whose binary representation grows with
`b`.  The interpreter stores that virtual meter, so a table bound solely in
`T` omits real state.

**Resolution.** Define the fixed polynomial magnitude envelope

```text
M = 1 + kappa + b + sum_x P_native^x(kappa,b),
```

over all aggregate profile coordinates.  Then every virtual quota/counter is
at most `M`, `T<=M`, and `O(L)` meter records use
`O(L log(M+1))` bits.  The virtual state and interpreter scans now use the
conservative bound `O((L+M+2)^2)`.

**Verdict.** Resolved; the earlier `T`-only formula was false.

### Attack 2: the random splitter uses work as a random-position bound

A component may consume many random bits relative to its transition
coordinate in a different primitive convention, and in any case the claimed
bound should cite the random envelope rather than work by analogy.

**Resolution.** The paired coordinate now uses
`j<=P_native^rand<=M`.  With node index `i<L`, the consumed master prefix is
strictly below `(L+M+2)^2`.  The Bernoulli cylinder proof is unchanged.

**Verdict.** Resolved without assuming that two distinct ledger coordinates
are equal.

### Attack 3: grade evaluation is free physical initialization

The universal machine must obtain the parameter/workload-dependent virtual
quotas.  Calling their evaluation external bookkeeping while claiming a
complete physical compiler profile omits input reading, integer arithmetic,
and quota-table construction.

**Resolution.** A fixed private evaluator receives meter-only unary tracks
`1^kappa,1^b`, evaluates the fixed finite grade library with ordinary integer
routines, and writes the binary table.  Their length and scanning, as well as
the compiled evaluator work and scratch, are included in the `M`-based
compiler profiles.  The table is never given to a simulated program; it is
used only for meter comparisons, so the non-observability premise remains
intact.

**Verdict.** Resolved at the selected machine layer.  The six finite routine
constants can be made numeric by printing transition tables.

### Eleventh-pass verdict

The generated-to-fixed theorem now pays for both executed simulation and the
representation/evaluation of dormant workload-dependent limits.  Its
polynomial conclusion survives with a larger, explicitly composed profile,
and its behavioral coupling is unchanged.

## Twelfth-pass review - generated-family initialization

### Attack 1: the generated graph is materialized before the run for free

Saying that generation, decoding, and grade evaluation happen “once at
initialization” is not an operational schedule.  If the universal component
begins in a fully decoded state, its generator work and graph storage have
been placed in the initial configuration without a charged transition.

**Resolution.** The fixed universal component starts with one
`initialized=false` bit.  On its first external activation it retains the
already routed input, runs the generator, decoder, and charged evaluator,
sets the bit, and then dispatches the stored input into the virtual graph.
Later activations use the persistent decoded state.  The work is therefore on
an actual trace, and the additive space bound includes the simultaneous input
buffer through the master envelope `M`.

**Verdict.** Resolved for the input-driven single-token semantics.

### Attack 2: lazy initialization changes a system with spontaneous output

A native graph that can emit before any query would be delayed until the first
query and hence would not be behaviorally preserved.

**Resolution.** Such a graph is not in the selected macro carrier: machines
are quiescent until an input activation and a macrostep returns the first
visible output caused by that activation.  A lower model with autonomous
startup must expose an initial token or initialization port and extend both
the native and universal semantics.

**Verdict.** Excluded by an existing carrier premise, now stated where the
compiler uses it.

### Attack 3: the first input is overwritten by the generated code

Running the generator inside the first activation can destroy or silently
duplicate the input that is eventually supplied to the virtual boundary.

**Resolution.** The physical input remains in its ordinary charged buffer
until initialization completes.  Generator, decoded tables, and input occupy
separate sequential-tape regions, and the conservative space profile adds
their envelopes.  The input is then copied through the same bit-costful
virtual boundary routine used on later calls.

**Verdict.** Resolved by the initialization invariant and additive profile.

### Twelfth-pass verdict

The generated presentation is now an actual lifetime program rather than a
family whose parameter-dependent initial state is assumed.  Its first-call
overhead is visible, its persistent state is preserved, and the restriction
to input-driven systems is explicit.

## Thirteenth-pass review - adaptive parallel switching

### Attack 1: conditioning on other realized transcripts is selection-biased

The earlier parallel RF/RP argument conditioned on the complete transcript of
the other instances.  Under a globally adaptive distinguisher, those
transcripts depend on responses from the instance currently being replaced.
They are not independent side randomness, so that conditioning does not by
itself leave an ordinary adaptive single-instance experiment.

**Resolution.** Use one simultaneous product coupling instead.  Independently
couple each random function with its random permutation and run the
distinguisher once.  Before the first disagreement, the complete joint
history is common.  Conditional on that history, the `i`th distinct query to
instance `j` collides with one of its preceding outputs with probability at
most `(i-1)/2^m`, regardless of how the distinguisher chose the instance and
query.  The union bound gives

```text
sum_j q_j(q_j-1)/2^(m+1) <= Q(Q-1)/2^(m+1).
```

No transcript is conditioned on after it has been adaptively selected.

**Verdict.** Resolved; the numerical and profile calculations are unchanged.

### Attack 2: repeated queries are counted as fresh collision trials

A lazy random function and permutation both answer a repeated input with the
stored output, so only distinct inputs create a fresh collision opportunity.

**Resolution.** If `d_j` is the number of distinct queries then the exact
bound uses `d_j(d_j-1)`.  The declared total-call bound satisfies
`d_j<=q_j`, so replacing `d_j` by `q_j` is a conservative upper bound and
continues to fund all repeated-query traffic.

**Verdict.** Resolved without assuming that every call is distinct.

### Thirteenth-pass verdict

The worked parallel reduction now supports arbitrary adaptive interleaving
across fixed independent instances through a direct history-conditional
coupling argument, with no invalid conditioning step.

## Fourteenth-pass review - random-tape instruction coherence

### Attack 1: “read-once” contradicts a non-advancing read

The core machine allowed a transition to inspect the current random bit and
leave the head in place, while calling the tape read-once.  The explicit coin
API then correctly charged repeated inspections of that same cell.  The
terminology described two different machines.

**Resolution.** The native object is now called a *one-way persistent random
tape*.  A transition either makes no inspection or inspects the current bit
and then stays or advances.  Each inspection is charged; repeated stays see
the same bit.  A fresh-bit-only source remains a separate constant-overhead
normal form.

**Verdict.** Resolved by one coherent tape convention.

### Attack 2: the generated transition grammar cannot classify read mode
before seeing the bit

The explicit reservation protocol needs to decide whether a random token is
required before the bit is returned, yet the compiler grammar put the random
bit directly in every source key and used an ambiguous
`{stay,read-and-advance}` action.

**Resolution.** A generated transition key now has an explicit `no-read` or
`read` mode.  A no-read key omits the random bit.  A read key includes it, and
the selected bit branch chooses `stay` or `advance`.  Validation rejects
mixed or incomplete modes for one scanned frame.  Thus use is known before
reservation while head movement may still depend on the bit.

**Verdict.** Resolved; the compiler, native machine, and `COIN` transaction
now implement the same instruction normal form.

### Fourteenth-pass verdict

The probability coupling was never affected, but the syntax-to-resource
refinement now has a single exact random-access convention instead of relying
on incompatible informal readings.

## Fifteenth-pass review - prepared output tariffs

### Attack 1: a strong `STORE` envelope can reject a fitting native step

The bounded-call proof gives every store response the coarse bound
`c_P(S+1)`.  If a commit reserves that amount on every transition, a late
small output can be rejected when less than `S` administrative traffic
remains—even though the actual native output and the paper's affine
`OriginalTraffic` envelope both fit.  This creates an explicit-only
exhaustion branch.

**Resolution.** `update.prepare` installs a private charging view containing
the prepared outcome tag, port class, and exact encoded output length `ell`.
The driver receives only an opaque fixed-size capability.  Before any primary
commit, the external private meter reserves `u_P+v_P*ell` for the commit and
private passage.  The coarse `c_P(S+1)` value remains a proof of bounded
accessibility, not the repeatedly used reservation.

**Verdict.** Resolved; the administrative traffic bound remains affine in
actual original traffic rather than `Steps*S`.

### Attack 2: output tariff failure tears a prepared transaction

Even if processor, coin, and store capacities fit, a later administrative
route could exhaust after primary state starts committing.

**Resolution.** All remaining fixed API and exact payload-passage charges are
reserved after store preparation but before the first primary commit.  In
`E(N)_B` the derived administrative envelope proves this reservation always
fits.  Coin, processor, and store commits and their private deliveries are
then infallible; the final store commit remains the first point at which a
native output can appear.

**Verdict.** Resolved under the encapsulated one-token meter.

### Attack 3: preparing an input duplicates the entire event

Passing `inputEvent` as the prepare query would already copy the payload into
the store before the capacity decision.

**Resolution.** The API is now
`accept.prepare(port,length)`.  It examines only the validated
self-delimiting header while the payload remains in the already charged
routing buffer.  The exact copy cost is reserved from `length`; one copy into
the reserved input region occurs only after both primary activation
reservations fit.

**Verdict.** Resolved.

### Attack 4: the exact prepared length is itself uncharged memory

The charging view is not constant-size when `S` varies with the parameter.

**Resolution.** The administrative peak now includes
`O(log(S+1))` bits for its self-delimiting length encoding, separately from
the fixed phase tag and the one payload buffer.  The complete explicit-state
formula already contains the same logarithmic store/counter term.

**Verdict.** Resolved.

### Fifteenth-pass verdict

The explicit simulation now reserves both primary state changes and every
remaining administrative effect in the only order that preserves failure
atomicity without worst-case overreservation.

## Sixteenth-pass review - uniformity of polynomial hybrids

### Attack 1: a uniform generator does not make pointwise adjacent errors
uniform

Suppose `h(kappa)=kappa` and one fixed generator emits deterministic hybrids

```text
H_i^kappa = 0  if i < kappa,
H_i^kappa = 1  if i >= kappa.
```

For every fixed natural index `i`, the adjacent pair changes at only the one
parameter `kappa=i+1`; its gap is therefore eventually zero and negligible.
Nevertheless `H_0^kappa` and `H_kappa^kappa` differ with advantage one for
every positive parameter.  The generator and every profile are uniform and
polynomial.  What fails is uniformity of the adjacent error over the moving
index.

**Resolution.** A polynomial hybrid theorem now requires one negligible
function `nu(kappa)` that bounds every adjacent gap
`0<=i<h(kappa)` after the stated profile reindexing.  A bounded-auxiliary
theorem over encoded `i` may provide such an envelope, or it may be a direct
concrete bound; pure pointwise statements for each fixed `i` do not.

**Verdict.** Resolved by adding the missing quantifier to the theorem,
dossier, and claim ledger.

### Attack 2: a polynomial profile bound is mistaken for an error bound

One aggregate resource profile ensures all hybrids are efficient but says
nothing about their pairwise statistical or computational distance.

**Resolution.** The theorem lists the polynomial number bound, aggregate
profile, and uniform negligible adjacent envelope as three separate
hypotheses.  Only the last controls the triangle sum; the first two establish
uniform syntax and efficient admissibility.

**Verdict.** Resolved.

### Sixteenth-pass verdict

The polynomial-hybrid clause now has the quantifier strength actually needed
for `h(kappa) nu(kappa)` to remain negligible and rejects the standard moving
bad-index diagonal.

## Seventeenth-pass review - lazy random-function implementation

### Attack 1: a repeated query resamples and ceases to be a function

Sampling an independent `n`-bit answer on every call realizes a random oracle
with fresh responses, not a random function.

**Resolution.** `LazyRF` scans a persistent dictionary.  It samples and
appends only on the first occurrence of an input and returns the unique stored
value thereafter.

**Verdict.** Resolved pathwise for repeats.

### Attack 2: adaptive queries invalidate the fresh-value argument

The next input may be an arbitrary function of all preceding answers, so
unconditional independence of tape blocks is not by itself the right
statement.

**Resolution.** Condition on the complete preceding adaptive transcript.  If
the query is new, an unexposed point of a uniform random function and the next
unused fair-tape block are both conditionally independent uniform `n`-bit
strings.  Induction therefore gives equality of every finite transcript law.

**Verdict.** Resolved without fixing the queries in advance.

### Attack 3: dictionary lookup is treated as constant-time RAM

With `Q` records, a sequential multitape component may scan all `Q` keys on
every call.

**Resolution.** The profile explicitly contains

```text
Q * 4Q(m+1)
```

scan work, plus validation, append, random-bit, and blank-output construction
cost.  Space retains every `(m+n)`-bit record and one active input/output
region.  Boundary query/response traffic is listed separately.

**Verdict.** Resolved for the selected sequential implementation; a RAM
dictionary would need its own lower API.

### Attack 4: the full ideal table is claimed implemented

A uniform function on an exponentially large domain has an exponentially
large extensional table.

**Resolution.** The theorem is explicitly relative to the polynomial lifetime
call envelope `Q`.  It realizes exactly every `Q`-query transcript while
materializing only queried points.  It does not claim to output, store, or
provide random access to the full table.

**Verdict.** Resolved by the operational transcript statement.

### Seventeenth-pass verdict

The two-sort oracle section now contains both sides of the boundary: genuinely
abstract access contracts and one exact, fully charged implementation theorem
when finite response length and a workload envelope make it possible.

## Eighteenth-pass review - program placement and initialization

### Attack 1: the stateless driver hides the complete executable

Writing `Drive_P` and saying that it “injects the program choice” permits an
implementation in which the driver's finite control contains `code(P)`.
That presentation can reproduce every transition while charging no processor
program state.  Calling the driver stateless does not cure the defect:
immutable code is still storage, and a family of such drivers can smuggle
nonuniform executables below the resource ledger.

**Resolution.** The selected resource is now
`PROC[P;T,A,L]`.  Its state contains one canonical immutable `code(P)`
coordinate and the full explicit report charges that coordinate.  `Drive_P`
only routes the fixed reserve/plan/commit protocol.  Its subscript is a typing
annotation for the native ports, not a program image, handle, or selection
message; connection to the already program-indexed processor determines the
executable.  Thus administrative erasure has one charged program copy and no
copy in the converter.

**Verdict.** Resolved by changing the resource signature and the macro
invariant, rather than by an informal accounting sentence.

### Attack 2: “load once” creates a program from nowhere

An initially blank processor cannot become `PROC[P;T,A,L]` unless some
boundary event or resource already supplies `code(P)`.  Moreover a copying
loader may temporarily retain the source and destination simultaneously.
Charging only the final `L` processor bits misses source storage, program
traffic, validation work, scratch, and peak overlap.

**Resolution.** Loading is no longer an equivalent description of the
selected initialized resource.  The separate loaded variant requires a
charged program event or an explicit `IMAGE[P,L]`, an initially blank
processor, an atomic reserve/validate/stream/commit phase, linear work and
traffic, logarithmic scratch, and the source/destination peak.  The initialized
refinement applies only after a valid load whose whole envelope is funded.
An erasing image, ownership-transfer wire, public reload, invalid-code policy,
or load-time leakage changes the resource and requires another theorem.

**Verdict.** Resolved as a scope-separated conditional corollary, not a free
initialization convention.

### Attack 3: a generated family varies the supposedly fixed processor

Even with charged code storage, installing a freshly generated graph as the
processor program at each security parameter would make the processor
functionality and the driver's port schema vary nonuniformly.

**Resolution.** The generated-to-fixed compiler is applied first.  Its one
fixed universal decoder/interpreter is the program index of the explicit
processor.  Generated graph code is charged data in the store, and the
physical processor/store/coin profile is the compiled universal profile.
Only then is the explicit-resource refinement applied.

**Verdict.** Resolved by the existing compilation order, now reflected in the
program-indexed notation.

### Eighteenth-pass verdict

The selected refinement now distinguishes three objects that the previous
wording conflated: an initialized program-indexed processor, a stateless typed
router, and an optional separately sourced and tariffed loader.

## Nineteenth-pass review - representation of the workload index

### Attack 1: a binary workload silently grants value-polynomial time

The generated compiler previously said only that its private evaluator
“receives `(kappa,b)`.”  If `b` is supplied in binary while the compiler is
allowed polynomial work in its numeric value, an exponentially long
computation relative to the administrative input length can be hidden in the
initial quota calculation.  Worse, treating `(kappa,b)` as metalevel naturals
can make conversion to the virtual quota table completely free.

**Resolution.** The physical compiler now receives two meter-only read-only
tracks `1^kappa` and `1^b`.  Their combined length, heads, full scans, and
retention are bounded by `M=1+kappa+b+sum_x P_native^x(kappa,b)` and hence by
the displayed evaluator work and space terms.  The evaluator uses charged
ordinary integer routines to construct binary quotas.  The generator sees
only `1^kappa`; decoded programs see neither the workload track nor quota
table.

For every fixed efficient context, `b=p(kappa+|a|)` and the relevant auxiliary
input bound are polynomial, so the unary administrative representation
preserves the intended asymptotic class.  It also makes explicit that this
physical compiler theorem is stronger than the baseline abstract convention
where evaluated grades are external bookkeeping.

**Verdict.** Resolved by fixing the representation and charging the existing
`M` envelope, without changing the virtual behavior.

### Nineteenth-pass verdict

The compiler no longer relies on an unspecified numeric input convention at
the exact point where representation length controls computational meaning.

## Twentieth-pass review - auxiliary-input and workload quantifiers

### Attack 1: the central advantage drops the input from the workload

The ambient policy is defined earlier as
`b_D(kappa,a)=p_D(kappa+|a|)`, but the indistinguishability equation later
used only `p_D(kappa)` and did not carry `a` in the experiment.  In pure mode
one could absorb the output length of a fixed input generator into another
polynomial, so the asymptotic class might survive.  That repair is unavailable
as an exact definition and obscures the bounded-auxiliary mode, where the
worst input varies with the parameter.

**Resolution.** The primitive advantage now has all indices

```text
Adv(D,b;kappa,a;R,S).
```

For a declared mode `M`, the paper defines an allowed set
`A_(D,M)(kappa)` and takes

```text
sup_{a in A_(D,M)(kappa)}
  Adv(D,p_D(kappa+|a|);kappa,a;R,S).
```

The set is a singleton produced by one fixed generator in pure mode, the
entire polynomial-length input ball in bounded auxiliary-input mode, and the
named input/advice singleton in explicit nonuniform mode.  The negligible
envelope is outside this supremum but inside quantification over each fixed
`D,p_D`.  The efficient-construction witness now cites the same
mode-indexed advantage.

**Verdict.** Resolved by one exact definition shared by security, reductions,
and the witness package.

### Attack 2: the claims ledger confuses workload with a test profile

Profile-reindexed nonexpansion transforms the aggregate test profile, not the
ambient workload index itself.  Writing
`Delta_b <= Delta_(T_alpha(b))` incorrectly suggests that absorption changes
the resource family's workload parameter.

**Resolution.** The claim is now written
`d_P(alpha R,alpha S) <= d_(T_alpha(P))(R,S)`.  The normalized closed graph
uses the same `(kappa,b)` on both sides; only its certified work/space/traffic/
oracle/report envelope grows.

**Verdict.** Resolved and aligned with the pathwise absorption theorem.

### Twentieth-pass verdict

The computational relation now has a single auditable order of quantifiers
over code, policy, allowed input, randomness, and negligible envelope.

## Twenty-first-pass review - effective terminal observations

### Attack 1: the test hides a noncomputable predicate in `o`

The pointwise terminal law contains a designated finite observation `o` of
the closing context's own state.  The computational section charged the
public-ledger report projection and terminal scorer, but did not separately
require the map from the context's terminal configuration to `o` to be
effective.  A test could therefore declare

```text
o = 1  iff its finite terminal tape encodes a member of a nonrecursive set
```

and let a constant-time scorer return `o`.  Charging the scorer would not
remove the hidden noncomputable advice.

**Resolution.** In the computational class, both the context-state projection
and public-ledger projection are fixed uniform effective codes, or canonical
encodings of explicitly declared accessible coordinates.  Their output
length, work, and space, the self-delimiting record construction, scorer input
reading, and scorer execution all belong to the test profile.  An absorbed
converter's additional report coordinates therefore enlarge the certified
record rather than appearing for free.

The unrestricted pointwise quotient still permits arbitrary measurable
terminal maps, where their purpose is to identify complete outcome laws.
That semantic observer is no longer conflated with an efficient
distinguisher.

**Verdict.** Resolved by charging the entire observation pipeline, not just
its final Boolean program.

### Twenty-first-pass verdict

Every transformation between the finite terminal state and a computational
decision is now effective, uniform, and profile-bounded.

## Twenty-second-pass review - exact output length is not free

### Attack 1: `STORE.update.prepare` scans the whole store on every step

The exact prepared output length is needed before processor/coin/store commit
so that a late small output is not rejected by a worst-case `S` reservation.
But simply asserting that `STORE` exposes this length hides a computation.
For an arbitrary sparse output tape, finding the final encoded cell can cost
`Theta(S)`; repeating that on every transition would change the claimed
affine administrative bound into `Theta(S*Steps)`.

**Resolution.** The selected native normal form now makes the output register
a blank-on-activation contiguous self-delimiting buffer.  A machine using an
arbitrary sparse output tape must first execute a charged normalization copy,
and the refinement applies to that transformed ledger.  `update.prepare`
performs no output scan for internal or block commands.  On `Emit` only, after
the tentative constant-local update and footprint check, a private read-only
access procedure scans the prepared code to its guaranteed terminator.  It
does not copy or commit the payload.

The scan pays

```text
u_len + v_len (ell+1)  work,
O(log(S+1))            scratch
```

and places only the binary `ell` in the meter-readable charging view.  Its
linear work is absorbed by the already present `OriginalTraffic` term; the
eventual private passage pays another declared linear term.  The derived
administrative envelope funds the scan before any primary commit, so it
cannot introduce a new failure branch.

**Verdict.** Resolved without worst-case reservation and without a hidden
random-access length primitive.

### Twenty-second-pass verdict

The exact prepared tariff is now operationally obtainable at a cost
proportional to the output that is actually emitted, not to every possible
store cell on every transition.

## Twenty-third-pass review - complete counter representation

### Attack 1: the “full” state bound serializes only four counters

The explicit resource formula displayed logarithmic storage for native
transition, activation, random-read, and logical-space bounds.  The actual
translation also has private administrative work/traffic reservations,
capability counters, and retained outer traffic/oracle meters.  Calling the
four-logarithm expression a complete explicit-state report either drops these
coordinates or counts them nowhere.

**Resolution.** For fixed program `P`, let `K_P` be the finite coordinate set
owned by the processor/store/coin bundle and private access meter, and extend
the native budget by its derived administrative envelope.  The complete new
counter term is

```text
CtrBits_P(B_exp)
  = sum_{x in K_P} ceil(log_2(B_exp[x]+1)).
```

Recording both used and remaining values changes only a fixed factor.  The
full bound is now

```text
L + CtrBits_P(B_exp)
  + O((S+H_P) log(T+S+2))
  + fixed scratch + MaxEvent.
```

Original-edge and named-specification meters deliberately left outside the
bundle remain serialized once by the surrounding graph; the translation
neither drops nor duplicates them.  Since `K_P` is fixed and every extended
grade coordinate is polynomial, the corrected counter term preserves
polynomial closure.

**Verdict.** Resolved by quantifying over the complete fixed meter vector
rather than naming a suggestive subset.

### Twenty-third-pass verdict

The representation theorem now covers every stateful counter introduced or
retained by the selected explicit refinement.

## Twenty-fourth-pass review - almost-sure versus strong support

### Attack 1: positive response support ignores hidden null successors

The machine-only implication from almost-sure to strong no-exhaustion is a
finite-cylinder argument: every finite fair-bit prefix has positive
probability.  Extending it by requiring positive probability for every
response/public-update value is not enough.  An oracle may return the same
public value on every seed, install a bad hidden successor only at `u=0`, and
make the next call exhaust from that state.  The response alphabet is a
full-support singleton, yet the bad raw sample is nonempty and null.
A continuous initial-state law has the same problem before the first call.

**Resolution.** The sufficient hypothesis is now a positive-branch
presentation for both initialization and every oracle step.  At each
reachable complete history there is a countable measurable branch label
which:

1. determines all successor information relevant to later finite operational
   behavior, not merely the visible response and public contract coordinate;
2. has strictly positive conditional probability for every label in the
   selected reachable sampler range.

A finite exhaustion run fixes finitely many fair bits and branch labels.
Iterated conditioning gives that witness positive probability, contradicting
almost-sure no-exhaustion.  Without this premise the hidden-`u=0` example is
almost-sure no-exhausting but not strong, and it remains a counterexample even
with a singleton response alphabet.

**Verdict.** Resolved at the exact behavioral equivalence-class level needed
by the cylinder proof.

### Twenty-fourth-pass verdict

The strength upgrade now accounts for hidden successor state and random
initial state, rather than confusing public full support with operational
full support.

## Twenty-fifth-pass review - effective expected-cost separator

### Attack 1: the counterexample assumes a primitive `1/kappa` coin

The claim “run for `kappa^3` steps with probability `1/kappa`” establishes the
probabilistic arithmetic but not a fixed fair-bit machine.  Exact Bernoulli
`1/kappa` sampling for arbitrary `kappa` is not one bounded finite-bit
primitive, and a rejection sampler would itself introduce a runtime tail.

**Resolution.** The separator now sets
`m=ceil(log_2(kappa))`, reads exactly `m` fair bits, and takes the long branch
iff all are zero.  Thus

```text
1/(2*kappa) <= 2^(-m) <= 1/kappa.
```

The program is fixed and uniform.  Its expected work is at most
`kappa^2+O(log kappa)`, while a corresponding quadratic meter exhausts on the
`kappa^3` branch with probability at least `1/(2*kappa)`, which is
nonnegligible.

**Verdict.** Resolved with an explicit finite fair-bit sampler.

### Twenty-fifth-pass verdict

The expected-cost separation no longer relies on an undeclared rational-coin
oracle or an unaccounted rejection loop.

## Twenty-sixth-pass review - exact MR11 compatibility

### Attack 1: “parallel specification absorption” is weaker than MR11 closure

The draft proved converter absorption and observed that the same idea applies
to a named ideal oracle.  MR11 Definition 16 is stronger: for the restricted
feasible algebra, `D^f[. || Phi^f]` must be contained in `D^f`.  The absorbed
parallel resource may contain an arbitrary feasible implementation graph,
several specification occurrences, or both.  Proving only the one-oracle case
does not instantiate that clause.

**Resolution.** The exact theorem now has two explicit cases.  For every
feasible resource graph `S`, `D[. || S]` is obtained by retaining the complete
graph of `S` around the remaining challenge boundary.  At every fixed
parameter, workload, machine tape, initial specification state, and oracle
seed sequence, `D(R || S)` and `D[. || S](R)` normalize to the same graph and
have the same labeled run.  Its transformer `T_S` charges every implementation
node, router, meter, terminal-record operation, and specification call in
`S`.  Polynomial substitution then proves membership in the feasible test
class.

### Attack 2: absorption can silently clone or grant an oracle

If the resource and test classes are described only as using “named
dependencies,” absorbing `S` could be read as giving the test a new oracle
primitive or as sampling a fresh copy of `S`'s hidden state.  Either reading
destroys the claimed pathwise identity.  It also makes the computational
relation depend on an undeclared change of model.

**Resolution.** All three feasible classes are now relative to one fixed
finite dependency signature `Gamma`.  A package fixes its interface,
initialization, kernel, codecs, public coordinate, tariff/reservation
evaluators, profiles, and independence convention.  Parallel composition
alpha-renames occurrences apart once; absorption retains exactly those
occurrence identities, initial states, and seed coordinates.  Tests are
finite feasible networks, not only terminal scorer programs.  Enlarging
`Gamma` is explicitly a change of computational model.  A
parameter-dependent family of independent occurrences requires one declared
indexed product-state package and cannot be emitted by the implementation
compiler.

### Twenty-sixth-pass verdict

The lower theorem now discharges the universal converter- and
parallel-resource-emulation clauses of MR11 Definitions 14, 16, and 17
relative to an explicit dependency signature; it no longer infers them from a
single ideal-oracle example.

## Twenty-seventh-pass review - MR16 attribution boundary

### Attack 1: a source analogy is stated as a proved processor theorem

The draft said that reifying simulator computation as an assumed processor
resource was “precisely” the resolution proposed in MR16 Section 4.3. The
source proves no such processor decomposition. Conditional on choosing its
model 3, it replaces a computational behavior `beta` by a parallel resource
`beta_bar` having that behavior and a trivial connecting converter. It also
does not require this resource presentation whenever concrete reduction cost
matters; carrying an explicit concrete loss is another legitimate level.

**Resolution.** The source-supported statement and the new result are now
separated. MR16 supplies the modeling option and the abstract
`[S,beta_bar] sigma` refactoring. This manuscript supplies the selected Turing
processor/store/coin API, the transactional simulation, and the pathwise proof
that its routed bundle realizes the former machine behavior. The
free-efficient alternative retains the simulator's full polynomial profile as
concrete reduction loss.

### Twenty-seventh-pass verdict

The paper no longer cites MR16 as if it had already proved the selected lower
resource implementation.

## Twenty-eighth-pass review - specification-uniform negligibility

### Attack 1: pointwise efficient members do not give a uniform specification

The algebra theorem absorbed each fixed feasible resource into a feasible
test. It then spoke as though the same fact automatically lifted to an
arbitrary specification (a set of efficient resource families). Jost's exact
parallel relaxation instead contains

```text
epsilon^S(D) = sup_{S in S} epsilon(D[. || S]).
```

The supremum precedes the negligibility conclusion. For every fixed `n`,
`eta_n(kappa)=1[kappa=n]` is negligible and a fixed uniform program can
recognize its hard-coded exceptional parameter. Nevertheless
`sup_n eta_n(kappa)=1` for all `kappa`. The memberwise statement therefore
cannot justify the specification-level one.

**Resolution.** The paper now distinguishes the elementwise feasible algebra
from its specification lifting. A uniform specification certificate supplies
one selector/compiler or indexed ideal package, a polynomial descriptor
bound, one aggregate profile, the fixed dependency signature, and a
negligible envelope after taking the descriptor supremum in the selected
input mode. A concrete bound uniform in that aggregate profile also suffices.
For a fixed finite specification, a finite maximum is controlled by the sum of
the memberwise negligible functions.

### Twenty-eighth-pass verdict

Parallel and sequential construction over specifications now state the
uniform quantifier required by the source theorem and reject the moving
bad-member diagonal.

## Twenty-ninth-pass review - simultaneous peak space

### Attack 1: local maxima do not determine the global maximum

The exact ledger stored one local `peak_v` per occurrence and later claimed
to derive

```text
max_t sum_v live_v(t).
```

This is false. Two components may attain their individual maxima at disjoint
times, so summing local peaks overestimates the true simultaneous maximum;
neither the sum nor any function of the local peaks alone recovers the exact
global trace statistic.

**Resolution.** The primitive ledger now has a separate scalar `gpeak`,
updated by the external accountant at every intermediate and committed
small-step configuration, including occupied canonical-routing buffers.
Local peaks remain for per-occurrence capacity and grades; `gpeak` is the
exact global space report. It is alpha-invariant because renaming only
permutes live-state summands.

The explicit-resource projection now distinguishes native and physical global
peaks. The native projection updates only at related transaction boundaries
and original routing states. The full physical `gpeak` also includes program
storage, counters, prepared store state, transaction scratch, and
administrative messages while they coexist.

### Twenty-ninth-pass verdict

The exact ledger no longer manufactures a simultaneous memory statistic from
insufficient per-component data, and the explicit refinement retains rather
than erases its additional physical peak.

## Thirtieth-pass review - stabilization under pre-reservation

### Attack 1: final exact charge need not fund admission

The draft claimed that every budget above the terminal exact ledger reproduces
a finite successful unmetered run. This is correct for ordinary machine
charges, whose prospective cumulative/peak values are bounded by the final
ledger. It is false for the oracle rule the paper later adopts. An oracle may
publicly reserve ten response units before sampling, commit an answer costing
one unit, and release nine. A budget equal to the final exact charge rejects
before the seed is read and does not reproduce the success.

**Resolution.** For a fixed-sample finite trace `rho`, define `Need(rho)` as
the coordinatewise maximum of every absolute vector that a meter would test
on that trace: prospective primitive ledgers, current cost plus public oracle
reservation, and declared atomic transaction reservations. Stabilization now
requires `B >= Need(rho)`. The final exact ledger is included, so
`Cost(rho) <= Need(rho)`. Equality is recovered in the machine-only or
exact-reservation case.

Budget monotonicity was also repaired: its induction uses the fact that every
prospective check vector accepted under `B` is accepted under `B'`, not merely
that committed prefix ledgers are ordered.

### Thirtieth-pass verdict

The metered/unmetered relation now respects the deliberate gap between a
strong public admission envelope and a smaller realized oracle charge.

## Thirty-first-pass review - unary parameter storage

### Attack 1: every component receives a parameter tape that no ledger owns

Uniformity gave each component a read-only `1^kappa` tape, while the live-space
description named only work, current input, output, and router buffers. If the
parameter copies are omitted, a generated graph can acquire polynomially many
length-`kappa` tapes as free storage. If they are physically shared instead,
that is a different multi-reader resource and requires an access convention.
The explicit `STORE` definition likewise omitted the track and its head.

**Resolution.** Each component's logical unary parameter track is now part of
its initial native live state. Its occupied cells and head contribute to
`peak_v`, `gpeak`, and the component grade, and reading it consumes ordinary
transitions. `STORE` owns the immutable parameter/auxiliary tracks in the
explicit refinement. The standard asymptotic experiment still supplies the
initial input before the first protocol activation; charging its physical
distribution requires a separately declared source or bus.

For generated graphs, the exact virtual ledger charges one logical track per
decoded component. The universal interpreter may physically share their
identical immutable contents while retaining separate virtual heads, because
physical ledger equality was never claimed. Its aggregate native space
certificate and normalized magnitude include all logical tracks.

### Thirty-first-pass verdict

Unary representation now constrains both time and storage; the compiler and
explicit-resource theorem no longer rely on unowned parameter tapes.

## Thirty-second-pass review - pure-input generator cost

### Attack 1: fixed and uniform does not mean polynomially bounded

The pure-uniform test mode selected the singleton input
`G_D(1^kappa)` but required only a fixed uniform generator. A fixed Turing
machine can take exponential time or emit an exponentially long string.
Because the ambient workload is then
`p_D(kappa+|G_D(1^kappa)|)`, this omission can make every component budget
exponential while the definition still labels the context uniform.

**Resolution.** `G_D` is now a fixed deterministic *graded* generator with
polynomial work, space, and output-length bounds in `kappa`; it receives no
ambient workload. Its execution, retained output, and installation as test
input belong to the initialization profile. Bounded auxiliary input instead
uses the declared polynomial `q_D`, and explicit nonuniform input/advice
carries one named combined-length polynomial. Supplying auxiliary data does
not charge a generator, but its storage, validation, delivery, and processing
remain charged.

### Thirty-second-pass verdict

All three input modes now constrain the size entering the workload policy and
account for how that size reaches the test.

## Thirty-third-pass review - generated compiler boundary staging

### Attack 1: the native profile cannot bound an adversarial first input

The generated-to-fixed proof said that the universal component retains the
first input while generating/decoding and that `M`, derived from the decoded
native profile, dominates this buffer. A context can deliberately send an
input larger than every native receiver quota. The decoded graph then rejects
at its virtual activation, but the universal component may exhaust merely
trying to retain the input before it knows the target. Its owner/status and
cost projection can differ. The challenged resource's profile cannot be used
to bound arbitrary context output.

**Resolution.** The fixed compiled boundary now has a staging face. In a
route-safe closure it uses the final whole-graph routing envelope, which
includes the context's produced event; otherwise an external-event envelope
must be supplied. The payload remains staged while generator, decoder, and
grade evaluation run. Its header suffices to compute the exact prospective
virtual activation charge. On rejection it is never installed and the virtual
target owner/status is returned. On admission, its length is bounded by the
native aggregate space coordinate in `M` and one charged copy installs it.

The theorem's displayed component profile is now explicitly supplemented by
the ordinary staging/routing profile. It no longer claims equivalence in an
unbounded, underfunded physical closure.

### Thirty-third-pass verdict

The lazy compiler handles precisely the oversized-input branch that native
metering is meant to expose, without charging context storage to the
challenged implementation.

## Thirty-fourth-pass review - alpha-invariant cost reports

### Attack 1: raw ledger names destroy the quotient

The ledger is indexed by component, edge, tape, and oracle occurrence names.
If a cost-aware supervisor receives that raw named tuple, it can decide by
testing whether an internal component has a particular fresh identifier.
Alpha-isomorphic graph presentations then have different observations, so
renaming is not well defined and converter connection-order invariance fails.

**Resolution.** The main paper now fixes a measurable report map satisfying

```text
Rep_(phi N)(phi_* ell) = Rep_N(ell)
```

for every internal alpha-isomorphism. Declared public party, interface,
oracle, and owner labels may remain; fresh internal names may not. At the
pointwise layer a maximal report is the alpha-orbit of the finite graph/ledger
pair. At the computational layer, the report projection must be fixed,
effective, output-length bounded, and charged; no potentially expensive
canonization is supplied for free.

### Thirty-fourth-pass verdict

The cost-aware contextual equivalence now has the name invariance required for
its claimed system algebra.

## Thirty-fifth-pass review - selected versus whole-experiment reification

### Attack 1: translating only protocol code is called an explicit-computation
model

Replacing `pi` and `sigma` by processor/store/coin bundles still leaves the
distinguisher interaction, pure-input generation, terminal projections,
record construction, and scoring as computational converters. That is a
valid mixed model, but not the “all computation is supplied as resources”
choice described in MR16. Conversely, simply calling the semantic terminal
observer a machine would turn lower `Block`/`Exhaust` into wire messages and
change the behavior.

**Resolution.** A whole-experiment proposition now compiles every *effective
code* in one fixed closed test harness into native occurrences and applies the
local explicit refinement to all of them. This includes input generation,
interaction, projections, record building, and scoring; nonuniform mode uses
one fixed universal evaluator with a named polynomial-length description.
The semantic supervisor only freezes the lower terminal record and activates
postprocessing; it does not inject a timeout response. Pathwise decision
equality and the native cost projection compose finitely.

The proposition also states the remaining primitive boundary. Maximal-run
detection, meter/reservation operations, and routing semantics are not yet
gate-level resources. Identical test-owned bundles must be present on both
sides, and changing which party receives a computer changes the resource
specification.

### Thirty-fifth-pass verdict

The paper now distinguishes a fully reified closed computational experiment
at the selected API from partial actor reification and from a still lower
physical implementation.

## Thirty-sixth-pass review - adaptive availability probability and credit

### Attack 1: a bad activation can manufacture more activation slots

The acyclic probabilistic arguments bounded failure by `sum_v N_v delta_v`.
But the deterministic recurrence for `N_v` is valid only while the local
call-count contracts hold. Once a component violates its contract it may
create arbitrarily many later calls, so a union bound over *all* actual
activations would be circular.

**Resolution.** The event is decomposed by the first failed local
certificate. Before that slot every earlier certificate holds, so the
deterministic forward recurrence bounds all candidate first-failure slots.
The local failure estimate is conditional on every complete certified prefix.
Summing those stopped conditional events proves the bound without
independence and without making any assertion about post-failure behavior,
which remains bounded by the external meters.

### Attack 2: the response-adaptive failure polynomial has no arguments

The response-adaptive theorem referred informally to the elementary
probabilistic premise even though local difficulty may depend on the current
cumulative child-response length. This left unclear what negligible function
was actually summed.

**Resolution.** The adaptive certificate now contains
`delta_v(kappa,b,n,z)`, uniform over every certified history with cumulative
response length at most `z`. The final error is explicitly

```text
sum_v N_v * delta_v(kappa,b,L_v,Z_v(kappa,b,L_v)).
```

The first-crossing size proof and first-failure probability proof are separate
stopping arguments.

### Attack 3: affine credit bounds only work and hides a free counter

A work inequality alone does not establish a polynomial ledger. Message
traffic, persistent state, active transient space, coins, and oracle calls
could be omitted. Moreover, calling credit “administrative” could be read as
granting a physically maintained counter at no cost.

**Resolution.** The theorem now states the message, cumulative-coordinate,
and simultaneous-space envelopes. It also distinguishes ghost credit, proved
from ordinary state and requiring no representation, from an implemented
counter, whose encoding, head, update work, and transmitted fields are
charged. The probabilistic credit theorem uses the same first-failure stopping
argument over at most `C_0+1` certified slots.

### Thirty-sixth-pass verdict

The availability rules now justify their adaptive probability estimates and
all advertised ledger coordinates without relying on post-failure behavior or
free administrative state.

## Thirty-seventh-pass review - explicit network-wide physical space

### Attack 1: local physical peaks do not prove a global simultaneous bound

The explicit refinement correctly preserved the native `gpeak` and listed
program, counter, sparse-store, scratch, and event terms for one translated
bundle. But “polynomial profiles add” did not itself display a pointwise bound
on the full physical simultaneous state of a network. In particular,
persistent programs and stores of inactive occurrences coexist, while an
active transaction and router buffer are live.

**Resolution.** For a fixed closed route-safe graph, the paper now sums the
persistent program/counter/store envelope of every translated occurrence,
adds a conservative copy of the final event envelope per bundle, and adds the
fixed router/staging/shared-meter state. This intentionally overcounts the
unique live token and message, but bounds every physical configuration and is
a fixed finite sum of polynomial profiles. The exact physical `gpeak` remains
the configuration maximum; the displayed sum is its funding certificate, not
an attempted reconstruction from local maxima.

### Attack 2: a challenged component cannot fund a hostile boundary message

Using the translated implementation's own `S_v` or `MaxEvent` to bound an
arbitrarily long first input would repeat the generated-compiler staging
error.

**Resolution.** The network-wide formula is explicitly relative to the final
closed route-safe routing envelope or a separately declared staging envelope.
An open component obtains no theorem that its own grade bounds hostile context
output.

### Thirty-seventh-pass verdict

The explicit refinement now has a concrete polynomial bound on its full
network-wide physical peak, with the same staging discipline as the generated
compiler.

## Thirty-eighth-pass review - oracle evaluator atomicity

### Attack 1: charging a post-sample evaluator is not enough

The oracle contract required effective reservation and charge evaluators and
said their work was charged. But the semantic reservation dominated only the
oracle tariff. If the response-dependent charge evaluator ran after sampling
and exhausted its owner, admission would again depend on a fresh response (or
leave ambiguous whether sampled hidden state and seed index were committed).
This is precisely the branch that pre-sample reservation was meant to remove.

**Resolution.** Oracle admission now has two administrative capabilities.
`EvalReserve_O` is checked before the deterministic total reserve evaluator
runs. Its computed semantic reservation is then checked jointly with
`PostReserve_O`, which dominates charge evaluation, record construction,
transient space, and commit bookkeeping for every compatible outcome. Only
after both fit is the seed consumed. The post-sample evaluator is total and
already funded; its actual trace is committed to the exact ledger and unused
capacity is released.

### Attack 2: peak space cannot be “added” to a reservation vector

Speaking only of summing semantic and evaluator reservations risks treating
peak coordinates like cumulative work.

**Resolution.** The combined prospective check explicitly uses the ledger
operation for each coordinate: cumulative coordinates add and peak
coordinates take the prospective simultaneous maximum. The funding
requirement `Need(rho)` now ranges over reserve-evaluator capabilities and
combined semantic/post-sample checks.

### Attack 3: reserve evaluation itself may fail after doing hidden work

If the reserve evaluator is merely run and metered, it can exhaust partway
through. This does not bias an oracle sample if no seed has been read, but it
leaves the advertised atomic API and stabilization high-water vector
underspecified.

**Resolution.** The evaluator is a fixed total code with a declared public
envelope. That envelope is checked first; rejection touches neither evaluator
nor oracle. On admission the exact evaluator work is charged and the unused
capability is released. Efficient accessibility now includes both evaluator
envelopes.

### Thirty-eighth-pass verdict

The bounded oracle API no longer hides a post-sample computational failure
inside a semantic “atomic call.” Kernel preservation and budget monotonicity
cover the evaluators as well as the tariff.

## Thirty-ninth-pass review - generated compiler with stateful oracle tariffs

### Attack 1: the interpreter cannot infer a meter-only charge from a reply

The generated compiler claimed to preserve the exact virtual native ledger
while fixed specification oracles remained external. But the oracle contract
allows the exact charge to depend on the next public contract coordinate,
which is supplied to the access accountant and need not occur on the ordinary
reply wire. An ordinary universal machine therefore cannot reconstruct that
charge or update the virtual remaining budget. Giving it the coordinate on an
ordinary wire would expose a cost/state side channel absent from the decoded
program.

**Resolution.** Each fixed named oracle dependency now has one fixed private
`OracleProxy` face. It reproduces the virtual pre-sample reservation decision,
makes one unchanged physical call only on virtual admission, receives the
accountant's authenticated commit receipt, and mirrors the exact charge and
next public coordinate into the interpreter's private virtual ledger. Decoded
code sees only the ordinary reply. Receipt codec, validation, traffic, work,
and transient state are charged. The proxy is not a generated oracle
occurrence.

### Attack 2: aggregate machine work does not count every simulated action

The interpreter work formula multiplied a per-step scan bound by native
machine/router work `T`. Receiver activations and admitted oracle transactions
are separate primitive actions and may require administrative simulation even
though they do not increment that coordinate. The text also contained a
garbled sentence calling `T` an upper bound on the entire trace.

**Resolution.** The compiler now uses

```text
H = 1 + W + A + Q,
```

where `W` is aggregate component/router work, `A` aggregate activations, and
`Q` aggregate named-oracle calls. `H` bounds primitive action slots and the
final check, while the normalized magnitude `M` includes every coordinate in
the fixed dependency signature. Interpreter work is
`8192 c_int H(L+M+2)^2`; the simulation invariant includes specification
public coordinates and oracle access state.

### Attack 3: physical oracle access can fail after virtual admission

Even if the proxy makes the correct virtual decision, an underfunded physical
access meter could add an extra compiler-owned exhaustion branch.

**Resolution.** The admitted aggregate certificate includes every fixed
dependency's semantic tariff, evaluator, receipt, and access envelope. The
physical proxy is funded for all virtually admitted calls. The theorem is
explicitly relative to this fixed oracle-accounting API; another oracle API
needs a new compiler theorem or a tariff determined by ordinary replies.

### Thirty-ninth-pass verdict

The oracle-relative generated compiler now has enough private information and
enough charged action slots to preserve the exact virtual ledger without
changing program-visible behavior.

## Fortieth-pass review - canonical router versus sequential link

### Attack 1: failure ledgers disagree if one copy is atomic

`SLINK` checked an entire message's traffic, work, and buffer capacity before
copying and rejected without delivery. The canonical router was described as
a bit-costful sequence of charged transitions. Read literally, an
underfunded canonical router could copy a prefix and then exhaust with a
partial work/traffic ledger, whereas `SLINK` would reject before committing
anything. The claimed exact-ledger edge refinement would then be false on
failure branches.

**Resolution.** The primitive routing convention is now explicit and shared.
From the validated self-delimiting header, both canonical router and `SLINK`
first reserve the whole message's copy-work, edge-traffic, and
destination-buffer envelope. Rejection commits no routing coordinate or
destination buffer. Admission grants a linear capability; both then execute
the same infallible bit-costful small-step copy, recording identical
transitions, traffic, intermediate buffers, and simultaneous `gpeak`, before
receiver delivery.

### Attack 2: atomic admission must not make copying unit-cost

Repairing failure equality by calling the entire routing action atomic could
erase the very bit-level cost the model was introduced to retain.

**Resolution.** Only the capacity decision is atomic. The admitted copy
remains an ordinary deterministic sequence of charged routing transitions,
and `gpeak` is updated at every intermediate configuration. The reservation
merely proves those already-priced steps cannot later fail.

### Fortieth-pass verdict

The communication refinement now agrees with canonical routing on rejection,
success, exact cost, and intermediate physical space, without turning message
movement into a unit-cost primitive.

## Forty-first-pass review - cross-file theorem propagation and source title

### Attack 1: the worked compiler example still uses the superseded loop count

After replacing the compiler's machine-work-only factor by
`H=1+W+A+Q`, the Flip-chain example still substituted `T+1=9q-4`.
Its `q` receiver activations are separately charged actions, so that value no
longer instantiated the theorem stated immediately above it.

**Resolution.** The example now computes

```text
H = 1 + (9q-5) + q + 0 = 10q-4
```

and substitutes that factor in both the paper and the complete calculation
sheet. The deliberately loose normalized magnitude still dominates it.

### Attack 2: the source audit gives Jost's thesis the wrong title

One audit row cited the correct theorem/definition numbers and printed pages
but called the source *Constructive Cryptography and Applications*. The local
primary PDF and its metadata identify it as *On Generalizations of Composable
Security*.

**Resolution.** The title is corrected. The text of Theorem 2.2.11 and
Definitions 2.2.14--2.2.15 was re-extracted from the primary PDF and confirms
the protocol/parallel relaxation and uniform-PPT/negligibility claims used in
the manuscript.

### Forty-first-pass verdict

The compiler example now literally instantiates the current theorem, and the
uniform-specification source trail names the checked primary document.

## Forty-second-pass review - generated example parameter storage

### Attack 1: the Flip chain gets `q` unary parameters for free

The compiler theorem now correctly charges one logical `1^kappa` track and
head for every decoded component. Its worked Flip chain nevertheless retained
the old bound `NativeSpace=2q`, accounting only for control/output cells. For
`q=kappa^2+kappa+1`, the omitted logical parameter state is
`Theta(q*kappa)`, so the example's normalized magnitude
`M_F=kappa+16q+16` did not dominate its own native space certificate.

**Resolution.** The native bound is now

```text
NativeSpace = q*(kappa+3),
```

covering the unary track, parameter head, control/state, and a conservative
output cell per node. The universal implementation may share immutable
contents physically, but the exact virtual ledger retains all logical copies.
The corrected normalized magnitude is

```text
M_F = kappa + q*(kappa+16) + 16,
```

which dominates the full displayed aggregate.

### Forty-second-pass verdict

The complete generated-family calculation now pays for the logical
initialization convention used by the theorem it illustrates.

## Forty-third-pass review - uniform parameter storage across examples

### Attack 1: absorbed converters silently lose their unary tracks

The primary uniform convention charges every component's retained
`1^kappa` cells and parameter head. The persistent-mask converter transformer
nevertheless added only four protocol cells, and the tagged/truncated
RF/RP wrapper transformer added only the old `4m+8` protocol scratch. These
profiles could not be literal instances of the declared space convention.

**Resolution.** The mask transformer now adds `kappa+4`: one unary track,
one head, and the converter protocol cells. The RF/RP calculation has two
wrapper occurrences in the absorbed graph and now adds
`4m+2*kappa+10`. The base mask ledger with peak four remains explicitly a
fixed unparameterized calculation; its uniform version has peak
`2*kappa+6`.

### Attack 2: implementation examples name length work but not parameter space

`LazyRF` received `1^kappa` and evaluated the length functions
`m(kappa),n(kappa)`, but `LenEval` and `LenSpace` were not defined tightly
enough to show that the retained asymptotic input was funded. Similarly, the
geometric-streaming formula did not say whether its reassembler track was
inside the symbolic space constants.

**Resolution.** `LenEval` now pays the fixed length evaluators and validators;
`LenSpace` includes their simultaneous scratch, the retained unary track, and
its head. For `GeoBits`, the fixed `beta_i` are selected so the `cQ` term
covers the reassembler track because `cQ=2*kappa*Q` for `Q>=1`. The
unbounded sampled suffix remains specification state and is not mislabeled as
polynomial implementation memory.

### Attack 3: the graph generator itself receives a parameter

Correcting the `q` decoded nodes does not by itself pay for `G_flip`'s own
unary input. Its displayed `GenSpace` needed an explicit domination argument.

**Resolution.** The generator discussion now records that
`q=kappa^2+kappa+1 >= kappa`, so the existing `16(q+1)` scratch term covers
the generator's logical parameter track and head in addition to its counters;
the separate `L_flip` term retains the entire generated code.

### Forty-third-pass verdict

Every exact worked profile now states where the uniform parameter cells live,
while preserving the paper's separate fixed unparameterized base ledger.

## Forty-fourth-pass review - prepared output funding

### Attack 1: exact length is learned only after doing response-sized work

The store scanned a prepared `Emit` buffer to obtain the exact length and only
then reserved the remaining administrative tariff. If the scan itself met an
exhausted private meter, the explicit system would acquire a failure branch
after processor/coin/store capacities had all fit. This is the same
pre-funding problem that arises for a response-dependent oracle charge
evaluator.

### Attack 2: committed traffic does not bound a rejected output

The affine overhead proof assigned the scan and private outgoing passage to
`OriginalTraffic`. But the prepared store must expose the native output before
the unchanged downstream router performs its whole-message admission. If that
router rejects, the output may be long while committed original traffic is
zero. The claimed prefix bound was therefore false exactly on a failure branch
that the refinement theorem promises to preserve.

**Resolution.** The selected blank, unaliased output register and local
head-motion convention imply the pathwise reach inequality

```text
sum_attempted_outputs (encodedLength+1)
  <= lambda_P * (1+Acts+Steps).
```

It counts outputs whose next route rejects. At initialization, the private
meter dedicates a coordinatewise output pool
`g_P*lambda_P*(1+A+T)` from the static native quotas without recording its
unused capacity as work or traffic. Actual scans and private outgoing bits
take exact sub-capabilities and report exact use. Hence they cannot fail after
primary prepare, yet no step repeatedly reserves `S`. Delivered input copies,
whose original route has already committed, remain charged to
`OriginalTraffic`; output handling is charged to the activation/step
coefficients. The output-pool counter is included in `B_exp` and physical
state.

### Forty-fourth-pass verdict

The response-dependent prepared-output transaction is now funded before it
can affect control flow, including the downstream-routing rejection case.

## Forty-fifth-pass review - progress inside variable-length phases

### Attack 1: eight phases are not eight microsteps

The no-divergence proof ordered eight administrative phases and then claimed
a fixed number of private events per native primitive. An admitted input
copy, prepared-output scan, or private output copy contains a number of
bit-costful microsteps proportional to its payload. Phase position does not
decrease during those microsteps, so it was not by itself a transition-level
well-founded rank.

**Resolution.** The progress measure is now lexicographic:

```text
(remaining phase suffix, remaining admitted microsteps).
```

Every scan/copy step decreases the second coordinate; a phase transition
decreases the first regardless of the next finite length. Admission fixes a
finite second coordinate and commits are infallible. The correct expansion
bound is `k_P+c_in*inputLength+c_out*outputLength`, not a constant. This
retains bit-level accounting while excluding an infinite administrative
suffix.

### Forty-fifth-pass verdict

Progress is now proved at the actual small-step granularity used by the
communication and access-cost model.

## Forty-sixth-pass review - local response versus closed productivity

### Attack 1: a responsive graph does not force its context to decide

The DAG and affine-credit constructor theorems bounded every tested-component
activation and local-certificate failure, then called the result
“productive.” But the paper's productivity predicate is the closed
`Success` event of a completion context. Even when the tested graph answers
perfectly, the context can suffer its separately certified safety,
shared-infrastructure, or progress failure. Those events were described in
the context definition but dropped from the constructor conclusions.

This is a quantifier error, not merely loose notation: a worst-case local
certificate implies strong *tested-side response*, whereas strong closed
productivity also requires a strong completion context.

**Resolution.** For each admitted completion context, `chi_D` now bounds the
union of its context-owned safety failure, shared-infrastructure failure, and
progress failure conditional on the tested side respecting the interface
envelope. The elementary DAG, solved response-adaptive DAG, and affine-credit
theorems first state their tested-side response/failure conclusions and then
derive

```text
closed failure <= local tested-side failure + chi_D.
```

Thus the response-adaptive bound is `Fail_RA+chi_D`, and the coarse credit
bound is `(C_0+1) max_v delta_v+chi_D`. Worst-case local certificates set only
the first term to zero; strong closed productivity requires `chi_D=0`.

### Forty-sixth-pass verdict

The availability constructors now respect the productivity quantifiers
defined earlier, including the observer's independently certified failures.

## Forty-seventh-pass review - parallel wrapper global space

### Attack 1: total calls do not determine persistent parallel state

The tagged RF/RP calculation correctly replaced the single-instance query
bound `q` by total calls `Q` for cumulative work, activations, traffic, and
oracle coordinates. It also reused the single-instance space expression
`4m+2*kappa+10` for `h` parallel instances. That expression contains only two
logical unary parameter tracks. The parallel graph has `2h` wrapper
occurrences, and all of those tracks coexist even though the scheduler has one
token. Fixed `h` makes the omission asymptotically harmless but does not make
the literal ledger bound true.

**Resolution.** The single-instance bound is retained for one pair. The
parallel theorem now uses the conservative global bound

```text
Space_parallel <= S + h*(4m+2*kappa+10).
```

This sums the per-instance strong space certificates and therefore does not
assume transient-buffer sharing. A sharper simultaneous-state proof could
reduce those buffer terms, but may not erase the `2h` persistent parameter
tracks. For the numerical `m=256,h=16` instance, the reported wrapper-space
increment is `32*kappa+16,544` cells.

### Forty-seventh-pass verdict

The parallel reduction now distinguishes cumulative call reindexing from
global persistent space and gives a literal fixed-`h` profile.

## Forty-eighth-pass review - persistent state in availability certificates

### Attack 1: a maximum over child peaks erases inactive siblings

The response-adaptive DAG recurrence added a parent's retained space to the
maximum child `Space_w`. That is valid for transient frames on one active call
stack, but not for complete child peaks: persistent dictionaries, parameter
tracks, heads, and suspended resource states of every inactive sibling remain
live simultaneously. A global maximum could underfund their sum.

### Attack 2: one activation does not bound a stateful lifetime

The local space polynomial was evaluated per activation although the same
occurrence may be called polynomially many times. A lazy table can grow on
every call while respecting the per-activation transient bound. Neither DAG
acyclicity nor affine credit prevents this accumulation.

**Resolution.** Both DAG rules now require two separate local certificates:

```text
u_v(...)       active/suspended transient space,
p_v(...,N,...) lifetime persistent state after at most N activations.
```

The forward pass computes `N_v`; every `p_v` is evaluated there and all
occurrences are summed into `Persist`. A reverse recurrence takes a
root-to-leaf maximum only over `u_v` plus suspended/routing frames. The global
space grade is

```text
sum_v p_v(...) + max_root Stack_v + fixed route/meter state.
```

The affine-credit rule analogously requires a polynomial `P_v` over its
`C_0+1`-activation certified prefix and sums all `P_v`, then adds one active
transient state, one live message, and routing stack. Represented credit and
parameter tracks belong to the persistent term.

### Forty-eighth-pass verdict

The availability theorems now bound simultaneous global space for stateful
components across their full certified lifetime, not only the active call.

## Forty-ninth-pass review - complete affine-credit ledger

### Attack 1: the final visible transfer disappeared from routing cost

The credit theorem permits at most `C_0` hidden transfers followed by one
visible answer, but its work formula called `Routing(C_0,L_max)`. The complete
numeric example likewise paid only the hidden routes. The theorem's own
traffic sentence used `C_0+1`, exposing the inconsistency.

### Attack 2: the worked example still omitted the new space premise

After the generic theorem began distinguishing persistent and transient
space, the “complete” two-node calculation still displayed only work,
traffic, and activations. It therefore did not instantiate its own updated
certificate.

**Resolution.** Routing now receives `C_0+1` messages. For
`x=kappa+b`, the corrected example is

```text
Work    = 9x^2 + 29x + 20,
Traffic = (x+1)(x+3),
Acts    = x+1.
```

The example additionally certifies `kappa+5` retained cells per node, one
`x+4` active transient frame, one `x+3` message, and eight routing-control
cells, giving global peak `4kappa+2b+25`. It names the credit as ghost and
sets random/oracle coordinates to zero; a represented counter would add
ordinary state and work.

### Forty-ninth-pass verdict

The worked credit instance now funds the final response and every advertised
ledger coordinate.

## Fiftieth-pass review - local realization versus closed productivity

### Attack 1: a funded machine profile does not fund its boundary

The lazy random-function proposition funded the component's dictionary,
randomness, activation, and output-construction coordinates and then called
the result strongly no-exhausting “against every adaptive context.”  The
same section listed `Qm` query bits and `Qn` response bits only as a later
boundary contribution.  A finite structural router can therefore reject an
otherwise valid query or reply unless a route-safe closure or an explicit
boundary envelope is part of the premise.

### Attack 2: local response was promoted to closed success

Even after routing is funded, the `LazyRF` occurrence answering every
delivered query does not force an arbitrary closing context to reach its
decision.  The availability definitions already assign the completion
context its own conditional progress, safety, and shared-infrastructure
failure bound `chi_D`.  Omitting that term repeats, for a worked
implementation, the quantifier error repaired in the generic DAG and credit
theorems.

**Resolution.** The proposition now distinguishes three conclusions:

```text
local profile + Qm/Qn route envelope
  => exact Q-query response law
  => no exhaustion and response by the LazyRF occurrence;

closed failure <= chi_D.
```

The final implication is strong only for a strong completion context
(`chi_D=0`).  The paper, oracle note, complete example, dossier, and claims
ledger all state the same boundary.

### Fiftieth-pass verdict

The complete lazy-random-function instance now proves exactly the local
implementation property its meter supports and carries the independent
closing-context obligation into productivity.

## Fifty-first-pass review - noncomputability with random tapes

### Attack 1: one probabilistic run is not a decision procedure

The non-surjectivity example argued that a machine realizing the halting DDS
could be run once to decide the halting problem.  That proof is immediate for
a deterministic machine, but the operational image also contains fair random
tapes and identifies laws.  Exact almost-sure correctness plus almost-sure
termination does not by itself turn one sampled run into a deterministic
halting decider, because the exceptional divergent set can be null.

### Attack 2: “computable fragment” overstates a pathwise claim

A finite machine code evaluated relative to an arbitrary infinite tape can
induce an individual fixed-tape DDS that is not computable without that tape.
What is finite-code generated is the stochastic experiment and its effective
cylinder structure, not necessarily every pathwise lifetime function.

**Resolution.** For a fixed input, the tape sets on which a finite-code
machine emits 0 and 1 after finite time are effectively enumerable unions of
dyadic cylinders. Their probabilities are therefore lower semicomputable.
If the transcript law were the total deterministic halting DDS, one of those
probabilities would be one and the other zero. Dovetailing their increasing
rational approximations until one exceeds one half yields a deterministic
halting decider, a contradiction. The exposition now calls the image the
“finite-code machine-generated fragment,” avoiding the false pathwise
computability reading.

### Fifty-first-pass verdict

The proper-image counterexample now excludes randomized exact realization,
including null divergent tapes, and states the operational restriction at the
correct stochastic level.

## Fifty-second-pass review - finite support is not a finite DDS horizon

### Attack 1: the cited finite-PDS definition had a missing premise

The finite-image corollary correctly inferred finite support of the
pushforward law, then claimed that a common domain alone made it a finite PDS
in the sense of Lanzenberger--Maurer. Their Definition 8 additionally inherits
the paper's finiteness convention: the input alphabet is finite and the
common domain is contained in histories of one finite maximum length. A
finite seed can select among finitely many *unbounded-lifetime* DDSs and
therefore does not supply that horizon.

### Attack 2: “finite DDS” was used without fixing its meaning

The implementation proposition hard-codes a finite graph, which is valid for
the cited bounded-horizon notion but not for an arbitrary DDS merely over
finite alphabets. Without an explicit convention, “finite” could be read as
only alphabet finiteness while leaving infinitely many histories.

**Resolution.** The background now defines a finite DDS exactly as a DDS with
finite input alphabet and domain contained in histories of length at most
some fixed `n`. The finite-image corollary separately states:

```text
finite image                 => finite-support lifetime law;
finite image + common finite horizon => cited finite common-domain PDS.
```

The finite-seed sentence now claims only finite support unless the separate
bounded-horizon premise is supplied.

### Fifty-second-pass verdict

The measure-level extension and the cited finite common-domain subtheory now
meet under the source's actual horizon hypothesis, with no conflation of
support size and lifetime length.

## Fifty-third-pass review - native logical space convention

### Attack 1: the examples charged heads but the ledger definition did not

The uniform parameter convention says that every parameter head contributes
to `peak_v` and `gpeak`; the flip-chain and mask calculations consequently
add one cell per such head. The dossier's ledger definition, however,
described `peak_v` only as nonblank work and input/output cells. Read
literally, the worked profiles and the declared coordinate used different
space measures.

### Attack 2: a logical head record is not its physical bit encoding

Counting a head as one native logical cell must not erase the cost of
serializing an integer position whose magnitude grows with the run. The
explicit-resource refinement later adds
`O((S+H_P) log(T+S+2))`; without naming the level distinction, either the
native examples overcount inconsistently or the physical refinement
double-counts without explanation.

**Resolution.** The native ledger now fixes one logical live-footprint
convention: occupied tape/register cells plus one unit for each fixed finite
control/state record and tape-head record; the mode and pending finite port
tag may be packed into the control record. A numeric head position is one
logical record at this level. The later explicit physical representation
separately charges the coordinate's bit length. The dossier and worked-example
ledger header use the same convention.

### Fifty-third-pass verdict

Uniform parameter tracks, native capacity, exact `gpeak`, and physical
serialization now refer to two explicitly related rather than silently mixed
space measures.

## Fifty-fourth-pass review - lazy-dictionary record traversal

### Attack 1: scanning keys still has to cross stored values

The earlier anti-RAM review replaced constant-time lookup by
`4Q(m+1)` scan work per call. But the selected object is a sequential list of
encoded `(x,y)` records. On a miss, reaching the next key requires traversing
the intervening `n`-bit value as well. A fixed multitape implementation can
split key and value tapes, but then locating or advancing past the
corresponding value records still costs their length. With large `n` and
large `Q`, the advertised work quota could fire on an honest scan.

**Resolution.** Bound each complete encoded record by `m+n+8` bits and charge

```text
Work_LRF
  <= Q(4Q(m+n+8)+8(m+n+1)) + LenEval.
```

The first term now pays literal passage over every key, stored value, and
record tag in the worst case. The second still pays validation, append,
random-bit reading, and blank-output construction. Space and randomness
bounds are unchanged. Every integrated formula and the claims ledger now use
`O(Q^2(m+n+1)+LenEval)`.

### Fifty-fourth-pass verdict

The exact lazy-function implementation no longer relies on an unmodeled jump
from one sequential key to the next.

## Fifty-fifth-pass review - generated-interpreter state encoding

### Attack 1: binary coordinates can add a hidden logarithmic factor

The compiler permits `L^2` declared tape headers and claims physical state
`O((L+M)^2)`. If every virtual tape cell were stored as a sparse record
repeating binary node, tape, and integer-position fields, the representation
could acquire extra logarithmic factors not present in that display. Merely
counting logical virtual cells would not establish the physical universal
machine's space profile.

**Resolution.** The selected layout is now stated in the integrated proof.
Directory order supplies positional node/tape identities. Each materialized
virtual tape is a unary interval over a fixed alphabet with its head marked in
place, so its total interval growth is bounded by the `LW` simulated head
moves. Untouched tapes need only their constant directory header. There are
only `O(L)` virtual meter records, whose binary quota/counter encodings cost
`O(L log(M+1))`. Hence the complete accounting is

```text
O(L^2 + LW + M + L log(M+1))
  subset O((L+M+2)^2),
```

using `W<=M`. A sparse coordinate-per-cell interpreter is explicitly a
different layout and would require its own bound.

### Fifty-fifth-pass verdict

The compiler's quadratic physical-space claim is now tied to a concrete
unary-interval/directory representation rather than an unspecified virtual
dictionary.

## Fifty-sixth-pass review - credit example and hidden workload

### Attack 1: a ghost bound cannot give the program access to `b`

The numeric cycle set `C_0(kappa,b)=kappa+b` and said that the zero-credit
activation emits. In the selected workload model, however, `b` is
administrative and program-hidden. If the nodes' branch at zero implicitly
read that countdown, the example would violate the information boundary; if
the countdown were represented, the advertised “ghost” space profile omitted
it.

**Resolution.** The worked service now receives an ordinary unary countdown
`z` in its external request, with the interface certificate `|z|<=kappa+b`.
Every hidden transfer deletes one symbol and the empty string causes the
visible response. The proof uses `|z|` as a ghost variant derived from already
charged message state and uses `kappa+b` only as its static upper bound.
Neither program sees `b`, a quota, or an extra credit register. Message,
transient-space, traffic, and work bounds already include the unary payload;
a distinct represented counter would add its ordinary profile.

### Fifty-sixth-pass verdict

The complete affine-credit instance now exhibits an actual program-visible
decreasing object while keeping the ambient workload administrative.

## Fifty-seventh-pass review - two-sided metering loss

### Attack 1: one coupling term was used for two experiments

The efficient witness said that metering changes an unmetered real/ideal
behavioral bound by at most `delta_C`, but described `delta_C` only as the
union of owner-specific exhaustion events without saying whether it covered
the real experiment, the ideal experiment, or both. The triangle inequality
requires one metered/unmetered coupling term on each side. If `delta_C`
bounded only one closed run, the displayed security loss could be short by a
factor of two or by an independently larger ideal-side failure.

### Attack 2: exhaustion and productivity had one unnamed field

The witness signature carried only `epsilon,delta` although its obligations
also required completion-context progress and productivity. This contradicted
the paper's earlier insistence that no-exhaustion and productivity are
logically separate.

**Resolution.** The witness now carries `epsilon,delta,eta`. For every
completion context, the no-exhaustion certificate is required in both
`C[pi R]` and `C[S sigma]`; `delta_C` dominates the sum of the three owner
classes across both experiments. The metering triangle bound can therefore
add at most `delta_C`. Separately, `eta_C` dominates the sum of the two
closed-productivity failure bounds after each adds tested-graph progress
failure and the context's `chi_C`. It enters only statements that require
closed success.

### Fifty-seventh-pass verdict

The efficient construction package now accounts for both sides of the
security comparison and keeps semantic error, exhaustion, and productivity
as three distinct losses.

## Fifty-eighth-pass review - compiler interval-growth notation

### Attack 1: an undefined variable obscured the physical-space certificate

The generated-network note described the selected directory/interval layout
as using `L^2 + 2LT` cells, although the compiler has no variable `T` in this
part of the argument.  The immediately preceding invariant bounds the total
number of simulated head moves by `LW`.  Read literally, the displayed term
was therefore undefined and could not support the later quadratic profile.

**Resolution.** The layout bound is `L^2 + 2LW`: `L^2` directory headers,
plus at most two interval endpoints/cells per aggregate simulated head move.
The integrated paper already used the corresponding
`O(L^2+LW+M+L log(M+1))` expression.  Since `W <= M`, the corrected detailed
bound is still contained in `O((L+M+2)^2)`.

### Attack 2: a long display overprinted its equation number in the PDF

The network-wide physical-peak certificate fit logically in the source but
its one-line typesetting collided with the equation number, hiding part of
the final summand.  That is not merely cosmetic in a cost paper: an unreadable
funding formula cannot be audited.

**Resolution.** The display is now aligned over three lines, with the
infrastructure term, per-bundle counter/serialization terms, and event
envelope all visible.  The regenerated PDF passes structural validation and
the repaired page was visually inspected.

### Fifty-eighth-pass verdict

The compiler's physical-space argument now uses one defined trace variable
throughout, and its global funding certificate is legible in the delivered
artifact.

## Fifty-ninth-pass review - witness-notation and loss-field drift

### Attack 1: the detailed adequacy note still exposed the obsolete witness

The integrated theorem now uses

```text
EffConstruct_(M,C)(
  pi R, S sigma;
  T_pi,T_sigma,epsilon,delta,eta),
```

where `delta` covers both metered/unmetered coupling terms and `eta` is the
separate closed-productivity loss.  The detailed adequacy note still wrote a
different tuple with `nu`, omitted the profile transformers from the
signature, and indexed the simulator inconsistently.  Although the prose
contained most ingredients, two incompatible formal signatures leave it
unclear which object the closure theorem composes.

**Resolution.** The adequacy note now uses `sigma` collectively for the
interface-simulator tuple, includes `T_pi,T_sigma` in the judgment, and uses
the same `epsilon,delta,eta` fields as the paper.  Its no-exhaustion clause
states explicitly that `delta_D` dominates tested, context, and shared
failure classes in both real and ideal experiments.  Sequential closure now
composes `delta`, not an obsolete `nu` field.  Local no-exhaustion predicates
may still use `nu_D`; the correction is specifically to the construction
witness package.

### Fifty-ninth-pass verdict

The main theorem, adequacy constructor rules, and closure formulas now refer
to one checkable efficient-construction object.

## Sixtieth-pass review - assumption-sensitive IITM evidence

### Attack 1: a summary table dropped the time-lock-puzzle premise

The source audit correctly records that the IITM composition/replication
counterexamples in the cited section are conditional on the existence of
time-lock puzzles.  The explanatory paragraph retained that premise, but the
adjacent comparison table and one related-work sentence compressed the result
to an unconditional “almost-bounded components need not compose.”  Readers
often quote tables without the following prose, so this violated the paper's
own source-attribution rule.

**Resolution.** The table now says explicitly “Under time-lock puzzles,” the
related-work sentence calls the closure failures assumption-conditional, and
the dossier comparison row carries the same qualification.  The paper's own
unconditional counterexamples remain separate: they refute naive
per-activation and local-shape rules, not every IITM environmental predicate.

### Sixtieth-pass verdict

The bottom-up literature is used as adversarial design evidence without
silently strengthening an assumption-sensitive source theorem.

## Sixty-first-pass review - shared stateful-oracle coherence

### Attack 1: an outside caller can stale the compiler's cached coordinate

The generated-to-fixed invariant stores each fixed stateful oracle's public
contract coordinate inside the interpreter and refreshes it from the private
commit receipt after a virtual call.  That is correct when all callers are
virtual callers behind the compiler proxy.  But the general dependency model
also permits intentional sharing of one oracle occurrence.  If an outside
caller could invoke that occurrence directly between two virtual calls, the
physical hidden state and public coordinate would advance while the cached
virtual coordinate did not.  The next virtual reservation could then use the
wrong tariff, breaking both admission equality and the exact virtual-ledger
invariant even though the ordinary response wire remained well typed.

**Resolution.** The compiler now carries an occurrence-coherence declaration.
Each fixed stateful dependency is either private to the compiled subsystem,
or one fixed charged multi-client proxy mediates *every* intentional caller.
Outside callers retain their own budgets, but every committed call updates
the proxy's authenticated public-coordinate record before another virtual
admission. Direct bypass sharing is outside the theorem. The premise is stated
in the integrated theorem, compiler construction, proof, dossier, dependency
audit, and claims ledger.

### Sixty-first-pass verdict

State sharing is no longer inferred from a reply-only simulation; the exact
compiler invariant names the coherence mechanism it requires.

## Sixty-second-pass review - compiled-profile display audit

### Attack 1: the fixed-work certificate collided with its equation number

The explicit fixed-interpreter example is intended to make every constant in
the generated-family compilation auditable.  Its one-line `FixedWork`
certificate was wider than the display column, so the final interpreter term
collided with Equation 95's number.  A mathematically present but visually
obscured summand defeats the purpose of giving an explicit certificate and can
make a reader misidentify the stated physical profile.

**Resolution.** The fixed-work and fixed-space certificates are now aligned
over multiple lines, with the decoder, evaluator, and interpreter terms
separated at stable breakpoints.  The paper was recompiled and the reflowed
pages were rendered and inspected at full resolution; Equations 95 and 96 and
their numbers are now disjoint and legible.

### Sixty-second-pass verdict

The generated-family example's explicit physical work and space bounds are
fully visible in the delivered artifact.

## Sixty-third-pass review - transport-definition exposition

### Attack 1: the transport section opened with an orphaned imperative

The section carrying native AC experiments into explicit resource bundles
introduced its central bundle equation with the isolated word “Write.”  The
equation was well formed, but the fragment did not identify what object was
being defined and looked like a typesetting remnant.  At the final refinement
boundary, that ambiguity makes it unnecessarily difficult to distinguish a
notation declaration from a proof instruction.

**Resolution.** The introduction now reads “For a native program bundle,
write,” immediately identifying the subject of the displayed definition.  The
change was compiled and all affected closing pages were reinspected.

### Sixty-third-pass verdict

The explicit-resource transport now introduces its bundle notation as a
complete, self-contained mathematical sentence.

## Sixty-fourth-pass review - duplicate-token audit

### Attack 1: duplicated prose obscured the generated-family calculation

An automated repeated-word scan of the rendered text found two instances of
“one one-bit” in the same explicit chain calculation.  In the first, “one”
was meant as a determiner for the fixed program; in the second, the intended
quantifier was over every internal route.  Leaving both duplicates makes the
reader pause over whether “one” is a numerical modeling restriction.

**Resolution.** The text now says “copies of the one-bit program `Flip`” and
“each one-bit internal route.”  The formulas are unchanged.  The manuscript
was rebuilt and the repeated-word scan rerun on the extracted PDF text.

### Sixty-fourth-pass verdict

The generated-family prose now states its fixed program and per-edge routing
cost without an accidental extra quantifier.
