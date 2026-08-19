# A cost-aware operational layer below random systems

## Executive conclusion

Constructive Cryptography does not lack a place for computation. Its top-down
architecture deliberately postpones the choice. The existing random-system
layer should therefore not be replaced by Turing machines; it should be
realized by a lower algebra whose denotation preserves the operations used
above.

The recommended lower algebra has two stages.

1. A finite, typed, single-token network of probabilistic interactive Turing
   machines gives the unbounded behavior. Fixed random tapes determine a
   deterministic partial run, first-visible-output macro execution determines
   a DDS, and the tape measure determines a random system.
2. The same small-step run carries an exact cost ledger. Non-observable meters
   bound each implementation component by a polynomial transformer of the
   security parameter and a common ambient workload. A closed efficient context
   chooses a polynomial workload. This creates a feedback-safe, cost-aware
   implementation algebra. Separately, abstract resources are accessed as
   charged oracles and need not be machine implementable.

Canonical structural routing is fully charged but receives a derived
aggregate envelope that dominates every possible matching action.  This
route-safe subalgebra embeds injectively into the selected standard-Borel
partial-random-system carrier.  An intentionally limited link is an explicit
resource node, so no physical limitation is erased by the structural
connection theorem.

This design gives three statements that must not be conflated.

- **Behavioral realization:** erasing microsteps and cost maps machine
  networks to an operational image of random systems.
- **Efficient execution:** every fixed uniform metered graph in a polynomial
  workload has polynomial total transitions, space, randomness, traffic,
  activations, and declared oracle calls.
- **Useful implementation:** on the advertised workload, the protocol does
  not merely stay within its quotas; it returns the behavior required by the
  target specification. This is a separate no-exhaustion and productivity
  proof.

The ambient workload is the crucial reactive ingredient. A service is not
given one lifetime polynomial that an environment of higher polynomial degree
can exhaust. Instead, for each fixed efficient context, the context supplies a
polynomial workload parameter and every component has a fixed polynomial
transformer of that parameter. This has the quantifier pattern

```text
for every fixed efficient context C
there is a polynomial bound for the closed experiment C[N].
```

At the same time, strict component meters make the implementation class closed
under arbitrary finite wiring and feedback: a bad cycle may exhaust, but it
cannot manufacture more computation. Availability remains an explicit
semantic obligation.

This is not a UC formalization. UC, RSIM, reactive polynomial time, and IITM
are used only as evidence about machine execution and the pathologies of naive
runtime definitions. No adversary role, corruption convention, session
identifier, or UC quantifier is imported.

## 1. Research question and scope

### 1.1 The question

The precise question is:

> What concrete operational and cost-aware algebra can be placed below the
> discrete/random-system layer of Abstract and Constructive Cryptography such
> that its denotation preserves the higher resource operations, supports both
> computationally unbounded and efficient regimes, and makes every efficiency
> and reduction loss explicit?

The answer has to settle the following lower-level choices.

- effective encodings and the representation of the security parameter;
- uniform versus nonuniform families;
- persistent local state, random tapes, and reset;
- routing, scheduling, activations, message lengths, and feedback;
- local versus global time, space, randomness, and communication;
- ideal-resource calls and their cost;
- partiality, divergence, and budget exhaustion;
- asymptotic distinguishers, auxiliary input, and negligibility;
- concrete reduction and simulator overhead;
- the relation between free efficient computation and explicit computation
  resources.

### 1.2 Non-goals

The work does not define UC inside CC. It does not prescribe parties,
adversaries, corruption, a network attacker, a session hierarchy, or a dummy
adversary. These can be expressed later as particular resources and
converters.

The work also does not claim that every abstract random system is machine
implementable. Nonrecursive response functions and noncomputable probability
parameters remain legitimate mathematical specifications. The theorem sought
is an image theorem, not surjectivity.

Finally, “polynomial time” is not asserted to be the only meaningful cost
notion. Exact ledgers are retained so that concrete, memory-bounded,
randomness-bounded, communication-bounded, hardware-specific, or
post-quantum variants can be selected later.

## 2. What the primary sources force

### 2.1 The abstraction hierarchy

MauRen11 explicitly contrasts bottom-up modeling - Turing machines, tapes,
steps, and a fixed efficiency notion - with a hierarchy in which the system
algebra is fixed first. Their Level 2 contains discrete and random systems;
Level 3 contains implementations and abstract cost; still lower levels can
choose a machine, timing, and physical model. A theorem at a higher level is
inherited once a lower level satisfies its axioms.

The consequence is methodological. A machine model should be judged by a
homomorphism into the random-system algebra, not by whether it resembles the
notation of an existing security framework.

### 2.2 Four cost regimes already anticipated by CC

MauRen16, Section 3.5, separates four choices.

1. Ignore computation and quantify over unrestricted converters.
2. Keep information-theoretic computation but expose memory, using stateless
   converters plus a memory resource.
3. Expose a processor resource and restrict converters to routing programs and
   data.
4. Treat all efficiently implementable converters as free, typically using a
   properly closed polynomial-time class.

These are not rival definitions of the same object. They are different lower
models selected according to which costs matter. Section 4.3 further explains
that a concrete simulator cost must be included as a resource or reduction
loss even when the high-level converter class is called free.

The proposed stack therefore supports both a free-PPT quotient and explicit
`CPU`, `MEM`, `RAND`, and `COMM` refinements.

### 2.3 The current high-level PPT wrapper is intentionally incomplete

Jost's Definition 2.2.14 calls a family efficient when one uniform PPT,
receiving unary security parameter, implements it. This is the right
asymptotic wrapper. It does not settle what “PPT” means for a persistent
interactive machine with arbitrarily many calls, what input length gives it
new work, whether routing is charged, or what an ideal oracle costs.

Jost's Theorem 2.2.11 is equally important. Absorbing a converter or parallel
resource into a distinguisher changes the reduction. The present layer makes
that change quantitative as a budget transformer rather than silently calling
it closure.

### 2.4 Runtime pathologies from bottom-up frameworks

The operational literature supplies counterexamples, not a framework to
import.

- A strict lifetime polynomial can be consumed by irrelevant queries from an
  environment with a higher-degree polynomial.
- A polynomial per activation in the current message length permits cyclic
  message growth.
- A protocol whose total output is polynomial in outside input is not
  necessarily closed under connection; two isolated forwarders can form an
  internal infinite loop.
- “Almost bounded” components can generate one another's rare bad inputs. The
  IITM time-lock-puzzle construction shows that negligible runtime overrun is
  not generically compositional.
- Reactive polynomial time uses the useful environment-relative pattern, but
  its class is itself not closed under arbitrary connection; composition
  needs a side condition.

The proposed model keeps the environment-relative polynomial degree while
obtaining syntactic closure through meters. It does not claim that the
unmetered responsive subclass is closed.

## 3. Requirements

The source analysis and counterexamples yield the following requirements.

**R1 - Behavioral conservativity.** Erasing costs from a successful metered
run must give exactly the unbounded run. Budget exhaustion must not be changed
into an ordinary response.

**R2 - Effective uniformity.** An efficient implementation has one finite code
independent of the security parameter. The parameter is given in unary.
Generated graphs and advice require separate, explicit conditions.

**R3 - Bit-level accounting.** A long message cannot appear, be routed, or be
read for constant cost. Encodings are self-delimiting and all serialization
and canonical routing are charged.

**R4 - Persistent lifetime accounting.** Time, live state, random-tape
position, and quotas persist across activations. Reset and erasure are
explicit operations.

**R5 - No complexity laundering.** Internal messages do not grant new
computation merely by being long. Oracle replies do not create budget.
Randomness and oracle work have separate coordinates.

**R6 - Feedback safety.** Arbitrary well-typed wiring must remain an object of
the bounded implementation algebra, even when it is not productive.

**R7 - Availability separation.** Polynomial resource use and successful
service are different predicates.

**R8 - Two sorts.** Ideal specifications require wire encodings and access
tariffs, not finite implementations.

**R9 - Reduction transparency.** Converter, simulator, routing, universal
simulation, message, and oracle overhead must transform the attack budget.

**R10 - Refinability.** The exact trace must support later hardware weights
and explicit resource presentations.

## 4. Behavioral core

### 4.1 Signatures and encodings

A call signature is a pair `A = (Q_A, R_A)` of countable query and response
sets with effective, prefix-free encodings into finite bit strings. For a
dependent signature, responses form a family `R_A(q)`. The length `|x|` always
means the length of the selected wire encoding, including the required
self-delimiting tags.

Every port occurrence has a name, a signature, and provider or client
polarity. A wire connects one provider occurrence to one client occurrence.
Fanout, broadcast, queues, multiplexing, dropping, and reordering are programs
or resources, not wiring conventions.

For an efficient implementation boundary, parsing and membership checking
must be computable within a declared polynomial tariff. An abstract
specification may use a mathematically defined value set, but a machine can
interact with it only through finite codes and a tariffed validation rule.

### 4.2 Component machines

A component is a finite-code probabilistic interactive multitape Turing
machine with:

- a read-only unary security tape containing `1^kappa`;
- a read-only current-input tape;
- finitely many persistent work tapes;
- a blank-at-activation output tape or register;
- a named one-way persistent random tape; a transition may make no inspection
  or inspect the current bit and then stay/advance as selected by that
  bit-dependent branch;
- finite control with active, suspended, blocked, and emit modes.

One transition changes only a constant number of tape cells and head
positions. It may read at most a constant number of random bits. An output
event is enabled only after a complete self-delimiting event has been written.
There is no pointer-valued operation that turns an existing input buffer into
an output for unit cost.

The program does not have access to its meter or remaining quota. It can use
`kappa`, input data, persistent state, and randomness. This non-observability is
required for budget monotonicity.

### 4.3 Networks and routing

A network is a finite typed graph of component occurrences, a partial matching
of compatible ports, and unmatched boundary ports. All component, tape, port,
and edge names are globally distinct.

There is one activation token. An external input can be delivered only when
the network is quiescent. The owner runs until it:

- emits on a wired port, transferring the token through the canonical router;
- emits on a boundary port, ending the macrostep;
- blocks; or
- runs forever.

The canonical router validates the event code, copies or transfers it using a
specified bit-cost model, clears the old buffer, and activates the receiver.
From the validated self-delimiting header it first reserves the complete
copy-work, traffic, and destination-buffer envelope. Rejection occurs before a
routing coordinate or destination buffer commits. Admission yields a linear
capability under which the ordinary bit-level copy runs infallibly; every
transition, transmitted bit, intermediate buffer, and simultaneous peak is
still recorded. Replacing it with a faster hardware router is a different
cost model or an explicit communication resource, not free bookkeeping.

One token eliminates an implicit scheduler. A model with several pending
messages must add an explicit scheduler component; its choices, time,
randomness, and queues are then charged. This extension does not change the
role of the denotation map.

### 4.4 Strict unbounded macro semantics

Fix one infinite random tape per machine. Delivery of an external input gives
a unique maximal small-step run. The partial macro transition returns the
first boundary output and the next quiescent configuration when that event
occurs after finitely many steps. It is undefined on blocking,
micro-divergence, or infinite hidden token transfer.

Folding macrosteps over external input histories yields a prefix-closed DDS.
Pushing the product tape measure through this map yields a law over lifetime
DDSs. Quotienting by transcript behavior yields a random system.

This is the existing unbounded realization. The efficient layer enriches its
small-step trace and does not redefine its successful behavior.

## 5. Exact cost traces

### 5.1 Primitive ledger

For a finite run prefix `rho`, define the exact ledger

```text
Cost(rho) =
  ( step_v,
    act_v,
    rand_v,
    peak_v,
    gpeak,
    traffic_e,
    calls_j,
    queryBits_j,
    responseBits_j ) .
```

There is one `v` coordinate for every implementation component, one `e`
coordinate for every wire including boundary wires, and one `j` coordinate
for every named abstract oracle.

- `step_v` counts component and canonical-router Turing transitions.
- `act_v` counts deliveries that activate the component.
- `rand_v` counts bits read from its named random tape.
- `peak_v` is the maximum native logical live footprint during the run
  prefix: occupied tape/register cells plus one logical cell for every fixed
  finite control/state record and tape-head record. The finite mode and
  pending-port tag may be packed into the control record. A numeric head
  coordinate is one logical record at this level; its physical serialization
  length is a separate lower cost.
- `gpeak` is the maximum, over small-step configurations in the prefix, of the
  simultaneous sum of all implementation and canonical-router live cells,
  including occupied in-flight routing buffers.
- `traffic_e` is the sum of encoded event lengths sent over edge `e`.
- `calls_j` counts queries admitted by oracle `j`.
- `queryBits_j` and `responseBits_j` record serialization separately.

Primitive-event ownership fixes exact failure order. A canonical router first
checks its whole-message work/traffic/buffer reservation. Rejection commits no
routing coordinate; admission makes the subsequent bit-costful copy
infallible while retaining every exact small-step and `gpeak` update. Receiver
delivery is then one receiver-owned charge that jointly installs the
validated input, increments `act_v`, and checks the resulting `peak_v`;
rejection leaves the receiver suspended after the completed routing cost. One
machine transition likewise jointly checks `step_v`, the prospective peak,
and `rand_v` iff it inspects the current random cell. Rejected transitions do
not move the random head. This convention is used by the explicit-resource
stuttering and sequential-link theorems.

The full ledger is deliberately not a single commutative-monoid grade. Time,
traffic, random bits, activations, and calls are cumulative; space is a peak.
Exact per-component and per-edge coordinates are kept until a later
aggregation.

### 5.2 Local and global views

A global report may use

```text
Work       = sum_v step_v
Activations = sum_v act_v
RandomBits = sum_v rand_v
PeakSpace  = max_t sum_v liveCells_v(t)
Traffic    = sum_e traffic_e
OracleCalls(j) = calls_j.
```

Here `PeakSpace` is exactly the stored `gpeak` coordinate. It cannot in
general be reconstructed from the individual `peak_v`: two components may
reach their local maxima at different times. The external accountant updates
`gpeak` at every intermediate and committed configuration. Per-component
peaks remain useful for local grades; the simultaneous coordinate is needed
for an exact global memory report.

Per-party, per-interface, energy, latency, or hardware-weighted reports are
monotone functions of the exact ledger. A selected weighting is part of a
cost model and should be named in a theorem. Two extensionally equal programs
can have different exact costs.

Because ledger coordinates use internal occurrence names, a public report is
always an isomorphism-invariant map satisfying
`Rep_(phi N)(phi_* ell)=Rep_N(ell)`. It may retain declared public
party/interface/oracle/owner labels but never a fresh alpha-name. The maximal
pointwise report can be the finite graph/ledger orbit. An efficient test uses
a fixed effective projection with charged output length and evaluation; it is
not given free graph canonization.

On the standard machine model, every newly visited cell, emitted bit, random
bit, and activation entails at least one charged transition, up to fixed
encoding/router constants. Thus a strict polynomial work bound implies
polynomial space, local randomness, and machine-produced traffic. They remain
separate because:

- concrete losses can depend on query or communication counts;
- an ideal oracle can return bits without implementation transitions;
- memory capacity can be relevant even when time is ignored;
- alternative hardware weights can break the constant-factor relation.

### 5.3 Lifetime and failure costs

The ledger persists over all macrosteps of one system lifetime. A finite
blocked execution has a finite prefix ledger. A divergent run has a directed
family of finite-prefix ledgers and at least one unbounded positive
coordinate. No infinite cost is treated as a completed computation.

Named persistent random tapes are essential. Resampling a new tape when a
history is replayed would describe a different resource and destroy lifetime
correlations.

## 6. Meters and grades

### 6.1 Ambient workload

An experiment has a public administrative workload parameter `b`. It is not a
cryptographic message and programs cannot read it. A fixed efficient context
chooses

```text
b = p(kappa + |a|)
```

for a fixed monotone polynomial `p` and auxiliary input `a`. More generally,
`b` can be a finite vector separating input volume, requested calls, and
available hardware. Scalar notation is used when no distinction matters.

The point of `b` is quantifier discipline. Different contexts may have
different polynomial degrees. A service's quota scales with the workload
chosen by the closed context, so it is not killed merely because another
context has a larger fixed polynomial.

### 6.2 Component grades

Each implementation occurrence `v` has a finite grade certificate

```text
F_v : (kappa,b) |-> B_v
```

where every coordinate of `B_v` is a monotone multivariate polynomial with
natural coefficients. The coordinates bound transitions, live cells, random
bits, produced/received traffic, activations, and named oracle calls.

The certificate is attached to the component occurrence in the final graph.
Alpha-renaming transports coordinates; parenthesization and construction
order do not change quotas. A fixed code may attempt to run longer, but its
meter stops it. Hence the efficient behavior is the behavior of the clocked
code, just as an ordinary PPT machine includes a clock.

### 6.3 Metered execution

Before executing a primitive action, the meter computes the next exact ledger.
If a quota would be exceeded, execution stops with lower-layer result
`Exhaust(v,c)`, where `v` is the alpha-invariant public owner and `c` is the
ledger accumulated so far. The result is not delivered to an ordinary system
port. Otherwise the primitive action occurs.

Every machine and routing transition consumes a positive time unit. Therefore
a finite time quota rules out actual micro-divergence in metered execution.
Oracle transitions are atomic but consume an oracle call and tariff; an oracle
that returns strict nonresponse yields `Block`, not a zero-cost infinite
transition.

The lower result type is:

```text
Success(y,c) | Block(v,c) | Exhaust(v,c).
```

The unbounded erasure keeps `y` from `Success` and maps both other outcomes to
strict nonresponse. A visible timeout is modeled only by an explicit timer
resource and an interface value.

### 6.4 Elementary metering theorems

**Theorem 1 - termination of metered machine execution.** For a fixed finite
transition quota, every machine-only macro execution reaches success, block,
or exhaustion after finitely many charged steps.

*Proof.* If success or block does not occur within the quota, the next
positive-cost transition would cross it and the meter returns exhaustion.

**Theorem 2 - budget monotonicity.** Let `B <= B'` coordinatewise. If a fixed
random-tape run succeeds under `B`, it follows the same small-step trace and
succeeds with the same output and successor state under `B'`.

*Proof.* Induct over the finite successful trace. Every prospective primitive
charge, reserve-evaluator envelope, or combined semantic/post-sample
administrative reservation tested on that trace fits under `B`, hence under
`B'`. Because the program cannot inspect the meter, the same transition is
selected at every prefix; fixed oracle seeds then select the same admitted
outcomes.

**Corollary 3 - stabilization.** For a finite unmetered fixed-sample run
`rho`, define `Need(rho)` as the coordinatewise maximum of every absolute
vector the meter would test along that trace: prospective primitive ledgers,
each reserve-evaluator envelope, the current ledger plus each combined
semantic/post-sample oracle reservation, and every other declared atomic
transaction reservation. It includes the final exact cost. Every
budget `B >= Need(rho)` yields the same metered success; if a metered run
succeeds, the unmetered run has the same success. In the machine-only model,
or with exact reservations, `Need(rho)=Cost(rho)`. In general only
`Cost(rho) <= Need(rho)`: an oracle may release unused reservation after
committing a cheaper sampled answer.

**Corollary 4 - divergence approximation.** A machine-only unmetered
micro-divergence or infinite hidden routing run exhausts every finite positive
time budget. Its budget-indexed approximants erase to nonresponse.

### 6.5 Closure and its limit

**Theorem 5 - polynomial boundedness of fixed metered graphs.** Let `N` be a
fixed finite graph whose component quotas and infrastructure quota are
polynomial in `(kappa,b)`. If `b=p(kappa+|a|)` for a polynomial `p`, every
closed metered run has polynomially bounded exact ledger.

*Proof.* Each coordinate is bounded by a finite sum or maximum of the
component and infrastructure quotas. Substituting the polynomial `p` into a
fixed multivariate polynomial remains polynomial. Connection can alter which
quotas are spent, but not their values.

This theorem includes feedback. A forwarding loop consumes activations,
traffic, and transitions until exhaustion. It does not establish that a
response occurs.

For a uniformly generated graph, per-node bounds are not enough: a generator
could create too many nodes or encode growing exponents. The generator must
provide a polynomial aggregate envelope for graph size plus all quotas. A
fixed universal component can instead encode logical sessions on persistent
tapes, avoiding dynamic physical nodes.

## 7. Uniformity and nonuniformity

### 7.1 Primary uniform presentation

A uniform implementation is one fixed finite graph template with fixed
machine codes, codecs, and polynomial grade transformers. Every machine sees
`1^kappa` on a read-only tape. Interfaces use identifiers inside messages if
the logical number of parties or sessions varies.

Each component's unary parameter tape is part of its initial native live
state: its `kappa` occupied cells and head contribute to `peak_v`, `gpeak`,
and the component space grade, and scans consume ordinary transitions. The
standard asymptotic experiment supplies this administrative input before the
first protocol activation. Physically distributing or sharing it is outside
protocol work in this presentation; a model in which that cost matters must
provide an explicit parameter-source or bus resource.

Unary representation is not cosmetic. If the parameter were supplied in
binary, a computation polynomial in its numerical value could be exponential
in the input representation. All polynomial statements below are in
`kappa`, equivalently in the length of `1^kappa`.

### 7.2 Generated network presentation

A generated family is a secondary presentation, not part of the primary
fixed-template carrier. It uses one fixed deterministic generator `G` that,
on `1^kappa`, emits a graph code in the language proved in
`generated-network-compiler.md`. The summary below records its profile
theorem; that note fixes the complete record grammar, validator, simulation
invariant, and random-tape splitter.

For `n >= 0`, let `gamma(n)` be Elias gamma encoding of `n+1`, of length

```text
2 floor(log_2(n+1)) + 1.
```

Encode a bit string `x` as `gamma(|x|) || x`, and encode a list by prefixing
its element count. After a fixed magic/version word, a graph code contains,
in this order:

1. a signature table;
2. a list of node records, each containing one encoded program, its grade
   identifier, public ownership identifier, and ordered typed ports;
3. a lexicographically ordered list of pairs of global port indices;
4. an ordered boundary list.

Node and port indices are their positions in the preceding lists, so duplicate
identifiers cannot occur. Polarity and signature compatibility, edge
disjointness, complete record consumption, and boundary status are checked by
the decoder. List positions are only administrative occurrence names:
alpha-isomorphic graphs need not have identical serializations, and no
uncharged graph-canonization algorithm is assumed.

The selected fixed multitape decoder scans the self-delimiting stream,
maintains unary-bounded index tables, and validates the sorted edge list.
Fix its finite scan/copy routine library, and let `c_dec,s_dec >= 1` be the
family-independent transition and scratch-space expansion constants obtained
when those routines are compiled to literal component-machine transitions.
On a code of length `L`, its conservative certified bounds are

```text
DecodeWork(L)  = 128 c_dec (L+1)^2,
DecodeSpace(L) = 16 s_dec (L+1)^2.
```

The numerical coefficients are part of this chosen elementary-routine
certificate, not machine-invariant claims. The proof allocates four
parsing/validation phases, at most `L` fields, and a bounded number of
at-most-`L`-cell scans per field. A dense endpoint-use table accounts for the
deliberately quadratic space bound. The symbolic constants can be computed
from a printed transition table; no theorem assumes they equal one.

The interpreter stores the decoded graph and the virtual configurations in
sequential tables. Let `W=P_native^work(kappa,b)`,
`A=P_native^act(kappa,b)`, `Q=sum_j P_native^calls_j(kappa,b)`, and

```text
H = 1 + W + A + Q.
```

This conservatively bounds component/router, activation, oracle-access, and
terminal-check slots. Normalize the aggregate profile by

```text
M = 1 + kappa + b + sum_x P_native^x(kappa,b),
```

where `x` ranges over every coordinate in the fixed dependency signature,
including tariff and oracle evaluator/receipt administration. Then
`W,A,Q,H<=M`, every virtual quota/counter is at most `M`, and `M` is a fixed
polynomial. The tempting live-dictionary estimate `L+W` is false for
a parameter-dependent multitape program: one native transition may move every
one of up to `L` tape heads of its owner. Moreover, compact declarations can
describe up to `L^2` tape headers across `L` nodes. A dense header directory
gives positional identities; fixed-alphabet unary intervals with in-place
head markers therefore need no repeated binary coordinate. After `W` native
transitions they have size `O(L^2+LW)`. Binary virtual quota and counter records add
`O(L log(M+1))`, so the complete state is safely
`O((L+M+2)^2)`. A bound in `W` alone would omit a large but mostly unused
workload-dependent quota.

One fixed master fair-bit tape is split pathwise into virtual node tapes using
Cantor's pairing function. The interpreter reads and caches the master prefix
needed for coordinates `(node-index, local-random-position)`; its length is
less than `(L+M+2)^2`, since every local random position is bounded by the
aggregate random envelope. Coordinate permutation preserves the independent
product Bernoulli law. A fixed private evaluator scans meter-only read-only
tracks `1^kappa` and `1^b`, evaluates the fixed grade library, and constructs
the binary quota table; the `M`-based physical profile includes their length,
heads, scan, and integer arithmetic. The generator sees only `1^kappa`, and
the evaluator never gives the workload or quotas to a simulated program.
Every decoded virtual component is nevertheless charged its own logical
`1^kappa` track and parameter head in the *virtual native* space ledger. The
universal interpreter may physically share the immutable contents and store
only the virtual heads; its physical profile is allowed to differ. The
aggregate native space certificate, and hence `M`, includes the logical
per-component tracks.

A fixed named stateful oracle needs a private accounting path. Its ordinary
reply need not expose the next public contract coordinate on which the exact
tariff depends, so the interpreter cannot reconstruct the virtual ledger from
the reply alone. For every fixed oracle dependency, the compiled template
therefore has one fixed `OracleProxy`. It checks the virtual reservation
before a physical seed is touched, makes exactly one unchanged physical call
on virtual admission, and receives a private authenticated commit receipt
from the access accountant containing the reply/block tag, exact charge, and
next public coordinate. It mirrors these into the virtual ledger and gives
decoded code only the ordinary reply. Initial public coordinates use the same
meter-level face. The receipt codec, validation, traffic, work, and transient
space are charged; the aggregate physical access envelope prevents a new
post-admission exhaustion. This is fixed administrative infrastructure, not a
generated oracle or a cost side channel to the simulated program.

The baseline invariant assumes the stateful occurrence is private to the
compiled subsystem. If it is intentionally shared with an outside caller,
one fixed charged multi-client `OracleProxy` must mediate every caller and
mirror every committed public-coordinate update before the next virtual
reservation. A direct bypass could leave the interpreter's cached coordinate
stale and is not covered by the compiler theorem.

Including that evaluation,
program lookup, virtual tapes, bit-costful routing, meter simulation, and
paired-bit retrieval, the fixed component uses at most, for fixed
family-independent routine-compilation constants
`c_eval,s_eval,c_int,s_int >= 1`,

```text
EvalWork(L,M)
  = 128 c_eval (L+M+2)^2,

EvalSpace(L,M)
  = 16 s_eval (L+M+2)^2,

InterpretWork(L,H,M)
  = 8192 c_int H (L+M+2)^2,

InterpretSpace(L,M)
  = 256 s_int (L+M+2)^2.
```

The constants allocate a fixed number of complete scans per primitive action,
including private oracle-receipt validation. Bit-costful output and router
instructions are included in `W`; the
interpreter cannot emit an `ell`-bit value in fewer than `ell` simulated
output instructions. The simulation relation preserves the virtual state,
meters, specification public coordinates, terminal status, native ledger, and
boundary transcript at every native step. It does not identify native
physical cost with interpreter physical cost.

Consequently, if the generator has work bound `g_work(kappa)`, graph-code
length bound `g_len(kappa)`, and the generated graph has aggregate native
profile `(P_native^x)_x`, put `L=g_len(kappa)`,
`H=1+W+A+Q`, and `M` as above. The fixed interpreter has the
explicit work envelope

```text
g_work(kappa)
+ 128 c_dec (L+1)^2
+ 128 c_eval (L+M+2)^2
+ 8192 c_int H(L+M+2)^2
```

and space envelope

```text
g_space(kappa)
+ 16 s_dec (L+1)^2
+ 16 s_eval (L+M+2)^2
+ 256 s_int (L+M+2)^2.
```

Both are polynomial when the displayed functions are fixed polynomials.
Pathwise, the master tape induces the decoded graph's named random tapes by
the pairing map, and the interpreter produces the same external transcript
and virtual status. Its physical ledger is the displayed reindexed profile,
not the native graph ledger.

Initialization is lazy rather than free precomputation. On the first external
activation, a fixed boundary staging face retains the routed event while the
universal component generates and validates the graph and evaluates virtual
grades. The header then permits the exact prospective virtual activation
check. A rejected event is never installed and receives the virtual target's
owner/status; an admitted input is bounded by the native space coordinate in
`M` and is copied once. The staging buffer is funded by the final route-safe
envelope, or by a separately supplied external-event envelope outside that
subalgebra; an arbitrary context value is not bounded by the challenged
resource's native profile. An `initialized` bit ensures this occurs once;
decoded state, meters, and the random cache persist thereafter. If the system
is never activated, it performs no hidden work. The selected model has no
spontaneous pre-input output; such behavior would need an explicit initial
token or initialization port.

The following are charged:

- transitions, space, and randomness used by `G`;
- the generated code and graph length;
- validation and port-resolution work;
- grade evaluation and quota-table storage;
- universal interpretation and routing;
- oracle-proxy receipt codecs, validation, work, traffic, and transient state.

Per-node bounds are insufficient. The generator's certificate must bound
`g_len` and the *sum/max aggregate* `P`; otherwise it could emit exponentially
many constant-time nodes or node annotations whose polynomial exponents grow
with `kappa`.

This completes the generated-to-fixed simulation for the selected graph
language and deliberately crude interpreter. Generated graphs remain a
presentation convenience. The theorem applies to generated implementation
nodes and requires one fixed external boundary. The fixed universal component
emits the same self-delimiting boundary event directly; output work is already
inside the interpreter bound. Fixed named specification oracles remain
external dependencies with unchanged state and kernels, rather than generated
as new ideal resources. Their fixed administrative proxy mirrors meter-level
commit information into the virtual ledger without revealing it to decoded
code. A stored virtual continuation routes the next ordinary response back to
the suspended virtual node in the one-token semantics. The primary definition
of a uniform implementation continues to be one fixed template, so no later
theorem depends on a choice of universal code.

### 7.3 Polynomially many copies and hybrids

There are two different claims often hidden by the phrase “polynomially many
components.”

**Logical copies in one fixed template.** A fixed machine code can maintain a
table of `q(kappa)` logical sessions and iterate a fixed protocol body over
them. Let `P_s(kappa,b,L_s)` be one fixed per-activation profile for that
body, let `A(kappa,b)` bound the total session activations, and let
`L_s(kappa,b)` bound a record length. A simple sequential-table dispatcher
uses at most

```text
16 q(kappa)(L_s(kappa,b)+log_2(q(kappa)+1)+1)

+ 32 A(kappa,b) q(kappa)
     (L_s(kappa,b)+log_2(q(kappa)+1)+1)
```

charged bit operations, and aggregate work is bounded by that table cost plus

```text
A(kappa,b) P_s(kappa,b,L_s(kappa,b)).
```

The linear `q` factor per dispatch is intentional: a sequential multitape
machine has no free random-access table. All four functions and the table
algorithm are fixed syntax; an indexed list of unrelated `P_i` would hide
nonuniformity. This is a primary fixed-template implementation; `q` is loop
data, not a parameter-dependent graph syntax.

**Physically generated copies.** A generator may instead emit `q(kappa)`
node records and their edges. It is uniform only under Section 7.2's code
length, generator cost, and aggregate-quota certificate. The explicit
interpreter bound then converts it to the primary presentation.

Similarly, a polynomial hybrid argument does not quantify over an arbitrary
family of hard-coded experiments. It requires one fixed uniform hybrid
generator `H(1^kappa,i)` for

```text
0 <= i <= q(kappa).
```

If one negligible `epsilon(kappa)` bounds *every* adjacent pair for the
reindexed profile produced by `H`, uniformly over
`0<=i<q(kappa)`, then

```text
Delta(H_0,H_q) <= q(kappa) epsilon(kappa)
```

by the triangle inequality. Negligibility follows for fixed polynomial `q`.
Uniform generation, profile bounds, and the uniform adjacent envelope are
premises; the hybrid lemma does not create them.  Pointwise negligibility for
each fixed natural index is insufficient because the worst index may move
with `kappa`.

### 7.4 Nonuniform variant

A nonuniform implementation is a fixed network template with advice
`z_kappa`, where `|z_kappa| <= p(kappa)` for a fixed polynomial. The advice
family is part of the object. Nonuniform computational security quantifies
over corresponding advice-bearing distinguishers.

An arbitrary family `(N_kappa)` is not an efficient family. Without a
generator or advice bound, `N_kappa` can hard-code the `kappa`th bit of the
halting set and answer it in constant runtime.

## 8. Abstract specifications as charged oracles

### 8.1 Why two sorts are necessary

Requiring every ideal resource family to be implemented by a uniform PPT
would exclude or misdescribe standard specifications. A random oracle, an
ideal sampling functionality with an exact real-valued law, or a trusted
channel can be efficiently queried even when the theory does not posit an
implementation of its hidden state transition.

The lower layer therefore has:

- an **implementation sort**, consisting of finite machine codes, exact
  ledgers, and grade certificates;
- a **specification sort**, consisting of abstract random-system families,
  effective wire encodings, measurable conditional behavior, and access
  tariffs.

Only the first sort is called efficiently implementable.

### 8.2 Oracle tariff

For each named oracle `O`, let `S_O` be a standard-Borel state space, let
`Q_O` and `R_O` be countable sets of finite prefix-free encoded queries and
responses, and let

```text
K_O : S_O x Q_O
        -> Prob((R_O x S_O) + Block(S_O))
```

be a measurable Markov kernel. A reply or block may update the persistent
oracle state. The state exposes only a declared public contract coordinate;
the meter does not compute it by traversing hidden state. For pathwise proofs,
choose a measurable standard-Borel randomization of `K_O` and one named iid
uniform seed sequence per oracle occurrence.

For a sampled reply or block with next state `s'`, its **public charging
view** contains only the reply/block tag and finite code together with the
next public contract coordinate. The kernel maintains that coordinate; the
caller receives only an ordinary reply and neither the caller nor tariff
evaluator receives an encoding of hidden `s'`.

The access contract contains an exact, publicly evaluable charge

```text
tau_O(kappa,b,current-public-summary,query-code,
      public-charging-view)
```

and, for the baseline exact-call rule, a query-only reservation envelope

```text
reserve_O(kappa,b,query-code,public-state-summary)
  >= tau_O(kappa,b,public-state-summary,query-code,view(z))
```

for every hidden state compatible with the public summary and every outcome
`z` in the selected randomization's range. The tariff has coordinates for:

- one admitted call;
- query serialization/access traffic;
- response serialization/access traffic;
- any public access latency or monetary charge.

It dominates the encoded query and response lengths. The calling
implementation must have enough remaining oracle and traffic quota for the
*reservation before the kernel is sampled*. The oracle never returns fresh
computational credit. Local processing of the response consumes the caller's
own transition and space quotas. Ordinary physical-edge routing remains in
the canonical ledger; an API-specific tariff may add a different access
coordinate, but one declared profile never counts the same transfer twice.

For the strong samplewise theorem, the selected randomization produces only
outcomes dominated by the reservation for every seed, including null seeds.
A kernel-almost-sure envelope would prove only an almost-sure metering
statement. The public reservation and tariff evaluators are effective and
their fixed profiles are charged locally or declared as administrative meter
work; they are not free noncomputable branch tests.

Charging these evaluators requires a transactional order. A public
`EvalReserve_O` envelope is checked before the deterministic reservation
evaluator runs. After that evaluator returns, the meter jointly checks the
semantic reservation and a public `PostReserve_O` envelope dominating every
response-dependent charge-evaluator, record-construction, and commit action.
Peak coordinates use prospective maxima; cumulative coordinates add. Only
then is a fresh kernel seed consumed. Thus no supposedly charged evaluator
can exhaust after sampling and silently create a response-dependent failure
branch.

The exact order of one atomic call is:

1. the caller pays its local work for constructing and serializing the query;
2. the meter checks `EvalReserve_O`; rejection touches no evaluator, seed, or
   hidden oracle state;
3. under that capability the total deterministic evaluator computes
   `reserve_O` without reading hidden state or a fresh sample;
4. if the semantic plus `PostReserve_O` reservation does not fit, the whole
   closed execution terminates in `Exhaust`; the kernel is not sampled,
   oracle state is unchanged, and no response is revealed;
5. if it fits, sample exactly once from `K_O(s,q)` and run the total
   response-dependent charge evaluator under the admitted capability;
6. atomically commit the sampled next state, exact tariff, and exact evaluator
   ledger, and deliver the finite response; or commit the sampled block-state
   and terminate in `Block`;
7. unused reserved capacity is released only in the external meter. Programs
   cannot observe it.

The admission decision is independent of the sampled response. Conditional
on admission, the delivered response and next state therefore have exactly
kernel law `K_O(s,q)`, rather than that law conditioned on a cheap response.
There is no rollback or resampling.

Treating a call as one ordinary machine step without this separation is
unsound. A one-bit query could request an exponentially long answer or the bit
of a nonrecursive language, turning hidden oracle work into free local power.

Response-dependent sample-then-check is also unsound as an exact-oracle rule.
For a fair-bit oracle, set tariff `1` on response `0`, tariff `2` on response
`1`, and give the caller one unit. Sampling and returning only fitting replies
makes every successful response `0`. Retrying after rollback removes even the
exhaustion branch and replaces the fair law by the point mass at `0`.
Query-only reservation `2` either admits the original fair call or rejects it
before sampling.

### 8.3 Oracle probability and partiality

The operational machine configuration space is countable under the selected
finite encodings. Meter states are countable vectors of natural numbers.
With standard-Borel oracle state, the product configuration space is
standard Borel. The pre-admission set

```text
{ (s,q,B) : reserve_O(kappa,b,q,u(s)) <= B }
```

is measurable by assumption. On that set, pushing `K_O` through the measurable
commit-and-deliver map gives the next-configuration kernel. On its complement
the next result is the deterministic `Exhaust` point. This piecewise
construction is a Markov kernel.

Every charged machine transition has a deterministic kernel and every oracle
call has the kernel just defined. Sequential kernel composition therefore
defines a unique law on every finite execution prefix. A finite positive work
meter makes the number of machine steps finite; a finite call coordinate makes
the number of oracle kernels finite. Thus the complete terminal experiment
kernel is well-defined. Extending compatible finite transcript laws to an
unbounded lifetime uses the same standard-Borel/projective carrier as the
unbounded layer; it is not needed merely to define one metered experiment.

Machine tapes and named oracle seed sequences are independent by default. Correlated
randomness is represented by a named common specification node. An admitted
call consumes exactly one kernel sample. A rejected reservation consumes none.
Because rejection is terminal this convention cannot be probed by a later
call, but fixing it is necessary for pathwise comparison and converter
absorption.

If response lengths have unbounded support, no finite response-independent
reservation can dominate their serialization cost. Such an oracle is not an
exact bounded-call oracle under the baseline rule. There are two honest
alternatives.

1. Change the specification so that the query contains a public length cap and
   the kernel returns a declared overflow outcome. This is a different
   resource.
2. Use a stateful streaming kernel plus a fixed metered reassembly converter.
   Sample the response and next state exactly once, commit that sample, and
   reveal fixed-size chunks under query-only per-chunk reservations. The
   converter retains the one token, stores charged chunks, and emits one event
   on the original interface. If a later chunk, local work, or buffer
   allocation does not fit, terminate in `Exhaust`; never roll back or
   resample. After hiding the chunk interface, the erased distance from the
   original oracle is at most the probability that the sampled encoding
   exceeds the available chunk/work/space budget.

Conditioning only on completed streaming calls generally biases toward short
responses. No theorem uses that conditional law. Instead, no-exhaustion
supplies an explicit tail bound, and the coupling inequality charges that
bound as an implementation failure.

The `GeoBits` instance completes this calculation for one unbounded law.
Sample `Pr[L=ell]=2^(-ell-1)`, choose `U` uniformly in `{0,1}^L`, and encode
the response as the prefix code `1^L 0 U` of length `2L+1`.  With chunk size
`c=2*kappa` and `Q=b+1` chunks, all call, traffic, copy/output work, and space
profiles are fixed polynomials.  Reassembly fails only if
`L >= kappa*(b+1)`, whose exact probability is
`2^(-kappa*(b+1))`.  `Start` commits the same sample on both sides and is
never retried, so this is an exhaustion tail rather than a conditional
short-response law.

## 9. Denotation into random systems

### 9.1 Costed and metered macro transitions

For fixed machine tapes and fixed selected oracle seed sequences, the exact-cost macro
transition is a partial map

```text
delta-cost : (state,input)
          -> (state,output,ledger-increment).
```

The metered transition at `(kappa,b)` is total into the lower result type:

```text
delta-metered :
  (state,meter-state,input)
    -> Success(state,meter-state,output)
     | Block(meter-state)
     | Exhaust(meter-state).
```

Folding successful transitions over histories gives a DDS on the ordinary
wire alphabet. A history ceases to be in the domain at the first block or
exhaustion. Thus every fixed-tape metered implementation is already an
ordinary partial DDS after erasure.

Let

```text
[[N]]_(kappa,b)
```

denote the random system obtained by pushing machine and oracle randomness
through the metered history map and taking the transcript quotient.

For implementations, there is also an unmetered denotation
`[[N]]_(kappa,infinity)`. It is notation for the original operational
semantics, not a completed infinite-budget machine.

### 9.2 Forgetful diagram

The intended chain is:

```text
machine graph with exact trace
  -> metered machine graph at (kappa,b)
  -> law over partial DDSs
  -> transcript quotient / random system
  -> AC resource
```

There are two forgetful maps.

- Erasing the ledger but retaining meter-induced nonresponse gives the
  budget-indexed random system.
- Erasing the meter as well gives the unbounded implementation behavior on
  every trace that terminates successfully before a finite cost.

The second map is not extensional equality between an arbitrary clocked
program and its unclocked code. A program that always exceeds its quota is a
partial metered implementation even if its unclocked code eventually answers.
The stabilization theorem states the precise relation through the high-water
funding requirement `Need`. The final committed ledger alone is sufficient in
the machine-only model but need not fund a public pre-sample oracle envelope.

### 9.3 Structural operations

Renaming transports graph names, ledger coordinates, and tariffs.
Independent parallel is disjoint graph union with separately named machine
random tapes and the product tape law. Connection adds one typed edge and
charges its canonical routing. Feedback is the same operation when the edge
creates a cycle.

An arbitrarily underfunded structural router cannot map to cost-free strict
DDS feedback: it could create a new nonresponse. The selected *route-safe*
subalgebra therefore gives every canonical physical matching a derived
aggregate envelope dominating all machine-emitted events and all tariffed
specification traffic. Routing remains in the exact ledger but cannot be the
first exhausted occurrence. A genuinely bandwidth- or memory-limited link is
an explicit resource node, so its failure remains in the denotation.

For fixed tapes, oracle seeds, and initial specification states, exact traces
of a route-safe graph obtained by wiring agree with the strict
first-visible-output evaluator on its denotations. Component and specification
meter states agree; finite physical routing steps correspond to one hidden
expansion step and are unobservable. Pushforward gives:

```text
[[rename N]] = rename [[N]]
[[N parallel M]] = [[N]] parallel [[M]]
[[connect N]] = connect [[N]].
```

The first two are direct pathwise theorems. The third is proved in
`partial-random-system-bridge.md` for the selected standard-Borel
maximal-transcript carrier. Comparison with another independently fixed
carrier remains conditional on that carrier choosing the same strict
nonresponse and feedback convention.

### 9.4 The finite costed operational carrier

The cost-aware lower algebra can be completed without first identifying it
with the abstract random-system feedback operator.  The full quotient and law
proof is recorded in `costed-operational-algebra.md`; this section summarizes
the construction.

Fix a boundary type `B`, a parameter `(kappa,b)`, and an
isomorphism-invariant public report map

```text
report : exact ledger -> public cost report.
```

The maximal report may retain aggregate work, traffic, random bits, peak
space, activations, and per-public-oracle calls. Internal occurrence names are
not observable as raw strings: alpha-isomorphic graphs induce a coordinate
bijection before `report` is applied.

A deterministic costed lifetime behavior returns, on every admissible next
input, one of

```text
Ok(transcript,test-observation,report(lifetime-ledger))
Stop(Block,owner,transcript,test-observation,report(lifetime-ledger))
Stop(Exhaust,owner,transcript,test-observation,report(lifetime-ledger)).
```

`owner` is an alpha-invariant public attribution class for the first blocking
or exhausted occurrence, not its internal name. `Stop` is terminal. A finite
meter makes this response relation total at the lower level. A cost-aware
context may branch on the status, owner, and public report.
An ordinary behavioral context retains the visible prefix and its own
designated terminal observation but not the report or stop reason; both
terminal statuses erase to the same maximal outcome
`NoResponse(transcript,test-observation)`. This is a semantic observation used
to compare transcript laws, not a visible wire symbol that a program may
receive.

Let `Graph^cost_(kappa,b)(B)` be the finite normalized open graphs with
boundary `B`, implementation nodes, and admitted tariffed specification
nodes. For the machine-only carrier, every closed experiment law is already
well-defined. For the oracle-extended carrier this statement uses the
pre-reserved tariffed-kernel semantics in Section 8.

Define costed contextual equivalence by

```text
G ~=cost H
```

exactly when every compatible finite cost-aware graph context with a total
semantic decision rule has the same decision distribution on `G` and `H`.
Define behavioral equivalence `~=beh` in the same way but restrict to
observations that factor through cost erasure.  The decision supervisor is
outside the ordinary wire alphabet, so totality does not turn nonresponse into
an `Err` message.

The pointwise carriers are the quotients

```text
R^cost_(kappa,b)(B)
  = Graph^cost_(kappa,b)(B) / ~=cost,

R^beh_(kappa,b)(B)
  = Graph^cost_(kappa,b)(B) / ~=beh.
```

Because every behavioral context is a cost-aware context that ignores its
extra input,

```text
G ~=cost H  =>  G ~=beh H.
```

Hence

```text
U : R^cost_(kappa,b)(B) -> R^beh_(kappa,b)(B),
U([G]_cost) = [G]_beh
```

is a well-defined erasure map. On the route-safe subalgebra, the later map
from `R^beh` into the selected partial-random-system carrier is the proved
homomorphism `J` summarized in Section 9.7.

For a selected context class `C_P` bounded by profile `P`, the cost-aware
pseudometric is

```text
d^cost_P(G,H)
  = sup_{D in C_P}
      |Pr[D[G]=1] - Pr[D[H]=1]|.
```

Symmetry and the triangle inequality hold pointwise before the supremum.
Zero distance yields the corresponding restricted observational quotient.

### 9.5 Graph normalization

An open operational graph consists of finite node and port occurrence sets, a
partial matching of compatible opposite-polarity ports, and a typed boundary.
The normalized presentation applies the following rules.

1. Internal node, port, state, and tape names are quotiented by typed
   alpha-isomorphism.
2. A bare wire is a typed bijection between two administrative boundary
   faces, not a relay node and not an arbitrary port equality. Consecutive
   aliases are fused by ordinary function composition; this cannot encode
   fanout.
3. After alias fusion, each remaining component-to-component or
   boundary-to-component connection is represented by one edge. Its traffic
   and canonical routing are charged once.
4. An explicit delay, copier, repeater, router, or physical link is a node or
   specification resource and is never erased by normalization.
5. Node records, ports, edges, and boundary occurrences receive their
   canonical order only for serialization. The mathematical graph remains an
   isomorphism class.

Alias fusion is terminating because every rewrite removes one bare-wire
occurrence. It is confluent because typed bijection composition is
associative; every order computes the same composite map on a maximal alias
chain. Thus normalization is unique up to the typed graph isomorphism already
being quotiented.

This convention resolves the identity-cost problem. Attaching an identity
does not add a transition, quota, or second routing charge. It merely changes
the presentation of an existing boundary incidence. Physical transport costs
must be represented explicitly if they are intended to survive identity
normalization.

### 9.6 Pointwise constructor laws

On normalized finite graphs define:

- `rho G` by a typed boundary renaming `rho`;
- `G tensor H` by alpha-disjoint union;
- `connect_(p,q)(G)` by adding one compatible matching edge and hiding
  endpoints `p,q`;
- `alpha G` by disjoint union with converter graph `alpha`, connection of its
  inner boundary to the selected boundary of `G`, and normalization;
- `id_A` by the bare boundary alias on interface `A`.

The following laws hold as equalities of normalized graph isomorphism classes,
and therefore as equalities in both contextual quotients.

**Renaming.**

```text
id G = G,
(rho_2 o rho_1)G = rho_2(rho_1 G).
```

**Symmetric parallel monoid.**

```text
(G tensor H) tensor K ~= G tensor (H tensor K),
G tensor H ~= H tensor G,
G tensor empty ~= G.
```

The isomorphisms transport independently named tapes and exact ledger
coordinates. Shared coins require an explicit common resource and are not
created by the symmetry.

**Disjoint connection order.** If `e` and `f` are legal disjoint new edges,

```text
connect_e(connect_f(G))
  ~= connect_f(connect_e(G)).
```

More generally, every sequence of legal connections producing the same final
typed matching yields the same normalized graph. This includes cyclic
feedback. It is a structural bounded-execution law, not a productivity claim.

**Converter action.**

```text
id_A G ~= G,
(alpha beta)G ~= alpha(beta G),
(alpha tensor beta)(G tensor H)
  ~= alpha G tensor beta H
```

for compatible disjoint interfaces. Each equation follows because the two
terms have the same union of nodes and the same final matching after alias
normalization.

**Context congruence.** If `G ~=cost H`, then `C[G] ~=cost C[H]` for every
compatible finite cost-aware context `C`. Given any closing test `D` for
`C[G]`, the composite syntax `D[C[-]]` is a closing test for `G`; apply the
definition of contextual equivalence. The same proof holds for `~=beh`.

**Erasure homomorphism.**

```text
U(rho G)             = rho U(G),
U(G tensor H)        = U(G) tensor U(H),
U(connect_e G)       = connect_e U(G),
U(alpha G)           = U(alpha) U(G),
U(id_A)              = id_A.
```

These are operational constructor equalities: erasure changes result
observations but neither nodes nor wiring. Identifying the right-hand
behavioral connection with cost-free strict feedback requires route-safe
canonical plumbing; Section 9.7 proves that theorem for the selected target.

**Profile-reindexed nonexpansion.** If absorbing converter `alpha` maps
profile class `P` into `T_alpha(P)`, then

```text
d^cost_P(alpha G, alpha H)
  <= d^cost_(T_alpha(P))(G,H).
```

Every left-hand test becomes the same normalized closed graph after absorbing
the converter into the test. No probability or asymptotic argument is needed.

These laws complete the finite costed operational system algebra, including
its oracle extension under Section 8's standard-Borel kernel, measurability,
finite-call, and pre-sample reservation hypotheses.

### 9.7 Route-safe partial-random-system bridge

`partial-random-system-bridge.md` fixes the remaining selected carrier. For
countable `X,Y`, partial DDSs form a Borel subset of

```text
(Y + {undefined})^(X^+).
```

A maximal transcript is either an infinite query-answer stream, a finite
environment stop, or a finite system stop retaining the unanswered query.
Probability laws on partial DDSs are observationally equivalent when these
maximal-transcript laws agree for every deterministic environment.

Strict connection is measurable: a finite visible answer is the countable
union over finite hidden expansion strings of DDS evaluation cylinders.
Congruence follows by lifting every environment for a connected system to an
environment for the unconnected system and applying a measurable hiding map.

The canonical route-safe envelope is derived from aggregate machine-work,
oracle-call, and oracle-traffic grades. It dominates router event count,
work, traffic, and the one live buffer. Hence the router is fully accounted
for but never introduces behavior absent from strict DDS feedback. Limited
communication remains an explicit resource.

At fixed `(kappa,b)`, finite operational contexts are pointwise complete for
the target quotient: every finite maximal-transcript cylinder uses only
finitely many encoded queries and responses and is implemented by a finite
lookup context with a sufficiently large constant grade. Conversely, a
behavioral context conditioned on its tapes, oracle seeds, and initial
specification states is a deterministic partial environment plus a semantic
score. This proves

```text
G ~=beh H  iff  J(G)=J(H)
```

for route-safe graphs, and yields the injective homomorphism

```text
R^cost_rs --U--> R^beh_rs --J--> RS_partial.
```

The finite common-domain PDS presentation embeds exactly. A carrier using a
different observation for nonresponse or different feedback remains a
separate comparison problem, not an unfinished operational theorem.

## 10. Efficient distinguishers

### 10.1 Uniform cost-aware tests

A pure uniform cost-aware distinguisher consists of:

1. one fixed metered network code `D`;
2. a fixed polynomial ambient-workload policy `p_D`;
3. either no auxiliary input or one produced by a fixed uniform generator;
4. one fixed uniform graded terminal-scorer code and a fixed default bit.

On parameter `kappa` and generated public input `a`, it interacts with the
challenge at workload

```text
b = p_D(kappa + |a|).
```

After interaction ends, the scorer receives a self-delimiting encoding of the
terminal data it is permitted to inspect. Its input reading, work, and space
are charged in the distinguisher profile. If the scorer blocks or exhausts,
the fixed default bit completes the experiment. A cost-aware scorer may
inspect the retained finite transcript, the test's designated terminal
observation, the lower stop reason and owner, and the public report. A
behavioral scorer receives only the image under erasure: it retains the
visible prefix and its own observation but identifies both stop reasons with
strict nonresponse and cannot read the report.

In the uniform cost-aware class, both the projection of the test's own
terminal configuration and the public-report projection are one fixed uniform
effective code (or canonical projections onto declared accessible
context/ledger coordinates), with certified polynomial evaluation and output
length. Record construction and scorer execution are charged. The profile
carries a whole-terminal-record-length bound so converter absorption also
accounts for a larger context observation or report.

The report read by the scorer is the interaction-phase report, frozen before
postprocessing begins. Report-projection and scorer work count toward test
admissibility, but are not recursively inserted into the value currently
being scored. If a concrete deployment wants a final audit containing
postprocessing cost, it can append that record after the decision without
changing the decision experiment.

The *pointwise* contextual quotient deliberately allows every total
measurable terminal bit map. That is an information-theoretic way to say that
the complete finite outcome laws are equal. It is not the computational test
class. Giving an arbitrary measurable supervisor or terminal-state projection
to a purported PPT distinguisher would supply a free noncomputable predicate
of its configuration, transcript, or report. The effective record constructor
and fixed graded scorer close that loophole.

Post-run scoring is a semantic completion of a bounded experiment, not a
message returned by the challenged resource. It cannot create a response or
continue the interaction. A security statement must name whether it uses the
costed or behavioral terminal record.

### 10.2 Advantage and uniformity in auxiliary input

For resources `R` and `S` with the same encoded boundary, define

```text
Adv(D,R,S;kappa,a,b)
  = | Pr[D^b(R,kappa,a)=1]
      - Pr[D^b(S,kappa,a)=1] |.
```

For *auxiliary-input security*, require for every uniform graded `D`, every
polynomial workload policy, and every polynomial auxiliary-input bound that

```text
sup_{|a| <= q_D(kappa)}
  Adv(D,R,S;kappa,a,p_D(kappa+|a|))
```

be negligible in `kappa`.

This supremum prevents a security claim from hiding a bad auxiliary string.
It also permits an arbitrary bad string to be selected separately at every
`kappa`; in that sense it has nonuniform/advice strength despite the fixed
code of `D`. Pure uniform security instead omits arbitrary auxiliary input or
requires one fixed deterministic polynomially graded generator. Its work,
space, polynomial output length, retained output, and installation are part
of the test's initialization profile, and it cannot inspect the ambient
workload that will be selected from its output length. A third variant
explicitly permits polynomial advice or circuit families, with a named
combined input/advice length bound. Supplied auxiliary input or advice has no
generation cost but does occupy, traverse, and validate charged storage and
traffic. The three modes must not share the same label.

The definition can be concrete: keep `kappa`, the complete budget vector, the
oracle query profile, and the numerical advantage. The negligible relation is
its asymptotic quotient.  For an input mode `M`, let `A_(D,M)(kappa)` be the
singleton uniformly generated input in pure mode, the set of all strings of
length at most `q_D(kappa)` in bounded auxiliary-input mode, or the singleton
named input/advice in explicit nonuniform mode.  Its exact order is

```text
for every fixed (D,p_D), there exists negligible nu_(D,p_D)
such that
  sup_{a in A_(D,M)(kappa)}
    Adv(D,R,S;kappa,a,p_D(kappa+|a|))
  <= nu_(D,p_D)(kappa).
```

The negligible envelope may depend on both the fixed code and its fixed
workload policy, but not on `a` or `kappa`.  There is no pointwise supremum
over all polynomial codes or policies.

### 10.3 Why an extensional efficient-system predicate is insufficient

An extensional random system has no unique runtime. Two machines with the
same transcript law can differ by an arbitrary delay or by unused
exponential computation. Conversely, a noncomputable history function has no
finite implementation even if its lookup table at each fixed parameter is
finite.

Efficiency therefore belongs to implementation codes and their grades.
Computational indistinguishability belongs to resource families plus a class
of such coded tests. These are different predicates.

## 11. Converter and reduction accounting

### 11.1 Graded converters

A converter is a metered implementation graph with outer and inner typed
ports. Its grade includes a monotone polynomial transformer

```text
T_alpha :
  (outer workload and decision budget)
     -> (local transitions, space, randomness,
         inner traffic, inner activations, oracle calls).
```

At fixed `(kappa,b)`, the component quota is obtained by evaluating this
transformer. A converter making hidden calls still satisfies the finite
hidden-query requirement because its call coordinate is finite. The bound is
uniform in the sequence of answers: it comes from the meter, not from
termination observed on one favorable resource.

Sequential converter composition is graph connection. Its transformer can be
bounded by polynomial substitution and addition. Parallel converter
composition combines independent coordinates and shared infrastructure
costs. The identity is a bare typed wire, not a relay machine. Normalization
fuses consecutive bare wires, so inserting identity syntax creates no
component and no new quota. Physical transport is charged once to the edge or
explicit communication resource in the normalized graph.

### 11.2 Exact absorption theorem

Let `D` interact with `alpha R`. Form a new distinguisher `D[alpha]` by
placing the exact converter occurrence between `D` and its challenge port.
Transport the same machine random tapes, selected oracle randomizations and
seed sequences, meters, public ownership labels, and routing codes. Absorption
does not relabel the converter from “protocol” to “context”; ownership is
semantic accountability data, not syntax-tree containment. In the route-safe
subalgebra, both presentations also derive the same canonical-router envelope
from the same final aggregate graph. Then for every fixed parameter,
auxiliary input, and ambient workload:

```text
Pr[D(alpha R)=1] = Pr[D[alpha](R)=1].
```

This equality is syntactic and pathwise before probability. The ambient
workload index `b` can remain the same, because the graphs are literally the
same. Their certified *aggregate cost profile* is not generally the original
distinguisher profile. It is bounded by

```text
Profile_(D[alpha])(kappa,b)
  <= T_alpha(Profile_D(kappa,b))
```

after adding the universal-simulation, routing, terminal-record-length, and
report/scorer coordinates selected by the cost model. In particular,
absorption may enlarge the encoded report; that input growth is part of
`T_alpha`, not free postprocessing.

Taking suprema over distinguishers admitted by a concrete profile gives
profile-reindexed nonexpansion:

```text
Delta_Profile(alpha R, alpha S)
  <= Delta_{T_alpha(Profile)}(R,S).
```

Likewise, emulating a parallel resource `Q` transforms the budget by its
access profile. This is the costed operational form of Jost's reduction
relaxation.

### 11.3 Asymptotic closure

If `b=p(kappa)` is polynomial and `T_alpha` is a fixed multivariate
polynomial, then `T_alpha(kappa,p(kappa))` is polynomial. Hence an efficient
converter can be absorbed into an efficient distinguisher.

If `epsilon(kappa)` is negligible, multiplying it by a fixed polynomial
number of hybrids leaves it negligible. Sequential construction adds
advantages and composes budget transformers. The familiar asymptotic
composition statement is therefore a corollary of:

- algebraic composition at each parameter and budget;
- polynomial closure of transformer substitution;
- the triangle inequality;
- closure of negligible functions under polynomial factors.

Concrete security should stop one step earlier and report the transformer.
A reduction with running time `2^kappa`, exponentially many oracle queries,
or an enormous success-probability loss is not useful merely because its
extensional converter exists.

#### Specification-level uniformity

Elementwise closure is not yet a theorem about arbitrary sets of resource
families. Jost's parallel relaxation has the form

```text
epsilon^S(D) = sup_{S in S} epsilon(D[. || S]).
```

The supremum is inside the error function. For each fixed natural `n`, the
function `eta_n(kappa)=1[kappa=n]` is negligible and is implemented by a
fixed uniform machine with `n` hard-coded. Yet
`sup_n eta_n(kappa)=1` for every parameter. Thus “every member is an
efficient uniform family” does not supply a uniform negligible error over a
specification.

A specification-level theorem therefore carries a uniform presentation
certificate: one selector/compiler (or one indexed ideal package), a
polynomial descriptor bound, one aggregate profile, the fixed dependency
signature, and one negligible envelope after the supremum over allowed
descriptors. A concrete bound uniform over that aggregate profile is an
equivalent sufficient witness. A fixed finite specification is the special
case where the maximum of finitely many memberwise negligible bounds remains
negligible. Sequential and parallel specification composition must compose
these presentation and error witnesses, not only their individual resource
graphs.

### 11.4 Simulator cost

A simulator is just another graded converter. Its local transitions,
persistent space, random bits, traffic, and oracle calls appear in the ideal
experiment profile. There is no separate convention under which simulator
work is free.

If the statement intentionally treats computation as a supplied resource, the
simulator's requirement can be moved to the ideal-side specification.
MauRen16, Section 4.3, demonstrates the abstract refactoring by replacing a
computational simulator system `beta` with a parallel behavioral resource
`beta_bar` and a trivial connector. It does not require this presentation for
every concrete-security theorem and does not select a processor API. If the
statement instead uses the free-PPT quotient, the simulator must have a
polynomial grade and its reduction transformer is retained for concrete loss.

## 12. Instantiating the AC layers

### 12.1 Pointwise carriers and erasure

At every fixed `(kappa,b)`, first take a *costed lower carrier*:

- `Phi^cost_(kappa,b)`: the contextual quotient of compatible normalized
  metered graphs, retaining lower terminal status and the selected
  isomorphism-invariant public ledger report;
- `Sigma_(kappa,b)`: denotations of typed graded converter codes;
- `D^cost_(kappa,b)`: cost-aware coded distinguishers;
- the lower pseudometric induced by `D^cost_(kappa,b)`;
- renaming, independent parallel, and strict connection.

Section 9 proves directly that this finite operational quotient is a system
algebra and that the forgetful map `U` preserves every graph constructor.
`U` erases ledger reports and maps both block and exhaustion to strict
nonresponse. Behavioral computational security uses distinguishers that
factor through `U`; performance-sensitive security may use the costed
carrier.

On the route-safe subalgebra, Section 9.7 maps the behavioral quotient
injectively into the selected standard-Borel partial-random-system carrier and
preserves every finite constructor. Thus the pointwise lower AC carrier is
complete. Only comparison with a separately mandated carrier that chooses
different nonresponse or feedback semantics remains conditional.

### 12.2 Efficient family carrier

An implementation family is uniform-efficient when it is generated by one
fixed template and fixed polynomial grades. A specification family is
efficiently accessible when reachable public-coordinate codes, query codes,
reservations, and codec/reservation/charge-evaluator profiles are polynomial
on a declared domain closed under admitted public updates; it is efficiently
implementable only if it also has a uniform implementation witness.

In the pure-uniform and bounded-auxiliary modes, the efficient converter class
contains fixed uniform graded converter codes. In the explicit-nonuniform
mode the advice/circuit family and one polynomial size bound are part of the
object. The same mode discipline applies to the interaction program,
effective public-report projection, and charged terminal scorer of a
distinguisher. These classes are closed under finite converter operations:
fixed codes compose, explicit advice concatenates with polynomial size, and
all grades compose polynomially. The computational relation identifies
resource families that have negligible advantage for every test admitted by
the selected mode.

**Efficient-algebra theorem.** Fix the codecs, uniformity mode, and a finite
dependency signature `Gamma` of named efficiently accessible specification
packages. Each package includes its typed interface, initialization rule,
kernel, codecs, public coordinate, reservation/tariff evaluators, profiles,
and independence convention. Route-safe `Gamma`-relative efficient resource
families, admitted converters, and admitted behavioral test networks form a
lower cryptographic algebra:

- pointwise renaming, finite independent tensor, legal finite connection,
  identity, and converter action satisfy the system-algebra laws;
- route-envelope recomputation remains a fixed polynomial transformation;
- exact absorption of either a converter or an arbitrary feasible parallel
  resource puts every composed test in the polynomially reindexed class;
- computational indistinguishability is an equivalence relation compatible
  with these operations;
- sequential construction composes profile transformers and adds negligible
  errors.

The proof uses the pointwise route-safe algebra, fixed/generated compilation,
exact absorption, polynomial substitution, and the triangle inequality. It
does not use pointwise full abstraction to admit noncomputable environments.
Nor does it infer availability: an adequate implementation still needs the
separate no-exhaustion, productivity, and realization witnesses below.
Lifting the elementwise theorem to a resource specification additionally
requires the uniform specification certificate above; arbitrary sets of
individually efficient families are not silently assigned a uniform error.

More explicitly, in the notation of MR11 Definitions 14, 16, and 17, let
`Phi^f_Gamma` be these route-safe feasible resource families, `Sigma^f` their
admitted converter families, and `D^f_Gamma` all admitted charged-scorer test
*networks* over the same signature. The last class is not only the set of
terminal scorer programs: it contains any fixed finite feasible graph around
the challenge. Graph order invariance makes converter actions at distinct
interfaces commute; the bare alias is neutral; computational equivalence is a
congruence; and the two pathwise absorption theorems close `D^f_Gamma` under
every converter in `Sigma^f` and every parallel resource in `Phi^f_Gamma`.
Before tensoring, occurrences are alpha-renamed apart; absorption retains the
same occurrence states and seed coordinates rather than cloning them.

This dependency-relative formulation is essential. Enlarging `Gamma` changes
the computational model and is not a reduction step. A parameter-dependent
number of independent oracle occurrences requires one fixed indexed
product-state package with a charged multiplexer and aggregate tariff; the
generated-network compiler cannot manufacture oracle independence. An honest
class `Sigma^e subset Sigma^f` can impose a stricter grade policy as long as
serial composition stays inside `Sigma^e`. The usual “all fixed polynomial
grades” choice takes the same polynomial regime for feasibility and honest
efficiency.

This gives the lower interpretation of the high-level symbols:

```text
efficient converter   = code/advice admitted by the named mode
                        + polynomial grade
feasible distinguisher = selected larger grade class, if desired
computational metric   = negligible quotient of budgeted advantages
efficient construction = ordinary AC construction
                         + code/grade witnesses
                         + no-exhaustion/productivity witnesses
```

Honest and dishonest converter classes may use different grade families.
Nothing in the top-down theory requires both to be the same PPT class.

### 12.3 Construction statement

For assumed specification `R`, protocol code `pi`, target specification `S`,
and simulator code `sigma`, a computational construction contains:

1. typing and effective-codec witnesses;
2. program/advice witnesses in the named uniformity mode for `pi` and
   `sigma`, using the fixed compiler when generated syntax is chosen;
3. polynomial grades and oracle tariffs;
4. route-safe canonical structural plumbing, with any intentionally limited
   communication mechanism represented as an explicit resource node;
5. a declared class of completion contexts with context-safety and
   conditional-progress certificates, and an alpha-invariant ownership
   assignment for tested, context, and shared meters;
6. overwhelming tested-side no-exhaustion in every admitted closed real and
   ideal experiment, combined with the context/shared bounds to obtain global
   no-exhaustion, with stronger worst-case or almost-sure status recorded when
   proved;
7. productivity on the target's declared responsive domain, including the
   completion-context progress-failure bound;
8. a negligible distinguishing bound, or a concrete reduction function;
9. a budget transformer for every reduction step.

At a schematic level:

```text
pi R  is computationally indistinguishable from  sigma S,
with advantage epsilon_D(kappa)
and reduction profile T_(pi,sigma,D).
```

The precise judgment is `EffConstruct_(M,C)` from
`adequacy-and-closure.md`. The higher AC construction theorem composes its
behavioral inequalities. Separate union bounds compose exhaustion and
productivity failure, and profile transformers compose the concrete costs.
The high-level theorem does not manufacture any of these lower witnesses.

### 12.4 What feedback closure means

There are two classes.

- The **metered implementation algebra** is closed under every well-typed
  finite connection. A bad cycle ends by lower-layer exhaustion and erases to
  nonresponse.
- The **adequately responsive subclass** contains systems for which the
  meter never fires on a declared workload and a visible answer occurs.
  This class is not automatically closed under feedback.

A paper must never infer the second closure from the first. Responsive
feedback needs one of:

- an acyclic call graph with response-independent elementary bounds;
- for response-adaptive calls on a fixed DAG, one polynomial cumulative
  response invariant per vertex satisfying the proved post-fixed-point
  inequality;
- a well-founded rank decreasing on every hidden transfer;
- a linear/affine credit that decreases on every cycle;
- a polynomial flow fixed-point certificate for the particular connection.

The last option is broad but composition-specific. The rank and credit options
are more restrictive but support constructor rules.

Every space certificate in these rules separates lifetime persistent state
from an active/suspended transient frame. The forward activation count is
substituted into each occurrence's persistent bound and those bounds are
summed, because inactive siblings coexist. Only the transient call frames use
a root-to-leaf maximum under the one-token scheduler. The credit theorem uses
the same sum of lifetime persistent occurrence bounds plus one active
transient/message stack. A per-activation peak cannot by itself certify a
stateful occurrence after polynomially many calls.

For probabilistic local certificates, neither DAG rule silently assumes that
the advertised activation count remains valid after a component has already
misbehaved. The proof stops at the *first* failed certificate. Every earlier
history is certified, so the deterministic forward recurrence bounds the
candidate first-failure slots; the history-uniform conditional bounds can then
be summed without independence. In the response-adaptive rule the local
failure polynomial is explicitly evaluated at the certified cumulative
response invariant. The affine-credit rule uses the same stopping argument:
before first failure there are at most `C_0+1` activations. Credit may be a
ghost variant derived from machine state; a physically stored or transmitted
counter incurs ordinary state, head, update, and traffic charges.

## 13. Counterexamples that the definitions must survive

### 13.1 Arbitrary-family nonuniformity

Let `H` be a nonrecursive subset of the natural numbers. At parameter
`kappa`, define a one-state machine description that returns the bit
`1[kappa in H]`. Every individual machine is constant time. The family is not
uniformly implementable. Therefore “each member has a small implementation”
does not define uniform efficiency.

### 13.2 Binary security parameter

If `kappa` is provided in binary, a loop of `kappa^2` iterations is
exponential in the representation length `log kappa`. Giving `1^kappa`
restores the conventional asymptotic measure.

### 13.3 Current-input laundering

Machine `A` maps `x` to `xx`; machine `B` repeats its input. Both are linear
per activation in the current message. Connect their outputs cyclically.
Starting from one bit, the message has length `2^t` after `t` visits to `A`.
No per-activation polynomial prevents exponential cumulative work.

Bit-costful output prevents the doubling itself from being free, but only a
global workload/flow invariant or meter prevents the cycle from spending
superpolynomial work.

### 13.4 Polynomial shape is not connection closed

Machine `F` forwards either outside input to one output. Machine `R` repeats
its input. In isolation, each output volume is linear in input from outside
the component. Connect `F` and `R` on one branch and leave the other input
open. One external message can circulate forever. This is the exact structural
failure identified in the reactive-runtime literature.

### 13.5 Strict service lifetime

Suppose a database has a lifetime clock `kappa^3`. An environment making
`kappa^4` harmless queries exhausts it. A natural implementation may still
answer each query, while the clocked ideal service stops. An ambient workload
lets the database quota scale with the fixed environment's polynomial rather
than selecting one global exponent.

### 13.6 Oracle laundering

An oracle receives one bit and returns an encoded witness of length
`2^kappa`, or a bit of the halting set. If a call counts as one local
transition and response delivery is free, the caller appears PPT while
obtaining unbounded work. Separate call, response-traffic, and tariff
coordinates prevent the conclusion. The oracle remains an ideal
specification.

### 13.7 Expected polynomial time

On input length `n`, a machine runs `n^2` steps with probability `1/n` and one
step otherwise. Its expected work is `O(n)`, but an inverse-polynomial fraction
of experiments has quadratic delay. Variants with larger tails can make
composition and concrete availability arbitrarily poor. Expected work alone
is therefore not the admissibility predicate.

### 13.8 Almost-bounded nonclosure

Under time-lock puzzles, one protocol can verify a rare hard input and then
produce a harder puzzle of a second type; another protocol swaps the types.
Each is almost bounded against every isolated efficient environment, but
together they solve successively harder puzzles for each other. The joint
system is not almost bounded. This is why negligible overrun is an optional
tail property, not the core wiring discipline.

### 13.9 Timeout is not error

Resource `R` never answers its first query. Resource `S` answers `Err`.
A context queries once and, only after receiving `Err`, submits a second query
and outputs one. It distinguishes them perfectly. Consequently budget
exhaustion erases to nonresponse unless `Err` is explicitly part of the
interface.

### 13.10 Peak space is not cumulative work

A program may reuse one kilobyte for a billion sequential operations, or
allocate a million cells and halt quickly. One scalar “cost” cannot recover
both facts. Exact ledgers retain a peak-space coordinate and an additive work
coordinate.

## 14. Worked examples

### 14.1 Persistent one-time mask

Consider a converter `C` with outer data interface and inner key interface.
On first data query `x`, it requests a key `k`, stores `k`, and returns
`x xor k`. On later queries it reuses the persistent key.

For a bit-level implementation on `n`-bit messages, a representative exact
profile is:

```text
first call:
  transitions  = T_init(kappa) + T_xor(n) + routing
  peak space   = O(kappa+n)
  random bits  = 0 locally
  key calls    = 1
  key traffic  = kappa query/response-dependent bits
  outer traffic = Theta(n)

later call:
  transitions  = T_xor(n) + routing
  peak space   = O(kappa+n)
  key calls    = 0.
```

If `KEY` is an abstract ideal resource, its sampling work is not charged to
`C`, but the response bits and one call are. If memory is relevant, `C` must
be replaced by a stateless router using an explicit `MEM[kappa]` resource.
The higher random-system behavior is the same only for contexts that cannot
observe the administrative memory interface.

This example shows why cost is lifetime state: a per-call table that forgets
the first stored key miscounts later activations and may change reset
behavior.

### 14.2 Reactive secure channel

An ideal secure channel may accept messages of any finite encoded length and
an arbitrary finite number of times. Giving it a fixed lifetime clock creates
the killing problem.

In the present layer, a channel implementation and its wrappers receive
quota transformers polynomial in ambient `b`. A context with total
polynomial workload can produce only polynomial total message bits. The
channel's routing and cryptographic work are polynomial in that `b`. No one
universal query-count exponent is fixed in the functionality.

The useful-channel theorem has two parts:

1. metered boundedness follows from the grade;
2. a flow/no-exhaustion proof shows that every context message within the
   advertised workload is delivered before the relevant quotas expire.

The second part is protocol-specific. It cannot be obtained from the word
“PPT.”

### 14.3 Random oracle

Let `RO_(m,n)` be the usual stateful ideal random function from `m` bits to
`n` bits. It is a specification oracle with tariff at least:

```text
one call, m query bits, n response bits, and canonical routing.
```

The resource's exponentially large conceptual function table is not called a
PPT implementation. A graded converter may make at most its declared number
of calls and must pay to encode, receive, store, and process all answers.

For finite polynomial lengths `m,n` and lifetime envelope `Q`, the dossier now
proves this implementation statement for one fixed sequential `LazyRF`
machine.  It has the exact `Q`-query adaptive transcript law and profile

```text
Work  <= Q(4Q(m+n+8)+8(m+n+1)) + LenEval,
Space <= (Q+1)(m+n+8) + LenSpace,
Random <= Qn.
```

`LenEval` pays the fixed evaluators and validators for `m(kappa),n(kappa)`;
`LenSpace` contains their simultaneous scratch together with the retained
logical `1^kappa` parameter track and head. The unary asymptotic input is
therefore not silently omitted from the space profile.

The quadratic scan traverses complete encoded records, including stored
values, and is charged rather than treated as RAM.  Repeated inputs
return stored values; a first-seen input and the next unused tape block have
the same conditionally independent uniform law.  This lazy machine is a
separate implementation object whose ledger can be compared to the oracle
specification. Boundary routing must additionally receive the displayed
`Qm,Qn` envelope (or a route-safe closure). The machine occurrence never
exhausts and answers on that domain; closed productivity still adds the
completion context's `chi_D`, and is strong only when `chi_D=0`. The
two-sorted model therefore supports both ideal use and implementation claims
without conflation.

### 14.4 Concrete reduction

Suppose reduction `B` runs distinguisher `D`, emulates converter `alpha`, and
answers at most `q_D` primitive queries by calls to an assumption challenger.
A useful theorem reports, for example:

```text
time_B <= c_sim time_D
          + T_alpha(kappa,b_D)
          + c_route totalTraffic_D
          + c_oracle q_D,

queries_B <= q_alpha(kappa,b_D) + q_D,

Adv_D(real,ideal)
  <= Adv_B(assumption) + epsilon_info(kappa).
```

The constants and polynomials depend on the selected universal machine and
codec. At the asymptotic quotient, the first two lines prove only that `B` is
PPT. In a concrete statement they are part of the result.

### 14.5 Stateful simulator with explicit processor

Assume a simulator algorithm `sigma` is needed on the ideal side. In the
free-PPT model, `sigma` is a graded converter and its quota transformer enters
the reduction. In the explicit-resource model:

```text
pi R = route_sigma [ S parallel CPU_B parallel MEM_M parallel RAND_r ].
```

`route_sigma` is intentionally narrow: it supplies a fixed program and routes
machine I/O. The processor, memory, and random source expose the resources
required by simulation. This refines the modeling move in MauRen16, Section
4.3. There the added resource is the behavior `beta_bar`; the source does not
decompose it into processor, store, and coin services. The pathwise
transaction theorem below is what justifies that additional decomposition for
the selected machine API.

## 15. Reifying costs as AC resources

### 15.1 API choice and statelessness

If all persistent memory is meant to be counted by `MEM`, program converters
must have no hidden persistent work tapes. They may retain only finite control
and explicit opaque handles whose storage is part of the resource contract.
Otherwise the converter can bypass the memory accounting.

This is the lesson highlighted by MauRen16's treatment of the
Ristenpart--Shacham--Shrimpton example: a Turing-machine converter comes with
memory unless the model removes or externalizes it.

The words CPU, memory, randomness, communication, and clock do not themselves
define resources.  Random access and sequential tape memory have different
costs; a shared processor needs scheduling and ownership; a visible clock
changes the behavioral observer.  The theorem below therefore chooses one
private sequential API and states its exclusions.

### 15.2 Selected sequential API

For a machine program `P` with native quota

```text
B_v = (T_v,A_v,R_v,S_v,...),
```

select:

- `PROC_v[P;T_v,A_v,L_v]`, an initialized transition engine whose resource
  state contains the unique charged immutable copy of `code(P)`, with step
  and activation tokens but no mutable machine state or coins;
- `STORE_v[S_v]`, which owns the native control, mode, input/work/output
  tapes, heads, and pending port, and tests exactly the native
  `live_P(c) <= S_v`;
- `COIN_v[R_v]`, which owns the named random tape/head and charged reads; and
- optionally `SLINK_e[C,W,S]`, one lossless copied-message buffer with no
  clock, reordering, or adversarial delivery.

`Drive_P` is only a private tag router.  Its subscript records native port
typing, not a program image or selection payload: the physical connection is
already to `PROC[P;...]`.  Dynamic phase, frame, and continuation state is in
`STORE` or the one in-flight record.  After attachment, no other party can
call the private administrative ports.

Program storage, processor/coin/store counters, transaction scratch, the live
routing buffer, and the canonical sparse serialization of tapes and ordinary
head coordinates are explicit coordinates.  They are not identified with the
native logical peak.  Under standard initialization, at most `S` live cells
and the fixed `H_P` heads have coordinates of magnitude at most `T+S+1`.
Consequently the explicit terminal-state encoding has the additional bound

```text
L + CtrBits_P(B_exp)
  + O((S+H_P) log(T+S+2))
  + fixed scratch + MaxInFlightOriginalEvent.
```

Here `B_exp` extends the native grade by the derived administrative
work/traffic/reservation envelope and
`CtrBits_P(B_exp)=sum_x ceil(log_2(B_exp[x]+1))` ranges over the fixed finite
counter vector owned by the bundle and private access meter.  Used and
remaining counters change only the fixed constant.  Original-edge and
specification meters left outside the bundle are serialized once by the
surrounding graph rather than duplicated.

The primary `STORE[S]` capacity is still exactly the selected native logical
cell metric; the expression above is the representation/report cost.  An
arbitrary sparse initial configuration must bring its serialized coordinate
map as charged input.  The ideal infinite coin tape is a randomness resource,
not a finite-memory implementation claim.  The `L` term is the sole program
copy in the selected initialized presentation.

A generic loaded presentation is separate.  It requires a charged program
event or `IMAGE[P,L]` resource and an initially blank processor.  A copying
loader reserves and validates the whole destination before commit, streams
the self-delimiting code with linear work and traffic and logarithmic scratch,
and exposes the simultaneous charged source/destination peak.  Only after a
valid, fully funded atomic load may the initialized refinement be invoked.
Reload, invalid-code behavior, erasing sources, or ownership transfer are new
resource policies, not free variants of `Drive_P`.

### 15.3 Transactional refinement

A direct sequence that spends a CPU token, reads a coin, and only then finds a
store overflow has a different failed ledger from the native joint meter.
Worst-case reservation over both random branches can also reject an actual
branch that fits.  The selected implementation therefore uses two-phase
reservation.

Every transition follows one padded private schedule:

```text
frame
  -> reserve processor
  -> reserve coin mode (genuine read or no-read dummy)
  -> plan actual command
  -> reserve actual store successor
  -> commit coin/no-read
  -> commit processor
  -> commit store.
```

Reservations lock capacity but commit no native coordinate; capabilities are
linear.  If a reservation fails, the run terminates with the native public
owner `v`.  Commits cannot fail, and only the final store commit can emit,
block, or start the next native transition.  Fixed padded records prevent a
secret coin or the read/no-read case from leaking through private message
length. A phase index alone is not a progress rank for a long admitted copy or
output scan. The actual rank is lexicographic in the remaining phase suffix
and the remaining admitted bit microsteps. It decreases on every internal
action, proving that the translation cannot introduce an administrative block
or livelock; the microstep bound is affine in the finite input/output lengths,
not constant.

`STORE.update.prepare` also maintains a private meter-readable charging view
of the prepared outcome tag, port class, and exact output-code length.  Before
any primary commit, the meter reserves the remaining fixed API costs and the
exact private output passage.  This is not returned to `Drive_P` and is not an
extra message phase.  The coarse `O(S)` reply bound proves bounded
accessibility, but reserving it on every commit could spuriously reject a
small late output; the refinement uses the exact prepared view.

That exact length is not a free random-access operation.  The selected native
normal form has a blank-on-activation contiguous self-delimiting output
buffer.  On `Emit` only, the store's private access procedure scans the
prepared buffer without copying or committing it, paying `O(ell+1)` work and
`O(log(S+1))` scratch before it publishes the binary length to the meter.
Well-typedness guarantees a terminator. Internal and block transitions do not
scan. Arbitrary sparse output tapes require a charged normalization first.

The scan cannot be funded from *committed* original output traffic: the
unchanged next router may reject the attempted value. Local head motion,
blanking, non-aliasing, and suspension imply instead that the sum of attempted
output lengths is `O(1+Acts+Steps)`. Before execution, the access meter
therefore dedicates a coordinatewise output pool of that size from the static
native `A,T` quotas. Scans and private store-to-driver output bits consume
their exact costs from it; the pool invariant makes them infallible after the
primary prepare. Delivered input copies remain bounded by original/boundary
traffic. Thus the affine administrative theorem holds even on a
downstream-routing rejection, without reserving `S` on every step.

Activation uses the analogous prepare/commit discipline.  The validated
self-delimiting length is inspected while the input remains in the charged
original routing buffer; store and activation capacities are reserved before
one private copy enters the native input region.

### 15.4 Completed macro theorem

The explicit-resource presentation is credible only with a theorem of the
form:

```text
erase_admin(
  Drive_P [PROC[P] parallel STORE parallel COIN]
) = [[machine(P)]],
```

For the selected API this is now proved.  At transaction boundaries relate
`STORE` to the native configuration, `COIN` to the native named tape/head, and
committed processor/coin counts to the native ledger.  Equal frames and tape
bits select the same actual successor.  All reservations succeed iff the
native joint charge fits; successful commits restore the relation, while a
failure commits no native coordinate.  Induction along the unique token gives
pathwise equality of maximal success/block/exhaust transcripts, including
cyclic networks.  The well-founded phase/microstep rank covers infinite
cases.  Using the same tape,
oracle-seed, and initial-state law then gives kernel equality.

The cost theorem is a projection:

```text
pi_native(Cost_explicit) = Cost_native.
```

The full explicit report correctly retains initialization, administrative,
counter, head, and sparse-state serialization costs.  Administrative work and
traffic satisfy a fixed affine bound in native activations, steps, coin reads,
and original traffic; the complete state-encoding bound is displayed above.
For a fixed closed route-safe graph, summing the persistent per-bundle
program/counter/store bounds and a conservative copy of the final event
envelope, then adding the fixed router/staging/shared-meter state, bounds the
physical simultaneous `gpeak` pointwise. This finite sum deliberately
overcounts the single live token but proves the global physical space profile
polynomial without deriving it from incompatible local maxima. Hence
polynomial native grades yield polynomial explicit grades; the same phase
rank transfers no-exhaustion and productivity. An open component's own grade
does not bound an arbitrary hostile boundary event.

For a generated network, compilation precedes reification.  The proved
generated-to-fixed theorem yields one fixed universal machine, physical
decoder/interpreter profile, and master coin tape.  Translating that one
occurrence gives one fixed `PROC[P_U]/STORE/COIN` bundle, and polynomial
substitution composes the profiles.  Translating decoded nodes first would
manufacture a parameter-dependent family of ideal resources and is invalid
without a separately specified indexed product-state computer resource.

Writing `C_P = PROC_P[P] || STORE_P || COIN_P`, the theorem also transports
construction experiments.  Every external behavioral test, and every
cost-aware test factoring its report through `pi_native`, has identical
advantage before and after translating selected machine occurrences.  Thus

```text
pi R ~=_epsilon S sigma
```

becomes

```text
Drive_pi [R || C_pi] ~=_epsilon
Drive_sigma [S || C_sigma]
```

with the same error and the enlarged explicit profile.  Translating the
simulator places its computation resource on the ideal side; retaining a
free-efficient simulator is a separately named mixed regime.

The local theorem can also be applied to the whole closed test harness. Make
the pure-mode input generator, interaction machines, effective terminal and
report projections, record builder, and scorer explicit native occurrences;
in nonuniform mode use one fixed universal evaluator with the named
polynomial-length circuit/advice description. Translate every occurrence
after any generated-network compilation. The decision kernel is pathwise
unchanged, `pi_native` recovers the full native ledger including `gpeak`, and
the full explicit profile is polynomial. This puts transition evaluation,
mutable configuration, and coins of every computational actor inside supplied
resources, leaving only finite tag routing in converters.

It still does not reify the semantic supervisor that detects a maximal run,
the non-observable meter/reservation primitives, or the chosen routing API.
Nor may a comparison give different test-owned computer resources on its two
sides. Reifying only selected protocol/simulator occurrences is therefore a
mixed regime, while changing resource ownership changes the construction
statement itself.

The complete API, invariant, proof, overhead calculation, link proposition,
and limitations are in `explicit-resource-refinement.md`.

### 15.5 Boundary

The theorem does not cover RAM, shared processor/coin/store access, reset,
secure erasure, leakage, asynchronous queues, adversarial delivery, or a
visible clock.  A visible clock in particular defeats unrestricted
administrative erasure by exposing the number of private phases.  These are
different lower APIs, not consequences of the selected theorem.

## 16. Relationship to reactive-runtime notions

The following comparison is deliberately operational.

| Notion | Bound | Generic wiring closure | Present use |
|---|---|---|---|
| A priori lifetime PPT | One polynomial per machine in `kappa` | Yes for fixed finite, hard-clocked machines; poor reactive expressiveness | One-shot special case |
| Per-activation PPT | Polynomial in current input | No; message amplification | Rejected as global criterion |
| Continuously polynomial / polynomial shape | Work and output related to visible or outside flow | No; connection needs shape check | Availability certificate |
| Reactive polynomial time | For every strict-PPT context, closed run is polynomial with overwhelming probability | No; composed protocol must be checked | Quantifier evidence |
| Uniform reactive polynomial time | One transformer polynomial in context runtime | No without composition condition | Closest source analogue of ambient grades |
| IITM environmental boundedness | Every universal environment induces an almost-polynomial closed run | Under time-lock puzzles, the almost-bounded class is not generically closed | Quantifier and assumption-conditional counterexample evidence |
| Present metered grade | Strict quota polynomial in `(kappa, ambient workload)` | Yes as a bounded partial implementation | Primary implementation algebra |
| Present responsive grade | Metered grade plus no-exhaustion/productivity on workload | Requires flow/rank/credit proof | Useful services |

The present strict meter is not the “strong reactive polynomial-time” security
notion shown problematic in the IITM/UC literature. Here every converter code,
including a simulator, has a syntactic grade; exhaustion is part of the
lower-layer behavior; and the AC metric is applied to those behaviors.
Admissibility is not a semantic side condition that can be invalidated by a
negligible bad branch after composition.

This choice has a cost: some natural unbounded service specifications need an
ambient-workload interface and a no-exhaustion theorem. That obligation is
preferable to an implicit runtime convention, because it states exactly which
workload and denial-of-service behavior are guaranteed.

## 17. Alternative designs and why they were not selected

### 17.1 Pure environment-relative semantic efficiency

One could call a network efficient iff every strict-PPT context makes the
closed run polynomial, as in reactive polynomial time. This includes natural
repeaters without clocks. It is broad and semantically elegant, but the class
is not closed under arbitrary connection. Every construction would need a new
global runtime proof.

The dossier retains this predicate as an adequacy property but does not use it
as the implementation algebra's closure mechanism.

### 17.2 Credit-only linear type system

One could attach consumable credit to every message and forbid machines from
creating credit. Every cycle would strictly decrease credit, providing strong
feedback closure without external per-component clocks.

This is attractive for certified implementations but can be restrictive.
Broadcast, polynomial output expansion, and services whose runtime is
polynomial rather than linear in input need the caller to prepay a suitable
potential. It is retained as one proof system for no-exhaustion/productivity,
not the only semantics.

### 17.3 Pure flow polynomials

One could assign each open component a polynomial transformer from outside
input volume to output and work. This closely matches polynomial shape and is
excellent for acyclic composition. Cyclic inequalities can have no finite
least polynomial solution, or can permit exponential growth. A connection
must therefore provide an explicit fixed-point certificate.

### 17.4 Universal global clock only

A single clock around the closed experiment trivially gives PPT execution.
It does not say how cost is attributed to protocol, simulator, router, or
oracle; it also gives no component-level reduction transformer. The selected
model keeps a global ambient workload but assigns exact local quotas and
ledgers.

### 17.5 Extensional cost on random systems

Assigning the minimum runtime over all programs realizing a random system
would be representation-independent, but it is generally uncomputable,
discards concrete implementations, and is undefined for nonrealizable
specifications. It is unsuitable as the constructive lower layer.

## 18. Proof portfolio

### 18.1 Proved directly from the definitions

- fixed-tape determinism and unique exact ledgers;
- prefix closure of unbounded and metered DDS behavior;
- bit/output/random/space domination by machine transitions, modulo fixed
  router constants;
- termination of finite-quota machine execution;
- budget monotonicity and finite-success stabilization;
- polynomial boundedness of a fixed finite graded graph in a polynomial
  ambient workload;
- syntactic closure of graded converter codes under finite composition;
- exact converter absorption and budget-reindexed nonexpansion;
- asymptotic closure under polynomial reindexing and polynomially many
  hybrids;
- the strong/almost-sure/overwhelming no-exhaustion implication structure,
  metered/unmetered coupling bound, elementary and response-adaptive
  post-fixed-point DAG certificates, and affine-credit feedback certificate;
- finite standard-Borel oracle terminal kernels, no-selection admission,
  budget monotonicity, the generic streaming/reassembly coupling, and the
  complete geometric-string tail/profile instance;
- the self-delimiting generated-network compiler, random-tape product
  coupling, and polynomial physical profile transformer;
- the finite cost-aware contextual system algebra and erasure homomorphism;
- the route-safe canonical-router envelope, standard-Borel partial-DDS and
  maximal-transcript carrier, strict-connection congruence, pointwise full
  abstraction, and injective homomorphism `J`;
- the complete persistent-mask, RF/RP switching, generated-chain, feedback,
  and oracle-tail calculations;
- the selected transactional processor/store/coin administrative-erasure and
  native-ledger projection theorem, plus the sequential-link refinement;
- nonuniform hard-coding and timeout-versus-error counterexamples.

### 18.2 Conditional claims

- comparison of the selected partial-random-system carrier with another
  independently mandated carrier using different nonresponse or feedback;
- composition of responsive, not merely bounded, feedback systems when no
  DAG/rank/credit/solved-flow certificate is supplied;
- application-specific streaming-oracle instances beyond the proved
  geometric-string model and generic one-token reassembly theorem.

### 18.3 Proposed refinements

- explicit-resource APIs beyond the proved private sequential
  `PROC/STORE/COIN/SLINK` instance, including RAM, sharing, reset, leakage,
  erasure, asynchronous communication, and visible clocks;
- causal/projective concurrency beyond the one-token boundary;
- mechanization of the costed operational semantics.

## 19. Recommended future formalization order

1. Encode the already specified exact ledger, meter, normalized finite graph,
   route-safe canonical-router envelope, and terminal-kernel semantics without
   changing their mathematical interfaces.
2. Formalize the finite contextual quotients and operation laws.
3. Formalize the selected standard-Borel partial-DDS/maximal-transcript
   carrier, environment-lifting congruence, and route-safe homomorphism `J`.
4. Add uniform families, polynomial profile transformers, and the asymptotic
   efficient-construction witness as a layer over the pointwise results.
5. Formalize the bounded oracle contract and one concrete streaming
   reassembler; keep kernel computation in the specification sort.
6. Add the generated-network compiler only if the secondary presentation is
   needed by a downstream example; the primary fixed-template definition does
   not depend on it.
7. Formalize the selected transactional processor/store/coin refinement only
   if an explicit-resource statement is needed; its mathematical
   macro-refinement theorem is now proved. Select a different API only for a
   theorem that needs RAM, sharing, timing, reset, leakage, or concurrency.

This order reflects the top-down methodology: each lower step adds only the
distinction needed for the next claim, and every forgetful map is proved
before adding another refinement.

## 20. Final assessment

The random-system layer is not the endpoint of Constructive Cryptography.
It is the behavioral interface above an implementation hierarchy. The
unbounded Turing-machine layer establishes which interactive behaviors are
computably realizable and why wiring commutes with denotation. The exact
ledger then exposes the facts erased by macro semantics. Polynomial grades,
ambient workload, and non-observable meters give a closed efficient
implementation algebra. Tariffed abstract oracles preserve the distinction
between efficient access and efficient implementation. Budget transformers
turn the slogan “PPT is closed” into a concrete reduction theorem.

The most important negative conclusion is equally precise: no local phrase
such as “polynomial per activation,” “PPT in the input length,” or
“environmentally almost bounded” can by itself guarantee efficient feedback.
One must either meter the composed execution or prove a global flow,
rank, or credit invariant. The recommended model does both at different
levels: metering supplies algebraic closure; a separate invariant supplies
availability.

The result is a lower instantiation of AC, not a competing composability
framework. It leaves the high-level construction theorem untouched and makes
the computation model, efficiency class, ideal-resource access, and concrete
losses explicit exactly where the abstraction hierarchy says they belong.
