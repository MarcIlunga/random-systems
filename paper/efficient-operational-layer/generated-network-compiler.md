# A concrete generated-network compiler

## 1. Status and purpose

The primary uniform carrier is one fixed finite network template.  A
parameter-dependent graph is admitted only as secondary syntax after it has
been compiled into that carrier.  This note fixes a graph language, a decoder,
a universal simulation invariant, the random-tape coupling, and the profile
transformation needed for that claim.

The compiler theorem below is for generated **implementation nodes**.
Tariffed specification oracles have fixed names and fixed types and remain
boundary dependencies of the universal template.  Calls to them may be
multiplexed by encoded virtual-node identifiers and are charged accordingly,
but a generator may not manufacture a parameter-dependent family of new
abstract specifications.  A separate theorem could provide a countable
product-state “oracle array”; it is not needed for the uniformity result here.
For a stateful tariff whose exact charge depends on the meter-only next public
coordinate, the fixed template uses the administrative oracle proxy specified
in Section 4.3. It mirrors charging information privately to the interpreter;
the simulated program still receives only the ordinary response. The baseline
theorem assumes that every such occurrence is private to the compiled
subsystem. If an occurrence is intentionally shared with an outside caller,
one fixed coherence proxy must mediate *all* callers and mirror every committed
public-coordinate update before the next virtual admission; otherwise the
interpreter's cached contract coordinate can become stale.

The theorem proved here is deliberately modest:

> A family produced by one fixed generator, using one fixed program and grade
> language, with a polynomial graph-length bound and a polynomial *aggregate*
> native profile, has a fixed-template universal implementation with a
> polynomially transformed profile and the same erased transcript law.

It does not say that an arbitrary indexed family of finite graphs is uniform.
It does not preserve the native exact cost report: universal interpretation
has a different, explicitly transformed report.

## 2. A self-delimiting graph language

### 2.1 Primitive codes

For `n in N`, write `n+1` in binary as `1u`, where `u` has length

```text
m = floor(log_2(n+1)).
```

Define

```text
Nat(n) = 0^m || 1 || u.
```

Thus

```text
|Nat(n)| = 2 floor(log_2(n+1)) + 1.
```

The initial zero run determines `m`, after which exactly `m+1` binary digits
are read.  Hence `Nat` is prefix-free and has a one-pass decoder.  In
particular `Nat(0)=1`.

Define the framing operations

```text
Bits(x)       = Nat(|x|) || x,
List(x_0,...,x_{r-1})
              = Nat(r) || x_0 || ... || x_{r-1},
```

where every `x_i` is itself a self-delimiting record of the required kind.
The list count, not a sentinel, determines where the list ends.  A decoder
rejects if a field is truncated or if bits remain after the last top-level
field.

### 2.2 Fixed libraries

A generated-family certificate contains four finite, parameter-independent
libraries.

1. `CodecLib` contains the effective query/response codecs that may occur on
   ports.  A graph code refers to them by natural-number index.
2. `ProgLib` is either a finite program library or the fixed syntax of the
   universal component language described below.  Program blobs are checked
   against this syntax.
3. `GradeLib = (F_0,...,F_{g-1})` is a finite list of fixed multivariate
   polynomial grade transformers.  A node contains an index `j<g`, never a
   parameter-dependent polynomial expression.
4. `OwnerLib` is a finite list of public accountability classes such as
   protocol, simulator, context-owned wrapper, or shared infrastructure.
   These labels attribute cost-layer block/exhaust events and are erased at
   the behavioral layer.

The fixed grade library prevents a generator from hiding an exponent that
grows with the security parameter.  A more general theorem could allow a
fixed polynomial-expression grammar with a uniform degree/coefficient
certificate; it gives no additional expressiveness needed here.

### 2.3 Program code

The universal component language is a binary multitape transition language.
A program record contains:

```text
Nat(number of persistent work tapes)
Nat(number of finite-control states)
List(transition records)
List(port-action records).
```

A transition record contains a source state, one scanned symbol per work
tape, one written symbol and one head move in `{L,S,R}` per work tape,
corresponding restricted actions on the distinguished read-only input and
blank-at-activation output tapes, a random-use mode, and a target state.  In
`no-read` mode the random bit is absent from the source key.  In `read` mode
it is present, and that bit's table branch chooses a head action in
`{stay,advance}`.  The validator rejects a scanned-frame key that mixes a
no-read record with read-bit records or otherwise leaves the use mode
ambiguous.  This makes the read/no-read decision available before sampling
while allowing the advance decision to depend on the sampled bit, exactly as
in the native machine convention.  The input and output buffers use the same
finite alphabet with blank and delimiter symbols.  A port-action record
identifies a control state as one of:

```text
emit(port), call(port), resume, block.
```

Records are sorted by their source key.  The validator rejects duplicate
source keys, out-of-range states, malformed alphabets, and port indices that
do not exist on the containing node.  A missing transition means `block`.
This format is finite and deterministic once the component's random tape is
fixed.  It directly represents the component machines used by the operational
semantics; no unit-cost pointer or string-copy instruction is present.

For the complexity proof only the following consequences matter.  On a graph
code of length `L`:

- every program has at most `L` tapes, states, ports, and transition records;
- every program lookup can be performed by a scan of at most `L` code bits;
- one native transition visits at most one new cell on each of at most `L`
  virtual tapes;
- every produced bit requires a native transition or a charged router step.

### 2.4 Graph records

Let an endpoint be a pair `(node-index, port-index)`.

```text
TypeRecord
  = Nat(query-codec-index) || Nat(response-codec-index)

PortRecord
  = polarity-bit || Nat(type-index)

NodeRecord
  = Bits(program-code)
    || Nat(grade-library-index)
    || Nat(owner-library-index)
    || List(PortRecord)

Endpoint
  = Nat(node-index) || Nat(port-index)

EdgeRecord
  = Endpoint(client) || Endpoint(provider)

BoundaryRecord
  = Bits(external-label) || Endpoint
```

The complete code is

```text
GraphCode
  = 01010010 01010011 01000111 00000001
    || List(TypeRecord)
    || List(NodeRecord)
    || List(EdgeRecord)
    || List(BoundaryRecord).
```

The first 32 bits are the magic/version word `RSG1`.  List position is the
only internal identifier.  Therefore node and port identifiers cannot be
duplicated.

The decoder enforces:

0. every declared list, tape, state, transition, and port count is at most the
   total code length `L`; a larger binary count is rejected immediately rather
   than expanded into a unary loop;
1. type records and boundary labels are in strict lexicographic order;
2. every query/response codec index occurring in a type record, every grade
   and owner index, every type index, and every endpoint index is in range in
   its respective fixed library or decoded table;
3. every edge has one client and one provider endpoint of the same type;
4. edge records are in lexicographic order of their endpoint pairs;
5. no endpoint occurs in two edges or two boundary records;
6. every port endpoint occurs exactly once, either in an internal edge or at
   the boundary;
7. every program port action names a port in its containing node;
8. all lists and the entire code are consumed exactly.

These conditions select a deterministic labeled presentation of a finite
normalized typed graph.  Two alpha-isomorphic graphs may still use different
node-list orders; computing a canonical graph labeling is neither assumed nor
charged here.  The decoder treats list positions as administrative occurrence
names, and the operational quotient later identifies the resulting
alpha-isomorphic graphs.  Physical routers, delays, copiers, and repeaters are
program nodes; a bare boundary alias is represented only by incidence and is
not a node.

### 2.5 Unique-decoding lemma

**Lemma 2.1.** Every accepted `GraphCode` has a unique parse and denotes one
finite normalized typed graph.  No accepted graph code is a proper prefix of
another accepted graph code.

**Proof.** `Nat` has a unique prefix parse.  Induction over the record grammar
therefore gives a unique parse for every field and list.  Range, sorting, and
linearity checks then determine one type table, node list, matching, and
boundary.  A proper extension of a completely parsed code leaves trailing
bits and is rejected by condition 8.  Conversely, serialization of a valid
labeled presentation satisfying the ordering and library rules is accepted.
This is not a claim that the serialization canonically labels an unlabeled
graph.

## 3. Decoder cost

The decoder uses separate tapes for the input code, unary list counters, the
type/node/port tables, the endpoint-used bitmap, and a work record.  It has
four phases.  The following table counts elementary full-scan/copy work, not
raw transitions of an unstated Turing-machine implementation.

| Phase | Operation | Elementary-work bound |
|---|---|---:|
| 1 | Copy the code and parse all primitive fields | `16(L+1)^2` |
| 2 | Validate program syntax and all indices | `32(L+1)^2` |
| 3 | Check order, polarity, typing, and endpoint linearity | `32(L+1)^2` |
| 4 | Produce the validated sequential graph table | `16(L+1)^2` |

The first phase can in fact be linear.  The quadratic allowance gives a
simple implementation in which every one of at most `L` fields may rescan the
at-most-`L`-bit code or a unary table.  In each phase the displayed constant
allows sixteen or thirty-two single-tape scan/copy passes for every field;
delimiter and finite-control changes occur in the same multitape transition.

Every elementary routine is a fixed multitape algorithm over a fixed alphabet:
move one head, compare one symbol, write one symbol, or change one finite
control state.  Compile these routines once to the component-machine syntax of
Section 2.3.  Let `c_dec >= 1` be the maximum number of compiled component
transitions used by one elementary step, and let `s_dec >= 1` be the analogous
constant for its scratch-cell footprint.  These constants exist because the
routine library is finite and are independent of `L`, `kappa`, and the
generated family.  We use the conservative certificate

```text
DecodeWork(L)  = 128 c_dec (L+1)^2,
DecodeSpace(L) = 16 s_dec (L+1)^2.
```

The elementary-work bound is the sum of the four rows with an additional
`32(L+1)^2` allowance for reject/cleanup paths, and multiplication by
`c_dec` transports it to actual component transitions.  The space bound
permits a dense endpoint-used table of quadratic size; a more careful indexed
implementation is linear.  The numerals are properties of this chosen routine
certificate, not invariants of Turing machines.  Publishing an actual
transition table would determine `c_dec` and `s_dec`; no later argument
pretends that either constant equals one.

**Lemma 3.1.** After the one-time routine compilation just described, the
fixed decoder accepts exactly the codes of Section 2 and obeys the displayed
work and space bounds.

**Proof.** Soundness and completeness are the validation checks and
Lemma 2.1.  There are at most `L` primitive/list/record fields because each
consumes at least one input bit.  Every validation subroutine uses the bounded
number of full scans allocated in the table.  Summing the elementary
certificates and applying the definitions of `c_dec` and `s_dec` gives the
displayed machine bounds.  No phase stores more than the code, the decoded
sequential tables, and one `L`-by-`L` endpoint bitmap.

The symbolic compilation constants can be replaced by the exact maxima read
from an implemented decoder without changing any later theorem.  What is
essential is that the decoder, its routine compiler, and its certificate are
fixed independently of `kappa`.

## 4. Universal simulation

### 4.1 Virtual configuration

The fixed universal component stores:

- the decoded graph table;
- the unique current token owner;
- for every virtual component, its control state, random-tape position,
  persistent work tapes, and suspended call stack;
- the current input/output buffers;
- the virtual component and router meters;
- the current public contract coordinate and exact virtual access ledger for
  every fixed named specification dependency;
- the exact native ledger;
- a cache for the random-tape splitting described below.

Write `W` for aggregate native component/router work, `A` for aggregate
activation count, and `Q` for aggregate named-oracle calls. Define

```text
H = 1 + W + A + Q
```

as a conservative number of native primitive-action/terminal-check slots, and
define the normalized numeric envelope

```text
M(kappa,b)
  = 1 + kappa + b
      + sum over all aggregate native profile coordinates.
```

The sum ranges over every scalar coordinate in the fixed dependency
signature, including work, space, randomness, traffic, activation,
oracle-call, query/response-bit, public-tariff, and charged oracle-evaluator
envelopes. Hence `M` is a fixed polynomial, `W,A,Q,H <= M` after harmless
constant inflation, and every virtual quota or counter value is at most `M`.
The distinction matters even for a short trace: the interpreter must encode a
large unused quota and the workload from which it was evaluated.

After at most `W` native component/router transitions:

- there are at most `L` nodes and at most `L` declared work tapes per node,
  hence at most `L^2` virtual work-tape headers;
- a native transition moves at most `L` heads, so the sum of head moves and
  newly visited work-tape cells over the whole trace is at most `LW`;
- buffers and stacks, including oracle continuations, are bounded by the
  aggregate native space/traffic coordinates and hence by `M`;
- there are only `O(L)` virtual meter records, each quota and counter has
  self-delimiting binary length `O(log(M+1))`; and
- control, graph, and virtual-meter records have length polynomial in `L+M`.

A dense directory of `L^2` tape headers supplies positional node/tape
identities, so those indices are not repeated beside each tape cell. It is
followed by one fixed-alphabet unary interval with an in-place head marker for
each materialized tape. This uses at most `L^2 + 2LW`
blank/visited-cell slots: the sum of interval growth is bounded by twice the
sum of head moves.  Untouched declared tapes need a header but no materialized
interval.  State identifiers, stack
metadata, and delimiters fit in another quadratic allowance.  One valid
virtual-configuration bound is therefore

```text
V(L,M) = 16 (L+M+2)^2.
```

This corrects the tempting but false bound `O(L+W)`: one multitape
transition may move every tape head of its owner, so up to `L` new tape
positions can become live in one native step.  It also avoids the false
global claim that a length-`L` graph can declare only `L` tapes: compact
declarations permit as many as `L^2`, even though the trace can touch only
`LW` new positions.  The use of `M` rather than only `W` additionally pays
for virtual meter encodings; a transition-count-only bound would be false
when a large workload supplies a large but mostly unused quota.

### 4.2 Splitting one fixed random tape

The primary fixed-template component has one fair one-way persistent tape,
which the splitter consumes monotonically, whereas the generated graph may
have a parameter-dependent finite set of independent fair tapes.  Let

```text
pair(i,j) = ((i+j)(i+j+1))/2 + j
```

be Cantor's computable bijection from `N x N` to `N`.  Define the `j`th bit of
virtual node `i` to be master-tape bit `pair(i,j)`.

When a requested coordinate is beyond the part of the master tape already
read, the interpreter reads and caches every intervening bit.  When it is
behind the head, the interpreter retrieves it from the cache.  For node
indices `i<L` and local random positions
`j<=P_native^rand(kappa,b)<=M`,

```text
pair(i,j) < (L+M+2)^2.
```

Thus at most a quadratic prefix is read and cached.  Because coordinate
permutation preserves product Bernoulli measure, the derived virtual tapes
are mutually independent fair tapes.  More strongly, for every fixed master
tape the derived tuple gives a pathwise native execution; the compiler does
not resample at a macrostep or after a call.

**Lemma 4.0 (random-splitting law).** If `Omega` has the Bernoulli product law
on `{0,1}^N`, then the array

```text
omega_i(j) = Omega(pair(i,j))
```

has the Bernoulli product law on `{0,1}^{N x N}`.

**Proof.** It suffices to check cylinder events.  For any finite set
`F subset N x N` and prescribed bits `(a_ij)`, bijectivity of `pair` makes
the coordinates `pair(i,j)` for `(i,j) in F` distinct.  Their joint
probability is therefore `2^(-|F|)`, which is exactly the finite-dimensional
product probability of the prescribed virtual bits.  Cylinder uniqueness
determines the product measure.  The cache changes only the order and number
of master coordinates physically read; it does not alter their values.

Shared randomness is not compiled by this splitter.  It must be a named common
node in the generated graph and is simulated as such.

### 4.3 One-step interpreter

To simulate one native step the interpreter:

1. scans the graph table to locate the token owner;
2. scans the owner's program for the matching transition;
3. scans/updates the dense virtual tape intervals and buffers;
4. if needed, retrieves one or a fixed number of paired random coordinates;
5. updates the virtual meter and exact native ledger;
6. on an emit/call action, performs the native canonical-router transitions
   one by one and changes token owner.

An oracle action needs one additional fixed administrative path. The ordinary
caller cannot in general reconstruct its exact tariff: the charging view may
contain the next public contract coordinate, which the specification exposes
to the access meter but not on the ordinary reply wire. For every fixed named
oracle dependency, the compiled template therefore contains one fixed private
`OracleProxy` face. It is not a generated oracle occurrence. It:

1. receives the virtual owner/occurrence identifier and query on a private
   self-delimiting administrative record;
2. checks the virtual semantic and evaluator reservations against the
   interpreter's virtual access ledger before a physical seed is touched;
3. on virtual rejection, returns the same virtual owner-labeled `Exhaust`
   without making a physical call;
4. on admission, invokes the unchanged physical oracle occurrence exactly
   once under its separately funded physical access envelope;
5. receives from the oracle access accountant a private authenticated commit
   receipt containing the reply/block tag, exact charge, and next public
   coordinate; and
6. mirrors that exact update into the virtual ledger while delivering only
   the ordinary response (or terminal block) to the simulated program.

The initial public coordinate is installed through the same private
accounting face from the declared oracle initialization law. The receipt is
administrative, not a program wire: decoded code cannot read it, remaining
budget, reservation slack, or the next public coordinate unless the original
oracle interface made that value public. Its codec, validation, work,
traffic, and transient space have fixed profiles dominated by the oracle
access and interpreter terms below. The physical access envelope is funded
for the aggregate admitted virtual profile, so it cannot create an extra
physical exhaustion after a virtual admission. This proxy is part of the
selected compiler API; an oracle API that supplies no meter-level commit view
requires either a tariff computable from ordinary replies alone or a separate
compiler theorem.

The invariant also needs coordinate coherence. In the baseline compiler all
callers of this occurrence are virtual callers behind this proxy. An
intentionally shared occurrence is admitted only through a fixed multi-client
version of the proxy: ordinary outside callers keep their own budgets, but
every successful call updates the proxy's one authenticated public-coordinate
record before another virtual reservation is evaluated. Direct bypass access
is outside Theorem 5.1.

All tables are sequential.  As for the decoder, fix finite grade-evaluator
and interpreter routine libraries and let
`c_eval,s_eval,c_int,s_int >= 1` be their one-time
elementary-step-to-transition and scratch-cell compilation constants.  A
fixed evaluator, given `1^kappa` and `1^b` on two meter-only read-only
administrative tracks, computes the entries of the fixed grade library and
the virtual quota table.  The simulated programs never receive those tracks
or the table.  Their length, tape heads, and scans are included below through
`M`.  Deliberately loose certificates are

```text
EvalWork(L,M)
  = 128 c_eval (L+M+2)^2,

EvalSpace(L,M)
  = 16 s_eval (L+M+2)^2,

InterpretWork(L,H,M)
  = 8192 c_int H(L+M+2)^2,

InterpretSpace(L,M)
  = 256 s_int (L+M+2)^2.
```

Here `H` bounds component/router transitions, receiver activations, admitted
oracle-access transactions, and one final terminal check. One interpreter or
proxy iteration uses at most `64(L+M+2)^2` elementary sequential-table,
receipt-validation, cache, and configuration operations; the displayed
constant absorbs that routine certificate. The evaluator uses schoolbook
integer routines on the fixed finite polynomial library. Its output table has
`O(L log(M+1))` bits, and its intermediates are bounded by a fixed polynomial
absorbed by harmless polynomial inflation of `M`. Compilation multiplies
elementary work by the corresponding fixed constant. The space bound contains
the virtual configuration, quota table, paired-bit cache, private oracle
receipt, and scratch copies. No unit-cost indirect addressing is assumed.

### 4.4 Simulation invariant

Let `Native(G,omega,c)` be the fixed-tape small-step configuration of decoded
graph `G`, and let `Univ(code(G),Omega,C)` be the universal configuration.
The relation `I` holds when:

1. the decoded graph in `C` is `G`;
2. every virtual control state, tape cell, head position, buffer, call stack,
   and token owner in `C` equals its native counterpart in `c`;
3. the virtual meters, specification public coordinates, public ownership
   labels, and native ledger in `C` equal those in `c`;
4. virtual random bit `(i,j)` equals `Omega[pair(i,j)]`;
5. the external boundary transcript is identical.

**Lemma 4.1 (one-step simulation).** If `I(c,C)` and the native graph takes
one component, router, or admitted specification-access transition
`c -> c'`, the universal component and its fixed administrative faces take a
finite positive number of transitions to a unique `C'` with `I(c',C')`. They
produce no additional ordinary boundary event. If the native transition
produces a boundary event or a terminal `Block`/`Exhaust`, the universal
simulation produces the same virtual event/status before continuing.

**Proof.** Program validation guarantees one applicable native transition or
the specified missing-transition block.  Steps 1--6 locate and perform exactly
that transition.  The paired coordinate supplies the same random bit.
Virtual meter checks are made before the virtual action, in the same order as
native checks. Router transitions are interpreted rather than replaced by a
unit-cost shortcut. For an oracle call, the proxy either reproduces virtual
pre-sample rejection or makes one call to the identically initialized
physical occurrence. Its private commit receipt gives the same exact charge
and next public coordinate, so the ledger/state relation is restored without
revealing that record to decoded code. All other universal transitions modify
only interpreter administrative tapes.

**Theorem 4.2 (finite-trace simulation).** Starting from related initial
configurations, induction on native trace length gives:

1. the same sequence of native boundary events;
2. the same virtual `Success`, `Block`, or `Exhaust` status, including the
   public ownership class of a block/exhaust action;
3. the same native ledger stored inside the interpreter;
4. grade-evaluation and administrative interpreter work and space bounded by
   the functions in Section 4.3.

Finite work, activation, and oracle-call quotas bound this induction by `H`.
If no semantic success or block occurs, the corresponding next primitive
check returns virtual `Exhaust`. Hence only the finite simulation theorem is
required for a metered generated graph.

## 5. Generated-to-fixed compilation theorem

### 5.1 Admitted generated family

An admitted generated family consists of:

- one fixed deterministic multitape generator `G`;
- the fixed libraries of Section 2.2;
- one fixed external typed boundary `B` that every generated graph is proved
  to have; parameter-dependent logical ports must be multiplexed inside
  ordinary messages;
- fixed monotone polynomial bounds

  ```text
  g_work(kappa), g_space(kappa), g_len(kappa),
  P_native^work(kappa,b), P_native^space(kappa,b),
  P_native^traffic(kappa,b), ...;
  ```

- a proof that, for every `kappa`, `G(1^kappa)` returns an accepted graph code
  of length at most `g_len(kappa)` whose decoded boundary is exactly `B`;
- a proof that, after evaluating its fixed grade-library entries at
  `(kappa,b)`, the sum/max aggregate of all component and canonical-router
  quotas, together with every fixed specification dependency's access,
  evaluator, and receipt profile, is at most the corresponding coordinate of
  `P_native`;
- an occurrence-coherence declaration: every fixed stateful specification
  dependency is private to the compiled subsystem, or one fixed charged
  multi-client proxy mediates every intentional outside caller and mirrors all
  public-coordinate commits.

The aggregate proof is semantic certificate data.  A decoder need not solve
the undecidable problem of verifying arbitrary program runtime.  Runtime is
enforced by the decoded virtual meters; adequacy requires the separate
no-exhaustion/productivity proof.

### 5.2 Fixed template

The compiled template is one fixed universal component exposing exactly the
fixed boundary `B`, together with one fixed staging face per boundary port.
Its finite control contains the fixed generator and decoder/interpreter
subroutines. Keeping these as subroutines of one machine avoids an uncharged
internal transmission of the generated code. It has one `initialized` control
bit. On the first external activation the staging face retains the routed
self-delimiting event while the universal component:

1. runs `G`;
2. decodes and validates its graph, including equality of the decoded
   boundary with `B`;
3. evaluates fixed grade-library entries at `(kappa,b)` using the charged
   private evaluator of Section 4.3;
4. simulates the decoded metered graph under Theorem 4.2.

Steps 1--3 occur once, set `initialized`, and are charged before the staged
input is dispatched virtually. The event header gives its encoded length
without copying the payload into universal local state. After decoding, the
interpreter computes exactly the prospective activation charge at the virtual
boundary target. If that charge fails, it records the target's virtual owner
and `Exhaust` status while the payload remains uninstalled. If it fits, the
input length is bounded by the aggregate native space envelope in `M`, and the
adapter copies it once into the virtual input tape.

The staging buffer is canonical infrastructure, not an unbounded free field
of the universal component. In the route-safe algebra it receives the final
whole-graph routing envelope, which includes the closing context's produced
event. Outside that algebra, the compiler theorem requires a separately
declared external-event envelope for the staging face. An arbitrary incoming
value is not falsely bounded by the challenged resource's native profile.
If no external activation occurs, no hidden precomputation is performed or
reported. The decoded virtual graph, all component work tapes, oracle-call
continuations, random positions, meters, and ledger then persist across
external macrosteps. Regenerating the graph or resampling virtual tapes on
every query would denote a different resource.
The selected operational model has no spontaneous pre-input output; a model
with autonomous initialization events would require an explicit initialization
port or initial token.

When a virtual native transition reaches a fixed external port, the universal
component writes the same self-delimiting event on the corresponding physical
port of `B`; those bit-producing transitions are already included in
`InterpretWork`.  When a response arrives, the stored virtual continuation
identifies the suspended node and port.  In particular, calls to a fixed named
specification oracle need no free random-access “oracle array”: the oracle
remains outside the compiler, its state and kernel are unchanged, and its
query, response, call-count, and traffic coordinates are bounded by the
decoded native profile. The fixed private proxy obtains the access
accountant's exact commit receipt and next public coordinate, updates the
virtual ledger, and exposes only the original reply to decoded code. Its
physical receipt work/traffic is part of the compiler profile. The theorem
does not simulate or replicate the oracle.

The ambient workload is represented by a read-only administrative unary track
`1^b`; a separate such track contains `1^kappa`.  Only the private
meter/grade evaluator can inspect the workload track.  The generator receives
`1^kappa`, exactly as in the generated-family definition, and neither decoded
programs nor their virtual input tapes receive `b`.  The `kappa+b+O(1)` input
length, its scanning and heads, polynomial evaluation, and binary quota-table
construction are included in the physical compiler profile through `M`.
Thus no unit-cost metalevel conversion from a binary integer of value `b` is
being assumed.  This is stricter than the baseline metering semantics, where
evaluation of one fixed component grade is external bookkeeping.  The
resulting quotas remain program-invisible, so increasing them cannot alter an
already successful virtual trace.

Each decoded virtual component does receive its own *logical* read-only
parameter track `1^kappa`. Its occupied cells and head count in the aggregate
native space certificate and exact virtual ledger. The universal component
may store their identical immutable contents once and maintain one virtual
head per component; this affects only its physical profile, which is already
allowed to differ from the virtual native ledger. The normalized magnitude
`M` includes the aggregate native space coordinate and therefore dominates
the logical copies as well as the one physical administrative track.

### 5.3 Profile transformer

Let

```text
L = g_len(kappa),
W = P_native^work(kappa,b),
A = P_native^act(kappa,b),
Q = sum_j P_native^calls_j(kappa,b),
H = 1 + W + A + Q,
M = 1 + kappa + b + sum_x P_native^x(kappa,b).
```

Here `x` ranges over every coordinate in the fixed dependency signature,
including public tariffs and oracle evaluator/receipt administration. A valid
compiled work profile is

```text
P_compile^work(kappa,b)
  = g_work(kappa)
    + 128 c_dec (L+1)^2
    + 128 c_eval (L+M+2)^2
    + 8192 c_int H(L+M+2)^2,
```

and a valid peak-space profile is

```text
P_compile^space(kappa,b)
  = g_space(kappa)
    + 16 s_dec (L+1)^2
    + 16 s_eval (L+M+2)^2
    + 256 s_int (L+M+2)^2.
```

The universal component emits exactly the native boundary events, so its
physical boundary traffic and oracle-call profile are bounded by the
corresponding decoded native coordinates. Private oracle receipts add their
fixed codec/validation traffic and work envelope, already included in the
interpreter and dependency-signature profiles. Internal virtual-edge traffic
is retained in the stored *native* ledger but is interpreter work rather than
physical wire traffic; cost-aware equivalence is therefore not asserted.
Physical activations are bounded by native boundary activations (and may
conservatively be reported as that number plus one initialization phase).  The
random profile contains at most
`(L+M+2)^2` master bits, a conservative bound on the paired prefix.  All
displayed functions are fixed polynomials when `g_work`, `g_space`, `g_len`,
and `P_native` are fixed polynomials because the six compilation constants
are fixed natural numbers.  The evaluator-space term also dominates the two
unary administrative tracks and their heads because their combined length is
at most `M`.

### 5.4 The theorem

**Theorem 5.1 (generated-to-fixed compilation).** Every admitted generated
family has a fixed-template uniform implementation satisfying the component
profile in Section 5.3 plus the ordinary staging/routing and fixed
oracle-accounting profiles, under its occurrence-coherence declaration. At every
`(kappa,b)`, in a route-safe closing graph or under a separately supplied
external-event envelope for the fixed staging faces:

1. the universal implementation and the decoded native graph have the same
   erased transcript law in every such compatible context;
2. they have the same virtual terminal status and native ledger under the
   master-tape/derived-tape coupling;
3. their *physical* cost reports can differ, but the universal report is
   bounded coordinatewise by the explicit compiler profile while the exact
   virtual native ledger is retained separately;
4. strong, almost-sure, or overwhelming native no-exhaustion and productivity
   transfer to the universal implementation when its external compiler meter
   dominates the displayed profile.

**Proof.** On the first external activation, generator validity gives an
accepted code within `g_work`; Lemma 3.1 gives the decoded graph within the
decoder term, while the physical input remains in the charged route-safe
staging buffer. The header and decoded virtual grade determine the same
prospective native activation check. On rejection, no payload is installed
and the virtual owner/status agree. On admission, its length is at most the
native space envelope in `M`, so one charged copy installs the same virtual
input. The pairing map turns the master
fair tape into the required product of virtual tapes.  Theorem 4.2 gives
pathwise trace/status equality and the interpreter bounds.  Pushforward
through the pairing map gives equality of transcript laws. The physical
oracle proxy first reproduces the virtual reservation decision, then makes
exactly one identically seeded physical call and mirrors its private commit
receipt; hence state, public coordinate, exact charge, block, and owner agree.
If the occurrence is intentionally shared, the declared multi-client proxy
has already mirrored every intervening outside commit; no caller may bypass
it.
The physical compiler ledger is bounded by the sum of the generator, decoder,
evaluator, admitted-input, interpreter/proxy, and separate staging/routing
profiles. The local installed-input term is dominated by `M`; the possibly
oversized rejected event remains in the separately funded staging buffer.
The event bound `H` includes activations and oracle calls as well as machine
and router work. Under those bounds the compiler itself does not exhaust, so
native progress and no-exhaustion events transfer.

## 6. Polynomially many logical copies

The compiler is not needed merely to express `q(kappa)` logical sessions.  One
fixed component can keep a sequential table with `q(kappa)` records.  What
must be charged is not just table construction but every later dispatch.

Suppose:

- `q(kappa)` bounds the number of live logical sessions;
- `A(kappa,b)` bounds the total number of session activations;
- `L_s(kappa,b)` bounds an encoded session record;
- one fixed session program has native work bounded by
  `P_s(kappa,b,L_s)` per activation, or a separately proved fixed polynomial
  `P_sessions(kappa,b)` bounds all session-native work in aggregate.

A simple linear-table dispatcher has the conservative profile

```text
TableInit
  <= 16 q(kappa)(L_s(kappa,b)+log_2(q(kappa)+1)+1),

TableDispatch
  <= 32 A(kappa,b) q(kappa)
       (L_s(kappa,b)+log_2(q(kappa)+1)+1),

TotalWork
  <= TableInit + TableDispatch + P_sessions(kappa,b),

PeakSpace
  <= 8 q(kappa)(L_s(kappa,b)+log_2(q(kappa)+1)+1).
```

One simple valid choice is

```text
P_sessions(kappa,b)
  = A(kappa,b) P_s(kappa,b,L_s(kappa,b)).
```

The linear factor `q` in every dispatch is essential for this sequential
multitape implementation.  Claiming logarithmic lookup without a charged
random-access or balanced-tree implementation would launder cost.  The
functions `q,A,L_s,P_s` and the table algorithm must all be fixed syntax; an
indexed collection of unrelated `P_i` would merely reintroduce nonuniformity.
Under these premises the four bounds are fixed polynomials and logical
replication remains uniform.

## 7. Failure modes excluded by the theorem

The theorem rejects all of the following.

1. **Arbitrary family:** no single fixed generator exists.
2. **Hidden advice:** the generator code depends on `kappa`.
3. **Growing exponent:** node grade syntax introduces a polynomial degree not
   bounded by the fixed grade library.
4. **Only per-node bounds:** graph size or the sum of quotas has no aggregate
   polynomial.
5. **Free initialization:** generator, decoder, code, and graph tables are not
   charged.
6. **Free routing:** the universal machine skips native bit-costful routers.
7. **Randomness collapse:** virtual nodes accidentally share one sequential
   stream or resample at every activation.
8. **Cost preservation overclaim:** behavioral equivalence is misstated as
   equality of native and interpreted physical ledgers.
9. **Uncharged table lookup:** polynomially many logical sessions are treated
   as unit-cost random-access memory.
10. **Meter-as-correctness:** the aggregate native quota is mistaken for a
    proof that the decoded graph answers before exhaustion.
11. **Oracle-charge blindness:** the interpreter tries to reconstruct a
    stateful tariff from the ordinary reply even though its next public
    contract coordinate is meter-only, or obtains that coordinate on a
    program-visible uncharged wire.

## 8. Remaining implementation-level refinement

The polynomial exponents and numerical elementary-routine coefficients in
Sections 3 and 4 are conservative certificates for the specified sequential
algorithms.  The only unspecified quantities are the six fixed compilation
constants obtained when the finite scan/copy/evaluation routine library is
expanded to
literal transition records.  A machine-checked transition table could compute
them and perhaps replace the bounds by smaller ones.  The theorem does not
depend on their values.  The mathematical obligations needed by the paper are
therefore explicit: self-delimitation, validation, finite routine compilation,
simulation invariant, random-tape product coupling, aggregate profile
transformation, and separation of behavioral from cost-report preservation.
