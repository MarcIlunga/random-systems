# A concrete processor--store--coin refinement

This note fixes one explicit computation-resource API and discharges the
administrative-trace erasure obligation for that API.  The construction is
deliberately sequential.  It is a lower implementation of the single-token
multitape model in the paper, not a claim that this is the unique or most
physical processor model.

The motivation from Maurer--Renner is only the modeling discipline: when
computing power or memory matters, it belongs in the resource, and converters
merely route information and select a program.  Their paper does not define
the resource API below.  In particular, all claims about atomic reservation,
cell capacity, failure, and administrative cost are claims of the present
model.

## 1. The theorem to be proved

Fix a well-typed bit-costful machine program `P`, a public owner label `v`, and
native bounds

```text
B_v = (T_v, A_v, R_v, S_v, ...),
```

where `T_v` bounds committed machine transitions, `A_v` bounds activations,
`R_v` bounds random-tape reads, and `S_v` bounds the native live-cell
footprint.  The omitted coordinates are the existing edge-traffic and named
specification-call bounds.

The native cost convention is part of the theorem.  A router first commits its
copy and original-edge traffic.  Receiver activation is then one
receiver-owned primitive charge which jointly installs the input, increments
`act_v`, and checks the resulting peak.  A machine transition similarly
checks `step_v`, any current-cell random read, and prospective peak as one
owner-`v` charge.  Rejection commits none of those receiver/transition
coordinates or state changes.  A different primitive-event split needs a
correspondingly modified transaction protocol.

We construct a private administrative network

```text
E_v(P,B_v)
  = Drive_P [
      PROC_v[P;T_v,A_v,L_v]
      || STORE_v[S_v]
      || COIN_v[R_v]
    ],
```

where `L_v >= |code(P)|`.  Its external ports are exactly the ports of `P`.
The three resource APIs and all administrative wires are private after
connection.  `Drive_P` is a fixed tag-routing adapter; its subscript records
the native port typing and is not a program image.  It has no mutable protocol
state and stores or transmits no program bit.

For a network `N`, let `E(N)` replace every machine occurrence `v` by
`E_v(P_v,B_v)`, alpha-renaming every private administrative name.  It leaves
ideal specification occurrences and the original external or inter-component
edges in place.

The target statement is pathwise:

```text
erase_admin(E(N)_B) = N_B,
pi_native(Cost_E(rho_hat)) = Cost_N(rho).
```

Here `rho_hat` is the explicit-resource run corresponding to the native run
`rho`; `erase_admin` contracts each finite administrative transaction;
`pi_native` retains committed transitions, activations, random reads, native
logical live space, original-edge traffic, and original specification calls.
It drops newly exposed program-storage and administrative coordinates.

The equality includes `Success`, `Block`, and owner-labeled `Exhaust`, not
only successful traces.  The theorem is first proved for fixed random tapes
and initial specification states.  Equality of the induced kernels then
follows by pushing forward the same product measure.

## 2. Native transition normal form

The API is easiest to state for the machine convention already used in the
paper.  A native configuration records:

- finite control and mode;
- the input tape and its head;
- finitely many finite-support work tapes and their heads;
- the output register and its write/read position;
- the position on the named random tape.

A transition sees only a fixed local frame: the control state, scanned input,
work, and output-register symbols, and, when requested, the current random
bit.  Numeric head positions remain in the store and are not part of the
frame.  The transition changes a fixed number of cells and heads and returns
one of:

```text
Internal(update)
Emit(port, update)
Block(update).
```

`Emit` names the already constructed output register.  It does not alias a
work tape or create an unbounded string in one processor transition.
The selected output register uses the paper's canonical buffer convention:
it is blank on activation, and a well-typed `Emit` state contains one
self-delimiting code contiguously from its designated origin.  If a source
machine uses an arbitrary sparse output tape, it must first run the ordinary
charged copy/normalization routine into this buffer; that transformed native
ledger is then the one refined below.

The random instruction has the form `read(advance?)`.  It returns the current
bit and optionally advances the random head.  Thus repeated non-advancing
reads return the same bit but are distinct charged reads.  If one instead
starts from a fresh-bit-only machine, this instruction is unnecessary.  If
one starts from a machine that can inspect a tape cell repeatedly for free,
cache the inspected bit in one work cell; that is a separate constant-overhead
normal-form compilation and its transformed ledger must be used.

Let `live_P(c)` be exactly the native live-cell quantity used by the original
meter.  The refinement does not silently replace it with allocated address
range, word-RAM space, or a physical byte count.

The output convention also gives an amortized reach bound which is needed
below. For fixed `P` there is a constant `lambda_P` such that every native run
prefix satisfies

```text
sum_{attempted Emit events e} (encodedLength(e)+1)
  <= lambda_P * (1 + Acts + Steps).
```

The sum includes an emitted value whose unchanged downstream router later
rejects it. Indeed, the output register is blank at activation, is not aliased
to an input/work tape, and an ordinary transition changes only a fixed number
of cells and moves every head by at most one. Charge every reached output
position since the last blanking activation to the transition that writes it
or first moves an output head to it. Suspension after `Emit` gives at most one
attempted output per activation. Summing over activations proves the display.
This is why the normal form matters: without blanking, non-aliasing, and local
head motion, output scans need not be affine in native work.

## 3. The selected resource APIs

### 3.1 `PROC[P;T,A,L]`

`PROC[P;T,A,L]` is the initialized transition-token resource for the selected
multitape instruction set.  Its initial and terminal resource state contains
one read-only coordinate equal to the canonical self-delimiting `code(P)`,
whose length is at most `L`.  There is no program-loading interface in the
selected theorem.  Thus indexing the resource by `P` is not a license to
store the transition table in a converter's finite control: the full explicit
report charges the processor's code coordinate once.

Its public resource state consists only of:

- remaining transition and activation tokens;
- the immutable program code and its declared length;
- one fixed-size reservation flag.

It contains no mutable machine configuration, work tape, input or output
buffer, and no random source.  Because the global execution has one token,
there is at most one outstanding reservation.

The private API is:

```text
reserveWake(frame)              -> wakeCap | Exhaust(v)
reserveStep(frame)              -> stepCap(kind) | Exhaust(v)
plan(stepCap, frame)            -> command | NeedCoin
planCoin(stepCap, frame, bit)    -> command(with advance flag)
commitWake(wakeCap)             -> Ack
commitStep(stepCap)             -> Ack
```

`frame` has constant size for fixed `P`: it contains only control, mode, the
scanned input/work/output symbols, and fixed administrative tags.  `plan` is
the transition table lookup.  A reservation makes a token
unavailable to a second
transaction but does not yet decrement the committed-token ledger.  A commit
cannot fail.  Every capability is linear; the resource rejects replay or use
in the wrong phase.  Since the private driver is the only caller, no external
context can use free planning calls as a computation oracle.

The resource is not an implementation claim about silicon.  One committed
step means one transition of the selected multitape model.  The earlier
universal-interpreter theorem translates this coordinate to another effective
machine with its stated overhead.

The unique program store and counters are not declared physically free.  The
explicit report includes at most
`L + O(log(T+1)+log(A+1))` bits of processor-resource state in addition to a
fixed reservation tag.  The transition-token API treats manipulation of this
state as primitive.  Refining that primitive into gates, energy, or a
lower-level memory hierarchy would be a further layer.

#### The distinct loaded variant

A generic loader cannot be obtained merely by saying that `Drive_P` “selects”
`P`.  It requires either a charged boundary event carrying `code(P)` or a
separate source such as

```text
IMAGE_v[P,L] || PROC_v[blank;T,A,L].
```

For a copying loader, `IMAGE` owns its source copy and exposes a sequential
read interface; the blank processor owns `L` reserved destination bits.  A
route-safe initialization first validates the self-delimiting length and
reserves the complete destination, validation, traffic, and work envelope.
It then streams the code, checks the canonical instruction syntax, and commits
the immutable program coordinate atomically before the first native
activation.  For fixed instruction encoding there are constants
`c_load,d_load` such that it needs at most
`c_load(|code(P)|+1)` work, `d_load(|code(P)|+1)` private traffic, and
`O(log(L+1))` scratch beyond the streaming cell.  During a copy the full peak
contains both the charged source and destination copies; an erasing source or
ownership-transfer wire is a different resource API and needs its own
refinement theorem.

If the image is valid and this initialization envelope is funded so loading
cannot be the first exhaustion event, contracting the finite initialization
prefix leaves exactly `PROC[P;T,A,L]`, after which the theorem below applies.
Invalid or oversized code, a publicly callable reload operation, and
load-time leakage are deliberately outside the selected theorem.  In
particular, no generic-loader claim is made without an explicit source,
tariff, and initialization policy.

### 3.2 `STORE[S]`

`STORE[S]` owns the entire mutable native configuration except the random tape
and its head, and it also owns immutable native parameter/auxiliary tracks.
It stores finite control, mode, input/work/output tapes, all ordinary heads,
and the pending external port.  In a uniform family, the occupied unary
parameter cells and their head are included in the initial live state. Its
logical capacity test is exactly

```text
live_P(c') <= S.
```

The store never evaluates a program transition.  Its only operations are:

```text
accept.prepare(port,length) -> wakeFrame, storeWakeCap | Exhaust(v)
frame()                     -> localFrame
update.prepare(command)     -> storeStepCap | Exhaust(v)
commitWake(storeWakeCap)    -> native active configuration
commitStep(storeStepCap)    -> Internal | Emit(port,value) | Block(v)
```

`update.prepare` applies a constant-size local update tentatively and checks
the prospective native live footprint.  It does not make the update visible.
`commitStep` cannot fail.  On `Emit`, it exports the finite output register
and suspends; on `Block`, it enters the same terminal lower stop as the native
machine.

The store contract has a private meter-readable charging coordinate for an
outstanding capability.  For `storeStepCap` it records only the prepared
outcome tag, port class, and exact encoded output length `ell` (zero for an
internal step or block); the driver receives an opaque fixed-size capability,
not this summary or the output.  Consequently the access meter can reserve
the exact commit-response and administrative-routing envelope
`u_P+v_P*ell` before any primary commit.  The fallback bound
`ell<=c_P(S+1)` proves bounded accessibility, but the refinement theorem does
not reserve that worst case on every step.  Doing so could reject a late
small output merely because `S` no longer fits in the remaining
administrative budget.

The length is not obtained by an uncharged random-access query.  Only when
the prepared outcome is `Emit`, the store's private access procedure scans
the prepared contiguous self-delimiting buffer once, without copying or
committing it, and writes the binary length into the charging view.  Fixed
codec constants bound this tariff by `u_len+v_len*(ell+1)` work and
`O(log(S+1))` scratch.  Well-typedness guarantees that the scan finds a valid
terminator.

This response-dependent scan is not allowed to discover an exhausted
administrative meter after the primary reservations have succeeded. At
initialization the private access meter dedicates, without committing used
work or traffic, a coordinatewise output pool

```text
OutPool_P(A,T) = g_P * lambda_P * (1+A+T)
```

for a fixed codec/routing constant `g_P`. The output-reach bound above proves
that all actual scan steps and all private store-to-driver output bits fit in
that pool. They consume and report only their exact costs. Internal and block
outcomes consume none. This is not a fresh worst-case `c_P(S+1)` reservation
on every step, so a late small output is not rejected because the full store
capacity is unavailable. The uncommitted pool capacity and its counter are
part of `B_exp` and the explicit physical state.

The store also has fixed administrative control recording one of finitely many
transaction phases and one constant-size pending frame or command.  This is
not hidden free memory.  It is reported separately as `adminSpace`.  For fixed
`P` it is at most a constant `h_P` in addition to the native logical cells.
An incoming payload is either still in the charged routing buffer or has
become the native input tape; it is not duplicated without being counted.

No reset, snapshot, leakage, secure-erasure, or concurrent-access operation is
present.  Adding any of them changes the resource specification and requires a
new theorem.

### 3.3 `COIN[R]`

`COIN[R]` owns one named infinite bit tape, its head, a remaining-read count,
and one fixed-size reservation flag.  Its tape is sampled from the same law as
the native named tape.  Its private API is:

```text
reserveMode(use?)             -> coinCap(bit) | Exhaust(v)
commitRead(coinCap,advance?)  -> Ack.
```

A genuine read reservation non-destructively returns the current bit and
prevents a second outstanding read.  A no-read request has the same padded
message shape, returns a fixed dummy bit, cannot fail, and locks no read
capacity.  A genuine commit consumes one charged read and advances the head
iff requested by the actual post-bit command.  The flag is deliberately not
supplied at reservation time: in the native transition table it may depend on
the bit just returned.  A failed later reservation ends the whole run, so the
speculatively exposed bit never reaches an external port.  Capabilities are
linear and cannot be replayed.  No converter, processor, or store has a second
private random tape.

The sampled infinite tape is the ideal randomness supplied by this resource,
not an asserted finite-memory implementation.  Its mutable control state is
one cached current bit, the head/read counters, and a reservation tag, using
`O(log(R+1))` ordinary bits over an admitted run.  A hardware RNG or
pseudorandom expansion is a different lower realization of `COIN`.

Different machine occurrences receive differently named `COIN` resources.
Their tapes have product measure unless sharing is represented by connecting
the components to one common randomness resource.

### 3.4 `Drive_P` and administrative routing

`Drive_P` is generated from a fixed finite wiring template.  It:

- renames the native ports;
- routes tags and payloads between the three private APIs; and
- exposes no administrative endpoint.

The connection is to the already program-indexed processor.  The subscript
`P` records the native port schema and fixed renaming only; the driver carries
neither `code(P)` nor a program handle.  Its executable transaction schema is
the same fixed reserve/plan/commit router.  For generated families the
compiler first reduces the varying graph to one fixed universal executable,
so this port schema does not vary with the security parameter.

It does not branch on a payload except by a finite tag dispatch, retain a
payload between activations, evaluate a transition, sample a coin, or inspect
a remaining quota.  Every dynamic phase, frame, and pending continuation is
in `STORE` or in the unique in-flight administrative message.  In particular,
the return destination is carried by a fixed tag; it is not remembered in a
hidden adapter register.

Only the native ports remain externally accessible after attachment.  Giving
another party direct access to the private processor, store, coin, or
transaction interfaces defines a shared-resource model and invalidates this
encapsulation theorem.

Administrative copying and routing remain ordinary bit-costful
infrastructure.  They receive the route-safe envelope derived from the native
grade and the fixed protocol below.  Consequently they cannot be the first
exhausted occurrence.  Their exact work, traffic, and peak buffer use remain
visible in the explicit cost report.

### 3.5 Measurability and bounded access

The selected nodes fit the paper's specification-access discipline rather
than becoming untyped magic calls.

- Finite-support tape configurations, integer heads, finite control, and
  finite counters form a countable standard-Borel state space.
- The coin tape is `{0,1}^N` with its product Borel structure and a countable
  head.  Current-bit evaluation and optional head advance are measurable.
- Program lookup, local tape update, capacity comparison, capability
  validation, and all codecs are effective.
- For fixed `P`, processor/control replies have fixed length and a coin reply
  has one payload bit.  A store output has encoded length at most
  `c_P(S+1)` for a fixed alphabet/codec constant.

The route-safe driver/meter pre-reserves call, traffic, and administrative
tariffs from these strong public envelopes. Fixed control calls use their
fixed envelopes. The output pool is dedicated once from the static
activation/transition quotas before the first protocol action; the prepared
store commit then takes an exact sub-capability from it using the private
charging coordinate. The `c_P(S+1)` bound remains the public per-call
accessibility envelope, not a repeatedly consumed worst-case charge. A
resource response therefore creates no new local budget and no unbounded
message. This is accessibility of the selected primitive resources, not an
implementation of their internal capacity checks in a still lower machine.

## 4. Why direct sequential calls are incorrect

The tempting implementation

```text
decrement CPU;
read COIN;
try STORE update
```

is not a refinement of the native meter.  Suppose the prospective update
crosses the space bound.  The native external meter rejects the one primitive
transition before changing its ledger or random head.  The direct
implementation would already have consumed a processor token and possibly a
coin.  It would therefore report a different cost and could expose a different
first exhausted owner.

Reserving worst-case space before reading the coin is also wrong.  It can
reject a run whose actual random branch fits.  Sampling a fresh coin and then
rolling it back is wrong when the coin source is shared or its access trace is
observable.

The selected API therefore uses a two-phase transaction.  Reservation may
lock a token, but only a successful all-resource prepare phase commits any
native coordinate.

## 5. Administrative protocols

### 5.1 Activation

Delivery of a native external or hidden event is simulated as follows.

1. The self-delimiting event header exposes the validated port and encoded
   length while the payload remains in the charged routing buffer.
2. `STORE.accept.prepare(port,length)` reserves, but does not yet fill, the prospective
   native input cells.
3. `PROC.reserveWake` reserves one activation token.
4. The private meter reserves the exact remaining input-copy and fixed commit
   costs from the known length.
5. If either primary reservation fails, the whole run ends with `Exhaust(v)` and no
   native coordinate is committed.
6. Otherwise the route-safe adapter copies the payload once into the reserved
   input region, and `PROC.commitWake` and `STORE.commitWake` run in that
   order.  None can fail.  The store is now exactly the native active
   configuration.

If the native labeling convention tests the activation token before the
space coordinate, the prepare order is swapped.  Both rejecting resources
carry the same public owner `v`, so this affects no owner-level theorem; the
order must nevertheless be fixed for a finer subowner report.

The external or original-edge traffic has already been charged before
activation on both sides.  The additional private copy is an administrative
coordinate.  Computing the prospective footprint from a validated length and
the current local footprint is part of the selected store-capacity primitive;
the copy itself is not atomic or free.

### 5.2 Deterministic transition

For a transition not inspecting the random tape:

1. `STORE.frame` sends the local frame to `PROC`.
2. `PROC.reserveStep` reserves one transition token and classifies the
   instruction as a no-read operation.
3. `COIN.reserveMode(false)` returns a padded dummy response without
   reserving read capacity.
4. `plan` returns the native command, and `STORE.update.prepare` checks its
   exact prospective live footprint. On `Emit` only, the already dedicated
   output pool grants an infallible scan capability; the store charges the
   actual linear scan of the prepared contiguous code and writes its exact
   length into the charging view. The private meter then takes the exact
   output-passage sub-capability from the same pool and reserves every
   remaining fixed commit cost.
5. On any failure, the run ends with `Exhaust(v)` and no native reservation
   is committed.
6. Otherwise the no-read acknowledgement, `PROC.commitStep`, and
   `STORE.commitStep` run in order.

The final store commit either starts the next internal transaction, emits the
same typed event as the native step, or produces `Block(v)`.

### 5.3 Random-reading transition

For a transition inspecting the current random bit:

1. reserve the processor transition as above;
2. `COIN.reserveMode(true)` checks the random-read quota and returns the actual
   current bit without advancing;
3. `PROC.planCoin` computes the command and its actual advance flag for that
   bit;
4. `STORE.update.prepare` checks that actual command, not the other branch,
   and, on `Emit`, consumes the same already dedicated output-pool capability
   for the actual prepared-buffer scan, exposing its exact commit length only
   to the private access meter;
5. take the exact output-passage sub-capability and reserve the remaining
   fixed commit/API costs;
6. if all reservations succeeded, commit `COIN` with that flag, then `PROC`,
   then `STORE`.

All commits and their private delivery paths are infallible because both
primary capacities and all remaining administrative charges were reserved.
The derived administrative envelope ensures that the latter reservation
never rejects in `E(N)_B`; its purpose is to make the call ordering explicit,
not to add another native failure branch.  The store commit is last, so no
boundary event or next native transition can occur between primary commits.
The output-pool invariant is what justifies “never”: it is established from
the static native quotas before execution, and the reach lemma charges even a
value whose next original-edge reservation will fail.

Every pre-commit control message has a fixed padded encoding for the selected
program.  The no-read and genuine-read modes, and both random branches, use
the same number and size of `planCoin`, reservation, and commit messages.
Thus whether a read occurs and the secret coin itself cannot leak merely
through branch-dependent administrative traffic.  The final native command
may of course change native output, space, or failure exactly as the original
transition does.

The intermediate states are not native states.  They are related to the same
pre-transition native state plus a transaction phase.  This is a stuttering
simulation, not a lock-step bisimulation at every administrative event.

### 5.4 No new divergence

A phase index alone is insufficient because an admitted input/output copy and
the prepared-output scan contain a data-dependent finite number of bit
microsteps. Give every private state the lexicographic rank

```text
(phaseSuffix, remainingAdmittedMicrosteps),

prepare frame > reserve processor > reserve coin
  > plan > reserve store/scan > commit coin
  > commit processor > commit store.
```

Within a phase, every bit-copy or scan action decreases the second coordinate.
Moving to the next phase strictly decreases the first coordinate, regardless
of the newly installed finite second coordinate. Reservations either answer
or produce a terminal lower stop; admission supplies a linear capability
whose encoded length fixes the second coordinate; commits cannot block or
fail. The no-read acknowledgement occupies the same fixed phase as a coin
commit.

Consequently one native primitive expands to at most

```text
k_P + c_in,P * inputLength + c_out,P * outputLength
```

private microsteps, not a length-independent number of microsteps. Every
length is finite and pre-admitted, so the lexicographic rank is well founded
and the translation cannot create an administrative livelock. This is the
progress certificate needed by the adequacy layer; merely observing that
every resource call has a meter would not suffice.

## 6. Component simulation theorem

Define a relation `c ~ c_hat` at transaction boundaries by:

1. the logical state stored by `STORE` is exactly the native configuration
   `c`, apart from the random position;
2. the `COIN` tape and head equal the native named tape and random head;
3. committed processor activations and steps equal the native `act_v` and
   `step_v` coordinates;
4. committed coin reads equal `rand_v`;
5. no reservation is outstanding and the private phase is idle; and
6. the explicit logical-space maximum equals the native `peak_v`, and the
   projected simultaneous global peak equals the native `gpeak`.

### Theorem 6.1 (one-transition stuttering simulation)

Fix the named random tape and native quota vector.  If `c ~ c_hat`, then:

- a native activation accepted by its meter corresponds to the finite
  activation protocol and reaches related active states;
- a native transition accepted by its meter corresponds to one finite
  administrative transaction and reaches related successor states;
- if the native transition emits, blocks, or remains internal, the explicit
  transaction has the same case after administrative erasure; and
- if the native meter rejects the primitive event, the explicit prepare phase
  ends in `Exhaust(v)` before any native coordinate commits.

#### Proof

For activation, `accept.prepare` computes exactly the native prospective
input-tape state, while `reserveWake` tests exactly the activation coordinate.
The two reservations therefore succeed iff the native joint charge fits.
Infallible commits establish clauses 1, 3, 5, and 6 of the relation.

For a transition, equality of the stored local frame and program code gives
the same transition-table case.  In the random case, equality of tape and
head gives the same bit.  The selected command is consequently the native
command.  `update.prepare` evaluates exactly `live_P(c')`, while the processor
and coin reservations test exactly the step and read coordinates.  Its
private charging view supplies the exact output length. The output-reach
invariant makes both the scan and exact output sub-capability fit in the pool
dedicated at initialization, and the derived administrative envelope makes
every other API/route reservation fit.
Thus the primary reservations succeed iff the native primitive charge fits.
On success,
commit order changes no selected command and establishes all six relation
clauses.  `Internal`, `Emit`, and `Block` follow directly from the final
command.  On failure no native reservation commits, and every possible
rejector carries owner `v`.

This argument uses atomic ownership of all coordinates updated by one native
primitive event.  A model exposing distinct CPU, store, and coin failure
owners needs either a declared deterministic rejection priority and a refined
native label or a coalescing map back to `v`.

### Theorem 6.2 (component trace and ledger)

From related quiescent states, fold Theorem 6.1 over the unique native
small-step run.  Every finite native prefix has a unique finite explicit
prefix.  At every transaction boundary,

```text
pi_native(Cost_explicit) = Cost_native.
```

The first native visible event, `Block(v)`, or `Exhaust(v)` is therefore the
first corresponding event after administrative erasure.  Conversely, the
phase-rank argument shows that an explicit run cannot have another
non-administrative outcome.

For an unmetered infinite native run, the explicit run is infinite as well.
For finite positive quotas, both executions reach the same native terminal
case; the explicit run cannot diverge inside one transaction.

## 7. Network and probabilistic lifting

Replace each machine occurrence independently and retain every original typed
edge.  The private names introduced for different occurrences are disjoint.
When the native token is owned by `v`, the explicit token executes only the
private transaction of `E_v`; all other stores and resources are passive.

### Theorem 7.1 (network macro refinement)

For every well-typed single-token native network `N`, fixed tuple of named
random tapes, fixed selected oracle randomizations, fixed initial
specification states, and fixed quota vector `B`,

```text
erase_admin(E(N)_B) = N_B
```

as maximal owner-labeled transcript semantics.  At every corresponding finite
prefix,

```text
pi_native(Cost_E) = Cost_N.
```

#### Proof

Use Theorem 6.2 while one occurrence owns the token.  A native hidden or
boundary emission is produced only by the last store commit, after which the
original canonical edge performs exactly the same delivery.  The next
component therefore begins in the state corresponding to the native
successor.  Induction covers finite successful prefixes, block, and
exhaustion.  An infinite native hidden-transfer or internal-step sequence
lifts to an infinite explicit sequence because every native step has a finite
nonempty implementation.  Conversely, the well-founded lexicographic rank in
phase suffix and remaining admitted scan/copy microsteps rules out a new
infinite administrative suffix.

The proof is insensitive to cyclic connection: it follows the unique token
rather than inducting over graph topology.  Ideal-resource calls are
unchanged external events of the replaced component, so their selected
kernel, tariff, seed, and initial state are identical on both sides.

### Corollary 7.2 (kernel equality)

Name each `COIN_v` tape by the native random-tape name and use the same product
measure and the same selected oracle randomizations and initial states.
Theorem 7.1 is pointwise in this sample.  Pushing the common measure through
the equal erased transcript map gives equality of the metered experiment
kernels.

The corollary does not require an independent resampling argument and does not
silently assume deterministic initial specification states.

## 8. Administrative cost and efficient families

The refinement exposes costs which the native projection deliberately did not
contain.  For fixed `P`, there are constants
`a_P,b_P,c_P,d_P,e_P,h_P` such that every finite explicit prefix satisfies

```text
AdminWork
  <= a_P
     + b_P Acts
     + c_P Steps
     + d_P Coins
     + e_P OriginalTraffic,

AdminTraffic
  <= a_P
     + b_P Acts
     + c_P Steps
     + d_P Coins
     + e_P OriginalTraffic,

AdminSpace
  <= h_P + MaxInFlightOriginalEvent + O(log(S+1)).
```

Here `OriginalTraffic` includes every original/boundary payload bit whose
delivery reaches a native activation. Its coefficient pays the one necessary
private input passage. Output scans and the private store-to-driver output
passage are instead charged to the `Acts`/`Steps` coefficients using the
output-reach lemma. This distinction is necessary: an output is attempted
before its unchanged downstream router decides whether to commit original
traffic, so a rejected output cannot be bounded by *committed*
`OriginalTraffic`. Control frames and commands are constant-size and padded
independently of a secret random branch. No input payload is copied into two
persistent buffers. The logarithmic space term stores the exact prepared
output length used by the private charging view; it is not a second payload
copy. At a prefix strictly inside the current transaction, `a_P` also covers
the one reserved-but-not-yet-committed local action; there is only one under
the global token.
The initialized presentation already charges its unique `code(P)` coordinate.
The distinct loaded variant described in Section 3.1 additionally charges its
source, linear initialization work/traffic, logarithmic scratch, and the
source/destination overlap; none is hidden in the driver.

The full explicit space report also contains processor program/counter state,
coin control state, meter counters, a serialization of the live tape map and
numeric ordinary tape-head coordinates, and the one active routing buffer.
Let `K_P` be the fixed finite set of counter coordinates owned by this
explicit bundle and its private access meter: it includes transition,
activation, random-read, logical-space, administrative work/traffic, and
reservation/output-pool coordinates. Extend the native budget by the derived
administrative envelope and write

```text
CtrBits_P(B_exp)
  = sum_{x in K_P} ceil(log_2(B_exp[x]+1)).
```

Storing both used and remaining values changes this only by a fixed factor.
Original-edge and named-specification meters that remain outside the bundle
are already serialized once in the surrounding graph and are not duplicated.
Let `H_P` be the fixed number of ordinary heads of `P`.  Under the selected
standard initialization, input is placed contiguously at the origin and every
head starts at a designated origin.  Each transition moves a head by at most
one.  Consequently every live-cell or head coordinate has signed magnitude at
most `T+S+1`.  A canonical sparse serialization has at most `S` cell records;
the tape index and alphabet symbol have fixed size, and every coordinate takes
`O(log(T+S+2))` bits.  For fixed `P`, the complete explicit-state encoding
therefore contributes

```text
L + CtrBits_P(B_exp)
  + O((S+H_P) log(T+S+2))
  + h_P
  + MaxInFlightOriginalEvent
```

This is a terminal-report/representation bound, not a change to the primary
`STORE[S]` capacity: the latter still counts exactly native logical live
cells.  Exact coefficients depend on the selected self-delimiting integer
codec and are not identified with `peak_v`.  The random-tape coordinate is
already covered by `log(R+1)`; the sampled infinite tape is an ideal
randomness resource and is not serialized.  The extra sparse-map and head
terms are necessary precisely because the native live-cell convention counts
support and registers, not the bit length of absolute coordinates.

The full explicit `gpeak` includes program images, counter encodings,
transaction scratch, prepared store state, and in-flight administrative
messages at the times they coexist.  The cost projection maintains a separate
native `gpeak`, updated only from related native configurations at transaction
boundaries and unchanged original-edge routing states.  Thus exact native
global space is preserved without pretending that the larger physical
simultaneous peak vanishes.

The per-bundle expression above also gives an explicit conservative bound for
a fixed *closed* translated graph. Let `Event_N` dominate every original or
private in-flight event under the final route/staging envelope, and let
`Infra_N` dominate the serialized state and counters of all fixed routers,
staging faces, and shared meters not already assigned to a bundle. Then

```text
PhysGPeak(E(N))
  <= Infra_N
     + sum_{v in N} [
         L_v
         + CtrBits_(P_v)(B_v^exp)
         + O((S_v+H_(P_v)) log(T_v+S_v+2))
         + h_(P_v)
         + Event_N
       ].
```

This intentionally overcounts the unique live token/message once per fixed
bundle. It is still a pointwise bound on every physical configuration:
persistent code, counters, and store states coexist and are included in the
sum, while any active transaction and routing buffer fit within the
overcounted administrative/event terms. The exact physical `gpeak` continues
to be measured from configurations; this display is only a funding envelope.
For the fixed normalized graph, a finite sum of the final polynomial profiles
is polynomial. An open component cannot use its own grade to bound an
arbitrary hostile boundary event; the formula is deliberately relative to the
closed route-safe or explicitly staged envelope.

If arbitrary finite-support initial configurations are supplied instead, the
serialized initial coordinate map is charged as input and initial space.  A
bound in terms of `S` alone would be false for such inputs.

For a pure uniform family, `P` is one fixed code receiving `1^kappa` and the
public auxiliary input, so the constants are independent of `kappa`.

For the secondary generated-*network* presentation, the order of refinement
matters.  First use the generated-to-fixed compiler to obtain one fixed
universal implementation with its physical decoder/interpreter profile.  Then
apply `E` to that one universal occurrence.  Substituting the compiler's fixed
polynomial profile into the administrative bounds again gives fixed
polynomials.  The universal store contains the generated code and virtual
configurations as charged data, and the universal coin resource supplies the
master tape used by the proved Cantor splitter.

Directly translating each decoded node would create a
parameter-dependent number of `PROC`, `STORE`, and `COIN` specification
occurrences.  The implementation generator is not licensed to manufacture
those ideal resources.  Such a presentation would require a separately fixed
indexed product-state computer resource, effective multiplexer, and aggregate
tariff.  Arbitrary parameter-indexed APIs are not admitted.

### Corollary 8.1 (efficient refinement)

If a primary fixed-template native family has polynomial grades, or if a
generated family first satisfies the generated-to-fixed compiler theorem,
then its ordered explicit-resource translation has polynomial processor,
store, coin, initialization, and administrative grades.  If the native family
also has a no-exhaustion and productivity certificate, the translated family
inherits it with zero additional probabilistic failure, provided the derived
administrative envelope is supplied.

The inherited productivity claim follows from exact erased behavior and the
well-founded phase/microstep rank.  Merely assigning polynomial meters to the
administrative nodes would not suffice.

There is no claim that accounting is costless.  The processor/store/coin
contracts, quota comparisons, and ledger append operations are the primitives
of this layer.  Attempting to charge those operations using the same API would
create a regress.  CC's top-down discipline permits a later realization of
these primitives; the present theorem states exactly where this layer stops.

## 9. A concrete sequential link resource

The word `COMM[c]` is too ambiguous for a theorem.  A selected communication
resource for this model is the one-place sequential link

```text
SLINK_e[C,W,S].
```

It has one input endpoint and one output endpoint, no concurrent queue, and no
clock.  On a code of length `l`, it checks:

```text
usedBits + l <= C,
usedWork + a0 + a1*l <= W,
buffer(l) <= S.
```

The canonical router convention uses the same whole-message reservation. If
all checks fit, the link obtains a linear capability, copies the code in
ordinary bit-costful small steps, clears the old buffer, and delivers exactly
one identical event. Those admitted copy steps cannot subsequently exhaust.
Otherwise it produces owner-labeled `Exhaust(e)` before committing routing
work, traffic, or a destination buffer. It never drops, duplicates, reorders,
delays, or leaks a message.

The validated self-delimiting length is available before allocation and
copying.  All three checks form one primitive charge owned by `e`; a
copy-then-discover-overflow implementation would not satisfy this API.

### Proposition 9.1 (edge refinement)

Replacing a metered canonical edge by `SLINK_e` with the same traffic, router
work, and buffer quotas preserves the maximal transcript and those exact
ledger coordinates, up to renaming the infrastructure owner. The proof
relates the unique routing buffer and remaining capacities. Both first make
the same owner-`e` whole-message reservation. On rejection neither commits a
routing coordinate. On admission both execute the same infallible
bit-costful copy with identical intermediate buffer, transition, traffic, and
`gpeak` updates before delivery.

When `C,W,S` dominate the route envelope, `SLINK_e` is observationally
transparent and cannot be the first exhausted occurrence.  With smaller
limits it is an explicit fallible resource node.  This distinction prevents a
bandwidth assumption from being mistaken for structural connection.

The proposition is about a one-token lossless link.  Latency, asynchronous
queues, contention, packetization, adversarial delivery, and topology are
different APIs.

## 10. Structural and AC consequences

The translation `E` is local and equivariant:

```text
E(rename(N))       ~= rename(E(N)),
E(N || M)          ~= E(N) || E(M),
E(connect_pq(N))   ~= connect_pq(E(N)),
```

where `~=` is alpha-isomorphism of private names.  The first two equations
follow from generated private names and disjoint union.  The third holds
because `E` preserves each native boundary port and connection adds only the
same original edge.  Administrative erasure respects all three equations.

Consequently the explicit-resource image is a lower AC resource algebra, and
the following diagram commutes on the selected route-safe class:

```text
explicit processor/store/coin/link resources
                  --erase_admin-->
metered machine networks
                  --erase_cost-->
behavioral operational systems
                  --J-->
partial random systems.
```

Only the first arrow is new here.  It is a report-projection homomorphism for
cost-aware tests and a pathwise equality for behavioral tests.  A cost-aware
test that is intentionally allowed to inspect `AdminWork` can of course
distinguish the two presentations; that is why the theorem states
`pi_native`, not equality of the full explicit ledger.

Let

```text
C_P(B_P) =
  PROC_P[P;T_P,A_P,L_P]
  || STORE_P[S_P]
  || COIN_P[R_P].
```

Then a program converter is represented explicitly by the routing-only
`Drive_P` attached to the parallel resource `C_P`.  For any two native
experiments `X,Y`, any behavioral test on their unchanged external ports has
the same acceptance probability on `E(X),E(Y)` as on `X,Y`.  The same is true
for a cost-aware test after composing its report input with `pi_native`.
Therefore a native simulation equation

```text
pi R ~=_epsilon S sigma
```

transports, when both costs are reified, to

```text
Drive_pi [R || C_pi] ~=_epsilon
Drive_sigma [S || C_sigma]
```

with no new distinguishing error.  Only the polynomial resource profile is
enlarged by the administrative bounds.  The computer interfaces must be
placed at the parties supplying those costs.  Translating only honest
computation while retaining a free-efficient simulator is a different,
permitted mixed regime; translating the simulator makes its ideal-side cost
explicit.

## 11. Clock and other non-conservative refinements

A non-observable processor token bound is already a meter.  A visible
`CLOCK[t]` is different: a context can distinguish two implementations with
the same first visible response but different numbers of private phases.
There can be no unrestricted contextual equality after erasing such a clock.
One must either:

- keep time hidden and use the meter semantics above;
- retain time in the target observation and prove a timed refinement; or
- restrict the test class to clock-insensitive tests.

The same warning applies to memory snapshots, access-pattern leakage, and
failure subowners.  They are useful explicit-resource models, but not
conservative refinements of the current behavioral carrier without a stated
observation map and test restriction.

## 12. Worked persistent-state instance

For the persistent-mask component `K`, the native state after its first
activation contains the sampled mask bit and the suspended control state.
The explicit presentation stores the mask and control in `STORE_K`; its
`COIN_K` head has advanced once; and its processor has committed the five
native transitions of the selected implementation.  Later activations read
the mask from `STORE_K` and make no coin reservation.

Under the paper's native ledger

```text
ell_q = (22q+2, 3q, 1, 2q, 4),
```

the native projection of the explicit ledger is exactly the same tuple for
the fixed unparameterized instance. In the primary uniform convention, both
stores additionally own their logical `1^kappa` tracks and heads, so the
projected peak is `2*kappa+6`; the other coordinates are unchanged. In either
case, program storage and the bounded transaction scratch appear only in the new
explicit coordinates.  Replacing `STORE_K` by a stateless adapter would lose
the cross-query mask and change the resource behavior; retaining it inside
`Drive_P` would reproduce the behavior while falsifying the memory claim.

## 13. Exact scope

The completed result is:

- one concrete sequential processor/store/coin API;
- one concrete sequential lossless-link API;
- pathwise preservation of success, strict block, and owner-labeled
  exhaustion;
- exact preservation of the native ledger under a named projection;
- a polynomial bound on all newly exposed administration;
- preservation of no-exhaustion and productivity by a finite phase-rank
  certificate; and
- a local translation commuting with the operational constructors.

It is not:

- a theorem for every possible `CPU`, RAM, communication, or clock API;
- a claim that program storage or administrative work is physically free;
- a concurrent or asynchronous processor model;
- a theorem for a processor, store, or coin resource shared through an
  additional adversarial interface;
- a secure-erasure, leakage, or reset theorem;
- a claim that an ideal oracle's internal computation has been implemented;
  or
- a UC execution model.

These exclusions identify separate lower refinements rather than gaps in the
selected theorem.
