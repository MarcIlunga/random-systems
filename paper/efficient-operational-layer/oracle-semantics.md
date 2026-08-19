# Typed charged specification oracles

## 1. Purpose and scope

An ideal resource need not be implemented by a Turing machine merely because
an efficient converter is allowed to call it.  The lower layer must instead
say exactly:

1. which finite strings are legal queries and responses;
2. which hidden state and transition law define the specification;
3. which part of the state, if any, is public to the access meter;
4. what must be reserved before fresh randomness is sampled;
5. what exact call, traffic, and tariff coordinates are charged afterward;
6. how the rule behaves when a response has no finite query-only envelope.

This note fixes that interface.  It proves the finite terminal-law,
no-selection-bias, budget-monotonicity, and no-budget-minting results used by
the efficient operational algebra.  It does not assert that the oracle's
hidden transition is efficiently computable.

## 2. A bounded-call oracle contract

Fix a security parameter `kappa`, ambient workload `b`, and a ledger dimension
`d`.  A bounded-call contract for a named specification occurrence `O`
contains the following data.

### 2.1 Encoded interface

- Countable query and response sets `Q_O` and `R_O`.
- Prefix-free injective encodings

  ```text
  enc_Q : Q_O -> {0,1}^*,
  enc_R : R_O -> {0,1}^*.
  ```

- Fixed decoders that either return one value and the unused suffix or reject.
  Their implementation work is charged to the caller or to an explicit
  codec component.  Prefix-freeness prevents a caller and specification from
  disagreeing about message boundaries.

The query and response sets may be infinite.  Every individual code is finite.

### 2.2 Hidden state and kernel

- A standard-Borel hidden state space `S_O`.
- A countable finite-code block reason set `E_O`.
- A measurable Markov kernel

  ```text
  K_O :
    S_O x Q_O
      -> Prob(
           (S_O x R_O x Reply)
           + (S_O x E_O x Block)
         ).
  ```

Both a reply and a block may update hidden state.  `Block` ends the current
closed partial interaction without placing an ordinary error value on a wire.

For pathwise proofs, the contract also fixes a measurable randomization

```text
sample_O :
  S_O x Q_O x [0,1]
    -> (S_O x R_O x Reply)
       + (S_O x E_O x Block)
```

whose pushforward of Lebesgue measure in the last coordinate is `K_O(s,q)`.
The standard-Borel randomization lemma (Kallenberg, *Foundations of Modern
Probability*, 2nd ed., Lemma 3.22) guarantees that at least one such map
exists. Choosing it does not change the one-experiment law; it only selects
the coupling used in pathwise simulation and budget-monotonicity statements.

Every oracle occurrence owns a named independent seed sequence

```text
U_O,0, U_O,1, ...  iid Uniform[0,1].
```

Two components share oracle state or seed randomness only by calling the same
named occurrence.  Merely using the same kernel name creates independent
occurrences after alpha-renaming.

### 2.3 Public contract state

The meter is not allowed to inspect arbitrary hidden state.  The contract
therefore fixes a countable public-summary set `U_O` with an effective
prefix-free finite encoding (hence a discrete standard-Borel space) and
presents the specification state with an explicit public coordinate,
equivalently with a measurable projection

```text
pub_O : S_O -> U_O.
```

The specification kernel maintains this coordinate together with its hidden
state.  The current summary is either already public in the transcript or
maintained as an explicit meter-readable contract coordinate; the
implementation does not compute it from an encoding of hidden state.  Taking
`U_O` to be a singleton gives a state-independent access price.

For a full sampled outcome `z`, define its finite public charging view

```text
view_O(z)
  = (Reply,r,pub_O(s'))   if z=(s',r,Reply),
    (Block,e,pub_O(s'))   if z=(s',e,Block).
```

The next public coordinate is maintained by the specification as part of the
contract state.  A caller receives only `r` on a reply; the meter receives the
charging view.  Neither is given an encoding of hidden `s'`.

### 2.4 Exact charge and reservation

Let the relevant ledger coordinates include at least

```text
oracle-call,
oracle-query-bits,
oracle-response-bits,
oracle-public-tariff.
```

The contract fixes an exact, publicly evaluable charge

```text
charge_O(kappa,b,u,q,view_O(z)) in N^d,
```

where `u=pub_O(s)` and `z` is the reply or block outcome.  Every reply charge
satisfies coordinatewise

```text
charge.call          >= 1,
charge.query-bits    >= |enc_Q(q)|,
charge.response-bits >= |enc_R(r)|.
```

A block charge similarly dominates its encoded public block record if one is
retained in the costed report.  Hidden oracle computation does not appear in
this vector.  Pricing it would require selecting an implementation or
connecting an explicit processor resource.

The contract also fixes a finite reservation

```text
reserve_O(kappa,b,u,q) in N^d
```

with the strong envelope property

```text
charge_O(kappa,b,u,q,sample_O(s,q,v))
  <= reserve_O(kappa,b,u,q)
```

for every hidden state `s` with `pub_O(s)=u` and every seed `v in [0,1]`.
Here and below `charge_O(...,sample_O(...))` abbreviates composition with
`view_O`; the charge never inspects the next hidden state itself.
Thus reservation depends only on public pre-call data and dominates every
outcome of the selected pathwise realization, including null seeds.  An
almost-sure envelope would suffice for a purely measure-level boundedness
claim but not for the paper's strong samplewise metering theorem.

The finite-code evaluators for `reserve_O` and `charge_O` on encoded
`(kappa,b,u,q,view_O(z))` must be effective when the oracle is called from the
implementation sort.  The public coordinates are supplied and maintained by
the contract; no local computation traverses hidden `s` or `s'`.  The
evaluators' fixed polynomial profiles are either:

1. included in the caller's local work grade; or
2. explicitly declared administrative meter work.

They are never an unmentioned unit-cost source of noncomputable branching.
The kernel `K_O` itself may remain noncomputable because it belongs to the
specification sort.

The contract also supplies two evaluator-funding envelopes.

```text
EvalReserve_O(kappa,b,u,q)
```

bounds deterministic evaluation and validation of `reserve_O` itself.

```text
PostReserve_O(kappa,b,u,q)
```

dominates, for every compatible sampled outcome, the work, transient space,
record construction, and commit bookkeeping needed to evaluate
`charge_O(...,view_O(z))` and install its exact ledger update. These envelopes
are ordinary owner-assigned coordinates. `PostReserve_O` is checked together
with the semantic `reserve_O` before sampling. Peak coordinates use the
declared prospective-peak update rather than an illicit additive
interpretation; cumulative coordinates add. The actual evaluator trace and
peak remain in the exact ledger, and unused reserved capacity is released.
This extra envelope is necessary: merely promising to “charge” a
response-dependent evaluator would still permit that evaluator to exhaust
after the oracle state had been sampled.

## 3. Atomic admission rule

Let `B in N^d` be the caller's remaining oracle/traffic/tariff budget and let
`j` be the next seed index of this oracle occurrence.

### Pre-sample evaluation and rejection

First check `EvalReserve_O`. If it does not fit, terminate with owner-labeled
`Exhaust` before running the evaluator and before touching any oracle seed or
hidden state. If it fits, the fixed total `reserve_O` evaluator runs under
that capability and its actual work/space is committed; unused capacity is
released. Thus reserve evaluation itself cannot fail halfway through.

If evaluation succeeds, form the combined prospective check consisting of
the semantic `reserve_O` and `PostReserve_O`, using the ledger's cumulative
and peak-coordinate update rules. If that check does not fit, reject as
follows.

If

```text
reserve_O(kappa,b,pub_O(s),q)
  together with PostReserve_O(kappa,b,pub_O(s),q)
does not fit in B,
```

the closed experiment returns `Exhaust` with its current transcript and
ledger, labeled by the declared public owner of the rejecting access meter
(caller, tested subsystem, or shared infrastructure).  It does not:

- evaluate `sample_O`;
- consume `U_O,j`;
- advance `j`;
- change hidden state;
- reveal a response or a response-dependent charge.

### Admission

If the reservation fits:

1. set `z=sample_O(s,q,U_O,j)` and advance the occurrence's seed index;
2. run the response-dependent charge evaluator under the already admitted
   `PostReserve_O` capability;
3. atomically update the oracle to the next hidden state in `z`;
4. add the exact vector
   `charge_O(kappa,b,pub_O(s),q,view_O(z))` to the ledger;
5. add the evaluator's actual work/space and commit-record charges;
6. deliver the finite response, or terminate in semantic `Block`;
7. release all unused semantic and administrative reservation inside the
   external meter.

Programs cannot read the reservation, remaining budget, or released slack.
The strong envelope guarantees that an admitted atomic call cannot discover
after sampling that either its exact charge or the charge evaluator does not
fit. The post-sample evaluator is total on the declared outcome domain; its
pre-reserved execution cannot introduce `Block` or `Exhaust`.

## 4. No response-selection bias

### Theorem 4.1

Condition on any complete pre-call history `h` that fixes the current state
`s`, query `q`, remaining budget `B`, and seed index `j`.  If the admission
predicate is true, the conditional law of the delivered outcome and next
state is exactly `K_O(s,q)`.

### Proof

Reservation evaluation and the combined admission predicate are functions of
`(kappa,b,pub_O(s),q,B)` and are therefore fixed before `U_O,j` is read.
Conditional on `h`, the fresh seed still has the uniform law and is
independent of the predicate. The pushforward property of `sample_O` gives
`K_O(s,q)`. The response-dependent evaluator is already funded and total. No
response is rejected, rolled back, or resampled after this draw.

### Corollary 4.2

For a random pre-call history, on the measurable event `Admit`, the regular
conditional next-step kernel is the original state-dependent kernel:

```text
Law(z | pre-call history, Admit) = K_O(s,q).
```

This statement does not claim that `z` is independent of the history; the
kernel is allowed to depend on the fixed current state and query.

### Why sample-then-check is different

If admission is instead the response-dependent event

```text
charge_O(...,view_O(z)) <= B,
```

then the successful response law is generally

```text
K_O(s,q) conditioned on charge_O(...,view_O(z)) <= B.
```

That is a legitimate *truncated costed specification* if exhaustion and state
commitment are kept visible.  It is not an exact admitted call to `K_O`.
Rolling back and retrying until a fitting response is obtained hides the
exhaustion event and silently replaces the advertised kernel by the
conditioned law.

Even under pre-reservation, an outcome's exact charge can affect whether a
*later* call fits.  This creates an honest correlation between the earlier
response and later exhaustion.  The theorem excludes selection of the current
fresh response; it does not erase response-dependent future costs.

## 5. Budget monotonicity

Order budgets coordinatewise.  Couple two executions with the same machine
tapes and named oracle seed sequences.

### Theorem 5.1

Suppose the two executions have identical configurations and ledgers before a
call, with remaining budgets `B <= B'`.  If the `B` execution admits the call,
then the `B'` execution admits it, consumes the same seed, obtains the same
outcome, changes to the same hidden state, and adds the same exact charge.

### Proof

The deterministic reserve-evaluator trace is the same in both executions, and
the combined reservation fitting below `B <= B'` proves both admissions. The
seed indices agree, so the selected randomization returns the same `z`;
post-sample evaluator traces, exact charges, and updates are functions of the
same data.

### Corollary 5.2

For complete metered executions, increasing the external budget cannot alter
the trace before the smaller execution's first exhaustion.  Every successful
run under the smaller budget is the identical successful run under the larger
budget.

The premise that programs cannot read budget or reservation slack is
essential.  Otherwise a larger budget could cause an earlier branch change
even though every primitive action fits.

## 6. Finite terminal law

### Theorem 6.1

Fix a closed finite normalized graph, finite evaluated component/router work
quotas, finite oracle-call quotas, and bounded-call contracts as above.  Its
terminal result law on

```text
Success(transcript,observation,report)
+ Block(owner,transcript,observation,report)
+ Exhaust(owner,transcript,observation,report)
```

is uniquely defined and measurable in the encoded public input and initial
oracle state.

### Proof

The implementation configuration space is countable.  A finite product with
standard-Borel oracle states is standard Borel.  Machine and router steps are
measurable deterministic kernels.  Section 3 gives a measurable piecewise
kernel for each oracle step: a Dirac exhaustion kernel on rejection and the
pushforward of `K_O` through the commit/deliver map on admission.

Every nonterminal implementation/router step consumes positive work and every
admitted oracle step consumes a positive call coordinate.  The sum of the
finite evaluated quotas therefore gives a deterministic finite horizon after
which a terminal state must have been reached.  Make terminal states
absorbing, compose the step kernel to that horizon, and push forward through
the terminal observation map.  Finite kernel composition gives existence,
measurability, and uniqueness.

This theorem is sufficient for one budgeted security experiment.  Using the
named seed sequences in the same way over a lifetime gives the measurable
partial-DDS law used in `partial-random-system-bridge.md`; that note proves
compatibility with its selected strict-feedback carrier.  Comparison with a
differently mandated carrier remains separate.

## 7. No budget minting

The phrase means neither that an ideal oracle is computationally weak nor that
its answer contains little information.  An ideal signature oracle, random
oracle, or noncomputable sampling resource can be powerful.  The precise
claim is only that a call does not enlarge the caller's implementation budget.

### Theorem 7.1

Let a closed implementation have remaining local-work vector `W`, local-space
cap `S`, and oracle/traffic vector `B` before a call.  Under the atomic rule:

1. the call never increases `W`, `S`, or `B`;
2. every delivered response bit is charged in the response-bit coordinate;
3. reading, copying, parsing, storing, or re-emitting that response consumes
   the implementation's ordinary work/space/traffic coordinates;
4. after at most `Q` admitted calls and aggregate response-bit quota `R`, at
   most `Q` oracle outcomes and at most `R` encoded response bits can enter
   the implementation;
5. hidden work used to choose those outcomes is absent by definition and
   cannot be reclassified as local machine work.

### Proof

The reservation test only rejects or permits the transition.  On admission
the meter subtracts the nonnegative exact charge and never adds to any
coordinate.  The response is copied into the distinguished finite input
buffer under the bit-costful router convention.  Subsequent machine actions
are ordinary transitions checked against the unchanged local quotas.  Summing
the positive call and response-bit charges proves item 4.  Item 5 is the
two-sorted modeling convention, not a computational simulation theorem.

### Consequence

If the caller has polynomial local grades, polynomial call and response-bit
grades, and polynomial codec/tariff evaluators, then every metered closed
experiment has a polynomial ledger after the context's polynomial workload is
substituted.  This does not make the oracle implementable.  It establishes an
oracle-relative efficient experiment whose oracle dependence remains visible
in the profile.

### Definition 7.2 (efficient accessibility on a domain)

Fix a declared reachable public query domain `A`, closed under the public
coordinate updates of admitted outcomes.  The bounded-call contract is
efficiently accessible on `A` when there are fixed monotone polynomials
`U,Q,R,E` such that, for every admitted `(kappa,b,u,q)` in `A`,

```text
|enc_U(u)| <= U(kappa,b),
|enc_Q(q)| <= Q(kappa,b),
reserve_O(kappa,b,u,q) <= R(kappa,b) coordinatewise,
EvalReserve_O(kappa,b,u,q) <= E(kappa,b),
PostReserve_O(kappa,b,u,q) <= E(kappa,b),
codec/reservation/charge evaluation work <= E(kappa,b).
```

This is an access predicate, not an implementation predicate.  A one-bit
oracle answer may encode a noncomputable fact and still have a constant
access tariff; the resulting construction is explicitly relative to that
oracle.  Conversely, a machine-computable kernel with exponentially long
responses need not satisfy efficient accessibility under an atomic interface.

## 8. Responses without a finite envelope

Suppose the encoded response length has unbounded support for one fixed public
query.  Then no finite strong reservation can dominate it.  Such an interface
does not satisfy the bounded-call contract, even if the response is finite
almost surely.

There are two honest replacements.

### 8.1 Publicly capped specification

Add a public cap `c` to the query and define an explicit overflow response.
The new kernel has response length bounded by `c` and fits the baseline rule.
This is a different specification; the cap and overflow event remain visible.

### 8.2 Stateful streaming specification

Replace one unbounded response by the following fixed-size interface and a
fixed metered reassembly converter `A_c`.

```text
Start(q)  -> handle or Block
Next(h)   -> Chunk(bits,done) or Block
```

On `Start`, the oracle samples the original response and next state exactly
once, commits that next state, and stores the unrevealed response behind a
hidden handle.  A `Next` response contains at most the fixed public chunk size
`c`, so it has a finite query-only reservation.  Each admitted `Next` call
commits exactly one chunk and advances the hidden handle.  A rejected chunk
call samples nothing, reveals nothing, and leaves the handle unchanged.

In the selected one-token theorem, `A_c` retains the token, permits one active
handle, repeatedly calls `Next`, stores the charged chunks in ordinary metered
memory, and emits one reassembled response on the original interface.  Thus
the auxiliary chunk transcript is hidden inside the converter.  An API with
several interleaved handles needs an additional scheduling and handle-length
profile; it is not implicit here.  No rule may roll back the sampled response
and try again merely because its length exceeds the caller's remaining budget.

### Theorem 8.1 (streaming/reassembly coupling)

Couple the original oracle and `A_c` attached to the streaming oracle with the
same sampled response.  If the converter has enough work, space, admitted
chunk calls, and response-bit budget to receive and emit the full encoding,
it returns exactly the original response and the committed next state agrees.
After hiding the converter's chunk interface, the erased external transcripts
can differ only on the event

```text
encoded response requires more chunks than the available chunk budget.
```

Hence their total-variation distance on finite transcript outcomes is at most
the probability of that event.

### Proof

Induct on the chunk index.  Before exhaustion, the concatenation of delivered
chunks is the corresponding prefix of the one sampled encoding and the hidden
suffix is the complement.  If all chunk, storage, and output actions fit, the
final concatenation and state are identical and `A_c` emits exactly the
original event.  Under the common-response coupling, disagreement is contained
in the displayed tail event (with converter work/space folded into “available
chunk budget”); apply the coupling inequality.

Conditioning on successful completion generally favors shorter responses.
Neither the semantics nor Theorem 8.1 replaces the original law by that
conditional distribution.

### 8.3 Concrete geometric-string instance

Let `GeoBits` sample `L in Nat` with

```text
Pr[L = ell] = 2^(-ell-1),
```

sample `U` uniformly from `{0,1}^L`, and return `(L,U)`.  Encode the response
as

```text
1^L 0 U,
```

which is prefix-free and has length `2L+1`.  The response is finite almost
surely but has unbounded support, so the atomic bounded-call contract cannot
admit it strongly.

The streaming version samples this code once on `Start` and retains it behind
one private handle.  A `Next` call returns at most

```text
c(kappa) = 2*kappa
```

code bits and tags the last full or partial chunk `done`.  Give the fixed
reassembler

```text
Q(kappa,b) = b+1
```

chunk calls.  For fixed handle/tag overhead `h` and fixed compiled-copy
constants `alpha_i,beta_i`, the complete implementation profile is bounded
by

```text
Calls     <= Q+1,
ChunkBits <= Q*(c+h),
Work      <= alpha_0 + alpha_1*Q + alpha_2*c*Q,
Space     <= beta_0 + beta_1*c*Q,
OutputBits <= c*Q + fixed outer tag.
```

The local profile includes parsing, storing every chunk, and constructing the
blank final output register. The fixed `beta_i` also cover the reassembler's
retained unary parameter track and head: for `kappa,Q >= 1`,
`cQ=2*kappa*Q` dominates their storage. The unbounded sampled suffix and its
hidden sampling work remain state and work of the specification oracle; they
are not mislabeled as polynomial implementation resources.

### Proposition 8.2 (geometric streaming tail)

For `kappa >= 1`, fund the displayed profile and hide the chunk interface.
The total-variation distance between the reassembled and one-shot finite
transcript laws is at most

```text
2^(-kappa*(b+1)).
```

**Proof.**  Reassembly fits when

```text
2L+1 <= cQ = 2*kappa*(b+1),
```

equivalently `L <= kappa*(b+1)-1`.  The complementary geometric tail is

```text
Pr[L >= kappa*(b+1)] = 2^(-kappa*(b+1)).
```

On the fitting event, Theorem 8.1 gives the same code, response, and state
under the common sample.  The funded deterministic local profile removes
every other failure event.  Apply the coupling inequality.  All displayed
coordinates are fixed polynomials, and the tail is at most `2^(-kappa)` for
every `b >= 0`.

`Start` is not retried on the long-answer event.  The same sample is committed
in both experiments, so this is an exhaustion tail rather than a
short-response-conditioned oracle.

## 9. Multiple occurrences and compilation

### 9.1 A complete implementable specification

The two-sort distinction does not prevent an implementation theorem when one
is available.  Let `RF_(m,n)` be the ideal uniformly sampled function from
`{0,1}^m` to `{0,1}^n`, where `m=m(kappa)` and `n=n(kappa)` are fixed
effectively evaluated polynomial length functions.  Let
`Q=Q(kappa,b)` be a fixed polynomial workload envelope.

One fixed `LazyRF` component keeps a sequential dictionary of distinct
`(x,y)` pairs.  It validates an `m`-bit query, scans the list, returns the
stored `y` on a hit, and on a miss consumes the next unused `n`-bit block of
its named fair tape, appends the pair, and copies `y` into a blank output
register.  It does not inspect `Q` or remaining budget.

Using ordinary sequential comparisons and copies, a conservative complete
profile is

```text
Work
  <= Q * (4Q(m+n+8) + 8(m+n+1)) + LenEval(kappa),

Space
  <= (Q+1)(m+n+8) + LenSpace(kappa),

Random <= Q*n,
Acts   <= Q,
BoundaryQueryBits    <= Q*m,
BoundaryResponseBits <= Q*n.
```

Here `LenEval(kappa)` pays the fixed machines that evaluate and validate the
two length functions. `LenSpace(kappa)` includes their simultaneous scratch,
the retained logical `1^kappa` parameter track, and its head. In particular,
neither the asymptotic input nor length evaluation is free storage.

Before every call there are at most `Q` records, each of encoded length at
most `m+n+8`.  The `4Q(m+n+8)` term pays a literal sequential scan, including
passage over stored values on a miss; the second term pays validation, the
worst-case append, random-bit reading, and output construction.  The space
bound retains every record and one active input/output region.

**Proposition 9.1 (exact bounded-query RF realization).**  Fund `LazyRF` by
the displayed local profile and fund boundary routing for at most `Qm` query
bits and `Qn` response bits, either through route-safe closure or an explicit
envelope.  On every adaptive history of at most `Q` valid calls, `LazyRF` has
exactly the erased response law of `RF_(m,n)`; the `LazyRF` occurrence never
exhausts and answers every delivered query.  A closed productivity statement
also assumes the completion context accepts the advertised responses and adds
its failure bound `chi_D`; it is strong when `chi_D=0`.  The implementation
makes no specification-oracle calls.

**Proof.**  Induct on the query history.  Repeated inputs obtain the one stored
value in both systems.  Conditional on every preceding adaptive transcript,
an unqueried point of a uniform random function has an independent uniform
`n`-bit value, as does the next unused block of the named fair tape.  Thus the
conditional response kernels, and hence all transcript laws, agree.  The
dictionary contains at most one record per call, so the displayed
scan/copy/storage/randomness bounds hold pathwise and the funded meters never
fire.  The route premise funds delivery and return separately.  The
completion-context definition contributes exactly its declared `chi_D` to a
closed-success statement.

This theorem is bounded in lifetime workload, not a finite materialization of
the full table.  A pseudorandom-function implementation would instead be a
computational construction with a named assumption, reduction profile, and
error.

### 9.2 Fixed and indexed occurrences

The default tensor of two oracle occurrences uses independent hidden states
and independent seed sequences, even if the kernel code/name is the same.
Shared state is a single common occurrence with several callers.

The generated-network compiler creates implementation nodes only.  It may
route a fixed decoded boundary call through the universal component and retain
the virtual continuation needed for the reply, but:

- the physical oracle occurrence already appears at a fixed named boundary;
- its hidden state, kernel, seed sequence, and tariff contract are unchanged;
- physical call/query/response profiles are bounded by the decoded native
  boundary profiles;
- the compiler does not create `q(kappa)` independent ideal copies.

If a theorem genuinely requires a polynomial family of independent ideal
instances, it must supply a fixed countable product-state specification with
an encoded instance identifier and a proved tariff/profile.  That is a new
specification theorem, not a free consequence of universal machine
simulation.

## 10. Exact residual obligations

The bounded-call result above is complete under its displayed interface
hypotheses.  The following extensions remain separate.

1. Compare the selected standard-Borel maximal-transcript carrier of
   `partial-random-system-bridge.md` with any separately mandated carrier that
   chooses different nonresponse or feedback semantics.  The selected
   route-safe bridge and connection congruence are proved.
2. Instantiate additional application-specific unbounded-output APIs as
   needed.  The `GeoBits` oracle above is one complete instance; it does not
   imply a tail bound for an unrelated response law.
3. If exact machine constants for codec/reservation evaluation matter, print
   or mechanize those fixed evaluator transition tables.
