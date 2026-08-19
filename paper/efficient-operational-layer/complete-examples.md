# Complete calculations for the efficient operational layer

## 1. Fixed accounting conventions

The examples use the following selected bit-machine routines. These are
certified upper bounds for one concrete implementation, not claims of
machine-independent optimality.

| Routine | Work charge | Other charge |
|---|---:|---:|
| `WriteConst(L)` | `2L + 1` | writes `L` output bits |
| `Copy(L)` | `3L + 1` | reads and writes `L` bits |
| `ReadFixed(L)` | `2L + 1` | validates and consumes `L` bits |
| `Emit` | `1` | one output event |
| `Route(L)` | `2L + 3` | `L` traffic bits, one receiver activation |
| `Random(L)` | `L` | `L` random bits |

`WriteConst` performs one write and one loop/control step per bit plus a final
exit. `Copy` performs one read, one write, and one loop/control step per bit
plus a final exit. `ReadFixed` performs one read and one loop/control step per
bit plus a final length check. `Route` validates the fixed-length envelope,
transfers its bits under the chosen buffer convention, and changes token
owner. Component activations are recorded in the activation coordinate rather
than added again to work.  The route row says that the receiver becomes
active; the activation is recorded once in the receiver's phase row, not a
second time in the route row.

The ledger order used below is

```text
(work, activations, random bits, internal traffic,
 native logical live footprint, oracle calls, oracle query bits,
 oracle response bits).
```

Boundary work performed by the surrounding context is excluded unless stated.

## 2. Persistent one-bit mask

### 2.1 Programs

The resource `K` has one hidden client-facing query `Unit` encoded by one bit.
On its first activation it reads one random bit `k`, stores it, and returns
`k`. On every later activation it returns the stored bit.

The converter `C` receives an outer bit `x`, stores it, sends `Unit` to `K`,
receives `k`, and emits `x xor k`.

The selected phase costs are:

| Phase | Work | Activations | Random | Traffic |
|---|---:|---:|---:|---:|
| `C` stores `x`, constructs `Unit`, emits | `4` | `1` | `0` | `0` |
| route one-bit request | `5` | `0` | `0` | `1` |
| first `K` call: sample, store, copy, emit | `5` | `1` | `1` | `0` |
| later `K` call: read, copy, emit | `3` | `1` | `0` | `0` |
| route one-bit response | `5` | `0` | `0` | `1` |
| `C` reads `x,k`, computes xor, emits | `5` | `1` | `0` | `0` |

The protocol-state peak is four bits: `C` may simultaneously hold `x`, the
received `k`, and its output bit, while `K` retains its persistent `k`.
In the primary uniform convention, the two components' logical `1^kappa`
tracks and parameter heads also coexist. Router buffers do not overlap that
peak under the single-token schedule. Thus the complete uniform peak is
`2*(kappa+1)+4 = 2*kappa+6`.

### 2.2 Exact lifetime ledger

The first outer query has ledger

```text
ell_1 = (24, 3, 1, 2, 2*kappa+6, 0, 0, 0).
```

Every later query contributes

```text
Delta ell_later = (22, 3, 0, 2, 0, 0, 0, 0),
```

where the zero in the peak coordinate means that the lifetime maximum remains
`2*kappa+6` in the uniform presentation (four in the fixed unparameterized
base presentation), not that no cells are live.

After exactly `q >= 1` outer queries, the lifetime ledger is

```text
ell_q = (22q + 2, 3q, 1, 2q, 2*kappa+6, 0, 0, 0).
```

Thus the grade

```text
Work(kappa,b)    = 22b + 2,
Acts(kappa,b)    = 3b,
Rand(kappa,b)    = 1,
Traffic(kappa,b) = 2b,
Space(kappa,b)   = 2*kappa + 6
```

is strong for every workload with at most `b` outer calls.
Dropping the two parameter tracks recovers the fixed unparameterized base
ledger with peak four used in the paper's pre-asymptotic cost section.

### 2.3 Exact transcript distinction

For inputs `x_1,...,x_q`, persistent masking returns

```text
y_i = x_i xor k
```

for one lifetime bit `k`. A fresh-mask implementation instead uses independent
bits `k_i`.

The distinguisher checks whether

```text
y_1 xor x_1 = y_i xor x_i
```

for every `2 <= i <= q`. It accepts persistent masking with probability one.
It accepts fresh masking exactly when all `q` independent masks are equal,
which has probability

```text
2 * 2^(-q) = 2^(1-q).
```

Its information-theoretic advantage is therefore

```text
epsilon_info(q) = 1 - 2^(1-q).
```

For `q=1` the advantage is zero; for `q=2` it is `1/2`. This calculation
contains no asymptotic placeholder.

### 2.4 Converter profile transformer

If only `C`, rather than `K`, is absorbed into a test, each outer query adds:

- `4+5 = 9` component-work units for the two `C` phases;
- two routes of one bit, costing `10` work and two traffic bits;
- two converter activations;
- at most three converter protocol cells, plus its logical `1^kappa` track
  and parameter head in the primary uniform convention.

For a test profile `P` making at most `q_D` outer calls, the absorbed profile
is bounded coordinatewise by

```text
T_C(P).work    = P.work    + 19 q_D,
T_C(P).acts    = P.acts    +  2 q_D,
T_C(P).traffic = P.traffic +  2 q_D,
T_C(P).space   = P.space   + kappa + 4,
T_C(P).random  = P.random,
T_C(P).calls   = P.calls.
```

Here `P.calls` counts named side-oracle calls.  The `q_D` calls to the
challenge resource are tracked by the separate challenge-query bound and do
not disappear.  The profile convention for `P` already includes the test's
outer challenge-boundary interaction; the displayed additions are precisely
the converter phases and the two new converter-to-inner-resource routes.
The ambient workload index does not change. The concrete profile does.

## 3. An exact sequential and parallel random-system reduction

### 3.1 Resources

Let `m=s+n`. Define:

- `RF_m`, a uniformly sampled function from `{0,1}^m` to `{0,1}^m`;
- `RP_m`, a uniformly sampled permutation of `{0,1}^m`;
- `Tag_j`, for fixed `j in {0,1}^s`, which maps an outer query
  `x in {0,1}^n` to `j || x`;
- `Trunc_l`, which returns the first `l <= m` bits of an inner response.

The sequentially wrapped resources are

```text
F_j = Trunc_l o RF_m o Tag_j,
P_j = Trunc_l o RP_m o Tag_j.
```

`Tag_j` and `Trunc_l` are named deterministic converter algorithms.

### 3.2 Exact per-query reduction cost

On one outer query:

1. the tag phase costs

   ```text
   WriteConst(s) + Copy(n) + Emit
   = (2s+1) + (3n+1) + 1
   = 2s + 3n + 3;
   ```

2. the inner `m`-bit query route costs `2m+3`;
3. the inner `m`-bit response route costs `2m+3`;
4. response validation and truncation cost

   ```text
   ReadFixed(m) + Copy(l) + Emit
   = (2m+1) + (3l+1) + 1
   = 2m + 3l + 3.
   ```

Therefore the exact certified sequential-wrapper overhead per query is

```text
C_seq(s,n,l)
  = 2s + 3n + 6m + 3l + 12
  = 8s + 9n + 3l + 12.
```

It adds two converter activations, `2m` internal traffic bits, one inner oracle
call, `m` oracle query bits, and `m` oracle response bits.

If an outer distinguisher `D` has work bound `t`, activation bound `a_D`,
traffic bound `c_D`, peak-space bound `s_D`, and makes at most `q` queries,
the absorbed single-resource distinguisher `B` has

```text
Work_B <= t + q(8s + 9n + 3l + 12),
Acts_B <= a_D + 2q,
Traffic_B <= c_D + 2qm,
Space_B <= s_D + 4m + 2*kappa + 10,
Calls_B <= q,
QBits_B <= qm,
RBits_B <= qm,
Random_B = Random_D.
```

Every outer query becomes exactly one inner query; there is no query or
success-probability loss. The deliberately loose `4m+8` protocol-space
increment allows a source buffer, destination buffer, router scratch, and one
active tag/truncation buffer under the single-token schedule. The additional
`2*(kappa+1)` counts the two wrapper occurrences' logical parameter tracks
and heads. The wrappers use no random tape.

### 3.3 Exact switching advantage

Couple lazy sampling of `RF_m` and `RP_m`. Give both resources the same fresh
uniform output until the random-function sampler repeats a previously used
output. Before that event their complete adaptive transcripts are identical.

For `d <= 2^m` distinct queried inputs, the exact collision probability is

```text
p_coll(d,m)
  = 1 - product_{i=0}^{d-1} (1 - i/2^m).
```

Since `d <= q`,

```text
p_coll(d,m)
  <= sum_{i=0}^{q-1} i/2^m
  = q(q-1)/2^(m+1).
```

Consequently every adaptive `q`-query distinguisher satisfies

```text
Adv(D,F_j,P_j)
  <= q(q-1)/2^(m+1).
```

Tagging and truncation do not add an error: the coupling is equal before
those deterministic maps, so it remains equal afterward.

### 3.4 Parallel adaptive composition

Now give `D` adaptive access to `h` independently sampled tagged instances.
It may choose both the instance index and the next query from all preceding
responses. Let `q_j` bound its total number of calls to instance `j`; the
number of distinct inputs queried there is at most `q_j`. Let

```text
Q = sum_{j=0}^{h-1} q_j.
```

Construct the lazy function/permutation coupling independently for every
instance and run `D` once against their product.  Until the first
within-instance function-output collision, the entire joint adaptive
transcript is identical.  Conditional on any common history before the `i`th
distinct query to instance `j`, its next fresh function output collides with
one of the preceding `i-1` outputs with probability at most
`(i-1)/2^m`; this remains true even though the choice of `j` and its query
depends on every earlier response from every instance.  A union bound over
query positions and instances gives the fully explicit bound

```text
Adv_parallel
  <= sum_r q_r(q_r-1)/2^(m+1)
  <= Q(Q-1)/2^(m+1).
```

The last inequality uses

```text
sum_r q_r(q_r-1) <= Q(Q-1).
```

The complete wrapper profile across all instances is

```text
Work <= t + Q(8s + 9n + 3l + 12),
Acts <= a_D + 2Q,
Calls <= Q,
QBits <= Qm,
RBits <= Qm,
Traffic <= c_D + 2Qm,
Space <= s_D + h*(4m + 2*kappa + 10),
Random = Random_D.
```

The cumulative coordinates depend on the total call count `Q`. Peak space
also counts all `2h` logical wrapper parameter tracks, which coexist even
under the single-token schedule. The displayed conservative bound simply sums
the `h` per-instance strong space grades; a sharper bound may share transient
buffer terms only after a separate simultaneous-state proof.

This is simultaneously a sequential-converter reduction and an adaptive
parallel-composition calculation. The side resources are named independent
specification nodes; no reduction silently simulates a random permutation by
an unbounded rejection loop.

This paragraph is pointwise for a fixed finite `h`.  If `h=h(kappa)` varies,
uniformity needs additional syntax: a fixed instance-index multiplexer and a
fixed countable product-state RF/RP specification (or another proved array
contract) with aggregate tariffs.  The generated implementation compiler
cannot manufacture `h(kappa)` independent ideal occurrences.  The numerical
instance below uses the fixed value `h=16`.

### 3.5 Numerical instance

Take

```text
m=256, s=32, n=224, l=128,
h=16, q_j <= 2^20.
```

Then `Q <= 2^24`. The parallel switching advantage is at most

```text
2^24(2^24-1)/2^257 < 2^-209.
```

The sequential-wrapper work per query is

```text
8*32 + 9*224 + 3*128 + 12 = 2668.
```

Thus total wrapper work is at most

```text
2668 * 2^24 = 44,761,612,288
```

charged bit-machine steps, in addition to the distinguisher's own work. The
conservative parallel wrapper-space increment is

```text
16*(4*256 + 2*kappa + 10) = 32*kappa + 16,544
```

cells. The number is large despite the tiny information-theoretic loss; the
concrete ledger makes that tradeoff visible.

## 4. A parameter-dependent generated network

### 4.1 Generated graph

Let

```text
q(kappa) = kappa^2 + kappa + 1.
```

The fixed deterministic generator `G_flip` emits a chain of `q(kappa)`
identical one-bit `Flip` nodes. Each node reads one bit, writes its complement,
and emits it to the next node. The boundary input enters node zero and the
last node emits the boundary output.

In the graph encoding of the dossier, use:

- one fixed valid `Flip` program code of length `ell_F`;
- one grade identifier `0`;
- one public owner identifier `0`;
- two ports per node, both using signature index `0`;
- a fixed codec library whose bit codec has index `0`, and a one-entry type
  table containing the pair of indices `(0,0)`;
- boundary labels equal to fixed two- and three-bit strings `in` and `out`;
- implicit node and port indices;
- `q-1` ordered internal edges and two boundary entries.

Put

```text
c_F = ell_F + 2 floor(log_2(ell_F+1)) + 10.
```

For the selected record layout, one node record has exactly:

```text
gamma(ell_F) || ell_F program bits
                                    ell_F
                                    + 2 floor(log_2(ell_F+1)) + 1 bits
grade identifier gamma(0)           1 bit
owner identifier gamma(0)           1 bit
port-count gamma(2)                  3 bits
two (polarity,type-index) records    4 bits
                                     -------
                                    c_F bits.
```

Let

```text
h_q = ceil(log_2(2q+1)).
```

Each node index has gamma length at most `2h_q+1`; a port index is `0` or `1`
and has gamma length at most three. Every edge record, which contains two
`(node,port)` endpoints, therefore has length at most `4h_q+8`.

The fixed 32-bit header and one-entry type list cost `32+3+2=37` bits: the
list count has length three and the two codec indices each have length one.
The node- and edge-list prefixes cost at most `4h_q+2`; the boundary-list
prefix and the two boundary records cost at most `2h_q+22`. Thus the emitted
code length satisfies

```text
L_flip(kappa)
  <= c_F q + (q-1)(4h_q+8) + 6h_q + 61.
```

Here `c_F` is one fixed integer determined once by the literal `Flip` program,
not a parameter-dependent coefficient. Every other term is determined by
`kappa`; there is no unspecified graph-size polynomial.

### 4.2 Generator and native execution cost

`G_flip` uses a unary nested loop to compute `q`, emits each fixed node record,
and emits binary-incremented edge indices. The deliberately loose certified
bounds are

```text
GenWork(kappa)
  = 128(c_F+1)(q(kappa)+1)^2,

GenSpace(kappa)
  = L_flip(kappa) + 16(q(kappa)+1).
```

The work bound follows from at most `q+1` outer iterations, each making
sequential counter/conversion scans of length at most `q+1`, plus writing the
code bounded above in Section 4.1. The space bound explicitly retains the
entire generated code until validation and adds unary counters and scratch
space. Because `q=kappa^2+kappa+1 >= kappa`, its `16(q+1)` term also covers
the generator's own unary parameter track and head. The earlier tempting
linear bound that counted only the counter but not the emitted code would be
false because `L_flip` grows as `Theta(q log q)`.

One `Flip` activation uses four work steps: read, complement branch, write,
and emit. Each one-bit internal route costs five work steps. Hence the native
graph profile for one boundary input is exactly bounded by

```text
NativeWork(kappa)    = 4q + 5(q-1) = 9q-5,
NativeActs(kappa)    = q,
NativeTraffic(kappa) = q-1,
NativeRandom(kappa)  = 0,
NativeSpace(kappa)   = q*(kappa+3).
```

The space bound allocates each decoded node its required logical read-only
`1^kappa` parameter track and parameter head, plus one control/state cell and
one possible output cell. It is conservative under the single-token schedule.
The universal implementation may physically share the immutable parameter
contents, but the exact *virtual native* ledger may not erase these `q`
logical tracks.

The erased output is

```text
x xor (q(kappa) mod 2).
```

### 4.3 Fixed-interpreter profile

For the one-query calculation at workload `b=1`, choose

```text
M_F(kappa) = kappa + q(kappa)*(kappa+16) + 16.
```

It dominates `1+kappa+b` plus every displayed native aggregate coordinate,
including `q(kappa+3)` native space.
Here

```text
H = 1 + NativeWork + NativeActs + NativeOracleCalls
  = 1 + (9q-5) + q + 0
  = 10q-4.
```

Substituting `L=L_flip(kappa)`, this `H`, and `M=M_F(kappa)` in the selected
compiler theorem gives

```text
FixedWork(kappa)
  <= 128(c_F+1)(q+1)^2
     + 128 c_dec (L_flip+1)^2
     + 128 c_eval (L_flip+M_F+2)^2
     + 8192 c_int (10q-4)(L_flip+M_F+2)^2,

FixedSpace(kappa)
  <= L_flip + 16(q+1)
     + 16 s_dec (L_flip+1)^2
     + 16 s_eval (L_flip+M_F+2)^2
     + 256 s_int (L_flip+M_F+2)^2.
```

The fixed interpreter and the generated graph have identical external
transcripts under the tape mapping (there is no randomness here). The
interpreter's cost is the displayed reindexed profile, not `9q-5`.  The six
lower-case constants are fixed once the finite decoder/evaluator/interpreter
routine libraries are expanded to literal machine transitions; none depends
on `kappa` or on this generated family.  The evaluator and the representation
of unused quotas are therefore not hidden initialization costs.

This example resolves all four uniformity questions separately:

1. `G_flip` is one fixed code;
2. graph size has the explicit bound `L_flip`;
3. native quotas are aggregated before interpretation;
4. generation, validation, routing, and interpretation all appear in the
   fixed-template profile.

## 5. Adequacy and feedback calculations

### 5.1 Metered but inadequate

Give `Spin` work quota `kappa^2`. It attempts transitions forever and therefore
returns

```text
Exhaust
```

after the attempt numbered `kappa^2+1`. Its completed ledger has work
`kappa^2`; its exhaustion probability is one. It satisfies
`MeteredBounded` and fails every no-exhaustion and productivity predicate.

### 5.2 Rare exhaustion

For `kappa>=1`, read `kappa` fair bits. On the all-zero string, spin to
exhaustion; otherwise return `0`. Give the program quota
`kappa^2+2kappa+4`, which dominates the read-and-return branch. Then

```text
Pr[Exhaust] = 2^-kappa.
```

It is overwhelmingly no-exhausting, not almost-sure no-exhausting at any
finite parameter.

### 5.3 Credit-guarded feedback

Let an external request to a cyclic two-node service contain a unary countdown
`z` with

```text
|z| <= C_0(kappa,b) = kappa + b
```

Every hidden transfer deletes one symbol, and the active node emits visibly
when the string is empty. Thus the credit is the ghost quantity `|z|` derived
from ordinary message state; neither node reads `b`, the grade, or a meter.
Each activation uses at most

```text
T_max(kappa,b) = 7(kappa+b)+11
```

work, sends at most `kappa+b+3` bits, and at credit zero must emit the visible
answer. Each of the two fixed nodes retains at most `kappa+5` cells (its
unary parameter track/head and four protocol cells), one active transient
frame uses at most `kappa+b+4` cells, and fixed routing control uses eight.
No separate credit counter is represented in this instance; adding one would
add its ordinary storage and update profile.

There are at most `C_0` hidden transfers, one final visible transfer, and
`C_0+1` activations. With
`Route(L)=2L+3`,

```text
Work
 <= (kappa+b+1)(7(kappa+b)+11)
    + (kappa+b+1)(2(kappa+b+3)+3)

 = 9(kappa+b)^2 + 29(kappa+b) + 20.
```

The traffic bound is

```text
(kappa+b+1)(kappa+b+3),
```

the activation bound is `kappa+b+1`, and the global peak-space bound is

```text
2(kappa+5) + (kappa+b+4) + (kappa+b+3) + 8
  = 4kappa + 2b + 25.
```

Random bits and named-oracle calls are zero. A meter with these coordinates
does not fire, and the zero-credit rule proves a visible response. The cycle
is therefore not merely bounded by truncation; it has an explicit progress
certificate.

## 6. Expected-time and almost-bounded failures

### 6.1 Expected polynomial work with nonnegligible exhaustion

At parameter `kappa>=2`, let a named rational Bernoulli kernel choose `Bad`
with probability exactly `1/kappa`; its fixed access tariff is accounted for
separately. On `Bad`, perform `kappa^3` branch-body work; otherwise perform no
branch-body work. Then

```text
E[branch-body work] = (1/kappa) kappa^3 = kappa^2.
```

With budget `kappa^2`, however,

```text
Pr[Exhaust] = 1/kappa,
```

which is not negligible. Expected polynomial work is therefore insufficient
for the efficient-construction witness. Adding the fixed sampling tariff does
not change either conclusion.

### 6.2 Numeric almost-bounded amplification

Put `r_kappa=ceil(sqrt(kappa))`.  Let one fair-tape component overrun exactly
when its next `r_kappa` bits are all zero, so

```text
p_kappa = 2^-r_kappa
```

and otherwise use one step. The function `p_kappa` is negligible: for every
constant `c`, eventually `sqrt(kappa) > c log_2(kappa)`.

Compose

```text
N_kappa = 2^r_kappa
```

independent copies and declare failure when any copy overruns. Then

```text
Pr[any overrun]
  = 1 - (1-p_kappa)^N_kappa
  -> 1 - e^-1.
```

Thus arbitrary parameter-dependent composition does not preserve an
almost-bounded predicate. This particular network has superpolynomial size
and is excluded by the aggregate uniformity discipline; that exclusion is a
premise, not a consequence of almost-boundedness.

### 6.3 Polynomial-size feedback can still manufacture exponential work

Two fixed decrement nodes accept a `kappa+1`-bit counter. Each activation
decrements it once and costs `O(kappa)` work. In isolation, one query causes
one activation. Connect the outputs in a cycle and initialize the counter to
`2^kappa`. The connected graph performs `2^kappa` hidden activations before
the zero case emits visibly.

The graph has two fixed nodes and every activation is polynomial. Nevertheless
its closed work is exponential. This is the explicit numeric
forwarder/repeater pathology that per-activation PPT and local polynomial
shape fail to exclude.

## 7. Oracle admission without response-selection bias

### 7.1 Finite response support

Let a fair-bit oracle have

```text
K(0)=K(1)=1/2,
tau(0)=1,
tau(1)=2.
```

With one remaining unit, sample-then-check yields:

```text
Pr[Success with 0]=1/2,
Pr[Exhaust]=1/2,
Pr[Success with 1]=0.
```

Conditioned on success, the response is `0` with probability one. Retrying
after rollback returns `0` with probability one and hides the rejection
entirely.

The exact reservation is

```text
reserve = max(tau(0),tau(1)) = 2.
```

With budget at least two, admission occurs before sampling and the delivered
bit remains fair. With budget one, exhaustion occurs before sampling. There is
no conditioned kernel and no state rollback.

### 7.2 Unbounded response length

Let an oracle sample a finite response length `L >= 1` with

```text
Pr[L=j] = 2^-j
```

and then return `j` fair bits. No finite query-only reservation dominates the
response length.

Use the stateful one-bit streaming oracle and the fixed reassembly converter
`A_1` from `oracle-semantics.md`.  At `Start`, commit the sampled `L`, response,
and next state once.  Give `A_1` at least `B` chunk calls, `B` response-bit
units, `B` cells of buffer space, and enough local work to request, store, and
emit `B` bits.  After hiding the chunk interface, the run completes exactly
on `L<=B`. Therefore

```text
Pr[Exhaust] = Pr[L>B]
            = sum_{j=B+1}^infinity 2^-j
            = 2^-B.
```

For `B=kappa`, exhaustion is negligible. Coupling the original oracle and
`A_1` attached to the streaming oracle with the same sampled response gives
total-variation distance at most `2^-kappa` on the original external
interface. The law conditioned on completion is truncated toward shorter
responses, but neither the semantics nor the theorem substitutes that
conditional law for the original oracle.

### 7.3 Exact lazy random-function implementation

For polynomial lengths `m=m(kappa)`, `n=n(kappa)` and lifetime call envelope
`Q=Q(kappa,b)`, a fixed `LazyRF` component stores distinct `(x,y)` pairs in a
sequential table.  A repeat scans and copies the stored result; a new input
uses the next `n` fair-tape bits, appends the record, and returns it.

For a table with at most `Q` records, the complete conservative profile is

```text
Work
  <= Q(4Q(m+n+8)+8(m+n+1)) + LenEval(kappa),

Space
  <= (Q+1)(m+n+8) + LenSpace(kappa),

Random <= Qn,
Acts   <= Q.
```

`LenEval(kappa)` pays the fixed machines evaluating and validating
`m(kappa),n(kappa)`. `LenSpace(kappa)` includes their simultaneous scratch,
the retained logical `1^kappa` track, and its parameter head. Thus the
asymptotic input and its length computations are not free space.

Each stored record has encoded length at most `m+n+8`; the quadratic scan
therefore pays to traverse values as well as keys. Closing-boundary traffic
contributes at most `Qm` query bits and `Qn`
response bits and must be funded by route-safe closure or an explicit
envelope.  The quadratic work term is intentional: sequential lookup is not
RAM.  Induction over an adaptive query history gives exact equality with a
uniform random function, because the value at every first-seen input and the
next unused tape block are both conditionally independent uniform `n`-bit
strings.  Thus the implementation occurrence has zero semantic error, never
exhausts, and answers every delivered query on the funded `Q`-call domain. A
closed productivity conclusion additionally adds the completion context's
failure bound `chi_D` and is strong only when `chi_D=0`.

## 8. Summary table

| Example | Exact work/profile | Failure/advantage |
|---|---|---|
| Persistent mask, `q` calls | `22q+2` work, `3q` activations, `2q` traffic | persistent vs fresh: `1-2^(1-q)` |
| Tagged/truncated RP/RF, `Q` calls | wrapper `Q(8s+9n+3l+12)` | at most `Q(Q-1)/2^(m+1)` |
| Generated flip chain | native `9q-5`; fixed interpreter formula in Section 4.3 | exact parity behavior |
| Credit feedback | `9(kappa+b)^2+29(kappa+b)+20`; space `4kappa+2b+25` | zero exhaustion on certified domain |
| Expected-time example | expectation `kappa^2` | exhaustion `1/kappa` |
| Almost-bounded copies | one-copy failure `2^-sqrt(kappa)` | composed failure tends to `1-e^-1` |
| Geometric streaming oracle | response budget `B` | exhaustion and coupling loss `2^-B` |
| Lazy random function, `Q` calls | `Q(4Q(m+n+8)+8(m+n+1))+LenEval` work; `(Q+1)(m+n+8)+LenSpace` space | exact response law; local zero exhaustion |

## 9. Route-safe plumbing calculations

The route-safe bridge distinguishes canonical structural routing from an
explicit limited communication resource. For the selected router routine,

```text
Route(L) = 2L + 3 work
```

and one live transfer holds at most `L` payload bits plus fixed control.
Whenever a concrete graph certificate already gives event count `E`, aggregate
routed bits `B`, and maximum event length `L_max`, the sharper canonical
envelope

```text
RouteWork    = 3E + 2B,
RouteTraffic = B,
RouteSpace   = L_max + fixed control
```

may be used instead of the deliberately loose machine-work envelope in
`partial-random-system-bridge.md`.

### 9.1 Persistent mask

Each outer call to `C[K]` creates exactly two hidden one-bit events: the key
request and key response. For `q` outer calls,

```text
E = 2q,
B = 2q,
L_max = 1.
```

Hence

```text
RouteWork    = 3(2q) + 2(2q) = 10q,
RouteTraffic = 2q.
```

This is exactly the routing contribution already included in lifetime work
`22q+2`. The machine-only contribution is therefore `12q+2`. Assigning the
canonical infrastructure at least the displayed envelope makes the router
strongly no-exhausting without erasing its `10q` exact work.

### 9.2 Generated flip chain

One boundary input traverses `q-1` internal one-bit edges. Thus

```text
E = B = q-1,
RouteWork = 5(q-1),
RouteTraffic = q-1.
```

The `q` node activations use `4q` machine steps, so

```text
4q + 5(q-1) = 9q-5,
```

recovering the native-work formula. Route safety adds no behavioral
assumption: the exact aggregate certificate already funds every transfer.

### 9.3 Tagged/truncated RF/RP wrapper

Every outer query produces one routed `m`-bit inner query and one routed
`m`-bit response. For `Q` calls,

```text
E = 2Q,
B = 2Qm,
RouteWork = Q(4m+6),
RouteTraffic = 2Qm.
```

These are precisely the two route phases in the wrapper derivation. A
bandwidth cap below `2Qm` would be modeled as a separate communication
resource and could legitimately change the erased behavior; it must not be
hidden by calling the structural router route-safe.
