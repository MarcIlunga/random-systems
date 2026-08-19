# Adequacy and closure for the metered operational layer

## 1. Why bounded execution is not an efficiency theorem

An external polynomial meter can stop every finite program graph after a
polynomial number of charged events. This yields a useful *total lower
execution relation*, but it does not establish any of the following:

1. that the program stays within its advertised budget;
2. that the program produces a visible response;
3. that its response agrees with its unmetered execution;
4. that it implements the intended abstract resource.

These are distinct predicates. In particular, a machine that deliberately
spins until its meter fires is metered-bounded. It is not an efficient
implementation of a responsive service.

This note fixes the quantifiers and gives the adequacy judgment used in the
efficient construction theorem.

## 2. Experiments and quantifier modes

### 2.1 Closed metered experiment

Fix:

- a security parameter `kappa` represented in unary;
- a public or auxiliary input `a`;
- a fixed uniform context code `D`;
- a fixed metered implementation or specification network `X`;
- the context's fixed polynomial ambient policy `p_D`;
- ambient workload `b_D(kappa,a) = p_D(kappa + |a|)`;
- the product probability space of all named machine tapes and the selected
  uniform seed sequences realizing specification-oracle kernels, together
  with the declared initial specification-state laws.

The closed metered experiment is written

```text
Run[D, X](kappa,a) in
  { Success(tau,o,ell),
    Block(v,tau,o,ell),
    Exhaust(v,tau,o,ell) }.
```

Here `tau` is the complete finite visible transcript, `o` is the context's
designated finite observation of its own terminal state (including its
decision when it produces one), `ell` is the exact lifetime ledger, and `v`
is the public ownership label of the occurrence whose action blocked or whose
meter rejected the next action. Ownership labels distinguish the tested
subsystem, the closing context, and explicitly shared infrastructure; they do
not expose fresh internal alpha-names. The external meter is deterministic
once the random tapes, oracle seeds, and initial specification states are
fixed. Programs cannot inspect quotas, remaining credit, or an impending
exhaustion.

For a declared set `A` of owned occurrences, let

```text
Exh_A[D,X,kappa,a]
  := { Run[D,X](kappa,a) is Exhaust(v,...) with v in A },

Blk_A[D,X,kappa,a]
  := { Run[D,X](kappa,a) is Block(v,...) with v in A },

Exh_all[D,X,kappa,a]
  := union over all owners A of Exh_A[D,X,kappa,a],

Suc[D,X,kappa,a]
  := { Run[D,X](kappa,a) is Success }.
```

`Success`, all ownership-labeled block events, and all ownership-labeled
exhaustion events partition the sample space once the oracle sampling rule is
fixed.  The label is necessary: without it, a context that deliberately spins
until its own meter fires would make *every* tested resource fail
no-exhaustion.

### 2.2 Admitted completion contexts

Resource adequacy is quantified over a declared completion-context class
`C`. Each `D in C` contains:

1. its fixed polynomial workload and grade;
2. an interface envelope describing the responses it is prepared to receive;
3. a context-safety certificate showing overwhelming (or stronger)
   no-exhaustion of context-owned occurrences whenever the tested side obeys
   that envelope;
4. a context-progress certificate showing that, whenever the tested side
   answers within that envelope, the context does not deliberately block or
   stop silently and reaches its designated decision within its certified
   bound (up to a separately stated failure probability);
5. a declaration of which shared router/oracle meters are charged to the
   context and which to the tested construction.

This premise does not assume that `X` is correct. It prevents a deliberately
self-exhausting or self-blocking observer from being used to refute
availability of every resource. Arbitrary metered cost-aware distinguishers
remain valid for behavioral security because their fixed graded terminal
scorer and default produce a decision; the extra context-safety and
context-progress premises are used only for no-exhaustion/productivity
judgments.

For later constructor theorems, write `CtxFail_D` for the union of
context-owned safety failure, declared shared-infrastructure failure, and
context-progress failure on a run where the tested side stays inside the
advertised response envelope. Let

```text
Pr[CtxFail_D] <= chi_D(kappa)
```

be the sum of the three certified bounds (or any sharper proved bound).
`chi_D=0` in the strong completion-context variant. A local service theorem
proves that the tested graph answers; a theorem about the closed `Success`
event must additionally carry `chi_D`.

### 2.3 Context and auxiliary-input modes

The phrase “for every efficient context” is always interpreted one fixed code
at a time. The polynomial and negligible functions may depend on that code,
but never on `kappa` or on the input selected at that parameter.

We use three input modes.

**Pure uniform mode.** A fixed deterministic polynomially graded generator
`G_D`, included in the context description, produces
`a = G_D(1^kappa)`. Its work, space, output length, retained output, and input
installation are part of the context's initialization profile; it receives no
ambient workload. Quantification is over fixed pairs `(D,G_D)`.

**Bounded auxiliary-input mode.** The context description contains a fixed
polynomial `q_D`; the property must hold uniformly for every bit string
`a` with `|a| <= q_D(kappa)`. Equivalently, probabilities below are replaced
by their supremum over that set. This mode has nonuniform distinguishing
strength because the worst `a` may vary arbitrarily with `kappa`.

**Explicit nonuniform mode.** The context receives an advice string `z_kappa`
from a named advice sequence satisfying `|z_kappa| <= q_D(kappa)`. The advice
sequence and combined public-input/advice length bound are part of the
quantified object. Supplying them does not charge a generator, but occupied
cells, validation, delivery, and processing are charged.

No theorem silently moves between these modes.

For compactness, write

```text
sup_M Pr[E(kappa,a)]
```

for:

- the single generated input in pure uniform mode;
- `sup_{|a| <= q_D(kappa)} Pr[E(kappa,a)]` in bounded auxiliary-input mode;
- the probability at the named advice and generated public input in explicit
  nonuniform mode.

Random tapes, oracle seeds, and random initial specification states are inside
`Pr`; auxiliary inputs are not.

## 3. Four separate predicates

### 3.1 Metered boundedness

`MeteredBounded_M(X)` holds when, for every fixed admitted context `D`, there
is a polynomial `P_D` such that, for all `kappa`, all inputs allowed by mode
`M`, and every choice of random tapes, selected oracle seed sequences, and
initial specification states,

```text
Run[D,X](kappa,a)
```

terminates in `Success`, `Block`, or `Exhaust`, and every coordinate of its
ledger is at most `P_D(kappa)`.

This is a worst-case property over the operational samples. In the selected
finite-graph metered model it follows syntactically from the grades after
substituting `b_D`. It says nothing about which terminal status occurs.

For specification oracles with unbounded response-length support, the
baseline bounded-call contract does not apply: no finite public pre-sample
reservation dominates the response. Such an interface must be publicly capped
or replaced by a stateful fixed-chunk oracle and a metered reassembly
converter. Strong boundedness then quantifies over the named seed sequence and
uses the converter's finite chunk, local-work, output, and buffer quotas. The
sampled response is never rolled back merely because reassembly later
exhausts.

### 3.2 No-exhaustion

There are three useful no-exhaustion strengths.

Let `A_X` be the declared ownership scope of the tested implementation,
including its protocol/simulator occurrences and any boundary infrastructure
assigned to it.  Write

```text
Exh_X[D,X,kappa,a] = Exh_(A_X)[D,X,kappa,a].
```

The predicates below concern `Exh_X`.  A *global* no-exhaustion conclusion
additionally unions the context and shared-infrastructure failure bounds.

**Strong no-exhaustion**

```text
StrongNoExhaust_M(X;C)
```

holds if `Exh_X[D,X,kappa,a]` is empty for every admitted `D in C`, every
`kappa`, every allowed `a`, and every machine-tape/oracle-seed sample.

**Almost-sure no-exhaustion**

```text
ASNoExhaust_M(X;C)
```

holds if, for every admitted `D in C`, every `kappa`, and every allowed `a`,

```text
Pr[Exh_X[D,X,kappa,a]] = 0.
```

This is a pointwise measure-zero statement, not an asymptotic one.

**Overwhelming no-exhaustion**

```text
OWNoExhaust_M(X;C)
```

holds if, for every admitted fixed context `D in C`, there is a negligible function
`nu_D` such that, for every `kappa`,

```text
sup_M Pr[Exh_X[D,X,kappa,a]] <= nu_D(kappa).
```

The negligible function may depend on the fixed context and its fixed
polynomials, but not on `a` or `kappa`.

The baseline efficient-construction judgment uses overwhelming
no-exhaustion. Strong and almost-sure variants are recorded when available.
Expected polynomial cost is not used as a substitute.

If `D`'s context-safety failure is at most `nu_D^ctx` and shared
infrastructure failure is at most `nu_D^sh`, then

```text
Pr[Exh_all]
  <= Pr[Exh_X] + nu_D^ctx + nu_D^sh.
```

Thus tested-side and context certificates yield the global closed-experiment
bound needed by a construction witness.

### 3.3 Productivity

Let `C` be a declared class of *completion contexts*. Such a context has a
decision interface and is considered complete only when it emits a visible
decision. It may call the tested resource adaptively before doing so. Its
context-progress certificate excludes deliberate context-owned block or
silent stop on executions where the tested side meets the declared response
envelope; otherwise a context that always blocks would make every resource
nonproductive.

**Overwhelming productivity relative to `C`** holds when, for every fixed
`D in C`, there is a negligible `eta_D` with

```text
sup_M Pr[not Suc[D,X,kappa,a]] <= eta_D(kappa).
```

Since the three terminal events partition the experiment, overwhelming
productivity implies overwhelming no-exhaustion. The converse fails because a
program can block without exhausting.

For an intentionally partial specification `S`, unconditional productivity is
the wrong contract. Let `C_S` be the contexts and inputs on which the
specification is declared responsive. Then `Productive_M(X | S;C)` quantifies
only over `C_S`. The responsiveness contract is part of the specification; it
cannot be reconstructed from an arbitrary partial DDS after the fact.

### 3.4 Behavioral realization

Let `erase` remove the ledger and identify both `Block` and `Exhaust` with
strict nonresponse. Let `Law_D(erase X;kappa,a)` be the resulting ordinary
transcript law. For an observer class `C` and distance `d_C`, define

```text
Realizes_M(X,S;epsilon)
```

to mean that for every fixed admitted observer `D`, every `kappa`, and all
inputs allowed by mode `M`,

```text
d_D(erase X, S; kappa,a) <= epsilon_D(kappa).
```

For computational realization, `D` ranges over fixed uniform graded
distinguishers and `epsilon_D` is negligible or is bounded by the named
construction error. For information-theoretic realization, `D` may range over
the chosen abstract observer carrier.

Behavioral realization alone is not an efficiency predicate. If `S` is strict
nonresponse, a program that always exhausts realizes `S` after erasure.

## 4. Exact implication and separation results

### Proposition 4.1 — implication chain

For every input mode `M`,

```text
StrongNoExhaust_M(X;C)
  => ASNoExhaust_M(X;C)
  => OWNoExhaust_M(X;C).
```

Moreover,

```text
Productive_M(X | S;C) => OWNoExhaust_M(X;C)
```

on the same completion-context class.

**Proof.** An empty event has probability zero, and zero is negligible.
Failure of success contains the exhaustion event.

### Counterexample 4.2 — metered boundedness does not imply no-exhaustion

Let `Spin` ignore its input and perform charged transitions forever. Give it
work quota `kappa^2`. Every closed execution terminates after exactly
`kappa^2 + 1` attempted charged transitions with `Exhaust`. Thus it is
metered-bounded by `kappa^2`, while

```text
Pr[Exh] = 1
```

for every parameter.

### Counterexample 4.3 — no-exhaustion does not imply productivity

Let `Silent` enter `Block` in one transition. It never exhausts and uses
constant resources, but `Pr[Suc] = 0` in every completion context that waits
for a response.

### Counterexample 4.4 — productivity does not imply correct realization

Let the target bit resource return its input bit and let `Flip` return its
complement in linear time. The `Flip` occurrence strongly never exhausts and
answers every delivered query; in a strong completion context it is
productive. A one-query context distinguishes it from the target with
advantage one.

### Counterexample 4.5 — behavioral realization does not imply adequacy

Let the target be strict nonresponse and let `Spin` be as in Counterexample
4.2. After erasure both experiments have the same ordinary partial transcript.
Their behavioral distance is zero, although the implementation exhausts with
probability one.

### Counterexample 4.6 — overwhelming is strictly weaker than almost sure

On parameter `kappa`, read `kappa` fresh fair bits. If all are zero, spin until
the meter fires; otherwise return `0` immediately. Then

```text
Pr[Exh] = 2^(-kappa).
```

The family is overwhelmingly no-exhausting but not almost-sure
no-exhausting at any finite parameter.

### Proposition and counterexample 4.7 — almost sure versus strong

In the machine-only model with fair Bernoulli tapes, every finite exhaustion
has a finite-prefix witness. Every such cylinder has positive probability.
Consequently almost-sure no-exhaustion implies strong no-exhaustion on
reachable tape samples.

For specifications, the sufficient hypothesis is a *positive-branch
presentation*. The initial-state law and, at every reachable complete
history, each selected oracle randomization admit a countable measurable
branch label such that:

1. conditional on the preceding branch labels and machine bits, the new label
   determines every part of the successor needed for subsequent finite
   operational behavior—not merely its response and public contract
   coordinate; and
2. every label in the selected sampler's reachable range has strictly positive
   conditional probability.

An exhaustion run has a finite operational witness. It therefore fixes
finitely many fair bits and positive branch labels, whose iterated conditional
probability is positive. Almost-sure no-exhaustion then excludes that witness
and implies strong no-exhaustion on the selected reachable sample
presentation.

Positive support of the response alphabet alone is insufficient. Two hidden
successor states may return the same public value and induce different later
behavior; likewise a continuously distributed initial hidden state may have a
null exceptional point. Such future-relevant null classes violate the
positive-branch premise.

Without the positive-branch premise the implication is strict. Let an
abstract oracle use an underlying uniform sample `u in [0,1]`, return the same
public value on every seed, but install a hidden bad state when `u=0`. On the
next call the bad state makes the program spin until exhaustion; every other
state returns immediately. The exhaustion sample set is nonempty but has
measure zero. The program is almost-sure no-exhausting but not strongly
no-exhausting under the raw-sample definition, although the response alphabet
is a singleton with full support. The same example can be placed in the
initial-state law.

Separately, the familiar program that reads random bits until the first `1`
terminates almost surely in the *unmetered* semantics, but with any finite
meter its exhaustion probability is positive. Thus almost-sure unmetered
termination does not imply almost-sure no-exhaustion at a chosen finite grade.

### Counterexample 4.8 — expected polynomial cost does not imply overwhelming
no-exhaustion

At parameter `kappa>=2`, let `m=ceil(log_2(kappa))`, read exactly `m` fair
bits, and perform `kappa^3` further steps iff all are zero.  This is one fixed
uniform fair-bit program.  The long branch has probability

```text
2^(-m) in [1/(2*kappa),1/kappa].
```

Its expected work is at most `kappa^2+O(log kappa)`. Against a work meter of
`kappa^2+O(log kappa)`, however, the long branch exhausts and

```text
Pr[Exh] >= 1/(2*kappa),
```

which is not negligible. An expected-cost definition therefore cannot replace
the overwhelming no-exhaustion premise of a cryptographic theorem.

### Proposition 4.9 — coupling with the unmetered execution

Fix tapes, oracle seed sequences, and initial specification states. Until the
first exhaustion check fires, the metered and unmetered runs have identical
configurations, visible events, and ledger prefixes. Consequently, for every
finite transcript event `A`,

```text
|Pr[erase(Run_metered) in A] - Pr[Run_unmetered in A]|
  <= Pr[Exh_all].
```

The same inequality holds for total-variation distance on the finite
transcript sigma-algebra.

**Proof.** Couple both runs with the same tapes, oracle seeds, and initial
specification states. The meter does not alter a transition that fits and is
not program-visible. The two outputs can differ only on samples at which the
meter fires. Apply the coupling inequality.

### Corollary 4.10 — productivity transfer from a responsive target

Suppose a completion context obtains a decision from `S` with probability at
least `1 - eta`, and the erased implementation is within statistical distance
`epsilon` of `S`. Then it obtains a decision from the erased implementation
with probability at least

```text
1 - eta - epsilon.
```

If the costed implementation also has exhaustion probability at most `nu`,
then one may retain `nu` as a separate cost-adequacy guarantee. Under a
maximal coupling of the erased transcript laws, the probability of target
noncompletion or visible transcript mismatch is at most `eta + epsilon`.
Exhaustion is already one way for the erased implementation not to complete,
so adding `nu` again would be a valid but needlessly loose union bound. If a
statement separately lists the three disjoint lower failures `Exhaust`,
`Block`, and visible mismatch, it must define the mismatch event under the
coupling before summing them.

## 5. Constructor rule for acyclic hidden calls

### 5.1 Local certificates

Let the hidden-call graph be a fixed finite directed acyclic graph. A local
certificate for component occurrence `v` contains fixed monotone polynomials:

```text
t_v(kappa,b,n,(R_w)_w) local charged work per activation,
r_v(kappa,b,n,(R_w)_w) maximum encoded response length of v,
u_v(kappa,b,n,(R_w)_w) active/suspended transient space per activation,
p_v(kappa,b,N,n,(R_w)_w)
                            lifetime persistent space after <= N activations,
m_vw(kappa,b,n)        maximum encoded query length sent from v to child w,
q_vw(kappa,b,n)        calls from one activation of v to child w,
delta_v(kappa,b,n)     probability of local certificate failure.
```

Here `n` bounds the encoded activation input and `(R_w)_w` supplies the
already certified child-response bounds used by the local parser and
continuation. The certificate has the semantic premise that, whenever child
calls satisfy those response-size contracts, component `v` returns or emits
one of the certified child calls within `t_v` local work and respects the
stated query-size, response-size, and call bounds. This elementary DAG rule
requires `m_vw` and `q_vw` to be independent of returned child values; local
work and the final response may depend on their certified length bounds
through `(R_w)_w`. Adaptive query growth needs a stronger local size invariant
or an explicitly solved polynomial recurrence and is not smuggled into this
rule. Child work is charged to the child occurrence and is not counted a
second time in `t_v`.

The persistent/transient split is semantic and mandatory for stateful
components. `p_v` includes the occurrence's parameter track, heads, tables,
and every cell retained between activations, uniformly over all certified
histories of length at most `N`. `u_v` includes the active frame, suspended
continuation, and activation-local buffers but excludes those persistent
cells. A one-activation peak bound cannot be reused as a lifetime persistent
bound after polynomially many calls.

In the probabilistic variant, `delta_v` is a bound on the conditional failure
probability given *every* certified pre-activation history and every adaptive
choice of earlier child responses.  A merely marginal bound for an isolated
activation is insufficient: another component could steer execution into its
rare hard inputs.  No independence assumption is used by the later union
bound. Failure means the first violation of the local progress, size, or
ledger contract. Prior to that event, the local certificate guarantees that
the activation either returns or issues one of its certified child calls.

### 5.2 Recursive aggregate

First process vertices in topological order from roots toward sinks. Let
`L_v` bound the input length of an activation of `v`. Set each root's `L_v`
and activation count `N_v` from the context's polynomial query and message
bounds. Recursively define

```text
N_w = sum_{v -> w} N_v * q_vw(kappa,b,L_v),
L_w = max_{v -> w} m_vw(kappa,b,L_v).
```

Then process vertices in reverse topological order and define

```text
R_v = r_v(kappa,b,L_v,(R_w)_{v -> w}).
```

Because the graph and its longest path are fixed and every displayed function
is a fixed polynomial, every `N_v`, `L_v`, and `R_v` has a polynomial upper
bound in `(kappa,b)`. Define

```text
Work_ACY = sum_v N_v * t_v(kappa,b,L_v,(R_w)_{v -> w}),
Fail_ACY = sum_v N_v * delta_v(kappa,b,L_v).
```

For space, define the transient call-stack recurrence

```text
Stack_v
  = u_v(kappa,b,L_v,(R_w)_{v -> w})
    + max_{v -> w} Stack_w
    + RouteStack_v,

Persist_ACY
  = sum_v p_v(kappa,b,N_v,L_v,(R_w)_{v -> w}),

Space_ACY
  = Persist_ACY + max_{root v} Stack_v + RouteBase_ACY.
```

Empty maxima are zero. `RouteStack_v` covers the suspended call record and
one active routed event at that level; `RouteBase_ACY` covers fixed router and
meter state. The sum is essential: inactive siblings' persistent states
coexist, while only the transient frames lie on one active root-to-leaf path.
All terms are fixed polynomial compositions.

### Theorem 5.1 — acyclic adequacy

If the meter quotas dominate the recursively computed ledger envelope, then:

1. the connected graph is metered-bounded;
2. if every local certificate is worst-case, the tested graph strongly
   answers without tested-side exhaustion on its declared domain; its closed
   completion experiment has failure probability at most `chi_D`;
3. with probabilistic local certificates, tested-side failure is at most
   `Fail_ACY`, and closed completion failure is at most
   `Fail_ACY+chi_D`. Hence it is overwhelmingly no-exhausting/productive when
   the local bounds and `chi_D` are negligible.

**Proof.** Induct upward from sinks. Each activation has only certified
children, and the DAG prevents re-entry at the same or a higher level. The
recursive counts bound every activation and message size. Summing the local
work bounds gives the cumulative quota envelope. The same induction bounds
one active transient stack; the forward `N_v` bounds every persistent
certificate, whose sum coexists globally. This proves `Space_ACY`. In the
probabilistic case, order the
deterministic activation slots and expose only the event that one slot is the
first local failure. Before that event all earlier contracts hold, so the
displayed `N_v` bounds the number of candidate slots. Condition on each
certified prefix and sum the history-uniform bounds. This is a stopped union
bound; behavior after the first failure is immaterial and independence is
unnecessary.

This rule is compositional only when the connection preserves acyclicity or
when a new aggregate certificate is supplied. “Each operand is acyclic” does
not imply that connecting them leaves the union acyclic.

### 5.4 Response-adaptive calls by a solved polynomial invariant

Acyclicity alone does not control repeated adaptive calls from one activation
to a lower-ranked child.  The following stronger certificate admits them
without pretending that iteration of an arbitrary polynomial stays
polynomial.

For each edge `v -> w`, let the local certificate give monotone polynomials

```text
Q_vw(kappa,b,n,z)  total calls to w,
M_vw(kappa,b,n,z)  length of the next query to w,
```

valid whenever the cumulative encoded length of child responses already
received in the activation is at most `z`.  Let

```text
t_v(kappa,b,n,z)   total local work,
u_v(kappa,b,n,z)   active/suspended transient space,
p_v(kappa,b,N,n,z) lifetime persistent space after <= N activations,
r_v(kappa,b,n,z)   final response length,
delta_v(kappa,b,n,z)
                       conditional local-certificate failure probability
```

be bounds under the same invariant. The failure bound is uniform over every
certified adaptive history whose current cumulative response length is at
most `z`. These are semantic certificates for the fixed program, not
conclusions from syntax. On a nonfailure branch, each activation either
returns or issues a certified child call within the displayed local envelope.

Process the fixed DAG from sinks toward roots. Suppose each child `w` already
has response, work, and transient-stack envelope functions

```text
Resp_w(kappa,b,m),
Work_w(kappa,b,m),
Stack_w(kappa,b,m)
```

for an input of length at most `m`.  The certificate for `v` supplies one
fixed monotone polynomial `Z_v(kappa,b,n)` and a proof of the post-fixed-point
inequality

```text
sum_{v -> w}
  Q_vw(kappa,b,n,Z_v)
  * Resp_w(kappa,b,M_vw(kappa,b,n,Z_v))
<= Z_v(kappa,b,n).                                    (RA)
```

For a sink take `Z_v = 0`.  Define

```text
Resp_v(kappa,b,n)
  = r_v(kappa,b,n,Z_v),

Work_v(kappa,b,n)
  = t_v(kappa,b,n,Z_v)
    + sum_{v -> w}
        Q_vw(kappa,b,n,Z_v)
        * Work_w(kappa,b,M_vw(kappa,b,n,Z_v))
    + Route_v(kappa,b,n,Z_v),

Stack_v(kappa,b,n)
  = u_v(kappa,b,n,Z_v)
    + max_{v -> w}
        Stack_w(kappa,b,M_vw(kappa,b,n,Z_v))
    + AdminStack_v(kappa,b,n,Z_v).
```

`AdminStack_v` accounts for the fixed-depth suspended call stack and the one
live routing buffer at that level. It does not include lifetime persistent
state. Other cumulative ledger coordinates use the same sum pattern. Because
the graph is fixed and every displayed expression is one fixed polynomial,
these per-activation envelopes are polynomial.

### Theorem 5.2 — response-adaptive acyclic adequacy

Assume the local adaptive certificates above, inequality `(RA)` for every
vertex and all natural `(kappa,b,n)`, and history-uniform conditional failure
bounds.  Compute global root inputs and activation multiplicities in the
forward direction using

```text
Q_vw(kappa,b,L_v,Z_v(kappa,b,L_v)),
M_vw(kappa,b,L_v,Z_v(kappa,b,L_v)).
```

After this forward pass, define

```text
Persist_RA
  = sum_v p_v(kappa,b,N_v,L_v,Z_v(kappa,b,L_v)),

Space_RA
  = Persist_RA
    + max_{root v} Stack_v(kappa,b,L_v)
    + RouteBase_RA.
```

`RouteBase_RA` covers fixed router and meter state. This global expression,
not a maximum of complete child peaks, is the response-adaptive space grade:
all occurrences' persistent states coexist, while one token activates only
one root-to-leaf transient stack.

Then meters dominating the resulting response-adaptive ledger envelope make
the tested graph strongly answer without tested-side exhaustion for
worst-case certificates. With probabilistic local certificates, define

```text
Fail_RA
  = sum_v N_v
      * delta_v(kappa,b,L_v,Z_v(kappa,b,L_v)).
```

`Fail_RA` bounds tested-side failure. Against completion context `D`, the
closed completion failure is at most `Fail_RA+chi_D`. It is overwhelmingly
adequate whenever both terms are negligible, relative to environments obeying
the advertised root workload and response envelope. In the worst-case local
variant `Fail_RA=0`; strong *closed* productivity additionally requires
`chi_D=0`.

**Proof.**  Consider one activation of `v` and suppose, toward a
contradiction, that its cumulative received-response length first exceeds
`Z_v`.  Before the crossing, every prefix satisfies the local invariant.
Hence every issued query has length at most the corresponding `M_vw` evaluated
at `Z_v`, the total number of calls is at most the corresponding `Q_vw`, and
the child induction hypothesis bounds every response.  The cumulative length
of all such responses is therefore at most the left side of `(RA)`, which is
at most `Z_v`, a contradiction.  Thus the invariant holds for the whole
activation. The displayed response, work, and transient-stack recurrences
follow. Reverse induction over the DAG proves the per-input envelopes; the
forward pass bounds activation multiplicity and hence every `p_v`. Summing
those simultaneous persistent bounds and adding the one active stack proves
`Space_RA`. Conditional union bounds handle local
probabilistic failures without independence: stop at the first failed
certificate, observe that every earlier activation was certified and
therefore belongs to one of the deterministic forward-count slots, condition
on its complete certified prefix, and sum the displayed `delta_v` bounds.

The candidate `Z_v` and proof of `(RA)` are substantive data.  They do not
exist for every locally polynomial program.  For example, let one activation
make `kappa` calls to an echo child, starting with a two-bit query and making
each next query the square-length encoding of the preceding reply.  The graph
has only the edge `v -> w`, but response lengths reach
`2^(2^(kappa-1))`.  The natural local bound has
`M_vw(z) >= z^2`, and no nonzero polynomial `Z_v` can satisfy
`Z_v >= kappa * Z_v^2` for all large parameters.  The new rule rejects this
acyclic but exponentially amplifying composition for the right reason.

Conversely, if every child reply has a public bound
`lambda(kappa,b)` independent of its query and the parent makes at most
`q(kappa,b,n)` calls, then

```text
Z_v(kappa,b,n) = q(kappa,b,n) * lambda(kappa,b)
```

satisfies `(RA)`.  The next query may depend arbitrarily on the contents and
cumulative length of prior replies, provided its certified length polynomial
is evaluated at this `Z_v`.  Thus the rule permits genuine adaptivity; it
excludes uncontrolled iterated size amplification.

## 6. Constructor rule for feedback by affine credit

### 6.1 Credit protocol

A feedback-capable macro execution receives an administrative credit

```text
C_0(kappa,b) in N
```

bounded by a fixed polynomial. Credit is held by the external operational
semantics, not by program memory. Equivalently, it may be a ghost variant
derived from ordinary machine state. If a concrete implementation instead
stores or transmits the counter, its encoding, head position, update work, and
message field are charged in the ordinary ledger; the proof rule does not
make such storage free.

The protocol rules are:

1. every hidden transfer through a feedback edge consumes at least one unit;
2. no hidden step can increase credit;
3. a component activated with credit `c` either
   - emits a visible response within its certified local work bound, or
   - emits one hidden event carrying strictly smaller credit;
4. at credit zero, every reachable activation emits a visible response within
   its certified local work bound;
5. message-size and local-work certificates are monotone polynomials in
   `(kappa,b,C_0)`;
6. each occurrence `v` supplies a polynomial
   `P_v(kappa,b,C_0)` bounding every cell retained between activations after
   any certified prefix of this macro execution, including its parameter
   track and any represented credit state.

The graph may contain arbitrary directed cycles. The dynamic credit, rather
than graph acyclicity, rules out an infinite hidden traversal.

### Theorem 6.1 — credit-guarded feedback adequacy

For a fixed finite graph satisfying the credit protocol uniformly over every
reachable history and remaining-credit value, every macro execution has at
most `C_0` hidden feedback transfers and at most `C_0 + 1` component
activations before a visible response. If

```text
T_max(kappa,b,C_0)
```

bounds the work of any such activation, `L_max` bounds every hidden and
visible message, and `S_max` bounds the transient state of an active
occurrence, then

```text
Work <= (C_0 + 1) * T_max + Routing(C_0+1,L_max),
```

and the corresponding traffic, activation, randomness, and space coordinates
have fixed polynomial bounds. More explicitly, traffic is at most
`(C_0+1)L_max` up to the fixed message framing and routing constants;
cumulative coin and oracle-call coordinates sum their local per-activation
envelopes. Put

```text
Persist_Credit = sum_v P_v(kappa,b,C_0).
```

Peak space is at most `Persist_Credit` plus one live `L_max`-bounded message,
one `S_max`-bounded active transient state, and the fixed routing stack. A meter
dominating these bounds never exhausts. The tested graph emits its certified
visible response on this domain; closed completion success additionally uses
the context certificate quantified by `chi_D`.

**Proof.** Credit is a natural-valued variant that strictly decreases on every
hidden feedback transfer. Hence there can be at most `C_0` such transfers.
Rule 4 forces the last activation to be visible rather than blocked. Sum the
local and routing envelopes. The statement is uniform over every reachable
history and remaining-credit value; an average or isolated-activation bound
would not suffice.

### Probabilistic variant

If a local rule fails with conditional probability at most `delta_v` per
activation uniformly over every certified adaptive history, the failure
probability is at most

```text
(C_0 + 1) * max_v delta_v
```

or the sharper sum over certified activation counts. It is negligible when
`C_0` is polynomial and the local failure bounds are negligible.

These are tested-graph response/failure statements. For the closed completion
experiment, add `chi_D`; under the coarse estimate the failure bound is

```text
(C_0 + 1) * max_v delta_v + chi_D.
```

Worst-case local credit rules yield strong closed productivity only for a
strong completion context with `chi_D=0`.

This again uses a first-failure stopping argument. Before the first failed
local certificate, every activation either answers or strictly decreases
credit, so there are at most `C_0+1` candidate failure slots. Conditional
history-uniform bounds can therefore be summed without independence; behavior
after a failure cannot create extra slots in this estimate.

### Why the credit is not another timeout

The meter may terminate an uncertified execution with `Exhaust`. The credit
certificate proves that a certified execution reaches a visible response
*before* either credit or meter is exhausted. Credit is therefore a progress
invariant used in a proof, not an observation silently replacing divergence
by an error.

## 7. The efficient-construction witness

Let the abstract constructive statement be

```text
R --pi--> S
```

with the tuple of interface simulators written collectively as `sigma`. An efficient witness
in input mode `M` consists of:

1. codes/advice admitted by the declared input mode, or fixed generators
   compiled to fixed templates, with polynomial grades for `pi` and every
   component of `sigma`;
2. tariffed access contracts for every abstract specification oracle;
3. a fixed context-relative ambient policy discipline, an admitted
   completion-context class `C` carrying both context-safety and
   context-progress certificates, and an ownership assignment for protocol,
   simulator, context, and shared infrastructure meters;
4. route-safe canonical structural plumbing, with every intentionally
   bandwidth-, latency-, or memory-limited communication mechanism represented
   as an explicit resource node;
5. the ordinary erased construction inequalities

   ```text
   d(erase(pi R), erase(S sigma)) <= epsilon;
   ```

6. overwhelming tested-side no-exhaustion for both closed experiments

   ```text
   D[pi R]          and          D[S sigma]
   ```

   for every fixed `D in C`, uniformly over the inputs allowed by `M`,
   together with `D`'s context-safety bound and any shared-infrastructure
   bound in each experiment; `delta_D` dominates the sum of the three owner
   classes across both experiments, as required by the two coupling terms in
   the metering triangle inequality;
7. productivity on the declared responsive domain of `S`, either established
   directly for both sides or transferred from `S` using the construction
   error, the no-exhaustion coupling, and the completion contexts'
   progress-failure bounds;
8. explicit polynomial profile transformers for absorbing `pi`, `sigma`,
   and any parallel specification into a context.

Call this judgment

```text
EffConstruct_(M,C)(
  pi R, S sigma;
  T_pi, T_sigma, epsilon, delta, eta).
```

The construction error `epsilon`, two-sided exhaustion bound `delta`, and productivity
failure `eta` remain separate quantities in concrete statements. They may be
combined only by an explicit union or triangle bound.

For an information-theoretic theorem, `epsilon` may be a concrete statistical
bound. For a computational theorem, each fixed efficient context receives a
negligible bound after profile reindexing. The no-exhaustion and productivity
clauses are still required; neither follows merely because all codes carry
polynomial meters.

## 8. Closure of efficient witnesses

### Sequential composition

Suppose `W_1` constructs `S` from `R` and `W_2` constructs `T` from `S`.
Assume the profile transformer of `W_2` composed with that of `W_1` remains
within the selected grades, the context class of `W_1` is closed under
absorbing the fixed codes of `W_2` with a transported context-safety
certificate, public ownership labels are preserved, and the intermediate
responsive-domain contracts match. Then:

```text
epsilon_21 <= epsilon_1 + epsilon_2,
delta_21   <= delta_1 + delta_2,
eta_21     <= eta_1 + eta_2,
```

after applying the appropriate profile substitutions. The bounds are sums
because the composed bad event is contained in the union of the two stage bad
events. A fixed finite number of stages preserves negligibility immediately.
A parameter-dependent polynomial number does so only when one fixed uniform
stage/hybrid generator, one aggregate polynomial profile, and one uniform
negligible adjacent bound are supplied. An arbitrary indexed list of stage
descriptions is not covered.

### Parallel composition

For a fixed finite parallel family with independent named randomness, ledger
envelopes add in work, traffic, activations, and random bits and take the
chosen maximum/sum convention for space. Error, exhaustion, and productivity
failure bounds add by a union or hybrid bound. Shared randomness must be a
named common resource and invalidates the independent-product formula.

### Connection and feedback

Metered boundedness is closed under arbitrary finite connection. Efficient
witnesses are not. A connected witness must additionally provide one of:

- an acyclic aggregate certificate;
- a well-founded rank certificate;
- an affine-credit certificate such as Section 6;
- a proved polynomial traffic fixed point plus a progress rule.

This is the exact place where the algebra of bounded lower executions is
larger than the algebra of adequately efficient implementations.

## 9. Consequence for terminology

The paper uses the following discipline.

- **Metered implementation** means only syntactically bounded lower execution.
- **Adequately efficient implementation** means metered boundedness,
  overwhelming no-exhaustion, and productivity on its declared domain.
- **Efficient realization** additionally includes behavioral realization of
  the target.
- **Efficient construction witness** includes the real/ideal AC comparison,
  simulators, profile transformations, no-exhaustion, and productivity.

No result may call an implementation “efficient for a service” solely because
an external meter truncates its execution.
