# The finite costed operational algebra

## 1. Scope

This note proves the algebraic result that can be obtained before solving the
independent measure-level random-system feedback problem.

Fix:

- a security parameter and ambient workload `(kappa,b)`;
- a finite effective signature library;
- the component-machine and canonical-router semantics;
- evaluated finite grades for every implementation occurrence;
- tariffed standard-Borel specification kernels satisfying the pre-sample
  reservation rule;
- a measurable, isomorphism-invariant public report map into a
  standard-Borel report space.

At these fixed parameters, every closed finite metered experiment has a
well-defined terminal law.  The quotient by all finite operational contexts
forms a costed system algebra.  Forgetting reports and identifying `Block`
with `Exhaust` gives a homomorphism to a behavioral operational algebra.

The primitive ledger contains both each occurrence's local peak and a scalar
`gpeak`, updated at every small-step configuration to
`max_t sum_v live_v(t)` including active canonical-routing buffers.  The
latter is not derivable from the tuple of local peaks when different
occurrences attain their maxima at different times.  Alpha-isomorphism
preserves `gpeak` because it only permutes the summands.

The unrestricted theorem does **not** identify an underfunded physical
matching with cost-free abstract feedback.  The route-safe subalgebra and its
standard-Borel partial-random-system embedding are proved separately in
`partial-random-system-bridge.md`; comparison with a differently chosen
external carrier remains a carrier-specific question.

## 2. Raw open graphs

### 2.1 Typed boundary

A port occurrence is

```text
(occurrence-name, signature, polarity)
```

with polarity in `{client,provider}`.  A boundary `B` is a finite set of
distinct port occurrences.  When an object has several roles—such as the
inner and outer sides of a converter or the hole and external side of a
context—`B` is partitioned into named boundary faces.  A typed renaming is a
bijection preserving signature and the polarity after transport to the common
orientation of the two faces.

An open graph with boundary `B` consists of:

1. a finite set of implementation occurrences, each carrying fixed code,
   initial state convention, named random tape, grade, and a public ownership
   class used only for cost-layer failure attribution;
2. a finite set of admitted specification occurrences, each carrying a named
   kernel and tariff contract;
3. all node-port occurrences;
4. a partial matching of equal-signature opposite-polarity ports;
5. the unmatched port occurrences, identified with `B`.

Fanout, delay, copying, multiplexing, scheduling, and physical links are
nodes.  They are never properties of an edge.

### 2.2 Alpha-isomorphism

An alpha-isomorphism is a bijection on internal node, port, tape, state, and
edge occurrence names that:

- fixes the external boundary labels;
- preserves node code/specification identity, grades, public ownership
  classes, signatures, polarity, and incidence;
- transports the exact ledger coordinates and the named product probability
  space.

Raw graphs are considered modulo alpha-isomorphism.  The public report map
must satisfy

```text
report(phi_* ell) = report(ell)
```

for every alpha-isomorphism `phi`, after the canonical permutation of hidden
ledger coordinates.  A report may retain coordinates carrying public party,
wire, or oracle labels, but it may not expose an arbitrary fresh internal
name.

## 3. Bare aliases and graph normalization

A bare alias contains no code, state, meter, or physical behavior.  It is a
typed bijection between two finite *administrative boundary faces*.  The
polarity on a converter's inner face is first transported to the common
interface orientation, so an alias always preserves signature and normalized
polarity.  An alias is not an arbitrary equality between node ports and cannot
encode fanout.

A graph presentation may contain a finite chain of such boundary-face
bijections created by renaming, plugging, or identity syntax.  Normalization:

1. composes every maximal alias chain as an ordinary typed bijection;
2. substitutes the resulting boundary names in node-port incidences and
   physical matchings;
3. removes the intermediate alias records and any boundary face hidden by a
   plug;
4. rejects a presentation if substitution creates a type/polarity mismatch,
   a non-bijective boundary map, or two physical matchings at one linear node
   port;
5. retains every explicit physical node;
6. assigns every remaining ordinary physical edge the administrative
   occurrence name determined by its ordered endpoint pair and charges one
   canonical routing operation on that edge.

**Lemma 3.1 (termination).** Rewriting one bare alias at a time terminates.

**Proof.** Every rewrite removes one alias occurrence and creates none.

**Lemma 3.2 (confluence).** Every legal rewrite order gives alpha-isomorphic
normal forms.

**Proof.** Function composition is associative.  Thus every order computes
the same composite typed bijection on each maximal alias chain.  The remaining
nodes and nonalias incidences are unchanged.  Intermediate names chosen while
performing substitutions differ only by alpha-renaming.

Consequently, normalization is a function into graph isomorphism classes.
The identity converter is the identity boundary-face bijection.  Attaching it
performs only name substitution: it has no transition and introduces no
second edge charge.  A charged wire must be an explicit link/resource node or
ordinary physical matching, not an alias.

## 4. Fixed-sample and probabilistic execution

### 4.1 Fixed sample

Fix:

- every implementation random tape;
- one infinite sequence of independent uniform seeds for every admitted
  specification occurrence.

The one-token small-step relation is deterministic.  The external meter checks
the next exact ledger before an action.  A closed activation terminates in

```text
Ok(tau,o,r)
  | Stop(Block,v,tau,o,r)
  | Stop(Exhaust,v,tau,o,r),
```

where `tau` is the complete finite visible transcript, `o` is the closing
test's designated finite observation of its own terminal state (including its
ordinary decision when one is produced), and `r=report(ell)` for the lifetime
ledger at that point.  The label `v` records an alpha-invariant public owner
class for the blocking/exhausting occurrence (tested subsystem, context, or
declared shared infrastructure), not its fresh internal name.  The projection
producing `o` is part of the test and cannot inspect hidden state of the tested
graph. `Stop` is terminal for the closed experiment. Retaining `tau`, `o`, and
the cost-layer ownership label is essential for attribution; behavioral
erasure below hides both stop reason and owner.

Each primitive charged action has one declared owner, so crossing several
local coordinates on that action has an unambiguous label.  If a selected
hardware model adds global caps whose rejecting meters have different public
owners, it must also fix an alpha-invariant priority order for simultaneous
rejection.  This makes the terminal result a function rather than a
set-valued tie and is observable at the cost layer.

For a canonical routing action, “checks the next exact ledger” begins with one
whole-message reservation computed from the validated self-delimiting header.
It covers the complete copy-work, edge-traffic, and destination-buffer
envelope. Rejection commits none of those coordinates. Admission grants a
linear capability under which the bit-costful copy proceeds in deterministic
small steps and cannot later exhaust; those steps and their intermediate
buffers still update the exact ledger and `gpeak`. Receiver activation is the
next, separately owned primitive check. This convention is what makes the
canonical router and the selected `SLINK` exact-ledger refinements of one
another.

A finite positive work quota makes the component/router part terminate.
Before an oracle is sampled, a finite call/traffic reservation either rejects
terminally or admits one kernel sample.  Thus a fixed closed lifetime quota
prevents an infinite sequence of admitted calls.

### 4.2 Probability kernel

Machine tapes carry the named product Bernoulli measure unless shared
randomness is an explicit common node.  A specification node has a
standard-Borel state, countable sets of finite query and response codes, a
measurable kernel, and a measurable reservation envelope depending only on
the public query and effectively encoded countable contract parameters, not
on hidden state or a fresh sample.  The envelope dominates the call,
serialization, and tariff
coordinates of every outcome in the selected randomization's range at every
reachable hidden state compatible with the public contract coordinate.

For pathwise language, choose once for each named kernel `K` a measurable
randomization

```text
sample_K : State_K x Query_K x [0,1] -> State_K x Response_K
```

whose pushforward of Lebesgue measure in the final coordinate is `K(s,q)`.
Kallenberg's kernel-randomization lemma supplies such a map
(*Foundations of Modern Probability*, 2nd ed., Lemma 3.22).  The `j`th
admitted call of a specification occurrence consumes its `j`th named seed.
Consequently “fixing every oracle sample” means fixing these seed sequences;
it does not assume that a state-dependent kernel came with a pre-existing
pathwise coupling.  Different choices of `sample_K` induce the same terminal
law, although not necessarily the same cross-experiment coupling.

On the measurable admission set, compose the oracle kernel with the
commit-and-deliver map.  On its complement use the Dirac kernel at
`Stop(Exhaust,v,tau,o,r)` for the rejecting meter's public owner `v`, current
transcript `tau`, and current
designated test observation `o`.  Machine transitions use deterministic
kernels.  Rejection neither changes the oracle state nor advances its named
seed index.  Hence admission does not condition the kernel on a response that
was sampled and discarded.  The sum
of the finite evaluated work and call quotas bounds the number of
nonterminal component, router, and oracle steps.  Iterating the corresponding
measurable kernels up to that bound and making terminal states absorbing
therefore gives a unique terminal law for every closed metered experiment.

This establishes the oracle-extended finite carrier under the displayed
kernel/tariff hypotheses; it is not merely a machine-only claim.

### Lemma 4.1 (finite terminal kernel)

For every closed normalized graph at fixed `(kappa,b)`, the map from its
encoded public input and initial specification state to

```text
Prob(
  Ok(Transcript,Observation,Report)
  + StopReason x Owner x Transcript x Observation x Report
)
```

is a Markov kernel.

**Proof.** The implementation part of a configuration is countable.  A finite
product of the admitted standard-Borel specification states and the named
seed spaces is standard Borel, as are finite transcripts, ledgers, and
reports.  A machine/router step is a measurable map because it is a
piecewise function on countably many encoded control cases.  An admitted
oracle step is the measurable kernel of Section 4.2; a rejected step is a
Dirac kernel.  Let `N` be the sum of all evaluated work, activation, routing,
and oracle-call quotas plus one terminal check per occurrence.  Every
nonterminal step decreases at least one of those remaining natural
coordinates, so no execution has more than `N` nonterminal steps.  Make
terminal configurations absorbing and compose the step kernel exactly `N+1`
times.  Pushforward by the measurable terminal observation map gives the
displayed kernel.  Uniqueness follows because the small-step kernel and
finite composition are fixed.

## 5. Contexts and observations

### 5.1 One-hole graph contexts

A graph context `C[-]` is a finite open graph with one distinguished typed
hole boundary.  Plugging a graph with the matching boundary means:

1. alpha-rename internal occurrences apart;
2. take disjoint union;
3. connect corresponding hole endpoints;
4. hide the hole boundary;
5. normalize.

Plugging never reassigns public ownership classes.  In particular, absorbing
a converter into a distinguisher for a reduction preserves its original
accountability label even though the same raw graph is now viewed as test
syntax.  Otherwise the cost-aware experiment equality would fail merely by
rebracketing.

Composition of contexts is plugging one context into the hole of another.
Associativity follows from equality of the final node union and matching,
followed by Lemma 3.2.

### 5.2 Cost-aware closing tests

A cost-aware closing test is a context whose remaining boundary is closed and
whose supervisor applies a total measurable `{0,1}`-valued decision kernel to

```text
Ok(tau,o,r), Stop(Block,v,tau,o,r), Stop(Exhaust,v,tau,o,r).
```

The supervisor is semantic observation, not an ordinary wire component.  It
can distinguish both terminal statuses and the selected public report.
Quantifying over every such measurable supervisor is appropriate for this
pointwise information-theoretic quotient: it is equivalent to comparing the
complete terminal outcome laws.  It is not, by itself, a computational test
definition.  In the uniform efficient class the supervisor is replaced by a
fixed graded scorer program whose input processing and report computation are
charged, with a fixed default bit if the scorer itself stops.

A behavioral closing test factors through

```text
erase(Ok(tau,o,r))          = Visible(tau,o),
erase(Stop(Block,v,tau,o,r))  = NoResponse(tau,o),
erase(Stop(Exhaust,v,tau,o,r))= NoResponse(tau,o).
```

`NoResponse(tau,o)` is the maximal finite-transcript/test-observation outcome
used by this finite operational quotient.  It retains everything already
visible to the closing test and says only that no next response occurs.  It is
not a visible wire symbol and cannot be fed back to a program.  This convention
prevents a “total decision rule” from accidentally turning exhaustion into an
ordinary error response.

## 6. The two contextual quotients

For graphs `G,H` with the same boundary, define

```text
G ~=cost H
```

when every compatible finite cost-aware closing test has the same decision
law on `G` and `H`.  Define

```text
G ~=beh H
```

analogously using behavioral tests.

### Lemma 6.1

Both relations are equivalence relations and are invariant under
alpha-isomorphism.

**Proof.** Equality of decision laws is reflexive, symmetric, and transitive.
Alpha-isomorphic closed graphs have a measure-preserving bijection of tapes
and named oracle-seed sequences.  Using the same selected randomization for
corresponding kernel identities transports kernel states, traces, ledgers, and
terminal results; report invariance finishes the cost-aware case.

### Lemma 6.2 (context congruence)

If `G ~=cost H`, then `C[G] ~=cost C[H]` for every compatible context `C`.
The analogous statement holds for `~=beh`.

**Proof.** For every closing test `D[-]` of `C[G]`, context composition
`D[C[-]]` is a closing test of `G`.  Apply contextual equivalence.  The
behavioral case is closed because the composite observation still factors
through erasure.

Define

```text
R_cost(kappa,b;B) = Graph(kappa,b;B) / ~=cost,
R_beh (kappa,b;B) = Graph(kappa,b;B) / ~=beh.
```

## 7. Operations

On raw normalized graphs define:

```text
rho(G)               typed boundary renaming,
G tensor H           alpha-disjoint union and normalization,
connect_{p,q}(G)     add one legal matching edge, hide p,q, normalize,
alpha @ G            tensor with converter alpha, connect inner ports,
I_A                   bare alias at interface A,
0                     empty graph.
```

Lemma 6.2 makes each operation well-defined on both quotients: every operation
is itself a graph context in each argument after the other arguments are
fixed.

### Theorem 7.1 (finite operational system algebra)

For every fixed `(kappa,b)`, the costed and behavioral quotients satisfy:

**Renaming**

```text
id(G) = G,
(rho_2 o rho_1)(G) = rho_2(rho_1(G)).
```

**Symmetric parallel monoid**

```text
(G tensor H) tensor K = G tensor (H tensor K),
G tensor H             = swap(H tensor G),
G tensor 0             = G.
```

**Connection order**

For any legal endpoint-disjoint final matching `E`, every order of adding the
edges of `E` yields the same quotient element.  In particular,

```text
connect_e(connect_f(G)) = connect_f(connect_e(G)).
```

**Converter action**

```text
I_A @ G                    = G,
(alpha ; beta) @ G         = beta @ (alpha @ G),
(alpha tensor beta) @
  (G tensor H)             =
  (alpha @ G) tensor (beta @ H).
```

The orientation of `;` is fixed by the second equation: `alpha` is the inner
converter and `beta` the outer converter.

**Proof.** Renaming is composition of typed bijections.  Parallel terms have
the same alpha-disjoint node union and matching.  The empty graph contributes
nothing.  Every connection order constructs the same final matching.  Every
converter equation constructs the same union of component nodes and final
matching after bare-alias normalization.  Lemma 3.2 identifies the normal
forms.  The proof includes final matchings containing cycles; it establishes
bounded operational meaning, not progress before exhaustion.

The theorem is an equality theorem in the contextual quotients, not merely a
collection of informal graph pictures.

## 8. Erasure homomorphism

Every behavioral test is a cost-aware test whose decision kernel ignores the
report and identifies the two stop reasons.  Therefore

```text
G ~=cost H  =>  G ~=beh H.
```

Define

```text
U_B : R_cost(kappa,b;B) -> R_beh(kappa,b;B),
U_B([G]_cost) = [G]_beh.
```

### Theorem 8.1

`U` is well-defined and preserves all operations:

```text
U(rho G)                 = rho U(G),
U(G tensor H)            = U(G) tensor U(H),
U(connect_{p,q} G)       = connect_{p,q} U(G),
U(alpha @ G)             = U(alpha) @ U(G),
U(I_A)                   = I_A.
```

**Proof.** Well-definedness is the implication above.  Erasure changes only
the observation of terminal results; it does not change nodes, matching,
renaming, normalization, or plugging.  Thus both sides of each equation have
the same raw normalized graph and differ only by when the quotient map is
applied.  `U` is understood on converter boundaries as the same family of
quotient maps.

## 9. Cost-aware pseudometrics and profile reindexing

Let `C_P(B)` be a specified class of uniform cost-aware closing tests for
boundary `B` and profile `P`.  Define

```text
d_P^cost(G,H)
  = sup_{D in C_P(B)}
      |Pr[D[G]=1] - Pr[D[H]=1]|.
```

When `C_P(B)` is called computational, its terminal scorer is one fixed
uniform effective code and the scorer's work, space, and input length are
included in `P`.  Its projection of its own terminal configuration to `o` and
its public-report projection are likewise fixed effective codes (or canonical
projections onto declared accessible context/ledger coordinates), each with
certified output length and evaluation cost.  `P` contains a bound on the
whole terminal record, so an absorbed converter cannot enlarge an observation
or report for free.  An arbitrary measurable outcome, terminal-state, or
report map is admitted only in the unrestricted pointwise quotient of
Section 6.
The value presented to the scorer is frozen from the interaction ledger
before report/scorer execution.  Their work is charged for test admissibility
but is not recursively included in the input they are computing.

### Lemma 9.1

`d_P^cost` is a pseudometric.

**Proof.** Reflexivity and symmetry hold for each test.  For every `D`,

```text
|p_D(G)-p_D(K)|
 <= |p_D(G)-p_D(H)| + |p_D(H)-p_D(K)|.
```

Taking the supremum and bounding the supremum of a sum by the sum of
suprema gives the triangle inequality.

Let a graded converter `alpha` have a profile transformer `T_alpha` with the
following exact closure property:

```text
D in C_P(alpha @ B)
  => D[alpha @ -] in C_{T_alpha(P)}(B).
```

The transformed test contains the same codes, random-tape names, oracle calls,
meters, and normalized graph as the original closed experiment.

### Theorem 9.2 (profile-reindexed nonexpansion)

```text
d_P^cost(alpha @ G, alpha @ H)
  <= d_{T_alpha(P)}^cost(G,H).
```

**Proof.** For every left-hand test `D`, absorb `alpha` into the hole.  The
two experiments are pathwise the same normalized graph, so their advantages
are equal.  The absorbed test belongs to the transformed class by premise.
Taking the supremum proves the inequality.

Same-profile nonexpansion is a corollary only when
`T_alpha(P) <= P` in the chosen profile order.  It is not claimed in general.

## 10. Relation to efficient construction

The algebra above proves that every well-typed finite wiring has a bounded
lower meaning: a feedback loop can terminate in `Exhaust`.  The subclass of
adequately efficient realizations is smaller.  To call a quotient element an
efficient implementation of a responsive specification, a witness must also
establish:

- overwhelming or stronger no-exhaustion;
- productivity on the declared responsive domain;
- behavioral realization after `U`;
- polynomial profile transformers for every constructor and simulator.

Those semantic side conditions are not automatically closed under arbitrary
connection.  Acyclicity, rank, affine credit, or another progress certificate
is required.

## 11. Route-safe bridge and intentionally limited links

The full quotient above permits an arbitrarily underfunded canonical router.
Erasure remains a homomorphism between the two *operational* quotients because
both retain the same physical graph.  It would be incorrect, however, to map
such a structural connection to cost-free strict DDS feedback: the physical
router could create a new exhausted branch.

`partial-random-system-bridge.md` resolves this by selecting the route-safe
subalgebra.  The canonical router receives a derived aggregate envelope that
dominates every routed machine/specification event.  It remains fully charged
in the exact ledger but cannot be the first exhausted occurrence.  A
bandwidth-limited or otherwise fallible link is represented as an explicit
resource node, not hidden in structural plumbing.

The route-safe costed and behavioral relations are formed using route-safe
graphs and route-safe closing contexts.  They are not obtained by simply
taking a subset of the finer unrestricted contextual quotient: an
underfunded structural-router test could distinguish target-equal behaviors
by hidden implementation cost.

For the route-safe behavioral quotient it proves

```text
J_B : R_beh^rs(kappa,b;B) -> RS_partial(B),
```

where `RS_partial` is the standard-Borel carrier of probability laws on
partial DDSs modulo maximal strict-transcript equivalence.  Environment
lifting proves connection congruence, finite transcript-cylinder compilation
proves pointwise full abstraction, and the token/expansion bisimulation proves
that `J` is an injective system-algebra homomorphism.  Consequently

```text
R_cost^rs --U--> R_beh^rs --J--> RS_partial
```

is the advertised lower realization.

What remains conditional is only comparison with another independently
mandated random-system carrier that chooses a different observation for
nonresponse or a different feedback convention.  The finite common-domain
PDS carrier embeds exactly in `RS_partial`.
