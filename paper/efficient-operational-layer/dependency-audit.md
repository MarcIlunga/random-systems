# Theorem-dependency and noncircularity audit

## 1. Purpose

The lower stack contains several forgetful maps and two different closure
claims.  This audit checks that no result is justified by a theorem that
already presupposes the result, and that optional adequacy or implementation
premises are not smuggled into the total bounded algebra.

The two closure claims are:

- **bounded operational closure:** every finite metered graph has a lower
  meaning, possibly ending in strict nonresponse through exhaustion;
- **adequate efficient closure:** selected compositions additionally return
  the advertised behavior with negligible or zero exhaustion.

Only the second needs DAG, rank, credit, or solved-flow certificates.

## 2. Dependency spine

| Stage | Inputs used | Result produced | Inputs deliberately not used |
|---|---|---|---|
| D1. Deterministic core | finite typed graph, one token, fixed machine tapes, deterministic routing | one maximal small-step run | probability, grades, asymptotics |
| D2. Macro collapse | D1, first-visible-output convention | partial state transition and prefix-closed DDS | time or space bound |
| D3. Machine probability | D2, named Bernoulli product tapes, countable encodings | measurable law on partial DDSs | oracle implementability |
| D4. Exact cost | D1, bit-costful output/router conventions | unique vector ledger for each finite prefix | polynomial grades |
| D5. Metering | D4, external non-observable finite quotas and the high-water check vector `Need(rho)` | success/block/exhaust semantics, monotonicity, stabilization above `Need` (above the final ledger in the machine-only/exact-reservation case) | productivity |
| D6. Oracle steps | standard-Borel kernel, selected sampler, pre-funded reserve evaluator, strong semantic reservation plus post-sample evaluator/commit envelope, D4-D5 | admitted kernel without selection, finite terminal kernel | efficient hidden kernel implementation |
| D7. Finite operational quotients | D5-D6, graph normalization, all finite closing contexts | costed and behavioral system algebras and erasure `U` | target random-system feedback |
| D8. Route safety | D4, component and oracle aggregate grades | dominating canonical-router envelope | no-exhaustion of arbitrary explicit links |
| D9. Partial random systems | D2-D3, standard-Borel partial DDSs, maximal strict transcripts | strict connection, order invariance, quotient congruence | metered cost reports |
| D10. Operational bridge | D7-D9, finite-cylinder context compilation | pointwise full abstraction and injective homomorphism `J` | uniform implementation of every abstract environment |
| D11. Uniform families | fixed unary-parameter template, or proved generated-to-fixed compiler with route/staging and fixed oracle-accounting faces, polynomial aggregate grades | uniform efficient implementation class | `J` surjectivity |
| D12. Reductions | D7-D8, exact graph absorption, polynomial profile transformers, D6 tariffs, fixed graded terminal scorers | budget-reindexed nonexpansion and asymptotic closure | free arbitrary measurable scoring; same-profile nonexpansion without domination |
| D13. Adequacy | D5, owner labels, completion-context safety, local flow/credit certificates | no-exhaustion, productivity, metered/unmetered coupling | bounded closure as a substitute for response |
| D14. Efficient construction witness | D10-D13, chosen uniformity mode | lower evidence attached to the ordinary AC construction | UC roles or quantifiers |
| D15. Selected explicit resources | D4-D5, D8, native transition locality, named tapes, private single-token interfaces | transactional `PROC/STORE/COIN` refinement, native ledger projection, `SLINK` edge refinement | target carrier, UC, shared-resource scheduling, visible clocks |

Every arrow points downward in this table.  In particular:

1. the finite contextual algebra `D7` is complete before `J`;
2. route safety `D8` uses exact upper bounds, not target semantics;
3. target connection congruence `D9` is proved on DDS laws, not inferred from
   operational graph syntax;
4. full abstraction `D10` uses both directions explicitly;
5. computational closure `D12` uses the coded test class, not pointwise
   full abstraction to admit arbitrary environments;
6. adequacy `D13` is not used to make bad graphs disappear from `D7`;
7. explicit refinement `D15` is proved by a small-step stuttering invariant
   and does not use the random-system embedding `J`.

## 3. The route-safety dependency

There are three distinct objects:

```text
unrestricted physical matching,
route-safe canonical matching,
explicit limited-link resource.
```

The unrestricted matching belongs to the general finite operational algebra.
It may exhaust and therefore has no homomorphism to cost-free strict DDS
connection.

The route-safe matching receives a derived envelope

```text
RouteEnvelope =
  fixed polynomial(
    aggregate nonrouter machine work,
    specification call count,
    specification traffic).
```

The derivation depends only on grades and fixed bit-machine constants.  Its
proof precedes and does not use `J`.  Once it is known never to exhaust, the
token/expansion correspondence establishes `J`.

An explicit limited link is a node.  Its own machine/specification behavior
is mapped by `J`; route safety applies only to the structural plumbing around
it.  Thus the bridge does not assume reliable communication where a theorem
intends to study unreliable communication.

## 4. Oracle dependency

The oracle results separate four questions.

1. **Law:** a measurable kernel defines the abstract response distribution.
2. **Pathwise coupling:** a selected measurable randomization and named seed
   sequence permit fixed-sample proofs.
3. **Bounded access:** a pre-funded deterministic reserve evaluator and a
   public combined semantic/post-sample administrative reservation make one
   admitted call fit for every selected seed and preserve the kernel without
   response selection.
4. **Implementation:** a finite machine realizes the hidden kernel.

Only 1-3 are premises of the oracle-relative algebra. Item 4 is never
inferred. The reserve evaluator runs and may be rejected before a fresh seed
is consumed; after admission, every response-dependent evaluator and commit
action is already funded and total, so it cannot create a selection branch.
The lifetime DDS map uses the selected seeds from item 2; the finite
terminal-kernel theorem uses items 1-3 and finite quotas. The route-safe
envelope uses only the public aggregate call/traffic bounds, never the
oracle's hidden work.

For unbounded response support, the bounded atomic contract is not invoked.
The one-shot object is a reference kernel; the admitted implementation uses a
bounded streaming interface plus a metered reassembler.  Its coupling loss
contains every chunk, traffic, work, output, and space failure.

## 5. Uniformity dependency

The primary uniform object is one fixed code receiving `1^kappa`.  It does
not depend on the generated-network theorem.

The secondary presentation requires, in order:

1. one fixed generator;
2. one self-delimiting graph language with fixed libraries and boundary;
3. a polynomial code-length bound;
4. a polynomial *aggregate* native profile;
5. the fixed decoder/interpreter theorem.

When fixed stateful oracle dependencies are present, item 5 includes the
selected private accounting proxy. Ordinary replies need not reveal the next
public contract coordinate used by the access meter, so the proxy mirrors the
authenticated exact commit receipt into the virtual ledger while hiding it
from decoded code. The simulated action bound includes component/router work,
activations, and oracle calls. The proxy is a fixed administrative face to an
already declared occurrence, not a generated specification.
The occurrence is either private to the compiled subsystem or every
intentional outside caller is mediated by one fixed charged multi-client
proxy; otherwise an outside commit could invalidate the cached public
coordinate used by the virtual reservation.

Per-node polynomial grades alone do not imply item 4.  The compiler creates
implementation nodes only and therefore cannot be used to justify a
parameter-dependent family of independent specification oracles.

Pointwise cylinder compilation in the proof of `J` is not a uniformity
result.  Its finite lookup code may depend on the fixed parameter, target
environment, and cylinder.  Asymptotic computational security still uses one
fixed uniform code and fixed polynomial policy.

Likewise, the pointwise quotient's arbitrary measurable terminal observers do
not enter the efficient class.  An efficient test contains one fixed uniform
terminal-scorer code; reading and processing its finite terminal record is
charged in the test profile, and a fixed default handles scorer
block/exhaust.  A cost-aware public-report projection is fixed and effective,
with its evaluation and output length certified; terminal-record length is
transformed during absorption.  This prevents the pointwise observer or
report map from becoming noncomputable advice.

## 6. Reduction dependency

Exact absorption is a graph identity:

```text
D[alpha R]  and  D[alpha][R]
```

have the same final normalized nodes, ownership labels, meters, specification
occurrences, seed names, and route-safe aggregate.  Probability is applied
only after this equality.

The profile inequality is separate:

```text
Profile(D[alpha]) <= T_alpha(Profile(D)).
```

Therefore the correct nonexpansion statement is reindexed:

```text
d_P(alpha R,alpha S)
  <= d_(T_alpha(P))(R,S).
```

Same-profile nonexpansion needs an additional proof
`T_alpha(P)<=P`.  Asymptotic closure then uses fixed-code quantifiers,
polynomial substitution, and—in a parameter-dependent hybrid argument—one
fixed uniform hybrid generator plus one uniform negligible adjacent bound.

## 7. Adequacy dependency

Owner labels prevent a context from turning its own exhaustion into a
resource failure.  For each completion context:

```text
Pr[Exh_all]
  <= Pr[Exh_tested]
     + Pr[Exh_context]
     + Pr[Exh_shared].
```

The context and shared terms are supplied by the completion-context contract.
The tested term is established by a local constructor certificate.

For productivity the completion contract has a second, independent field:
conditional context progress.  No-exhaustion alone does not stop a context
from blocking or stopping silently.  The progress field says that a context
whose tested side obeys the response envelope reaches its designated
decision, up to its own stated failure bound.

- The elementary DAG rule requires response-independent child query lengths
  and call counts plus response bounds computed in reverse topological order.
- The response-adaptive DAG rule instead requires one supplied polynomial
  cumulative-response invariant per vertex and a proved post-fixed-point
  inequality.  A first-crossing argument establishes the invariant before the
  same reverse/forward passes are used.
- The affine-credit rule requires local activations already to terminate
  without block/exhaust; credit controls hidden composition, not local
  correctness.

No-exhaustion does not imply productivity, and productivity does not imply
behavioral realization.  All three remain separate fields of
`EffConstruct`.

For a real/ideal construction comparison, the witness supplies these
owner-specific exhaustion bounds in both closed experiments. Its metering
loss `delta_C` dominates their sum, because the triangle inequality uses one
metered/unmetered coupling per side. The separate `eta_C` field dominates the
sum of both closed-productivity failures after each includes the completion
context's own `chi_C`.

## 8. Explicit-resource dependency

The selected explicit translation depends on the native machine and meter,
not conversely.  Its key invariant is checked only at transaction boundaries:
`STORE` equals the native configuration, `COIN` equals the named tape/head,
and committed resource tokens equal the native ledger.  Processor, coin, and
store reservations all precede an infallible commit sequence, so a rejected
native joint charge has no committed explicit native coordinate.

Private control messages follow a padded eight-phase schedule.  A
well-founded lexicographic rank in phase suffix and remaining admitted
scan/copy microsteps supplies local progress, and the route envelope funds
every private copy. Thus administrative erasure and native cost projection
are established before any appeal to behavioral quotienting or `J`.
Probability enters only after the pathwise statement, by assigning `COIN` the
same named tape law.

The full explicit ledger is intentionally larger: it retains program storage,
resource counters, transaction work, private traffic, and scratch.  Exactness
is only under `pi_native`; this prevents the result from being used
circularly as a claim that reification itself has no cost.

For a generated network, D11's compiler must run before D15.  It produces one
fixed universal implementation and physical profile; D15 then translates that
single occurrence.  Applying D15 nodewise first would create
parameter-dependent specification-resource occurrences, contradicting the
compiler's implementation-only premise.  The two orders are not silently
identified.

## 9. Residual leaves

The following leaves are not dependencies of any theorem advertised as
complete:

- comparison with an external carrier using different nonresponse or
  feedback;
- automated discovery of the polynomial post-fixed points used by the proved
  response-adaptive DAG rule;
- application-specific streaming APIs beyond the proved geometric-string
  instance and generic coupling;
- explicit APIs beyond the selected transition-token processor,
  native-configuration store, named coin tape, and sequential lossless link,
  including RAM, sharing, reset, leakage, erasure, and visible clocks;
- genuine concurrency;
- literal universal-machine transition tables and mechanization.

Their absence therefore narrows scope but creates no circular proof gap in
the selected lower AC instantiation.
