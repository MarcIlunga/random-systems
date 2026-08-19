# Random-systems source contract

Status: primary-source contract for the behavior, attainment, and coupling
roadmaps. Verified against the original PDFs on 2026-07-20.

This document separates three things that must not be conflated:

1. what a source states;
2. what its proof actually uses; and
3. what Lean may prove as a separately advertised generalization.

Repository notes, OCR, extracted text, and implementation sketches are not
authorities for the mathematics. In particular,
[`THM231_ATTAINMENT.md`](THM231_ATTAINMENT.md) is a chronological
implementation/design log. Later dated entries can supersede earlier sketches.
Use it to locate code and failed approaches, never to freeze a theorem or
attribute an argument to a paper. The attainment and coupling receipts below
are grounded in the original thesis and Lanzenberger--Maurer PDFs.

## 1. Sources and pagination

| Short name | Original PDF | Pagination used below |
| --- | --- | --- |
| CR18 | Ueli Maurer, *Cryptography Foundations*, Spring 2018 | [`../CR18_LN.pdf`](../CR18_LN.pdf). Each landscape PDF leaf contains two printed pages: printed 57--58 = PDF leaf 35, 59--60 = 36, 63--64 = 38, 65--66 = 39, 67--68 = 40, 69--70 = 41, and 95--96 = 54. |
| Thesis | David Lanzenberger, *A Theory of Random Systems, Games, and Hardness Amplification*, 2023 | [`../thesis (1).pdf`](<../thesis (1).pdf>). Printed page = PDF leaf minus 10 in Chapter 2 and Appendix A: printed 13--16 = leaves 23--26, 20--23 = 30--33, and 87--88 = 97--98. |
| LanMau20 | David Lanzenberger and Ueli Maurer, *Coupling of Random Systems* | [`../LanMau20.pdf`](../LanMau20.pdf). Printed and PDF page numbers agree for the pages used here. |
| Maurer02 | Ueli Maurer, *Indistinguishability of Random Systems* | [`../Maurer02.pdf`](../Maurer02.pdf). Printed and PDF page numbers agree for the pages used here. |

The page references below are printed page numbers. PDF leaf numbers are
included above so that later checks do not silently use a different page.

## 2. Carrier vocabulary fixed by the sources

The word "distribution" does not have one mass convention across the sources.
The formalization must expose that distinction in the types or hypotheses.

| Layer | Source convention | Lean contract |
| --- | --- | --- |
| Arbitrary finite distribution | Thesis p. 15 before Definition 2.14 and LanMau20 pp. 10, 12 explicitly say that distributions need not have weight one unless stated. | `PFunPDS X Y` is finite nonnegative distribution/subdistribution machinery. One-sided `delta` may be used without normalization; symmetry and probability language may not. |
| Normalized probabilistic system | CR18 Definition 3.14, p. 64, is a random variable over DDSs in a finite probability experiment. Maurer02 Definition 3 and footnote 5, p. 6, require every conditional output distribution to sum to one. | `PFunPDS.Prob X Y` is the public representative layer for probability random systems. Public coupling lives here. |
| Random system | Thesis Definition 2.17 and Notation 2.19, p. 16, and LanMau20 Definition 10 and Notation 1, p. 14, use an observational equivalence class of PDSs. Maurer02 Definition 3, p. 6, uses the corresponding conditional-behavior object. | The eventual `RandomSystem X Y` is the behavioral quotient of `PFunPDS.Prob X Y`, at one fixed external signature `(X,Y)`. |

The arbitrary-weight layer is not an alternative public meaning of
"probability." It is required internally because successor distributions in
the attainment proof lose mass.

## 3. CR18: partial systems, observable bottom, and behavior

### Receipt CR18-A: a DDS is partial and prefix closed

**Source.** CR18 Definition 3.2, printed p. 57 (PDF leaf 35), defines an
`(X,Y)`-DDS as a partial function from nonempty input strings to `Y` whose
domain is prefix closed. The same definition calls a DDS finite when its
domain has a finite depth bound. It does not impose a common domain on two
different DDSs.

**Consequences used later.** Prefix closure prohibits a DDS from becoming
undefined on an input history and then becoming defined on an extension of
that same retained history.

**Lean delta.** `PFunDDS.DDS X Y` represents the source partial function and
validity condition. Statements over arbitrary ambient `X` or without a global
depth bound are generalizations and need their own finite-support argument;
they are not consequences of the word "finite" in CR18.

### Receipt CR18-B: `s⊥` skips rejected inputs

**Source.** CR18 Definition 3.3, printed p. 58 (PDF leaf 35), defines the fully
defined system denoted in the source by `s⊥` (spelled `s_bot` where an ASCII
identifier is needed). On a new query it evaluates the underlying partial DDS
after deleting earlier inputs,
starting at the first, that made the partial DDS undefined. It returns the
special symbol `⊥` precisely when the retained history followed by the new
query is undefined. The paragraph immediately before the definition explains
the intended semantics: an input outside the currently allowed domain is not
seen by the underlying system, so a later accepted input is answered as if the
rejected input had never been given.

**Observable transcript semantics.** CR18 Definitions 3.6--3.7, printed p. 60
(PDF leaf 36), define a deterministic environment as a total function on
histories over `Y ∪ {⊥}`, with either a next input or the stop symbol as
result. The transcript uses the fully defined `s⊥`. Thus:

- the rejected query remains visible in the transcript;
- its answer is visibly `⊥`;
- the environment sees that `⊥` and may continue; and
- only the history used internally by the DDS deletes the rejected query.

A system-side undefined reply does not itself stop the interaction. The
transcript stops when the environment emits its stop symbol.

**Lean delta.** The repository spells the extended output alphabet as
`Option Y`, with `none` representing CR18's `bot`. Its skip/kept-prefix
operation must agree with Definition 3.3. Any behavior/transcript theorem must
cover `none` histories and continuation after `none`; assuming
`TotalOnNonempty` is only a restricted intermediate theorem, not a CR18
hypothesis.

### Receipt CR18-C: PDSs and lack of a common-domain restriction

**Source.** CR18 Definition 3.14, printed p. 64 (PDF leaf 38), defines a PDS
as a random variable over a set of DDSs. Section 3.5 states that the notes work
in discrete probability theory with finite sample spaces. Definition 3.14 does
not require the sampled DDSs to share one partial domain. Definition 3.16 and
the paragraph following it define a probabilistic environment and the random
transcript by independently sampling system and environment.

**Lean delta.** The CR18-facing theorem must not inherit the thesis's
common-domain or compatible-environment hypotheses. Explicit `Option Y` and
`s_bot` semantics make all environment interactions defined at the resource
view, while retaining partiality as an observable event.

### Receipt CR18-D: conditional and cumulative behavior

**Source statement.** CR18 Section 3.6, printed pp. 65--70 (PDF leaves
39--41), presents behavior as the complete observable input/output behavior of
a probabilistic system.

- Printed p. 65 says that transcript distributions for every possible
  environment suffice to characterize complete observable behavior.
- Definition 3.18, printed p. 67, defines `b(S)` as the sequence of local
  conditional output distributions. A term is undefined when its conditioning
  event has probability zero; footnotes 14 and 16 spell out this partiality.
- Definition 3.19, printed p. 68, defines two PDSs to be equivalent when their
  behaviors are equal.
- Definition 3.20, printed p. 69, defines cumulative behavior as the
  conditional distribution of an entire output sequence for a fixed input
  sequence. Equation (3.2) gives cumulative behavior as the product of the
  local conditionals, and the following displayed quotient reconstructs a
  local conditional from cumulative behavior whenever the denominator is
  nonzero.

For partial functions, the channel discussion on printed p. 65 explicitly
allows the sum of probabilities of defined outputs to be smaller than one.
Together with Definition 3.3, the missing mass is the observable `⊥` branch.

**Proof status.** CR18 does not package the two directions as one numbered
iff theorem.

- Behavior determines transcript laws by the factorization in Lemma 3.2,
  printed p. 70. The notes explicitly say, immediately before the lemma, that
  its proof is omitted.
- The reverse characterization is given by the complete-observable-behavior
  statement on p. 65 and the cumulative reconstruction on p. 69, rather than
  by a separately numbered proof.
- The later use on printed p. 96 (PDF leaf 54) recalls Definition 3.19 and
  states explicitly that equivalent systems behave identically in every
  environment, meaning that they generate the same transcript distribution.

**Lean theorem, separated from the source presentation.** The intended
repository endpoint is a theorem with the semantic shape

```text
behavior equality
  iff
equality of transcript distributions in every deterministic environment
```

on normalized PDS laws with CR18's explicit `Option Y`/skip semantics. Lean
must supply both the omitted factorization proof and the reconstruction proof,
including:

- `none` as an observable answer;
- deletion of rejected inputs only from the DDS's retained history;
- continuation of the environment after `none`;
- zero-probability conditional histories; and
- the zero-query law needed to expose total mass.

These are proof obligations created by the explicit Lean representation, not
extra assumptions to add to CR18's equivalence definition. The frozen public
name is `behavior_equivalent_iff_transcript_equivalent`: it is lowercase and
states the semantic content. A restricted total-system lemma must have a name
that makes the restriction visible and must not occupy the public
source-facing name.

## 4. Thesis: transcript equivalence and its proof

### Receipt TH-A: finite common-domain PDSs and compatible environments

**Source.** Thesis Definition 2.9, printed p. 13, defines a finite DDS using a
finite input alphabet and a bounded-depth prefix-closed domain. Definitions
2.11--2.12, printed p. 14, define a DDE as a partial function `Y* -> X` and
require it to be compatible with the DDS: it may not query outside the DDS
domain. If the DDE is undefined, it stops; this presentation has no observable
`bot` reply.

Definition 2.14, printed p. 15, defines a PDS as a distribution over DDSs all
having the same domain, and again assumes a finite input alphabet and bounded
depth. The paragraph immediately before the definition explicitly says that
these distributions need not sum to one unless stated.

**Lean delta.** This is a strict specialization of the CR18-facing carrier.
The common-domain/compatible-environment theorem should be recoverable from
the general `Option Y` theorem, but it must not be used to erase CR18's
undefined-answer cases.

### Receipt TH-B: equivalence by transcript laws

**Source statement.** Thesis Definition 2.17, printed p. 16 (PDF leaf 26),
defines two same-domain PDSs `S` and `T` to be equivalent exactly when
`tr(S,e) = tr(T,e)` for every compatible deterministic DDE `e`. The paragraph
above the definition says that probabilistic environments induce the same
equivalence relation.

Lemma 2.18 on the same page states an iff: for same-domain PDSs, it suffices to
test all compatible non-adaptive deterministic DDEs. Footnote 6 defines
non-adaptive to mean that the query at a round depends only on the round
number, not on previous answers. The paragraph following Lemma 2.18 says that
the resulting equivalence class describes exactly a Maurer02 random system,
whose alternative presentation is a sequence of conditional distributions.

**Proof status.** Appendix A.1, printed pp. 87--88 (PDF leaves 97--98), gives
a complete proof, under the heading "Proof (of Theorem 2.18)" even though the
main-text result is labeled Lemma 2.18. The nontrivial direction is proved by
contrapositive. From an adaptive environment and one transcript on which the
two laws differ, the proof builds a non-adaptive deterministic environment
that asks exactly that transcript's input sequence. For the selected
transcript, the system-side event depends only on those fixed inputs and
outputs, so its mass is unchanged.

**Lean delta.** The source proof directly supports the finite,
same-domain/compatible specialization. Extending it to CR18 partial systems
requires a new proof that also fixes the locations of observable `none`
answers and respects skip semantics. Removing ambient `Fintype X` is a genuine
Lean generalization and must be justified from finite law support or finitely
many observable query patterns.

### Relationship between CR18 and the thesis

The behavior/transcript characterization is present in both developments,
but in different forms:

- CR18 starts from conditional behavior and includes partial DDSs, `s⊥`,
  observable `⊥`, and unrestricted environments.
- The thesis starts from transcript-law equivalence, proves that fixed-query
  deterministic environments suffice, and identifies the quotient with
  Maurer02's conditional behavior, under common-domain compatibility.

The Lean theorem reconciles these source presentations. It is not a new
definition dictated by Abstract Cryptography.

## 5. Lanzenberger--Maurer and the thesis: attainment

### Receipt LM-A: arbitrary weights are intentional

**Source.** LanMau20 p. 10 explicitly states that distributions are not
assumed to have weight one unless stated and says this is important because
Theorem 1 relies on arbitrary-weight distributions. Its Definition 3 on the
same page defines a one-sided statistical distance; the following paragraph
notes that it is not symmetric when weights differ. Thesis p. 15 makes the
same arbitrary-weight convention.

LanMau20 Definition 8, p. 13, and thesis Definition 2.14, p. 15, impose common
DDS domain, finite input alphabet, and bounded depth. LanMau20 Definition 10,
p. 14, and thesis Definition 2.17, p. 16, use equality of transcript laws in
every compatible DDE as equivalence.

### Receipt LM-B: class distance equals optimal transcript advantage and is attained

**Source statement.** LanMau20 Definitions 11--12 and Theorem 1, p. 15, and
thesis Definitions 2.26--2.28 and Theorem 2.31, printed p. 20, define:

- `Adv(S,T)` as the supremum of transcript statistical distance over
  compatible DDEs;
- class distance as the infimum of representative distance over `S`'s and
  `T`'s equivalence classes; and
- equality of those quantities, together with representatives at which the
  infimum is attained.

Both statements require the two random systems to have the same domain.

**Proof status and hypotheses actually used.** The proof is present in
LanMau20 pp. 15--18 and thesis printed pp. 20--23.

1. The single-query case uses LanMau20 Lemma 6, p. 16 (thesis Lemma 2.33,
   printed p. 21), which constructs joint distributions for finite families
   whose left marginals all have one common weight and whose right marginals
   all have another common weight. The lemma itself is arbitrary-weight and
   is proved in full.
2. The general case introduces successor systems on LanMau20 pp. 16--17 and
   thesis printed p. 21. Both sources stress that even when the original PDS
   is a probability distribution, a successor normally is not: its weight is
   the probability mass of the selected first answer.
3. The proof inducts on the maximal number of answered queries. It decomposes
   advantage by first query and answer, invokes the induction hypothesis on
   successor systems, prepends the first branch, sums disjoint answer
   branches, and uses Lemma 6/Lemma 2.33 to join the first-query marginals.
4. LanMau20 p. 18 and thesis printed p. 23 verify that the constructed
   representatives remain in the original equivalence classes, completing
   attainment.

Thus normalization must not be inserted into the recursive successor lemmas.
It belongs only at the public random-system boundary.

### Receipt LM-C: the varying-domain `s_bot` extension is false

The common-domain hypothesis in Theorem 1/Theorem 2.31 is mathematically
substantive. It cannot be removed merely because CR18's `s_bot` makes every
interaction total. The following normalized, finite, two-query example is a
counterexample to

```text
class distance = optimal transcript advantage
```

on the unrestricted varying-domain `PFunPDS` carrier.

Let `X = {a,b}` and `Y = {0}`. Consider four prefix-closed DDSs, all of which
have no defined history of length two:

- `s_ab` answers either `a` or `b` with `0` and then self-destructs;
- `s_a` answers only `a`;
- `s_b` answers only `b`; and
- `s_empty` answers neither query.

Set

```text
S = (1/2) s_ab + (1/2) s_empty,
T = (1/2) s_a  + (1/2) s_b.
```

For any environment whose first query is `a`, the mass-`1/2` pair
`(s_ab,s_a)` has identical transcripts: both answer `a` with `0` and then
answer `bot` forever. Only the remaining mass `1/2` can differ. The argument
is symmetric when the first query is `b`, and an environment that initially
stops has distance zero. Hence every transcript distance is at most `1/2`.
The environment that asks `a` and, only after receiving `bot`, asks `b`
attains `1/2`. Therefore

```text
optimal transcript advantage(S,T) = 1/2.
```

Transcript equivalence nevertheless fixes the complete distribution of the
four root answer patterns. This is not an assumption; the masses are recovered
by concrete transcript events. For an arbitrary representative `R`, write
`p_empty`, `p_a`, `p_b`, and `p_ab` for the masses of atoms whose defined
first-query sets are respectively `empty`, `{a}`, `{b}`, and `{a,b}`. Then:

```text
weight(R) = the mass of the fuel-0 transcript;

p_empty = Pr_R[(a,bot),(b,bot)]
          under "ask a; after bot ask b";

p_b     = Pr_R[(a,bot),(b,0)]
          under the same environment;

p_a     = Pr_R[(b,bot),(a,0)]
          under "ask b; after bot ask a";

p_ab    = weight(R) - p_empty - p_a - p_b.
```

The environments stop after a defined first answer. Rejected queries are
skipped internally exactly as in CR18 Definition 3.3, so the displayed events
measure the stated root patterns. Thus every `S'` transcript-equivalent to
`S` has pattern law

```text
(p_empty,p_a,p_b,p_ab) = (1/2,0,0,1/2),
```

whereas every `T'` transcript-equivalent to `T` has pattern law

```text
(p_empty,p_a,p_b,p_ab) = (0,1/2,1/2,0).
```

These two pushforward distributions are disjoint. Statistical-distance data
processing under the root-pattern map and the weight upper bound therefore
give, for every such pair of representatives,

```text
1 = delta(pattern(S'),pattern(T')) <= delta(S',T') <= weight(S') = 1.
```

Consequently the class distance is `1`, not `1/2`, and no representatives
attain the transcript advantage. A construction that stratifies by the full
root `bot`-pattern necessarily preserves this obstruction; finite
stabilization of that construction can stabilize at `1` and therefore cannot
close the attainment proof.

**Lean theorem and generalization boundary.** The source-facing endpoints
should be named semantically and in lowercase, for example:

- `class_distance_eq_optimal_advantage`;
- `exists_equivalent_representatives_with_distance_eq_optimal_advantage`.

The first implementation must follow the actual finite source boundary:

- one common DDS domain for both equivalence classes;
- a finite first-query family (source-exactly, a finite input alphabet); and
- one finite bound `q` on the maximal number of answered queries.

At that boundary the proof is induction on `q`; it is not a stabilization
proof. Same-domain removes the counterexample above, but same-domain alone
does not make the induction terminate for an unbounded `PFunDDS`. Conversely,
bounded fuel does not repair varying domains.

An arbitrary-`X` theorem is a separately advertised strengthening. It may
replace the source's finite maximum only after proving a finite realized
first-query family, or a finite range together with an attained maximizing
query, at every induction node. An unbounded-depth theorem likewise requires
a new proof. In particular, showing that each fuel-indexed `valueSet n` is
finite does not imply global finite stabilization: the finite set changes
with `n`, and its repeated truncated-difference closure can have an infinite
union. Even a separate stabilization theorem would not overcome the
varying-domain counterexample, which already stabilizes at the wrong value.

There must therefore be no unrestricted varying-domain endpoint with either
of the lowercase names above. A CR18-facing behavioral quotient may remain
more general, but the source theorem applies only to its common-domain,
bounded-query specialization unless and until a different valid metric
theorem is proved.

## 6. Coupling: probability theorem and equal-mass internal bridge

### Receipt C-A: the classical coupling lemma is probability-level

**Source.** LanMau20 Lemma 4, p. 11, and thesis Lemma 2.8, printed p. 13,
start with two probability distributions over the same set. They state both
the lower bound for every coupling and existence of a coupling whose
off-diagonal probability equals statistical distance.

### Receipt C-B: coupling of random systems

**Source statement.** LanMau20 Theorem 2, p. 15, and thesis Theorem 2.32,
printed p. 20, state that representatives can be chosen with a joint
distribution such that

```text
optimal distinguishing advantage = probability that the representatives differ.
```

Both sources call this an immediate consequence of attainment and the
classical coupling lemma. Neither supplies a separate proof of Theorem 2 /
Theorem 2.32. The coupling-theorem sentence does not repeat "same domain,"
but the immediately preceding attainment theorem does, and the cited coupling
lemma requires both marginals to live on the same carrier.

**Mass discipline forced by the cited proof.** The surrounding distribution
machinery is arbitrary-weight, but the cited coupling lemma explicitly assumes
probability distributions and the theorem's conclusion uses probability
notation. Moreover, the two marginals of any one joint distribution
necessarily have the same total mass. Therefore the Lean contract is:

- the public random-system coupling theorem is stated for normalized
  representatives;
- an internal subdistribution coupling theorem may be generalized to equal
  total mass, with off-diagonal *weight* rather than unqualified probability;
  and
- there is no unconditional coupling theorem for arbitrary pairs of
  subdistributions. Unequal-mass marginals make such a joint impossible.

This is the source-valid reconciliation of arbitrary-weight successors with
probability-level public coupling. It does not label the arbitrary-weight
attainment proof erroneous.

**Lean realization.** The coupling construction works over an arbitrary
ambient DDS carrier by using finite support rather than an ambient `Fintype`
instance. The final normalized theorem is
`exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded`;
its arguments expose both the probability layer and the source attainment
boundary. Any equal-mass internal bridge remains explicitly weight-level.

## 7. Maurer02: normalization of the public behavior object

**Source.** Maurer02 Definition 3 and Figure 2, printed p. 6, define an
`(X,Y)`-random system as a sequence of conditional probability distributions.
Footnote 5 makes normalization explicit: for every input history and previous
output history, the conditional probabilities over the next output sum to
one. The preceding random-automaton presentation on the same page samples
internal randomness and initial state from a probability distribution.
Footnote 6 records that cumulative output laws are products of the local
conditionals and that conditionals may be undefined on zero-probability
histories.

**Contract.** Maurer02 is the normalization anchor for the public random
system object. The thesis/LanMau transcript quotient identifies its normalized
equivalence classes with this conditional-behavior object. Arbitrary-weight
PDSs remain proof machinery below that boundary.

**Lean delta.** A finite-support normalized PDS is one presentation of a
Maurer02 behavior, not the behavior's identity. The behavioral quotient must
forget interaction-invisible correlations while preserving normalized
transcript laws.

## 8. Frozen theorem matrix

| Deliverable | Source theorem | Source hypotheses | Proof status | Lean-only strengthening |
| --- | --- | --- | --- | --- |
| Behavior determines transcript laws | CR18 Lemma 3.2, p. 70 | PDS and independent PDE; CR18 partial DDS/resource semantics | Proof explicitly omitted | Supply proof for explicit `Option Y` and skip semantics. |
| Transcript laws characterize behavior | CR18 Section 3.6, pp. 65--70; thesis Definition 2.17/Lemma 2.18 and following paragraph, p. 16 | CR18: partial DDSs; thesis: finite, same-domain PDSs and compatible DDEs | CR18 presents it across prose/definitions; thesis Appendix A.1 proves the non-adaptive reduction | One general CR18 theorem without `TotalOnNonempty`, plus a thesis specialization. |
| Class distance equals advantage | LanMau20 Theorem 1, p. 15; thesis Theorem 2.31, p. 20 | Finite first-query family, bounded answered-query depth, common-domain random systems; arbitrary-weight internal PDSs | Full proof: LanMau20 pp. 15--18; thesis pp. 20--23 | Arbitrary `X` only via a proved finite realized-query reduction. Varying-domain `s_bot` systems are explicitly excluded: Receipt LM-C is a normalized finite counterexample. |
| Attained representatives | Same theorem | Same | Same full proof | Separate lowercase semantic existence theorem on the same common-domain, bounded-query boundary. Unbounded depth needs a new proof. |
| Optimal coupling of distributions | LanMau20 Lemma 4, p. 11; thesis Lemma 2.8, p. 13 | Probability distributions on one carrier | Cited classical lemma | Equal-weight subdistribution bridge may be proved separately. |
| Coupling of random systems | LanMau20 Theorem 2, p. 15; thesis Theorem 2.32, p. 20 | Probability-level representatives; same random-system signature/domain | Immediate corollary stated; no separate proof | Arbitrary carrier via finite support; never unequal-mass marginals. |

## 9. Downstream Abstract Cryptography boundary

The downstream requirements are recorded in
[`LIBRARY_GUIDE.md`](../../../abstract-crypto/LIBRARY_GUIDE.md), especially
"Modeling invariants" and "Instantiating AC with a concrete carrier." They are
instantiation receipts, not hypotheses of the random-systems theorems above.

The serial AC instance must consume:

1. a fixed-signature resource carrier `RandomSystem X Y`, not a heterogeneous
   sigma carrier with identity behavior on signature mismatch;
2. the behavioral quotient, so source behavioral equivalence becomes Lean
   equality and converter application descends through it;
3. a converter action/trace quotient with exact lowercase semantic unit and
   composition laws; raw protocol functions retain off-tree junk and do not
   form the required monoid;
4. a resource carrier closed under every advertised converter, so the
   `MulAction` is genuinely total--quotienting a partial operation does not
   make it total; and
5. the normalized distinguishing metric and its converter non-expansion
   theorem, with any representative-distance characterization supplied only
   by an RS theorem whose common-domain and bounded-query hypotheses the
   instance actually satisfies.

The import direction is one way:

```text
RandomSystems mathematics
        -> fixed-signature quotient/action/metric receipts
        -> RandomSystemsCC instance
        -> AbstractCrypto consumers
```

Abstract Cryptography must not alter the definition of behavior, strengthen
attainment hypotheses, normalize successor subdistributions, or turn typed
parallel composition into a homogeneous operation by hiding signature
changes. Serial fixed-signature instantiation comes first. Parallel
composition remains a separate typed/router theorem and a later optional AC
instance.

In particular, AC must not force the false varying-domain
representative-distance theorem from Receipt LM-C. If the chosen CR18
resource carrier includes all varying-domain `s_bot` laws, its operational
distinguishing metric remains available, but Theorem 2.31 cannot be used to
identify that metric with the infimum of raw representative `delta`. The AC
instance must either use the source-valid common-domain specialization or
consume the operational quotient metric directly.

## 10. Stop conditions for implementation

Revise a statement before proving it if any of the following occurs:

- a theorem uses probability language but its type exposes arbitrary mass;
- a proposed joint distribution has marginals of unequal total weight;
- a CR18 theorem needs `TotalOnNonempty` rather than handling observable
  `none`;
- a thesis theorem is cited after removing common-domain, compatibility, or
  finiteness assumptions without a separate generalization proof;
- class distance is identified with transcript advantage on unrestricted
  varying-domain `s_bot` systems (Receipt LM-C is a counterexample);
- per-fuel finiteness of `valueSet n` is treated as one uniform finite range
  or as a proof of global stabilization;
- a theorem is attributed to CR18 coupling rather than LanMau20/the thesis;
- a chronological implementation note is used as primary-source evidence;
- an uppercase or opaque identifier replaces a lowercase semantic theorem
  name; or
- an AC typeclass requirement is fed back into the RS mathematical theorem.
