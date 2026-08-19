# Common self-answering normalization

Status: DERIVED

This note isolates the theory used to remove pointless queries.  It is a
transcript-law normalization argument, not an H-coefficient argument.

## 1. Setting

Let `E` be a class of environments and let `E0` be a distinguished subclass.
For two systems `S` and `T`, write

    P e := the transcript law of S against e
    Q e := the transcript law of T against e.

Suppose every `e : E` has a normalized environment `norm e : E0`.  The
normalized run may have a different transcript carrier because omitted answers
are no longer recorded.  Assume there is a reconstruction function `R e`, the
same function for both endpoints, such that

    P e = pushforward (R e) (P (norm e))
    Q e = pushforward (R e) (Q (norm e)).

The word "same" is the essential hypothesis.  Endpoint-specific
reconstructions would not give a data-processing comparison between the two
original laws.

## 2. Carrier-independent theorem

For every environment `e`, data processing gives

    distance (P e) (Q e)
      <= distance (P (norm e)) (Q (norm e)).

Taking the supremum over `e` gives

    unrestricted advantage <= restricted advantage.

The reverse inequality is only set inclusion: every restricted environment is
also an unrestricted one.  Hence the two advantages are equal.

This theorem knows nothing about transcripts.  `P` and `Q` may be arbitrary
families of distributions, their normalized carrier may differ from their
original carrier, and `R e` may depend on `e`.  Its entire probabilistic content
is a common pushforward factorization.

## 3. Self-answering environments as a producer

A query is erasable after history `h` when both endpoints satisfy two facts:

1. its answer is the same deterministic value `det h x`; and
2. answering it has no hidden effect on the state used by later queries.

Given these facts, `norm e` answers the query locally and does not send it to
the system.  Reconstruction replays the omitted query-answer pairs into the
short transcript.  The existing `SelfAnswerFilter.consume`, `advance`, and
`reconstruct` construction supplies exactly this map.

The proof obligation for that construction is therefore not a bespoke
statistical-distance estimate.  It is the pair of law equalities in Section 1.
Once those equalities are exposed, the carrier-independent theorem performs the
whole distance argument.

The monotonicity condition on the pointless-query predicate is operational: an
answer inserted locally must not invalidate the decision to erase queries while
replaying the transcript.  It is not part of the abstract factorization theorem.

## 4. Consistent function oracles

For a static function oracle `f : X -> Y`, repeated input `x` after a previous
pair `(x, f x)` is erasable.  Its answer is read from the history, and evaluating
the same static function has no state effect.  Thus the generic self-answering
construction yields the common factorization whenever both endpoint functions
agree with the history-determined answer on erased queries.

PRFs and random functions are instances.  A permutation oracle is also an
instance on its forward interface; a two-sided permutation interface additionally
permits inverse queries determined by a prior forward answer and conversely.

## 5. HCTR2 composition

Let

    X := HCTR2 with a random permutation
    Y := the plus/minus random intermediate system
    Z := the tweakable random permutation endpoint.

The coherent endpoint pair `X,Z` admits common self-answering normalization.
The intermediate `Y` does not satisfy the same two-sided coherence, so no
normalization claim is made for `X,Y` or `Y,Z` separately.  The composition is

    Adv_all(X,Z)
      = Adv_no_pointless(X,Z)
      <= Adv_no_pointless(X,Y) + Adv_no_pointless(Y,Z).

Consequently the H argument remains explicitly restricted to no-pointless
environments.  Normalization is applied once, outside the hybrid triangle.  In
particular, this refactor must not turn the paper's restricted H obligation into
an unrestricted one.

## 6. Dependency DAG and reuse ledger

    common pushforward factorization
      -> data processing for one environment
      -> supremum bound
      -> reverse bound by subset inclusion
      -> equality of unrestricted and restricted advantage
      -> generic self-answering producer
      -> static-function consistency corollary
      -> HCTR2 coherent-endpoint instance

Reuse/adaptation ledger:

| node | source | action |
|---|---|---|
| pushforward data processing | `Dist.δ_fTransform_le` | reuse |
| supremum monotonicity | existing `sSup`/advantage infrastructure | reuse |
| transcript reconstruction | `SelfAnswerFilter.reconstruct` | adapt |
| reconstruction law equalities | current proof inside `statDist_le_filteredAdv_of_selfAnswer` | extract |
| function-oracle determinism | current `functionEvaluator` reconstruction lemmas | adapt |
| HCTR2 endpoint coherence | current `bit_pointless_wlog` assumptions | reuse |

Rejected route: H technique.  It is downstream of this theorem and would hide
the common-factorization invariant inside a transcript-specific game proof.

## 7. Lean receipt target

The finished surface should make the layers visible in theorem names:

1. a theorem about arbitrary distribution families and a common pushforward;
2. a theorem saying `SelfAnswerFilter` produces that factorization;
3. a corollary for consistent function evaluators;
4. an HCTR2 theorem that normalizes only the coherent endpoints before applying
   the restricted hybrid bound.

