# SoP/XoP via LM20 and Additive Orbits

This note records the current proof direction for the sum/XOR of two
independent permutations.  It is written for peer review, not as a final paper
section.  The goal is to isolate the part of the argument that is exact and
finite-\(N\), and to separate it from later orbit enumeration or asymptotic
estimates.

The main point is this:

> The tight transcript-level distinguishing advantage is exactly an orbit-mass
> discrepancy.  The orbit partition is induced by coordinate permutations and
> affine transformations of the output group.  LM20 explains this as an optimal
> coupling between representatives that first choose an additive orbit and then
> sample uniformly inside it.

This is not a small-\(q\) argument.  Small-\(q\) values are useful for testing,
but the proof below is stated for arbitrary \(q\).

## Setting and notation

Let \(G = \mathbb F_2^n\), written additively, and let

\[
  N = |G|.
\]

Fix \(q\) distinct input points \(x_1,\ldots,x_q\).  The real system is

\[
  F(x) = P_1(x) + P_2(x),
\]

where \(P_1,P_2\) are independent uniform random permutations of \(G\).  The
ideal system is a uniform random function \(U : G \to G\).

For the fixed input tuple, write the visible output tuple as

\[
  Y = (Y_1,\ldots,Y_q) \in G^q.
\]

For \(y \in G^q\), define the compatible hidden-state count

\[
  C(y)
  =
  \#\{a \in G^q :
      a_1,\ldots,a_q \text{ are distinct and }
      a_1+y_1,\ldots,a_q+y_q \text{ are distinct}\}.
\]

This is the same object currently formalized in Lean as
`SoP.compatibleCountNat y`, reusing the existing XoP combinatorics layer.

## The exact transcript law

The first exact statement is the fixed-input transcript formula.

**Lemma 1.** For every \(y \in G^q\),

\[
  \Pr[F(x_i)=y_i \text{ for all } i]
  =
  \frac{C(y)}{((N)_q)^2},
\]

where

\[
  (N)_q = N(N-1)\cdots(N-q+1).
\]

For the ideal system,

\[
  \Pr[U(x_i)=y_i \text{ for all } i] = \frac{1}{N^q}.
\]

**Proof.** Since the inputs \(x_1,\ldots,x_q\) are distinct, the tuple

\[
  A = (P_1(x_1),\ldots,P_1(x_q))
\]

is uniform over injective \(q\)-tuples in \(G\).  The same is true independently
for

\[
  B = (P_2(x_1),\ldots,P_2(x_q)).
\]

Thus the pair \((A,B)\) is uniform over a set of size \(((N)_q)^2\).

The event \(A+B=y\) is equivalent to \(B=A+y\), coordinatewise.  Therefore the
number of pairs \((A,B)\) producing the visible output \(y\) is exactly the
number of injective tuples \(a\) such that \(a+y\) is also injective.  This is
\(C(y)\).  Dividing by the total number \(((N)_q)^2\) gives the real transcript
law.

For the ideal system, the outputs at distinct inputs are independent uniform
elements of \(G\), so every \(y \in G^q\) has probability \(N^{-q}\).  \(\square\)

Consequently the fixed-input statistical distance is

\[
  \Delta_q
  =
  \sum_{y \in G^q}
    \left(
      \frac{C(y)}{((N)_q)^2} - \frac{1}{N^q}
    \right)_+ .
\]

Equivalently,

\[
  \Delta_q
  =
  \frac12
  \sum_{y \in G^q}
    \left|
      \frac{C(y)}{((N)_q)^2} - \frac{1}{N^q}
    \right|.
\]

Here \((r)_+ = \max(r,0)\).  This is the same convention as the repository's
`statDist`: the positive part, equal to half the \(\ell_1\) distance.

## From fixed inputs to adaptive \(q\)-query advantage

The fixed-input formula is the whole transcript law needed for the usual
\(q\)-query distinguishing advantage.  The reason is not a hybrid argument; it
is an input-symmetry reduction.

Consider a deterministic adaptive distinguisher making at most \(q\) queries.
Randomized distinguishers are mixtures of deterministic ones, so it is enough
to discuss deterministic distinguishers.  Repeated queries can be removed from
the analysis: both the real and ideal systems answer repeats consistently, so a
repeat only reveals a value the distinguisher already knows.

After removing repeats, suppose the distinguisher has made \(k\) fresh queries.
The actual names of the \(k\) queried inputs do not affect the law of the next
fresh answer.  In the ideal system this is immediate from the definition of a
uniform random function.  In the real system it follows because, for any
distinct input tuple \(x_1,\ldots,x_k\),

\[
  (P_1(x_1),\ldots,P_1(x_k))
\]

is uniform over injective \(k\)-tuples, and the same holds independently for
\(P_2\).  This law depends only on \(k\), not on the input names.

Thus every deterministic adaptive strategy induces the same output-sequence law
as some fixed sequence of \(q\) distinct inputs, followed by a deterministic
post-processing map that decides when to stop, which fresh input name to choose
next, and what bit to output.  Statistical distance cannot increase under
deterministic post-processing.  Conversely, a fixed-input test is a valid
nonadaptive distinguisher.  Therefore the optimal adaptive \(q\)-query
advantage is the same \(\Delta_q\) computed above.

This is the point where the fixed transcript calculation becomes a
random-system statement.  In the Lean development, this is the bridge that
should connect the SoP transcript law to the already formalized adaptive PDS
equivalence layer.

## Invariance of the compatible count

The next step is to understand how much information \(C(y)\) really depends on.
It is not an arbitrary function on \(G^q\).  It is constant on affine-coordinate
orbits.

Let \(S_q\) act on \(G^q\) by permuting coordinates.  Let

\[
  \operatorname{Aff}(G) = GL(G) \ltimes G
\]

act diagonally on \(G^q\), where \(GL(G)\) means additive group automorphisms of
\(G\).  Since \(G=\mathbb F_2^n\), this is the usual affine group.

**Lemma 2.** The count \(C(y)\) is invariant under:

1. coordinate permutations,
2. global translations \(y_i \mapsto y_i+t\),
3. additive equivalences \(y_i \mapsto e(y_i)\), where \(e : G \simeq_+ G\).

Therefore \(C(y)\) is constant on the orbits of

\[
  S_q \times \operatorname{Aff}(G)
\]

acting on \(G^q\).

**Proof.**

For coordinate permutations, let \(\sigma \in S_q\).  The map

\[
  a \mapsto a \circ \sigma
\]

is a bijection between hidden tuples compatible with \(y\) and hidden tuples
compatible with \(y \circ \sigma\).  It preserves injectivity of \(a\) and of
\(a+y\), because it only reindexes coordinates.

For global translations, fix \(t \in G\).  The hidden tuple \(a\) is compatible
with \(y\) if and only if it is compatible with \(y+t\), because

\[
  a_i + (y_i+t) = (a_i+y_i)+t.
\]

Adding \(t\) to every shifted coordinate is a bijection of \(G\), so it preserves
injectivity.

For additive equivalences, fix \(e : G \simeq_+ G\).  The map

\[
  a \mapsto e(a)
\]

is a bijection from hidden tuples compatible with \(y\) to hidden tuples
compatible with \(e(y)\).  Injectivity of \(a\) is preserved because \(e\) is
bijective.  Also,

\[
  e(a_i) + e(y_i) = e(a_i+y_i),
\]

so injectivity of \(a+y\) is equivalent to injectivity of \(e(a)+e(y)\).

These three bijections generate invariance under
\(S_q \times \operatorname{Aff}(G)\).  \(\square\)

The translation, additive-equivalence, and coordinate-permutation parts are now
formalized in the SoP Lean files.  The packaged theorem is
`visibleStatDist_eq_classifierStatDist_of_affineCoordOrbitClassifier`: once a
classifier is exactly the affine-coordinate orbit classifier, the visible
statistical distance collapses to the classifier-level statistical distance.

## Exact orbit decomposition

Let \(\Omega_q\) be the finite set of
\(S_q \times \operatorname{Aff}(G)\)-orbits in \(G^q\).  For an orbit
\(\omega \in \Omega_q\), write:

\[
  |\omega| = \#\{y \in G^q : y \in \omega\},
\]

and define \(C_\omega\) to be the common value of \(C(y)\) on \(\omega\).
This is well-defined by Lemma 2.

Define the real and ideal masses of an orbit by

\[
  w_R(\omega)
  =
  |\omega| \cdot \frac{C_\omega}{((N)_q)^2},
\]

and

\[
  w_I(\omega)
  =
  |\omega| \cdot \frac{1}{N^q}.
\]

These are probability distributions on \(\Omega_q\): summing \(w_R\) over all
orbits gives \(1\), and summing \(w_I\) over all orbits gives \(1\).

**Theorem 3.** The fixed-input distinguishing advantage is exactly

\[
  \Delta_q
  =
  \sum_{\omega \in \Omega_q}
    \left(w_R(\omega)-w_I(\omega)\right)_+.
\]

Equivalently,

\[
  \Delta_q
  =
  \frac12
  \sum_{\omega \in \Omega_q}
    |w_R(\omega)-w_I(\omega)|.
\]

**Proof.** Start from the pointwise formula:

\[
  \Delta_q
  =
  \sum_{y \in G^q}
    \left(
      \frac{C(y)}{((N)_q)^2} - \frac{1}{N^q}
    \right)_+.
\]

Partition \(G^q\) by the orbits \(\omega \in \Omega_q\).  On a fixed orbit,
\(C(y)=C_\omega\), so the summand is constant:

\[
  \left(
    \frac{C(y)}{((N)_q)^2} - \frac{1}{N^q}
  \right)_+
  =
  \left(
    \frac{C_\omega}{((N)_q)^2} - \frac{1}{N^q}
  \right)_+.
\]

Therefore the contribution of the orbit \(\omega\) is

\[
  |\omega|
  \left(
    \frac{C_\omega}{((N)_q)^2} - \frac{1}{N^q}
  \right)_+
  =
  \left(
    |\omega|\frac{C_\omega}{((N)_q)^2}
    -
    |\omega|\frac{1}{N^q}
  \right)_+.
\]

This is

\[
  (w_R(\omega)-w_I(\omega))_+.
\]

Summing over all orbits proves the positive-part formula.  Since \(w_R\) and
\(w_I\) are both probability distributions, the positive part equals half the
\(\ell_1\) distance:

\[
  \sum_\omega (w_R(\omega)-w_I(\omega))_+
  =
  \frac12 \sum_\omega |w_R(\omega)-w_I(\omega)|.
\]

\(\square\)

This theorem is the concrete tight result shape.  It is finite-\(N\), exact, and
contains no asymptotic notation.  What remains computational is the enumeration
of the orbits and the calculation of the values \(C_\omega\).

## LM20 interpretation

The orbit formula has a direct LM20 reading.

For each orbit \(\omega\), let \(D_\omega\) be the uniform distribution on
visible transcript tuples \(y \in \omega\).  The real and ideal transcript laws
can be written as

\[
  R^\star = \sum_{\omega \in \Omega_q} w_R(\omega) D_\omega,
\]

and

\[
  I^\star = \sum_{\omega \in \Omega_q} w_I(\omega) D_\omega.
\]

This is not a new approximation.  It is just the real and ideal transcript
distributions rewritten using the orbit partition.  The reason it matters is
that the common conditional distributions \(D_\omega\) expose the optimal
coupling.

Couple \(R^\star\) and \(I^\star\) as follows:

1. First maximally couple the orbit labels \(\omega_R,\omega_I\) under
   \(w_R,w_I\).
2. If \(\omega_R=\omega_I=\omega\), sample one common \(y\) from \(D_\omega\)
   and use it for both systems.
3. If \(\omega_R\neq\omega_I\), sample independently from the corresponding
   orbit-conditionals.

The failure probability of this coupling is

\[
  \Pr[\omega_R \neq \omega_I]
  =
  \frac12 \sum_{\omega \in \Omega_q} |w_R(\omega)-w_I(\omega)|
  =
  \Delta_q.
\]

This is exactly the LM20 picture at the transcript level: choose representatives
whose only mismatch is the additive-orbit label.  The failure event is not a
hybrid-game failure event; it is the static event that the two representatives
select different orbit components.

For full deterministic-system representatives, one still needs an extension
lemma: a sampled visible transcript tuple must be lifted to a deterministic
function table in a way that preserves the required \(q\)-query observations.
The transcript-level coupling above is already enough to identify the exact
finite transcript distance; the full PDS lift is the formal bridge to the
LM20 equivalence-class statement.

## Relation to the spatial-reconstruction bound

The existing spatial-reconstruction line gives the explicit upper bound

\[
  B_q(N)
  =
  \binom q2
  \frac{(N)_q}{N^q (N-1)^2}.
\]

For \(q \ll \sqrt N\), this has leading term

\[
  B_q(N) \sim \frac{\binom q2}{N^2}
  =
  \frac{q(q-1)}{2N^2}.
\]

More precisely, if \(C=\binom q2\), then

\[
  \frac{(N)_q}{N^q}
  =
  1 - \frac{C}{N} + O_q(N^{-2}),
\]

and

\[
  \frac{1}{(1-1/N)^2}
  =
  1 + \frac{2}{N} + O(N^{-2}).
\]

Thus

\[
  B_q(N)
  =
  \frac{C}{N^2}
  -
  \frac{C(C-2)}{N^3}
  +
  O_q(N^{-4}).
\]

Equivalently,

\[
  B_q(N)
  =
  \frac{q(q-1)}{2N^2}
  -
  \frac{q(q-1)(q(q-1)-4)}{4N^3}
  +
  O_q(N^{-4}).
\]

This corrects a factor-of-two slip in the earlier informal expansion.  For
example:

- \(q=2\): \(C=1\), so \(B_2(N)=N^{-2}+N^{-3}+O(N^{-4})\), matching
  \(1/(N(N-1))\).
- \(q=3\): \(C=3\), so the \(N^{-3}\) coefficient is \(-3\).
- \(q=4\): \(C=6\), so the \(N^{-3}\) coefficient is \(-24\).

The orbit formula explains where the gap between \(B_q(N)\) and the exact
advantage can enter: it is hidden in the finer additive orbit structure of
\(G^q\).  Equality-patterns alone are not enough once affine dependencies among
the \(y_i\)'s matter.

## What is proved, what remains

The exact finite-\(N\) result currently supported by the argument is the orbit
sum:

\[
  \Delta_q
  =
  \sum_{\omega \in \Omega_q}
    \left(
      |\omega| \frac{C_\omega}{((N)_q)^2}
      -
      |\omega| \frac{1}{N^q}
    \right)_+.
\]

This is the right shape for a tight result.  It does not by itself give a closed
single rational function for every \(q\), because that requires orbit
enumeration and compatible-count formulas for each orbit.

The general formalization steps completed so far are:

1. `compatibleCountNat` is invariant under translations, additive equivalences,
   and coordinate permutations.
2. These invariances are packaged as affine-coordinate invariance.
3. The generic finite-partition theorem is proved:

   \[
     \text{if } C \text{ is constant on classifier fibers, then }
     \Delta = \sum_{\alpha} (w_R(\alpha)-w_I(\alpha))_+.
   \]

4. The theorem is instantiated with abstract affine-coordinate orbit
   classifiers.
5. The finite collision-event layer is formalized.  The Lean layer uses the
   indexed event family with one hidden and one shifted event for every query
   pair; if \(y_i=y_j\), the two indexed events impose the same equation, and
   inclusion-exclusion over indexed duplicate event sets is still valid.  This
   gives the first inclusion-exclusion theorem:

   \[
     C(y)
     =
     \sum_{T\subseteq \mathcal E}
       (-1)^{|T|}\,
       \#\{a : \text{all indexed events in }T\text{ occur}\}.
   \]

6. The indexed events are now equipped with oriented labels, an underlying
   undirected support relation, and its reflexive-transitive connectedness
   relation.  The connectedness relation is packaged as a finite quotient of
   coordinates by support components.
7. The nonempty solution fiber is formalized.  If a labelled subfamily has one
   solution, then all solutions are exactly that solution plus a
   component-constant offset, and component-constant offsets are exactly
   functions on the component quotient.  Consequently the formalized solution
   count is

   \[
     \#\{a : a \text{ satisfies }T\}=|G|^{\kappa(T)}
   \]

   whenever a base solution exists.
8. The inclusion-exclusion theorem has also been rewritten using semantic
   consistency:

   \[
     C(y)
     =
     \sum_{T\subseteq\mathcal E}
       (-1)^{|T|}
       \mathbf 1_{\operatorname{satisfiable}(T)}
       |G|^{\kappa(T)}.
   \]

   This is already the exact gain-graph shape, with semantic existence of a
   solution as the consistency predicate.
9. The explicit labelled-walk obstruction is now formalized in both directions.
   A subfamily has an oriented step relation carrying signed labels, a labelled
   reachability relation carrying accumulated walk labels, and a closed-walk
   consistency predicate.  The formalized equivalence is:

   \[
     \operatorname{satisfiable}(T)
     \;\Longleftrightarrow\;
     \text{every closed labelled walk in }T\text{ has accumulated label }0.
   \]

   The converse constructs a satisfying assignment by choosing one
   representative per connected component and assigning each vertex the negated
   label of a path from that representative.  The path-label uniqueness lemma
   under closed-walk consistency is also formalized.
10. The inclusion-exclusion theorem has been rewritten with the explicit
    closed-walk condition:

    \[
      C(y)
      =
      \sum_{T}
        (-1)^{|T|}
        \mathbf 1_{\operatorname{cycle\text{-}consistent}(T)}
        |G|^{\kappa(T)}.
    \]

    This is the Lean version of the gain-graph formula in Lemma 4, stated for
    the repository's indexed collision-event family.
11. The finite classifier/orbit-mass layer is now formalized.  The partition
    file names classifier fibers and classifier weights, proves that classifier
    weights are the pushforward masses, and packages the exact finite
    cardinality-times-compatible-count formula.  The affine file specializes
    this to any affine-coordinate orbit classifier:

    \[
      \Delta_q
      =
      \sum_{\omega\in\Omega}
        \left(
          w_R(\omega)-w_I(\omega)
        \right)_+.
    \]

    The affine file now also provides the representative-level rank handoff:
    `classifierCompatibleCountNat_eq_rankZero_add_rankOne_add_tail_of_affineCoordOrbitClassifier_mem`
    says that for any occupied orbit block and any representative transcript
    \(y\) in that block, the numerator \(C_\omega\) is exactly the
    rank-zero/rank-one/tail gain-graph expansion of \(C(y)\).

    Equivalently, using the fiber cardinality \(|\omega|\) and common
    compatible count \(C_\omega\),

    \[
      \Delta_q
      =
      \sum_{\omega\in\Omega}
        \left(
          |\omega|\frac{C_\omega}{((N)_q)^2}
          -
          |\omega|\frac1{N^q}
        \right)_+.
    \]
12. The fixed-input bridge back to the concrete XoP PDS is now formalized in
    `XoPModel`.  For every injective input sequence,

    \[
      \delta\bigl(
        \operatorname{tr}(\mathrm{XoP},x^q),
        \operatorname{tr}(\mathrm{URF},x^q)
      \bigr)
      =
      \Delta_q^{\mathrm{visible}}.
    \]

    This uses the existing transcript embedding for fixed inputs and the new
    SoP visible laws.  It proves that the orbit formula is not only a standalone
    visible-output calculation: it computes the fixed-input transcript distance
    of the concrete XoP-vs-URF PDS.
13. The restricted nonadaptive advantage over injective inputs is now exact:

    \[
      \operatorname{Adv}_{\mathrm{inj}}(\mathrm{XoP},\mathrm{URF})
      =
      \Delta_q^{\mathrm{visible}}.
    \]

    The proof uses \(q\le |G|\) to choose at least one injective input tuple,
    then observes that every injective input tuple has the same transcript
    distance by the fixed-input bridge.  Thus the restricted supremum is a
    supremum of a constant.
14. Combining the previous two items gives the current theorem-facing exact
    endpoint: for any affine-coordinate orbit classifier,

    \[
      \operatorname{Adv}_{\mathrm{inj}}(\mathrm{XoP},\mathrm{URF})
      =
      \delta\bigl(\kappa_\# R_{\mathrm{vis}},\kappa_\# I_{\mathrm{vis}}\bigr)
      =
      \sum_{\omega\in\Omega}
        \left(
          |\omega|\frac{C_\omega}{((N)_q)^2}
          -
          |\omega|\frac1{N^q}
        \right)_+.
    \]

    This is formalized in `SoP.Affine`, not `XoPModel`, to respect the existing
    import graph.  It is the exact restricted transcript/orbit statement that a
    later LM20 representative lift must realize as an honest coupling of PDS
    representatives.
15. The orbit-label coupling witness is now formalized.  For any
    affine-coordinate orbit classifier there exists a coupling \(C_\Omega\) of
    the real and ideal orbit-label distributions such that

    \[
      \operatorname{Adv}_{\mathrm{inj}}(\mathrm{XoP},\mathrm{URF})
      =
      \Pr_{C_\Omega}[\omega_R\ne\omega_I].
    \]

    The proof applies the repository's optimal coupling lemma to the classifier
    pushforwards.  This is the precise transcript/orbit-level LM20 coupling
    statement currently supported by the formalization.
16. The actual visible-transcript coupling witness is now formalized.  There is
    a coupling \(C_{\mathrm{vis}}\) of the real and ideal visible transcript
    laws such that

    \[
      \operatorname{Adv}_{\mathrm{inj}}(\mathrm{XoP},\mathrm{URF})
      =
      \Pr_{C_{\mathrm{vis}}}[Y_R\ne Y_I].
    \]

    Moreover, for any affine-coordinate orbit classifier \(\kappa\), the same
    theorem package records

    \[
      \Pr_{C_{\mathrm{vis}}}[Y_R\ne Y_I]
      =
      \delta\bigl(\kappa_\# R_{\mathrm{vis}},
                  \kappa_\# I_{\mathrm{vis}}\bigr).
    \]

    This is a stronger transcript-level bridge than the label-only coupling:
    it couples the actual output tuples while preserving the orbit-mass
    interpretation of the failure probability.  It is still deliberately below
    the full LM20 PDS-representative layer.
17. The exact orbit distance is now placed inside the unrestricted adaptive
    advantage chain as a formal lower bound:

    \[
      \Delta_q^{\mathrm{visible}}
      \le
      \operatorname{Adv}_{\mathrm{adapt}}(\mathrm{XoP},\mathrm{URF}).
    \]

    The proof uses a new generic lemma
    `advantageOn_le_advantage`, then the existing lemma
    `advantage_le_advantageAdaptive`.  This does not solve the adaptive
    reduction; it isolates the only missing inequality.  To get the final exact
    adaptive theorem, we still need the XoP-specific input-symmetry upper bound

    \[
      \operatorname{Adv}_{\mathrm{adapt}}(\mathrm{XoP},\mathrm{URF})
      \le
      \Delta_q^{\mathrm{visible}}.
    \]
18. The generic adaptive transcript decomposition is now formalized in
    `Equiv.lean`.  For any two PDSs \(S,T\) and any deterministic adaptive
    environment \(e\),

    \[
      \delta(\operatorname{tr}(S,e),\operatorname{tr}(T,e))
      =
      \sum_{t:\, e\text{ follows }t}
        \left(
          \operatorname{tr}(S,\operatorname{inputs}(t))(t)
          -
          \operatorname{tr}(T,\operatorname{inputs}(t))(t)
        \right)_+.
    \]

    This is the formal reduction of the adaptive upper bound to the
    XoP-specific input-symmetry problem.  It uses the existing deterministic
    fiber lemmas: an unfollowed transcript has zero adaptive mass under both
    systems, and a followed transcript has adaptive mass equal to the
    nonadaptive mass at the input sequence recorded by the transcript.
19. The repeat-consistency layer is now formalized.  A transcript is
    repeat-consistent if repeated input names always carry the same output.
    Any adaptive transcript produced by a stateless function oracle
    `DDS.ofFunq f` is repeat-consistent, and any PDS obtained by sampling such
    stateless function oracles assigns zero adaptive mass to
    repeat-inconsistent transcripts.  The concrete XoP real and ideal systems
    both instantiate this lemma:

    \[
      \Pr[\operatorname{tr}(\mathrm{XoP},e)=t]=0
      \quad\text{and}\quad
      \Pr[\operatorname{tr}(\mathrm{URF},e)=t]=0
    \]

    whenever \(t\) has the same input name with two different outputs.  This
    separates the repeat-query bookkeeping from the fresh-query orbit argument.
20. The fresh-position projection is now formalized.  A position is fresh if
    its input name has not appeared earlier in the transcript.  For every
    transcript \(t\), the map from fresh positions to input names is injective.
    Every position has an earlier-or-equal fresh representative with the same
    input name; if \(t\) is repeat-consistent, that representative also has the
    same output value.  In particular, the fresh-position count is bounded by
    both the query bound and the input-domain cardinality:

    \[
      |\operatorname{Fresh}(t)| \le q,
      \qquad
      |\operatorname{Fresh}(t)| \le |G|.
    \]

    This gives the canonical injective input tuple needed to invoke the SoP
    visible law on the fresh part of an adaptive transcript.
21. The fresh-position projection is now reindexed by `Fin |Fresh(t)|`, and the
    existing fixed-input XoP theorem has been applied to it.  For every
    transcript \(t\),

    \[
      \delta\bigl(
        \operatorname{tr}(\mathrm{XoP},\operatorname{freshInputs}(t)),
        \operatorname{tr}(\mathrm{URF},\operatorname{freshInputs}(t))
      \bigr)
      =
      \Delta^{\mathrm{visible}}_{|\operatorname{Fresh}(t)|}.
    \]

    The proof is just the previously formalized fixed-injective law plus the
    injectivity of the fresh input tuple.  This is the first theorem that
    directly feeds an arbitrary adaptive transcript into the SoP orbit formula.
22. The fresh fixed-input theorem has also been stated pointwise.  The real
    fresh transcript mass is

    \[
      \frac{C(\operatorname{freshOutputs}(t))}
           {((N)_{|\operatorname{Fresh}(t)|})^2},
    \]

    while the ideal fresh transcript mass is

    \[
      \frac{1}{N^{|\operatorname{Fresh}(t)|}}.
    \]

    These are now Lean theorems for the transcript obtained by embedding
    `freshInputsFin t` and `freshOutputsFin t`.  This is the pointwise form
    needed to compare individual adaptive paths with the orbit/SoP law.
23. The generic stateless-oracle fiber bridge is now formalized in `Equiv`.
    Let a PDS be obtained by first sampling a stateless oracle \(f : X\to Y\)
    from an arbitrary finite distribution and then using the deterministic
    system `DDS.ofFunq f`.  If an adaptive environment follows a transcript
    \(t\), and \(t\) is repeat-consistent, then producing \(t\) adaptively is
    equivalent to producing the fresh subtranscript nonadaptively:

    \[
      \operatorname{tr}(\operatorname{ofFunq}(f),e)=t
      \quad\Longleftrightarrow\quad
      \operatorname{tr}(\operatorname{ofFunq}(f),
        \operatorname{freshInputs}(t))
      =
      (\operatorname{freshInputs}(t),\operatorname{freshOutputs}(t)).
    \]

    After summing over the sampled oracle distribution, the adaptive point mass
    equals the fresh fixed-input point mass.  This is stronger than the earlier
    decomposition by followed paths: it removes repeat queries from each
    followed path pointwise, before any statistical-distance or orbit argument.
24. The generic bridge is instantiated for the concrete XoP real and ideal
    systems in `XoPModel`.  On any followed, repeat-consistent adaptive path,

    \[
      \Pr[\operatorname{tr}(\mathrm{XoP},e)=t]
      =
      \Pr[\operatorname{tr}(\mathrm{XoP},
        \operatorname{freshInputs}(t))
        =
        (\operatorname{freshInputs}(t),\operatorname{freshOutputs}(t))]
    \]

    and the same equality holds for URF.  Combining this with item 22 gives the
    pointwise adaptive path laws:

    \[
      \Pr[\operatorname{tr}(\mathrm{XoP},e)=t]
      =
      \frac{C(\operatorname{freshOutputs}(t))}
           {((N)_{|\operatorname{Fresh}(t)|})^2},
      \qquad
      \Pr[\operatorname{tr}(\mathrm{URF},e)=t]
      =
      \frac{1}{N^{|\operatorname{Fresh}(t)|}},
    \]

    whenever \(e\) follows \(t\) and \(t\) is repeat-consistent; if \(t\) is
    repeat-inconsistent, both masses are \(0\).  This is now the concrete
    local form of the adaptive-to-fresh reduction.
25. The deterministic output-history replay layer is now formalized in
    `Equiv`.  For every adaptive environment \(e\), define

    \[
      \operatorname{Replay}_e(y_1,\ldots,y_q)_i
      =
      \left(e_i(y_1,\ldots,y_{i-1}),\,y_i\right).
    \]

    This transcript is followed by \(e\), has output history \(y^q\), and every
    followed transcript \(t\) is recovered by replaying its output history:

    \[
      \operatorname{Replay}_e(\operatorname{outputs}(t))=t.
    \]

    Therefore the replay map is injective, and for every PDS \(S\),

    \[
      \operatorname{tr}(S,e)
      =
      (\operatorname{Replay}_e)_\#
      \operatorname{outputs}_\#\operatorname{tr}(S,e).
    \]

    Consequently, for any two PDSs \(S,T\),

    \[
      \delta(\operatorname{tr}(S,e),\operatorname{tr}(T,e))
      =
      \delta(
        \operatorname{outputs}_\#\operatorname{tr}(S,e),
        \operatorname{outputs}_\#\operatorname{tr}(T,e)
      ).
    \]

    This is the formal version of the input-symmetry reduction's deterministic
    half: adaptive transcripts contain no more information than their output
    histories once the environment is fixed.  The remaining XoP-specific
    theorem is to identify the adaptive output-history laws as deterministic
    postprocessings of the fixed distinct-query output laws.
26. The adaptive output-history laws for stateless oracle systems are now
    exposed directly.  For a PDS sampled by first drawing an oracle \(f:X\to Y\)
    and then using `DDS.ofFunq f`, the adaptive output-history law under an
    environment \(e\) is exactly the pushforward of the oracle distribution by

    \[
      f \mapsto
      \operatorname{outputs}
      \bigl(\operatorname{interact}(\operatorname{ofFunq}(f),e)\bigr).
    \]

    The concrete XoP model instantiates this twice:

    \[
      \operatorname{outputs}_\#\operatorname{tr}(\mathrm{XoP},e)
      =
      (p_1,p_2 \mapsto
        \operatorname{OutputHist}_e(x\mapsto -p_1(x)+p_2(x)))_\#
      \operatorname{Unif}(\operatorname{Perm}(G)^2),
    \]

    and

    \[
      \operatorname{outputs}_\#\operatorname{tr}(\mathrm{URF},e)
      =
      (f\mapsto \operatorname{OutputHist}_e(f))_\#
      \operatorname{Unif}(G^G).
    \]

    The concrete theorem
    `statDist_xop_adaptiveTranscriptDist_eq_adaptiveOutputDist` also records
    that, for every \(e\), the XoP-vs-URF adaptive transcript distance is
    exactly the statistical distance between these two output-history laws.
    This places the remaining adaptive upper-bound problem at the correct
    level: compare two distributions on output histories induced by adaptively
    chosen input names, using the input-name symmetry of permutation pairs and
    functions.
27. The output-history point masses are now reduced to the replayed transcript
    point masses.  For any PDS \(S\), environment \(e\), and output tape
    \(y^q\),

    \[
      \Pr[\operatorname{outputs}(\operatorname{tr}(S,e))=y^q]
      =
      \Pr[\operatorname{tr}(S,e)=\operatorname{Replay}_e(y^q)].
    \]

    Instantiating this with XoP and URF gives the exact local adaptive
    output-history laws.  If the replayed transcript

    \[
      t_y = \operatorname{Replay}_e(y^q)
    \]

    is repeat-inconsistent, then both real and ideal output-history masses are
    \(0\).  If \(t_y\) is repeat-consistent, then

    \[
      \Pr_R[\operatorname{outputs}=y^q]
      =
      \frac{C(\operatorname{freshOutputs}(t_y))}
           {((N)_{|\operatorname{Fresh}(t_y)|})^2},
      \qquad
      \Pr_I[\operatorname{outputs}=y^q]
      =
      \frac{1}{N^{|\operatorname{Fresh}(t_y)|}}.
    \]

    This is the current strongest formal adaptive endpoint: the arbitrary
    adaptive environment has disappeared except through the deterministic
    replay map \(y^q\mapsto t_y\), and each nonzero output-history mass is
    governed by the already-formalized fresh SoP compatible-count law.
28. The previous pointwise laws have now been summed.  For every environment
    \(e\), the adaptive output-history distance is exactly

    \[
      \sum_{y^q\in G^q}
      \begin{cases}
        \displaystyle
        \frac{C(\operatorname{freshOutputs}(t_y))}
             {((N)_{|\operatorname{Fresh}(t_y)|})^2}
        -
        \frac{1}{N^{|\operatorname{Fresh}(t_y)|}},
        &\text{if }t_y=\operatorname{Replay}_e(y^q)
          \text{ is repeat-consistent},\\[1.2em]
        0,
        &\text{otherwise}.
      \end{cases}
    \]

    The same formula holds for adaptive transcript distance, because adaptive
    transcript distance equals adaptive output-history distance.  This is the
    exact finite adaptive decomposition currently formalized in Lean.  The
    remaining inequality is now sharply isolated: prove that the sum above is
    bounded by the exact \(q\)-query SoP/orbit distance, not merely by a loose
    union bound over fresh-query counts.
29. The conditional data-processing bridge from adaptive replay laws to the
    SoP visible/orbit distance is now formalized.  For fixed injective inputs
    \(x^q\), the output-vector statistical distance is exactly the SoP visible
    distance:

    \[
      \Delta\bigl((F(x_1),\ldots,F(x_q))_R,
                  (F(x_1),\ldots,F(x_q))_I\bigr)
      =
      \operatorname{SoP.visibleStatDist}_q .
    \]

    Moreover, if an adaptive environment \(e\) has a common deterministic
    output-history factorization

    \[
      \Pr_R[\operatorname{outputs}_e\in -]
      = \phi_*\Pr_R[(F(x_1),\ldots,F(x_q))\in -],
      \qquad
      \Pr_I[\operatorname{outputs}_e\in -]
      = \phi_*\Pr_I[(F(x_1),\ldots,F(x_q))\in -],
    \]

    then data processing gives

    \[
      \Delta(\operatorname{tr}(R,e),\operatorname{tr}(I,e))
      \le \operatorname{SoP.visibleStatDist}_q .
    \]

    Consequently, the unrestricted adaptive advantage is bounded by the exact
    SoP visible/orbit distance under the single remaining hypothesis that every
    adaptive environment admits such a common replay factorization.  This
    isolates the last Track-A theorem: prove the factorization from
    input-name symmetry for XoP and URF, not from a hybrid argument.
30. The deterministic fresh-value dependency lemma is now formalized in the
    generic adaptive layer.  For any stateless oracle interaction, if a second
    oracle \(g\) agrees with the fresh input-output pairs generated by an
    oracle \(f\) against the same environment \(e\), then the visible adaptive
    output history is unchanged:

    \[
      g(x)=y \text{ on every fresh pair }(x,y)
      \quad\Longrightarrow\quad
      \operatorname{outputs}_e(g)=\operatorname{outputs}_e(f).
    \]

    This is the deterministic core of fresh-tape replay.  It proves that, once
    the fresh values consumed along an adaptive path are fixed, the rest of the
    output history is forced by the environment and repeat consistency.  The
    remaining probabilistic step is to replace those path-dependent fresh input
    names by a fixed injective input tuple using the input-name symmetry of XoP
    and URF.
31. The fixed-input-name symmetry needed for that replacement is now
    formalized for full \(q\)-tuples.  If \(x^q\) and \(x'^q\) are both
    injective, then the real fixed-output laws agree:

    \[
      (F_R(x_1),\ldots,F_R(x_q))
      \equiv
      (F_R(x'_1),\ldots,F_R(x'_q)).
    \]

    The ideal fixed-output laws agree as well.  In Lean these are proved by
    rewriting both sides to the corresponding SoP visible laws.  This gives the
    exact input-name symmetry statement that the replay-factorization proof
    should consume; what remains is aligning the adaptive fresh-prefix length
    with the fixed \(q\)-tuple tape.
32. The fixed \(q\)-tape replay map is now present in the generic adaptive
    layer.  Given a tape \(y^q\), define a deterministic DDS that, at position
    \(i\), looks at the input prefix and returns the tape entry belonging to the
    first occurrence of the current input name.  Interacting this DDS with an
    environment \(e\) defines

    \[
      \phi_e(y^q) := \operatorname{outputs}(\operatorname{interact}
        (\operatorname{PositionTape}(y^q), e)).
    \]

    The selected first occurrence is proved to have the same input value as the
    current position.  This gives the concrete deterministic candidate for the
    common replay map in item 29.  The remaining work is the distributional
    theorem:

    \[
      \operatorname{outputs}_e(R) \equiv \phi_{e*}(F_R(x^q)),
      \qquad
      \operatorname{outputs}_e(I) \equiv \phi_{e*}(F_I(x^q)),
    \]

    for any fixed injective \(x^q\).
33. The first local correctness property of \(\phi_e\) is now formalized.  If a
    position is fresh in the transcript generated by the position-tape DDS,
    then the output at that position is exactly the tape entry at the same
    coordinate:

    \[
      i\text{ fresh}
      \quad\Longrightarrow\quad
      \operatorname{outputs}_i(\operatorname{PositionTape}(y^q),e)=y_i.
    \]

    The proof factors through the first-occurrence selector: when no earlier
    prefix input matches the current input, the first occurrence is the current
    index itself.  This is the local invariant needed for the fiber-count proof
    of the distributional replay theorem.
34. Position-tape replay is now proved repeat-consistent.  The generic adaptive
    layer defines a global first-occurrence index for an input history and proves
    that equal input names have the same first occurrence.  Since the
    position-tape DDS returns the tape value at that first occurrence, repeated
    adaptive input names receive the same output:

    \[
      x_i=x_j
      \quad\Longrightarrow\quad
      \operatorname{outputs}_i(\operatorname{PositionTape}(y^q),e)
      =
      \operatorname{outputs}_j(\operatorname{PositionTape}(y^q),e).
    \]

    This establishes that \(\phi_e(y^q)\) always lies in the same
    repeat-consistent output-history support as a stateless function oracle.
    The remaining distributional replay theorem can now focus on counting
    fibers of the map \(y^q\mapsto \phi_e(y^q)\), rather than on repeated-query
    consistency.
35. The image/support side of the replay map is now formalized.  Replaying the
    visible output history \(\phi_e(y^q)\) through the same environment recovers
    the original position-tape interaction:

    \[
      \operatorname{transcriptOfOutputs}_e(\phi_e(y^q))
      =
      \operatorname{interact}(\operatorname{PositionTape}(y^q),e).
    \]

    Consequently this replayed transcript is repeat-consistent.  This packages
    the previous point in the exact form needed for the support half of the
    uniform-tape fiber count: every output history produced by the position-tape
    map corresponds to a repeat-consistent transcript on the same adaptive path.
36. The deterministic preimage half of the position-tape fiber count is now
    formalized.  For a target output history \(z^q\), let
    \(t_z=\operatorname{transcriptOfOutputs}_e(z^q)\).  If \(t_z\) is
    repeat-consistent and a tape \(y^q\) agrees with \(z^q\) on every fresh
    position of \(t_z\), then replaying \(y^q\) produces \(z^q\):

    \[
      \bigl(\forall i.\ \operatorname{FreshAt}(t_z,i)\Rightarrow y_i=z_i\bigr)
      \quad\Longrightarrow\quad
      \phi_e(y^q)=z^q.
    \]

    The proof first establishes the fixed-input version: a position tape
    reproduces any repeat-consistent transcript when it agrees on fresh
    positions.  The adaptive version then follows from the existing
    `FollowsTranscript` bridge.  This leaves the converse and cardinality
    statement as the next exact counting step.
37. The exact position-tape fiber count is now formalized.  For a
    repeat-consistent target transcript \(t_z\), the fiber of the replay map is
    exactly the set of tapes agreeing with \(z^q\) on the fresh positions of
    \(t_z\).  Hence

    \[
      |\phi_e^{-1}(z^q)|
      =
      |Y|^{q-|\operatorname{FreshPos}(t_z)|}.
    \]

    This is the core finite-counting statement for the common replay map.  It
    reduces the eventual pushforward-distribution theorem to comparing this
    fiber count with the corresponding stateless-function fiber over the fresh
    input set.
38. The uniform position-tape point masses are now formalized.  If
    \(t_z=\operatorname{transcriptOfOutputs}_e(z^q)\) is repeat-consistent, then

    \[
      \Pr_{y^q\leftarrow Y^q}[\phi_e(y^q)=z^q]
      =
      \frac{|Y|^{q-|\operatorname{FreshPos}(t_z)|}}{|Y|^q}.
    \]

    If \(t_z\) is repeat-inconsistent, the mass is \(0\).  This is the
    position-tape side of the ideal/URF common replay-map theorem.  The
    remaining comparison is the stateless-function side:
    \[
      \Pr_{f\leftarrow Y^X}[\operatorname{outputs}(\operatorname{interact}(f,e))=z^q],
    \]
    which should reduce to the same expression by counting functions on the
    fresh input set.
39. The ideal/URF common replay-map theorem is now formalized in the concrete
    XoP model.  For every adaptive environment \(e\),

    \[
      \operatorname{adaptiveOutputDist}(\operatorname{URF},e)
      =
      \phi_{e*}(\operatorname{Unif}(G^q)).
    \]

    The proof compares point masses.  Repeat-inconsistent replayed transcripts
    have zero mass on both sides.  Repeat-consistent transcripts use the
    position-tape mass from item 38 and the existing URF fresh-transcript mass;
    the arithmetic identity is
    \[
      \frac{|G|^{q-f}}{|G|^q}=\frac1{|G|^f},
      \qquad f=|\operatorname{FreshPos}(t_z)|.
    \]

40. The real/XoP common replay-map theorem is now formalized.  For every
    adaptive environment \(e\), assuming \(q\le |G|\),

    \[
      \operatorname{adaptiveOutputDist}(\operatorname{XoP},e)
      =
      \phi_{e*}(\operatorname{realVisibleDist}_q).
    \]

    The proof is again pointwise.  Repeat-inconsistent replayed transcripts
    have zero mass on both sides.  For repeat-consistent \(z^q\), the preimage
    condition under \(\phi_e\) is equivalent to agreement with \(z^q\) on the
    fresh positions of \(t_z=\operatorname{transcriptOfOutputs}_e(z^q)\).
    Projecting \(\operatorname{realVisibleDist}_q\) to those fresh coordinates
    gives \(\operatorname{realVisibleDist}_f\), and its point mass is

    \[
      \frac{C(\operatorname{freshOutputs}(t_z))}{((|G|)_f)^2}.
    \]

    This is implemented as
    `xopReal_adaptiveOutputDist_eq_positionTape_realVisible`.

41. The conditional adaptive upper bound has been discharged.  The common map is
    now explicitly \(\phi_e=\operatorname{outputHistoryOfPositionTape}_e\), so
    data processing gives

    \[
      \operatorname{Adv}^{\operatorname{adaptive}}_q(\operatorname{XoP},\operatorname{URF})
      \le
      \operatorname{visibleStatDist}_q(\operatorname{SoP}).
    \]

    The formal theorem is `xop_adaptiveAdvantage_le_sop_visibleStatDist`.

42. Combining item 41 with the already formalized fixed-injective lower bound
    closes the adaptive reduction:

    \[
      \operatorname{Adv}^{\operatorname{adaptive}}_q(\operatorname{XoP},\operatorname{URF})
      =
      \operatorname{visibleStatDist}_q(\operatorname{SoP}).
    \]

    This is the current Track-A endpoint, formalized as
    `xop_adaptiveAdvantage_eq_sop_visibleStatDist`.  The remaining core work is
    no longer an adaptive-symmetry issue; it is the exact finite-\(N\)
    evaluation or bounding of the SoP/orbit visible distance.

43. The affine-orbit API now exposes the closed adaptive theorem directly.  For
    any affine-coordinate orbit classifier \(\kappa:G^q\to\Omega\),

    \[
      \operatorname{Adv}^{\operatorname{adaptive}}_q(\operatorname{XoP},\operatorname{URF})
      =
      \operatorname{SD}(\kappa_*\operatorname{realVisibleDist}_q,
                        \kappa_*\operatorname{idealVisibleDist}_q),
    \]

    and equivalently

    \[
      \operatorname{Adv}^{\operatorname{adaptive}}_q
      =
      \sum_{\omega\in\Omega}
      \left(
        |\kappa^{-1}(\omega)|\,
        \frac{C_\omega}{((|G|)_q)^2}
        -
        |\kappa^{-1}(\omega)|\,\frac1{|G|^q}
      \right)_+ .
    \]

    The Lean endpoints are
    `xop_adaptiveAdvantage_eq_classifierStatDist_of_affineCoordOrbitClassifier`,
    `xop_adaptiveAdvantage_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier`,
    and `exists_orbitMassCoupling_xop_adaptiveAdvantage`.

44. The gain-graph inclusion-exclusion formula is now rank-stratified in Lean.
    For a collision-event subfamily \(T\), define the graphic rank

    \[
      r(T)=q-\kappa(T),
    \]

    where \(\kappa(T)\) is the number of connected components of the support
    graph on all \(q\) vertices.  The formalization packages this as the finite
    classifier `collisionSubfamilyGraphicRankFin`.  The explicit grouped formula
    is

    \[
      C(y)
      =
      \sum_{r=0}^{q}
        \sum_{\substack{T\subseteq\mathcal E_q\\ r(T)=r}}
          (-1)^{|T|}
          \mathbf 1_{\operatorname{cycleConsistent}(T)}
          |G|^{q-r}.
    \]

    In Lean this is
    `compatibleCountNat_eq_rankSum_cycleConsistentSubfamilies_explicit`.
    This is the first general formal step toward a uniform tail bound: the
    remaining estimates can now target rank layers rather than the raw powerset
    of collision events.

45. The rank-\(0\) layer is now isolated.  The empty subfamily has \(q\)
    connected components and graphic rank \(0\); every nonempty collision-event
    subfamily has positive graphic rank because it identifies the two distinct
    endpoints of at least one collision event.  Consequently the rank-\(0\)
    layer contributes exactly

    \[
      |G|^q.
    \]

    The Lean theorem is `collisionSubfamily_rankZeroLayer_eq_card_fun`.  The
    file also records that singleton subfamilies are semantically consistent
    and cycle-consistent.  This sets up the rank-\(1\) coefficient computation
    without yet committing to any small-\(q\) enumeration.

46. Singleton collision-event subfamilies now have exact graphic rank one.  The
    proof identifies the connected components of the one-edge support graph
    with all query coordinates except the right endpoint of the selected edge:

    \[
      \pi_0(\{e\}) \simeq \{i\in\operatorname{Fin}(q): i\ne \operatorname{right}(e)\}.
    \]

    Hence

    \[
      \kappa(\{e\})=q-1,\qquad r(\{e\})=1.
    \]

    The Lean endpoints are `collisionSubfamilyComponentCount_singleton` and
    `collisionSubfamilyGraphicRank_singleton`.  This gives the singleton part
    of the rank-\(1\) coefficient.  The remaining rank-\(1\) work is to handle
    two-event parallel subfamilies, which are the source of the \(+K(y)\)
    correction in the indexed event family.

47. Nonempty same-endpoint collision-event subfamilies now have exact graphic
    rank one.  This generalizes the singleton lemma from one event to any
    finite subfamily whose events all use the same query-coordinate pair
    \((i,j)\), possibly with different collision kinds.  The support graph is
    still just one ordinary edge between \(i\) and \(j\), so its connected
    components are again identified with all coordinates except the common
    right endpoint:

    \[
      \pi_0(T) \simeq \{k\in\operatorname{Fin}(q): k\ne j\},
      \qquad
      \kappa(T)=q-1,\qquad r(T)=1.
    \]

    The Lean endpoints are `collisionSubfamilySameEndpoints`,
    `collisionSubfamilyComponentCount_eq_of_sameEndpoints`, and
    `collisionSubfamilyGraphicRank_eq_one_of_sameEndpoints`.  This captures the
    graph-rank part of the parallel-event correction without doing any
    small-\(q\) enumeration.  The next proof obligation is semantic: prove that
    a two-event same-endpoint subfamily is cycle-consistent exactly when the
    two event labels agree.  For a hidden/shifted pair this specializes to the
    visible equality condition \(y_i=y_j\), which is the source of the
    \(+K(y)\) correction in the rank-\(1\) layer.

48. The semantic part of the two-event parallel correction is now formalized.
    For any two collision events \(e_1,e_2\) with the same endpoints, the
    labelled equation system on \(\{e_1,e_2\}\) is satisfiable exactly when
    their labels agree:

    \[
      \operatorname{consistent}_y(\{e_1,e_2\})
      \quad\Longleftrightarrow\quad
      \ell_y(e_1)=\ell_y(e_2).
    \]

    The same equivalence holds for closed-walk cycle consistency by the
    semantic/cycle-consistency theorem.  For the concrete hidden/shifted pair
    on one query pair \(i<j\), this becomes

    \[
      \operatorname{cycleConsistent}_y(\{(i,j,\mathrm{hidden}),
        (i,j,\mathrm{shifted})\})
      \quad\Longleftrightarrow\quad
      y_j=y_i.
    \]

    The Lean endpoints are
    `collisionSubfamilyConsistent_pair_sameEndpoints_iff_label_eq`,
    `collisionSubfamilyCycleConsistent_pair_sameEndpoints_iff_label_eq`,
    `collisionEventLabel_hidden_eq_shifted_iff`, and
    `collisionSubfamilyCycleConsistent_hidden_shifted_pair_iff`.  This closes
    the local proof obligation that the rank-\(1\) non-singleton contribution
    is controlled exactly by visible equality collisions.

49. The pair-local indexed event set is now packaged.  For a query pair
    \(p=(i,j)\), define

    \[
      \mathcal E_p=\{(p,\mathrm{hidden}),(p,\mathrm{shifted})\}.
    \]

    Every nonempty subfamily \(T\subseteq \mathcal E_p\) has graphic rank one,
    because all its events share the same support edge.  The full pair-local
    set is cycle-consistent exactly when the visible pair collides:

    \[
      \operatorname{cycleConsistent}_y(\mathcal E_p)
      \quad\Longleftrightarrow\quad
      y_j=y_i.
    \]

    The Lean endpoints are `collisionPairEvents`,
    `collisionSubfamilySameEndpoints_of_subset_collisionPairEvents`,
    `collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents`,
    and `collisionPairEvents_cycleConsistent_iff`.  This gives the indexed,
    pairwise building block needed to turn the rank-\(1\) layer into the
    coefficient \(-(2H-K(y))|G|^{q-1}\).

50. The pair-local alternating coefficient is now formalized in explicit
    three-term form.  For a query pair \(p=(i,j)\), the two singleton
    constraints each contribute \(-1\), and the full hidden/shifted pair
    contributes \(+1\) exactly when \(y_i=y_j\):

    \[
      -1-1+\mathbf 1[y_i=y_j]
      =
      -2+\mathbf 1[y_i=y_j].
    \]

    The Lean endpoint is `collisionPairEvents_localAlternatingCoefficient`.
    This is deliberately stated locally rather than as a global powerset
    identity: the remaining work is the separate rank-\(1\) classification
    theorem saying that every graphic-rank-one nonempty subfamily is contained
    in a unique pair-local event set \(\mathcal E_p\).  Once that classification
    is available, summing this local coefficient over all \(p\in\binom{[q]}2\)
    gives the rank-\(1\) coefficient \(-2H+K(y)\).

51. The monotonicity spine for the global rank-\(1\) classification is now
    formalized.  If \(S\subseteq T\), then every support adjacency and every
    support path in \(S\) is also present in \(T\).  Consequently enlarging the
    selected collision-event family can only merge connected components and can
    only increase graphic rank:

    \[
      S\subseteq T
      \quad\Longrightarrow\quad
      \kappa(T)\le \kappa(S),\qquad r(S)\le r(T).
    \]

    The Lean endpoints are `collisionSubfamilyAdjacent_mono`,
    `collisionSubfamilyConnected_mono`, `collisionSubfamilyComponentCount_anti`,
    and `collisionSubfamilyGraphicRank_mono`.  These lemmas are the graph-level
    infrastructure needed for the remaining converse: if \(T\ne\varnothing\)
    and \(r(T)=1\), then \(T\) is contained in the pair-local event set
    \(\mathcal E_p\) for the endpoint pair of any event in \(T\).

52. The monotonicity layer now also records the immediate rank-\(1\) inheritance
    consequences.  If \(S\subseteq T\) and \(r(T)=1\), then \(r(S)\le 1\); if
    \(S\) is nonempty, then \(r(S)=1\).  The Lean endpoints are
    `collisionSubfamilyGraphicRank_le_one_of_subset_rank_one` and
    `collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_rank_one`.
    This reduces the global rank-\(1\) converse to the two-event support
    problem: any two selected events in a rank-\(1\) family form a nonempty
    rank-\(1\) subfamily, so it remains to prove that a two-event rank-\(1\)
    support has one endpoint pair.

53. The global rank-\(1\) support classification is now formalized.  The proof
    uses the natural quotient map between support components: if
    \(S\subseteq T\) and \(\kappa(S)=\kappa(T)\), then every connection present
    in \(T\) was already present in \(S\).  Applying this to
    \(\{e_1\}\subseteq T\) with \(r(T)=1\), the endpoints of any selected
    \(e_2\in T\) are connected in the singleton support of \(e_1\).  The
    singleton representative calculation then forces equality of endpoint
    pairs.

    The final theorem is
    `collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents`:

    \[
      r(T)=1
      \quad\Longleftrightarrow\quad
      T\ne\varnothing\ \wedge\
      \exists p,\ T\subseteq \mathcal E_p.
    \]

    Supporting Lean endpoints include
    `collisionSubfamilyComponentMap`,
    `collisionSubfamilyConnected_of_connected_of_componentCount_eq`,
    `collisionSubfamilyEvent_connected_in_singleton_of_rank_one`,
    `collisionEvent_endpoints_eq_of_mem_graphicRank_eq_one`, and
    `collisionSubfamily_subset_collisionPairEvents_of_graphicRank_eq_one`.
    This closes the structural classification of the rank-\(1\) layer.  The
    remaining coefficient theorem is now a finite disjoint-sum/cardinality
    argument over pair-local subfamilies, not a graph-theoretic open point.

54. Pair-local uniqueness is now formalized.  If an event lies in
    \(\mathcal E_p\), then its underlying query pair is exactly \(p\).  Hence a
    nonempty subfamily \(T\) can be contained in at most one pair-local event
    set:

    \[
      T\ne\varnothing,\ T\subseteq\mathcal E_{p_1},\
      T\subseteq\mathcal E_{p_2}
      \quad\Longrightarrow\quad
      p_1=p_2.
    \]

    The Lean endpoints are `collisionEvent_pairIndex_eq_of_mem_collisionPairEvents`
    and `collisionPairEvents_subset_unique_of_nonempty`.  Together with item
    53, this gives the disjointness needed to rewrite the global rank-\(1\)
    sum as a sum over pair indices of the pair-local three-term coefficient.

55. The rank-\(1\) support classifier is now formalized.  Given
    \(r(T)=1\), Lean defines
    `collisionSubfamilyRankOnePair T hrank`, the unique query pair \(p\) such
    that \(T\subseteq\mathcal E_p\).  The supporting theorems are:

    - `collisionSubfamilyRankOne_nonempty`: rank-\(1\) families are nonempty;
    - `collisionSubfamily_subset_rankOnePairEvents`: the chosen pair supports
      \(T\);
    - `collisionSubfamilyRankOnePair_eq_of_subset`: any other pair-local
      support for \(T\) is the same pair.

    I deliberately stopped short of forcing the full dependent sigma
    equivalence in this step.  The transport proof for the equivalence is pure
    Lean bookkeeping; the mathematical content needed for the rank-\(1\)
    coefficient is the classifier plus uniqueness.  The next coefficient proof
    should use these lemmas directly, or introduce a small purpose-built
    `Finset.disjiUnion` over classifier fibers if the sum rewrite requires it.

56. The pair-local coefficient is now connected to the actual nonempty
    powerset sum.  A small generic finite-set lemma,
    `finset_pair_powerset_filter_nonempty`, identifies the nonempty subsets of
    a two-element set with the two singletons and the full pair.  Specializing
    this to

    \[
      \mathcal E_p=\{(p,\mathrm{hidden}),(p,\mathrm{shifted})\}
    \]

    gives the Lean theorem
    `collisionPairEvents_localPowersetAlternatingCoefficient`:

    \[
      \sum_{\varnothing\ne T\subseteq\mathcal E_p}
        (-1)^{|T|}
        \mathbf 1_{\operatorname{cycleConsistent}_y(T)}
      =
      -2+\mathbf 1[y_j=y_i].
    \]

    This removes the gap between the manual three-term local coefficient in
    item 50 and the form needed by the global rank-\(1\) powerset layer.  The
    remaining global proof obligation is now the reindexing of the rank-\(1\)
    nonempty subfamily sum by the unique classifier
    `collisionSubfamilyRankOnePair`.

57. The rank-\(1\) classifier is now packaged for finite-sum reindexing.  The
    partial classifier `collisionSubfamilyRankOnePair T hrank` is wrapped by
    the total optional classifier
    `collisionSubfamilyRankOnePairOption`.  Its `some p` fiber is exactly

    \[
      \{\varnothing\ne T:T\subseteq\mathcal E_p\}.
    \]

    Lean endpoints:

    - `collisionSubfamilyRankOnePairOption_eq_some_iff`;
    - `collisionSubfamilyRankOnePairOption_fiber_eq_pairPowerset`;
    - `collisionSubfamilyRankOneSubfamilies_eq_biUnion_pairPowersets`;
    - `collisionSubfamilyRankOneFinSubfamilies_eq_biUnion_pairPowersets`.

    The last theorem states the same decomposition for the finite rank
    classifier used by the rank-stratified formula.  It has the necessary
    hypothesis \(0<q\), because `Fin (q+1)` only contains the value \(1\) when
    \(q\) is nonzero.

58. The global rank-\(1\) coefficient is now formalized.  The pair-local
    powerset fibers are pairwise disjoint
    (`collisionPairEvents_powerset_nonempty_pairwiseDisjoint`), so the
    `biUnion` decomposition can be used with `Finset.sum_biUnion`.  The
    resulting coefficient theorem is
    `collisionSubfamily_rankOneLayerAlternatingCoefficient`:

    \[
      \sum_{\substack{T\subseteq\mathcal E_q\\ r(T)=1}}
        (-1)^{|T|}
        \mathbf 1_{\operatorname{cycleConsistent}_y(T)}
      =
      \sum_{p=(i,j)}
        \left(-2+\mathbf 1[y_j=y_i]\right).
    \]

    The weighted version that appears directly in the rank-stratified
    compatible-count formula is
    `collisionSubfamily_rankOneLayer_eq_card_pow_mul_pairCoefficient`:

    \[
      \sum_{\substack{T\subseteq\mathcal E_q\\ r(T)=1}}
        (-1)^{|T|}
        \mathbf 1_{\operatorname{cycleConsistent}_y(T)}
        |G|^{q-1}
      =
      |G|^{q-1}
      \sum_{p=(i,j)}
        \left(-2+\mathbf 1[y_j=y_i]\right).
    \]

    This completes the general, non-small-\(q\) formal proof of the rank-\(1\)
    layer.  The next genuinely new mathematical layer is a uniform treatment
    of \(r(T)\ge 2\), where triangles are still pattern-level and the first
    affine-value dependence appears through rank-\(3\) four-cycle constraints.

59. The finite-partition theorem has now been strengthened into an explicit
    LM20 block-coupling statement.  The distribution-level theorem
    `statDist_eq_classifierStatDist_of_commonConditionals` already said that,
    if two transcript laws share the same conditional distribution inside
    every classifier fiber, their statistical distance is exactly the distance
    between pushed-forward classifier masses.  The new theorem
    `exists_classifierMassCoupling_of_commonConditionals` adds the coupling
    witness:

    \[
      \exists C:\operatorname{Coupling}(\kappa_*X,\kappa_*Y),
      \qquad
      \delta(X,Y)=\Pr_C[\omega_X\ne\omega_Y].
    \]

    There is also a constant-fiber version,
    `exists_classifierMassCoupling_of_constantFibers`, and an SoP visible-law
    specialization,
    `exists_visibleClassifierMassCoupling_of_compatibleCount_constant`.
    This is the abstract form of the intended LM20 move: couple classifier
    labels optimally; once labels match, there is no remaining distinguishing
    mass inside the block.

60. The affine-orbit XoP coupling theorem now goes through the abstract
    classifier-coupling theorem.  The endpoints
    `exists_orbitMassCoupling_xop_advantageOn_injective` and
    `exists_orbitMassCoupling_xop_adaptiveAdvantage` still state the same
    result as before, but their proof now factors through
    `exists_visibleClassifierMassCoupling_of_compatibleCount_constant`.
    This is the first correction toward making LM20 load-bearing rather than a
    post-hoc explanation of the orbit count.

61. The LM20 nonadaptive-to-adaptive representative lift is now named in the
    core `Equiv` layer.  The theorem
    `PDS.equivAdaptive_of_transcriptDist_eq` states that equality of
    nonadaptive transcript distributions for all fixed input sequences implies
    full adaptive PDS equivalence:

    \[
      \bigl(\forall x^q,\ \operatorname{tr}(S,x^q)=\operatorname{tr}(T,x^q)\bigr)
      \Longrightarrow
      S\equiv_{\mathrm{adaptive}}T.
    \]

    This is the exact formal bridge needed by future transcript-level
    representative constructions.  What remains is not the LM20 bridge itself;
    it is the construction of an honest PDS whose fixed-input transcript law is
    the chosen block/orbit representative.

62. The first honest PDS representative constructor is now formalized in the
    core `Equiv` layer.  The new transcript helper
    `Transcript.ofOutputs` embeds an output vector into a transcript with fixed
    input components.  The new position-tape lemmas prove that, on an
    injective fixed input sequence, replaying a position-indexed tape consumes
    exactly the same position of the tape:

    \[
      \operatorname{transcript}(\operatorname{ofPositionTape}(y^q),x^q)
      =
      \operatorname{ofOutputs}(x^q,y^q).
    \]

    The PDS constructor `PDS.ofPositionTapeDist` then turns any distribution
    \(D\) over output vectors into an honest distribution over deterministic
    discrete systems by sampling a tape and replaying it.  The theorem
    `PDS.transcriptDist_ofPositionTapeDist_eq` proves the exact fixed-input
    law:

    \[
      \operatorname{transcriptDist}
        (\operatorname{ofPositionTapeDist}(D),x^q)
      =
      (\operatorname{ofOutputs}(x^q,\cdot))_*D
    \]

    whenever \(x^q\) is injective.  This is a system-level LM20 lift, not a
    counting estimate: arbitrary output-vector laws, including future
    “choose an orbit, then sample uniformly inside it” laws, can now be
    realized as honest PDS representatives on the injective nonadaptive slice.
    The remaining XoP-specific step is to choose \(D\) from the affine-orbit
    block law and prove that this pushed-forward tape law matches the natural
    XoP or URF visible transcript law on every injective input sequence.

63. The “sample a block, then sample uniformly inside the block” law is now a
    named object at the finite-distribution layer.  For any classifier
    \(\kappa : A\to\Omega\), `classifierBlockUniform X κ` assigns to
    \(a\in A\) the mass

    \[
      \frac{(\kappa_*X)(\kappa(a))}
           {|\kappa^{-1}(\kappa(a))|}.
    \]

    This is no longer just a pointwise formula.  The file now defines
    `classifierFiberUniform κ ω`, the uniform conditional law on the fiber
    \(\kappa^{-1}(\omega)\), extended by zero outside the fiber.  The key
    formal facts are:

    - `classifierFiberUniform_sum_of_nonempty`: on a nonempty fiber,
      `classifierFiberUniform` has total mass \(1\);
    - `classifierFiberUniform_sum_eq_indicator`: empty fibers have total mass
      \(0\), nonempty fibers have total mass \(1\);
    - `classifierBlockUniform_factor_through_fiberUniform`: pointwise,
      \[
        \operatorname{BlockUniform}_X(a)
        =
        (\kappa_*X)(\kappa(a))\cdot
        \operatorname{FiberUniform}_{\kappa(a)}(a).
      \]

    This is the explicit LM20 representative semantics: sample the block label
    according to the original block mass, then sample from the uniform
    conditional distribution inside that block.

    The theorem `classifierBlockUniform_eq_of_constantFibers` proves that, if
    \(X\) is constant on classifier fibers, then this block-uniform
    representative is exactly \(X\).  The SoP specializations
    `realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant`
    and `idealVisibleDist_eq_classifierBlockUniform` instantiate this for the
    real and ideal visible laws.  Thus the intended LM20 representatives have
    now been proved, at the visible-output distribution level, to be precisely:
    choose a classifier/orbit label according to the real or ideal block mass,
    then sample uniformly in that block.  The PDS lift combines this
    block-uniform visible law with `PDS.ofPositionTapeDist` and the existing
    adaptive/nonadaptive bridge.

    The block masses themselves are now named in computable form.  For the real
    visible law,
    `classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount`
    proves

    \[
      W_R(\omega)
      =
      |\kappa^{-1}(\omega)|
      \frac{C_\omega}{(N)_q^2},
    \]

    and `classifierWeight_idealVisibleDist_eq_card_mul_uniformMass` proves

    \[
      W_I(\omega)
      =
      |\kappa^{-1}(\omega)|\frac{1}{N^q}.
    \]

    The affine specializations
    `classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount_of_affineCoordOrbitClassifier`
    and
    `classifierWeight_idealVisibleDist_eq_card_mul_uniformMass_of_affineCoordOrbitClassifier`
    expose the same formulas at the XoP orbit layer.  This makes the exact
    block-mass discrepancy explicit before any gain-graph estimate is applied.
    The named XoP endpoints
    `xop_advantageOn_injective_eq_sum_classifierWeights_of_affineCoordOrbitClassifier`
    and
    `xop_adaptiveAdvantage_eq_sum_classifierWeights_of_affineCoordOrbitClassifier`
    now state this discrepancy directly as the restricted and unrestricted
    XoP advantage.

64. The block-uniform representatives have now been lifted to honest adaptive
    PDS representatives for XoP/URF.  The generic theorem
    `PDS.adaptiveOutputDist_ofPositionTapeDist_eq` proves that a
    position-tape PDS has adaptive output-history law

    \[
      (DDE.outputHistoryOfPositionTape(e))_*D.
    \]

    In `XoPModel`, the natural systems are shown output-equivalent to the
    position-tape representatives built from the block-uniform visible laws:
    `xopReal_adaptiveOutputDist_eq_positionTape_blockUniform` and
    `xopIdeal_adaptiveOutputDist_eq_positionTape_blockUniform`.  Since adaptive
    equivalence in the repository is governed by the LM20
    adaptive/nonadaptive bridge, the proof now exposes the intermediate
    nonadaptive statements:

    - `xopReal_transcriptDist_eq_positionTape_blockUniform`, showing that the
      natural real XoP PDS and its block-uniform position-tape representative
      have the same fixed-input transcript law for every input sequence;
    - `xopIdeal_transcriptDist_eq_positionTape_blockUniform`, the analogous
      statement for URF.

    The adaptive equivalence theorems
    `xopReal_equivAdaptive_positionTape_blockUniform` and
    `xopIdeal_equivAdaptive_positionTape_blockUniform` are now direct
    applications of `PDS.equivAdaptive_of_transcriptDist_eq`, whose proof rests
    on `PDS.equivAdaptive_iff_nonadaptive`.

    Finally, the affine-orbit file packages both representatives together in
    `xop_equivAdaptive_blockUniformRepresentatives_of_affineCoordOrbitClassifier`.
    This is the proof shape we wanted: starting from the natural XoP and URF
    PDSs, LM20 allows us to replace them by honest equivalent representatives
    that choose an affine/output block and then sample uniformly inside it.
    The existing orbit-mass coupling theorem can now be read as a coupling
    between the label laws of these representatives, with perfect agreement
    inside matched labels.

65. The representative and coupling layers are now packaged in one LM20-native
    endpoint.  The generic theorem
    `statDist_classifierBlockUniform_eq_classifierStatDist` states the direct
    distance identity for block-uniform representatives:

    \[
      \delta(\operatorname{BlockUnif}_\kappa(X),
              \operatorname{BlockUnif}_\kappa(Y))
      =
      \delta(\kappa_*\operatorname{BlockUnif}_\kappa(X),
              \kappa_*\operatorname{BlockUnif}_\kappa(Y)).
    \]

    The theorem `exists_classifierMassCoupling_of_blockUniform` then gives an
    optimal classifier-label coupling:

    \[
      \delta(\operatorname{BlockUnif}_\kappa(X),
              \operatorname{BlockUnif}_\kappa(Y))
      =
      \Pr[\omega_R\ne\omega_I].
    \]

    The stronger theorem
    `exists_fullAndClassifierMassCouplings_of_blockUniform` also produces a
    full coupling of the block-uniform representatives with the same failure
    probability as the classifier-label coupling.  This certifies the LM20
    value at the representative-distribution level.  The new theorem
    `classifierBlockUniform_fTransform` records the corresponding mass
    preservation identity:

    \[
      \kappa_*(\operatorname{BlockUnif}_\kappa(X))=\kappa_*X.
    \]

    The explicit joint distribution
    `labelFirstBlockCouplingJoint` now names the intended label-first lift:
    sample classifier labels from a label coupling; if the labels match, sample
    one element uniformly from the common fiber and return it on both sides; if
    the labels differ, sample uniformly in the two fibers.  The theorem
    `labelFirstBlockCouplingJoint_eq_zero_of_same_label_ne` proves the first
    key property of this joint: same-label off-diagonal pairs have zero mass.
    The support lemmas
    `classifierMassCoupling_joint_eq_zero_of_left_empty` and
    `classifierMassCoupling_joint_eq_zero_of_right_empty` prove that an
    all-label coupling cannot put mass on labels whose actual classifier
    fibers are empty.  Finally,
    `sum_labelFirstBlockCouplingJoint_same_label_right` and
    `sum_labelFirstBlockCouplingJoint_same_label_left` prove the diagonal
    fiber-sum identities used by the two marginal calculations.  The theorems
    `labelFirstBlockCouplingJoint_marginal_fst` and
    `labelFirstBlockCouplingJoint_marginal_snd` prove the explicit joint has
    the intended block-uniform representative marginals, and
    `labelFirstBlockCoupling` packages it as an honest `DistCoupling` of the
    representatives.  The theorems
    `sum_labelFirstBlockCouplingJoint_fibers` and
    `labelFirstBlockCouplingJoint_fTransform_labels` prove that pushing the
    lifted joint through the two classifier labels recovers the original
    label coupling.  Finally, `labelFirstBlockCoupling_prDisagree` proves that
    the lifted full coupling disagrees exactly when the label coupling
    disagrees.  Consequently
    `exists_fullAndClassifierMassCouplings_of_blockUniform` now uses the
    literal label-first construction as its full representative coupling,
    rather than an abstract optimal-coupling witness.

    The affine/XoP theorem
    `exists_fullBlockUniformRepresentativeOrbitCoupling_xop_adaptiveAdvantage`
    combines this with the honest representative theorem:

    - the natural XoP PDS is adaptively equivalent to the real block-uniform
      position-tape representative;
    - the natural URF PDS is adaptively equivalent to the ideal block-uniform
      position-tape representative;
    - an optimal coupling of the representatives' affine-orbit labels has
      disagreement probability exactly equal to the unrestricted adaptive XoP
      advantage;
    - the explicit label-first full coupling of the block-uniform
      representatives has the same disagreement probability.

    At this point the LM20 layer is no longer bolted onto a transcript count:
    it starts from the natural PDSs, replaces them by honest equivalent
    representatives, and couples those representatives with value equal to the
    orbit-label mismatch.  The explicit label-first joint construction is now
    the coupling witness used by the generic block theorem.  The
    gain-graph/rank expansion is now only the subsequent analytic method for
    evaluating or bounding the resulting label-mass discrepancy.

    The generic partition layer now also has the cleaner original-label-mass
    form:

    - `statDist_classifierBlockUniform_eq_originalClassifierStatDist`, proving
      that the distance between block-uniform representatives is exactly the
      distance between the original classifier pushforwards
      \(κ_*X\) and \(κ_*Y\);
    - `exists_fullAndOriginalClassifierMassCouplings_of_blockUniform`, proving
      that an optimal coupling of those original classifier masses can be
      lifted to the explicit label-first full coupling of the block-uniform
      representatives.

    This removes a type-level nuisance from the statement: the label coupling
    is now over the real and ideal block weights themselves, not merely over
    the pushforwards of already-block-uniform representatives.

66. The representative coupling has also been lifted from visible output tapes
    to the distributions over deterministic systems used by LM20.  The generic
    coupling theorem `DistCoupling.fTransform` pushes a coupling forward
    through any deterministic map on both sides, and
    `DistCoupling.prDisagree_fTransform_of_injective` proves that an injective
    map preserves its disagreement probability.

    For position-tape representatives, the map from output tapes to DDSs is
    injective whenever the input alphabet admits an injective \(q\)-query
    sequence.  This is formalized as
    `DDS.ofPositionTape_injective_of_injective_inputs`: replaying that fixed
    fresh-input sequence observes every tape coordinate.  The corresponding
    PDS-distribution lift is `PDS.positionTapeDistCoupling`, with value
    preservation theorem
    `PDS.positionTapeDistCoupling_prDisagree_of_injective_inputs`.

    The affine/XoP endpoint
    `exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_cardCompatibleCountSum`
    now states the strongest LM20-native shape currently formalized:

    - the natural XoP and URF PDSs are adaptively equivalent to honest
      position-tape PDS representatives built from block-uniform visible laws;
    - the label coupling is an optimal coupling of the original affine-orbit
      masses `Dist.fTransform κ realVisibleDist` and
      `Dist.fTransform κ idealVisibleDist`;
    - the label-coupling failure probability is exactly the finite orbit sum
      \[
        \sum_\omega
        \left(
          |\kappa^{-1}(\omega)|\frac{C_\omega}{(N)_q^2}
          -
          |\kappa^{-1}(\omega)|\frac{1}{N^q}
        \right)_+;
      \]
    - the representative PDS distributions themselves have a coupling over DDS
      values;
    - this DDS-level coupling has failure probability equal to the same
      cardinality-times-\(C_\omega\) orbit sum, hence equal to the unrestricted
      adaptive XoP advantage.

Bounds and small-\(q\) calculations should remain separate applications of the
formula, not part of the adaptive core theorem.

## Response to peer review: the matroid interface needs one correction

The peer review correctly identifies the geometric object behind the orbit
partition: an orbit is the same kind of data as an unordered affine
configuration of \(q\) points in \(\mathbb F_2^n\), equivalently an
\(\mathbb F_2\)-representable affine matroid with labels forgotten up to
isomorphism.

However, the proposed direct formula

\[
  C_\omega =
  \sum_{X \subseteq M} (-1)^{|X|}
    N^{\operatorname{rank}(M)-\operatorname{rank}(X)}
\]

should not be used as stated.  It is not yet a theorem, and in this form it is
not the right object.  The compatible count does not only ask for independent
sets of the visible affine matroid.  It asks for a hidden tuple \(a\) avoiding
two families of pairwise collision constraints:

1. hidden collisions \(a_i=a_j\),
2. shifted collisions \(a_i+y_i=a_j+y_j\).

The second family depends on the visible differences \(y_i+y_j\).  Thus the
natural inclusion-exclusion object is a labelled graphic constraint system, or
equivalently a gain-graph/affine-arrangement object, not merely the ordinary
Tutte polynomial of the affine matroid of \(Y\).

The exact replacement is the following formula.

For \(y \in G^q\), it is often clean on paper to define the deduplicated finite
event set

\[
  \mathcal E(y)
  =
  \{(i,j,0) : 1 \le i < j \le q\}
  \cup
  \{(i,j,y_i+y_j) : 1 \le i < j \le q,\; y_i \ne y_j\}.
\]

The event \((i,j,\lambda)\) means the affine equation

\[
  a_i+a_j=\lambda.
\]

The label \(0\) gives the hidden collision \(a_i=a_j\).  The label
\(y_i+y_j\) gives the shifted collision \(a_i+y_i=a_j+y_j\).  When
\(y_i=y_j\), these are the same event, so the shifted copy is deliberately not
duplicated.

The current Lean formalization uses the slightly more direct indexed family
with both the hidden and shifted event for every pair.  When \(y_i=y_j\), those
two indexed events are duplicate constraints.  Inclusion-exclusion over an
indexed family with duplicate sets remains valid, and the duplicate version can
later be quotiented to the deduplicated paper version if that becomes useful
for presentation.

For \(T \subseteq \mathcal E(y)\), let \(\Gamma_T\) be the labelled graph on
vertices \(\{1,\ldots,q\}\) with edge labels \(\lambda\).  Say that \(T\) is
consistent if, on every cycle of \(\Gamma_T\), the xor of the edge labels around
the cycle is \(0\).  Since the equations are over characteristic \(2\), this is
exactly the condition for the system

\[
  a_i+a_j=\lambda
  \qquad ((i,j,\lambda)\in T)
\]

to have a solution.

Let \(\kappa(T)\) be the number of connected components of the underlying graph
on all \(q\) vertices, including isolated vertices.

**Lemma 4.** For every \(y \in G^q\),

\[
  C(y)
  =
  \sum_{T \subseteq \mathcal E(y)}
    (-1)^{|T|}
    \mathbf 1_{\operatorname{consistent}(T)}
    N^{\kappa(T)}.
\]

**Proof.** The forbidden events for compatibility are precisely the events in
\(\mathcal E(y)\).  A tuple \(a\) is compatible with \(y\) if and only if none
of these events occurs.  Inclusion-exclusion gives

\[
  C(y)
  =
  \sum_{T \subseteq \mathcal E(y)}
    (-1)^{|T|}
    \#\{a \in G^q : a_i+a_j=\lambda
       \text{ for every } (i,j,\lambda)\in T\}.
\]

It remains to count the solution set for a fixed \(T\).  In any connected
component of \(\Gamma_T\), choosing one vertex value determines every other
vertex value if the labels are cycle-consistent.  If some cycle has nonzero xor
label, the equations force \(a_v=a_v+\mu\) for some \(\mu\ne0\), so there is no
solution.  Therefore a consistent \(T\) contributes one free element of \(G\)
per connected component, hence \(N^{\kappa(T)}\), and an inconsistent \(T\)
contributes \(0\).  \(\square\)

This lemma is the precise combinatorial bridge we should formalize before
talking about Tutte polynomials.  After it is proved, one can ask whether the
sum is a known specialization of a gain-graph Tutte polynomial, a
characteristic polynomial of an affine hyperplane arrangement, or a matroidal
invariant attached to the affine configuration.  But the proof should use
Lemma 4 as the primary object, because it is exact and directly tied to
`compatibleCountNat`.

### Rank-stratifying the exact formula

Lemma 4 gives more than an exact counting formula.  It tells us where every
term in the \(1/N\)-expansion comes from.

Let

\[
  H = \binom q2,
\]

and let

\[
  K(y)=\#\{1\le i<j\le q : y_i=y_j\}
\]

be the number of visible equality pairs.  Since \(\mathcal E(y)\) contains one
hidden-collision edge for every pair and one additional shifted-collision edge
exactly when \(y_i\ne y_j\), we have

\[
  |\mathcal E(y)| = 2H-K(y).
\]

For \(T\subseteq\mathcal E(y)\), define its graphic rank by

\[
  r(T)=q-\kappa(T),
\]

where \(\kappa(T)\) is the number of connected components of the underlying
labelled graph on all \(q\) vertices.  Lemma 4 can then be grouped by rank:

\[
  C(y)
  =
  \sum_{r=0}^{q}
    N^{q-r}
    \sum_{\substack{T\subseteq \mathcal E(y)\\ r(T)=r}}
      (-1)^{|T|}
      \mathbf 1_{\operatorname{consistent}(T)}.
\]

The first two ranks are explicit:

\[
  C(y)
  =
  N^q
  -
  (2H-K(y))N^{q-1}
  +
  B_2(y)N^{q-2}
  +
  O_q(N^{q-3}),
\]

where

\[
  B_2(y)
  =
  \sum_{\substack{T\subseteq \mathcal E(y)\\ r(T)=2}}
    (-1)^{|T|}
    \mathbf 1_{\operatorname{consistent}(T)}.
\]

This coefficient is already not a plain pair count.  It includes two-edge
forests, but it also includes consistent labelled cycles of graphic rank \(2\),
such as triangles.  This is the first place where a naive “count only the
number of forbidden pair events” approximation loses information.

The current Lean formalization has now separated the exact expansion into
named rank layers.  The reusable definitions and lemmas are:

- `collisionSubfamilyRankLayerInt`, the integer-valued contribution of a fixed
  graphic-rank layer;
- `compatibleCountNat_eq_sum_rankLayers`, the exact equality
  \(C(y)=\sum_r \text{rankLayer}_r(y)\);
- `collisionSubfamily_rankLayer_zero_eq_card_fun`, proving the rank-zero layer
  is exactly \(N^q\);
- `collisionSubfamily_rankLayer_one_eq_card_pow_mul_pairCoefficient`, proving
  the rank-one layer is exactly
  \(N^{q-1}\sum_{i<j}(-2+\mathbf 1[y_i=y_j])\);
- `collisionSubfamilyRankResidualBeyondOneInt`, the exact algebraic residual
  after subtracting the proved rank-zero and rank-one layers; and
- `compatibleCountNat_eq_rankZero_add_rankOne_add_residual`, the exact
  decomposition of \(C(y)\) into those two proved layers plus the residual.
- `collisionSubfamilyRankTailBeyondOneInt`, the explicit filtered sum over all
  rank layers except rank zero and rank one; and
- `collisionSubfamilyRankResidualBeyondOneInt_eq_tail`, proving that the
  residual is exactly this higher-rank filtered sum.
- `collisionSubfamilyRankTailBeyondOneInt_eq_sum_rank_ge_two`, rewriting the
  tail as the sum over all ranks \(r\) with \(r\ge2\), which is the form needed
  for rank-tail estimates.
- `collisionSubfamilyRankTailBeyondOneInt_eq_subfamily_sum_rank_ge_two`,
  flattening the same object to one inclusion-exclusion sum over collision
  subfamilies \(T\) with \(r(T)\ge2\).  This is the form that exposes the
  actual graph families to count or bound.
- `collisionSubfamily_card_ge_two_of_graphicRank_ge_two`, the first elementary
  size fact for the tail: any \(T\) in the tail contains at least two collision
  events.
- `collisionSubfamilyRankZeroSubfamilies_eq_singleton`, proving that the
  rank-\(0\) subfamily set is exactly \(\{\emptyset\}\).
- `collisionPairEvents_powerset_nonempty_card`, proving that each pair-local
  hidden/shifted collision family has exactly three nonempty subfamilies.
- `collisionSubfamilyRankOneSubfamilies_card`, proving that the global
  rank-\(1\) subfamily count is \(3\cdot |\operatorname{PairIndex}(q)|\).
- `collisionSubfamilyLowRankSubfamilies_card`, proving that the complete
  low-rank count is
  \[
    1 + 3\cdot |\operatorname{PairIndex}(q)|.
  \]
- `collisionSubfamilyRankTailSubfamilies_card_add_lowRank_card`, proving that
  the rank-tail subfamilies plus this fully counted low-rank part exhaust the
  full collision-event powerset.
- `compatibleCountNat_eq_rankZero_add_rankOne_add_tail`, the exact
  compatible-count decomposition stated directly with the higher-rank tail.
- `compatibleCountLowRankInt`, naming the rank-zero plus rank-one
  approximation \(C_{\mathrm{low}}(y)\).
- `compatibleCountNat_eq_lowRank_add_tail`, the split
  \[
    C(y)=C_{\mathrm{low}}(y)+\operatorname{tail}(y).
  \]
- `abs_collisionSubfamilyRankTailBeyondOneInt_le_sum_consistent_terms`, a
  triangle-inequality estimate that keeps the cycle-consistency filter.
- `abs_collisionSubfamilyRankTailBeyondOneInt_le_sum_rank_terms`, the coarser
  estimate that drops cycle consistency and bounds by the raw graphic-rank
  powers.
- `abs_collisionSubfamilyRankTailBeyondOneInt_le_tailCard_mul_card_pow`, the
  immediate consequence that the tail is at most the number of rank-tail
  subfamilies times \(N^{q-2}\).
- `collisionSubfamilyRankTailSubfamilies_card_mul_add_lowRank_mul`, the same
  exact low-rank/tail split after multiplying by a common factor.
- `abs_collisionSubfamilyRankTailBeyondOneInt_add_lowRank_mul_card_pow_le_powersetCard_mul_card_pow`,
  the subtraction-free sharpened inequality
  \[
    |\operatorname{tail}(y)|
      + \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr)N^{q-2}
    \le
      2^{q(q-1)}N^{q-2}.
  \]
- `abs_collisionSubfamilyRankTailBeyondOneInt_le_powersetCard_mul_card_pow`,
  an intentionally crude fallback replacing the rank-tail count by the full
  collision-event powerset size.
- `pairIndex_card_mul_two`, `collisionEvent_card`,
  `collisionEvent_card_eq_query_pair_twice`, and
  `collisionEvent_univ_powerset_card`, identifying the crude powerset factor as
  \(2^{q(q-1)}\).
- `pairCollisionFiberEquiv` and `pairCollisionFiber_card`, proving that for
  each fixed query pair \(p=\{i,j\}\), the number of visible tuples with
  \(y_i=y_j\) is exactly \(N^{q-1}\).
- `sum_pairCollisionIndicators_eq_pairIndex_card_mul_card_pow`, proving the
  aggregate low-rank collision count
  \[
    \sum_{y\in G^q}\sum_{p\in\operatorname{PairIndex}(q)}
      \mathbf{1}[y_{p_1}=y_{p_2}]
    =
    |\operatorname{PairIndex}(q)|N^{q-1}.
  \]
  This is the finite counting fact behind the \(B_q(N)\) term: under the
  ideal visible law, the expected number of visible coordinate collisions is
  \(|\operatorname{PairIndex}(q)|/N\).
- `uniformAverage_pairCollisionIndicators_eq_pairIndex_card_div_card`, the
  normalized form of the same statement:
  \[
    \frac{1}{N^q}
    \sum_{y\in G^q}\sum_{p\in\operatorname{PairIndex}(q)}
      \mathbf{1}[y_{p_1}=y_{p_2}]
    =
    \frac{|\operatorname{PairIndex}(q)|}{N}.
  \]
  This is the exact expectation statement that should feed the low-rank
  positive-part bound.
- `collisionSubfamilyRankTailSubfamilies_card_eq`, the subtraction form of the
  exact rank-tail cardinality:
  \[
    \#\{T:\operatorname{rank}(T)\ge 2\}
    =
    2^{q(q-1)}
      - \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr).
  \]
- `abs_collisionSubfamilyRankTailBeyondOneInt_le_explicitTailCard_mul_card_pow`,
  the corresponding closed pointwise estimate:
  \[
    |\operatorname{tail}(y)|
    \le
    \Bigl(2^{q(q-1)}
      - \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr)\Bigr)N^{q-2}.
  \]
- `abs_compatibleCountNat_sub_lowRank_le_explicitTailCard_mul_card_pow`,
  the same estimate in the count-error form needed by the visible positive-part
  proof:
  \[
    |C(y)-C_{\mathrm{low}}(y)|
    \le
    \Bigl(2^{q(q-1)}
      - \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr)\Bigr)N^{q-2}.
  \]
- `abs_collisionSubfamilyRankTailBeyondOneInt_le_queryEvent_pow_mul_card_pow`,
  the corresponding closed fallback estimate
  \[
    |\operatorname{tail}(y)| \le 2^{q(q-1)}N^{q-2}.
  \]

This is still intentionally weaker than a sharp tail estimate, but the formal
counting layer now knows exactly what it has already removed: the empty
subfamily and all pair-local rank-\(1\) subfamilies.  The first concrete
finite error term coming from this theorem is

\[
  E_{\mathrm{tail}}(q,N)
  =
  \Bigl(2^{q(q-1)}
      - \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr)\Bigr)
  \frac{N^{2q-2}}{((N)_q)^2}.
\]

Indeed, the normalized density contribution of the tail is
\[
  \frac{\operatorname{tail}(y)}{((N)_q)^2/N^q},
\]
so the pointwise estimate above gives
\[
  \left|
  \frac{\operatorname{tail}(y)}{((N)_q)^2/N^q}
  \right|
  \le
  E_{\mathrm{tail}}(q,N).
\]
Equivalently,
\[
  E_{\mathrm{tail}}(q,N)
  =
  \Bigl(2^{q(q-1)}
      - \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr)\Bigr)
  \frac{1}{N^2}
  \left(\frac{N^q}{(N)_q}\right)^2.
\]

This is a concrete finite \(q,N\) quantity, but it is not yet the desired
state-of-the-art remainder: it is obtained by triangle inequality over all
rank-tail subfamilies and therefore still has the exponential
\(2^{q(q-1)}\) combinatorial factor.

The concrete right-hand-side pieces are now named in Lean:

- `spatialReconstructionBound G q` is
  \[
    B_q(N)=|\operatorname{PairIndex}(q)|\frac{(N)_q}{N^q(N-1)^2}.
  \]
- `rankTailErrorBound G q` is the explicit \(E_{\mathrm{tail}}(q,N)\) above.
- `lowRankCollisionFiberResidualErrorBound G q` is the exact finite residual
  by which the low-rank positive part exceeds the spatial term:
  \[
    R_{\mathrm{low}}(q,N)
    =
    \left(
      \frac{1}{N^q}
      \sum_{k=0}^{|\operatorname{PairIndex}(q)|}
        \#\{y:K(y)=k\}\,(f_{q,N}(k)-1)_+
      -
      B_q(N)
    \right)_+ .
  \]
  This is deliberately not a new asymptotic estimate; it is the exact
  one-dimensional occupancy residual left after the LM20/orbit reduction.
- `finiteOrbitErrorBound G q` packages the current unconditional finite error
  term
  \[
    E_{\mathrm{orbit}}(q,N)=R_{\mathrm{low}}(q,N)+E_{\mathrm{tail}}(q,N).
  \]
- `rankTailAverageErrorBound G q hq0` keeps the exact higher-rank gain-graph
  tail instead of replacing it pointwise by the powerset-cardinality bound:
  \[
    E_{\mathrm{tail}}^{\mathrm{avg}}(q,N)
    =
    \mathbb E_{y\leftarrow G^q}
    \frac{
      |\operatorname{tail}(y)|
    }{
      ((N)_q)^2/N^q
    }.
  \]
  The Lean theorem
  `compatibleCountDensityTailPointwise_eq_rankTail` proves the pointwise
  identity
  \[
    |\rho(y)-\rho_{\mathrm{low}}(y)|
    =
    \frac{|\operatorname{tail}(y)|}{((N)_q)^2/N^q}.
  \]
  Consequently,
  `compatibleCountAverageTail_le_rankTailAverageErrorBound` and
  `visibleStatDistLowRankTailBridge_of_rankTailAverage` replace the old
  pointwise tail estimate by the exact average absolute tail.
  The comparison theorem
  `rankTailAverageErrorBound_le_rankTailErrorBound` proves that this exact
  average tail is never worse than the previous closed-form powerset tail in
  the regime \(2\le q\le N\):
  \[
    E_{\mathrm{tail}}^{\mathrm{avg}}(q,N)
    \le
    E_{\mathrm{tail}}(q,N).
  \]
- The old average tail still includes graphic rank \(2\).  The next split is
  now formalized:
  `collisionSubfamilyRankTailBeyondOneInt_eq_rankTwo_add_tailBeyondTwo`
  proves
  \[
    \operatorname{tail}_{\ge 2}(y)
    =
    \operatorname{layer}_2(y)+\operatorname{tail}_{\ge 3}(y).
  \]
  Here `collisionSubfamilyRankLayerInt ... (collisionSubfamilyGraphicRankTwoFin q hq2)`
  is the rank-two layer, and `collisionSubfamilyRankTailBeyondTwoInt` is the
  sum of all rank layers with numeric rank at least three.
- `rankTwoLayerAverageErrorBound G q hq2` names the exact normalized average
  absolute rank-two contribution:
  \[
    E_2^{\mathrm{avg}}(q,N)
    =
    \mathbb E_{y\leftarrow G^q}
    \frac{|\operatorname{layer}_2(y)|}{((N)_q)^2/N^q}.
  \]
- `rankTailBeyondTwoAverageErrorBound G q` names the exact normalized average
  absolute contribution from graphic ranks at least three:
  \[
    E_{\ge 3}^{\mathrm{avg}}(q,N)
    =
    \mathbb E_{y\leftarrow G^q}
    \frac{|\operatorname{tail}_{\ge 3}(y)|}{((N)_q)^2/N^q}.
  \]
  The comparison theorem
  `rankTailAverageErrorBound_le_rankTwo_add_tailBeyondTwoAverage` proves
  \[
    E_{\mathrm{tail}}^{\mathrm{avg}}(q,N)
    \le
    E_2^{\mathrm{avg}}(q,N)+E_{\ge 3}^{\mathrm{avg}}(q,N).
  \]
  This is intentionally a theorem boundary, not yet the final estimate.  It
  isolates the rank-two layer, which the peer analysis predicts is still
  equality-pattern/universal, from the genuinely affine-dependent rank
  \(3+\) gain-graph tail.
- `rankTailBeyondTwoErrorBound G q` is the closed pointwise fallback for the
  rank \(3+\) tail:
  \[
    E_{\ge 3}(q,N)
    =
    2^{q(q-1)}
    \frac{N^{2q-3}}{((N)_q)^2}.
  \]
  This is obtained by the theorem
  `abs_collisionSubfamilyRankTailBeyondTwoInt_le_powersetCard_mul_card_pow`,
  which proves the count-scale estimate
  \[
    |\operatorname{tail}_{\ge 3}(y)|
    \le
    2^{q(q-1)}N^{q-3}.
  \]
  The normalized pointwise theorem
  `rankTailBeyondTwoPointwise_le_rankTailBeyondTwoErrorBound`, followed by
  `rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound`, gives
  \[
    E_{\ge 3}^{\mathrm{avg}}(q,N)
    \le
    E_{\ge 3}(q,N).
  \]
  This is not cancellation-aware yet, but it is already one power of \(N\)
  sharper than applying the old rank \(2+\) pointwise fallback to the whole
  tail.
- `finiteOrbitAverageTailErrorBound G q hq0` is the sharper current finite
  error term
  \[
    E_{\mathrm{orbit}}^{\mathrm{avg}}(q,N)
    =
    R_{\mathrm{low}}(q,N)+E_{\mathrm{tail}}^{\mathrm{avg}}(q,N).
  \]
  `finiteOrbitAverageTailErrorBound_le_finiteOrbitErrorBound` lifts the same
  comparison to the full finite error term:
  \[
    E_{\mathrm{orbit}}^{\mathrm{avg}}(q,N)
    \le
    E_{\mathrm{orbit}}(q,N).
  \]
- `finiteOrbitRankTwoTailBeyondTwoAverageErrorBound G q hq2` packages this
  rank split at the finite-error level:
  \[
    E_{\mathrm{orbit}}^{2,\ge 3}(q,N)
    =
    R_{\mathrm{low}}(q,N)
    +
    E_2^{\mathrm{avg}}(q,N)
    +
    E_{\ge 3}^{\mathrm{avg}}(q,N).
  \]
  `finiteOrbitAverageTailErrorBound_le_rankTwoTailBeyondTwoAverageErrorBound`
  proves
  \[
    E_{\mathrm{orbit}}^{\mathrm{avg}}(q,N)
    \le
    E_{\mathrm{orbit}}^{2,\ge 3}(q,N).
  \]
- `finiteOrbitRankTwoClosedBeyondTwoErrorBound G q hq2` replaces only the
  rank \(3+\) average by its closed fallback:
  \[
    E_{\mathrm{orbit}}^{2,\ge 3\mathrm{cl}}(q,N)
    =
    R_{\mathrm{low}}(q,N)
    +
    E_2^{\mathrm{avg}}(q,N)
    +
    E_{\ge 3}(q,N).
  \]
  The theorem
  `finiteOrbitAverageTailErrorBound_le_rankTwoClosedBeyondTwoErrorBound`
  proves
  \[
    E_{\mathrm{orbit}}^{\mathrm{avg}}(q,N)
    \le
    E_{\mathrm{orbit}}^{2,\ge 3\mathrm{cl}}(q,N).
  \]
- `lowRankCollisionMaxResidualErrorBound G q` is a closed-form fallback for
  the exact occupancy residual.  It uses only the endpoint value of the scalar
  low-rank density on the finite support \(0\le K(y)\le
  |\operatorname{PairIndex}(q)|\):
  \[
    R_{\mathrm{low}}^{\max}(q,N)
    =
    \left(
      \left(
        f_{q,N}\bigl(|\operatorname{PairIndex}(q)|\bigr)-1
      \right)_+
      -
      B_q(N)
    \right)_+ .
  \]
  The endpoint value is itself closed form:
  \[
    f_{q,N}\bigl(|\operatorname{PairIndex}(q)|\bigr)
    =
    \operatorname{slack}_{q,N}
    \left(
      1-\frac{|\operatorname{PairIndex}(q)|}{N}
    \right).
  \]
  This identity is formalized as
  `lowRankDensityFromCollisionCountReal_pairIndex_card_eq`, and
  `lowRankCollisionMaxResidualErrorBound_eq_slack` rewrites
  \(R_{\mathrm{low}}^{\max}\) using exactly this RHS.
  The Lean theorem
  `lowRankDensityFromCollisionCountReal_le_pairIndex_card` proves that
  \(f_{q,N}(k)\) is monotone in \(k\) on this finite support, and
  `compatibleCountLowRankPositiveErrorReal_le_pairIndex_card_positivePart`
  lifts this to
  \[
    \operatorname{PE}_{\mathrm{low}}(q,N)
    \le
    \left(
      f_{q,N}\bigl(|\operatorname{PairIndex}(q)|\bigr)-1
    \right)_+ .
  \]
  Consequently
  `lowRankCollisionFiberResidualErrorBound_le_lowRankCollisionMaxResidualErrorBound`
  proves
  \[
    R_{\mathrm{low}}(q,N)
    \le
    R_{\mathrm{low}}^{\max}(q,N).
  \]
  This bound is intentionally weaker than the exact occupancy-fiber residual,
  but it is useful because it contains no fiber-cardinality distribution.
- `finiteOrbitAverageTailMaxResidualErrorBound G q hq0` packages the closed
  fallback residual together with the exact average higher-rank tail:
  \[
    E_{\mathrm{orbit}}^{\mathrm{avg},\max}(q,N)
    =
    R_{\mathrm{low}}^{\max}(q,N)
    +
    E_{\mathrm{tail}}^{\mathrm{avg}}(q,N).
  \]
  The comparison theorem
  `finiteOrbitAverageTailErrorBound_le_finiteOrbitAverageTailMaxResidualErrorBound`
  records
  \[
    E_{\mathrm{orbit}}^{\mathrm{avg}}(q,N)
    \le
    E_{\mathrm{orbit}}^{\mathrm{avg},\max}(q,N).
  \]
- `finiteOrbitMaxResidualErrorBound G q` is the fully closed current fallback:
  \[
    E_{\mathrm{orbit}}^{\max}(q,N)
    =
    R_{\mathrm{low}}^{\max}(q,N)+E_{\mathrm{tail}}(q,N).
  \]
  Both summands are explicit finite-\(q,N\) expressions: the low-rank term uses
  only the endpoint \(K=|\operatorname{PairIndex}(q)|\), and the rank-tail term
  is the existing pointwise powerset-cardinality estimate.  The comparison
  theorem `finiteOrbitErrorBound_le_finiteOrbitMaxResidualErrorBound` proves
  \[
    E_{\mathrm{orbit}}(q,N)
    \le
    E_{\mathrm{orbit}}^{\max}(q,N).
  \]
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound`
  is the RS-style endpoint: once the visible/orbit proof establishes
  \[
    \operatorname{visibleStatDist}_q
    \le
    B_q(N)+E_{\mathrm{tail}}(q,N),
  \]
  the unrestricted adaptive XoP advantage satisfies the same bound by the
  already-proved LM20/adaptive bridge.
- `compatibleCountLowRankDensityReal G q y` is the signed real-valued density
  ratio obtained from the rank-zero plus rank-one approximation
  \(C_{\mathrm{low}}(y)\).
- `pairCollisionCountInt G q y` and
  `pairCoefficient_sum_eq_pairCollisionCountInt_sub_two_pairIndex` expose the
  rank-one coefficient as
  \[
    \sum_{i<j}(-2+\mathbf 1[y_i=y_j])
    =
    \#\{i<j:y_i=y_j\}-2|\operatorname{PairIndex}(q)|.
  \]
  Consequently,
  `compatibleCountLowRankInt_eq_card_pow_add_collisionCount` proves
  \[
    C_{\mathrm{low}}(y)
    =
    N^q+
    N^{q-1}\bigl(\#\{i<j:y_i=y_j\}-2|\operatorname{PairIndex}(q)|\bigr).
  \]
  This is the formal reason the low-rank layer is a one-dimensional problem in
  the visible collision count.
- `lowRankDensityFromCollisionCountReal G q k` packages that one-dimensional
  density as a scalar function of \(k\), while
  `lowRankDensityFromCollisionCountReal_eq_slack_mul` rewrites it as
  \[
    f_{q,N}(k)
    =
    \operatorname{slack}_{q,N}
    \left(1+\frac{k-2|\operatorname{PairIndex}(q)|}{N}\right),
  \]
  where
  \[
    \operatorname{slack}_{q,N}=\frac{N^q}{(N)_q^2/N^q}.
  \]
  `compatibleCountLowRankDensityReal_eq_collisionCountScalar` and
  `compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage`
  rewrite the low-rank positive error as
  \[
    \mathbb E_{y\leftarrow G^q}
      \left(
        f_{q,N}\bigl(\#\{i<j:y_i=y_j\}\bigr)-1
      \right)_+ .
  \]
  The remaining low-rank proof is therefore a scalar tail/moment estimate for
  the collision count \(K(y)\).
- `pairCollisionCountNat G q y` is the natural-valued version of the same
  collision count, and `pairCollisionCountNat_le_pairIndex_card` proves the
  finite support bound
  \[
    0\le K(y)\le |\operatorname{PairIndex}(q)|.
  \]
  The cast lemmas `pairCollisionCountInt_eq_pairCollisionCountNat` and
  `pairCollisionCountReal_eq_pairCollisionCountNat` connect this natural
  occupancy variable to the integer and real forms used by the low-rank
  density and by the spatial bound.
- `pairCollisionCountFiberCard G q k` names the occupancy fiber size
  \[
    \#\{y\in G^q:K(y)=k\}.
  \]
  `uniformAverage_of_pairCollisionCountNat` proves the exact finite
  one-dimensional reduction
  \[
    \mathbb E_{y\leftarrow G^q}F(K(y))
    =
    \frac{1}{N^q}
    \sum_{k=0}^{|\operatorname{PairIndex}(q)|}
      \#\{y:K(y)=k\}\,F(k).
  \]
  Specializing this identity gives
  `compatibleCountLowRankPositiveErrorReal_eq_collisionCountFiberSum`:
  \[
    \operatorname{PE}_{\mathrm{low}}(q,N)
    =
    \frac{1}{N^q}
    \sum_{k=0}^{|\operatorname{PairIndex}(q)|}
      \#\{y:K(y)=k\}\,
      (f_{q,N}(k)-1)_+ .
  \]
  The same fiber API also records the first moment:
  `pairCollisionCountFiberCard_weightedAverage_eq_pairIndex_card_div_card`
  proves
  \[
    \frac{1}{N^q}
    \sum_{k=0}^{|\operatorname{PairIndex}(q)|}
      \#\{y:K(y)=k\}\,k
    =
    \frac{|\operatorname{PairIndex}(q)|}{N}.
  \]
  Thus the remaining fiber inequality is exactly the question of bounding the
  positive part of the affine scalar \(f_{q,N}(K)-1\) by the first moment of the
  occupancy distribution.
- `CompatibleCountLowRankScalarCollisionBound G q` names that scalar
  tail/moment estimate directly, and
  `compatibleCountLowRankAverageCollisionBound_of_scalarCollision` proves that
  it implies the average collision-envelope obligation.
- `CompatibleCountLowRankCollisionFiberBound G q` is the same remaining
  low-rank estimate in occupancy-fiber form.  The bridge theorem
  `compatibleCountLowRankScalarCollisionBound_of_fiberBound` proves that this
  finite sum implies the scalar collision-count obligation.  The current
  strongest endpoint therefore also has a fiber version,
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_collisionFiber_countTail`.
- `compatibleCountLowRankPositiveErrorReal G q` is its positive part under the
  ideal visible law:
  \[
    \mathbb E_{y\leftarrow G^q}
      \bigl(\rho_{\mathrm{low}}(y)-1\bigr)_+ .
  \]
- `CompatibleCountLowRankPositiveErrorBound G q` is the named obligation
  \[
    \operatorname{PE}_{\mathrm{low}}(q,N)\le B_q(N).
  \]
- `pairCollisionCountReal G q y` is the visible number of equal-coordinate
  pairs in a transcript \(y\), and
  `uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card` proves
  its exact ideal average:
  \[
    \mathbb E_{y\leftarrow G^q}
      \#\{i<j:y_i=y_j\}
    =
    \frac{|\operatorname{PairIndex}(q)|}{N}.
  \]
- `CompatibleCountLowRankPointwiseCollisionBound G q` names the last low-rank
  pointwise collision-envelope candidate:
  \[
    (\rho_{\mathrm{low}}(y)-1)_+
    \le
    \frac{(N)_q}{N^{q-1}(N-1)^2}
    \#\{i<j:y_i=y_j\}.
  \]
  `compatibleCountLowRankPositiveErrorBound_of_pointwiseCollision` proves that
  this pointwise envelope implies
  `CompatibleCountLowRankPositiveErrorBound G q`, using the average collision
  count above.  This is a valid sufficient condition, but it is too strong as
  the intended final route: high-collision transcripts can exceed the pointwise
  line while still being harmless after averaging.
- `CompatibleCountLowRankAverageCollisionBound G q` is therefore the correct
  remaining low-rank target:
  \[
    \operatorname{PE}_{\mathrm{low}}(q,N)
    \le
    \frac{(N)_q}{N^{q-1}(N-1)^2}
    \mathbb E_{y\leftarrow G^q}\#\{i<j:y_i=y_j\}.
  \]
  `compatibleCountLowRankPositiveErrorBound_of_averageCollision` proves that
  this average envelope implies
  `CompatibleCountLowRankPositiveErrorBound G q`.
- `VisibleStatDistLowRankTailBridge G q` is the named obligation
  \[
    \operatorname{visibleStatDist}_q
    \le
    \operatorname{PE}_{\mathrm{low}}(q,N)+E_{\mathrm{tail}}(q,N).
  \]
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank`
  proves the desired RS-style adaptive endpoint from exactly these two
  obligations.  This is now the formal theorem boundary: the old broad
  `hvisible` assumption has been split into the low-rank positive-part bound
  and the low-rank/tail comparison.
- `compatibleCountTruePositiveErrorReal G q` is the true density positive
  error over `ℝ`, and
  `visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal` proves that
  this is exactly the visible statistical distance after casting to `ℝ`.
- `max_sub_one_le_max_sub_one_add_abs_sub` is the pointwise positive-part
  inequality
  \[
    (a-1)_+ \le (b-1)_+ + |a-b|.
  \]
- `compatibleCountTruePositiveErrorReal_le_lowRank_add_average_abs_diff`
  applies that inequality under the uniform visible average:
  \[
    \operatorname{PE}_{\mathrm{true}}
    \le
    \operatorname{PE}_{\mathrm{low}}
    +
    \mathbb E_{y\leftarrow G^q}
      |\rho(y)-\rho_{\mathrm{low}}(y)|.
  \]
- `CompatibleCountAverageTailBound G q` names the remaining average density-tail
  obligation, and `compatibleCountAverageTailBound_of_pointwise` proves it from
  a pointwise density-tail bound.  Consequently,
  `visibleStatDistLowRankTailBridge_of_averageTail` proves
  `VisibleStatDistLowRankTailBridge G q` from the average-tail obligation.
- `compatibleCountDensityTailPointwise_le_rankTailErrorBound` performs that
  normalizer cast in the nontrivial regime \(2\le q\): the integer tail bound
  \[
    |C(y)-C_{\mathrm{low}}(y)|
    \le
    T_q N^{q-2}
  \]
  becomes
  \[
    |\rho(y)-\rho_{\mathrm{low}}(y)|
    \le
    \frac{T_q N^{2q-2}}{((N)_q)^2}
    =
    E_{\mathrm{tail}}(q,N).
  \]
- `compatibleCountAverageTailBound_of_count_tail` and
  `visibleStatDistLowRankTailBridge_of_count_tail` now close the entire
  tail side from the existing count-tail theorem.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank_countTail`
  is the strongest current formal endpoint: for \(2\le q\le N\), the adaptive
  XoP advantage is bounded by \(B_q(N)+E_{\mathrm{tail}}(q,N)\) assuming only
  the low-rank positive-error obligation
  `CompatibleCountLowRankPositiveErrorBound G q`.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_pointwiseCollision_countTail`
  gives the stronger sufficient pointwise route: it assumes only the pointwise
  low-rank collision-envelope inequality
  `CompatibleCountLowRankPointwiseCollisionBound G q`.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_averageCollision_countTail`
  is the current best theorem boundary: for \(2\le q\le N\), it reduces the
  adaptive \(B_q(N)+E_{\mathrm{tail}}(q,N)\) endpoint to the average low-rank
  collision-envelope obligation
  `CompatibleCountLowRankAverageCollisionBound G q`.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_scalarCollision_countTail`
  is the same endpoint exposed at the scalar level: proving
  `CompatibleCountLowRankScalarCollisionBound G q` is now enough.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_collisionFiber_countTail`
  pushes the boundary one step further down to the occupancy distribution of
  \(K(y)\).  Proving the one-dimensional fiber inequality
  `CompatibleCountLowRankCollisionFiberBound G q` is enough for the same
  adaptive \(B_q(N)+E_{\mathrm{tail}}(q,N)\) endpoint.
- `compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual`
  proves unconditionally that
  \[
    \operatorname{PE}_{\mathrm{low}}(q,N)
    \le
    B_q(N)+R_{\mathrm{low}}(q,N).
  \]
  Together with the already-formalized count-tail theorem this gives
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_fiberResidual_add_rankTailErrorBound`:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+R_{\mathrm{low}}(q,N)+E_{\mathrm{tail}}(q,N).
  \]
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitErrorBound`
  is the same theorem in the compact \(B_q(N)+E(q,N)\) form:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{orbit}}(q,N).
  \]
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitMaxResidualErrorBound`
  is the current fully closed \(B_q(N)+E(q,N)\) fallback:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{orbit}}^{\max}(q,N).
  \]
  This is the most concrete bound presently formalized: it has no occupancy
  fiber sum and no transcript-average tail term.  It is deliberately weaker
  than the exact-residual and average-tail endpoints below.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailErrorBound`
  is the stronger version using the exact average rank-tail error:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{orbit}}^{\mathrm{avg}}(q,N).
  \]
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoTailBeyondTwoAverageErrorBound`
  is the endpoint after splitting the average tail into rank two and
  rank \(3+\):
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{orbit}}^{2,\ge 3}(q,N).
  \]
  This is the current best structural theorem boundary for sharpening the
  gain-graph tail: close \(E_2^{\mathrm{avg}}\) using the rank-two
  equality-pattern calculation, then close \(E_{\ge 3}^{\mathrm{avg}}\) using
  the one-power-better rank \(3+\) cardinality/cancellation estimate.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoClosedBeyondTwoErrorBound`
  is the same endpoint with the rank \(3+\) average replaced by its closed
  fallback:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{orbit}}^{2,\ge 3\mathrm{cl}}(q,N).
  \]
  Here
  \[
    E_{\ge3}^{\mathrm{cl}}(q,N)
    =
    2^{q(q-1)}\frac{N^{2q-3}}{((N)_q)^2}.
  \]
- The proof now also has a sharper rank-two-adjusted comparison point.  The
  Lean definition `compatibleCountRankTwoDensityReal G q hq2 y` is
  \[
    \rho_{\le 2}(y)
    =
    \frac{C_{\mathrm{low}}(y)+\operatorname{layer}_2(y)}
         {((N)_q)^2/N^q},
  \]
  with the rank-two layer kept as a signed inclusion-exclusion contribution.
  The theorem `compatibleCountDensityTailPointwise_eq_tailBeyondTwo` proves the
  exact identity
  \[
    |\rho(y)-\rho_{\le 2}(y)|
    =
    \frac{|\operatorname{tail}_{\ge 3}(y)|}{((N)_q)^2/N^q}.
  \]
  This is a genuine improvement over the previous bridge: the RHS no longer
  contains \(|\operatorname{layer}_2(y)|\).
- `rankTwoPositiveResidualErrorBound G q hq2` names the remaining signed
  rank-two positive-part residual
  \[
    R_{\le2}(q,N)
    =
    \left(
      \mathbb E_{y\leftarrow U(G^q)}
        [(\rho_{\le2}(y)-1)_+]
      -
      B_q(N)
    \right)_+.
  \]
  The endpoint
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveTailBeyondTwoAverageErrorBound`
  proves
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+R_{\le2}(q,N)+E_{\ge3}^{\mathrm{avg}}(q,N).
  \]
  The closed fallback
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveClosedBeyondTwoErrorBound`
  proves
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+R_{\le2}(q,N)+E_{\ge3}^{\mathrm{cl}}(q,N).
  \]
  This is the sharpest formal theorem boundary in residual form: the old
  \(N^{-2}\)-scale absolute rank-two slack \(E_2^{\mathrm{cl}}\) has been
  removed and replaced by the exact signed residual \(R_{\le2}\).  The
  quadratic-positive endpoint recorded below is the more algebraic sufficient bound
  \[
    R_{\le2}(q,N)
    \le
    R_{\mathrm{low}}(q,N)+Q_2^+(q,N),
  \]
  which avoids re-opening the rank-two gain-graph layer.  The remaining
  mathematical task is now sharper: prove a joint sign/cancellation estimate
  for \(R_{\mathrm{low}}+Q_2^+\), or prove the exact residual
  \(R_{\le2}\) directly, at \(O(q^4/N^4)\) scale.
  Lean now also proves the comparison theorem
  `finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound_le_rankTwoTailBeyondTwoAverageErrorBound`:
  \[
    R_{\le2}(q,N)+E_{\ge3}^{\mathrm{avg}}(q,N)
    \le
    R_{\mathrm{low}}(q,N)+E_2^{\mathrm{avg}}(q,N)
      +E_{\ge3}^{\mathrm{avg}}(q,N).
  \]
  Its pointwise input is
  `compatibleCountRankTwoPositiveErrorReal_le_lowRank_add_rankTwoLayerAverage`,
  the positive-part inequality
  \[
    (\rho_{\le2}(y)-1)_+
    \le
    (\rho_{\le1}(y)-1)_+
    +
    \left|\rho_{\le2}(y)-\rho_{\le1}(y)\right|.
  \]
  Thus the rank-two-positive endpoint is now formally certified to be no worse
  than the older termwise rank-two split while exposing the exact sign-control
  residual needed for the paper-grade theorem.
- `rankTwoSubfamilyCount q` is the finite combinatorial quantity
  \[
    \#\{T\subseteq \mathcal E_q:\operatorname{rank}(T)=2\}.
  \]
  The theorem `rankTwoLayerAverageErrorBound_le_rankTwoLayerErrorBound`
  closes the exact rank-two average by the pointwise fallback
  \[
    E_2^{\mathrm{cl}}(q,N)
    =
    \#\{T:\operatorname{rank}(T)=2\}
    \frac{N^{2q-2}}{((N)_q)^2}.
  \]
- The next rank-two target is now named as an equality-pattern identity rather
  than an absolute-value estimate.  The Lean definitions
  `pairCollisionCoefficientInt`, `rankTwoForestCoefficientInt`,
  `rankTwoTriangleCorrectionInt`, and `rankTwoEqualityCoefficientInt` encode
  the signed rank-two coefficient
  \[
    C_2^{=}(y)
    =
    \sum_{\{p,r\}\subseteq \operatorname{PairIndex}(q)}
      c_p(y)c_r(y)
    +
    \sum_{\{i,j,k\}\subseteq [q]}
      \left(-2+\mathbf 1[y_i=y_j=y_k]\right),
  \]
  where
  \[
    c_p(y)=-2+\mathbf 1[y_{p_1}=y_{p_2}].
  \]
  `RankTwoEqualityPatternIdentity G q` is the formal next theorem:
  \[
    \operatorname{layer}_2(y)=N^{q-2} C_2^{=}(y).
  \]
  This is the cancellation/sign-control statement needed to replace
  \(E_2^{\mathrm{cl}}\).  It says that graphic rank two is governed by
  equality patterns only: two-edge forests multiply the pair-local
  coefficients, and three-edge triangles contribute the local correction
  \(-2+\mathbf 1[y_i=y_j=y_k]\).  Affine value-dependence is therefore pushed
  to rank \(3+\).
- The rank-two target has now been split into a field-size-free coefficient
  problem.  The definition `rankTwoAlternatingCoefficientInt G q y` is
  \[
    A_2(y)
    =
    \sum_{\substack{T\subseteq \mathcal E_q\\ \operatorname{rank}(T)=2}}
      \mathbf 1[\operatorname{balanced}_y(T)](-1)^{|T|}.
  \]
  The theorem
  `collisionSubfamily_rankTwoLayer_eq_card_pow_mul_alternatingCoefficient`
  proves
  \[
    \operatorname{layer}_2(y)=N^{q-2}A_2(y).
  \]
  The remaining coefficient-level target is
  `RankTwoAlternatingCoefficientIdentity G q`:
  \[
    A_2(y)=C_2^{=}(y).
  \]
  The theorem `RankTwoEqualityPatternIdentity.of_alternatingCoefficient`
  proves that this coefficient identity implies the original scaled
  `RankTwoEqualityPatternIdentity G q`.  Thus the rank-two cancellation proof
  no longer has to reason about the normalizing power of \(N\); it is purely a
  classification of graphic-rank-two gain subgraphs into two-pair forest terms
  and three-vertex triangle corrections.
- The first support-level API for that classification is now formalized.
  `collisionSubfamilyPairSupport q T` forgets the hidden/shifted kind and keeps
  only the query pairs touched by a collision-event subfamily.  The proved
  lemmas
  `mem_collisionSubfamilyPairSupport_iff`,
  `collisionSubfamily_subset_biUnion_pairSupport`, and
  `collisionSubfamilyPairSupport_card_eq_one_of_graphicRank_eq_one` establish
  the rank-one sanity check:
  \[
    \operatorname{rank}(T)=1
    \quad\Longrightarrow\quad
    |\operatorname{pairSupport}(T)|=1.
  \]
  The lemma
  `collisionSubfamilyPairSupport_two_le_of_graphicRank_eq_two` proves the
  corresponding lower bound for rank two:
  \[
    \operatorname{rank}(T)=2
    \quad\Longrightarrow\quad
    2\le |\operatorname{pairSupport}(T)|.
  \]
  The next rank-two classification should add the upper bound and sharpen this
  to
  \[
    \operatorname{rank}(T)=2
    \quad\Longrightarrow\quad
    |\operatorname{pairSupport}(T)|=2
      \ \text{or}\
    |\operatorname{pairSupport}(T)|=3,
  \]
  where the two cases correspond to the forest product and triangle correction
  in \(C_2^{=}(y)\).
- Before proving that upper bound outright, the coefficient has been split
  exactly by support size.  The definitions
  `rankTwoAlternatingCoefficientSupportCardEqInt` and
  `rankTwoAlternatingCoefficientSupportCardGeInt` isolate the support-cardinality
  pieces, and
  `rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_add_ge_four`
  proves
  \[
    A_2(y)
    =
    A_{2,|\mathrm{supp}|=2}(y)
    +A_{2,|\mathrm{supp}|=3}(y)
    +A_{2,|\mathrm{supp}|\ge4}(y).
  \]
  This uses the formal lower bound \(2\le|\operatorname{pairSupport}(T)|\).
  The remaining upper-bound theorem is now exactly the statement that the
  \(|\mathrm{supp}|\ge4\) summand is zero.
- That remaining statement has been isolated as a graph-only obligation.
  `RankTwoPairSupportUpperBound q` asserts
  \[
    \operatorname{rank}(T)=2
    \quad\Longrightarrow\quad
    |\operatorname{pairSupport}(T)|\le 3
  \]
  for every collision-event subfamily \(T\).  It is deliberately independent
  of the output group \(G\), transcript \(y\), and cycle-consistency labels.
  Under this obligation,
  `rankTwoAlternatingCoefficientSupportCardGe_four_eq_zero_of_pairSupportUpperBound`
  proves
  \[
    A_{2,|\mathrm{supp}|\ge4}(y)=0,
  \]
  and
  `rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_of_pairSupportUpperBound`
  reduces the rank-two coefficient to the two structurally meaningful cases:
  \[
    A_2(y)
    =
    A_{2,|\mathrm{supp}|=2}(y)
    +A_{2,|\mathrm{supp}|=3}(y).
  \]
  The exact final assembly is also formalized.  The predicates
  `RankTwoSupportCardTwoCoefficientIdentity G q` and
  `RankTwoSupportCardThreeCoefficientIdentity G q` state that these two pieces
  are respectively the forest product and triangle-correction terms.  The
  theorem `RankTwoAlternatingCoefficientIdentity.of_supportCardIdentities`
  proves that
  \[
    \texttt{RankTwoPairSupportUpperBound}\ q
    \quad+\quad
    A_{2,|\mathrm{supp}|=2}=C_{2,\mathrm{forest}}^{=}
    \quad+\quad
    A_{2,|\mathrm{supp}|=3}=C_{2,\mathrm{triangle}}^{=}
  \]
  implies the coefficient-level rank-two identity
  `RankTwoAlternatingCoefficientIdentity G q`.  This is a real narrowing of
  the rank-two frontier: the remaining proof is now three small structural
  facts rather than a monolithic rank-two cancellation statement.
- The graph side has two new support-to-component bridge lemmas.
  `collisionSubfamilyPairSupport_connected` proves that every touched query
  pair has connected endpoints in the support graph, and
  `collisionSubfamilyPairSupport_component_eq` records the same fact in the
  component quotient.  These are the first reusable ingredients for proving
  the pure graph endpoint `RankTwoPairSupportUpperBound q`.
  The definitions `collisionSubfamilyComponentVertexSet` and
  `collisionSubfamilyComponentPairSet`, together with
  `collisionSubfamilyPairSupport_subset_biUnion_componentPairSet`, refine this
  into a block statement:
  \[
    \operatorname{pairSupport}(T)
    \subseteq
    \bigcup_{\mathcal C\in \pi_0(T)}
      \{\{i,j\}: i,j\in \mathcal C\}.
  \]
  The next pure graph move is therefore a finite partition/cardinality
  argument: rank \(2\) means the component-size excess
  \(\sum_{\mathcal C}(|\mathcal C|-1)\) is \(2\), and the largest possible
  number of component-internal query pairs is then \(3\).
  This has been named formally as `RankTwoComponentPairUnionBound q`, and
  `RankTwoPairSupportUpperBound.of_componentPairUnionBound` proves that this
  component-union cardinality statement implies the original pair-support
  upper bound.
  One half of the component-union proof is now discharged:
  `collisionSubfamilyComponentPairSet_card_le_choose` proves
  \[
    |\{\{i,j\}: i,j\in \mathcal C\}|
    \le
    \binom{|\mathcal C|}{2}
  \]
  for each component \(\mathcal C\), by injecting each internal `PairIndex`
  into the two-element endpoint subset.  The theorem
  `componentPairSetChooseBound` packages this local fact, and
  `RankTwoComponentPairUnionBound.of_componentChooseSumBound` reduces the
  whole endpoint to the remaining component-size arithmetic obligation
  `RankTwoComponentChooseSumBound q`:
  \[
    \operatorname{rank}(T)=2
    \quad\Longrightarrow\quad
    \sum_{\mathcal C\in\pi_0(T)}
      \binom{|\mathcal C|}{2}
    \le 3.
  \]
  The component partition facts needed for this arithmetic step are now
  formalized:
  `collisionSubfamilyComponentVertexSet_nonempty`,
  `collisionSubfamilyComponentVertexSet_pairwiseDisjoint`, and
  `collisionSubfamilyComponentVertexSet_biUnion_eq_univ` show that component
  vertex sets form a genuine finite partition of the query coordinates.
  Consequently `sum_componentVertexSet_card_eq_query` proves
  \[
    \sum_{\mathcal C\in\pi_0(T)} |\mathcal C|=q,
  \]
  and `sum_componentVertexSet_card_sub_one_eq_graphicRank` proves the exact
  excess identity
  \[
    \sum_{\mathcal C\in\pi_0(T)} (|\mathcal C|-1)
    =
    \operatorname{rank}(T).
  \]
  The component arithmetic is now discharged.  The pointwise Nat lemma
  `two_mul_choose_two_le_three_mul_sub_one_of_sub_one_le_two` proves
  \[
    n-1\le 2
    \quad\Longrightarrow\quad
    2\binom n2\le 3(n-1),
  \]
  and `sum_choose_two_le_three_of_sum_sub_one_eq_two` sums this inequality
  over any finite family whose total excess is \(2\).  Instantiating this
  with component vertex-set cardinalities gives
  `componentChooseSumBoundFromExcessTwo q`, then
  `rankTwoComponentChooseSumBound q`, `rankTwoComponentPairUnionBound q`,
  and finally the unconditional graph endpoint
  `rankTwoPairSupportUpperBound q`:
  \[
    \operatorname{rank}(T)=2
    \quad\Longrightarrow\quad
    |\operatorname{pairSupport}(T)|\le 3.
  \]
  Consequently
  `collisionSubfamilyPairSupport_card_eq_two_or_three_of_graphicRank_eq_two`
  packages the rank-two support classification:
  \[
    \operatorname{rank}(T)=2
    \quad\Longrightarrow\quad
    |\operatorname{pairSupport}(T)|=2
      \ \text{or}\
    |\operatorname{pairSupport}(T)|=3.
  \]
  At the coefficient level,
  `rankTwoAlternatingCoefficientSupportCardGe_four_eq_zero` eliminates the
  support-cardinality \(\ge4\) summand, and
  `rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three` reduces the
  rank-two alternating coefficient unconditionally to the two structurally
  meaningful classes: support size \(2\) and support size \(3\).  Thus the
  remaining rank-two equality-pattern cancellation is no longer blocked by
  support cardinality; it is exactly the two local classification identities
  `RankTwoSupportCardTwoCoefficientIdentity G q` and
  `RankTwoSupportCardThreeCoefficientIdentity G q`, as packaged by
  `RankTwoAlternatingCoefficientIdentity.of_supportCardIdentities'`.
  The support-size-two proof has now started by formalizing the required
  pair-fiber decomposition.  `collisionSubfamilyPairFiber T p` is the
  pair-local part of \(T\) over query pair \(p\);
  `collisionSubfamilyPairFiber_nonempty_iff` proves that these nonempty fibers
  are exactly indexed by `collisionSubfamilyPairSupport q T`; and
  `collisionSubfamily_eq_biUnion_pairSupport_fibers` proves
  \[
    T=\bigsqcup_{p\in\operatorname{pairSupport}(T)} T_p .
  \]
  The theorem `collisionSubfamilyPairFiber_pairwiseDisjoint` gives the
  disjointness, `sum_pairFiber_card_eq_card` gives cardinality additivity, and
  `collisionSubfamilyPairFiber_card_le_two` records that each local fiber has
  at most the two hidden/shifted events over its query pair.  The next local
  normal forms are now formalized too:
  `collisionSubfamilyPairFiber_card_eq_one_or_two_of_mem_support` says every
  touched fiber is either a singleton or the full pair;
  `collisionSubfamilyPairFiber_eq_pairEvents_of_card_eq_two` identifies the
  two-event case with `collisionPairEvents p`; and
  `exists_collisionSubfamilyPairFiber_eq_singleton_of_card_eq_one` identifies
  the one-event case as `{(p,k)}` for some collision kind.  Finally,
  `collisionSubfamily_card_eq_two_or_three_or_four_of_pairSupport_card_eq_two`
  records that support-cardinality \(2\) has exactly the three event-cardinality
  cases \(2,3,4\).  This is the structural input needed to turn
  support-cardinality \(2\) into a product of two pair-local rank-one sums.
  The product expansion has now been put into the standard finite-product form.
  `rankTwoPairSupportPiProductCoefficientInt G q y S` is the `Finset.pi` sum
  over functions choosing one nonempty pair-local event subfamily over each
  \(p\in S\), and `rankTwoPairSupportProductCoefficientInt_eq_piProduct` proves
  that the existing product coefficient is exactly this `Finset.pi` expansion:
  \[
    \prod_{p\in S}
      \sum_{\varnothing\ne U\subseteq\mathcal E_p}
        (-1)^{|U|}\mathbf 1[\operatorname{balanced}_y(U)]
    =
    \sum_{F\in\prod_{p\in S}\mathcal P_+(\mathcal E_p)}
      \prod_{p\in S}
        (-1)^{|F_p|}\mathbf 1[\operatorname{balanced}_y(F_p)].
  \]
  This avoids a hand expansion of the two support pairs and is the right
  reindexing object for arbitrary \(q\).  The inverse maps for the upcoming
  bijection are also formalized.  `collisionSubfamilyPairChoiceUnion F`
  reassembles a subfamily from a local choice \(F_p\) over each \(p\in S\);
  `collisionSubfamilyPairSupport_pairChoiceUnion_eq` proves that if every
  \(F_p\) is nonempty and pair-local then the reassembled subfamily has pair
  support exactly \(S\);
  `collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq` proves that
  reassembling the actual fibers of an exact-support subfamily returns the
  original subfamily; and `collisionSubfamilyPairFiber_pairChoiceUnion_eq` proves
  that taking the \(p\)-fiber of a reassembled local choice returns \(F_p\).
  Arbitrary local choices now have the same normal forms as actual fibers:
  `pairLocalChoice_card_eq_one_or_two_of_nonempty_subset_pairEvents`,
  `pairLocalChoice_eq_pairEvents_of_card_eq_two`, and
  `exists_pairLocalChoice_eq_singleton_of_card_eq_one` prove that every nonempty
  pair-local choice is either a singleton event or the full hidden/shifted pair.
  The corresponding `Finset.pi` corollaries
  `pairChoice_mem_pi_subset_pairEvents`, `pairChoice_mem_pi_nonempty`,
  `pairChoice_mem_pi_card_eq_one_or_two`,
  `pairChoice_mem_pi_eq_pairEvents_of_card_eq_two`, and
  `exists_pairChoice_mem_pi_eq_singleton_of_card_eq_one` make these facts
  directly available inside the product expansion.
  For the triangle calculation we cannot factor the summand into independent
  pair-local balance tests, because the decisive balanced cycles use all three
  query-pair fibers at once.  This non-factorized reindexing is now formalized:
  `rankTwoPairSupportPiUnionCoefficientInt G q y S` is the `Finset.pi` sum over
  nonempty pair-local choices while retaining the global cycle-consistency
  predicate of their reassembled union, and
  `rankTwoAlternatingCoefficientPairSupportEqNoRankInt_eq_piUnion` proves the
  exact-support no-rank coefficient equals this pair-fiber choice sum.  The
  proof uses Mathlib's `Finset.sum_bij'` with the already-formalized fiber and
  reassembly inverse maps; no support-specific enumeration is introduced.
  The rank-retaining companion is formalized as well:
  `rankTwoPairSupportPiUnionRankCoefficientInt G q y S` keeps both the
  graphic-rank-two test and the global cycle-consistency predicate after
  reassembling the local choices, and
  `rankTwoAlternatingCoefficientPairSupportEqInt_eq_piUnionRank` proves that it
  is exactly the original exact-support rank-two coefficient.  This is now the
  safest local form for the remaining triangle computation: later lemmas may
  either prove rank automaticity for `queryPairSet V`, or evaluate the rank test
  directly inside this three-fiber choice space.
  The handoff is now also available at the whole triangle-layer level:
  `rankTwoTriangleVertexPiUnionRankCoefficientInt G q y` sums these ranked
  pair-fiber choice coefficients over all three-coordinate vertex sets, and
  `rankTwoTriangleVertexSupportCoefficientInt_eq_piUnionRank` rewrites the
  vertex-indexed support-cardinality-three layer into that form pointwise.
  The summand's cardinality factor is also preserved:
  `collisionSubfamilyPairChoiceUnion_card_eq_sum` proves
  \[
    \left|\bigcup_{p\in S}F_p\right|
    =
    \sum_{p\in S}|F_p|.
  \]
  The sign consequence is now formalized as
  `collisionSubfamilyPairChoiceUnion_neg_one_pow_card_eq_prod`:
  \[
    (-1)^{|\bigcup_{p\in S}F_p|}
    =
    \prod_{p\in S}(-1)^{|F_p|}.
  \]
  Finally,
  `collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_cycleConsistent_iff`
  proves that if the labelled cycle-consistency predicate factors over the
  reassembled union,
  \[
    \operatorname{balanced}_y\!\left(\bigcup_{p\in S}F_p\right)
    \Longleftrightarrow
    \forall p\in S,\ \operatorname{balanced}_y(F_p),
  \]
  then the whole signed summand factors:
  \[
    (-1)^{|\bigcup F_p|}
      \mathbf 1[\operatorname{balanced}_y(\bigcup F_p)]
    =
    \prod_{p\in S}
      (-1)^{|F_p|}\mathbf 1[\operatorname{balanced}_y(F_p)].
  \]
  The easy direction of this labelled predicate is also formalized:
  `collisionSubfamilyStepLabel_mono`, `collisionSubfamilyLabelReach_mono`, and
  `collisionSubfamilyCycleConsistent_mono` prove downward closure of balanced
  subfamilies, and
  `collisionSubfamilyPairChoiceUnion_local_cycleConsistent_of_global` applies it
  to each local \(F_p\).

  The hard direction for two touched query pairs is now formalized.  The local
  lemma `pairLocalChoice_labels_eq_of_cycleConsistent` proves that a
  cycle-consistent pair-local choice has a single label value.  The semantic
  lemma `collisionSubfamilyConsistent_two_singletons_of_pairIndex_ne` proves
  that two singleton constraints over distinct query pairs are always
  satisfiable, using a component-constant shift on the singleton support graph;
  `collisionEvent_endpoints_not_connected_singleton_of_pairIndex_ne` is the
  graph fact that makes that shift available.  Combining these gives
  `collisionSubfamilyPairChoiceUnion_cycleConsistent_iff_of_card_eq_two`:
  for \(|S|=2\),
  \[
    \operatorname{balanced}_y\!\left(\bigcup_{p\in S}F_p\right)
    \Longleftrightarrow
    \forall p\in S,\ \operatorname{balanced}_y(F_p).
  \]
  Therefore `collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_card_eq_two`
  closes the labelled/sign part of the two-support product expansion, not just
  its easy direction.

  The product side is now named and evaluated:
  `rankTwoForestPairFiberProductCoefficientInt` is the sum over two-pair supports
  of the product of the two local nonempty-powerset alternating sums,
  and `rankTwoForestPairFiberProductCoefficientInt_eq_forest` proves that this
  product form is exactly `rankTwoForestCoefficientInt G q y` by reusing the
  existing pair-local theorem
  `collisionPairEvents_localPowersetAlternatingCoefficient_ite`.  Therefore
  the remaining support-size-two obligation has been isolated as the raw
  reindexing statement `RankTwoSupportCardTwoPairFiberProductIdentity G q`.
  The bridge
  `RankTwoSupportCardTwoCoefficientIdentity.of_pairFiberProduct` proves that
  this reindexing statement implies the desired
  `RankTwoSupportCardTwoCoefficientIdentity G q`.
  The first reindexing layer of that raw statement is now formalized.  The
  definition `rankTwoAlternatingCoefficientPairSupportEqInt G q y S` restricts
  the raw rank-two alternating sum to subfamilies with exact query-pair support
  \(S\), and
  `rankTwoAlternatingCoefficientSupportCardEq_two_eq_sum_pairSupportEq` proves
  \[
    A_{2,|\mathrm{supp}|=2}(y)
    =
    \sum_{\substack{S\subseteq\operatorname{PairIndex}(q)\\ |S|=2}}
      A_{2,\mathrm{supp}=S}(y).
  \]
  On the product side,
  `rankTwoPairSupportProductCoefficientInt G q y S` names the corresponding
  exact-support product, and
  `rankTwoForestPairFiberProductCoefficientInt_eq_sum_pairSupportProduct`
  rewrites the global product coefficient as the same sum over two-element
  supports.  Consequently the remaining support-size-two theorem has been
  narrowed to the pointwise exact-support identity
  `RankTwoPairSupportEqProductIdentity G q`:
  \[
    A_{2,\mathrm{supp}=S}(y)
    =
    \prod_{p\in S}
      \sum_{\varnothing\ne U\subseteq\mathcal E_p}
        (-1)^{|U|}
        \mathbf 1[\operatorname{balanced}_y(U)]
    \qquad(|S|=2).
  \]
  The theorem
  `RankTwoSupportCardTwoPairFiberProductIdentity.of_pairSupportProduct` proves
  that this pointwise identity implies the global pair-fiber product identity,
  and `RankTwoSupportCardTwoCoefficientIdentity.of_pairSupportProduct` composes
  this with the already-evaluated product side to imply the forest coefficient
  identity directly.  The support-size-two task is therefore no longer a global
  summation problem; it is a local bijection/product expansion over the two
  touched pair fibers.
  This local task has now been split into its two independent ingredients.  The
  no-rank coefficient
  `rankTwoAlternatingCoefficientPairSupportEqNoRankInt G q y S` removes the
  graphic-rank test from the exact-support summand.  The graph-only predicate
  `RankTwoPairSupportRankAutomatic q` says that every exact two-pair support has
  graphic rank \(2\), and
  `rankTwoAlternatingCoefficientPairSupportEqInt_eq_noRank_of_rankAutomatic`
  proves that, under this graph fact,
  \(A_{2,\mathrm{supp}=S}\) equals the no-rank exact-support coefficient.  The
  remaining product expansion is named
  `RankTwoPairSupportNoRankProductIdentity G q`.  The bridge theorem
  `RankTwoPairSupportEqProductIdentity.of_rankAutomatic_noRankProduct` shows
  that rank automaticity plus the no-rank product expansion imply the pointwise
  exact-support product identity, and
  `RankTwoSupportCardTwoCoefficientIdentity.of_rankAutomatic_noRankProduct`
  composes this all the way to the support-cardinality-two forest identity.
  The no-rank product expansion itself is no longer an assumption:
  `rankTwoPairSupportNoRankProductIdentity` proves
  `RankTwoPairSupportNoRankProductIdentity G q` unconditionally by a
  `Finset.sum_bij'` between exact-support global subfamilies and their nonempty
  pair-local fibers.  Thus the support-cardinality-two rank-two contribution is
  reduced only to the graph-only rank-automaticity fact.  The wrapper
  `RankTwoSupportCardTwoCoefficientIdentity.of_rankAutomatic` records the
  current endpoint:
  \[
    \texttt{RankTwoPairSupportRankAutomatic}\ q
    \Longrightarrow
    \texttt{RankTwoSupportCardTwoCoefficientIdentity}\ G\ q.
  \]
  The bridge
  `RankTwoSupportCardTwoCoefficientIdentity.of_hiddenRepresentative_card_two`
  records the even sharper dependency:
  the specialized hidden-representative two-edge rank bound
  `HiddenRepresentativeGraphicRankLeTwoOnCardTwo q` alone closes the
  support-cardinality-two coefficient identity.
  The graph side has also been reduced to the standard inequality
  `GraphicRankLePairSupportCard q`,
  \[
    \operatorname{rank}(T)\le |\operatorname{pairSupport}(T)|,
  \]
  via `RankTwoPairSupportRankAutomatic.of_graphicRank_le_pairSupportCard`.
  The proof has now removed hidden/shifted multiplicity from this graph
  obligation.  `collisionSubfamilyAdjacent_iff_of_pairSupport_eq` and
  `collisionSubfamilyConnected_iff_of_pairSupport_eq` prove that adjacency and
  connectivity depend only on query-pair support.  The quotient-level endpoint
  `collisionSubfamilyComponentEquivOfPairSupportEq` gives equivalent component
  quotients for subfamilies with the same support, and
  `collisionSubfamilyComponentCount_eq_of_pairSupport_eq` plus
  `collisionSubfamilyGraphicRank_eq_of_pairSupport_eq` show that component count
  and graphic rank are support-only invariants.

  The canonical support graph is
  `collisionPairSupportHiddenRepresentative S`, the subfamily containing one
  hidden event over each \(p\in S\).  The theorems
  `collisionSubfamilyPairSupport_hiddenRepresentative` and
  `collisionPairSupportHiddenRepresentative_card` prove that this representative
  has exactly support \(S\) and cardinality \(|S|\).  The remaining graph
  inequality is therefore named in its canonical form as
  `HiddenRepresentativeGraphicRankLeCard q`, and
  `GraphicRankLePairSupportCard.of_hiddenRepresentative` proves that this
  canonical simple-graph rank bound implies the original
  `GraphicRankLePairSupportCard q` for arbitrary hidden/shifted subfamilies.
  For the rank-two cancellation path, the proof also exposes the smaller
  endpoint `HiddenRepresentativeGraphicRankLeTwoOnCardTwo q`: a canonical
  hidden representative with exactly two query-pair edges has graphic rank at
  most \(2\).  The bridge
  `RankTwoPairSupportRankAutomatic.of_hiddenRepresentative_card_two` proves that
  this specialized endpoint is already enough to obtain
  `RankTwoPairSupportRankAutomatic q`; the general edge-count theorem remains a
  reusable strengthening, not a prerequisite for support-size-two cancellation.
  Work then attacked this graph endpoint directly.  The helper
  `collisionEventPairEndpointSet e₁ e₂` names the four coordinates touched by a
  two-event support graph.  The theorems
  `collisionSubfamilyAdjacent_pair_left_mem_endpointSet` and
  `collisionSubfamilyConnected_pair_eq_of_left_not_mem_endpointSet` prove that
  any coordinate outside this endpoint set is isolated in `{e₁,e₂}`.  This is
  the first component-count ingredient for proving that two support edges reduce
  the number of connected components by at most two.
  The next component-count ingredient is now also formalized.  The deletion set
  `collisionEventPairDeletionSet e₁ e₂` chooses at most two coordinates and hits
  both selected events.  The lemmas
  `collisionEventPairDeletionSet_card_le_two`,
  `collisionEventPairDeletionSet_right_one_mem`, and
  `collisionEventPairDeletionSet_endpoint_two_mem` record those properties, and
  `collisionSubfamilyAdjacent_pair_not_both_not_mem_deletionSet` proves that no
  adjacency in `{e₁,e₂}` has both endpoints outside this deletion set.  The proof
  deliberately uses the standard Mathlib finite-cardinality lemmas
  `Finset.card_sdiff_of_subset` and `Finset.card_le_card_of_injOn` as the next
  bridge target rather than re-formalizing finite injections by hand.
  The graph endpoint was then isolated as the pure proposition
  `TwoEventGraphicRankLeTwo q`.  The theorem
  `collisionPairSupportHiddenRepresentative_eq_pair_of_card_eq_two` proves that
  every two-element hidden representative is literally a two-event support graph,
  and `HiddenRepresentativeGraphicRankLeTwoOnCardTwo.of_twoEvent` proves
  \[
    \texttt{TwoEventGraphicRankLeTwo}\ q
    \Longrightarrow
    \texttt{HiddenRepresentativeGraphicRankLeTwoOnCardTwo}\ q.
  \]
  The standard graph statement
  \[
    \operatorname{rank}(\{e_1,e_2\})\le 2,
  \]
  with no gain labels and no parallel hidden/shifted events is now proved as
  `twoEventGraphicRankLeTwo q`.  The proof did not introduce a new graph
  library.  It reuses the local singleton-component quotient machinery and
  standard finite-cardinality tools already available in Mathlib:
  `Fintype.card_le_of_surjective`, `Fintype.card_coe`,
  `Fintype.card_subtype_compl`, and `Finset.card_erase_of_mem`.  The main
  construction is `collisionSubfamilyPairComponentRep e₁ e₂`, a folded
  representative that first collapses the singleton graph `{e₁}` and then
  folds the singleton component of the right endpoint of `e₂` into the
  singleton component of its left endpoint.  The theorems
  `collisionSubfamilyPairComponentRep_eq_of_adjacent` and
  `collisionSubfamilyPairComponentRep_eq_of_connected` show this representative
  is constant on connected components of `{e₁,e₂}`.  The map
  `collisionSubfamilyPairComponentToRepImage` sends two-event components onto
  the image of this folded representative, while
  `collisionSubfamilyPairComponentRep_image_card_lower` proves that this image
  has at least \(q-2\) values.  Therefore `{e₁,e₂}` has at least \(q-2\)
  components and graphic rank at most \(2\).

  This closes the entire support-cardinality-two rank-two coefficient path.
  The unconditional theorem `hiddenRepresentativeGraphicRankLeTwoOnCardTwo q`
  composes `twoEventGraphicRankLeTwo q` with the hidden-representative bridge.
  From it, `rankTwoPairSupportRankAutomatic q` proves that every exact two-pair
  support is automatically a rank-two support, and
  `rankTwoSupportCardTwoCoefficientIdentity G q` proves the full
  support-cardinality-two forest identity without hypotheses.  Consequently the
  global rank-two equality-pattern theorem no longer depends on any
  support-cardinality-two graph or product obligation.  The new bridges
  `RankTwoAlternatingCoefficientIdentity.of_supportCardThree` and
  `RankTwoEqualityPatternIdentity.of_supportCardThree` reduce the remaining
  rank-two cancellation problem to the single triangle statement
  `RankTwoSupportCardThreeCoefficientIdentity G q`.

  The triangle path has now started in the same style as the two-pair forest
  path.  First, `rankTwoAlternatingCoefficientSupportCardEq_three_eq_sum_pairSupportEq`
  proves the purely finite-sum regrouping
  \[
    C_{2,|S|=3}(y)
      =
      \sum_{\substack{S\subseteq \mathrm{PairIndex}(q)\\ |S|=3}}
        C_{2,S}(y),
  \]
  where \(C_{2,S}(y)\) is the exact-pair-support coefficient already named as
  `rankTwoAlternatingCoefficientPairSupportEqInt`.  This uses the same
  Mathlib/local machinery as the two-pair regrouping:
  `Finset.sum_fiberwise_eq_sum_filter`, `Finset.sum_filter`, and `sum_congr`.
  No small-\(q\) enumeration enters.

  Second, the graph classification now has its first cardinal endpoint for
  support-cardinality three.  The theorem
  `collisionSubfamilyPairSupport_eq_componentPairUnion_of_graphicRank_eq_two_card_eq_three`
  says that if \(T\) has graphic rank \(2\) and touches exactly three query
  pairs, then its pair support equals the whole union of component-internal
  query pairs.  This is a direct use of the already-proved
  `rankTwoComponentPairUnionBound q` plus Mathlib's
  `Finset.eq_of_subset_of_card_le`.

  The theorem
  `exists_componentVertexSet_card_three_of_graphicRank_eq_two_pairSupport_card_three`
  then proves that such a \(T\) has a connected component containing exactly
  three query coordinates.  Otherwise every component would have at most two
  vertices, and the local arithmetic lemma `choose_two_le_sub_one_of_le_two`
  would bound the total component-internal pair capacity by the rank-two excess
  \(2\), contradicting the three touched query pairs.  This is the first formal
  point where the support-cardinality-three class is forced to be a genuine
  triangle rather than an arbitrary three-pair graph.  The supporting lemma
  `collisionSubfamilyComponentPairSet_eq_empty_of_vertexSet_card_le_one` records
  the complementary endpoint: a component with at most one query coordinate has
  no internal query pair.  It uses Mathlib's `Finset.card_le_one_iff`, so the
  proof does not re-formalize singleton finset reasoning.

  The triangle graph classification is now sharper still.  The theorem
  `collisionSubfamilyComponentVertexSet_card_eq_one_of_graphicRank_eq_two_of_ne_card_three`
  proves that once one rank-two component has three vertices, every other
  component is a singleton.  The proof uses `Finset.sum_eq_sum_diff_singleton_add`
  to split the component-excess sum at the three-vertex component; any second
  nonsingleton component would force total excess at least \(3\), contradicting
  rank two.  Then
  `collisionSubfamilyComponentPairUnion_eq_componentPairSet_of_graphicRank_eq_two_card_three`
  collapses the whole component-internal pair union to the pair set of that one
  three-vertex component.  Finally,
  `exists_component_card_three_pairSupport_eq_componentPairSet_of_graphicRank_eq_two_card_three`
  packages the statement needed for the coefficient proof:
  if \(T\) has graphic rank \(2\) and pair-support cardinality \(3\), then
  \[
    \exists c,\quad |V_c|=3
    \quad\text{and}\quad
    \operatorname{pairSupport}(T)=\operatorname{componentPairSet}(T,c).
  \]
  Thus the remaining support-cardinality-three coefficient calculation can now
  be localized to one genuine triangle component, rather than an arbitrary
  three-pair support graph.

  To prepare the coefficient reindexing, the proof now factors out the
  component-independent vertex-pair support
  `queryPairSet S`, the finset of all `PairIndex q` values whose endpoints both
  lie in a query-coordinate set \(S\).  The old
  `collisionSubfamilyComponentPairSet T c` is now definitionally
  `queryPairSet (collisionSubfamilyComponentVertexSet T c)`.  This small
  refactor keeps the next theorem honest: the triangle correction is indexed by
  arbitrary three-element vertex sets, not by connected components.  The
  reusable cardinal lemma `queryPairSet_card_le_choose` proves
  \[
    |\operatorname{queryPairSet}(S)|\le { |S| \choose 2 },
  \]
  and `collisionSubfamilyComponentPairSet_card_le_choose` is now just this
  lemma applied to a component vertex set.  Finally,
    `exists_vertexSet_card_three_pairSupport_eq_queryPairSet_of_graphicRank_eq_two_card_three`
    gives the component-free graph classification:
    every graphic-rank-two subfamily with three touched query pairs has
  \[
    \operatorname{pairSupport}(T)=\operatorname{queryPairSet}(V)
    \quad\text{for some } V\subseteq \operatorname{Fin}(q),\ |V|=3.
  \]
  This is the exact support-shape statement needed before evaluating the
  signed 27-term local triangle sum.

  The component-free support layer has also been made exact.  The canonical
  constructor `pairIndexOfNe i j hij` orients two distinct query coordinates
  as a `PairIndex q`, and `pairIndexOfNe_endpointSet` records that its endpoint
  finset is exactly \(\{i,j\}\).  The proof uses Mathlib's existing
  `Finset.card_eq_three` and `Finset.pair_comm`, rather than introducing a
  bespoke three-element finset eliminator.  With these lemmas,
  `queryPairSet_card_eq_three_of_card_eq_three` proves
  \[
    |V|=3\quad\Longrightarrow\quad
    |\operatorname{queryPairSet}(V)|=3.
  \]
  This gives the reverse cardinal endpoint missing from the earlier
  `queryPairSet_card_le_choose` upper bound.  The follow-up theorem
  `queryPairSet_injective_on_card_three` proves that, on three-coordinate
  vertex sets, `queryPairSet` determines the vertex set itself.  This prepares
  the later reindexing from triangle-support sets back to vertex triples; it is
  intentionally kept as a support lemma rather than folded into the local
  coefficient calculation.

  That reindexing is now formalized.  The proof introduces the named finite
  sets `queryTriangleVertexSet q` and `queryTriangleSupportSet q`.  The theorem
  `queryTriangleSupportSet_eq_image_queryPairSet` proves
  \[
    \operatorname{queryTriangleSupportSet}(q)
    =
    \operatorname{queryPairSet}\bigl[
      \operatorname{queryTriangleVertexSet}(q)
    \bigr],
  \]
  and `rankTwoTriangleSupportFilteredCoefficientInt_eq_vertexSupport` applies
  Mathlib's existing `Finset.sum_image` theorem, using
  `queryPairSet_injective_on_card_three` as the injectivity side condition.
  Consequently the proved bridge
  `rankTwoAlternatingCoefficientSupportCardEq_three_eq_vertexSupport` rewrites
  the whole three-pair rank-two layer as
  \[
    A_{2,|\mathrm{supp}|=3}(y)
    =
    \sum_{\substack{V\subseteq\operatorname{Fin}(q)\\ |V|=3}}
      A_{2,\operatorname{queryPairSet}(V)}(y).
  \]
  The remaining theorem is therefore purely local on a fixed three-coordinate
  vertex set \(V\): evaluate the exact-support coefficient
  \(A_{2,\operatorname{queryPairSet}(V)}(y)\) as
  \(-2+\mathbf 1[\text{all visible outputs on }V\text{ are equal}]\).

  At the coefficient level, the proof now introduces the predicate
  `IsQueryTriangleSupport S`, meaning
  \(S=\operatorname{queryPairSet}(V)\) for some three-coordinate set \(V\).
  The theorem
  `rankTwoAlternatingCoefficientPairSupportEqInt_eq_zero_of_not_triangleSupport`
  proves that an exact three-pair support not satisfying this predicate has
  zero rank-two contribution: if any summand had graphic rank two, the graph
  classification above would produce the required \(V\), contradiction.
  Consequently
  `rankTwoAlternatingCoefficientSupportCardEq_three_eq_sum_triangleSupport`
  rewrites the whole support-cardinality-three layer as the filtered sum
  over genuine triangle supports only:
  \[
    A_{2,|\mathrm{supp}|=3}(y)
    =
    \sum_{\substack{S:\ |S|=3\\
      \exists V,\ |V|=3,\ S=\operatorname{queryPairSet}(V)}}
      A_{2,S}(y).
  \]
  This is the precise Lean-backed statement that the remaining local
  calculation is a triangle calculation, not a calculation over arbitrary
  three-edge query-pair supports.

  The triangle-support calculation has now been reduced to a single local
  ranked pair-fiber identity.  The predicate
  `RankTwoTriangleVertexPiUnionRankIdentity G q` says that for every
  three-coordinate set \(V\),
  \[
    \operatorname{rankTwoPairSupportPiUnionRankCoefficientInt}
      (G,q,y,\operatorname{queryPairSet}(V))
    =
    -2+\mathbf 1[\text{all visible outputs on }V\text{ are equal}].
  \]
  The theorem
  `RankTwoSupportCardThreeCoefficientIdentity.of_vertexPiUnionRank` proves that
  this local identity implies the global support-cardinality-three identity,
  and
  `RankTwoAlternatingCoefficientIdentity.of_triangleVertexPiUnionRank` composes
  it with the already-closed support-cardinality-two forest path to prove the
  full rank-two equality-pattern coefficient identity.  Thus the remaining
  rank-two cancellation work is no longer a global regrouping problem: it is the
  finite local evaluation of one ranked three-fiber choice sum.
  This local statement was split into the two mathematically distinct
  obligations.  `RankTwoTriangleSupportRankAutomatic q` is the graph-only
  assertion that every subfamily with exact support
  \(\operatorname{queryPairSet}(V)\), \(|V|=3\), has graphic rank two, while
  `RankTwoTriangleVertexPiUnionNoRankIdentity G q` is the signed no-rank
  three-fiber evaluation.

  The graph-only branch is now closed.  If
  \(\operatorname{pairSupport}(T)\subseteq\operatorname{queryPairSet}(V)\), then
  `collisionSubfamilyAdjacent_mem_of_pairSupport_subset_queryPairSet` says any
  adjacency step lands in \(V\), and
  `collisionSubfamilyConnected_mem_of_pairSupport_subset_queryPairSet` extends
  this to support-graph paths.  The component version
  `collisionSubfamilyComponentVertexSet_subset_of_mem_of_pairSupport_subset_queryPairSet`
  proves that any connected component containing one vertex of \(V\) is wholly
  contained in \(V\).  The complementary lemmas
  `collisionSubfamilyConnected_eq_of_not_mem_of_pairSupport_subset_queryPairSet`
  and
  `collisionSubfamilyComponentVertexSet_eq_singleton_of_not_mem_of_pairSupport_subset_queryPairSet`
  prove that any coordinate outside \(V\) is isolated.  Under exact support,
  `collisionSubfamilyConnected_of_mem_of_mem_of_pairSupport_eq_queryPairSet`
  connects every two vertices of \(V\), and
  `collisionSubfamilyComponentVertexSet_eq_of_mem_of_pairSupport_eq_queryPairSet`
  identifies the component containing one vertex of \(V\) with \(V\) itself.
  Combining these component descriptions with the already-formalized component
  excess identity
  `sum_componentVertexSet_card_sub_one_eq_graphicRank` proves
  `rankTwoTriangleSupportRankAutomatic q`.

  Consequently the ranked local triangle identity now reduces directly to the
  remaining signed no-rank three-fiber calculation.  The composition lemmas
  `RankTwoTriangleVertexPiUnionRankIdentity.of_noRank`,
  `RankTwoAlternatingCoefficientIdentity.of_triangleNoRank`, and
  `RankTwoEqualityPatternIdentity.of_triangleNoRank` wire
  `RankTwoTriangleVertexPiUnionNoRankIdentity G q` all the way back to the
  rank-two equality-pattern theorem.  The next formal target is therefore only
  the finite signed local identity, not another graph-rank classification.
  The all-equal branch of that local identity is now closed.  First,
  `collisionEventLabel_eq_zero_of_mem_queryPairSet_of_visibleAllEqualOn` proves
  that every hidden/shifted internal event over an all-equal visible vertex set
  has zero gain, and
  `collisionSubfamilyCycleConsistent_of_pairSupport_subset_queryPairSet_of_visibleAllEqualOn`
  upgrades this to cycle consistency for any selected subfamily whose pair
  support stays inside that vertex set.  Then
  `rankTwoPairSupportPiUnionCoefficientInt_eq_localProduct_of_visibleAllEqualOn`
  uses Mathlib's `Finset.prod_sum` to factor the no-rank exact-support sum into
  three independent nonempty pair-fiber alternating sums.  The local identity
  `collisionPairEvents_localNonemptyPowersetAlternatingCard` evaluates each
  pair-fiber sum to \(-1\), so
  `rankTwoPairSupportPiUnionCoefficientInt_eq_neg_one_of_visibleAllEqualOn`
  proves the all-equal value:
  \[
    \operatorname{rankTwoPairSupportPiUnionCoefficientInt}
      (G,q,y,\operatorname{queryPairSet}(V))=-1
  \]
  whenever \(|V|=3\) and all visible outputs on \(V\) are equal.  This is
  exactly the \(-2+1\) branch of `RankTwoTriangleVertexPiUnionNoRankIdentity`.
  The remaining local work is the complementary branch: prove that the same
  exact-support no-rank coefficient is \(-2\) when the three visible outputs
  are not all equal.  The first pruning lemmas for that branch are now in
  place: `pairChoice_visible_eq_of_global_cycleConsistent_of_eq_pairEvents`
  proves that any globally cycle-consistent summand using the full
  hidden/shifted local pair on an edge forces visible equality on that edge,
  and
  `exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent`
  turns this around to show that visibly unequal edges can only contribute
  singleton local choices in globally consistent summands.  This is the formal
  split needed for the two non-all-equal equality patterns: all-distinct
  triangles have singleton choices on all three edges, while one-collision
  triangles may have a full pair only on the visibly equal edge.  The labelled
  walk equation
  `collisionSubfamilyCycleConsistent_triangle_label_eq_add` is also in place:
  in any cycle-consistent triangle, the direct edge label equals the sum of the
  two path labels through the third vertex.  This is the algebraic constraint
  that will count exactly which singleton-kind assignments survive in the
  non-all-equal branch.  The all-distinct singleton case has now been reduced
  to its exact two survivors:
  `triangle_singletonKinds_all_hidden_or_all_shifted_of_pairwise_visible_ne`
  proves that, when all three visible outputs are pairwise unequal, a
  cycle-consistent singleton assignment on the three edges must be either all
  hidden or all shifted.  The remaining formal counting step for the
  all-distinct branch is smaller now: the two survivor assignments are also
  proven cycle-consistent by
  `collisionSubfamilyCycleConsistent_orderedTriangle_allHidden` and
  `collisionSubfamilyCycleConsistent_orderedTriangle_allShifted`.  What remains
  is to reindex the globally consistent singleton summands onto these two
  assignments and sum their two \((-1)^3\) contributions.  The support
  normalization for that reindexing is also now available:
  `queryPairSet_orderedTriple` rewrites an ordered three-vertex support
  \(\{i,j,k\}\), \(i<j<k\), into exactly the three canonical internal pair
  indices.  The edge-pruning step has likewise been lifted to triangle
  granularity:
  `orderedTriangle_pairChoice_allSingletons_of_pairwise_visible_ne` proves
  that a globally cycle-consistent summand over an all-distinct ordered
  triangle must choose singleton local fibers on all three edges.  Combining
  that pruning with the triangle label equation gives
  `orderedTriangle_pairChoice_allHidden_or_allShifted_of_pairwise_visible_ne`:
  the only globally consistent all-distinct summands are the all-hidden
  singleton triangle and the all-shifted singleton triangle.  The remaining
  all-distinct proof obligation has now been discharged:
  `rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_pairwise_visible_ne`
  uses `Finset.sum_subset` to collapse the pair-local product-domain sum to
  those two survivors, and
  `orderedTriangle_singletonChoiceTerm_eq_neg_one` evaluates each survivor
  term as \((-1)^3=-1\).  Thus the ordered all-distinct triangle branch now
  formally contributes \(-2\).  The remaining local triangle work is the
  one-collision branch, where the visibly equal edge may still use the full
  hidden/shifted pair and the two visibly unequal edges should force a total
  contribution of \(-2\).  The first one-collision facts are now formal:
  `triangle_singletonKinds_unequal_edges_eq_of_left_visible_eq` proves that the
  triangle label equation forces the two visibly unequal singleton edges to use
  the same hidden/shifted kind, and
  `orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_left_visible_eq`
  lifts this to globally cycle-consistent pair-choice summands while leaving
  the visibly equal edge as the remaining local alternating fiber.  The next
  canonical representatives for that fiber are now also formalized.
  `orderedTriangle_oneCollisionChoice` builds the candidate summand from an
  arbitrary local nonempty equal-edge fiber and one common singleton kind on
  the two unequal edges.  The proof uses the existing local
  `queryPairSet_orderedTriple` normalization rather than adding a second
  three-edge membership API.  The supporting lemmas
  `orderedTriangle_oneCollisionChoice_mem_pi` and
  `orderedTriangle_oneCollisionChoice_cycleConsistent` show respectively that
  these candidates live in the product of pair-local fibers and are globally
  cycle-consistent.  The signed/cardinality evaluation is now formalized too:
  `orderedTriangle_oneCollisionChoiceUnion_eq` identifies the reassembled
  subfamily as the equal-edge local fiber plus two singleton unequal-edge
  events, `orderedTriangle_oneCollisionChoiceUnion_card` evaluates its
  cardinality as \(U.card+2\), and
  `orderedTriangle_oneCollisionChoiceTerm_eq_neg_one_pow_card` reduces each
  candidate summand to the alternating sign \((-1)^{U.card}\) of the remaining
  equal-edge fiber.  The canonical-candidate total is now formalized as
  `orderedTriangle_oneCollisionCandidateTermSum_eq_neg_two`: summing over every
  nonempty equal-edge local fiber and both common singleton kinds gives exactly
  \(-2\), using the existing pair-local alternating sum
  `collisionPairEvents_localNonemptyPowersetAlternatingCard`.  This leaves only
  the final `Finset.sum_subset` collapse that proves every globally consistent
  one-collision summand is one of these canonical candidates.  That collapse is
  now formalized.  The theorem
  `orderedTriangle_pairChoice_eq_oneCollisionChoice_of_left_visible_eq` turns
  the one-collision classification into literal equality with a canonical
  candidate function, and
  `rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_left_visible_eq`
  proves that the one-collision ordered triangle contributes exactly \(-2\).
  The proof uses `Finset.sum_subset` for the zero outside-candidate region and
  Mathlib's `Finset.sum_biUnion`/`Finset.sum_image` for the candidate
  reindexing.  The other two one-collision placements are now closed in the
  same local style.  The right-equality branch (`y_j=y_k`) is handled by
  `orderedTriangle_oneCollisionRightChoice` and
  `rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_right_visible_eq`;
  the outer-equality branch (`y_i=y_k`) is handled by
  `orderedTriangle_oneCollisionOuterChoice` and
  `rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_outer_visible_eq`.
  Thus every non-all-equal ordered triangle branch contributes \(-2\), while
  the all-equal branch contributes \(-1\).

  The ordered-local calculation has also been assembled back into arbitrary
  three-coordinate sets.  The supporting normalization lemma
  `exists_orderedTriple_eq_of_card_eq_three` uses Mathlib's
  `Finset.orderEmbOfFin`: every `V` with `V.card = 3` has ordered coordinates
  \(i<j<k\) with \(V=\{i,j,k\}\).  The theorem
  `rankTwoTriangleVertexPiUnionNoRankIdentity` then case-splits the three
  visible outputs into all-equal, all-distinct, and the three one-collision
  placements, proving `RankTwoTriangleVertexPiUnionNoRankIdentity G q`
  unconditionally.  This composes through
  `rankTwoTriangleVertexPiUnionRankIdentity`,
  `rankTwoSupportCardThreeCoefficientIdentity`,
  `rankTwoAlternatingCoefficientIdentity`, and
  `rankTwoEqualityPatternIdentity`: the rank-two gain-graph layer is now
  formally identified with the equality-pattern coefficient rather than an
  absolute \(E_2\) tail.

  Finally, `collisionSubfamilyPairSupport_eq_iff` characterizes exact support by
  nonempty pair fibers over the claimed support and no events outside the
  corresponding `biUnion` of pair-local event sets; the corollaries
  `collisionSubfamilyPairFiber_eq_empty_of_not_mem_support` and
  `collisionSubfamilyPairFiber_eq_empty_of_not_mem_of_pairSupport_eq` record the
  outside-fiber vanishing needed for the upcoming product bijection.
- The analytic bridge from this combinatorial identity back to density
  estimation is now named too.  `compatibleCountRankTwoEqualityDensityReal`
  is the scalar density obtained by replacing the raw rank-two gain-graph
  layer with
  \[
    N^{q-2} C_2^{=}(y),
  \]
  where \(C_2^{=}(y)\) is the forest-plus-triangle equality-pattern
  coefficient.  The theorem
  `compatibleCountRankTwoDensityReal_eq_equalityDensity_of_rankTwoEqualityPattern`
  proves that `RankTwoEqualityPatternIdentity G q` rewrites the signed
  rank-two-adjusted density into this equality-pattern density.  This is the
  bridge needed for the next sign-control step.  Since the rank-two
  classification facts above are now proven, the residual
  `rankTwoPositiveResidualErrorBound G q hq2` can be attacked directly as a
  one-dimensional/equality-pattern positive-part problem rather than as a raw
  gain-graph powerset problem.  This rewrite is now available pointwise as
  `compatibleCountRankTwoDensityReal_eq_equalityDensity` and at the positive
  part level as
  `compatibleCountRankTwoPositiveErrorReal_eq_equalityPositiveError`.
  The first statistic-level normalization is also in place:
  `pairCollisionSet_card` identifies the visible pair-collision count as an
  actual filtered set cardinality, and
  `rankTwoTriangleCorrectionInt_eq_choose_add_allEqualTripleCount` rewrites the
  triangle correction as
  \[
    -2\binom q3 + T_{=}(y),
  \]
  where `visibleAllEqualTripleCountNat G y` is the number of all-equal
  three-coordinate visible subsets.  The first moment infrastructure for this
  statistic is now closed.  The fixed-coordinate theorem
  `orderedTripleAllEqualFiber_card` proves that for three pairwise distinct
  coordinates \(i,j,k\), exactly \(N^{q-2}\) visible tuples satisfy
  \(y_i=y_j=y_k\); `visibleAllEqualOn_fiber_card_of_card_eq_three` lifts this
  to arbitrary three-element coordinate sets; and
  `sum_visibleAllEqualTripleCountNat_eq_choose_mul_card_pow` sums the fixed
  fibers over all triples.  The normalized statement is
  `uniformAverage_visibleAllEqualTripleCountNat_eq_choose_div_card_sq`:
  \[
    \mathbb E_{y\leftarrow G^q} T_=(y)=\binom q3/N^2
  \]
  for \(2\le q\), without enumerating small \(q\).  Consequently
  the proof now also exposes the next occupancy moment needed for low-rank
  sign control.  The new definition `pairPairCollisionFiberCard G S` counts
  visible transcripts where every query pair in a two-subset
  \(S\subseteq\operatorname{PairIndex}(q)\) is a visible collision.  Reusing
  Mathlib's `Finset.powersetCard` API and the already-formalized
  `pairCollisionSet`, the theorem
  `sum_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard` proves
  the exact second-factorial-moment bridge
  \[
    \sum_{y\in G^q} \binom{K(y)}2
    =
    \sum_{\substack{S\subseteq\operatorname{PairIndex}(q)\\ |S|=2}}
      \#\{y:S\subseteq\operatorname{Coll}(y)\}.
  \]
  Its normalized real form is
  `uniformAverage_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard`.
  The local uniform-fiber theorem is now formalized.  The bridge
  `pairCollisionSet_subset_iff_componentConstant_hiddenRepresentative` proves
  that asking for all pairs in \(S\) to visibly collide is equivalent to
  component-constancy on the canonical hidden representative
  `collisionPairSupportHiddenRepresentative S`.  The cardinality theorem
  `pairPairCollisionFiberCard_eq_componentConstant_card` converts the visible
  filter into the existing component-constant subtype, and
  `pairPairCollisionFiberCard_eq_card_pow_of_card_eq_two` reuses the existing
  graph theorem `rankTwoPairSupportRankAutomatic` plus
  `card_collisionSubfamilyComponentConstant` to evaluate every two-pair fiber
  as \(N^{q-2}\).  Thus `pairPairCollisionFiberUniform` closes the formerly
  named local obligation.  The closed moment is available as
  `uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq_closed`,
  while the older implication theorem
  `uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq`
  remains as a reusable parameterized variant.  The result is
  \[
    \mathbb E_{y\leftarrow G^q}\binom{K(y)}2
    =
    \binom{|\operatorname{PairIndex}(q)|}{2}/N^2.
  \]
  This is the right replacement for the false pointwise low-rank envelope:
  the first moment is already formalized, and the second factorial moment is
  the next occupancy input for an averaged positive-part bound.  That
  averaged bridge is now present in Lean.  The new obligation
  `CompatibleCountLowRankQuadraticCollisionBound G q ε` states a scalar
  quadratic envelope
  \[
    (\rho_{\le1}(K)-1)_+
    \le
    \lambda K+\varepsilon \binom K2,
  \]
  where the slope \(\lambda\) is `lowRankCollisionSlopeReal G q`.  The theorem
  `compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_quadraticCollision`
  proves, using the first and second moments, that this implies
  \[
    \operatorname{Pos}_{\le1}
    \le
    B_q(N)+
    \varepsilon\binom{|\operatorname{PairIndex}(q)|}{2}/N^2.
  \]
  Thus an envelope with \(\varepsilon=O(N^{-2})\) gives exactly the desired
  \(O(q^4/N^4)\) low-rank remainder.  This is also connected to the
  rank-two-adjusted route:
  `compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_quadraticCollision_add_quadraticPositive`
  and
  `visibleStatDist_le_spatialReconstructionBound_add_quadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage`
  replace the old low-rank fiber residual by this second-moment remainder in
  the visible endpoint.
  Consequently
  `uniformAverage_rankTwoTriangleCorrectionInt_eq` gives the averaged triangle
  contribution as
  \[
    -2\binom q3+\binom q3/N^2.
  \]
  `rankTwoEqualityCoefficientInt_eq_forest_sub_choose_add_allEqualTripleCount`
  reduces the rank-two equality coefficient to the forest coefficient plus
  this explicit all-equal-triple statistic.  The next residual-control step is
  to put the forest coefficient into the same collision-count/statistic form.
  The first reduction of that step is now formalized:
  `pairCollisionCoefficientInt_eq_pairCollisionSet` rewrites each pair-local
  forest weight through the visible collision-pair set, and
  `rankTwoForestCoefficientInt_eq_collisionSet` proves that the whole two-edge
  forest coefficient depends on the transcript only through
  `pairCollisionSet G y`.  Thus the remaining forest calculation is a finite
  elementary-symmetric problem over a two-valued weight function on
  `PairIndex q`, rather than a gain-graph or field-valued problem.  The
  theorem `rankTwoForestCollisionSetCoefficientInt_eq_power` then applies
  Mathlib's standard `Finset.prod_filter_mul_prod_filter_not` split to rewrite
  each summand as
  \[
    (-1)^{|S\cap C|}(-2)^{|S\setminus C|}.
  \]
  The two-subset sum has now been evaluated without introducing a separate
  mixed-fiber bijection.  The key pointwise identity is
  `rankTwoForestCollisionSetPowerSummand_eq_piecewise`:
  for a two-subset \(S\),
  \[
    (-1)^{|S\cap C|}(-2)^{|S\setminus C|}
    =
    2-\mathbf{1}_{S\subseteq C}
      +2\mathbf{1}_{S\subseteq C^c}.
  \]
  The theorems `rankTwoForestCollisionSet_sum_subset_indicator`,
  `rankTwoForestCollisionSetPowerCoefficientInt_eq_count`, and
  `rankTwoForestCollisionSetCoefficientInt_eq_count` then use
  `Finset.card_powersetCard` to close the forest coefficient as
  \[
    2\binom{|\mathrm{PairIndex}\ q|}{2}
      -\binom{|C|}{2}
      +2\binom{|C^c|}{2}.
  \]
  Finally,
  `rankTwoEqualityCoefficientInt_eq_collisionCount_sub_choose_add_allEqualTripleCount`
  threads this into the full equality-pattern rank-two coefficient:
  the rank-two layer is now expressed only through the visible pair-collision
  set and the all-equal-triple count.  The subsequent theorem
  `rankTwoEqualityCoefficientInt_eq_pairCollisionCount_sub_choose_add_allEqualTripleCount`
  removes the set-valued complement too, using `pairCollisionSet_card` and
  `Finset.card_sdiff_of_subset`; the coefficient is now a purely numeric
  statistic of \(K(y)\), the visible pair-collision count, and \(T_=(y)\), the
  all-equal-triple count.  This scalarization has also been lifted from the
  coefficient to the density level: `rankTwoEqualityDensityFromStatsReal`
  packages the low-rank plus rank-two equality-pattern density as a function
  of \(K,T_=\), and
  `compatibleCountRankTwoEqualityDensityReal_eq_stats` proves the pointwise
  rewrite.  The positive part has the same scalar form:
  `rankTwoEqualityStatsFiberCard` defines the joint fiber size for
  \((K,T_=)\), `uniformAverage_of_rankTwoEqualityStats` collapses any average
  of a function of these two statistics to a finite two-dimensional fiber sum,
  and `rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum` gives the exact
  finite sign-control target for the rank-two-adjusted positive error.
  The endpoint residual has now been rewritten to the same scalar target:
  `rankTwoEqualityStatsPositiveResidualErrorBound` is
  \[
    \left(
      \frac{1}{N^q}
      \sum_{y\in G^q}
        \bigl(\rho_{\le2}(K(y),T_=(y))-1\bigr)_+
      -
      B_q(N)
    \right)_+,
  \]
  and `rankTwoPositiveResidualErrorBound_eq_statsResidual` proves that it is
  exactly the residual used by the signed-rank-two endpoint.  Thus the
  remaining rank-two sign-control obligation is no longer an orbit or
  transcript-average statement: it is a finite two-statistic inequality over
  the occupancy fibers of \(K\) and \(T_=\).
  The exact residual expression is available as
  `rankTwoEqualityStatsPositiveResidualErrorBound_eq_fiberSum`, which expands
  this target to the concrete finite sum
  \[
    \left(
      \frac{1}{N^q}
      \sum_{k,t}
        |\{y:K(y)=k,\ T_=(y)=t\}|
        \bigl(\rho_{\le2}(k,t)-1\bigr)_+
      -
      B_q(N)
    \right)_+.
  \]
  The deletion-aware residual is now explicit as
  `rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q S`, obtained by
  replacing the full \((k,t)\)-support in the displayed sum by \(R\setminus S\).
  Theorems `rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff` and
  `rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff_of_density_le_one`
  prove that this is equal to the original residual whenever every fiber in
  \(S\) has zero positive part, respectively density at most \(1\).  This is
  not just a restatement of the old residual: after a sign lemma certifies a
  nonempty \(S\), the formal residual obligation is over a strictly smaller
  finite support.
  The scalar density itself has also been put in the right analytic normal
  form.  `rankTwoEqualityDensityFromStatsReal_eq_slack_mul` proves
  \[
    \rho_{\le2}(k,t)
    =
    S_q(N)
    \left(
      1+\frac{k-2m}{N}
        +\frac{C_2(k,t)}{N^2}
    \right),
  \]
  where \(m=|\mathrm{PairIndex}(q)|\), \(S_q(N)\) is the existing
  visible-normalizer slack, and \(C_2(k,t)\) is
  `rankTwoEqualityCoefficientFromStatsInt q k t`.  The companion theorem
  `rankTwoEqualityDensityFromStatsReal_eq_lowRank_add_quadratic` rewrites this
  as the low-rank density plus the explicit quadratic correction
  \(S_q(N)C_2(k,t)/N^2\).  This is the algebraic form needed for the remaining
  sign-region proof; it avoids returning to individual rank-two gain-graph
  subfamilies.  As a first inequality from this normal form,
  `rankTwoEqualityStatsPositiveErrorReal_le_lowRank_add_quadraticPositive`
  proves
  \[
    \mathbb{E}\bigl[(\rho_{\le2}-1)_+\bigr]
    \le
    \mathbb{E}\bigl[(\rho_{\le1}-1)_+\bigr]
    +
    \mathbb{E}\bigl[(S_q(N)C_2(K,T_=)/N^2)_+\bigr].
  \]
  This is still not the desired final cancellation estimate, because the
  low-rank and quadratic rank-two terms ultimately need to be controlled
  together.  It is nevertheless a genuine improvement over the old
  term-by-term rank-two fallback: rank two is now charged through the positive
  part of one scalar statistic rather than by absolute values of all
  graphic-rank-two subfamilies.
  The scalar positive part is now exposed as an NNReal bound in Lean:
  `rankTwoEqualityQuadraticPositiveErrorBound G q`, with coercion theorem
  `rankTwoEqualityQuadraticPositiveErrorBound_coe`.  It is also reduced to a
  finite two-statistic fiber sum by
  `rankTwoEqualityQuadraticPositiveErrorReal_eq_fiberSum`:
  \[
    Q_2^+(q,N)
    =
    \frac{1}{N^q}
    \sum_{k,t}
      |\{y:K(y)=k,\ T_=(y)=t\}|
      \left(
        S_q(N)\frac{C_2(k,t)}{N^2}
      \right)_+.
  \]
  The new endpoint
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound`
  proves
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)
    + R_{\mathrm{low}}(q,N)
    + Q_2^+(q,N)
    + E_{\ge3}^{\mathrm{avg}}(q,N),
  \]
  where \(R_{\mathrm{low}}\) is the exact low-rank occupancy-fiber residual and
  \[
    Q_2^+(q,N)
    =
    \mathbb E_{y\leftarrow U(G^q)}
      \left[
        \left(
          S_q(N)\frac{C_2(K(y),T_=(y))}{N^2}
        \right)_+
      \right].
  \]
  The plug-in theorem
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowRankResidual_add_quadraticPositive_add_tail`
  now exposes exactly three finite obligations:
  \[
    R_{\mathrm{low}}(q,N)\le \varepsilon_{\mathrm{low}},\qquad
    Q_2^+(q,N)\le \varepsilon_2,\qquad
    E_{\ge3}^{\mathrm{avg}}(q,N)\le \varepsilon_{\ge3}.
  \]
  These imply
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+\varepsilon_{\mathrm{low}}+\varepsilon_2+\varepsilon_{\ge3}.
  \]
  The closed-tail variant replaces \(E_{\ge3}^{\mathrm{avg}}\) by
  \(E_{\ge3}^{\mathrm{cl}}\).  This endpoint is weaker than a final joint
  sign-region theorem, but it is more cancellation-aware than the old
  rank-two absolute-value split: the rank-two contribution has been reduced to
  one scalar positive-part statistic over the \((K,T_=)\) fibers.
  The same quadratic-positive route now also has a low-rank-discharged form.
  The theorem
  `compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_quadraticPositive_of_lowRank`
  combines the scalar rank-two inequality with
  `CompatibleCountLowRankPositiveErrorBound G q`, so the explicit
  \(R_{\mathrm{low}}\) term disappears.  At the adaptive level,
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoAverage_of_lowRank`
  proves
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+Q_2^+(q,N)+E_{\ge3}^{\mathrm{avg}}(q,N),
  \]
  assuming only the named low-rank positive-error bound.  The companion theorem
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoAverage_of_collisionFiber`
  derives the same RHS from the existing one-dimensional scalar/fiber
  low-rank obligation `CompatibleCountLowRankCollisionFiberBound G q`.  This is
  a genuine RHS improvement over the previous quadratic endpoint: the
  rank-two absolute \(N^{-2}\)-scale slack is already gone, and now the
  low-rank residual is gone once the low-rank scalar inequality is supplied.
  The closed-tail companion
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoClosed_of_collisionFiber`
  replaces \(E_{\ge3}^{\mathrm{avg}}\) by the closed fallback
  `rankTailBeyondTwoErrorBound G q`.
  This route is useful as a theorem-chain diagnostic, but it is not the final
  paper-grade sign-control target.  The isolated positive quadratic term can
  still have \(N^{-2}\)-scale mass: formally,
  `rankTwoEqualityCoefficientFromStatsInt_zero_zero` proves that at
  \(K=0,T_=0\)
  \[
    c_2(q,0,0)=4\binom{\binom q2}{2}-2\binom q3,
  \]
  and `rankTwoEqualityCoefficientFromStatsInt_four_zero_zero` gives
  \(c_2(4,0,0)=52\).  Thus \(Q_2^+\) must not be treated as the desired
  \(O(q^4/N^4)\) residual.  The cancellation that removes the apparent
  \(N^{-2}\)-scale rank-two slack lives in the joint sign region of the
  low-rank-plus-rank-two density, i.e. in
  `rankTwoEqualityStatsPositiveResidualErrorBound G q`.  The lemma
  `rankTwoEqualityDensityFromStatsReal_zero_zero_eq_slack_mul` records the
  corresponding joint-density normal form for the zero-collision fiber:
  \[
    \rho_{\le2}(0,0)
    =
    \mathrm{slack}_q(N)
    \left(
      1-\frac{2\binom q2}{N}
      +\frac{4\binom{\binom q2}{2}-2\binom q3}{N^2}
    \right),
  \]
  expressed in Lean's `PairIndex` notation.  This is the sign-region expression
  that has to be shown nonpositive, or charged sharply, in the below-birthday
  regime.  The local deletion step is now formalized too:
  `rankTwoEqualityStatsPositiveFiberTerm_eq_zero_of_density_le_one` removes
  any \((K,T_=)\)-fiber whose scalar density is at most \(1\), and
  `rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_slack_mul_le_one`
  specializes this to the zero-collision fiber using the displayed normal
  form.  The theorem
  `rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_descFactorial_le`
  then rewrites this same deletion condition against the exact normalizer
  \((N)_q^2\): it suffices to prove
  \[
    N^{2q}
    \left(
      1-\frac{2\binom q2}{N}
      +\frac{4\binom{\binom q2}{2}-2\binom q3}{N^2}
    \right)
    \le (N)_q^2.
  \]
  The remaining analytic work is therefore to prove sufficiently sharp
  inequalities for these normal-form sign conditions, rather than to enumerate
  rank-two gain-graph terms.  Once that inequality is supplied, the theorem
  `rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_erase_zero_zero` removes
  the whole \((K,T_)=(0,0)\) fiber from the rank-two positive-error sum.  This
  is the first formal residual-sum cancellation step: a large all-distinct
  transcript class is no longer charged by the rank-two positive part.  The
  same deletion argument has now been abstracted as
  `rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_sdiff`: for any finite set
  \(S\) of \((K,T_=)\)-fibers, if every fiber in \(S\) has scalar density at
  most \(1\), the positive-error sum may be rewritten over the support
  complement \(R\setminus S\).  The density-facing wrapper
  `rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_sdiff_of_density_le_one`
  is the form intended for later analytic use.  This is the right RS/Lean
  interface for the next analytic stage: prove sign conditions for whole
  regions of the two-statistic lattice, then delete them from the residual sum
  without repeating any `Finset` bookkeeping.  The endpoint theorem
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsSdiffResidual_add_tail`
  consumes this smaller residual directly:
  \[
    \rho_{\le2}(k,t)\le 1 \text{ for all }(k,t)\in S,\quad
    R_{\le2}^{\mathrm{stats}}(R\setminus S)\le\varepsilon_2,\quad
    E_{\ge3}^{\mathrm{avg}}\le\varepsilon_{\ge3}
    \Longrightarrow
    \operatorname{Adv}^{\mathrm{adapt}}_q
      \le B_q(N)+\varepsilon_2+\varepsilon_{\ge3}.
  \]
  There is also a concrete first nonempty deletion endpoint,
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidualEraseZeroZero_add_tail`:
  under the displayed descending-factorial sign inequality, the residual
  hypothesis is stated over
  \(R\setminus\{(0,0)\}\).  This is the first theorem boundary whose RHS is
  genuinely improved by sign-control, because the all-distinct zero-triple
  fiber is no longer part of the rank-two residual that must be bounded.
  The corresponding exact finite error terms are now named too:
  `finiteOrbitRankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound`
  and
  `finiteOrbitRankTwoStatsPositiveEraseZeroZeroClosedBeyondTwoErrorBound`.
  The adaptive endpoints
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound`
  and
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveEraseZeroZeroClosedBeyondTwoErrorBound`
  state the concrete bounds
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q
    \le
    B_q(N)+
    R_{\le2}^{\mathrm{stats}}(R\setminus\{(0,0)\})
    +E_{\ge3}
  \]
  with either the exact average or closed rank-three-plus tail.  This is the
  current strongest formal RHS: it replaces the full rank-two residual by an
  erased-support residual under one explicit sign condition.
  A second, canonical version avoids choosing \(S\) manually:
  `rankTwoEqualityStatsNonpositiveFiberSet` is the finite set of all
  two-statistic fibers satisfying \(\rho_{\le2}(k,t)\le 1\).  The finite errors
  `finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound`
  and `finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound`
  use the residual over the complement of this exact sign-certified region.
  The support and sign regions are now named explicitly in Lean:
  `rankTwoEqualityStatsSupport G q` is
  \[
    R=\{0,\ldots,|\operatorname{PairIndex}(q)|\}
      \times \{0,\ldots,\binom q3\},
  \]
  with membership theorem `mem_rankTwoEqualityStatsSupport_iff`, and
  `rankTwoEqualityStatsPositiveFiberSet G q` is
  \[
    R\setminus\{(k,t)\in R:\rho_{\le2}(k,t)\le1\}.
  \]
  The theorem `mem_rankTwoEqualityStatsPositiveFiberSet_iff` proves the exact
  characterization
  \[
    (k,t)\in\operatorname{PositiveRegion}
    \quad\Longleftrightarrow\quad
    (k,t)\in R\ \text{and}\ 1<\rho_{\le2}(k,t).
  \]
  The strict inequality has now also been rewritten without the abstract
  normalizer.  The Lean definition
  `rankTwoEqualityDensityPolynomialFactorReal G q k t` names the polynomial
  factor
  \[
    P_{q,N}(k,t)
      =
      1+\frac{k-2\binom q2}{N}
        +\frac{C_2(q,k,t)}{N^2},
  \]
  where \(C_2(q,k,t)\) is
  `rankTwoEqualityCoefficientFromStatsInt q k t`.  The theorem
  `mem_rankTwoEqualityStatsNonpositiveFiberSet_iff_pow_mul_factor_le_descFactorial_sq`
  proves the deletion-side finite inequality
  \[
    (k,t)\in\operatorname{NonpositiveRegion}
    \Longleftrightarrow
    (k,t)\in R
    \text{ and }
    N^{2q} P_{q,N}(k,t) \le (N)_q^2,
  \]
  while
  `mem_rankTwoEqualityStatsPositiveFiberSet_iff_descFactorial_sq_lt` proves
  the equivalent charged-region inequality
  \[
    (k,t)\in\operatorname{PositiveRegion}
    \Longleftrightarrow
    (k,t)\in R
    \text{ and }
    (N)_q^2 < N^{2q} P_{q,N}(k,t).
  \]
  This is the next analytic handle: the remaining sign-control problem is now
  a concrete falling-factorial comparison, not a statement about the opaque
  LM20/orbit normalizer.
  Two endpoint wrappers package the extreme case:
  `rankTwoEqualityStatsPositiveFiberSet_eq_empty_of_forall_pow_mul_factor_le_descFactorial_sq`
  says that a uniform proof of
  \(N^{2q}P_{q,N}(k,t)\le (N)_q^2\) on every supported fiber makes the strict
  positive region empty, and
  `rankTwoEqualityStatsPositiveResidualErrorBoundOn_empty` proves that the
  residual over the empty positive region is zero.  Thus a future global
  falling-factorial estimate can discharge the rank-two sign-region residual
  without reopening the finite-sum definitions.
  More generally,
  `rankTwoEqualityStatsPositiveResidualErrorBoundOn_le_of_real_bound` converts
  any real-valued estimate
  \[
    \frac{1}{N^q}
      \sum_{(k,t)\in\operatorname{PositiveRegion}}
        |\{y:K(y)=k,T_=(y)=t\}|
        (\rho_{\le2}(k,t)-1)_+
      -B_q(N)
    \le \varepsilon_2
  \]
  into the corresponding `NNReal` residual bound.  The adaptive theorem
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionRealBound_add_tail`
  consumes this real inequality directly:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q
    \le B_q(N)+\varepsilon_2+\varepsilon_{\ge3}.
  \]
  The density excess itself has been rewritten as a single normalized
  falling-factorial numerator:
  `rankTwoEqualityDensityFromStatsReal_sub_one_eq_factorial_excess_div`
  proves
  \[
    \rho_{\le2}(k,t)-1
    =
    \frac{N^{2q}P_{q,N}(k,t)-(N)_q^2}{(N)_q^2},
  \]
  and
  `rankTwoEqualityStatsPositiveRegionSum_eq_factorialExcessSum` lifts this
  identity through the whole strict-positive-region sum.  The Lean theorem
  `rankTwoEqualityStatsPositiveResidualErrorBoundOn_positiveSet_eq_factorialExcess`
  now packages the same rewrite at the residual level, and
  `rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_factorialExcess`
  identifies the canonical erased-support sign-region residual with this
  exact falling-factorial excess:
  \[
    R_{\le2}^{\mathrm{sign}}(q,N)
    =
    \left(
      \frac{1}{N^q}
      \sum_{(k,t)\in\operatorname{PositiveRegion}}
        |\{y:K(y)=k,T_=(y)=t\}|
        \frac{N^{2q}P_{q,N}(k,t)-(N)_q^2}{(N)_q^2}
      -B_q(N)
    \right)_+ .
  \]
  This is the precise finite object whose sign/moment estimate must replace
  the old scalar quadratic-positive fallback.  The endpoint
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionFactorialExcessBound_add_tail`
  is now complemented by
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionFactorialExcessBound_add_consistentTail`,
  the preferred paper-facing interface for the remaining analytic work: prove
  the factorial-excess sum is at most \(B_q(N)+\varepsilon_2\), then bound the
  consistency-filtered rank-\(3+\) gain-graph average by \(\varepsilon_{\ge3}\).
  The residual can now be stated directly over this positive region instead of
  indirectly as the complement of a deleted nonpositive set:
  `rankTwoEqualityStatsPositiveResidualErrorBoundOn` names
  \[
    \left(
      \frac{1}{N^q}
      \sum_{(k,t)\in\operatorname{PositiveRegion}}
        |\{y:K(y)=k,T_=(y)=t\}|
        (\rho_{\le2}(k,t)-1)_+
      -B_q(N)
    \right)_+,
  \]
  and
  `rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_on_positiveSet`
  proves that the exact sign-region endpoint charges precisely this expression.
  On each charged fiber, the positive part has no remaining ambiguity:
  `rankTwoEqualityStatsPositiveFiberTerm_eq_density_sub_one_of_mem_positiveFiberSet`
  proves
  \[
    (\rho_{\le2}(k,t)-1)_+=\rho_{\le2}(k,t)-1.
  \]
  This is the finite analytic object that must be controlled next: a weighted
  excess over strict-positive two-statistic fibers.
  The positive region is now split at the right analytic boundary.  The Lean
  definitions
  `rankTwoEqualityStatsLowCollisionPositiveFiberSet` and
  `rankTwoEqualityStatsHighCollisionPositiveFiberSet` partition the strict
  positive region according to \(K<2\) and \(K\ge2\), and
  `rankTwoEqualityStatsPositiveRegionContributionReal_eq_low_add_high` proves
  the corresponding contribution identity.  This reflects the actual
  obstruction found by exact arithmetic: low-collision fibers are not
  uniformly nonpositive in the full small-query regime, so they cannot simply
  be deleted.  They are instead the part that must account for the main
  spatial term \(B_q(N)\).

  The high-collision part has a separate moment interface.  The theorem
  `rankTwoEqualityStatsSupport_chooseTwoContribution_eq_pairIndex_chooseTwo_div_card_sq`
  reuses the already-formalized second factorial moment
  `uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq_closed`
  after regrouping by the joint \((K,T_=)\)-fibers.  Consequently
  `rankTwoEqualityStatsHighCollisionPositiveRegionContributionReal_le_chooseTwo`
  proves the exact implication
  \[
    \forall (k,t)\in\operatorname{PositiveRegion}_{K\ge2},\quad
      (\rho_{\le2}(k,t)-1)_+\le \varepsilon\,\binom{k}{2}
    \Longrightarrow
    \operatorname{HighRegionMass}
      \le
      \varepsilon\frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^2}.
  \]
  The averaged high-region RHS is named
  `rankTwoEqualityStatsHighCollisionChooseTwoErrorBound`.  At the adaptive
  RS level,
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowCollisionPositiveRegionBound_add_highCollisionChooseTwoBound_add_consistentTail`
  now gives the sharper proof boundary
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q
    \le
    B_q(N)+
    \varepsilon_{\mathrm{low}}
    +\varepsilon_{\mathrm{high}}
      \frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^2}
    +\varepsilon_{\ge3}^{\mathrm{cons}}.
  \]
  This is stronger than the previous opaque sign-region endpoint: the
  \(K\ge2\) rank-two mass is now tied to a second-moment bound, so a pointwise
  high-collision coefficient estimate of order \(O(N^{-2})\) yields the desired
  \(O(q^4/N^4)\) contribution.
  The pointwise high-collision coefficient is now itself an exact finite
  certificate rather than a free hypothesis:
  `rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal` is the maximum,
  over supported \((K,T_=)\)-fibers with \(K\ge2\), of
  \[
    \max\left(
      \frac{(\rho_{\le2}(k,t)-1)_+}{\binom{k}{2}},0
    \right).
  \]
  The theorem
  `rankTwoEqualityStatsHighCollisionPositiveFiberTerm_le_envelope_mul_chooseTwo`
  proves that this finite maximum supplies the required pointwise
  `choose K 2` bound, and
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowCollisionPositiveRegionBound_add_highCollisionEnvelopeBound_add_consistentTail`
  packages the current strongest rank-two boundary:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q
    \le
    B_q(N)+
    \varepsilon_{\mathrm{low}}
    +
    \alpha_{\mathrm{high}}(q,N)
      \frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^2}
    +\varepsilon_{\ge3}^{\mathrm{cons}}.
  \]
  Thus the high-collision rank-two task is reduced to proving
  \(\alpha_{\mathrm{high}}(q,N)=O(N^{-2})\) in the desired range.
  This is still an interface theorem, not the final numerical estimate: it
  fixes the target of the remaining analytic work.  To reach a paper-grade
  \(B_q(N)+O(q^4/N^4)\) bound, the next proof must bound the low-collision
  residual over \(K<2\), prove an \(O(N^{-2})\) pointwise coefficient for
  high-collision fibers, and then combine these with the consistency-filtered
  rank-\(\ge3\) tail.
  The corresponding endpoints
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound`
  and
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound`
  require no separate sign hypothesis: the deleted set is defined by the sign
  predicate itself.  Analytically, this is the best sign-region reduction
  available at the current two-statistic abstraction level; the remaining work
  is to bound the positive-region residual without crude termwise rank-two
  counting.
  This has also been packaged as a theorem boundary:
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidual_add_tail`
  says that any explicit bounds
  \[
    R_{\le2}^{\mathrm{stats}}(q,N)\le \varepsilon_2,
    \qquad
    E_{\ge3}^{\mathrm{avg}}(q,N)\le \varepsilon_{\ge3}
  \]
  immediately give
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+\varepsilon_2+\varepsilon_{\ge3}.
  \]
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_closedRankSplitErrorBound`
  packages the current closed gain-graph split:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+R_{\mathrm{low}}(q,N)
      +E_2^{\mathrm{cl}}(q,N)+E_{\ge3}^{\mathrm{cl}}(q,N).
  \]
- `rankSplitTailErrorBound G q` names the same closed rank-two plus
  rank-\(3+\) tail without the low-rank residual:
  \[
    E_{\mathrm{split}}^{\mathrm{cl}}(q,N)
    =
    E_2^{\mathrm{cl}}(q,N)+E_{\ge3}^{\mathrm{cl}}(q,N).
  \]
  The theorem
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankSplitTailErrorBound_of_lowRank`
  proves the clean conditional endpoint
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{split}}^{\mathrm{cl}}(q,N),
  \]
  assuming only `CompatibleCountLowRankPositiveErrorBound G q`.  The theorem
  `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankSplitTailErrorBound_of_collisionFiber`
  gives the same endpoint from the one-dimensional occupancy-fiber obligation
  `CompatibleCountLowRankCollisionFiberBound G q`.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailMaxResidualErrorBound`
  is the corresponding closed-fallback endpoint:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+E_{\mathrm{orbit}}^{\mathrm{avg},\max}(q,N).
  \]
  This endpoint is not the target final theorem.  Its role is to keep an
  explicit finite-\(q,N\) RHS available while the sharper occupancy-fiber
  inequality and cancellation-aware gain-graph tail are being proved.
- `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_maxResidualClosedRankSplitErrorBound`
  is the fully closed rank-split fallback with no transcript averages and no
  occupancy-fiber sum:
  \[
    \operatorname{Adv}^{\mathrm{adapt}}_q(\mathrm{XoP},\mathrm{URF})
    \le
    B_q(N)+R_{\mathrm{low}}^{\max}(q,N)
      +E_2^{\mathrm{cl}}(q,N)+E_{\ge3}^{\mathrm{cl}}(q,N).
  \]

The remaining visible-side proof has now been separated into the right two
pieces:

1. prove the signed rank-two residual estimate for
   `rankTwoEqualityStatsPositiveResidualErrorBound G q`.  The rank-two
   equality-pattern identity and scalarization lemmas have already reduced
   \(\rho_{\le2}\) to a finite problem in the two statistics \(K(y)\) and
   \(T_=(y)\).  The separate quadratic-positive route is retained only as a
   diagnostic/wrapper endpoint: the all-distinct fiber already makes
   \(Q_2^+\) \(N^{-2}\)-scale, so the next concrete sign-control problem is the
   joint residual, not a standalone bound on \(Q_2^+\);
2. sharpen the genuinely higher-rank fallback \(E_{\ge 3}^{\mathrm{cl}}\) by
   using consistency probabilities instead of the powerset cardinality.  The
   old \(E_{\mathrm{tail}}(q,N)\) and the older rank-split endpoints remain as
   proved fallbacks, but the main theorem boundary now points at
   \[
     B_q(N)+R_{\le2}(q,N)+E_{\ge3}(q,N),
   \]
   which is the correct finite-\(q,N\) shape for reaching
   \(B_q(N)+O(q^4/N^4)\).

This gives the first post-LM20 quantitative bridge: after the
representative/coupling theorem says that the problem is the orbit-label mass
discrepancy, the compatible-count formula can be peeled into the universal
equality-pair contribution and the remaining higher-rank structure.

Now define the density ratio of the real visible law against the ideal law:

\[
  \rho(y)
  =
  \frac{\Pr_R[Y=y]}{\Pr_I[Y=y]}
  =
  \frac{N^q C(y)}{((N)_q)^2}.
\]

Let

\[
  S_2(q)=\sum_{r=0}^{q-1} r^2
  =
  \frac{q(q-1)(2q-1)}{6}.
\]

Since

\[
  \frac{(N)_q}{N^q}
  =
  1-\frac{H}{N}
  +
  \frac{H^2-S_2(q)}{2N^2}
  +
  O_q(N^{-3}),
\]

we get

\[
  \frac{N^{2q}}{((N)_q)^2}
  =
  1+\frac{2H}{N}
  +
  \frac{2H^2+S_2(q)}{N^2}
  +
  O_q(N^{-3}).
\]

Combining this denominator expansion with the rank expansion of \(C(y)\)
gives the local density expansion

\[
  \rho(y)
  =
  1
  +
  \frac{K(y)}{N}
  +
  \frac{
    B_2(y)-2H^2+2H K(y)+S_2(q)
  }{N^2}
  +
  O_q(N^{-3}).
\]

This formula is a useful checkpoint for the research program:

1. The leading positive deviation comes only from visible collisions
   \(K(y)>0\).
2. All-distinct output tuples have no \(1/N\) deviation; their first deviation
   starts at order \(1/N^2\).
3. The order \(1/N^2\) local term already depends on rank-\(2\) labelled
   subgraphs, not just equality pattern.
4. Finer affine distinctions, such as the \(q=4\) plane/general split, arise
   from still higher graphic-rank strata of Lemma 4.

This is the correct route to a tight finite-\(N\) proof.  The orbit-sum theorem
gives the exact answer once all ranks are included.  The spatial-reconstruction
bound corresponds to retaining only the dominant visible-collision mechanism
and bounding the remaining labelled-graph strata.

### The first affine-dependent stratum

The peer-review criticism usefully sharpens the rank picture.  The coefficient
\(B_2(y)\) does not see non-trivial affine dependencies among all-distinct
outputs.  For all-distinct \(y\), every pair \(i<j\) contributes exactly two
possible labels, \(0\) and \(y_i+y_j\), and the parallel pair on the same
vertices is inconsistent because \(y_i+y_j\ne0\).

For all-distinct \(y\), the rank-\(2\) coefficient is therefore independent of
the affine shape of the tuple.  Explicitly,

\[
  B_2^{\mathrm{distinct}}(q)
  =
  \binom{2H}{2}
  -
  H
  -
  2\binom q3 .
\]

The first two terms count two-edge forests in the labelled complete graph:
choose two labelled edges, then remove the \(H\) inconsistent parallel pairs.
The final term subtracts the consistent labelled triangles.  On a triple of
all-distinct vertices, the only consistent simple triangles are the all-hidden
triangle and the all-shifted triangle.

This explains why affine geometry does not affect the local density through
order \(N^{-2}\) on the all-distinct stratum.  The first place it can enter is
graphic rank \(3\).

For \(q=4\), the all-distinct rank coefficients are:

\[
  C_{\mathrm{plane}}(y)
  =
  N^4 - 12N^3 + 52N^2 - 78N,
\]

when \(y_1+y_2+y_3+y_4=0\), and

\[
  C_{\mathrm{general}}(y)
  =
  N^4 - 12N^3 + 52N^2 - 84N,
\]

when \(y_1+y_2+y_3+y_4\ne0\).  Thus

\[
  B_3^{\mathrm{plane}} - B_3^{\mathrm{general}} = 6.
\]

The mixed four-cycle

\[
  (1,2,0),\quad
  (2,3,y_2+y_3),\quad
  (3,4,0),\quad
  (4,1,y_4+y_1)
\]

is the minimal visible witness: its cycle label is

\[
  y_1+y_2+y_3+y_4.
\]

It is consistent exactly on the affine-plane orbit.  Direct enumeration of the
rank-\(3\) labelled subgraphs gives the coefficient shift above.  The important
point is not merely that the local coefficient changes by \(6\), but that the
tuples satisfying a fixed four-point affine dependency are rare.  Under the
ideal law, for any fixed four indices,

\[
  y_i+y_j+y_k+y_\ell=0
\]

has probability \(1/N\) before excluding coincidences.  Therefore a local
rank-\(3\) affine shift of size \(O(N^{-3})\) contributes globally at scale

\[
  O\!\left(\frac{\binom q4}{N^4}\right),
\]

not \(O(\binom q4/N^3)\).  This is consistent with the observed fixed-\(q\)
gaps: the spatial bound and exact advantage agree through order \(N^{-3}\) in
the tested \(q=3,4\) cases, and the first visible discrepancy appears at order
\(N^{-4}\).

This gives a sharper research target:

\[
  \Delta_q
  =
  B_q(N)
  -
  \Theta_q(N^{-4})
  \quad\text{for fixed }q\ge3,
\]

with the \(N^{-4}\) coefficient governed by the rank-\(3\) labelled-graph
stratum together with the \(1/N\)-rarity of four-point affine dependencies.
The statement above is a target, not yet a theorem.  To prove it uniformly in
the regime \(q\ll \sqrt N\), we need a bound that combines:

1. the number of index quadruples,
2. the probability that a quadruple satisfies a non-trivial affine dependency,
3. the maximum rank-\(3\) coefficient shift per dependent quadruple,
4. the remaining higher-rank labelled-graph tail.

This is the first place where the exact orbit formula can plausibly yield a
tighter proof than spatial reconstruction alone.

### Gain-graph identification and what it buys

The labelled graph in Lemma 4 is not merely analogous to a gain graph; it is a
gain graph over the additive group \(G\).  Orient each edge from the smaller
index to the larger index and assign gain \(\lambda\) to an edge
\((i,j,\lambda)\).  A coloring is a map

\[
  a : \{1,\ldots,q\}\to G.
\]

The proper-coloring condition for the gain edge \((i,j,\lambda)\) is

\[
  a_i+a_j\ne \lambda.
\]

For the hidden edge \(\lambda=0\), this is \(a_i\ne a_j\).  For the shifted
edge \(\lambda=y_i+y_j\), this is

\[
  a_i+y_i\ne a_j+y_j.
\]

Therefore \(C(y)\) is exactly the number of proper \(G\)-colorings of this gain
graph.  Lemma 4 is the Whitney expansion of that gain-graph chromatic function:
balanced subgraphs are precisely the consistent labelled subgraphs.

This resolves the polynomial-identification question at the level needed for
the proof.  The right external language is Zaslavsky-style gain graphs or
biased graphs.  Ordinary matroid references remain useful for classifying
affine point configurations, but the compatible-count polynomial itself is a
gain-graph chromatic object.

### The finite-partition theorem

The abstract partition step is now settled.  Let \(X\) be finite and let
\(\Omega\) be a finite partition of \(X\).  Suppose \(P\) and \(Q\) are
probability distributions on \(X\) such that, for every block
\(\omega\in\Omega\), their conditionals inside the block agree:

\[
  P(x\mid x\in\omega)=Q(x\mid x\in\omega)=D_\omega(x).
\]

Write

\[
  w_P(\omega)=P(\omega),\qquad w_Q(\omega)=Q(\omega).
\]

Then

\[
  P(x)=w_P(\omega)D_\omega(x),
  \qquad
  Q(x)=w_Q(\omega)D_\omega(x)
  \quad (x\in\omega).
\]

Hence

\[
  \frac12\sum_{x\in X}|P(x)-Q(x)|
  =
  \frac12\sum_{\omega\in\Omega}
    |w_P(\omega)-w_Q(\omega)|
    \sum_{x\in\omega}D_\omega(x)
  =
  \frac12\sum_{\omega\in\Omega}|w_P(\omega)-w_Q(\omega)|.
\]

This is the exact abstract theorem behind the orbit-sum formula.  The
repository now has this in two forms:

1. `statDist_eq_classifierStatDist_of_constantFibers`, which states the
   collapse to classifier pushforwards.
2. `visibleStatDist_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier`,
   which states the affine-orbit version as a finite sum over classifier fibers.
3. `classifierCompatibleCountNat_eq_compatibleCountNat_of_mem` and
   `classifierCompatibleCount_eq_compatibleCountNNReal_of_mem`, which state
   that on any occupied classifier fiber the abstract fiber count is exactly the
   compatible count of any chosen representative transcript in that fiber.  The
   `Nat` version is the formal bridge from the LM20/orbit representative theorem
   back to the gain-graph rank expansion: choose a transcript in the block,
   compute \(C(y)\) there, and the result is the block's \(C_\omega\).  The
   `NNReal` version is the corresponding probability-mass form.  The affine
   specialization
   `classifierCompatibleCountNat_eq_compatibleCountNat_of_affineCoordOrbitClassifier_mem`
   exposes the same bridge directly for affine-coordinate orbit classifiers.
   The stronger affine theorem
   `classifierCompatibleCountNat_eq_rankZero_add_rankOne_add_tail_of_affineCoordOrbitClassifier_mem`
   immediately rewrites the occupied block numerator \(C_\omega\) as the
   rank-zero/rank-one/tail expansion of any representative \(y\) in the block.
4. `classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount` and
   `classifierWeight_idealVisibleDist_eq_card_mul_uniformMass`, plus their
   affine specializations, which spell out the real and ideal block weights.
   These are the formulas whose positive-part distance is the exact LM20
   coupling failure.
5. `xop_adaptiveAdvantage_eq_sum_classifierWeights_of_affineCoordOrbitClassifier`,
   the unrestricted adaptive statement that the XoP advantage itself is the
   positive-part sum of real orbit mass minus ideal orbit mass.

The first two results are transcript-level partition identities.  The later
PDS endpoints lift them to honest equivalent representatives and explicit
couplings over deterministic systems.

### What is still not proved

One peer claim still should not be accepted without more work.

The proposed gain-graph tail bound is still a target, not a theorem.
Counting rank-\(r\) subgraphs and assigning an \(N^{-r}\) factor is not by
itself enough, because the statistical distance involves signs, positive
parts, orbit masses, and the rarity of the visible dependencies that make some
rank-\(r\) subgraphs balanced.  The \(q=4\) plane/general calculation shows the
right mechanism, but a uniform \(q,N\) bound needs a separate argument.

### Signed and virtual representatives

The signed-measure discussion is a genuine extension of the LM20 mindset, not
an objection to it.  LM20 distributions are nonnegative finite measures over
DDSs, with probability PDSs as the weight-\(1\) case.  The extension under
consideration replaces the positive cone by the ambient vector space of signed
finite measures and asks which parts of the LM20 advantage theorem survive.

Let \(D\) be a finite DDS space and write

\[
  V_D = \mathbb R^D.
\]

For each environment \(e\), let

\[
  T_e : V_D \to \mathbb R^{\mathrm{Tr}_e}
\]

be the linear transcript pushforward.  A full-behavioral signed class for a
random system \(\mathbf S\) would be

\[
  \mathcal L_{\mathrm{full}}(\mathbf S)
  =
  \{\mu\in V_D :
      T_e\mu=\mathrm{Tr}_e(\mathbf S)\text{ for every environment }e\}.
\]

With the signed total-variation/base norm

\[
  \|\eta\|_1=\sum_d|\eta(d)|,
\]

the natural signed relaxation is

\[
  \operatorname{LinAdv}_{\mathrm{full}}(\mathbf R,\mathbf I)
  =
  \inf_{\mu\in\mathcal L_{\mathrm{full}}(\mathbf R),\,
       \nu\in\mathcal L_{\mathrm{full}}(\mathbf I)}
       \frac12\|\mu-\nu\|_1.
\]

The important point is that, with full behavioral constraints, this extension
does **not** relax the value below advantage.  For any feasible signed
\(\mu,\nu\), pushforward contraction gives

\[
  \frac12\|\mu-\nu\|_1
  \ge
  \frac12\|T_e\mu-T_e\nu\|_1
  =
  \delta(\mathrm{Tr}_e(\mathbf R),\mathrm{Tr}_e(\mathbf I))
\]

for every \(e\).  Taking the supremum over environments gives

\[
  \frac12\|\mu-\nu\|_1\ge \operatorname{Adv}(\mathbf R,\mathbf I).
\]

Thus

\[
  \operatorname{LinAdv}_{\mathrm{full}}\ge \operatorname{Adv}.
\]

The reverse inequality uses the ordinary LM20 representative theorem: honest
nonnegative representatives are included in the signed classes, and LM20 gives
honest representatives attaining, or arbitrarily approaching, the advantage.
Therefore the full-behavioral signed extension is a linear certificate language
for the same value, not a way to beat the value.

This conclusion depends critically on using full behavioral constraints.  If
one uses only partial constraints, the signed relaxation can collapse.  For
example, let \(X=\{0,1\}\), \(P=\delta_0\), \(Q=\delta_1\), and constrain only
total mass.  Then both signed classes contain every signed measure of total
mass \(1\), so the signed infimum is \(0\), while the true TV distance is \(1\).

For SoP/XoP this clarifies the role of signed objects:

1. The affine-orbit decomposition is honest and nonnegative:

   \[
     R=\sum_\omega w_R(\omega)D_\omega,\qquad
     I=\sum_\omega w_I(\omega)D_\omega.
   \]

   The finite-partition theorem computes TV exactly from orbit masses.

2. The gain-graph expansion is signed but analytic:

   \[
     C(y)=
     \sum_T(-1)^{|T|}
       \mathbf 1_{\mathrm{balanced}_y(T)}N^{\kappa(T)}.
   \]

   It computes the honest count \(C(y)\).  It should not be treated as a PDS
   representative.

3. Coefficient positive parts in an overlapping signed basis are not TV.  A
   minimal warning example is

   \[
     b_1=(1,-1),\qquad b_2=(-1,1)
   \]

   on \(X=\{0,1\}\).  Then \(b_1+b_2=0\), but summing positive coefficient
   contributions would report nonzero mass.  Therefore gain-graph, Fourier,
   Möbius, and ANOVA coordinates can certify or bound density deviations only
   after the signed expansion is resummed pointwise or controlled by a valid
   norm inequality.

## Peer review status

The peer exchange has now resolved the original framing questions.  The
remaining work is no longer about which viewpoint to use; it is about proving
the tail estimates and integrating the result into the random-systems
formalization.

### Settled decisions

1. **Main theorem shape.** The exact finite-\(N\) orbit-sum identity is the main
   structural theorem:

   \[
     \Delta_q
     =
     \sum_{\omega\in\Omega_q}
       (w_R(\omega)-w_I(\omega))_+.
   \]

   The spatial-reconstruction expression \(B_q(N)\) should be presented as a
   computable upper bound or corollary, not as the fundamental identity.

2. **LM20 placement.** The transcript-level orbit coupling comes first because
   it exposes the counting invariant.  The full PDS lifting lemma should appear
   immediately after it as the operational bridge to LM20 representatives.
   Putting the lift before the transcript identity would obscure the simple
   combinatorial core.

3. **Classifier granularity.** The structural classifier is the
   affine-coordinate orbit set

   \[
     \Omega_q = G^q/(S_q\times\operatorname{Aff}(G)).
   \]

   Equality partitions are too coarse: they miss the rank-\(3\) affine-plane
   correction.  Coarser classifiers may be useful for estimates, but not for the
   exact structural theorem.

4. **Counting object.** The exact count \(C(y)\) should be handled through the
   gain graph of Lemma 4.  Ordinary affine-matroid data is useful for
   classifying configurations, but the compatible-count formula is a
   Zaslavsky-style gain-graph chromatic function because it includes both
   hidden and shifted collision constraints.

5. **First affine correction.** On all-distinct transcripts, \(B_2(y)\) is
   independent of non-trivial affine dependencies.  The first affine-dependent
   local correction occurs at graphic rank \(3\), and for \(q=4\) the
   plane/general split changes the \(B_3\) coefficient by \(6\).

6. **Finite-partition theorem.** The abstract partition step is settled:
   common conditionals on classifier fibers imply that total variation distance
   collapses to total variation distance between classifier masses.  The SoP
   specialization is also formalized for affine-coordinate orbit classifiers,
   including the cardinality-times-\(C_\omega\) formula.  This is now also
   stated in coupling form: an optimal coupling of classifier masses witnesses
   the full transcript distance whenever the within-fiber conditionals match.

7. **Signed/virtual LM20 framing.** Signed objects should be presented as a
   linearized extension of LM20, not as a replacement for honest PDS
   representatives.  With full behavioral constraints and the signed
   total-variation/base norm, the signed optimum equals the ordinary advantage
   assuming the LM20 representative theorem.  With partial constraints, signed
   relaxations can collapse.

8. **Terminology.** Use **honest representative** for nonnegative LM20 PDSs,
   **virtual representative** or **signed representative** for elements of the
   ambient signed vector space, **linearized LM20** for the extension, and
   **observational nullspace** or **positivity gap** for failures caused by weak
   constraints.  Avoid presenting signed gain-graph terms as systems.

### Current endpoint and remaining open problems

1. **LM20 representative endpoint.** The main representative/coupling layer is
   now formalized at both the visible-output and PDS-distribution levels.
   `classifierBlockUniform` identifies the intended block-uniform visible laws;
   `PDS.ofPositionTapeDist` realizes those laws as honest deterministic-system
   distributions; `labelFirstBlockCoupling` gives the explicit label-first
   coupling of the visible representatives; and
   `exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_cardCompatibleCountSum`
   lifts this to a coupling of the equivalent position-tape PDS distributions
   over DDS values and records that its value is exactly the explicit
   cardinality-times-compatible-count orbit sum.  The remaining work is no longer
   representative packaging; it is quantitative evaluation or bounding of the
   orbit-label mass discrepancy.  The first bridge from the representative
   layer to computation is also named:
   `classifierCompatibleCountNat_eq_compatibleCountNat_of_mem` says that an
   occupied orbit block's natural compatible count can be computed using any
   transcript representative of that block, and the `NNReal` theorem casts that
   fact back to transcript probabilities.  For the concrete affine-orbit
   classifier layer, the corresponding API is
   `classifierCompatibleCountNat_eq_compatibleCountNat_of_affineCoordOrbitClassifier_mem`.
   The real and ideal orbit-label masses themselves are now exposed by
   `classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount_of_affineCoordOrbitClassifier`
   and
   `classifierWeight_idealVisibleDist_eq_card_mul_uniformMass_of_affineCoordOrbitClassifier`.
   The theorem
   `exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_cardCompatibleCountSum`
   is now the most direct formal handoff from LM20 to counting: unrestricted
   adaptive advantage and representative-coupling failure both equal the finite
   orbit sum whose real-side numerator is \(C_\omega\).  The theorem
   `classifierCompatibleCountNat_eq_rankZero_add_rankOne_add_tail_of_affineCoordOrbitClassifier_mem`
   then rewrites each occupied \(C_\omega\) by choosing any representative
   transcript in the orbit and applying the rank-zero/rank-one/tail expansion.

2. **Low-rank positive-part bound.** The low-rank scalar coefficient is now
   discharged in the small-query regime \(q(q-1)\le N\).  The proof does not
   use a pointwise false envelope.  It first covers the \(k=0,1\) collision
   fibers by the spatial line, then bounds every high-collision fiber by a
   finite quadratic correction.  The new closed theorem
   `lowRankQuadraticEnvelopeCoefficient_le_twelve_inv_sq_of_queryPair_le_card`
   proves
   \[
     \alpha_q(G)
     =
     \operatorname{lowRankQuadraticEnvelopeCoefficient}(G,q)
     \le \frac{12}{N^2}.
   \]
   Consequently the visible paper-shaped endpoint
   `visibleStatDist_le_spatialReconstructionBound_add_twelve_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage`
   is now formalized:
   \[
   \begin{aligned}
     \operatorname{Adv}_q
     \le{}&
     B_q(N)
     +
     12\frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^4}\\
     &+
     E_2^+(q,N)
     +
     E_{\ge3}^{\mathrm{avg}}(q,N).
   \end{aligned}
   \]
   The same package is now exposed at the adaptive XoP/PDS level by
   `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoTwelveQuadraticPositiveTailBeyondTwoAverageErrorBound`.
   Its error term is named
   `finiteOrbitRankTwoTwelveQuadraticPositiveTailBeyondTwoAverageErrorBound`
   and expands to
   \[
     12\frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^4}
     +
     E_2^+(q,N)
     +
     E_{\ge3}^{\mathrm{avg}}(q,N).
   \]
   Thus the old low-rank residual is no longer a blocker.  The remaining
   quantitative work is the rank-two-positive and rank-\(\ge3\) gain-graph
   cancellation/sign-control.

   A new comparison theorem also closes a bookkeeping gap between the two
   rank-two routes.  The theorem
   `rankTwoEqualityStatsPositiveResidualErrorBound_le_lowRank_add_quadraticPositive`
   proves that the exact two-statistic residual is bounded by the older
   low-rank-plus-quadratic-positive residual:
   \[
     E_{2,\mathrm{stats}}^+(q,N)
     \le
     E_{\mathrm{low}}(q,N)+E_{2,\mathrm{quad}}^+(q,N).
   \]
   Consequently
   `finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound_le_quadraticPositive`
   shows that the exact two-statistic finite endpoint is never worse than the
   scalar quadratic-positive finite endpoint.  This matters because any closed
   estimate proved for the scalar route can now be inherited by the sharper
   statistics/sign-region route without reopening the rank-two gain-graph
   proof.

   The sign-region route is now ordered formally, not only heuristically.
   `rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_le` proves that
   deleting any certified rank-two equality-statistic fibers can only decrease
   the residual.  Specializing this to the exact nonpositive fiber set gives
   `finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound_le_statsPositive`,
   and transitivity gives
   `finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound_le_quadraticPositive`.
   This is a genuine RHS improvement: the current sharp rank-two term is the
   positive region of the two-statistic density, while the older scalar
   quadratic route remains only a fallback upper bound.
   The same ordering is available for the closed-tail endpoints via
   `finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound_le_statsPositive`
   and
   `finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound_le_quadraticPositive`,
   so the comparison also applies to the older closed finite RHS.

   There is also now a zero-rank-two-residual endpoint for any regime in which
   the rank-two equality-statistic sign condition can be proved uniformly.
   `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_consistentTail_of_rankTwoStats_nonpositive`
   assumes the falling-factorial inequality
   \[
     N^{2q}P_{q,N}(k,t)\le (N)_q^2
   \]
   for every supported two-statistic fiber \((k,t)\), and concludes directly
   \[
     \operatorname{Adv}_q \le B_q(N)+E_{\ge3}^{\mathrm{cons}}(q,N).
   \]
   This is the cleanest formal boundary for completely eliminating the
   rank-two slack: it reduces that step to one scalar sign proof over the
   supported equality-pattern fibers.

3. **Uniform tail bound.** Improve the current explicit tail term
   \[
     E_{\mathrm{tail}}(q,N)
     =
     \Bigl(2^{q(q-1)}
       - \bigl(1+3\cdot |\operatorname{PairIndex}(q)|\bigr)\Bigr)
     \frac{N^{2q-2}}{((N)_q)^2}
   \]
   by exploiting cancellation and the rarity of balanced high-rank gain
   subgraphs.  The current RS-style theorem packages this as the pending
   visible-side obligation
   \[
     \operatorname{visibleStatDist}_q
     \le B_q(N)+E_{\mathrm{tail}}(q,N),
   \]
   after which the adaptive XoP theorem follows automatically.  The target is
   to turn the heuristic

   \[
     \Delta_q = B_q(N) - \Theta_q(N^{-4})
   \]

   for fixed \(q\) into a theorem with explicit constants or a usable
   \(q,N\)-dependent remainder.

   The next bridge is now formalized.  Instead of immediately discarding all
   gain labels with the powerset-cardinality estimate, the theorem
   `rankTailBeyondTwoAverageErrorBound_le_consistentAverageErrorBound` proves
   \[
     E_{\ge3}^{\mathrm{avg}}(q,N)
     \le
     E_{\ge3}^{\mathrm{cons}}(q,N),
   \]
   where the new RHS is the average, over visible transcripts \(y\), of only
   those rank-three-and-higher collision-event subfamilies whose gain labels are
   cycle-consistent.  The corresponding adaptive endpoint is
   `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound`:
   \[
     \operatorname{Adv}_q
     \le
     B_q(N)
     +
     E_{2,\mathrm{sign}}^+(q,N)
     +
     E_{\ge3}^{\mathrm{cons}}(q,N).
   \]
   This does not yet close the \(O(q^4/N^4)\) estimate, but it moves the
   remaining high-rank work to the right object: prove that balanced
   rank-three-and-higher gain subgraphs are rare on average, rather than
   charging every labelled subgraph pointwise.

   A second bridge now exposes the next signed cancellation layer before any
   absolute value is taken.  The definitions
   `compatibleCountRankThreeDensityReal`,
   `rankThreePositiveResidualErrorBound`, and
   `rankTailBeyondThreeAverageErrorBound` split the comparison as
   \[
     \rho(y)
     =
     \rho_{\le3}^{\mathrm{signed}}(y)
     +
     \rho_{\ge4}^{\mathrm{tail}}(y).
   \]
   The visible theorem
   `visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeAverage`
   and its adaptive wrapper
   `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreePositiveTailBeyondThreeAverageErrorBound`
   prove
   \[
     \operatorname{Adv}_q
     \le
     B_q(N)
     +
     E_{3,\mathrm{sign}}^+(q,N)
     +
     E_{\ge4}^{\mathrm{avg}}(q,N).
   \]
   This is not yet a final finite \(B_q(N)+O(q^4/N^4)\) theorem.  Its value is
   that rank three is no longer charged as an absolute high-rank tail: the
   remaining proof must either control the signed rank-three positive residual
   directly, or combine it with a sign-region argument, while the absolute tail
   begins only at rank four.

   This boundary has now been sharpened in the same style as the previous
   high-rank consistency bridge.  Lean defines
   `rankTailBeyondThreeConsistentAverageErrorBound` and proves
   `rankTailBeyondThreeAverageErrorBound_le_consistentAverageErrorBound`, giving
   the endpoint
   \[
     \operatorname{Adv}_q
     \le
     B_q(N)
     +
     E_{3,\mathrm{sign}}^+(q,N)
     +
     E_{\ge4}^{\mathrm{cons}}(q,N).
   \]
   A closed fallback is also present:
   `rankTailBeyondThreeAverageErrorBound_le_rankTailBeyondThreeErrorBound` and
   `xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreePositiveClosedBeyondThreeErrorBound`
   prove, for \(q\ge4\),
   \[
     \operatorname{Adv}_q
     \le
     B_q(N)
     +
     E_{3,\mathrm{sign}}^+(q,N)
     +
     2^{q(q-1)}\frac{N^{2q-4}}{((N)_q)^2}.
   \]
   Thus the closed high-rank tail has the desired fourth-order scale after rank
   three is separated.  The remaining non-closed term is precisely the signed
   rank-three positive residual.

4. **Reference hygiene.** Pin down the exact Zaslavsky theorem name and citation
   for the Whitney expansion of gain-graph chromatic functions.  The proof note
   now uses the correct object, but the final paper should cite the precise
   theorem rather than a broad gain-graph reference.

5. **Concrete applications.** After the general framework is formalized, add
   concrete orbit calculations only as applications.  The \(q=4\) plane/general
   computation is the first useful example because it demonstrates the rank-\(3\)
   affine correction without making small-\(q\) values the proof architecture.

The following signed/virtual LM20 items are **Track B**.  They are recorded here
only so the interface with Track A stays clear; they are not prerequisites for
the orbit proof.

## Current finite-certificate endpoint

The low-rank obstruction has now been separated into a finite scalar
certificate rather than a vague "prove the sign region" placeholder.

Let \(K(y)\) be the visible pair-collision count and let
\[
  L(k)
  =
  \max\bigl(
    \operatorname{lowRankDensityFromCollisionCountReal}(k)-1,0
  \bigr).
\]
The Lean definition
`lowRankQuadraticEnvelopeCoefficient G q` is the finite maximum, over
\[
  0\le k\le |\operatorname{PairIndex}(q)|,
\]
of
\[
  \max\left(
    \frac{L(k)-\lambda k}{\binom{k}{2}},0
  \right)
\]
on the range \(k\ge 2\), where
\[
  \lambda=\operatorname{lowRankCollisionSlopeReal}(G,q).
\]
The denominator is why the two exceptional counts \(k=0,1\) are recorded
separately as `LowRankLowCollisionLineCovered G q`: for those counts the
quadratic correction is exactly zero, so they must be covered by the spatial
line itself.

The new Lean theorem
`compatibleCountLowRankQuadraticCollisionBound_of_finiteCoefficient` proves
the exact finite implication:
\[
  \operatorname{LowRankLowCollisionLineCovered}(G,q)
  \Longrightarrow
  L(K(y))
  \le
  \lambda K(y)
  +
  \alpha_q(G)\binom{K(y)}{2}
\]
for every transcript \(y\), with
\(\alpha_q(G)=\operatorname{lowRankQuadraticEnvelopeCoefficient}(G,q)\).
This is not yet the final closed paper bound; it is the finite certificate that
turns the sign-region problem into a one-dimensional scalar estimate.

Plugging this certificate into the already-formalized first and second
occupancy moments gives the visible endpoint
`visibleStatDist_le_spatialReconstructionBound_add_finiteQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage`:
\[
\begin{aligned}
  \operatorname{Adv}_q
  \le{}&
  B_q(N)
  +
  \alpha_q(G)
    \frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^2} \\
  &+
  E_2^+(q,N)
  +
  E_{\ge 3}^{\mathrm{avg}}(q,N).
\end{aligned}
\]

This is a concrete RS proof state.  The finite-certificate endpoint now
discharges the exceptional low-collision cases directly.  The Lean theorems
`lowRankDensityZeroPositivePart_le_zero_of_queryPair_le_card` and
`lowRankDensityOnePositivePart_le_slope_of_queryPair_le_card` prove the
\(k=0\) and \(k=1\) line checks in the small-query regime
\[
  q(q-1)\le N.
\]
Both proofs deliberately reuse the existing RS falling-factorial estimate
`XoP.ANOVA.descFactorial_div_pow_ge_one_sub_sum` and the existing small-query
sum bound `XoP.ANOVA.sum_range_div_card_le_half_of_queryPair_le_card`.  The
new bridge facts are notation adapters plus one scalar inequality:

- `pairIndex_card_eq_sum_range`, connecting
  \(|\operatorname{PairIndex}(q)|\) to \(\sum_{i<q} i\);
- `pairIndex_card_div_eq_sum_range_div`, the corresponding real normalized
  identity;
- `one_sub_two_mul_le_sq_one_sub`, the scalar arithmetic fact
  \(1-2x\le (1-x)^2\);
- `one_collision_factor_le_first_order_sq_mul_slope_correction`, the scalar
  inequality that handles the \(k=1\) excess against the spatial slope.

Thus the \(k=0\) proof is not a new product estimate.  It is exactly the
existing falling-factorial lower bound squared:
\[
  1-2\sum_{i<q}\frac{i}{N}
  \le
  \left(1-\sum_{i<q}\frac{i}{N}\right)^2
  \le
  \left(\frac{(N)_q}{N^q}\right)^2 .
\]
The \(k=1\) proof uses the same first-order lower bound, plus the slope
correction.  Writing \(P=|\operatorname{PairIndex}(q)|\), it reduces to
\[
  1+\frac{1-2P}{N}
  \le
  \left(1-\frac{P}{N}\right)^2
  \left(
    1+\left(1-\frac{P}{N}\right)\frac{N}{(N-1)^2}
  \right).
\]
The proof splits on the triangular-pair-count fact that, for \(q\ge2\), either
\(P=1\) or \(P\ge3\).

The theorem `lowRankLowCollisionLineCovered_of_queryPair_le_card` packages the
two checks, and the small-query endpoint
`visibleStatDist_le_spatialReconstructionBound_add_finiteQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage_of_queryPair_le_card`
now instantiates the finite certificate without carrying
`LowRankLowCollisionLineCovered G q` as an assumption.

The remaining Track A work is now sharply identified:

1. Replace or sharpen \(E_2^+\) and \(E_{\ge3}^{\mathrm{avg}}\) using
   rank/gain-graph cancellation rather than the current positive-part/tail
   packaging.
2. If the constant matters for the final statement, improve the scalar
   coefficient constant \(12\).  This is secondary: the important structural
   milestone is that the entire low-rank contribution is now fourth-order.

There is also now a paper-shaped bridge theorem:

`visibleStatDist_le_spatialReconstructionBound_add_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage_of_queryPair_le_card`

It says that if the finite scalar certificate satisfies
\[
  \alpha_q(G)\le \frac{c}{N^2},
\]
then the visible bound becomes
\[
\begin{aligned}
  \operatorname{Adv}_q
  \le{}&
  B_q(N)
  +
  c\frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^4}\\
  &+
  E_2^+(q,N)
  +
  E_{\ge3}^{\mathrm{avg}}(q,N).
\end{aligned}
\]
This was the first formal theorem in the file whose low-rank residual has the
desired fourth-order shape without the old low-collision assumption.  The
coefficient input is now discharged with \(c=12\) by
`lowRankQuadraticEnvelopeCoefficient_le_twelve_inv_sq_of_queryPair_le_card`.

The point is not that these hypotheses are the final theorem; the point is that
the remaining sign-control problem has been reduced to a one-dimensional
coefficient estimate, and the RS endpoint already knows how to convert that
estimate into a fourth-order finite bound.

The coefficient estimate itself has now been split once more so that the next
analytic task is not about finite maxima.  The theorem
`lowRankQuadraticEnvelopeCoefficient_le_of_forall_term_le` is the
`Finset.max'_le` direction for the finite certificate: to prove
\(\alpha_q(G)\le B\), it is enough to prove that every scalar term in the
defining range is at most \(B\).  The closed target version is
`lowRankQuadraticEnvelopeCoefficient_le_inv_sq_of_forall_high_collision`:
if \(c\ge0\) and, for every \(2\le k\le |\operatorname{PairIndex}(q)|\),
\[
  \frac{L(k)-\lambda k}{\binom{k}{2}}
  \le
  \frac{c}{N^2},
\]
then
\[
  \alpha_q(G)\le \frac{c}{N^2}.
\]
The \(k=0,1\) cases no longer appear in this theorem because they are zero in
the max defining \(\alpha_q(G)\).  Thus the next proof obligation is a pure
high-collision scalar inequality for \(k\ge2\), reusing the same normalizer
lower bounds already used for the \(k=0,1\) line checks.

That reuse has now been made formal.  The scalar bridge
`highCollisionNormalizedPositivePart_le_inv_sq_of_scalar` proves the following
pure real statement.  Let
\[
  r=\frac{(N)_q}{N^q},\qquad P=|\operatorname{PairIndex}(q)|,
  \qquad 2\le k\le P,\qquad 2P\le N.
\]
If \(1-P/N\le r\) and
\[
  \frac{1+(k-2P)/N}{(1-P/N)^2}
  -1
  -
  k(1-P/N)\frac{N}{(N-1)^2}
  \le
  c\,\frac{k(k-1)/2}{N^2},
\]
then
\[
  \frac{
    \max\!\left(
      r^{-2}\left(1+\frac{k-2P}{N}\right)-1,0
    \right)
    -
    k r\frac{N}{(N-1)^2}
  }{k(k-1)/2}
  \le
  \frac{c}{N^2}.
\]
The RS-level theorem
`lowRankQuadraticEnvelopeCoefficient_le_inv_sq_of_first_order_scalar` threads
this through the actual definitions.  Under \(q\ge2\), \(q\le N\), and
\(q(q-1)\le N\), it proves
\[
  \alpha_q(G)\le \frac{c}{N^2}
\]
from only the displayed rational inequality for every
\(2\le k\le P\).  This rational inequality is now proved with constant \(12\)
as `firstOrderHighCollisionScalar_le_twelve`.  The proof uses the slack
coordinates
\[
  a=N-2P,\qquad b=P-k,\qquad c=k-2
\]
and clears denominators against the positive product
\[
  N^2(N-P)^2(N-1)^2.
\]
After this substitution, the numerator is a polynomial with nonnegative
monomials except for one quadratic block, certified by
\[
  0\le \left(b-\frac{c+2}{2}\right)^2.
\]
The polynomial certificate is named
`firstOrderHighCollisionScalarClearedTwelve_nonneg`.

Composing these facts gives the closed small-query endpoint
\[
\boxed{
  \operatorname{Adv}_q
  \le
  B_q(N)
  +
  12\frac{\binom{|\operatorname{PairIndex}(q)|}{2}}{N^4}
  +
  E_2^+(q,N)
  +
  E_{\ge3}^{\mathrm{avg}}(q,N)
}
\]
under \(q\ge2\), \(q\le N\), and \(q(q-1)\le N\).  The falling-factorial lower
bound, normalizer slack, positive part, slope monotonicity, and
\(\binom{k}{2}\)-normalization are therefore no longer open RS obligations.

The endpoint above is intentionally stated with \(E_2^+(q,N)\) still visible.
The current Lean development now has two compatible ways to discharge or
sharpen that term:

- the scalar quadratic-positive route, which is easier to close numerically;
- the exact two-statistic/sign-region route, which is sharper and is now proved
  to be no worse than the scalar route.

The next Track A proof should therefore target the exact sign-region sum when
possible, while using the scalar route as a certified fallback.  In particular,
the earlier idea of deleting the \((K,T)=(0,0)\) fiber under only
\(q(q-1)\le N\) should not be used as a global shortcut: that pointwise sign
condition is stronger than the current small-query hypothesis.  The formal
safe endpoint is the full nonpositive-fiber sign-region theorem, not the
single-fiber deletion theorem.

The rank-\(\ge3\) part has also been refined.  The new definition
`rankTailBeyondTwoConsistentAverageErrorBound` keeps the cycle-consistency
filter from the gain-graph expansion:
\[
  E_{\ge3}^{\mathrm{cons}}(q,N)
  =
  \mathbb E_y
  \left[
    \frac{1}{Z}
    \sum_{\substack{T\subseteq \mathcal E_q\\ r(T)\ge3}}
      \mathbf 1[T\text{ balanced on }y]\,
      N^{q-r(T)}
  \right],
\]
where \(Z=((N)_q)^2/N^q\) is the visible normalizer used by the Lean
development.  The theorem
`rankTailBeyondTwoAverageErrorBound_le_consistentAverageErrorBound` is the
formal triangle-inequality step with the consistency predicate retained.
Composed with the exact two-statistic sign-region endpoint, this gives the
current best structured target:
\[
  \operatorname{Adv}_q
  \le
  B_q(N)
  +
  E_{2,\mathrm{sign}}^+(q,N)
  +
  E_{\ge3}^{\mathrm{cons}}(q,N).
\]
The next mathematical step is now a rarity theorem for the balanced
rank-\(\ge3\) subfamilies in this displayed sum.

The rank-\(\ge3\) part has also been split in a cancellation-aware direction.
The theorem
`collisionSubfamilyRankTailBeyondTwoInt_eq_rankThree_add_tailBeyondThree`
proves the exact signed identity
\[
  T_{\ge3}(y)=T_3(y)+T_{\ge4}(y).
\]
Using this identity, Lean now has the endpoint
\[
  \operatorname{Adv}_q
  \le
  B_q(N)
  +
  E_{3,\mathrm{sign}}^+(q,N)
  +
  E_{\ge4}^{\mathrm{avg}}(q,N),
\]
where \(E_{3,\mathrm{sign}}^+\) is the positive residual of the
rank-three-adjusted signed density and \(E_{\ge4}^{\mathrm{avg}}\) is the
normalized average absolute rank-four-and-higher tail.  This is the correct
next boundary for Track A: prove that the signed rank-three residual is already
fourth-order, then bound the rank-four tail separately.  It is strictly more
informative than the previous consistency-filtered absolute tail for this
purpose, because it separates the rank-three layer before the triangle
inequality is applied.

The rank-four tail has now been pushed one step further.  Lean includes the
consistency-filtered rank-four tail
\[
  E_{\ge4}^{\mathrm{cons}}(q,N)
\]
and proves
\[
  E_{\ge4}^{\mathrm{avg}}(q,N)
  \le
  E_{\ge4}^{\mathrm{cons}}(q,N).
\]
It also includes a closed fallback
\[
  E_{\ge4}^{\mathrm{avg}}(q,N)
  \le
  2^{q(q-1)}\frac{N^{2q-4}}{((N)_q)^2}
  \qquad (q\ge4).
\]
So the proof architecture has reached the point where the only obstruction to
the paper-grade \(B_q(N)+O(q^4/N^4)\) theorem is the signed rank-three positive
residual \(E_{3,\mathrm{sign}}^+\).  The remaining work is no longer a generic
high-rank tail problem.

The paper-facing plug-in theorem for this boundary is now explicit:
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeResidual_add_consistentTail`.
It assumes two named obligations,
`RankThreePositiveResidualBound` and
`RankTailBeyondThreeConsistentAverageBound`, and concludes
\[
  \operatorname{Adv}_q
  \le
  B_q(N)+\varepsilon_3+\varepsilon_{\ge4}.
\]
This is the clean Track A interface after rank-two cancellation: prove a sharp
finite estimate for the signed rank-three positive residual and a separate
gain-graph rarity estimate for balanced rank-four-and-higher subfamilies.
The theorem
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeCoefficientRealBound_add_consistentTail`
goes one step closer to the intended calculation: it replaces the named
rank-three residual hypothesis by the real inequality
\[
  E_3^{+,\mathrm{coeff}}(q,N)-B_q(N)\le \varepsilon_3,
\]
where \(E_3^{+,\mathrm{coeff}}\) is the positive part of the explicit
rank-three alternating-coefficient density.

This coefficient obligation has now been split by query-pair support size.
Lean proves
`compatibleCountRankThreeCoefficientDensityReal_eq_supportLeFour_add_geFive`
and the positive-error consequence
`compatibleCountRankThreeCoefficientPositiveErrorReal_le_supportLeFour_add_geFive`.
The corresponding adaptive endpoint is
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeSupportLeFourRealBound_add_geFiveRealBound_add_consistentTail`.
It reduces the rank-three estimate to:
\[
  E_{3,\le4}^{+,\mathrm{coeff}}(q,N)-B_q(N)\le \varepsilon_{\le4},
  \qquad
  E_{3,\ge5}^{\mathrm{abs}}(q,N)\le \varepsilon_{\ge5}.
\]
The first term is now the finite affine-geometry calculation on supports of
size three or four; the second term is a higher-support remainder to be bounded
by support rarity or a closed counting fallback.
Lean further splits the low-support term:
`compatibleCountRankThreeSupportLeFourCoefficientDensityReal_eq_supportThree_add_four`
and
`compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal_le_supportThree_add_four`
separate exact support-size three from exact support-size four.  The current
sharp endpoint is
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeSupportThreeRealBound_add_fourRealBound_add_geFiveRealBound_add_consistentTail`,
which reduces the remaining estimate to
\[
  E_{3,=3}^{+,\mathrm{coeff}}(q,N)-B_q(N)\le \varepsilon_3,\qquad
  E_{3,=4}^{\mathrm{abs}}(q,N)\le \varepsilon_4,\qquad
  E_{3,\ge5}^{\mathrm{abs}}(q,N)\le \varepsilon_{\ge5}.
\]
This is the finest formal split currently available before doing the local
rank-three support calculations.

The rank-three residual has now been exposed one level deeper.  Lean defines
the field-size-free coefficient
\[
  A_3(y)
  =
  \sum_{\substack{T\subseteq\mathcal E_q\\ r(T)=3}}
    \mathbf 1_{\mathrm{consistent}(T,y)}(-1)^{|T|},
\]
formalized as `rankThreeAlternatingCoefficientInt`, and proves the exact
factorization
\[
  T_3(y)=N^{q-3}A_3(y).
\]
It also rewrites the rank-three-adjusted density and positive residual through
this coefficient:

- `compatibleCountRankThreeDensityReal_eq_coefficientDensity`;
- `compatibleCountRankThreePositiveErrorReal_eq_coefficientPositiveError`.

Thus Track A's current target is sharper than "bound rank three": control the
positive sign region of the explicit coefficient density
\[
  \frac{
    C_{\le1}(y) + N^{q-2}A_2^{\mathrm{eq}}(y) + N^{q-3}A_3(y)}
  {Z_q},
\]
where \(A_2^{\mathrm{eq}}\) is the already-proved rank-two equality-pattern
coefficient and \(Z_q\) is the visible normalizer.  The expected \(O(q^4/N^4)\)
improvement must come from this sign-region control, not from another
triangle-inequality tail bound.

The first structural split of \(A_3(y)\) is also formalized.  Lean proves that
rank-three subfamilies touch at least three query pairs:

\[
  r(T)=3 \quad\Longrightarrow\quad |\operatorname{supp}(T)|\ge 3.
\]

The proof reuses the existing rank-one support classifier and the exact
two-pair rank automaticity theorem; it does not introduce a new graph
formalization.  Consequently,

\[
  A_3(y)
  =
  A_{3,\operatorname{supp}=3}(y)
  +
  A_{3,\operatorname{supp}=4}(y)
  +
  A_{3,\operatorname{supp}\ge5}(y),
\]

formalized as
`rankThreeAlternatingCoefficientInt_eq_supportCard_three_add_four_add_ge_five`.
This is the correct next local-combinatorics boundary:

- support size \(3\): triangle/rank-three local configurations;
- support size \(4\): first four-coordinate affine-dependency configurations;
- support size \(\ge5\): should be treated as a higher-order support remainder,
  not mixed into the low-support sign calculation.

For each fixed support size \(m\), Lean also proves the finite reindexing
identity
\[
  A_{3,\operatorname{supp}=m}(y)
  =
  \sum_{|S|=m} A_{3,\operatorname{supp}=S}(y),
\]
formalized as
`rankThreeAlternatingCoefficientSupportCardEq_eq_sum_pairSupportEq`.  This
puts the next calculations at the exact-support level, matching the rank-two
proof style and avoiding any new enumeration mechanism.

The exact-support layer has also been unfolded into the same pair-local choice
language used by the rank-two triangle calculation.  The new definitions and
bridges are:

- `rankThreePairSupportPiUnionRankCoefficientInt`;
- `rankThreeAlternatingCoefficientPairSupportEqInt_eq_piUnionRank`;
- `rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_piUnionRank`;
- `rankThreeAlternatingCoefficientSupportCardEq_four_eq_sum_piUnionRank`.

These do not yet evaluate the local rank-three terms.  They put the remaining
work into the precise finite form needed for evaluation: for each exact
query-pair support \(S\) of size \(3\) or \(4\), sum over nonempty pair-local
hidden/shifted choices and test global cycle consistency plus graphic rank
three.  This is the direct rank-three analogue of the rank-two local triangle
proof.

One further simplification is now formalized.  The graphic-rank test can be
moved from each pair-local choice to the exact support graph itself.  Lean names
the support rank

\[
  r(S)=r(\text{canonical hidden representative of }S)
\]

as `pairSupportGraphicRank` and proves

\[
  r(T)=r(\operatorname{supp}(T)).
\]

Consequently, for fixed support cardinality \(m\),

\[
  A_{3,\operatorname{supp}=m}(y)
  =
  \sum_{\substack{|S|=m\\ r(S)=3}}
    A_{3,\operatorname{supp}=S}^{\mathrm{no\ rank}}(y),
\]

formalized as
`rankThreeAlternatingCoefficientSupportCardEq_eq_sum_supportRankThree_noRank`.
Supports with \(r(S)\ne 3\) are proved to contribute zero, and supports with
\(r(S)=3\) use the no-rank pair-local choice sum.  This is a genuine narrowing
of the rank-three problem: the remaining local calculation only sees exact
support graphs of rank three.

The size-three specialization is now named separately:

\[
  A_{3,\operatorname{supp}=3}(y)
  =
  \sum_{\substack{|S|=3\\ r(S)=3}}
    A_{3,\operatorname{supp}=S}^{\mathrm{no\ rank}}(y),
\]

formalized as
`rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_supportRankThree_noRank`.
This is only a specialization of the general support-rank filter, but it is the
right entry point for the next local calculation because it removes every
support-size-three graph whose canonical support rank is not three.

The next handoff is also formalized.  The predicate
`PairSupportCycleConsistentFactors G y S` says that, for an exact support
\(S\), global cycle consistency of a reassembled pair-local choice is equivalent
to cycle consistency of every individual pair-local fiber.  Lean proves the
adapter
`rankTwoPairSupportPiUnionCoefficientInt_eq_product_of_cycleConsistentFactors`:
under this predicate, the union-form exact-support coefficient equals the
product-form coefficient already used in the rank-two forest layer.

Specializing this to size-three rank-three supports gives the local obligation
`RankThreeSupportCardThreeCycleConsistentFactors`.  If that obligation is
supplied, Lean proves

\[
  A_{3,\operatorname{supp}=3}(y)
  =
  \sum_{\substack{|S|=3\\ r(S)=3}}
    \prod_{p\in S} a_p(y),
\]

where the product-form coefficient is
`rankTwoPairSupportProductCoefficientInt`, and the local pair factors reduce by
the existing theorem
`collisionPairEvents_localPowersetAlternatingCoefficient_ite`.  This is now the
precise finite endpoint for the size-three rank-three calculation: prove the
cycle-consistency factorization for the surviving three-edge support graphs,
then the layer collapses to a known local product form.

The local product form has been made explicit as well.  Lean proves
`rankTwoPairSupportProductCoefficientInt_eq_prod_pairCollisionCoefficientInt`,
so the product-form exact-support coefficient is

\[
  \prod_{p\in S}\left(-2+\mathbf{1}_{y_{p_L}=y_{p_R}}\right).
\]

Combining this with the factorization adapter gives
`rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_pairCollisionProduct`.
Thus the size-three rank-three layer no longer needs any hidden-event
enumeration once `RankThreeSupportCardThreeCycleConsistentFactors` is proved;
it is reduced to an explicit visible-collision polynomial over exact
three-edge rank-three supports.

The size-three rank boundary has now been cross-linked with the existing
rank-two triangle infrastructure.  Lean proves
`pairSupportGraphicRank_eq_two_of_isQueryTriangleSupport`: if
\(S=\operatorname{queryPairSet}(V)\) for a three-coordinate set \(V\), then
the support graph has rank \(2\), not rank \(3\).  The immediate corollary
`pairSupportGraphicRank_ne_three_of_isQueryTriangleSupport` states that genuine
triangle supports never enter the rank-three layer.  The contrapositive form
`not_isQueryTriangleSupport_of_pairSupportGraphicRank_eq_three` is also
available for later exact-support filters.  The support-filtered membership
corollary
`not_isQueryTriangleSupport_of_mem_rankThree_supportCard_three_filter` packages
this in exactly the form needed for the size-three rank-three summation above.

Thus support size \(3\) in the rank-three problem is not the already-solved
rank-two triangle correction.  After the support-rank filter, it consists only
of three-pair supports with graphic rank \(3\).  Equivalently, these are the
three-edge support graphs that survive the exact-support rank test.  The next
local calculation should evaluate their no-rank pair-local choice sum directly,
without reopening the triangle calculation or importing new graph theory.

6. **Separate signed-measure research track.** Signed or virtual LM20
   representatives are a separate research question, not the Track A proof path.
   If pursued, it should add a small finite signed-measure API before
   formalizing any signed LM20 statement:

   - `SignedDist A := A →₀ ℝ`,
   - total mass,
   - \(\ell_1\) norm,
   - pushforward,
   - positive and negative parts if needed.

   The first theorem should be pushforward contraction:

   \[
     \|f_*\eta\|_1\le \|\eta\|_1.
   \]

7. **Jordan/TV bridge.** Prove the finite equal-mass identity

   \[
     \frac12\|\mu-\nu\|_1 = (\mu-\nu)^+(X).
   \]

   Also record the one-point unequal-mass warning: if \(\mu(*)=2\) and
   \(\nu(*)=1\), then half-\(\ell_1\) is \(1/2\) while positive mass is \(1\).

8. **Signed full-behavior theorem.** State and prove the lower-bound half of
   linearized LM20:

   \[
     \frac12\|\mu-\nu\|_1
     \ge
     \operatorname{Adv}(\mathbf R,\mathbf I)
   \]

   whenever \(\mu,\nu\) satisfy all behavioral transcript constraints.  The
   reverse inequality should be stated as relying on the ordinary LM20
   representative theorem, not as a new signed-measure fact.

9. **Partial-constraint collapse counterexample.** Formalize the toy example
   \(X=\{0,1\}\), \(P=\delta_0\), \(Q=\delta_1\), with only total mass
   constrained.  The signed classes overlap, so the signed infimum is \(0\)
   while true TV is \(1\).

10. **Overlapping-basis warning.** Formalize or at least document the counterexample

   \[
     b_1=(1,-1),\qquad b_2=(-1,1),\qquad b_1+b_2=0.
   \]

   This prevents using positive coefficient mass as TV for gain-graph,
   Fourier, Möbius, or ANOVA expansions unless the basis is disjoint and
   sign-controlled.

11. **Signed SoP/XoP analytic layer.** Develop signed expansions only under
    `compatibleCountNat` or density-ratio analysis, not under PDS
    representatives.  The gain-graph formula should be the signed certificate
    for the honest count \(C(y)\); the orbit partition remains the honest TV
    decomposition.

12. **Bibliography and theorem map.** For the paper version, classify references
    by role:

    - direct substrate: finite signed measures, Hahn-Jordan decomposition,
      total variation norm, base-norm/ordered-vector spaces;
    - SoP/XoP combinatorics: Zaslavsky gain graphs and chromatic functions;
    - cryptographic proof analogue: Patarin's H-coefficient technique;
    - proof-technique analogues: Fourier, Möbius/inclusion-exclusion,
      cluster/Mayer/Ursell expansions;
    - loose analogy only: quasi-probability and Wigner negativity.
