# Foundations for Random-System Proofs

Status: mandatory notation and presentation standard for pen-and-paper work in
this repository.

This chapter follows the order, notation, and theorem structure of Chapter 2 of
David Lanzenberger's thesis and Sections 2--4 of Lanzenberger and Maurer,
*Coupling of Random Systems*. The mathematical definitions and displayed
statements retain the source form. The surrounding prose is adapted. Sections
3 onward are repository extensions and are not attributed to those sources.

All research notes in this repository shall use this chapter as their notation
authority. A note may introduce additional notation only after stating it
explicitly and checking that it does not conflict with the notation below.

Sources:

- [David Lanzenberger, *Coupling Techniques for Cryptographic Proofs*, Chapter 2](<papers/thesis (1).pdf>).
- [David Lanzenberger and Ueli Maurer, *Coupling of Random Systems*, Sections 2--4](papers/LanMau20.pdf).

## 1. Scope and Source Convention

The purpose of this chapter is to fix one vocabulary for the mathematical
work that precedes formalization. It contains the source theory needed by the
research program and the repository extensions used to construct signed
certificates.

## 2. Theory of Random Systems and Games

### 2.1. Introduction

A random system is specified by the behavior visible in one interaction. A
probabilistic discrete system is one concrete distribution over deterministic
systems that realizes this behavior. Distinct probabilistic discrete systems
may therefore represent the same random system.

This distinction permits the representatives of two random systems to be
chosen jointly. The coupling theorem states that suitable representatives and a
suitable coupling attain the optimal distinguishing advantage exactly.

The positive theory is developed first. The signed theory is then obtained by
linear extension. Signed representatives are proof objects and are not
probability distributions.

### 2.2. Preliminaries

#### Notation

For $n\in\mathbb N$, let $[n]$ denote $\{1,\ldots,n\}$, with
$[0]=\varnothing$. The set of sequences of length $n$ over an alphabet
$\mathcal A$ is denoted by $\mathcal A^n$. An element of $\mathcal A^n$ is
written

$$
a^n=(a_1,\ldots,a_n).
$$

The empty sequence is denoted by $\varepsilon$. The sets of finite and
nonempty finite sequences over $\mathcal A$ are

$$
\mathcal A^*=\bigcup_{n\in\mathbb N}\mathcal A^n,
\qquad
\mathcal A^+=\mathcal A^*\setminus\{\varepsilon\}.
$$

A subset $\mathcal D\subseteq\mathcal A^*$ is prefix-closed if membership of a
sequence implies membership of each of its prefixes. If $a^i\in\mathcal A^i$
and $\widehat a^j\in\mathcal A^j$, their concatenation is denoted by

$$
a^i\mathbin{\|}\widehat a^j
  =(a_1,\ldots,a_i,\widehat a_1,\ldots,\widehat a_j).
$$

A total function from $\mathcal X$ to $\mathcal Y$ is written
$f:\mathcal X\to\mathcal Y$. A partial function from $\mathcal X$ to
$\mathcal Y$ is a total function from a subset $\mathcal X'$ of $\mathcal X$
to $\mathcal Y$ and is written $f:\mathcal X\rightharpoonup\mathcal Y$. Its
domain is denoted by $\operatorname{dom}(f)$. If the codomain has a
distinguished zero, the support of $f$ is

$$
\operatorname{supp}(f)=\{x\in\mathcal X:f(x)\ne0\}.
$$

For a proposition $P$, the indicator $\mathbf 1[P]$ is one if $P$ holds and
zero otherwise. For a finite set $\mathcal A$, $U_{\mathcal A}$ denotes the
uniform probability distribution over $\mathcal A$. The law of a random
variable $Z$ is denoted by $\operatorname{Law}(Z)$, and expectation under a
distribution $X$ is denoted by $\mathbb E_X$.

For integers $0\le q\le N$, the falling factorial is

$$
(N)_q=N(N-1)\cdots(N-q+1),
\qquad
(N)_0=1.
$$

The set of injections from $[q]$ to $\mathcal A$ is denoted by
$\operatorname{Inj}([q],\mathcal A)$. The set of permutations of $\mathcal A$
is denoted by $\operatorname{Sym}(\mathcal A)$.

A multiset over $\mathcal A$ is a function $M:\mathcal A\to\mathbb N$. Its
cardinality is

$$
|M|=\sum_{a\in\mathcal A}M(a).
$$

Union, intersection, sum, and difference of multisets are defined pointwise.
Their symmetric difference is

$$
M\mathbin{\triangle}M'
  =(M\cup M')-(M\cap M').
$$

#### Distributions

**Definition 2.1 (distribution).** A distribution over $\mathcal A$ is a
function

$$
X:\mathcal A\longrightarrow\mathbb R_{\ge0}
$$

with finite support. Its weight is

$$
|X|=\sum_{a\in\mathcal A}X(a).
$$

A probability distribution is a distribution of weight one. For a subset
$\mathcal B\subseteq\mathcal A$, the same symbol $X$ also denotes the induced
set function

$$
X(\mathcal B)=\sum_{a\in\mathcal B}X(a).
$$

Unless probability is stated explicitly, a distribution need not have weight
one. Arbitrary weight here means arbitrary nonnegative weight.

**Definition 2.2 (marginal distribution).** Let $X$ be a distribution over
$\mathcal A_1\times\cdots\times\mathcal A_n$. Its $i$-th marginal $X_i$ is

$$
X_i(a_i)
  =\sum_{\substack{a\in\mathcal A_1\times\cdots\times\mathcal A_n\\
                   a_i\text{ fixed}}}X(a).
$$

**Lemma 2.3 (joint distribution).** Let $X_1,\ldots,X_n$ be distributions of
one common weight $p$. There exists a joint distribution of weight $p$ having
$X_1,\ldots,X_n$ as its marginals.

For $p>0$, one possible choice is

$$
X(a_1,\ldots,a_n)
  =p^{-(n-1)}\prod_{i\in[n]}X_i(a_i).
$$

The case $p=0$ is the zero distribution.

#### Statistical distance

**Definition 2.4 (statistical distance).** For distributions $X$ and $Y$ over
$\mathcal A$, define

$$
\begin{aligned}
\delta(X,Y)
  &=\sum_{a\in\mathcal A}\max\{0,X(a)-Y(a)\}\\
  &=|X|-\sum_{a\in\mathcal A}\min\{X(a),Y(a)\}.
\end{aligned}
$$

If $X$ and $Y$ have different weights, $\delta$ need not be symmetric. If they have the
same weight, then

$$
\delta(X,Y)=\frac12\sum_{a\in\mathcal A}|X(a)-Y(a)|.
$$

For probability distributions, $\delta$ is their total-variation distance.

**Lemma 2.5 (decomposition over disjoint supports).** Let
$(\mathcal A_i)_{i\in[n]}$ be a partition of $\mathcal A$. Suppose that $X_i$
and $Y_i$ are supported on $\mathcal A_i$, and put $X=\sum_iX_i$ and
$Y=\sum_iY_i$. Then

$$
\delta(X,Y)=\sum_{i\in[n]}\delta(X_i,Y_i).
$$

#### Transformations

**Definition 2.6 (transformation of a distribution).** Let $X$ be a
distribution over $\mathcal A$ and let $f:\mathcal A\to\mathcal B$ be total.
The $f$-transformation, or pushforward, of $X$ is the distribution $f(X)$ over
$\mathcal B$ given by

$$
f(X)(b)
  =X\!\left(f^{-1}(\{b\})\right)
  =\sum_{\substack{a\in\mathcal A\\f(a)=b}}X(a).
$$

**Lemma 2.7 (data processing).** For distributions $X$ and $Y$ over
$\mathcal A$ and a total function $f:\mathcal A\to\mathcal B$,

$$
\delta(f(X),f(Y))\le\delta(X,Y).
$$

#### Coupling

A joint distribution of $X$ and $Y$ is a distribution over the product set
whose marginals are $X$ and $Y$.

**Lemma 2.8 (coupling lemma).** Let $X$ and $Y$ be probability distributions
over the same set.

1. Every coupling of $X$ and $Y$ satisfies

   $$
   \delta(X,Y)\le\Pr[X\ne Y].
   $$

2. There exists a coupling of $X$ and $Y$ satisfying

   $$
   \delta(X,Y)=\Pr[X\ne Y].
   $$

A coupling satisfying the equality is called maximal.

### 2.3. Definition of the Basic Objects

#### 2.3.1. Deterministic Discrete Systems

The first response of a deterministic system is a function of the first
query. Since each earlier response is already determined by the earlier
queries, the $i$-th response may be represented as a function of the first $i$
queries alone.

**Definition 2.9 (DDS).** A deterministic discrete
$(\mathcal X,\mathcal Y)$-system, or $(\mathcal X,\mathcal Y)$-DDS, is a
partial function

$$
s:\mathcal X^+\rightharpoonup\mathcal Y
$$

with prefix-closed domain. It is finite if $\mathcal X$ is finite and its domain contains
sequences of bounded length. The set of legal first queries is

$$
\operatorname{dom}_1(s)
  =\operatorname{dom}(s)\cap\mathcal X^1.
$$

A DDS records only input-output behavior. Internal state and implementation
details are not part of the object.

**Example 2.10.** The four one-query
$(\{0,1\},\{0,1\})$-DDSs are

$$
\mathsf{zero}(x)=0,\qquad
\mathsf{one}(x)=1,\qquad
\mathsf{id}(x)=x,\qquad
\mathsf{flip}(x)=1-x.
$$

An environment supplies queries to a system and receives its responses. Its
next query may depend on all preceding responses, and it may stop after any
round.

**Definition 2.11 (DDE).** A deterministic discrete environment for an
$(\mathcal X,\mathcal Y)$-DDS, or $(\mathcal Y,\mathcal X)$-DDE, is a partial
function

$$
e:\mathcal Y^*\rightharpoonup\mathcal X
$$

with prefix-closed domain.

**Definition 2.12 (transcript).** The transcript of $s$ in environment $e$ is
denoted by $\operatorname{tr}(s,e)$. It is the sequence

$$
\bigl((x_1,y_1),\ldots,(x_\ell,y_\ell)\bigr),
$$

where, for $i\ge1$,

$$
x_i=e(y_1,\ldots,y_{i-1}),
\qquad
y_i=s(x_1,\ldots,x_i).
$$

The environment is compatible with $s$ if it never queries outside
$\operatorname{dom}(s)$. When $e$ is undefined on the current response
history, the interaction stops.

**Definition 2.13 (parallel composition).** Let
$(s_i)_{i\in[n]}$ be a family of $(\mathcal X,\mathcal Y)$-DDSs. Their
parallel composition is the $(\mathcal X\times[n],\mathcal Y)$-DDS
$[s_1,\ldots,s_n]$ defined as follows. For
$\widehat x\in(\mathcal X\times[n])^*$ ending in $(x,i)$, let
$\widehat x_i\in\mathcal X^*$ be the projection of $\widehat x$ onto the
queries whose second component is $i$. Then

$$
[s_1,\ldots,s_n](\widehat x)=s_i(\widehat x_i).
$$

Thus the second component of a query selects one system, and each component
sees only its own projected query history.

#### 2.3.2. Probabilistic Discrete Systems

Probabilistic systems and environments are distributions over deterministic
systems and environments. The term probabilistic does not by itself imply
weight one.

**Definition 2.14 (PDS).** A probabilistic discrete
$(\mathcal X,\mathcal Y)$-system, or $(\mathcal X,\mathcal Y)$-PDS, is a
distribution over $(\mathcal X,\mathcal Y)$-DDSs such that all DDSs in its
support have one common domain, denoted by $\operatorname{dom}(S)$. A PDS is
finite when the underlying systems are finite with a common query bound.

**Definition 2.15 (PDE).** A probabilistic discrete environment for an
$(\mathcal X,\mathcal Y)$-PDS, or $(\mathcal Y,\mathcal X)$-PDE, is a
distribution over $(\mathcal Y,\mathcal X)$-DDEs.

A PDS contains enough information to rewind a sampled deterministic system and
query it again with the same internal randomness. A random system describes
only one interaction. Consequently, different PDSs may have identical behavior
in every environment.

**Example 2.16 (different representatives of one random bit system).** For
$0\le\alpha\le\frac12$, define

$$
V_\alpha
  =\alpha\,\mathsf{zero}
   +\alpha\,\mathsf{one}
   +\left(\frac12-\alpha\right)\mathsf{id}
   +\left(\frac12-\alpha\right)\mathsf{flip}.
$$

For either query $x\in\{0,1\}$, $V_\alpha$ returns a uniform bit. Hence all
$V_\alpha$ have the
same one-interaction behavior, although they are different distributions over
DDSs.

**Definition 2.17 (equivalent PDSs).** Two
$(\mathcal X,\mathcal Y)$-PDSs $S$ and $T$ are equivalent, denoted by

$$
S\equiv T,
$$

if they have the same domain and

$$
\operatorname{tr}(S,e)=\operatorname{tr}(T,e)
$$

for every compatible deterministic $(\mathcal Y,\mathcal X)$-DDE $e$. Here
$\operatorname{tr}(S,e)$ is the $\operatorname{tr}(\,\cdot\,,e)$-transformation
of $S$. The equivalence class of $S$ is denoted by

$$
[S]=\{S':S'\equiv S\}.
$$

**Lemma 2.18 (nonadaptive characterization).** Two PDSs with the same domain
are equivalent if and only if their transcript distributions agree for every
compatible nonadaptive deterministic environment.

A nonadaptive deterministic environment is determined by a query sequence.
Thus an equivalence class is characterized by the output distributions
observed under all fixed query sequences.

**Notation 2.19 (random system).** A bold symbol such as $\mathbf S$ denotes a
random system, that is, an equivalence class of PDSs. A plain symbol $S$
denotes a particular representative with $S\in\mathbf S$. Since the transcript
distribution
depends only on the class, it is denoted by

$$
\operatorname{tr}(\mathbf S,e).
$$

This document follows the source convention: bold Latin letters denote random
systems, and plain Latin letters denote concrete representatives.

#### 2.3.3. Random Games

A monotone condition records an event that, once true, remains true for every
extension of the interaction. A system equipped with such a condition is
called a game.

**Definition 2.20 (monotone condition and DDG).** A monotone condition for an
$(\mathcal X,\mathcal Y)$-DDS is a predicate

$$
A:\mathcal X^*\longrightarrow\{0,1\}
$$

such that $A(t)=1$ implies $A(t\mathbin{\|}t')=1$ for every extension $t'$.
A deterministic discrete game is a pair $(s,A)$, denoted by $s^A$.

**Definition 2.21 (game transcript).** Let $t=\operatorname{tr}(s,e)$, and let
$t_{\mathcal X}$ be the projection of $t$ onto its query sequence. The
transcript of $s^A$ in $e$ is

$$
\operatorname{tr}(s^A,e)=\bigl(t,A(t_{\mathcal X})\bigr).
$$

**Definition 2.22 (PDG and equivalence).** A probabilistic discrete game is a
distribution over deterministic discrete games with a common domain. Two PDGs
are equivalent if their game-transcript distributions agree under every
compatible deterministic environment.

**Remark 2.23.** The environment does not in general observe the monotone
condition. Revealing it may disclose information about internal randomness
that is absent from the ordinary output transcript.

**Notation 2.24.** A bold expression $\mathbf S^A$ denotes a random game, that is, an
equivalence class of PDGs.

**Definition 2.25 (supremum winning probability).** Let $\mathcal T_w$ be the set of game
transcripts whose final condition bit is one. Define

$$
\nu(\mathbf S^A)
  =\sup_e
     \Pr^{\mathbf S^A,e}
       [\operatorname{tr}(\mathbf S^A,e)\in\mathcal T_w],
$$

where the supremum ranges over compatible deterministic environments.

Deterministic environments suffice because the randomness of a probabilistic
environment can be fixed optimally.

#### 2.3.4. Conditional Equivalence

This subsection fixes the separate CR18 terminology used by the
conditional-equivalence proofs.  It is not a representative-selection
principle.

Let $\widehat S$ be an $(\mathcal X,\mathcal Y\times\{0,1\})$-system with
MBO $A_i$, and let $\widehat S^{-}$ denote the ordinary
$(\mathcal X,\mathcal Y)$-system obtained by ignoring the MBO.

**Definition (CR18 Definition 4.19).** The monitored system $\widehat S$ is
conditionally equivalent to an ordinary $(\mathcal X,\mathcal Y)$-system
$T$, written

$$
\widehat S\mid\!\equiv T,
$$

if, for every $i\ge1$, its response behavior while the MBO is zero equals the
response behavior of $T$:

$$
p^{\widehat S}_{Y^i\mid X^i,A_i=0}
=p^T_{Y^i\mid X^i}.
$$

Equivalently, without division,

$$
p^{\widehat S}_{Y^i,A_i=0\mid X^i}
=p^{\widehat S}_{A_i=0\mid X^i}\,p^T_{Y^i\mid X^i}.
$$

**Theorem (CR18 Theorem 4.17).** If $S=\widehat S^{-}$ and
$\widehat S\mid\!\equiv T$, then the distinguishing advantage between $S$
and $T$ is at most the maximal blind winning probability of $\widehat S$.
Here blind means that the ordinary outputs are blocked, so the winning inputs
are chosen nonadaptively.

Strict conditional equivalence enhances one source system and compares it to
one ordinary target system.  It does not take an infimum over equivalent PDSs
and does not authorize changing representatives.

Maurer--Pietrzak--Renner Lemma 5 is a neighboring but broader statement: it
enhances both systems with MBOs and constructs equal pre-winning mass by a
recursive common-part split.  That symmetric two-game construction can be
exact for each distinguisher and query horizon.  It shall be called
**symmetric common-part game equivalence**, not completeness of strict CR18
conditional equivalence.

Accordingly, a paper using this method shall distinguish the following steps:

1. design of the ideal-world simulator and hence of the target system;
2. optional choice of an equivalent PDS presentation, justified separately;
3. attachment of one or two hidden monotone conditions;
4. proof of strict conditional equivalence or symmetric pre-winning game
   equivalence; and
5. estimation of the corresponding winning probability.

### 2.4. Elementary Results on Random Systems and Games

#### 2.4.1. Distance of Equivalence Classes and the Coupling Theorem

The optimal distinguishing advantage measures the distance between the
transcript behaviors of two random systems.

**Definition 2.26 (optimal distinguishing advantage).** For random systems
$\mathbf S$ and $\mathbf T$ with the same domain, define

$$
\operatorname{Adv}(\mathbf S,\mathbf T)
  =\sup_e
     \delta\!\left(
       \operatorname{tr}(\mathbf S,e),
       \operatorname{tr}(\mathbf T,e)
     \right),
$$

where the supremum ranges over compatible deterministic environments.

For normalized systems, this is also the largest difference in acceptance
probability of any information-theoretic distinguisher.

**Definition 2.27 (distance of several random systems).** Let
$\mathcal S=\{\mathbf S_1,\ldots,\mathbf S_n\}$ be finite, with all systems
having the same domain. Define

$$
\begin{aligned}
\Delta(\mathcal S)
  &=\inf_{(S_1,\ldots,S_n)\in
          \mathbf S_1\times\cdots\times\mathbf S_n}
    \inf_{\mathcal E}
    \Pr^{\mathcal E}[\neg(S_1=\cdots=S_n)]\\
  &=1-
    \sup_{(S_1,\ldots,S_n)\in
          \mathbf S_1\times\cdots\times\mathbf S_n}
    \sup_{\mathcal E}
    \Pr^{\mathcal E}[S_1=\cdots=S_n],
\end{aligned}
$$

where $\mathcal E$ ranges over joint distributions of the representatives.

**Source erratum.** The dissertation prints an infimum, rather than a
supremum, over the representatives after $1-$. That display cannot be correct:
already for two systems it contradicts
$\inf_{S,T}\delta(S,T)$ and the classical coupling identity
$\delta(S,T)=1-\sup_{\mathcal E}\Pr^{\mathcal E}[S=T]$. The equations above
state the mathematically consistent definition used by Definitions 2.28 and
Theorem 2.31.

**Remark (multi-user security).** Definition 2.27 is a simultaneous
many-system coupling distance. It is not the distinguishing advantage of a
multi-user construction.

For $u$ users, let $\mathbf F_i$ and $\mathbf I_i$ be the real and ideal system
of user $i$. Form the user-indexed parallel systems of Definition 2.13,

$$
\mathbf F^{[u]}=[\mathbf F_1,\ldots,\mathbf F_u],
\qquad
\mathbf I^{[u]}=[\mathbf I_1,\ldots,\mathbf I_u].
$$

The native multi-user advantage is the ordinary pairwise advantage

$$
\operatorname{Adv}_{\mathrm{mu}}
  =\operatorname{Adv}\!\left(
      \mathbf F^{[u]},\mathbf I^{[u]}
    \right).
$$

The environment may choose the user index adaptively. Independent users are
represented by a product distribution over their PDS randomness. If users
share a primitive or correlated randomness, that dependence belongs in the
joint representative of the composite real system.

Definition 2.27 is useful when several alternative random systems must be
represented and coupled simultaneously. It may therefore support a multi-world
hybrid argument, but it is not the multi-user game itself.

**Tight multi-user accounting.** Let $c(x,i)$ be the cost of a query to user
$i$, and restrict both tagged systems to the common horizon

$$
\mathcal D_Q
  =\left\{
      \widehat x\in(\mathcal X\times[u])^*:
      \sum_{(x,i)\in\widehat x}c(x,i)\le Q
    \right\}.
$$

The global-work multi-user advantage is

$$
\operatorname{Adv}_{\mathrm{mu}}(Q)
  =\operatorname{Adv}\!\left(
      \left.\mathbf F^{[u]}\right|_{\mathcal D_Q},
      \left.\mathbf I^{[u]}\right|_{\mathcal D_Q}
    \right).
$$

For a completed transcript, write $Q_i$ for the work sent to user $i$, so
$\sum_i Q_i\le Q$. A tight proof should first retain the workload profile and
derive a pathwise failure charge $B(Q_1,\ldots,Q_u)$. The theorem then takes
the maximum of this expression over every profile allowed by the horizon (or
uses a justified expectation of the pathwise charge). Only afterwards should
it pass to a global envelope
$B(Q_1,\ldots,Q_u)\le\overline B(Q)$. A representative intended for this
purpose samples or activates user $i$ only when that user is first queried, and
couples the entire tagged transcript with one global first-disagreement event.
This avoids losses caused solely by a hybrid over all declared users or by
charging users that are never queried.

A bound with no explicit $u$ is meaningful only under such a global budget, or
under an equivalent profile constraint. If a theorem instead permits $q$
queries to each of $u$ users, then the adversary has as many as $uq$ queries;
dependence on $u$ can be information-theoretically unavoidable. Random-system
composition removes proof-induced user losses, not genuine amplification from
additional work or independent trials.

**Definition 2.28 (pair distance).** For two random systems $\mathbf S$ and
$\mathbf T$ with the
same domain, define

$$
\begin{aligned}
\Delta(\mathbf S,\mathbf T)
  &=\inf_{\substack{S\in\mathbf S\\T\in\mathbf T}}\delta(S,T)\\
  &=1-
    \sup_{\substack{S\in\mathbf S\\T\in\mathbf T}}
    \sup_{\mathcal E}\Pr^{\mathcal E}[S=T].
\end{aligned}
$$

The infimum is essential. Equivalent PDSs may themselves have statistical
distance one.

**Theorem 2.29 (several-system comparison).** Let
$\mathcal S=\{\mathbf S_1,\ldots,\mathbf S_n\}$. Then

$$
\max_{\substack{i,j\in[n]\\i\ne j}}
  \Delta(\mathbf S_i,\mathbf S_j)
\le
  \Delta(\mathcal S)
\le
  \bigl(\min\{n,\ell\}-1\bigr)
  \max_{\substack{i,j\in[n]\\i\ne j}}
  \Delta(\mathbf S_i,\mathbf S_j),
$$

where $\ell$ is the number of deterministic systems occurring in the union of the
supports of all representatives.

**Source erratum.** The dissertation prints minima over the pairwise
distances in Theorem 2.29. The extrema must be maxima: simultaneous agreement
is at least as difficult as agreement of the farthest pair, and the proof via
Lemma 2.30 bounds the several-system distance by a multiple of that farthest
pair distance.

**Theorem 2.31 (distance equals advantage).** For finite random systems
$\mathbf S$ and $\mathbf T$ with the same domain,

$$
\Delta(\mathbf S,\mathbf T)
  =\operatorname{Adv}(\mathbf S,\mathbf T).
$$

Moreover, there exist representatives $S\in\mathbf S$ and $T\in\mathbf T$
satisfying

$$
\delta(S,T)=\Delta(\mathbf S,\mathbf T).
$$

**Theorem 2.32 (coupling theorem for random systems).** For two finite random
systems $\mathbf S$ and $\mathbf T$ with the same domain, there exist
representatives $S\in\mathbf S$ and $T\in\mathbf T$ and a coupling of $S$ and
$T$ such that

$$
\operatorname{Adv}(\mathbf S,\mathbf T)=\Pr[S\ne T].
$$

The theorem first chooses the representatives and then couples them. Coupling
arbitrary representatives need not attain the operational distance.

#### 2.4.2. Proof of Theorem 2.31

**The single-query case.** Let
$\mathcal X=\{x_1,\ldots,x_n\}$. A single-query
$(\mathcal X,\mathcal Y)$-DDS may be represented by a tuple

$$
(y_{x_1},\ldots,y_{x_n})\in\mathcal Y^n,
\qquad
s(x_i)=y_{x_i}.
$$

Hence single-query PDSs $S$ and $T$ may be represented as distributions over
$\mathcal Y^n$. If $S_i$ and $T_i$ are their $i$-th marginals, then

$$
\operatorname{Adv}(\mathbf S,\mathbf T)
  =\max_{i\in[n]}\delta(S_i,T_i).
$$

**Lemma 2.33 (joint distributions with maximal marginal distance).** Let
$X_i$ and $Y_i$ be distributions over $\mathcal A_i$. Suppose that all $X_i$
have common weight $p_X$ and all $Y_i$ have common weight $p_Y$. There exist
joint distributions $X$ and $Y$ with these respective marginals such that

$$
\delta(X,Y)=\max_{i\in[n]}\delta(X_i,Y_i).
$$

The lemma supplies equivalent single-query representatives whose distance is
the optimal advantage.

**The general case.** The proof proceeds by induction on the number of
remaining queries. The induction uses unnormalized successor systems.

**Notation 2.34 (successors).** For a DDS $s$ and a legal first query $x$,
define

$$
s^{\uparrow x}(\widehat x^i)
  =s(x\mathbin{\|}\widehat x^i).
$$

For a DDE $e$ and an answer $y$, define

$$
e^{\uparrow y}(\widehat y^i)
  =e(y\mathbin{\|}\widehat y^i).
$$

For a PDS $S$, the successor branch $S^{\uparrow x\downarrow y}$ is obtained
by retaining those systems satisfying $s(x)=y$ and mapping each retained
system to $s^{\uparrow x}$.

If $S$ has weight one, then

$$
\left|S^{\uparrow x\downarrow y}\right|
  =\Pr_{s\leftarrow S}[s(x)=y].
$$

Thus a successor branch is generally not a probability distribution. This is
the reason arbitrary nonnegative weights are part of the basic theory.

Let $\mathcal X'=\operatorname{dom}_1(S)=\operatorname{dom}_1(T)$. Decomposing
over the first answer and using adaptivity after that answer gives

$$
\sup_e\delta\!\left(
  \operatorname{tr}(S,e),\operatorname{tr}(T,e)
\right)
=
\max_{x\in\mathcal X'}
\sum_{y\in\mathcal Y}
\sup_{e'}
\delta\!\left(
  \operatorname{tr}(S^{\uparrow x\downarrow y},e'),
  \operatorname{tr}(T^{\uparrow x\downarrow y},e')
\right).
$$

The induction hypothesis chooses attaining representatives for each successor
branch. Lemma 2.33 then combines the branches belonging to the possible first
queries without increasing their maximum distance.

#### 2.4.3. Game Winnability

**Definition 2.35 (winnable deterministic game).** A deterministic game
$s^A$ is winnable if there exists a legal query sequence for which $A$ becomes
one.

**Definition 2.36 (infimum winnability).** For a random game $\mathbf S^A$,
define

$$
\omega(\mathbf S^A)
  =\inf_{S^A\in\mathbf S^A}
     \Pr_{s^A\leftarrow S^A}[s^A\text{ is winnable}].
$$

**Theorem 2.37 (winnability theorem).** For every finite random game,

$$
\nu(\mathbf S^A)=\omega(\mathbf S^A).
$$

The infimum is attained by a representative of the game.

This theorem is the representative form of the monotone-bad-event method. A
chosen representative may make winnability easy to count; the equality states
that the best representative recovers the optimal winning probability.

## 3. Virtual Random Systems

This section is a linear extension of the preceding theory. Its definitions
are repository definitions. They are not definitions from Lanzenberger and
Maurer.

### 3.1. Virtual Distributions

**Definition 3.1 (virtual distribution).** A virtual distribution over
$\mathcal A$ is a function

$$
\mu:\mathcal A\longrightarrow\mathbb R
$$

with finite support. Its weight and L1 norm are

$$
|\mu|=\sum_{a\in\mathcal A}\mu(a),
\qquad
\|\mu\|_1=\sum_{a\in\mathcal A}|\mu(a)|.
$$

A distribution in the sense of Definition 2.1 is a nonnegative virtual
distribution. A probability distribution is a nonnegative virtual distribution
of weight one.

For a subset $\mathcal B\subseteq\mathcal A$, define

$$
\mu(\mathcal B)=\sum_{a\in\mathcal B}\mu(a).
$$

This value need not lie in $[0,1]$. It is an evaluation, not a probability.

Every virtual distribution has a Jordan decomposition

$$
\mu=\mu^+-\mu^-,
$$

where

$$
\mu^+(a)=\max\{\mu(a),0\},
\qquad
\mu^-(a)=\max\{-\mu(a),0\}.
$$

The supports of $\mu^+$ and $\mu^-$ are disjoint, and

$$
\|\mu\|_1=|\mu^+|+|\mu^-|.
$$

Pushforward, restriction, addition, scalar multiplication, and tensor product
are defined by the same finite sums as in the positive theory.

**Lemma 3.2 (signed data processing).** For a total function
$f:\mathcal A\to\mathcal B$,

$$
\|f(\mu)\|_1\le\|\mu\|_1.
$$

Consequently, for virtual distributions $\mu$ and $\nu$,

$$
\frac12\|f(\mu)-f(\nu)\|_1
  \le\frac12\|\mu-\nu\|_1.
$$

### 3.2. Virtual PDSs and Observational Equivalence

Fix one common domain of DDSs.

**Definition 3.3 (virtual PDS).** A virtual PDS is a virtual distribution over
the DDSs having that domain.

For every compatible deterministic environment $e$, transcript generation is a
linear map

$$
\operatorname{Tr}_e:
  \mathsf{VPDS}\longrightarrow\mathsf{VDist}(\mathsf{Transcripts}).
$$

**Definition 3.4 (virtual equivalence).** Two virtual PDSs $\sigma$ and $\tau$ are
virtually equivalent, denoted by

$$
\sigma\equiv_{\mathrm v}\tau,
$$

if

$$
\operatorname{Tr}_e(\sigma)=\operatorname{Tr}_e(\tau)
$$

for every compatible deterministic environment $e$.

If $\mathbf S$ is an honest random system, define its virtual representative
class by

$$
[\mathbf S]_{\mathrm v}
  =\left\{
      \sigma:
      \operatorname{Tr}_e(\sigma)
        =\operatorname{tr}(\mathbf S,e)
      \text{ for every compatible }e
    \right\}.
$$

The honest representative class is contained in $[\mathbf S]_{\mathrm v}$.

Equivalently, virtual random systems form the quotient vector space

$$
\mathsf{VPDS}\Big/\bigcap_e\ker(\operatorname{Tr}_e).
$$

### 3.3. Signed Representative Distance

**Definition 3.5 (signed representative distance).** For normalized finite
random systems $\mathbf S$ and $\mathbf T$ with a common domain, define

$$
d_{\pm}(\mathbf S,\mathbf T)
  =\inf_{\substack{
      \sigma\in[\mathbf S]_{\mathrm v}\\
      \tau\in[\mathbf T]_{\mathrm v}}}
    \frac12\|\sigma-\tau\|_1.
$$

**Theorem 3.6 (signed representative theorem).** For finite systems with a
common domain and a uniform bound on the number of queries,

$$
d_{\pm}(\mathbf S,\mathbf T)
  =\operatorname{Adv}(\mathbf S,\mathbf T).
$$

**Proof.** Fix $\sigma\in[\mathbf S]_{\mathrm v}$,
$\tau\in[\mathbf T]_{\mathrm v}$, and a compatible environment $e$. Signed
data processing gives

$$
\begin{aligned}
\delta\!\left(
  \operatorname{tr}(\mathbf S,e),
  \operatorname{tr}(\mathbf T,e)
\right)
  &=\frac12
    \left\|
      \operatorname{Tr}_e(\sigma)-\operatorname{Tr}_e(\tau)
    \right\|_1\\
  &\le\frac12\|\sigma-\tau\|_1.
\end{aligned}
$$

Taking the supremum over $e$ and then the infimum over $\sigma$ and $\tau$
yields

$$
\operatorname{Adv}(\mathbf S,\mathbf T)
  \le d_{\pm}(\mathbf S,\mathbf T).
$$

Theorem 2.31 supplies honest representatives $S$ and $T$ for which

$$
\frac12\|S-T\|_1
  =\operatorname{Adv}(\mathbf S,\mathbf T).
$$

Honest representatives are virtual representatives. Hence the reverse
inequality holds. ∎

Negative coefficients therefore do not reduce the exact operational distance.
They enlarge the set of descriptions in which cancellations may be performed
before an absolute value is taken.

### 3.4. Virtual Joints and Signed Coupling

**Definition 3.7 (virtual joint).** Let $\mu$ and $\nu$ be virtual
distributions of the same weight over a finite set $\mathcal A$. A virtual
joint, or quasi-coupling, of $\mu$ and $\nu$ is a virtual distribution $\Gamma$
over $\mathcal A\times\mathcal A$ whose first and second marginals are $\mu$
and $\nu$.

The signed mass

$$
\Gamma\!\left(\{(a,b)\in\mathcal A^2:a\ne b\}\right)
$$

is not a probability and is not a sound disagreement cost. The appropriate
cost is

$$
\operatorname{cost}_{\pm}(\Gamma)
  =\sum_{\substack{a,b\in\mathcal A\\a\ne b}}|\Gamma(a,b)|.
$$

**Lemma 3.8 (signed transport lemma).** For equal-weight virtual
distributions $\mu$ and $\nu$,

$$
\frac12\|\mu-\nu\|_1
  =\inf_{\Gamma}
     \operatorname{cost}_{\pm}(\Gamma),
$$

where the infimum ranges over virtual joints of $\mu$ and $\nu$.

**Proof.** For every $\Gamma$,

$$
\mu(a)-\nu(a)
  =\sum_{b\ne a}\Gamma(a,b)
   -\sum_{b\ne a}\Gamma(b,a).
$$

Summing the triangle inequality over $a$ gives

$$
\frac12\|\mu-\nu\|_1
  \le\operatorname{cost}_{\pm}(\Gamma).
$$

For the reverse inequality, let $\rho=\mu-\nu$. Transport the positive part
$\rho^+$ to the negative part $\rho^-$ with a nonnegative off-diagonal table
of total mass $\frac12\|\rho\|_1$. Put the remaining coefficient of each state
on the diagonal. The resulting virtual joint has marginals $\mu$ and $\nu$ and
the required cost. ∎

When $\mu$ and $\nu$ have weight one and $\Gamma$ is nonnegative,
$\operatorname{cost}_{\pm}(\Gamma)$ is the ordinary
probability of disagreement. Lemma 3.8 then reduces to the classical
maximal-coupling statement.

**Corollary 3.9 (virtual coupling certificate).** Let
$\sigma\in[\mathbf S]_{\mathrm v}$ and
$\tau\in[\mathbf T]_{\mathrm v}$. Every quasi-coupling $\Gamma$ of $\sigma$
and $\tau$ gives

$$
\operatorname{Adv}(\mathbf S,\mathbf T)
  \le\frac12\|\sigma-\tau\|_1
  \le\operatorname{cost}_{\pm}(\Gamma).
$$

A paper shall use the word coupling without qualification only for a
nonnegative joint distribution. It shall use virtual joint or quasi-coupling
when negative coefficients are present.

### 3.5. Successors and Conditioning

Unnormalized restriction and successor operations are linear and therefore
extend to virtual distributions without change.

Normalized conditioning does not extend in general. A nonzero signed fiber may
have weight zero, and division by that weight is undefined. Positivity is what
normally ensures that a zero-weight fiber is pointwise zero.

Every signed proof shall therefore use unnormalized successors. Normalization
is permitted only after proving that the restricted object is nonnegative and
has strictly positive weight.

### 3.6. Signed Accounting Rule

Suppose that a virtual representative is expanded into signed atoms. All
coefficients belonging to the same final atom shall be combined before an
absolute value, positive part, Jordan decomposition, or triangle inequality is
applied.

The permitted order is

$$
\text{expand}
\;\longrightarrow\;
\text{identify equal atoms}
\;\longrightarrow\;
\text{add signed coefficients}
\;\longrightarrow\;
\text{take a norm}.
$$

Termwise absolute values before identification discard the cancellation that
the virtual representative was introduced to preserve.

## 4. Finite Transcript Laws

This section fixes the notation used in the current research program.

### 4.1. Real and Ideal Laws

Let $\Omega$ be a finite transcript space. The real transcript law is denoted
by $P$ and the ideal transcript law by $Q$. If $P$ is absolutely continuous
with respect to $Q$, its likelihood ratio is

$$
L(\omega)=\frac{P(\omega)}{Q(\omega)}.
$$

When $Q$ is uniform on $\Omega$,

$$
L(\omega)=|\Omega|P(\omega).
$$

**Lemma 4.1 (exact L1 expression).** For probability distributions $P$ and
$Q$,

$$
\delta(P,Q)
  =\frac12\mathbb E_Q|L-1|
  =\mathbb E_Q[(L-1)^+]
  =\max_{\mathcal A\subseteq\Omega}\bigl(P(\mathcal A)-Q(\mathcal A)\bigr).
$$

An optimal event is

$$
\mathcal A^*=\{\omega\in\Omega:L(\omega)>1\}.
$$

Thus the likelihood ratio gives both the exact upper bound and a matching
Boolean test.

### 4.2. Proxy Laws and Signed Remainders

Let $C$ be a normalized nonnegative density with respect to $Q$, and write

$$
L=C+R.
$$

The proxy law has density $C$ and the signed remainder has density $R$.

**Lemma 4.2 (proxy comparison).**

$$
\left|
  \delta(P,Q)-\frac12\mathbb E_Q|C-1|
\right|
\le\frac12\mathbb E_Q|R|.
$$

Let $\mathcal A_C=\{C>1\}$. The acceptance gap of $\mathcal A_C$ under $P$
and $Q$ differs from the
proxy distance by at most

$$
\frac12\mathbb E_Q|R|.
$$

Consequently,

$$
\begin{aligned}
\left|\operatorname{Adv}-\operatorname{ProxyAdv}\right|
  &\le \operatorname{Rem},\\
\left|\operatorname{Adv}-\operatorname{AttackGap}\right|
  &\le 2\operatorname{Rem},
\end{aligned}
$$

once the adaptive system has been reduced exactly to $P$ and $Q$, where
$\operatorname{Rem}=\frac12\mathbb E_Q|R|$.

The letter $R$ is reserved for a signed remainder. A random system is denoted
by a bold letter and shall not be denoted by $R$ in the same argument.

### 4.3. Common-Carrier Conditioning

Let $Z$ be an ideal carrier with law $Q$ and let $\mathcal E$ be an event of
positive probability. If the real carrier is $Z$ conditioned on $\mathcal E$,
then its visible
likelihood is

$$
L(\omega)
  =\frac{
      \Pr[\mathcal E\mid\operatorname{visible}(Z)=\omega]
    }{
      \Pr[\mathcal E]
    }.
$$

This identity shall be used before a union bound. It retains cancellations
between compatible-count fibers and identifies the exact transcript statistic.

### 4.4. Adaptive Reduction

A fixed-query law may replace an adaptive interaction only after the reduction
has been stated.

The standard sufficient route is:

1. repeated construction queries are answered consistently and are removed by
   a fresh-query filter;
2. the real and ideal systems have the same deterministic behavior on repeats;
3. the fresh-query law is invariant under relabeling of the unused domain;
4. every adaptive strategy therefore induces the same fresh-answer law as a
   fixed sequence of distinct queries.

If any of these conditions is absent, adaptivity shall remain explicit.

### 4.5. Injection and Collision Notation

For a finite set $\mathcal A$ of size $N$, the normalized injection density on
$\mathcal A^q$ is

$$
\mu_q(a)=
\begin{cases}
\dfrac{N^q}{(N)_q},
  &a\in\operatorname{Inj}([q],\mathcal A),\\[1ex]
0,&\text{otherwise}.
\end{cases}
$$

For $y\in\mathcal A^q$, put

$$
M=\binom q2,
\qquad
K(y)=
\left|\{(i,j):1\le i<j\le q,\ y_i=y_j\}\right|.
$$

$M$ denotes the number of coordinate pairs. $K$ denotes the observed number
of equal-answer pairs. No other quantity in the same note shall be denoted by
$M$ or $K$.

The standard query regimes are

$$
\begin{array}{lll}
\text{sparse:}
  &q/\sqrt N\to0,\\
\text{transition:}
  &\binom q2/N\to\lambda\in(0,\infty),\\
\text{dense:}
  &q/\sqrt N\to\infty\ \text{and}\ q=o(N),\\
\text{saturation:}
  &q=\Theta(N).
\end{array}
$$

The Poisson distribution of mean $\lambda$ is denoted by
$\operatorname{Pois}(\lambda)$. A normal distribution with mean $m$ and
variance $v$ is denoted by $\mathcal N(m,v)$.

All $O(\cdot)$, $o(\cdot)$, and asymptotic-equivalence statements shall name
the limiting variable and the parameter range.

## 5. Combinatorial and Algebraic Expansions

### 5.1. Hoeffding Decomposition

Let $Q$ be a product probability distribution on $\mathcal A^q$ and let
$f:\mathcal A^q\to\mathbb R$. For $S\subseteq[q]$, let $\mathbb E_Sf$ be the
conditional expectation of $f$ given the coordinates in $S$, viewed as a
function on $\mathcal A^q$.

Define

$$
f_S
  =\sum_{T\subseteq S}
     (-1)^{|S|-|T|}\mathbb E_Tf.
$$

Then

$$
f=\sum_{S\subseteq[q]}f_S.
$$

Distinct support components are orthogonal in $L^2(Q)$, and $f_S$ has zero
conditional mean in each coordinate in $S$.

The phrase level $k$ denotes

$$
\sum_{\substack{S\subseteq[q]\\|S|=k}}f_S.
$$

It shall not denote an uncentered k-coordinate marginal.

### 5.2. Partition Möbius Expansion

Let $\Pi(S)$ be the lattice of set partitions of $S$, ordered by refinement. Its
minimum element is the discrete partition and its maximum element is the
one-block partition.

For partitions $\pi\le\sigma$, the Möbius function is denoted by
$\mu_\Pi(\pi,\sigma)$. In
particular,

$$
\mu_\Pi(\widehat0,\pi)
  =\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!.
$$

Injectivity indicators are expanded by Möbius inversion on $\Pi(S)$. A block
records coordinates forced to be equal. A singleton block records a coordinate
not linked to another coordinate.

When singleton components cancel, the remaining partitions shall be described
as singleton-free. The cancellation must be shown before their absolute
weights are summed.

### 5.3. Connected Expansions

A constraint diagram has one vertex for each exposed or hidden variable and
one edge for each equality, permutation, or algebraic compatibility constraint.
A diagram is connected when its underlying undirected graph is connected.

A connected expansion is an identity in which disconnected diagrams have
already canceled or factored into lower-order terms. The phrase connected
remainder may be used only after this identity has been proved.

The support of a diagram is the set of visible coordinates incident to its
connected components. Its order is the number of visible coordinates in that
support.

### 5.4. Gain Graphs

Let $G$ be a finite group. A $G$-gain graph is an oriented graph with a gain
$g(u,v)\in G$ on each oriented edge and

$$
g(v,u)=g(u,v)^{-1}.
$$

The gain of a walk is the ordered product of its edge gains. A closed walk is
balanced if its gain is the identity of $G$. A gain graph is balanced if every
closed walk is balanced.

A switching function is a map $\varphi:V\to G$. It transforms the gains by

$$
g^\varphi(u,v)
  =\varphi(u)^{-1}g(u,v)\varphi(v).
$$

The gain of a closed walk is conjugated by switching. Hence balancedness is
switching invariant.

**Lemma 5.1 (tree and cycle constraints).** Consider vertex labels $z_v\in G$
subject to

$$
z_v=z_u g(u,v)
$$

on every oriented edge.

- A connected tree has exactly $N$ solutions.
- A connected graph has $N$ solutions if it is balanced and no solution
  otherwise.

Thus tree components contribute free labels, whereas cycles contribute
compatibility conditions. Signed gain-graph proofs shall eliminate tree
components before estimating cycle components.

For a graph with $c$ connected components, its cycle rank is

$$
\beta=|E|-|V|+c.
$$

### 5.5. Conflict Graphs and Rook Polynomials

When a transcript imposes forbidden coincidences, the conflict graph has one
vertex for each possible coincidence and edges joining incompatible
coincidences. Let $r_k$ be the number of size-$k$ compatible selections. The
rook
polynomial is

$$
\mathscr R(z)=\sum_{k\ge0}r_kz^k.
$$

Inclusion-exclusion evaluates the avoidance count at $z=-1$. A signed rook
expansion shall combine selections producing the same visible transcript
before taking absolute values.

## 6. Algebraic and Cryptographic Conventions

### 6.1. Finite Groups

The symbol $G$ denotes a finite group and

$$
N=|G|.
$$

The identity is denoted by $1_G$. Multiplication is written in the order in
which it is performed, and inversion is denoted by $g^{-1}$. No commutativity
may be used unless $G$ has been declared abelian.

The commutator subgroup is $[G,G]$, and the abelianization is

$$
G_{\mathrm{ab}}=G/[G,G].
$$

For an abelian group, additive notation may be used. Its identity is then $0$,
its two-torsion subgroup and doubling image are

$$
G[2]=\{g\in G:2g=0\},
\qquad
2G=\{2g:g\in G\}.
$$

For a general group, the square-root profile is

$$
r_G(y)=|\{a\in G:a^2=y\}|.
$$

The character group of a finite abelian group $G$ is denoted by $\widehat G$.
Characters are denoted by $\chi$. Fourier normalization shall be stated at the
first use.

### 6.2. Random Functions and Permutations

A uniform random function from $\mathcal X$ to $\mathcal Y$ is denoted by

$$
\operatorname{URF}(\mathcal X,\mathcal Y).
$$

It answers a fresh query with an independent $U_{\mathcal Y}$ value and repeats the
previous answer on a repeated query.

A uniform random permutation of $\mathcal A$ is denoted by

$$
\pi\leftarrow U\!\left(\operatorname{Sym}(\mathcal A)\right).
$$

Independent random permutations are denoted by $\pi_1,\pi_2,\ldots$. A
uniform random permutation system is denoted by
$\operatorname{URP}(\mathcal A)$. Forward and inverse oracle access shall be
stated explicitly.

### 6.3. Sum or Product of Permutations

For two independent uniform permutations $\pi_1$ and $\pi_2$ of a finite group
$G$, the
two-permutation product construction is

$$
\operatorname{SoP2}_G(x)=\pi_1(x)\pi_2(x).
$$

In an abelian group written additively, the same construction may be written

$$
\operatorname{SoP2}_G(x)=\pi_1(x)+\pi_2(x).
$$

The one-permutation paired-product construction uses disjoint domain points
 $x_i^0$ and $x_i^1$ and returns

$$
\operatorname{SoP1}_G(i)=\pi(x_i^0)\pi(x_i^1).
$$

Equivalently, after $q$ fresh queries,

$$
(A_1,B_1,\ldots,A_q,B_q)
$$

is a uniform ordered injection into $G$ and the visible answers are $A_iB_i$.

These definitions shall not be conflated with a difference construction
$A_i-B_i$ or with Boolean XOR unless the group assumptions make the laws
equal.

### 6.4. Query Parameters

The following symbols are reserved when applicable:

| Symbol | Meaning |
|---|---|
| $q$ | total construction queries |
| $q_e$ | construction or encryption-oracle queries |
| $q_i$ | queries to the $i$-th primitive |
| $\ell$ | maximum blocks in one message |
| $\sigma$ | total queried blocks |
| $N$ | size of the principal finite state space |
| $M$ | $\binom q2$ |
| $K$ | observed pair-collision count |

If a paper uses a different query profile, it shall define the profile before
the game and shall not silently replace a total-query parameter by a
per-oracle parameter.

## 7. Required Structure of Research Notes

Every new pen-and-paper note shall use the following order.

### 7.1. Setting

State the alphabets, random primitives, oracle interfaces, query limits, and
group assumptions. State whether repeated, inverse, public-primitive, and
adaptive queries are allowed.

### 7.2. Real and Ideal Systems

Define both random systems before introducing a bound. Give the exact
transcript law or state the reduction needed to obtain it.

### 7.3. Proof Object

Specify only the proof object actually used.

- For a representative or coupling proof, specify the honest representative,
  virtual representative, coupling, or quasi-coupling.  For a virtual object,
  state the transcript-pushforward identity that makes the certificate
  operationally sound.
- For a conditional-equivalence proof, specify the ideal-world simulator, the
  monitored source system, its MBO, and the ordinary target system.  Do not
  call simulator design or MBO attachment a representative choice.
- For a symmetric common-part proof, specify both monitored systems and their
  equal pre-winning sublaw.
- For an H-technique proof, specify the extended transcript and the good/bad
  partition.

### 7.4. Main Result

State one finite theorem with every constant and parameter restriction. Follow
it with the sparse, transition, dense, and saturation consequences that are
actually covered by that theorem.

### 7.5. Matching Test

Give a deterministic transcript event. Compare its gap with the upper bound.
If no matching test is known, state that explicitly.

### 7.6. Proof

Present exact identities before inequalities. Combine identical signed atoms
before applying a norm. Separate algebraic cancellation from analytic
estimation.

### 7.7. Previous Results

Compare only overlapping models and parameter ranges. State construction,
oracle access, adaptivity, group, query range, and normalization before
claiming an improvement.

### 7.8. Proof Status

Use exactly the following labels:

- **CLOSED.** An exact identity or inequality checked from the stated model.

- **DERIVED.** A complete pen-and-paper derivation awaiting independent formal
  verification.

- **OPEN.** A precisely stated remaining obligation.

- **CONJECTURAL.** A target not yet supported by a complete derivation.

A theorem statement shall not contain a status label. The status appears in
the section title or immediately after the statement.

## 8. Notation Index

| Symbol | Meaning |
|---|---|
| $[n]$ | $\{1,\ldots,n\}$, with $[0]=\varnothing$ |
| $\mathcal A^n,\mathcal A^*,\mathcal A^+$ | sequences of fixed, arbitrary, and positive length |
| $\varepsilon$ | empty sequence |
| $\operatorname{dom}(f),\operatorname{supp}(f)$ | domain and support |
| $X,Y$ | nonnegative finite distributions |
| $\mu,\nu$ | virtual distributions |
| $\lvert X\rvert$ | weight of $X$ |
| $\lVert\mu\rVert_1$ | L1 norm of $\mu$ |
| $\delta$ | statistical distance of concrete distributions |
| $\Delta$ | distance of random-system equivalence classes |
| $\operatorname{Adv}$ | optimal distinguishing advantage |
| $\nu$ | supremum winning probability |
| $\omega$ | infimum winnability |
| $s,t$ | deterministic discrete systems |
| $e$ | deterministic environment |
| $S,T$ | concrete PDS representatives |
| $\mathbf S,\mathbf T$ | random systems |
| $\sigma,\tau$ | virtual PDS representatives |
| $\Gamma$ | coupling or quasi-coupling, with its sign stated |
| $P,Q$ | real and ideal transcript laws |
| $L=dP/dQ$ | likelihood ratio |
| $C$ | proxy density |
| $R$ | signed likelihood remainder |
| $G,N$ | finite group and its order |
| $\pi$ | permutation |
| $(N)_q$ | falling factorial |
| $M=\binom q2$ | number of coordinate pairs |
| $K$ | pair-collision count |
| $\Pi(S)$ | partition lattice of $S$ |
| $\mu_\Pi$ | Möbius function of a partition lattice |
| $\beta$ | cycle rank of a graph |

## 9. Source Map

The positive definitions and results in Sections 2.2--2.4 correspond to:

- thesis Definitions 2.1--2.28, Theorems 2.29, 2.31, 2.32, and 2.37;
- thesis Lemmas 2.3, 2.5, 2.7, 2.8, 2.18, and 2.33;
- thesis Notations 2.19 and 2.34;
- Lanzenberger--Maurer Definitions 1--12, Lemmas 1--6, and Theorems 1--2.

The virtual-distribution definitions and Theorem 3.6 correspond to the
repository's signed linear layer:

- [signed virtual representatives](sketches/signed-virtual-pds.md);
- [RandomSystems/VirtualPDS.lean](RandomSystems/VirtualPDS.lean);
- [bounded attainment](RandomSystems/BoundedAttainment.lean).

The finite-transcript and expansion conventions in Sections 4--6 are the
common vocabulary for:

- [the signed-PDS research program](sketches/signed-pds-research-program.md);
- [SoP2 over general finite groups](sketches/sop2-general-groups.md);
- [SoP1 over general finite groups](sketches/sop1-general-groups.md);
- [the symmetric-cryptography benchmark program](sketches/signed-pds-symmetric-benchmarks.md).
