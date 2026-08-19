# Conditional Equivalence for SequenceHash

## Abstract

This chapter studies the stable C2SP SequenceHash v1.0.0 construction in the
random-oracle model. For a fixed public domain tag whose customization string
has at most one hash block, the construction has a particularly simple form: a
message is first sent to an inner random-oracle site, and the hidden result is
then sent to a separately framed outer site. The public random-oracle interface
remains available to the distinguisher.

The proof represents the construction, the ideal random oracle, and its
simulator on a common carrier. At each newly activated message, the already
fixed outer sites define a small occupancy profile. Conditional equivalence is
obtained by retaining the common part of the real answer law and the uniform
ideal answer law. If the profile contains $c$ occupied sites,
the exact local loss is

$$
\delta(r)
=
\frac{1}{2N}
\sum_{y\in\mathcal Y}
\left|r(y)-\frac{c}{N}\right|,
$$

and hence

$$
\delta(r)
\le
\frac{c(N-1)}{N^2}.
$$

For $Q$ relevant construction and primitive queries, this gives

$$
\operatorname{Adv}_{\mathrm{indiff}}
\le
\min\!\left\{
1,
\binom Q2\frac{N-1}{N^2}
\right\}.
$$

The bound is exact for two construction queries with the same domain tag.

## 1. Setting

Random systems, representatives, games, conditional equivalence,
$\operatorname{Adv}$, and $\nu$ have the meanings fixed in
[FOUNDATIONS.md](../../FOUNDATIONS.md).

Let $\mathcal Y$ be the hash-output set and write

$$
N=|\mathcal Y|.
$$

Fix a customization string $S$, an item count $n$, the digest-length field
$L$, and the function indicator. Together these values determine one outer
domain tag $t$. Let $\mathcal X_t$ be the set of accepted sequences in that
query class. A point $x\in\mathcal X_t$ is a sequence of exactly $n$ items

$$
(M_1,\ldots,M_n).
$$

Throughout the main theorem,

$$
|S|\le b,
\tag{1.1}
$$

where $b$ is the block length of the underlying hash function. Under (1.1),
the stable v1.0.0 derivation of $S$ is deterministic and makes no additional
random-oracle call.

The C2SP encoding gives an inner site

$$
I:\mathcal X_t\longrightarrow\mathcal D
$$

and an outer-site map for the fixed tag

$$
O_t:\mathcal Y\longrightarrow\mathcal D.
$$

For v1.0.0 these are the byte strings

$$
I(x)
=
K_I\mathbin\|\operatorname{HeaderI}
\mathbin\|\operatorname{Encode}(M_1)
\mathbin\|\cdots\mathbin\|\operatorname{Encode}(M_n)
$$

and

$$
O_t(z)
=
K_O\mathbin\|\operatorname{HeaderO}
\mathbin\|S'
\mathbin\|\operatorname{EncodeMSBF}(n)
\mathbin\|\operatorname{EncodeMSBF}(L)
\mathbin\|z.
$$

Here $K$ is empty, $K_I$ and $K_O$ use tweaks `0x55` and `0xaa`, and the
function indicator is $F_{\rm SEQHSH}=2$.

The fixed-width fields and the suffix length encoding imply the following
properties.

1. $I$ is injective.
2. $O_t$ is injective.
3. The ranges of $I$ and $O_t$ are disjoint.

The theorem below is stated from these three framing properties. Thus its
probabilistic argument is independent of the byte-level encoding proof.

## 2. The two random systems

Let

$$
H\leftarrow U(\mathcal Y^{\mathcal D})
$$

be a public random oracle. The real construction is

$$
\operatorname{SH}^{H}_t(x)
=
H\bigl(O_t(H(I(x)))\bigr).
\tag{2.1}
$$

The real two-interface system is

$$
\mathbf A_t=(\operatorname{SH}^{H}_t,H).
$$

Let

$$
R_t\leftarrow U(\mathcal Y^{\mathcal X_t})
$$

be an ideal random oracle on sequences. The ideal system is

$$
\mathbf B_t=(R_t,\Sigma^{R_t}),
$$

where $\Sigma$ simulates the public $H$ interface while using $R_t$.

A message $x$ is *activated* at the first occurrence of either

- a construction query at $x$, or
- a primitive query at the recognizable inner site $I(x)$.

A primitive query of the form $O_t(z)$ is called an *outer prequery* if it is
made before any activated message has linked that site to an ideal answer.
All other primitive queries are answered by ordinary lazy sampling and do not
enter the bound.

Let $a$ be the number of activated messages and let $p$ be the number of
distinct outer prequeries. Put

$$
Q=a+p.
\tag{2.2}
$$

Repeated queries do not increase these quantities.

## 3. The occupancy profile

Fix a transcript before a new message $x$ is activated. Certain values
$z\in\mathcal Y$ already lead to a fixed outer answer at $O_t(z)$. They arise
from earlier activated messages or from outer prequeries.

Let $C\subseteq\mathcal Y$ be this set of occupied hidden values and put

$$
c=|C|.
$$

For $z\in C$, write $w_z$ for the already fixed answer at $O_t(z)$. Define the
profile

$$
r(y)=|\{z\in C:w_z=y\}|.
\tag{3.1}
$$

Then

$$
\sum_{y\in\mathcal Y}r(y)=c.
\tag{3.2}
$$

### Lemma 3.1 (one-step answer law)

Conditioned on the preceding transcript, the real answer $Y$ for the newly
activated message has distribution

$$
\Pr[Y=y]
=
\frac{r(y)}{N}
+
\frac{N-c}{N^2}
=
\frac1N+\frac1N\left(r(y)-\frac cN\right).
\tag{3.3}
$$

#### Proof

The hidden inner value $Z=H(I(x))$ is uniform. If $Z\in C$, the outer answer
has already been fixed and equals $w_Z$. This contributes $r(y)/N$. If
$Z\notin C$, the outer site is fresh and its answer is uniform; this
contributes $(N-c)/N^2$. Adding the two contributions proves (3.3). $\square$

### Lemma 3.2 (balanced common part)

Let $U$ denote the uniform law on $\mathcal Y$. The exact statistical distance
between the law in (3.3) and $U$ is

$$
\delta(r)
=
\frac{1}{2N}
\sum_{y\in\mathcal Y}
\left|r(y)-\frac cN\right|.
\tag{3.4}
$$

Moreover,

$$
\delta(r)
\le
\frac{c(N-1)}{N^2}.
\tag{3.5}
$$

#### Proof

Equation (3.4) follows by subtracting $1/N$ from (3.3). Equivalently, the real
law is

$$
\left(1-\frac cN\right)U+\frac cN R_C,
$$

where $R_C$ is the empirical distribution of the fixed answers
$(w_z)_{z\in C}$. Hence

$$
\delta(r)
=
\frac cN\,\Delta(R_C,U)
\le
\frac cN\left(1-\frac1N\right),
$$

which is (3.5). Equality in (3.5) occurs when all occupied sites carry the
same answer. $\square$

### Lemma 3.3 (causal common-carrier representative)

There are representatives $A_t\in\mathbf A_t$ and $B_t\in\mathbf B_t$ on a
common carrier and a monotone condition $G$ with the following properties.

1. Before $G$ fails, the two visible transcripts are identical.
2. At the activation described above, conditioned on the preceding good
   transcript, the failure probability is exactly $\delta(r)$.
3. The primitive-interface answers of $B$ are generated causally by a
   simulator $\Sigma^{R_t}$.

#### Proof

Write $P_r$ for the real answer law in (3.3) and $U(y)=1/N$. For every answer
$y$, put

$$
m(y)=\min\{P_r(y),U(y)\}.
\tag{3.6}
$$

The common carrier has a good atom of mass $m(y)$ on which both systems answer
$y$. The remaining real mass $P_r(y)-m(y)$ and ideal mass $U(y)-m(y)$ are put
on bad atoms with their respective visible answers. Any joint refinement of
the two residual measures may be used. Therefore both transition marginals
are exact, including on the bad branch, and

$$
\Pr[\neg G\mid\text{preceding good transcript}]
=
1-\sum_y m(y)
=
\delta(r).
\tag{3.7}
$$

On a good atom, sample the hidden value $Z$ from the real posterior law given
the common answer $y$. If $Z$ selects a fresh outer site, record $y$ at that
site. If $Z$ selects an occupied site, the posterior assigns mass only when its
stored answer is $y$. Thus the linked primitive table agrees in both systems.

The simulator realizes the ideal marginal causally. When $I(x)$ is first
exposed, it queries $R_t(x)$, consults only its current outer table, samples the
corresponding hidden value from the transition kernel above, and records the
link. Earlier outer queries are already in the table; later outer queries are
answered from the link. Generic sites are lazily sampled. The disjointness and
injectivity assumptions ensure that each primitive query has at most one role.

After the first bad atom, set $G$ permanently to false and continue each
representative with its own original transition kernel. This preserves both
full marginals and makes $G$ monotone. Induction over the adaptive transcript
proves all three claims. $\square$

The proof of Lemma 3.3 is the conditional-equivalence step. In particular, it
uses the realized profile $r$ rather than deleting every occupied hidden value.
This is what retains the exact local deficiency (3.4).

## 4. Indifferentiability theorem

### Theorem 4.1 (profile bound)

For every adaptive distinguisher,

$$
\operatorname{Adv}(\mathbf A_t,\mathbf B_t)
\le
\mathbb E\!\left[
\sum_s \delta(r_s)
\right],
\tag{4.1}
$$

where $s$ ranges over first activations and $r_s$ is the occupied-site profile
immediately before activation $s$.

#### Proof

By Lemma 3.3, the representatives are conditionally equivalent until the first
failure of $G$. The conditional-equivalence theorem bounds distinguishing
advantage by the probability that $G$ fails. The chain rule for the monotone
condition and a union bound over its conditional failure probabilities give
(4.1). $\square$

### Theorem 4.2 (finite query bound)

Let $p_s$ be the number of distinct outer prequeries immediately before
activation $s$. Then

$$
\operatorname{Adv}(\mathbf A_t,\mathbf B_t)
\le
\min\!\left\{
1,
\frac{N-1}{N^2}
\left(
\binom a2
+
\sum_s p_s
\right)
\right\}.
\tag{4.2}
$$

Consequently,

$$
\operatorname{Adv}(\mathbf A_t,\mathbf B_t)
\le
\min\!\left\{
1,
\frac{N-1}{N^2}
\left(
\binom a2+ap
\right)
\right\}
\tag{4.3}
$$

and, with $Q$ as in (2.2),

$$
\boxed{
\operatorname{Adv}(\mathbf A_t,\mathbf B_t)
\le
\min\!\left\{
1,
\binom Q2\frac{N-1}{N^2}
\right\}.}
\tag{4.4}
$$

#### Proof

Before the $s$-th activation, an occupied site comes either from an earlier
activation or from an outer prequery. Thus

$$
c_s\le (s-1)+p_s.
$$

Apply (3.5), sum over activations, and use

$$
\sum_{s=1}^{a}(s-1)=\binom a2.
$$

This proves (4.2). The inequality $p_s\le p$ gives (4.3). Finally,

$$
\binom a2+ap
\le
\binom{a+p}{2},
$$

which proves (4.4). $\square$

The quantity $Q$ counts relevant first occurrences, not raw repeated queries.
If a conventional query budget counts every construction and primitive query,
then $Q$ is at most that budget.

## 5. Construction-only security and tightness

If the distinguisher does not query the public primitive interface, distinct
outer tags can be included at once. Conditioned on the shared inner table, the
outer tables are disjoint random functions. Writing $q_t$ for the number of
distinct construction queries under tag $t$, the same proof gives

$$
\operatorname{Adv}
\le
\min\!\left\{
1,
\frac{N-1}{N^2}
\sum_t\binom{q_t}{2}
\right\}.
\tag{5.1}
$$

This refinement is useful in protocols that use customization strings as
public domain tags. It depends on the total number of same-tag pairs, not on a
separate number of users.

For two distinct messages $x,x'$ with the same tag, consider the distinguisher
that accepts exactly when the two answers are equal. In the real system,

$$
\Pr[\operatorname{SH}^{H}_t(x)=\operatorname{SH}^{H}_t(x')]
=
\frac1N+\left(1-\frac1N\right)\frac1N
=
\frac2N-\frac1{N^2}.
$$

For an ideal random oracle the probability is $1/N$. The advantage is therefore

$$
\frac{N-1}{N^2}.
\tag{5.2}
$$

Thus (5.1) and (4.4) are exact when $Q=2$.

## 6. Composition with a concrete hash construction

Suppose a public hash construction $\mathbf H$ is
$\varepsilon_H$-indifferentiable from a random oracle for the required query
and work budgets. Replacing $H$ in (2.1) and applying composition gives

$$
\operatorname{Adv}_{\mathrm{indiff}}
(\operatorname{SequenceHash}[\mathbf H],R)
\le
\varepsilon_H
+
\binom Q2\frac{N-1}{N^2}.
\tag{6.1}
$$

Equation (6.1) is a modular statement. The direct ideal-compression theorem
for the short-customization instance is proved separately in
[A Framing-Aware Simulator for SequenceHash over Merkle--Damgård](SEQUENCEHASH_MD_SMART_SIMULATOR.md).
It analyzes the complete compression-call graph in one conditional-equivalence
proof.

## 7. Comparison with generic double-hash bounds

The leading order in (4.4) is $Q^2/(2N)$. This is the birthday order expected
for double hashing with a public primitive. The present statement adds three
features that a black-box birthday estimate does not expose:

1. the exact local profile loss (3.4);
2. the same-tag refinement in (5.1); and
3. the exact two-query constant in (5.2).

The proof also gives an explicit simulator and a monotone condition suitable
for a later formalization in the random-systems framework.

## References

1. C2SP, [*SequenceHash and SequenceMAC*](https://c2sp.org/sequencehash),
   version 1.0.0, 2026.
2. Dodis, Ristenpart, Steinberger, and Tessaro,
   [*To Hash or Not to Hash Again?*](https://eprint.iacr.org/2013/382),
   CRYPTO 2012 / IACR ePrint 2013/382.
3. Maurer, *Indistinguishability of Random Systems*, 2002.
4. Lanzenberger, *The Theory of Random Systems*, doctoral thesis.

## Appendix A. Multiple tags and arbitrary customization strings

The full two-interface theorem in Section 4 fixes one public tag. The
construction-only corollary (5.1) already permits many tags because distinct
outer prefixes select disjoint random-oracle tables. With public primitive
queries, one inner value can be exposed and then used under several outer tags.
A simultaneous theorem therefore keeps one shared inner-link table and a
separate occupancy profile for every outer tag. The same local law (3.3)
applies, but the causal simulator must activate a tagged cell only when that
cell becomes observable.

When $|S|>b$, v1.0.0 sets

$$
S'=\operatorname{Pad}(H(S),b).
$$

The construction then contains a third random-oracle node whose raw input is
chosen by the caller. A long customization string can equal a syntactically
valid inner or outer query. Therefore the three disjoint-site properties in
Section 1 do not by themselves cover arbitrary $S$.

The unrestricted theorem is obtained by combining the shared multi-tag state
with derivation nodes and proving a schedule lemma for all deterministic overlaps.
Ordinary collisions among distinct derivation outputs remain birthday events;
literal overlap of their raw inputs must be handled by the simulator rather
than charged as a random collision. This schedule lemma is the precise
remaining extension from the theorem above to unrestricted v1.0.0 inputs.

## Appendix B. Ideal compression functions

Merkle--Damgård with its ordinary strengthening is not, by itself,
indifferentiable from a random oracle. Consequently, (6.1) is not a substitute
for a direct proof when the public primitive is an ideal compression function.

The short-customization theorem is given in
[A Framing-Aware Simulator for SequenceHash over Merkle--Damgård](SEQUENCEHASH_MD_SMART_SIMULATOR.md).
It replaces the HMAC key parser and colored-oracle hop by the public v1.0.0
typed path grammar. Its natural work parameter is the total number $\sigma$
of compression calls made by both interfaces, and its simple envelope is

$$
\min\!\left\{1,\frac{2\sigma^2}{N}\right\}.
$$

Extending that theorem to the long-customization nodes described in Appendix
A remains open.

## Appendix C. Other representatives

A maximal coupling of the one-step laws in Lemma 3.2 gives the same local
quantity $\delta(r)$. Signed representatives express (3.3) as a uniform law
plus the centered profile $r-c/N$. Both viewpoints explain the cancellation,
but neither is needed in the main proof: conditional equivalence already uses
the full common part of the two honest laws.

## Appendix D. Version and verification record

The theorem in the main text concerns one fixed tag of the stable v1.0.0
framing under the short-customization hypothesis (1.1). The earlier v0.1.0
draft used a shared, untweaked key block in a different position and a prefix
length encoding; its existing formalization is a separate result.

The evidence labels have the following meanings: **CLOSED** denotes an exact
identity or inequality checked with its boundary cases; **DERIVED** denotes a
complete pen-and-paper derivation not yet independently formalized or peer
reviewed; **OPEN** denotes a precisely identified remaining obligation; and
**CONJECTURAL** is reserved for a target without a complete derivation.

| Item | Status |
| --- | --- |
| Stable v1.0.0 fixed-tag framing facts | **CLOSED** |
| One-step law (3.3), profile distance (3.4), and bound (3.5) | **CLOSED** |
| Two-query matching distinguisher (5.2) | **CLOSED** |
| Causal common-carrier construction, Lemma 3.3 | **DERIVED** |
| Fixed-tag indifferentiability bounds (4.1)--(4.4) | **DERIVED** |
| Construction-only multi-tag refinement (5.1) | **DERIVED** |
| Full two-interface theorem for simultaneous tags | **OPEN** |
| Arbitrary long-customization schedule | **OPEN** |
| Direct short-customization ideal-compression theorem | **DERIVED** |
| Direct long-customization ideal-compression theorem | **OPEN** |
| Lean formalization of stable v1.0.0 | **OPEN** |
