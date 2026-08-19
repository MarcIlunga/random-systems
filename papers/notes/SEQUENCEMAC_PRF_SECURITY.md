# PRF Security of SequenceMAC

## Abstract

This chapter gives three complementary security statements for the stable
C2SP SequenceMAC v1.0.0 construction.

1. In the standard model, SequenceMAC is reduced to the strong multi-user PRF
   security of the compression family together with an explicit key-schedule
   term.
2. In the ideal-compression model, the H-technique gives a direct
   extended-transcript bound, with the v1.0.0 schedule contribution displayed
   separately.
3. As a modular corollary, PRF security follows from an allowed-key
   indifferentiability theorem for the general `SequenceFunction`
   construction.

The three statements have different hypotheses and should not be identified.
In particular, indifferentiability of the unkeyed SequenceHash instance does
not by itself imply PRF security of SequenceMAC.

## 1. Setting

Random systems, representatives, games, parallel composition,
$\operatorname{Adv}$, and $\nu$ have the meanings fixed in
[FOUNDATIONS.md](../../FOUNDATIONS.md).

Let the compression function have $c$-bit chaining values and $\beta$-bit
message blocks. Write

$$
\mathcal C=\{0,1\}^c,
\qquad
N=|\mathcal C|=2^c.
$$

Let $H$ be the iterated hash obtained from the compression function and the
specified padding rule. Stable SequenceMAC is

$$
\operatorname{SMAC}_{K,S}(M_1,\ldots,M_n)
=
\operatorname{SequenceFunction}
(H,K,S,F_{\rm SEQMAC};M_1,\ldots,M_n),
$$

where

$$
F_{\rm SEQMAC}=1
$$

and $|K|\ge32$ bytes.

The v1.0.0 derived blocks are

$$
K_I=\operatorname{Derive}(K,H,\mathtt{0x55}),
\qquad
K_O=\operatorname{Derive}(K,H,\mathtt{0xaa}),
$$

and

$$
S'=\operatorname{Derive}(S,H,\mathtt{0x00}).
$$

The evaluated byte string is

$$
H\!\left(
K_O\mathbin\|\operatorname{HeaderO}\mathbin\|S'
\mathbin\|\operatorname{EncodeMSBF}(n)
\mathbin\|\operatorname{EncodeMSBF}(L)
\mathbin\|
H\!\left(
K_I\mathbin\|\operatorname{HeaderI}
\mathbin\|\operatorname{Encode}(M_1)
\mathbin\|\cdots\mathbin\|\operatorname{Encode}(M_n)
\right)
\right).
\tag{1.1}
$$

The position and relation of $K_I$ and $K_O$ are part of the construction.
They may not be replaced by independent NMAC keys without a reduction.

### 1.1. Query parameters

The adversary makes at most $q$ MAC queries. Let $\lambda$ be a pathwise upper
bound on the number of compression calls made by one complete evaluation,
including key and customization derivation when these call $H$. Let

$$
\sigma\le q\lambda
$$

be the total construction work. In the ideal-compression model, the adversary
also makes at most $p$ direct compression queries.

For multi-user security, users are indexed by a finite set $\mathcal U$. The
budgets $q$, $p$, and $\sigma$ are aggregate budgets over all users. No theorem
below introduces a multiplicative factor $|\mathcal U|$.

## 2. PRF systems

For one user, sample a secret key $K$ from the prescribed key distribution and
let

$$
\mathbf M=(x\mapsto\operatorname{SMAC}_{K}(x))
$$

be the real random system. Let

$$
\mathbf R\leftarrow U(\mathcal C^{\mathcal X})
$$

be a uniform random function on accepted SequenceMAC inputs. The PRF advantage
is

$$
\operatorname{Adv}_{\rm prf}(q)
=
\operatorname{Adv}
(\lceil q\rceil\mathbf M,\lceil q\rceil\mathbf R).
\tag{2.1}
$$

For several users, the real system is the parallel family

$$
(\mathbf M_u)_{u\in\mathcal U}
$$

under one shared compression primitive and independently sampled user keys.
The ideal system is the corresponding family of random functions. The native
multi-user distance is taken once between these two parallel systems under the
aggregate query filter.

## 3. Schedule normalization

The security reductions use a normalized cascade whose secret-bearing states
are sampled independently. This section states the exact interface between the
literal v1.0.0 schedule and that cascade.

Let $\mathbf M^{\rm lit}$ be (1.1), and let $\mathbf M^{\rm cas}$ be the
normalized system obtained by replacing the joint effective inner and outer
states generated from $(K_I,K_O)$ by the key objects required by the cascade
theorem. Define

$$
\varepsilon_{\rm KS}
=
\operatorname{Adv}
(\lceil q\rceil\mathbf M^{\rm lit},
 \lceil q\rceil\mathbf M^{\rm cas}).
\tag{3.1}
$$

A schedule-normalization certificate also supplies a trace-preserving map from
every query of $\mathbf M^{\rm cas}$ to the literal NMAC experiment used in
Theorem 4.1 below. The map identifies the effective inner and outer keys,
preserves answers and repeated-query consistency, and proves the advertised
depth and query counts. The distance (3.1) alone is not a substitute for this
trace map.

This is a distance between random systems, not a heuristic failure
probability. It includes precisely the following effects when they occur.

- The two first blocks are related deterministic transforms of one secret key.
- If $|K|$ exceeds the block length, both blocks depend on the shared value
  $H(K)$.
- Outer prefix states vary with the customization and framed length class.
- The literal padding and suffix-length encoding determine the exact cascade
  depth.

The distinct tweaks and headers provide role separation, but role separation
alone does not make the two derived states independent.

### Lemma 3.1 (normalization)

For every adversary and every ideal comparison system $\mathbf T$,

$$
\operatorname{Adv}
(\mathbf M^{\rm lit},\mathbf T)
\le
\varepsilon_{\rm KS}
+
\operatorname{Adv}
(\mathbf M^{\rm cas},\mathbf T).
\tag{3.2}
$$

#### Proof

This is the triangle inequality with (3.1). $\square$

Equation (3.1) is the natural place for a standard-model related-key or
key-schedule assumption. In the ideal-compression proof of Section 5, the
literal schedule can instead be kept inside the extended transcript and
analyzed directly.

## 4. Standard-model PRF theorem

Let

$$
\varepsilon_{\rm mu}(r)
$$

denote the strong multi-user PRF advantage of the compression family for the
collection of effective cascade roles reached within depth $r$. This one
quantity already permits adaptive queries across all users and roles.

The normalized cascade theorem of Backendal, Bellare, Günther, and Scarlata
has the form

$$
\operatorname{Adv}
(\mathbf M^{\rm cas},\mathbf R)
\le
(m+2)\varepsilon_{\rm mu}
+
\frac{q(q-1)}{2N},
\tag{4.1}
$$

where, if $L_{\rm in}$ is the maximum bit length of the normalized NMAC input,

$$
m=1+\left\lceil\frac{L_{\rm in}}{\beta}\right\rceil.
$$

For the literal SequenceMAC schedule, $L_{\rm in}$ is obtained from the encoded
items and the final padding, not by counting input items alone.

### Theorem 4.1 (standard-model SequenceMAC)

Suppose there is a trace-preserving v1.0.0 schedule-normalization certificate
with distance $\varepsilon_{\rm KS}$ and inner depth at most $m$, and

$$
mq<2^\beta.
$$

Then

$$
\boxed{
\operatorname{Adv}_{\rm prf}^{\rm mu}(q)
\le
\varepsilon_{\rm KS}
+
(m+2)\varepsilon_{\rm mu}
+
\frac{q(q-1)}{2N}.}
\tag{4.2}
$$

The same statement with one user gives the single-user theorem.

#### Proof

Apply Lemma 3.1 with the ideal random-function family and then apply (4.1) to
the normalized cascade. The reduction uses one strong multi-user compression
experiment, so the coefficient depends on depth and aggregate queries, not on
the number of users. $\square$

### 4.1. Relation to the classical NMAC bound

If only single-user adaptive and non-adaptive compression assumptions are
available, the Gaži--Pietrzak--Rybár reduction gives the alternative
endpoint

$$
\operatorname{Adv}_{\rm prf}(q)
\le
\varepsilon_{\rm KS}
+
\varepsilon_{\rm ad}
+
(m+1)q\,\varepsilon_{\rm na}
+
\frac{q^2}{N}.
\tag{4.3}
$$

The strong multi-user theorem (4.2) removes the row-hybrid factor $q$ and uses
the exact birthday term $\binom q2/N$.

## 5. Ideal-compression PRF theorem

Assume now that the compression function is a uniform random function

$$
f:\mathcal C\times\{0,1\}^{\beta}\longrightarrow\mathcal C
$$

available both to SequenceMAC and through a public primitive interface. The
comparison system contains an ideal random-function family together with the
same public ideal-compression table. This is a PRF experiment with primitive
access, not an indifferentiability experiment, so no simulator is introduced.

The H-technique extends the transcript with the internal chaining values of
every SequenceMAC evaluation. Its monotone bad condition records the first
event of one of the following forms.

1. A direct primitive query hits a secret-bearing path before that path is
   completed.
2. Two construction paths merge at an internal chaining value in a way not
   reproduced by the ideal random function.
3. A direct primitive query completes an outer path whose final value has
   already been fixed by the ideal system.
4. A key-derivation or framing path meets an inner or outer data path outside
   the separated schedule prescribed by v1.0.0.

On the complement of these events, the real and ideal extended transcripts
have the same conditional law.

Let $\varepsilon_{\rm KS}^{\rm IC}$ denote the H-technique mass assigned to
schedule-specific events in item 4. It includes the actual entropy profile of
the padded derived key blocks. This term is necessary because the C2SP minimum
key length can be smaller than the compression block length; in that case the
first secret-bearing block is not uniform over all $2^\beta$ blocks.

Let $\ell$ denote the padded message-block length in the normalized HMAC trace
of Shen, Zhang, Wang, and Gu. It does not count the additional v1.0.0
key-derivation or outer-prefix calls. Those calls belong to the schedule
embedding measured by $\varepsilon_{\rm KS}^{\rm IC}$.

For $p\ge1$, define the full-block schedule bound

$$
\begin{aligned}
B_{\rm FB}(p,q,\ell,\beta,c)
={}&
\frac{pq\ell}{2^c}
+\frac{5q^2\ell}{2^c}
+\frac{6q^2}{2^c}
+\frac{pq}{2^c}
\\
&+\frac{32q^2\ell^4}{2^{2c}}
+\frac{q^2(\beta+6+\ln p)}{2^{\beta+1}}
+\frac{4pq}{2^\beta}
+\frac{q^2\ell(\ln p+2)}{2^\beta}.
\end{aligned}
\tag{5.1}
$$

The terms with denominator $2^\beta$ are the block-domain estimates for a
full-entropy secret block. The actual stable key distribution and every call
outside the normalized HMAC trace are accounted for by
$\varepsilon_{\rm KS}^{\rm IC}$.

### Theorem 5.1 (ideal-compression SequenceMAC)

Suppose the non-key portions of the v1.0.0 call schedule satisfy the
separated-path hypotheses of the extended-transcript lemmas, its
schedule-specific bad mass is at most $\varepsilon_{\rm KS}^{\rm IC}$, and
the embedded HMAC trace has padded message-block length at most $\ell$, while the
literal evaluation has total work at most $\lambda$. Then

$$
\boxed{
\operatorname{Adv}_{\rm prf,IC}^{\rm mu}(p,q,\lambda)
\le
\min\{1,
\varepsilon_{\rm KS}^{\rm IC}
+B_{\rm FB}(p,q,\ell,\beta,c)\}.}
\tag{5.2}
$$

The theorem is stated for $p\ge1$, as in the source bound. For $p=0$, monotonicity
gives the valid endpoint obtained by evaluating the right-hand side at $p=1$;
terms containing $p$ are not deleted separately.

#### Proof

Expose the internal chaining values in chronological order. The equality on
good follows from the prefix and role separation of the v1.0.0 schedule. The
four event classes above are bounded by the corresponding H-technique
predecessor, merge, completion, and block-domain estimates. The literal
key-schedule events contribute $\varepsilon_{\rm KS}^{\rm IC}$; summing the
remaining estimates gives (5.1). Conditional equivalence of the visible
transcript after forgetting the extension gives (5.2). $\square$

The dominant terms are

$$
\frac{pq\ell+q^2\ell}{N}.
\tag{5.3}
$$

They depend on aggregate work and primitive queries and contain no separate
user-count loss.

## 6. PRF security through indifferentiability

The modular route starts from the general keyed construction, not from the
unkeyed SequenceHash instance.

Let

$$
\mathbf{SF}^{H}
=
\bigl((K,x)\mapsto
\operatorname{SequenceFunction}(H,K,x)\bigr)
$$

denote the allowed-key SequenceFunction system, with the function indicator
and customization included in $x$. Let

$$
\mathbf{KRO}
\leftarrow
U(\mathcal C^{\mathcal K\times\mathcal X})
$$

be a keyed random oracle. Suppose there is a simulator $\Sigma$ such that

$$
\operatorname{Adv}_{\rm indiff}
\bigl((\mathbf{SF}^{H},H),(\mathbf{KRO},\Sigma^{\mathbf{KRO}})\bigr)
\le
\varepsilon_{\rm ind}.
\tag{6.1}
$$

### Theorem 6.1 (indifferentiability-to-PRF corollary)

Sample a secret key $K$, fix $F=F_{\rm SEQMAC}$, and hide the public primitive
interface. Then

$$
\boxed{
\operatorname{Adv}_{\rm prf}(\operatorname{SequenceMAC})
\le
\varepsilon_{\rm ind}.}
\tag{6.2}
$$

#### Proof

Secret-key restriction and removal of the primitive interface are converters.
By data processing, they cannot increase distinguishing advantage. For a
uniformly sampled secret key, the corresponding row of $\mathbf{KRO}$ is a
uniform random function. $\square$

For several users, apply the same converter to several key rows under the one
aggregate query filter. If the ideal multi-user system identifies equal sampled
keys, no key-collision term is introduced. If it instead gives independent
functions to user labels even when their sampled keys coincide, add the exact
distance between those two key-indexing conventions.

## 7. Comparison of the three routes

The standard-model theorem is the appropriate statement when the compression
function is a concrete keyed primitive and its strong multi-user PRF security
is an assumption. Its principal term is depth times the compression advantage,
plus the exact birthday term.

The ideal-compression theorem is information-theoretic. It directly measures
the interaction between construction paths and the public compression table.
Its leading order

$$
\Theta\!\left(\frac{pq\ell+q^2\ell}{N}\right)
$$

matches the known generic attacks on the normalized HMAC trace up to constants
and lower-order terms, provided the v1.0.0 schedule term is smaller.

The indifferentiability corollary is the most modular statement. Once (6.1) is
available for the general allowed-key construction, PRF security follows in
one data-processing step. It may nevertheless give a larger numerical bound
than a direct PRF proof because the indifferentiability adversary receives the
public primitive interface.

## 8. Matching attacks

Two attacks explain the leading terms of the ideal-compression core.

First, choose $q$ distinct messages whose normalized inner traces have a common
suffix of $\ell-1$ blocks. If any pair of traces meets at the same chaining
value before that suffix, their final tags agree in the real system. There are
$\Theta(q^2\ell)$ candidate meetings, each with probability about $1/N$, while
an ideal random-function family has only the ordinary output-collision rate.
This gives advantage

$$
\Theta\!\left(\frac{q^2\ell}{N}\right)
$$

in the birthday range.

Second, use about $p\asymp\sqrt N$ primitive queries to find a cycle in the
functional graph of one fixed-block compression map. Two construction queries
of length $\ell\asymp\sqrt N$ can then test whether their inner traces enter
that cycle. The resulting advantage is constant, matching

$$
\frac{pq\ell}{N}
$$

for $q=2$ up to a constant factor.

These attacks are proved for the normalized HMAC trace. They transfer to
SequenceMAC once the v1.0.0 schedule embedding is shown to preserve the
required common-suffix and fixed-block trace families. An attack matching a
non-negligible $\varepsilon_{\rm KS}$ or
$\varepsilon_{\rm KS}^{\rm IC}$ must instead target the actual C2SP key
schedule.

## References

1. C2SP, [*SequenceHash and SequenceMAC*](https://c2sp.org/sequencehash),
   version 1.0.0, 2026.
2. Gaži, Pietrzak, and Rybár,
   [*Exact PRF-Security of NMAC and HMAC*](https://eprint.iacr.org/2014/578),
   CRYPTO 2014 / IACR ePrint 2014/578.
3. Backendal, Bellare, Günther, and Scarlata,
   [*When Messages are Keys: Is HMAC a dual-PRF?*](https://eprint.iacr.org/2023/861),
   2023.
4. Shen, Zhang, Wang, and Gu,
   [*Tight Generic PRF Security of HMAC and NMAC*](https://eprint.iacr.org/2025/2260),
   2025.
5. Dodis, Ristenpart, Steinberger, and Tessaro,
   [*To Hash or Not to Hash Again?*](https://eprint.iacr.org/2013/382),
   CRYPTO 2012 / IACR ePrint 2013/382.

## Appendix A. Exact stable schedule

Version 1.0.0 differs materially from the public v0.1.0 draft. It uses distinct
tweaked blocks $K_I$ and $K_O$, places each key block before its header, places
the item length after each item, and derives the customization string with
tweak `0x00`. The versioned specification archive records both texts and their
immutable upstream commits.

For $8|K|\le\beta$, the two derived key blocks differ by fixed tweaks of the
first byte. For $8|K|>\beta$, both contain the shared digest $H(K)$ before the
tweak is applied. Consequently, a standard-model proof must either establish
$\varepsilon_{\rm KS}$ from an appropriate related-key assumption or retain the
literal schedule inside its compression experiment.

## Appendix B. Alternative proof techniques

Conditional equivalence can express the ideal-compression proof by taking the
H-technique bad condition as its monotone condition. A raw tape coupling gives
the same event inventory. Signed representatives can center the collision
indicators and may simplify the summation of overlapping path events. These are
alternative analyses of the same random-system distance; they are not needed
for the statements in Sections 4--6.

## Appendix C. Evidence and verification record

The evidence labels have the following meanings: **CLOSED** denotes an exact
identity or inequality checked with its boundary cases; **DERIVED** denotes a
complete pen-and-paper derivation not yet independently formalized or peer
reviewed; **OPEN** denotes a precisely identified remaining obligation; and
**CONJECTURAL** is reserved for a target without a complete derivation.
Published theorems are identified separately.

| Item | Status |
| --- | --- |
| Backendal--Bellare--Günther--Scarlata NMAC endpoint (4.1), including constants and range | **CLOSED; PUBLISHED** |
| Stable v1.0.0 trace-preserving standard-model schedule bridge | **OPEN** |
| Conditional standard-model assembly (4.2) | **DERIVED** |
| Shen--Zhang--Wang--Gu HMAC formula (5.1), with source parameter $\ell$ | **CLOSED; PUBLISHED** |
| Stable v1.0.0 extended-transcript embedding and bound on $\varepsilon_{\rm KS}^{\rm IC}$ | **OPEN** |
| Conditional ideal-compression assembly (5.2) | **DERIVED** |
| Keyed-random-oracle data-processing corollary, Theorem 6.1 | **CLOSED** |
| Allowed-key SequenceFunction indifferentiability premise (6.1) | **OPEN** |
| Matching attacks for the normalized HMAC trace | **CLOSED; PUBLISHED** |
| Attack-preserving transfer to the stable v1.0.0 schedule | **OPEN** |
| Lean formalization of stable v1.0.0 | **OPEN** |

Accordingly, (4.2) and (5.2) are conditional reduction theorems rather than
unconditional concrete bounds for every accepted v1.0.0 input. The existing
Lean development models v0.1.0 and does not yet formalize the v1.0.0 schedule
bridges.
