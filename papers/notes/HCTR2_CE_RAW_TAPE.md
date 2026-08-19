# HCTR2 Without a Switching Hybrid: Symmetric Common-Part Game Equivalence

## Abstract

HCTR2 constructs a variable-input-length tweakable permutation from one
$n$-bit permutation. This chapter gives a direct information-theoretic proof
against the variable-input-length tweakable random permutation. The real and
ideal systems have honest representatives on one i.i.d. random tape. The same
prefix-monotone condition is attached to both representatives, and their
pre-winning transcript sublaws are equal.

The resulting bound is

$$
\operatorname{Adv}
\le
\min\!\left\{
  1,
  \frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\},
\qquad N=2^n.
$$

This is the symmetric two-game branch of Maurer's conditional-equivalence
method: **symmetric common-part game equivalence** in the terminology of
[FOUNDATIONS.md](../../FOUNDATIONS.md). It is not strict CR18 conditional
equivalence, which has one monitored source and one ordinary target. The proof
contains neither an intermediate random function nor a permutation-switching
term. Section 7 proves that neither direct orientation of strict CR18
conditional equivalence can yield the stated negligible bound.

## 1. Setting

Random systems, representatives, games, parallel composition,
$\operatorname{Adv}$, and $\nu$ have the meanings fixed in
[FOUNDATIONS.md](../../FOUNDATIONS.md).

Let

$$
\mathcal B=\{0,1\}^n,
\qquad
N=|\mathcal B|=2^n.
$$

The primitive is a uniform random permutation

$$
\pi\leftarrow U_{\operatorname{Sym}(\mathcal B)}.
$$

The construction has the tagged bidirectional query alphabet

$$
\mathcal X
=
\{\mathsf{enc}(T,P)\}
\mathbin{\uplus}
\{\mathsf{dec}(T,C)\}.
$$

Encryption and decryption queries may be interleaved adaptively. Exact repeats
and inverse queries are answered consistently. A query belongs to the class
$(T,\ell)$ when its data string has length $\ell$.
Data strings have length at least $n$. The environment has no public interface
to the primitive permutation. Block addition is XOR on $\mathcal B$; POLYVAL
uses the configured field structure on $\mathcal B$.

For the $s$-th query, let

$$
m_s=\left\lceil\frac{\ell_s}{n}\right\rceil
$$

be its number of data blocks, and let $d_s$ be the degree parameter of the
POLYVAL call on that query. With the HCTR2 encoding used here,

$$
d_s
=m_s+\left\lceil\frac{|T_s|}{n}\right\rceil.
$$

The environment makes at most $q$ construction queries and satisfies the
pathwise work bound

$$
\sum_s d_s\le\sigma.
$$

The proof is non-vacuous when

$$
\sigma+2<N.
\tag{1.1}
$$

When (1.1) does not hold, the statistical distance is bounded by one.

### 1.1. HCTR2 equations

Write a plaintext and ciphertext as

$$
P=M\mathbin\|P_R,
\qquad
C=U\mathbin\|C_R,
$$

where $M,U\in\mathcal B$. Define

$$
\bar h=\pi(\operatorname{bin}(0)),
\qquad
L=\pi(\operatorname{bin}(1)).
$$

For one query, the primitive sites inferred from the visible data and the
hidden final-block suffix are

$$
\begin{aligned}
MM&=M\oplus H_{\bar h}(T,P_R),\\
UU&=U\oplus H_{\bar h}(T,C_R),\\
S&=MM\oplus UU\oplus L,\\
S_j&=S\oplus\operatorname{bin}(j),
       &&1\le j<m,\\
Y_1\|\cdots\|Y_{m-1}
  &=(P_R\oplus C_R)\|D.
\end{aligned}
\tag{1.2}
$$

Here $D$ is the unused suffix of the last $n$-bit stream block. The real
execution satisfies

$$
\pi(MM)=UU,
\qquad
\pi(S_j)=Y_j
\quad(1\le j<m).
\tag{1.3}
$$

### 1.2. Hash assumptions

The proof uses the following POLYVAL properties. Let $Z,Z'$ denote distinct
encoded hash inputs, let $a\in\mathcal B$, and let $h$ be uniform in
$\mathcal B$. If the degrees of $Z$ and $Z'$ are at most $d$ and $d'$, then

$$
\begin{aligned}
\Pr[H_h(Z)=a]&\le\frac dN,\\
\Pr[H_h(Z)\oplus H_h(Z')=a]
  &\le\frac{\max(d,d')}N,\\
\Pr[h\oplus H_h(Z)=a]&\le\frac dN.
\end{aligned}
\tag{1.4}
$$

These inequalities follow from the corresponding nonzero polynomial
equations in the POLYVAL key. Equality of the encoded hash inputs is handled
by consistency of repeated and inverse queries.

## 2. Real and Ideal Random Systems

Let $\mathbf H$ denote HCTR2 with the primitive permutation sampled uniformly
from $\operatorname{Sym}(\mathcal B)$.

Let $\widetilde{\mathbf T}$ denote the ideal variable-input-length tweakable
permutation. For every class $(T,\ell)$ it samples an independent permutation

$$
\rho_{T,\ell}
\leftarrow
U_{\operatorname{Sym}(\{0,1\}^{\ell})}.
$$

It answers

$$
\mathsf{enc}(T,P)\mapsto\rho_{T,|P|}(P),
\qquad
\mathsf{dec}(T,C)\mapsto\rho_{T,|C|}^{-1}(C).
$$

For pathwise query limits $(q,\sigma)$, write

$$
\operatorname{Adv}_{q,\sigma}(\mathbf H,\widetilde{\mathbf T})
$$

for the supremum, over compatible deterministic environments satisfying
those limits, of the statistical distance between the two transcript laws.

## 3. Proof Object

The proof object consists of two honest representatives on a common positive
probability space and one hidden monotone condition attached to both. No
signed distribution or virtual joint is used.

Fix the finite $(q,\sigma)$ horizon. The common probability space is

$$
\Omega
=(h^*,l^*)\times W\times R_G\times R_F,
\tag{3.1}
$$

with independent coordinates:

1. $h^*,l^*$ are uniform in $\mathcal B$.
2. $W=(W_{s,j})$ is a position-indexed family of i.i.d. uniform elements of
   $\mathcal B$. The index $s$ is the construction-query position and $j$ is
   the primitive-call position within that query.
3. $R_G=(R_{G,0},R_{G,s,j})$ is a family of independent uniform rankings of
   $\mathcal B$; $R_{G,0}$ is reserved for the seed correction.
4. $R_F=(R_{F,s})$ is a family of independent uniform rankings of the
   relevant variable-length response spaces.

The used prefix of the final $W$-cell supplies the visible partial block in
(1.2); its unused suffix supplies $D$. Thus partial and complete final blocks
are treated by the same tape.

Set

$$
\widetilde h=h^*.
$$

If $h^*\ne l^*$, set $\widetilde l=l^*$. If $h^*=l^*$, let
$\widetilde l$ be the first element of an independent ranking $R_{G,0}$ that
differs from $h^*$. Consequently,

$$
(\widetilde h,\widetilde l)
$$

is uniform on the ordered pairs of distinct elements of $\mathcal B$.
Indeed, for $a\ne b$,

$$
\Pr[(\widetilde h,\widetilde l)=(a,b)]
=\frac1{N^2}+\frac1{N^2(N-1)}
=\frac1{N(N-1)}.
\tag{3.2}
$$

### 3.1. Real representative

For $\omega\in\Omega$, define a deterministic system $g_\omega$ by lazy
sampling a global partial permutation $\widehat\pi$. Initially,

$$
\widehat\pi
=\{
\operatorname{bin}(0)\mapsto\widetilde h,
\operatorname{bin}(1)\mapsto\widetilde l
\}.
$$

For a fresh forward evaluation at $x$, propose the assigned raw cell
$W_{s,j}$. If the proposal is outside $\operatorname{ran}(\widehat\pi)$, use
it. Otherwise, use the first element of $R_{G,s,j}$ outside that range. A
fresh inverse evaluation is sampled symmetrically from the unused domain.
Previously defined inputs and outputs are replayed. HCTR2 is then evaluated
against $\widehat\pi$.

Let $u=|\widehat\pi|$ before a fresh assignment and let $v$ be unused. The
probability that the assignment equals $v$ is

$$
\frac1N
+\frac uN\frac1{N-u}
=\frac1{N-u}.
\tag{3.3}
$$

Thus every fresh assignment is uniform on the unused side.

### 3.2. Ideal representative

For $\omega\in\Omega$, define a deterministic system $f_\omega$ as follows.
For every class $(T,\ell)$, maintain the list of established
plaintext-ciphertext pairs. Exact repeats and inverse queries replay the
established partner.

On a fresh encryption query, set

$$
UU=W_{s,0},
\qquad
Y_j=W_{s,j}\quad(1\le j<m_s),
$$

and use (1.2), with hash key $\widetilde h$, to form a raw ciphertext
candidate. If the candidate is unused in the class, return it. Otherwise,
return the first unused class value in the ranking $R_{F,s}$. Fresh decryption
is defined symmetrically, with

$$
MM=W_{s,0}.
$$

For every fixed $\widetilde h$, the map from $W_{s,0}$ and the first
$\ell-n$ stream bits to the variable-length raw response is a bijection. For
encryption, the stream prefix determines $C_R$, and then $W_{s,0}=UU$
determines $U$; the decryption direction is dual. The remaining suffix bits
are unread by the visible response. Hence the raw response is uniform in
$\{0,1\}^{\ell}$. If the class already contains $k$ pairs, each unused
response $v$ has probability

$$
\frac1{2^\ell}
+\frac{k}{2^\ell}\frac1{2^\ell-k}
=\frac1{2^\ell-k}.
\tag{3.4}
$$

It is therefore uniform on the unused class responses.

### Lemma 3.1 (exact marginals)

Let

$$
F=\operatorname{Law}(f_\omega),
\qquad
G=\operatorname{Law}(g_\omega),
\qquad \omega\leftarrow\Omega.
$$

Then

$$
F\in\widetilde{\mathbf T},
\qquad
G\in\mathbf H.
\tag{3.5}
$$

**Proof.** Equation (3.3) is the lazy-sampling rule for one uniform global
permutation conditioned on its two initial values. The distribution of those
values is uniform on ordered distinct pairs, as required for
$(\pi(\operatorname{bin}(0)),\pi(\operatorname{bin}(1)))$.

Equation (3.4) is the lazy-sampling rule for a uniform permutation in a class.
Its transition kernel, conditional on the entire visible past, is uniform on
the unused values and is the same for every value of $\widetilde h$ and every
other class state. Thus the chain rule gives exactly the independent
per-class permutation law. Replays give forward-inverse consistency. ∎

### 3.3. The two monitored systems

Section 6 defines a prefix-monotone condition $\mathsf{Bad}_\omega$ from the
raw tape. Attach it to both deterministic systems and average over the common
carrier:

$$
F^{\mathsf{Bad}}
=\operatorname{Law}(f_\omega,\mathsf{Bad}_\omega),
\qquad
G^{\mathsf{Bad}}
=\operatorname{Law}(g_\omega,\mathsf{Bad}_\omega).
\tag{3.6}
$$

Their stripped systems represent $\widetilde{\mathbf T}$ and $\mathbf H$,
respectively. The certificate to be proved is the symmetric pre-winning
identity

$$
p^{F^{\mathsf{Bad}}}_{Y^i,A_i=0\mid X^i}
=
p^{G^{\mathsf{Bad}}}_{Y^i,A_i=0\mid X^i}
\quad(i\ge1).
\tag{3.7}
$$

This identity specifies the proof contract. It does not assert either
$F^{\mathsf{Bad}}\mid\!\equiv\mathbf H$ or
$G^{\mathsf{Bad}}\mid\!\equiv\widetilde{\mathbf T}$.

## 4. Main Result

### Theorem 4.1 (single-user HCTR2)

Let $N=2^n$. Under the hash assumptions (1.4), every query profile satisfying
the pathwise limits $(q,\sigma)$ obeys

$$
\boxed{
\operatorname{Adv}_{q,\sigma}
  (\mathbf H,\widetilde{\mathbf T})
\le
\min\!\left\{
  1,
  \frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\}.}
\tag{4.1}
$$

### Corollary 4.2 (computational HCTR2)

Let $E$ be a block cipher and let $t$ be the running time of the HCTR2
adversary. Then

$$
\begin{aligned}
\operatorname{Adv}^{\pm\widetilde{\mathrm{prp}}}_{\mathrm{HCTR2}[E]}
&\le
\operatorname{Adv}^{\pm\mathrm{prp}}_E
  (\sigma+2,t+O(\sigma))\\
&\quad+
\min\!\left\{
  1,
  \frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\}.
\end{aligned}
\tag{4.2}
$$

### Theorem 4.3 (multi-user HCTR2)

Consider independent real and ideal systems for users $i\in[u]$, composed by
the tagged parallel construction of Definition 2.13 in
[FOUNDATIONS.md](../../FOUNDATIONS.md). Suppose every interaction path has
user profile $(q_i,\sigma_i)_{i\in[u]}$, and let

$$
a=|\{i:q_i>0\}|.
$$

Then

$$
\boxed{
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{
1,
\frac{
3\sum_i\sigma_i^2
+2\sum_iq_i\sigma_i
+7\sum_i\sigma_i
+2a
}{2N}
\right\}.}
\tag{4.3}
$$

In particular, if

$$
\sum_i\sigma_i\le\sigma,
\qquad
\max_i\sigma_i\le\sigma_{\max},
$$

then $q_i\le\sigma_i$ and $a\le\sigma$ give

$$
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{
1,
\frac{5\sigma_{\max}\sigma+9\sigma}{2N}
\right\}.
\tag{4.4}
$$

## 5. Matching Test

Two deterministic transcript events show that the constant-order and
quadratic-work scales in Theorem 4.1 are genuine.

### 5.1. One-block fixed-point test

For the concrete POLYVAL padding used by HCTR2, take empty tweak and plaintext
$0^n$. In the configured field (in particular for HCTR2's $n=128$ instance)
there is a nonzero field constant

$$
c=x^{1-n},
\qquad c\ne1,
$$

such that, with $h=\pi(0)$, the ciphertext is

$$
C=\pi(ch)\oplus ch.
\tag{5.1}
$$

If $h=0$, then $C=0$. If $h\ne0$, then $ch\ne0$ and $ch\ne h$; moreover
$\pi(ch)$, conditional on $\pi(0)=h$, is uniform on
$\mathcal B\setminus\{h\}$. Therefore

$$
\Pr_{\mathbf H}[C=0]=\frac2N,
\qquad
\Pr_{\widetilde{\mathbf T}}[C=0]=\frac1N,
\tag{5.2}
$$

and, more precisely,

$$
\Pr_{\mathbf H}[C=z]
=
\begin{cases}
2/N,&z=0,\\[1mm]
(N-2)/(N(N-1)),&z\ne0.
\end{cases}
\tag{5.3}
$$

For $z\ne0$, the seed $h=0$ cannot produce $z$, and exactly one nonzero $h$
solves $ch\oplus z=h$, making the required permutation value forbidden. The
other $N-2$ seeds each contribute $1/(N(N-1))$, which proves (5.3).

The exact one-query advantage is $1/N$. For $a$ independently keyed users,
the event that at least one ciphertext is zero has exact gap

$$
(1-1/N)^a-(1-2/N)^a.
\tag{5.4}
$$

Thus the $1/N$ term and active-user dependence cannot both be removed.

### 5.2. XCTR-tail repetition test

Make one known-plaintext encryption query whose XCTR tail exposes $r\ge2$
complete blocks. From the ciphertext and known plaintext, the test recovers

$$
Y_j=\pi(S\oplus\operatorname{bin}(j)),
\qquad 1\le j\le r.
$$

The real blocks are pairwise distinct because their permutation inputs are
pairwise distinct. In the ideal system, one fresh response is uniform over its
entire class, so the exposed blocks are independent uniform $n$-bit strings.
The deterministic event “some exposed tail block repeats” has exact gap

$$
1-\frac{(N)_r}{N^r}.
\tag{5.5}
$$

For independent users exposing $r_i$ complete blocks, the corresponding gap
is

$$
1-\prod_i\frac{(N)_{r_i}}{N^{r_i}}
=
\frac1N\sum_i\binom{r_i}{2}
+O\!\left(
  \frac{\sum_i r_i^3+(\sum_i r_i^2)^2}{N^2}
\right)
\tag{5.6}
$$

in the sparse range. Hence the scale $\sum_i\sigma_i^2/N$ in (4.3) is
unavoidable.

## 6. Proof

### 6.1. The monotone condition

The two representatives are made into games by attaching one condition to
their common carrier.

#### 6.1.1. Essential freshness

Fix $\omega\in\Omega$ and a query sequence $x^i$. Run $f_\omega$ on every
prefix of $x^i$. An encryption query is essentially fresh if its plaintext is
absent from the record of its class. A decryption query is essentially fresh
if its ciphertext is absent. Exact repeats and inverse queries are therefore
not essentially fresh and contribute no new raw primitive sites.

For every essentially fresh query $s$, define its raw entries before either
ranking correction. For encryption,

$$
MM_s=M_s\oplus H_{h^*}(T_s,P_{R,s}),
\qquad
UU_s=W_{s,0},
$$

and for decryption,

$$
UU_s=U_s\oplus H_{h^*}(T_s,C_{R,s}),
\qquad
MM_s=W_{s,0}.
$$

For $1\le j<m_s$, set

$$
Y_{s,j}=W_{s,j},
\qquad
S_{s,j}
=MM_s\oplus UU_s\oplus\widetilde l
 \oplus\operatorname{bin}(j).
\tag{6.1}
$$

#### 6.1.2. Domain and range lists

Through query $i$, let the raw domain list be

$$
\mathcal D_i
=\bigl(
\operatorname{bin}(0),\operatorname{bin}(1),
(MM_s,S_{s,1},\ldots,S_{s,m_s-1})_{s\le i,\,s\text{ fresh}}
\bigr),
\tag{6.2}
$$

and let the raw range list be

$$
\mathcal R_i
=\bigl(
h^*,\widetilde l,
(UU_s,Y_{s,1},\ldots,Y_{s,m_s-1})_{s\le i,\,s\text{ fresh}}
\bigr).
\tag{6.3}
$$

Define

$$
\mathsf{Bad}_\omega(x^i)=1
$$

if at least one query has occurred and either

$$
h^*=l^*,
\tag{6.4}
$$

or one of the lists $\mathcal D_i$ and $\mathcal R_i$ contains a repeated
entry. Equivalently, the condition records the first same-side collision among
the raw inferred permutation sites.

The function

$$
\mathsf{Bad}_\omega:\mathcal X^*\longrightarrow\{0,1\}
$$

is prefix-monotone. It is defined for every seed and every query sequence and
therefore defines a monotone condition independently of an environment.

Let $F^{\mathsf{Bad}}$ and $G^{\mathsf{Bad}}$ be the probabilistic games
obtained by attaching this condition to $f_\omega$ and $g_\omega$,
respectively. Write $\operatorname{ignore}$ for erasing the hidden condition
from a game. By Lemma 3.1,

$$
\operatorname{ignore}(F^{\mathsf{Bad}})\in\widetilde{\mathbf T},
\qquad
\operatorname{ignore}(G^{\mathsf{Bad}})\in\mathbf H.
\tag{6.5}
$$

#### Lemma 6.1 (agreement before the first collision)

For every $\omega\in\Omega$ and every query prefix $x^i$,

$$
\mathsf{Bad}_\omega(x^i)=0
\quad\Longrightarrow\quad
f_\omega(x^j)=g_\omega(x^j)
\quad\text{for every }j\le i.
\tag{6.6}
$$

**Proof.** Proceed by induction on $j$, maintaining that both visible records
agree and that the real partial permutation consists exactly of

$$
\{\operatorname{bin}(0)\mapsto h^*,
  \operatorname{bin}(1)\mapsto l^*\}
\cup
\{MM_r\mapsto UU_r,\ S_{r,k}\mapsto Y_{r,k}:r<j\text{ fresh}\}.
$$

The assumption $\mathsf{Bad}=0$ gives $h^*\ne l^*$, so
$\widetilde l=l^*$. For a non-fresh query, the induction hypothesis makes
both systems classify it identically. An inverse query after a recorded
encryption recomputes $UU_r$, hits the unique preimage $MM_r$, and then hits
all $S_{r,k}$; encryption after a recorded decryption is dual. Exact repeats
use the same chain of hits. Thus both representatives replay the recorded
partner, consume no tape coordinate, and preserve the invariant.

Consider a fresh encryption query. Since $\mathcal D_j$ is injective, $MM_j$
is a new domain point and every $S_{j,k}$ is new. Since $\mathcal R_j$ is
injective, $W_{j,0}$ and the cells $W_{j,k}$ are new range points. Hence the
real representative uses all raw proposals without an $R_G$ correction and
returns the raw HCTR2 response.

If the same raw response were already present as a ciphertext in its ideal
class, equality of the two ciphertexts and the common hash key would imply
$UU_j=UU_r$ for the earlier record $r$. This contradicts injectivity of
$\mathcal R_j$. The ideal representative therefore also uses the raw response.

For decryption, injectivity of $\mathcal R_j$ first makes the
query-determined $UU_j$ a new inverse-output site; injectivity of
$\mathcal D_j$ makes $W_{j,0}$ a new preimage and all counter sites new. If
the raw plaintext repeated an ideal class plaintext, the same cancellation
would imply $MM_j=MM_r$. Thus both representatives again return the same raw
response. This preserves the induction invariant. Every possible first
deviation is therefore either a lookup at an earlier raw site, a rejection of
a raw cell, or an ideal class correction; each is one of the same-side
collisions excluded above. ∎

### 6.2. Symmetric common-part game equivalence

The following positive common-carrier lemma is the exact game-equivalence
step. It is stated without normalized conditioning.

#### Lemma 6.2 (common-carrier pre-winning identity)

Let $\Omega$ be a finite probability space. For each $\omega\in\Omega$, let
$f_\omega$ and $g_\omega$ be deterministic systems with the same domain and
output alphabet, and let

$$
A_\omega:\mathcal X^*\longrightarrow\{0,1\}
$$

be prefix-monotone. Suppose

$$
A_\omega(x^i)=0
\quad\Longrightarrow\quad
f_\omega(x^j)=g_\omega(x^j)
\quad(j\le i).
\tag{6.7}
$$

Attach $A_\omega$ to both systems and denote the resulting probabilistic games
by $F^A$ and $G^A$. Let $F$ and $G$ denote their stripped PDSs. Then, for
every $x^i$ and $y^i$,

$$
\Pr^{F^A}[Y^i=y^i,A_i=0\mid X^i=x^i]
=
\Pr^{G^A}[Y^i=y^i,A_i=0\mid X^i=x^i].
\tag{6.8}
$$

Consequently, the two games have the same pre-winning behavior. For every
compatible deterministic environment $e$, if this common subdistribution is
$c_e$ and has weight $1-\varepsilon_e$, then

$$
\delta\!\left(
  \operatorname{tr}(F,e),
  \operatorname{tr}(G,e)
\right)
\le\varepsilon_e.
\tag{6.9}
$$

**Proof.** The left side of (6.8) is

$$
\sum_{\omega\in\Omega}
\Pr[\omega]\,
\mathbf 1[(f_\omega(x^1),\ldots,f_\omega(x^i))=y^i]\,
\mathbf 1[A_\omega(x^i)=0].
\tag{6.10}
$$

On every nonzero summand, (6.7) permits replacing the complete $f$-response
prefix by the $g$-response prefix. The resulting sum is the right side of
(6.8). Prefix monotonicity identifies $A_i=0$ with absence of a win throughout
the prefix.

For an adaptive $e$, its next query is a deterministic function of the
preceding responses. Multiplying (6.8) by these deterministic transition
indicators, or equivalently repeating the same carrier sum directly for the
closed interaction, gives one common pre-winning transcript subdistribution
$c_e$. Write the two ordinary transcript laws as

$$
P_e=c_e+r_{F,e},
\qquad
Q_e=c_e+r_{G,e},
$$

where both residuals are nonnegative. Since $P_e$ and $Q_e$ have weight one,
both residuals have weight $\varepsilon_e=1-|c_e|$. Hence

$$
\delta(P_e,Q_e)
=\frac12\lVert r_{F,e}-r_{G,e}\rVert_1
\le\frac12(|r_{F,e}|+|r_{G,e}|)
=\varepsilon_e.
$$

This proves (6.9) without any blind-environment reduction. ∎

Applying Lemma 6.2 with $A=\mathsf{Bad}$ and using Lemma 6.1 gives

$$
\Pr^{F^{\mathsf{Bad}}}
  [Y^i=y^i,\mathsf{Bad}_i=0\mid X^i=x^i]
=
\Pr^{G^{\mathsf{Bad}}}
  [Y^i=y^i,\mathsf{Bad}_i=0\mid X^i=x^i].
\tag{6.11}
$$

This is symmetric common-part game equivalence: both systems carry a monitor,
and (6.11) is their equal pre-winning sublaw. Lemma 6.2 yields

$$
\operatorname{Adv}_{q,\sigma}
  (\mathbf H,\widetilde{\mathbf T})
\le
\nu(F^{\mathsf{Bad}}),
\tag{6.12}
$$

where $\nu$ is the supremum winning probability of Definition 2.25 in
[FOUNDATIONS.md](../../FOUNDATIONS.md). The two winning probabilities are
equal for each fixed environment because both are one minus the weight of the
common sublaw. Equation (6.5) identifies the stripped games with the ideal and
real systems.

### 6.3. Probability of the monotone condition

It remains to bound the probability of a raw collision in the ideal-side game
$F^{\mathsf{Bad}}$.

#### Lemma 6.3 (ideal-prefix posterior constancy)

Fix a deterministic environment and a query position $s$. Conditional on a
visible $F$-transcript through position $s-1$, the joint law of

$$
h^*,l^*,R_G,
W_{s,\bullet},W_{s+1,\bullet},\ldots,
$$

the unread suffixes of earlier $W$-cells, and the rankings
$R_{F,s},R_{F,s+1},\ldots$ is their prior product law.

**Proof.** A replay has a deterministic visible response. At each prior
essentially fresh query $t<s$ of length $\ell$, the used $W$-coordinates form
a uniform raw candidate in $\{0,1\}^{\ell}$ for every fixed value of $h^*$.
If $k$ class responses are already occupied, rejection-once changes this
candidate into a uniform element of the $2^\ell-k$ unused responses. Hence
the likelihood of each visible response is

$$
\frac1{2^\ell-k},
$$

independently of every coordinate listed in the statement. Multiplying the
step likelihoods and applying Bayes' rule preserves their prior product law.
At the current query, $R_{F,s}$ is averaged over when deriving this kernel; it
is omitted from the future-coordinate statement after that response has been
observed. No claim is made after fixing the current ranking. ∎

#### 6.3.1. Slot-wise first-collision decomposition

Charge the seed event $h^*=l^*$ separately. It has probability $1/N$. On its
complement, $\widetilde l=l^*$. For every later collision, take the first
query position $s$ at which either $\mathcal D_s$ or $\mathcal R_s$ ceases to
be injective. Earlier raw entries can then be written in the inference form
(1.2), while Lemma 6.3 leaves the current pinning coordinate uniform.

The event is defined on the raw entries *before* either rejection-once
correction. This is load-bearing: an ideal class correction can replace a
repeated raw candidate by an unused visible response, but it cannot erase the
raw slot that caused the correction. At the first failing position, every
earlier executed entry is still raw by Lemma 6.1, so no correction cascade is
missed.

Every collision belongs to one of the following pair families. In the table,
$r<s$ and the indices $i,j$ range over the counter positions of their queries.

| Location | Domain-side pairs | Range-side pairs |
|---|---|---|
| constants | $(\operatorname{bin}(0),\operatorname{bin}(1))$ | $(h^*,l^*)$ |
| constant–query | $(\operatorname{bin}(b),MM_s)$, $(\operatorname{bin}(b),S_{s,j})$ | $(h^*,UU_s)$, $(l^*,UU_s)$, $(h^*,Y_{s,j})$, $(l^*,Y_{s,j})$ |
| within one query | $(MM_s,S_{s,j})$, $(S_{s,i},S_{s,j})$ | $(UU_s,Y_{s,j})$, $(Y_{s,i},Y_{s,j})$ |
| between queries | $(MM_r,MM_s)$, $(MM_r,S_{s,j})$, $(S_{r,i},MM_s)$, $(S_{r,i},S_{s,j})$ | $(UU_r,UU_s)$, $(UU_r,Y_{s,j})$, $(Y_{r,i},UU_s)$, $(Y_{r,i},Y_{s,j})$ |

After substitution from (1.2), the corresponding equations have four forms.

1. **Impossible.** The pair
   $(\operatorname{bin}(0),\operatorname{bin}(1))$ cannot collide. Within one
   query, $S_{s,i}\ne S_{s,j}$ for $i\ne j$.
2. **Mask-key pin.** After intersecting with $h^*\ne l^*$ and substituting
   $\widetilde l=l^*$, the following seven types pin $l^*$ to one value:

   $$
   \begin{gathered}
   l^*=UU_s,\quad l^*=Y_{s,j},\quad
   \operatorname{bin}(b)=S_{s,j},\\
   S_{r,i}=MM_s,\quad MM_r=S_{s,j},\quad MM_s=S_{s,j}.
   \end{gathered}
   $$

   Here $b\in\{0,1\}$, so the displayed constant type contributes two slot
   types. The right side after solving is independent of $l^*$ by Lemma 6.3.
   After dropping the intersection with $h^*\ne l^*$, the pin equation has
   probability exactly $1/N$, so every charged slot has probability at most
   $1/N$. The range-constant event is the seed collision $h^*=l^*$, exactly
   $1/N$.
3. **Hash-key pin.** In the hash direction, the six green cells are

   $$
   \operatorname{bin}(b)=MM_s,\quad MM_r=MM_s,\quad
   h^*=UU_s,\quad UU_r=UU_s,\quad Y_{r,i}=UU_s.
   $$

   Again the first displayed type has two values of $b$. The resulting
   nonconstant polynomial in $h^*$ has probability at most $d_s/N$ or
   $\max(d_r,d_s)/N$ by (1.4). In the opposite query direction the same
   figure cell is instead a raw-cell pin of probability $1/N$.
4. **Raw-cell pin.** Every remaining equation determines one current cell
   $W_{s,j}$ from the visible prefix, the hash and mask keys, hidden earlier
   suffixes, and the other tape cells. This includes the grey directions of
   the preceding hash cells, all $Y_{s,j}$ columns, the possible
   within-query pairs $(MM_s,S_{s,j})$, $(UU_s,Y_{s,j})$ and
   $(Y_{s,i},Y_{s,j})$, and the cross-query pair
   $(S_{r,i},S_{s,j})$. The selected raw cell does not occur in its target.
   Lemma 6.3 makes it independent and uniform, so the relaxed pin equation is
   exactly $1/N$ and the charged slot is at most $1/N$.

The same-class freshness rule guarantees that a hash equation with identical
encoded inputs is either inconsistent or belongs to a repeated or inverse
query. Thus every hash-key equation charged above is nonconstant.

Some cross-query equations contain an unread suffix $D_r$ from an earlier
partial final block. Condition first on $D_r$. The polynomial-root estimate in
(1.4) is uniform in its value, and averaging over $D_r$ leaves the same bound.
This exhaustive inventory is precisely where the without-replacement
inflation disappears: every grey cell is charged through an i.i.d. raw tape
coordinate, not through a corrected permutation response.

#### 6.3.2. Summation

Let

$$
\sigma_m=2+\sum_{s\text{ fresh}}m_s.
$$

There are $\sigma_m$ raw entries on each side of the partial permutation, and

$$
\sigma_m\le\sigma+2.
\tag{6.13}
$$

Charging $1/N$ for each unordered same-side pair gives the baseline

$$
\frac{2\binom{\sigma_m}{2}}N.
$$

The exact refinements to this baseline are

$$
\begin{aligned}
c_b&=-1,\\
c_f&\le2\sigma,\\
c_w&\le0,\\
c_a&\le(q-1)\sigma+\binom\sigma2.
\end{aligned}
\tag{6.14}
$$

Here $c_b$ removes the impossible constant-domain pair; the range-constant
baseline unit is exactly the separately charged event $h^*=l^*$, not an
additional charge. The term $c_f$ is the excess
of the constant–query polynomial bounds over their baseline charges: at most
$2(d_s-1)$ for an encryption query and at most $d_s-1$ for a decryption
query, hence at most $2\sigma$ in total.
The term $c_w$ accounts for the impossible within-query counter-input pairs.
Finally, the adaptive cross-query polynomial excess satisfies

$$
\sum_{r<s}
\left(
  \max(d_r,d_s)-1
  +(m_r-1)(d_s-1)
\right)
\le
(q-1)\sigma+\binom\sigma2.
\tag{6.15}
$$

Combining (6.13)–(6.15) gives, uniformly over every adaptive transcript,

$$
\begin{aligned}
\Pr[\mathsf{Bad}]
&\le
\frac{
  2\binom{\sigma+2}{2}
  -1
  +2\sigma
  +(q-1)\sigma
  +\binom\sigma2
}{N}\\[1mm]
&=
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}.
\end{aligned}
\tag{6.16}
$$

Taking the supremum over compatible environments therefore yields

$$
\nu(F^{\mathsf{Bad}})
\le
\min\!\left\{
1,
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\}.
\tag{6.17}
$$

### 6.4. Assembly

#### Proof of Theorem 4.1

Lemma 3.1 identifies the stripped games with representatives of
$\widetilde{\mathbf T}$ and $\mathbf H$. Lemma 6.1 gives agreement before the
monotone condition fires. Lemma 6.2 converts this pointwise agreement into
equality of the pre-winning transcript sublaws and bounds distance by their
common residual mass. The winning-probability estimate (6.17) is exactly the
right side of (4.1). ∎

#### Proof of Corollary 4.2

Replace the block cipher by a uniform random permutation. The resulting
construction is $\mathbf H$, and Theorem 4.1 bounds its distance from
$\widetilde{\mathbf T}$. The standard substitution distinguisher makes at most
$\sigma+2$ primitive queries and adds the first term of (4.2). ∎

#### Proof of Theorem 4.3

Give user $i$ an independent copy $\Omega_i$ of (3.1), and form the tagged
parallel representatives

$$
[F_1,\ldots,F_u],
\qquad
[G_1,\ldots,G_u].
$$

The global monotone condition is the disjunction of the per-user conditions.
It is activated for user $i$ only when that user's projected query sequence is
nonempty. Off this condition, Lemma 6.1 holds simultaneously for every user,
so Lemma 6.2 applies to the complete tagged transcript.

At a query to user $i$, the unread coordinates of $\Omega_i$ remain
independent of the entire tagged visible prefix. Applying (6.16) to each user
and summing the disjoint first-failure charges gives

$$
\frac1{2N}
\sum_{i:q_i>0}
\left(3\sigma_i^2+2q_i\sigma_i+7\sigma_i+2\right),
$$

which is (4.3). Equation (4.4) follows from

$$
\sum_i\sigma_i^2\le\sigma_{\max}\sigma,
\qquad
\sum_iq_i\sigma_i\le\sum_i\sigma_i^2,
\qquad
a\le\sigma.
$$

∎

## 7. Previous Results

### 7.1. Comparison with the published HCTR2 proof

Crowley, Huckleberry, and Biggers first compare
$\mathbf{HCTR2}[\operatorname{Perm}(n)]$ with a fresh random-response system
by the H-coefficient technique. They obtain

$$
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}.
$$

They then use a PRP–RND switch to reach the variable-input-length tweakable
random permutation, adding $q^2/(2N)$. Thus their final
information-theoretic term is

$$
\frac{3\sigma^2+2q\sigma+q^2+7\sigma+2}{2N}.
$$

Theorem 4.1 uses the same tagged encryption/decryption access, permits adaptive
interleaving, and uses the same pathwise normalization
$\sum_s d_s\le\sigma$. It targets the tweakable random permutation directly,
so the switching term is absent. The tests in Section 5 show that the
remaining $1/N$ and quadratic-work scales are inherent.

### 7.2. Why this is not direct strict CR18 conditional equivalence

Strict CR18 conditional equivalence has one monitored source
$\widehat{\mathbf S}$ and one ordinary target $\mathbf T$. For every fixed
query sequence $x^i$, its division-free identity is

$$
p^{\widehat{\mathbf S}}_{Y^i,A_i=0\mid X^i=x^i}
=s(x^i)\,p^{\mathbf T}_{Y^i\mid X^i=x^i},
\qquad
s(x^i)=p^{\widehat{\mathbf S}}_{A_i=0\mid X^i=x^i}.
\tag{7.1}
$$

The following proposition rules out a sharp *direct* certificate in either
orientation.

#### Proposition 7.1 (direct strict-CE obstruction)

1. If the stripped monitored source is $\mathbf H$ and the ordinary target is
   $\widetilde{\mathbf T}$, there is a one-query input $x$ for which (7.1)
   forces $s(x)=0$. The monitor wins with probability one.
2. If the stripped monitored source is $\widetilde{\mathbf T}$ and the
   ordinary target is $\mathbf H$, the empty-tweak one-block query of
   Section 5.1 forces $s(x)\le1/2$. The monitor wins with probability at least
   $1/2$.

**Proof.** For the first orientation, choose one known-plaintext encryption
query exposing at least two complete XCTR tail blocks. Let $E$ be the visible
event that two exposed blocks repeat. In real HCTR2 the blocks are permutation
outputs at distinct inputs, so

$$
\Pr_{\mathbf H}[E\mid x]=0.
$$

One fresh ideal response is uniform on its complete response space, so
$\Pr_{\widetilde{\mathbf T}}[E\mid x]>0$. The pre-winning law on the left of
(7.1) is a subdistribution of the stripped real law and therefore gives $E$
zero mass. The right side gives it
$s(x)\Pr_{\widetilde{\mathbf T}}[E\mid x]$. Hence $s(x)=0$.

For the reverse orientation, (5.2) and (7.1), evaluated at $C=0$, give

$$
s(x)\frac2N
=
\Pr^{\widehat{\mathbf T}}[C=0,A_1=0\mid x]
\le
\Pr_{\widetilde{\mathbf T}}[C=0\mid x]
=\frac1N.
$$

Thus $s(x)\le1/2$. ∎

The obstruction also survives output augmentation, including a terminal
reveal label: sum (7.1) over every augmented-output fiber erased to one visible
response. The same identity then holds for the visible pushforward, and the
two arguments above apply unchanged. Proposition 7.1 concerns a direct
certificate between these endpoints; it does not rule out a chain through
intermediate systems.

The common-part proof avoids the obstruction because (6.11) asks for one
subdistribution common to *both monitored games*. It does not require that
this subdistribution be a scalar multiple of either endpoint's complete
response law. This is exactly the distinction between strict CR18 conditional
equivalence and Maurer's symmetric game-equivalence construction (Maurer
2013, Definition 11 and Lemma 2; Maurer–Pietrzak–Renner 2007, Lemma 5).

### 7.3. Sources

- Crowley, Huckleberry, and Biggers,
  [*Length-preserving encryption with HCTR2*](../2021-1441.pdf), 2021.
- Maurer,
  [*Cryptography Foundations*](../CR18_LN.pdf), Sections 3–4.
- Maurer,
  [*Conditional Equivalence of Random Systems and Indistinguishability
  Proofs*](../Maurer13b.pdf), 2013.
- Maurer, Pietrzak, and Renner,
  [*Indistinguishability Amplification*](../MaPiRe07.pdf), Lemma 5, 2007.
- Lanzenberger and Maurer,
  [*Coupling of Random Systems*](../LanMau20.pdf), 2020.

## 8. Proof Status

**DERIVED.** Theorem 4.1 and its multi-user extension are complete
pen-and-paper derivations. The proof includes exact endpoint marginals,
seedwise agreement, the adaptive pre-winning identity, posterior constancy,
the exhaustive raw-slot collision inventory, and the paper-exact summation.

**CLOSED.** Proposition 7.1 settles the direct strict-CE question in both
orientations, including visible pushforwards of augmented-output variants.

**OPEN.** Lean formalization of the common carrier, the two monitored games,
their stripped marginals, and the pre-winning mass identity remains separate
work. The existing Lean HCTR2 result uses the H-technique rather than this
certificate.
