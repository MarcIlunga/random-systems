# SoP1: coupling one permutation across an ordered-pair partition

> **Separate construction.** This is not the sum of two independent
> permutations proved in `SoP2.md`. Here one uniform permutation is evaluated
> on the two endpoints of each block in a fixed ordered-pair partition.

### Abstract

Let $H$ be a finite group of even order $N$, let $X$ have size $N/2$,
and fix an equivalence
$P : X \times \operatorname{Fin}(2) \simeq H$.
For a uniform permutation $\pi$ of $H$, the real oracle is
$$
  R_P(x)=\pi(P(x,0))+\pi(P(x,1)),
$$
while the ideal oracle is a uniform random function $X\to H$. We derive the
exact adaptive fresh-tape law for every finite group, construct explicit
couplings, determine the exact one-query obstruction, and analyze the Boolean
case through an online hidden-matching coupling. On its closed range the
coupling proves
$$
  \operatorname{PairAdv}_q
  =1-\left(1-\frac1N\right)^q.
$$
Outside that range we retain an explicit statewise maximal-coupling bound and
the audited small-parameter and saturation results below.

## 1. Proof

This manuscript analyzes a construction different from the sum of two
independent permutations in `SoP2.md`.  There are not two independent permutations.  Instead, the input
points of one permutation are partitioned into ordered pairs, and the two
images in each pair are combined.  The prefix presentation
$$
\pi(0\mathbin\Vert x)\mathbin\oplus\pi(1\mathbin\Vert x)
$$
is one concrete ordered-pair partition.  The abstraction below shows that
the names and geometry of the blocks do not matter.

### 1.1 General partition and group law

**Definition 27 (ordered-pair partition construction).**
Let $\Omega$ and $G$ be finite sets of the same even cardinality $N$, and
give $G$ a group operation written multiplicatively.  Let $X$ have
cardinality $N/2$, and let
$$
\ell,r:X\longrightarrow\Omega
$$
be injections with disjoint images whose union is $\Omega$.  Thus
$$
P_x=(\ell(x),r(x)),\qquad x\in X,
$$
is an ordered partition of $\Omega$ into pairs.

Choose a uniform bijection $\pi:\Omega\to G$.  The real oracle is
$$
\mathsf{Pair}_\pi(x)=\pi(\ell(x))\,\pi(r(x)).
$$

The ideal oracle is a uniform random function $F:X\to G$.  Let
$\operatorname{PairAdv}_q(G)$ be their optimal information-theoretic
distinguishing advantage under at most $q$ adaptive calls, with repeated
inputs answered consistently, and put
$$
m=\min\{q,N/2\}.
$$

For an abelian group we may write the operation additively.  The construction
asked about in the discussion is the Boolean specialization
$$
G=\mathbb F_2^n,\qquad N=2^n,\qquad
\ell(x)=0\mathbin\Vert x,\qquad r(x)=1\mathbin\Vert x.
$$

The order inside each pair is needed for a noncommutative group.  Any two
ordered-pair partitions give the same random-system law: a bijection carrying
one partition to the other can be composed with the uniform $\pi$.

**Lemma 28 (uniform matching representative and adaptive reduction).**
On the successive fresh query ranks, let
$$
(A_1,B_1,\ldots,A_m,B_m)
$$
be a uniform ordered injection of length $2m$ into $G$, and put
$$
Y_i=A_iB_i. \tag{60}
$$

Let $Z_1,\ldots,Z_m$ be independent uniform elements of $G$.  Lazy systems
that assign $Y_i$, respectively $Z_i$, to the $i$-th fresh queried block and cache
the answer are honest representatives of the real and ideal bounded random
systems.

Consequently every coupling of $Y$ and $Z$ is an adaptive coupling of the
oracles.  Tape equality makes the complete interactions equal, including
adaptive query choices, randomized stopping, and repeats.

*Proof.*
The values of a uniform bijection on any ordered list of $2m$ distinct domain
points form a uniform ordered injection.  After some pairs have been exposed,
all unqueried blocks are exchangeable: a domain permutation that swaps two
unqueried blocks and fixes the exposed blocks preserves both the uniform law
of $\pi$ and the previous answers.  Hence an adaptively selected fresh block
may receive the next pair $(A_i,B_i)$.  A repeated block replays its cached
answer and consumes no pair.

The same fresh-rank argument for a uniform random function gives independent
uniform $Z_i$.  Couple the private adversary coins identically.  If the two
tapes agree, induction on calls makes all queries, answers, stopping
decisions, and final outputs agree.  Finally, querying any fixed $m$ distinct
blocks returns the whole tape, so no tape distance is lost in the adaptive
reduction.  QED.

**Definition 29 (compatible ordered-matching count).**
For $y=(y_1,\ldots,y_m)\in G^m$, define
$$
\begin{aligned}
M_G(y)=\#\{&(a_1,b_1,\ldots,a_m,b_m):\\
&\text{all }2m\text{ entries are distinct and }
  a_ib_i=y_i\text{ for every }i\}.
\end{aligned}
\tag{61}
$$

Write $(N)_k=N(N-1)\cdots(N-k+1)$.

**Theorem 30 (exact finite characterization and maximal coupling).**
For every finite group of even order and every query budget,
$$
\Pr[Y=y]=\frac{M_G(y)}{(N)_{2m}},
\qquad
\Pr[Z=y]=\frac1{N^m},                                 \tag{62}
$$
and
$$
\operatorname{PairAdv}_q(G)
=\frac12\sum_{y\in G^m}
\left|\frac{M_G(y)}{(N)_{2m}}-\frac1{N^m}\right|.
\tag{63}
$$

There is a coupling of honest representatives whose disagreement probability
is exactly the right-hand side of (63).

*Proof.*
The fibers in (61) partition all $(N)_{2m}$ ordered injections, proving (62)
and
$$
\sum_yM_G(y)=(N)_{2m}.
$$

For each tape $y$, place diagonal joint mass
$$
\min\left\{\frac{M_G(y)}{(N)_{2m}},\frac1{N^m}\right\}.
$$

The remaining masses of the two marginals have equal total mass and disjoint
supports according to which marginal is larger.  If their common residual
mass is $d>0$, define the residual joint mass at $(y,z)$ to be
$$
\frac{P_{\mathrm{res}}(y)Q_{\mathrm{res}}(z)}d.
$$

This has total mass $d$ and the two required residual subprobability
marginals.  If $d=0$, omit it.  The resulting probability coupling has
disagreement exactly half the $L^1$ distance in (63).

Conditioned on a sampled real tape $y$, choose its endpoint injection
uniformly from the $M_G(y)$ compatible injections and then complete $\pi$
uniformly on the unused domain points.  Every complete bijection has
probability
$$
\frac{M_G(y)}{(N)_{2m}}\,
\frac1{M_G(y)}\,
\frac1{(N-2m)!}
=\frac1{N!},
$$

so this is an honest uniform-permutation marginal, not merely a coupling of
output laws.  Lemma 28 transports it to the adaptive systems.  Conversely,
fixed fresh queries realize every tape event, so the statistical distance is
also a lower bound on adaptive advantage.  QED.

**Proposition 31 (exact one-query algebraic obstruction).**
For a finite group, put
$$
r_G(y)=\#\{a\in G:a^2=y\}.
$$

Then
$$
\Pr[Y_1=y]=\frac{N-r_G(y)}{N(N-1)},
\qquad
\operatorname{PairAdv}_1(G)
=\frac1{2N(N-1)}\sum_y|r_G(y)-1|.
\tag{64}
$$

If $G$ is abelian, let
$$
G[2]=\{a:2a=0\},\qquad t=|G[2]|,\qquad
2G=\{2a:a\in G\}.
$$

Then
$$
r_G(y)=
\begin{cases}
t,&y\in2G,\\
0,&y\notin2G,
\end{cases}
\qquad
\operatorname{PairAdv}_1(G)=\frac{t-1}{t(N-1)}.
\tag{65}
$$

In particular, for the Boolean group $t=N$ and
$\operatorname{PairAdv}_1=1/N$.  For an abelian group of even order,
$t\ge2$; thus the one-query law cannot be exactly uniform.  The formula
also explains why the answer depends on the group and
not only on $N$.

*Proof.*
For each $a$, the equation $ab=y$ has the unique solution $b=a^{-1}y$.
This pair is excluded precisely when $a=b$, equivalently $a^2=y$, giving
$N-r_G(y)$ allowed ordered pairs.  Subtracting $1/N$ from
the resulting probability gives (64).

In an abelian group the doubling map is a homomorphism with kernel $G[2]$.
Every element of its image has exactly $t$ preimages and every other element
has none.  Since $|2G|=N/t$, summing the two constant absolute deviations
gives (65).  QED.

### 1.2 Boolean matching colors and the exact transport

From now on in this section,
$$
G=\mathbb F_2^n,\qquad n\ge2,\qquad N=2^n,\qquad
0\le q\le N/2.
$$

For a larger external query budget, replace $q$ by
$m=\min\{q,N/2\}$.  For $n=1$, there is only one fresh block and
Proposition 31 gives the complete answer
$\operatorname{PairAdv}_q=1/2$ for every $q\ge1$.
Every nonzero $z$ colors the perfect matching
$$
\bigl\{\{a,a+z\}:a\in G\bigr\}.
$$

Thus the real fresh tape is the color sequence of labeled edges drawn from
one uniform perfect matching of $G$.

For $z=(z_1,\ldots,z_q)$ with every $z_i$ nonzero, write $M_N(z)$ for the count
in (61), and define
$$
\mathcal H_q=(G\setminus\{0\})^q,\qquad
P_q(z)=\frac{M_N(z)}{(N)_{2q}},\qquad
Q_q(z)=\frac1{N^q},\qquad
\delta_0=1-\left(1-\frac1N\right)^q.
\tag{66a}
$$

If some coordinate of $z$ is zero, then $M_N(z)=0$, because distinct
Boolean-group elements never have XOR zero.

**Lemma 32 (exact distance decomposition).**
For the standing range $0\le q\le N/2$,
$$
\operatorname{PairAdv}_q(\mathbb F_2^n)
=\delta_0+\sum_{z\in\mathcal H_q}
       \bigl(Q_q(z)-P_q(z)\bigr)_+.
\tag{66}
$$

Consequently the zero-output test is exactly optimal if and only if
$$
P_q(z)\ge Q_q(z)\qquad\text{for every }z\in\mathcal H_q.
$$

*Proof.*
The ideal mass outside $\mathcal H_q$ is exactly $\delta_0$, while the real
mass there is zero.  On $\mathcal H_q$,
$$
\sum_z\bigl(P_q(z)-Q_q(z)\bigr)=\delta_0.
$$

Splitting the absolute values in (63) into positive and negative parts gives
(66).  The second statement is immediate.  QED.

**Lemma 33 (hidden-state next-color law).**
After $i$ fresh real pairs have been exposed, let $S$ be their used endpoint
set, put
$$
s=|S|=2i,\qquad U=G\setminus S,\qquad h=|U|=N-s,
$$
and, for $z\ne0$,
$$
D_S(z)=|S\cap(S+z)|.
$$

Conditional on this complete hidden state, the real next color has law
$$
c_S(z)=N-2s+D_S(z),\qquad
p_S(0)=0,\qquad
p_S(z)=\frac{c_S(z)}{h(h-1)}\quad(z\ne0).
\tag{67}
$$

Given real color $z$, choosing its first endpoint uniformly among the
$c_S(z)$ valid choices and setting the second endpoint to $a+z$ makes the
next ordered endpoint pair uniform on all $h(h-1)$ unused ordered pairs.
Moreover,
$$
c_S(z)=N-|S\cup(S+z)|\ge N-2s=N-4i.
\tag{68}
$$

*Proof.*
The first endpoint $a$ is valid exactly when both $a$ and $a+z$ lie outside
$S$.  Inclusion-exclusion gives (67) and (68).  The probability of any
particular valid ordered pair with color $z$ is
$$
\frac{p_S(z)}{c_S(z)}=\frac1{h(h-1)},
$$

which proves the uniform real-pair marginal.  QED.

**Theorem 34 (exact online coupling in the closed range).**
If
$$
2(q-1)(2q-1)\le N, \tag{69}
$$
there is an explicit online coupling of honest representatives which
disagrees exactly when the ideal random function gives zero on a fresh
query.  Consequently
$$
\operatorname{PairAdv}_q(\mathbb F_2^n)
=1-\left(1-\frac1N\right)^q.
\tag{70}
$$

Equivalently, a convenient integer range is
$$
q\le\left\lfloor\frac{3+\sqrt{4N+1}}4\right\rfloor.
$$

*Proof.*
At fresh rank $i+1$, condition on the complete hidden real state $S$, where
$0\le i<q$.  Lemma 33 gives, for every nonzero $z$,
$$
p_S(z)\ge\frac{N-4i}{(N-2i)(N-2i-1)}.
$$

The right-hand side is at least $1/N$ precisely when
$$
N(N-4i)\ge(N-2i)(N-2i-1),
$$

and the difference between the two sides is
$$
N-2i-4i^2.
$$

Condition (69) makes it nonnegative for every $i<q$.

Now define the complete conditional joint kernel of the real color $C$ and
ideal answer $Z$ by
$$
\begin{aligned}
K_S(C=z,Z=z)&=\frac1N &&(z\ne0),\\
K_S(C=z,Z=0)&=p_S(z)-\frac1N &&(z\ne0),\\
K_S(C=c,Z=z)&=0 &&\text{otherwise}.
\end{aligned}
\tag{71}
$$

All masses are nonnegative.  Its $C$-marginal is $p_S$.  Every nonzero
$Z=z$ has mass $1/N$, while
$$
\sum_{z\ne0}\left(p_S(z)-\frac1N\right)=\frac1N,
$$
so its $Z$-marginal is uniform on $G$.  Given $C$, choose the real endpoint
pair as in Lemma 33 and remove it from $U$.  Hence the real representative
is a lazy uniform ordered injection and, after uniform completion, a uniform
permutation.  Since the $Z$-marginal is uniform for every complete joint
past and every hidden $S$, the successive fresh ideal answers are
independent uniform elements.  Cache both sides on repeats.

Kernel (71) disagrees if and only if $Z=0$.  The ideal fresh coordinates are
independent, so the probability of any disagreement through $q$ fresh
queries is exactly $1-(1-1/N)^q$.  Lemma 28 transports this to every
adaptive environment.  The fixed-query zero-output test has the same
advantage in the opposite direction, proving equality.  QED.

**Theorem 35 (full-law statewise maximal coupling at every query depth).**
For $0\le i<N/2$, put
$$
T_i=\bigl[2i(2i+1)-N\bigr]_+,\qquad
b_i=\min\left\{1,\frac1N+\frac{T_i}{N(N-2i-1)}\right\},
$$
where $[x]_+=\max\{x,0\}$.  For every $0\le q\le N/2$, there is an
honest online coupling satisfying the residual-free bound
$$
\operatorname{PairAdv}_q(\mathbb F_2^n)
\le1-\prod_{i=0}^{q-1}(1-b_i).
\tag{72}
$$

The coupling at each hidden state is a maximal coupling of the real next
color with the full uniform law on $G$, not merely with the uniform
nonzero law.  When all $T_i$ with $i<q$ vanish, (72) is exactly (70).

*Proof.*
At hidden state $S$, extend $p_S$ by $p_S(0)=0$ and put $u(z)=1/N$ for
every $z\in G$.  For every $z$, place diagonal mass
$$
a_z=\min\{p_S(z),u(z)\}.
$$

Let $r_z=p_S(z)-a_z$, $t_z=u(z)-a_z$, and
$d=\sum_zr_z=\sum_zt_z$.  If $d>0$, put residual joint mass
$$
\frac{r_ct_z}{d}
$$
at $(C=c,Z=z)$; if $d=0$, omit the residual part.  The row sums are $p_S$,
the column sums are $u$, and $r_zt_z=0$ for every $z$.  Hence all residual
mass disagrees and this is the explicit maximal coupling of the two complete
next-color laws.  Given $C$, choose its ordered endpoint pair by Lemma 33.
The real pair is uniform on the unused ordered pairs, while the conditional
law of $Z$ is uniform for every complete joint past.  Iteration therefore
gives an honest uniform-permutation marginal and independent uniform ideal
answers.

Writing statistical distance as the total ideal deficit
$\sum_z(u(z)-p_S(z))_+$, the zero coordinate contributes $1/N$.  For
$z\ne0$, direct subtraction in (67) gives
$$
\left(\frac1N-p_S(z)\right)_+
=\frac{\bigl[s(s+1)-N(D_S(z)+1)\bigr]_+}{Nh(h-1)}.
$$

Consequently the exact conditional disagreement probability is
$$
\tau(S)=\frac1N+
\frac1{Nh(h-1)}
\sum_{z\ne0}\bigl[s(s+1)-N(D_S(z)+1)\bigr]_+.
\tag{72a}
$$

Write $T=[s(s+1)-N]_+$.  If $T=0$, the sum in (72a) vanishes.  If $T>0$,
then for every $d$ with $0\le d\le s$,
$$
[T-Nd]_+\le T\left(1-\frac ds\right).
$$

Indeed this is immediate above the zero of the left side, and below that
zero it reduces to $T\le Ns$, which holds because $s\le N-2$.  Using
$$
\sum_{z\ne0}D_S(z)=s(s-1)
$$
and $h=N-s$, summation gives
$$
\tau(S)\le
\min\left\{1,\frac1N+\frac{T}{N(N-s-1)}\right\}.
\tag{72b}
$$

At fresh rank $i+1$, $s=2i$, so the right-hand side is $b_i$.  Conditional
on agreement at all previous ranks, the next agreement probability is at
least $1-b_i$, regardless of the resulting hidden state.  The chain rule
therefore gives agreement probability at least
$$
\prod_{i=0}^{q-1}(1-b_i).
$$

This proves (72).  Repeats are cached and consume no state.  Finally,
$T_i=0$ for every $i<q$ precisely under (69); then every $b_i=1/N$, so
(72) equals the zero-output lower bound and recovers (70).  QED.

**Corollary 36 (closed sparse-query coupling bound).**
Put
$$
k_N=\left\lfloor\frac{\sqrt{4N+1}-1}{4}\right\rfloor+1,
\qquad
A(t)=\frac{t(t-1)(4t+1)}3,
$$
and
$$
C(N,q)=
\begin{cases}
0,&q\le k_N,\\
A(q)-A(k_N)-(q-k_N)N,&q>k_N.
\end{cases}
$$

If $q\le N/4$, then
$$
\operatorname{PairAdv}_q(\mathbb F_2^n)
\le1-\left(1-\frac1N\right)^q
  +\frac{C(N,q)}{N(N-2q+1)}.
\tag{73}
$$

The correction term is identically zero throughout the exact range (69).
If $\sqrt N=o(q)$ and $q=o(N)$, it is at most
$$
\left(\frac43+o(1)\right)\frac{q^3}{N^2}.
$$

Thus (73) is useful as a coupling-only bound beyond the exact range, but no
claim is made that its large-query cubic correction improves the known
chi-squared bounds.

*Proof.*
For $i<q$, set
$$
r_i=\frac{T_i}{N(N-2i-1)}.
$$

In the range $q\le N/4$, $1/N+r_i<1$.  Factoring
$1-1/N$ from every factor in (72), and using
$1-\prod_i(1-x_i)\le\sum_i x_i$, gives
$$
\operatorname{PairAdv}_q
\le1-\left(1-\frac1N\right)^q+\sum_{i=0}^{q-1}r_i.
$$

Indeed, with $s=2i\le N/2-2$,
$$
r_i\le\frac{s(s+1)}{N(N-s-1)}
\le\frac sN<1-\frac1N.
$$

After factorization, the multiplier of $\sum_i r_i$ is
$\left(1-1/N\right)^{q-1}\le1$ (and $q=0$ is trivial).

The positive part $T_i$ vanishes exactly for $i<k_N$.  Moreover,
$$
\sum_{i=0}^{t-1}2i(2i+1)=A(t).
$$

Therefore $\sum_{i<q}T_i=C(N,q)$.  Replacing every denominator
$N-2i-1$ by the common lower bound $N-2q+1$ proves (73).

Finally, $k_N=O(\sqrt N)$.  Under $\sqrt N=o(q)$ and $q=o(N)$,
the terms $A(k_N)$ and $(q-k_N)N$ are $o(q^3)$, while
$A(q)=(4/3+o(1))q^3$ and $N(N-2q+1)=(1+o(1))N^2$.
This proves the last estimate.  QED.

### 1.3 Exact small parameters and the large-query obstruction

**Proposition 37 (exact two- and three-query laws).**
For Boolean groups:

1. If $N\ge8$, then
   $$
   \operatorname{PairAdv}_2=1-\left(1-\frac1N\right)^2.
   $$

2. If $N\ge16$, then
   $$
   \operatorname{PairAdv}_3=1-\left(1-\frac1N\right)^3.
   $$

3. At the first exceptional sizes,
   $$
   \begin{array}{c|c}
   (N,q)&\operatorname{PairAdv}_q\\ \hline
   (4,2)&13/16\\
   (8,3)&211/512
   \end{array}
   $$

   These are strictly larger than the corresponding zero-event
   probabilities $7/16$ and $169/512$.

*Proof.*
For two prescribed nonzero colors, the exact compatible counts are
$$
M_N(z_1,z_2)=
\begin{cases}
N(N-2),&z_1=z_2,\\
N(N-4),&z_1\ne z_2.
\end{cases}
\tag{74}
$$

The smaller count dominates $(N)_4/N^2$ for powers of two $N\ge8$, because
after cancelling $N$ the difference is
$$
N^2(N-4)-(N-1)(N-2)(N-3)
=2N^2-11N+6>0.
$$

For $N=8+x$ the last polynomial is $2x^2+21x+46$, so the sign assertion
holds for every $N\ge8$.
Lemma 32 then proves the first assertion.

For three colors, iterating the lower bound (68) gives the universal count
$$
M_N(z_1,z_2,z_3)\ge N(N-4)(N-8).
$$

Equality is attained at $(u,v,u+v)$ with $u,v$ distinct: after two disjoint
edges, the four used vertices contain no edge of color $u+v$.  The lower
count dominates $(N)_6/N^3$ for $N\ge16$, since after cancelling
$N(N-4)$ the required difference is
$$
N^3(N-8)-(N-1)(N-2)(N-3)(N-5)
=3N^3-41N^2+61N-30>0.
$$

For $N=16+x$ this is
$3x^3+103x^2+1053x+2738$, proving positivity for every $N\ge16$.
This proves the second assertion.

For $N=4$, a complete two-edge matching has the same nonzero color on both
edges, uniformly among the three possibilities.  Its three tape atoms have
real mass $1/3$ and ideal mass $1/16$, so the total variation is
$3(1/3-1/16)=13/16$.

For $N=8,q=3$, exactly the $7\cdot6=42$ ordered triples
$$
(u,v,u+v),\qquad u,v\ne0,\quad u\ne v,
$$

are impossible: the unused pair would have XOR zero.  Every other nonzero
triple is feasible.  If all colors agree, its compatible count is
$8\cdot6\cdot4=192$.  Otherwise the group of eight common translations and eight
independent edge-orientation flips acts freely on any realization, so every
positive compatible count is at least $64$.  Indeed, if translation by $t$
together with flip bit $e_i$ fixes ordered edge $i$, then
$$
e_i=0\Longrightarrow t=0,\qquad
e_i=1\Longrightarrow t=z_i.
$$

A nonidentity stabilizer can therefore occur only when every edge is flipped
and all three colors are equal, the case already separated.  Since
$$
\frac{64}{(8)_6}=\frac1{315}>\frac1{512},
$$

the only nonzero ideal deficits are the 42 impossible tapes.  Formula (66)
therefore gives
$$
\frac{169}{512}+\frac{42}{512}=\frac{211}{512}.
$$

For completeness, feasibility of the remaining triples is explicit.  Up to
reordering, two equal colors have the form $(u,u,v)$; choose a vector $w$
outside the span of $u,v$ and use
$$
\{0,u\},\qquad\{v,u+v\},\qquad\{w,w+v\}.
$$

Three distinct colors with nonzero total are linearly independent; for
colors $(u,v,w)$ use
$$
\{0,u\},\qquad\{w,w+v\},\qquad\{u+v,u+v+w\}.
$$

QED.

**Proposition 38 (saturation and prescribed-difference obstruction).**
Assume $n\ge3$.

1. At $q=N/2-1$, every nonzero color tape satisfying
   $$
   z_1\mathbin\oplus\cdots\mathbin\oplus z_q=0
   $$

   is impossible.  Such tapes exist, so zero-event optimality cannot extend
   to all query depths.

2. At the full fresh domain $q=N/2$,
   $$
   \bigoplus_{i=1}^{N/2}Y_i
   =\bigoplus_{g\in G}g
   =0 \tag{75}
   $$

   deterministically.  The corresponding ideal XOR is uniform, hence
   $$
   \operatorname{PairAdv}_{N/2}\ge1-\frac1N.
   $$

3. For budgets above $N/2$, the advantage is unchanged: every further call
   repeats an already available block.

*Proof.*
After $N/2-1$ matching edges have been used, two distinct vertices remain.
The XOR of their values equals the XOR of all group elements and all exposed
edge colors.  For $n\ge2$, the XOR of all elements of $\mathbb F_2^n$ is zero.
Therefore a zero total exposed color would force the two remaining values to
have XOR zero and hence to be equal, a contradiction.
Such a tape exists for every stated $N$: take three colors
$u,v,u+v$ and fill the remaining even number of positions with repeated
pairs $w,w$.

At saturation, every group element appears exactly once among the endpoints,
which proves (75).  An ideal tape has uniform total XOR, giving the stated
test.  The last assertion follows from the finite input domain and consistent
repeats.  QED.

There is a genuine combinatorial boundary here.  Deciding whether every
zero-sum list of $N/2$ nonzero Boolean differences is realized by a perfect
matching is the Balister--Gyori--Schelp prescribed-differences conjecture.
It remains open in general; current work proves substantial special cases.
Moreover, universal feasibility at $q=N/2-1$ for every tape with nonzero
total XOR would imply that conjecture by appending the forced leftover edge.
Therefore the small cases must not be extrapolated into an unproved
near-saturation theorem.

### 1.4 Exact comparison with prior one-permutation bounds

The complete source audit changes the earlier preliminary comparison.  The
known one-permutation results are:

* Dai--Hoang--Tessaro, for $n\ge8$ and $q\le N/32$:
  $$
  \operatorname{Adv}_q
  \le\frac qN+3\left(\frac qN\right)^{3/2}.
  $$

* Bhattacharya--Nandi, for $q<N/2$:
  $$
  \operatorname{Adv}_q
  \le\frac qN+
  \sqrt{\frac{2(N-1)q^3}{(N-2q)^4}}.
  $$

* Dutta--Nandi--Saha's Mirror Theorem, for $n\ge12$ and $q\le N/58$:
  $$
  \operatorname{Adv}_q
  =1-\left(1-\frac1N\right)^q.
  \tag{76}
  $$

The last equality combines their Theorem 2 count with Corollary 1 and the
zero-output distinguisher.  Thus the exact zero-test result on a linear range
was already known.  It is stronger in query range than the exact online
coupling range here whenever its assumptions apply; for example, at $N=4096$
condition (69) reaches $q=32$, while $\lfloor N/58\rfloor=70$.

Accordingly, no numerical novelty over the Mirror theorem is claimed.  The
proved contributions of this section are instead:

* an exact arbitrary-group, arbitrary-pair-partition characterization;
* an explicit coupling of honest permutation and random-function
  representatives whose failure is the analyzed event;
* a short self-contained coupling-only proof of exact zero-test optimality
  on the closed range (69), without importing an H-technique endpoint;
* a statewise maximal-coupling bound for every query depth;
* exact exceptional small parameters and honest large-query obstructions.

For $q\ge1$, on the intersection of (69) with each source theorem's stated
hypotheses, (70) is strictly smaller than the corresponding displayed
chi-squared upper bound:
$1-(1-1/N)^q\le q/N$, while both bounds add a
positive residual.  This is an exact-value comparison, not merely an
asymptotic one.  Importing the Mirror pointwise count and placing its mass on
the diagonal would merely repackage the forbidden good-transcript density
argument.  It is therefore recorded only as the external benchmark (76),
not used in Theorems 34--35.

In summary, for one paired permutation,
$$
\operatorname{PairAdv}_q
=1-\left(1-\frac1N\right)^q
=\frac qN+O\left(\frac{q^2}{N^2}\right)
$$
under $2(q-1)(2q-1)\le N$.  Hence the leading scale is $q/N$, not
$q^2/N^2$.  The Mirror theorem already proves the same exact value on its
larger linear range $q\le N/58$ for $n\ge12$.  Beyond the online exact
range, (72) is the direct full-law statewise-maximal coupling bound.

## 2. Freeze and audit record

This ordered-pair proof has its own normalization, marginal, adaptive,
finite-count, small-parameter, and boundary audits. Independent checks
recomputed the hidden-state kernels, the full-law conditional distance, the
product and closed bounds, and every even hidden state for $N=4,8,16$.
No theorem in this manuscript uses the two-independent-permutation coupling
from `SoP2.md`.

## 3. Frozen result-to-formalization correspondence

The mathematical numbering is retained from the original combined draft so
that existing citations remain stable.

| Paper result | Lean declaration or intended declaration |
|---|---|
| Definition 27 | `ordered_pair_partition`, `ordered_pair_real`, `ordered_pair_ideal` |
| Lemma 28 | `ordered_pair_real_fresh_tape_eq_uniform_matching`, `ordered_pair_advantage_eq_fresh_tape_distance` |
| Definition 29 | `ordered_matching_compatible_count` |
| Theorem 30 | `ordered_pair_advantage_eq_count_distance_of_le_card`, `ordered_pair_maximal_coupling` |
| Proposition 31 | `ordered_pair_one_query_law`, `ordered_pair_abelian_one_query_advantage` |
| Lemma 32 | `ordered_pair_advantage_deficit_decomposition` |
| Lemma 33 | `ordered_pair_hidden_state_next_color_law`, `ordered_pair_next_pair_uniform` |
| Theorem 34 | `ordered_pair_exact_online_coupling`, `ordered_pair_advantage_eq_zero_event_closed_range` |
| Theorem 35 | `ordered_pair_full_statewise_maximal_coupling_bound` |
| Corollary 36 | `ordered_pair_closed_sparse_coupling_bound` |
| Proposition 37 | `ordered_pair_advantage_two`, `ordered_pair_advantage_three`, `ordered_pair_small_exceptions` |
| Proposition 38 | `ordered_pair_penultimate_support_obstruction`, `ordered_pair_saturation_lower_bound` |

## References

1. David Lanzenberger, *A Theory of Random Systems, Games, and Hardness
   Amplification*, doctoral dissertation, ETH Zurich, Diss. ETH No. 29554,
   2023.
2. David Lanzenberger and Ueli Maurer, “Coupling of Random Systems,” full
   version of the TCC 2020 paper, 2021.
3. Wei Dai, Viet Tung Hoang, and Stefano Tessaro, “Information-theoretic
   Indistinguishability via the Chi-squared Method,” CRYPTO 2017; revised full
   version, IACR ePrint 2017/537.
4. Avijit Dutta, Mridul Nandi, and Abishanka Saha, “Proof of Mirror Theory for
   xi_max = 2,” IACR ePrint 2020/669, revised 2022 version.
5. Srimanta Bhattacharya and Mridul Nandi, “Revisiting Variable Output Length
   XOR Pseudorandom Function,” IACR ePrint 2019/249.
6. Benedek Kovacs, “Finding a Perfect Matching of F_2^n with Prescribed
   Differences,” arXiv:2310.17433; subsequently published in *Ars Mathematica
   Contemporanea*.
