# A Conditional-Equivalence Proof for SequenceHash over Merkle--Damgård

## Abstract

This chapter proves indifferentiability of the stable C2SP SequenceHash
v1.0.0 construction when the underlying hash is strengthened
Merkle--Damgård over an ideal compression function. The theorem is stated for
one fixed public customization string of at most one compression block. In
this case the two derived-key blocks and the customization block are public
constants; no recursive customization hash is present.

The proof uses a single typed compression graph and an exact
conditional-equivalence argument. Both the real and ideal systems are first
represented by the same executable machine. In the real representative its
construction tape is the two-pass Merkle--Damgård evaluation of its
compression tape. In the ideal representative the construction and
compression tapes are independent. Two honest monotone games retain exactly
the same unnormalized mass before their bad event. This is the symmetric
game-equivalence form of the conditional-equivalence method.

The only nontrivial local replacement concerns an outer terminal that was
queried before its hidden inner endpoint was linked. For a fixed profile of
\(c\) occupied terminal sites, the real and ideal laws have exact common mass

\[
1-\frac{c(N-1)}{N^2}.
\]

The proof realizes this common mass by a positive condition, not by a signed
measure and not by a probabilistic coupling.

Let \(a\) be a worst-case bound on the number of distinct construction
queries, let \(q\) bound the number of distinct direct compression queries,
and let \(\sigma\) be the corresponding total compression cost. Then

\[
\operatorname{Adv}_{\mathrm{indiff}}
\le
\min\!\left\{
1,\,
\frac{\binom{\sigma-a+1}{2}+q(\sigma-a)}{N}
+
\frac{qa(N-1)}{N^2}
\right\}.
\tag{A.1}
\]

In particular,

\[
\operatorname{Adv}_{\mathrm{indiff}}
\le
\min\!\left\{1,\frac{2\sigma^2}{N}\right\}.
\tag{A.2}
\]

Every transition used by the proof is listed explicitly. The proof also
accounts for adaptive query order, hidden construction paths, repeated
compression points, the two possible temporal orders of an out-of-order
query, and the zero-mass boundary. A direct attack against the stated
simulator has advantage

\[
\binom r2\frac{N-1}{N^2}
-
\binom{\binom r2}{2}
\left(\frac{N-1}{N^2}\right)^2
\]

or larger on a suitable \(r\)-input workload. Hence the birthday order of
the theorem is attained when \(r=o(\sqrt N)\).

## 1. Setting

Random systems, representatives, games, distinguishing advantage, and
conditioning have the meanings fixed in
[FOUNDATIONS.md](../../FOUNDATIONS.md).

Let \(\mathcal C\) be the finite nonempty chaining-value set and
\(\mathcal B\) the finite compression-block set. Put

\[
N=|\mathcal C|,
\]

and fix \(\mathsf{IV}\in\mathcal C\). The real compression function is

\[
f\leftarrow U_{\mathcal C^{\mathcal C\times\mathcal B}}.
\]

For a nonempty block word

\[
W=(W_1,\ldots,W_m)\in\mathcal B^+,
\]

define

\[
\operatorname{MD}_f(W)
=f(\cdots f(f(\mathsf{IV},W_1),W_2)\cdots,W_m).
\tag{1.1}
\]

The byte-to-block map includes the strengthening of the underlying hash.
We assume its serialization is injective on the accepted input-length
domain, as it is for the standard strengthened Merkle--Damgård codecs.
Thus every word below is the complete padded block word supplied to
\(\operatorname{MD}\).

### 1.1. Stable SequenceHash framing

Fix a public customization string \(S\) such that

\[
|S|\le b,
\tag{1.2}
\]

where \(b\) is the compression-block length in bytes. SequenceHash uses the
empty key. Its two derived-key blocks are therefore

\[
K_I=55\,00\cdots00,
\qquad
K_O=\mathrm{aa}\,00\cdots00,
\tag{1.3}
\]

and

\[
K_I\ne K_O.
\tag{1.4}
\]

The padded customization \(S'\) is one public block.

For an accepted input sequence

\[
x=(M_1,\ldots,M_n),
\]

let \(I(x)\in\mathcal B^+\) be the complete padded block word for

\[
K_I
\mathbin\|
\operatorname{HeaderI}(b,F_{\rm SEQHSH},\varepsilon)
\mathbin\|
\operatorname{Encode}(M_1)
\mathbin\|\cdots\mathbin\|
\operatorname{Encode}(M_n).
\tag{1.5}
\]

Let

\[
t(x)=(S,n,L)
\]

denote the public outer tag. For \(z\in\mathcal C\), let
\(O(t,z)\in\mathcal B^+\) be the complete padded block word for

\[
K_O
\mathbin\|
\operatorname{HeaderO}
  (b,F_{\rm SEQHSH},S,\varepsilon)
\mathbin\|S'
\mathbin\|\operatorname{EncodeMSBF}(n)
\mathbin\|\operatorname{EncodeMSBF}(L)
\mathbin\|z.
\tag{1.6}
\]

The output length \(L\) is fixed. The construction is

\[
z_x=\operatorname{MD}_f(I(x)),
\qquad
\operatorname{Seq}_f(x)
=\operatorname{MD}_f(O(t(x),z_x)).
\tag{1.7}
\]

### Lemma 1.1 (typed block grammar)

The stable v1.0.0 encoding satisfies the following properties.

1. The map \(x\mapsto I(x)\) is injective.
2. A complete outer word determines \(t\) and \(z\) uniquely.
3. Every inner word begins with \(K_I\), and every outer word begins with
   \(K_O\).
4. No complete inner word is a complete outer word.
5. For fixed \(S\) and \(L\), all outer words have one common block length.
   Consequently, no complete outer word is a proper prefix of another.
6. Every nonempty block word has one of the following mutually exclusive
   parser classifications:

   \[
   \mathsf{InnerPrefix},\quad
   \mathsf{InnerComplete}(x),\quad
   \mathsf{OuterPrefix},\quad
   \mathsf{OuterComplete}(t,z),\quad
   \mathsf{Invalid}.
   \tag{1.8}
   \]

   A complete inner word may still be a prefix of a longer complete inner
   word. A complete outer word is terminal.

#### Proof

Each encoded item ends in its fixed-width 128-bit length. Starting at the
right, that length determines exactly how many preceding bytes form the
item. Repeating this operation recovers every item and reaches the
role-specific header. Hence the inner encoding has a unique right-to-left
parse and is injective.

In an outer word, \(n\) and \(L\) have fixed-width encodings and \(z\) has
the fixed digest width. The fixed header and the fixed-length
customization field determine all remaining boundaries. Thus a complete
outer word recovers \(t\) and \(z\) uniquely.

The first complete block is \(K_I\) in the inner role and \(K_O\) in the
outer role. Equation (1.4) separates the roles before any variable field is
read. Native strengthening records the unpadded byte length, so padded
serialization is injective. Once \(S\) and \(L\) are fixed, changing \(n\)
changes only the contents of a fixed-width field. Therefore every outer
word has the same length. These observations also give the parser in
(1.8), including its soundness on prefixes and the terminal property of a
complete outer word. \(\square\)

The remainder of the proof uses exactly the six properties in Lemma 1.1.
It does not use any other feature of the byte encoding.

## 2. Systems, workload, and condition games

Let

\[
r\leftarrow U_{\mathcal C^{\mathcal X}}
\]

be an ideal random oracle on accepted sequences. The two systems are

\[
\mathbf A=(\operatorname{Seq}_f,f),
\qquad
\mathbf B=(r,\Sigma^r),
\tag{2.1}
\]

where \(\Sigma\) is the simulator defined in Section 3. The distinguisher
may interleave the two interfaces.

Repeated queries are answered consistently and create no new table
coordinate. The workload parameters are worst-case bounds over every run:

- \(a\) is the number of distinct construction queries;
- \(q\) is the number of distinct direct compression queries;
- \(\sigma\) is \(q\) plus the sum of the complete inner and outer
  compression costs of the \(a\) construction queries.

If the \(j\)-th distinct construction input has inner and outer costs
\(m_{I,j}\) and \(m_{O,j}\), then

\[
\sigma=q+\sum_{j=1}^{a}(m_{I,j}+m_{O,j}).
\tag{2.2}
\]

The final outer call for a construction query is a terminal answer, not a
live prefix state. The total number of critical state samples is therefore
at most

\[
s
\le
q+\sum_{j=1}^{a}(m_{I,j}+m_{O,j}-1)
=\sigma-a.
\tag{2.3}
\]

Shared prefixes, repeated table points, and terminal direct queries can only
decrease the actual number.

### 2.1. Symmetric conditional equivalence

Let \(\widehat S\) be a system with a hidden monotone bit \(A_i\). For a
fixed nonempty query and answer history, define its unnormalized
pre-winning mass by

\[
g_{\widehat S}(y^i;x^i)
=
\Pr_{\widehat S}
[Y^i=y^i,\ A_i=0\mid X^i=x^i].
\tag{2.4}
\]

Two games are conditionally equivalent as games, written

\[
\widehat S\equiv_g\widehat T,
\]

if their quantities in (2.4) are equal for every \(i,x^i,y^i\). This is the
cumulative form of game equivalence in Maurer's 2018 lecture notes
(CR18), Definition 4.16. One-sided conditional equivalence, CR18
Definition 4.19, constructs such a game-equivalent pair by enhancing one
target system. Here it is more direct to construct the two games
symmetrically.

### Lemma 2.1 (symmetric condition lemma)

Suppose that

\[
\widehat A^{-}=\mathbf A,
\qquad
\widehat B^{-}=\mathbf B,
\qquad
\widehat A\equiv_g\widehat B,
\tag{2.5}
\]

where the superscript minus means that the hidden bit is erased. Then, for
every adaptive distinguisher \(D\),

\[
\operatorname{Adv}_D(\mathbf A,\mathbf B)
\le
\Pr[D\text{ wins }\widehat A]
=
\Pr[D\text{ wins }\widehat B].
\tag{2.6}
\]

#### Proof

Fix the randomness of \(D\). For a complete transcript \(\tau\), the
probability that \(D\) issues the queries in \(\tau\) is a product of
deterministic query-selection indicators. Multiplying (2.4) by these
indicators shows

\[
\Pr[D^{\widehat A}\text{ produces }\tau,\ A=0]
=
\Pr[D^{\widehat B}\text{ produces }\tau,\ A=0].
\tag{2.7}
\]

Summing (2.7) over all transcripts gives equal non-winning probabilities
and therefore equal winning probabilities; call the common value
\(\beta_D\).

For any acceptance event \(E\), the two contributions from
\(E\cap\{A=0\}\) cancel by (2.7). Each remaining contribution lies between
zero and \(\beta_D\). Hence

\[
\left|
\Pr[D^{\mathbf A}\in E]-\Pr[D^{\mathbf B}\in E]
\right|
\le\beta_D.
\]

Averaging over the randomness of \(D\) proves (2.6). \(\square\)

Lemma 2.1 is a conditioning theorem. It does not construct a joint
distribution of a real and an ideal run.

### Lemma 2.2 (finite-kernel realization)

Fix a finite query bound. Any family of causal probability kernels indexed
by the finite public histories and finite internal audit states reachable up
to that bound is the behavior of an honest PDS. If each kernel is
partitioned into a nonnegative retained subkernel and a nonnegative residual
subkernel, the residual label defines an honest monotone game.

#### Proof

For every reachable history-and-state node, independently pre-sample the
random choice used by its transition kernel. The resulting complete table
of choices is a deterministic discrete system with hidden state. The product
law of all tables is a PDS, and induction down the query tree gives the
prescribed causal kernels. Add one bit to each pre-sampled choice indicating
retained or residual. The running disjunction of these bits is monotone, and
erasing it restores the original transition kernel at every node.
\(\square\)

The stable specification bounds sequence counts and byte lengths, so the
formal query alphabet is finite. Equivalently, Lemma 2.2 may be applied
after restricting to the finite query tree reachable under the stated
workload.

## 3. One executable simulator and two representatives

The simulator stores a partial compression table

\[
T:\mathcal C\times\mathcal B\rightharpoonup\mathcal C.
\]

An entry \(T(v,B)=w\) is an edge

\[
v\xrightarrow{B}w.
\]

It also stores the following indices.

- \(\mathsf{word}[v]\) is a certified word labeling a known path from
  \(\mathsf{IV}\) to \(v\).
- \(\mathsf{inner}[z]=x\) means that the certified word at \(z\) is \(I(x)\).
- \(\mathsf{pending}[t,z]=w\) means that the complete outer word
  \(O(t,z)\) was queried before a matching inner endpoint was known, and
  its terminal answer was \(w\).
- \(\mathsf{seen}\) is the set of construction inputs already queried.

Terminal outer answers remain in \(T\), but they are not inserted into the
live-word index. Lemma 1.1 shows that no valid construction word extends a
complete outer word.

It is useful to define one deterministic machine

\[
\mathcal M(F,G),
\]

where \(F:\mathcal X\to\mathcal C\) is a complete construction tape and
\(G:\mathcal C\times\mathcal B\to\mathcal C\) is a complete ordinary
compression tape.

On a construction query \(x\), the machine returns \(F(x)\) and records
\(x\) in \(\mathsf{seen}\).

On a direct compression query \((v,B)\), it acts as follows.

1. If \(T(v,B)\) is defined, return it.
2. If \(\mathsf{word}[v]\) is undefined, return \(G(v,B)\), install the
   result, and record \(v\) as a loose root.
3. Otherwise parse \(\mathsf{word}[v]\mathbin\|B\) by (1.8).
4. At a correctly tagged outer completion \(O(t(x),z)\) with
   \(\mathsf{inner}[z]=x\), return \(F(x)\).
5. At every other fresh point, return \(G(v,B)\).
6. Propagate the live-word index only for inner and nonterminal outer
   prefixes. Record an unlinked outer completion in
   \(\mathsf{pending}\).

If a destination already has an incompatible live word, the machine records
a local join flag and stops propagating through that destination. It remains
total and continues to answer from \(F\), \(G\), and \(T\).

The ideal simulator is

\[
\Sigma^r=\mathcal M(r,g)_{\rm prim},
\tag{3.1}
\]

where \(r\) and \(g\) are independent uniform functions. Calls to \(r\)
caused by construction-interface queries are not simulator calls. The
simulator itself consults \(r\) only on a fresh correctly tagged linked
outer terminal.

### Lemma 3.1 (common-machine representatives)

The following are exact representative identities:

\[
\mathbf A
\equiv
\mathcal M(\operatorname{Seq}_f,f),
\tag{3.2}
\]

and

\[
\mathbf B
\equiv
\mathcal M(r,g),
\qquad
r\perp g.
\tag{3.3}
\]

#### Proof

Equation (3.3) is the definition of the ideal system and simulator.

For (3.2), maintain two deterministic invariants. First, every installed
table entry agrees with \(f\). Second, if
\(\mathsf{word}[v]=W\), following \(W\) from \(\mathsf{IV}\) through the
installed table gives \(v\).

Both invariants hold initially. Installing an ordinary, loose-root,
nonterminal, unlinked-terminal, or invalid edge stores exactly
\(f(v,B)\), so it preserves table agreement. Extending a certified path by
that edge certifies the new word. A repeated point changes no state.

It remains to check the linked-terminal branch. Its hypotheses give

\[
\mathsf{word}[v]\mathbin\|B=O(t(x),z)
\quad\text{and}\quad
z=\operatorname{MD}_f(I(x)).
\]

The queried point is therefore the final compression point in the outer
evaluation of \(x\), whence

\[
f(v,B)=\operatorname{Seq}_f(x).
\]

Thus the value returned from the correlated construction tape is again the
real compression answer. The parser has exactly the nine primitive leaves
listed in Section 6.3, so this argument covers every primitive transition.
Construction queries return \(\operatorname{Seq}_f(x)\) by definition.
Induction over the public query history proves (3.2). \(\square\)

Lemma 3.1 is also the reason no construction-query notification is given to
\(\Sigma\). Hidden construction paths occur only in the proof of the
correlated representative. They are not inserted into the ideal simulator's
public table.

## 4. The exact occupied-link condition

This section first records the exact finite calculation for a fixed occupied
profile. The adaptive proof uses its one-site form in Section 4.1; it does
not condition on a realized profile that may itself have been selected from
earlier answers.

Fix a construction input \(x\). Treat a set of complete outer sites

\[
C\subseteq\mathcal C
\]

with tag \(t(x)\), and their stored answers \(w_z\), as fixed parameters.
Write \(c=|C|\). Let

\[
Z=\operatorname{MD}_f(I(x)),
\qquad
Y=\operatorname{Seq}_f(x).
\]

Expose no coordinate of \(Z\) or \(Y\) when fixing these parameters. Before
a graph join, deferred sampling gives the following joint real law:

\[
P(z,y)=
\begin{cases}
1/N,   & z\in C\text{ and }y=w_z,\\
1/N^2, & z\notin C,\\
0,     & \text{otherwise}.
\end{cases}
\tag{4.1}
\]

In the independent ideal representative,

\[
Q(z,y)=\frac1{N^2}.
\tag{4.2}
\]

Equation (4.1) is a joint coordinate identity, not a claim that \(Z\) stays
uniform after conditioning on every chronologically visible answer. The
descriptor construction below is what makes the identity safe under either
temporal order.

### Lemma 4.1 (occupied-link law)

The laws in (4.1) and (4.2) are probability distributions and

\[
\delta(P,Q)=\frac{c(N-1)}{N^2}.
\tag{4.3}
\]

#### Proof

Every row has mass \(1/N\), so both laws have weight one and uniform
\(Z\)-marginal. If \(z\notin C\), the two rows agree. If \(z\in C\), the
real row places mass \(1/N\) at \(w_z\), while the ideal row places mass
\(1/N^2\) in every column. Its positive excess is

\[
\frac1N-\frac1{N^2}=\frac{N-1}{N^2}.
\]

Summing over the \(c\) occupied rows proves (4.3). \(\square\)

### Lemma 4.2 (positive common condition)

There are honest monotone conditions on the real and ideal laws whose
retained point masses agree exactly and whose discarded masses are both
\(c(N-1)/N^2\).

#### Proof

Fix \(u_0\in\mathcal C\). Enlarge only the real representative by an
independent \(U\leftarrow U_{\mathcal C}\); this does not change its
ordinary behavior.

On the real side retain the sample if

\[
Z\notin C
\quad\text{or}\quad
U=u_0.
\tag{4.4}
\]

On the ideal side retain it if

\[
Z\notin C
\quad\text{or}\quad
Y=w_Z.
\tag{4.5}
\]

For \(z\notin C\), both retained masses are \(1/N^2\) at every
\((z,y)\). For \(z\in C\), both retained masses are \(1/N^2\) at
\((z,w_z)\) and zero elsewhere: the real mass \(1/N\) is retained with
probability \(1/N\), while the ideal atom already has mass \(1/N^2\).
Thus the retained subdistribution is pointwise

\[
K(z,y)=\min\{P(z,y),Q(z,y)\}.
\tag{4.6}
\]

The discarded real mass is

\[
\Pr[Z\in C]\Pr[U\ne u_0]
=\frac cN\frac{N-1}{N},
\]

and the discarded ideal mass is

\[
\Pr[Z\in C]\Pr[Y\ne w_Z\mid Z\in C]
=\frac cN\frac{N-1}{N}.
\]

These are equal to (4.3). Once discarded, the game bit is kept equal to
one, so both conditions are monotone. \(\square\)

The real thinning in (4.4) is necessary for exact equality of retained
mass. Merely requiring consistency on the ideal side would retain
\(1/N\) real mass and \(1/N^2\) ideal mass in an occupied matching cell.

### 4.1. Descriptor form

For adaptive executions it is convenient to apply Lemma 4.2 one pending
site at a time. A link descriptor is a pair

\[
d=(x,(t,z))
\tag{4.7}
\]

where \(x\) has been queried at the construction interface,
\(t=t(x)\), and \((t,z)\) is a distinct pending outer site.
The game records that the pair has been tested, so the same descriptor is
never applied twice.

If \(Z_x\ne z\), the descriptor retains all mass. If \(Z_x=z\), the real
side uses the \(1/N\) thinning in (4.4), and the ideal side retains exactly
when the pending answer equals the construction answer. For a fixed \(x\),
at most one distinct \(z\) can equal \(Z_x\). Hence the descriptor
conditions compose without multiplying the charge in (4.3).

The descriptor is created only after both of its public objects exist. It
may inspect the hidden seed value \(Z_x\); a game condition is allowed to
depend on system randomness, and its bit is hidden from the distinguisher.
Thus the condition is causal even when the construction query and pending
query occur in the opposite order.

The embedded value \(z\) in a new descriptor may depend on all earlier
visible answers, including \(Y_x\). The adaptive proof therefore never
asserts that the final realized set \(C\) is independent of \(Y_x\).
Instead, it uses deferred sampling to bound the equality
\(Z_x=z\) at the moment each descriptor is created. This distinction is
used explicitly in Lemma 7.2.

### Lemma 4.3 (the two temporal orders)

At the public transition that creates a descriptor, the rules in
Lemma 4.2 give equal retained one-step submass in both temporal orders.

#### Proof

Suppose first that the pending site exists before the construction query.
The retained history fixes \(z\) and \(w_z\).

If \(Z_x\ne z\), this descriptor imposes no relation on the construction
answer and retains the whole mass assigned by the remaining descriptors.
If \(Z_x=z\), the real answer is the fixed value \(w_z\); retaining it with
probability \(1/N\) gives transition mass \(1/N\) at that answer. The ideal
answer is uniform and is retained exactly when it equals \(w_z\), which
gives the same transition mass \(1/N\).

Suppose instead that the construction query exists before the pending site.
The retained history fixes its answer \(Y_x\). If \(Z_x\ne z\), this
descriptor again imposes no relation and retains all mass. If \(Z_x=z\),
the real pending answer is the obligated \(Y_x\); retaining it with
probability \(1/N\) agrees with the ideal rule that retains its fresh answer
exactly when it equals \(Y_x\).

If \(Z_x\) was already publicly certified before the outer query, the site
with \(z=Z_x\) is linked and creates no descriptor. Thus the preceding cases
are exhaustive. \(\square\)

## 5. Deferred sampling and the graph event

### Lemma 5.1 (adaptive deferred sampling)

Let \(G\) be uniform in \(\mathcal C^{\mathcal D}\). Suppose that
\(P_i\in\mathcal D\) is selected from the values exposed before round \(i\).
Conditional on \(P_i\) not having appeared earlier,

\[
\Pr[G(P_i)=y\mid\text{the previous table}]=\frac1N
\tag{5.1}
\]

for every \(y\in\mathcal C\). If \(P_i\) appeared earlier, its answer is
the stored answer.

The same law is obtained if unobserved table entries are represented as
ghost assignments and are revealed only when first needed.

#### Proof

Fix a partial table with \(m\) distinct assigned points. Exactly

\[
N^{|\mathcal D|-m}
\]

complete functions extend it. At a new point, exactly
\(N^{|\mathcal D|-m-1}\) extensions give each prescribed answer \(y\).
This proves (5.1). Induction over the adaptively selected points proves the
first assertion. The count depends only on the assigned partial table, not
on the order in which its coordinates were exposed, which proves the ghost
form. \(\square\)

Lemma 5.1 permits the proof to audit the hidden inner and outer paths of a
construction query without installing those paths in the simulator. A
future direct query either reveals the corresponding ghost value or names
an unrelated fresh point. Naming an unexposed ghost source is included in
the graph event below.

### 5.1. Critical samples and external targets

A critical sample is any of the following first-assignment values:

1. the output of a distinct direct compression query that is propagated as
   an inner state, an inner endpoint, or a nonterminal outer state;
2. a nonterminal state on a hidden inner or outer construction path;
3. an inner endpoint.

Ordinary loose-root answers, invalid-word answers, pending or linked outer
terminal answers, and the final outer value of a construction query are not
critical: none is inserted into the live-word graph. A direct query can
still contribute at most one critical sample, so (2.3) bounds their total
number by \(s\).

A loose root is a chaining value first used as the source of a direct
compression query when it has no certified word and is not an already
exposed critical value. There are at most \(q\) distinct loose roots. If a
query source is an exposed live critical value, its word is already
certified. If an ordinary terminal or invalid answer is later used as a
source, that use creates a loose root and is charged only from that point
onward.

A pending target is the embedded value \(z\) in a newly queried unlinked
outer terminal \(O(t,z)\). A direct compression query contributes at most
one external target:

- an undefined source contributes its loose root; or
- a parsed unlinked outer terminal contributes its pending target.

The alternatives are disjoint because parsing an outer terminal requires a
certified source word. Hence the total number of external targets is at most
\(q\).

### 5.2. The monotone bad event

The game bit is the disjunction

\[
\mathsf{Bad}
=
\mathsf{Join}\vee
\mathsf{Select}\vee
\mathsf{Link}\vee
\mathsf{Parse}.
\tag{5.2}
\]

Its prefix-closed running value is the monotone bad event (MBO) used by the
proof.

The branch \(\mathsf{Join}\) fires when a critical sample equals

- \(\mathsf{IV}\);
- a previous critical sample; or
- a loose root.

Both temporal orders of the last event are included. If the root exists
first, the equality is detected when the hidden state is sampled. If the
state exists first, the equality is detected when the loose root is named.

The branch \(\mathsf{Select}\) handles adaptive choice of a construction
input. It fires if a completed inner endpoint \(Z_x\) equals a compatible
pending target \((t(x),z)\) that existed before \(x\) was queried at the
construction interface. If the pending target exists first, the equality is
detected when \(Z_x\) is sampled or revealed. If \(Z_x\) exists first but
remains hidden in a ghost path, it is detected when the target is named.

This branch is essential for a tight adaptive statement. Without it, a
distinguisher could expose many candidate endpoints, choose a candidate only
after seeing that it hits a pending target, and turn a nominal \(1/N\)
descriptor probability into a search probability. If \(x\) was already a
construction query before the equality became available, no such selection
occurred; that case is retained through the sharper \(\mathsf{Link}\)
condition.

Within a fresh construction-query transition, \(x\) is considered fixed
before its hidden path is audited. Thus an endpoint first sampled by that
audit uses \(\mathsf{Link}\), not \(\mathsf{Select}\). This ordering reflects
the information available to the distinguisher: it chose \(x\) before
receiving the construction answer.

The branch \(\mathsf{Link}\) is the discarded branch of Lemma 4.2 for any
link descriptor.

The branch \(\mathsf{Parse}\) records an ambiguous live word or two semantic
decodings of one complete word. Lemma 6.1 shows

\[
\mathsf{Parse}\subseteq\mathsf{Join},
\tag{5.3}
\]

so it has no separate probability charge.

All four branches are prefix-monotone. After the first branch fires, the
underlying representative continues with its original transition law and
the bit remains one. Erasing the bit therefore recovers the representatives
in Lemma 3.1 exactly.

## 6. Equality of all pre-winning transcript masses

### Lemma 6.1 (unique typed paths)

Before \(\mathsf{Join}\), every indexed live state has one certified path
word from \(\mathsf{IV}\). That word has at most one role and at most one
complete parse. A correctly tagged linked outer terminal determines at most
one construction input.

#### Proof

Initially only \(\mathsf{IV}\) has the empty word. A new live destination is
installed only when it is different from \(\mathsf{IV}\), every previous
critical value, and every loose root. Thus it cannot already have a
different certified predecessor. Induction gives one word per indexed
state.

The first block separates the inner and outer roles by (1.4). Inner
injectivity and outer unique decoding give uniqueness within each role. A
complete outer word is terminal. Hence two different parses or two
different words at one state imply an earlier critical-state equality.
This proves (5.3) and the lemma. \(\square\)

### Lemma 6.2 (fresh-path law)

Fix a public history before \(\mathsf{Bad}\), together with its certified
partial table and ghost paths.

1. A new nonterminal state is uniform on \(\mathcal C\) before the join
   test.
2. If an outer terminal is not pending, its fresh answer is uniform and
   independent of the preceding path.
3. For a fixed pending profile independent of the still-unexposed endpoint
   and answer coordinates, their simultaneous law is (4.1) and (4.2). For
   an adaptive profile, every newly related site has the one-row common
   condition of Lemma 4.2.
4. A direct query cannot meet an unexposed ghost edge without either
   following its certified prefix or causing \(\mathsf{Join}\).

#### Proof

Every new path edge selects a compression point as a function of the
already exposed path. Lemma 5.1 gives a fresh uniform answer at a new
point. This proves the first assertion.

At a nonpending outer terminal, the terminal point has not been assigned.
Lemma 5.1 makes its answer a new uniform coordinate, independent of the
earlier path. At a fixed pending terminal, the stored answer must be reused.
For the unique row \(Z=z\), this is exactly the first line of (4.1); all
other rows use a fresh terminal coordinate.

If the site was chosen adaptively, freeze the public history immediately
before its unresolved endpoint equality is tested. Its embedded value is
then fixed, while the fresh endpoint coordinate is uniform by Lemma 5.1.
The real and ideal answer relation in the equality row is exactly the
one-row instance of Lemma 4.2. This proves the second and third assertions
without conditioning on the final adaptive profile.

Finally, an unexposed ghost edge has a hidden source state. If a direct
query reaches it by its certified predecessor, it is an ordinary sequential
reveal. Otherwise the direct query must name the hidden source as a loose
root, which is the loose-root branch of \(\mathsf{Join}\). \(\square\)

### 6.1. The retained-state invariant

The pre-winning induction uses an audit state that is not visible to the
simulator. On retained histories it satisfies the following invariant.

1. The real and ideal retained submasses are indexed by the same public
   table, word index, inner index, pending index, and seen set.
2. Every indexed word follows the public table from \(\mathsf{IV}\).
3. Every hidden construction path has a ghost trace. Any part already
   revealed at the primitive interface agrees with the public table.
4. A queried construction input carries a terminal obligation
   \((x,p,Y_x)\), where \(p\) is its semantic outer-terminal point. On the
   real side the hidden compression coordinate at \(p\) equals \(Y_x\). On
   the ideal side the ordinary tape coordinate at \(p\) remains deferred
   until the simulator either links or exposes it as a pending site.
5. A ghost path and an unrelated public path have disjoint live states.
6. Every correctly tagged outer terminal carries at most one construction
   obligation.
7. For every construction input and pending site already related by a link
   descriptor, the retained real and ideal masses agree pointwise as in
   Lemma 4.2.

The audit state is proof data only. In particular, items 3 and 4 do not
notify the ideal simulator that a construction query occurred and do not
write its ordinary tape.

### 6.2. One-step retained kernel

Let \(h\) be a retained audit state and let \(u\) be the next public query.
For \(W\in\{\mathbf A,\mathbf B\}\), write

\[
\mu^W_{h,u}(y,h')
\]

for the one-step mass of answer \(y\) and successor audit state \(h'\).
The successor audit state records every fresh semantic coordinate exposed by
the transition, including ghost coordinates. Auxiliary thinning coins are
summed into the retained or residual branch mass. Thus the two kernels are
mass functions on one common finite successor-atom set
\(\mathcal A_{h,u}\).

### Lemma 6.3 (one-step common subkernel)

For every retained \(h\) and public query \(u\), there is a nonnegative
subkernel \(\kappa_{h,u}\) such that

\[
\mu^{\mathbf A}_{h,u}
=\kappa_{h,u}+\rho^{\mathbf A}_{h,u},
\qquad
\mu^{\mathbf B}_{h,u}
=\kappa_{h,u}+\rho^{\mathbf B}_{h,u},
\tag{6.1}
\]

where both residuals are nonnegative. The common subkernel consists exactly
of transitions that preserve the retained-state invariant. Every residual
transition is labeled by \(\mathsf{Join}\), \(\mathsf{Select}\), or
\(\mathsf{Link}\).

#### Proof

Apply Lemma 5.1 to every fresh ordinary coordinate and first classify all
outcomes that cause a graph join. Next classify an endpoint/pending-target
equality as \(\mathsf{Select}\) when the endpoint's input had not yet been
queried at the construction interface. On the complementary branch, inner
endpoints and outer obligations are unique by Lemma 6.1, and every
construction input was fixed before its unresolved endpoint test. Apply the
pointwise common condition in Lemma 4.2 to every link descriptor there. The
resulting retained mass is \(\kappa_{h,u}\). The complements in (6.1) are
nonnegative by construction.

Equivalently, after the auxiliary thinning coins have been marginalized, the
definition on successor atoms is pointwise:

\[
\kappa_{h,u}(\alpha)
=
\begin{cases}
0,
  &\alpha\text{ causes }\mathsf{Join}\text{ or }\mathsf{Select},\\
\min\{\mu^{\mathbf A}_{h,u}(\alpha),
      \mu^{\mathbf B}_{h,u}(\alpha)\},
  &\text{otherwise}.
\end{cases}
\]

The transition audit below proves more than the tautological common-part
identity: on a no-join, no-selection atom the two masses are already equal
at every ordinary coordinate, and their only possible difference is exactly an
occupied-link row. Although one public transition can create several
descriptors, at most one is active on a no-join atom: a fixed endpoint has
one embedded value, and distinct construction obligations have distinct
endpoints. Every other descriptor retains all mass. Lemmas 4.2 and 4.3
therefore identify the displayed minimum and its residual charge.

For completeness, consider separately the only transition whose random
coordinates are not all public.

On a fresh construction query, audit the real inner and outer evaluations in
their execution order. A table hit reuses the common retained table.
Every new nonterminal point has the common uniform law of Lemma 5.1, and an
unrecognized overlap is a join. At a fresh outer terminal, the real
compression coordinate and the ideal construction coordinate are both one
new uniform value; record that common value as the terminal obligation
\((x,p,Y_x)\). The ideal ordinary coordinate at \(p\) is not sampled by the
simulator and remains deferred. If \(p\) was already represented by a
compatible pending site, use Lemma 4.2 instead. These are the only two
terminal cases by Lemma 6.1.

Suppose that a later primitive query reaches a recorded terminal obligation.
If the matching inner endpoint is already certified, the native linked leaf
returns \(Y_x\) in both representatives. If it is not certified, the query
creates a pending site: the real ordinary coordinate is the obligated
\(Y_x\), the ideal ordinary coordinate is fresh and independent, and
Lemma 4.2 gives their exact common submass. A query that names the terminal
point without following its semantic prefix must name a hidden live source
and is a join. Thus deferring the ideal terminal coordinate creates no
unclassified case.

All remaining transitions expose only public-table coordinates. Section 6.3
lists every native observation made by the machine and checks its retained
action. There is no default branch. \(\square\)

### 6.3. Exhaustive transition audit

The construction interface has two leaves.

| Observation | Retained action |
|---|---|
| \(x\in\mathsf{seen}\) | Return the stored construction coordinate. No state or probability changes. |
| \(x\notin\mathsf{seen}\) | Audit the hidden inner and outer paths by deferred sampling. Fresh nonterminal states use Lemma 5.1; graph coincidences are \(\mathsf{Join}\). If an already exposed endpoint was used to select \(x\) after a pending-target hit, \(\mathsf{Select}\) has already fired; otherwise every compatible pending site uses Lemma 4.2. The retained answer is inserted in \(\mathsf{seen}\). |

The primitive interface first splits on the table lookup, then on the source
word, then on every constructor of (1.8), and finally on the inner lookup
and tag equality. This gives exactly nine leaves.

| Leaf | Machine action | Retained-law justification |
|---|---|---|
| table hit | Return the stored value. | The retained tables are identical. |
| undefined source word | Sample an ordinary value and record a loose root. | Lemma 5.1; meeting a hidden ghost source is \(\mathsf{Join}\). |
| inner prefix | Sample and propagate a live state. | Lemma 5.1, followed by the IV/live/loose join test. |
| complete inner word | Sample and record \(\mathsf{inner}[z]=x\). | The same fresh-state test. Equality with an earlier pending target is \(\mathsf{Select}\) if \(x\notin\mathsf{seen}\), and otherwise reveals the already fixed link condition. No descriptor is charged twice. |
| outer prefix | Sample and propagate a live state. | Lemma 5.1, followed by the join test. |
| complete outer word, no inner entry | Sample and record a pending site. | Ordinary lazy sampling. Compare its embedded value with hidden audited endpoints: an unseen matching input gives \(\mathsf{Select}\); every already seen compatible \(x\) gives the descriptor (4.7) and Lemma 4.2. |
| complete outer word, wrong tag | Sample and record a pending site. | The tag mismatch forbids a link; otherwise identical to the preceding leaf. |
| complete outer word, correct tag | Return the construction coordinate and install it at the terminal point. | Lemma 6.1 gives one obligation. In the real representative Lemma 3.1 identifies this coordinate with the terminal compression answer; in the ideal representative it is the required oracle answer. |
| invalid word | Sample and install an ordinary value without live propagation. | Lemma 5.1; no semantic index changes. |

Every live propagation has four destination outcomes: equality with
\(\mathsf{IV}\), equality with an indexed live state, equality with a loose
root, or freshness. The first three set \(\mathsf{Join}\); only the fourth
installs a new word. Thus changes to the parser or to any lookup create a new
mathematical case rather than being absorbed into an unspecified ordinary
branch.

The table also covers legitimate prefix reuse. If a compression point was
already exposed along the same certified word, it is a table hit and creates
no new sample. If two different words try to reuse it, their source or
destination equality is already \(\mathsf{Join}\).

### Theorem 6.4 (pre-winning conditional equivalence)

There are honest monotone games \(\widehat A\) and \(\widehat B\) such that

\[
\widehat A^{-}=\mathbf A,
\qquad
\widehat B^{-}=\mathbf B,
\qquad
\widehat A\equiv_g\widehat B.
\tag{6.2}
\]

#### Proof

Enlarge the real representative by the independent thinning coordinates of
Lemma 4.2. Their erasure leaves its law unchanged. Label every residual in
Lemma 6.3 bad, continue with the original representative after the first
bad label, and keep the bit equal to one thereafter. This constructs two
causal kernel families. Lemma 2.2 realizes them as honest monotone games.
Equation (6.1) reconstructs the complete transition kernel on each side.
Lemmas 3.1 and 5.1 identify those kernels with the original real and
ideal representatives. Erasing the bit therefore proves the first two
identities in (6.2).

For the third identity, induct on the length of a fixed public transcript.
At length zero, both retained audit states have mass one. Suppose the
retained audit-state masses agree after a prefix. Multiplying each common
mass by the same subkernel \(\kappa_{h,u}\) in Lemma 6.3 gives equal masses
for every retained answer and successor audit state. Summing over audit
states gives

\[
\Pr_{\widehat A}[Y^i=y^i,A_i=0\mid X^i=x^i]
=
\Pr_{\widehat B}[Y^i=y^i,A_i=0\mid X^i=x^i].
\tag{6.3}
\]

This is (2.4), hence \(\widehat A\equiv_g\widehat B\). The induction is over
the actual interleaved query order and therefore already includes adaptive
histories. \(\square\)

Theorem 6.4 is the exact-until-bad statement. It compares unnormalized
retained masses. It does not assume that the survival probability is
independent of the transcript, and it does not normalize after each local
condition.

## 7. Mass of the bad event

The counting below is deliberately performed on unnormalized mass.
Conditioning on earlier retained link tests can bias a hidden endpoint.
Unnormalized common mass is pointwise dominated by the independent ideal
lazy-sampling law, so restricting to an earlier good event can only decrease
the mass of every later collision descriptor.

Here \(\Pr[\mathsf{Join}]\), \(\Pr[\mathsf{Select}]\), and
\(\Pr[\mathsf{Link}]\) denote first-bad mass: the prefix was retained before
the named branch fired. Transitions after an earlier bad label are not
charged again. By Lemma 2.1 the two games have the same total winning
probability. We bound that common value by counting first-bad mass in the
ideal monitored game, whose construction and ordinary tapes are
independent.

### Lemma 7.1 (graph joins and adaptive selection)

With at most \(s\) critical samples and \(q\) external targets,

\[
\Pr[\mathsf{Join}\vee\mathsf{Select}]
\le
\frac{\binom{s+1}{2}+qs}{N}.
\tag{7.1}
\]

#### Proof

Order first-assignment critical values by the moment at which the audit
exposes them. Lemma 5.1 supplies an independent uniform coordinate whenever
the selected compression point is new. Legitimate table reuse creates no
coordinate. Illegitimate reuse is already one of the join witnesses.

For the \(j\)-th critical coordinate, equality with
\(\mathsf{IV}\) or one of the preceding \(j-1\) coordinates contributes at
most

\[
\frac jN
\]

of unnormalized mass. Summing over \(j=1,\ldots,s\) gives

\[
\frac{1+2+\cdots+s}{N}
=
\frac{\binom{s+1}{2}}{N}.
\tag{7.2}
\]

There are at most \(qs\) external-target/critical-coordinate descriptors.
For a loose root, if the root is named first, the later fresh coordinate
hits it with mass \(1/N\). If the hidden coordinate exists first, the root
is selected from the public history while that coordinate remains an
unexposed ideal lazy-sampling value. Its equality mass is again at most
\(1/N\). A source with a certified live word is not loose and its merge was
counted as a critical--critical equality. A previously visible terminal or
invalid answer has no certified word; if it is later used as a source, it is
a loose root, and independence from the still-hidden live coordinate gives
the same \(1/N\) charge.

For a pending target, the same two temporal orders apply. If the target is
present first, a later unresolved inner endpoint hits it with mass \(1/N\).
If a hidden endpoint exists first, naming the target is an adaptive guess of
that independent ideal coordinate. A hit belonging to an input already
fixed at the construction interface is not classified as
\(\mathsf{Select}\) and is handled by Lemma 7.2; deleting those descriptors
only decreases the present count.

Earlier retained conditions only restrict the common submass. Pointwise
domination by the independent ideal tape shows that they cannot increase
any one of these unnormalized descriptor masses. The union bound over
(7.2) and the \(qs\) external-target descriptors proves (7.1).
\(\square\)

### Lemma 7.2 (adaptive link mass)

Let \(p\) bound the number of distinct pending outer sites over every run.
Then

\[
\Pr[\mathsf{Link}]
\le
\frac{pa(N-1)}{N^2}.
\tag{7.3}
\]

#### Proof

Pair each distinct queried construction input with each compatible pending
site. There are at most \(pa\) link descriptors.

Consider one descriptor \(d=(x,(t(x),z))\). It is created only while \(z\)
is not a known endpoint of \(x\); otherwise the terminal query is linked,
not pending. Moreover, the retained prefix has not fired
\(\mathsf{Select}\). Therefore, if the pending target existed before the
construction query, the input \(x\) was not selected after observing a
matching endpoint. Equivalently, on every equality-bearing retained branch,
one of \(x\) and \(z\) was fixed before the unresolved endpoint coordinate
was available.

In the independent ideal lazy-sampling law, that endpoint is uniform at its
first fresh assignment. If it was assigned earlier but remained hidden, a
later embedded value is an adaptive guess of an unexposed independent
coordinate. Thus, in either temporal order,

\[
\Pr[Z_x=z]\le\frac1N
\tag{7.4}
\]

in unnormalized ideal mass. This is precisely the deferred-sampling
statement of Lemma 5.1.

Conditional on this equality, the ideal residual is the event that two
independent uniform answers disagree, of probability \((N-1)/N\). The real
residual uses the independent thinning coordinate and has the same
probability. Hence the residual mass assigned to one descriptor is at most

\[
\frac1N\frac{N-1}{N}
=
\frac{N-1}{N^2}.
\tag{7.5}
\]

For one \(x\), distinct descriptor equalities \(Z_x=z\) are disjoint.
Across different \(x\), a union bound is sufficient. As in Lemma 7.1,
intersecting with previous retained conditions cannot increase the
unnormalized mass in (7.5).

Formally, order descriptors by their creation time and append dummy
descriptors until the list has length \(pa\). For each position, sum
(7.4) over the disjoint retained histories at which that position is
created. Histories in which \(x\) was selected after its endpoint hit a
prior target belong to \(\mathsf{Select}\) and are absent. Deferred sampling
therefore bounds the total incoming mass of the remaining equality-bearing
histories by \(1/N\); the mismatch or thinning factor then bounds their
residual mass by (7.5). A union bound over the \(pa\) positions proves
(7.3). \(\square\)

Each new pending site requires a distinct direct terminal compression
query. Therefore

\[
p\le q.
\tag{7.6}
\]

### Theorem 7.3 (framing-aware SequenceHash bound)

Under Lemma 1.1, every adaptive distinguisher satisfying the workload bounds
in Section 2 has

\[
\operatorname{Adv}_{\mathrm{indiff}}
\le
\min\!\left\{
1,\,
\frac{\binom{s+1}{2}+qs}{N}
+
\frac{pa(N-1)}{N^2}
\right\}.
\tag{7.7}
\]

Consequently,

\[
\operatorname{Adv}_{\mathrm{indiff}}
\le
\min\!\left\{
1,\,
\frac{\binom{\sigma-a+1}{2}+q(\sigma-a)}{N}
+
\frac{qa(N-1)}{N^2}
\right\}.
\tag{7.8}
\]

#### Proof

Theorem 6.4 and Lemma 2.1 bound distinguishing advantage by the common
winning probability of the two games. The parse branch is contained in the
join branch by Lemma 6.1. A union bound, followed by Lemmas 7.1 and 7.2,
gives (7.7). Substitute \(s\le\sigma-a\) from (2.3) and \(p\le q\) from
(7.6). The right-hand side is monotone in \(s\) and \(p\), which gives
(7.8). Statistical distance is at most one, giving the displayed caps.
\(\square\)

### Corollary 7.4 (simple quadratic form)

For every workload,

\[
\operatorname{Adv}_{\mathrm{indiff}}
\le
\min\!\left\{1,\frac{2\sigma^2}{N}\right\}.
\tag{7.9}
\]

#### Proof

The statement is immediate when \(\sigma=0\). Suppose \(\sigma\ge1\). Since
\((N-1)/N\le1\), the numerator obtained from (7.8) over the common
denominator \(N\) is at most

\[
\binom{\sigma-a+1}{2}
+q(\sigma-a)+qa
=
\binom{\sigma-a+1}{2}+q\sigma.
\]

Now \(0\le a\le\sigma\), \(q\le\sigma\), and

\[
\binom{\sigma-a+1}{2}
\le
\binom{\sigma+1}{2}
\le\sigma^2.
\]

Thus the numerator is at most \(2\sigma^2\). \(\square\)

### 7.1. Simulator complexity

The simulator consults \(r(x)\) only when a fresh direct compression query
completes a correctly tagged linked outer word. There is at most one such
consultation per distinct direct compression query, so the simulator makes
at most \(q\) ideal-oracle calls. Construction-interface calls made by the
distinguisher are not counted as simulator calls.

The table and all indices contain at most polynomially many entries in the
public transcript length. Parent pointers and incremental parsers therefore
give polynomial time and space. No exhaustive search over \(\mathcal C\) is
required.

## 8. Comparison with the HMAC simulator

The DRST proof for HMAC over strengthened Merkle--Damgård first proves an
intermediate replacement bounded by \(10\sigma^2/N\) in its Lemma 4.5. Its
preimage-awareness and composition steps yield the endpoint in its
Theorem 4.4:

\[
\operatorname{Adv}_{\rm HMAC}
<
\frac{13\sigma^2}{N}
\qquad
\text{for }\sigma\le N/4.
\tag{8.1}
\]

The stable SequenceHash framing exposes information that is hidden in HMAC.

- The first block is exactly \(K_I\) or \(K_O\).
- The blocks differ unconditionally.
- The next block is role-specific.
- Fixed-width outer fields determine the outer parse.
- Suffix lengths determine the inner input.

Consequently, one typed graph replaces the allowed-key parser, colored
compression oracles, and separate preimage extractor used for HMAC. For this
different and more strongly framed construction, Corollary 7.4 gives

\[
\frac{2\sigma^2}{N}
\tag{8.2}
\]

instead of the HMAC envelope in (8.1). The sharper statement is (7.8),
which separates construction terminals, graph joins and external targets,
and the pending links retained through the exact condition. Equation (7.8)
is valid for every finite budget after capping by one; the DRST statement
quoted in (8.1) is restricted to \(\sigma\le N/4\).

This comparison explains the proof simplification. It is not a claim that
the HMAC theorem itself can be replaced by (7.8), because the constructions
have different framing.

## 9. Matching attack against the stated simulator

Assume that the stable encoding contains \(r\) valid inputs
\(x_1,\ldots,x_r\) with one common outer tag and inner words of the form

\[
I(x_i)=P\mathbin\|B_i,
\tag{9.1}
\]

where the final complete padded blocks \(B_i\) are distinct. Standard SHA-2
instances of stable SequenceHash supply such families: choose equal-length
one-item messages so that the last strengthened block contains variable
message bytes, keep all earlier bytes fixed, and vary those bytes. The item
length and strengthening fields then remain common. If \(d\) bytes of that
block are variable, this gives every \(r\le256^d\).

The distinguisher first evaluates the common prefix \(P\) through the
compression interface, reaching a state \(v\). It then queries the \(r\)
distinct points

\[
(v,B_1),\ldots,(v,B_r)
\]

and receives \(Z_1,\ldots,Z_r\). Finally it queries the construction
interface on every \(x_i\), receiving \(Y_1,\ldots,Y_r\). It accepts exactly
when

\[
\exists\,i<j:
\quad
Z_i=Z_j
\quad\text{and}\quad
Y_i\ne Y_j.
\tag{9.2}
\]

### Proposition 9.1 (birthday lower bound)

Let

\[
M=\binom r2,
\qquad
\eta=\frac{N-1}{N^2}.
\]

For every family satisfying (9.1), against the simulator of Section 3, the
attack in (9.2) has advantage at least

\[
M\eta-\binom M2\eta^2.
\tag{9.3}
\]

In particular, if \(r=o(\sqrt N)\) as \(N\to\infty\), then

\[
\operatorname{Adv}
\ge
(1-o(1))\frac{\binom r2}{N}.
\tag{9.4}
\]

#### Proof

In the real system, \(Z_i=Z_j\) and \(t(x_i)=t(x_j)\) imply

\[
O(t(x_i),Z_i)=O(t(x_j),Z_j).
\]

The two outer Merkle--Damgård computations are identical, so
\(Y_i=Y_j\). The real acceptance probability is therefore zero.

In the ideal system, the \(r\) queried compression points are distinct.
The simulator answers the complete inner leaves from its ordinary uniform
tape, so \(Z_1,\ldots,Z_r\) are independent uniform values. The construction
answers \(Y_1,\ldots,Y_r\) are independent uniform values from \(r\), and
they are independent of the \(Z_i\).

For \(i<j\), let

\[
E_{ij}=\{Z_i=Z_j,\ Y_i\ne Y_j\}.
\]

Then

\[
\Pr[E_{ij}]
=\frac1N\left(1-\frac1N\right)
=\eta.
\tag{9.5}
\]

For two distinct unordered pairs, the two equality constraints on the
\(Z\)-coordinates have probability \(1/N^2\). This remains true when the
pairs share one index. Conditional on the relevant \(Y\)-coordinate or
coordinates, the two inequality constraints have probability
\(((N-1)/N)^2\). Hence

\[
\Pr[E_{ij}\cap E_{k\ell}]=\eta^2
\tag{9.6}
\]

for any two distinct pair indices. The first two terms of
Bonferroni's inequality give

\[
\Pr\!\left[\bigcup_{i<j}E_{ij}\right]
\ge
\sum_{i<j}\Pr[E_{ij}]
-
\sum_{\{i,j\}<\{k,\ell\}}
\Pr[E_{ij}\cap E_{k\ell}],
\]

which is (9.3). If \(M/N\to0\), the second term is
\(o(M/N)\), proving (9.4). \(\square\)

The common prefix is queried once and every branch has constant additional
cost. If the inner and outer schedules are fixed, then
\(\sigma=\Theta(r)\). Proposition 9.1 is therefore
\(\Theta(\sigma^2/N)\) below the birthday threshold. The exponent in
Corollary 7.4 is tight for the stated simulator. At \(r=2\), the exact
attack advantage is \((N-1)/N^2\), equal to the one-row occupied-link
charge.

## 10. Extensions

### 10.1. Several public short customization strings

For several fixed short customization strings, include \(S\) in the outer
tag and in the pending index. Distinct tags have distinct outer words. The
proof applies with workload totals summed over tags. A refined theorem may
retain shared inner prefixes across tags instead of charging them twice.

### 10.2. Long customization strings

When \(|S|>b\), stable v1.0.0 first computes a digest of \(S\). This creates
a third path type and a second hidden link. The simulator then needs a
\(\mathsf{custom}\) index and a second occupied-link condition. The present
theorem does not include that additional path or its overlap with framed
inner and outer words.

### 10.3. SequenceMAC

For SequenceMAC, \(K_I\) and \(K_O\) depend on the secret key and can
themselves require hashing. Key derivation becomes another hidden-link
layer. The public role headers remain useful, but Lemma 1.1 must be replaced
by the corresponding keyed grammar and key-derivation analysis.

## Appendix A. Validation ledger

This appendix records the checks needed for the theorem. It is not an
additional source of assumptions.

### A.1. Marginals

1. The real machine identity is unconditional: every ordinary primitive
   leaf returns \(f(v,B)\), and the linked leaf returns the same value by
   path certification.
2. The ideal representative samples \(r\) and \(g\) independently and is
   exactly the simulator in Section 3.
3. Real thinning coordinates are independent unused randomness. Erasing
   the game bit and these coordinates recovers the original real law.
4. Every common/residual decomposition is nonnegative and reconstructs its
   original law pointwise.

### A.2. Causality and monotonicity

1. A link descriptor is evaluated only after its construction input and
   pending site both exist.
2. The condition may inspect hidden seed values but never reveals them.
3. A pending-target hit that occurs before its construction input is fixed
   is labeled \(\mathsf{Select}\); it cannot be exploited later without
   already being bad.
4. Once any residual, graph join, or selection event is labeled bad, all
   later prefixes remain bad.
5. Hidden construction traces are proof-only ghost data; they do not update
   the simulator.

### A.3. Exhaustiveness

The proof separates both construction leaves, all nine primitive leaves,
and all four destination-propagation outcomes. Repeats, inner completion,
outer completion before and after its inner link, wrong tags, invalid words,
loose roots, and pending-target selection each have an explicit branch.

### A.4. Adaptivity

Theorem 6.4 is an induction over arbitrary interleaved public histories.
Lemmas 7.1 and 7.2 use adaptive deferred sampling. They estimate
unnormalized descriptor mass and therefore do not assume that endpoint
coordinates remain uniform after conditioning on earlier successful tests.
In particular, exposing \(k\) candidate endpoints and only then choosing a
construction input that hits one of \(p\) pending values is charged by the
\(pk\) pending-target descriptors inside the \(qs/N\) term, not
incorrectly by one link descriptor.

### A.5. Counting

1. At most \(s\) IV/live or live/live samples give
   \(\binom{s+1}{2}\) descriptors.
2. Every direct query contributes at most one loose-root or pending-value
   target. At most \(q\) external targets and \(s\) critical samples
   therefore give \(qs\) descriptors.
3. At most \(p\) pending sites and \(a\) construction inputs give \(pa\)
   link descriptors after selection hits have been removed.
4. Every pending site comes from a distinct direct compression query, so
   \(p\le q\).
5. Every construction computation contributes at most one fewer critical
   state than compression calls, giving \(s\le\sigma-a\).

### A.6. Boundary cases

If \(N=1\), the link charge is zero and all displayed upper bounds remain
valid. If \(\sigma=0\), both systems have the empty transcript and advantage
zero. When a displayed combinatorial expression exceeds one, the statistical
distance cap in Theorem 7.3 applies. No division by a survival probability is
used, so a zero common-mass fiber causes no undefined conditional law.

## Appendix B. Proof status

| Item | Status |
|---|---|
| Stable v1.0.0 short-customization grammar | Closed in this paper |
| Exact common-machine representative lemma | Closed in this paper |
| Positive occupied-link condition and exact coefficient | Closed in this paper |
| Deferred-path invariant and all transition cases | Closed in this paper |
| Adaptive pre-winning game equivalence | Closed in this paper |
| Adaptive join, selection, and link counts | Closed in this paper |
| Finite bound (7.8) and quadratic corollary | Closed in this paper |
| Matching birthday-order attack against the stated simulator | Closed in this paper |
| Long-customization extension | Open |
| SequenceMAC keyed extension | Open |
| End-to-end stable-v1 Lean theorem | Open |

The paper theorem is complete under the explicit short-customization and
typed-grammar hypotheses. The last row means only that the complete theorem
has not yet been checked by the Lean kernel; it is not an additional
mathematical premise.

## References

1. C2SP, [SequenceHash and SequenceMAC](../../sequence-hash/specs/v1.0.0/sequencehash.md),
   stable version v1.0.0.
2. Y. Dodis, T. Ristenpart, J. Steinberger, and S. Tessaro,
   [To Hash or Not to Hash Again? (In)differentiability Results for
   \(H^2\) and HMAC](../../sequence-hash/2013-382.pdf), full version, 2013.
3. U. Maurer, [Cryptography Foundations](../CR18_LN.pdf), ETH Zürich
   lecture notes, Spring 2018, Sections 4.10--4.11.
