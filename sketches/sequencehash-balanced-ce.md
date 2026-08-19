# SequenceHash balanced conditional equivalence - pen-and-paper sketch

This note develops a tighter conditional-equivalence analysis for the
fixed-short-customization SequenceHash simulator.  The proof changes the
ideal-world simulator itself: at a fresh semantic inner completion it uses a
balanced transport kernel determined by the already occupied outer sites.
It does not appeal to alternative PDS representatives, coupling, signed mass,
or Lanzenberger attainment.  The local transport theorem below is exact.  The
full compression-graph theorem is stated separately from the remaining global
counting obligation.

## (a) Objects

Let $\mathcal C$ be the chaining-value set and put $N=|\mathcal C|$.  Fix one
semantic construction input $x$.  Immediately before its hidden inner endpoint
is fixed, let

$$
C\subseteq\mathcal C
$$

be the set of already occupied outer terminal sites compatible with $x$.
For $z\in C$, let $w_z$ be the answer already stored at that site.  Write

$$
c=|C|,
\qquad
c_y=|\{z\in C:w_z=y\}|,
\qquad
r=|\{w_z:z\in C\}|.
$$

The real local coordinates are the inner endpoint $Z$ and the construction
answer $Y$.  Their law is

$$
P(z,y)=
\begin{cases}
1/N, & z\in C\text{ and }y=w_z,\\
1/N^2, & z\notin C,\\
0, & \text{otherwise}.
\end{cases}
\tag{1}
$$

The ideal construction answer must remain uniform.  The ideal simulator is
free to choose the conditional law of its primitive answer $Z$ given that
answer, subject to being an online oracle algorithm.

## (b) Exact balanced transport

When $c=0$, define $Q=P$.  When $r=N$, necessarily $c=N$ and every $c_y=1$;
again define $Q=P$.  In the remaining case $0<c$ and $r<N$, define

$$
Q(z,y)=
\begin{cases}
1/N^2,
  &z\notin C,\\[1mm]
c/(N^2c_{w_z}),
  &z\in C\text{ and }y=w_z,\\[1mm]
(Nc_{w_z}-c)/(N^2c_{w_z}(N-r)),
  &z\in C\text{ and }c_y=0,\\[1mm]
0,
  &\text{otherwise}.
\end{cases}
\tag{2}
$$

All entries are nonnegative because $c\le N$ and $c_{w_z}\ge1$.

### Lemma 1 (two uniform marginals)

Both the $Z$-marginal and the $Y$-marginal of $Q$ are uniform on
$\mathcal C$.

#### Proof

Every unoccupied row has mass $1/N$.  If $z\in C$ and $t=w_z$, its row mass
is

$$
\frac{c}{N^2c_t}
+(N-r)\frac{Nc_t-c}{N^2c_t(N-r)}
=\frac1N.
$$

For an occupied answer $y$, the occupied rows carrying $y$ contribute
$c/N^2$ and the $N-c$ unoccupied rows contribute $(N-c)/N^2$.  For an
unoccupied answer $y$, the occupied rows contribute

$$
\sum_{t:c_t>0}
c_t\frac{Nc_t-c}{N^2c_t(N-r)}
=\frac{Nc-cr}{N^2(N-r)}
=\frac c{N^2},
$$

and the unoccupied rows again contribute $(N-c)/N^2$.  Every column therefore
also has mass $1/N$.  $\square$

Consequently the ideal simulator can implement $Q$ after learning the ideal
answer $Y=y$ by sampling $Z$ with probability

$$
K(z\mid y)=NQ(z,y).
\tag{3}
$$

Unlike the naive posterior kernel $P(Z\mid Y)$, this balanced kernel leaves a
primitive-only transcript exactly uniform.

### Lemma 2 (exact local distance)

The distance between the real local law and the balanced ideal law is

$$
\delta(P,Q)=\frac{c(N-r)}{N^2}.
\tag{4}
$$

#### Proof

The laws agree on every unoccupied row.  In an occupied row $z$ with
$t=w_z$, the common mass is $c/(N^2c_t)$ at $(z,t)$.  The real surplus in
that row is

$$
\frac1N-\frac{c}{N^2c_t}.
$$

Summing over the $c_t$ rows of each of the $r$ occupied answer classes gives

$$
\sum_{t:c_t>0}
c_t\left(\frac1N-\frac{c}{N^2c_t}\right)
=\frac cN-\frac{cr}{N^2}
=\frac{c(N-r)}{N^2}.
$$

The same mass is placed by $Q$ in cells with $c_y=0$, where $P$ is zero.
Thus the displayed quantity is both one-sided excess and half the $L^1$
distance.  $\square$

### Lemma 3 (local optimality)

Among all ideal local laws whose $Y$-marginal is uniform, no simulator can
have distance from $P$ below (4).  The balanced law $Q$ attains this lower
bound while also keeping $Z$ uniform.

#### Proof

Data processing under projection to $Y$ gives

$$
\delta(P,Q')\ge
\delta(P_Y,U_{\mathcal C}).
$$

From (1),

$$
P_Y(y)=\frac{N-c}{N^2}+\frac{c_y}{N}.
$$

Because $0\le c\le N$, every nonzero $c_y$ is at least $c/N$.  Hence the
positive excess columns are exactly the $r$ occupied answer classes, and

$$
\delta(P_Y,U_{\mathcal C})
=\sum_{y:c_y>0}
\left(\frac{N-c}{N^2}+\frac{c_y}{N}-\frac1N\right)
=\frac{c(N-r)}{N^2}.
$$

Lemma 2 proves attainment.  $\square$

## (c) The honest condition games

Let

$$
H(z,y)=\min\{P(z,y),Q(z,y)\}.
$$

The real monitored system retains every unoccupied row and, in an occupied
row $z$ with $t=w_z$, retains the atom $(z,t)$ with probability

$$
\frac{H(z,t)}{P(z,t)}=\frac{c}{Nc_t}.
\tag{5}
$$

The ideal monitored system retains every atom in the support of $H$ and marks
as bad precisely the transported residual cells with $z\in C$ and $c_y=0$.
Both retained sublaws are exactly $H$ and both bad masses equal (4).  Taking
the running disjunction over successive activations gives honest MBOs.

This is the symmetric common-part game construction.  To invoke strict
one-sided CR18 conditional equivalence, one must package the common retained
kernel as the ordinary target system and separately strip the ideal game's
MBO.  No representative-optimization claim is used.

## (d) Sequential profile theorem

Let semantic activations be ordered by the first point at which both the
construction answer and its compatible occupied-site profile are fixed.
Write $C_j$, $c_j$, and $r_j$ for the realized profile at activation $j$.
Assume that all other compression-graph transitions are already in a common
good kernel.  Then the running common-part game gives

$$
\operatorname{Adv}
\le
\Pr[\mathsf{GraphConflict}]
+\mathbb E\left[
  \sum_j\frac{c_j(N-r_j)}{N^2}
\right].
\tag{6}
$$

Equation (6) uses a union bound only across activations.  A sharper finite
form retains the conditional survival product instead of replacing it by the
sum.

The profile term is pointwise no larger than the old charge:

$$
\frac{c_j(N-r_j)}{N^2}
\le
\frac{c_j(N-1)}{N^2},
\tag{7}
$$

with equality exactly when all occupied sites have one common answer.  If the
occupied answers form a permutation of $\mathcal C$, the new charge is zero
while the old charge is $1-1/N$.

## (e) Full graph target

The existing proof puts every incompatible live-word collision into
$\mathsf{Join}$.  A CE-oriented simulator should instead maintain all semantic
labels reaching each chaining state.  A state collision is retained when the
induced completed constraints agree.  It becomes
$\mathsf{GraphConflict}$ only when one compression-table point is forced to
carry two unequal ideal answers, or when a previously exposed point carries an
answer inconsistent with a newly completed semantic constraint.

For $a$ construction queries, $p$ direct primitive queries, and maximum
semantic path length $\ell$, the intended counting target is

$$
\Pr[\mathsf{GraphConflict}]
=O\left(\frac{pa\ell+a^2\ell}{N}\right)
\tag{8}
$$

with no primitive-only $p^2/N$ term.  Equation (8) is not established by the
local transport lemmas.  Its proof requires a suffix-compatible structure
graph showing that benign state mergers may be propagated without loss and
that each pair of completed semantic paths creates only $O(\ell)$, rather
than $O(\ell^2)$, inconsistent terminal constraints.  Until that counting
lemma is closed, (8) is a target and not a theorem.

## (f) Technique and rejected routes

Technique: symmetric common-part games followed, where desired, by the strict
CR18 conditional-equivalence endpoint.  The creative obligations are the
balanced local kernel and the suffix-compatible graph-conflict count.

Rejected terminology: changing representatives is not a conditional-
equivalence operation.  An equivalent-PDS presentation may be chosen in a
separate Maurer--Lanzenberger step, but no such step occurs in Lemmas 1--3.

Rejected proof route: coupling is unnecessary for the local theorem.  The
matrix $Q$ is the ideal simulator's transition law, not a joint distribution
with marginals $P$ and another law.

## (g) Obligation DAG

```text
balanced CE bound
|- balanced_transport_nonnegative              [ROUTINE]
|- balanced_transport_two_uniform_marginals    [CREATIVE, CLOSED]
|- balanced_transport_exact_distance           [CREATIVE, CLOSED]
|- balanced_transport_optimal                   [CREATIVE, CLOSED]
|- common_part_games_are_monotone               [ROUTINE]
|- sequential_common_mass_induction             [CREATIVE]
|  `- two_temporal_orders                       [CREATIVE]
`- graph_conflict_bound                         [CREATIVE, OPEN]
   |- benign_join_propagation                   [CREATIVE, OPEN]
   |- suffix_compatible_descriptor_count        [CREATIVE, OPEN]
   `- adaptive_deferred_sampling                [CREATIVE, EXISTING SHAPE]
```

## (h) Adaptation table

| Existing event or term | Verdict | Reason |
| --- | --- | --- |
| Occupied-link charge $c(N-1)/N^2$ | **Shrinks exactly** | Balanced transport gives $c(N-r)/N^2$ and is locally optimal. |
| Primitive-only graph collisions | **Killed in the target** | With no construction query, both public primitive interfaces can be exactly the same random function. |
| Any incompatible live-word join | **Too broad** | A merger is harmless until it forces inconsistent completed answers. |
| Completed unequal-answer constraint | **Remains** | One function-table point cannot return two different values. |
| Previously exposed inconsistent terminal | **Remains** | Causality prevents retroactive reprogramming. |
| Two-query same-tag collision loss | **Remains exactly** | For $c=r=1$, (4) is $(N-1)/N^2$. |

## (i) Proof status

- Balanced transport, uniform marginals, exact distance, and local optimality:
  **CLOSED pen-and-paper**.
- Honest local common-part conditions: **CLOSED pen-and-paper**.
- Sequential composition through the two temporal orders: **DERIVED; requires
  a full history induction in the main paper**.
- Explicit $O((pa\ell+a^2\ell)/N)$ graph-conflict theorem: **OPEN**.
- Lean formalization of the balanced simulator and its games: **OPEN**.
