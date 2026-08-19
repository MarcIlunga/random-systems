# One-permutation SoP over general finite groups

Status: pen-and-paper research note.  The exact model, one-row laws, proxy, and
saturation attacks are closed.  The connected multirow remainder is open.  No
Lean claim is made here.

Date: 2026-08-04.

Notation and presentation:
[FOUNDATIONS.md](../FOUNDATIONS.md). This note uses that document as its
notation authority.

Program context:
[`signed-pds-research-program.md`](signed-pds-research-program.md).

## 1. Model audit: three constructions that must not be conflated

### Repository SoP1

The repository partitions the input domain of one uniform permutation into
ordered pairs.  If `G` has order `N` and the paired query domain has size
`N/2`, a fresh query exposes

```text
Y_i = A_i * B_i,
```

where

```text
(A_1,B_1,...,A_q,B_q)
```

is a uniform ordered injection into `G`.

### Published Boolean XOR1

Dai-Hoang-Tessaro and Dutta-Nandi-Saha analyze

```text
pi(x||0) XOR pi(x||1).
```

This agrees with the repository construction when `G` is a Boolean group.

### Finite-abelian difference construction

Bhattacharya-Nandi study a finite-abelian generalization based on

```text
A_i-B_i.
```

Outside exponent-two groups this is not the same law as `A_i+B_i`, and neither
is the same as ordered multiplication in a nonabelian group.

Every theorem below concerns the repository ordered-product construction unless
explicitly stated otherwise.

## 2. Exact adaptive reduction — CLOSED

Let

```text
m = min(q,N/2).
```

After filtering repeated construction queries, domain symmetry makes the real
fresh tape

```text
(A_i*B_i)_(i=1..m)
```

for a uniform ordered injection of all `2m` endpoints.  The ideal fresh tape is
`m` independent uniform elements of `G`.  Therefore

```text
Adv_q
  = TV(
      Law((A_i*B_i)_i | all 2m endpoints distinct),
      U_G^m
    ).
```

This is the exact operational problem.

## 3. Honest paired-card representative — CLOSED

Use one common carrier.

```text
Ideal:
  sample q iid endpoint pairs (A_i,B_i) uniformly from G^2;
  expose only A_i*B_i.

Real:
  use the same carrier conditioned on all 2q endpoints being distinct;
  expose only A_i*B_i.
```

The ideal products are iid uniform.  Conditioning the endpoints on global
distinctness produces the exact real law.  Thus the transcript likelihood is

```text
L(y)
  = Pr[all endpoints distinct | A_i*B_i=y_i]
      / Pr[all endpoints distinct].
```

This is the simplest conceptual representative: independent paired cards
versus the same deal without replacement.

A useful two-stage factorization is

```text
iid endpoint pairs
  -> condition A_i != B_i separately in every row
  -> condition different rows are mutually disjoint.
```

The first arrow retains the complete one-row signal.  Signed inclusion-
exclusion should be applied only to the second arrow, after the static signal
has been removed.

## 4. Exact one-query law — CLOSED

Define the square-root profile

```text
r_G(y) = #{a in G : a*a=y}.
```

Among the `N` ordered pairs `(a,a^(-1)y)` with product `y`, precisely
`r_G(y)` have equal endpoints.  Therefore

```text
Pr_real[Y=y]
  = (N-r_G(y))/(N*(N-1)).
```

The exact one-query advantage is

```text
Adv_1(G)
  = 1/(2*N*(N-1))
      * sum over y in G of |r_G(y)-1|.
```

This proves immediately that no sharp theorem depending only on `N` can hold
for arbitrary groups.

The exact independent-row proxy is `P_1^q`, with likelihood relative to the
uniform tape

```text
L_row(y_1,...,y_q)
  = product_i (N-r_G(y_i))/(N-1).
```

Its exact optimal test accepts on the positive part of `L_row-1`, equivalently
on a threshold of

```text
sum_i log((N-r_G(y_i))/(N-1)).
```

This test is explicit once the square-root profile is known.

## 5. Finite abelian groups — CLOSED proxy

Let `G` be finite abelian and define

```text
t  = |G[2]|,
2G = {2a : a in G}.
```

The doubling map has kernel size `t` and image size `N/t`.  Hence

```text
r_G(y) = t  if y in 2G,
         0  otherwise.
```

Let

```text
K = #{i : Y_i in 2G}.
```

Under the ideal law,

```text
K ~ Bin(q,1/t).
```

Under the independent-row real proxy,

```text
K ~ Bin(q,(N-t)/(t*(N-1))).
```

Therefore the exact proxy advantage is

```text
BinomialProxy(N,t,q)
  = TV(
      Bin(q,(N-t)/(t*(N-1))),
      Bin(q,1/t)
    ).
```

The likelihood-threshold test on `K` attains this proxy distance.

For fixed `t` and `q=o(N)`, the small-bias normal prediction is

```text
BinomialProxy(N,t,q)
  ~ sqrt((t-1)*q)/(sqrt(2*pi)*N),
```

provided the binomial variance is large enough for the normal regime.  Sparse
and fixed-rate cases should instead retain the exact binomial expression.

## 6. Boolean groups and the DNS boundary

For a Boolean group,

```text
t=N,
2G={0}.
```

The one-row real proxy never outputs zero, while an ideal row is zero with
probability `1/N`.  Thus

```text
BinomialProxy(N,N,q)
  = 1-(1-1/N)^q.
```

This is the zero-output test used in the Boolean XOR1 literature.  DNS proves
that it gives the exact advantage in its stated range.  Consequently:

- no new method can numerically improve the exact Boolean result there;
- a representative proof may still simplify the derivation;
- extending the equality to a larger range would require proving that all
  cross-row residual mass has the appropriate one-sided sign.

The general-group project must not describe its group-dependent binomial proxy
as a stronger Boolean XOR1 bound.

## 7. Exact depletion identity — CLOSED

Suppose a set `S` of `s` endpoints has already been used.  Define

```text
D_S(y) = #{a in S : a^(-1)*y in S},
f_S(y) = #{a in S : a*a=y}.
```

The number of fresh ordered distinct pairs with product `y` is exactly

```text
c_S(y)
  = N-r_G(y)-2s+D_S(y)+f_S(y).
```

Writing `h=N-s`, its deviation from the uniform average is

```text
c_S(y)-h*(h-1)/N
  = 1-r_G(y)
      + D_S(y)+f_S(y)-s*(s+1)/N.
```

Interpretation:

```text
1-r_G(y):
  static one-row square-root signal;

D_S(y)+f_S(y)-s*(s+1)/N:
  centered interaction caused by depletion across rows.
```

Taking a statewise absolute value of the second line would destroy the desired
global cancellation.  The interaction must be grouped into connected diagrams
over the whole transcript first.

## 8. Abelian matching-graph language

For an abelian group, the map

```text
a |-> y-a
```

is an involution.

- If `y` is not in `2G`, it is a perfect matching on `G`.
- If `y` is in `2G`, it has `t` fixed points and `(N-t)/2` two-cycles.

This gives an elementary graph representation of each output fiber.  A row
selects an oriented edge from the corresponding matching-with-fixed-points;
the real game asks that all selected endpoints be disjoint.

The signed expansion should:

1. retain the fixed-point count, equivalently the `2G` statistic, exactly;
2. center every cross-row endpoint collision;
3. cancel disconnected collision components;
4. bound only connected components spanning multiple rows.

This is the most constrained path to a new theorem.

## 9. Nonabelian cycle language

For a nonabelian group, the fiber map

```text
a |-> a^(-1)*y
```

need not be an involution.  It is a directed permutation whose cycle structure
depends on `y` and the group multiplication table.  Connected diagrams then
encode solutions to group word equations.

A useful nonabelian theorem will require group-dependent parameters, for
example:

- the full square-root profile `r_G`;
- the abelianization size `|G_ab|`;
- centralizer or conjugacy-class data;
- a word-map mixing parameter;
- possibly a quasirandomness/minimal-irrep parameter.

An `N`-only nonabelian remainder is unlikely to remain sharp beyond the first
universal collision terms.

## 10. Candidate comparison theorem — OPEN

The correct theorem shape is

```text
|Adv_q^product(G)
    - TV(P_1^q,U_G^q)|
  <= R_G(q,N),
```

where `R_G` is the total half-`L1` mass of connected endpoint-collision
diagrams spanning at least two rows.

For finite abelian groups:

```text
|Adv_q^sum(G)
    - BinomialProxy(N,t,q)|
  <= R_ab(N,t,q).
```

A conservative first research target is

```text
R_ab(N,t,q)
  = O(q/N^(3/2)+q^2/N^2)
```

on a clearly stated sparse range.  This order has not been proved and may not
be optimal.

A stronger representative should retain both:

1. the row statistic `K=#{i:Y_i in 2G}`;
2. the exact level-two output-collision/convolution statistic.

If every remaining connected component then spans at least three rows, a
cubic tail may be possible.  This is CONJECTURAL until the diagrams are
enumerated.

## 11. Dense regime and saturation — CLOSED lower bounds

The construction has at most `N/2` distinct paired queries.

### Finite abelian groups

At `q=N/2`, every group element appears once among all endpoints, so

```text
sum_i Y_i = sum over g in G of g
```

deterministically.  The ideal checksum is uniform.  Therefore

```text
Adv_(N/2) >= 1-1/N.
```

The real law need not be uniform inside the checksum fiber, so equality is not
automatic.

### Nonabelian groups

The full ordered product is not generally deterministic in `G`, but its image
in `G_ab` is.  Hence

```text
Adv_(N/2) >= 1-1/|G_ab|.
```

For perfect groups this invariant is trivial.  A sharp dense theorem must then
analyze nonabelian word products or representation-theoretic structure.

The sparse independent-row proxy cannot be extrapolated blindly through this
global invariant.  Dense analysis should use a complementary representative
based on the few unused endpoints.

## 12. Literature comparison

### Boolean XOR1

Dai-Hoang-Tessaro prove, in their stated range, a bound of the form

```text
q/N + 3*q^(3/2)/N^(3/2).
```

Dutta-Nandi-Saha prove the stronger exact zero-output expression

```text
1-(1-1/N)^q
```

in their stated Boolean range.

### Finite abelian groups

Bhattacharya-Nandi analyze a difference primitive.  Their theorem cannot be
used as an order-only theorem for the repository sum/product model outside
exponent-two groups.

Primary references:

- [Dai-Hoang-Tessaro](https://eprint.iacr.org/2017/537).
- [Dutta-Nandi-Saha](https://eprint.iacr.org/2020/669).
- [Bhattacharya-Nandi](https://eprint.iacr.org/2019/249.pdf).

## 13. Proof tasks

```text
GG1-1  Enumerate all two-row connected endpoint diagrams over finite abelian G.
GG1-2  Express their total contribution through t=|G[2]| and output collisions.
GG1-3  Define the level-two augmented proxy and prove it is normalized.
GG1-4  Prove a signed cancellation lemma for disconnected matching components.
GG1-5  Bound the at-least-three-row remainder with exact constants.
GG1-6  Transfer the K-threshold attack to the true construction.
GG1-7  Build a complementary unused-endpoint representative near q=N/2.
GG1-8  Determine which nonabelian parameters are sufficient for a family theorem.
```

## 14. Recommended first theorem

Start with finite abelian `G` and freeze `t=|G[2]|`.

The first theorem should retain the exact binomial `2G` statistic and every
two-row connected collision contribution.  It should then prove a finite bound
on the remaining at-least-three-row diagrams over a conservative query range.

This target has the best combination of:

- a high-school-level paired-card representative;
- a genuinely group-dependent new law;
- an explicit likelihood-threshold attack;
- elementary matching-graph fibers;
- a sharply isolated analytic obstruction.
