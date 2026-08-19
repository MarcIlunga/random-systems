# Conditional Equivalence for HCTR2

## Abstract

Let `H` be HCTR2 built from a uniform permutation on `n`-bit blocks, and let
`T` be an ideal variable-input-length tweakable permutation. This note proves
a direct information-theoretic bound between `H` and `T` by conditional
equivalence. Both systems are realized on a common random tape and monitored
for collisions among the primitive inputs and outputs inferred from the HCTR2
equations. Before the first collision, the two monitored systems are game
equivalent.

The monitored ideal system is balanced so that its probability of surviving
each query depends only on the input prefix. Its good-response kernel defines
an ordinary causal system `J`, and the balanced game is strictly conditionally
equivalent to `J`. Blocking its responses gives an input-only game that wins
at query `i` with conditional probability `rho_i(x^i)`. The absorption theorem
of CR18 replaces every adaptive winner by a winner of this blind game. Its
fixed-query winning probability gives the bound

```text
Adv_(q,sigma)(H,T)
 <= min(
      1,
      (3*sigma^2 + 2*q*sigma + 7*sigma + 2)
      / (2*(N-sigma*(sigma+1)*(sigma+2)))
    )
```

whenever `sigma*(sigma+1)*(sigma+2)<N`. The proof compares HCTR2 directly
with the ideal tweakable permutation and does not pass through a random
function.

## 1. Setting

Let

```text
B = {0,1}^n,
N = |B| = 2^n.
```

The primitive is a uniform permutation `pi` of `B`. HCTR2 accepts forward and
inverse construction queries

```text
enc(T,P)    and    dec(T,C).
```

The queries may be interleaved adaptively. Exact repeats and inverse queries
return the partner fixed by the first query. The environment has no interface
to the primitive. Every data string has length at least `n` bits.

For query `s`, define

```text
ell_s = length of the data string in bits,
m_s   = ceil(ell_s/n),
d_s   = m_s + ceil(|T_s|/n).
```

The number `d_s` bounds the degree of the POLYVAL expression used in query
`s`. The environment makes at most `q` construction queries and satisfies the
pathwise work bound

```text
sum_s d_s <= sigma.
```

In particular, `sum_s m_s<=sigma`.

### 1.1. HCTR2 equations

Write the data strings as

```text
P = M || P_R,
C = U || C_R,
```

where `M,U` are `n`-bit blocks. Define the two setup values

```text
h = pi(bin(0)),
L = pi(bin(1)).
```

For a completed record of query `s`, put

```text
MM_s = M_s xor H_h(T_s,P_(R,s)),
UU_s = U_s xor H_h(T_s,C_(R,s)),
S_s  = MM_s xor UU_s xor L,
S_(s,j) = S_s xor bin(j),                 1 <= j < m_s,
Y_(s,1) || ... || Y_(s,m_s-1)
    = (P_(R,s) xor C_(R,s)) || D_s.
```

Here `D_s` is the unused suffix of the last XCTR output block. The primitive
relations used by the proof are

```text
pi(MM_s)    = UU_s,
pi(S_(s,j)) = Y_(s,j),                    1 <= j < m_s.
```

### 1.2. Hash assumptions

For distinct encoded inputs `Z,Z'`, uniform `h` in `B`, and every `a` in `B`,
assume

```text
Pr[H_h(Z) = a]                    <= deg(Z)/N,
Pr[H_h(Z) xor H_h(Z') = a]       <= max(deg(Z),deg(Z'))/N,
Pr[h xor H_h(Z) = a]             <= deg(Z)/N.
```

These are the standard POLYVAL root bounds. Each equation is a nonzero
polynomial in `h`, so the number of solutions is at most its degree. Equal
encoded inputs yield either a replay or an inconsistent freshness equation
and require no additional charge.

The fibre count below also contains XOR sums of at most four POLYVAL
expressions. After cancellation of `L`, each such expression is a polynomial
in `h` of degree at most the largest participating `d_s`. On every nonempty
good fibre it is either nonzero, and hence covered by the same root bound, or
the collision equation is identically false.

### 1.3. Completed responses

For a response of length `ell_s`, append the `n*m_s-ell_s` unused bits of its
last raw block. The resulting completed response is the visible response
together with `D_s`. For fixed `h`, the map

```text
(m_s raw blocks) <-> (visible response,D_s)
```

is a bijection. Uniform raw blocks therefore induce a uniform completed
response.

For later reference, write

```text
(a)_r = a(a-1)...(a-r+1)
```

for the falling factorial.

## 2. Real and Ideal Systems

Let `H` denote HCTR2 evaluated with one uniform permutation `pi` of `B`.

Let `T` denote the ideal variable-input-length tweakable permutation. For each
tweak-length class `(T,ell)`, it samples an independent uniform permutation of
`{0,1}^ell`; forward and inverse queries use the two directions of that same
permutation.

For an environment `D`, let `Adv_D(H,T)` be its statistical distinguishing
advantage. Define

```text
Adv_(q,sigma)(H,T)
```

as the supremum over all adaptive environments satisfying the query and work
bounds of Section 1.

### 2.1. Completed systems

Define augmented systems `H+` and `T+`. On a fresh query, `H+` returns the
ordinary HCTR2 response together with the unused suffix `D_s` of the last
primitive output block. On a fresh query, `T+` returns its ordinary
class-permutation response together with an independent uniform string of the
same length as `D_s`. Repeated and inverse queries return the completed pair
fixed previously.

Erasing the suffix gives the original systems:

```text
erase_D(H+) = H,
erase_D(T+) = T.
```

It follows by data processing that

```text
Adv_(q,sigma)(H,T) <= Adv_(q,sigma)(H+,T+).        (2.1)
```

### 2.2. Common random-tape realizations

Fix a finite query horizon and sample independent coordinates

```text
h*, l*              uniform in B,
W_(s,j)             uniform in B for every query position and raw cell,
R_(G,s)              uniform ranking of B for every correction step,
R_(F,s)              uniform ranking of the relevant response space
                     for every correction step.
```

For a fresh query, the raw cells are interpreted as

```text
encryption:  W_(s,0) = UU_s,
decryption:  W_(s,0) = MM_s,
both:        W_(s,j) = Y_(s,j),       1 <= j < m_s.
```

The unused portion of the final cell is `D_s`.

The rankings implement sampling without replacement. A primitive lookup in
the real system first returns an established table partner when one exists.
At a fresh site, it accepts the raw proposal if the corresponding range value
is unused and otherwise uses `R_(G,s)` to select the first unused value. Set
`h=h*`; if `h*!=l*`, set `L=l*`, and otherwise use the setup ranking to select
the first value different from `h*`. Thus `(h,L)` is uniform over the ordered
distinct pairs, and the lazy primitive table is a uniform permutation.

In the ideal system, an established construction input first returns its
recorded partner. At a fresh input, the raw cells determine a completed
candidate response. If its visible part is occupied in the relevant
tweak-length class, `R_(F,s)` selects the first unused class response. For
fixed `h*`, the map from the raw cells to `(response,D_s)` is bijective, and
the rejection decision depends only on the visible response. The accepted
response is uniform among the unused class values, while `D_s` remains
independent and uniform.

Call these two systems `G` and `F`. Their visible laws are respectively
`H+` and `T+`.

## 3. Proof Object

### 3.1. Collision MBO

For each fresh query `s`, infer the primitive pairs

```text
(MM_s,UU_s),
(S_(s,j),Y_(s,j)),                    1 <= j < m_s,
```

and include the setup pairs

```text
(bin(0),h*),
(bin(1),l*).
```

These sites are computed from the raw completed candidate and from `h*,l*`
before either ranking correction is applied.

Through query `i`, form the domain and range lists

```text
D_i = [bin(0), bin(1),
       MM_s, S_(s,1),...,S_(s,m_s-1) for fresh s <= i],

R_i = [h*, l*,
       UU_s, Y_(s,1),...,Y_(s,m_s-1) for fresh s <= i].
```

Let `C_i=1` if `h*=l*` or if either list contains a repeated entry, and let
`C_i=0` otherwise. Replays add no new inferred sites. The predicate is
monotone: `C_i=1` implies `C_j=1` for every `j>=i`.

Attach this MBO to `G` and `F`, obtaining the monitored systems

```text
G0 = (G,C),
F0 = (F,C).
```

### 3.2. Game equivalence

Suppose `C_i=0`. Every proposed primitive domain and range value is fresh, so
the real system accepts all raw cells without correction. The HCTR2 equations
then make its completed response equal to the raw ideal response. That ideal
response is also unused in its tweak-length class: equality with a preceding
class response, after cancellation in the completed HCTR2 equations, would
give a repeated inferred primitive domain or range. The ideal system therefore
accepts its raw response without correction as well.

The two response prefixes agree pointwise on every random tape for which the
MBO remains zero. Hence

```text
G0 ==g F0,                                            (3.1)
```

where `==g` denotes equality of the pre-winning behavior.

### 3.3. Good-response kernel

Fix an augmented visible history `z^(i-1)` of nonzero pre-winning mass and a
next input `x_i`. Define the local good subkernel of `F0` by

```text
K_i(z_i | z^(i-1),x^i)
  = Pr_F0[Z_i=z_i and C_i=0
          | Z^(i-1)=z^(i-1), C_(i-1)=0, X^i=x^i]
```

and its total mass by

```text
a_i(z^(i-1),x^i)
  = sum_z_i K_i(z_i | z^(i-1),x^i).
```

Thus `a_i` is the conditional probability that the collision MBO remains zero
on query `i`. When `a_i>0`, set

```text
J_i(z_i | z^(i-1),x^i)
  = K_i(z_i | z^(i-1),x^i)/a_i(z^(i-1),x^i).
```

On histories of zero pre-winning mass, choose any probability kernel. The
kernels `J_i` define an ordinary causal system `J`.

### 3.4. Balanced monitored systems

Section 6 proves an input-prefix lower bound

```text
lambda_i(x^i) <= a_i(z^(i-1),x^i).                 (3.2)
```

Put `rho_i(x^i)=1-lambda_i(x^i)`.

After `F0` survives query `i`, retain the execution with probability

```text
lambda_i(x^i)/a_i(z^(i-1),x^i).
```

A rejection sets the balanced MBO to one. Let `A_i` equal one precisely when
either a raw collision or a balancing rejection has occurred through query
`i`. The resulting monitored ideal system is denoted by `Fhat=(F,A)`.

Apply the same transition, with a coin of the same law, to `G0`. Equation
(3.1) gives identical pre-winning kernels on both sides, so the resulting
real system `Ghat=(G,A)` satisfies

```text
Ghat ==g Fhat.                                      (3.3)
```

Removing the MBO recovers the completed systems:

```text
Ghat^- = G in H+,
Fhat^- = F in T+.
```

### 3.5. The blind game

Let `b` be the blocking converter of CR18, Definition 4.20. The game `bFhat`
forwards every construction query to `Fhat` and blocks the completed response
`Z_i`. Its winning event is still `A_i=1`. A winner connected to `bFhat` sees
no response values, so after fixing its private randomness it submits a fixed
query list.

For this proof, `bFhat` has the following equivalent input-only description.
Define `HBlind` by the transition

```text
state:  an input prefix x^(i-1) and a monotone bit A_(i-1),
input:  x_i,

if A_(i-1)=1:
    A_i = 1;
if A_(i-1)=0:
    sample E_i with Pr[E_i=1] = rho_i(x^i),
    A_i = E_i;

response: none.
```

The coins may be sampled independently conditional on the input prefixes.
For every fixed input list, `bFhat` and `HBlind` induce the same law of the MBO
bits. In particular,

```text
Pr_HBlind[A_t=0 | X^t=x^t]
  = product_(i=1)^t lambda_i(x^i),                 (3.4)

Win_HBlind(x^t)
  = 1-product_(i=1)^t lambda_i(x^i).               (3.5)
```

The equality of the two MBO laws is proved in Section 6.5.

## 4. Main Result

For an input prefix through query `i`, put

```text
M_i = 2 + sum_(s<=i) m_s.
```

Define the cumulative first-collision count

```text
P_i = 2*choose(M_i,2) - 1
      + 2*sum_(s<=i)(d_s-1)
      + sum_(r<s<=i) [
          max(d_r,d_s)-1 + (m_r-1)(d_s-1)
        ].
```

Set

```text
beta_1 = P_1,
beta_i = P_i-P_(i-1),                    i > 1.
```

Then `sum_(i<=q) beta_i=P_q`.

The hidden-fibre count is

```text
Phi_i = 1
        + sum_(s<=i) [(m_s+2)d_s + 5m_s - 4]
        + sum_(r<s<=i) [
            2*max(d_r,d_s)
            + (m_r-1) + (m_s-1)
            + (m_r-1)(m_s-1)max(d_r,d_s)
            + (m_s-1)d_r
            + (m_r-1)d_s
          ],

Phi_0 = 0.
```

For every query position, define

```text
rho_i = min(1, beta_i/(N-Phi_(i-1)))    if Phi_(i-1)<N,
rho_i = 1                               if Phi_(i-1)>=N,
lambda_i = 1-rho_i.                                (4.1)
```

For a fixed input list `x^t`, `t<=q`, set

```text
epsilon_profile(x^t)
  = 1-product_(i=1)^t lambda_i.                    (4.2)
```

Let `Q_(q,sigma)` be the set of fixed input lists of length at most `q` for
which `sum_s d_s<=sigma`, and define

```text
epsilon_CE(q,sigma)
  = sup_(x^t in Q_(q,sigma)) epsilon_profile(x^t). (4.3)
```

The inventories may count every position as fresh. Replays introduce no new
primitive sites, so this convention can only increase `P_i` and `Phi_i`.

### Theorem 4.1 (conditional-equivalence bound)

Under the setting and hash assumptions of Section 1,

```text
Adv_(q,sigma)(H,T) <= epsilon_CE(q,sigma).          (4.4)
```

For every fixed input list with `Phi_t<N`,

```text
epsilon_profile(x^t)
  <= min(1, P_t/(N-Phi_t)).                         (4.5)
```

### Corollary 4.2 (query bound)

The two inventories satisfy

```text
P_t <= (3*sigma^2 + 2*q*sigma + 7*sigma + 2)/2,
Phi_t <= sigma*(sigma+1)*(sigma+2).
```

Consequently, if

```text
sigma*(sigma+1)*(sigma+2) < N,
```

then

```text
Adv_(q,sigma)(H,T)
 <= min(
      1,
      (3*sigma^2 + 2*q*sigma + 7*sigma + 2)
      / (2*(N-sigma*(sigma+1)*(sigma+2)))
    ).                                               (4.6)
```

For all remaining parameters, `Adv_(q,sigma)(H,T)<=1`.

## 5. Matching Test

### 5.1. One-block fixed point

For the empty tweak and plaintext `0^n`, the concrete POLYVAL encoding gives
a nonzero field constant `c!=1` such that

```text
C = pi(c*h) xor c*h,
h = pi(0).
```

It follows that

```text
Pr_H[C=0] = 2/N,
Pr_T[C=0] = 1/N.
```

The exact one-query distinguishing advantage is therefore `1/N`.

### 5.2. Repeated XCTR blocks

Make one known-plaintext query whose tail contains `r>=2` complete XCTR
output blocks. Under HCTR2 these blocks are permutation outputs at distinct
inputs and are pairwise distinct. Under the ideal system they are independent
uniform blocks. The deterministic event that two tail blocks are equal has
gap

```text
1 - (N)_r/N^r
  = choose(r,2)/N + O(r^3/N^2).
```

Thus deterministic transcript tests attain both the `1/N` term and the
quadratic work scale in the numerator of (4.6). No corresponding test is
known for the cubic term in the denominator.

## 6. Proof

### 6.1. Marginals and game equivalence

In `G`, each fresh primitive image is uniform in the unused range and each
fresh inverse image is uniform in the unused domain. The pair `(h,L)` is
uniform among ordered distinct pairs. The lazy table is consequently a
uniform permutation, so the visible law of `G` is `H+`.

In `F`, fix `h*`. The raw-cell tuple for a fresh query is uniform in
`B^(m_s)`, and the bijection of Section 1.3 makes the raw response and `D_s`
independent and uniform. If `k` responses are occupied in the relevant
tweak-length class, rejection through a uniform ranking replaces the candidate
by a uniform member of the `2^ell_s-k` unused responses. Since the rejection
decision is independent of `D_s`, the suffix remains uniform. The visible law
of `F` is therefore `T+`.

On `C_i=0`, every proposed primitive domain and range is new. No real
correction occurs, and the HCTR2 equations identify the real completed
response with the raw ideal completed response. A repeated ideal class
response would force a repeated inferred primitive domain or range, so no
ideal correction occurs either. This proves (3.1). Adding the same balancing
transition to both pre-winning kernels proves (3.3).

### 6.2. The hidden good fibre

Fix an augmented input-output prefix through query `i` with nonzero good mass
under `F0`. Once every completion `D_s` is fixed, each pair `(h,L)` determines
a unique tuple of raw cells realizing the prefix without an ideal correction.
All such tuples have the same random-tape probability. Conditional on the
fixed prefix and `C_i=0`, `(h,L)` is therefore uniform over the collision-free
pairs.

After substitution of the completed transcript, every collision equation has
one of the following forms:

1. A false deterministic equation.
2. An equation containing `L` once, which excludes at most one `L` for each
   `h` and hence at most `N` pairs.
3. An equation in which `L` cancels, leaving a nonzero polynomial in `h` of
   degree at most `e`; it excludes at most `eN` pairs.

In the following tables, `b` ranges over `{0,1}` and rows containing two query
indices use `r<s`. The domain collision families and their exclusion weights
are:

| Domain collision | Multiplicity | Weight |
| --- | ---: | ---: |
| `bin(0)=bin(1)` | `1` | `0` |
| `bin(b)=MM_s` | `2` | `d_s` |
| `bin(b)=S_(s,j)` | `2(m_s-1)` | `1` |
| `MM_r=MM_s` | `1` | `max(d_r,d_s)` |
| `MM_r=S_(s,j)` | `m_s-1` | `1` |
| `S_(r,k)=MM_s` | `m_r-1` | `1` |
| `S_(r,k)=S_(s,j)` | `(m_r-1)(m_s-1)` | `max(d_r,d_s)` |
| `MM_s=S_(s,j)` | `m_s-1` | `1` |
| `S_(s,k)=S_(s,j)`, `k<j` | `choose(m_s-1,2)` | `0` |

The range collision families are:

| Range collision | Multiplicity | Weight |
| --- | ---: | ---: |
| `h=L` | `1` | `1` |
| `h=UU_s` | `1` | `d_s` |
| `h=Y_(s,j)` | `m_s-1` | `1` |
| `L=UU_s` | `1` | `1` |
| `L=Y_(s,j)` | `m_s-1` | `1` |
| `UU_r=UU_s` | `1` | `max(d_r,d_s)` |
| `UU_r=Y_(s,j)` | `m_s-1` | `d_r` |
| `Y_(r,k)=UU_s` | `m_r-1` | `d_s` |
| `Y_(r,k)=Y_(s,j)` | `(m_r-1)(m_s-1)` | `0` |
| `UU_s=Y_(s,j)` | `m_s-1` | `d_s` |
| `Y_(s,k)=Y_(s,j)`, `k<j` | `choose(m_s-1,2)` | `0` |

For example, `L` cancels from `S_(r,k)=S_(s,j)`, leaving a polynomial in
`h` of degree at most `max(d_r,d_s)`. In `MM_r=S_(s,j)`, `L` occurs once and
is fixed by `h` and the completed transcript. A collision between two fixed
`Y` blocks is a deterministic false equation on a nonempty good fibre.

Summing the weights gives `Phi_i`. The number of good hidden pairs is therefore

```text
#GoodFibre_i >= N^2-Phi_i*N
                 = N*(N-Phi_i).                    (6.1)
```

A coarser estimate follows directly. Each inferred list has at most

```text
M_i = 2+sum_(s<=i)m_s
```

entries. There are at most `2*choose(M_i,2)=M_i(M_i-1)` same-side pairs, and
each excludes at most `dmax_i*N` hidden pairs, where

```text
dmax_i = max_(s<=i)d_s.
```

Since `M_i<=sigma+2` and `dmax_i<=sigma`,

```text
Phi_i <= M_i(M_i-1)dmax_i
      <= sigma*(sigma+1)*(sigma+2).                (6.2)
```

### 6.3. The first collision on a query

Fix a completed visible history through query `i-1` and extend its unique
no-correction reconstruction from the good fibre to every pair `(h,L)` in
`B^2`. Give these `N^2` pairs equal weight and sample the current raw cells
independently and uniformly. On the previous-good fibre this counting measure
is exactly the conditional random-tape measure of `F0`. A hash collision is
bounded by counting roots in `h`; a response collision is bounded by the
unique value of one current raw cell that realizes it.

Orient every pair in the two tables of Section 6.2 so that query `s` is the
new query. The five families whose charge can exceed `1/N`, together with the
two impossible domain families, are listed below. Every other feasible pair,
including `h=L`, has probability at most `1/N`.

| Current collision | Later encryption | Later decryption |
| --- | ---: | ---: |
| `bin(b)=MM_s` | `d_s/N` | `1/N` |
| `MM_r=MM_s` | `max(d_r,d_s)/N` | `1/N` |
| `h=UU_s` | `1/N` | `d_s/N` |
| `UU_r=UU_s` | `1/N` | `max(d_r,d_s)/N` |
| `Y_(r,k)=UU_s` | `1/N` | `d_s/N` |
| `h=L` or any remaining feasible family | at most `1/N` | at most `1/N` |
| `bin(0)=bin(1)` or `S_(s,k)=S_(s,j)` | `0` | `0` |

Every `1/N` entry fixes either `L` or one current raw cell, and the fixed cell
does not occur in its target. This also covers a partial final block because
the completed cell, including `D_s`, is sampled uniformly.

Charge `1/N` initially to every unordered pair in each inferred list. The
constant-domain pair `bin(0)=bin(1)` is impossible and removes one unit. For
query `s`, replacing the baseline charges by the polynomial bounds adds at
most

```text
2(d_s-1).
```

For a pair of queries `r<s`, it adds at most

```text
max(d_r,d_s)-1 + (m_r-1)(d_s-1).
```

Keeping the baseline charge for the impossible within-query counter pairs
preserves an upper bound. The cumulative weight through query `i` is `P_i`.
The collision families introduced by query `i` therefore have total
probability at most

```text
beta_i/N.                                           (6.3)
```

For `i=1`, this count includes the setup collision `h*=l*`.

Using `sum_s m_s<=sigma`, `sum_s d_s<=sigma`, and at most `q` queries gives

```text
P_t
 <= 2*choose(sigma+2,2)-1
    + 2*sigma
    + (q-1)*sigma
    + choose(sigma,2)

 = (3*sigma^2 + 2*q*sigma + 7*sigma + 2)/2.        (6.4)
```

### 6.4. Local survival

Consider a visible good history through query `i-1`. By (6.1), its hidden
good fibre contains at least

```text
N*(N-Phi_(i-1))
```

pairs. Under the unrestricted hidden fibre, the numerator of the event that
query `i` creates the first collision is bounded by (6.3). Restriction to the
previous good fibre can only reduce this numerator. Dividing by the lower
bound on the good fibre yields

```text
1-a_i(z^(i-1),x^i)
 <= beta_i/(N-Phi_(i-1))                           (6.5)
```

whenever `Phi_(i-1)<N`. Together with the definition (4.1), this gives

```text
a_i(z^(i-1),x^i) >= lambda_i(x^i).                 (6.6)
```

The right-hand side depends only on the input prefix.

### 6.5. Conditional equivalence

The balancing calculation is an identity for causal games. Let `K_i(y|z,x^i)`
be a local good subkernel, let

```text
a_i(z,x^i) = sum_y K_i(y|z,x^i),
```

and suppose `0<=lambda_i(x^i)<=a_i(z,x^i)`. Retaining a good transition with
probability `lambda_i/a_i` gives the balanced good subkernel

```text
K_i(y|z,x^i) * lambda_i/a_i
  = lambda_i(x^i) * J_i(y|z,x^i),                  (6.7)
```

where `J_i=K_i/a_i`. Multiplication over the first `i` queries gives

```text
Pr_Fhat[Z^i=z^i,A_i=0 | X^i=x^i]
  = Lambda_i(x^i) * Pr_J[Z^i=z^i | X^i=x^i],      (6.8)

Lambda_i(x^i) = product_(s<=i) lambda_s(x^s).
```

Summing (6.8) over all response prefixes shows that `Lambda_i(x^i)` is the
survival probability of `Fhat` for the fixed input prefix. Hence the response
law of `Fhat`, conditional on survival, is the response law of `J`:

```text
Fhat |== J.                                         (6.9)
```

Equation (6.8) is also valid when a survival probability is zero, since both
sides then vanish.

The same calculation identifies the blocked game. At any internal history
with `A_(i-1)=0`, a new win occurs either through the raw collision, with
probability `1-a_i`, or through rejection of a surviving transition, with
probability `a_i-lambda_i`. Hence

```text
Pr_Fhat[A_i=1 | A_(i-1)=0,z^(i-1),x^i]
  = (1-a_i) + (a_i-lambda_i)
  = 1-lambda_i
  = rho_i(x^i).                                    (6.10)
```

This probability is independent of the hidden response history. After the
responses are blocked, (6.10) is exactly the transition law of `HBlind`.
Thus `bFhat` and `HBlind` have the same MBO law on every fixed input list,
which proves (3.4) and (3.5).

### 6.6. Blind winning

Apply the CR18 absorption construction to (6.9). Given an adaptive winner
`W`, the absorbed winner runs `J` internally and supplies its responses to
`W`; it sends only the resulting queries to the live copy of `Fhat`. The live
game supplies no responses to the absorbed winner. Thus its query list is
fixed once the internal random tape of `J` and `W` has been fixed. Conditional
equivalence gives the exact identity

```text
Win_Fhat(W)
  = Win_bFhat(absorb(W,J)).                         (6.11)
```

Fix the private randomness of `W` and `J`. The absorbed winner then submits a
fixed list `x^t` to `bFhat`. By the equality with `HBlind`,

```text
Win_bFhat(x^t)
  = Win_HBlind(x^t)
  = 1-Lambda_t(x^t)
  = 1-product_(i=1)^t lambda_i
  = epsilon_profile(x^t).                          (6.12)
```

Averaging over the internal random tape and then taking the supremum over all
lists in `Q_(q,sigma)` gives

```text
Win_Fhat(W) <= epsilon_CE(q,sigma).                 (6.13)
```

If `Phi_t<N`, use `1-product_i(1-u_i)<=sum_i u_i`, monotonicity of `Phi_i`,
and `sum_i beta_i=P_t` to obtain

```text
epsilon_profile(x^t)
 <= sum_i beta_i/(N-Phi_(i-1))
 <= P_t/(N-Phi_t).                                 (6.14)
```

Equations (6.2), (6.4), and (6.14) prove Corollary 4.2.

### 6.7. Distinguishing bound

Let `D` be an environment for `H` and `T`, and let its lifted version ignore
the completion strings returned by `H+` and `T+`. The two views have exactly
the same acceptance probabilities as in the original experiment. The
fundamental monitored-system inequality, applied in both orientations, gives

```text
Adv_D(H,T) <= Win_Ghat(D).                          (6.15)
```

Game equivalence (3.3) implies

```text
Win_Ghat(D) = Win_Fhat(D).                          (6.16)
```

Finally, (6.13) bounds the latter probability by
`epsilon_CE(q,sigma)`. Taking the supremum over all compatible environments
proves Theorem 4.1.

## 7. Previous Results

CR18 develops the monitored-system method used here: game equivalence gives
the fundamental distinguishing inequality, strict conditional equivalence
permits absorption into an ordinary system, and absorption turns adaptive
winning into blind winning. Its switching and CBC-MAC analyses provide the
corresponding proof pattern for permutation systems and iterated block-cipher
constructions.

The published HCTR2 analysis allows adaptive forward and inverse construction
queries, with no public primitive interface and the same work parameters as
above. It first compares HCTR2 with a fresh random-response system and obtains

```text
B(q,sigma)
  = (3*sigma^2 + 2*q*sigma + 7*sigma + 2)/(2N).
```

A PRP-RND transition then gives the ideal variable-input-length tweakable
permutation, adding at most `q^2/(2N)`. The first-collision inventory in
Section 6.3 is the direct counterpart of the collision count in that proof.

The common-part argument in
[HCTR2_CE_RAW_TAPE.md](HCTR2_CE_RAW_TAPE.md) also compares HCTR2 directly with
the ideal tweakable permutation. It proves the bound `B(q,sigma)` by equality
of the two pre-winning sublaws. The present proof instead establishes strict
conditional equivalence to the causal system `J`, and obtains the profile
bound (4.2) and its uniform consequence (4.6).

Sources:

- [CR18 lecture notes](../CR18_LN.pdf), Sections 4.10-4.11 and 6.2.3.
- [Length-preserving encryption with HCTR2](../2021-1441.pdf), Figures 2-5
  and Sections 3.4-3.5.

## 8. Proof Status

**DERIVED.** Theorem 4.1 and Corollary 4.2 follow from the common-tape game
equivalence, the hidden-fibre and first-collision counts, the balancing
identity, the explicit blind game `HBlind`, and CR18 absorption.

**OPEN.** The balanced MBO, the causal system `J`, the equality with `HBlind`,
and the fibre inventory `Phi_i` have not yet been formalized in Lean.
