# Signed virtual representatives for random systems

Status: source-checked research note plus compiled exact linear layer.  Signed
`L1` contraction, operational soundness, the signed-class infimum, and its
unconditional equality with advantage on the finite/common-domain/bounded
source class are formalized in `RandomSystems/VirtualPDS.lean`.  The proof
composes the honest attainment theorem from `BoundedAttainment.lean`, whose
signed-`Real` migration is complete.  The fixed-visible XOR instantiation is
formalized in `SoP/XORVirtualRepresentative.lean`.

Date: 2026-08-03.

Notation and presentation:
[FOUNDATIONS.md](../FOUNDATIONS.md). This note predates that document; where
symbols differ, FOUNDATIONS.md is authoritative.

## 1. Answer in one paragraph

Lanzenberger does require nonnegative coefficients, but only because a PDS is
defined to be an honest distribution over deterministic systems. This does not
make negative representatives mathematically unsound. There is a canonical
larger space of signed, or virtual, PDSs: finite real linear combinations of
deterministic systems, identified when all transcript pushforwards agree. In
the finite common-domain setting, the infimum of half the `L1` distance over
signed equivalent representatives is still exactly the optimal distinguishing
advantage. Negative representatives therefore cannot push a valid bound below
the true distance. Their practical purpose is more important: they enlarge the
space of tractable certificates, expose cancellations before any triangle
inequality, and may lower the **best bound we currently know how to prove** all
the way toward the true optimum. What fails is only the direct probabilistic
interpretation: a signed joint is not an ordinary coupling, its disagreement
mass need not be a probability, and normalized conditioning is not always
defined.

## 2. What the thesis actually permits

The source boundary is explicit.

- Thesis Definition 2.1, printed page 11, defines a distribution as a
  finite-support map into the nonnegative reals.
- The next paragraph permits distributions of arbitrary weight. Here
  "arbitrary" means any nonnegative total mass, not arbitrary real
  coefficients.
- Definition 2.14, printed page 15, defines a PDS as such a distribution over
  DDSs with a common domain.
- Definition 2.17, printed page 16, defines equivalence by equality of every
  compatible transcript distribution.
- Lemma 2.8, printed page 13, states the coupling lemma only for probability
  distributions.
- Theorems 2.31 and 2.32, printed page 20, first produce honest attaining PDS
  representatives and then obtain an operational coupling from the positive
  coupling lemma.

These claims were checked directly in
[Lanzenberger's thesis](<../papers/thesis (1).pdf>) and agree with the full
paper [Coupling of Random Systems](../papers/LanMau20.pdf), especially its
Definitions 1, 8, and 10 and Theorems 1 and 2.

So the accurate statement is:

```text
negative mass is not an honest Lanzenberger PDS;
the thesis does not rule out signed PDSs as virtual proof objects.
```

## 3. The thesis example already linearizes

Example 2.16 uses the four deterministic one-query bit systems

```text
zero, one, identity, flip
```

and, for `0 <= alpha <= 1/2`, the representative

```text
V_alpha =
    alpha       * zero
  + alpha       * one
  + (1/2-alpha) * identity
  + (1/2-alpha) * flip.
```

The interval restriction is exactly what keeps every coefficient nonnegative.
The observable transcript equations themselves hold for every real `alpha`.
For example,

```text
V_1 = zero + one - 1/2 * identity - 1/2 * flip
```

still outputs a uniform bit for either possible query. Thus:

```text
honest equivalent representatives: a line segment
signed equivalent representatives: the entire affine line
```

This is the extra cancellation freedom relevant to the gain-graph expansion.

## 4. The signed extension

For a finite set `A`, the current source already defines

```text
Dist(A) = VirtualDist(A) = {finite functions A -> Real}.
```

No positivity condition is imposed. Its basic operations are linear:

```text
weight(mu)            = sum_a mu(a)
push(f,mu)(b)         = sum_{a : f(a)=b} mu(a)
restrict(mu,E)(a)     = mu(a) if a in E, else 0
tensor(mu,nu)(a,b)    = mu(a) * nu(b)
```

For DDSs with one fixed domain, a virtual PDS is a `VirtualDist` over those
DDSs. Every deterministic environment induces a linear transcript map

```text
Tr_e : VirtualPDS -> VirtualDist(Transcripts).
```

Define virtual equivalence by

```text
sigma ==virt tau

iff

Tr_e(sigma) = Tr_e(tau) for every compatible deterministic environment e.
```

Equivalently, virtual random systems form the quotient vector space

```text
VirtualPDS / intersection_e kernel(Tr_e).
```

The honest PDSs sit inside this space as the positive cone. Honest random
systems are positive elements of total weight one.

## 5. Exact signed representative theorem

Let `S` and `T` be normalized finite random systems with a common domain.
Define

```text
d_signed(S,T) =
  inf over virtual sigma ==virt S and virtual tau ==virt T of
    1/2 * sum_d |sigma(d)-tau(d)|.
```

Then

```text
d_signed(S,T) = Adv(S,T).
```

This is not a conjecture. It follows in two short directions.

### 5.1 Signed representatives cannot understate advantage

Fix virtual representatives `sigma` and `tau` and an environment `e`.
Transcript generation is a deterministic pushforward. Grouping coefficients
inside each pushforward fiber and applying the triangle inequality gives

```text
1/2 * ||Tr_e(sigma)-Tr_e(tau)||_1
  <= 1/2 * ||sigma-tau||_1.
```

Because `sigma` and `tau` are virtually equivalent to the honest normalized
systems, the two transcript pushforwards on the left are honest probability
distributions. Their half-`L1` distance is their total-variation distance.
Taking the best transcript event and then the best environment gives

```text
Adv(S,T) <= 1/2 * ||sigma-tau||_1.
```

This holds for every signed candidate, hence

```text
Adv(S,T) <= d_signed(S,T).
```

### 5.2 Honest representatives already attain advantage

Lanzenberger's Theorem 2.31 produces honest nonnegative representatives
`S0 == S` and `T0 == T` such that

```text
1/2 * ||S0-T0||_1 = delta(S0,T0) = Adv(S,T).
```

Honest representatives are special signed representatives, so

```text
d_signed(S,T) <= Adv(S,T).
```

The two inequalities prove equality. In particular, allowing negative weights
does not change the unknowable-in-advance optimum, and the signed infimum is
still attained by an honest pair. It can nevertheless improve a concrete
state-of-the-art theorem. Existing proofs optimize only over representatives
and estimates that we have managed to construct; they generally apply local
triangle inequalities long before reaching the mathematical infimum. A signed
description can retain cancellations until identical transcript atoms have
been combined, producing a smaller certified upper bound than every currently
known positive construction. Thus the distinction is:

```text
exact optimum over all representatives       unchanged: Adv(S,T)
best upper bound presently known to humans   can decrease, perhaps sharply
```

Proof simplicity is one mechanism for this improvement, not the final goal.

## 6. What survives and what does not

```text
construction or claim                         signed extension

finite transcript pushforward                 exact and linear
observational equivalence                     exact
deterministic converter application           extends linearly
independent parallel composition              extends bilinearly
unnormalized successor/restriction             exact and linear
half-L1 contraction under pushforward          valid
optimal representative distance = advantage   valid as proved above
event evaluation                               real-valued, not a probability
normalized conditioning                       fails in general
bad-event firing probability                   no operational meaning
ordinary coupling/disagreement probability     fails
Jordan positive and negative parts             valid after coefficients combine
```

### 6.1 Why conditioning fails

Consider the signed table

```text
          y=0   y=1
x=0        1    -1
x=1        0     1
```

The `x=0` marginal is zero even though its row is nonzero. No normalized
conditional can reconstruct that row, because

```text
zero marginal * any conditional = zero row.
```

Positivity normally guarantees that a zero total mass is made only of zero
entries. Signed cancellation destroys that zerosumfree property. Virtual
proofs should therefore use unnormalized successor branches and normalize only
branches already known to be positive with strictly positive weight.

### 6.2 Why an ordinary coupling fails

Let both marginals be the uniform bit and consider the signed joint table

```text
gamma_t =
  [ 1/2+t   -t    ]
  [  -t     1/2+t ]
```

Every row and column still sums to `1/2`, but the signed mass on the two
disagreement cells is `-2t`. It can be negative and arbitrarily large in
magnitude. It is therefore not a probability of disagreement and cannot be
used in the ordinary coupling lemma.

Use the vocabulary:

```text
positive joint distribution: coupling
signed joint distribution:   virtual joint or quasi-coupling
```

The cost of a virtual joint must be a norm or another sound functional, not
the signed mass of an event.

## 7. The maximum-general formulation

The clean conceptual object is an ordered quotient vector space.

```text
ambient vector space: finite signed PDSs
null subspace:        intersection of all transcript kernels
random-system space: quotient by the null subspace
positive cone:        images of honest nonnegative PDSs
normalized base:      positive elements of weight one
operational norm:     quotient base norm
```

For a virtual difference `z`, the quotient base norm can be written as the
least `L1` norm among all representative lifts of `z`. The theorem in Section
5 says that, in Lanzenberger's finite common-domain setting,

```text
Adv(S,T) = 1/2 * quotient_base_norm(S-T).
```

This is the linear completion of the coupling method:

- the positive cone retains the systems that can be sampled;
- the full vector space permits cancellations in proofs;
- positive maps are the physical converters;
- arbitrary linear maps are algebraic proof transformations;
- the base norm is the operational boundary that prevents negative
  representations from cheating.

With parallel side information, physical transformations should be required
to remain positive after tensoring with identities, the classical analogue of
complete positivity.

## 8. Consequence for the gain-graph proof

The gain-graph inclusion-exclusion expansion can be treated as a genuine
virtual representative or virtual certificate. There is no need to split it
into Jordan parts before proving an upper bound. The sound route is

```text
honest SoP and URF
  -> choose virtually equivalent signed representatives
  -> expand them into red and blue gain-graph cards
  -> combine all coefficients of identical cards
  -> cancel opposite cards
  -> bound half the L1 mass of what survives
  -> conclude an operational advantage bound by pushforward contraction.
```

If the surviving half-`L1` mass is `B`, this constructs the theorem

```text
Adv(SoP,URF) <= B.
```

The equality of the signed infimum with advantage says that this search is in
principle capable of reaching the optimal bound. It does not say that the first
gain-graph representative will do so. The research task is to choose a virtual
representative and a cancellation normal form whose computable `B` is smaller
than the DNS, Dinur, DHT, and current collision-proxy bounds.

The first such certificate is now complete.  It combines Fourier row levels
two and three pointwise, classifies the sign of their sum in the sparse range,
and takes `L1` only afterward.  With `N=2^n`, `10<=n`, `2q<=N`, and
`2*choose(q,2)<=N`, Lean proves

```text
|Adv - A23|
  <= 1/2 * sqrt((1152/7)*q^4/N^6 + 8*q^4/N^8),

A23 = (N)_q/N^q *
  (choose(q,2)/(N-1)^2
    - 8*choose(q,3)/((N-1)^2*(N-2)^2)).
```

This improves the closed collision-proxy certificate because the triangle
layer cancels before the norm and is absent from the residual energy.  It does
so provably: Lean proves that the displayed new bound is no larger than the
old `min(sparse,dense) + remainder` certificate throughout this range, and
strictly smaller for every `q >= 3`.  The dense comparison follows from the
finite rational estimate `(N)_q/N^q <= N/(N+choose(q,2))`.  This does not
formalize the general signed PDS category, and it does not yet settle the dense
normal-constant problem beyond the range `2*choose(q,2) <= N`.

If an actual probabilistic coupling is desired afterward, invoke
Lanzenberger's attainment theorem to obtain an honest optimal representative
pair and then apply the ordinary coupling lemma.

The non-negotiable accounting rule is:

```text
combine all signed coefficients belonging to the same atom first;
only then take absolute values or positive/negative parts.
```

Taking a triangle inequality term by term would erase the cancellation freedom
that motivated the signed representative.

## 9. Related theory

The extension agrees with several independent lines of work.

- Fritz, Gonda, Houghton-Larsen, Lorenzin, Perrone, and Stein explicitly define
  `FinStoch+/-`, whose matrices have real entries and columns summing to one,
  without nonnegativity. It is a Markov category, so composition, tensoring,
  copying, and discarding remain coherent. They also show why it is not a
  positive Markov category and has no general conditionals; Proposition 2.12
  connects this failure to non-zerosumfree coefficients:
  <https://arxiv.org/abs/2211.02507>.
- Misshula proves that finite signed measures are the universal additive
  extension of finite positive measures. This supports the linear-envelope
  construction directly; the paper leaves the corresponding general
  signed-kernel universal property open:
  <https://arxiv.org/abs/2606.30273>.
- Abramsky and Brandenburger interpret signed hidden-variable measures through
  ordinary probabilities on positively and negatively marked events followed
  by cancellation. This is a simulation of signed mass, not an assertion that
  negative mass is itself a probability:
  <https://arxiv.org/abs/1401.2561>.
- Dzhafarov, Cervantes, and Kujala study real-valued quasi-couplings using total
  variation as the meaningful cost:
  <https://arxiv.org/abs/1703.01252>.
- Ordered-vector-space and generalized-probabilistic-theory language supplies
  the abstract positive cone, normalized base, effects, and base norm. A useful
  overview is Plavala:
  <https://arxiv.org/abs/2103.07469>.

## 10. Formalization route

The carrier and the linear core are now implemented.

1. `Dist A = A →₀ Real` is the virtual distribution carrier.
2. `Dist.NonNeg` and `Dist.isProbDist` cut out honest and normalized laws.
3. `PFunPDS` is therefore already the virtual PDS carrier.
4. `VirtualPDS.lean` defines half-`L1`, proves pushforward contraction, and
   proves signed representatives cannot understate `Adv`.
5. It defines the signed representative infimum, proves equality from an
   honest attainment witness, and exports the unconditional
   finite/common-domain/bounded theorem by applying `BoundedAttainment.lean`.
6. `XORVirtualRepresentative.lean` connects the XOR density decomposition to
   this generic cost without pretending the fixed visible truncation is a
   simultaneous all-environment PDS representative.
7. Normalized conditioning, probabilities, and coupling constructors stay in
   the positive layer only.

For exact gain-graph algebra, use integer or rational virtual coefficients as
long as possible, then map into the real envelope only when applying a norm.
