# Signed-PDS targets in symmetric cryptography

Status: pen-and-paper research audit only. No Lean claim in this note.

Date: 2026-08-04.

Notation and presentation:
[FOUNDATIONS.md](../FOUNDATIONS.md). This note uses that document as its
notation authority.

Program context:
[`signed-pds-research-program.md`](signed-pds-research-program.md).

## 1. Scope and the important caveat

This note ranks symmetric-cryptography benchmarks where Lanzenberger-style
representatives, ordinary couplings, or signed virtual representatives could
plausibly give a shorter or tighter information-theoretic proof. It deliberately
separates three kinds of statement:

```text
published       a theorem or attack in the cited source
derived target  a formula obtained by expanding an exact published likelihood
conjectural     a research target, not a theorem
```

A signed representative cannot change the true distinguishing advantage. Its
half-L1 norm still upper-bounds every environment's transcript distance, and the
infimum over signed representatives equals the operational advantage. The gain
is therefore epistemic: negative coefficients let us combine equal transcript
atoms and cancel disconnected structures before taking absolute values. This
can lower the best bound we know how to prove, even though it cannot lower the
unknown exact answer.

Unless stated otherwise, `N = 2^n` is the block-domain size, `q` counts
construction queries, `p` counts direct primitive queries, `ell` is a maximum
message length in blocks, and `sigma` is the total number of queried blocks.
Computational PRP terms are orthogonal: a better information-theoretic
representative does not improve the assumed block cipher.

The literature check concentrated on primary papers and theorem statements,
not just abstracts. “Best published” below means the best reference located in
this audit for the stated game; it should be rerun before claiming a new SOTA
result in print.

## 2. Executive ranking

The ranking measures the chance that this machinery produces a useful theorem,
not the practical importance of the primitive.

| Rank | Benchmark | What can realistically improve | Confidence |
|---:|---|---|---|
| 1 | Truncated random permutation | Sharp constants and one formula in every query regime | Very high |
| 2 | Key-alternating ciphers | Replace a threshold-tuned bound by a pointwise link-count bound | High |
| 3 | Cascaded LRW2 / LRW+ | Remove the square-root mirror term; expose the four-cycle attack | High-medium |
| 4 | Equal-length permutation CBC-MAC | Resolve the open message-length gap, one way or the other | Medium |
| 5 | OMAC/CMAC/XCBC/TMAC | Cancel invisible internal path accidents and reduce length loss | Medium |
| 6 | HCTR2 | Remove switching loss and replace collision unions by one score | High for simplification |
| 7 | FX/DESX | Exact hypergeometric/Poisson interpolation and sharp constant | High for constants |
| 8 | Three-round Luby-Rackoff | Elementary exact occupancy proof; sharp constant | High for simplicity |
| 9 | DbHtS / LightMAC-Plus / PMAC-Plus | Replace mirror counting by zero-gain cycle counting | Medium-high |
| 10 | Keyed sponge | Separate capacity collisions from primitive links sharply | Medium |
| 11 | Triple encryption | Replace path thresholds by a direct complete-path process | Medium |
| 12 | Many-round/generalized Feistel | Connected coalescence diagrams and better round constants | Medium-low |
| 13 | GCM | Cleaner separation of permutation collisions and GHASH roots | Medium for exposition |
| 14 | OCB3 | Sharper offset-profile bounds and a less case-heavy proof | Medium-low |
| 15 | Sponge, MD, or Feistel indifferentiability | Potentially major, but first needs a simulator-minimax extension | Speculative |

The first three are the clearest candidates for a genuinely stronger
pointwise advantage theorem. Items 6--8 and 13--14 are more likely to improve
constants and proof clarity than asymptotic exponents. Items involving an
indifferentiability simulator are outside the currently justified signed-PDS
theory.

## 3. The common proof template

For a fixed deterministic adversary, let `Q` be the ideal transcript law and
write the real likelihood as `L(t) Q(t)`. Then

```text
Adv = (1/2) E_Q |L - 1|.
```

The proposed representatives try to make the following expansion literal:

```text
L - 1
  = sum of connected pair/link/cycle contributions
  + sum of connected higher-order contributions.
```

Disconnected components cancel because they merely reparameterize hidden
randomness. The first surviving connected component gives both a proxy random
variable and the natural matching test. A Poisson or normal approximation to
that proxy supplies the sparse, transition, and dense regimes. The remaining
task is to bound the connected higher-order tail before taking absolute values.

This is not universally available. It is most promising when all of the
following hold:

1. the real transcript count has an exact falling-factorial or graph-solution
   formula;
2. the leading obstruction is one explicit local structure;
3. a known attack tests the count of that same structure;
4. adaptivity changes which vertices appear but not the conditional counting
   identity.

## 4. Rank 1: truncated random permutation

### Game

Choose a uniform permutation on `N = 2^n` points, hide `m` output bits, and
expose the remaining `n-m` bits on each of `q` distinct inputs. Compare this
with a uniform random function to the visible range. Put

```text
H = 2^m          hidden points in each visible bucket
B = N/H          number of visible buckets
M = binom(q,2).
```

### Published result

Gilboa and Gueron prove, for every `q`,

```text
Adv = Theta(min(q(q-1)/N, q/sqrt(NH), 1)).
```

They also give the exact likelihood of a visible transcript with bucket
occupancies `c_z`:

```text
L(c) = B^q * product_z (H)_{c_z} / (N)_q.
```

Source: [The Advantage of Truncated Permutations](https://arxiv.org/abs/1610.02518),
Theorem 1 and equation (10).

### Dominant statistic and matching test

Under the ideal random function, let

```text
K = number of pairs of queries with the same visible output.
```

Then `E K = M/B`. The real truncated permutation has slightly fewer visible
collisions. Thresholding `K` below its ideal mean is already the published
lower-bound mechanism in the middle regime.

### Candidate representative

Sample the visible ideal transcript first. For each bucket, attach hidden slots
using the signed falling-factorial correction `(H)_{c_z}/H^{c_z}`; attach the
global injection correction `N^q/(N)_q`; and expand only after equal occupancy
profiles have been combined. This is a signed occupancy representative, not a
bad-event deletion.

The first connected term is exact:

```text
L - 1 = -(K - M/B)/H + higher occupancy clusters.
```

Hence the pair proxy is

```text
A_pair = E|K - M/B| / (2H).
```

### Derived sharp target

This proxy automatically gives all three nontrivial regimes:

```text
q << sqrt(B):
  Adv ~ M/N.

q = c sqrt(B), lambda = c^2/2:
  Adv ~ lambda * Pr[Poisson(lambda) = floor(lambda)] / H.

sqrt(B) << q << sqrt(NH):
  Adv ~ q / (2 sqrt(pi N H)).
```

The first-order formulas follow from the exact likelihood; what is not yet a
theorem is a uniform L1 bound on the higher occupancy clusters strong enough to
preserve these constants. The matching statistic is already present, so this
is the least speculative target in the list.

### Chief obstruction

One needs a cluster-tail estimate uniform across the Poisson-to-normal
transition and near bucket saturation. A pointwise Taylor bound is too crude;
the proof must average under the multinomial occupancy law before taking L1.

## 5. Rank 2: t-round key-alternating ciphers

### Game

For independent public random permutations `P_1,...,P_t`, define

```text
E_k(x) = k_t xor P_t(k_{t-1} xor ... P_1(k_0 xor x) ...).
```

The adversary gets forward and inverse access to the construction and to every
public permutation. The ideal world has `t+1` independent uniform random
permutations. Let `q_e` count construction queries and `q_i` primitive queries.

### Published result

Chen and Steinberger prove, for `q <= N/3` and any `C > 0`, in the equal
primitive-query case,

```text
Adv <= (q_e q^t/N^t) * C t^2 (6C)^t + (t+1)^2/C.
```

Their proof notes that the product `q_e q^t` generalizes to
`q_e product_i q_i`. Optimizing `C` proves the tight threshold
`q around N^(t/(t+1))`, matching the generalized Daemen attack, but it does not
give a pointwise bound proportional to the sparse complete-link probability.

Source: [Tight Security Bounds for Key-Alternating Ciphers](https://eprint.iacr.org/2013/222.pdf),
Theorem 1 and Corollary 1.

### Dominant statistic and attack

A construction edge is distinguishing only when it can be completed through
all `t` public-permutation tables using one consistent tuple of hidden subkeys.
Partial links are not observable. The generalized attack searches for complete
links, reaching constant advantage at `N^(t/(t+1))` balanced queries.

### Candidate representative

Sample the ideal `t+1` permutation transcripts. Overlay translated public
edges for a candidate key tuple. Use a signed Möbius expansion over the layered
link graph:

```text
isolated vertices and incomplete paths cancel;
only connected paths touching a construction edge and all t layers survive.
```

This is a direct virtual analogue of the paper's exact compatibility count,
but it postpones the `good/bad` threshold and its adjustable `C`.

### Conjectural target and gain

The clean sparse target is

```text
Adv <= C_t * min(1, q_e * product_i q_i / N^t)
       + explicitly lower-order overlap terms,
```

with a reasonable, monotone dependence on `t`. This would retain the known
optimal threshold while being much stronger at small advantage and far more
useful for concrete `t`. It would also explain the attack and proof using the
same complete-link count.

### Chief obstruction

Complete paths overlap through keys and table vertices. The source explicitly
warns that second-order factors remain important beyond the birthday range.
A successful proof needs a dependency-graph or Stein estimate for linked paths,
not merely formal inclusion-exclusion. It also does not automatically cover
AES's repeated round permutation or dependent key schedule.

## 6. Rank 3: cascaded LRW2 and LRW+

### Game

One LRW2 layer maps

```text
(tweak, message) -> P(message xor h(tweak)) xor h(tweak).
```

Cascaded LRW2 composes two independently keyed layers and is compared with a
uniform tweakable random permutation under forward and inverse queries.

### Published result

For an ideal `1/N`-AXU hash family, Jha and Nandi's Corollary 6.1 gives

```text
Adv_info <= 54 q^4/N^3 + 2 q^2/N^(3/2) + 4 q^2/N^2,
```

and the computational theorem adds two SPRP advantages. The bound becomes
constant near `q = N^(3/4)`, the known attack threshold. A later LRW+ paper
notes an omitted transcript subcase in the original analysis and reports that
repairing it changes only a small constant factor, not the order.

Sources:
[Tight Security of Cascaded LRW2](https://eprint.iacr.org/2019/1495.pdf),
Corollary 6.1; and
[Tight Security of TNT and Beyond](https://eprint.iacr.org/2023/1272.pdf),
Remark 6.1.

### Dominant statistic and attack

The transcript becomes a bipartite gain graph. Tree components are freely
solvable. The first real obstruction is an alternating four-cycle whose edge
gains sum to zero. The known attack deliberately creates and tests such a
cycle.

### Candidate representative

Sample the ideal tweakable-permutation transcript and the hash gains, then use
a signed gain-graph representative. Eliminate one vertex per tree component;
tree weights cancel exactly. Expand the injectivity correction only over the
cycle space. The first surviving atom is a zero-gain four-cycle.

### Conjectural target and gain

For the ideal `1/N`-AXU setting, the natural pointwise target is

```text
Adv <= C q^4/N^3 + C' q^2/N^2 + higher connected cycles,
```

removing the published `q^2/N^(3/2)` square-root term. This does not change the
optimal `N^(3/4)` threshold, but it can be quadratically smaller in the sparse
regime and makes the matching cycle attack manifest. It may also replace much
of the restricted mirror-theory solution count by elementary cycle counting.

### Chief obstruction

Hash gains are adversarially shaped through chosen tweaks, and distinctness
constraints couple otherwise separate graph components. The proof must show
that all forests cancel before bounding injective assignments and must include
the transcript subcase flagged by the 2023 paper.

## 7. Rank 4: equal-length CBC-MAC over a random permutation

### Game

For messages of exactly `ell` blocks, iterate one random permutation in CBC
fashion from the fixed initial value and return the last state. Compare the
tags with a random function on messages. Queries may be adaptive.

### Published result and genuine gap

For the random-permutation construction, the standard clean comparison is

```text
lower bound: Omega(q^2/N)
upper bound: O(ell q^2/N).
```

Thus the dependence on message length is unresolved in this game. For the
prefix-free game, structure-graph analyses give `O(sigma q/N)` in their stated
length range; this does not close the equal-length permutation gap.

Sources:
[On the Exact Security of Message Authentication Using Pseudorandom Functions](https://eprint.iacr.org/2017/172.pdf),
Table 1 and its discussion; [Improved Security Analyses for CBC MACs](../papers/cbc-improved.pdf);
and Jha--Nandi's corrected structure-graph analysis,
[doi:10.1515/jmc-2016-0030](https://doi.org/10.1515/jmc-2016-0030).

### Dominant statistic and attack

Every message is a path in the hidden state graph. Existing upper bounds charge
many internal state collisions. The obvious visible attack, however, is a
collision or structured equality among final tags. Internal coalescences that
never connect two queried terminals should cancel from the transcript law.

### Candidate representative

Sample ideal tags first. Represent each message by a rooted hidden path whose
internal labels are quotient variables. Use a signed path-forest expansion and
contract every component not touching two visible terminals. Only
terminal-connected coalescences remain.

### Conjectural target and gain

The ambitious target is

```text
Adv = O(q^2/N)
```

for equal-length messages throughout a natural nonsaturation range, independent
of `ell`. This would close the published gap. The honest outcome of the same
calculation could instead be an explicit surviving `ell`-dependent connected
diagram, which would immediately suggest the missing attack. Either outcome is
valuable; the length-independent bound is not presently guaranteed.

### Chief obstruction

Adaptive messages can share long prefixes and can force merges in the path
graph. The fixed IV and reuse of one permutation make component factorization
delicate. A proof must distinguish genuinely invisible internal collisions from
ones that alter later chosen queries.

## 8. Rank 5: OMAC/CMAC, XCBC, and TMAC

### Game

These are prefix-free CBC-like PRFs with a final-block mask or finalization
key. The most direct target is OMAC/CMAC under a random permutation, with `q`
messages of at most `ell` blocks.

### Published result

The unrestricted OMAC analysis gives

```text
Adv = O(q^2/N + q ell^2/N).
```

The known lower bound cited there is `Omega(q^2/N)`, so the result is tight
when `ell <= sqrt(q)` and leaves a length gap outside that region. The same
paper develops analogous bounds for XCBC and TMAC.

Source: [Towards Tight Security Bounds for OMAC](https://eprint.iacr.org/2022/1234.pdf),
Table 1.1 and the main OMAC theorem.

### Dominant statistic and attack

The useful objects are masked CBC paths. The current proof pays for internal
self-intersections and reset-sampling failures. The visible attack still counts
terminal tag collisions. The final mask is correlated with the same underlying
permutation, which is exactly where naive independence fails.

### Candidate representative

Quotient each path by the final-mask translation and use a signed path
expansion. Cancel a self-intersection unless it joins two visible message paths
or changes a later finalization equation. Treat the derived mask as a marked
root in the same graph, rather than switching it to an independent key.

### Prospective gain

The first objective is not to assert `O(q^2/N)` blindly, but to replace
`q ell^2/N` by the count of terminal-connected path diagrams. Such a term must
vanish for one visible query, unlike the coarse published expression. If all
remaining diagrams require two messages, a length-independent birthday bound
may follow over a much wider range.

### Chief obstruction

The derived final mask and all internal steps use the same permutation.
Self-intersections are nonlocal, and some may be made visible by a later
adaptive message. This is a harder version of the CBC path-cancellation problem.

## 9. Rank 6: HCTR2

### Game

HCTR2 is a variable-input-length tweakable enciphering mode built from one
block cipher, a polynomial hash, and an XCTR stream. The adversary makes
forward and inverse queries under chosen tweaks. Let `q` be the query count and
`sigma` the total number of blocks.

### Published result

The ideal-permutation-to-randomized-system step in the HCTR2 paper is

```text
(3 sigma^2 + 2 q sigma + 7 sigma + 2)/(2N).
```

The final theorem then pays a PRP-to-random-function switching term
`q^2/(2N)` in addition to the block-cipher SPRP term.

Source: [HCTR2: Efficient Wide-Block Encryption for Arbitrary-Length Inputs](../papers/2021-1441.pdf),
Sections 3.4--3.5.

### Dominant statistic and attack

After revealing the hash key and mask, each transcript determines sets of
inferred permutation inputs and outputs. The proof declares bad any collision
in either multiset and separately pays polynomial-hash root events.

### Candidate representative

Sample the ideal tweakable-permutation answers first and assign the inferred
block-cipher sites through one injection representative. Encode input and output
conflicts in a bipartite rook graph. A signed rook polynomial combines
collisions that correspond to the same visible transcript before L1. Keep the
hash-root carrier separate and tensor it only after quotienting identical
equations.

### Prospective gain

A direct Lanzenberger representative can compare against the ideal tweakable
permutation without the external PRP--RND hop, eliminating the standalone
`q^2/(2N)` switching loss. The signed refinement could then replace the union
of input/output collision events by the L1 norm of one centered conflict score,
sharpening constants and making a collision-count attack explicit. The
birthday order in `sigma` is likely real, so no exponent improvement is
promised.

### Chief obstruction

Encryption and decryption expose different inferred-site formulas, and XCTR
creates structured arithmetic relations among sites. Polynomial-root events
must not be incorrectly canceled with injection defects.

## 10. Rank 7: FX/DESX

### Game

For an ideal cipher `E` with `K = 2^kappa` keys and block domain `N`, FX uses
input and output whitening:

```text
FX_{k,a,b}(x) = b xor E_k(x xor a).
```

The adversary sees `q` construction pairs and makes `p` direct ideal-cipher
queries, in both directions.

### Published result and attack

Kilian--Rogaway's classical ideal-cipher analysis gives the clean information
bound, in modern notation,

```text
Adv <= 2 p q/(K N),
```

up to truncation at one. Their effective-key-length statement is
`kappa+n-1-log2(q)`, and generic attacks match the resulting data--time tradeoff
in order.

Sources: [How to Protect DES Against Exhaustive Key Search](https://www.cs.ucdavis.edu/~rogaway/papers/desx-abstract.html)
and the theorem summary in
[Quantum Key-Length Extension](https://eprint.iacr.org/2021/579.pdf), Section 3.

### Dominant statistic and matching test

A direct ideal-cipher edge becomes useful when one pair of global whitening
masks translates it onto one observed construction edge. Thus the natural
statistic is the number of online--offline links. Its sparse mean is
proportional to `pq/(KN)`.

### Candidate representative

Sample the two edge tables independently, then sample the masks. Represent
mask-consistent links by a hypergeometric point process. A signed cluster
expansion cancels isolated edges and retains connected sets sharing a mask or
an ideal-cipher key.

### Prospective gain

The realistic target is an exact finite interpolation, with a Poisson law in
the sparse regime and the correct high-data transition, replacing the factor-2
union bound. This is principally a sharp-constant and high-school-proof target:
the known order `min(1,pq/(KN))` is already matched by attacks.

### Chief obstruction

The same masks correlate every potential link, and primitive queries are split
adaptively across ideal-cipher keys. The dense regime is not a collection of
independent Bernoulli links.

## 11. Rank 8: three-round Luby-Rackoff

### Game

Apply three independent random-function Feistel rounds to two `n`-bit halves
and compare the resulting `2n`-bit permutation with a uniform permutation,
under forward queries.

### Published result

Maurer's random-systems proof gives

```text
Delta_q <= 2 p_coll(N,q) < q^2/N.
```

The proof is already representative-based: it conditions on freshness of the
two hidden middle-coordinate sequences. It improves older treatments that paid
an additional `q^2/N^2` term.

Source: [Indistinguishability of Random Systems](../papers/Maurer02.pdf),
Theorem 7.

### Dominant statistic and attack

The leading obstruction is a repeated hidden middle wire. Classical
distinguishers exploit the corresponding equality relation among external
input/output halves, so birthday order is unavoidable.

### Candidate representative

Instead of deleting whenever either middle sequence repeats, sample the
external random-permutation transcript and decorate it with hidden middle
labels. Use a signed rook polynomial for the two injection constraints. Group
configurations producing the same visible equality pattern before L1.

### Prospective gain

The target is the exact or sharp-asymptotic total variation expressed through
one occupancy statistic, with a Poisson transition near `q=sqrt(N)`. It may
improve the leading constant and make the standard proof almost elementary,
but it cannot improve the `q^2/N` order because matching birthday attacks
exist.

### Chief obstruction

The two middle collision families interact through the Feistel equations; they
are not independent birthday experiments. Chosen-ciphertext security requires
four or more rounds and a more involved two-sided representative.

## 12. Rank 9: double-block hash-then-sum MACs

### Game

DbHtS schemes hash a variable-length message to two `n`-bit values and
finalize by XORing two permutation outputs. Important instances include
PMAC-Plus, LightMAC-Plus, SUM-ECBC, and PolyMAC. The ideal object is a random
function on messages.

### Published result

The refined-mirror analyses establish beyond-birthday security. For example,
2k-LightMAC-Plus has a message-length-independent `3n/4`-bit bound and a
matching `2^(3n/4)`-query attack. Related DbHtS theorems expose error terms of
order `q^4/N^3` together with hash and lower-order permutation terms.

Sources:
[Tight Security Bounds for Double-Block Hash-then-Sum MACs](https://doi.org/10.1007/978-3-030-45721-1_16)
and [Tight Security Bound of 2k-LightMAC Plus](https://eprint.iacr.org/2023/1422).

### Dominant statistic and attack

Conditioned on the two hash profiles, finalization is a constrained sum of two
permutations. The first nontrivial transcript structures are compatible
four-edge or zero-gain cycles. The matching attacks deliberately create those
hash/cycle configurations.

### Candidate representative

First quotient messages by equal hash pairs. Conditional on that quotient,
insert the signed sum-of-permutations representative. Expand only connected
gain cycles and average over the hash key before taking absolute values. This
is precisely where signed representatives can avoid paying separately for two
hash collisions whose transcript contributions cancel.

### Prospective gain

For the `3n/4`-secure instances, the realistic target is a transparent

```text
Adv <= C q^4/N^3 + explicit hash-collision and lower-order terms
```

with sharp constants and no mirror-theory black box. The exponent is already
matched; the main gain is simplicity, constants, and possibly removal of
message-length or multiplicity cutoffs in particular variants.

### Chief obstruction

Practical schemes reuse block-cipher-derived masks, so the two hash coordinates
are not always independent. Adversarial messages control the gain graph, and
the average over the hash key must precede L1 to realize any cancellation.

## 13. Rank 10: keyed sponge

### Game

A keyed sponge absorbs a secret key and a variable-length message into a public
random permutation of width `n=r+c`, exposes `r` rate bits, and hides `c`
capacity bits. The adversary makes `q_C` construction queries of at most `ell`
blocks and `q_pi` direct permutation/inverse queries.

### Published result and attacks

For the random-IV keyed sponge, Gazi--Pietrzak--Tessaro prove a concrete bound
whose leading capacity terms, after suppressing constants and the tunable
higher-order term, have the form

```text
O((n q_C^2 + ell q_C + q_C q_pi)/2^c)
```

plus full-state terms over `2^n`; their displayed theorem assumes
`ell < 2^(n/4)`. They give generic attacks of order `q_C^2/2^c` and
`q_C q_pi/2^c` in the relevant ranges. The theorem for ordinary key absorption
adds explicit key-extraction terms.

Source: [Tight Bounds for Keyed Sponges and Truncated CBC](https://eprint.iacr.org/2015/053.pdf),
Theorems 2--3 and the attacks following Theorem 2.

### Dominant statistic and matching attacks

There are two leading structures:

```text
two construction paths collide in their hidden capacity state;
a direct primitive query links to an internal construction state.
```

Both have known attacks, so a representative should track these counts rather
than every internal permutation collision.

### Candidate representative

Represent each message as a rooted path with visible rate labels and hidden
capacity labels. Mark direct primitive edges. Quotient common prefixes, cancel
unrooted path components, and retain connected components containing either
two construction roots or one construction root and one direct-query mark.

### Prospective gain

A sharp target in the moderate-length regime is

```text
Theta(min(1, (q_C^2 + q_C q_pi)/2^c))
```

plus necessary full-state and key-absorption terms, with Poisson interpolation
and no artificial factor `n`. This agrees with the known attack statistics.
The more ambitious gain is to replace maximum-length restrictions by the
actual rooted-path profile.

### Chief obstruction

Messages share prefixes, squeezing can reveal several rate blocks from one
state path, and the public permutation is queried in both directions. Ordinary
key absorption adds a rare but global event in which the adversary covers the
entire key path.

## 14. Rank 11: three-key and two-key triple encryption

### Game

In the ideal-cipher model,

```text
TE_{k1,k2,k3}(x) = E_{k3}(E_{k2}(E_{k1}(x))).
```

The adversary queries both the outer construction and the keyed ideal cipher,
forward and backward. The two-key variant sets `k3=k1`.

### Published result and attack

Jooyoung Lee closes the query-threshold gap: three-key triple encryption is
secure up to

```text
2^(kappa + min(kappa,n/2))
```

ideal-cipher queries, matching the best generic attack scale. The detailed
finite bound still contains threshold and cube-root terms. For two-key triple
encryption the theorem gives separate construction/primitive tradeoffs and
matches the classical meet-in-the-middle data--time phenomenon.

Source: [Tight Security Bounds for Triple Encryption](https://eprint.iacr.org/2014/015.pdf),
Corollaries 1--2.

### Dominant statistic and attack

Each primitive query is a directed edge in a key-indexed graph. A construction
pair becomes explained by a directed path of length three under one key triple.
The paper's improvement comes from counting such paths more carefully. Generic
attacks search for complete paths or meet-in-the-middle joins.

### Candidate representative

Sample the ideal outer permutation and ideal-cipher edge tables. Use a signed
layered-path representative: open paths and isolated edges cancel; complete
outer-to-outer three-paths and connected overlaps remain. Approximate the count
of complete paths directly rather than declaring high-degree vertices bad.

### Prospective gain

The exponent is already tight. The plausible gain is a pointwise finite bound
in terms of the complete-path intensity, with a Poisson transition and clearer
data--time constants, replacing cube-root threshold optimization. This is also
a historically apt target: the published proof already uses the random-systems
framework and a path graph.

### Chief obstruction

Queries concentrate adaptively on selected ideal-cipher keys, producing
high-degree graph vertices. Three paths can share one or two edges, and the
two-key variant creates additional backtracking dependencies.

## 15. Rank 12: many-round and generalized Feistel

### Game

Use many independent random functions in balanced or type-1/type-2/type-3
generalized Feistel networks, and compare with a uniform permutation under
chosen-plaintext/ciphertext queries.

### Published result

Hoang--Rogaway prove near-full-domain CCA security with enough rounds. For
example, for fixed branch count `k` and repetition parameter `r`, their type-1
and type-2 bounds have the form

```text
Adv <= (2q/(r+1)) * (2k(k-1)q/N)^r,
```

with explicit round counts; type 3 replaces the inner constant by
`4(k-1)^2`. Thus any `N^(1-epsilon)` query exponent is reached with enough
rounds.

Source: [On Generalized Feistel Networks](https://www.cs.ucdavis.edu/~rogaway/papers/feistel.pdf),
Theorem 10.

### Dominant statistic and attack

The coupling follows bundles of internal wires until enough rounds have made
all query trajectories independent. Failure occurs when trajectories
coalesce in a connected history. Known lower bounds make near-`N` behavior the
right asymptotic target when rounds grow.

### Candidate representative

Use a partition-valued coalescent representative: the state records only which
query wires are equal, not their labels. Apply a signed connected-diagram
expansion to histories of partition merges. Components that separate again
without reaching an external constraint cancel.

### Prospective gain

This could unify several Feistel variants and reduce large factors such as
`2k(k-1)` or `4(k-1)^2`. A genuinely better exponent is unlikely where the
published bound is already near optimal. The main prize is one conceptual
proof across round counts, with constants governed by connected coalescences
instead of a stepwise union bound.

### Chief obstruction

The partition state grows superexponentially with `q`, inverse queries reverse
the dependency direction, and round-function evaluations reused by several
trajectories destroy a simple Markov collision process.

## 16. Rank 13: GCM

### Game

Nonce-respecting GCM combines counter-mode calls to one block cipher with the
polynomial hash GHASH. The main games are privacy and authenticity with `q`
encryption queries, `v` verification queries, total input length `sigma`,
maximum authenticated length `ell`, and `t`-bit tags.

### Published reference bound

For 96-bit nonces, the Niwa et al. bounds as restated in a recent GCM paper are

```text
privacy info term:
  0.5 (sigma+q+1)^2/N + 2(sigma+q)/N

authenticity info terms:
  0.5 (sigma+q+v+1)^2/N
  + 2(sigma+q+v)/N
  + v(ell+1)/2^t.
```

A block-cipher PRP advantage is added in both cases.

Source: [Generic Security of GCM-SST](https://eprint.iacr.org/2024/1928.pdf),
Theorems 1--2, restating Niwa et al.'s GCM theorems.

### Dominant statistic and attacks

The first term is the collision profile of counter/permutation sites. The last
authenticity term is a GHASH polynomial-root event. Algebraic forgery attacks
show that the GHASH term cannot simply be canceled away.

### Candidate representative

Sample ideal ciphertexts and tags, then maintain two carriers: an injection
carrier for counter-mode permutation sites and an equation carrier for GHASH.
Use a signed rook expansion within the first and quotient identical field
equations within the second. Combine them only after the transcript fixes which
roots are genuinely distinct.

### Prospective gain

The likely gain is sharper constants and query-profile dependence in the
birthday term, plus a clean explanation of why the GHASH term survives. A
representative proof must retain `v(ell+1)/2^t` up to constants because matching
algebraic attacks exist. This is therefore an elegance and concrete-bound
project, not an exponent breakthrough.

### Chief obstruction

Privacy and authenticity have different visible events, rejected decryption
queries are adaptive, and short tags amplify the algebraic carrier independently
of the permutation carrier.

## 17. Rank 14: OCB3

### Game

OCB3 is nonce-based authenticated encryption using offsets derived from one
random permutation. Its analysis has both privacy and multi-forgery integrity
components.

### Published result

The improved OCB3 analysis gives the ideal-cipher information terms

```text
privacy:   5 sigma_T^2/N + 2 sigma^4/N^2
integrity: (64 q' ell_max + 15 q')/N,
```

in the paper's notation and stated query conditions, plus the block-cipher PRP
term.

Source: [Improved Security for OCB3](https://eprint.iacr.org/2017/845.pdf),
Section 4.1 and the main theorems.

### Dominant statistic and attack

The proof enumerates collisions among block-cipher inputs generated by the
offset schedule. Integrity additionally tracks equations created by forgery
attempts. The offset sequence lies on a deterministic doubling orbit generated
from the random mask `L=P(0)`.

### Candidate representative

Quotient internal sites by the doubling orbit and build an offset-collision
gain graph. A signed cycle expansion can combine cases that are separate in the
published exhaustive analysis but induce the same visible nonce/message/tag
equation.

### Prospective gain

The birthday order for privacy and the linear forgery order are already the
right broad shapes. The plausible gain is smaller constants, dependence on the
actual nonce/message profile instead of worst-case `ell_max`, and a proof that
does not require exhaustive collision case analysis.

### Chief obstruction

All offsets depend on the same `P(0)`, header and message domains use different
offset conventions, and decryption attempts expose only an accept/reject bit.

## 18. Rank 15: simulator-based indifferentiability

Three important benchmarks fit the graph intuition but not the current theorem
surface:

1. classical sponge versus a random oracle;
2. prefix-free Merkle--Damgard versus a random oracle;
3. public-random-function Feistel versus a random permutation.

For the classical sponge, Bertoni--Daemen--Peeters--Van Assche give explicit
simulator bounds. With capacity `c`, the random-transformation expression is

```text
1 - product_{i=1}^Q (1 - i/2^c)
  < Q(Q+1)/2^(c+1),
```

and they give the corresponding finite random-permutation expression.

Source: [On the Indifferentiability of the Sponge Construction](../papers/BDPV08_SpongeIndifferentiability.pdf).

The graph statistic is again a hidden-capacity collision or a simulator
programming conflict. A signed connected expansion may greatly simplify the
accounting. But indifferentiability is

```text
inf over simulators  sup over interactive distinguishers,
```

not the distance between one fixed pair of random systems. A signed object may
have negative mass, so it cannot itself answer the simulator's online oracle
queries. Before using it soundly, one needs a minimax theorem showing that a
virtual simulator certificate can be rounded to an honest causal simulator
without increasing the claimed distance. No such extension has been
established here. These are therefore frontier problems, not immediate
applications.

For reference, Dai--Steinberger's eight-round Feistel construction proves
indifferentiability with an `O(q^8/N)`-type bound over an `n`-bit round-function
domain, while fewer than six rounds are impossible; improving this is
interesting but currently much more speculative than the fixed-pair Feistel
games above. Source:
[Indifferentiability of 8-Round Feistel Networks](https://eprint.iacr.org/2015/1069.pdf).

## 19. Recommended order of attack

The projects should not be started in construction-size order. A disciplined
sequence is:

1. **Truncated permutation.** Prove the signed occupancy identity and a
   Poisson/normal L1 remainder. This validates the reusable analytic engine on
   an exact likelihood with a known matching statistic.
2. **Key-alternating cipher.** Port the engine from occupancy clusters to
   layered complete-link clusters. The goal is a pointwise product bound, not
   merely the already-known threshold.
3. **Cascaded LRW2.** Port it again to gain-graph cycle space and test whether
   the `q^2/N^(3/2)` mirror term disappears.
4. **CBC-MAC and OMAC.** Only after the cancellation lemma is trustworthy,
   use it on hidden paths to resolve the length gap. Here the hoped-for theorem
   may be false, so the calculation must also be designed to emit an attack
   statistic when a connected length-dependent diagram survives.
5. **HCTR2, FX, and three-round LR.** Use these as exposition and
   sharp-constant case studies.
6. **Keyed sponge, triple encryption, DbHtS, and generalized Feistel.** These
   need multitype dependency graphs but no fundamentally new operational
   definition.
7. **Indifferentiability.** Postpone until the simulator-minimax extension is
   proved independently.

## 20. Bottom line

The most credible new sharp theorem is the truncated-permutation
collision-proxy formula. The most consequential pointwise improvement is the
key-alternating complete-link bound. The cleanest opportunity to replace mirror
theory is cascaded LRW2's zero-gain four-cycle. CBC-MAC is the most valuable
open gamble: signed path cancellation could either remove the unexplained
factor `ell` or identify the missing length-dependent attack. FX, Luby-Rackoff,
HCTR2, GCM, and OCB3 are excellent candidates for simpler and sharper proofs,
but their known attacks make major exponent improvements unlikely.
