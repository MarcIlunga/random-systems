# SpoC full-AEAD break — pen-and-paper sketch

## 1. Setting

The construction is the block-aligned SpoC-128 model. Nonces, plaintext and
ciphertext blocks, and tags are 128 bits. Associated data, plaintexts, and
ciphertexts are finite block lists. The public 256-bit permutation and its
inverse are available to the attacker in the current semantic model. Queries
may be adaptive.

Fix an encryption-query bound `q_e` and a maximum encryption plaintext length
`ell`. An admissible environment, on every possible response path:

- contain at most `q_e` encryption queries;
- use distinct nonces across encryption queries; and
- give every encryption plaintext at most `ell` blocks.

These are restrictions on the environment, not on either PDS domain. The real
and ideal systems remain defined on every nonempty query history. Decryption
queries may reuse an encryption nonce: this is necessary for replay and
forgery tests.

## 2. Real and ideal systems

The real system samples one uniform secret key and retains it for the complete
interaction. It answers encryption and decryption queries with SpoC.

The ideal system samples one finite random tape before the interaction. The
tape contains `q_e` rows of `ell` independent uniform ciphertext blocks and
`q_e` independent uniform tags. On the `i`-th encryption of an `n`-block
plaintext, the ideal system returns the first `n` blocks of row `i` and tag
`i`. The answer is independent of nonce, associated data, and plaintext
contents; only plaintext length is leaked.

The ideal representative uses a default row/tag after row `q_e` and truncates
requests beyond length `ell`. These choices give a total mathematical PDS; the
adversary-admissibility proof shows the security experiment never observes
either out-of-capacity behavior.

The ideal system records `(nonce, associated data, ciphertext, tag,
plaintext)`. Decryption of an exact recorded tuple returns the stored
plaintext. Every fresh tuple returns verification failure. Sampling the tape
once makes rewinding a deterministic representative consistent, while the
uniform tape distribution gives a normalized probabilistic system.

## 3. Proof object

The proof object is one explicit deterministic three-query distinguisher. No
coupling, virtual representative, H-technique partition, or conditional
equivalence is used.

The distinguisher makes two encryption queries:

```text
q0 = Encrypt(nonce = 0,          AD = [], plaintext = [])
q1 = Encrypt(nonce = tagControl, AD = [], plaintext = [0])
```

It then computes:

```text
candidateKey = capacity(inversePermutation(q0.tag || q1.ciphertext[0]))
forgery      = Encrypt(candidateKey, nonce = 0, AD = [], plaintext = [0])
q2           = Decrypt(nonce = 0, AD = [], forgery.ciphertext, forgery.tag)
```

Its verdict is the verification bit returned for `q2`.

## 4. Main result

For `q_e = 2` and `ell = 1`, the concrete distinguisher is admissible. For
every permutation it has signed distinguishing advantage exactly one between
the two total systems:

```text
Pr[verdict = true in the real system]  = 1
Pr[verdict = true in the ideal system] = 0
```

Here signed advantage is real acceptance probability minus ideal acceptance
probability.

## 5. Matching test

The deterministic test is the distinguisher's final verification bit. Its gap
is exactly the claimed advantage, so no separate upper-bound argument is
required.

## 6. Proof

In the real system, `q0.tag` is the capacity half of
`permutation(key || tagControl)`. The first ciphertext block returned for
`q1` is the rate half of the same permutation output. Joining those halves and
applying the inverse permutation recovers `key || tagControl`; taking the
capacity half therefore recovers the exact key. Encryption/decryption
correctness makes `q2` verify.

In the ideal system, this reasoning need not hold and `candidateKey` may be
arbitrary. Nevertheless, for every sampled random tape, the ciphertext from
`q0` is empty and the ciphertext submitted in `q2` has one block. Thus `q2`
cannot replay `q0`. It cannot replay `q1` because their nonces are respectively
zero and `tagControl`, which are distinct. The ideal system therefore rejects
`q2` for every tape.

The final probability calculation is pointwise: every real key yields verdict
true and every ideal tape yields verdict false. Normalization of the two
uniform distributions gives masses one and zero.

Technique: exact pointwise transcript/verdict calculation. The existing
forgery predicate is rejected as the main endpoint because it expresses only
authenticity. H-technique and coupling routes are rejected because there is no
approximation, bad event, or disagreement probability to bound.

## 7. Previous result

The existing SpoC theorem uses the same distinguisher against an ideal that
keeps real encryption and changes only decryption. It already checks the key
recovery and fresh-forgery mechanics, but it does not compare SpoC with the
privacy-and-authenticity ideal system defined here.

## 8. Proof status

**CLOSED.** Both laws are normalized and total on all nonempty histories. The
environment-side bounds, pointwise real and ideal transcripts, and exact
advantage-one result are checked in Lean.

## 9. Obligation DAG

`full_aead_break`

- statement: the normalized, three-query-admissible concrete attack has
  real-minus-ideal verdict probability one;
- class: [LIB] assembly after the two pointwise verdict nodes;
- depends: `real_verdict`, `ideal_no_verdict`, `attack_admissible`,
  `systems_total`, `real_normalized`, `ideal_normalized`.

`real_verdict`

- statement: every fixed real key makes the final verification bit true;
- class: [ADAPT];
- depends: `key_recovery`, `scheme_correctness`, `systems_total`.

`ideal_no_verdict`

- statement: every fixed ideal tape makes the final verification bit false;
- class: [CREATIVE];
- depends: `ideal_response_shape`, `ideal_freshness`, `systems_total`.

`attack_admissible`

- statement: on every response path, the environment emits at most three
  queries, including at most two encryption calls with distinct nonces and
  plaintext lengths at most one; on the complete interaction it makes exactly
  two encryption calls;
- class: [ROUTINE];
- depends: `CR18.replay`, `replay_eq_of_stall`.

`systems_total`

- statement: every nonempty query history is in every real and ideal
  representative's domain;
- class: [LIB];
- depends: none.

`ideal_freshness`

- statement: the final decryption tuple differs from the first record in
  ciphertext length and from the second record in nonce;
- class: [ROUTINE];
- depends: `ideal_response_shape`.

`ideal_response_shape`

- statement: ideal encryption preserves plaintext block length;
- class: [CREATIVE];
- depends: `ideal_tape_definition`.

`key_recovery`

- statement: the two real encryption responses recover the exact key;
- class: [LIB];
- depends: none.

`scheme_correctness`

- statement: decrypting a scheme-generated ciphertext returns the plaintext
  with verification success;
- class: [LIB];
- depends: none.

`real_normalized`

- statement: uniform key sampling gives a probability system;
- class: [LIB];
- depends: none.

`ideal_normalized`

- statement: uniform finite-tape sampling gives a probability system;
- class: [LIB];
- depends: `ideal_tape_definition`.

`ideal_tape_definition`

- statement: the finite tape supplies independent uniform blocks and tags for
  every allowed encryption ordinal;
- class: [ROUTINE];
- depends: none.

## 10. Reuse audit

- **REUSE:** `AEAD.Query` and `AEAD.Response`, `CR18.replay` and its stall
  lemma, `Dist.uniform`, probability-preserving pushforward,
  `verdictProb_single`, `Dist.mass_fTransform`, and the existing SpoC real
  system, key-recovery lemma, and correctness theorem.
- **ADAPT:** the existing query-history projections and the current
  three-query transcript proof.
- **NEW:** the environment-side `AdmissibleEnvironment` predicate, finite ideal
  tape, and full privacy-and-authenticity ideal oracle. AEAD-specific
  admissibility lives on the environment/game side, never as a PDS domain
  filter.

The existing `AEAD.game` is not the target: it marks fresh verified
decryptions and therefore expresses authenticity only. The CPA layer is also
not the target because it has no decryption interface. No existing module in
RandomSystems, RandomSystemsCC, or the sibling AbstractCryptography repository
defines the combined real/ideal AEAD system needed here.
