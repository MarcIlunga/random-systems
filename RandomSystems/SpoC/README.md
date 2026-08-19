# SpoC-128 full-AEAD attack

This directory formalizes the block-aligned part of SpoC-128 and a
three-query key-recovery distinguisher. The main checked endpoint proves a
perfect separation between real SpoC and a full privacy-and-authenticity AEAD
ideal system.

## Files

- [`DDC.lean`](DDC.lean) defines the mode, its direct oracle and interactive
  DDC, encryption/decryption correctness, and their coherence.
- [`Distinguishing.lean`](Distinguishing.lean) defines the attack, the real and
  replay-only ideal, and the original exact advantage proof.
- [`FullAEAD.lean`](FullAEAD.lean) instantiates the generic
  [`AEAD.RealIdealGame`](../AEAD/RealIdeal.lean), proves both worlds are total
  on one public domain, certifies the attack's query bounds, and proves exact
  full-AEAD advantage one.
- [`NIST.lean`](NIST.lean) instantiates sLiSCP-light-256 and checks NIST
  Round-2 known-answer vector Count 529.

## SpoC model

[`Block`](DDC.lean#L16-L27) is 128 bits and `State` is 256 bits. The state is
`capacity || rate`, initialized as `key || nonce`. The full associated-data,
plaintext, and tag controls are respectively `0x20`, `0x40`, and `0x80` in
the [mode definition](DDC.lean#L29-L113). Associated data and
plaintext/ciphertext are lists of complete 128-bit blocks.

The model proves [encryption/decryption correctness](DDC.lean#L149-L177) and
proves that the direct oracle is exactly the [interactive DDC applied to the
permutation evaluator](DDC.lean#L687-L746). The concrete NIST permutation is
anchored by [known-answer vector Count 529](NIST.lean#L143-L169) from the
[official Round-2 SpoC specification](https://csrc.nist.gov/CSRC/media/Projects/lightweight-cryptography/documents/round-2/spec-doc-rnd2/spoc-spec-round2.pdf).

This is only the block-aligned path. Partial final blocks, `10*` padding, and
chopped ciphertext are not yet modeled.

## Attack interaction

The adaptive [environment](Distinguishing.lean#L52-L58) makes these queries:

```text
q0 = Encrypt(nonce = 0,          AD = [], plaintext = [])
q1 = Encrypt(nonce = tagControl, AD = [], plaintext = [0])

recovered = capacity(inversePermutation(q0.tag || q1.ciphertext[0]))

q2 = Decrypt(nonce = 0, AD = [],
             ciphertext and tag freshly computed under recovered)
```

For `q0`, the tag is the capacity half of
`permutation(key || tagControl)`. For `q1`, the first ciphertext block is the
rate half of that same permutation output. Joining the halves and applying
the inverse permutation therefore yields `key || tagControl`. Taking its
capacity half recovers the key. Lean proves this identity for every key and
every permutation in [`recovered_key`](Distinguishing.lean#L31-L50).

In the real system, `q2` verifies because the recovered key is the actual key
and `spoc_correct` applies. In the full ideal system, `q2` is not a replay: it
differs from `q0` in ciphertext length and from `q1` in nonce, so the ideal
rejects it for every sampled tape.

## Full-AEAD game

The generic game samples a finite random tape once. Within the declared query
and message capacities, ideal encryption returns a uniformly random ciphertext
of the plaintext's block length and a uniform tag; it does not use nonce,
associated data, or plaintext contents. Ideal decryption returns the stored
plaintext only for an exact prior encryption tuple and rejects every fresh
tuple.

The generic module separately proves equal-length encryption queries induce
the same uniform-tape response law and every legal exact replay returns its
recorded plaintext.

Both real and ideal PDS laws are defined on every nonempty query history. The
bounds belong to the adversary: Lean proves that, on every possible response
path, this environment makes at most three total queries, at most two of them
encryption queries, uses distinct encryption nonces, and encrypts at most one
block per query. The ideal tape has matching finite capacity; its totalizing
default row/tag after the query bound and its length truncation beyond the
message bound are therefore unreachable by this adversary.

## What is proved

The environment returns the final decryption `verified` bit.
[`full_aead_break`](FullAEAD.lean) packages its adversary-side admissibility,
three-query bound, and distinguisher-normalization certificates with
[`full_aead_advantage_one`](FullAEAD.lean), which proves:

```text
Pr[verified in the real system]  = 1
Pr[verified in the ideal system] = 0
distinguishing advantage         = 1
```

This result is not an artifact of an RS-library quirk:

- the key is sampled uniformly once and retained for the interaction;
- the ideal random tape is sampled uniformly once and retained;
- both worlds are normalized and total on exactly the nonempty histories;
- the query and nonce restrictions are proved about every adaptive response
  path of the environment, not imposed as PDS filters;
- the point distinguisher is itself a normalized distribution;
- the proof computes the complete three-query transcript in both worlds;
- success and failure are proved pointwise for every key, tape, and
  permutation; and
- DDC coherence connects the convenient direct oracle to the interactive
  converter/permutation composition.

The checked files contain no `sorry` or `admit` placeholders.

## Security scope

This is a full-AEAD real/ideal distinction, not merely a theorem about the
repository's authenticity-only [`AEAD.win`](../AEAD/Game.lean). The concrete
attack distinguishes through a fresh accepted ciphertext, so its winning path
is an authenticity failure. That is sufficient to break the combined ideal,
whose encryption side also enforces privacy. No separate IND-CPA theorem is
claimed.

The older [`attack_distinguishing_advantage`](Distinguishing.lean) remains as
a smaller replay-only result in which encryption is real in both worlds.

The present environment also uses the public permutation and its inverse as
host computations; it does not yet count those calls. Padding and explicit
operational cost accounting are separate completeness improvements.
