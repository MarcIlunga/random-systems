# SpoC-128 distinguishing attack

This directory formalizes the block-aligned part of SpoC-128 and a
three-query key-recovery distinguisher. The checked endpoint proves a perfect
separation between real SpoC and a replay-only ideal system. It is a genuine
semantic break, but it is not yet a theorem stated against a standard full
AEAD game.

## Files

- [`DDC.lean`](DDC.lean) defines the mode, its direct oracle and interactive
  DDC, encryption/decryption correctness, and their coherence.
- [`Distinguishing.lean`](Distinguishing.lean) defines the attack, the real and
  ideal systems, and the exact advantage proof.
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
and `spoc_correct` applies. In the [ideal system](Distinguishing.lean#L61-L93),
`q2` is not a replay: it differs from `q0` in ciphertext length and from `q1`
in nonce, so the ideal rejects it.

## What is proved

The environment returns the final decryption `verified` bit. The main theorem,
[`attack_distinguishing_advantage`](Distinguishing.lean#L108-L325), proves:

```text
Pr[verified in the real system]  = 1
Pr[verified in the ideal system] = 0
distinguishing advantage         = 1
```

This result is not an artifact of an empty or impossible RS interaction:

- the key is sampled uniformly once and retained for the interaction;
- both representatives answer every nonempty history;
- the proof computes the complete three-query transcript in both worlds;
- success and failure are proved pointwise for every key and permutation; and
- DDC coherence connects the convenient direct oracle to the interactive
  converter/permutation composition.

The checked files contain no `sorry` or `admit` placeholders.

## Security scope

The current ideal keeps real encryption and changes only decryption. Thus the
present theorem isolates the authenticity failure: it proves a perfect
distinction from this replay-only ideal, but it is not yet connected to a
standard full AEAD game. The repository's current [`AEAD.win`](../AEAD/Game.lean#L50-L72)
is itself a forgery predicate, not a combined privacy-and-authenticity game.

The intended next endpoint is a full AEAD real-vs-ideal experiment: real SpoC
versus an ideal authenticated-encryption system that hides plaintexts and
accepts only legitimate replays. The same key-recovery attack should
distinguish those worlds with advantage `1`.

The present environment also uses the public permutation and its inverse as
host computations; it does not yet count those calls. Padding and explicit
operational cost accounting are separate completeness improvements.
