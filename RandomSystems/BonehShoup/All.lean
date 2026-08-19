/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Prelude
import RandomSystems.BonehShoup.Ch2Encryption
import RandomSystems.BonehShoup.Ch3StreamCiphers
import RandomSystems.BonehShoup.Ch4BlockCiphers
import RandomSystems.BonehShoup.Ch5CPA
import RandomSystems.BonehShoup.Ch6MAC
import RandomSystems.BonehShoup.Ch7UHF
import RandomSystems.BonehShoup.Ch8Hash
import RandomSystems.BonehShoup.Ch9AE
import RandomSystems.BonehShoup.Converters

/-!
# Boneh–Shoup Part I as random systems

Aggregator for the symmetric-cryptography library: every construction of
Part I of Boneh and Shoup, *A Graduate Course in Applied Cryptography*
(v0.6, Jan 2023; `papers/BonehShoup.pdf`), declared as the random system it
names.

**Definitions only.**  No security notion, no attack game, no advantage bound
and no theorem about any of these objects appears in this tree.  What is
proved is exactly what the book itself verifies in passing — that a cipher
decrypts to what it encrypted — because those laws are part of the *syntax* of
a cipher, not of its security.  There are no `sorry`s.

## Contents

| Module | Book | Constructions |
| --- | --- | --- |
| `Prelude` | — | keyed systems, the coin resource, strings, `chunk` |
| `Ch2Encryption` | §2.1–2.2 | Shannon cipher, one-time pad, variable length OTP, substitution cipher |
| `Ch3StreamCiphers` | §3.1–3.4 | PRG, stream cipher, parallel and Blum–Micali sequential composition |
| `Ch4BlockCiphers` | §4.1–4.7 | block cipher, PRF, ECB, 2E/3E/Triple-DES, PRG-from-PRF, deterministic counter mode, Luby–Rackoff, GGM tree, ideal cipher, Even–Mansour, `EX` |
| `Ch5CPA` | §5.4–5.5 | generic hybrid, randomized and nonce-based counter mode, CBC, `CBC-ESSIV` |
| `Ch6MAC` | §6.1–6.11 | MAC-from-PRF, CBC and cascade PRFs, encrypted PRF, ECBC, NMAC, prefix-free encodings, CMAC, ANSI CBC-MAC, PMAC₀ |
| `Ch7UHF` | §7.1–7.6 | polynomial UHF, XOR-hash, PRF(UHF), Carter–Wegman, nonce-based MACs, one-time MACs from PUFs |
| `Ch8Hash` | §8.2–8.11 | hash-then-MAC, Merkle–Damgård, Davies–Meyer and variants, HMAC, sponge, Merkle trees, HKDF, TCR |
| `Ch9AE` | §9.1–9.8 | AE and AD ciphers, encrypt-then-MAC, MAC-then-encrypt, GCM, GMAC, TLS 1.3 record |

## Two organizing decisions

**Randomness is a resource.**  A `PFunPDS` is a finite-support law over
deterministic systems, so a system answering unboundedly many queries with
independent fresh coins is not one: `n` queries would need `|R|^n` transcript
atoms where a `k`-atom mixture gives at most `k`.  What *is* expressible is
randomness indexed by a finite type — which is exactly a uniform random
function.  So `coins` is a URF, composed in parallel with the primitive, and a
single converter, `randomizeNonce` (`Ch5CPA.lean`), turns any nonce-based
scheme into its randomized counterpart.  That converter is used by randomized
counter mode, CBC, the generic hybrid, Carter–Wegman and encrypt-then-MAC; no
other object in this tree touches randomness.  This mirrors the book's own
§5.5, which presents the nonce-based schemes as the §5.4 schemes with the
sampled value "treated as a nonce".

**Constructions are generic.**  Everything is parameterized over its abstract
primitive.  The fixed round functions — DES, AES, SHA256, Salsa/ChaCha, RC4,
the linear congruential and subset-sum generators — are not declared: they are
bit-level specifications with no random-system content that `blockCipherSystem`
and `prfSystem` do not already carry.  Where the book itself leaves an
encoding abstract (§6.6's `pf`, §6.8's `inj`, GCM's nonce and length
formatting) it stays a parameter here too.

Also not declared: the "fun application" sections (§2.4, §3.12, §4.8, §5.6,
§6.12, §7.7, §8.12, §9.11).  Those are protocols and applications — anonymous
routing, bit commitment, private information retrieval — rather than symmetric
primitives.

## Reuse

Three points where this tree defers to what the repository already has, rather
than restating it: `RandomSystems.CR18.cbcState` is the CBC chaining for
§6.4.1 (the same function Maurer's CBC-MAC theorem is proved about);
`PFunPDS.URF` and `PFunPDS.URP` are the ideal PRF and block cipher of Attack
Games 4.1 and 4.2; and `PFunPDS.par` / `PFunPDS.apply` are the parallel
composition and converter application that put the coin resource in place.
-/
