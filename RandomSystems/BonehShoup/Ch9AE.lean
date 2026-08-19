/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch8Hash

/-!
# Boneh–Shoup Chapter 9: authenticated encryption

Boneh–Shoup §9.1–§9.8 (`papers/BonehShoup.pdf`, book pp. 358–386): the
authenticated-encryption interface, the two generic compositions, nonce-based
authenticated encryption with associated data, GCM, and the TLS 1.3 record
protocol.

## The rejecting interface

What separates this chapter's objects from Chapters 2 and 5 is that decryption
may **reject**.  `AECipher` and `ADCipher` therefore have `dec` returning
`Option`, where `none` is the book's `reject`, and their correctness laws say
a genuine ciphertext decrypts to `some m`.

## Randomness

Same discipline as Ch. 5: the deterministic or nonce-based object is the
primitive one, and the probabilistic §9.4 ciphers are obtained by composing it
with the `coins` resource under `randomizeNonce`.  `nonceEncryptThenMAC` is the
hinge — it is both the nonce-based form that GCM instantiates and the core
that the randomized §9.4.1 cipher randomizes.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §9.1 Authenticated encryption -/

/-- **An authenticated-encryption cipher** (Boneh–Shoup §9.1): a cipher whose
decryption algorithm may reject.  `none` is the book's `reject`.

AE security is the conjunction of CPA security and *ciphertext integrity* —
the adversary cannot produce any new ciphertext that decrypts successfully.
Neither is declared here. -/
structure AECipher (K : Type w) (M : Type u) (C : Type v) where
  /-- The encryption algorithm `E : K × M → C`. -/
  enc : K → M → C
  /-- The decryption algorithm `D : K × C → M ∪ {reject}`. -/
  dec : K → C → Option M
  /-- Correctness: a genuine ciphertext decrypts to its plaintext. -/
  dec_enc : ∀ k m, dec k (enc k m) = some m

namespace AECipher

variable {K : Type w} {M : Type u} {C : Type v}

/-- **The encryption oracle of an AE cipher**. -/
def encSystem (E : AECipher K M C) (keyDist : Dist K) : PFunPDS M C :=
  keyed keyDist E.enc

/-- **The chosen-ciphertext oracle of an AE cipher** (Boneh–Shoup §9.2.2): the
adversary may encrypt via `.inl` or decrypt via `.inr`, the latter answering
`none` on rejection.  Theorem 9.1 — that authenticated encryption implies
chosen-ciphertext security — is a statement about this system, and is not
made here. -/
def system (E : AECipher K M C) (keyDist : Dist K) : PFunPDS (M ⊕ C) (C ⊕ Option M) :=
  keyed keyDist fun k q =>
    match q with
    | Sum.inl m => Sum.inl (E.enc k m)
    | Sum.inr c => Sum.inr (E.dec k c)

/-- The AE encryption oracle is a probability distribution over systems
whenever the key law is. -/
@[simp] theorem isProbDist_encSystem (E : AECipher K M C) (keyDist : Dist K) :
    (E.encSystem keyDist).isProbDist ↔ keyDist.isProbDist :=
  keyed_isProbDist _ _

end AECipher

/-! ## §9.4.1 Encrypt-then-MAC -/

/-- **Encrypt-then-MAC** (Boneh–Shoup §9.4.1): encrypt, then MAC *the
ciphertext*,

  `E_EtM((kₑ, kₘ), m) := c ← E(kₑ, m), t ← S(kₘ, c), output (c, t)`,
  `D_EtM((kₑ, kₘ), (c, t)) := reject if V(kₘ, c, t) rejects, else D(kₑ, c)`.

Theorem 9.2: this is AE-secure whenever the cipher is CPA-secure and the MAC
is secure — the book's recommended generic composition.

Two implementation mistakes the book calls out, both visible in this
signature: the keys `kₑ` and `kₘ` must be *independent*, so they appear as a
pair and not as one key; and the MAC must cover the *whole* ciphertext, which
is why `I` is a MAC on `C` and not on some part of it.  Applying the MAC to
only part of a randomized-CBC ciphertext — leaving the IV unprotected —
destroys ciphertext integrity. -/
def encryptThenMAC {Kₑ Kₘ M C T : Type*}
    (E : Cipher Kₑ M C) (I : MAC Kₘ C T) : AECipher (Kₑ × Kₘ) M (C × T) where
  enc k m := (E.enc k.1 m, I.sign k.2 (E.enc k.1 m))
  dec k p := if I.verify k.2 p.1 p.2 then some (E.dec k.1 p.1) else none
  dec_enc k m := by simp [I.verify_sign, E.dec_enc]

/-! ## §9.4.4 MAC-then-encrypt -/

/-- **MAC-then-encrypt** (Boneh–Shoup §9.4.4, eq. 9.11): MAC the *message*,
then encrypt message and tag together,

  `E_MtE((kₑ, kₘ), m) := t ← S(kₘ, m), c ← E(kₑ, m ‖ t)`,
  `D_MtE((kₑ, kₘ), c) := (m ‖ t) ← D(kₑ, c); reject unless V(kₘ, m, t)`.

MtE is **not** generically secure, and the book documents padding-oracle
attacks against it in SSL and TLS 1.0 (including Lucky13).  Theorem 9.3
rescues it for specific ciphers — randomized counter mode, and randomized CBC
without message padding — where it is AE-secure even with a merely one-time
secure MAC.

Splitting the decrypted string needs the tag length, so `tagLen` and the
hypothesis that `I` produces tags of that length are explicit; the book fixes
`T := Y^{ℓₜ}`. -/
def macThenEncrypt {Kₑ Kₘ A : Type*} (tagLen : ℕ)
    (E : Cipher Kₑ (List A) (List A)) (I : MAC Kₘ (List A) (List A))
    (hTag : ∀ k m, (I.sign k m).length = tagLen) :
    AECipher (Kₑ × Kₘ) (List A) (List A) where
  enc k m := E.enc k.1 (m ++ I.sign k.2 m)
  dec k c :=
    let p := E.dec k.1 c
    let m := p.take (p.length - tagLen)
    let t := p.drop (p.length - tagLen)
    if I.verify k.2 m t then some m else none
  dec_enc k m := by
    have hp : E.dec k.1 (E.enc k.1 (m ++ I.sign k.2 m)) = m ++ I.sign k.2 m :=
      E.dec_enc k.1 _
    simp only [hp, List.length_append, hTag k.2 m, Nat.add_sub_cancel,
      List.take_left, List.drop_left, I.verify_sign, if_true]

/-! ## §9.5 Nonce-based authenticated encryption with associated data -/

/-- **A nonce-based AD cipher** (Boneh–Shoup §9.5): encryption and decryption
are deterministic and take a nonce and *associated data* — data whose
integrity the ciphertext protects but whose secrecy it does not.

Correctness holds when decryption is given the same nonce and associated data
as encryption.  With the empty message the cipher degenerates to a MAC on the
associated data, which is how GMAC arises from GCM. -/
structure ADCipher (K : Type w) (N : Type u) (D : Type v) (M C : Type*) where
  /-- The encryption algorithm `E : K × M × D × N → C`. -/
  enc : K → N → D → M → C
  /-- The decryption algorithm `D : K × C × D × N → M ∪ {reject}`. -/
  dec : K → N → D → C → Option M
  /-- Correctness: under matching nonce and associated data, decryption
  inverts encryption. -/
  dec_enc : ∀ k n d m, dec k n d (enc k n d m) = some m

namespace ADCipher

variable {K : Type w} {N : Type u} {D : Type v} {M C : Type*}

/-- **The encryption oracle of an AD cipher**: a key drawn once, and every
nonce/associated-data/message triple answered with its ciphertext. -/
def encSystem (E : ADCipher K N D M C) (keyDist : Dist K) : PFunPDS (N × D × M) C :=
  keyed keyDist fun k q => E.enc k q.1 q.2.1 q.2.2

/-- **The two-port oracle of an AD cipher**: encryption via `.inl` and
decryption via `.inr`, the interface the book's AEAD attack games use. -/
def system (E : ADCipher K N D M C) (keyDist : Dist K) :
    PFunPDS ((N × D × M) ⊕ (N × D × C)) (C ⊕ Option M) :=
  keyed keyDist fun k q =>
    match q with
    | Sum.inl p => Sum.inl (E.enc k p.1 p.2.1 p.2.2)
    | Sum.inr p => Sum.inr (E.dec k p.1 p.2.1 p.2.2)

/-- The AD encryption oracle is a probability distribution over systems
whenever the key law is. -/
@[simp] theorem isProbDist_encSystem (E : ADCipher K N D M C) (keyDist : Dist K) :
    (E.encSystem keyDist).isProbDist ↔ keyDist.isProbDist :=
  keyed_isProbDist _ _

end ADCipher

/-- **Nonce-based encrypt-then-MAC**: the §9.4.1 composition over a nonce-based
cipher, yielding a nonce-based AD cipher with no associated data.

This is the hinge of the chapter.  Read forwards it is what GCM instantiates
(§9.7); read backwards, composing it with the `coins` resource recovers the
probabilistic encrypt-then-MAC cipher of §9.4.1, exactly as §5.5 relates the
nonce-based and randomized modes. -/
def nonceEncryptThenMAC {Kₑ Kₘ N M C T : Type*}
    (E : NonceCipher Kₑ N M C) (I : MAC Kₘ C T) :
    ADCipher (Kₑ × Kₘ) N Unit M (C × T) where
  enc k n _ m := (E.enc k.1 n m, I.sign k.2 (E.enc k.1 n m))
  dec k n _ p := if I.verify k.2 p.1 p.2 then some (E.dec k.1 n p.1) else none
  dec_enc k n _ m := by simp [I.verify_sign, E.dec_enc]

/-- **Randomized encrypt-then-MAC as a random system** (Boneh–Shoup §9.4.1
over a probabilistic cipher): the nonce drawn fresh from the `coins` resource
per message and carried in the ciphertext.

The book's §9.4.1 writes `c ←R E(kₑ, m)` with a probabilistic `E`; here the
probabilism is factored out into the coin resource, so the composition itself
stays deterministic. -/
def randomizedEncryptThenMACSystem {Kₑ Kₘ N M C T Ix : Type*}
    [Fintype (Ix → N)] [Nonempty (Ix → N)] [Fintype Kₑ] [Nonempty Kₑ]
    [Fintype Kₘ] [Nonempty Kₘ]
    (E : NonceCipher Kₑ N M C) (I : MAC Kₘ C T) (idx : ℕ → Ix) :
    PFunPDS M (N × (C × T)) :=
  PFunPDS.apply (randomizeNonce idx)
    (PFunPDS.par (coins Ix N)
      (keyed (Dist.uniform (Kₑ × Kₘ)) fun k p =>
        (nonceEncryptThenMAC E I).enc k p.1 () p.2))

/-! ## §9.7 Galois counter mode -/

variable {F : Type u} [CommRing F]

/-- **GHASH** (Boneh–Shoup §9.7, eq. 9.18), the keyed hash inside GCM's
Carter–Wegman MAC:

  `GHASH(k, z) := z[0]·k^v + z[1]·k^{v-1} + ⋯ + z[v-1]·k`,

polynomial evaluation in `GF(2^128)`, where addition is XOR and multiplication
is modulo `g(X) = X^128 + X^7 + X^2 + X + 1`.  This is `H_xpoly` from §7.4 with
the field changed from `ℤ_p` to `GF(2^n)`, which is what makes it fast on
128-bit blocks and gives GCM its name.

Written by Horner's method, so processing a block costs one addition and one
multiplication. -/
def ghash (k : F) (z : List F) : F :=
  k * z.foldl (fun t a => t * k + a) 0

/-- The counter-mode keystream of GCM: `E(k, x), E(k, inc x), E(k, inc² x), …`
for `n` blocks. -/
def gcmKeystream {K : Type w} (E : BlockCipher K F) (inc : F → F) (k : K) (start : F)
    (n : ℕ) : List F :=
  (List.range n).map fun i => E k (inc^[i] start)

/-- **Galois counter mode** (Boneh–Shoup §9.7), a nonce-based AEAD cipher
standardized by NIST in 2007 and the recommended way to get authenticated
encryption in practice.

It is encrypt-then-MAC with nonce-based counter mode as the cipher and a
Carter–Wegman MAC over GHASH as the MAC, but with the keys "cut a few
corners": a single block-cipher key `k` serves for all three roles — the GHASH
key is `E(k, 0)`, the counter-mode keystream starts at `inc x`, and the
Carter–Wegman pad is `E(k, x)`.  Starting the message keystream one step past
`x` is what keeps the PRF inputs used for encryption disjoint from the one
used for the pad.

`nonceToCounter` is the book's derivation of the initial counter `x` from the
nonce — `𝓍 ‖ 0^31 1` for the 96-bit case, `GHASH(kₘ, 𝓍' ‖ length(𝓍))`
otherwise — and `lenBlock` the trailing block holding the two 64-bit length
fields.  Both are formatting, and both are parameters here; the associated
data and ciphertext are already block sequences, so the book's zero-padding of
each to a multiple of 128 bits is implicit.

GCM has **no** nonce-reuse resistance: repeating a nonce loses secrecy for
both messages and exposes the GHASH key, so ciphertext integrity falls too. -/
def gcm {K : Type w} {N : Type v} [DecidableEq F] (E : BlockCipher K F) (inc : F → F)
    (nonceToCounter : N → F) (lenBlock : ℕ → ℕ → F) :
    ADCipher K N (List F) (List F) (List F × F) where
  enc k n d m :=
    let x := nonceToCounter n
    let c := xorKeystream (gcmKeystream E inc k (inc x) m.length) m
    let h := ghash (E k 0) (d ++ c ++ [lenBlock d.length c.length])
    (c, h + E k x)
  dec k n d p :=
    let x := nonceToCounter n
    let h := ghash (E k 0) (d ++ p.1 ++ [lenBlock d.length p.1.length])
    if h + E k x = p.2 then
      some (unxorKeystream (gcmKeystream E inc k (inc x) p.1.length) p.1)
    else none
  dec_enc k n d m := by
    have hks : (gcmKeystream E inc k (inc (nonceToCounter n)) m.length).length
        = m.length := by simp [gcmKeystream]
    simp only [length_xorKeystream, hks, min_self, if_true]
    exact congrArg some
      (unxorKeystream_xorKeystream _ m (le_of_eq hks.symm))

/-- **GMAC**: GCM on the empty message, a MAC for the associated data alone.
The book notes this falls out of the AD-cipher syntax without a separate
construction. -/
def gmac {K : Type w} {N : Type v} [DecidableEq F] (E : BlockCipher K F) (inc : F → F)
    (nonceToCounter : N → F) (lenBlock : ℕ → ℕ → F) (k : K) (n : N) (d : List F) :
    List F × F :=
  (gcm E inc nonceToCounter lenBlock).enc k n d []

/-! ## §9.8 The TLS 1.3 record protocol -/

/-- **The TLS 1.3 record nonce** (Boneh–Shoup §9.8): pad the party's 64-bit
write sequence number on the left with zeroes to the nonce length, then XOR
with the fixed `client_write_iv` or `server_write_iv` derived from the master
secret at session setup.

The initial nonce is randomized rather than zero on purpose: with a zero
nonce the first record — often a known fixed value — would give an attacker a
known plaintext/ciphertext pair at a fixed nonce, opening a time-space
tradeoff attack on the key. -/
def tlsRecordNonce (writeIv : List Bool) (encodeSeq : ℕ → List Bool) (seq : ℕ) :
    List Bool :=
  xorBits (encodeSeq seq) writeIv

/-- **A TLS 1.3 record** (Boneh–Shoup §9.8): the AEAD ciphertext framed with
its cleartext header,

  `type ‖ version ‖ length ‖ c`.

The associated data is empty and the nonce is *not* transmitted — the receiver
recomputes it from its own sequence number, which is why `tlsRecordNonce` is
deterministic in the sequence number. -/
def tlsRecord (recordType version : List Bool) (encodeLength : ℕ → List Bool)
    (c : List Bool) : List Bool :=
  recordType ++ version ++ encodeLength c.length ++ c

/-- **The TLS 1.3 record protocol as a random system**: a uniform key, and
each `(sequence number, plaintext)` answered with the framed encrypted record.

Records are encrypted under a nonce-based AEAD cipher with empty associated
data; a sequence number that never repeats is what discharges the cipher's
nonce-uniqueness requirement, so no coin resource appears. -/
def tlsRecordSystem {K : Type w} [Fintype K] [Nonempty K]
    (E : ADCipher K (List Bool) Unit (List Bool) (List Bool))
    (writeIv : List Bool) (encodeSeq : ℕ → List Bool)
    (recordType version : List Bool) (encodeLength : ℕ → List Bool) :
    PFunPDS (ℕ × List Bool) (List Bool) :=
  uniformKeyed fun k q =>
    tlsRecord recordType version encodeLength
      (E.enc k (tlsRecordNonce writeIv encodeSeq q.1) () q.2)

end RandomSystems.BonehShoup
