/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch6MAC
import RandomSystems.UniversalHash

/-!
# Boneh–Shoup Chapter 7: message integrity from universal hashing

Boneh–Shoup §7.1–§7.6 (`papers/BonehShoup.pdf`, book pp. 252–276): universal
hash functions and their constructions, the hash-then-PRF paradigm, the
Carter–Wegman MAC, nonce-based MACs, and unconditionally secure one-time MACs.

A UHF in the book is a *keyed hash function* together with a bound on its
collision probability.  The carrier is therefore the same as a PRF's — `PRF`
is what the constructions below are declared at — and the bound is
`IsUHF`, the length-independent case of the tree's one universality notion,
`RandomSystems.IsAlmostUniversal` (`RandomSystems/UniversalHash.lean`).

## Reuse

Three identifications, all stated rather than duplicated:

* the book's UHF security (Definition 7.4, Attack Game 7.1) is
  `RandomSystems.IsEpsUniversal` at a uniform key; there is no separate
  Boneh–Shoup universality predicate, only the abbreviation `IsUHF` that fixes
  the key law.

* PRF(UHF) composition (§7.3) is the *same formula* as the encrypted PRF of
  §6.5 — `F(k₂, H(k₁, m))` — under a different hypothesis on the inner
  function, so `prfUhfComposition` is `encryptedPRF`.
* The randomized Carter–Wegman MAC (§7.4) draws a fresh randomizer per
  message and returns it inside the tag.  That is precisely the shape
  `randomizeNonce` was written for in Ch. 5, so the coin resource enters here
  by reusing that converter, not a new one.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §7.1 Universal hash functions -/

/-- **An `ε`-UHF** (Boneh–Shoup Definition 7.4 with Attack Game 7.1): a keyed
hash function `H` such that two distinct messages collide under a uniform key
with probability at most `ε`.

The carrier is the same as a PRF's, so the constructions below are declared at
`PRF`; what makes a keyed hash a *UHF* is this bound, and the bound is the
tree's one universality notion — the length-independent case of
`RandomSystems.IsAlmostUniversal` (CR18 lecture notes Definition 6.2), whose
`δ` here is the constant `ε`.  The book's `ℓ/p` bound for `hpoly` reads the
message length, so a family stated at that bound is
`RandomSystems.IsAlmostUniversal` directly rather than through this
abbreviation. -/
abbrev IsUHF {K : Type w} {M : Type u} {T : Type v} [Fintype K] [Nonempty K]
    (H : PRF K M T) (ε : NNReal) : Prop :=
  RandomSystems.IsEpsUniversal H (Dist.uniform K) ε

/-! ## §7.2.1 Construction 1: UHFs using polynomials -/

/-- **The polynomial hash `H_poly`** (Boneh–Shoup §7.2.1, eq. 7.3).  Read the
message as the lower coefficients of a monic polynomial and evaluate it at the
secret key:

  `H_poly(k, (a₁, …, a_v)) := k^v + a₁k^{v-1} + ⋯ + a_{v-1}k + a_v`.

Implemented by Horner's method — `t ← 1; for i ← 1 to v do t ← t·k + aᵢ` —
which is what lets a long message be hashed one block at a time, without
knowing its length in advance.  The book shows it is an `ℓ/p`-UHF: two
distinct messages give polynomials whose difference is nonzero of degree at
most `ℓ`, hence has at most `ℓ` roots. -/
def hpoly {p : ℕ} (k : ZMod p) (m : List (ZMod p)) : ZMod p :=
  m.foldl (fun t a => t * k + a) 1

/-- **The shifted polynomial hash `H_xpoly`** (Boneh–Shoup §7.3.2, eq. 7.23):
one extra factor of the key,

  `H_xpoly(k, (a₁, …, a_v)) = k^{v+1} + a₁k^v + ⋯ + a_v·k = k · H_poly(k, m)`.

The shift is what makes it a *difference* unpredictable function rather than
merely a UHF, which is what the Carter–Wegman analysis needs. -/
def hxpoly {p : ℕ} (k : ZMod p) (m : List (ZMod p)) : ZMod p :=
  k * hpoly k m

/-! ## §7.2.2 Construction 2: CBC and cascade are computational UHFs

No new object: Corollary 7.5 states that `cbcPRF` and `cascadePRF` from §6.4,
already declared in `Ch6MAC.lean`, are computational UHFs.  That is a theorem
about those functions, not a different construction, so nothing is restated
here. -/

/-! ## §7.2.3 Construction 3: a parallel UHF from a small PRF -/

/-- **XOR-hash `F^⊕`** (Boneh–Shoup §7.2.3), a UHF suited to parallel
hardware: tag each block with its position, apply the PRF, and XOR the
results,

  `t ← 0ⁿ;  for i ← 1 to v do t ← t ⊕ F(k, (aᵢ, i));  output t`.

Unlike CBC and cascade, its collision bound does not depend on the message
length. -/
def xorHash {K : Type w} {X : Type u} {Y : Type v} [AddCommGroup Y]
    (F : PRF K (X × ℕ) Y) : PRF K (List X) Y :=
  fun k m => (m.mapIdx fun i a => F k (a, i + 1)).foldl (· + ·) 0

/-! ## §7.3 PRF(UHF) composition -/

/-- **PRF(UHF) composition** (Boneh–Shoup §7.3, eq. 7.18): hash the long
message to a short digest, then apply the PRF,

  `F'((k₁, k₂), m) := F(k₂, H(k₁, m))`.

This is the same formula as the encrypted PRF of §6.5; the difference is the
hypothesis — there `PF` had to be an extendable prefix-free secure PRF, here
`H` need only be a computational UHF.  ECBC, NMAC and PMAC₀ are all instances,
which is how §7.3.1 and §7.3.3 re-derive their security. -/
abbrev prfUhfComposition {K₁ K₂ : Type w} {M : Type u} {X T : Type v}
    (H : PRF K₁ M X) (F : PRF K₂ X T) : PRF (K₁ × K₂) M T :=
  encryptedPRF H F

/-! ## §7.4 The Carter–Wegman MAC -/

/-- **A nonce-based MAC** (Boneh–Shoup §7.5): signing and verification are
deterministic, and both take a nonce.  Correctness holds whenever signer and
verifier use the same nonce; security (Attack Game 7.4) additionally forbids
the adversary from ever repeating one. -/
structure NonceMAC (K : Type w) (N : Type u) (M : Type v) (T : Type*) where
  /-- The signing algorithm `S : K × M × N → T`. -/
  sign : K → N → M → T
  /-- The verification algorithm `V : K × M × T × N → {accept, reject}`. -/
  verify : K → N → M → T → Bool
  /-- Correctness: a tag produced under a nonce verifies under that nonce. -/
  verify_sign : ∀ k n m, verify k n m (sign k n m) = true

namespace NonceMAC

variable {K : Type w} {N : Type u} {M : Type v} {T : Type*}

/-- **The signing oracle of a nonce-based MAC**: a key drawn once, and every
nonce/message pair answered with its tag. -/
def signSystem (I : NonceMAC K N M T) (keyDist : Dist K) : PFunPDS (N × M) T :=
  keyed keyDist fun k p => I.sign k p.1 p.2

/-- **The randomized signing oracle**: the nonce drawn fresh from the `coins`
resource per message and returned as part of the tag.  This is the §7.4 shape
— a randomized MAC whose tag is `(r, v)` — obtained from the nonce-based one
by the Ch. 5 converter. -/
def randomizedSignSystem {Ix : Type*} [Fintype (Ix → N)] [Nonempty (Ix → N)]
    (I : NonceMAC K N M T) (keyDist : Dist K) (idx : ℕ → Ix) : PFunPDS M (N × T) :=
  PFunPDS.apply (randomizeNonce idx) (PFunPDS.par (coins Ix N) (I.signSystem keyDist))

/-- The nonce-based signing oracle is a probability distribution over systems
whenever the key law is. -/
@[simp] theorem isProbDist_signSystem (I : NonceMAC K N M T) (keyDist : Dist K) :
    (I.signSystem keyDist).isProbDist ↔ keyDist.isProbDist :=
  keyed_isProbDist _ _

end NonceMAC

/-- **The nonce-based Carter–Wegman MAC** (Boneh–Shoup §7.5.1): mask the hash
of the message with the PRF evaluated at the nonce,

  `S((k₁, k₂), m, 𝓍) := H(k₁, m) + F(k₂, 𝓍)`.

Reusing a nonce across different messages breaks this completely: the
difference of two tags is the difference of their hashes, with the mask gone. -/
def carterWegmanNonceMAC {K₁ K₂ N M T : Type*}
    [AddCommGroup T] [DecidableEq T] (H : PRF K₁ M T) (F : PRF K₂ N T) :
    NonceMAC (K₁ × K₂) N M T where
  sign k n m := H k.1 m + F k.2 n
  verify k n m t := decide (H k.1 m + F k.2 n = t)
  verify_sign _ _ _ := by simp

/-- **The Carter–Wegman MAC** (Boneh–Shoup §7.4) as a random system.  The
signing algorithm draws a fresh randomizer `r ←R R`, computes
`v ← H(k₁, m) + F(k₂, r)`, and outputs the tag `(r, v)` — the book's first
randomized MAC, in which every message has many valid tags.

The randomizer only ever needs to be *distinct* across signatures, which is
exactly the observation §7.5 turns into the nonce-based version above; here it
is drawn from the `coins` resource. -/
def carterWegmanSystem {K₁ K₂ R M T Ix : Type*} [AddCommGroup T] [DecidableEq T]
    [Fintype (Ix → R)] [Nonempty (Ix → R)] [Fintype K₁] [Nonempty K₁]
    [Fintype K₂] [Nonempty K₂]
    (H : PRF K₁ M T) (F : PRF K₂ R T) (idx : ℕ → Ix) : PFunPDS M (R × T) :=
  (carterWegmanNonceMAC H F).randomizedSignSystem (Dist.uniform (K₁ × K₂)) idx

/-! ## §7.6 Unconditionally secure one-time MACs -/

/-- **A pairwise unpredictable function from a difference unpredictable one**
(Boneh–Shoup §7.6.2, eq. 7.32): add an independent uniform offset,

  `H'((k₁, k₂), m) := H(k₁, m) + k₂`.

Lemma 7.11: the offset makes the response to the adversary's one query
uniform and independent of `k₁`, so predicting `H'` at a second point requires
predicting the *difference* of `H` at two points. -/
def pufOfDuf {K : Type w} {M : Type u} {T : Type v} [AddCommGroup T]
    (H : PRF K M T) : PRF (K × T) M T :=
  fun k m => H k.1 m + k.2

/-- **The polynomial pairwise unpredictable function** (Boneh–Shoup §7.6.2,
eq. 7.33):

  `H'_xpoly((k₁, k₂), (a₁, …, a_v)) := k₁^{v+1} + a₁k₁^v + ⋯ + a_v k₁ + k₂`,

which is `pufOfDuf` applied to `hxpoly`.  The book shows it is an
`(ℓ+1)/p`-PUF. -/
def hxpolyPuf {p : ℕ} : PRF (ZMod p × ZMod p) (List (ZMod p)) (ZMod p) :=
  pufOfDuf (fun k m => hxpoly k m)

/-- **The one-time MAC derived from a keyed hash function** (Boneh–Shoup
§7.6.3): sign with the hash, verify by recomputing.

Theorem 7.12 is that when `H` is an `ε`-PUF this MAC is *unconditionally*
secure for a single signing query — the MAC analogue of the one-time pad.
This is the same construction as `macOfPRF`; what changes is the hypothesis on
the keyed function and the restriction to one query. -/
abbrev oneTimeMACOfPUF {K : Type w} {M : Type u} {T : Type v} [DecidableEq T]
    (H : PRF K M T) : MAC K M T :=
  macOfPRF H

/-- **The one-time MAC as a random system**: a uniform key, and each message
answered with its hash. -/
def oneTimeMACSystem {K : Type w} {M : Type u} {T : Type v} [DecidableEq T]
    [Fintype K] [Nonempty K] (H : PRF K M T) : PFunPDS M T :=
  (oneTimeMACOfPUF H).signSystem (Dist.uniform K)

end RandomSystems.BonehShoup
