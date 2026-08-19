/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch7UHF

/-!
# Boneh–Shoup Chapter 8: message integrity from collision resistant hashing

Boneh–Shoup §8.2–§8.11 (`papers/BonehShoup.pdf`, book pp. 291–341): hash-then-
MAC, the Merkle–Damgård paradigm, compression functions from block ciphers,
the keying methods and HMAC, the sponge, Merkle trees, HKDF, and target
collision resistance.

Hash functions here are *keyless*, so most of this file declares plain
functions rather than random systems; collision resistance, second-preimage
resistance and target collision resistance are all security notions and none
of them appears.  The keyed constructions — HMAC, the derived TCR hash,
hash-then-MAC — do get their random system.

Bit-level constructions (padding, HMAC's `ipad`/`opad`, the sponge) are stated
over `List Bool` with `chunk` from the prelude doing the partitioning.  Where
the book leaves an encoding abstract — the Merkle–Damgård length field, HKDF's
`Octet` — it stays a parameter here too.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## Bit strings -/

/-- Bitwise XOR of two strings, truncating to the shorter one. -/
def xorBits (a b : List Bool) : List Bool :=
  List.zipWith xor a b

/-! ## §8.2 Building a MAC for large messages -/

/-- **Hash-then-MAC** (Boneh–Shoup §8.2, eq. 8.1): extend a MAC's message
space by hashing first,

  `S'(k, m) := S(k, H(m))`,  `V'(k, m, t) := V(k, H(m), t)`.

Theorem 8.1 makes this secure when `H` is collision resistant.  The book warns
that this dependence is essential and, worse, that a collision on `H` can be
found *offline*, which is the reason §8.7 looks for something better. -/
def hashThenMAC {K : Type w} {M : Type u} {D T : Type v}
    (I : MAC K D T) (H : M → D) : MAC K M T where
  sign k m := I.sign k (H m)
  verify k m t := I.verify k (H m) t
  verify_sign k m := I.verify_sign k (H m)

/-- **Hash-then-MAC as a random system**: a uniform key, and every long
message answered with the tag of its digest. -/
def hashThenMACSystem {K : Type w} {M : Type u} {D T : Type v} [Fintype K] [Nonempty K]
    (I : MAC K D T) (H : M → D) : PFunPDS M T :=
  (hashThenMAC I H).signSystem (Dist.uniform K)

/-! ## §8.4 The Merkle–Damgård paradigm -/

/-- **The Merkle–Damgård chain** (Boneh–Shoup §8.4): iterate the compression
function over the message blocks, starting from the initial value,

  `t₀ ← IV;  for i ← 1 to s do tᵢ ← h(t_{i-1}, mᵢ);  output t_s`. -/
def merkleDamgardChain {X : Type u} {B : Type v} (h : X → B → X) (iv : X)
    (blocks : List B) : X :=
  blocks.foldl h iv

/-- **The Merkle–Damgård hash** derived from a compression function: pad the
message into blocks, then chain.  SHA256 is of this form, with `ℓ = 512` and
`n = 256`. -/
def merkleDamgard {X : Type u} {B : Type v} {M : Type w} (h : X → B → X) (iv : X)
    (pad : M → List B) (m : M) : X :=
  merkleDamgardChain h iv (pad m)

/-- **The Merkle–Damgård padding** (Boneh–Shoup §8.4): append the padding
block `PB := 100…00 ‖ ⟨s⟩`, where `⟨s⟩` is a fixed-width encoding of the
number of blocks, and cut the result into `ℓ`-bit blocks.

Encoding the *length* into the padding is what the collision-resistance proof
uses: two colliding messages must then have the same block count, which is
what lets the proof walk both chains backwards in step.  `encodeLength` must
produce exactly `w` bits; the book typically takes `w = 64`. -/
def merkleDamgardPad (l w : ℕ) (encodeLength : ℕ → List Bool) (m : List Bool) :
    List (List Bool) :=
  let zeros := (l - (m.length + 1 + w) % l) % l
  let total := m.length + 1 + zeros + w
  chunk l (m ++ true :: List.replicate zeros false ++ encodeLength (total / l))

/-! ## §8.5 Building compression functions -/

/-- **A simple but inefficient compression function** (Boneh–Shoup §8.5.1,
eq. 8.3): `H(a, b) = abs(x^a y^b mod p)`, folded back into `[1, q]` by
`abs z = z` for `z ≤ q` and `p - z` otherwise, where `q = (p-1)/2`.

Collision resistance rests on a standard number-theoretic assumption, but the
function is far slower than the block-cipher constructions below, so it is
hardly ever used. -/
def simpleCompression (p q x y : ℕ) (a b : ℕ) : ℕ :=
  let z := (x ^ a * y ^ b) % p
  if z ≤ q then z else p - z

variable {X : Type u} [AddCommGroup X]

/-- **The Davies–Meyer compression function** (Boneh–Shoup §8.5.2):

  `h_DM(x, y) := E(y, x) ⊕ x`,

with the *message block* `y` used as the block cipher key and the chaining
variable `x` as the data block.  The whole SHA family uses this.

Note it is the message, over which the adversary has full control, that keys
the cipher — which is why collision resistance here is proved in the ideal
cipher model rather than from block-cipher security. -/
def daviesMeyer {K : Type w} (E : BlockCipher K X) (x : X) (y : K) : X :=
  E y x + x

/-- **The Matyas–Meyer–Oseas compression function** (Boneh–Shoup §8.5.2,
Figure 8.7): `h₁(x, y) := E(x, y) ⊕ y`, with the roles reversed — the
*chaining variable* keys the cipher.  Because of that reversal, using it in
Merkle–Damgård needs an auxiliary encoding `g : X → K` of the chaining
variable into the key space. -/
def matyasMeyerOseas {K : Type w} (E : BlockCipher K X) (g : X → K) (t m : X) : X :=
  E (g t) m + m

/-- **The Miyaguchi–Preneel compression function** (Boneh–Shoup §8.5.2,
Figure 8.7): `h₂(x, y) := E(x, y) ⊕ y ⊕ x`, Matyas–Meyer–Oseas with the
chaining variable fed forward as well.  Whirlpool uses this method. -/
def miyaguchiPreneel {K : Type w} (E : BlockCipher K X) (g : X → K) (t m : X) : X :=
  E (g t) m + m + t

/-- **A third block-cipher compression function** (Boneh–Shoup §8.5.2):
`h₃(x, y) := E(x ⊕ y, y) ⊕ y`.  The book lists it alongside Davies–Meyer as
one of the twelve variants of Preneel et al. that can be shown collision
resistant. -/
def compressionVariant₃ {K : Type w} (E : BlockCipher K X) (g : X → K) (t m : X) : X :=
  E (g (t + m)) m + m

/-! ## §8.7 Keying a hash function, and HMAC -/

/-- **Prepend the key** (Boneh–Shoup §8.7): `F_pre(k, M) := H(k ‖ M)`.

Completely insecure for a Merkle–Damgård hash — the extension attack computes
`F_pre(k, M ‖ PB ‖ M')` from `F_pre(k, M)` without the key.  It *is* secure
when `H` is a sponge, which is one of the sponge's selling points. -/
def prependKey {T : Type v} (H : List Bool → T) (k M : List Bool) : T :=
  H (k ++ M)

/-- **Append the key** (Boneh–Shoup §8.7): `F_post(k, M) := H(M ‖ k)`.  This
one is vulnerable to an *offline* collision attack on the compression
function, so it does not meet the section's goal either. -/
def appendKey {T : Type v} (H : List Bool → T) (k M : List Bool) : T :=
  H (M ++ k)

/-- **The envelope method** (Boneh–Shoup §8.7):
`F_env(k, M) := H(k ‖ M ‖ k)`, provably a secure PRF under reasonable
pseudorandomness assumptions on the compression function. -/
def envelopeKey {T : Type v} (H : List Bool → T) (k M : List Bool) : T :=
  H (k ++ M ++ k)

/-- **The two-key nest** (Boneh–Shoup §8.7):

  `F_nest((k₁, k₂), M) := H(k₂ ‖ H(k₁ ‖ M))`.

§8.7.1 shows this is a secure PRF: the outer keys `k₁, k₂` only serve to
derive chaining values, and what is left is exactly a bit-wise NMAC over the
compression function. -/
def twoKeyNest (H : List Bool → List Bool) (k₁ k₂ M : List Bool) : List Bool :=
  H (k₂ ++ H (k₁ ++ M))

/-- **HMAC** (Boneh–Shoup §8.7.2), the most widely deployed MAC on the
Internet:

  `HMAC(k, M) := H((k ⊕ opad) ‖ H((k ⊕ ipad) ‖ M))`.

This is the two-key nest with the two keys *derived from one* by XORing with
the constants `ipad = 0x36…36` and `opad = 0x5C…5C`.  That derivation is what
breaks the two-key-nest proof — the derived keys are related, their XOR being
`ipad ⊕ opad` — so HMAC needs the stronger assumption that the compression
function resists related-key attacks. -/
def hmac (H : List Bool → List Bool) (ipad opad : List Bool) (k M : List Bool) :
    List Bool :=
  H (xorBits k opad ++ H (xorBits k ipad ++ M))

/-- **HMAC as a random system**: a uniform key, and every message answered
with its HMAC tag. -/
def hmacSystem {K : Type w} [Fintype K] [Nonempty K]
    (H : List Bool → List Bool) (ipad opad : List Bool) (key : K → List Bool) :
    PFunPDS (List Bool) (List Bool) :=
  uniformKeyed fun k M => hmac H ipad opad (key k) M

/-! ## §8.8 The sponge construction -/

/-- **The sponge's absorbing stage** (Boneh–Shoup §8.8.1): starting from the
all-zero state, XOR each `r`-bit message block (zero-extended to the full
width) into the state and apply the permutation,

  `h ← 0ⁿ;  for i ← 1 to s do h ← π(h ⊕ (mᵢ ‖ 0^c))`.

Only the leading `r` bits — the *rate* — are ever touched by the message; the
trailing `c` bits are the *capacity*, which the attacker can neither see nor
tamper with, and which is what the security bound depends on. -/
def spongeAbsorb (r c : ℕ) (pi : List Bool → List Bool) (blocks : List (List Bool)) :
    List Bool :=
  blocks.foldl (fun h m => pi (xorBits h (m ++ List.replicate c false)))
    (List.replicate (r + c) false)

/-- **The sponge's squeezing stage** (Boneh–Shoup §8.8.1): read off the
leading `r` bits, permute, and repeat, for as many rounds as the requested
output length needs. -/
def spongeSqueeze (r : ℕ) (pi : List Bool → List Bool) : ℕ → List Bool → List Bool
  | 0, _ => []
  | q + 1, h => h.take r ++ spongeSqueeze r pi q (pi h)

/-- **The sponge hash** (Boneh–Shoup §8.8.1): absorb the padded message, then
squeeze `v` bits.  SHA3, SHAKE128 and SHAKE256 are of this form.

Unlike Merkle–Damgård the output length is variable, and the padding needs
only to be injective — a string of the form `10*` suffices, though SHA3 uses
`10*1`. -/
def sponge (r c v : ℕ) (pi : List Bool → List Bool) (pad : List Bool → List (List Bool))
    (M : List Bool) : List Bool :=
  (spongeSqueeze r pi ((v + r - 1) / r) (spongeAbsorb r c pi (pad M))).take v

/-! ## §8.9 Merkle trees -/

/-- One level of a Merkle tree: hash adjacent pairs together, leaving an odd
final node alone. -/
def merkleLevel {Y : Type v} (h₂ : Y → Y → Y) : List Y → List Y
  | a :: b :: rest => h₂ a b :: merkleLevel h₂ rest
  | l => l

/-- Fold a level list up `d` times. -/
def merkleFold {Y : Type v} (h₂ : Y → Y → Y) : ℕ → List Y → List Y
  | 0, l => l
  | d + 1, l => merkleFold h₂ d (merkleLevel h₂ l)

/-- **The Merkle tree hash** (Boneh–Shoup §8.9): hash each of the `n = 2^depth`
items, then hash adjacent pairs up the tree to a single root.

The point of the structure is not the root but the *proofs*: membership of one
item can be checked with `log₂ n` hashes instead of rehashing the whole list,
which is what makes it usable for verifying an executable block by block. -/
def merkleTreeHash {A : Type u} {Y : Type v} (h₁ : A → Y) (h₂ : Y → Y → Y)
    (depth : ℕ) (xs : List A) : List Y :=
  merkleFold h₂ depth (xs.map h₁)

/-- **Recomputing a Merkle root from a proof** (Boneh–Shoup §8.9, eq. 8.16).
Given the item, its zero-based position, and the sibling hashes on the path to
the root, walk upwards — combining on the left or the right according to the
bits of the position — and return the root the proof implies.

Verification compares this against the stored root; Theorem 8.8 says a
collision resistant `h` makes a convincing wrong proof infeasible. -/
def merkleRootFromProof {A : Type u} {Y : Type v} (h₁ : A → Y) (h₂ : Y → Y → Y)
    (x : A) (idx : ℕ) (siblings : List Y) : Y :=
  (siblings.foldl
    (fun st sib => (if st.2 % 2 = 0 then h₂ st.1 sib else h₂ sib st.1, st.2 / 2))
    (h₁ x, idx)).1

/-! ## §8.10.5 HKDF -/

/-- **HKDF's extract stage** (Boneh–Shoup §8.10.5, RFC 5869):
`t ← HMAC(salt, s)`.

With an empty salt this is the book's `HMAC₀`, which §8.10.3 argues can be
treated as a random oracle; a non-secret but independent salt lets the same
step be justified under weaker assumptions. -/
def hkdfExtract (hmacFn : List Bool → List Bool → List Bool) (salt s : List Bool) :
    List Bool :=
  hmacFn salt s

/-- The chained output blocks of HKDF's expand stage:
`zᵢ ← HMAC(t, z_{i-1} ‖ info ‖ Octet(i))`, starting from the empty string. -/
def hkdfBlocks (hmacFn : List Bool → List Bool → List Bool) (t info : List Bool)
    (octet : ℕ → List Bool) : ℕ → ℕ → List Bool → List Bool
  | 0, _, _ => []
  | n + 1, i, prev =>
      let z := hmacFn t (prev ++ info ++ octet i)
      z ++ hkdfBlocks hmacFn t info octet n (i + 1) z

/-- **HKDF's expand stage** (Boneh–Shoup §8.10.5): iterate HMAC as a PRF to
stretch the extracted key to the requested length, with `info` naming the
derived sub-key so that keys for different purposes stay independent.

The book counts `L` in octets; here it is a bit count, since everything in
this file is bit-level. -/
def hkdfExpand (hmacFn : List Bool → List Bool → List Bool) (t info : List Bool)
    (octet : ℕ → List Bool) (q L : ℕ) : List Bool :=
  (hkdfBlocks hmacFn t info octet q 1 []).take L

/-- **HKDF** (Boneh–Shoup §8.10.5): extract, then expand. -/
def hkdf (hmacFn : List Bool → List Bool → List Bool) (salt s info : List Bool)
    (octet : ℕ → List Bool) (q L : ℕ) : List Bool :=
  hkdfExpand hmacFn (hkdfExtract hmacFn salt s) info octet q L

/-! ## §8.11 Security without collision resistance -/

/-- **A TCR hash from a second-preimage resistant one** (Boneh–Shoup §8.11.3,
eq. 8.18): `H_tcr(k, m) := H(k ⊕ m)`.

Theorem 8.12: second-preimage resistance of `H` suffices — a weaker assumption
than collision resistance.  The catch is that the key is as long as the
message, so this is only usable directly on short messages, which is what the
derived hash below fixes. -/
def tcrOfSecondPreimage {T : Type v} (H : List Bool → T) (k m : List Bool) : T :=
  H (xorBits k m)

/-- The 2-adic valuation `ν(i)` — the largest `n` with `2ⁿ ∣ i` — which indexes
which key element the derived TCR hash masks with at step `i`.  The book notes
`ν(i) ≤ 7` for more than 99% of the integers, which is why a key of length
`1 + log₂ L` suffices. -/
def nu (i : ℕ) : ℕ := padicValNat 2 i

/-- The chaining loop of the derived TCR hash, carrying the step index. -/
def derivedTcrChain {T : Type u} {B : Type v} {K : Type w} [AddCommGroup T]
    (h : K → T × B → T) (k₁ : K) (k₂ : ℕ → T) : ℕ → T → List B → T
  | _, t, [] => t
  | i, t, m :: ms => derivedTcrChain h k₁ k₂ (i + 1) (h k₁ (k₂ (nu i) + t, m)) ms

/-- **The derived TCR hash** (Boneh–Shoup §8.11.3, Figure 8.15): extend a
short-input TCR hash to long inputs,

  `t₀ ← IV;  for i ← 1 to s do u ← k₂[ν(i)] ⊕ t_{i-1};  tᵢ ← h(k₁, (u, mᵢ))`.

It looks like Merkle–Damgård but is not: the book stresses that plugging
`h(k₁, ·)` directly into Merkle–Damgård can fail to give a TCR hash.  The
`ν`-indexed masks are what makes the reduction go through, at a key length
logarithmic rather than linear in the message length. -/
def derivedTcrHash {T : Type u} {B : Type v} {K : Type w} [AddCommGroup T]
    (h : K → T × B → T) (iv : T) (k₁ : K) (k₂ : ℕ → T) (blocks : List B) : T :=
  derivedTcrChain h k₁ k₂ 1 iv blocks

end RandomSystems.BonehShoup
