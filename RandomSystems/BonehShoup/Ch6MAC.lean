/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch5CPA
import RandomSystems.CBCMAC

/-!
# Boneh–Shoup Chapter 6: message integrity

Boneh–Shoup §6.1–§6.11 (`papers/BonehShoup.pdf`, book pp. 215–245): MACs from
PRFs, the CBC and cascade prefix-free PRFs, the three routes from a prefix-free
secure PRF to a fully secure one (encrypted PRF, prefix-free encodings, CMAC),
and the parallel MAC PMAC₀.

## Reuse

The CBC chaining `F_CBC(k, m)` of §6.4.1 — `t ← 0ⁿ; t ← F(k, aᵢ ⊕ t)` — is
already in this repository as `RandomSystems.CR18.cbcState`, the chaining
Maurer's CBC-MAC theorem is proved about (`RandomSystems/CBCMAC.lean`).  It is
imported and reused rather than restated, so the Boneh–Shoup and Maurer
developments talk about literally the same function.

## Level of abstraction

§6.6 and §6.8 parameterize over an encoding (`pf`, `inj`) rather than fixing
one, and that is followed here.  Where the book does give a concrete bit-level
encoding, `chunk` from the prelude supplies the partitioning; the padding
itself is stated over `List Bool`.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §6.1 Message authentication codes -/

/-- **A message authentication code** (Boneh–Shoup §6.1): a signing algorithm
and a verification algorithm, with the correctness property that a genuine tag
verifies. -/
structure MAC (K : Type w) (M : Type u) (T : Type v) where
  /-- The signing algorithm `S : K × M → T`. -/
  sign : K → M → T
  /-- The verification algorithm `V : K × M × T → {accept, reject}`. -/
  verify : K → M → T → Bool
  /-- Correctness: a tag produced by `sign` is accepted by `verify`. -/
  verify_sign : ∀ k m, verify k m (sign k m) = true

namespace MAC

variable {K : Type w} {M : Type u} {T : Type v}

/-- **The signing oracle of a MAC**: a key drawn once, and every message
answered with its tag.  This is the system the book's Attack Game 6.1
challenger runs. -/
def signSystem (I : MAC K M T) (keyDist : Dist K) : PFunPDS M T :=
  keyed keyDist I.sign

/-- **The signing-and-verification oracle of a MAC** (Boneh–Shoup §6.2): the
adversary may sign, via `.inl m`, or ask for a verdict on a message/tag pair,
via `.inr (m, t)`.  §6.2's theorem — that verification queries do not help —
is exactly a comparison of this system with `signSystem`, and is not made
here. -/
def system (I : MAC K M T) (keyDist : Dist K) : PFunPDS (M ⊕ (M × T)) (T ⊕ Bool) :=
  keyed keyDist fun k q =>
    match q with
    | Sum.inl m => Sum.inl (I.sign k m)
    | Sum.inr p => Sum.inr (I.verify k p.1 p.2)

/-- The signing oracle is a probability distribution over systems whenever the
key law is. -/
@[simp] theorem isProbDist_signSystem (I : MAC K M T) (keyDist : Dist K) :
    (I.signSystem keyDist).isProbDist ↔ keyDist.isProbDist :=
  keyed_isProbDist _ _

end MAC

/-! ## §6.3 Constructing MACs from PRFs -/

/-- **The MAC derived from a PRF** (Boneh–Shoup §6.3): sign by evaluating the
PRF, verify by recomputing and comparing.

This is the construction the whole chapter serves: every later section builds a
PRF on a large message space, and this turns it into a MAC. -/
def macOfPRF {K : Type w} {M : Type u} {T : Type v} [DecidableEq T] (F : PRF K M T) :
    MAC K M T where
  sign := F
  verify k m t := decide (F k m = t)
  verify_sign k m := by simp

/-! ## §6.4 Prefix-free PRFs for long messages -/

variable {X : Type u} [AddCommGroup X]

/-- **The CBC prefix-free secure PRF `F_CBC`** (Boneh–Shoup §6.4.1):

  `t ← 0ⁿ;  for i ← 1 to v do t ← F(k, aᵢ ⊕ t);  output t`.

Two differences from CBC-mode encryption (§5.4.3): no intermediate chaining
value is output, and the initial value is the fixed constant `0ⁿ` rather than
a fresh random IV.

This is `RandomSystems.CR18.cbcState` applied to the round function `F k` —
the same chaining Maurer's Theorem 6.1 is about.

`F_CBC` is only *prefix-free* secure: §6.4.3 gives an existential forgery
against the MAC derived from it directly. -/
def cbcPRF {K : Type w} (l : ℕ) (F : PRF K X X) : PRF K (StrLE X l) X :=
  fun k m => cbcState (F k) m.val

/-- **The cascade prefix-free secure PRF `F*`** (Boneh–Shoup §6.4.2):

  `t ← k;  for i ← 1 to v do t ← F(t, aᵢ);  output t`.

Unlike CBC, the cascade re-keys at every round, so its security carries no
additive birthday term and it stays secure on a small block space.  It has an
even worse extension property than CBC: anyone knowing `F*(k, m)` can compute
`F*(k, m ‖ m')` for any `m'`.

The book notes this generalizes §4.6's variable length tree construction: for
`F` over `(K, {0,1}, K)`, cascade *is* `variableLengthTreePRF` for the PRG
`k ↦ (F(k,0), F(k,1))`. -/
def cascadePRF {K : Type w} {A : Type v} (l : ℕ) (F : PRF K A K) : PRF K (StrLE A l) K :=
  fun k m => m.val.foldl (fun t a => F t a) k

/-! ## §6.5 From prefix-free to fully secure, method 1: the encrypted PRF -/

/-- **The encrypted PRF `EF`** (Boneh–Shoup §6.5, eq. 6.17): run the
prefix-free PRF, then encrypt its short output under a second PRF,

  `EF((k₁, k₂), m) := F(k₂, PF(k₁, m))`.

Theorem 6.5 requires `PF` to be *extendable* as well as prefix-free secure;
both CBC and cascade are. -/
def encryptedPRF {K₁ K₂ : Type w} {M : Type u} {Y T : Type v}
    (PF : PRF K₁ M Y) (F : PRF K₂ Y T) : PRF (K₁ × K₂) M T :=
  fun k m => F k.2 (PF k.1 m)

/-- **ECBC, the encrypted-CBC PRF** (Boneh–Shoup §6.5.1.1): the encrypted PRF
construction applied to CBC, using the *same* underlying PRF `F` for the chain
and for the final encryption, so ECBC is defined over `(K², X^{≤ℓ}, X)`.

This MAC is standardized by ANSI and used in the banking industry. -/
def ecbcPRF {K : Type w} (l : ℕ) (F : PRF K X X) : PRF (K × K) (StrLE X l) X :=
  encryptedPRF (cbcPRF l F) F

/-- **NMAC, the encrypted-cascade PRF** (Boneh–Shoup §6.5.1.2): the encrypted
PRF construction applied to cascade.  The cascade's output lies in the key
space `K`, so a fixed pad `fpad` maps it into the PRF's input space before the
final application — the `t ‖ fpad` step of Figure 6.5b. -/
def nmacPRF {K : Type w} {A : Type v} (l : ℕ) (F : PRF K A K) (fpad : K → A) :
    PRF (K × K) (StrLE A l) K :=
  fun k m => F k.2 (fpad (cascadePRF l F k.1 m))

/-! ## §6.6 From prefix-free to fully secure, method 2: prefix-free encodings -/

/-- **A PRF from a prefix-free encoding** (Boneh–Shoup §6.6): encode the
message so that no encoded input is a prefix of another, then apply the
prefix-free secure PRF,

  `F(k, m) := PF(k, pf(m))`.

Theorem 6.8 is immediate once `pf` is injective with prefix-free image; those
are properties of `pf`, not of this construction. -/
def prefixFreeEncodedPRF {K : Type w} {M : Type u} {A : Type v} {Y : Type*}
    (PF : PRF K (List A) Y) (pf : M → List A) : PRF K M Y :=
  fun k m => PF k (pf m)

/-- **Prefix-free encoding, method 1: prepend the length** (Boneh–Shoup
§6.6.1): `pf(m) := (⟨v⟩, a₁, …, a_v)` where `⟨v⟩` encodes the block count.

The resulting MAC is not a streaming MAC — the sender must know the message
length before starting. -/
def prependLengthEncoding {A : Type v} (encodeLength : ℕ → A) (m : List A) : List A :=
  encodeLength m.length :: m

/-- **Prefix-free encoding, method 2: stop bits** (Boneh–Shoup §6.6.1).  Over
blocks of width `n-1`, append a `0` bit to every block but the last, and a `1`
bit to the last: `pf(m) := ((a₁ ‖ 0), …, (a_{v-1} ‖ 0), (a_v ‖ 1))`.

This *is* a streaming encoding, at the cost of widening the message by `v`
bits and hence of extra evaluations of the underlying PRF. -/
def stopBitsEncoding (m : List (List Bool)) : List (List Bool) :=
  m.dropLast.map (fun a => a ++ [false]) ++ (m.getLast?.map (fun a => a ++ [true])).toList

/-! ## §6.7 From prefix-free to fully secure, method 3: randomized encodings -/

/-- **A PRF from a randomized prefix-free encoding** (Boneh–Shoup §6.7,
eq. 6.21): `F((k, k₁), m) := PF(k, rpf(k₁, m))`.

`rpf(k₁, ·)` need not have prefix-free image, nor even be injective; what
Theorem 6.9 needs is that for distinct messages the encodings are comparable
with probability at most `ε` over the choice of `k₁`. -/
def randomizedPrefixFreeEncodedPRF {K K₁ : Type w} {M : Type u} {A : Type v} {Y : Type*}
    (PF : PRF K (List A) Y) (rpf : K₁ → M → List A) : PRF (K × K₁) M Y :=
  fun k m => PF k.1 (rpf k.2 m)

/-- **The simple randomized prefix-free encoding** (Boneh–Shoup §6.7): XOR the
key into the final block,

  `rpf(k, (a₁, …, a_v)) := (a₁, …, a_{v-1}, a_v ⊕ k)`.

The book shows this is a randomized `1/|X|`-prefix-free encoding. -/
def simpleRpf (k : X) (m : List X) : List X :=
  m.dropLast ++ (m.getLast?.map (fun a => a + k)).toList

/-! ## §6.8 Converting a block-wise PRF to a bit-wise PRF -/

/-- **The bit-wise PRF derived from a block-wise one** (Boneh–Shoup §6.8):
`F_bit(k, x) := F(k, inj(x))` for an injective `inj : {0,1}^{≤nℓ} → X^{≤ℓ+1}`.

The book stresses that any such `inj` must sometimes add a dummy block, since
`{0,1}^{≤nℓ}` is larger than `X^{≤ℓ}` — which is the inefficiency CMAC
removes. -/
def bitwisePRF {K : Type w} {M : Type u} {A : Type v} {Y : Type*}
    (F : PRF K (List A) Y) (inj : M → List A) : PRF K M Y :=
  fun k x => F k (inj x)

/-- **The standard injective padding** (Boneh–Shoup §6.8, Figure 6.7): append
a `1` bit and then `0` bits up to the next multiple of the block size,
appending a whole block `1 ‖ 0^{n-1}` when the length is already a multiple.

Appending `1 ‖ 0*` rather than `0*` is what makes it injective: scanning from
the right past the zeros and the first one recovers the message. -/
def onePadBlocks (n : ℕ) (m : List Bool) : List (List Bool) :=
  chunk n (m ++ true :: List.replicate (n - m.length % n - 1) false)

/-! ## §6.9 / §6.10 ANSI CBC-MAC and CMAC -/

/-- **ANSI CBC-MAC** (Boneh–Shoup §6.9): ECBC over a padding of the message,
with the final tag truncated.

The ANSI X9.9/X9.19 and ISO 8731-1/9797 standards specify this with DES as the
underlying PRF, the §6.8 padding, and `trunc` taking the leading `w` bits for
`w ∈ {32, 48, 64}`.  Truncation is harmless for the PRF but costs a `1/2^w`
term in the derived MAC's security, so the smaller `w` is, the weaker the MAC.

`pad` and `trunc` are parameters because truncation is a map out of the block
space, which the abstract block type `X` does not name. -/
def ansiCbcMac {K : Type w} {M T : Type u} (F : PRF K X X) (pad : M → List X)
    (trunc : X → T) : PRF (K × K) M T :=
  fun k m =>
    trunc (encryptedPRF (fun k₁ (x : M) => cbcState (F k₁) (pad x)) F k m)

/-- **CMAC's randomized prefix-free encoding** (Boneh–Shoup §6.10).  The
message is partitioned into blocks; the last block is masked with `k₁` when
the original length was a positive multiple of the block size, and with `k₂`
otherwise — after the `1 ‖ 0*` padding that made it a whole block.

The two sub-keys are what let CMAC avoid appending a dummy block: they resolve
collisions between a message whose length is already a multiple of the block
size and a shorter message padded up to one.  `blocks` reports the partition
together with that "was already a whole number of blocks" flag. -/
def cmacRpf {M : Type u} (blocks : M → List X × Bool) (k : X × X) (m : M) : List X :=
  let parts := blocks m
  let mask := if parts.2 then k.1 else k.2
  parts.1.dropLast ++ (parts.1.getLast?.map (fun a => a + mask)).toList

/-- **The CMAC PRF** (Boneh–Shoup §6.10, Table 6.1): CBC chaining under `k₀`
over CMAC's randomized encoding, truncated to `w` symbols.

Sub-key generation derives `(k₀, k₁, k₂)` from a single key `k` by doubling in
`GF(2ⁿ)`; that derivation makes the three keys *dependent*, which is outside
the book's own randomized-encoding framework (the book cites a more intricate
analysis).  It is therefore left as the parameter `subkeys` rather than fixed
here. -/
def cmacPRF {K : Type w} {M : Type u} (F : PRF K X X)
    (subkeys : K → X × X) (blocks : M → List X × Bool) (k₀ : K) (k : K) : M → X :=
  fun m => cbcState (F k₀) (cmacRpf blocks (subkeys k) m)

/-! ## §6.11 PMAC: a parallel MAC -/

/-- **PMAC₀, a parallel MAC** (Boneh–Shoup §6.11).  Every block is masked by a
multiple of the key and fed to `F₁` independently; the results are XORed and
the sum is passed through `F₂`:

  `t ← ⊕ᵢ F₁(k₁, aᵢ + i·k)`,  output `F₂(k₂, t)`.

Unlike ECBC, CMAC and NMAC, block `i` does not wait for block `i-1`, so each
processor can compute `aᵢ + i·k` and apply `F₁` on its own. -/
def pmac0 {K₁ K₂ : Type w} {Y : Type u} {Z : Type v} [AddCommGroup Y] {p : ℕ}
    (F₁ : PRF K₁ (ZMod p) Y) (F₂ : PRF K₂ Y Z) :
    PRF (ZMod p × K₁ × K₂) (List (ZMod p)) Z :=
  fun key m =>
    F₂ key.2.2
      ((m.mapIdx fun i a => F₁ key.2.1 (a + ((i + 1 : ℕ) : ZMod p) * key.1)).foldl
        (· + ·) 0)

/-! ## The MACs as random systems

Each PRF above becomes a MAC by `macOfPRF` and a random system by
`MAC.signSystem`; the composite is spelled out here for the two headline
constructions so that the objects the chapter's theorems range over are
present by name. -/

/-- **The ECBC MAC as a random system**: a uniform key pair, and every message
answered with its encrypted-CBC tag. -/
def ecbcSystem {K : Type w} [Fintype K] [Nonempty K] [DecidableEq X] (l : ℕ)
    (F : PRF K X X) : PFunPDS (StrLE X l) X :=
  (macOfPRF (ecbcPRF l F)).signSystem (Dist.uniform (K × K))

/-- **The PMAC₀ MAC as a random system**: a uniform key triple, and every
block sequence answered with its parallel tag. -/
def pmac0System {K₁ K₂ : Type w} {Y : Type u} {Z : Type v} [AddCommGroup Y] {p : ℕ}
    [NeZero p] [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂] [DecidableEq Z]
    (F₁ : PRF K₁ (ZMod p) Y) (F₂ : PRF K₂ Y Z) : PFunPDS (List (ZMod p)) Z :=
  (macOfPRF (pmac0 F₁ F₂)).signSystem (Dist.uniform (ZMod p × K₁ × K₂))

end RandomSystems.BonehShoup
