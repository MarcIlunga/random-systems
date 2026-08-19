/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch4BlockCiphers
import RandomSystems.CompatibleMetric

/-!
# Boneh–Shoup Chapter 5: CPA secure ciphers

Boneh–Shoup §5.4–§5.5 (`papers/BonehShoup.pdf`, book pp. 183–205): the generic
hybrid construction, randomized counter mode, CBC mode, and the nonce-based
recasting of all three.

## How randomness enters

The book's §5.4 ciphers must be probabilistic, and §5.5 observes that each is
its §5.4 counterpart with the sampled value `x` "treated as a nonce".  That
observation is the organizing principle here, and it is what keeps randomness
confined to one place:

* the **nonce-based** scheme is the primitive object — a deterministic
  `NonceCipher`, hence an ordinary keyed random system;
* the **randomized** scheme is that object composed in parallel with the
  `coins` resource, under a single converter, `randomizeNonce`.

So exactly one converter in this file touches randomness, and the three
randomized ciphers of §5.4 are three applications of it.  `randomizeNonce` is
a `PFunConverter.ProtocolFn` rather than a `DDC.ofStep`, because it must know
*which* activation it is on in order to draw a fresh coin, and `ofStep`
converters are outer-memoryless.  Its schedule is two inner queries per outer
query — draw the nonce, then encrypt under it — so the round bookkeeping is
just division by two, independently of message length.

Deliberately not covered: §5.4.1 in the book permits the underlying cipher `E`
to be probabilistic (`c ←R E(k, m)`).  `Cipher` here is deterministic, which
is the same restriction §5.5.1 imposes; a probabilistic `E` would need a coin
port of its own.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §5.5 Nonce-based encryption -/

/-- **A nonce-based cipher** (Boneh–Shoup §5.5): encryption and decryption
both take a nonce alongside the key, and correctness holds for every nonce.
Unlike a §5.4 cipher, a nonce-based cipher is deterministic — the caller, not
the algorithm, is responsible for never repeating a nonce. -/
structure NonceCipher (K : Type w) (N : Type u) (M : Type v) (C : Type*) where
  /-- The encryption algorithm `E : K × M × N → C`. -/
  enc : K → N → M → C
  /-- The decryption algorithm `D : K × C × N → M`. -/
  dec : K → N → C → M
  /-- Correctness: decryption under the same key and nonce inverts encryption. -/
  dec_enc : ∀ k n m, dec k n (enc k n m) = m

namespace NonceCipher

variable {K : Type w} {N : Type u} {M : Type v} {C : Type*}

/-- **A nonce-based cipher as a random system**: a key drawn once, and every
nonce/message pair answered with its ciphertext.  This is the object the
book's nonce-based CPA attack game (Attack Game 5.3) talks to. -/
def system (E : NonceCipher K N M C) (keyDist : Dist K) : PFunPDS (N × M) C :=
  keyed keyDist fun k p => E.enc k p.1 p.2

/-- The uniform-key form of `NonceCipher.system`. -/
def uniformSystem [Fintype K] [Nonempty K] (E : NonceCipher K N M C) : PFunPDS (N × M) C :=
  uniformKeyed fun k p => E.enc k p.1 p.2

/-- The nonce-based system is a probability distribution over systems whenever
the key law is. -/
@[simp] theorem isProbDist_system (E : NonceCipher K N M C) (keyDist : Dist K) :
    (E.system keyDist).isProbDist ↔ keyDist.isProbDist :=
  keyed_isProbDist _ _

end NonceCipher

/-! ## Randomizing a nonce-based cipher

The one converter in this development that consumes randomness.  Its inner
resource is `coins ∥ nonceScheme`: port `.inl` supplies fresh nonces, port
`.inr` is the deterministic nonce-based cipher.  On its `k`-th activation the
converter

1. queries the coin resource at index `k-1`, receiving a nonce `x`;
2. queries the nonce-based cipher at `(x, m)`, receiving a ciphertext `c`;
3. answers `(x, c)` — the book's ciphertext, which carries the nonce.

Two inner answers per outer query, so the current round is `|answers| / 2`. -/

/-- **The randomizing converter.**  Turns a nonce-based cipher into the
corresponding §5.4 probabilistic cipher by drawing each nonce from the coin
resource, at the activation index given by `idx`.

Freshness is exactly injectivity of `idx` on the activations that occur: the
coin resource answers repeated indices consistently, so a colliding `idx` is a
nonce reuse.  That is a property of `idx`, not of this converter. -/
def randomizeNonce {Ix : Type u} {M : Type v} {N : Type w} {C : Type*} (idx : ℕ → Ix) :
    PFunConverter.ProtocolFn M (N × C) (Ix ⊕ (N × M)) (N ⊕ C) :=
  fun p =>
    match p.1.getLast? with
    | none => Part.none
    | some m =>
      let round := p.1.length - 1
      let base := 2 * round
      match p.2.length - base with
      | 0 => Part.some (Sum.inl (Sum.inl (idx round)))
      | 1 =>
        match p.2[base]? with
        | some (some (Sum.inl nonce)) => Part.some (Sum.inl (Sum.inr (nonce, m)))
        | _ => Part.none
      | _ =>
        match p.2[base]?, p.2[base + 1]? with
        | some (some (Sum.inl nonce)), some (some (Sum.inr c)) =>
            Part.some (Sum.inr (nonce, c))
        | _, _ => Part.none

/-- **A nonce-based cipher randomized** (the §5.4 shape).  The `coins`
resource in parallel with the nonce-based cipher, under `randomizeNonce`:
each message is answered by `(x, c)` for a freshly drawn `x`. -/
def NonceCipher.randomizedSystem {K N M C Ix : Type*}
    [Fintype (Ix → N)] [Nonempty (Ix → N)]
    (E : NonceCipher K N M C) (keyDist : Dist K) (idx : ℕ → Ix) : PFunPDS M (N × C) :=
  PFunPDS.apply (randomizeNonce idx) (PFunPDS.par (coins Ix N) (E.system keyDist))

/-- A canonical activation index into a `Fin (q+1)`-indexed coin resource.
Indices past the budget wrap around, so a scheme run for more than `q+1`
activations reuses nonces — the budget is visible in the object rather than
hidden in a side condition. -/
def finCoinIndex (q : ℕ) : ℕ → Fin (q + 1) :=
  fun i => ⟨i % (q + 1), Nat.mod_lt _ (Nat.succ_pos q)⟩

/-! ## §5.4.1 / §5.5.1 The generic hybrid construction -/

/-- **The nonce-based generic hybrid cipher** (Boneh–Shoup §5.5.1).  A PRF
`F : K' × X → K` derives a one-time key from the nonce, and the underlying
cipher is run under that key:

  `E'(k', m, x) := E(k, m)` where `k := F(k', x)`,
  `D'(k', c, x) := D(k, c)` where `k := F(k', x)`.

The PRF's output space must be the underlying cipher's key space. -/
def nonceHybrid {K K' M C : Type*} {X : Type*} (E : Cipher K M C) (F : PRF K' X K) :
    NonceCipher K' X M C where
  enc k' x m := E.enc (F k' x) m
  dec k' x c := E.dec (F k' x) c
  dec_enc k' x m := E.dec_enc (F k' x) m

/-- **The generic hybrid construction** (Boneh–Shoup §5.4.1) as a random
system: the nonce-based hybrid with its input `x` drawn fresh per message,

  `E'(k', m) := x ←R X, k ← F(k', x), c ← E(k, m), output (x, c)`. -/
def hybridSystem {K K' M C X Ix : Type*}
    [Fintype (Ix → X)] [Nonempty (Ix → X)] [Fintype K'] [Nonempty K']
    (E : Cipher K M C) (F : PRF K' X K) (idx : ℕ → Ix) : PFunPDS M (X × C) :=
  (nonceHybrid E F).randomizedSystem (Dist.uniform K') idx

/-- **Example 5.2**, the hybrid construction instantiated with the one-time
pad: `E₀(k', m) := x ←R X, output (x, F(k', x) ⊕ m)`.  The book calls the
result a "popular cipher"; it is the generic hybrid over `oneTimePad`. -/
def hybridOneTimePadSystem {K' G X Ix : Type*} [AddCommGroup G]
    [Fintype G] [Fintype (Ix → X)] [Nonempty (Ix → X)] [Fintype K'] [Nonempty K']
    (F : PRF K' X G) (idx : ℕ → Ix) : PFunPDS G (X × G) :=
  hybridSystem (oneTimePad (G := G)) F idx

/-! ## §5.4.2 / §5.5.2 Counter mode -/

variable {Y : Type u} [AddCommGroup Y]

/-- **The counter-mode keystream body** (Boneh–Shoup §5.4.2).  From a starting
point `x` in `ℤ_N`, the `j`-th ciphertext block is

  `c[j] := F(k, x + j mod N) ⊕ m[j]`.

The block cipher's decryption algorithm is never needed; only the PRF is. -/
def ctrCore {K : Type w} {N : ℕ} (F : PRF K (ZMod N) Y) (k : K) (x : ZMod N)
    (m : List Y) : List Y :=
  xorKeystream (counterKeystream (fun j => F k (x + (j : ZMod N))) m.length) m

/-- Counter mode preserves message length. -/
@[simp] theorem length_ctrCore {K : Type w} {N : ℕ} (F : PRF K (ZMod N) Y) (k : K)
    (x : ZMod N) (m : List Y) : (ctrCore F k x m).length = m.length := by
  simp [ctrCore]

/-- **Counter mode as a nonce-based cipher with the IV as the nonce.**  This is
the deterministic body of §5.4.2: given the starting point `x`, encryption is
the keystream XOR.  Randomizing `x` recovers the book's randomized counter
mode; scaling the nonce recovers §5.5.2. -/
def ivCounterMode {K : Type w} {N : ℕ} (l : ℕ) (F : PRF K (ZMod N) Y) :
    NonceCipher K (ZMod N) (StrLE Y l) (StrLE Y l) where
  enc k x m := ⟨ctrCore F k x m.val, by simpa using m.property⟩
  dec k x c := ⟨unxorKeystream
      (counterKeystream (fun j => F k (x + (j : ZMod N))) c.val.length) c.val, by
    simp only [length_unxorKeystream, length_counterKeystream, min_self]
    exact c.property⟩
  dec_enc k x m := Subtype.ext <| by
    simp only [ctrCore, length_xorKeystream, length_counterKeystream, min_self]
    exact unxorKeystream_xorKeystream _ m.val (by simp)

/-- **Randomized counter mode** (Boneh–Shoup §5.4.2) as a random system: a
fresh starting point `x ←R ℤ_N` per message, and the ciphertext `(x, c)`. -/
def randomizedCounterModeSystem {K Ix : Type*} {N : ℕ}
    [Fintype (Ix → ZMod N)] [Nonempty (Ix → ZMod N)] [Fintype K] [Nonempty K]
    (l : ℕ) (F : PRF K (ZMod N) Y) (idx : ℕ → Ix) :
    PFunPDS (StrLE Y l) (ZMod N × StrLE Y l) :=
  (ivCounterMode l F).randomizedSystem (Dist.uniform K) idx

/-- **Nonce-based counter mode** (Boneh–Shoup §5.5.2).  Treating the starting
point directly as a nonce is insecure — two nonces whose counter intervals
overlap reuse keystream — so the nonce `𝓍` is translated to the PRF input
`x := 𝓍·ℓ`.

The book takes the nonce space to be `{0, …, N/ℓ - 1}`, which together with
`ℓ ∣ N` makes the intervals `{𝓍ℓ, …, 𝓍ℓ + ℓ - 1}` disjoint for distinct
nonces.  That restriction is a hypothesis of Theorem 5.6, not of the
construction, so the nonce space here is all of `ℤ_N`. -/
def nonceCounterMode {K : Type w} {N : ℕ} (l : ℕ) (F : PRF K (ZMod N) Y) :
    NonceCipher K (ZMod N) (StrLE Y l) (StrLE Y l) where
  enc k n m := (ivCounterMode l F).enc k (n * (l : ZMod N)) m
  dec k n c := (ivCounterMode l F).dec k (n * (l : ZMod N)) c
  dec_enc k n m := (ivCounterMode l F).dec_enc k (n * (l : ZMod N)) m

/-! ## §5.4.3 / §5.5.3 CBC mode -/

/-- **The CBC chaining** (Boneh–Shoup §5.4.3): `c[j+1] := E(k, c[j] ⊕ m[j])`,
starting from the initial value `c[0]`.  Returns the chain *without* the
initial value; the ciphertext prepends it. -/
def cbcChain {K : Type w} {X : Type u} [AddCommGroup X] (E : BlockCipher K X) (k : K) :
    X → List X → List X
  | _, [] => []
  | prev, mj :: ms =>
      let cj := E k (prev + mj)
      cj :: cbcChain E k cj ms

/-- **The CBC unchaining**: `m[j] := D(k, c[j+1]) ⊕ c[j]`.  Unlike counter
mode, CBC genuinely needs the block cipher's decryption algorithm. -/
def cbcUnchain {K : Type w} {X : Type u} [AddCommGroup X] (E : BlockCipher K X) (k : K) :
    X → List X → List X
  | _, [] => []
  | prev, cj :: cs => ((E k).symm cj - prev) :: cbcUnchain E k cj cs

/-- CBC chaining preserves length. -/
@[simp] theorem length_cbcChain {K : Type w} {X : Type u} [AddCommGroup X]
    (E : BlockCipher K X) (k : K) (prev : X) (m : List X) :
    (cbcChain E k prev m).length = m.length := by
  induction m generalizing prev with
  | nil => rfl
  | cons mj ms ih => simpa [cbcChain] using ih (E k (prev + mj))

/-- CBC unchaining preserves length. -/
@[simp] theorem length_cbcUnchain {K : Type w} {X : Type u} [AddCommGroup X]
    (E : BlockCipher K X) (k : K) (prev : X) (c : List X) :
    (cbcUnchain E k prev c).length = c.length := by
  induction c generalizing prev with
  | nil => rfl
  | cons cj cs ih => simpa [cbcUnchain] using ih cj

/-- **Correctness of CBC** (the verification the book calls easy): unchaining
from the same initial value inverts chaining. -/
theorem cbcUnchain_cbcChain {K : Type w} {X : Type u} [AddCommGroup X]
    (E : BlockCipher K X) (k : K) (prev : X) (m : List X) :
    cbcUnchain E k prev (cbcChain E k prev m) = m := by
  induction m generalizing prev with
  | nil => rfl
  | cons mj ms ih => simpa [cbcChain, cbcUnchain] using ih (E k (prev + mj))

/-- **CBC mode as a nonce-based cipher with the IV as the nonce** — the
deterministic body of §5.4.3. -/
def ivCbcMode {K : Type w} {X : Type u} [AddCommGroup X] (l : ℕ) (E : BlockCipher K X) :
    NonceCipher K X (StrLE X l) (StrLE X l) where
  enc k iv m := ⟨cbcChain E k iv m.val, by simpa using m.property⟩
  dec k iv c := ⟨cbcUnchain E k iv c.val, by simpa using c.property⟩
  dec_enc k iv m := Subtype.ext <| by simpa using cbcUnchain_cbcChain E k iv m.val

/-- **CBC mode** (Boneh–Shoup §5.4.3) as a random system: `c[0] ←R X`, then
the chain, with the ciphertext carrying the initial value.

The book writes the ciphertext as the single sequence `(c[0], …, c[v])` in
`X^{≤ℓ+1} \ X^0`; here it is the pair `(c[0], (c[1], …, c[v]))`, which carries
the same data and makes the initial value's role explicit. -/
def cbcModeSystem {K X Ix : Type*} [AddCommGroup X]
    [Fintype (Ix → X)] [Nonempty (Ix → X)] [Fintype K] [Nonempty K]
    (l : ℕ) (E : BlockCipher K X) (idx : ℕ → Ix) :
    PFunPDS (StrLE X l) (X × StrLE X l) :=
  (ivCbcMode l E).randomizedSystem (Dist.uniform K) idx

/-- **Nonce-based CBC mode, `CBC-ESSIV`** (Boneh–Shoup §5.5.3).  Using the
initial value directly as a nonce is insecure — equal one-block messages under
equal nonces give equal ciphertexts — so the nonce is passed through a second
PRF to produce a pseudo-random IV: `c[0] := F(k', 𝓍)`, under a key `k'`
independent of the block-cipher key `k`.

Because the decryptor recomputes the IV from the nonce, it is not transmitted;
the ciphertext is the chain alone.  This mode is used by full disk encryption
systems such as `dm-crypt`, with the sector number as the nonce. -/
def nonceCbcMode {K K' : Type w} {X : Type u} {Nn : Type*} [AddCommGroup X] (l : ℕ)
    (E : BlockCipher K X) (F : PRF K' Nn X) :
    NonceCipher (K × K') Nn (StrLE X l) (StrLE X l) where
  enc k n m := ⟨cbcChain E k.1 (F k.2 n) m.val, by simpa using m.property⟩
  dec k n c := ⟨cbcUnchain E k.1 (F k.2 n) c.val, by simpa using c.property⟩
  dec_enc k n m := Subtype.ext <| by
    simpa using cbcUnchain_cbcChain E k.1 (F k.2 n) m.val

end RandomSystems.BonehShoup
