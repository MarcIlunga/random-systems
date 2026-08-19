/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch3StreamCiphers

/-!
# Boneh–Shoup Chapter 4: block ciphers and pseudo-random functions

Boneh–Shoup §4.1–§4.7 (`papers/BonehShoup.pdf`, book pp. 96–160).

A block cipher is a keyed *permutation* of the data block space, so it is
carried here as `K → Equiv.Perm X`: the inverse and the correctness property
come with the `Equiv`, which is also the form `PFunPDS.ofPermDist` consumes.
A PRF is just a keyed function `K → X → Y`, so it needs no wrapper at all —
`uniformKeyed` turns it into the random system of Attack Game 4.2, and
`PFunPDS.URF` is the ideal object that game compares it against.

Declared here: the block cipher and PRF systems (§4.1, §4.4), including the
two-port form for strongly secure block ciphers (§4.1.3); ECB mode (§4.1.4);
the `2E` and `3E` iterated ciphers and the NIST Triple-DES variant (§4.2.3);
the PRG built from a PRF and deterministic counter mode (§4.4.4); the
Luby–Rackoff three-round Feistel cipher (§4.5); the tree construction and its
variable-length form (§4.6); the ideal cipher and ideal permutation models
(§4.7); and Even–Mansour together with `EX` (§4.7.3).

Not declared: §4.2.1's DES and §4.2.4's AES, which are fixed round functions
rather than constructions over an abstract primitive, and §4.3's attacks.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §4.1 Block ciphers -/

/-- **A block cipher** (Boneh–Shoup §4.1), defined over a key space `K` and a
data block space `X`: a key-indexed permutation of `X`.

The book presents it as a cipher `(E, D)` over `(K, X)` in which `E(k, ·)` is
one-to-one onto; carrying it as `Equiv.Perm X` records exactly that, and
supplies `D` and the correctness property definitionally. -/
abbrev BlockCipher (K : Type w) (X : Type u) := K → Equiv.Perm X

namespace BlockCipher

variable {K : Type w} {X : Type u}

/-- A block cipher is in particular a Shannon cipher, with decryption given by
the inverse permutation. -/
def toCipher (E : BlockCipher K X) : Cipher K X X where
  enc k := E k
  dec k := (E k).symm
  dec_enc k x := (E k).symm_apply_apply x

/-- **A block cipher as a random system** (Attack Game 4.1, Experiment 0):
a uniform key, and every data block answered by its encryption.  Only forward
queries are offered, matching the book's basic block-cipher attack game. -/
def system [Fintype K] [Nonempty K] (E : BlockCipher K X) : PFunPDS X X :=
  uniformKeyed (fun k => (E k : X → X))

/-- **A block cipher as a two-port random system** (Boneh–Shoup §4.1.3, the
*strongly secure* block cipher game): the adversary may query in either
direction, `.inl x` for `E(k, x)` and `.inr y` for `D(k, y)`. -/
def strongSystem [Fintype K] [Nonempty K] (E : BlockCipher K X) : PFunPDS (X ⊕ X) X :=
  uniformKeyed fun k q =>
    match q with
    | Sum.inl x => E k x
    | Sum.inr y => (E k).symm y

/-- The block-cipher system is a probability distribution over systems. -/
@[simp] theorem system_isProbDist [Fintype K] [Nonempty K] (E : BlockCipher K X) :
    (E.system).isProbDist :=
  uniformKeyed_isProbDist _

/-- The two-port block-cipher system is a probability distribution over
systems. -/
@[simp] theorem strongSystem_isProbDist [Fintype K] [Nonempty K] (E : BlockCipher K X) :
    (E.strongSystem).isProbDist :=
  uniformKeyed_isProbDist _

end BlockCipher

/-- **The ideal object for a block cipher** (Attack Game 4.1, Experiment 1): a
uniform random permutation of the data block space.  This is CR18's `𝖯`, so
the repository's existing `PFunPDS.URP` is reused rather than redefined. -/
abbrev idealBlockCipher (X : Type u) [Fintype X] : PFunPDS X X :=
  PFunPDS.URP X

/-! ## §4.4 Pseudo-random functions -/

/-- **A pseudo-random function** (Boneh–Shoup §4.4.1): a keyed function from
an input space to an output space.  No wrapper is needed — the content of the
definition is entirely in the attack game, which is not declared here. -/
abbrev PRF (K : Type w) (X : Type u) (Y : Type v) := K → X → Y

/-- **A PRF as a random system** (Attack Game 4.2, Experiment 0): a uniform
key, and every input answered by the keyed function. -/
def prfSystem {K : Type w} {X : Type u} {Y : Type v} [Fintype K] [Nonempty K]
    (F : PRF K X Y) : PFunPDS X Y :=
  uniformKeyed F

/-- The PRF system is a probability distribution over systems. -/
@[simp] theorem prfSystem_isProbDist {K : Type w} {X : Type u} {Y : Type v}
    [Fintype K] [Nonempty K] (F : PRF K X Y) : (prfSystem F).isProbDist :=
  uniformKeyed_isProbDist _

/-- **The ideal object for a PRF** (Attack Game 4.2, Experiment 1): a uniform
random function from the input space to the output space — CR18's `𝖱`. -/
abbrev idealPRF (X : Type u) (Y : Type v) [Fintype (X → Y)] [Nonempty (X → Y)] :
    PFunPDS X Y :=
  PFunPDS.URF (X := X) (Y := Y)

/-! ## §4.1.4 Using a block cipher directly for encryption: ECB mode -/

/-- **ECB mode** (Boneh–Shoup §4.1.4), the `ℓ`-wise ECB cipher derived from a
block cipher: encrypt each data block separately,

  `E'(k, m) := (E(k, m[0]), …, E(k, m[v-1]))`.

The book's Theorem 4.1 recovers semantic security only after restricting the
message space to sequences of *distinct* blocks; no such restriction is
imposed on the declaration, which is the mode as stated. -/
def ecb {K : Type w} {X : Type u} (l : ℕ) (E : BlockCipher K X) :
    Cipher K (StrLE X l) (StrLE X l) where
  enc k m := ⟨m.val.map (E k), by simpa using m.property⟩
  dec k c := ⟨c.val.map (E k).symm, by simpa using c.property⟩
  dec_enc k m := Subtype.ext <| by simp [List.map_map]

/-- **ECB mode as a random system**: a uniform block-cipher key, and every
message answered by its block-wise encryption. -/
def ecbSystem {K : Type w} {X : Type u} [Fintype K] [Nonempty K] (l : ℕ)
    (E : BlockCipher K X) : PFunPDS (StrLE X l) (StrLE X l) :=
  (ecb l E).uniformEncSystem

/-! ## §4.2.3 Strengthening against exhaustive search: the `2E` and `3E`
constructions -/

/-- **The `2E` construction** (Boneh–Shoup §4.2.3.1), double encryption under
two independent keys:

  `E₂((k₁, k₂), x) := E(k₂, E(k₁, x))`.

The book declares this construction *insecure* — the meet-in-the-middle attack
of Theorem 4.2 breaks it in time proportional to `|K|` — and it is declared
here for exactly that reason: it is one of the chapter's constructions. -/
def twoE {K : Type w} {X : Type u} (E : BlockCipher K X) : BlockCipher (K × K) X :=
  fun k => (E k.1).trans (E k.2)

/-- **The `3E` construction** (Boneh–Shoup §4.2.3), triple encryption under
three independent keys:

  `E₃((k₁, k₂, k₃), x) := E(k₃, E(k₂, E(k₁, x)))`.

Instantiated with DES this is **Triple-DES**, with a `3 × 56 = 168`-bit key. -/
def threeE {K : Type w} {X : Type u} (E : BlockCipher K X) : BlockCipher (K × K × K) X :=
  fun k => (E k.1).trans ((E k.2.1).trans (E k.2.2))

/-- **The NIST Triple-DES variant** (Boneh–Shoup §4.2.3), encrypt–decrypt–
encrypt:

  `E₃((k₁, k₂, k₃), x) := E(k₃, D(k₂, E(k₁, x)))`.

The middle inversion is what lets `k₁ = k₂ = k₃` collapse the construction to
a single application of `E`, so that Triple-DES hardware can implement plain
DES. -/
def threeEDE {K : Type w} {X : Type u} (E : BlockCipher K X) : BlockCipher (K × K × K) X :=
  fun k => (E k.1).trans ((E k.2.1).symm.trans (E k.2.2))

/-! ## §4.4.4 Constructing PRGs from PRFs -/

/-- **A PRG built from a PRF** (Boneh–Shoup §4.4.4).  For fixed distinct
inputs `x₁, …, x_ℓ`,

  `G(k) := (F(k, x₁), …, F(k, x_ℓ))`,

a generator with seed space `K` and output space `Y^ℓ`.  Distinctness of the
inputs is a hypothesis of the book's security theorem, not of the
construction, so it is not imposed here. -/
def prgOfPRF {K : Type w} {X : Type u} {Y : Type v} (F : PRF K X Y) (xs : List X) :
    K → List Y :=
  fun k => xs.map (F k)

/-! ## §4.4.4.1 Deterministic counter mode -/

variable {X : Type u} [AddCommGroup X]

/-- The first `n` values of a counter-driven keystream: `mask 0, …, mask (n-1)`.
For deterministic counter mode `mask i` is `E(k, ⟨i⟩ₙ)`. -/
def counterKeystream (mask : ℕ → X) (n : ℕ) : List X :=
  (List.range n).map mask

omit [AddCommGroup X] in
@[simp] theorem length_counterKeystream (mask : ℕ → X) (n : ℕ) :
    (counterKeystream mask n).length = n := by
  simp [counterKeystream]

/-- **Deterministic counter mode** (Boneh–Shoup §4.4.4.1).  With `⟨i⟩ₙ` the
`n`-bit encoding of `i`, carried here as an abstract counter encoding
`ctr : ℕ → X`,

  `E'(k, m) := (E(k, ⟨0⟩ₙ) ⊕ m[0], …, E(k, ⟨v-1⟩ₙ) ⊕ m[v-1])`.

Note that the block cipher's *decryption* algorithm is never used: this is the
stream cipher whose keystream is `E(k, ⟨0⟩ₙ), E(k, ⟨1⟩ₙ), …`, which is how the
book derives the mode (Theorems 4.4, 4.8 and 3.1 in sequence). -/
def deterministicCounterMode {K : Type w} (l : ℕ) (E : BlockCipher K X) (ctr : ℕ → X) :
    Cipher K (StrLE X l) (StrLE X l) where
  enc k m := ⟨xorKeystream (counterKeystream (fun i => E k (ctr i)) m.val.length) m.val, by
    simp only [length_xorKeystream, length_counterKeystream, min_self]
    exact m.property⟩
  dec k c := ⟨unxorKeystream (counterKeystream (fun i => E k (ctr i)) c.val.length) c.val, by
    simp only [length_unxorKeystream, length_counterKeystream, min_self]
    exact c.property⟩
  dec_enc k m := Subtype.ext <| by
    simp only [length_xorKeystream, length_counterKeystream, min_self]
    exact unxorKeystream_xorKeystream _ m.val (by simp)

/-- **Deterministic counter mode as a random system**: a uniform block-cipher
key, and every message answered by its counter-mode encryption. -/
def deterministicCounterModeSystem {K : Type w} [Fintype K] [Nonempty K] (l : ℕ)
    (E : BlockCipher K X) (ctr : ℕ → X) : PFunPDS (StrLE X l) (StrLE X l) :=
  (deterministicCounterMode l E ctr).uniformEncSystem

/-! ## §4.5 Constructing block ciphers from PRFs: Luby–Rackoff -/

/-- **One Feistel round** (Boneh–Shoup §4.5): the round function

  `φₖ : X² → X²,  (a, b) ↦ (b, a ⊕ F(k, b))`.

The book observes that `φₖ` is a permutation of `X²` for every fixed `k`; that
observation is what the `Equiv` records here. -/
def feistelRound {K : Type w} (F : PRF K X X) (k : K) : Equiv.Perm (X × X) where
  toFun p := (p.2, p.1 + F k p.2)
  invFun p := (p.2 - F k p.1, p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- **The Luby–Rackoff block cipher** (Boneh–Shoup §4.5): a three-round
Feistel network over a PRF, with key space `K³` and data block space `X²`,

  `E((k₁, k₂, k₃), ·) = φ_{k₃} ∘ φ_{k₂} ∘ φ_{k₁}`.

Unfolded, on input `(u, v)`: `w ← u ⊕ F(k₁, v)`, `x ← v ⊕ F(k₂, w)`,
`y ← w ⊕ F(k₃, x)`, output `(x, y)`. -/
def lubyRackoff {K : Type w} (F : PRF K X X) : BlockCipher (K × K × K) (X × X) :=
  fun k => (feistelRound F k.1).trans
    ((feistelRound F k.2.1).trans (feistelRound F k.2.2))

/-- The Luby–Rackoff cipher computes the book's three-round schedule: on input
`(u, v)` it returns `(x, y)` for `w = u ⊕ F(k₁, v)`, `x = v ⊕ F(k₂, w)` and
`y = w ⊕ F(k₃, x)`. -/
theorem lubyRackoff_apply {K : Type w} (F : PRF K X X) (k₁ k₂ k₃ : K) (u v : X) :
    lubyRackoff F (k₁, k₂, k₃) (u, v) =
      (v + F k₂ (u + F k₁ v), (u + F k₁ v) + F k₃ (v + F k₂ (u + F k₁ v))) :=
  rfl

/-! ## §4.6 The tree construction: from PRGs to PRFs -/

/-- **The tree evaluation `G*`** (Boneh–Shoup §4.6).  From a PRG
`G : S → S × S`, written `G(s) = (G₀(s), G₁(s))`, walk down the evaluation
tree following the bits of the input:

  `t ← s;  for i ← 1 to n do t ← G_{aᵢ}(t);  output t`.

A `false` bit takes the first component and a `true` bit the second, so the
result is the label of the tree node addressed by the input string. -/
def treeEval {S : Type w} (G : S → S × S) : List Bool → S → S
  | [], s => s
  | a :: as, s => treeEval G as (if a then (G s).2 else (G s).1)

/-- **The tree construction** (Boneh–Shoup §4.6): the PRF with key space `S`,
input space `{0,1}^ℓ` and output space `S` given by `F(s, x) := G*(s, x)`,
the label of the leaf addressed by `x`. -/
def treePRF {S : Type w} (l : ℕ) (G : S → S × S) : PRF S (Str Bool l) S :=
  fun s x => treeEval G x.val s

/-- **The variable length tree construction** (Boneh–Shoup §4.6.1): the same
evaluation on inputs of length *at most* `ℓ`, `F̃(s, x) := G*(s, x)`, which now
addresses internal nodes as well as leaves.

The book stresses that `F̃` is **not** a secure PRF — the extension attack
computes `F̃(s, u ‖ w)` from `F̃(s, u)` — and is secure only against prefix-free
adversaries (Definition 4.5, Theorem 4.11).  It is declared because §6.4.2
builds on it. -/
def variableLengthTreePRF {S : Type w} (l : ℕ) (G : S → S × S) : PRF S (StrLE Bool l) S :=
  fun s x => treeEval G x.val s

/-! ## §4.7 The ideal cipher model -/

/-- **The ideal cipher** (Boneh–Shoup §4.7.1): an independent uniform
permutation of the data block space for every key, offered in the forward
direction.  A query is a key together with a data block. -/
def idealCipher (K : Type w) (X : Type u) [Fintype (K → Equiv.Perm X)]
    [Nonempty (K → Equiv.Perm X)] : PFunPDS (K × X) X :=
  uniformKeyed (K := K → Equiv.Perm X) fun sigma q => sigma q.1 q.2

/-- **The two-sided ideal cipher**: the same object with both `Π` and `Π⁻¹`
queries, which is the interface the book's ideal-cipher adversaries use
(`Q_ic` counts queries to either direction). -/
def idealCipherStrong (K : Type w) (X : Type u) [Fintype (K → Equiv.Perm X)]
    [Nonempty (K → Equiv.Perm X)] : PFunPDS ((K × X) ⊕ (K × X)) X :=
  uniformKeyed (K := K → Equiv.Perm X) fun sigma q =>
    match q with
    | Sum.inl p => sigma p.1 p.2
    | Sum.inr p => (sigma p.1).symm p.2

/-- The ideal cipher is a probability distribution over systems. -/
@[simp] theorem idealCipher_isProbDist (K : Type w) (X : Type u)
    [Fintype (K → Equiv.Perm X)] [Nonempty (K → Equiv.Perm X)] :
    (idealCipher K X).isProbDist :=
  uniformKeyed_isProbDist _

/-! ## §4.7.3 The Even–Mansour block cipher and the `EX` construction -/

/-- **The Even–Mansour block cipher** (Boneh–Shoup §4.7.3, eq. 4.35).  From a
single public permutation `π` of `X`, with key `(P₁, P₂) ∈ X²`:

  `E((P₁, P₂), x) := π(x ⊕ P₁) ⊕ P₂`,   `D((P₁, P₂), y) := π⁻¹(y ⊕ P₂) ⊕ P₁`.

The book analyses this by modelling `π` as a uniform random permutation; both
pads are needed, and the security bound is unchanged when `P₁ = P₂`. -/
def evenMansour (pi : Equiv.Perm X) : BlockCipher (X × X) X :=
  fun k => ((Equiv.addRight k.1).trans pi).trans (Equiv.addRight k.2)

/-- **The `EX` construction** (Boneh–Shoup §4.7.3, eq. 4.37): Even–Mansour
applied to a full block cipher rather than a fixed permutation, with key space
`K × X²`:

  `EX((k, P₁, P₂), x) := E(k, x ⊕ P₁) ⊕ P₂`,
  `DX((k, P₁, P₂), y) := D(k, y ⊕ P₂) ⊕ P₁`.

Applied to DES with `P₁ = P₂` this is **DESX**. -/
def ex {K : Type w} (E : BlockCipher K X) : BlockCipher (K × X × X) X :=
  fun k => ((Equiv.addRight k.2.1).trans (E k.1)).trans (Equiv.addRight k.2.2)

/-- `EX` at a fixed key is the Even–Mansour construction over the permutation
that key selects — the sense in which Theorem 4.14 proves both at once. -/
theorem ex_eq_evenMansour {K : Type w} (E : BlockCipher K X) (k : K) (p₁ p₂ : X) :
    ex E (k, p₁, p₂) = evenMansour (E k) (p₁, p₂) :=
  rfl

end RandomSystems.BonehShoup
