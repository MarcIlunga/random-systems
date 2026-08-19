/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch2Encryption

/-!
# Boneh–Shoup Chapter 3: pseudo-random generators and stream ciphers

Boneh–Shoup §3.1–§3.4 (`papers/BonehShoup.pdf`, book pp. 45–62).  A PRG is a
deterministic map `G : S → R` from a seed space to an output space; the random
system it names is the challenger of Attack Game 3.1, which samples a seed and
publishes `G(s)`.  Its ideal counterpart, Experiment 1 of the same game, is
the system that publishes a uniform element of `R`.  Both are declared; the
game relating them is not.

Also declared: the stream cipher of §3.2, and the two PRG composition
constructions of §3.4 — the `n`-wise parallel composition (§3.4.1) and the
`n`-wise sequential composition of Blum and Micali (§3.4.2).

Not declared: §3.6–§3.9 (Salsa/ChaCha, linear congruential and subset-sum
generators, the DVD cipher, RC4).  Those are concrete round functions rather
than constructions over an abstract primitive, and carry no random-system
structure that is not already in `prgSystem`.  §3.12's bit-commitment protocol
is a two-party protocol rather than a symmetric primitive.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §3.1 Pseudo-random generators -/

/-- **A PRG as a random system** (Boneh–Shoup §3.1, Attack Game 3.1,
Experiment 0).  Sample a seed `s ←R S` and publish `G(s)`.

The system has a one-element query alphabet because a PRG is used *once*: the
adversary receives the output and nothing more.  Repeated activations are
answered with the same value, since the seed is drawn once — which is the
random-system reading of "the challenger computes `r ← G(s)` and sends `r`". -/
def prgSystem {S : Type w} {R : Type v} [Fintype S] [Nonempty S] (G : S → R) :
    PFunPDS Unit R :=
  uniformKeyed (fun s (_ : Unit) => G s)

/-- **The ideal counterpart of a PRG** (Attack Game 3.1, Experiment 1): the
system that publishes a uniform element of `R`, independent of everything
else.  A PRG is secure exactly when this system and `prgSystem G` are hard to
tell apart; that comparison is not made here. -/
def uniformSource (R : Type v) [Fintype R] [Nonempty R] : PFunPDS Unit R :=
  uniformKeyed (K := R) (fun r (_ : Unit) => r)

/-- The PRG system is a probability distribution over systems. -/
@[simp] theorem prgSystem_isProbDist {S : Type w} {R : Type v} [Fintype S] [Nonempty S]
    (G : S → R) : (prgSystem G).isProbDist :=
  uniformKeyed_isProbDist _

/-- The uniform source is a probability distribution over systems. -/
@[simp] theorem uniformSource_isProbDist (R : Type v) [Fintype R] [Nonempty R] :
    (uniformSource R).isProbDist :=
  uniformKeyed_isProbDist _

/-! ## §3.2 Stream ciphers: encryption with a PRG -/

/-- **The stream cipher constructed from a PRG** (Boneh–Shoup §3.2).  For a
PRG `G : S → {0,1}^L` and a message of length `v ≤ L`,

  `E(s, m) := G(s)[0 .. v-1] ⊕ m`.

This is definitionally the variable length one-time pad of Example 2.2 with
its key produced by `G` instead of sampled uniformly — which is exactly the
content of the book's Theorem 3.1, before any security is claimed. -/
def streamCipher {A : Type u} [AddCommGroup A] {S : Type w} (L : ℕ) (G : S → Str A L) :
    Cipher S (StrLE A L) (StrLE A L) :=
  (variableLengthOneTimePad (G := A) L).rekey G

/-- **The stream cipher as a random system**: a uniform seed, and every
message answered by its encryption under the induced keystream. -/
def streamCipherSystem {A : Type u} [AddCommGroup A] {S : Type w} [Fintype S] [Nonempty S]
    (L : ℕ) (G : S → Str A L) : PFunPDS (StrLE A L) (StrLE A L) :=
  (streamCipher L G).uniformEncSystem

/-! ## §3.4.1 A parallel construction -/

/-- **The `n`-wise parallel composition of a PRG** (Boneh–Shoup §3.4.1):
`G'` applies `G` to `n` independent seeds and concatenates the outputs,

  `G'(s₁, …, sₙ) := (G(s₁), …, G(sₙ))`,

so `G'` is defined over `(Sⁿ, Rⁿ)`.  The book calls `n` the *repetition
parameter*. -/
def prgParallel {S : Type w} {R : Type v} (n : ℕ) (G : S → R) :
    (Fin n → S) → (Fin n → R) :=
  fun seeds i => G (seeds i)

/-- **The parallel composition as a random system**: `n` uniform seeds, and
the concatenated outputs published in one activation. -/
def prgParallelSystem {S : Type w} {R : Type v} [Fintype S] [Nonempty S] (n : ℕ) (G : S → R) :
    PFunPDS Unit (Fin n → R) :=
  prgSystem (prgParallel n G)

/-! ## §3.4.2 A sequential construction: the Blum–Micali method -/

/-- **The Blum–Micali iteration** (Boneh–Shoup §3.4.2).  Starting from a seed
`s₀ := s`, repeatedly apply `G : S → R × S`, emitting the `R` component and
carrying the `S` component forward:

  `for i ← 1 to n do (rᵢ, sᵢ) ← G(sᵢ₋₁)`,

returning `(r₁, …, rₙ)` together with the final state `sₙ`. -/
def prgSequential {S : Type w} {R : Type v} (G : S → R × S) : ℕ → S → List R × S
  | 0, s => ([], s)
  | n + 1, s =>
      let step := G s
      let rest := prgSequential G n step.2
      (step.1 :: rest.1, rest.2)

/-- The Blum–Micali iteration emits exactly `n` outputs, so that
`prgSequential G n` is a map `S → Rⁿ × S` as the book states. -/
@[simp] theorem length_prgSequential {S : Type w} {R : Type v} (G : S → R × S) (n : ℕ) (s : S) :
    (prgSequential G n s).1.length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa [prgSequential] using ih (G s).2

/-- **The `n`-wise sequential composition of a PRG** (Boneh–Shoup §3.4.2): the
Blum–Micali iteration read as a PRG `G'` over `(S, Rⁿ × S)`.

The book's headline special case: for `G` over `({0,1}^ℓ, {0,1}^{t+ℓ})`, read
the output space as `{0,1}^t × {0,1}^ℓ`, and `G'` stretches `ℓ` bits to
`nt + ℓ` bits — an arbitrary amount of stretch from a generator that stretches
only a little. -/
def prgSequentialComposition {S : Type w} {R : Type v} (n : ℕ) (G : S → R × S) :
    S → List R × S :=
  prgSequential G n

/-- **The sequential composition as a random system**: a uniform seed, and the
whole emitted sequence together with the final state published in one
activation. -/
def prgSequentialSystem {S : Type w} {R : Type v} [Fintype S] [Nonempty S] (n : ℕ)
    (G : S → R × S) : PFunPDS Unit (List R × S) :=
  prgSystem (prgSequentialComposition n G)

end RandomSystems.BonehShoup
