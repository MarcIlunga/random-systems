/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Prelude

/-!
# Boneh–Shoup Chapter 2: Shannon ciphers as random systems

Boneh–Shoup §2.1–§2.2 (`papers/BonehShoup.pdf`, book pp. 4–15).  A Shannon
cipher over `(K, M, C)` is a pair of algorithms `(E, D)` satisfying the
correctness property `D k (E k m) = m`; §2.2.1's *computational* cipher adds a
key-generation algorithm and a security parameter on top of the same syntax.

The random system attached to a cipher is its **encryption oracle**: draw the
key once, then answer each message with its ciphertext.  That single object is
what the book's Attack Game 2.1 talks to, and it is all this file declares —
perfect security (Def. 2.1), semantic security (Def. 2.2) and the theorems
around them are deliberately absent.

The four ciphers of §2.1.1 appear as Examples 2.1–2.4.  Examples 2.1 and 2.4
are the *same* construction read in two different groups, so they are declared
once, generically, over an `AddCommGroup`: the bit-string one-time pad is the
case `G = Fin L → ZMod 2` (where `+` is `⊕`), and the additive one-time pad
mod `n` is the case `G = ZMod n`.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## §2.1.1 The syntax of a Shannon cipher -/

/-- **A Shannon cipher** (Boneh–Shoup §2.1.1), defined over a key space `K`, a
message space `M` and a ciphertext space `C`: an encryption algorithm, a
decryption algorithm, and the correctness property tying them together. -/
structure Cipher (K : Type w) (M : Type u) (C : Type v) where
  /-- The encryption algorithm `E : K × M → C`. -/
  enc : K → M → C
  /-- The decryption algorithm `D : K × C → M`. -/
  dec : K → C → M
  /-- Correctness: `D(k, E(k, m)) = m` for every key and message. -/
  dec_enc : ∀ k m, dec k (enc k m) = m

namespace Cipher

variable {K : Type w} {M : Type u} {C : Type v}

/-- **The encryption oracle of a cipher.**  Draw a key from `keyDist` once,
then answer every message with its encryption.  This is the random system the
book's Attack Game 2.1 challenger runs. -/
def encSystem (E : Cipher K M C) (keyDist : Dist K) : PFunPDS M C :=
  keyed keyDist E.enc

/-- **The encryption oracle under a uniform key** — the form used throughout
Chapter 2, where the key is always drawn uniformly from the key space. -/
def uniformEncSystem [Fintype K] [Nonempty K] (E : Cipher K M C) : PFunPDS M C :=
  uniformKeyed E.enc

/-- **The decryption oracle of a cipher**, for the settings (from Chapter 9
onwards) where the adversary is given decryption access as well. -/
def decSystem (E : Cipher K M C) (keyDist : Dist K) : PFunPDS C M :=
  keyed keyDist E.dec

/-- **Rekeying a cipher**: precompose encryption and decryption with a map
into the key space.  The book uses this shape whenever a key is *derived*
rather than sampled directly — most immediately in §3.2, where a stream
cipher is the variable length one-time pad rekeyed through a PRG. -/
def rekey {K' : Type*} (E : Cipher K M C) (φ : K' → K) : Cipher K' M C where
  enc k := E.enc (φ k)
  dec k := E.dec (φ k)
  dec_enc k := E.dec_enc (φ k)

/-- The encryption oracle is a probability distribution over systems whenever
the key law is. -/
@[simp] theorem isProbDist_encSystem (E : Cipher K M C) (keyDist : Dist K) :
    (E.encSystem keyDist).isProbDist ↔ keyDist.isProbDist :=
  keyed_isProbDist keyDist E.enc

/-- The uniform-key encryption oracle is a probability distribution over
systems. -/
@[simp] theorem isProbDist_uniformEncSystem [Fintype K] [Nonempty K]
    (E : Cipher K M C) : (E.uniformEncSystem).isProbDist :=
  uniformKeyed_isProbDist E.enc

end Cipher

/-! ## Keystream XOR

Examples 2.2 and the §3.2 stream cipher share one operation: XOR a message
against a prefix of a keystream.  `List.zipWith` truncates to the shorter
list, which is precisely the book's `k[0 .. ℓ - 1]` truncation. -/

variable {G : Type u} [AddCommGroup G]

/-- **Encrypt against a keystream**: `ks[0 .. |m| - 1] ⊕ m`, the book's
`E(k, m) := k[0 .. ℓ - 1] ⊕ m` for a message of length `ℓ`. -/
def xorKeystream (ks m : List G) : List G :=
  List.zipWith (· + ·) ks m

/-- **Decrypt against a keystream**: `ks[0 .. |c| - 1] ⊕ c`, written as
subtraction so that it inverts `xorKeystream` in any abelian group, not only
in one of characteristic two. -/
def unxorKeystream (ks c : List G) : List G :=
  List.zipWith (fun k c => c - k) ks c

/-- Keystream encryption preserves length when the keystream is long enough. -/
@[simp] theorem length_xorKeystream (ks m : List G) :
    (xorKeystream ks m).length = min ks.length m.length :=
  List.length_zipWith

/-- Keystream decryption preserves length in the same way. -/
@[simp] theorem length_unxorKeystream (ks c : List G) :
    (unxorKeystream ks c).length = min ks.length c.length :=
  List.length_zipWith

/-- **Correctness of keystream encryption** (the verification the book leaves
to the reader in Example 2.2): a message no longer than the keystream is
recovered exactly. -/
theorem unxorKeystream_xorKeystream (ks m : List G) (h : m.length ≤ ks.length) :
    unxorKeystream ks (xorKeystream ks m) = m := by
  induction ks generalizing m with
  | nil =>
      have hm : m = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp (by simpa using h))
      simp [xorKeystream, unxorKeystream, hm]
  | cons k ks ih =>
      cases m with
      | nil => rfl
      | cons x xs =>
          simp only [xorKeystream, unxorKeystream, List.zipWith_cons_cons,
            add_sub_cancel_left, List.cons.injEq, true_and]
          exact ih xs (by simpa using h)

/-! ## §2.1.1, Examples 2.1 and 2.4: the one-time pad -/

/-- **The one-time pad** (Boneh–Shoup Examples 2.1 and 2.4).  Keys, messages
and ciphertexts all live in one finite abelian group `G`; encryption is
translation by the key.

* Example 2.1, the bit-string one-time pad over `K = M = C = {0,1}^L`, is the
  case `G = Fin L → ZMod 2`, where the group law is bitwise `⊕`.
* Example 2.4, the additive one-time pad mod `n`, is the case `G = ZMod n`. -/
def oneTimePad : Cipher G G G where
  enc k m := k + m
  dec k c := c - k
  dec_enc _ _ := by simp

/-- **The one-time pad as a random system**: a uniform key `k ←R G`, and every
message answered by `k + m`. -/
def oneTimePadSystem [Fintype G] : PFunPDS G G :=
  letI : Nonempty G := ⟨0⟩
  (oneTimePad (G := G)).uniformEncSystem

/-! ## §2.1.1, Example 2.2: the variable length one-time pad -/

/-- **The variable length one-time pad** (Boneh–Shoup Example 2.2).  The key
is a fixed-length keystream and the message is a string of at most that
length; encryption XORs the message against the matching prefix of the key.

The book's spaces are `K = {0,1}^L` and `M = C = {0,1}^{≤L}`; here the key is
a length-`L` list over `G` and the message space is the subtype of lists no
longer than the key, which is exactly `{0,1}^{≤L}`. -/
def variableLengthOneTimePad (L : ℕ) : Cipher (Str G L) (StrLE G L) (StrLE G L) where
  enc ks m := ⟨xorKeystream ks.val m.val, by
    simp only [length_xorKeystream, ks.property]
    exact le_trans (min_le_right _ _) m.property⟩
  dec ks c := ⟨unxorKeystream ks.val c.val, by
    simpa only [unxorKeystream, List.length_zipWith] using
      le_trans (min_le_right _ _) c.property⟩
  dec_enc ks m := Subtype.ext <| by
    have hlen : m.val.length ≤ ks.val.length := by rw [ks.property]; exact m.property
    simpa using unxorKeystream_xorKeystream ks.val m.val hlen

/-! ## §2.1.1, Example 2.3: the substitution cipher -/

/-- **The substitution cipher** (Boneh–Shoup Example 2.3).  The key is a
permutation of the symbol alphabet `Σ`, applied component-wise to the message.

The book fixes the message space to `Σ^L`; taking it to be `List Σ` declares
the same component-wise construction uniformly in the length, and the book's
space is recovered by restricting to lists of length `L`. -/
def substitutionCipher (Sigma : Type u) : Cipher (Equiv.Perm Sigma) (List Sigma) (List Sigma) where
  enc k m := m.map k
  dec k c := c.map k.symm
  dec_enc k m := by simp [List.map_map]

/-- **The substitution cipher as a random system**: a uniform permutation of
the alphabet, applied symbol-wise to every queried message. -/
def substitutionCipherSystem (Sigma : Type u) [Fintype Sigma] [DecidableEq Sigma] :
    PFunPDS (List Sigma) (List Sigma) :=
  letI : Nonempty (Equiv.Perm Sigma) := ⟨Equiv.refl Sigma⟩
  (substitutionCipher Sigma).uniformEncSystem

/-! ## §2.2.1: computational ciphers

A computational cipher (Def. 2.9) is a Shannon cipher whose key is produced by
a key-generation algorithm and whose spaces are indexed by a security
parameter.  This repository's random systems are not asymptotic, so the
security parameter has no counterpart here; what does carry over is that the
key need not be uniform.  That is already `Cipher.encSystem`, which takes an
arbitrary key law — `Cipher.uniformEncSystem` is the special case where key
generation samples uniformly. -/

end RandomSystems.BonehShoup
