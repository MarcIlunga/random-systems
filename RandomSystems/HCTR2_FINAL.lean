/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.HTechnique.Derivation
import RandomSystems.HTechnique.StrongPRP
import RandomSystems.HTechnique.TweakablePRP
import RandomSystems.HTechnique.GF2Field

/-!
# HCTR2 (ePrint 2021/1441) — formalized section by section

A re-formalization of *Length-preserving encryption with HCTR2*
(Crowley–Huckleberry–Biggers), built one paper section at a time, each Lean
object placed opposite the paper text it transcribes.  Material is copied from
`RandomSystems/HCTR2.lean` and `RandomSystems/HTechnique/HCTR2Paper.lean`
wherever those already say the right thing.

## File convention

Paper-facing declarations are placed under the section in which the paper
introduces them.  A docstring says explicitly when a declaration transcribes a
paper definition, display, property, or theorem.  Declarations under `Facts`
are Lean support unless their own docstring identifies a paper statement; they
must not silently acquire a paper attribution merely because a later proof uses
them.

Some paper sections are conceptual rather than definitional.  In particular,
§1 contributes motivation but no mathematical object, while §3.3 contributes a
generic theorem about two random variables.  The latter is reused from the
carrier-independent Random Systems layer instead of being redefined for HCTR2
transcripts.

## The layering

The existing development makes `BlockBits : F ≃ BitVec n` a hypothesis of the
*whole model*, so field elements appear in the **message type**
(`bitMsg = F × (Fin ℓ → F) × BitVec r`, `RandomSystems/HCTR2.lean:297`).  That is
backwards: HCTR2's Figures 2–3 use only XOR and the block cipher on messages;
field multiplication occurs solely inside POLYVAL.  The cost in the old file is
that one message passes through six shapes — `Sigma bitMsgL`, `bitMsg`,
`BitTailS`, `List F`, `ℕ → F`, `BitVec n` — each re-encoding paying its own
injectivity and congruence lemmas, several dependent (`padMsg_inj` returns an
`HEq`, `RandomSystems/HTechnique/HCTR2Paper.lean:1647`).

Three layers, no lower one mentioning a higher:

| layer | owns | mentions |
|---|---|---|
| **1. bits** | `{0,1}*`, `\|X\|`, `λ`, `‖`, `⊕`, `X[a;l]`, `bin`, `pad`, `𝒯`, `ℳ` | nothing |
| **1.5 blocks** | `chunk : BitVec (n*m) ≃ (Fin m → BitVec n)` | layer 1 |
| **2. field** | `GF(2ⁿ)`, POLYVAL, the hash | layers 1–1.5 |

`BlockBits` is thereby demoted from a hypothesis of the model to a hypothesis of
the *hash instantiation*.

Length stays a **type index** throughout (`Σ k, BitVec k`), so a length-preserving
permutation is one permutation per index and `|π(T,M)| = |M|` is structural, not a
side condition.  This is a re-indexing of the old design, not a weakening: the old
`Fin (L*n)` index is already in bijection with the length via `k = n(1+ℓ)+r`.

## Status

* §1 Introduction — scope commentary only; it introduces no formal object.
* §2.1 Notation — `Bits`.
* §2.2 Polynomial hash function — `Hash`.
* §2.3 XCTR mode — `XCTR`.
* §2.4 HCTR2 (Figures 2–3) — `HCTR2`.
* §3.1 Definitions (PDS objects, advantages) — `Sec`.
* §3.2 Hash function — `Poly`: `poly`, `d`, `polyStr`, `Hpoly`,
  **all four** structural properties of the map: 1 (injectivity), 2 (never `0` nor
  `xⁿh`), 3 (zero constant term) and 4 (`deg = d(T,M)`, sharper than the paper's
  `≤`).  `Poly.GF128.blockField` is the paper's `n = 128` instantiation, so none
  of it is vacuous.  `Facts.H_eq_eval` connects §2.2's value to it — `H_h̄(T,M)` is
  this polynomial at `h = x⁻ⁿh̄` — and `Facts.card_keys_root_le` is the root count
  the probabilities need.  **Properties 1–3 of `H_h̄` are complete**, as
  `Poly.Facts.prop1/prop2/prop3` in the closing section — after Appendix A,
  because Property 2 consumes injectivity.
* Appendix A Injectivity of `H` onto polynomials — `AppendixA`: `GetTM`, and
  §3.2's property 1 as `AppendixA.Facts.Hpoly_injective`.
* §3.3 H-coefficient technique — the paper's zero-defect, two-cell argument is
  `RandomSystems.δ_hTechnique_le_on_good_of_bad_le`.  It is stated for arbitrary
  distributions; transcript laws and augmented transcript laws are merely later
  instantiations.  No HCTR2-specific H theorem is introduced here.
* §3.4 Main lemma — complete through `main_lemma_paper`: good observations,
  exhaustive bad-transcript collision fibres, table summation, and the final
  raw-transcript advantage bound.  There are no admissions in this file.
* §3.5 — the unconditional p. 17 theorem is scaffolded top-down and is
  intentionally red.  It fixes one Maurer distinguisher, normalizes it without
  changing the endpoint bracket, telescopes the three signed brackets, and
  exposes substitution, the main lemma bridge, PRP–RND, and arithmetic as the
  missing named steps.
* §3.6 onwards — to come.
-/

namespace RandomSystems.HCTR2Final

/-! ## Paper §1 — Introduction (pp. 1–3)

Section 1 motivates a tweakable, length-preserving super-pseudorandom
permutation and summarizes HCTR2's specification, performance, and security
claims.  It introduces no definition used by the proof, so there is deliberately
no Lean declaration corresponding solely to §1.

The mathematical content announced there is realized where the paper defines
it: the bit-level mode in §§2.1–2.4, the security experiments in §3.1, the hash
properties in §3.2, and the generic H argument in §3.3.  Implementation-speed,
interoperability, and patent statements are outside this formal proof. -/

/-! ## Paper §2.1 — Notation (pp. 3–4)

Layer 1: no definition here mentions a field.

Bit order, fixed once: the paper indexes a string from the left with `X[a; l]` at
0-based `a` and reads blocks little-endian, so **paper index `a` = `BitVec` LSB
index `a`**.  Lean's `BitVec.append x y` puts `x` in the *high* bits — the
opposite of `X‖Y` — so `cat` fixes the paper's order and width and `++` never
appears in a statement.  `Facts.getLsbD_cat` is that convention as a theorem.

Notation, both scoped: `x ∥ y` for `X‖Y`, `x[a; l]` for `X[a; l]`.  The
concatenation bar is **U+2225 `∥`, not U+2016 `‖`**: Mathlib binds `‖` as the
delimiter of `‖x‖`, and the parser treats a `‖` in term position as *opening* a
norm without backtracking to an infix reading, so `infixl " ‖ "` both fails to
parse `x ‖ y` and breaks ordinary `‖r‖` in the same file.  `∥` is an infix in
Mathlib (`Parallel`), so the readings disambiguate by elaboration.  `x[a; l]`
forbids whitespace before the bracket (`noWs`), exactly as `getElem` does —
without that, a list literal in argument position (`POLYVAL u h []`) is parsed as
the start of a substring. -/

namespace Bits

/-- `{0,1}^k` — bit strings of length `k`.  `{0,1}*` is the dependent sum
`Σ k, Str k`; length is the index, never a function. -/
abbrev BitString (k : ℕ) : Type := BitVec k

/-- `λ` — the empty string, `|λ| = 0`. -/
def empty_bit_string : BitString 0 := 0

-- `BitVec` carries no `Fintype` from Mathlib; §3.1's transcript spaces need one.
instance instFintypeStr (k : ℕ) : Fintype (BitString k) :=
  Fintype.ofEquiv (Fin (2 ^ k)) ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩

instance instNonemptyStr (k : ℕ) : Nonempty (BitString k) := ⟨0⟩

/-- `X ‖ Y` — concatenation in the paper's order: `x` occupies indices
`0 .. a-1` and `y` indices `a .. a+b-1`. -/
def concat {a b : ℕ} (x : BitString a) (y : BitString b) : BitString (a + b) :=
  BitVec.cast (Nat.add_comm b a) (y ++ x)

@[inherit_doc concat] scoped infixl:65 " ∥ " => concat

/-- `X[a; l]` — the substring of length `l` starting at 0-based index `a`. -/
def substring {k : ℕ} (x : BitString k) (a l : ℕ) : BitString l := BitVec.extractLsb' a l x

@[inherit_doc substring] scoped syntax:max term noWs "[" term "; " term "]" : term

scoped macro_rules | `($x[$a; $l]) => `(Bits.substring $x $a $l)

/-- `bin_l : {0…2ˡ−1} → {0,1}ˡ` — little-endian integer encoding.  Layer 1: a bit
string, with no field interpretation attached. -/
def bin (l i : ℕ) : BitString l := BitVec.ofNat l i

/-- `bin₈` — the paper maps bytes to bit strings with it. -/
abbrev bin_8 : ℕ → BitString 8 := bin 8

/-- The length of `pad(X)` for `|X| = k` at block size `n`: the least multiple of
`n` that is `≥ k`. -/
def padLen (n k : ℕ) : ℕ := n * ((k + n - 1) / n)

/-- `pad(X) = X ‖ 0ᵛ`, `v` least with `n ∣ |X| + v`. -/
def pad (n : ℕ) {k : ℕ} (x : BitString k) : BitString (padLen n k) := x.setWidth (padLen n k)

/-! ### The permissible tweak and message sets

    𝒯 = ⋃_{i ∈ {0 … 2ⁿ⁻¹−2}}      {0,1}ⁱ
    ℳ = ⋃_{i ∈ {n … n+2ⁿ⁻¹−2}}    {0,1}ⁱ

Dependent sums over the length, so the index *is* `|X|`.  `ℳ`'s lower bound `n`
is expressed by indexing the *excess* over one block, making "a message is at
least one block" true by construction.  The caps are parameters; the paper takes
`cap = 2ⁿ⁻¹ − 2` for both, a value forced by the mode block `bin(2|T|+3)` having
to fit in `n` bits (§3.2). -/

/-- `𝒯` — permissible tweaks. -/
abbrev Tweak (cap : ℕ) : Type := Σ i : Fin (cap + 1), BitString i.val

/-- `ℳ` — permissible messages. -/
abbrev Msg (n cap : ℕ) : Type := Σ j : Fin (cap + 1), BitString (n + j.val)

/-- `|T|`. -/
def Tweak.len {cap : ℕ} (t : Tweak cap) : ℕ := t.1.val

/-- `|M|`. -/
def Msg.len {n cap : ℕ} (m : Msg n cap) : ℕ := n + m.1.val

/-! ### Layer 1.5 — block decomposition

Still field-free.  `blocks` accepts a string of *any* length, so no dependent
length arithmetic is ever needed at a use site; on a block-aligned string it is
exact, and beyond the string's end `sub` reads zero. -/

/-- `⌈k/n⌉` — the number of `n`-bit blocks of a `k`-bit string. -/
def numBlocks (n k : ℕ) : ℕ := (k + n - 1) / n

/-- The first `m` `n`-bit blocks of a string, low block first, for a count `m` given
independently of the string's width.  Reads past the end are zero (`Bits.sub` is
total), so no relation between `m` and `k` is needed. -/
def blocksTake (n m : ℕ) {k : ℕ} (x : BitString k) : List (BitString n) :=
  List.ofFn (fun i : Fin m => x[n * i.val; n])

@[simp] theorem length_blocksTake (n m : ℕ) {k : ℕ} (x : BitString k) :
    (blocksTake n m x).length = m := List.length_ofFn

/-- The `n`-bit blocks of a string, low block first. -/
def blocks (n : ℕ) {k : ℕ} (x : BitString k) : List (BitString n) :=
  List.ofFn (fun i : Fin (numBlocks n k) => x[n * i.val; n])

theorem blocks_eq_blocksTake (n : ℕ) {k : ℕ} (x : BitString k) :
    blocks n x = blocksTake n (numBlocks n k) x := rfl

/-! ## Facts

Not in the paper; the supporting lemmas later sections consume.  `getLsbD_cat`,
`sub_cat_left` and `sub_cat_right` are the bit-order convention stated as
theorems. -/

namespace Facts

@[simp] theorem getLsbD_cat {a b : ℕ} (x : BitString a) (y : BitString b) (i : ℕ) :
    (x ∥ y).getLsbD i = if i < a then x.getLsbD i else y.getLsbD (i - a) := by
  rw [concat, BitVec.getLsbD_cast, BitVec.getLsbD_append]

/-- `X[0; |X|] = X` — a string is its own full slice. -/
@[simp] theorem sub_full {a : ℕ} (x : BitString a) : x[0; a] = x := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [substring, BitVec.getLsbD_extractLsb']
  simp [hi]

/-- A slice that ends inside the left factor of a concatenation reads only that
factor. -/
theorem sub_cat_lo {a b : ℕ} (x : BitString a) (y : BitString b) {s l : ℕ} (h : s + l ≤ a) :
    (x ∥ y)[s; l] = x[s; l] := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [substring, substring, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', getLsbD_cat]
  simp [show s + i < a by omega]

/-- A slice that starts past the left factor reads only the right one. -/
theorem sub_cat_hi {a b : ℕ} (x : BitString a) (y : BitString b) {s l : ℕ} (h : a ≤ s) :
    (x ∥ y)[s; l] = y[s - a; l] := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [substring, substring, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', getLsbD_cat,
    if_neg (by omega), show s + i - a = s - a + i by omega]

/-- The left factor of a concatenation is the low substring. -/
theorem sub_cat_left {a b : ℕ} (x : BitString a) (y : BitString b) : (x ∥ y)[0; a] = x :=
  (sub_cat_lo x y (by omega)).trans (sub_full x)

/-- The right factor is the high substring. -/
theorem sub_cat_right {a b : ℕ} (x : BitString a) (y : BitString b) : (x ∥ y)[a; b] = y := by
  rw [sub_cat_hi x y le_rfl, Nat.sub_self, sub_full]

/-- `⊕` cancels — the only algebraic fact Figures 2–3 need about strings. -/
@[simp] theorem xor_cancel {k : ℕ} (x y : BitString k) : (x ^^^ y) ^^^ y = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Splitting and recombining is the identity — the `M‖N ← P, |M| = n` of
Figures 2–3 read backwards. -/
theorem cat_sub_sub {a b : ℕ} (x : BitString (a + b)) : x[0; a] ∥ x[a; b] = x := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [getLsbD_cat, substring, substring, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  by_cases h : i < a
  · simp [h]
  · simp only [h, if_false, Nat.zero_add]
    have : a + (i - a) = i := by omega
    simp [this, show i - a < b by omega]

/-- `bin_l` is injective on its stated domain `{0…2ˡ−1}`. -/
theorem bin_inj {l i j : ℕ} (hi : i < 2 ^ l) (hj : j < 2 ^ l) (h : bin l i = bin l j) :
    i = j := by
  have := congrArg BitVec.toNat h
  rwa [bin, bin, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

/-- A slice of an integer encoding is the encoding of the shifted integer — the
right-shift `bin_l⁻¹` performs when it reads a field out of a packed block. -/
theorem sub_bin {n : ℕ} (v : ℕ) {s l : ℕ} (h : s + l ≤ n) :
    (bin n v)[s; l] = bin l (v / 2 ^ s) := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [substring, BitVec.getLsbD_extractLsb', bin, bin, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
    ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  simp [hi, show s + i < n by omega]

/-- `|{0,1}ᵏ| = 2ᵏ`. -/
@[simp] theorem card_Str (k : ℕ) : Fintype.card (BitString k) = 2 ^ k :=
  (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
    BitString k ≃ Fin (2 ^ k))).trans (Fintype.card_fin _)

@[simp] theorem bin_zero (l : ℕ) : bin l 0 = 0 := by simp [bin]

/-- `n ∣ a → a % n = 0`, in the shape `GetTM` line 2 asserts. -/
theorem dvd_mod_zero {n a : ℕ} (h : n ∣ a) : a % n = 0 := by
  obtain ⟨m, rfl⟩ := h
  exact Nat.mul_mod_right n m

/-- `bin_l⁻¹` on its stated domain. -/
theorem toNat_bin {l v : ℕ} (h : v < 2 ^ l) : (bin l v).toNat = v := by
  rw [bin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A one-bit encoding is the parity. -/
theorem bin_one_eq_zero_iff (v : ℕ) : bin 1 v = 0 ↔ v % 2 = 0 := by
  constructor
  · intro h
    have hv := congrArg BitVec.toNat h
    rw [bin, BitVec.toNat_ofNat] at hv
    simpa using hv
  · intro h
    refine BitVec.eq_of_toNat_eq ?_
    rw [bin, BitVec.toNat_ofNat]
    simpa using h

/-- `bin_l` sends only `0` to the zero string. -/
theorem bin_ne_zero {l v : ℕ} (h0 : v ≠ 0) (hv : v < 2 ^ l) : bin l v ≠ 0 := fun h =>
  h0 (bin_inj hv (Nat.two_pow_pos l) (h.trans (by simp [bin])))

/-- The cap, specialised to a tweak drawn from `𝒯`. -/
theorem cap_of_tweak {n tcap : ℕ} (T : Tweak tcap) (hcap : 2 * tcap + 3 < 2 ^ n) :
    2 * T.len + 3 < 2 ^ n := by
  have := T.1.isLt
  simp only [Tweak.len]
  omega

/-- What the paper's cap gives the reads of the mode block `bin(2|T|+2/3)`: the
block size is at least `2`, and `|T| + 1` fits in the `n − 1` bits above the
alignment flag. -/
theorem cap_bounds {n tl : ℕ} (hcap : 2 * tl + 3 < 2 ^ n) : 2 ≤ n ∧ tl + 1 < 2 ^ (n - 1) := by
  have hn : 2 ≤ n := by
    by_contra hlt
    interval_cases n <;> simp at hcap
  refine ⟨hn, ?_⟩
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    ring
  omega

/-- Padding does not shorten. -/
theorem le_padLen {n : ℕ} (hn : 0 < n) (k : ℕ) : k ≤ padLen n k := by
  have h1 := Nat.div_add_mod (k + n - 1) n
  have h2 := Nat.mod_lt (k + n - 1) hn
  simp only [padLen]
  omega

/-- Padding lands on a block boundary. -/
theorem dvd_padLen (n k : ℕ) : n ∣ padLen n k := ⟨(k + n - 1) / n, rfl⟩

/-- Padding adds fewer than `n` bits. -/
theorem padLen_le (n k : ℕ) : padLen n k ≤ k + n - 1 := by
  simpa [padLen, Nat.mul_comm] using Nat.div_mul_le_self (k + n - 1) n

/-- A nonempty string pads to at least one block. -/
theorem le_padLen' {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : 0 < j) : n ≤ padLen n j := by
  have h : 1 ≤ (j + n - 1) / n := (Nat.one_le_div_iff hn).mpr (by omega)
  calc n = n * 1 := by ring
    _ ≤ n * ((j + n - 1) / n) := Nat.mul_le_mul_left n h

/-- A slice inside the payload of a padded string reads the payload. -/
theorem sub_pad_of_le {n k : ℕ} (x : BitString k) {j : ℕ} (hj : j ≤ padLen n k) :
    (pad n x)[0; j] = x[0; j] := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [substring, substring, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', pad,
    BitVec.getLsbD_setWidth]
  simp [show i < padLen n k by omega]

/-- Padding is recoverable: the payload is the low substring. -/
theorem sub_pad {n : ℕ} (hn : 0 < n) {k : ℕ} (x : BitString k) : (pad n x)[0; k] = x :=
  (sub_pad_of_le x (le_padLen hn k)).trans (sub_full x)

/-- Every message is at least one block. -/
theorem n_le_Msg_len {n cap : ℕ} (m : Msg n cap) : n ≤ m.len := Nat.le_add_right _ _

/-! ### Layer 1.5 — chunking is injective

The header's table promises `chunk : BitVec (n*m) ≃ (Fin m → BitVec n)`; `blocks`
is its forward direction and `blocks_inj` the half §3.2 needs — on block-aligned
strings the block list determines the string, length included. -/

@[simp] theorem length_blocks {n k : ℕ} (x : BitString k) :
    (blocks n x).length = numBlocks n k := by
  simp [blocks]

/-- `pad` is exactly `⌈k/n⌉` blocks. -/
theorem padLen_eq_mul (n k : ℕ) : padLen n k = n * numBlocks n k := rfl

/-- Appending the `10*` marker bit costs no extra block when the payload was not
already aligned — which is why `d(T,M)` can be stated with `⌈|M|/n⌉` in both
branches. -/
theorem numBlocks_succ_of_not_dvd {n k : ℕ} (hn : 0 < n) (h : ¬ n ∣ k) :
    numBlocks n (k + 1) = numBlocks n k := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hp
    · exact absurd (dvd_zero n) h
    · exact hp
  have hkk : k - 1 + 1 = k := by omega
  have hs : k / n = (k - 1) / n := by
    conv_lhs => rw [← hkk]
    rw [Nat.succ_div, if_neg (by rw [hkk]; exact h), Nat.add_zero]
  rw [numBlocks, numBlocks, show k + 1 + n - 1 = k + n by omega,
    show k + n - 1 = k - 1 + n by omega, Nat.add_div_right _ hn, Nat.add_div_right _ hn, hs]

theorem numBlocks_of_dvd {n k : ℕ} (hn : 0 < n) (h : n ∣ k) : numBlocks n k = k / n := by
  obtain ⟨m, rfl⟩ := h
  rw [numBlocks, show n * m + n - 1 = n * m + (n - 1) by omega, Nat.mul_add_div hn,
    Nat.div_eq_of_lt (by omega), Nat.mul_div_cancel_left _ hn, Nat.add_zero]

/-- Bit `i` of a string is bit `i mod n` of block `⌊i/n⌋`. -/
theorem getLsbD_blocks {n : ℕ} (hn : 0 < n) {k : ℕ} (x : BitString k) {i : ℕ} (hi : i < k) :
    ((blocks n x).getD (i / n) 0).getLsbD (i % n) = x.getLsbD i := by
  have hlt : i / n < numBlocks n k := by
    have h1 : i / n ≤ (k - 1) / n := Nat.div_le_div_right (by omega)
    have h2 : numBlocks n k = (k - 1) / n + 1 := by
      rw [numBlocks, show k + n - 1 = (k - 1) + n by omega, Nat.add_div_right _ hn]
    omega
  rw [blocks, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn, substring,
    BitVec.getLsbD_extractLsb', Nat.div_add_mod]
  simp [Nat.mod_lt _ hn, hi]

/-- The first block of a nonempty string is its low `n` bits.  Stated through the
`map` §3.2 applies, because that is the only place it is read. -/
theorem getD_map_blocks_zero {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 0 < k) (x : BitString k)
    {α : Type} (f : BitString n → α) (d : α) : ((blocks n x).map f).getD 0 d = f (x[0; n]) := by
  have hlt : 0 < numBlocks n k := Nat.div_pos (by omega) hn
  rw [blocks, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
    List.getElem_ofFn]
  simp

/-- The last block of a block-aligned string is its top `n` bits. -/
theorem getD_map_blocks_last {n : ℕ} (hn : 0 < n) {k : ℕ} (hdvd : n ∣ k) (hk : 0 < k)
    (x : BitString k) {α : Type} (f : BitString n → α) (d : α) :
    ((blocks n x).map f).getD (numBlocks n k - 1) d = f (x[k - n; n]) := by
  have hl : numBlocks n k = k / n := numBlocks_of_dvd hn hdvd
  have hpos : 0 < k / n := Nat.div_pos (Nat.le_of_dvd hk hdvd) hn
  have hidx : n * (numBlocks n k - 1) = k - n := by
    obtain ⟨m, rfl⟩ := hdvd
    rw [hl, Nat.mul_div_cancel_left _ hn, Nat.mul_sub, mul_one]
  rw [blocks, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_ofFn]; omega),
    List.getElem_map, List.getElem_ofFn, hidx]

/-- Chunking a block-aligned string with one further block appended. -/
theorem blocks_cat_block {n a : ℕ} (hn : 0 < n) (hdvd : n ∣ a) (x : BitString a) (y : BitString n) :
    blocks n (x ∥ y) = blocks n x ++ [y] := by
  have hna : numBlocks n a = a / n := numBlocks_of_dvd hn hdvd
  have hnan : numBlocks n (a + n) = numBlocks n a + 1 := by
    rw [numBlocks_of_dvd hn (Nat.dvd_add hdvd dvd_rfl), Nat.add_div_right _ hn, hna]
  have hmul : n * numBlocks n a = a := by rw [hna]; exact Nat.mul_div_cancel' hdvd
  have hL : blocks n (x ∥ y)
      = List.ofFn (fun i : Fin (numBlocks n (a + n)) => (x ∥ y)[n * i.val; n]) := rfl
  have hR : blocks n x = List.ofFn (fun i : Fin (numBlocks n a) => x[n * i.val; n]) := rfl
  rw [hL, hR]
  refine List.ext_getElem (by simp [hnan]) (fun i h₁ h₂ => ?_)
  rw [List.getElem_ofFn]
  by_cases hi : i < numBlocks n a
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_ofFn]
    exact sub_cat_lo _ _ (by
      calc n * i + n = n * (i + 1) := by ring
        _ ≤ n * numBlocks n a := Nat.mul_le_mul_left n hi
        _ = a := hmul)
  · have hia : i = numBlocks n a := by
      simp only [List.length_ofFn, hnan] at h₁
      omega
    rw [List.getElem_append_right (by simpa using Nat.not_lt.mp hi)]
    simp only [hia, hmul, List.length_ofFn, Nat.sub_self]
    rw [sub_cat_right]
    rfl

/-- On block-aligned strings, `blocks` is injective — length and all. -/
theorem blocks_inj {n : ℕ} (hn : 0 < n) {k₁ k₂ : ℕ} (h₁ : n ∣ k₁) (h₂ : n ∣ k₂)
    {x₁ : BitString k₁} {x₂ : BitString k₂} (h : blocks n x₁ = blocks n x₂) :
    (⟨k₁, x₁⟩ : Σ k : ℕ, BitString k) = ⟨k₂, x₂⟩ := by
  have hlen : k₁ = k₂ := by
    have hl := congrArg List.length h
    rw [length_blocks, length_blocks, numBlocks_of_dvd hn h₁, numBlocks_of_dvd hn h₂] at hl
    have hm : k₁ / n * n = k₂ / n * n := by rw [hl]
    rwa [Nat.div_mul_cancel h₁, Nat.div_mul_cancel h₂] at hm
  subst hlen
  exact congrArg _ (BitVec.eq_of_getLsbD_eq fun i hi => by
    rw [← getLsbD_blocks hn x₁ hi, ← getLsbD_blocks hn x₂ hi, h])

/-! ### The `10*` pad (paper Appendix A, lines 14–18)

Appendix A recovers `|M|` from `pad(M‖1)` with a `while` loop scanning down for
the marker bit.  Its content is that **the marker is the highest set bit**: bit
`|M|` is set, everything above it is clear, and everything below it is `M`.  The
three lemmas below say exactly that, so the loop needs no transcription. -/

/-- The `10*` marker sits at index `|M|`. -/
theorem pad10_marker {n : ℕ} (hn : 0 < n) {k : ℕ} (M : BitString k) :
    (pad n (M ∥ bin 1 1)).getLsbD k = true := by
  have h : k < padLen n (k + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self k) (le_padLen hn (k + 1))
  rw [pad, BitVec.getLsbD_setWidth, getLsbD_cat]
  simp [h, bin]

/-- Above the marker the padded block is zero. -/
theorem pad10_high {n : ℕ} {k j : ℕ} (hj : k < j) (M : BitString k) :
    (pad n (M ∥ bin 1 1)).getLsbD j = false := by
  rw [pad, BitVec.getLsbD_setWidth, getLsbD_cat, if_neg (Nat.not_lt.mpr hj.le)]
  have : ¬ (j - k < 1) := by omega
  simp [BitVec.getLsbD_eq_getElem?_getD, this]

/-- Below the marker the padded block is `M`. -/
theorem pad10_low {n : ℕ} (hn : 0 < n) {k j : ℕ} (hj : j < k) (M : BitString k) :
    (pad n (M ∥ bin 1 1)).getLsbD j = M.getLsbD j := by
  have h : j < padLen n (k + 1) :=
    lt_of_lt_of_le (by omega) (le_padLen hn (k + 1))
  rw [pad, BitVec.getLsbD_setWidth, getLsbD_cat, if_pos hj]
  simp [h]

end Facts

end Bits

/-! ## Paper §2.2 — Polynomial hash function (p. 4)

Layer 2: the first section that mentions a field.  The paper's opening sentence,
"we interpret `n`-bit blocks as little-endian field elements of `GF(2ⁿ)`, so
`001‖0ⁿ⁻³` is interpreted as the element `x²`", is the single bridge from layer
1 — packaged as `BlockField` and required *only here*, not by the model as a
whole.  (In `RandomSystems/HCTR2.lean:289` the same content is `BlockBits`, a
hypothesis of everything.)

The paper's concrete `n = 128` instantiation — reduction polynomial
`x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1` and the unit `x⁻ⁿ = x¹²⁷+x¹²⁴+x¹²¹+x¹¹⁴+1` — is
`RandomSystems/HTechnique/GF2Field.lean` (`mPoly`, `uPolyval`), with the
little-endian reading canonical there as `gf128OfNat`; `Poly.GF128.blockField`
assembles it into a `BlockField`, which is what keeps §3.2 non-vacuous. -/

namespace Hash

open Bits Bits.Facts

variable {F : Type} [Field F] {n : ℕ}

/-- The paper's block↔field reading: `n`-bit blocks *are* little-endian elements
of `GF(2ⁿ)`.  Bijective, carrying `⊕` to `+` — which is what makes the field
addition of §2.4's Figures 2–3 the same operation as bit XOR — and sending the
basis blocks to the powers of `x`.

This is not an abstraction of the paper's field, it *is* the paper's field: a
bijection carrying `⊕` to `+` makes `(F, +) ≅ (ℤ/2)ⁿ`, so `|F| = 2ⁿ` and
`1 + 1 = 0` (`Facts.card_eq`, `Facts.charTwo`), and a finite field of order `2ⁿ`
is `GF(2ⁿ)`.  What the structure adds beyond that is the *choice* of reading, and
`enc_pow` is the paper's own sentence for it — without it `enc` would be pinned
only up to a `GF(2)`-linear relabelling, and §3.2's property 2 would be false
under a relabelling sending `bin(2)` to `1`. -/
structure BlockField (F : Type) [Field F] (n : ℕ) where
  /-- The little-endian block↔field bijection. -/
  enc : BitString n ≃ F
  /-- Bit XOR is field addition. -/
  enc_xor : ∀ a b : BitString n, enc (a ^^^ b) = enc a + enc b
  /-- `x` — the paper's generator. -/
  x : F
  /-- "`001‖0ⁿ⁻³` is interpreted as the element `x²`": the basis blocks are the
  powers of `x`.  With `enc_xor` this determines `enc` on every block. -/
  enc_pow : ∀ j < n, enc (bin n (2 ^ j)) = x ^ j

/-- **`x⁻ⁿ`** — POLYVAL's dot unit (§2.2; §5.2.1: "the polynomial is evaluated not
at the parameter `h̄` but at `x⁻ⁿh̄` so that Montgomery multiplication is
key-agile").  The paper fixes it, so it is a field of the reading rather than a
parameter of the mode. -/
def BlockField.u (bf : BlockField F n) : F := (bf.x ^ n)⁻¹

/-- **POLYVAL** (paper §2.2, [GLL17; GLL19]):

    POLYVAL(h̄, λ)   = 0ⁿ
    POLYVAL(h̄, A‖B) = (POLYVAL(h̄, A) ⊕ B) ⊗ h̄ ⊗ x⁻ⁿ

Written as the left fold the two equations define; `Facts.POLYVAL_nil` and
`Facts.POLYVAL_concat` are the paper's two lines.  The fold keeps the dot unit
`u` generic — that is [GLL17]'s definition — but every *use* below takes it from
the reading, as `bf.u = x⁻ⁿ`, which is what the paper fixes. -/
def POLYVAL (u h : F) (bs : List F) : F :=
  bs.foldl (fun acc b => (acc + b) * h * u) 0

/-- **The string the paper hashes**:

    bin(2|T| + 2) ‖ pad(T) ‖ M            if n divides |M|
    bin(2|T| + 3) ‖ pad(T) ‖ pad(M‖1)     otherwise

Layer 1 — pure bits.  The two branches have different widths, hence the `Σ`;
that costs nothing downstream because `blocks` and `∥` are width-polymorphic.

This is spelled **once**: §2.2's `hashInput` chunks it, and §3.2's `Hpoly`
chunks it with the paper's trailing `0ⁿ` appended.  Spelling it twice would let
an edit to one branch of one silently diverge from the other.

`M` is an **arbitrary** bit string, not a member of `ℳ`: Figure 2 evaluates
`H_h̄(T, N)` where `N` is the plaintext minus its head block, which may be
shorter than `n` and may be empty. -/
def hashStr {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) : Σ w : ℕ, BitString w :=
  if n ∣ k then
    ⟨_, bin n (2 * T.len + 2) ∥ pad n T.2 ∥ M⟩
  else
    ⟨_, bin n (2 * T.len + 3) ∥ pad n T.2 ∥ pad n (M ∥ bin 1 1)⟩

/-- The paper's hash input block list — `hashStr` in blocks.  The field appears
only in `H`. -/
def hashInput {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) : List (BitString n) :=
  blocks n (hashStr (n := n) T M).2

/-- **`H_h̄(T, M)`** (paper §2.2): POLYVAL over the hash input, at the paper's dot
unit `x⁻ⁿ`.  `h` is the key `h̄` as a field element; §3.2 reads this as the formal
polynomial `Hpoly` evaluated at `h = x⁻ⁿh̄`. -/
def H (bf : BlockField F n) (h : F) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) : F :=
  POLYVAL bf.u h ((hashInput (n := n) T M).map bf.enc)

/-- `H_h̄(T, M)` read back as an `n`-bit block, and with the hash key given as the
bit string `h̄ ∈ {0,1}ⁿ` the paper uses.  This is the form Figures 2–3 XOR with;
it is the only place the field surfaces in §2.4. -/
def hashBits (bf : BlockField F n) (hbar : BitString n) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) : BitString n :=
  bf.enc.symm (H bf (bf.enc hbar) T M)

/-! ## Facts -/

namespace Facts

/-- `enc 0 = 0` — carrying `⊕` to `+` already forces it, so `BlockField` states no
separate axiom. -/
@[simp] theorem enc_zero (bf : BlockField F n) : bf.enc 0 = 0 := by
  have h := bf.enc_xor 0 0
  rw [BitVec.xor_self] at h
  have h2 : (0 : F) + bf.enc 0 = bf.enc 0 + bf.enc 0 := by rw [zero_add]; exact h
  exact (add_right_cancel h2).symm

/-- Only the zero block reads as the zero field element. -/
theorem enc_eq_zero_iff (bf : BlockField F n) {a : BitString n} : bf.enc a = 0 ↔ a = 0 := by
  rw [← enc_zero bf]
  exact bf.enc.apply_eq_iff_eq

/-- `|F| = 2ⁿ`: the reading is a bijection. -/
theorem card_eq (bf : BlockField F n) : Nat.card F = 2 ^ n := by
  rw [Nat.card_congr bf.enc.symm, Nat.card_eq_fintype_card, card_Str]

/-- `1 + 1 = 0`: `⊕` is `+` and `a ⊕ a = 0`. -/
theorem charTwo (bf : BlockField F n) (a : F) : a + a = 0 := by
  obtain ⟨b, rfl⟩ := bf.enc.surjective a
  rw [← bf.enc_xor, BitVec.xor_self]
  exact enc_zero bf

/-- `bin(2)` reads as `x`, the paper's `010ⁿ⁻²`.  Needs `n ≥ 2`: at `n = 1` there
is no second basis block. -/
theorem enc_two (bf : BlockField F n) (hn : 2 ≤ n) : bf.enc (bin n 2) = bf.x := by
  simpa using bf.enc_pow 1 (by omega)

theorem x_ne_zero (bf : BlockField F n) (hn : 2 ≤ n) : bf.x ≠ 0 := by
  rw [← enc_two bf hn, Ne, enc_eq_zero_iff]
  refine bin_ne_zero (by omega) ?_
  calc (2 : ℕ) < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- **The paper's `x^{n−1} ≠ 1`** (p. 7).  It is a statement about the *basis*,
not about the reduction polynomial: `bin(1)` and `bin(2ⁿ⁻¹)` are distinct blocks
reading as `x⁰` and `xⁿ⁻¹`, and `enc` is injective. -/
theorem x_pow_pred_ne_one (bf : BlockField F n) (hn : 2 ≤ n) : bf.x ^ (n - 1) ≠ 1 := by
  intro h
  have h0 : bf.enc (bin n 1) = 1 := by simpa using bf.enc_pow 0 (by omega)
  have h1 : bf.enc (bin n (2 ^ (n - 1))) = 1 := by rw [bf.enc_pow (n - 1) (by omega), h]
  have h2 : (2 : ℕ) ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ≤ 2 ^ (n - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := bin_inj h2 (by omega) (bf.enc.injective (h1.trans h0.symm))
  omega

/-- The dot unit is invertible, so `h̄ ↦ x⁻ⁿh̄` is a bijection of the field — the
paper's "multiplication by a nonzero field element is a bijection of the field to
itself" (p. 7). -/
theorem u_ne_zero (bf : BlockField F n) (hn : 2 ≤ n) : bf.u ≠ 0 :=
  inv_ne_zero (pow_ne_zero n (x_ne_zero bf hn))

/-- `h̄ = xⁿh` — the substitution §3.2 evaluates at, read the other way. -/
theorem x_pow_mul_u (bf : BlockField F n) (hn : 2 ≤ n) : bf.x ^ n * bf.u = 1 :=
  mul_inv_cancel₀ (pow_ne_zero n (x_ne_zero bf hn))

/-- Moving a summand across an equation, in characteristic 2. -/
theorem add_eq_iff (bf : BlockField F n) {a b c : F} : a + b = c ↔ a + c = b := by
  constructor
  · rintro rfl
    calc a + (a + b) = a + a + b := by ring
      _ = b := by rw [charTwo bf a, zero_add]
  · rintro rfl
    calc a + (a + c) = a + a + c := by ring
      _ = c := by rw [charTwo bf a, zero_add]

/-- In characteristic 2, `⊕` and `=` are one relation.  The paper's perturbations
`H(T,M) ⊕ g` and `H(T,M) ⊕ g ⊕ h̄` are read through this. -/
theorem add_eq_zero_iff (bf : BlockField F n) {a b : F} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [charTwo bf b, add_zero]
      _ = a + b + b := by ring
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact charTwo bf a

/-- **The paper's `xⁿ ≠ x`** (p. 7), the degenerate half of §3.2's property 2. -/
theorem x_pow_ne_self (bf : BlockField F n) (hn : 2 ≤ n) : bf.x ^ n ≠ bf.x := by
  intro h
  refine x_pow_pred_ne_one bf hn ?_
  have hx := x_ne_zero bf hn
  have : bf.x * bf.x ^ (n - 1) = bf.x * 1 := by
    rw [mul_one, ← pow_succ']
    rwa [show n - 1 + 1 = n by omega]
  exact mul_left_cancel₀ hx this

/-- The hashed string is block-aligned — every piece of it is. -/
theorem dvd_hashStr {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    n ∣ (hashStr (n := n) T M).1 := by
  rw [hashStr]
  split
  · exact Nat.dvd_add (Nat.dvd_add dvd_rfl (dvd_padLen n T.len)) ‹n ∣ k›
  · exact Nat.dvd_add (Nat.dvd_add dvd_rfl (dvd_padLen n T.len)) (dvd_padLen n (k + 1))

/-- The paper's first POLYVAL equation. -/
@[simp] theorem POLYVAL_nil (u h : F) : POLYVAL u h [] = 0 := rfl

/-- The paper's second POLYVAL equation, `A‖B` with `|B| = n`. -/
theorem POLYVAL_concat (u h : F) (bs : List F) (b : F) :
    POLYVAL u h (bs ++ [b]) = (POLYVAL u h bs + b) * h * u := by
  simp [POLYVAL]

/-! ### The shape both branches hash

Either branch of `hashStr`, with §3.2's trailing `0ⁿ`, is

    bin(v) ‖ pad(T) ‖ Y ‖ 0ⁿ

— a mode block, the padded tweak, a payload, and the zero block; only `v` and the
payload differ.  Every slice §3.2 and Appendix A take is a slice of *this*, so the
six reads are proved once here instead of once per branch per section. -/

/-- **Read a slice of a concatenation.**  Every read below is "push the slice into
whichever factor contains it", and the only work is the index arithmetic, which is
`omega`'s.  `sub_cat_lo` and `sub_cat_hi` share a left-hand side, so the discharger
is what picks between them. -/
local macro "read_slice" : tactic =>
  `(tactic| simp (disch := omega) only [sub_cat_lo, sub_cat_hi, sub_cat_left, sub_cat_right,
      sub_full, sub_pad, sub_pad_of_le, sub_bin, bin_zero, Nat.sub_self, pow_one, pow_zero,
      Nat.div_one])

section Shape

variable {n tl p : ℕ} (v : ℕ) (Tw : BitString tl) (Y : BitString p)

/-- The mode block leads. -/
theorem shape_mode : ((bin n v ∥ pad n Tw ∥ Y) ∥ bin n 0)[0; n] = bin n v := by read_slice

/-- The zero block trails (`GetTM` line 4). -/
theorem shape_top : ((bin n v ∥ pad n Tw ∥ Y) ∥ bin n 0)[n + padLen n tl + p; n] = 0 := by
  read_slice

/-- The mode block above its alignment flag (`GetTM` line 5). -/
theorem shape_len (hn : 0 < n) :
    ((bin n v ∥ pad n Tw ∥ Y) ∥ bin n 0)[1; n - 1] = bin (n - 1) (v / 2) := by read_slice

/-- The alignment flag (`GetTM` line 9). -/
theorem shape_flag (hn : 0 < n) :
    ((bin n v ∥ pad n Tw ∥ Y) ∥ bin n 0)[0; 1] = bin 1 v := by read_slice

/-- The tweak (`GetTM` line 21). -/
theorem shape_tweak (hn : 0 < n) : ((bin n v ∥ pad n Tw ∥ Y) ∥ bin n 0)[n; tl] = Tw := by
  have := le_padLen hn tl
  read_slice

/-- A prefix of the payload (`GetTM` lines 11 and 19). -/
theorem shape_payload {j : ℕ} (hj : j ≤ p) :
    ((bin n v ∥ pad n Tw ∥ Y) ∥ bin n 0)[n + padLen n tl; j] = Y[0; j] := by read_slice

end Shape

end Facts

end Hash

/-! ## Paper §2.3 — XCTR mode (p. 4)

    XCTR_k(S) = E_k(S ⊕ bin(1)) ‖ E_k(S ⊕ bin(2)) ‖ E_k(S ⊕ bin(3)) ‖ ⋯

Back to layer 1: `⊕` is bit XOR and `bin` is layer 1, so **no field appears** —
only a block cipher on `n`-bit strings.  Following §2.1's subscript convention,
`E` below is `E_k`, the cipher with its key already applied.

The paper writes the keystream as an unbounded string and truncates it with
`[0; m]`.  We take the truncation as primitive rather than carrying an infinite
object, and recover the displayed concatenation as a theorem
(`Facts.sub_xctr`).  The paper's cost remark — "generating the first `m` bits
takes `⌈m/n⌉` block cipher calls" — is `Facts.xctr_congr`: the first `m` bits
depend on the cipher at exactly the `⌈m/n⌉` points `S ⊕ bin(1) … S ⊕ bin(⌈m/n⌉)`. -/

namespace XCTR

open Bits

variable {n : ℕ}

/-- The `j`-th keystream block, 1-based as in the paper: `E_k(S ⊕ bin(j))`. -/
def block (E : BitString n → BitString n) (S : BitString n) (j : ℕ) : BitString n := E (S ^^^ bin n j)

/-- `XCTR_k(S)[0; m]` — the first `m` bits of the keystream.  Bit `i` is bit
`i mod n` of block `⌊i/n⌋ + 1`, which is what the displayed concatenation means
under §2.1's index convention. -/
def xctr (E : BitString n → BitString n) (S : BitString n) (m : ℕ) : BitString m :=
  BitVec.ofFnLE (fun i : Fin m => (block E S (i.val / n + 1)).getLsbD (i.val % n))

/-! ## Facts -/

namespace Facts

@[simp] theorem getLsbD_xctr (E : BitString n → BitString n) (S : BitString n) {m i : ℕ} (hi : i < m) :
    (xctr E S m).getLsbD i = (block E S (i / n + 1)).getLsbD (i % n) := by
  rw [xctr, BitVec.getLsbD_ofFnLE, dif_pos hi]

/-- **The paper's display, as a theorem**: the `i`-th `n`-bit slice of the
keystream is `E_k(S ⊕ bin(i+1))`, i.e. XCTR *is* the concatenation of the cipher
outputs. -/
theorem sub_xctr (hn : 0 < n) (E : BitString n → BitString n) (S : BitString n) {m i : ℕ} (hi : i < m) :
    (xctr E S (n * m))[n * i; n] = block E S (i + 1) := by
  refine BitVec.eq_of_getLsbD_eq (fun t ht => ?_)
  have hlt : n * i + t < n * m := by
    calc n * i + t < n * i + n := by omega
      _ = n * (i + 1) := by ring
      _ ≤ n * m := Nat.mul_le_mul_left n hi
  rw [substring, BitVec.getLsbD_extractLsb', getLsbD_xctr E S hlt]
  have hdiv : (n * i + t) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht]; omega
  have hmod : (n * i + t) % n = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  rw [hdiv, hmod]
  simp [ht]

/-- **The paper's cost remark, as a theorem**: the first `m` bits of the
keystream depend on the cipher at exactly the `⌈m/n⌉ = numBlocks n m` points
`S ⊕ bin(1) … S ⊕ bin(⌈m/n⌉)` — "takes `⌈m/n⌉` block cipher calls". -/
theorem xctr_congr (hn : 0 < n) {E₁ E₂ : BitString n → BitString n} {S : BitString n} {m : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ numBlocks n m → E₁ (S ^^^ bin n j) = E₂ (S ^^^ bin n j)) :
    xctr E₁ S m = xctr E₂ S m := by
  refine BitVec.eq_of_getLsbD_eq (fun i hi => ?_)
  rw [getLsbD_xctr E₁ S hi, getLsbD_xctr E₂ S hi]
  have hle : i / n + 1 ≤ numBlocks n m := by
    have h1 : i / n ≤ (m - 1) / n := Nat.div_le_div_right (by omega)
    have h2 : (m - 1) / n + 1 = (m + n - 1) / n := by
      rw [← Nat.add_div_right (m - 1) hn]
      congr 1
      omega
    simp only [numBlocks]
    omega
  rw [block, block, h (i / n + 1) (Nat.le_add_left 1 _) hle]

end Facts

end XCTR

/-! ## Paper §2.4 — HCTR2 (Figures 2–3, p. 3; §2.4, p. 5)

    ENCRYPT(k,T,P)                        DECRYPT(k,T,C)
      h̄ ← E_k(bin(0))                       h̄ ← E_k(bin(0))
      L ← E_k(bin(1))                       L ← E_k(bin(1))
      M‖N ← P, |M| = n                      U‖V ← C, |U| = n
      MM ← M ⊕ H_h̄(T,N)                     UU ← U ⊕ H_h̄(T,V)
      UU ← E_k(MM)                          MM ← E_k⁻¹(UU)
      S ← MM ⊕ UU ⊕ L                       S ← MM ⊕ UU ⊕ L
      V ← N ⊕ XCTR_k(S)[0;|N|]              N ← V ⊕ XCTR_k(S)[0;|V|]
      U ← UU ⊕ H_h̄(T,V)                     M ← MM ⊕ H_h̄(T,N)
      C ← U‖V                               P ← M‖N

Where §2.1–2.3 meet.  Three things the layering buys, visible in the code:

* Every line is **bit** algebra — `^^^`, `∥`, `[·;·]` — with the field entering
  only through `Hash.hashBits`, which is `H` read back as an `n`-bit block.  In
  `RandomSystems/HCTR2.lean:385` the same lines are field addition on `F`,
  because the message type carries field elements.
* `M‖N ← P, |M| = n` is `P.2[0; n]` and `P.2[n; |N|]`; `Facts.cat_sub_sub` is the
  same line read backwards, and it is what closes correctness.
* "returns a ciphertext of the same length as the plaintext" (§2.4) is
  **definitional** — encryption preserves the fiber index — so `length_encrypt`
  is `rfl`.

`E` is `Equiv.Perm (Str n)` rather than a bare function: §2.1 types the cipher as
a function, but Figure 3 uses `E_k⁻¹`, so invertibility is assumed by the paper
and is stated here rather than left implicit. -/

namespace HCTR2

open Bits Bits.Facts Hash XCTR

variable {F : Type} [Field F] {n : ℕ}

/-- **`S`, Figure 2's XCTR nonce** `S = MM ⊕ UU ⊕ L`.  Named because §3.4.1's
inference is written in terms of `Sˢ` and its offsets `Sⱼˢ = Sˢ ⊕ bin(j)`, and
because §3.4's leftover block `Dˢ` is a slice of the keystream at `Sˢ`. -/
def nonce (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (P : Msg n cap) : BitString n :=
  let hbar := E (bin n 0)
  let MM := P.2[0; n] ^^^ hashBits bf hbar T P.2[n; P.1.val]
  MM ^^^ E MM ^^^ E (bin n 1)

/-- **`D`, §3.4's leftover block**: `XCTR_π(S)[|P| − n; n⌈|N|/n⌉ − |N|]`, the part
of the last keystream block that XCTR generated and the mode did not use.  Empty
exactly when the message tail is block-aligned. -/
def leftover (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (P : Msg n cap) :
    BitString (padLen n P.1.val - P.1.val) :=
  (xctr (⇑E) (nonce bf E T P) (padLen n P.1.val))[P.1.val; padLen n P.1.val - P.1.val]

/-- **Figure 2 — HCTR2 encryption.** -/
def encrypt (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (P : Msg n cap) : Msg n cap :=
  let hbar := E (bin n 0)
  let L := E (bin n 1)
  let M := P.2[0; n]
  let N := P.2[n; P.1.val]
  let MM := M ^^^ hashBits bf hbar T N
  let UU := E MM
  let S := MM ^^^ UU ^^^ L
  let V := N ^^^ xctr (⇑E) S P.1.val
  let U := UU ^^^ hashBits bf hbar T V
  ⟨P.1, U ∥ V⟩

/-- Figure 2's `S` is `nonce`. -/
theorem nonce_eq (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (P : Msg n cap) :
    nonce bf E T P
      = (P.2[0; n] ^^^ hashBits bf (E (bin n 0)) T P.2[n; P.1.val]) ^^^
          E (P.2[0; n] ^^^ hashBits bf (E (bin n 0)) T P.2[n; P.1.val]) ^^^ E (bin n 1) := rfl

/-- **Figure 3 — HCTR2 decryption.** -/
def decrypt (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (C : Msg n cap) : Msg n cap :=
  let hbar := E (bin n 0)
  let L := E (bin n 1)
  let U := C.2[0; n]
  let V := C.2[n; C.1.val]
  let UU := U ^^^ hashBits bf hbar T V
  let MM := E.symm UU
  let S := MM ^^^ UU ^^^ L
  let N := V ^^^ xctr (⇑E) S C.1.val
  let M := MM ^^^ hashBits bf hbar T N
  ⟨C.1, M ∥ N⟩

/-! ## Facts -/

namespace Facts

/-- §2.4: "returns a ciphertext of the same length as the plaintext" — structural
here, since encryption preserves the fiber index. -/
@[simp] theorem length_encrypt (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (P : Msg n cap) :
    (encrypt bf E T P).1 = P.1 := rfl

/-- **§2.4 correctness**: `DECRYPT(k, T, ENCRYPT(k, T, P)) = P`. -/
theorem decrypt_encrypt (bf : BlockField F n) (E : Equiv.Perm (BitString n))
    {tcap cap : ℕ} (T : Tweak tcap) (P : Msg n cap) :
    decrypt bf E T (encrypt bf E T P) = P := by
  obtain ⟨j, p⟩ := P
  -- name every intermediate of Figure 2, so the sharing between the two figures
  -- is syntactic rather than a 30-line term the matcher has to align
  set hbar := E (bin n 0) with hhbar
  set M := p[0; n] with hM
  set N := p[n; (j : ℕ)] with hN
  set MM := M ^^^ hashBits bf hbar T N with hMM
  set UU := E MM with hUU
  set S := MM ^^^ UU ^^^ E (bin n 1) with hS
  set ks := xctr (⇑E) S (j : ℕ) with hks
  set V := N ^^^ ks with hV
  set U := UU ^^^ hashBits bf hbar T V with hU
  show decrypt bf E T ⟨j, U ∥ V⟩ = ⟨j, p⟩
  simp only [decrypt, sub_cat_left, sub_cat_right]
  rw [hU, xor_cancel, hUU, Equiv.symm_apply_apply, ← hS, ← hks, hV, xor_cancel,
    hMM, xor_cancel, hM, hN, cat_sub_sub]

end Facts

end HCTR2

/-! ## Paper §3.1 — Definitions (pp. 5–6)

This section turns the paper's oracle notation into typed probabilistic systems:

* `Perm n`, `pmE`, and `pmPerm` model the real and ideal two-sided block-cipher
  experiments;
* `TPerm`, `tprp`, `hctr2E`, and `hctr2Perm` model the tweakable experiments;
* `Budget q σ` is the paper's at-most query/block restriction; and
* `advPRP` and `advTPRP` are the corresponding optimal advantages.

The paper writes a maximum over adversaries.  Lean uses the CR18 Random Systems
distance `Δ`, whose definition takes the supremum over probability-distribution
interactive distinguishers.  Thus the distinguisher model and optimal advantage
are reused rather than redefined for HCTR2.  Randomization is already present in
the distribution over distinguishers; the paper's reduction to fixed
deterministic adversaries is used later when reasoning about one transcript law
in §3.3.

The paper also carries a running-time parameter `t`.  This information-theoretic
file has no machine-cost model, so it formalizes the `q` and `σ` restrictions but
does not claim to formalize the time bound.  Declarations below whose docstrings
name §3.4 are later proof vocabulary kept in `Sec` for namespace ownership; they
are not part of this §3.1 correspondence. -/

namespace Sec

open Bits HCTR2
open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique (QueryDir)
open scoped RandomSystems.CR18

variable {F : Type} [Field F] {n cap tcap m : ℕ}

/-! ### The block-cipher game -/

/-- `Perm(n)` — all permutations on `{0,1}ⁿ`. -/
abbrev Perm (n : ℕ) : Type := Equiv.Perm (BitString n)

/-- The two-sided (`±`) oracle of a permutation: forward queries evaluate `π`,
inverse queries `π⁻¹`.  §3.1 gives the adversary both, which is why §2.1's
"block cipher" must in fact be invertible. -/
def pmFun (π : Perm n) : QueryDir × BitString n → BitString n := fun z =>
  match z.1 with
  | QueryDir.fwd => π z.2
  | QueryDir.inv => π.symm z.2

/-- `±E` — the two-sided keyed cipher under a uniform key. -/
noncomputable def pmE {K : Type} [Fintype K] [Nonempty K] (E : K → Perm n) :
    ProbPDS (QueryDir × BitString n) (BitString n) :=
  PFunPDS.Prob.functionEvaluator ⟨Dist.uniform K, Dist.uniform_isProbDist⟩
    (fun k => pmFun (E k))

/-- `±Perm(n)` — the two-sided uniform permutation oracle. -/
noncomputable def pmPerm (n : ℕ) : ProbPDS (QueryDir × BitString n) (BitString n) :=
  PFunPDS.Prob.functionEvaluator ⟨Dist.uniform (Perm n), Dist.uniform_isProbDist⟩ pmFun

/-! ### The tweakable-SPRP game -/

-- These short local names follow the paper's notation.  A future public API may
-- expose longer names such as `TweakablePermutation` and `TweakableQuery`.
/-- `Perm^𝒯(ℳ)` — tweakable length-preserving permutations.  The paper's two
conditions, `|π(T,M)| = |M|` and "`π_T` is a permutation on `ℳ`", collapse into
one here: length is the fiber index, so a length-preserving permutation of `ℳ`
*is* a permutation of each fiber, one per `(tweak, length class)`. -/
abbrev TPerm (n cap tcap : ℕ) : Type :=
  ∀ p : Tweak tcap × Fin (cap + 1), Equiv.Perm (BitString (n + p.2.val))

/-- Queries of the tweakable game: a direction, a tweak, and a message. -/
abbrev TQ (n cap tcap : ℕ) : Type := QueryDir × Tweak tcap × Msg n cap

/-- Responses: a message of the same length class. -/
abbrev TM (n cap : ℕ) : Type := Msg n cap

/-- The ideal oracle: `π` forward, `π⁻¹` inverse, per `(tweak, length class)`. -/
def tprpFun (π : TPerm n cap tcap) : TQ n cap tcap → TM n cap :=
  TweakablePRP.tprpFun (MsgK := fun j : Fin (cap + 1) => BitString (n + j.val)) π

/-- `±p̃rp`'s ideal world: a uniform `π ←$ Perm^𝒯(ℳ)`. -/
noncomputable def tprp (n cap tcap : ℕ) : ProbPDS (TQ n cap tcap) (TM n cap) :=
  TweakablePRP.tprp
    (MsgK := fun j : Fin (cap + 1) => BitString (n + j.val)) (T := Tweak tcap)

/-- The two-sided HCTR2 oracle at a fixed permutation — the paper's `HCTR2[π]`. -/
def hctr2Fun (bf : Hash.BlockField F n) (π : Perm n) :
    TQ n cap tcap → TM n cap := fun z =>
  match z.1 with
  -- Direction is the first query coordinate; the remaining pair is `(T, M)`.
  | QueryDir.fwd => encrypt bf π z.2.1 z.2.2
  | QueryDir.inv => decrypt bf π z.2.1 z.2.2

/-- `HCTR2[Perm(n)]` — the real world of the information-theoretic step. -/
noncomputable def hctr2Perm (bf : Hash.BlockField F n) :
    ProbPDS (TQ n cap tcap) (TM n cap) :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform (Perm n), Dist.uniform_isProbDist⟩ (hctr2Fun bf)

/-- `HCTR2[E]` — the real world of the computational step, `E_k` for `k ←$ K`. -/
noncomputable def hctr2E {K : Type} [Fintype K] [Nonempty K]
    (bf : Hash.BlockField F n) (E : K → Perm n) :
    ProbPDS (TQ n cap tcap) (TM n cap) :=
  PFunPDS.Prob.functionEvaluator ⟨Dist.uniform K, Dist.uniform_isProbDist⟩
    (fun k => hctr2Fun bf (E k))

/-! ### `±rnd` — §3.4's ideal world

The paper's main lemma (§3.4) does not compare `HCTR2[Perm(n)]` with `±p̃rp`
directly.  It compares it with `±rnd`, "which maps every query to a random
response such that all responses of the appropriate length are equally likely",
and pays for the difference with the PRP-RND lemma in §3.5.

`±rnd` is a random *function*, not a permutation: no injectivity, and no
consistency between the two directions.  Length preservation is structural here
too — the table is indexed by the query, and its value at `z` has the length
class of `z`'s message, so `rndFun` cannot produce a response of the wrong
length. -/

/-- The response table `±rnd` draws: one string per query, of that query's
length class. -/
abbrev RndTable (n cap tcap : ℕ) : Type := ∀ z : TQ n cap tcap, BitString (n + z.2.2.1.val)

/-- The oracle of a response table. -/
def rndFun (f : RndTable n cap tcap) : TQ n cap tcap → TM n cap := fun z => ⟨z.2.2.1, f z⟩

/-- The full key `±rnd` draws: a response table, the pair `(h̄, L)`, and one leftover
per query.  Only the table is used to answer; the rest is the "random output of the
expected length" that §3.4 substitutes for `HCTR2[Perm(n)]`'s extra information.
Carrying it in the key — rather than in a second, augmented system — is what makes
§3.4's augmentation a refinement of the *observation*.

**The expected length is `padLen n j - j`, not `n`.**  §3.4's `Dˢ` is
`XCTR_π(Sˢ)[|Pˢ| − n; nmˢ − |Pˢ|]`, so it is the tail of the last keystream block and
its width is whatever the padding added.  Handing world `Y` an `n`-bit block instead
gives the two augmented laws *disjoint supports*, which would make §3.4.1's ratio
false rather than merely unproved. -/
abbrev RndKey (n cap tcap : ℕ) : Type :=
  RndTable n cap tcap × (BitString n × BitString n) ×
    (∀ z : TQ n cap tcap, BitString (padLen n z.2.2.1.val - z.2.2.1.val))

/-- `±rnd` — the generic independent-response system at HCTR2's message
fibers.  The augmented proof later uses an equivalent representative with
additional independent reveal coins. -/
noncomputable def rnd (n cap tcap : ℕ) : ProbPDS (TQ n cap tcap) (TM n cap) :=
  TweakablePRP.rnd
    (MsgK := fun j : Fin (cap + 1) => BitString (n + j.val)) (T := Tweak tcap)

/-! ### The adversary classes and the two advantages -/

/-- Blocks charged to one query: `⌈|Tˢ|/n⌉ + ⌈|Pˢ|/n⌉`. -/
def qBlocks (x : TQ n cap tcap) : ℕ :=
  numBlocks n x.2.1.len + numBlocks n x.2.2.len

/-- The paper's resource predicate: at most `q` answered queries and at most
`σ` charged blocks.  It is installed on both systems as a common domain
filter; the time bound is omitted because this surface has no cost model. -/
def Budget (q σ : ℕ) (l : List (TQ n cap tcap)) : Prop :=
  l.length ≤ q ∧ (l.map qBlocks).sum ≤ σ

/-- `Budget` is prefix-closed: removing a suffix cannot increase either the
query count or the block cost. -/
theorem budget_prefixClosed (q σ : ℕ) :
    PrefixClosed (Budget (n := n) (cap := cap) (tcap := tcap) q σ) := by
  rintro l₁ l₂ ⟨t, rfl⟩ ⟨hlen, hσ⟩
  rw [List.map_append, List.sum_append] at hσ
  exact ⟨le_trans (by simp) hlen, by omega⟩

/-- The paper's at-most-`(q,σ)` resource restriction as the ordinary bundled
Random Systems domain filter. -/
def budget (q σ : ℕ) : PFunPDS.DomFilter (TQ n cap tcap) :=
  ⟨Budget q σ, budget_prefixClosed q σ⟩

/-- The remaining §3.4 environment restriction on a raw partial-resource
transcript.  Rejected attempts are discarded and the reusable tweakable-PRP
predicate is applied to the answered pair list.  Resource accounting is not
duplicated here; it is already enforced by `budget`. -/
def PaperNonPointless
    (t : List (TQ n cap tcap × Option (TM n cap))) : Prop :=
  TweakablePRP.NPList (PFunDDS.answeredEntries t)

/-- The paper's no-pointless restriction on an environment.  It is stated
possibilistically, independently of either system: every raw transcript prefix
consistent with the environment has a no-pointless answered subtranscript. -/
def EnvAvoidsPointless
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) : Prop :=
  ∀ t : List (TQ n cap tcap × Option (TM n cap)),
    (∀ k (hk : k < t.length),
      e (PFunDDS.transcriptOutputs (t.take k)) = some (t[k].1)) →
    PaperNonPointless t

/-- Direct range premise used by the `S_i ≠ S_j` cells of Figures 4–5: every
message length class has at most `2^n` block-cipher inputs.  The paper's message
cap implies this; keeping the proof-use condition explicit gives the abstract
main lemma its most general honest statement. -/
def MessageBlocksInRange (n cap : ℕ) : Prop :=
  ∀ j : Fin (cap + 1), numBlocks n (n + j.val) ≤ 2 ^ n

/-- `Adv^{±prp}_E(q)` — the block-cipher distinguishing advantage.

The paper maximizes over `A(q,t)`.  Here `⌈q⌉` installs the common at-most-`q`
domain filter, while `Δ` supplies the supremum over deterministic environments;
only the unmodeled time coordinate is omitted. -/
noncomputable def advPRP {K : Type} [Fintype K] [Nonempty K]
    (E : K → Perm n) (q : ℕ) : ℝ :=
  Δ(⌈q⌉ (pmE E).val, ⌈q⌉ (pmPerm n).val)

/-- `Adv^{±rnd}_{HCTR2[Perm(n)]}(q, σ)` — §3.4's proof-facing intermediate
quantity.  Both resources carry the same `budget q σ` domain filter, which is
the genuine at-most-resource restriction.  The supremum is additionally
restricted to no-pointless environments because `±rnd` is not a coherent
two-sided permutation: that restriction can be normalized away only around
the two coherent endpoints of the full hybrid. -/
noncomputable def advRnd (bf : Hash.BlockField F n) (q σ : ℕ) : ℝ :=
  restrictedLawFamilyAdvantage
    (fun p : PFunDDS.DDE (TQ n cap tcap) (TM n cap) × ℕ =>
      EnvAvoidsPointless p.1)
    (fun p => transcriptDist
      (PFunPDS.filterOf (budget q σ) (rnd n cap tcap).val) p.1 p.2)
    (fun p => transcriptDist
      (PFunPDS.filterOf (budget q σ)
        (hctr2Perm (cap := cap) (tcap := tcap) bf).val) p.1 p.2)

/-- The main lemma's bound, `(3σ² + 2qσ + 7σ + 2)/2ⁿ⁺¹` (paper p. 17). -/
noncomputable def mainBound (n q σ : ℕ) : ℝ :=
  (3 * σ ^ 2 + 2 * q * σ + 7 * σ + 2) / 2 ^ (n + 1)

/-- `Adv^{±p̃rp}_{HCTR2[E]}(q, σ)` as the canonical Random Systems distance
between the two commonly resource-filtered systems.  This is the paper's
maximum over `A(q,σ,t)`, apart from the unmodeled time coordinate: `Δ` supplies
the adversary supremum and `budget q σ` itself supplies both at-most resource
restrictions.  No exact-count advantage is introduced. -/
noncomputable def advTPRP {K : Type} [Fintype K] [Nonempty K]
    (bf : Hash.BlockField F n) (E : K → Perm n) (q σ : ℕ) : ℝ :=
  Δ(PFunPDS.filterOf (budget q σ) (hctr2E bf E).val,
    PFunPDS.filterOf (budget q σ) (tprp n cap tcap).val)

end Sec

/-! ## Paper §3.2 — Hash function (pp. 6–7)

§2.2 defined `H_h̄(T,M)` as a *value*.  §3.2 introduces the different object the
security argument actually reasons about: `H(T,M)` as a **formal polynomial in
`h`**, of which `H_h̄` is the evaluation at `h = x⁻ⁿh̄`.  The paper is explicit
that formal equality is meant — "`h+2` and `2h+1` can be equal in value if
`h = 1`, they are not equal as formal polynomials".

The paper's four structural properties of the map `(T,M) ↦ H(T,M)`:

1. the map is injective                              (Appendix A)
2. the polynomial is never `0` or `xⁿh`
3. the constant term is always zero
4. `deg ≤ d(T,M) = 1 + ⌈|T|/n⌉ + ⌈|M|/n⌉`

Property 1 is Appendix A, proved below as `AppendixA.Facts.Hpoly_injective`; its
two halves are `Facts.poly_inj` — the polynomial determines the coefficient
string, because the mode block is never zero (`Facts.polyStr_head_ne_zero`) — and
`AppendixA.Facts.getTM_polyStr`, which reads `(T,M)` back off that string.

Property 2 is `Facts.Hpoly_ne_zero` and `Facts.Hpoly_ne_x_pow_mul_X`.  Both are
the same single coefficient: `H(T,M).coeff (l−1)` is the mode block, which is
nonzero, and `C(xⁿ)·X` carries no coefficient above `1` — so the two can only
meet at `l = 2`, the paper's degenerate `|T| = |M| = 0`
(`Facts.degenerate_of_numBlocks_eq_two`), where the mode block is `bin(2) = x`
and meeting would force `xⁿ = x`.  The paper defers that last step to the
concrete field ("Since `x^{n−1} ≠ 1`"), but it is really a statement about the
*power basis*: `Hash.Facts.x_pow_pred_ne_one` reads it off `enc_pow` and the
injectivity of `enc`, so property 2 needs no hypothesis beyond the cap.

Property 3 is `Facts.Hpoly_coeff_zero`, and it is not true by construction: §3.2
appends `0ⁿ` to the *string*, so what is proved is that chunking finds it again as
the last block (`Facts.polyStr_last`).  Appending `[0]` to the block list instead
would have made the property definitional and the paper's phrasing vacuous.

Property 4 is `Facts.Hpoly_natDegree_le`, the paper's phrasing, derived from
`Facts.Hpoly_natDegree`: the degree is *exactly* `d(T,M)`.  `poly_natDegree_le`
bounds any `poly` by its block count; the nonzero mode block turns that into an
equality, and `Facts.polyStr_len` supplies the count — the hashed string is
`d(T,M) + 1` blocks, the `+ 1` being the trailing `0ⁿ`.  The unaligned branch
lands on the same `d` because the `10*` bit costs no extra block
(`Bits.Facts.numBlocks_succ_of_not_dvd`).

The three probability properties of `H_h̄` that follow from these four
structural facts are proved later as `Poly.Facts.prop1`, `prop2`, and `prop3`.
They are application ingredients for §3.4's collision estimates; they are not
hypotheses of the carrier-independent H-coefficient theorem in §3.3. -/

namespace Poly

open Bits Bits.Facts Hash Polynomial

variable {F : Type} [Field F] {n : ℕ}

/-- **`poly`** (paper p. 6): `poly(M₀‖⋯‖M_{l−1}) = M₀h^{l−1} ⊕ ⋯ ⊕ M_{l−1}` —
block `i` at power `h^{l−1−i}`, so block `0` leads and the **last block is the
constant term**. -/
noncomputable def poly (bs : List F) : Polynomial F :=
  ∑ i : Fin bs.length, C (bs.get i) * X ^ (bs.length - 1 - i.val)

/-- **`d(T,M)`** (paper p. 7): `1 + ⌈|T|/n⌉ + ⌈|M|/n⌉`. -/
def d (n tlen mlen : ℕ) : ℕ := 1 + numBlocks n tlen + numBlocks n mlen

/-- **The string §3.2 hashes**: §2.2's `hashStr` with the trailing `0ⁿ` the
polynomial display appends,

    bin(2|T|+2) ‖ pad(T) ‖ M ‖ 0ⁿ            if n divides |M|
    bin(2|T|+3) ‖ pad(T) ‖ pad(M‖1) ‖ 0ⁿ     otherwise

spelled once so that `Hpoly` and Appendix A cannot drift apart: Appendix A's `X`
*is* this string (`AppendixA.Facts.getTM_polyStr`). -/
def polyStr {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) : Σ w : ℕ, BitString w :=
  ⟨_, (hashStr (n := n) T M).2 ∥ bin n 0⟩

/-- **`H(T,M)` as a formal polynomial** (paper p. 7): `poly` of `polyStr`.

The argument is the paper's **bit-string** concatenation, `0ⁿ` included, chunked
into blocks and read into the field — *not* §2.2's block list with a zero block
appended at the list level.  The two differ in what they assume: appending `[0]`
to the list makes "the constant term is zero" true by construction, whereas the
paper states it as a property to be *proved*, of the string it actually hashes.
`H_h̄` is this polynomial evaluated at `h = x⁻ⁿh̄`. -/
noncomputable def Hpoly (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    Polynomial F :=
  poly ((blocks n (polyStr (n := n) T M).2).map bf.enc)

/-! ## Facts -/

namespace Facts

/-- Coefficient extraction: the exponents `l−1−i` are distinct across `i`. -/
theorem poly_coeff (bs : List F) (i : Fin bs.length) :
    (poly bs).coeff (bs.length - 1 - i.val) = bs.get i := by
  rw [poly, finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hji ?_), mul_zero]
    exact Fin.val_injective (by have := i.isLt; have := j.isLt; omega)
  · exact fun h => absurd (Finset.mem_univ i) h

theorem poly_natDegree_le (bs : List F) : (poly bs).natDegree ≤ bs.length - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    le_trans (natDegree_C_mul_le _ _)
      (le_trans (natDegree_X_pow_le _) (by have := i.isLt; omega))

/-- The constant term of `poly` is its last block. -/
theorem poly_coeff_zero {bs : List F} (h : 0 < bs.length) :
    (poly bs).coeff 0 = bs.getD (bs.length - 1) 0 := by
  rw [List.getD_eq_getElem _ _ (by omega)]
  simpa using poly_coeff bs ⟨bs.length - 1, by omega⟩

/-- `poly` as a range sum — the same display with a plain `ℕ` index, so that
appending a block is not a dependent rewrite. -/
theorem poly_eq_sum_range (bs : List F) :
    poly bs = ∑ i ∈ Finset.range bs.length, C (bs.getD i 0) * X ^ (bs.length - 1 - i) := by
  rw [poly, ← Fin.sum_univ_eq_sum_range (fun i => C (bs.getD i 0) * X ^ (bs.length - 1 - i))]
  exact Finset.sum_congr rfl (fun i _ => by rw [List.getD_eq_getElem _ _ i.isLt]; simp)

/-- **Horner**: one more block multiplies by `h` and adds.  The paper's display
`poly(M₀‖⋯‖M_{l−1}) = M₀h^{l−1} ⊕ ⋯ ⊕ M_{l−1}` read as a recursion, and the exact
companion of `Hash.Facts.POLYVAL_concat`. -/
theorem poly_concat (bs : List F) (b : F) : poly (bs ++ [b]) = poly bs * X + C b := by
  rw [poly_eq_sum_range, poly_eq_sum_range, show (bs ++ [b]).length = bs.length + 1 by simp,
    Finset.sum_range_succ]
  have hlast : (bs ++ [b]).getD bs.length 0 = b := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have hinit : ∀ i ∈ Finset.range bs.length,
      C ((bs ++ [b]).getD i 0) * X ^ (bs.length + 1 - 1 - i)
        = C (bs.getD i 0) * X ^ (bs.length - 1 - i) * X := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hi,
      ← List.getD_eq_getElem _ _ hi,
      show bs.length + 1 - 1 - i = bs.length - 1 - i + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hinit, ← Finset.sum_mul, hlast]
  simp

/-- **A trailing zero block is multiplication by `h`.**  `poly` gives block `i` the
power `h^{l−1−i}`, so one more block at the bottom shifts every power up by one
and contributes nothing at `h⁰`. -/
theorem poly_cat_zero (bs : List F) : poly (bs ++ [0]) = poly bs * X := by
  rw [poly_concat, map_zero, add_zero]

/-- **POLYVAL's value has no constant term** — for any blocks at all.  Its fold
multiplies by `z = h̄x⁻ⁿ` *after* adding each block, the last one included, so
`POLYVAL(h̄, M₀‖⋯‖M_{l−1}) = M₀z^l + ⋯ + M_{l−1}z¹`, with no `z⁰` term.

This is the structural fact behind §3.2's trailing `0ⁿ`, and it is worth being
precise about which way the implication runs.  The formal polynomial whose
evaluation is `H_h̄` is *forced* to be `h · poly(S)`; `poly(S‖0ⁿ)` is just how §3.2
writes that in its own `poly(·)` notation (`poly_cat_zero`).  So property 3, "the
constant term is always zero", is not a separate property the format happens to
enjoy — it is this same fact restated, and `H_eq_eval` could not hold without it. -/
theorem POLYVAL_eq_mul_eval (u h : F) (bs : List F) :
    POLYVAL u h bs = h * u * (poly bs).eval (h * u) := by
  induction bs using List.reverseRecOn with
  | nil => simp [POLYVAL, poly]
  | append_singleton bs b ih =>
    rw [Hash.Facts.POLYVAL_concat, ih]
    simp only [poly_concat, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    ring

/-- **`POLYVAL(h̄, ·)` is `poly` evaluated at `x⁻ⁿh̄`** — §2.2's value is §3.2's
formal polynomial, at the point §3.2 says.  The `[0]` carries the factor of `z`
that `POLYVAL_eq_mul_eval` exhibits. -/
theorem POLYVAL_eq_eval (u h : F) (bs : List F) :
    POLYVAL u h bs = (poly (bs ++ [0])).eval (h * u) := by
  rw [poly_cat_zero, Polynomial.eval_mul, Polynomial.eval_X, POLYVAL_eq_mul_eval]
  ring

/-- The top coefficient of `poly` is its first block. -/
theorem poly_coeff_top {bs : List F} (h : 0 < bs.length) :
    (poly bs).coeff (bs.length - 1) = bs.getD 0 0 := by
  rw [List.getD_eq_getElem _ _ h]
  simpa using poly_coeff bs ⟨0, h⟩

/-- With a nonzero leading block the degree is exactly `l − 1`, so the polynomial
records how many blocks it came from.  This is what §5.2.2 buys by making the
mode block never zero. -/
theorem poly_natDegree {bs : List F} (h0 : bs.getD 0 0 ≠ 0) :
    (poly bs).natDegree = bs.length - 1 := by
  have hlen : 0 < bs.length := by
    rcases bs with _ | ⟨b, bs⟩
    · exact absurd rfl h0
    · exact Nat.succ_pos _
  exact le_antisymm (poly_natDegree_le bs)
    (le_natDegree_of_ne_zero (by rw [poly_coeff_top hlen]; exact h0))

/-- **The paper's remark** "`poly(M) = poly(M′)` only if `M = 0^{ln}‖M′`": with a
nonzero leading block, the formal polynomial determines the block list.  This is
the polynomial-to-string half of Appendix A. -/
theorem poly_inj {bs cs : List F} (hb : bs.getD 0 0 ≠ 0) (hc : cs.getD 0 0 ≠ 0)
    (h : poly bs = poly cs) : bs = cs := by
  have hbl : 0 < bs.length := by
    rcases bs with _ | ⟨b, bs⟩
    · exact absurd rfl hb
    · exact Nat.succ_pos _
  have hcl : 0 < cs.length := by
    rcases cs with _ | ⟨c, cs⟩
    · exact absurd rfl hc
    · exact Nat.succ_pos _
  have hlen : bs.length = cs.length := by
    have h1 := poly_natDegree hb
    rw [h, poly_natDegree hc] at h1
    omega
  refine List.ext_getElem hlen (fun i h₁ h₂ => ?_)
  have e₁ : (poly bs).coeff (bs.length - 1 - i) = bs[i] := by
    simpa using poly_coeff bs ⟨i, h₁⟩
  have e₂ : (poly cs).coeff (cs.length - 1 - i) = cs[i] := by
    simpa using poly_coeff cs ⟨i, h₂⟩
  rw [← e₁, ← e₂, h, hlen]

/-! ### The string §3.2 hashes -/

/-- The `n ∣ |M|` branch. -/
theorem polyStr_aligned {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) (h : n ∣ k) :
    polyStr (n := n) T M = ⟨_, (bin n (2 * T.len + 2) ∥ pad n T.2 ∥ M) ∥ bin n 0⟩ := by
  rw [polyStr, hashStr, if_pos h]

/-- The `n ∤ |M|` branch. -/
theorem polyStr_unaligned {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) (h : ¬ n ∣ k) :
    polyStr (n := n) T M
      = ⟨_, (bin n (2 * T.len + 3) ∥ pad n T.2 ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0⟩ := by
  rw [polyStr, hashStr, if_neg h]

/-- Every piece of the hashed string is a whole number of blocks. -/
theorem dvd_polyStr {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    n ∣ (polyStr (n := n) T M).1 := by
  by_cases h : n ∣ k
  · rw [polyStr_aligned T M h]
    exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_add dvd_rfl (dvd_padLen n T.len)) h) dvd_rfl
  · rw [polyStr_unaligned T M h]
    exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_add dvd_rfl (dvd_padLen n T.len))
      (dvd_padLen n (k + 1))) dvd_rfl

theorem polyStr_len_pos (hn : 0 < n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    0 < (polyStr (n := n) T M).1 :=
  lt_of_lt_of_le hn (Nat.le_add_left n (hashStr (n := n) T M).1)

/-- The mode block leads the hashed string — `n ∣ |M|` branch. -/
theorem polyStr_head_aligned {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) (h : n ∣ k) :
    (polyStr (n := n) T M).2[0; n] = bin n (2 * T.len + 2) := by
  rw [polyStr_aligned T M h]
  exact Hash.Facts.shape_mode _ _ _

/-- The mode block leads the hashed string — `n ∤ |M|` branch. -/
theorem polyStr_head_unaligned {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) (h : ¬ n ∣ k) :
    (polyStr (n := n) T M).2[0; n] = bin n (2 * T.len + 3) := by
  rw [polyStr_unaligned T M h]
  exact Hash.Facts.shape_mode _ _ _

/-- **§5.2.2's "it is never zero"**: the mode block leads the hashed string and is
nonzero, so the degree of `H(T,M)` pins down the number of blocks. -/
theorem polyStr_head_ne_zero {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) : (polyStr (n := n) T M).2[0; n] ≠ 0 := by
  by_cases h : n ∣ k
  · rw [polyStr_head_aligned T M h]
    exact bin_ne_zero (by omega) (by omega)
  · rw [polyStr_head_unaligned T M h]
    exact bin_ne_zero (by omega) (by omega)

/-- The `0ⁿ` §3.2 appends is the last block of the hashed string.  This is the
read that makes property 3 a theorem rather than a construction: the zero block
is appended to the *string*, so it has to be found again in the block list. -/
theorem polyStr_last {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    (polyStr (n := n) T M).2[(polyStr (n := n) T M).1 - n; n] = 0 := by
  by_cases h : n ∣ k
  · rw [polyStr_aligned T M h]
    show ((bin n (2 * T.len + 2) ∥ pad n T.2 ∥ M) ∥ bin n 0)[
      n + padLen n (T.1 : ℕ) + k + n - n; n] = 0
    rw [show n + padLen n (T.1 : ℕ) + k + n - n = n + padLen n (T.1 : ℕ) + k by omega]
    exact Hash.Facts.shape_top _ _ _
  · rw [polyStr_unaligned T M h]
    show ((bin n (2 * T.len + 3) ∥ pad n T.2 ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0)[
      n + padLen n (T.1 : ℕ) + padLen n (k + 1) + n - n; n] = 0
    rw [show n + padLen n (T.1 : ℕ) + padLen n (k + 1) + n - n
      = n + padLen n (T.1 : ℕ) + padLen n (k + 1) by omega]
    exact Hash.Facts.shape_top _ _ _

/-- The hashed string is at least two blocks: the mode block and the trailing `0ⁿ`. -/
theorem two_le_numBlocks_polyStr (hn : 0 < n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    2 ≤ numBlocks n (polyStr (n := n) T M).1 := by
  rw [numBlocks_of_dvd hn (dvd_polyStr T M)]
  have h2n : 2 * n ≤ (polyStr (n := n) T M).1 := by
    by_cases h : n ∣ k
    · rw [polyStr_aligned T M h]
      show 2 * n ≤ n + padLen n T.len + k + n
      omega
    · rw [polyStr_unaligned T M h]
      show 2 * n ≤ n + padLen n T.len + padLen n (k + 1) + n
      omega
  calc 2 = 2 * n / n := by rw [Nat.mul_div_cancel _ hn]
    _ ≤ _ := Nat.div_le_div_right h2n

/-- **The paper's "`H(T,M)` can be of degree 1 only if `|T| = |M| = 0`"** (p. 7).
The unaligned branch cannot reach two blocks: `pad(M‖1)` is a block of its own. -/
theorem degenerate_of_numBlocks_eq_two (hn : 0 < n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (h : numBlocks n (polyStr (n := n) T M).1 = 2) : T.len = 0 ∧ k = 0 := by
  rw [numBlocks_of_dvd hn (dvd_polyStr T M)] at h
  have hW : (polyStr (n := n) T M).1 = 2 * n := by
    have hd := Nat.div_mul_cancel (dvd_polyStr (n := n) T M)
    rw [h] at hd
    omega
  by_cases hdvd : n ∣ k
  · rw [polyStr_aligned T M hdvd] at hW
    have hW' : n + padLen n T.len + k + n = 2 * n := hW
    have := le_padLen hn T.len
    exact ⟨by omega, by omega⟩
  · rw [polyStr_unaligned T M hdvd] at hW
    have hW' : n + padLen n T.len + padLen n (k + 1) + n = 2 * n := hW
    have := le_padLen' hn (show 0 < k + 1 by omega)
    omega

/-! ### §3.2's property 2 — the polynomial is never `0` nor `xⁿh`

Both halves are one coefficient: `H(T,M).coeff (l−1)` is the mode block, which is
nonzero.  `C(xⁿ)·X` has no coefficient above `1`, so it can only agree at `l = 2`
— the degenerate case, where the mode block is `bin(2) = x` and agreement would
force `xⁿ = x`. -/

/-- The leading coefficient of `H(T,M)` is the mode block, read into the field. -/
theorem Hpoly_coeff_top (bf : BlockField F n) (hn : 0 < n) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) :
    (Hpoly bf T M).coeff (numBlocks n (polyStr (n := n) T M).1 - 1)
      = bf.enc ((polyStr (n := n) T M).2[0; n]) := by
  have hW := polyStr_len_pos hn T M
  have hnb : 0 < numBlocks n (polyStr (n := n) T M).1 := Nat.div_pos (by omega) hn
  have hlen : ((blocks n (polyStr (n := n) T M).2).map bf.enc).length
      = numBlocks n (polyStr (n := n) T M).1 := by simp
  rw [Hpoly, ← hlen, poly_coeff_top (by omega), getD_map_blocks_zero hn hW]

/-- **The hashed string is `d(T,M) + 1` blocks.**  The paper's `d` counts the mode
block, the padded tweak and the message; the `+ 1` is §3.2's trailing `0ⁿ`.  In
the unaligned branch the `10*` bit costs no extra block
(`Bits.Facts.numBlocks_succ_of_not_dvd`), which is what lets one `d` serve both. -/
theorem polyStr_len (hn : 0 < n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    (polyStr (n := n) T M).1 = n * (d n T.len k + 1) := by
  have h1 : padLen n T.len = n * numBlocks n T.len := padLen_eq_mul n T.len
  by_cases h : n ∣ k
  · rw [polyStr_aligned T M h]
    show n + padLen n T.len + k + n = n * (d n T.len k + 1)
    have h2 : n * numBlocks n k = k := by
      rw [numBlocks_of_dvd hn h]; exact Nat.mul_div_cancel' h
    rw [d, h1, show n * (1 + numBlocks n T.len + numBlocks n k + 1)
      = n + n * numBlocks n T.len + n * numBlocks n k + n by ring, h2]
  · rw [polyStr_unaligned T M h]
    show n + padLen n T.len + padLen n (k + 1) + n = n * (d n T.len k + 1)
    rw [d, h1, padLen_eq_mul n (k + 1), numBlocks_succ_of_not_dvd hn h,
      show n * (1 + numBlocks n T.len + numBlocks n k + 1)
        = n + n * numBlocks n T.len + n * numBlocks n k + n by ring]

/-- The leading block of `H(T,M)`'s coefficient list — the mode block — is nonzero.
This is the hypothesis both `poly_natDegree` and `poly_inj` want. -/
theorem Hpoly_blocks_head_ne_zero (bf : BlockField F n) (hn : 0 < n) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) (hcap : 2 * T.len + 3 < 2 ^ n) :
    ((blocks n (polyStr (n := n) T M).2).map bf.enc).getD 0 0 ≠ 0 := by
  rw [getD_map_blocks_zero hn (polyStr_len_pos hn T M), Ne, Hash.Facts.enc_eq_zero_iff]
  exact polyStr_head_ne_zero T M hcap

/-- **§3.2, property 4** — `H(T,M)` has degree *exactly* `d(T,M)`.  The paper
claims only `≤`; §5.2.2's nonzero mode block (`polyStr_head_ne_zero`) pins the
degree to the block count, so the bound is tight at every `(T, M)`. -/
theorem Hpoly_natDegree (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) : (Hpoly bf T M).natDegree = d n T.len k := by
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  have hlen : ((blocks n (polyStr (n := n) T M).2).map bf.enc).length
      = numBlocks n (polyStr (n := n) T M).1 := by simp
  rw [Hpoly, poly_natDegree (Hpoly_blocks_head_ne_zero bf hn T M hcap), hlen,
    polyStr_len hn T M, numBlocks_of_dvd hn ⟨d n T.len k + 1, rfl⟩,
    Nat.mul_div_cancel_left _ hn]
  omega

/-- **§3.2, property 4 as the paper states it** — `deg H(T,M) ≤ d(T,M)`. -/
theorem Hpoly_natDegree_le (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) : (Hpoly bf T M).natDegree ≤ d n T.len k :=
  le_of_eq (Hpoly_natDegree bf T M hcap)

/-- **§3.2, property 3** — the constant term of `H(T,M)` is always zero.

Not true by construction: §3.2 appends `0ⁿ` to the *string*, so what has to be
shown is that chunking finds it again as the last block.  Unconditional — the cap
never enters, because the mode block is not involved. -/
theorem Hpoly_coeff_zero (bf : BlockField F n) (hn : 0 < n) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) : (Hpoly bf T M).coeff 0 = 0 := by
  have hW := polyStr_len_pos hn T M
  have hnb : 0 < numBlocks n (polyStr (n := n) T M).1 := Nat.div_pos (by omega) hn
  have hlen : ((blocks n (polyStr (n := n) T M).2).map bf.enc).length
      = numBlocks n (polyStr (n := n) T M).1 := by simp
  rw [Hpoly, poly_coeff_zero (by omega), hlen,
    getD_map_blocks_last hn (dvd_polyStr T M) hW, polyStr_last T M, Hash.Facts.enc_zero]

/-- **§3.2, property 2 (first half)** — `H(T,M)` is never the zero polynomial. -/
theorem Hpoly_ne_zero (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) : Hpoly bf T M ≠ 0 := by
  obtain ⟨hn, -⟩ := cap_bounds hcap
  intro h
  have hc := Hpoly_coeff_top bf (by omega) T M
  rw [h, Polynomial.coeff_zero] at hc
  exact polyStr_head_ne_zero T M hcap ((Hash.Facts.enc_eq_zero_iff bf).mp hc.symm)

/-- **§3.2, property 2 (second half)** — `H(T,M)` is never `xⁿh`.  Unconditional:
the paper's `xⁿ ≠ x` is `Hash.Facts.x_pow_ne_self`, forced by the power basis of
`BlockField`. -/
theorem Hpoly_ne_x_pow_mul_X (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) : Hpoly bf T M ≠ C (bf.x ^ n) * X := by
  obtain ⟨hn, -⟩ := cap_bounds hcap
  intro h
  have h2 := two_le_numBlocks_polyStr (show 0 < n by omega) T M
  have hc := Hpoly_coeff_top bf (show 0 < n by omega) T M
  rw [h, Polynomial.coeff_C_mul, Polynomial.coeff_X] at hc
  rcases Nat.lt_or_ge 2 (numBlocks n (polyStr (n := n) T M).1) with hgt | hle
  · rw [if_neg (by omega), mul_zero] at hc
    exact polyStr_head_ne_zero T M hcap ((Hash.Facts.enc_eq_zero_iff bf).mp hc.symm)
  · have hl2 : numBlocks n (polyStr (n := n) T M).1 = 2 := by omega
    obtain ⟨ht, hk⟩ := degenerate_of_numBlocks_eq_two (show 0 < n by omega) T M hl2
    rw [hl2, if_pos rfl, mul_one, polyStr_head_aligned T M (hk ▸ dvd_zero n), ht] at hc
    rw [show 2 * 0 + 2 = 2 from rfl, Hash.Facts.enc_two bf hn] at hc
    exact Hash.Facts.x_pow_ne_self bf hn hc


/-! ### §2.2 meets §3.2

"`H_h̄(T, M)` is then evaluation of this polynomial at `h = x⁻ⁿh̄`" (p. 6–7).

**The two sections hash different strings, and that is the paper's doing, not a
transcription slip.**  §2.2 (p. 4) defines `H_h̄` as `POLYVAL(h̄, bin(2|T|+2)‖
pad(T)‖M)`; §3.2 (p. 7) defines `H` as `poly(bin(2|T|+2)‖pad(T)‖M‖0ⁿ)`, with a
trailing `0ⁿ` the first does not have.  Anyone tempted to make `hashInput` and
`polyStr` agree should read `Facts.POLYVAL_eq_mul_eval` first: POLYVAL's fold
leaves a factor of `z = h̄x⁻ⁿ` in front, so the polynomial whose evaluation it is
must be `h · poly(S)`, and `poly(S‖0ⁿ)` is exactly that. -/

/-- The block list §3.2 hashes is §2.2's with the zero block appended. -/
theorem blocks_polyStr (hn : 0 < n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) :
    blocks n (polyStr (n := n) T M).2 = hashInput (n := n) T M ++ [bin n 0] :=
  blocks_cat_block hn (Hash.Facts.dvd_hashStr T M) _ _

/-- **The bridge** (paper p. 6–7): `H_h̄(T, M)` is `H(T, M)` evaluated at
`h = x⁻ⁿh̄`. -/
theorem H_eq_eval (bf : BlockField F n) (hn : 0 < n) (h : F) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) :
    H bf h T M = (Hpoly bf T M).eval (h * bf.u) := by
  have hz : bf.enc (bin n 0) = 0 := Hash.Facts.enc_zero bf
  rw [H, POLYVAL_eq_eval, Hpoly, blocks_polyStr hn T M, List.map_append, List.map_cons,
    List.map_nil, hz]

/-- The bridge in the form Figures 2–3 use: the hash of `(T, M)` under the key
block `h̄`, as the formal polynomial evaluated at `x⁻ⁿh̄`. -/
theorem hashBits_eq (bf : BlockField F n) (hn : 0 < n) (hbar : BitString n) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) :
    hashBits bf hbar T M = bf.enc.symm ((Hpoly bf T M).eval (bf.enc hbar * bf.u)) := by
  rw [hashBits, H_eq_eval bf hn]

/-! ### The root count

The one probabilistic ingredient §3.2's three `H_h̄` properties share: "For any
nonzero polynomial `p(h)` in `GF(2ⁿ)`, there are at most `deg(p)` values `h` such
that `p(h) = 0` … Since multiplication by a nonzero field element is a bijection
of the field to itself, it follows that `Pr_{h̄}[p(x⁻ⁿh̄) = 0] ≤ deg(p)/2ⁿ`"
(p. 7).  Counted over the keys `h̄ ∈ {0,1}ⁿ`, of which there are `2ⁿ`
(`Bits.Facts.card_Str`) — so this *is* the paper's `deg(p)/2ⁿ`, with the choice of
probability formalism deferred to whoever states the three properties. -/

/-- **The root count** (paper p. 7), transported along the paper's substitution
`h̄ ↦ x⁻ⁿh̄`.  Stated for an arbitrary nonzero multiplier `v`, since the transport
uses nothing about `x⁻ⁿ` but `Hash.Facts.u_ne_zero`. -/
theorem card_keys_root_le [DecidableEq F] (bf : BlockField F n) {p : Polynomial F}
    (hp : p ≠ 0) {v : F} (hv : v ≠ 0) :
    (Finset.univ.filter fun hbar : BitString n => p.eval (bf.enc hbar * v) = 0).card
      ≤ p.natDegree := by
  have hinj : Function.Injective (fun hbar : BitString n => bf.enc hbar * v) := fun a b hab =>
    bf.enc.injective (mul_right_cancel₀ hv hab)
  calc (Finset.univ.filter fun hbar : BitString n => p.eval (bf.enc hbar * v) = 0).card
      = ((Finset.univ.filter fun hbar : BitString n => p.eval (bf.enc hbar * v) = 0).image
          fun hbar => bf.enc hbar * v).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ p.roots.toFinset.card := by
        refine Finset.card_le_card (fun z hz => ?_)
        simp only [Finset.mem_image, Finset.mem_filter] at hz
        obtain ⟨hb, ⟨-, hroot⟩, rfl⟩ := hz
        exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hp, hroot⟩)
    _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
    _ ≤ p.natDegree := p.card_roots'

end Facts


/-! ### The paper's `n = 128` instantiation

`BlockField` carries an axiom (`enc_pow`), so everything above would be vacuous
if no `BlockField` existed.  It does: the paper's own field, `GF(2¹²⁸)` presented
as `GF(2)[X]/(x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1)` with the power basis, is
`RandomSystems/HTechnique/GF2Field.lean`.  This is the receipt, and the only
place in the file that mentions a concrete `n`. -/

namespace GF128

open RandomSystems.HTechnique.GF2Field

/-- **The paper's block↔field reading at `n = 128`.**  `enc` is `gf128OfNat` on
the block's value, `enc_xor` is `gf128OfNat_xor`, and `enc_pow` is the power
basis `toPoly_two_pow`. -/
noncomputable def blockField : BlockField GF128 128 where
  enc := (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
    BitString 128 ≃ Fin (2 ^ 128)).trans gf128FinEquiv
  enc_xor a b := by
    show gf128OfNat (a ^^^ b).toNat = gf128OfNat a.toNat + gf128OfNat b.toNat
    rw [BitVec.toNat_xor, gf128OfNat_xor]
  x := xGF
  enc_pow j hj := by
    show gf128OfNat (bin 128 (2 ^ j)).toNat = xGF ^ j
    rw [bin, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj), gf128OfNat,
      toPoly_two_pow, map_pow, AdjoinRoot.mk_X, xGF]

/-- Cross-check: the basis argument of `Hash.Facts.x_pow_ne_self` reproduces
`GF2Field.xGF_pow_n_ne_x`, which was proved from the modulus instead. -/
example : xGF ^ 128 ≠ xGF := Hash.Facts.x_pow_ne_self blockField (by norm_num)

/-- Cross-check: the reading's dot unit is the paper's
`x⁻¹²⁸ = x¹²⁷+x¹²⁴+x¹²¹+x¹¹⁴+1`, i.e. `GF2Field.uPolyval`. -/
example : blockField.u = (uPolyval : GF128) := uPolyval_coe.symm

end GF128

end Poly

/-! ## Paper Appendix A — Injectivity of `H` onto polynomials (pp. 31–32)

     1: procedure GetTM(X)
     2:     assert |X| mod n = 0
     3:     assert |X| ≥ 2n
     4:     assert X[|X| − n; n] = 0ⁿ
     5:     t ← bin⁻¹_{n−1}(X[1; n − 1])
     6:     assert t > 0
     7:     t ← t − 1
     8:     w ← n(1 + ⌈t/n⌉)
     9:     if X[0; 1] = 0 then
    10:         assert w + n ≤ |X|
    11:         M ← X[w; |X| − w − n]
    12:     else
    13:         assert w + 2n ≤ |X|
    14:         assert X[|X| − 2n + 1; n − 1] ≠ 0ⁿ⁻¹
    15:         i ← |X| − n − 1
    16:         while X[i; 1] = 0 do
    17:             i ← i − 1
    18:         end while
    19:         M ← X[w; i − w]
    20:     end if
    21:     T ← X[n; t]
    22:     return T, M
    23: end procedure

`X` is "a binary string of length `|X| = n(1 + deg(H(T,M)))` representing the
coefficients of the polynomial `H(T,M)` in binary form, starting with the
greatest nonzero power".  §3.2's `poly` puts block `0` at the *highest* power, so
that string is exactly `Poly.polyStr T M` — provided the leading block is nonzero,
which §5.2.2 arranges ("It is never zero, so its position in the polynomial can
be inferred from the degree", `Poly.Facts.polyStr_head_ne_zero`).  Property 1 is
therefore two independent steps, and both are proved here:

* polynomial ⟶ string, `Poly.Facts.poly_inj` — the paper's own remark that
  `poly(M) = poly(M′)` only up to leading zero blocks;
* string ⟶ `(T, M)`, `getTM_polyStr` — Appendix A's algorithm, a left inverse.

`|X|` is the index of the dependent pair, so `getTM` takes `{0,1}*` and its
signature *is* the paper's `GetTM(X)` returning `T, M`: bare strings, with no
mention of `𝒯`.  The cap enters only in the theorems, as `2|T| + 3 < 2ⁿ` — "the
mode block `bin(2|T| + 3)` fits in `n` bits" — which the paper's
`cap = 2ⁿ⁻¹ − 2` satisfies, and which already forces `n ≥ 2`.

### The two halves of a procedure

`GetTM` does two separable things: it *checks* its input (the asserts) and it
*reads* `(T, M)` out of it (the assignments).  Only the reads carry the
injectivity argument, and they are total — nothing in lines 5, 7–9, 11, 15–19 and
21–22 can fail.  So the asserts are `Wellformed`, a predicate, and the reads are
`getTM`, a function into a plain pair; `getTM_polyStr` and `wellformed_polyStr`
are the two halves of "the procedure accepts the hashed string and returns
`(T, M)`".  Bundling them into one `Option`-valued procedure would make every
downstream statement carry a `some` for no gain, and the definitions would read
as a program rather than as the assignments they transcribe.

The paper's `t`, `w` and `|M|` become the three definitions `tlen`, `off`, `mlen`
— named, so lines 21 and 22 can be spelled once each.

Two lines are transcribed in closed form.  Line 8's `n(1 + ⌈t/n⌉)` is
`n + padLen n t`.  Lines 15–18's downward scan is *the index of the highest set
bit*, `msbIdx`: `Bits.Facts.pad10_marker` and `pad10_high` are exactly the
statement that the `10*` marker is that bit, so the loop needs no transcription,
and by line 4 its start `|X| − n − 1` finds the same bit as `|X| − 1`. -/

namespace AppendixA

open Bits Bits.Facts Hash Poly Poly.Facts

/-- The index of the highest set bit — Appendix A's `while` loop (lines 15–18) in
closed form.  `0` on the zero string, which line 14's assert excludes. -/
def msbIdx {p : ℕ} (Y : BitString p) : ℕ := Nat.findGreatest (fun i => Y.getLsbD i = true) p

/-- Lines 5 and 7 — `t`, the tweak length: `bin⁻¹` of the mode block above its
alignment flag, less the `1` §5.2.2 adds to eliminate the zero-length case. -/
def tlen (n : ℕ) (X : Σ w : ℕ, BitString w) : ℕ := (X.2[1; n - 1]).toNat - 1

/-- Line 8 — `w`, where the message begins: `n(1 + ⌈t/n⌉)`. -/
def off (n : ℕ) (X : Σ w : ℕ, BitString w) : ℕ := n + padLen n (tlen n X)

/-- Lines 9, 11 and 19 — `|M|`: up to the trailing zero block when line 9's flag
is clear, else down to the `10*` marker. -/
def mlen (n : ℕ) (X : Σ w : ℕ, BitString w) : ℕ :=
  if X.2[0; 1] = 0 then X.1 - off n X - n else msbIdx X.2 - off n X

/-- **`GetTM`'s reads** (paper Appendix A, lines 21–22): `T ← X[n; t]` and
`M ← X[w; |M|]`. -/
def getTM (n : ℕ) (X : Σ w : ℕ, BitString w) : (Σ t : ℕ, BitString t) × (Σ k : ℕ, BitString k) :=
  (⟨tlen n X, X.2[n; tlen n X]⟩, ⟨mlen n X, X.2[off n X; mlen n X]⟩)

/-- **`GetTM`'s asserts** (paper Appendix A, lines 2–4, 6, 10, 13–14). -/
def Wellformed (n : ℕ) (X : Σ w : ℕ, BitString w) : Prop :=
  X.1 % n = 0 ∧ 2 * n ≤ X.1 ∧ X.2[X.1 - n; n] = 0 ∧ 0 < (X.2[1; n - 1]).toNat ∧
    if X.2[0; 1] = 0 then off n X + n ≤ X.1
    else off n X + 2 * n ≤ X.1 ∧ X.2[X.1 - 2 * n + 1; n - 1] ≠ 0

/-! ## Facts -/

namespace Facts

/-- Lines 15–18 do find the marker: a set bit with nothing above it is `msbIdx`. -/
theorem msbIdx_eq {p : ℕ} (Y : BitString p) {j : ℕ} (hj : j ≤ p) (hset : Y.getLsbD j = true)
    (hhigh : ∀ i, j < i → Y.getLsbD i = false) : msbIdx Y = j := by
  rw [msbIdx, Nat.findGreatest_eq_iff]
  exact ⟨hj, fun _ => hset, fun i hi _ => by simp [hhigh i hi]⟩

/-- `GetTM` on the `n ∣ |M|` branch of the hashed string (line 9's `then`).  One
lemma for both halves, since they share every read. -/
private theorem run_aligned (n : ℕ) {tl : ℕ} (Tw : BitString tl) {k : ℕ} (M : BitString k)
    (hcap : 2 * tl + 3 < 2 ^ n) (hdvd : n ∣ k) :
    Wellformed n ⟨_, (bin n (2 * tl + 2) ∥ pad n Tw ∥ M) ∥ bin n 0⟩ ∧
      getTM n ⟨_, (bin n (2 * tl + 2) ∥ pad n Tw ∥ M) ∥ bin n 0⟩ = (⟨tl, Tw⟩, ⟨k, M⟩) := by
  obtain ⟨hn2, htlt⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  have hle : tl ≤ padLen n tl := le_padLen hn tl
  -- the reads (`Hash.Facts.shape_*`), specialised to `v = 2|T| + 2` and payload `M`
  have e5 : ((bin n (2 * tl + 2) ∥ pad n Tw ∥ M ∥ bin n 0)[1; n - 1]).toNat = tl + 1 := by
    rw [Hash.Facts.shape_len _ _ _ hn, toNat_bin (by omega)]
    omega
  have e9 : (bin n (2 * tl + 2) ∥ pad n Tw ∥ M ∥ bin n 0)[0; 1] = 0 := by
    rw [Hash.Facts.shape_flag _ _ _ hn, bin_one_eq_zero_iff]
    omega
  have e11 : (bin n (2 * tl + 2) ∥ pad n Tw ∥ M ∥ bin n 0)[n + padLen n tl; k] = M := by
    rw [Hash.Facts.shape_payload _ _ _ (le_refl k), sub_full]
  -- the three named intermediates
  have htlen : tlen n ⟨_, (bin n (2 * tl + 2) ∥ pad n Tw ∥ M) ∥ bin n 0⟩ = tl := by
    show ((bin n (2 * tl + 2) ∥ pad n Tw ∥ M ∥ bin n 0)[1; n - 1]).toNat - 1 = tl
    omega
  have hoff : off n ⟨_, (bin n (2 * tl + 2) ∥ pad n Tw ∥ M) ∥ bin n 0⟩
      = n + padLen n tl := by rw [off, htlen]
  have hmlen : mlen n ⟨_, (bin n (2 * tl + 2) ∥ pad n Tw ∥ M) ∥ bin n 0⟩ = k := by
    rw [mlen]
    show (if (bin n (2 * tl + 2) ∥ pad n Tw ∥ M ∥ bin n 0)[0; 1] = 0 then _ else _) = k
    rw [if_pos e9, hoff]
    show n + padLen n tl + k + n - (n + padLen n tl) - n = k
    omega
  refine ⟨?_, by rw [getTM, htlen, hmlen, hoff, e11, Hash.Facts.shape_tweak _ _ _ hn]⟩
  rw [Wellformed]
  dsimp only
  rw [hoff, if_pos e9]
  refine ⟨dvd_mod_zero (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add dvd_rfl
      (dvd_padLen n tl)) hdvd) dvd_rfl), by omega, ?_, by omega, by omega⟩
  rw [show n + padLen n tl + k + n - n = n + padLen n tl + k by omega]
  exact Hash.Facts.shape_top _ _ _

/-- `GetTM` on the `n ∤ |M|` branch (line 9's `else`), where the `10*` marker has
to be found. -/
private theorem run_unaligned (n : ℕ) {tl : ℕ} (Tw : BitString tl) {k : ℕ} (M : BitString k)
    (hcap : 2 * tl + 3 < 2 ^ n) (hdvd : ¬ n ∣ k) :
    Wellformed n ⟨_, (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0⟩ ∧
      getTM n ⟨_, (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0⟩
        = (⟨tl, Tw⟩, ⟨k, M⟩) := by
  obtain ⟨hn2, htlt⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  have hle : tl ≤ padLen n tl := le_padLen hn tl
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (dvd_zero n) hdvd
    · exact h
  have hkp : k < padLen n (k + 1) := lt_of_lt_of_le (Nat.lt_succ_self k) (le_padLen hn (k + 1))
  have hnp : n ≤ padLen n (k + 1) := le_padLen' hn (by omega)
  -- the marker sits strictly below the top block, which is what line 14 asserts
  have hpk : padLen n (k + 1) < k + n := by
    rcases Nat.lt_or_ge (padLen n (k + 1)) (k + n) with h | h
    · exact h
    · refine absurd ?_ hdvd
      have hle' := padLen_le n (k + 1)
      have he : padLen n (k + 1) = n + k := by omega
      exact (Nat.dvd_add_right dvd_rfl).mp (he ▸ dvd_padLen n (k + 1))
  -- the reads, specialised to `v = 2|T| + 3` and payload `pad(M‖1)`
  have e5 : ((bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥
      bin n 0)[1; n - 1]).toNat = tl + 1 := by
    rw [Hash.Facts.shape_len _ _ _ hn, toNat_bin (by omega)]
    omega
  have e9 : (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0)[0; 1] ≠ 0 := by
    rw [Hash.Facts.shape_flag _ _ _ hn, Ne, bin_one_eq_zero_iff]
    omega
  have e19 : (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0)[
      n + padLen n tl; k] = M := by
    rw [Hash.Facts.shape_payload _ _ _ (by omega), sub_pad_of_le _ (by omega),
      sub_cat_lo _ _ (by omega), sub_full]
  -- lines 15–18: the marker is the highest set bit
  have hmark : (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0).getLsbD
      (n + padLen n tl + k) = true := by
    rw [getLsbD_cat, if_pos (by omega), getLsbD_cat, if_neg (by omega),
      show n + padLen n tl + k - (n + padLen n tl) = k by omega]
    exact pad10_marker hn M
  have hhigh : ∀ j, n + padLen n tl + k < j →
      (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0).getLsbD j = false := by
    intro j hj
    rw [getLsbD_cat]
    by_cases hjp : j < n + padLen n tl + padLen n (k + 1)
    · rw [if_pos hjp, getLsbD_cat, if_neg (by omega)]
      exact pad10_high (by omega) M
    · rw [if_neg hjp, bin]
      simp
  have emsb : msbIdx (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0)
      = n + padLen n tl + k := msbIdx_eq _ (by omega) hmark hhigh
  -- line 14: the last block of `pad(M‖1)` is nonzero above its bit 0
  have e14 : (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0)[
      n + padLen n tl + padLen n (k + 1) + n - 2 * n + 1; n - 1] ≠ 0 := by
    intro h
    have hb : ((bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0)[
        n + padLen n tl + padLen n (k + 1) + n - 2 * n + 1; n - 1]).getLsbD
        (n + padLen n tl + k - (n + padLen n tl + padLen n (k + 1) + n - 2 * n + 1)) = true := by
      rw [substring, BitVec.getLsbD_extractLsb',
        show n + padLen n tl + padLen n (k + 1) + n - 2 * n + 1 +
            (n + padLen n tl + k - (n + padLen n tl + padLen n (k + 1) + n - 2 * n + 1))
          = n + padLen n tl + k by omega, hmark]
      simp [show n + padLen n tl + k - (n + padLen n tl + padLen n (k + 1) + n - 2 * n + 1)
        < n - 1 by omega]
    rw [h] at hb
    simp at hb
  -- the three named intermediates
  have htlen : tlen n
      ⟨_, (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0⟩ = tl := by
    show ((bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥
      bin n 0)[1; n - 1]).toNat - 1 = tl
    omega
  have hoff : off n ⟨_, (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0⟩
      = n + padLen n tl := by rw [off, htlen]
  have hmlen : mlen n
      ⟨_, (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1)) ∥ bin n 0⟩ = k := by
    rw [mlen]
    show (if (bin n (2 * tl + 3) ∥ pad n Tw ∥ pad n (M ∥ bin 1 1) ∥ bin n 0)[0; 1] = 0
      then _ else _) = k
    rw [if_neg e9, hoff, emsb]
    omega
  refine ⟨?_, by rw [getTM, htlen, hmlen, hoff, e19, Hash.Facts.shape_tweak _ _ _ hn]⟩
  rw [Wellformed]
  dsimp only
  rw [hoff, if_neg e9]
  refine ⟨dvd_mod_zero (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add dvd_rfl
      (dvd_padLen n tl)) (dvd_padLen n (k + 1))) dvd_rfl), by omega, ?_, by omega,
    ⟨by omega, e14⟩⟩
  rw [show n + padLen n tl + padLen n (k + 1) + n - n
    = n + padLen n tl + padLen n (k + 1) by omega]
  exact Hash.Facts.shape_top _ _ _

/-- **Appendix A, the reads**: `GetTM` recovers `T` and `M` from the string of
coefficients of `H(T, M)`. -/
theorem getTM_polyStr (n : ℕ) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) :
    getTM n (polyStr (n := n) T M) = (⟨T.len, T.2⟩, ⟨k, M⟩) := by
  obtain ⟨i, Tw⟩ := T
  by_cases hdvd : n ∣ k
  · rw [polyStr_aligned _ _ hdvd]
    exact (run_aligned n Tw M hcap hdvd).2
  · rw [polyStr_unaligned _ _ hdvd]
    exact (run_unaligned n Tw M hcap hdvd).2

/-- **Appendix A, the asserts**: `GetTM` accepts the string of coefficients of
`H(T, M)`. -/
theorem wellformed_polyStr (n : ℕ) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (hcap : 2 * T.len + 3 < 2 ^ n) : Wellformed n (polyStr (n := n) T M) := by
  obtain ⟨i, Tw⟩ := T
  by_cases hdvd : n ∣ k
  · rw [polyStr_aligned _ _ hdvd]
    exact (run_aligned n Tw M hcap hdvd).1
  · rw [polyStr_unaligned _ _ hdvd]
    exact (run_unaligned n Tw M hcap hdvd).1

/-- The paper's `cap = 2ⁿ⁻¹ − 2` (§2.1) meets the cap hypothesis, and only just:
`2·cap + 3 = 2ⁿ − 1`.  This is the sense in which the value is "forced by the mode
block `bin(2|T|+3)` having to fit in `n` bits". -/
theorem paper_cap_lt {n : ℕ} (hn : 2 ≤ n) : 2 * (2 ^ (n - 1) - 2) + 3 < 2 ^ n := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    ring
  have h2 : 2 ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_one] at h2
  omega

/-- **Appendix A, the conclusion**: distinct `(T, M)` hash distinct strings. -/
theorem polyStr_injective (n : ℕ) {tcap : ℕ} (hcap : 2 * tcap + 3 < 2 ^ n) :
    Function.Injective
      (fun p : Tweak tcap × (Σ k : ℕ, BitString k) => polyStr (n := n) p.1 p.2.2) := by
  rintro ⟨⟨i₁, Tw₁⟩, k₁, M₁⟩ ⟨⟨i₂, Tw₂⟩, k₂, M₂⟩ h
  have key := congrArg (getTM n) h
  dsimp only at key
  rw [getTM_polyStr n ⟨i₁, Tw₁⟩ M₁ (by have := i₁.isLt; simp only [Tweak.len]; omega),
    getTM_polyStr n ⟨i₂, Tw₂⟩ M₂ (by have := i₂.isLt; simp only [Tweak.len]; omega)] at key
  obtain ⟨hT, hM⟩ := Prod.mk.inj key
  obtain ⟨hi, hTw⟩ := Sigma.mk.inj hT
  obtain rfl : i₁ = i₂ := Fin.ext hi
  obtain rfl := eq_of_heq hTw
  obtain ⟨rfl, hMM⟩ := Sigma.mk.inj hM
  obtain rfl := eq_of_heq hMM
  rfl

/-- **§3.2, property 1** — "the map is injective": `(T, M) ↦ H(T, M)` is injective
onto formal polynomials.  Two steps, as the paper has them: the leading block is
nonzero, so the polynomial determines the coefficient string (`Poly.Facts.poly_inj`
with `Poly.Facts.polyStr_head_ne_zero`), and `GetTM` reads `(T, M)` back off that
string. -/
theorem Hpoly_injective {F : Type} [Field F] {n : ℕ} (bf : Hash.BlockField F n) {tcap : ℕ}
    (hcap : 2 * tcap + 3 < 2 ^ n) :
    Function.Injective (fun p : Tweak tcap × (Σ k : ℕ, BitString k) => Hpoly bf p.1 p.2.2) := by
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  refine fun p q h => polyStr_injective n hcap ?_
  -- the leading coefficient of `H(T,M)` is the mode block, and it is nonzero
  have head : ∀ r : Tweak tcap × (Σ k : ℕ, BitString k),
      ((blocks n (polyStr (n := n) r.1 r.2.2).2).map bf.enc).getD 0 0 ≠ 0 := fun r =>
    Hpoly_blocks_head_ne_zero bf hn r.1 r.2.2
      (by have := r.1.1.isLt; simp only [Tweak.len]; omega)
  have hblocks : blocks n (polyStr (n := n) p.1 p.2.2).2
      = blocks n (polyStr (n := n) q.1 q.2.2).2 :=
    List.map_injective_iff.mpr bf.enc.injective (poly_inj (head p) (head q) h)
  exact blocks_inj hn (dvd_polyStr p.1 p.2.2) (dvd_polyStr q.1 q.2.2) hblocks

end Facts

end AppendixA

/-! ## Paper §3.2, concluded — Properties 1–3 of `H_h̄` (pp. 7–8)

These are the three probability statements later used to bound concrete
collision cells in §3.4.  They do **not** specialize or extend the H-coefficient
theorem of §3.3: H only asks for a good-point likelihood comparison and an ideal
bad-event mass bound, regardless of how an application proves those facts.

They sit after Appendix A rather than with the rest of §3.2 because Property 2's
proof opens "`H` is injective onto polynomials", and that is Appendix A; the paper
states them in place only because it can forward-reference.  Names stay in
`Poly.Facts`, next to the structural properties they use.

All three are the same three steps: read the event as "`h̄` is a root of a
perturbed polynomial", show the perturbation is still nonzero and of bounded
degree, and apply `Poly.Facts.card_keys_root_le`.  What differs is only which
structural property rules the perturbation out. -/

namespace Poly.Facts

open Bits Bits.Facts Hash Polynomial

variable {F : Type} [Field F] {n : ℕ}

/-! ### Property 1 of `H_h̄`

    **Property 1**  For any `T, M` and any `g ∈ {0,1}ⁿ`,
        Pr_{h̄ ←$ {0,1}ⁿ}[H_h̄(T, M) = g] ≤ d(T,M)/2ⁿ
    Proof: since `H(T,M)` is nonzero and has a zero constant term, the polynomial
    `H(T,M) ⊕ g` is nonzero and has the same degree, at most `d(T,M)`.

The paper's proof cites properties 2 and 3; the argument below uses property 4
instead of property 3, because with the degree in hand both claims collapse into
one: `H(T,M)` has degree `d(T,M) ≥ 1`, so it is not a constant, so adding one
cannot make it zero and cannot change its degree.  Property 3 is what makes that
reading legitimate in the first place (`POLYVAL_eq_mul_eval`). -/

theorem one_le_d (n a b : ℕ) : 1 ≤ d n a b := by rw [d]; omega

/-- `Hash.Facts.add_eq_zero_iff` coefficientwise: over a `BlockField`, `⊕` and `=`
are one relation for polynomials too. -/
theorem poly_add_eq_zero_iff (bf : BlockField F n) {p q : Polynomial F} :
    p + q = 0 ↔ p = q := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun r => Polynomial.coeff r i) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero] at hi
    exact (Hash.Facts.add_eq_zero_iff bf).mp hi
  · rintro rfl
    ext i
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero]
    exact Hash.Facts.charTwo bf _

/-- The perturbation `H(T,M) ⊕ g` is still nonzero: `H(T,M)` has degree `≥ 1`, so
it is not the constant `g`. -/
theorem Hpoly_add_C_ne_zero (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (c : F) (hcap : 2 * T.len + 3 < 2 ^ n) : Hpoly bf T M + C c ≠ 0 := by
  intro h
  have hd := Hpoly_natDegree bf T M hcap
  rw [add_eq_zero_iff_eq_neg.mp h, Polynomial.natDegree_neg, Polynomial.natDegree_C] at hd
  have := one_le_d n T.len k
  omega

/-- …and still of degree `d(T,M)`, for the same reason. -/
theorem Hpoly_add_C_natDegree (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (c : F) (hcap : 2 * T.len + 3 < 2 ^ n) :
    (Hpoly bf T M + C c).natDegree = d n T.len k := by
  have hd := Hpoly_natDegree bf T M hcap
  rw [Polynomial.natDegree_add_C, hd]

/-- The event `H_h̄(T,M) = g`, as a root of the perturbed polynomial. -/
theorem hashBits_eq_iff (bf : BlockField F n) (hn : 0 < n) (hbar : BitString n) {tcap k : ℕ}
    (T : Tweak tcap) (M : BitString k) (g : BitString n) :
    hashBits bf hbar T M = g
      ↔ (Hpoly bf T M + C (bf.enc g)).eval (bf.enc hbar * bf.u) = 0 := by
  rw [hashBits_eq bf hn, Equiv.symm_apply_eq, Polynomial.eval_add, Polynomial.eval_C,
    Hash.Facts.add_eq_zero_iff bf]

/-- **§3.2, Property 1 of `H_h̄`** (paper p. 7). -/
theorem prop1 [DecidableEq F] (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (g : BitString n) (hcap : 2 * T.len + 3 < 2 ^ n) :
    (Dist.uniform (BitString n)).mass (fun hbar => hashBits bf hbar T M = g)
      ≤ (d n T.len k : ℝ) / 2 ^ n := by
  -- The mode-block cap implies `n ≥ 2`, hence the substitution multiplier is nonzero.
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  -- First prove the paper's numerator bound: at most `d(T,M)` hash keys are roots.
  have hcard : (Finset.univ.filter fun hbar : BitString n => hashBits bf hbar T M = g).card
      ≤ d n T.len k := by
    -- Rewrite the hash equation as a root of `H(T,M) + g`.
    rw [Finset.filter_congr (fun hbar _ => by rw [hashBits_eq_iff bf hn]),
      ← Hpoly_add_C_natDegree bf T M (bf.enc g) hcap]
    -- A nonzero degree-`d(T,M)` polynomial has at most `d(T,M)` roots.
    exact card_keys_root_le bf (Hpoly_add_C_ne_zero bf T M _ hcap) (Hash.Facts.u_ne_zero bf hn2)
  -- Uniform mass is the root count divided by `|{0,1}ⁿ| = 2ⁿ`.
  rw [Dist.uniform_mass_eq_card_filter, card_Str]
  push_cast
  gcongr



/-! ### Property 2 of `H_h̄`

    **Property 2**  For any `(T₁, M₁) ≠ (T₂, M₂)` and any `g ∈ {0,1}ⁿ`
        Pr_{h̄}[H_h̄(T₁,M₁) ⊕ H_h̄(T₂,M₂) = g] ≤ max(d(T₁,M₁), d(T₂,M₂))/2ⁿ
    Proof: `H` is injective onto polynomials and the constant term is zero,
    therefore `H(T₁,M₁) ⊕ H(T₂,M₂) ⊕ g` is not the zero polynomial and has degree
    at most `max(d(T₁,M₁), d(T₂,M₂))`.  This is the almost-XOR-universal property.

The property that pays for Appendix A: injectivity is what makes the *difference*
of the two polynomials nonzero.  Property 3 (zero constant term) is genuinely
needed here as well, and cannot be replaced by the degree argument that served
Property 1 — the two mode blocks coincide whenever `|T₁| = |T₂|` with the same
alignment, so `H(T₁,M₁) ⊕ H(T₂,M₂)` can have its leading terms cancel and drop to
low degree.  What rules out its being a nonzero *constant* is that both constant
terms are zero. -/

/-- The event `H_h̄(T₁,M₁) ⊕ H_h̄(T₂,M₂) = g`, as a root of the summed polynomial. -/
theorem hashBits_xor_eq_iff (bf : BlockField F n) (hn : 0 < n) (hbar : BitString n)
    {tcap k₁ k₂ : ℕ} (T₁ : Tweak tcap) (M₁ : BitString k₁) (T₂ : Tweak tcap) (M₂ : BitString k₂)
    (g : BitString n) :
    hashBits bf hbar T₁ M₁ ^^^ hashBits bf hbar T₂ M₂ = g
      ↔ (Hpoly bf T₁ M₁ + Hpoly bf T₂ M₂ + C (bf.enc g)).eval (bf.enc hbar * bf.u) = 0 := by
  have e₁ : bf.enc (hashBits bf hbar T₁ M₁) = (Hpoly bf T₁ M₁).eval (bf.enc hbar * bf.u) := by
    rw [hashBits_eq bf hn, Equiv.apply_symm_apply]
  have e₂ : bf.enc (hashBits bf hbar T₂ M₂) = (Hpoly bf T₂ M₂).eval (bf.enc hbar * bf.u) := by
    rw [hashBits_eq bf hn, Equiv.apply_symm_apply]
  rw [← bf.enc.injective.eq_iff, bf.enc_xor, e₁, e₂, Polynomial.eval_add, Polynomial.eval_add,
    Polynomial.eval_C, Hash.Facts.add_eq_zero_iff bf]

/-- **Injectivity, cashed in**: distinct `(T, M)` give a nonzero difference, and the
zero constant terms keep it nonzero after perturbing by `g`. -/
theorem Hpoly_xor_add_C_ne_zero (bf : BlockField F n) {tcap : ℕ}
    (hcap : 2 * tcap + 3 < 2 ^ n) {k₁ k₂ : ℕ} (T₁ : Tweak tcap) (M₁ : BitString k₁)
    (T₂ : Tweak tcap) (M₂ : BitString k₂)
    (hne : ((T₁, ⟨k₁, M₁⟩) : Tweak tcap × Σ k : ℕ, BitString k) ≠ (T₂, ⟨k₂, M₂⟩)) (c : F) :
    Hpoly bf T₁ M₁ + Hpoly bf T₂ M₂ + C c ≠ 0 := by
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  intro h
  refine hne (AppendixA.Facts.Hpoly_injective bf hcap ?_)
  have hsum : Hpoly bf T₁ M₁ + Hpoly bf T₂ M₂ = -C c := add_eq_zero_iff_eq_neg.mp h
  have hc0 : (Hpoly bf T₁ M₁ + Hpoly bf T₂ M₂).coeff 0 = 0 := by
    rw [Polynomial.coeff_add, Hpoly_coeff_zero bf hn T₁ M₁, Hpoly_coeff_zero bf hn T₂ M₂,
      add_zero]
  rw [hsum, Polynomial.coeff_neg, Polynomial.coeff_C_zero] at hc0
  rw [neg_eq_zero.mp hc0, map_zero, neg_zero] at hsum
  exact (poly_add_eq_zero_iff bf).mp hsum

/-- The degree bound: `max` of the two, since a sum can only reach the larger. -/
theorem Hpoly_xor_add_C_natDegree_le (bf : BlockField F n) {tcap : ℕ}
    (hcap : 2 * tcap + 3 < 2 ^ n) {k₁ k₂ : ℕ} (T₁ : Tweak tcap) (M₁ : BitString k₁)
    (T₂ : Tweak tcap) (M₂ : BitString k₂) (c : F) :
    (Hpoly bf T₁ M₁ + Hpoly bf T₂ M₂ + C c).natDegree
      ≤ max (d n T₁.len k₁) (d n T₂.len k₂) := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (by simp))
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [Hpoly_natDegree bf T₁ M₁ (cap_of_tweak T₁ hcap),
    Hpoly_natDegree bf T₂ M₂ (cap_of_tweak T₂ hcap)]

/-- **§3.2, Property 2 of `H_h̄`** (paper p. 7): the almost-XOR-universal property. -/
theorem prop2 [DecidableEq F] (bf : BlockField F n) {tcap : ℕ}
    (hcap : 2 * tcap + 3 < 2 ^ n) {k₁ k₂ : ℕ} (T₁ : Tweak tcap) (M₁ : BitString k₁)
    (T₂ : Tweak tcap) (M₂ : BitString k₂)
    (hne : ((T₁, ⟨k₁, M₁⟩) : Tweak tcap × Σ k : ℕ, BitString k) ≠ (T₂, ⟨k₂, M₂⟩)) (g : BitString n) :
    (Dist.uniform (BitString n)).mass
        (fun hbar => hashBits bf hbar T₁ M₁ ^^^ hashBits bf hbar T₂ M₂ = g)
      ≤ (max (d n T₁.len k₁) (d n T₂.len k₂) : ℝ) / 2 ^ n := by
  -- The common tweak cap again guarantees a nonzero evaluation multiplier.
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  have hn : 0 < n := by omega
  -- Count the keys satisfying the XOR equation before turning the count into probability.
  have hcard : (Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T₁ M₁ ^^^ hashBits bf hbar T₂ M₂ = g).card
      ≤ max (d n T₁.len k₁) (d n T₂.len k₂) := by
    -- The event is exactly a root of `H(T₁,M₁) + H(T₂,M₂) + g`.
    rw [Finset.filter_congr (fun hbar _ => by rw [hashBits_xor_eq_iff bf hn])]
    -- Injectivity makes that polynomial nonzero; its degree is at most the larger `d`.
    exact le_trans
      (card_keys_root_le bf (Hpoly_xor_add_C_ne_zero bf hcap T₁ M₁ T₂ M₂ hne _)
        (Hash.Facts.u_ne_zero bf hn2))
      (Hpoly_xor_add_C_natDegree_le bf hcap T₁ M₁ T₂ M₂ _)
  -- Divide the finite root count by the `2ⁿ` equally likely hash keys.
  rw [Dist.uniform_mass_eq_card_filter, card_Str]
  push_cast
  gcongr
  exact_mod_cast hcard

/-! ### Property 3 of `H_h̄`

    **Property 3**  For any `T, M` and any `g ∈ {0,1}ⁿ`
        Pr_{h̄}[H_h̄(T,M) ⊕ h̄ = g] ≤ d(T,M)/2ⁿ
    Proof: `H(T,M)` has a zero constant term and cannot be equal to the polynomial
    `xⁿh`.  `H(T,M) ⊕ g ⊕ h̄ = H(T,M) ⊕ g ⊕ xⁿh` thus cannot be the zero polynomial
    and has degree at most `d(T,M)`.

This is the property `h̄ ← E_k(bin(0))` forces (§5.2.2: "guarantee `H(T,M) ≠ h̄`,
required because `h̄ ← E_k(bin(0))`"): the key itself appears in the event, so the
perturbation is by the *degree-one* polynomial `xⁿh` rather than by a constant.
That is why the second half of property 2 (`Hpoly_ne_x_pow_mul_X`, and behind it
`x^{n−1} ≠ 1`) had to be proved separately — with `d = 1` the degree argument that
served Property 1 says nothing.

The step `h̄ = xⁿh` is `Hash.Facts.x_pow_mul_u`: the paper's substitution
`h = x⁻ⁿh̄` read backwards, and the only place it is used in earnest. -/

/-- The event `H_h̄(T,M) ⊕ h̄ = g`, as a root of `H(T,M) ⊕ g ⊕ xⁿh`. -/
theorem hashBits_xor_key_eq_iff (bf : BlockField F n) (hn : 2 ≤ n) (hbar : BitString n)
    {tcap k : ℕ} (T : Tweak tcap) (M : BitString k) (g : BitString n) :
    hashBits bf hbar T M ^^^ hbar = g
      ↔ (Hpoly bf T M + C (bf.enc g) + C (bf.x ^ n) * X).eval (bf.enc hbar * bf.u) = 0 := by
  have hkey : bf.x ^ n * (bf.enc hbar * bf.u) = bf.enc hbar := by
    rw [← mul_assoc, mul_comm (bf.x ^ n), mul_assoc, Hash.Facts.x_pow_mul_u bf hn, mul_one]
  have e₁ : bf.enc (hashBits bf hbar T M) = (Hpoly bf T M).eval (bf.enc hbar * bf.u) := by
    rw [hashBits_eq bf (by omega), Equiv.apply_symm_apply]
  rw [← bf.enc.injective.eq_iff, bf.enc_xor, e₁, Polynomial.eval_add, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X, hkey,
    Hash.Facts.add_eq_zero_iff bf]
  exact Hash.Facts.add_eq_iff bf

/-- `H(T,M) ⊕ g ⊕ xⁿh` is nonzero: its constant term forces `g = 0`, and then it
is `H(T,M) ⊕ xⁿh`, which property 2 says is nonzero. -/
theorem Hpoly_add_C_add_key_ne_zero (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap)
    (M : BitString k) (hcap : 2 * T.len + 3 < 2 ^ n) (c : F) :
    Hpoly bf T M + C c + C (bf.x ^ n) * X ≠ 0 := by
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  intro h
  rw [add_assoc] at h
  have hEq : Hpoly bf T M = C c + C (bf.x ^ n) * X := (poly_add_eq_zero_iff bf).mp h
  have hc0 : (Hpoly bf T M).coeff 0 = 0 := Hpoly_coeff_zero bf (by omega) T M
  rw [hEq] at hc0
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_zero, mul_zero, add_zero] at hc0
  rw [hc0, map_zero, zero_add] at hEq
  exact Hpoly_ne_x_pow_mul_X bf T M hcap hEq

/-- …and of degree at most `d(T,M)`, since `xⁿh` contributes only degree `1 ≤ d`. -/
theorem Hpoly_add_C_add_key_natDegree_le (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap)
    (M : BitString k) (hcap : 2 * T.len + 3 < 2 ^ n) (c : F) :
    (Hpoly bf T M + C c + C (bf.x ^ n) * X).natDegree ≤ d n T.len k := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_of_eq (Hpoly_add_C_natDegree bf T M c hcap)
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X]
    exact one_le_d n T.len k

/-- **§3.2, Property 3 of `H_h̄`** (paper p. 8). -/
theorem prop3 [DecidableEq F] (bf : BlockField F n) {tcap k : ℕ} (T : Tweak tcap) (M : BitString k)
    (g : BitString n) (hcap : 2 * T.len + 3 < 2 ^ n) :
    (Dist.uniform (BitString n)).mass (fun hbar => hashBits bf hbar T M ^^^ hbar = g)
      ≤ (d n T.len k : ℝ) / 2 ^ n := by
  -- Here `n ≥ 2` is also needed to rule out the degree-one key polynomial.
  obtain ⟨hn2, -⟩ := cap_bounds hcap
  -- Count roots of the polynomial that contains both the hash value and the key itself.
  have hcard : (Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T M ^^^ hbar = g).card ≤ d n T.len k := by
    -- Substitute `hbar = xⁿ h`, obtaining `H(T,M) + g + xⁿ h`.
    rw [Finset.filter_congr (fun hbar _ => by rw [hashBits_xor_key_eq_iff bf hn2])]
    -- Property 2 keeps the perturbation nonzero; the degree remains at most `d(T,M)`.
    exact le_trans
      (card_keys_root_le bf (Hpoly_add_C_add_key_ne_zero bf T M hcap _)
        (Hash.Facts.u_ne_zero bf hn2))
      (Hpoly_add_C_add_key_natDegree_le bf T M hcap _)
  -- Convert the root count to probability under the uniform `n`-bit key.
  rw [Dist.uniform_mass_eq_card_filter, card_Str]
  push_cast
  gcongr

end Poly.Facts


/-! ## Paper §3.3 — H-coefficient technique (pp. 8–9)

This section is deliberately not implemented as a transcript-specific theorem.
Its mathematical input is just two random variables on one observation carrier:

* `real : Dist A`, the law called world `X` by the paper; and
* `ideal : Dist A`, the law called world `Y` by the paper.

For a fixed deterministic adversary, sampling a deterministic oracle and then
running the interaction is a deterministic map from the world's coins to an
observation.  Hence the transcript law is an ordinary pushforward distribution.
Nothing in H depends on the observation being a transcript: `A` may equally be
a plain transcript, an augmented transcript, or any other random-variable
carrier.

The paper's remaining ingredients translate as follows:

* Its compatible-transcript set is not an extra H parameter.  A fixed
  environment makes syntactically incompatible interactions impossible, and
  the ideal transcript law's `support` records the compatible points that can
  actually occur in that world.  The H sum needs only those points.
* Its optimal acceptance rule, together with the chosen orientation
  `Pr[A(Y)=1] ≥ Pr[A(X)=1]`, is exactly the one-sided distance
  `δ ideal real`: sum the positive excess of ideal mass over real mass.
* A predicate `Bad : A → Prop` determines the whole two-cell partition.  The
  good cell is simply `¬ Bad`, so coverage and disjointness are logical facts,
  not application obligations.
* The paper's first bullet becomes support-local good dominance:
  `ideal a ≤ real a` for every `a ∈ ideal.support` with `¬ Bad a`.
* Its second bullet is `probBad ideal Bad ≤ beta`.

The carrier-independent theorem implementing exactly these two bullets is
`RandomSystems.δ_hTechnique_le_on_good_of_bad_le`.  Besides nonnegativity of the
two laws, applying it exposes only good dominance and the ideal bad-mass bound,
and concludes `δ ideal real ≤ beta`.  Requiring dominance only on
`ideal.support` is slightly cleaner than the paper's statement for every good
compatible transcript: points of zero ideal mass contribute nothing.

At the system level, `RandomSystems.adv_le_of_le_on_good` applies the same result
to every environment and transcript depth before taking the supremum.  An
HCTR2 proof may instead apply the distribution theorem directly to whatever
observation law makes its two obligations easiest.  In particular, no separate
"augmented H-coefficient technique" is required: stripping an augmentation is
ordinary deterministic data processing, a later §3.4 composition step rather
than part of §3.3 itself. -/


/-! ## Paper §3.4 — Main lemma (pp. 9–17): the augmented worlds

    We give the adversary some extra information which is included in the
    transcript.  In world X, this information is:
      * the "leftover block" for each query … `Dˢ = XCTR_π(Sˢ)[|Pˢ| − n; nmˢ − |Pˢ|]`
      * the hash key `h̄`, given after all queries are complete
      * the mask `L`, given after all queries are complete
    In world Y, random output of the expected length is substituted.  Since the
    adversary can always ignore this information, giving it to them cannot make
    their performance worse.

The augmentation is terminal information, not an oracle query.  For each fixed
environment it is a random variable on the same representative coins as the
ordinary transcript (with independent coordinates added to the ideal
representative).  Forgetting the extra coordinates returns the ordinary
transcript exactly, so the comparison with the base experiment is just data
processing at the first projection.

The leftover is a slice of the keystream at the query's own nonce.  Both
directions share one `Sˢ` (Figures 2 and 3 compute the same value), so `Dˢ` is
defined once, off the query's *plaintext*, which for a decryption query is
`decrypt`'s output. -/

namespace MainLemma

open Bits Bits.Facts Hash HCTR2 Sec
open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique (QueryDir)
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.PFunDDS

variable {F : Type} [Field F] {n cap tcap m : ℕ}

/-! ### §3.4's augmented-transcript contract

For a fixed environment and observation depth `m`, the base observation is the
ordinary raw transcript of the commonly resource-filtered system.  Its `none`
entries are shared rejection behavior; the augmentation records one leftover
only for each answered query.  The richer observation is a random variable on
the same representative coins, and first projection recovers the raw
transcript exactly. -/

/-- The answered query/response pairs of a raw partial-resource transcript. -/
abbrev transcriptEntries {X Y : Type}
    (t : List (X × Option Y)) : List (X × Y) :=
  PFunDDS.answeredEntries t

/-- §3.4's augmented observation carrier.  Observation depth belongs to the
random variable producing this value, not to the carrier itself. -/
abbrev AugObs (n cap tcap : ℕ) : Type :=
  List (TQ n cap tcap × Option (TM n cap)) ×
    (BitString n × BitString n) × List (Σ w : ℕ, BitString w)

/-- Width of the leftover revealed for a query with excess-message length `j`. -/
def leftoverWidth (w : TQ n cap tcap) : ℕ :=
  padLen n w.2.2.1.val - w.2.2.1.val

/-- The plaintext of a query, whichever direction it was asked in. -/
def plainOf (bf : Hash.BlockField F n) (π : Perm n) (w : TQ n cap tcap) :
    BitString (n + w.2.2.1.val) :=
  match w.1 with
  | QueryDir.fwd => w.2.2.2
  | QueryDir.inv => (decrypt bf π w.2.1 w.2.2).2

/-- The leftover block of one transcript entry, as an element of `{0,1}*`. -/
def leftoverOf (bf : Hash.BlockField F n) (π : Perm n)
    (w : TQ n cap tcap) : Σ width : ℕ, BitString width :=
  ⟨leftoverWidth w, leftover bf π w.2.1 ⟨w.2.2.1, plainOf bf π w⟩⟩

/-- The deterministic HCTR2 representative after the common resource filter. -/
noncomputable def hctr2DDS (bf : Hash.BlockField F n) (q σ : ℕ) (π : Perm n) :
    PFunDDS.DDS (TQ n cap tcap) (TM n cap) :=
  PFunDDS.filterDom (Budget q σ) (budget_prefixClosed q σ)
    (PFunDDS.functionEvaluator (hctr2Fun bf π))

/-- The deterministic random-function representative after the same filter. -/
noncomputable def rndDDS (n cap tcap q σ : ℕ) (f : RndTable n cap tcap) :
    PFunDDS.DDS (TQ n cap tcap) (TM n cap) :=
  PFunDDS.filterDom (Budget q σ) (budget_prefixClosed q σ)
    (PFunDDS.functionEvaluator (rndFun f))

/-- **World X's augmented observation**, as a function of the permutation
coins.  Rejected attempts remain visible in the first component and contribute
no leftover entry. -/
noncomputable def augPerm (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (π : Perm n) : AugObs n cap tcap :=
  let t := PFunDDS.transcript (hctr2DDS bf q σ π) e m
  (t, (π (bin n 0), π (bin n 1)),
    (transcriptEntries t).map (fun entry => leftoverOf bf π entry.1))

/-- **World Y's augmented observation**, on the enlarged representative coins
`RndKey`.  Only its table coordinate answers queries; the other coordinates are
terminal independent reveals. -/
noncomputable def augRnd (n cap tcap q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (k : RndKey n cap tcap) : AugObs n cap tcap :=
  let t := PFunDDS.transcript (rndDDS n cap tcap q σ k.1) e m
  (t, k.2.1,
    (transcriptEntries t).map
      (fun entry : TQ n cap tcap × TM n cap =>
        ⟨padLen n entry.1.2.2.1.val - entry.1.2.2.1.val, k.2.2 entry.1⟩))

/-- Pointwise stripping contract for the real augmented random variable. -/
@[simp] theorem fst_augPerm (bf : Hash.BlockField F n)
    (q σ : ℕ) (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (π : Perm n) :
    (augPerm bf q σ e m π).1 =
      PFunDDS.transcript (hctr2DDS bf q σ π) e m := by
  simp [augPerm]

/-- Pointwise stripping contract for the ideal augmented random variable. -/
@[simp] theorem fst_augRnd
    (q σ : ℕ) (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (k : RndKey n cap tcap) :
    (augRnd n cap tcap q σ e m k).1 =
      PFunDDS.transcript (rndDDS n cap tcap q σ k.1) e m := by
  simp [augRnd]

/-- The augmented laws, bundled as probability distributions. -/
noncomputable def augLawPerm (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ) :
    Dist.ProbDist (AugObs n cap tcap) :=
  Dist.PMF ⟨Dist.uniform (Perm n), Dist.uniform_isProbDist⟩
    (augPerm bf q σ e m)

noncomputable def augLawRnd (n cap tcap q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ) :
    Dist.ProbDist (AugObs n cap tcap) :=
  Dist.PMF ⟨Dist.uniform (RndKey n cap tcap), Dist.uniform_isProbDist⟩
    (augRnd n cap tcap q σ e m)

/-- The ideal augmented representative projects to the generic `±rnd`
transcript law.  The only extra step is the uniform-product marginal
`RndKey → RndTable`. -/
theorem fst_augLawRnd (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ) :
    Dist.fTransform Prod.fst (augLawRnd n cap tcap q σ e m).val =
      transcriptDist
        (PFunPDS.filterOf (budget q σ) (rnd n cap tcap).val) e m := by
  calc
    Dist.fTransform Prod.fst (augLawRnd n cap tcap q σ e m).val =
        Dist.fTransform
          (fun k : RndKey n cap tcap =>
            PFunDDS.transcript (rndDDS n cap tcap q σ k.1) e m)
          (Dist.uniform (RndKey n cap tcap)) := by
            rw [augLawRnd, Dist.PMF]
            exact Dist.fTransform_comp_eq_of_pointwise _ _ _ _
              (fun k => fst_augRnd q σ e m k)
    _ = Dist.fTransform
          (fun f : RndTable n cap tcap =>
            PFunDDS.transcript (rndDDS n cap tcap q σ f) e m)
          (Dist.fTransform Prod.fst (Dist.uniform (RndKey n cap tcap))) := by
            rw [Dist.fTransform_comp]
            congr 1
    _ = Dist.fTransform
          (fun f : RndTable n cap tcap =>
            PFunDDS.transcript (rndDDS n cap tcap q σ f) e m)
          (Dist.uniform (RndTable n cap tcap)) := by
            rw [Dist.fTransform_fst_uniform]
    _ = transcriptDist
          (PFunPDS.filterOf (budget q σ) (rnd n cap tcap).val) e m := by
            rw [rnd, TweakablePRP.rnd,
              PFunPDS.filterOf_functionEvaluator, transcriptDist_fTransform]
            rfl

/-- The real augmented representative projects to the ordinary
`HCTR2[Perm(n)]` transcript law. -/
theorem fst_augLawPerm (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ) :
    Dist.fTransform Prod.fst (augLawPerm bf q σ e m).val =
      transcriptDist
        (PFunPDS.filterOf (budget q σ)
          (hctr2Perm (cap := cap) (tcap := tcap) bf).val) e m := by
  calc
    Dist.fTransform Prod.fst (augLawPerm bf q σ e m).val =
        Dist.fTransform
          (fun π : Perm n => PFunDDS.transcript (hctr2DDS bf q σ π) e m)
          (Dist.uniform (Perm n)) := by
            rw [augLawPerm, Dist.PMF]
            exact Dist.fTransform_comp_eq_of_pointwise _ _ _ _
              (fun π => fst_augPerm bf q σ e m π)
    _ = transcriptDist
          (PFunPDS.filterOf (budget q σ)
            (hctr2Perm (cap := cap) (tcap := tcap) bf).val) e m := by
            rw [hctr2Perm, PFunPDS.filterOf_functionEvaluator,
              transcriptDist_fTransform]
            rfl

/-- Stripping augmentation is exactly data processing at `Prod.fst`. -/
theorem δ_le_δ_aug (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ) :
    δ (transcriptDist
        (PFunPDS.filterOf (budget q σ) (rnd n cap tcap).val) e m)
      (transcriptDist
        (PFunPDS.filterOf (budget q σ)
          (hctr2Perm (cap := cap) (tcap := tcap) bf).val) e m) ≤
      δ (augLawRnd n cap tcap q σ e m).val
        (augLawPerm bf q σ e m).val := by
  rw [← fst_augLawRnd, ← fst_augLawPerm]
  exact δ_fTransform_le Prod.fst _ (augLawPerm bf q σ e m).2.nonNeg

/-- Support-local structural contract: there is exactly one leftover for each
answered query, in the same order and at the paper-prescribed width. -/
def WellFormedAugObs (o : AugObs n cap tcap) : Prop :=
  o.2.2.map Sigma.fst =
    (transcriptEntries o.1).map (leftoverWidth ∘ Prod.fst)

theorem wellFormed_augRnd (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (k : RndKey n cap tcap) :
    WellFormedAugObs (augRnd n cap tcap q σ e m k) := by
  simp [WellFormedAugObs, augRnd, leftoverWidth, Function.comp_def, List.map_map]

theorem wellFormed_augPerm (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (π : Perm n) : WellFormedAugObs (augPerm bf q σ e m π) := by
  simp [WellFormedAugObs, augPerm, leftoverOf, Function.comp_def, List.map_map]

theorem wellFormed_of_mem_support_rnd (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (o : AugObs n cap tcap)
    (ho : o ∈ (augLawRnd n cap tcap q σ e m).val.support) :
    WellFormedAugObs o := by
  change o ∈ (Dist.fTransform (augRnd n cap tcap q σ e m)
    (Dist.uniform (RndKey n cap tcap))).support at ho
  obtain ⟨k, _, hk⟩ := Dist.mem_support_fTransform _ _ ho
  rw [← hk]
  exact wellFormed_augRnd q σ e m k

theorem wellFormed_of_mem_support_perm (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (o : AugObs n cap tcap)
    (ho : o ∈ (augLawPerm bf q σ e m).val.support) :
    WellFormedAugObs o := by
  change o ∈ (Dist.fTransform (augPerm bf q σ e m)
    (Dist.uniform (Perm n))).support at ho
  obtain ⟨π, _, hπ⟩ := Dist.mem_support_fTransform _ _ ho
  rw [← hπ]
  exact wellFormed_augPerm bf q σ e m π

/-- The answered query history carried by an augmented raw transcript. -/
def answered (o : AugObs n cap tcap) : List (TQ n cap tcap) :=
  PFunDDS.answeredQueries o.1

/-- Every ideal observation inherits the query-count and block-cost receipt
from the system's domain filter.  No environment budget premise is involved. -/
theorem budget_of_mem_support (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (o : AugObs n cap tcap)
    (ho : o ∈ (augLawRnd n cap tcap q σ e m).val.support) :
    Budget q σ (answered o) := by
  change o ∈ (Dist.fTransform (augRnd n cap tcap q σ e m)
    (Dist.uniform (RndKey n cap tcap))).support at ho
  obtain ⟨k, _, hk⟩ := Dist.mem_support_fTransform _ _ ho
  rw [← hk]
  exact PFunDDS.filterDom_answeredQueries (Budget q σ)
    (budget_prefixClosed q σ) ⟨Nat.zero_le q, Nat.zero_le σ⟩
    (PFunDDS.functionEvaluator (rndFun k.1)) e m

/-- A respecting environment supplies the separate no-pointless receipt on
the answered pair list. -/
theorem nonPointless_of_mem_support (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (o : AugObs n cap tcap)
    (ho : o ∈ (augLawRnd n cap tcap q σ e m).val.support) :
    TweakablePRP.NPList (transcriptEntries o.1) := by
  change o ∈ (Dist.fTransform (augRnd n cap tcap q σ e m)
    (Dist.uniform (RndKey n cap tcap))).support at ho
  obtain ⟨k, _, hk⟩ := Dist.mem_support_fTransform _ _ ho
  rw [← hk]
  exact hE _ (transcript_consistent (rndDDS n cap tcap q σ k.1) e m).1.1

/-! ### §3.4.1 — the inference, and `𝒯_bad`

    M‖N = P,  U‖V = C,  MM = M ⊕ H_h̄(T,N),  UU = U ⊕ H_h̄(T,V),
    S = MM ⊕ UU ⊕ L,   Sⱼ = S ⊕ bin(j),   Y₁‖⋯‖Y_{m−1} = (N ⊕ V)‖D

`Bad` is a predicate on the **augmented observation**, which is where `h̄`, `L` and
the `Dˢ` live.  No casts appear: `Bits.sub` is total and `Bits.blocks` accepts any
width, so a malformed observation infers garbage rather than failing to
typecheck — and totality is what the H endpoint needs. -/

/-- Where an inferred block came from.  §3.4.2's four corrections are conditions on
a *pair* of origins — "both seeds", "seed against query", "within one query",
"across two queries" — so the inference must be **labelled**.  A flat list would
make the group of a pair depend on the per-query block counts, and the four groups
would not partition any fixed index set. -/
inductive Origin
  /-- `bin(0)`, `bin(1)` on the `𝒟` side; `h̄`, `L` on the `ℛ` side. -/
  | seed (k : ℕ)
  /-- Block `k` of query `s`. -/
  | block (s k : ℕ)
  deriving DecidableEq

namespace Origin

/-- An origin shape that can occur in an inferred list.  Blocks carry their
query and block indices directly; the only nontrivial condition is that the
two seed positions are exactly `seed 0` and `seed 1`.

This predicate is intentionally proved from `labelsOf_eq` below.  It prevents
the collision table from silently acquiring cases for labels that the
reconstruction never emits. -/
def Valid : Origin → Prop
  | seed k => k < 2
  | block _ _ => True

/-- `c_b` — both from the seeds. -/
def bothSeed : Origin → Origin → Prop
  | seed _, seed _ => True
  | _, _ => False

/-- `c_f` — one seed, one query block. -/
def seedQuery : Origin → Origin → Prop
  | seed _, block _ _ => True
  | block _ _, seed _ => True
  | _, _ => False

/-- `c_w` — both from the same query. -/
def sameQuery : Origin → Origin → Prop
  | block s _, block s' _ => s = s'
  | _, _ => False

/-- `c_a` — from two different queries. -/
def crossQuery : Origin → Origin → Prop
  | block s _, block s' _ => s ≠ s'
  | _, _ => False

/-- The four groups are **exhaustive**: every pair of origins falls in exactly one.
This is what lets §3.4.2's sum split into four, and hence what lets Lean expose the
four corrections as obligations. -/
theorem four_groups (a b : Origin) :
    bothSeed a b ∨ seedQuery a b ∨ sameQuery a b ∨ crossQuery a b := by
  rcases a with k | ⟨s, k⟩ <;> rcases b with k' | ⟨s', k'⟩
  · exact Or.inl trivial
  · exact Or.inr (Or.inl trivial)
  · exact Or.inr (Or.inl trivial)
  · by_cases h : s = s'
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- …and mutually exclusive. -/
theorem four_groups_disjoint (a b : Origin) :
    (bothSeed a b → ¬ seedQuery a b ∧ ¬ sameQuery a b ∧ ¬ crossQuery a b) ∧
      (seedQuery a b → ¬ sameQuery a b ∧ ¬ crossQuery a b) ∧
      (sameQuery a b → ¬ crossQuery a b) := by
  cases a <;> cases b <;> simp [bothSeed, seedQuery, sameQuery, crossQuery]

end Origin

/-- One entry's labelled contribution to `(𝒟, ℛ)`, given `(h̄, L)`, the query index
`s`, and that entry's leftover. -/
def inferEntry (bf : Hash.BlockField F n) (hbar L : BitString n) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w) :
    List (Origin × BitString n) × List (Origin × BitString n) :=
  let w := entry.1
  let r := entry.2
  -- `j` is read off the **query**, never the response.  The paper's `mˢ` counts the
  -- blocks of `Pˢ`, whose length is the query's length class.  `Bits.sub` keeps this
  -- definition total even on a malformed, length-mismatched observation.
  let j : ℕ := w.2.2.1.val
  let q := w.2.2.2
  let a := r.2
  let T := w.2.1
  let MN : BitString n × BitString j :=
    match w.1 with
    | QueryDir.fwd => (q[0; n], q[n; j])
    | QueryDir.inv => (a[0; n], a[n; j])
  let UV : BitString n × BitString j :=
    match w.1 with
    | QueryDir.fwd => (a[0; n], a[n; j])
    | QueryDir.inv => (q[0; n], q[n; j])
  let MM := MN.1 ^^^ hashBits bf hbar T MN.2
  let UU := UV.1 ^^^ hashBits bf hbar T UV.2
  let S := MM ^^^ UU ^^^ L
  ((Origin.block s 0, MM) ::
      (List.range (numBlocks n j)).map
        (fun i => (Origin.block s (i + 1), S ^^^ bin n (i + 1))),
    (Origin.block s 0, UU) ::
      (blocksTake n (numBlocks n j) ((MN.2 ^^^ UV.2) ∥ D.2)).zipIdx.map
        (fun p => (Origin.block s (p.2 + 1), p.1)))

/-- `𝒟` and `ℛ`, labelled: the two seeds, then every query's blocks. -/
def inferred (bf : Hash.BlockField F n) (o : AugObs n cap tcap) :
    List (Origin × BitString n) × List (Origin × BitString n) :=
  let per := ((transcriptEntries o.1).zip o.2.2).zipIdx.map
    (fun p => inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2)
  ((Origin.seed 0, bin n 0) :: (Origin.seed 1, bin n 1) :: (per.map Prod.fst).flatten,
    (Origin.seed 0, o.2.1.1) :: (Origin.seed 1, o.2.1.2) :: (per.map Prod.snd).flatten)

/-- **`𝒯_bad`** (paper §3.4.1): a repeat among the inferred block-cipher plaintexts
or among the inferred ciphertexts.  The labels are bookkeeping — the repeat is
among the *values*. -/
def Bad (bf : Hash.BlockField F n) (o : AugObs n cap tcap) : Prop :=
  ¬ ((inferred bf o).1.map Prod.snd).Nodup ∨ ¬ ((inferred bf o).2.map Prod.snd).Nodup

/-- `σₘ = |𝒟| = |ℛ|`, the block-cipher calls charged. -/
def sigmaM (bf : Hash.BlockField F n) (o : AugObs n cap tcap) : ℕ :=
  (inferred bf o).1.length

/-- One side of the inference: `𝒟` when `d`, `ℛ` otherwise.  Both sides are analysed
by the same four cases, so every statement below is uniform in `d`. -/
def sideOf (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool) :
    List (Origin × BitString n) :=
  if d then (inferred bf o).1 else (inferred bf o).2

/-! #### `σₘ ≤ σ + 2`, derived

Paper p. 17 uses `σ + 2` twice — once to bound `2·C(σₘ,2)` and once as the simulator's
call count in §3.5's substitution — and both times it is a *consequence* of the
adversary class `𝒜(q,σ)`, not an assumption.  So is it here: the inference charges one
call per hash block and one per keystream block, which is exactly `mˢ = numBlocks n |Pˢ|`
per answered query, and `𝒜(q,σ)`'s second conjunct caps `Σ_s qBlocks ≥ Σ_s mˢ`. -/

/-- The calls the inference charges to one transcript entry: exactly `mˢ`. -/
def entryCharge (entry : TQ n cap tcap × TM n cap) : ℕ :=
  numBlocks n entry.1.2.2.len

/-- `mˢ ≤ ⌈|Tˢ|/n⌉ + ⌈|Pˢ|/n⌉` — the charge never exceeds what `𝒜(q,σ)` counts.  In
fact `mˢ = ⌈|Pˢ|/n⌉` exactly; the slack is the tweak's blocks, which `qBlocks` counts
and the block cipher is not called on. -/
theorem entryCharge_le_qBlocks (entry : TQ n cap tcap × TM n cap) :
    entryCharge entry ≤ qBlocks entry.1 := by
  exact Nat.le_add_left _ _

/-- `mˢ = ⌈(n+j)/n⌉ = 1 + ⌈j/n⌉`. -/
theorem numBlocks_Msg_len (w : Msg n cap) (hn : 0 < n) :
    numBlocks n w.len = 1 + numBlocks n w.1.val := by
  rw [Msg.len, numBlocks, numBlocks,
    show n + w.1.val + n - 1 = n + (w.1.val + n - 1) by omega, Nat.add_div_left _ hn]
  omega

/-- Both inferred sides have `mˢ = 1 + numBlocks n j` entries per query. -/
theorem length_inferEntry_fst (bf : Hash.BlockField F n) (hbar L : BitString n) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w) (hn : 0 < n) :
    (inferEntry bf hbar L s entry D).1.length = entryCharge entry := by
  rcases entry with ⟨w, r⟩
  simp [inferEntry, entryCharge, numBlocks_Msg_len w.2.2 hn]
  omega

theorem length_inferEntry_snd (bf : Hash.BlockField F n) (hbar L : BitString n) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w) (hn : 0 < n) :
    (inferEntry bf hbar L s entry D).2.length = entryCharge entry := by
  rcases entry with ⟨w, r⟩
  simp [inferEntry, entryCharge, numBlocks_Msg_len w.2.2 hn]
  omega

/-- **UPSTREAM-CANDIDATE.**  Zipping can only drop entries, so it can only lower a sum. -/
theorem sum_map_zip_le {α β : Type*} (f : α → ℕ) :
    ∀ (l₁ : List α) (l₂ : List β), ((l₁.zip l₂).map (fun p => f p.1)).sum ≤ (l₁.map f).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: t₁, _ :: t₂ => by
      simpa [List.zip_cons_cons] using Nat.add_le_add_left (sum_map_zip_le f t₁ t₂) (f a)

/-- The flattened per-query contribution of one side, as a charge sum.  The index the
labels carry does not affect any length, which is why `List.zipIdx_map_fst` closes it
with no induction. -/
private theorem length_flatten_inferEntry (bf : Hash.BlockField F n) (hbar L : BitString n)
    (g : List (Origin × BitString n) × List (Origin × BitString n) → List (Origin × BitString n))
    (hg : ∀ (s : ℕ) (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w),
      (g (inferEntry bf hbar L s entry D)).length = entryCharge entry)
    (l : List ((TQ n cap tcap × TM n cap) × (Σ w : ℕ, BitString w))) :
    ((l.zipIdx.map (fun p => g (inferEntry bf hbar L p.2 p.1.1 p.1.2))).flatten).length
      = (l.map (fun p => entryCharge p.1)).sum := by
  rw [List.length_flatten, List.map_map,
    show (List.length ∘ fun p : ((TQ n cap tcap × TM n cap) × (Σ w : ℕ, BitString w)) × ℕ =>
        g (inferEntry bf hbar L p.2 p.1.1 p.1.2))
      = (fun x => entryCharge x.1) ∘ Prod.fst from funext fun p => hg p.2 p.1.1 p.1.2,
    ← List.map_map, List.zipIdx_map_fst]

/-- `σₘ = 2 + Σ_s mˢ`, both sides. -/
theorem sigmaM_eq_charge (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (hn : 0 < n) :
    sigmaM bf o = (((transcriptEntries o.1).zip o.2.2).map
      (fun p => entryCharge p.1)).sum + 2 := by
  show (_ :: _ :: _).length = _
  rw [List.length_cons, List.length_cons, List.map_map, Function.comp_def,
    length_flatten_inferEntry bf o.2.1.1 o.2.1.2 Prod.fst
      (fun s entry D => length_inferEntry_fst bf o.2.1.1 o.2.1.2 s entry D hn)]

/-- The two sides have equal length, as the paper's `σₘ = |𝒟| = |ℛ|` says. -/
theorem length_inferred_snd (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (hn : 0 < n) :
    (inferred bf o).2.length = sigmaM bf o := by
  rw [sigmaM_eq_charge bf o hn]
  show (_ :: _ :: _).length = _
  rw [List.length_cons, List.length_cons, List.map_map, Function.comp_def,
    length_flatten_inferEntry bf o.2.1.1 o.2.1.2 Prod.snd
      (fun s entry D => length_inferEntry_snd bf o.2.1.1 o.2.1.2 s entry D hn)]

theorem length_sideOf_le (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool)
    (hn : 0 < n) : (sideOf bf o d).length ≤ sigmaM bf o := by
  cases d
  · exact le_of_eq (length_inferred_snd bf o hn)
  · exact le_of_eq rfl

/-- The charge is bounded by what `𝒜(q,σ)` counts, entry by entry. -/
theorem sum_entryCharge_le (l : List (TQ n cap tcap × TM n cap)) :
    (l.map entryCharge).sum ≤ (l.map (qBlocks ∘ Prod.fst)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      exact Nat.add_le_add (entryCharge_le_qBlocks a) ih

/-- **`σₘ ≤ σ + 2`, derived from `𝒜(q,σ)`** — paper p. 17, no longer a hypothesis. -/
theorem sigmaM_le_of_budget (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (q σ : ℕ)
    (hn : 0 < n) (h : Budget q σ (answered o)) : sigmaM bf o ≤ σ + 2 := by
  have h1 := sum_entryCharge_le (n := n) (cap := cap) (tcap := tcap)
    (transcriptEntries o.1)
  have h2 := sum_map_zip_le (entryCharge (n := n) (cap := cap) (tcap := tcap))
    (transcriptEntries o.1) o.2.2
  have h3 := sigmaM_eq_charge bf o hn
  have h4 := h.2
  have hqueries : (transcriptEntries o.1).map (qBlocks ∘ Prod.fst) =
      (answered o).map qBlocks := by
    rw [answered, ← List.map_map, PFunDDS.answeredEntries_map_fst]
  rw [hqueries] at h1
  omega

/-! ### §3.4.2 — the bad mass, and the paper's bound

    Pr[Y ∈ 𝒯_bad] ≤ (Σ_{[a,b]⊆𝒟} Pr[a=b]) + (Σ_{[a,b]⊆ℛ} Pr[a=b]) = (2·C(σₘ,2)+c)/2ⁿ

`c = c_b + c_f + c_w + c_a` with `c_b = −1`, `c_f ≤ 2σ`, `c_w ≤ 0`,
`c_a ≤ (q−1)σ + C(σ,2)` (pp. 15–16); fourteen of the twenty-two cases sit at
exactly `1/2ⁿ` and contribute nothing.  Each open leaf consumes §3.2: `prop1`,
`prop2` (the AXU step Appendix A pays for), `prop3`. -/

/-- §3.4.2's bad-mass bound at `σₘ ≤ σ + 2` and the four corrections. -/
noncomputable def badBound (n q σ : ℕ) : ℝ :=
  ((σ + 2) * (σ + 1) - 1 + 2 * σ + (q - 1) * σ + σ * (σ - 1) / 2) / 2 ^ n

/-- **§3.4.2's closing arithmetic** (p. 17) — an *equality*, so the paper's `≤`
chain is tight at this step. -/
theorem badBound_eq_mainBound (n q σ : ℕ) : badBound n q σ = mainBound n q σ := by
  rw [badBound, mainBound, pow_succ]
  ring

/-! #### §3.4.1's ratio

For a good observation the two point masses are

    world Y :  2^{−n σₘ}                    world X :  ∏_{i<σₘ} 1/(2ⁿ − i)

The exponent on the left is `n σₘ` and not something else: world Y draws `h̄`, `L`
(`2n` bits) and, per query, a response and a leftover (`n + jˢ` and `padLen n jˢ − jˢ`
bits), so the total is `2n + Σ_s n·mˢ = n·σₘ` — the same `σₘ` the inference counts.  On
the right, `¬ Bad` says the σₘ inferred plaintexts are distinct and so are the
ciphertexts, so `π` is constrained on σₘ distinct points.

The proof below establishes these facts support-locally.  Its real-side bound
uses the reusable `uniform_perm_consistent_mass_ge`, which packages the exact
permutation-fiber count together with the same without-replacement arithmetic;
`pow_inv_le_prod_inv_sub` records the paper's factor-by-factor form explicitly. -/

/-- §3.4.1's `σₘ ≤ 2ⁿ` is **not** a side condition — the paper is right not to state
it.  `¬ Bad` says the inferred plaintexts are pairwise distinct, and a `Nodup` list of
`Str n` has at most `Fintype.card (Str n) = 2ⁿ` entries, so it cannot fail on a good
observation. -/
theorem sigmaM_le_card_of_good (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (hgood : ¬ Bad bf o) : sigmaM bf o ≤ 2 ^ n := by
  rw [Bad, not_or, not_not, not_not] at hgood
  calc sigmaM bf o = ((inferred bf o).1.map Prod.snd).length := by
        rw [List.length_map]; rfl
    _ ≤ Fintype.card (BitString n) := hgood.1.length_le_card
    _ = 2 ^ n := Bits.Facts.card_Str n

/-- **§3.4.1's arithmetic**, the reason the ratio holds at `ε = 0`: sampling without
replacement is *tighter* than uniform coins, factor by factor.  No hypothesis beyond
`k ≤ N`, which `sigmaM_le_card_of_good` supplies. -/
theorem pow_inv_le_prod_inv_sub (N k : ℕ) (hk : k ≤ N) :
    ((1 : ℝ) / N) ^ k ≤ ∏ i ∈ Finset.range k, (1 : ℝ) / ((N : ℝ) - i) := by
  calc ((1 : ℝ) / N) ^ k = ∏ _i ∈ Finset.range k, (1 : ℝ) / N := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (1 : ℝ) / ((N : ℝ) - i) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => ?_)
        have hiN : (i : ℝ) < (N : ℝ) :=
          Nat.cast_lt.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
        exact one_div_le_one_div_of_le (by linarith)
          (by linarith [Nat.cast_nonneg (α := ℝ) i])

/-! The good-transcript proof is split at its actual abstraction boundary.
The lemmas up to `inferEntry_reconstruct` are deterministic: inferred
block-cipher pins reconstruct one HCTR2 answer and its terminal leftover.  The
subsequent two lemmas lift that fact first to the complete adaptive observation
and then to its probability mass. -/

private theorem mem_raw_of_mem_answered {X Y : Type}
    {t : List (X × Option Y)} {x : X} {y : Y}
    (h : (x, y) ∈ PFunDDS.answeredEntries t) : (x, some y) ∈ t := by
  simp only [PFunDDS.answeredEntries, List.mem_filterMap] at h
  obtain ⟨⟨a, oy⟩, hm, heq⟩ := h
  cases oy with
  | none => simp at heq
  | some b =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact hm

private theorem answered_functionEvaluator
    {X Y : Type} (P : List X → Prop) (hP : PrefixClosed P)
    (f : X → Y) (e : PFunDDS.DDE X Y) (m : ℕ) :
    ∀ entry ∈ PFunDDS.answeredEntries
        (PFunDDS.transcript
          (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m),
      f entry.1 = entry.2 := by
  intro entry hentry
  rcases entry with ⟨x, y⟩
  change f x = y
  let S := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)
  let t := PFunDDS.transcript S e m
  have hraw : (x, some y) ∈ t :=
    mem_raw_of_mem_answered (t := t) hentry
  obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp hraw
  have hs := (transcript_consistent S e m).2 i hi
  rw [hit] at hs
  rw [take_succ_get' t i hi, transcriptInputs_append,
    List.get_eq_getElem, hit] at hs
  have hout : PFunDDS.output (PFunDDS.fullyDefined S)
      (((t.take i)↓ₓ ++ [x])) (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) = some y := by
    apply Part.get_eq_of_mem
    rw [hs]
    exact Part.mem_some _
  rw [PFunDDS.output_fullyDefined] at hout
  simp only [List.dropLast_append, List.dropLast_singleton, List.append_nil,
    List.getLast_append, List.getLast_singleton] at hout
  split at hout
  · rename_i hnext
    exact Option.some.inj (by simpa [S, PFunDDS.output_filterDom,
      PFunDDS.functionEvaluator_output] using hout)
  · simp at hout

private theorem mem_answered_of_mem_raw {X Y : Type}
    {t : List (X × Option Y)} {x : X} {y : Y}
    (h : (x, some y) ∈ t) : (x, y) ∈ PFunDDS.answeredEntries t := by
  simp only [PFunDDS.answeredEntries, List.mem_filterMap]
  exact ⟨(x, some y), h, rfl⟩

private theorem transcript_filter_functionEvaluator_eq
    {X Y : Type} (P : List X → Prop) (hP : PrefixClosed P)
    (f g : X → Y) (e : PFunDDS.DDE X Y) (m : ℕ)
    (hagree : ∀ entry ∈ PFunDDS.answeredEntries
        (PFunDDS.transcript
          (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m),
      g entry.1 = entry.2) :
    PFunDDS.transcript
        (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator g)) e m =
      PFunDDS.transcript
        (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m := by
  let Sf := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)
  let Sg := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator g)
  let t := PFunDDS.transcript Sf e m
  have hc := transcript_consistent Sf e m
  apply (transcript_eq_iff_of_consistent hc.1.1 hc.1.2 Sg).2
  intro i hi
  have hs := hc.2 i hi
  rw [take_succ_get' t i hi, transcriptInputs_append]
  rw [take_succ_get' t i hi, transcriptInputs_append] at hs
  let x := t[i].1
  let prev := (t.take i)↓ₓ
  change (PFunDDS.fullyDefined Sg).1 (prev ++ [x]) = Part.some t[i].2
  change (PFunDDS.fullyDefined Sf).1 (prev ++ [x]) = Part.some t[i].2 at hs
  have hdom : prev ++ [x] ∈ PFunDDS.dom (PFunDDS.fullyDefined Sg) := by
    rw [PFunDDS.dom_fullyDefined]
    simp
  rw [Part.eq_some_iff]
  refine ⟨hdom, ?_⟩
  change PFunDDS.output (PFunDDS.fullyDefined Sg) (prev ++ [x]) hdom = t[i].2
  have hdomF : prev ++ [x] ∈ PFunDDS.dom (PFunDDS.fullyDefined Sf) := by
    rw [PFunDDS.dom_fullyDefined]
    simp
  have houtF : PFunDDS.output (PFunDDS.fullyDefined Sf) (prev ++ [x])
      hdomF = t[i].2 := by
    apply Part.get_eq_of_mem
    rw [hs]
    exact Part.mem_some _
  rw [PFunDDS.output_fullyDefined] at houtF ⊢
  have hdrop : (prev ++ [x]).dropLast = prev := by simp
  have hlastG : (prev ++ [x]).getLast (by exact hdom) = x := by simp
  have hlastF : (prev ++ [x]).getLast (by exact hdomF) = x := by simp
  rw [hdrop, hlastG]
  rw [hdrop, hlastF] at houtF
  have hkeep : PFunDDS.keptPrefix Sf prev = PFunDDS.keptPrefix Sg prev := by
    rfl
  rw [← hkeep]
  dsimp only at houtF ⊢
  split
  · rename_i hcandG
    have hcandF : PFunDDS.keptPrefix Sf prev ++ [x] ∈ PFunDDS.dom Sf := by
      exact hcandG
    rw [dif_pos hcandF] at houtF
    rw [PFunDDS.output_filterDom, PFunDDS.functionEvaluator_output]
    rcases hy : t[i].2 with _ | y
    · simp [hy] at houtF
    · have hmemraw : (x, some y) ∈ t := by
        have hm := List.get_mem t ⟨i, hi⟩
        have hv : t.get ⟨i, hi⟩ = (x, some y) := by
          rw [List.get_eq_getElem]
          exact Prod.ext rfl hy
        rwa [hv] at hm
      have hgy := hagree (x, y) (mem_answered_of_mem_raw hmemraw)
      simpa [hy, x] using hgy
  · rename_i hcandG
    have hcandF : PFunDDS.keptPrefix Sf prev ++ [x] ∉ PFunDDS.dom Sf := by
      exact hcandG
    rw [dif_neg hcandF] at houtF
    exact houtF

private theorem forall₂_flatten_map_of_mem {A B C : Type}
    (R : B → C → Prop) (f : A → List B) (g : A → List C)
    (l : List A) (hlen : ∀ a ∈ l, (f a).length = (g a).length)
    (hrel : List.Forall₂ R (l.map f).flatten (l.map g).flatten) :
    ∀ a ∈ l, List.Forall₂ R (f a) (g a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have haLen := hlen a (by simp)
      have ha := List.forall₂_take (f a).length hrel
      have ha' : List.Forall₂ R (f a) (g a) := by
        simpa [haLen] using ha
      have ht := List.forall₂_drop (f a).length hrel
      have ht' : List.Forall₂ R (l.map f).flatten (l.map g).flatten := by
        simpa [haLen] using ht
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha'
      · exact ih (fun c hc => hlen c (by simp [hc])) ht' b hb

private theorem xctr_eq_of_blocks (hn : 0 < n) (E : BitString n → BitString n)
    (S : BitString n) (j : ℕ) (Y : BitString (padLen n j))
    (h : ∀ i (hi : i < numBlocks n j),
      E (S ^^^ bin n (i + 1)) =
        (blocksTake n (numBlocks n j) Y).get ⟨i, by simpa using hi⟩) :
    XCTR.xctr E S (padLen n j) = Y := by
  refine BitVec.eq_of_getLsbD_eq (fun p hp => ?_)
  have hi : p / n < numBlocks n j := by
    rw [padLen_eq_mul] at hp
    exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hp)
  rw [XCTR.Facts.getLsbD_xctr E S hp, XCTR.block, h (p / n) hi]
  simp only [blocksTake, List.get_ofFn, substring, BitVec.getLsbD_extractLsb']
  have hidx : n * (p / n) + p % n = p := by
    simpa [Nat.add_comm] using (Nat.mod_add_div p n)
  simpa [Nat.mod_lt p hn, hp, hidx]

private theorem encrypt_reconstruct (bf : Hash.BlockField F n) (hn : 0 < n)
    (E : Perm n) (T : Tweak tcap) (j : Fin (cap + 1))
    (M U : BitString n) (N V : BitString j.val)
    (D : BitString (padLen n j.val - j.val)) (hbar L : BitString n)
    (hhbar : E (bin n 0) = hbar) (hL : E (bin n 1) = L)
    (hMM : E (M ^^^ hashBits bf hbar T N) = U ^^^ hashBits bf hbar T V)
    (hblocks : ∀ i (hi : i < numBlocks n j.val),
      E ((M ^^^ hashBits bf hbar T N) ^^^
          (U ^^^ hashBits bf hbar T V) ^^^ L ^^^ bin n (i + 1)) =
        (blocksTake n (numBlocks n j.val) ((N ^^^ V) ∥ D)).get
          ⟨i, by simpa using hi⟩) :
    encrypt bf E T ⟨j, M ∥ N⟩ = ⟨j, U ∥ V⟩ ∧
      leftover bf E T ⟨j, M ∥ N⟩ = D := by
  have hj : j.val ≤ padLen n j.val := le_padLen hn _
  have hwidth : j.val + (padLen n j.val - j.val) = padLen n j.val :=
    Nat.add_sub_of_le hj
  let S := (M ^^^ hashBits bf hbar T N) ^^^
    (U ^^^ hashBits bf hbar T V) ^^^ L
  let Y : BitString (padLen n j.val) :=
    BitVec.cast hwidth ((N ^^^ V) ∥ D)
  have hblocks' : ∀ i (hi : i < numBlocks n j.val),
      E (S ^^^ bin n (i + 1)) =
        (blocksTake n (numBlocks n j.val) Y).get ⟨i, by simpa using hi⟩ := by
    intro i hi
    rw [hblocks i hi]
    apply BitVec.eq_of_getLsbD_eq
    intro p hp
    simp [Y, blocksTake, substring, BitVec.getLsbD_cast]
  have hY : XCTR.xctr E S (padLen n j.val) = Y :=
    xctr_eq_of_blocks hn E S j.val Y hblocks'
  have hks : XCTR.xctr E S j.val = N ^^^ V := by
    refine BitVec.eq_of_getLsbD_eq (fun p hp => ?_)
    have hp' : p < padLen n j.val := lt_of_lt_of_le hp hj
    have hbit := congrArg (fun z => z.getLsbD p) hY
    change (XCTR.xctr E S (padLen n j.val)).getLsbD p = Y.getLsbD p at hbit
    rw [XCTR.Facts.getLsbD_xctr E S hp'] at hbit
    rw [XCTR.Facts.getLsbD_xctr E S hp]
    simpa [Y, Bits.Facts.getLsbD_cat, hp, BitVec.getLsbD_cast] using hbit
  constructor
  · simp only [encrypt, sub_cat_left, sub_cat_right]
    rw [hhbar, hMM, hL]
    show (⟨j, ((U ^^^ hashBits bf hbar T V) ^^^ hashBits bf hbar T
      (N ^^^ XCTR.xctr E S j.val)) ∥ (N ^^^ XCTR.xctr E S j.val)⟩ : Msg n cap) =
        ⟨j, U ∥ V⟩
    have hNV : N ^^^ (N ^^^ V) = V := by
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [hks, hNV, xor_cancel]
  · simp only [leftover, HCTR2.nonce, sub_cat_left, sub_cat_right]
    rw [hhbar, hMM, hL]
    change (XCTR.xctr E S (padLen n j.val))[j.val; padLen n j.val - j.val] = D
    rw [hY]
    refine BitVec.eq_of_getLsbD_eq (fun p hp => ?_)
    simp only [Y, substring, BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb']
    rw [Bits.Facts.getLsbD_cat]
    simp [show ¬ j.val + p < j.val by omega, show j.val + p - j.val = p by omega, hp]

private theorem inferLists_reconstruct (bf : Hash.BlockField F n) (hn : 0 < n)
    (E : Perm n) (hbar L : BitString n) (s : ℕ) (T : Tweak tcap)
    (j : Fin (cap + 1)) (M U : BitString n) (N V : BitString j.val)
    (D : BitString (padLen n j.val - j.val))
    (hhbar : E (bin n 0) = hbar) (hL : E (bin n 1) = L)
    (hrel : List.Forall₂ (fun d r : Origin × BitString n => E d.2 = r.2)
      ((Origin.block s 0, M ^^^ hashBits bf hbar T N) ::
        (List.range (numBlocks n j.val)).map (fun i =>
          (Origin.block s (i + 1),
            (M ^^^ hashBits bf hbar T N) ^^^
              (U ^^^ hashBits bf hbar T V) ^^^ L ^^^ bin n (i + 1))))
      ((Origin.block s 0, U ^^^ hashBits bf hbar T V) ::
        (blocksTake n (numBlocks n j.val) ((N ^^^ V) ∥ D)).zipIdx.map
          (fun p => (Origin.block s (p.2 + 1), p.1)))) :
    encrypt bf E T ⟨j, M ∥ N⟩ = ⟨j, U ∥ V⟩ ∧
      leftover bf E T ⟨j, M ∥ N⟩ = D := by
  cases hrel with
  | cons hhead htail =>
    have hblocks : ∀ i (hi : i < numBlocks n j.val),
        E ((M ^^^ hashBits bf hbar T N) ^^^
            (U ^^^ hashBits bf hbar T V) ^^^ L ^^^ bin n (i + 1)) =
          (blocksTake n (numBlocks n j.val) ((N ^^^ V) ∥ D)).get
            ⟨i, by simpa using hi⟩ := by
      intro i hi
      have hiD : i <
          ((List.range (numBlocks n j.val)).map (fun i =>
            (Origin.block s (i + 1),
              (M ^^^ hashBits bf hbar T N) ^^^
                (U ^^^ hashBits bf hbar T V) ^^^ L ^^^ bin n (i + 1)))).length := by
        simp [hi]
      have hiR : i <
          ((blocksTake n (numBlocks n j.val) ((N ^^^ V) ∥ D)).zipIdx.map
            (fun p => (Origin.block s (p.2 + 1), p.1))).length := by
        simp [hi]
      have hiEq := htail.get hiD hiR
      simpa [List.get_eq_getElem, blocksTake] using hiEq
    exact encrypt_reconstruct bf hn E T j M U N V D hbar L
      hhbar hL hhead hblocks

private theorem inferEntry_reconstruct (bf : Hash.BlockField F n) (hn : 0 < n)
    (E : Perm n) (hbar L : BitString n) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w)
    (hlen : entry.2.1 = entry.1.2.2.1)
    (hD : D.1 = leftoverWidth entry.1)
    (hhbar : E (bin n 0) = hbar) (hL : E (bin n 1) = L)
    (hrel : List.Forall₂ (fun d r : Origin × BitString n => E d.2 = r.2)
      (inferEntry bf hbar L s entry D).1
      (inferEntry bf hbar L s entry D).2) :
    hctr2Fun bf E entry.1 = entry.2 ∧ leftoverOf bf E entry.1 = D := by
  rcases entry with ⟨⟨dir, T, j, P⟩, j', A⟩
  dsimp only at hlen hD ⊢
  subst j'
  rcases D with ⟨w, D⟩
  dsimp only [leftoverWidth] at hD
  subst w
  cases dir
  · let M : BitString n := P[0; n]
    let N : BitString j.val := P[n; j.val]
    let U : BitString n := A[0; n]
    let V : BitString j.val := A[n; j.val]
    have hP : M ∥ N = P := Bits.Facts.cat_sub_sub P
    have hA : U ∥ V = A := Bits.Facts.cat_sub_sub A
    have henc := inferLists_reconstruct bf hn E hbar L s T j M U N V D
      hhbar hL (by simpa [inferEntry, M, N, U, V] using hrel)
    constructor
    · simpa [hctr2Fun, hP, hA] using henc.1
    · change (⟨padLen n j.val - j.val, leftover bf E T ⟨j, P⟩⟩ :
          Σ width : ℕ, BitString width) = ⟨padLen n j.val - j.val, D⟩
      refine Sigma.ext rfl ?_
      exact heq_of_eq (by rw [← hP]; exact henc.2)
  · let M : BitString n := A[0; n]
    let N : BitString j.val := A[n; j.val]
    let U : BitString n := P[0; n]
    let V : BitString j.val := P[n; j.val]
    have hA : M ∥ N = A := Bits.Facts.cat_sub_sub A
    have hP : U ∥ V = P := Bits.Facts.cat_sub_sub P
    have henc := inferLists_reconstruct bf hn E hbar L s T j M U N V D
      hhbar hL (by simpa [inferEntry, M, N, U, V] using hrel)
    have hdec := congrArg (decrypt bf E T) henc.1
    rw [HCTR2.Facts.decrypt_encrypt] at hdec
    have hdec' : decrypt bf E T ⟨j, P⟩ = ⟨j, A⟩ := by
      simpa [hA, hP] using hdec.symm
    constructor
    · simpa [hctr2Fun] using hdec'
    · change (⟨padLen n j.val - j.val,
          leftover bf E T ⟨j, (decrypt bf E T ⟨j, P⟩).2⟩⟩ :
          Σ width : ℕ, BitString width) = ⟨padLen n j.val - j.val, D⟩
      have hplain : (decrypt bf E T ⟨j, P⟩).2 = A := by
        simp only [decrypt]
        simp only [decrypt] at hdec'
        exact eq_of_heq (Sigma.mk.inj_iff.mp hdec').2
      rw [hplain]
      refine Sigma.ext rfl ?_
      exact heq_of_eq (by rw [← hA]; exact henc.2)

private theorem augPerm_eq_of_inferred (bf : Hash.BlockField F n) (hn : 0 < n)
    (q σ : ℕ) (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (o : AugObs n cap tcap) (hwf : WellFormedAugObs o)
    (hlen : ∀ entry ∈ transcriptEntries o.1, entry.2.1 = entry.1.2.2.1)
    (table : RndTable n cap tcap)
    (ht : o.1 = PFunDDS.transcript (rndDDS n cap tcap q σ table) e m)
    (E : Perm n)
    (hrel : List.Forall₂ (fun d r : Origin × BitString n => E d.2 = r.2)
      (inferred bf o).1 (inferred bf o).2) :
    augPerm bf q σ e m E = o := by
  let entries := transcriptEntries o.1
  let leftovers := o.2.2
  have hlenLists : entries.length = leftovers.length := by
    have := congrArg List.length hwf
    simpa [WellFormedAugObs, entries, leftovers] using this.symm
  simp only [inferred] at hrel
  cases hrel with
  | cons hhbar hrel =>
    cases hrel with
    | cons hL hflat =>
      let zipped := (entries.zip leftovers).zipIdx
      let f := fun p : ((TQ n cap tcap × TM n cap) × (Σ w : ℕ, BitString w)) × ℕ =>
        (inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2).1
      let g := fun p : ((TQ n cap tcap × TM n cap) × (Σ w : ℕ, BitString w)) × ℕ =>
        (inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2).2
      have hlocal : ∀ p ∈ zipped,
          List.Forall₂ (fun d r : Origin × BitString n => E d.2 = r.2) (f p) (g p) := by
        apply forall₂_flatten_map_of_mem _ f g zipped
        · intro p hp
          rw [show (f p).length = entryCharge p.1.1 by
                exact length_inferEntry_fst bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2 hn,
            show (g p).length = entryCharge p.1.1 by
                exact length_inferEntry_snd bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2 hn]
        · simpa [zipped, f, g, entries, leftovers] using hflat
      have hpair : List.Forall₂
          (fun entry D => hctr2Fun bf E entry.1 = entry.2 ∧
            leftoverOf bf E entry.1 = D) entries leftovers := by
        rw [List.forall₂_iff_get]
        refine ⟨hlenLists, ?_⟩
        intro i hiE hiD
        have hzlen : i < zipped.length := by
          simpa [zipped, hlenLists] using hiD
        have hzmem := List.get_mem zipped ⟨i, hzlen⟩
        have hloc := hlocal (zipped.get ⟨i, hzlen⟩) hzmem
        have hwf' : leftovers.map Sigma.fst =
            entries.map (leftoverWidth ∘ Prod.fst) := by
          simpa [WellFormedAugObs, entries, leftovers] using hwf
        have hwidthMap := congrArg (fun l => l[i]?) hwf'
        have hwidth' : (leftovers.get ⟨i, hiD⟩).1 =
            leftoverWidth (entries.get ⟨i, hiE⟩).1 := by
          simpa [List.getElem?_map, List.getElem?_eq_getElem, hiD, hiE,
            Function.comp_def] using hwidthMap
        have hloc' : List.Forall₂ (fun d r : Origin × BitString n => E d.2 = r.2)
            (inferEntry bf o.2.1.1 o.2.1.2 i
              (entries.get ⟨i, hiE⟩) (leftovers.get ⟨i, hiD⟩)).1
            (inferEntry bf o.2.1.1 o.2.1.2 i
              (entries.get ⟨i, hiE⟩) (leftovers.get ⟨i, hiD⟩)).2 := by
          simpa [zipped, f, g, List.get_eq_getElem, hlenLists] using hloc
        exact inferEntry_reconstruct bf hn E o.2.1.1 o.2.1.2 i
          (entries.get ⟨i, hiE⟩) (leftovers.get ⟨i, hiD⟩)
          (hlen _ (List.get_mem entries ⟨i, hiE⟩)) hwidth' hhbar hL hloc'
      have hagree : ∀ entry ∈ entries, hctr2Fun bf E entry.1 = entry.2 := by
        intro entry hentry
        obtain ⟨i, hiE, hget⟩ := List.mem_iff_getElem.mp hentry
        have hiD : i < leftovers.length := by simpa [← hlenLists] using hiE
        have hp := hpair.get hiE hiD
        simpa [List.get_eq_getElem, hget] using hp.1
      have htrans : PFunDDS.transcript (hctr2DDS bf q σ E) e m = o.1 := by
        have h := transcript_filter_functionEvaluator_eq
          (Budget (n := n) (cap := cap) (tcap := tcap) q σ)
          (budget_prefixClosed q σ) (rndFun table) (hctr2Fun bf E) e m
          (by
            intro entry hentry
            apply hagree entry
            simpa [entries, ht, rndDDS] using hentry)
        simpa [rndDDS, hctr2DDS, ht] using h
      have hleftAux : ∀ {es : List (TQ n cap tcap × TM n cap)}
          {ds : List (Σ w : ℕ, BitString w)},
          List.Forall₂ (fun entry D => hctr2Fun bf E entry.1 = entry.2 ∧
            leftoverOf bf E entry.1 = D) es ds →
            es.map (fun entry => leftoverOf bf E entry.1) = ds := by
        intro es ds h
        induction h with
        | nil => rfl
        | cons hp hps ih => simp [hp.2, ih]
      have hleft : entries.map (fun entry => leftoverOf bf E entry.1) = leftovers :=
        hleftAux hpair
      change (PFunDDS.transcript (hctr2DDS bf q σ E) e m,
          (E (bin n 0), E (bin n 1)),
          (transcriptEntries (PFunDDS.transcript (hctr2DDS bf q σ E) e m)).map
            (fun entry => leftoverOf bf E entry.1)) = o
      rw [htrans]
      exact Prod.ext rfl
        (Prod.ext (Prod.ext hhbar hL) (by simpa [entries, leftovers] using hleft))

private theorem augPerm_mass_ge (bf : Hash.BlockField F n) (hn : 0 < n)
    (q σ : ℕ) (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (o : AugObs n cap tcap) (hwf : WellFormedAugObs o)
    (hlen : ∀ entry ∈ transcriptEntries o.1, entry.2.1 = entry.1.2.2.1)
    (table : RndTable n cap tcap)
    (ht : o.1 = PFunDDS.transcript (rndDDS n cap tcap q σ table) e m)
    (hgood : ¬ Bad bf o) :
    (((2 ^ n : ℕ) : ℝ) ^ sigmaM bf o)⁻¹ ≤ (augLawPerm bf q σ e m).val o := by
  rw [Bad, not_or, not_not, not_not] at hgood
  let dvals := (inferred bf o).1.map Prod.snd
  let rvals := (inferred bf o).2.map Prod.snd
  have hdlen : sigmaM bf o = dvals.length := by simp [sigmaM, dvals]
  have hrlen : sigmaM bf o = rvals.length := by
    simp [rvals, length_inferred_snd bf o hn]
  let a : Fin (sigmaM bf o) → BitString n := fun i => dvals.get (Fin.cast hdlen i)
  let b : Fin (sigmaM bf o) → BitString n := fun i => rvals.get (Fin.cast hrlen i)
  have ha : Function.Injective a := by
    intro i j hij
    have hcast : Fin.cast hdlen i = Fin.cast hdlen j :=
      (hgood.1.get_inj_iff).mp hij
    exact (Fin.cast_injective hdlen) hcast
  have hb : Function.Injective b := by
    intro i j hij
    have hcast : Fin.cast hrlen i = Fin.cast hrlen j :=
      (hgood.2.get_inj_iff).mp hij
    exact (Fin.cast_injective hrlen) hcast
  have hcard : sigmaM bf o ≤ Fintype.card (BitString n) := by
    simpa [Bits.Facts.card_Str] using sigmaM_le_card_of_good bf o
      (by rw [Bad, not_or, not_not, not_not]; exact hgood)
  have hmass := uniform_perm_consistent_mass_ge a ha b hb hcard
  rw [augLawPerm, Dist.PMF, Dist.fTransform_apply_eq_mass]
  refine le_trans (by simpa [Bits.Facts.card_Str] using hmass)
    (Dist.mass_mono Dist.uniform_nonNeg ?_)
  intro E hE
  apply augPerm_eq_of_inferred bf hn q σ e m o hwf hlen table ht E
  rw [List.forall₂_iff_get]
  refine ⟨length_inferred_snd bf o hn |>.symm, ?_⟩
  intro i hiD hiR
  have hi : i < sigmaM bf o := by simpa [sigmaM] using hiD
  have hEi := hE ⟨i, hi⟩
  simpa [a, b, dvals, rvals, hdlen, hrlen, List.get_eq_getElem] using hEi

private theorem uniform_dpi_output_le {I : Type} [Fintype I] [DecidableEq I]
    (A : I → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] {k : ℕ} (xs : Fin k → I)
    (v : ∀ i : Fin k, A (xs i)) :
    (Dist.uniform (∀ x, A x)).mass (fun f => ∀ i, f (xs i) = v i) ≤
      ∏ x ∈ Finset.univ.image xs, ((Fintype.card (A x) : ℝ))⁻¹ := by
  classical
  rw [uniform_dpi_eval_mass A xs (fun i a => a = v i)]
  calc
    ∏ x : I, (Dist.uniform (A x)).mass
        (fun a => ∀ i (h : xs i = x), h ▸ a = v i) ≤
        ∏ x : I, if x ∈ Finset.univ.image xs then
          ((Fintype.card (A x) : ℝ))⁻¹ else 1 := by
      refine Finset.prod_le_prod (fun _ _ => Dist.uniform_nonNeg.mass_nonneg _)
        (fun x _ => ?_)
      by_cases hx : x ∈ Finset.univ.image xs
      · rw [if_pos hx]
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
        subst x
        rw [Dist.uniform_mass_eq_card_filter, ← one_div,
          div_le_div_iff_of_pos_right (by positivity)]
        have hcard : (Finset.univ.filter (fun a : A (xs i) =>
            ∀ j (h : xs j = xs i), h ▸ a = v j)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact (ha i rfl).trans (hb i rfl).symm
        exact_mod_cast hcard
      · rw [if_neg hx]
        exact (Dist.mass_le_weight Dist.uniform_nonNeg _).trans_eq Dist.weight_uniform
    _ = ∏ x ∈ Finset.univ.image xs, ((Fintype.card (A x) : ℝ))⁻¹ := by
      rw [Finset.prod_ite_mem]
      congr 1
      exact (Finset.univ.image xs).inter_eq_right.mpr (by simp)

private theorem response_leftover_card_inv (hn : 0 < n) (j : ℕ) :
    ((Fintype.card (BitString (n + j)) : ℝ))⁻¹ *
        ((Fintype.card (BitString (padLen n j - j)) : ℝ))⁻¹ =
      ((((2 ^ n : ℕ) : ℝ) ^ (1 + numBlocks n j)))⁻¹ := by
  have hj : j ≤ padLen n j := le_padLen hn j
  have hexp : n + j + (padLen n j - j) = n * (1 + numBlocks n j) := by
    rw [show n + j + (padLen n j - j) = n + (j + (padLen n j - j)) by omega,
      Nat.add_sub_of_le hj, padLen_eq_mul]
    simp [Nat.mul_add]
  norm_num [Bits.Facts.card_Str, Nat.cast_pow]
  rw [← mul_inv, ← pow_add, hexp, pow_mul]

private theorem augRnd_mass_le (bf : Hash.BlockField F n) (hn : 0 < n)
    (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (k₀ : RndKey n cap tcap)
    (hnp : TweakablePRP.NPList
      (transcriptEntries (augRnd n cap tcap q σ e m k₀).1)) :
    (augLawRnd n cap tcap q σ e m).val (augRnd n cap tcap q σ e m k₀) ≤
      (((2 ^ n : ℕ) : ℝ) ^ sigmaM bf
        (augRnd n cap tcap q σ e m k₀))⁻¹ := by
  classical
  let o := augRnd n cap tcap q σ e m k₀
  let entries := transcriptEntries o.1
  let xs : Fin entries.length → TQ n cap tcap := fun i =>
    (entries.get ⟨i.val, i.isLt⟩).1
  let vs : Fin entries.length → TM n cap := fun i =>
    (entries.get ⟨i.val, i.isLt⟩).2
  let A : RndTable n cap tcap → Prop := fun f =>
    ∀ i, rndFun f (xs i) = vs i
  let B : BitString n × BitString n → Prop := fun z => z = k₀.2.1
  let C : (∀ z : TQ n cap tcap,
      BitString (padLen n z.2.2.1.val - z.2.2.1.val)) → Prop := fun g =>
    ∀ i, g (xs i) = k₀.2.2 (xs i)
  have himpl : ∀ k : RndKey n cap tcap, augRnd n cap tcap q σ e m k = o →
      A k.1 ∧ B k.2.1 ∧ C k.2.2 := by
    intro k hk
    have ht : PFunDDS.transcript (rndDDS n cap tcap q σ k.1) e m = o.1 := by
      exact congrArg Prod.fst hk
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hentry := List.get_mem entries ⟨i.val, i.isLt⟩
      have hentryK : entries.get ⟨i.val, i.isLt⟩ ∈ transcriptEntries
          (PFunDDS.transcript (rndDDS n cap tcap q σ k.1) e m) := by
        rw [ht]
        simpa [entries] using hentry
      have hans := answered_functionEvaluator
        (Budget (n := n) (cap := cap) (tcap := tcap) q σ)
        (budget_prefixClosed q σ) (rndFun k.1) e m
        (entries.get ⟨i.val, i.isLt⟩)
        (by simpa [rndDDS] using hentryK)
      exact hans
    · have hz := congrArg (fun z : AugObs n cap tcap => z.2.1) hk
      simpa [B, o, augRnd] using hz
    · intro i
      have hz := congrArg (fun z : AugObs n cap tcap => z.2.2) hk
      simp only [o, augRnd] at hz
      rw [ht] at hz
      change entries.map (fun entry =>
          (⟨padLen n entry.1.2.2.1.val - entry.1.2.2.1.val,
            k.2.2 entry.1⟩ : Σ w : ℕ, BitString w)) =
        entries.map (fun entry =>
          (⟨padLen n entry.1.2.2.1.val - entry.1.2.2.1.val,
            k₀.2.2 entry.1⟩ : Σ w : ℕ, BitString w)) at hz
      have hz' := congrArg (fun l => l[i.val]?) hz
      have hi : i.val < entries.length := i.isLt
      have hsigma :
          (⟨padLen n (xs i).2.2.1.val - (xs i).2.2.1.val, k.2.2 (xs i)⟩ :
              Σ w : ℕ, BitString w) =
            ⟨padLen n (xs i).2.2.1.val - (xs i).2.2.1.val, k₀.2.2 (xs i)⟩ := by
        apply Option.some.inj
        simpa [xs,
          List.getElem?_map, List.getElem?_eq_getElem, hi,
          List.get_eq_getElem] using hz'
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  rw [augLawRnd, Dist.PMF, Dist.fTransform_apply_eq_mass]
  refine le_trans (Dist.mass_mono Dist.uniform_nonNeg himpl) ?_
  change (Dist.uniform (RndKey n cap tcap)).mass
      (fun k => A k.1 ∧ B k.2.1 ∧ C k.2.2) ≤ _
  rw [← Dist.prod_uniform]
  have hrect : (fun k : RndKey n cap tcap => A k.1 ∧ B k.2.1 ∧ C k.2.2) =
      (fun k => A k.1 ∧ (fun z => B z.1 ∧ C z.2) k.2) := by
    funext k
    rfl
  rw [hrect]
  change (Dist.prod (Dist.uniform (RndTable n cap tcap))
      (Dist.uniform ((BitString n × BitString n) ×
        (∀ z : TQ n cap tcap,
          BitString (padLen n z.2.2.1.val - z.2.2.1.val))))).mass
      (fun k => A k.1 ∧ (fun z => B z.1 ∧ C z.2) k.2) ≤ _
  rw [Dist.mass_prod_and (Dist.uniform (RndTable n cap tcap))
    (Dist.uniform ((BitString n × BitString n) ×
      (∀ z : TQ n cap tcap,
        BitString (padLen n z.2.2.1.val - z.2.2.1.val))))
    A (fun z => B z.1 ∧ C z.2)]
  rw [show Dist.uniform ((BitString n × BitString n) ×
        (∀ z : TQ n cap tcap, BitString (padLen n z.2.2.1.val - z.2.2.1.val))) =
      Dist.prod (Dist.uniform (BitString n × BitString n))
        (Dist.uniform (∀ z : TQ n cap tcap,
          BitString (padLen n z.2.2.1.val - z.2.2.1.val))) from Dist.prod_uniform.symm,
    Dist.mass_prod_and]
  have hxs : Function.Injective xs := by
    intro i j hij
    apply hnp.1
    simpa [TweakablePRP.NPList, TweakablePRP.NP,
      TweakablePRP.transcriptOfPairs, List.Vector.get, xs, entries, o,
      List.get_eq_getElem] using hij
  have hA := TweakablePRP.rnd_output_le xs vs
  rw [Finset.prod_image (fun i _ j _ hij => hxs hij)] at hA
  have hC := uniform_dpi_output_le
    (fun z : TQ n cap tcap =>
      BitString (padLen n z.2.2.1.val - z.2.2.1.val)) xs
    (fun i => k₀.2.2 (xs i))
  rw [Finset.prod_image (fun i _ j _ hij => hxs hij)] at hC
  have hA' : (Dist.uniform (RndTable n cap tcap)).mass A ≤
      ∏ i : Fin entries.length,
        ((Fintype.card (BitString (n + (xs i).2.2.1.val)) : ℝ))⁻¹ := by
    simpa [A, rndFun, TweakablePRP.rndFun] using hA
  have hC' : (Dist.uniform (∀ z : TQ n cap tcap,
      BitString (padLen n z.2.2.1.val - z.2.2.1.val))).mass C ≤
      ∏ i : Fin entries.length,
        ((Fintype.card
          (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹ := by
    simpa [C] using hC
  have hB : (Dist.uniform (BitString n × BitString n)).mass B =
      (((2 ^ n : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [show B = (fun z : BitString n × BitString n => z = k₀.2.1) from rfl,
      Dist.mass_singleton, Dist.uniform_apply, Fintype.card_prod,
      Bits.Facts.card_Str]
    norm_num [Nat.cast_mul, pow_two, mul_inv]
  calc
    (Dist.uniform (RndTable n cap tcap)).mass A *
        ((Dist.uniform (BitString n × BitString n)).mass B *
          (Dist.uniform (∀ z : TQ n cap tcap,
            BitString (padLen n z.2.2.1.val - z.2.2.1.val))).mass C) ≤
      (∏ i : Fin entries.length,
          ((Fintype.card (BitString (n + (xs i).2.2.1.val)) : ℝ))⁻¹) *
        ((((2 ^ n : ℕ) : ℝ) ^ 2)⁻¹ *
          ∏ i : Fin entries.length,
            ((Fintype.card
              (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹) := by
        rw [hB]
        have hBC : (((2 ^ n : ℕ) : ℝ) ^ 2)⁻¹ *
              (Dist.uniform (∀ z : TQ n cap tcap,
                BitString (padLen n z.2.2.1.val - z.2.2.1.val))).mass C ≤
            (((2 ^ n : ℕ) : ℝ) ^ 2)⁻¹ *
              ∏ i : Fin entries.length,
                ((Fintype.card
                  (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hC' (by positivity)
        exact mul_le_mul hA' hBC
          (mul_nonneg (by positivity) (Dist.uniform_nonNeg.mass_nonneg _))
          (Finset.prod_nonneg fun _ _ => by positivity)
    _ = (((2 ^ n : ℕ) : ℝ) ^ sigmaM bf o)⁻¹ := by
      have hlen : entries.length = o.2.2.length := by
        have h := congrArg List.length (wellFormed_augRnd q σ e m k₀)
        simpa [WellFormedAugObs, entries, o] using h.symm
      have hzip :
          ((entries.zip o.2.2).map (fun p => entryCharge p.1)) =
            entries.map entryCharge := by
        simpa [Function.comp_def] using congrArg (List.map entryCharge)
          (List.map_fst_zip (le_of_eq hlen))
      have hsigma : sigmaM bf o = (entries.map entryCharge).sum + 2 := by
        rw [sigmaM_eq_charge bf o hn, hzip]
      have hsum :
          (∑ i : Fin entries.length, entryCharge (entries.get i)) =
            (entries.map entryCharge).sum := by
        rw [← Fin.sum_ofFn]
        simpa using congrArg List.sum (List.ofFn_comp' entries.get entryCharge)
      have hfactor (i : Fin entries.length) :
          ((Fintype.card (BitString (n + (xs i).2.2.1.val)) : ℝ))⁻¹ *
              ((Fintype.card
                (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹ =
            ((((2 ^ n : ℕ) : ℝ) ^ entryCharge (entries.get i)))⁻¹ := by
        rw [show entryCharge (entries.get i) =
            1 + numBlocks n (xs i).2.2.1.val by
          simpa [entryCharge, xs] using
            numBlocks_Msg_len (entries.get i).1.2.2 hn]
        exact response_leftover_card_inv hn _
      have hpairprod :
          (∏ i : Fin entries.length,
              ((Fintype.card (BitString (n + (xs i).2.2.1.val)) : ℝ))⁻¹) *
              (∏ i : Fin entries.length,
                ((Fintype.card
                  (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹) =
            ∏ i : Fin entries.length,
              ((((2 ^ n : ℕ) : ℝ) ^ entryCharge (entries.get i)))⁻¹ := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun i _ => hfactor i)
      have hchargeprod :
          (∏ i : Fin entries.length,
              ((((2 ^ n : ℕ) : ℝ) ^ entryCharge (entries.get i)))⁻¹) =
            ((((2 ^ n : ℕ) : ℝ) ^ (entries.map entryCharge).sum))⁻¹ := by
        rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, hsum]
      calc
        (∏ i : Fin entries.length,
              ((Fintype.card (BitString (n + (xs i).2.2.1.val)) : ℝ))⁻¹) *
            (((((2 ^ n : ℕ) : ℝ) ^ 2))⁻¹ *
              ∏ i : Fin entries.length,
                ((Fintype.card
                  (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹) =
          ((((2 ^ n : ℕ) : ℝ) ^ 2))⁻¹ *
            ((∏ i : Fin entries.length,
                ((Fintype.card (BitString (n + (xs i).2.2.1.val)) : ℝ))⁻¹) *
              ∏ i : Fin entries.length,
                ((Fintype.card
                  (BitString (padLen n (xs i).2.2.1.val - (xs i).2.2.1.val)) : ℝ))⁻¹) := by
            ring
        _ = ((((2 ^ n : ℕ) : ℝ) ^ 2))⁻¹ *
              (∏ i : Fin entries.length,
                ((((2 ^ n : ℕ) : ℝ) ^ entryCharge (entries.get i)))⁻¹) := by
            rw [hpairprod]
        _ = ((((2 ^ n : ℕ) : ℝ) ^ 2))⁻¹ *
              ((((2 ^ n : ℕ) : ℝ) ^ (entries.map entryCharge).sum))⁻¹ := by
            rw [hchargeprod]
        _ = ((((2 ^ n : ℕ) : ℝ) ^ ((entries.map entryCharge).sum + 2)))⁻¹ := by
            rw [← mul_inv, ← pow_add, Nat.add_comm]
        _ = (((2 ^ n : ℕ) : ℝ) ^ sigmaM bf o)⁻¹ := by rw [hsigma]
    _ = (((2 ^ n : ℕ) : ℝ) ^ sigmaM bf
        (augRnd n cap tcap q σ e m k₀))⁻¹ := rfl

private theorem response_length_augRnd (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (k : RndKey n cap tcap) :
    ∀ entry ∈ transcriptEntries (augRnd n cap tcap q σ e m k).1,
      entry.2.1 = entry.1.2.2.1 := by
  intro entry hentry
  have hanswer := answered_functionEvaluator
    (Budget (n := n) (cap := cap) (tcap := tcap) q σ)
    (budget_prefixClosed q σ) (rndFun k.1) e m entry
    (by simpa [rndDDS] using hentry)
  simpa [rndFun] using (congrArg Sigma.fst hanswer).symm

/-- **§3.4.1's support-local good dominance.**  An ideal-support witness fixes
the adaptive transcript, the two seeds, and every leftover.  Its ideal mass is
at most `2^{−n σₘ}`.  On `¬ Bad`, the inferred inputs and outputs are two
injective `σₘ`-tuples; every permutation satisfying those pins reconstructs
the complete augmented observation, so its real mass is at least the same
quantity.  `TweakablePRP.NP` is the paper's standing adversary restriction,
not an H premise.

The support premise is deliberate: `δ` only sums over the ideal support, so neither H nor
the paper requires point-mass calculations for unreachable observations. -/
theorem good_ratio_holds (bf : Hash.BlockField F n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (o : AugObs n cap tcap)
    (ho : o ∈ (augLawRnd n cap tcap q σ e m).val.support)
    (hnp : TweakablePRP.NPList (transcriptEntries o.1))
    (hgood : ¬ Bad bf o) :
    (augLawRnd n cap tcap q σ e m).val o ≤
      (augLawPerm bf q σ e m).val o := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [Bad, inferred] at hgood
    exact hgood.1.1 (Subsingleton.elim _ _)
  change o ∈ (Dist.fTransform (augRnd n cap tcap q σ e m)
    (Dist.uniform (RndKey n cap tcap))).support at ho
  obtain ⟨k₀, _, hk₀⟩ := Dist.mem_support_fTransform _ _ ho
  have hnp₀ : TweakablePRP.NPList
      (transcriptEntries (augRnd n cap tcap q σ e m k₀).1) := by
    rw [hk₀]
    exact hnp
  have hideal := augRnd_mass_le bf hn q σ e m k₀ hnp₀
  have hideal' : (augLawRnd n cap tcap q σ e m).val o ≤
      (((2 ^ n : ℕ) : ℝ) ^ sigmaM bf o)⁻¹ := by
    simpa only [hk₀] using hideal
  have hwf : WellFormedAugObs o := by
    rw [← hk₀]
    exact wellFormed_augRnd q σ e m k₀
  have hlen : ∀ entry ∈ transcriptEntries o.1,
      entry.2.1 = entry.1.2.2.1 := by
    rw [← hk₀]
    exact response_length_augRnd q σ e m k₀
  have ht : o.1 = PFunDDS.transcript
      (rndDDS n cap tcap q σ k₀.1) e m := by
    rw [← hk₀]
    exact fst_augRnd q σ e m k₀
  exact hideal'.trans
    (augPerm_mass_ge bf hn q σ e m o hwf hlen k₀.1 ht hgood)

/-! #### The bridging: one free coordinate

Every one of §3.4.2's twenty-two cases is the same argument — *fix everything except one
`n`-bit coordinate; at most `B` values of it make the equation hold; therefore the
probability is at most `B/2ⁿ`*.  p. 11 states it once and applies it throughout:

  > conditioning on a query and all prior queries and responses, we still have that `h̄`,
  > `L`, and the query response are uniformly random and independent

`Dist.mass_le_of_fiber_bound` is that sentence.  Note what it conditions on: the *other key
coordinates*, which are independent by construction of `RndKey` — never the transcript.
That is what dissolves p. 11's adaptivity caution ("if the choice of later query depends
on the earlier response…") rather than having to reason around it. -/

/-! #### Figures 4 and 5 as a cost table

The paper's case analysis is a **table**.  For each pair of inferred labels, Figure 4
(`𝒟`) and Figure 5 (`ℛ`) record how many values of one free coordinate make that pair
collide: red `0` impossible, grey `1` exactly one value, green `dˢ` or `max(dʳ,dˢ)` the
roots of a polynomial.  `cost` is that table transcribed.

Reading it as a table rather than as four aggregate groups is what keeps each obligation
**local**, and what gives §3.2 somewhere to attach: the green cells *are* the root counts,
so `prop1`/`prop2`/`prop3` are consumed exactly at the cells the paper cites them for. -/

/-- `dˢ` for query `s`: `mˢ + ⌈|Tˢ|/n⌉`, the degree of that query's hash polynomial
(paper p. 10).  Unasked queries have degree `0`. -/
def degOf (o : AugObs n cap tcap) (s : ℕ) : ℕ :=
  match (answered o)[s]? with
  | some entry => Poly.d n entry.2.1.len entry.2.2.1.val
  | none => 0

/-- Whether query `s` is an **encryption** query.  The table depends on it: p. 12, under
the figures — "*even where a square is green, if query `s` is a decryption query, the
probability of a particular collision of that kind is `1/2ⁿ`*", and dually "*Figure 5 …
it is only decryption queries where probabilities may be above `1/2ⁿ`*". -/
def dirOf (o : AugObs n cap tcap) (s : ℕ) : Bool :=
  match (answered o)[s]? with
  | some entry => match entry.1 with
      | QueryDir.fwd => true
      | QueryDir.inv => false
  | none => true

/-- The exhaustive structural cells of an ordered pair of inferred labels.

`head` means block `0`; `tail s k` means block `k + 1`.  Keeping these as an
inductive type, rather than a wildcard-heavy numeric function, is the
coverage boundary for §3.4.2: a proof that dispatches on a `CollisionCell`
must handle every constructor, and adding a new inferred-origin shape breaks
that dispatch.

The three apparently reversed constructors (`headSeed`, `tailSeed`, and some
same-query index orders) are retained deliberately.  `cellOfOrigins` is total
on arbitrary origins, while a `RealizedPair` below proves that the particular
origins came from the reconstructed list.  The case proof must therefore
either handle a cell or discharge it from the list order; it cannot disappear
behind a default branch. -/
inductive CollisionCell
  | seedSeed (a b : ℕ)
  | seedHead (a s : ℕ)
  | seedTail (a s k : ℕ)
  | headSeed (s a : ℕ)
  | tailSeed (s k a : ℕ)
  | headHead (r s : ℕ)
  | headTail (r s k : ℕ)
  | tailHead (r k s : ℕ)
  | tailTail (r k s l : ℕ)
  deriving DecidableEq

namespace CollisionCell

/-- The pair of loose origins denoted by a structural cell. -/
def origins : CollisionCell → Origin × Origin
  | seedSeed a b => (Origin.seed a, Origin.seed b)
  | seedHead a s => (Origin.seed a, Origin.block s 0)
  | seedTail a s k => (Origin.seed a, Origin.block s (Nat.succ k))
  | headSeed s a => (Origin.block s 0, Origin.seed a)
  | tailSeed s k a => (Origin.block s (Nat.succ k), Origin.seed a)
  | headHead r s => (Origin.block r 0, Origin.block s 0)
  | headTail r s k => (Origin.block r 0, Origin.block s (Nat.succ k))
  | tailHead r k s => (Origin.block r (Nat.succ k), Origin.block s 0)
  | tailTail r k s l =>
      (Origin.block r (Nat.succ k), Origin.block s (Nat.succ l))

/-- The four numerical certificates used by Figures 4 and 5.  This is kept
separate from `CollisionCell`: cells remember the equation shape; bounds only
remember how many values of the selected free coordinate may solve it. -/
inductive Bound
  | impossible
  | unit
  | degree (s : ℕ)
  | maxDegree (r s : ℕ)
  deriving DecidableEq

namespace Bound

/-- Interpret a symbolic cell bound using the observation's degree function. -/
def cost (deg : ℕ → ℕ) : Bound → ℕ
  | impossible => 0
  | unit => 1
  | degree s => deg s
  | maxDegree r s => max (deg r) (deg s)

end Bound

/-- Figures 4 and 5, still symbolically: `side = true` for the input side and
`false` for the output side.  Direction and same-query tests refine a
structural cell to the certificate that its equation must supply. -/
def bound (side : Bool) (dir : ℕ → Bool) : CollisionCell → Bound
  | seedSeed _ _ => if side then .impossible else .unit
  | seedHead _ s => if dir s = side then .degree s else .unit
  | seedTail _ _ _ => .unit
  | headSeed s _ => if dir s = side then .degree s else .unit
  | tailSeed _ _ _ => .unit
  | headHead r s => if dir s = side then .maxDegree r s else .unit
  | headTail _ _ _ => .unit
  | tailHead r _ s =>
      if r = s then .unit
      else if side then .unit
      else if dir s = side then .degree s else .unit
  | tailTail r _ s _ =>
      if r = s then (if side then .impossible else .unit) else .unit

end CollisionCell

/-- Total structural classification of two loose origins.  There is no
catch-all cell: head/tail is exposed by recursion on each block index. -/
def cellOfOrigins : Origin → Origin → CollisionCell
  | Origin.seed a, Origin.seed b => .seedSeed a b
  | Origin.seed a, Origin.block s 0 => .seedHead a s
  | Origin.seed a, Origin.block s (Nat.succ k) => .seedTail a s k
  | Origin.block s 0, Origin.seed a => .headSeed s a
  | Origin.block s (Nat.succ k), Origin.seed a => .tailSeed s k a
  | Origin.block r 0, Origin.block s 0 => .headHead r s
  | Origin.block r 0, Origin.block s (Nat.succ k) => .headTail r s k
  | Origin.block r (Nat.succ k), Origin.block s 0 => .tailHead r k s
  | Origin.block r (Nat.succ k), Origin.block s (Nat.succ l) => .tailTail r k s l

/-- Classification reconstructs exactly the origins it classified.  This is
the semantic equation later used to rewrite a generic collision into the
equation attached to its cell. -/
@[simp] theorem origins_cell_of_origins (a b : Origin) :
    (cellOfOrigins a b).origins = (a, b) := by
  cases a with
  | seed a =>
      cases b with
      | seed b => rfl
      | block s k => cases k <;> rfl
  | block r i =>
      cases b with
      | seed b => cases i <;> rfl
      | block s j => cases i <;> cases j <;> rfl

/-- **Figures 4 and 5** (paper p. 12), `side = true` for `𝒟` and `false` for `ℛ`.

Pairs are read in inference order — seeds, then by query, then by block — which is the
order positions occur in `inferred`, so `r ≤ s` throughout.

**A green cell is only green on one side.** `𝒟`'s green cells count for encryption
queries, `ℛ`'s for decryption queries, so the gate is `dirOf s = side` and each query
pays on exactly one of the two sides.  Dropping the gate is not conservative: it doubles
`c_f` to `4σ` and `costSum_le` becomes false.

The two sides then differ in exactly three ways, and each is one of the paper's
asymmetries:

* `(bin 0, bin 1)` is impossible on `𝒟` but `(h̄, L)` costs `1` on `ℛ`  — this is `c_b = −1`
* `(Sᵢˢ, Sⱼˢ)` is impossible on `𝒟` but `(Yᵢˢ, Yⱼˢ)` costs `1` on `ℛ` — this is `c_w ≤ 0`
* `(Sᵢʳ, MMˢ)` costs `1` on `𝒟` but `(Yᵢʳ, UUˢ)` costs `dˢ` on `ℛ` — this is `c_a`'s
  `(mʳ − 1)(dˢ − 1)` term

Two cells are deliberately over-approximated, and the gate is what keeps that free:
`(L, UUˢ)` is grey in Figure 5 but scored `dˢ` here, and likewise `(bin 1, MMˢ)`'s mirror.
Because only one side's greens are live per query, the total is still the paper's
`Σ_s 2(dˢ − 1) ≤ 2σ`, which is exactly its `max(2(dˢ−1), dˢ−1)`.

The `block r 0, block s 0` cell at `r = s` is unreachable: labels are unique, so two
distinct positions never carry the same label.

This numeric view is now derived from the exhaustive symbolic classifier; it
is not a second transcription of the figures. -/
def cost (side : Bool) (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (a b : Origin) : ℕ :=
  ((cellOfOrigins a b).bound side dir).cost deg

/-! #### The layout

`costSum` sums the table over *positions*, so bounding it needs to know which label sits
where.  Both sides have the same layout — two seeds, then each query's `mˢ` blocks in order
— which is `length_inferEntry_fst`/`_snd` refined from lengths to labels. -/

/-- **UPSTREAM-CANDIDATE.**  Mapping a function of the index over `zipIdx`. -/
theorem zipIdx_map_index {α β : Type*} (l : List α) (f : ℕ → β) :
    (l.zipIdx.map (fun p => f p.2)) = (List.range l.length).map f := by
  rw [show (fun p : α × ℕ => f p.2) = f ∘ Prod.snd from rfl, List.map_map.symm,
    List.zipIdx_map_snd, List.range_eq_range']

/-- **UPSTREAM-CANDIDATE.**  Peeling the head off a `range`-map. -/
theorem range_map_succ {β : Type*} (k : ℕ) (f : ℕ → β) :
    (List.range (1 + k)).map f = f 0 :: (List.range k).map (fun i => f (i + 1)) := by
  rw [Nat.add_comm, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- The label sequence of one side. -/
def labelsOf (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool) : List Origin :=
  (sideOf bf o d).map Prod.fst

/-- The per-query label block: `[block s 0, …, block s (mˢ−1)]`. -/
def queryLabels (entry : TQ n cap tcap × TM n cap) (s : ℕ) : List Origin :=
  (List.range (entryCharge entry)).map (Origin.block s)

private theorem map_fst_inferEntry (bf : Hash.BlockField F n) (hbar L : BitString n) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w) (hn : 0 < n) :
    ((inferEntry bf hbar L s entry D).1.map Prod.fst) = queryLabels entry s ∧
      ((inferEntry bf hbar L s entry D).2.map Prod.fst) = queryLabels entry s := by
  rcases entry with ⟨w, r⟩
  have hm : entryCharge ((w, r) : TQ n cap tcap × TM n cap)
      = 1 + numBlocks n w.2.2.1.val := by
      rw [entryCharge, numBlocks_Msg_len w.2.2 hn]
  have hpeel : queryLabels ((w, r) : TQ n cap tcap × TM n cap) s
      = Origin.block s 0 ::
        (List.range (numBlocks n w.2.2.1.val)).map (fun i => Origin.block s (i + 1)) := by
    rw [queryLabels, hm, range_map_succ]
  refine ⟨?_, ?_⟩
  · rw [hpeel]
    simp only [inferEntry, List.map_cons, List.map_map]
    rfl
  · rw [hpeel]
    simp only [inferEntry, List.map_cons, List.map_map, Function.comp_def]
    refine congrArg (Origin.block s 0 :: ·) ?_
    rw [zipIdx_map_index (f := fun i => Origin.block s (i + 1)), length_blocksTake]

/-- **The layout**: two seeds, then every query's blocks in order — the same on both sides. -/
theorem labelsOf_eq (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n) :
    labelsOf bf o d = Origin.seed 0 :: Origin.seed 1 ::
      (((transcriptEntries o.1).zip o.2.2).zipIdx.map
        (fun p => queryLabels p.1.1 p.2)).flatten := by
  have hper : ∀ g : List (Origin × BitString n) × List (Origin × BitString n) → List (Origin × BitString n),
      (∀ (s : ℕ) (entry : TQ n cap tcap × TM n cap) (D : Σ w : ℕ, BitString w),
        (g (inferEntry bf o.2.1.1 o.2.1.2 s entry D)).map Prod.fst = queryLabels entry s) →
      (((((transcriptEntries o.1).zip o.2.2).zipIdx.map
          (fun p => inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2)).map g).flatten).map Prod.fst
        = (((transcriptEntries o.1).zip o.2.2).zipIdx.map
          (fun p => queryLabels p.1.1 p.2)).flatten := by
    intro g hg
    rw [List.map_map, List.map_flatten, List.map_map]
    exact congrArg List.flatten (List.map_congr_left fun p _ => hg p.2 p.1.1 p.1.2)
  cases d
  · show ((inferred bf o).2).map Prod.fst = _
    simp only [inferred, List.map_cons]
    exact congrArg (fun t => Origin.seed 0 :: Origin.seed 1 :: t)
      (hper Prod.snd fun s entry D => (map_fst_inferEntry bf o.2.1.1 o.2.1.2 s entry D hn).2)
  · show ((inferred bf o).1).map Prod.fst = _
    simp only [inferred, List.map_cons]
    exact congrArg (fun t => Origin.seed 0 :: Origin.seed 1 :: t)
      (hper Prod.fst fun s entry D => (map_fst_inferEntry bf o.2.1.1 o.2.1.2 s entry D hn).1)

/-- The label at position `i` of side `d`. -/
def labelAt (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool) (i : ℕ) :
    Option Origin := ((sideOf bf o d)[i]?).map Prod.fst

/-- Every label found at an actual position is one emitted by the layout:
the two seeds are `0` and `1`, and every other label is a query block.  This is
the promised proof that the collision classifier covers the reconstructed
list, rather than merely covering the loose `Origin` datatype. -/
theorem label_at_valid (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (hn : 0 < n) {i : ℕ} {x : Origin}
    (h : labelAt bf o d i = some x) : Origin.Valid x := by
  have hi : (labelsOf bf o d)[i]? = some x := by
    simpa only [labelsOf, labelAt, List.getElem?_map] using h
  have hmem : x ∈ labelsOf bf o d := List.mem_iff_getElem?.mpr ⟨i, hi⟩
  rw [labelsOf_eq bf o d hn] at hmem
  simp only [List.mem_cons, List.mem_flatten, List.mem_map] at hmem
  rcases hmem with rfl | rfl | ⟨ys, ⟨p, _, rfl⟩, hx⟩
  · simp [Origin.Valid]
  · simp [Origin.Valid]
  · simp only [queryLabels, List.mem_map] at hx
    rcases hx with ⟨k, _, rfl⟩
    simp [Origin.Valid]

/-- Two ordered positions together with the exact entries reconstructed there.

This is the typed input to the §3.4.2 case split.  In particular, neither the
origins nor the values can be invented independently of `sideOf`: both lookup
equations are fields of the witness. -/
structure RealizedPair (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (i j : ℕ) where
  left : Origin × BitString n
  right : Origin × BitString n
  left_eq : (sideOf bf o d)[i]? = some left
  right_eq : (sideOf bf o d)[j]? = some right
  ordered : i < j

namespace RealizedPair

variable {bf : Hash.BlockField F n} {o : AugObs n cap tcap}
  {d : Bool} {i j : ℕ}

/-- The semantic event carried by a realized pair. -/
def Collides (p : RealizedPair bf o d i j) : Prop := p.left.2 = p.right.2

/-- The exhaustive structural cell of the two reconstructed labels. -/
def cell (p : RealizedPair bf o d i j) : CollisionCell :=
  cellOfOrigins p.left.1 p.right.1

/-- A realized pair reconstructs both labels at the stated positions. -/
theorem labels (p : RealizedPair bf o d i j) :
    labelAt bf o d i = some p.left.1 ∧
      labelAt bf o d j = some p.right.1 := by
  constructor
  · simp [labelAt, p.left_eq]
  · simp [labelAt, p.right_eq]

/-- The cell's origin equation is exactly the pair's reconstructed origin
equation; no semantic information is lost by classification. -/
@[simp] theorem cell_origins (p : RealizedPair bf o d i j) :
    p.cell.origins = (p.left.1, p.right.1) := by
  exact origins_cell_of_origins _ _

/-- Actual pairs satisfy the seed/layout validity invariant. -/
theorem valid_origins (p : RealizedPair bf o d i j) (hn : 0 < n) :
    Origin.Valid p.left.1 ∧ Origin.Valid p.right.1 :=
  ⟨label_at_valid bf o d hn p.labels.1,
    label_at_valid bf o d hn p.labels.2⟩

end RealizedPair

/-- Collision of two fixed positions, expressed through an actual reconstructed
pair rather than a free existential over labels and values. -/
def pairCollision (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (i j : ℕ) : Prop :=
  ∃ p : RealizedPair bf o d i j, p.Collides

/-- The classifier at two fixed positions.  `none` means that the positions
are absent or not in inference order; `some cell` is the unique structural
case generated by their actual labels. -/
def collisionCellAt (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (i j : ℕ) : Option CollisionCell :=
  if i < j then
    match labelAt bf o d i, labelAt bf o d j with
    | some a, some b => some (cellOfOrigins a b)
    | _, _ => none
  else none

/-- Classification succeeds on every realized pair. -/
theorem RealizedPair.cell_at_eq_some
    {bf : Hash.BlockField F n} {o : AugObs n cap tcap}
    {d : Bool} {i j : ℕ} (p : RealizedPair bf o d i j) :
    collisionCellAt bf o d i j = some p.cell := by
  rw [collisionCellAt, if_pos p.ordered, p.labels.1, p.labels.2]
  rfl

/-- **Coverage theorem for the case split.**  A positional collision is
equivalent to a colliding realized pair whose unique cell was produced by the
total classifier.  This is the theorem the §3.4.2 fiber proof must eliminate;
case coverage can therefore no longer be asserted independently of the full
inferred list. -/
theorem pair_collision_iff_exists_cell
    (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool) (i j : ℕ) :
    pairCollision bf o d i j ↔
      ∃ p : RealizedPair bf o d i j,
        p.Collides ∧ collisionCellAt bf o d i j = some p.cell := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hp, p.cell_at_eq_some⟩
  · rintro ⟨p, hp, -⟩
    exact ⟨p, hp⟩

/-- Compatibility with the raw lookup form, now as a proved theorem rather
than the definition of the event. -/
theorem pair_collision_iff_raw
    (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (d : Bool) (i j : ℕ) :
    pairCollision bf o d i j ↔
      i < j ∧ ∃ a b : Origin × BitString n,
        (sideOf bf o d)[i]? = some a ∧
        (sideOf bf o d)[j]? = some b ∧ a.2 = b.2 := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.ordered, p.left, p.right, p.left_eq, p.right_eq, hp⟩
  · rintro ⟨hij, a, b, ha, hb, hab⟩
    exact ⟨⟨a, b, ha, hb, hij⟩, hab⟩

/-- The table entry for positions `i < j` of side `d`, obtained only after
classifying their reconstructed labels.  Absent and unordered positions cost
nothing. -/
def costAt (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (i j : ℕ) : ℕ :=
  match collisionCellAt bf o d i j with
  | some cell => (cell.bound d (dirOf o)).cost (degOf o)
  | none => 0

/-- On a realized pair, the positional cost is exactly the symbolic cell's
numeric interpretation. -/
theorem cost_at_eq_of_realized_pair
    {bf : Hash.BlockField F n} {o : AugObs n cap tcap}
    {d : Bool} {i j : ℕ} (p : RealizedPair bf o d i j) :
    costAt bf o d i j = cost d (degOf o) (dirOf o) p.left.1 p.right.1 := by
  rw [costAt, p.cell_at_eq_some]
  rfl

/-- **Paper p. 15's `2·C(σₘ,2) + c`**: the total table cost of every inferred pair, both
sides.  Indices run to `σ + 2` because `sigmaM_le_of_budget` bounds `σₘ` there. -/
def costSum (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (σ : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (σ + 2), ∑ j ∈ Finset.range (σ + 2),
    (costAt bf o true i j + costAt bf o false i j)

/-- The mass that two actual ordered positions of side `d` carry the same
value.  Ordering and list realization are inside `pairCollision`; there is no
parallel untyped event to keep synchronized with the classifier. -/
noncomputable def collAt (bf : Hash.BlockField F n) (law : Dist (AugObs n cap tcap))
    (d : Bool) (i j : ℕ) : ℝ :=
  law.mass (fun o => pairCollision bf o d i j)

/-- **Global collision completeness.**  The list-based definition of `Bad` is
equivalent to the existence of a colliding `RealizedPair` on one of the two
sides.  Unlike the budgeted union-bound theorem below, this equivalence has no
cutoff and therefore certifies the full inferred list. -/
theorem bad_iff_exists_pair_collision (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) :
    Bad bf o ↔
      (∃ i j, pairCollision bf o true i j) ∨
        (∃ i j, pairCollision bf o false i j) := by
  have forward : ∀ d : Bool, ¬ ((sideOf bf o d).map Prod.snd).Nodup →
      ∃ i j, pairCollision bf o d i j := by
    intro d hd
    rw [List.nodup_iff_getElem?_ne_getElem?] at hd
    push Not at hd
    obtain ⟨i, j, hij, hjlen, heq⟩ := hd
    have hjl : j < (sideOf bf o d).length := by simpa using hjlen
    have hil : i < (sideOf bf o d).length := lt_trans hij hjl
    refine ⟨i, j, ⟨⟨(sideOf bf o d)[i], (sideOf bf o d)[j],
      List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hjl, hij⟩, ?_⟩⟩
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hil,
      List.getElem?_eq_getElem hjl] at heq
    exact Option.some_injective _ heq
  have reverse : ∀ d : Bool, (∃ i j, pairCollision bf o d i j) →
      ¬ ((sideOf bf o d).map Prod.snd).Nodup := by
    rintro d ⟨i, j, p, hp⟩ hnodup
    rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
    have hjl : j < (sideOf bf o d).length :=
      (List.getElem?_eq_some_iff.mp p.right_eq).choose
    have hne := hnodup i j p.ordered (by simpa using hjl)
    apply hne
    rw [List.getElem?_map, List.getElem?_map, p.left_eq, p.right_eq]
    exact congrArg some hp
  constructor
  · rintro (hbad | hbad)
    · exact Or.inl (forward true (by simpa [sideOf] using hbad))
    · exact Or.inr (forward false (by simpa [sideOf] using hbad))
  · rintro (hbad | hbad)
    · exact Or.inl (by simpa [sideOf] using reverse true hbad)
    · exact Or.inr (by simpa [sideOf] using reverse false hbad)

/-- A bad observation has two colliding positions on one side, both below `σ + 2`. -/
theorem bad_iff_exists_pair (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (σ : ℕ)
    (hn : 0 < n) (hb : sigmaM bf o ≤ σ + 2) (h : Bad bf o) :
    ∃ p ∈ (Finset.range (σ + 2)) ×ˢ (Finset.range (σ + 2)),
      pairCollision bf o true p.1 p.2 ∨
        pairCollision bf o false p.1 p.2 := by
  have place : ∀ d i j, pairCollision bf o d i j →
      (i, j) ∈ (Finset.range (σ + 2)) ×ˢ (Finset.range (σ + 2)) := by
    rintro d i j ⟨p, -⟩
    have hjl : j < (sideOf bf o d).length :=
      (List.getElem?_eq_some_iff.mp p.right_eq).choose
    have hjσ : j < σ + 2 :=
      lt_of_lt_of_le (lt_of_lt_of_le hjl (length_sideOf_le bf o d hn)) hb
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_trans p.ordered hjσ), Finset.mem_range.mpr hjσ⟩
  rcases (bad_iff_exists_pair_collision bf o).mp h with
      ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact ⟨(i, j), place true i j hij, Or.inl hij⟩
  · exact ⟨(i, j), place false i j hij, Or.inr hij⟩

/-- **The union bound** (paper p. 15's first display): `Pr[𝒯_bad] ≤ Σ_pairs Pr[a = b]`. -/
theorem probBad_le_sum_collAt (bf : Hash.BlockField F n)
    (law : Dist (AugObs n cap tcap))
    (hnn : law.NonNeg) (σ : ℕ) (hn : 0 < n)
    (hbudget : ∀ o ∈ law.support, sigmaM bf o ≤ σ + 2) :
    probBad law (Bad bf)
      ≤ ∑ p ∈ (Finset.range (σ + 2)) ×ˢ (Finset.range (σ + 2)),
          (collAt bf law true p.1 p.2 + collAt bf law false p.1 p.2) := by
  classical
  refine le_trans (Dist.mass_mono_support hnn (Q := fun o =>
      ∃ p ∈ (Finset.range (σ + 2)) ×ˢ (Finset.range (σ + 2)),
        pairCollision bf o true p.1 p.2 ∨
          pairCollision bf o false p.1 p.2)
    (fun o ho hbad => bad_iff_exists_pair bf o σ hn (hbudget o ho) hbad))
    (le_trans (Dist.mass_exists_le hnn _ _) (Finset.sum_le_sum fun p _ => ?_))
  simpa only [collAt] using
    (Dist.mass_or_le hnn
      (fun o => pairCollision bf o true p.1 p.2)
      (fun o => pairCollision bf o false p.1 p.2))

-- The collision-fibre proof below is private, generated case-analysis scaffolding.
-- Its binders are deliberately inferred from the surrounding dependent types;
-- restore the project-wide explicit-binder discipline immediately afterwards.
set_option autoImplicit true

def plainPartsP (entry : TQ n cap tcap × TM n cap) :
    BitString n × BitString entry.1.2.2.1.val :=
  match entry.1.1 with
  | .fwd => (entry.1.2.2.2[0; n], entry.1.2.2.2[n; entry.1.2.2.1.val])
  | .inv => (entry.2.2[0; n], entry.2.2[n; entry.1.2.2.1.val])

def cipherPartsP (entry : TQ n cap tcap × TM n cap) :
    BitString n × BitString entry.1.2.2.1.val :=
  match entry.1.1 with
  | .fwd => (entry.2.2[0; n], entry.2.2[n; entry.1.2.2.1.val])
  | .inv => (entry.1.2.2.2[0; n], entry.1.2.2.2[n; entry.1.2.2.1.val])

def mmP (bf : Hash.BlockField F n) (hbar : BitString n)
    (entry : TQ n cap tcap × TM n cap) : BitString n :=
  (plainPartsP entry).1 ^^^
    hashBits bf hbar entry.1.2.1 (plainPartsP entry).2

def uuP (bf : Hash.BlockField F n) (hbar : BitString n)
    (entry : TQ n cap tcap × TM n cap) : BitString n :=
  (cipherPartsP entry).1 ^^^
    hashBits bf hbar entry.1.2.1 (cipherPartsP entry).2

def ssP (bf : Hash.BlockField F n) (hbar L : BitString n)
    (entry : TQ n cap tcap × TM n cap) : BitString n :=
  mmP bf hbar entry ^^^ uuP bf hbar entry ^^^ L

def yBlocksP (entry : TQ n cap tcap × TM n cap) (D : Σ w, BitString w) :
    List (BitString n) :=
  blocksTake n (numBlocks n entry.1.2.2.1.val)
    (((plainPartsP entry).2 ^^^ (cipherPartsP entry).2) ∥ D.2)

theorem inferEntry_eq_semanticP (bf : Hash.BlockField F n) (hbar L : BitString n)
    (s : ℕ) (entry : TQ n cap tcap × TM n cap) (D : Σ w, BitString w) :
    inferEntry bf hbar L s entry D =
      ((Origin.block s 0, mmP bf hbar entry) ::
        (List.range (numBlocks n entry.1.2.2.1.val)).map
          (fun i => (Origin.block s (i + 1),
            ssP bf hbar L entry ^^^ bin n (i + 1))),
       (Origin.block s 0, uuP bf hbar entry) ::
        (yBlocksP entry D).zipIdx.map
          (fun p => (Origin.block s (p.2 + 1), p.1))) := by
  rcases entry with ⟨⟨dir, T, j, qv⟩, resp⟩
  cases dir <;> rfl

theorem mem_inferEntry_fst_iffP (bf : Hash.BlockField F n) (hbar L : BitString n)
    (r s k : ℕ) (entry : TQ n cap tcap × TM n cap) (D : Σ w, BitString w)
    (v : BitString n) :
    (Origin.block s k, v) ∈ (inferEntry bf hbar L r entry D).1 ↔
      r = s ∧
        ((k = 0 ∧ v = mmP bf hbar entry) ∨
          ∃ u < numBlocks n entry.1.2.2.1.val,
            k = u + 1 ∧ v = ssP bf hbar L entry ^^^ bin n (u + 1)) := by
  rw [inferEntry_eq_semanticP]
  simp only [List.mem_cons, Prod.mk.injEq, Origin.block.injEq, List.mem_map,
    List.mem_range]
  aesop

theorem mem_inferEntry_snd_iffP (bf : Hash.BlockField F n) (hbar L : BitString n)
    (r s k : ℕ) (entry : TQ n cap tcap × TM n cap) (D : Σ w, BitString w)
    (v : BitString n) :
    (Origin.block s k, v) ∈ (inferEntry bf hbar L r entry D).2 ↔
      r = s ∧
        ((k = 0 ∧ v = uuP bf hbar entry) ∨
          ∃ u : Fin (yBlocksP entry D).length,
            k = u.val + 1 ∧ v = (yBlocksP entry D).get u) := by
  rw [inferEntry_eq_semanticP]
  simp only [List.mem_cons, Prod.mk.injEq, Origin.block.injEq, List.mem_map]
  constructor
  · rintro (h | ⟨p, hp, hpair⟩)
    · exact ⟨h.1.1.symm, Or.inl ⟨h.1.2, h.2⟩⟩
    · have hget := List.mem_zipIdx' hp
      exact ⟨hpair.1.1, Or.inr ⟨⟨p.2, hget.1⟩, hpair.1.2.symm,
        hpair.2.symm.trans (by simpa [List.get_eq_getElem] using hget.2)⟩⟩
  · rintro ⟨rfl, (⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩)⟩
    · exact Or.inl ⟨⟨rfl, rfl⟩, rfl⟩
    · refine Or.inr ⟨((yBlocksP entry D).get u, u.val), ?_, ?_⟩
      · exact (List.mem_zipIdx_iff_getElem?).2
          (by rw [List.getElem?_eq_getElem u.isLt, List.get_eq_getElem])
      · exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem mem_side_blockP (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (s k : ℕ) (v : BitString n)
    (h : (Origin.block s k, v) ∈ sideOf bf o d) :
    ∃ p ∈ ((transcriptEntries o.1).zip o.2.2).zipIdx,
      (Origin.block s k, v) ∈
        (if d then
          (inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2).1
        else (inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2).2) := by
  cases d
  · change (Origin.block s k, v) ∈
      (Origin.seed 0, o.2.1.1) :: (Origin.seed 1, o.2.1.2) ::
        (((((transcriptEntries o.1).zip o.2.2).zipIdx.map
          (fun p => inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2)).map
            Prod.snd).flatten) at h
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    obtain ⟨l, hl, hmem⟩ := List.mem_flatten.mp h
    obtain ⟨a, ha, hal⟩ := List.mem_map.mp hl
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
    subst a
    subst l
    exact ⟨p, hp, hmem⟩
  · change (Origin.block s k, v) ∈
      (Origin.seed 0, bin n 0) :: (Origin.seed 1, bin n 1) ::
        (((((transcriptEntries o.1).zip o.2.2).zipIdx.map
          (fun p => inferEntry bf o.2.1.1 o.2.1.2 p.2 p.1.1 p.1.2)).map
            Prod.fst).flatten) at h
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    obtain ⟨l, hl, hmem⟩ := List.mem_flatten.mp h
    obtain ⟨a, ha, hal⟩ := List.mem_map.mp hl
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
    subst a
    subst l
    exact ⟨p, hp, hmem⟩

def blockValueP (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (s k : ℕ) : BitString n :=
  match (((transcriptEntries o.1).zip o.2.2)[s]?) with
  | none => 0
  | some (entry, D) =>
      if d then
        if k = 0 then mmP bf o.2.1.1 entry
        else ssP bf o.2.1.1 o.2.1.2 entry ^^^ bin n k
      else
        if k = 0 then uuP bf o.2.1.1 entry
        else (yBlocksP entry D).getD (k - 1) 0

theorem mem_side_block_semanticP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n) (s k : ℕ) (v : BitString n)
    (h : (Origin.block s k, v) ∈ sideOf bf o d) :
    ∃ entryD : (TQ n cap tcap × TM n cap) × (Σ w, BitString w),
      ((transcriptEntries o.1).zip o.2.2)[s]? = some entryD ∧
        k < entryCharge entryD.1 ∧ v = blockValueP bf o d s k := by
  obtain ⟨p, hp, hmem⟩ := mem_side_blockP bf o d s k v h
  rcases p with ⟨entryD, r⟩
  have hpget := List.mem_zipIdx_iff_getElem?.mp hp
  cases d
  · obtain ⟨hrs, hshape⟩ :=
      (mem_inferEntry_snd_iffP bf o.2.1.1 o.2.1.2 r s k entryD.1 entryD.2 v).mp hmem
    subst r
    refine ⟨entryD, hpget, ?_, ?_⟩
    · rcases hshape with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · rw [entryCharge, numBlocks_Msg_len entryD.1.1.2.2 hn]
        omega
      · rw [entryCharge, numBlocks_Msg_len entryD.1.1.2.2 hn]
        have hu : u.val < numBlocks n entryD.1.1.2.2.1.val := by
          simpa [yBlocksP] using u.isLt
        omega
    · rcases hshape with ⟨rfl, hv⟩ | ⟨u, rfl, hv⟩
      · simpa [blockValueP, hpget] using hv
      · have hgetD : (yBlocksP entryD.1 entryD.2).getD u.val 0 =
            (yBlocksP entryD.1 entryD.2).get u :=
          List.getD_eq_getElem _ _ u.isLt
        simpa [blockValueP, hpget, hgetD] using hv
  · obtain ⟨hrs, hshape⟩ :=
      (mem_inferEntry_fst_iffP bf o.2.1.1 o.2.1.2 r s k entryD.1 entryD.2 v).mp hmem
    subst r
    refine ⟨entryD, hpget, ?_, ?_⟩
    · rcases hshape with ⟨rfl, -⟩ | ⟨u, hu, rfl, -⟩
      · rw [entryCharge, numBlocks_Msg_len entryD.1.1.2.2 hn]
        omega
      · rw [entryCharge, numBlocks_Msg_len entryD.1.1.2.2 hn]
        omega
    · rcases hshape with ⟨rfl, hv⟩ | ⟨u, -, rfl, hv⟩
      · simpa [blockValueP, hpget] using hv
      · simpa [blockValueP, hpget] using hv

def originValueP (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) : Origin → BitString n
  | .seed k =>
      if d then bin n k else if k = 0 then o.2.1.1 else o.2.1.2
  | .block s k => blockValueP bf o d s k

theorem mem_side_valueP (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (hn : 0 < n) (a : Origin) (v : BitString n)
    (h : (a, v) ∈ sideOf bf o d) : v = originValueP bf o d a := by
  cases a with
  | block s k =>
      exact (mem_side_block_semanticP bf o d hn s k v h).choose_spec.2.2
  | seed k =>
      cases d <;>
        simp only [sideOf, Bool.false_eq_true, if_false, if_true, inferred,
          List.mem_cons] at h
      · rcases h with h | h | h
        · have hk := congrArg (fun p => p.1) h
          cases hk
          simpa [originValueP] using congrArg (fun p => p.2) h
        · have hk := congrArg (fun p => p.1) h
          cases hk
          simpa [originValueP] using congrArg (fun p => p.2) h
        · obtain ⟨l, hl, hm⟩ := List.mem_flatten.mp h
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
          rw [inferEntry_eq_semanticP] at hm
          simp at hm
      · rcases h with h | h | h
        · have hk := congrArg (fun p => p.1) h
          cases hk
          simpa [originValueP] using congrArg (fun p => p.2) h
        · have hk := congrArg (fun p => p.1) h
          cases hk
          simpa [originValueP] using congrArg (fun p => p.2) h
        · obtain ⟨l, hl, hm⟩ := List.mem_flatten.mp h
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
          rw [inferEntry_eq_semanticP] at hm
          simp at hm

namespace Origin

def BeforeP : Origin → Origin → Prop
  | .seed a, .seed b => a < b
  | .seed _, .block _ _ => True
  | .block _ _, .seed _ => False
  | .block r k, .block s l => r < s ∨ (r = s ∧ k < l)

end Origin

def queryLayoutFromP
    (start : ℕ)
    (entries : List ((TQ n cap tcap × TM n cap) × (Σ w, BitString w))) : List Origin :=
  match entries with
  | [] => []
  | entry :: entries =>
      queryLabels entry.1 start ++ queryLayoutFromP (start + 1) entries

theorem queryLayoutFrom_eqP
    (start : ℕ)
    (entries : List ((TQ n cap tcap × TM n cap) × (Σ w, BitString w))) :
    queryLayoutFromP start entries =
      ((entries.zipIdx start).map (fun p => queryLabels p.1.1 p.2)).flatten := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry entries ih =>
      simp only [queryLayoutFromP, List.zipIdx_cons, List.map_cons,
        List.flatten_cons]
      rw [ih]

theorem mem_queryLayoutFrom_indexP
    {start : ℕ}
    {entries : List ((TQ n cap tcap × TM n cap) × (Σ w, BitString w))}
    {s k : ℕ} (h : Origin.block s k ∈ queryLayoutFromP start entries) :
    start ≤ s ∧ s < start + entries.length := by
  induction entries generalizing start with
  | nil => simp [queryLayoutFromP] at h
  | cons entry entries ih =>
      rw [queryLayoutFromP, List.mem_append] at h
      rcases h with h | h
      · simp only [queryLabels, List.mem_map, List.mem_range] at h
        obtain ⟨u, -, hu⟩ := h
        cases hu
        simp
      · have hs := ih h
        simp only [List.length_cons]
        omega

theorem pairwise_queryLabels_beforeP
    (entry : TQ n cap tcap × TM n cap) (s : ℕ) :
    (queryLabels entry s).Pairwise Origin.BeforeP := by
  rw [queryLabels, List.pairwise_map]
  simpa [Origin.BeforeP] using
    (List.pairwise_lt_range : (List.range (entryCharge entry)).Pairwise (· < ·))

theorem seed_not_mem_queryLayoutFromP
    (start : ℕ)
    (entries : List ((TQ n cap tcap × TM n cap) × (Σ w, BitString w))) (a : ℕ) :
    Origin.seed a ∉ queryLayoutFromP start entries := by
  induction entries generalizing start with
  | nil => simp [queryLayoutFromP]
  | cons entry entries ih =>
      rw [queryLayoutFromP, List.mem_append]
      push_neg
      exact ⟨by simp [queryLabels], ih (start + 1)⟩

theorem pairwise_queryLayoutFrom_beforeP
    (start : ℕ)
    (entries : List ((TQ n cap tcap × TM n cap) × (Σ w, BitString w))) :
    (queryLayoutFromP start entries).Pairwise Origin.BeforeP := by
  induction entries generalizing start with
  | nil => simp [queryLayoutFromP]
  | cons entry entries ih =>
      rw [queryLayoutFromP, List.pairwise_append]
      refine ⟨pairwise_queryLabels_beforeP entry.1 start, ih (start + 1), ?_⟩
      intro a ha b hb
      simp only [queryLabels, List.mem_map, List.mem_range] at ha
      obtain ⟨k, -, rfl⟩ := ha
      rcases b with j | ⟨s, l⟩
      · exact absurd hb (seed_not_mem_queryLayoutFromP (start + 1) entries j)
      · have hs := (mem_queryLayoutFrom_indexP hb).1
        exact Or.inl (by omega)

theorem labelsOf_pairwise_beforeP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n) :
    (labelsOf bf o d).Pairwise Origin.BeforeP := by
  rw [labelsOf_eq bf o d hn, ← queryLayoutFrom_eqP]
  rw [List.pairwise_cons, List.pairwise_cons]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp [Origin.BeforeP]
    rcases a with k | ⟨s, k⟩
    · exact absurd ha (seed_not_mem_queryLayoutFromP 0 _ k)
    · trivial
  · intro a ha
    rcases a with k | ⟨s, k⟩
    · exact absurd ha (seed_not_mem_queryLayoutFromP 0 _ k)
    · trivial
  · exact pairwise_queryLayoutFrom_beforeP 0 _

theorem RealizedPair.beforeP
    {bf : Hash.BlockField F n} {o : AugObs n cap tcap}
    {d : Bool} {i j : ℕ} (p : RealizedPair bf o d i j) (hn : 0 < n) :
    Origin.BeforeP p.left.1 p.right.1 := by
  have his : i < (sideOf bf o d).length :=
    (List.getElem?_eq_some_iff.mp p.left_eq).choose
  have hjs : j < (sideOf bf o d).length :=
    (List.getElem?_eq_some_iff.mp p.right_eq).choose
  have hi : i < (labelsOf bf o d).length := by
    simpa [labelsOf] using his
  have hj : j < (labelsOf bf o d).length := by
    simpa [labelsOf] using hjs
  have hpair := (List.pairwise_iff_getElem.mp
    (labelsOf_pairwise_beforeP bf o d hn)) i j hi hj p.ordered
  have hleft : (sideOf bf o d)[i] = p.left := by
    have h := p.left_eq
    rw [List.getElem?_eq_getElem his] at h
    exact Option.some.inj h
  have hright : (sideOf bf o d)[j] = p.right := by
    have h := p.right_eq
    rw [List.getElem?_eq_getElem hjs] at h
    exact Option.some.inj h
  have hlabelleft : (labelsOf bf o d)[i] = ((sideOf bf o d)[i]).1 := by
    simp [labelsOf]
  have hlabelright : (labelsOf bf o d)[j] = ((sideOf bf o d)[j]).1 := by
    simp [labelsOf]
  rw [hlabelleft, hlabelright, hleft, hright] at hpair
  exact hpair

theorem RealizedPair.valuesP
    {bf : Hash.BlockField F n} {o : AugObs n cap tcap}
    {d : Bool} {i j : ℕ} (p : RealizedPair bf o d i j) (hn : 0 < n) :
    p.left.2 = originValueP bf o d p.left.1 ∧
      p.right.2 = originValueP bf o d p.right.1 := by
  have hleft : p.left ∈ sideOf bf o d :=
    List.mem_iff_getElem?.2 ⟨i, p.left_eq⟩
  have hright : p.right ∈ sideOf bf o d :=
    List.mem_iff_getElem?.2 ⟨j, p.right_eq⟩
  exact ⟨mem_side_valueP bf o d hn p.left.1 p.left.2 hleft,
    mem_side_valueP bf o d hn p.right.1 p.right.2 hright⟩

theorem RealizedPair.collides_iffP
    {bf : Hash.BlockField F n} {o : AugObs n cap tcap}
    {d : Bool} {i j : ℕ} (p : RealizedPair bf o d i j) (hn : 0 < n) :
    p.Collides ↔
      originValueP bf o d p.left.1 = originValueP bf o d p.right.1 := by
  rw [RealizedPair.Collides]
  obtain ⟨hl, hr⟩ := p.valuesP hn
  rw [hl, hr]

/-! A block-coordinate view of all ideal coins.  One response and its
leftover are jointly exactly the blocks charged to that query. -/

def catEquivP (a b : ℕ) : BitString a × BitString b ≃ BitString (a + b) where
  toFun p := p.1 ∥ p.2
  invFun x := (x[0; a], x[a; b])
  left_inv p := by
    apply Prod.ext
    · exact Bits.Facts.sub_cat_left p.1 p.2
    · exact Bits.Facts.sub_cat_right p.1 p.2
  right_inv x := Bits.Facts.cat_sub_sub x

def strCastEquivP {a b : ℕ} (h : a = b) : BitString a ≃ BitString b where
  toFun := BitVec.cast h
  invFun := BitVec.cast h.symm
  left_inv x := by subst b; rfl
  right_inv x := by subst b; rfl

private theorem numBlocks_mulP {n m : ℕ} (hn : 0 < n) :
    numBlocks n (n * m) = m := by
  rw [numBlocks, show n * m + n - 1 = n * m + (n - 1) by omega,
    Nat.mul_add_div hn, Nat.div_eq_of_lt (by omega)]
  omega

def chunkFunP (n m : ℕ) (x : BitString (n * m)) : Fin m → BitString n :=
  fun i => x[n * i.val; n]

theorem chunkFunP_injective {n m : ℕ} (hn : 0 < n) :
    Function.Injective (chunkFunP n m) := by
  intro x y hxy
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hi : p / n < m := by
    exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hp)
  have hb := congrFun hxy ⟨p / n, hi⟩
  have hbit := congrArg (fun z : BitString n => z.getLsbD (p % n)) hb
  simp only [chunkFunP, substring, BitVec.getLsbD_extractLsb'] at hbit
  have hmod : p % n < n := Nat.mod_lt p hn
  have hidx : n * (p / n) + p % n = p := by
    simpa [Nat.add_comm] using Nat.mod_add_div p n
  simpa [hmod, hp, hidx] using hbit

noncomputable def chunkEquivP {n m : ℕ} (hn : 0 < n) :
    BitString (n * m) ≃ (Fin m → BitString n) :=
  Equiv.ofBijective (chunkFunP n m)
    ((Fintype.bijective_iff_injective_and_card (chunkFunP n m)).2
      ⟨chunkFunP_injective hn, by
        rw [Fintype.card_fun, Fintype.card_fin, Bits.Facts.card_Str,
          Bits.Facts.card_Str, pow_mul]⟩)

@[simp] theorem chunkEquivP_apply {n m : ℕ} (hn : 0 < n)
    (x : BitString (n * m)) : chunkEquivP hn x = chunkFunP n m x := rfl

def queryChargeP (z : TQ n cap tcap) : ℕ :=
  1 + numBlocks n z.2.2.1.val

theorem queryCoinWidthP (hn : 0 < n) (z : TQ n cap tcap) :
    (n + z.2.2.1.val) +
        (padLen n z.2.2.1.val - z.2.2.1.val) =
      n * queryChargeP z := by
  have hj := le_padLen hn z.2.2.1.val
  rw [queryChargeP, Nat.mul_add, Nat.mul_one,
    show (n + z.2.2.1.val) +
      (padLen n z.2.2.1.val - z.2.2.1.val) =
        n + (z.2.2.1.val +
          (padLen n z.2.2.1.val - z.2.2.1.val)) by omega,
    Nat.add_sub_of_le hj, padLen_eq_mul]

noncomputable def queryCoinsEquivP (hn : 0 < n) (z : TQ n cap tcap) :
    BitString (n + z.2.2.1.val) ×
        BitString (padLen n z.2.2.1.val - z.2.2.1.val) ≃
      (Fin (queryChargeP z) → BitString n) :=
  (catEquivP _ _).trans
    ((strCastEquivP (queryCoinWidthP hn z)).trans (chunkEquivP hn))

abbrev ResponseBlockIndexP (n cap tcap : ℕ) :=
  Σ z : TQ n cap tcap, Fin (queryChargeP z)

abbrev ResponseBlocksP (n cap tcap : ℕ) :=
  ResponseBlockIndexP n cap tcap → BitString n

noncomputable def rndKeyBlockEquivP (hn : 0 < n) :
    RndKey n cap tcap ≃ ResponseBlocksP n cap tcap × (BitString n × BitString n) where
  toFun k :=
    (fun p => queryCoinsEquivP hn p.1 (k.1 p.1, k.2.2 p.1) p.2, k.2.1)
  invFun p :=
    let joint := fun z => (queryCoinsEquivP hn z).symm (fun b => p.1 ⟨z, b⟩)
    (fun z => (joint z).1, (p.2, fun z => (joint z).2))
  left_inv k := by
    apply Prod.ext
    · funext z
      have h := (queryCoinsEquivP hn z).symm_apply_apply (k.1 z, k.2.2 z)
      exact congrArg Prod.fst h
    · apply Prod.ext
      · rfl
      · funext z
        have h := (queryCoinsEquivP hn z).symm_apply_apply (k.1 z, k.2.2 z)
        exact congrArg Prod.snd h
  right_inv p := by
    apply Prod.ext
    · funext idx
      exact congrFun ((queryCoinsEquivP hn idx.1).apply_symm_apply
        (fun b => p.1 ⟨idx.1, b⟩)) idx.2
    · rfl

abbrev CoinIndexP (n cap tcap : ℕ) := Bool ⊕ ResponseBlockIndexP n cap tcap
abbrev CoinBlocksP (n cap tcap : ℕ) := CoinIndexP n cap tcap → BitString n

def packCoinBlocksP :
    ResponseBlocksP n cap tcap × (BitString n × BitString n) ≃
      CoinBlocksP n cap tcap where
  toFun p
    | .inl false => p.2.1
    | .inl true => p.2.2
    | .inr idx => p.1 idx
  invFun w := (fun idx => w (.inr idx), (w (.inl false), w (.inl true)))
  left_inv p := rfl
  right_inv w := by
    funext idx
    rcases idx with (b | idx)
    · cases b <;> rfl
    · rfl

noncomputable def rndKeyCoinEquivP (hn : 0 < n) :
    RndKey n cap tcap ≃ CoinBlocksP n cap tcap :=
  (rndKeyBlockEquivP hn).trans packCoinBlocksP

def SelflocAnchorP {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A]
    (loc : (ι → A) → ι) (a₀ : A) :=
  { ω : ι → A // ω (loc ω) = a₀ }

def selflocEquivP {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A]
    (loc : (ι → A) → ι) (a₀ : A)
    (hloc : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω) :
    (ι → A) ≃ SelflocAnchorP loc a₀ × A where
  toFun ω :=
    (⟨Function.update ω (loc ω) a₀, by
      rw [hloc, Function.update_self]⟩, ω (loc ω))
  invFun p := Function.update p.1.1 (loc p.1.1) p.2
  left_inv ω := by
    change Function.update (Function.update ω (loc ω) a₀)
      (loc (Function.update ω (loc ω) a₀)) (ω (loc ω)) = ω
    rw [hloc]
    funext i
    by_cases hi : i = loc ω
    · subst i; simp
    · simp [Function.update_of_ne hi]
  right_inv p := by
    rcases p with ⟨⟨ω, hω⟩, v⟩
    apply Prod.ext
    · apply Subtype.ext
      change Function.update (Function.update ω (loc ω) v)
        (loc (Function.update ω (loc ω) v)) a₀ = ω
      rw [hloc]
      funext i
      by_cases hi : i = loc ω
      · subst i; simp [hω]
      · simp [Function.update_of_ne hi]
    · change (Function.update ω (loc ω) v)
        (loc (Function.update ω (loc ω) v)) = v
      rw [hloc, Function.update_self]

/-- A variable-size version of the self-locating pin.  The located fiber may
have `B ω` solutions; because both the location and `B` are invariant along that
fiber, its global probability is the expected fiber size divided by `|A|`. -/
theorem uniform_pi_selfloc_fiber_expect_leP
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : (ι → A) → Prop) [DecidablePred P]
    (loc : (ι → A) → ι) (a₀ : A) (B : (ι → A) → ℕ)
    (hloc : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω)
    (hB : ∀ ω v, B (Function.update ω (loc ω) v) = B ω)
    (hfiber : ∀ ω, (Finset.univ.filter
      (fun v : A => P (Function.update ω (loc ω) v))).card ≤ B ω) :
    (Dist.uniform (ι → A)).mass P ≤
      Dist.expect (Dist.uniform (ι → A)) (fun ω => (B ω : ℝ)) /
        Fintype.card A := by
  classical
  let φ := selflocEquivP loc a₀ hloc
  let S := SelflocAnchorP loc a₀
  letI : Fintype S := by
    dsimp only [S, SelflocAnchorP]
    infer_instance
  letI : DecidableEq S := Classical.decEq S
  let Q : S × A → Prop := fun p => P (φ.symm p)
  let bnd : S → NNReal := fun s => (B s.1 : NNReal) / Fintype.card A
  have hnonemptyS : Nonempty S := by
    let ω : ι → A := Classical.arbitrary (ι → A)
    exact ⟨⟨Function.update ω (loc ω) a₀, by
      rw [hloc, Function.update_self]⟩⟩
  letI : Nonempty S := hnonemptyS
  have hmass : (Dist.uniform (S × A)).mass Q ≤
      expectW (Dist.uniform (S × A)) (fun p => bnd p.1) := by
    refine mass_le_of_fiber_snd_cond_wexp
      (Dist.uniform (S × A))
      (fun _ : S => ((Fintype.card S : ℝ))⁻¹)
      (Dist.uniform A) ?_ (fun _ => by positivity)
      Dist.weight_uniform (P := Q) (V := fun _ => True) bnd
      (fun _ _ _ => trivial) ?_
    · intro s v
      rw [Dist.uniform_apply, Dist.uniform_apply, Fintype.card_prod,
        Nat.cast_mul, one_div, one_div, mul_inv, mul_comm]
    · intro s _ _
      rw [Dist.uniform_mass_eq_card_filter]
      change (((Finset.univ.filter (fun v : A =>
        P (Function.update s.1 (loc s.1) v))).card : ℝ) /
          Fintype.card A) ≤ _
      have hs := hfiber s.1
      simpa [bnd, NNReal.coe_div] using
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr hs)
          (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _))
  rw [uniform_mass_equiv φ P]
  refine hmass.trans_eq ?_
  simp only [expectW, Dist.expect_eq_sum, Dist.uniform_apply, bnd]
  rw [show Fintype.card (S × A) = Fintype.card (ι → A) by
    exact Fintype.card_congr φ.symm]
  rw [Fintype.sum_prod_type]
  have hBsymm : ∀ (s : S) (v : A), B (φ.symm (s, v)) = B s.1 := by
    intro s v
    exact hB s.1 v
  have hsumtransport :
      (∑ ω : ι → A,
        (1 / (Fintype.card (ι → A) : ℝ)) * (B ω : ℝ)) =
        ∑ p : S × A,
          (1 / (Fintype.card (ι → A) : ℝ)) * (B (φ.symm p) : ℝ) := by
    exact Fintype.sum_equiv φ
      (fun ω => (1 / (Fintype.card (ι → A) : ℝ)) * (B ω : ℝ))
      (fun p => (1 / (Fintype.card (ι → A) : ℝ)) * (B (φ.symm p) : ℝ))
      (fun _ => by simp)
  rw [hsumtransport]
  rw [Fintype.sum_prod_type]
  simp_rw [hBsymm, NNReal.coe_div, NNReal.coe_natCast]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

noncomputable def coinKeyP (hn : 0 < n) (w : CoinBlocksP n cap tcap) :
    RndKey n cap tcap :=
  (rndKeyCoinEquivP hn).symm w

noncomputable def coinObsP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) : AugObs n cap tcap :=
  augRnd n cap tcap q σ e m (coinKeyP hn w)

noncomputable def coinUpdateP (w : CoinBlocksP n cap tcap)
    (idx : CoinIndexP n cap tcap) (v : BitString n) : CoinBlocksP n cap tcap := by
  classical
  exact Function.update w idx v

theorem expect_fTransformP {A B : Type*} (X : Dist A) (f : A → B)
    (g : B → ℝ) :
    Dist.expect (Dist.fTransform f X) g = Dist.expect X (g ∘ f) := by
  classical
  unfold Dist.expect Dist.fTransform
  rw [Finsupp.sum_sum_index
    (fun _ => zero_mul (g _))
    (fun _ m₁ m₂ => add_mul m₁ m₂ (g _))]
  apply Finsupp.sum_congr
  intro a ha
  simp [Function.comp_def]

noncomputable def coinBadValuesP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j : ℕ)
    (loc : CoinBlocksP n cap tcap → CoinIndexP n cap tcap)
    (w : CoinBlocksP n cap tcap) : Finset (BitString n) := by
  classical
  exact Finset.univ.filter (fun v =>
    pairCollision bf
      (coinObsP hn q σ e m (coinUpdateP w (loc w) v)) d i j)

theorem collAt_le_expected_of_coin_fiberP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j : ℕ)
    (loc : CoinBlocksP n cap tcap → CoinIndexP n cap tcap)
    (hloc : ∀ w v, loc (coinUpdateP w (loc w) v) = loc w)
    (hcost : ∀ w v,
      costAt bf (coinObsP hn q σ e m (coinUpdateP w (loc w) v)) d i j =
        costAt bf (coinObsP hn q σ e m w) d i j)
    (hfiber : ∀ w, (coinBadValuesP bf hn q σ e m d i j loc w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j) :
    collAt bf (augLawRnd n cap tcap q σ e m).val d i j ≤
      (∑ o ∈ (augLawRnd n cap tcap q σ e m).val.support,
        (augLawRnd n cap tcap q σ e m).val o *
          (costAt bf o d i j : ℝ)) / 2 ^ n := by
  classical
  let law := (augLawRnd n cap tcap q σ e m).val
  let P : CoinBlocksP n cap tcap → Prop := fun w =>
    pairCollision bf (coinObsP hn q σ e m w) d i j
  let B : CoinBlocksP n cap tcap → ℕ := fun w =>
    costAt bf (coinObsP hn q σ e m w) d i j
  have hloc' : ∀ w v, loc (Function.update w (loc w) v) = loc w := by
    simpa only [coinUpdateP] using hloc
  have hcost' : ∀ w v,
      B (Function.update w (loc w) v) = B w := by
    simpa only [B, coinUpdateP] using hcost
  have hfiber' : ∀ w, (Finset.univ.filter (fun v : BitString n =>
      P (Function.update w (loc w) v))).card ≤ B w := by
    simpa only [P, B, coinBadValuesP, coinUpdateP] using hfiber
  have hmain := uniform_pi_selfloc_fiber_expect_leP P loc (0 : BitString n) B
    hloc' hcost' hfiber'
  have hlaw : law = Dist.fTransform (augRnd n cap tcap q σ e m)
      (Dist.uniform (RndKey n cap tcap)) := rfl
  have hmass : collAt bf law d i j =
      (Dist.uniform (CoinBlocksP n cap tcap)).mass P := by
    rw [collAt, hlaw, Dist.mass_fTransform,
      uniform_mass_equiv (rndKeyCoinEquivP hn)]
    rfl
  have hexpect :
      ∑ o ∈ law.support, law o * (costAt bf o d i j : ℝ) =
        Dist.expect (Dist.uniform (CoinBlocksP n cap tcap))
          (fun w => (B w : ℝ)) := by
    rw [← Dist.expect_eq_sum_of_support_subset law
      (fun o => (costAt bf o d i j : ℝ)) (Finset.Subset.rfl)]
    rw [hlaw, expect_fTransformP, Dist.expect_eq_sum]
    simp only [Function.comp_apply]
    rw [← Equiv.sum_comp (rndKeyCoinEquivP hn).symm
      (fun k : RndKey n cap tcap =>
        Dist.uniform (RndKey n cap tcap) k *
          (costAt bf (augRnd n cap tcap q σ e m k) d i j : ℝ))]
    simp only [Dist.uniform_apply]
    rw [Fintype.card_congr (rndKeyCoinEquivP hn)]
    rw [Dist.expect_eq_sum]
    simp only [Dist.uniform_apply]
    simp [B, coinObsP, coinKeyP, Function.comp_def]
  rw [hmass, hexpect]
  simpa [Bits.Facts.card_Str, Nat.cast_pow] using hmain

theorem answeredEntries_get_decomposeP {X Y : Type*}
    (t : List (X × Option Y)) (s : ℕ) (entry : X × Y)
    (h : (PFunDDS.answeredEntries t)[s]? = some entry) :
    ∃ pre post,
      t = pre ++ (entry.1, some entry.2) :: post ∧
        PFunDDS.answeredEntries pre =
          (PFunDDS.answeredEntries t).take s := by
  induction t generalizing s with
  | nil => simp [PFunDDS.answeredEntries] at h
  | cons a t ih =>
      rcases a with ⟨x, oy⟩
      cases oy with
      | none =>
          simp only [PFunDDS.answeredEntries, List.filterMap_cons,
            Option.map_none] at h ⊢
          obtain ⟨pre, post, ht, hp⟩ := ih s h
          refine ⟨(x, none) :: pre, post, ?_, ?_⟩
          · rw [ht]; rfl
          · simpa [PFunDDS.answeredEntries] using hp
      | some y =>
          cases s with
          | zero =>
              simp only [PFunDDS.answeredEntries, List.filterMap_cons,
                Option.map_some, List.getElem?_cons_zero, Option.some.injEq] at h
              subst entry
              exact ⟨[], t, rfl, by simp [PFunDDS.answeredEntries]⟩
          | succ s =>
              simp only [PFunDDS.answeredEntries, List.filterMap_cons,
                Option.map_some, List.getElem?_cons_succ] at h
              obtain ⟨pre, post, ht, hp⟩ := ih s h
              refine ⟨(x, some y) :: pre, post, ?_, ?_⟩
              · rw [ht]; rfl
              · simpa [PFunDDS.answeredEntries] using hp

theorem mem_raw_of_mem_answeredP {X Y : Type*}
    {t : List (X × Option Y)} {x : X} {y : Y}
    (h : (x, y) ∈ PFunDDS.answeredEntries t) : (x, some y) ∈ t := by
  simp only [PFunDDS.answeredEntries, List.mem_filterMap] at h
  obtain ⟨⟨a, oy⟩, hm, heq⟩ := h
  cases oy with
  | none => simp at heq
  | some b =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact hm

theorem answered_functionEvaluatorP
    {X Y : Type*} (P : List X → Prop) (hP : PrefixClosed P)
    (f : X → Y) (e : PFunDDS.DDE X Y) (m : ℕ) :
    ∀ entry ∈ PFunDDS.answeredEntries
        (PFunDDS.transcript
          (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m),
      f entry.1 = entry.2 := by
  intro entry hentry
  rcases entry with ⟨x, y⟩
  change f x = y
  let S := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)
  let t := PFunDDS.transcript S e m
  have hraw : (x, some y) ∈ t :=
    mem_raw_of_mem_answeredP (t := t) hentry
  obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp hraw
  have hs := (transcript_consistent S e m).2 i hi
  rw [hit] at hs
  rw [take_succ_get' t i hi, transcriptInputs_append,
    List.get_eq_getElem, hit] at hs
  have hout : PFunDDS.output (PFunDDS.fullyDefined S)
      (((t.take i)↓ₓ ++ [x])) (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) = some y := by
    apply Part.get_eq_of_mem
    rw [hs]
    exact Part.mem_some _
  rw [PFunDDS.output_fullyDefined] at hout
  simp only [List.dropLast_append, List.dropLast_singleton, List.append_nil,
    List.getLast_append, List.getLast_singleton] at hout
  split at hout
  · exact Option.some.inj (by simpa [S, PFunDDS.output_filterDom,
      PFunDDS.functionEvaluator_output] using hout)
  · simp at hout

theorem mem_answered_of_mem_rawP {X Y : Type*}
    {t : List (X × Option Y)} {x : X} {y : Y}
    (h : (x, some y) ∈ t) : (x, y) ∈ PFunDDS.answeredEntries t := by
  simp only [PFunDDS.answeredEntries, List.mem_filterMap]
  exact ⟨(x, some y), h, rfl⟩

theorem transcript_filter_functionEvaluator_eqP
    {X Y : Type*} (P : List X → Prop) (hP : PrefixClosed P)
    (f g : X → Y) (e : PFunDDS.DDE X Y) (m : ℕ)
    (hagree : ∀ entry ∈ PFunDDS.answeredEntries
        (PFunDDS.transcript
          (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m),
      g entry.1 = entry.2) :
    PFunDDS.transcript
        (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator g)) e m =
      PFunDDS.transcript
        (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m := by
  let Sf := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)
  let Sg := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator g)
  let t := PFunDDS.transcript Sf e m
  have hc := transcript_consistent Sf e m
  apply (transcript_eq_iff_of_consistent hc.1.1 hc.1.2 Sg).2
  intro i hi
  have hs := hc.2 i hi
  rw [take_succ_get' t i hi, transcriptInputs_append]
  rw [take_succ_get' t i hi, transcriptInputs_append] at hs
  let x := t[i].1
  let prev := (t.take i)↓ₓ
  change (PFunDDS.fullyDefined Sg).1 (prev ++ [x]) = Part.some t[i].2
  change (PFunDDS.fullyDefined Sf).1 (prev ++ [x]) = Part.some t[i].2 at hs
  have hdom : prev ++ [x] ∈ PFunDDS.dom (PFunDDS.fullyDefined Sg) := by
    rw [PFunDDS.dom_fullyDefined]
    simp
  rw [Part.eq_some_iff]
  refine ⟨hdom, ?_⟩
  change PFunDDS.output (PFunDDS.fullyDefined Sg) (prev ++ [x]) hdom = t[i].2
  have hdomF : prev ++ [x] ∈ PFunDDS.dom (PFunDDS.fullyDefined Sf) := by
    rw [PFunDDS.dom_fullyDefined]
    simp
  have houtF : PFunDDS.output (PFunDDS.fullyDefined Sf) (prev ++ [x])
      hdomF = t[i].2 := by
    apply Part.get_eq_of_mem
    rw [hs]
    exact Part.mem_some _
  rw [PFunDDS.output_fullyDefined] at houtF ⊢
  have hdrop : (prev ++ [x]).dropLast = prev := by simp
  have hlastG : (prev ++ [x]).getLast (by exact hdom) = x := by simp
  have hlastF : (prev ++ [x]).getLast (by exact hdomF) = x := by simp
  rw [hdrop, hlastG]
  rw [hdrop, hlastF] at houtF
  have hkeep : PFunDDS.keptPrefix Sf prev = PFunDDS.keptPrefix Sg prev := by
    rfl
  rw [← hkeep]
  dsimp only at houtF ⊢
  split
  · rename_i hcandG
    have hcandF : PFunDDS.keptPrefix Sf prev ++ [x] ∈ PFunDDS.dom Sf := hcandG
    rw [dif_pos hcandF] at houtF
    rw [PFunDDS.output_filterDom, PFunDDS.functionEvaluator_output]
    rcases hy : t[i].2 with _ | y
    · simp [hy] at houtF
    · have hmemraw : (x, some y) ∈ t := by
        have hm := List.get_mem t ⟨i, hi⟩
        have hv : t.get ⟨i, hi⟩ = (x, some y) := by
          rw [List.get_eq_getElem]
          exact Prod.ext rfl hy
        rwa [hv] at hm
      have hgy := hagree (x, y) (mem_answered_of_mem_rawP hmemraw)
      simpa [hy, x] using hgy
  · rename_i hcandG
    have hcandF : PFunDDS.keptPrefix Sf prev ++ [x] ∉ PFunDDS.dom Sf := hcandG
    rw [dif_neg hcandF] at houtF
    exact houtF

theorem transcript_answered_prefix_updateP
    {X Y : Type*} (P : List X → Prop) (hP : PrefixClosed P)
    (f g : X → Y) (e : PFunDDS.DDE X Y) (m s : ℕ)
    (z : X) (y : Y)
    (hsel : (PFunDDS.answeredEntries
      (PFunDDS.transcript
        (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m))[s]? =
        some (z, y))
    (hnodup : ((PFunDDS.answeredEntries
      (PFunDDS.transcript
        (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m)).map
          Prod.fst).Nodup)
    (hoff : ∀ x, x ≠ z → g x = f x) :
    ∃ pre : List (X × Option Y),
      PFunDDS.answeredEntries pre =
        (PFunDDS.answeredEntries
          (PFunDDS.transcript
            (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)) e m)).take s ∧
      pre ++ [(z, some (g z))] <+:
        PFunDDS.transcript
          (PFunDDS.filterDom P hP (PFunDDS.functionEvaluator g)) e m := by
  let Sf := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator f)
  let Sg := PFunDDS.filterDom P hP (PFunDDS.functionEvaluator g)
  let t := PFunDDS.transcript Sf e m
  have hsel' : (PFunDDS.answeredEntries t)[s]? = some (z, y) := by
    simpa [t, Sf] using hsel
  obtain ⟨pre, post, hdecomp, hanswered⟩ :=
    answeredEntries_get_decomposeP t s (z, y) hsel'
  have hqdecomp : (PFunDDS.answeredEntries t).map Prod.fst =
      (PFunDDS.answeredEntries pre).map Prod.fst ++
        z :: (PFunDDS.answeredEntries post).map Prod.fst := by
    rw [hdecomp]
    simp [PFunDDS.answeredEntries]
  have hnodup' : ((PFunDDS.answeredEntries t).map Prod.fst).Nodup := by
    simpa [t, Sf] using hnodup
  rw [hqdecomp] at hnodup'
  have hz : z ∉ (PFunDDS.answeredEntries pre).map Prod.fst := by
    intro hzpre
    have hzpost : z ∈ z :: (PFunDDS.answeredEntries post).map Prod.fst := by simp
    exact (List.disjoint_left.mp hnodup'.disjoint) hzpre hzpost
  have hprelen : pre.length ≤ t.length := by
    rw [hdecomp]
    simp
  obtain ⟨fuel, hfuel, hprefuel⟩ :=
    exists_transcript_eq_take Sf e hprelen
  have htake : t.take pre.length = pre := by
    rw [hdecomp, List.take_append_of_le_length le_rfl, List.take_length]
  rw [htake] at hprefuel
  have hpreG : PFunDDS.transcript Sg e fuel = pre := by
    have h := transcript_filter_functionEvaluator_eqP P hP f g e fuel ?_
    · change PFunDDS.transcript Sg e fuel = PFunDDS.transcript Sf e fuel at h
      exact h.trans hprefuel
    · intro entry hentry
      have hentry' : entry ∈ PFunDDS.answeredEntries pre := by
        rwa [← hprefuel]
      have hne : entry.1 ≠ z := by
        intro heq
        apply hz
        exact List.mem_map.mpr ⟨entry, hentry', heq⟩
      exact (hoff entry.1 hne).trans
        (answered_functionEvaluatorP P hP f e fuel entry hentry)
  have hfuel_lt : fuel < m := by
    by_contra hnot
    have heq : fuel = m := by omega
    subst fuel
    have hlen := congrArg List.length hprefuel
    change t.length = pre.length at hlen
    rw [hdecomp] at hlen
    simp at hlen
  have hrawlt : pre.length < t.length := by
    rw [hdecomp]
    simp
  have hget : t[pre.length] = (z, some y) := by
    have hget? : t[pre.length]? = some (z, some y) := by
      rw [hdecomp]
      simp
    rw [List.getElem?_eq_getElem hrawlt] at hget?
    exact Option.some.inj hget?
  have htakeSucc : t.take (pre.length + 1) = pre ++ [(z, some y)] := by
    rw [hdecomp]
    simp [List.take_append]
  have hc := transcript_consistent Sf e m
  have henv : e (PFunDDS.transcriptOutputs pre) = some z := by
    have h := hc.1.1 pre.length hrawlt
    change e (PFunDDS.transcriptOutputs (t.take pre.length)) =
      some t[pre.length].1 at h
    rw [htake, hget] at h
    simpa using h
  have hsys : (PFunDDS.fullyDefined Sf).1
      (PFunDDS.transcriptInputs pre ++ [z]) = Part.some (some y) := by
    have h := hc.2 pre.length hrawlt
    change (PFunDDS.fullyDefined Sf).1
      (PFunDDS.transcriptInputs (t.take (pre.length + 1))) =
        Part.some t[pre.length].2 at h
    rw [htakeSucc, hget] at h
    simpa using h
  have hdomF : PFunDDS.transcriptInputs pre ++ [z] ∈
      PFunDDS.dom (PFunDDS.fullyDefined Sf) := by
    rw [PFunDDS.dom_fullyDefined]
    simp
  have houtF : PFunDDS.output (PFunDDS.fullyDefined Sf)
      (PFunDDS.transcriptInputs pre ++ [z]) hdomF = some y := by
    apply Part.get_eq_of_mem
    rw [hsys]
    exact Part.mem_some _
  rw [PFunDDS.output_fullyDefined] at houtF
  have hdropF : (PFunDDS.transcriptInputs pre ++ [z]).dropLast =
      PFunDDS.transcriptInputs pre := by simp
  have hlastF : (PFunDDS.transcriptInputs pre ++ [z]).getLast hdomF = z := by simp
  rw [hdropF, hlastF] at houtF
  have hnext : PFunDDS.keptPrefix Sf (PFunDDS.transcriptInputs pre) ++ [z]
      ∈ PFunDDS.dom Sf := by
    dsimp only at houtF
    split at houtF
    · assumption
    · simp at houtF
  have hdomG : PFunDDS.transcriptInputs pre ++ [z] ∈
      PFunDDS.dom (PFunDDS.fullyDefined Sg) := by
    rw [PFunDDS.dom_fullyDefined]
    simp
  have houtG : PFunDDS.output (PFunDDS.fullyDefined Sg)
      (PFunDDS.transcriptInputs pre ++ [z]) hdomG = some (g z) := by
    rw [PFunDDS.output_fullyDefined]
    have hdropG : (PFunDDS.transcriptInputs pre ++ [z]).dropLast =
        PFunDDS.transcriptInputs pre := by simp
    have hlastG : (PFunDDS.transcriptInputs pre ++ [z]).getLast hdomG = z := by simp
    rw [hdropG, hlastG]
    have hkeep : PFunDDS.keptPrefix Sg (PFunDDS.transcriptInputs pre) =
        PFunDDS.keptPrefix Sf (PFunDDS.transcriptInputs pre) := rfl
    have hnextG : PFunDDS.keptPrefix Sg (PFunDDS.transcriptInputs pre) ++ [z]
        ∈ PFunDDS.dom Sg := by
      rw [hkeep]
      rw [PFunDDS.mem_dom_filterDom] at hnext ⊢
      exact ⟨by rw [PFunDDS.dom_functionEvaluator]; simp, hnext.2⟩
    rw [dif_pos hnextG, PFunDDS.output_filterDom,
      PFunDDS.functionEvaluator_output]
  have henvG : e (PFunDDS.transcriptOutputs
      (PFunDDS.transcript Sg e fuel)) = some z := by
    rw [hpreG]
    exact henv
  have hstep := transcript_succ_fire henvG
  rw [hpreG] at hstep
  have hstep' : PFunDDS.transcript Sg e (fuel + 1) =
      pre ++ [(z, some (g z))] := by
    simpa only [houtG] using hstep
  refine ⟨pre, by simpa [t, Sf] using hanswered, ?_⟩
  have hpref := transcript_prefix_of_le Sg e (Nat.succ_le_iff.mpr hfuel_lt)
  rw [hstep'] at hpref
  simpa [Sg] using hpref

theorem coinKey_table_offP (hn : 0 < n) (w : CoinBlocksP n cap tcap)
    (z : TQ n cap tcap) (b : Fin (queryChargeP z)) (v : BitString n)
    (x : TQ n cap tcap) (hx : x ≠ z) :
    (coinKeyP hn (coinUpdateP w (.inr ⟨z, b⟩) v)).1 x =
      (coinKeyP hn w).1 x := by
  classical
  unfold coinKeyP coinUpdateP rndKeyCoinEquivP packCoinBlocksP
    rndKeyBlockEquivP
  change ((queryCoinsEquivP hn x).symm
      (fun k => Function.update w (.inr ⟨z, b⟩) v (.inr ⟨x, k⟩))).1 =
    ((queryCoinsEquivP hn x).symm (fun k => w (.inr ⟨x, k⟩))).1
  congr 2
  funext k
  rw [Function.update_of_ne]
  intro heq
  have hxz : x = z := congrArg (fun p : CoinIndexP n cap tcap =>
    match p with
    | .inl _ => z
    | .inr idx => idx.1) heq
  exact hx hxz

theorem query_nodup_of_npListP
    (entries : List (TQ n cap tcap × TM n cap))
    (hnp : TweakablePRP.NPList entries) :
    (entries.map Prod.fst).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b hab
  let a' : Fin entries.length := ⟨a.val, by simpa using a.isLt⟩
  let b' : Fin entries.length := ⟨b.val, by simpa using b.isLt⟩
  have hab' : a' = b' := hnp.1 (by
    simpa [TweakablePRP.NPList, TweakablePRP.NP,
      TweakablePRP.transcriptOfPairs, List.Vector.get,
      List.get_eq_getElem, a', b'] using hab)
  exact Fin.ext (by simpa [a', b'] using congrArg Fin.val hab')

theorem coinObs_entries_update_prefixP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y)) :
    (transcriptEntries
      (coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)).1).take (s + 1) =
      (transcriptEntries (coinObsP hn q σ e m w).1).take s ++
        [(z, rndFun (coinKeyP hn
          (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z)] := by
  classical
  let k := coinKeyP hn w
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let k' := coinKeyP hn w'
  let f := rndFun k.1
  let g := rndFun k'.1
  let S := rndDDS n cap tcap q σ k.1
  let t := PFunDDS.transcript S e m
  have ht : t = (coinObsP hn q σ e m w).1 := rfl
  have hnp : TweakablePRP.NPList (transcriptEntries t) := by
    apply hE t
    exact (transcript_consistent S e m).1.1
  have hnodup : ((transcriptEntries t).map Prod.fst).Nodup :=
    query_nodup_of_npListP _ hnp
  have hoff : ∀ x, x ≠ z → g x = f x := by
    intro x hx
    unfold f g rndFun k k' w'
    rw [coinKey_table_offP hn w z b v x hx]
  have hsel' : (PFunDDS.answeredEntries
      (PFunDDS.transcript
        (PFunDDS.filterDom (Budget q σ) (budget_prefixClosed q σ)
          (PFunDDS.functionEvaluator f)) e m))[s]? = some (z, y) := by
    simpa [f, S, rndDDS, t, ht] using hsel
  obtain ⟨pre, hpreAns, hpref⟩ := transcript_answered_prefix_updateP
    (Budget q σ) (budget_prefixClosed q σ) f g e m s z y hsel'
    (by simpa [f, S, rndDDS, t] using hnodup) hoff
  rcases hpref with ⟨rest, hrest⟩
  have hslt : s < (transcriptEntries t).length :=
    (List.getElem?_eq_some_iff.mp (by simpa [t, ht] using hsel)).choose
  have htakeLen : ((transcriptEntries t).take s ++ [(z, g z)]).length = s + 1 := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hslt)]
  have hpreAns' : PFunDDS.answeredEntries pre =
      (transcriptEntries t).take s := by
    simpa [f, S, rndDDS, t] using hpreAns
  change (PFunDDS.answeredEntries
      (PFunDDS.transcript
        (PFunDDS.filterDom (Budget q σ) (budget_prefixClosed q σ)
          (PFunDDS.functionEvaluator g)) e m)).take (s + 1) = _
  rw [← hrest]
  rw [show PFunDDS.answeredEntries (pre ++ [(z, some (g z))] ++ rest) =
      PFunDDS.answeredEntries pre ++ [(z, g z)] ++
        PFunDDS.answeredEntries rest by simp [PFunDDS.answeredEntries]]
  rw [hpreAns']
  rw [List.take_append_of_le_length
    (l₁ := (transcriptEntries t).take s ++ [(z, g z)])
    (l₂ := PFunDDS.answeredEntries rest)
    (i := s + 1) (by simpa using Nat.le_of_lt hslt)]
  simpa [g, f, k', w', t, ht]

@[simp] theorem coinKey_hbarP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) :
    (coinKeyP hn w).2.1.1 = w (.inl false) := by
  rfl

@[simp] theorem coinKey_LP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) :
    (coinKeyP hn w).2.1.2 = w (.inl true) := by
  rfl

theorem coinKey_query_blockP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) :
    queryCoinsEquivP hn z ((coinKeyP hn w).1 z, (coinKeyP hn w).2.2 z) b =
      w (.inr ⟨z, b⟩) := by
  exact congrFun ((queryCoinsEquivP hn z).apply_symm_apply
    (fun b => w (.inr ⟨z, b⟩))) b

theorem coinKey_response_headP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap) :
    ((coinKeyP hn w).1 z)[0; n] =
      w (.inr ⟨z, ⟨0, by simp [queryChargeP]⟩⟩) := by
  have h := coinKey_query_blockP hn w z ⟨0, by simp [queryChargeP]⟩
  rw [queryCoinsEquivP, Equiv.trans_apply, Equiv.trans_apply,
    chunkEquivP_apply, strCastEquivP, catEquivP] at h
  change (((coinKeyP hn w).1 z ∥ (coinKeyP hn w).2.2 z)[0; n]) = _ at h
  rw [Bits.Facts.sub_cat_lo _ _ (by omega)] at h
  exact h

theorem sub_cat_drop_headP (x : BitString (n + j)) (D : BitString w) (k : ℕ) :
    (x ∥ D)[n + n * k; n] = (x[n; j] ∥ D)[n * k; n] := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  simp only [substring, BitVec.getLsbD_extractLsb', Bits.Facts.getLsbD_cat]
  by_cases h : n * k + p < j
  · simp [hp, h, show n + n * k + p < n + j by omega]
    congr 1
    omega
  · simp [hp, h, show ¬ n + n * k + p < n + j by omega]
    congr 1
    omega

theorem coinKey_response_tail_blockP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (k : Fin (numBlocks n z.2.2.1.val)) :
    (blocksTake n (numBlocks n z.2.2.1.val)
      (((coinKeyP hn w).1 z)[n; z.2.2.1.val] ∥
        (coinKeyP hn w).2.2 z)).get
          ⟨k.val, by simpa using k.isLt⟩ =
      w (.inr ⟨z, ⟨k.val + 1, by simp [queryChargeP]; omega⟩⟩) := by
  let b : Fin (queryChargeP z) :=
    ⟨k.val + 1, by simp [queryChargeP]; omega⟩
  have h := coinKey_query_blockP hn w z b
  rw [queryCoinsEquivP, Equiv.trans_apply, Equiv.trans_apply,
    chunkEquivP_apply, strCastEquivP, catEquivP] at h
  change (((coinKeyP hn w).1 z ∥ (coinKeyP hn w).2.2 z)[n * b.val; n]) = _ at h
  simp only [blocksTake, List.get_ofFn]
  change ((((coinKeyP hn w).1 z)[n; z.2.2.1.val] ∥
      (coinKeyP hn w).2.2 z)[n * k.val; n]) = _
  rw [← sub_cat_drop_headP
    ((coinKeyP hn w).1 z) ((coinKeyP hn w).2.2 z) k.val]
  simpa [b, Nat.mul_add, Nat.add_comm] using h

theorem mapIdx_zip_fstP {A B C : Type*}
    (l₁ : List A) (l₂ : List B) (f : ℕ → A → C)
    (hlen : l₁.length = l₂.length) :
    (l₁.zip l₂).mapIdx (fun i p => f i p.1) = l₁.mapIdx f := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx, List.zip, List.getElem?_zipWith]
  by_cases hi : i < l₁.length
  · have hi₂ : i < l₂.length := by simpa [hlen] using hi
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi₂]
    rfl
  · have hi₂ : ¬ i < l₂.length := by simpa [hlen] using hi
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hi),
      List.getElem?_eq_none (Nat.le_of_not_gt hi₂)]
    rfl

def transcriptLabelsP
    (entries : List (TQ n cap tcap × TM n cap)) : List Origin :=
  Origin.seed 0 :: Origin.seed 1 ::
    (entries.mapIdx (fun s entry => queryLabels entry s)).flatten

theorem labelsOf_eq_transcriptLabelsP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n)
    (hwf : WellFormedAugObs o) :
    labelsOf bf o d = transcriptLabelsP (transcriptEntries o.1) := by
  rw [labelsOf_eq bf o d hn]
  unfold transcriptLabelsP
  congr 2
  have hz :
      (((transcriptEntries o.1).zip o.2.2).zipIdx.map
        (fun p => queryLabels p.1.1 p.2)) =
      ((transcriptEntries o.1).zip o.2.2).mapIdx
        (fun s p => queryLabels p.1 s) := by
    rw [List.mapIdx_eq_zipIdx_map]
  rw [hz]
  apply congrArg List.flatten
  have hlen := congrArg List.length hwf
  exact mapIdx_zip_fstP (transcriptEntries o.1) o.2.2
    (fun s entry => queryLabels entry s)
    (by simpa [WellFormedAugObs] using hlen.symm)

def queryLayoutEntriesFromP (start : ℕ)
    (entries : List (TQ n cap tcap × TM n cap)) : List Origin :=
  match entries with
  | [] => []
  | entry :: entries =>
      queryLabels entry start ++ queryLayoutEntriesFromP (start + 1) entries

theorem queryLayoutEntriesFrom_eq_mapIdxP (start : ℕ)
    (entries : List (TQ n cap tcap × TM n cap)) :
    queryLayoutEntriesFromP start entries =
      (entries.mapIdx (fun i entry => queryLabels entry (start + i))).flatten := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry entries ih =>
      rw [queryLayoutEntriesFromP, List.mapIdx_cons, List.flatten_cons,
        ih (start + 1)]
      congr 2
      apply congrArg (fun f => entries.mapIdx f)
      funext i x
      have hi : start + 1 + i = start + (i + 1) := by omega
      rw [hi]

theorem transcriptLabels_eq_layoutP
    (entries : List (TQ n cap tcap × TM n cap)) :
    transcriptLabelsP entries =
      Origin.seed 0 :: Origin.seed 1 :: queryLayoutEntriesFromP 0 entries := by
  unfold transcriptLabelsP
  rw [queryLayoutEntriesFrom_eq_mapIdxP]
  simp

theorem queryLayoutEntriesFrom_appendP (start : ℕ)
    (l₁ l₂ : List (TQ n cap tcap × TM n cap)) :
    queryLayoutEntriesFromP start (l₁ ++ l₂) =
      queryLayoutEntriesFromP start l₁ ++
        queryLayoutEntriesFromP (start + l₁.length) l₂ := by
  induction l₁ generalizing start with
  | nil => simp [queryLayoutEntriesFromP]
  | cons entry l₁ ih =>
      simp only [List.cons_append, queryLayoutEntriesFromP,
        List.length_cons, List.append_assoc]
      rw [ih (start + 1)]
      have hs : start + 1 + l₁.length = start + (l₁.length + 1) := by omega
      rw [hs]

theorem mem_queryLayoutEntriesFrom_indexP
    {start : ℕ} {entries : List (TQ n cap tcap × TM n cap)}
    {s k : ℕ} (h : Origin.block s k ∈
      queryLayoutEntriesFromP start entries) :
    start ≤ s ∧ s < start + entries.length := by
  induction entries generalizing start with
  | nil => simp [queryLayoutEntriesFromP] at h
  | cons entry entries ih =>
      rw [queryLayoutEntriesFromP, List.mem_append] at h
      rcases h with h | h
      · simp only [queryLabels, List.mem_map, List.mem_range] at h
        obtain ⟨u, -, hu⟩ := h
        cases hu
        simp
      · have hs := ih h
        simp only [List.length_cons]
        omega

def transcriptLabelsPrefixP
    (entries : List (TQ n cap tcap × TM n cap)) (s : ℕ) : List Origin :=
  Origin.seed 0 :: Origin.seed 1 ::
    queryLayoutEntriesFromP 0 (entries.take (s + 1))

theorem transcriptLabelsPrefix_isPrefixP
    (entries : List (TQ n cap tcap × TM n cap)) (s : ℕ) :
    transcriptLabelsPrefixP entries s <+:
      transcriptLabelsP entries := by
  rw [transcriptLabels_eq_layoutP]
  unfold transcriptLabelsPrefixP
  refine ⟨queryLayoutEntriesFromP
    ((entries.take (s + 1)).length) (entries.drop (s + 1)), ?_⟩
  simp only [List.cons_append]
  congr 2
  calc
    queryLayoutEntriesFromP 0 (entries.take (s + 1)) ++
        queryLayoutEntriesFromP (entries.take (s + 1)).length
          (entries.drop (s + 1)) =
      queryLayoutEntriesFromP 0
        (entries.take (s + 1) ++ entries.drop (s + 1)) := by
          simpa using (queryLayoutEntriesFrom_appendP 0
            (entries.take (s + 1)) (entries.drop (s + 1))).symm
    _ = queryLayoutEntriesFromP 0 entries := by simp

theorem transcriptLabelsPrefix_update_eqP
    (entries entries' : List (TQ n cap tcap × TM n cap))
    (s : ℕ) (z : TQ n cap tcap) (y y' : TM n cap)
    (hsel : entries[s]? = some (z, y))
    (hnew : entries'.take (s + 1) = entries.take s ++ [(z, y')]) :
    transcriptLabelsPrefixP entries' s =
      transcriptLabelsPrefixP entries s := by
  have hs : s < entries.length :=
    (List.getElem?_eq_some_iff.mp hsel).choose
  have hget : entries[s] = (z, y) := by
    have hg := hsel
    rw [List.getElem?_eq_getElem hs] at hg
    exact Option.some.inj hg
  have hold : entries.take (s + 1) = entries.take s ++ [(z, y)] := by
    rw [List.take_succ_eq_append_getElem hs, hget]
  unfold transcriptLabelsPrefixP
  rw [hnew, hold, queryLayoutEntriesFrom_appendP,
    queryLayoutEntriesFrom_appendP]
  have hlen : (entries.take s).length = s := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hs)]
  simp [queryLayoutEntriesFromP, queryLabels, entryCharge, hlen]

theorem block_mem_transcriptLabelsPrefixP
    (entries : List (TQ n cap tcap × TM n cap))
    (s k : ℕ) (z : TQ n cap tcap) (y : TM n cap)
    (hsel : entries[s]? = some (z, y))
    (hk : k < entryCharge (z, y)) :
    Origin.block s k ∈ transcriptLabelsPrefixP entries s := by
  have hs : s < entries.length :=
    (List.getElem?_eq_some_iff.mp hsel).choose
  have hget : entries[s] = (z, y) := by
    have hg := hsel
    rw [List.getElem?_eq_getElem hs] at hg
    exact Option.some.inj hg
  unfold transcriptLabelsPrefixP
  simp only [List.mem_cons]
  right; right
  rw [List.take_succ_eq_append_getElem hs, hget,
    queryLayoutEntriesFrom_appendP]
  apply List.mem_append_right
  have hlen : (entries.take s).length = s := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hs)]
  simp only [hlen, zero_add, queryLayoutEntriesFromP, List.mem_append,
    List.not_mem_nil, or_false]
  simp [queryLabels, hk]

theorem labelsOf_nodupP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n) :
    (labelsOf bf o d).Nodup := by
  apply (labelsOf_pairwise_beforeP bf o d hn).imp
  intro a b hab heq
  subst b
  rcases a with k | ⟨s, k⟩ <;> simp [Origin.BeforeP] at hab

theorem labelAt_eq_labels_getP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (i : ℕ) :
    labelAt bf o d i = (labelsOf bf o d)[i]? := by
  simp [labelAt, labelsOf, List.getElem?_map]

theorem label_block_receiptP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n)
    (i s k : ℕ) (hlabel : labelAt bf o d i = some (Origin.block s k)) :
    ∃ v : BitString n,
      (sideOf bf o d)[i]? = some (Origin.block s k, v) ∧
      ∃ entryD : (TQ n cap tcap × TM n cap) × (Σ w, BitString w),
        ((transcriptEntries o.1).zip o.2.2)[s]? = some entryD ∧
          k < entryCharge entryD.1 ∧ v = blockValueP bf o d s k := by
  unfold labelAt at hlabel
  cases hget : (sideOf bf o d)[i]? with
  | none => simp [hget] at hlabel
  | some p =>
      rw [hget] at hlabel
      simp only [Option.map_some, Option.some.injEq] at hlabel
      rcases p with ⟨a, v⟩
      dsimp only at hlabel
      subst a
      refine ⟨v, rfl, ?_⟩
      apply mem_side_block_semanticP bf o d hn s k v
      exact List.mem_iff_getElem?.2 ⟨i, hget⟩

theorem label_block_index_lt_prefixP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n)
    (hwf : WellFormedAugObs o) (i s k : ℕ)
    (hlabel : labelAt bf o d i = some (Origin.block s k))
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y))
    (hk : k < entryCharge (z, y)) :
    i < (transcriptLabelsPrefixP (transcriptEntries o.1) s).length := by
  let entries := transcriptEntries o.1
  let pref := transcriptLabelsPrefixP entries s
  have hmem : Origin.block s k ∈ pref :=
    block_mem_transcriptLabelsPrefixP entries s k z y hsel hk
  obtain ⟨r, hrget⟩ := List.mem_iff_getElem?.mp hmem
  have hr : r < pref.length :=
    (List.getElem?_eq_some_iff.mp hrget).choose
  have hpref : pref <+: transcriptLabelsP entries :=
    transcriptLabelsPrefix_isPrefixP entries s
  rcases hpref with ⟨suffix, happ⟩
  have hrfull : r < (transcriptLabelsP entries).length := by
    rw [← happ]
    simp only [List.length_append]
    omega
  have hrgetfull : (transcriptLabelsP entries)[r]? =
      some (Origin.block s k) := by
    rw [← happ, List.getElem?_append_left (by simpa using hr)]
    exact hrget
  have hlabels : labelsOf bf o d = transcriptLabelsP entries :=
    labelsOf_eq_transcriptLabelsP bf o d hn hwf
  have higet : (transcriptLabelsP entries)[i]? =
      some (Origin.block s k) := by
    rw [← hlabels, ← labelAt_eq_labels_getP]
    exact hlabel
  have hnodup : (transcriptLabelsP entries).Nodup := by
    rw [← hlabels]
    exact labelsOf_nodupP bf o d hn
  have hri : r = i :=
    List.getElem?_inj hrfull hnodup (hrgetfull.trans higet.symm)
  simpa [pref, entries, hri] using hr

theorem coinObs_answered_update_prefixP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y)) :
    (answered (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v))).take (s + 1) =
      (answered (coinObsP hn q σ e m w)).take (s + 1) := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)
  have hnew := coinObs_entries_update_prefixP hn q σ e m hE w z b v s y hsel
  have hs : s < (transcriptEntries o.1).length :=
    (List.getElem?_eq_some_iff.mp (by simpa [o] using hsel)).choose
  have hget : (transcriptEntries o.1)[s] = (z, y) := by
    have hg : (transcriptEntries o.1)[s]? = some (z, y) := by simpa [o] using hsel
    rw [List.getElem?_eq_getElem hs] at hg
    exact Option.some.inj hg
  have hold : (transcriptEntries o.1).take (s + 1) =
      (transcriptEntries o.1).take s ++ [(z, y)] := by
    rw [List.take_succ_eq_append_getElem hs, hget]
  rw [answered, ← PFunDDS.answeredEntries_map_fst,
    answered, ← PFunDDS.answeredEntries_map_fst]
  rw [← List.map_take, ← List.map_take]
  rw [show (transcriptEntries o'.1).take (s + 1) =
      (transcriptEntries o.1).take s ++
        [(z, rndFun (coinKeyP hn
          (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z)] by
      simpa [o, o'] using hnew, hold]
  simp

theorem coinObs_degOf_update_eqP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (r : ℕ) (hr : r ≤ s) :
    degOf (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)) r =
      degOf (coinObsP hn q σ e m w) r := by
  have hp := coinObs_answered_update_prefixP hn q σ e m hE w z b v s y hsel
  have hrs : r < s + 1 := by omega
  have hget := congrArg (fun l => l[r]?) hp
  have hget' :
      (answered (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)))[r]? =
      (answered (coinObsP hn q σ e m w))[r]? := by
    simpa [List.getElem?_take, hrs] using hget
  unfold degOf
  rw [hget']

theorem coinObs_dirOf_update_eqP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (r : ℕ) (hr : r ≤ s) :
    dirOf (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)) r =
      dirOf (coinObsP hn q σ e m w) r := by
  have hp := coinObs_answered_update_prefixP hn q σ e m hE w z b v s y hsel
  have hrs : r < s + 1 := by omega
  have hget := congrArg (fun l => l[r]?) hp
  have hget' :
      (answered (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)))[r]? =
      (answered (coinObsP hn q σ e m w))[r]? := by
    simpa [List.getElem?_take, hrs] using hget
  unfold dirOf
  rw [hget']

theorem coinObs_labelAt_update_eqP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (d : Bool) (idx : ℕ)
    (hidx : idx < (transcriptLabelsPrefixP
      (transcriptEntries (coinObsP hn q σ e m w).1) s).length) :
    labelAt bf (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)) d idx =
      labelAt bf (coinObsP hn q σ e m w) d idx := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)
  have hnew := coinObs_entries_update_prefixP hn q σ e m hE w z b v s y hsel
  have hprefEq : transcriptLabelsPrefixP (transcriptEntries o'.1) s =
      transcriptLabelsPrefixP (transcriptEntries o.1) s := by
    apply transcriptLabelsPrefix_update_eqP
      (transcriptEntries o.1) (transcriptEntries o'.1) s z y
      (rndFun (coinKeyP hn
        (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z)
    · simpa [o] using hsel
    · simpa [o, o'] using hnew
  have hwf : WellFormedAugObs o := by
    exact wellFormed_augRnd q σ e m (coinKeyP hn w)
  have hwf' : WellFormedAugObs o' := by
    exact wellFormed_augRnd q σ e m
      (coinKeyP hn (coinUpdateP w (.inr ⟨z, b⟩) v))
  rw [labelAt_eq_labels_getP, labelAt_eq_labels_getP,
    labelsOf_eq_transcriptLabelsP bf o' d hn hwf',
    labelsOf_eq_transcriptLabelsP bf o d hn hwf]
  rcases transcriptLabelsPrefix_isPrefixP (transcriptEntries o'.1) s with
    ⟨suffix', happ'⟩
  rcases transcriptLabelsPrefix_isPrefixP (transcriptEntries o.1) s with
    ⟨suffix, happ⟩
  rw [← happ', ← happ]
  rw [List.getElem?_append_left (by simpa [hprefEq] using hidx),
    List.getElem?_append_left (by simpa [o] using hidx)]
  exact congrArg (fun l => l[idx]?) hprefEq

theorem costAt_congr_entriesP (bf : Hash.BlockField F n) (hn : 0 < n)
    (o o' : AugObs n cap tcap) (hwf : WellFormedAugObs o)
    (hwf' : WellFormedAugObs o')
    (hentries : transcriptEntries o'.1 = transcriptEntries o.1)
    (d : Bool) (i j : ℕ) :
    costAt bf o' d i j = costAt bf o d i j := by
  have hlabels : labelsOf bf o' d = labelsOf bf o d := by
    rw [labelsOf_eq_transcriptLabelsP bf o' d hn hwf',
      labelsOf_eq_transcriptLabelsP bf o d hn hwf, hentries]
  have hans : answered o' = answered o := by
    rw [answered, ← PFunDDS.answeredEntries_map_fst,
      answered, ← PFunDDS.answeredEntries_map_fst]
    exact congrArg (List.map Prod.fst) hentries
  have hdeg : degOf o' = degOf o := by
    funext s
    unfold degOf
    rw [hans]
  have hdir : dirOf o' = dirOf o := by
    funext s
    unfold dirOf
    rw [hans]
  have hcell : collisionCellAt bf o' d i j =
      collisionCellAt bf o d i j := by
    unfold collisionCellAt
    rw [labelAt_eq_labels_getP, labelAt_eq_labels_getP,
      labelAt_eq_labels_getP, labelAt_eq_labels_getP, hlabels]
  unfold costAt
  rw [hcell, hdeg, hdir]

theorem coinKey_table_terminalP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (a : Bool) (v : BitString n) :
    (coinKeyP hn (coinUpdateP w (.inl a) v)).1 = (coinKeyP hn w).1 := by
  classical
  funext z
  unfold coinKeyP coinUpdateP rndKeyCoinEquivP packCoinBlocksP
    rndKeyBlockEquivP
  change ((queryCoinsEquivP hn z).symm
      (fun b => Function.update w (.inl a) v (.inr ⟨z, b⟩))).1 =
    ((queryCoinsEquivP hn z).symm (fun b => w (.inr ⟨z, b⟩))).1
  congr 2
  funext b
  rw [Function.update_of_ne]
  simp

theorem coinObs_entries_terminalP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (a : Bool) (v : BitString n) :
    transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inl a) v)).1 =
      transcriptEntries (coinObsP hn q σ e m w).1 := by
  change transcriptEntries
      (PFunDDS.transcript (rndDDS n cap tcap q σ
        (coinKeyP hn (coinUpdateP w (.inl a) v)).1) e m) =
    transcriptEntries
      (PFunDDS.transcript (rndDDS n cap tcap q σ
        (coinKeyP hn w).1) e m)
  rw [coinKey_table_terminalP hn w a v]

theorem coinObs_costAt_terminalP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (a : Bool) (v : BitString n)
    (d : Bool) (i j : ℕ) :
    costAt bf (coinObsP hn q σ e m
      (coinUpdateP w (.inl a) v)) d i j =
      costAt bf (coinObsP hn q σ e m w) d i j := by
  apply costAt_congr_entriesP bf hn
  · exact wellFormed_augRnd q σ e m (coinKeyP hn w)
  · exact wellFormed_augRnd q σ e m
      (coinKeyP hn (coinUpdateP w (.inl a) v))
  · exact coinObs_entries_terminalP hn q σ e m w a v

def responseCoinAtP (o : AugObs n cap tcap) (s b : ℕ) :
    CoinIndexP n cap tcap :=
  match (transcriptEntries o.1)[s]? with
  | none => .inl false
  | some entry =>
      if hb : b < queryChargeP entry.1 then
        .inr ⟨entry.1, ⟨b, hb⟩⟩
      else .inl false

noncomputable def collisionLocP (bf : Hash.BlockField F n) (hn : 0 < n)
    (q σ : ℕ) (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap) :
    CoinIndexP n cap tcap :=
  let o := coinObsP hn q σ e m w
  match collisionCellAt bf o d i j with
  | none => .inl false
  | some cell =>
      match cell with
      | .seedSeed _ _ => if d then .inl false else .inl true
      | .seedHead _ s =>
          if dirOf o s = d then .inl false else responseCoinAtP o s 0
      | .seedTail _ s k =>
          if d then .inl true else responseCoinAtP o s (k + 1)
      | .headSeed _ _ => .inl false
      | .tailSeed _ _ _ => .inl false
      | .headHead r s =>
          if r = s then .inl false
          else if dirOf o s = d then .inl false else responseCoinAtP o s 0
      | .headTail r s k =>
          if d then .inl true
          else if r = s then
            if dirOf o s then responseCoinAtP o s 0
            else responseCoinAtP o s (k + 1)
          else responseCoinAtP o s (k + 1)
      | .tailHead r _ s =>
          if r = s then .inl false
          else if d then .inl true
          else if dirOf o s = d then .inl false else responseCoinAtP o s 0
      | .tailTail r _ s l =>
          if r = s then
            if d then .inl false else responseCoinAtP o s (l + 1)
          else if d then responseCoinAtP o s 0
          else responseCoinAtP o s (l + 1)

theorem collisionCellAt_labelsP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (i j : ℕ)
    (cell : CollisionCell)
    (hcell : collisionCellAt bf o d i j = some cell) :
    i < j ∧ labelAt bf o d i = some cell.origins.1 ∧
      labelAt bf o d j = some cell.origins.2 := by
  unfold collisionCellAt at hcell
  split at hcell
  · rename_i hij
    cases hleft : labelAt bf o d i <;>
      cases hright : labelAt bf o d j <;> simp_all
    subst cell
    simp
  · simp at hcell

theorem collisionCellAt_beforeP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n) (i j : ℕ)
    (cell : CollisionCell)
    (hcell : collisionCellAt bf o d i j = some cell) :
    Origin.BeforeP cell.origins.1 cell.origins.2 := by
  obtain ⟨hij, hleft, hright⟩ := collisionCellAt_labelsP bf o d i j cell hcell
  rw [labelAt_eq_labels_getP] at hleft hright
  have hi : i < (labelsOf bf o d).length :=
    (List.getElem?_eq_some_iff.mp hleft).choose
  have hj : j < (labelsOf bf o d).length :=
    (List.getElem?_eq_some_iff.mp hright).choose
  have hp := (List.pairwise_iff_getElem.mp
    (labelsOf_pairwise_beforeP bf o d hn)) i j hi hj hij
  rw [List.getElem?_eq_getElem hi] at hleft
  rw [List.getElem?_eq_getElem hj] at hright
  rw [Option.some.inj hleft, Option.some.inj hright] at hp
  exact hp

theorem responseCoinAt_update_eqP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (c : ℕ) (hc : c < queryChargeP z) :
    responseCoinAtP
      (coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)) s c =
      responseCoinAtP (coinObsP hn q σ e m w) s c := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)
  have hnew := coinObs_entries_update_prefixP hn q σ e m hE w z b v s y hsel
  have hsold : s < (transcriptEntries o.1).length :=
    (List.getElem?_eq_some_iff.mp (by simpa [o] using hsel)).choose
  have htakeLen :
      ((transcriptEntries (coinObsP hn q σ e m w).1).take s).length = s := by
    simpa [o, List.length_take] using
      (Nat.min_eq_left (Nat.le_of_lt hsold))
  have htakeget : ((transcriptEntries o'.1).take (s + 1))[s]? =
      some (z, rndFun (coinKeyP hn
        (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z) := by
    rw [hnew]
    rw [List.getElem?_append_right (by omega)]
    rw [htakeLen]
    simp
  have hsel' : (transcriptEntries o'.1)[s]? =
      some (z, rndFun (coinKeyP hn
        (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z) := by
    simpa [List.getElem?_take] using htakeget
  unfold responseCoinAtP
  rw [show (transcriptEntries o'.1)[s]? = _ by exact hsel',
    show (transcriptEntries o.1)[s]? = some (z, y) by simpa [o] using hsel]

theorem entryCharge_eq_queryChargeP (hn : 0 < n)
    (entry : TQ n cap tcap × TM n cap) :
    entryCharge entry = queryChargeP entry.1 := by
  rw [entryCharge, queryChargeP,
    numBlocks_Msg_len entry.1.2.2 hn]

theorem collisionCellAt_congr_entriesP (bf : Hash.BlockField F n)
    (hn : 0 < n) (o o' : AugObs n cap tcap)
    (hwf : WellFormedAugObs o) (hwf' : WellFormedAugObs o')
    (hentries : transcriptEntries o'.1 = transcriptEntries o.1)
    (d : Bool) (i j : ℕ) :
    collisionCellAt bf o' d i j = collisionCellAt bf o d i j := by
  have hlabels : labelsOf bf o' d = labelsOf bf o d := by
    rw [labelsOf_eq_transcriptLabelsP bf o' d hn hwf',
      labelsOf_eq_transcriptLabelsP bf o d hn hwf, hentries]
  unfold collisionCellAt
  rw [labelAt_eq_labels_getP, labelAt_eq_labels_getP,
    labelAt_eq_labels_getP, labelAt_eq_labels_getP, hlabels]

theorem collisionLoc_terminal_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap)
    (a : Bool) (v : BitString n) :
    collisionLocP bf hn q σ e m d i j (coinUpdateP w (.inl a) v) =
      collisionLocP bf hn q σ e m d i j w := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inl a) v)
  have he : transcriptEntries o'.1 = transcriptEntries o.1 := by
    exact coinObs_entries_terminalP hn q σ e m w a v
  have hwf : WellFormedAugObs o :=
    wellFormed_augRnd q σ e m (coinKeyP hn w)
  have hwf' : WellFormedAugObs o' :=
    wellFormed_augRnd q σ e m (coinKeyP hn (coinUpdateP w (.inl a) v))
  have hcell := collisionCellAt_congr_entriesP bf hn o o' hwf hwf' he d i j
  have hans : answered o' = answered o := by
    rw [answered, ← PFunDDS.answeredEntries_map_fst,
      answered, ← PFunDDS.answeredEntries_map_fst]
    exact congrArg (List.map Prod.fst) he
  have hdir : dirOf o' = dirOf o := by
    funext s
    unfold dirOf
    rw [hans]
  have hresp : ∀ s b, responseCoinAtP o' s b = responseCoinAtP o s b := by
    intro s b
    unfold responseCoinAtP
    rw [he]
  simp only [collisionLocP]
  change (match collisionCellAt bf o' d i j with
    | none => (Sum.inl false : CoinIndexP n cap tcap)
    | some cell => match cell with
      | .seedSeed _ _ => if d then .inl false else .inl true
      | .seedHead _ s => if dirOf o' s = d then .inl false else responseCoinAtP o' s 0
      | .seedTail _ s k => if d then .inl true else responseCoinAtP o' s (k + 1)
      | .headSeed _ _ => .inl false
      | .tailSeed _ _ _ => .inl false
      | .headHead r s => if r = s then .inl false else
          if dirOf o' s = d then .inl false else responseCoinAtP o' s 0
      | .headTail r s k => if d then .inl true else if r = s then
          if dirOf o' s then responseCoinAtP o' s 0 else responseCoinAtP o' s (k + 1)
        else responseCoinAtP o' s (k + 1)
      | .tailHead r _ s => if r = s then .inl false else if d then .inl true else
          if dirOf o' s = d then .inl false else responseCoinAtP o' s 0
      | .tailTail r _ s l => if r = s then
          if d then .inl false else responseCoinAtP o' s (l + 1)
        else if d then responseCoinAtP o' s 0 else responseCoinAtP o' s (l + 1)) = _
  rw [hcell, hdir]
  cases hc : collisionCellAt bf o d i j with
  | none => rfl
  | some cell =>
      simp only
      cases cell <;> simp only <;> simp_rw [hresp] <;> rfl

theorem coinObs_collisionCellAt_update_eqP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (d : Bool) (i j : ℕ) (cell : CollisionCell) (k : ℕ)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j = some cell)
    (hright : cell.origins.2 = Origin.block s k)
    (hk : k < entryCharge (z, y)) :
    collisionCellAt bf (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)) d i j = some cell := by
  let o := coinObsP hn q σ e m w
  have hcLabels := collisionCellAt_labelsP bf o d i j cell (by simpa [o] using hcell)
  have hij := hcLabels.1
  have hjlabel := hcLabels.2.2
  rw [hright] at hjlabel
  have hwf : WellFormedAugObs o :=
    wellFormed_augRnd q σ e m (coinKeyP hn w)
  have hjpref := label_block_index_lt_prefixP bf o d hn hwf j s k
    hjlabel z y (by simpa [o] using hsel) hk
  have hipref : i < (transcriptLabelsPrefixP
      (transcriptEntries o.1) s).length := lt_trans hij hjpref
  have hiEq := coinObs_labelAt_update_eqP bf hn q σ e m hE
    w z b v s y hsel d i (by simpa [o] using hipref)
  have hjEq := coinObs_labelAt_update_eqP bf hn q σ e m hE
    w z b v s y hsel d j (by simpa [o] using hjpref)
  unfold collisionCellAt
  rw [hiEq, hjEq]
  simpa [collisionCellAt, hij, o] using hcell

theorem coinObs_costAt_response_update_eqP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (d : Bool) (i j : ℕ) (cell : CollisionCell) (k : ℕ)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j = some cell)
    (hright : cell.origins.2 = Origin.block s k)
    (hk : k < entryCharge (z, y)) :
    costAt bf (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)) d i j =
      costAt bf (coinObsP hn q σ e m w) d i j := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)
  have hcell' := coinObs_collisionCellAt_update_eqP bf hn q σ e m hE
    w z b v s y hsel d i j cell k hcell hright hk
  have hbefore : Origin.BeforeP cell.origins.1 cell.origins.2 :=
    collisionCellAt_beforeP bf o d hn i j cell (by simpa [o] using hcell)
  have hdeg : ∀ r, r ≤ s →
      degOf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) r =
        degOf (coinObsP hn q σ e m w) r := by
    intro r hr
    exact coinObs_degOf_update_eqP hn q σ e m hE w z b v s y hsel r hr
  have hdir : ∀ r, r ≤ s →
      dirOf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) r =
        dirOf (coinObsP hn q σ e m w) r := by
    intro r hr
    exact coinObs_dirOf_update_eqP hn q σ e m hE w z b v s y hsel r hr
  unfold costAt
  rw [show collisionCellAt bf o' d i j = some cell by simpa [o'] using hcell',
    show collisionCellAt bf o d i j = some cell by simpa [o] using hcell]
  cases cell with
  | seedSeed a b => simp [CollisionCell.origins] at hright
  | seedHead a s' =>
      simp only [CollisionCell.origins, Prod.snd] at hright
      injection hright with hs hk'
      subst s'; subst k
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      rw [hdir s (le_refl s)]
      by_cases hd : dirOf (coinObsP hn q σ e m w) s = d <;>
        simp [hd, hdeg s (le_refl s)]
  | seedTail a s' k' =>
      simp [CollisionCell.bound, CollisionCell.Bound.cost]
  | headSeed s' a => simp [CollisionCell.origins] at hright
  | tailSeed s' k' a => simp [CollisionCell.origins] at hright
  | headHead r s' =>
      simp only [CollisionCell.origins, Prod.fst, Prod.snd] at hbefore hright
      injection hright with hs hk'
      subst s'; subst k
      have hrs : r < s := by simpa [Origin.BeforeP] using hbefore
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      rw [hdir s (le_refl s)]
      by_cases hd : dirOf (coinObsP hn q σ e m w) s = d <;>
        simp [hd, hdeg r (Nat.le_of_lt hrs), hdeg s (le_refl s)]
  | headTail r s' k' =>
      simp [CollisionCell.bound, CollisionCell.Bound.cost]
  | tailHead r k' s' =>
      simp only [CollisionCell.origins, Prod.fst, Prod.snd] at hbefore hright
      injection hright with hs hk''
      subst s'; subst k
      have hrs : r < s := by simpa [Origin.BeforeP] using hbefore
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      rw [hdir s (le_refl s)]
      have hrsne : r ≠ s := ne_of_lt hrs
      by_cases hd : d = true
      · simp [hrsne, hd]
      · have hd0 : d = false := by cases d <;> simp_all
        subst d
        by_cases hg : dirOf (coinObsP hn q σ e m w) s = false <;>
          simp [hrsne, hg, hdeg s (le_refl s)]
  | tailTail r k' s' l =>
      by_cases hrs : r = s' <;> by_cases hd : d = true <;>
        simp [CollisionCell.bound, CollisionCell.Bound.cost, hrs, hd]

theorem coinObs_collisionLoc_response_update_eqP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (d : Bool) (i j : ℕ) (cell : CollisionCell) (k : ℕ)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j = some cell)
    (hright : cell.origins.2 = Origin.block s k)
    (hk : k < entryCharge (z, y)) :
    collisionLocP bf hn q σ e m d i j
      (coinUpdateP w (.inr ⟨z, b⟩) v) =
      collisionLocP bf hn q σ e m d i j w := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)
  have hcell' := coinObs_collisionCellAt_update_eqP bf hn q σ e m hE
    w z b v s y hsel d i j cell k hcell hright hk
  have hdir : ∀ r, r ≤ s →
      dirOf o' r = dirOf o r := by
    intro r hr
    exact coinObs_dirOf_update_eqP hn q σ e m hE w z b v s y hsel r hr
  have hresp : ∀ c, c < queryChargeP z →
      responseCoinAtP o' s c = responseCoinAtP o s c := by
    intro c hc
    exact responseCoinAt_update_eqP hn q σ e m hE w z b v s y hsel c hc
  have hhead : 0 < queryChargeP z := by simp [queryChargeP]
  simp only [collisionLocP]
  rw [show collisionCellAt bf o' d i j = some cell by simpa [o'] using hcell',
    show collisionCellAt bf o d i j = some cell by simpa [o] using hcell]
  cases cell with
  | seedSeed a b => simp [CollisionCell.origins] at hright
  | seedHead a s' =>
      simp only [CollisionCell.origins] at hright
      injection hright with hs hk'
      subst s'; subst k
      simp only
      rw [hdir s (le_refl s), hresp 0 hhead]
  | seedTail a s' k' =>
      simp only [CollisionCell.origins] at hright
      injection hright with hs hk'
      subst s'; subst k
      have htail : k' + 1 < queryChargeP z := by
        rwa [← entryCharge_eq_queryChargeP hn (z, y)]
      simp only
      rw [hresp (k' + 1) htail]
  | headSeed s' a => simp [CollisionCell.origins] at hright
  | tailSeed s' k' a => simp [CollisionCell.origins] at hright
  | headHead r s' =>
      simp only [CollisionCell.origins] at hright
      injection hright with hs hk'
      subst s'; subst k
      simp only
      rw [hdir s (le_refl s), hresp 0 hhead]
  | headTail r s' k' =>
      simp only [CollisionCell.origins] at hright
      injection hright with hs hk''
      subst s'; subst k
      have htail : k' + 1 < queryChargeP z := by
        rwa [← entryCharge_eq_queryChargeP hn (z, y)]
      simp only
      rw [hdir s (le_refl s), hresp 0 hhead, hresp (k' + 1) htail]
  | tailHead r k' s' =>
      simp only [CollisionCell.origins] at hright
      injection hright with hs hk''
      subst s'; subst k
      simp only
      rw [hdir s (le_refl s), hresp 0 hhead]
  | tailTail r k' s' l =>
      simp only [CollisionCell.origins] at hright
      injection hright with hs hk''
      subst s'; subst k
      have htail : l + 1 < queryChargeP z := by
        rwa [← entryCharge_eq_queryChargeP hn (z, y)]
      simp only
      rw [hresp 0 hhead, hresp (l + 1) htail]

theorem label_block_query_receiptP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n)
    (i s k : ℕ) (hlabel : labelAt bf o d i = some (Origin.block s k)) :
    ∃ z : TQ n cap tcap, ∃ y : TM n cap,
      (transcriptEntries o.1)[s]? = some (z, y) ∧
        k < entryCharge (z, y) := by
  obtain ⟨v, hget, entryD, hzip, hk, hv⟩ :=
    label_block_receiptP bf o d hn i s k hlabel
  have hz := (List.getElem?_zip_eq_some.mp hzip).1
  exact ⟨entryD.1.1, entryD.1.2, hz, hk⟩

theorem responseCoinAt_eq_inrP (o : AugObs n cap tcap)
    (s c : ℕ) (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y))
    (hc : c < queryChargeP z) :
    responseCoinAtP o s c = Sum.inr ⟨z, ⟨c, hc⟩⟩ := by
  unfold responseCoinAtP
  rw [hsel]
  simp [hc]

theorem collisionLoc_certificateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap) :
    (∃ a : Bool, collisionLocP bf hn q σ e m d i j w = .inl a) ∨
      ∃ (cell : CollisionCell) (s k : ℕ) (z : TQ n cap tcap)
        (y : TM n cap) (b : Fin (queryChargeP z)),
        collisionCellAt bf (coinObsP hn q σ e m w) d i j = some cell ∧
        cell.origins.2 = Origin.block s k ∧
        (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y) ∧
        k < entryCharge (z, y) ∧
        collisionLocP bf hn q σ e m d i j w = .inr ⟨z, b⟩ := by
  let o := coinObsP hn q σ e m w
  cases hcell : collisionCellAt bf o d i j with
  | none =>
      exact Or.inl ⟨false, by simp [collisionLocP, o, hcell]⟩
  | some cell =>
      have hcell' :
          collisionCellAt bf (coinObsP hn q σ e m w) d i j = some cell := by
        simpa [o] using hcell
      have hlabels := collisionCellAt_labelsP bf o d i j cell hcell
      have rightReceipt : ∀ s k,
          cell.origins.2 = Origin.block s k →
          ∃ z : TQ n cap tcap, ∃ y : TM n cap,
            (transcriptEntries o.1)[s]? = some (z, y) ∧
              k < entryCharge (z, y) := by
        intro s k hright
        apply label_block_query_receiptP bf o d hn j s k
        rw [← hright]
        exact hlabels.2.2
      cases cell with
      | seedSeed a b =>
          cases d
          · exact Or.inl ⟨true, by simp [collisionLocP, hcell']⟩
          · exact Or.inl ⟨false, by simp [collisionLocP, hcell']⟩
      | seedHead a s =>
          obtain ⟨z, y, hsel, hk⟩ := rightReceipt s 0 rfl
          have hc : 0 < queryChargeP z := by simp [queryChargeP]
          by_cases hg : dirOf o s = d
          · exact Or.inl ⟨false, by simp [collisionLocP, hcell', o, hg]⟩
          · refine Or.inr ⟨.seedHead a s, s, 0, z, y, ⟨0, hc⟩,
              by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
            rw [show collisionLocP bf hn q σ e m d i j w =
                responseCoinAtP o s 0 by simp [collisionLocP, hcell', o, hg],
              responseCoinAt_eq_inrP o s 0 z y hsel hc]
      | seedTail a s k =>
          obtain ⟨z, y, hsel, hk⟩ := rightReceipt s (k + 1) rfl
          have hc : k + 1 < queryChargeP z := by
            rwa [← entryCharge_eq_queryChargeP hn (z, y)]
          cases d
          · refine Or.inr ⟨.seedTail a s k, s, k + 1, z, y,
                ⟨k + 1, hc⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
            rw [show collisionLocP bf hn q σ e m false i j w =
                responseCoinAtP o s (k + 1) by
                  simp [collisionLocP, hcell', o],
              responseCoinAt_eq_inrP o s (k + 1) z y hsel hc]
          · exact Or.inl ⟨true, by simp [collisionLocP, hcell']⟩
      | headSeed s a =>
          exact Or.inl ⟨false, by simp [collisionLocP, hcell']⟩
      | tailSeed s k a =>
          exact Or.inl ⟨false, by simp [collisionLocP, hcell']⟩
      | headHead r s =>
          obtain ⟨z, y, hsel, hk⟩ := rightReceipt s 0 rfl
          have hc : 0 < queryChargeP z := by simp [queryChargeP]
          by_cases hrs : r = s
          · exact Or.inl ⟨false, by simp [collisionLocP, hcell', hrs]⟩
          · by_cases hg : dirOf o s = d
            · exact Or.inl ⟨false, by simp [collisionLocP, hcell', o, hrs, hg]⟩
            · refine Or.inr ⟨.headHead r s, s, 0, z, y, ⟨0, hc⟩,
                  by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
              rw [show collisionLocP bf hn q σ e m d i j w =
                  responseCoinAtP o s 0 by
                    simp [collisionLocP, hcell', o, hrs, hg],
                responseCoinAt_eq_inrP o s 0 z y hsel hc]
      | headTail r s k =>
          obtain ⟨z, y, hsel, hk⟩ := rightReceipt s (k + 1) rfl
          have htail : k + 1 < queryChargeP z := by
            rwa [← entryCharge_eq_queryChargeP hn (z, y)]
          have hhead : 0 < queryChargeP z := by simp [queryChargeP]
          cases d
          · by_cases hrs : r = s
            · by_cases hdir : dirOf o s = true
              · refine Or.inr ⟨.headTail r s k, s, k + 1, z, y,
                    ⟨0, hhead⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
                rw [show collisionLocP bf hn q σ e m false i j w =
                    responseCoinAtP o s 0 by
                      simp [collisionLocP, hcell', o, hrs, hdir],
                  responseCoinAt_eq_inrP o s 0 z y hsel hhead]
              · refine Or.inr ⟨.headTail r s k, s, k + 1, z, y,
                    ⟨k + 1, htail⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
                rw [show collisionLocP bf hn q σ e m false i j w =
                    responseCoinAtP o s (k + 1) by
                      simp [collisionLocP, hcell', o, hrs, hdir],
                  responseCoinAt_eq_inrP o s (k + 1) z y hsel htail]
            · refine Or.inr ⟨.headTail r s k, s, k + 1, z, y,
                  ⟨k + 1, htail⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
              rw [show collisionLocP bf hn q σ e m false i j w =
                  responseCoinAtP o s (k + 1) by
                    simp [collisionLocP, hcell', o, hrs],
                responseCoinAt_eq_inrP o s (k + 1) z y hsel htail]
          · exact Or.inl ⟨true, by simp [collisionLocP, hcell']⟩
      | tailHead r k s =>
          obtain ⟨z, y, hsel, hk⟩ := rightReceipt s 0 rfl
          have hc : 0 < queryChargeP z := by simp [queryChargeP]
          by_cases hrs : r = s
          · exact Or.inl ⟨false, by simp [collisionLocP, hcell', hrs]⟩
          · cases d
            · by_cases hg : dirOf o s = false
              · exact Or.inl ⟨false, by simp [collisionLocP, hcell', o, hrs, hg]⟩
              · refine Or.inr ⟨.tailHead r k s, s, 0, z, y, ⟨0, hc⟩,
                    by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
                rw [show collisionLocP bf hn q σ e m false i j w =
                    responseCoinAtP o s 0 by
                      simp [collisionLocP, hcell', o, hrs, hg],
                  responseCoinAt_eq_inrP o s 0 z y hsel hc]
            · exact Or.inl ⟨true, by simp [collisionLocP, hcell', hrs]⟩
      | tailTail r k s l =>
          obtain ⟨z, y, hsel, hk⟩ := rightReceipt s (l + 1) rfl
          have htail : l + 1 < queryChargeP z := by
            rwa [← entryCharge_eq_queryChargeP hn (z, y)]
          have hhead : 0 < queryChargeP z := by simp [queryChargeP]
          by_cases hrs : r = s
          · cases d
            · refine Or.inr ⟨.tailTail r k s l, s, l + 1, z, y,
                  ⟨l + 1, htail⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
              rw [show collisionLocP bf hn q σ e m false i j w =
                  responseCoinAtP o s (l + 1) by
                    simp [collisionLocP, hcell', o, hrs],
                responseCoinAt_eq_inrP o s (l + 1) z y hsel htail]
            · exact Or.inl ⟨false, by simp [collisionLocP, hcell', hrs]⟩
          · cases d
            · refine Or.inr ⟨.tailTail r k s l, s, l + 1, z, y,
                  ⟨l + 1, htail⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
              rw [show collisionLocP bf hn q σ e m false i j w =
                  responseCoinAtP o s (l + 1) by
                    simp [collisionLocP, hcell', o, hrs],
                responseCoinAt_eq_inrP o s (l + 1) z y hsel htail]
            · refine Or.inr ⟨.tailTail r k s l, s, l + 1, z, y,
                  ⟨0, hhead⟩, by simpa [o] using hcell, rfl, hsel, hk, ?_⟩
              rw [show collisionLocP bf hn q σ e m true i j w =
                  responseCoinAtP o s 0 by
                    simp [collisionLocP, hcell', o, hrs],
                responseCoinAt_eq_inrP o s 0 z y hsel hhead]

theorem collisionLoc_self_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap) (v : BitString n) :
    collisionLocP bf hn q σ e m d i j
        (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v) =
      collisionLocP bf hn q σ e m d i j w := by
  rcases collisionLoc_certificateP bf hn q σ e m d i j w with
    ⟨a, hloc⟩ | ⟨cell, s, k, z, y, b, hcell, hright, hsel, hk, hloc⟩
  · calc
      collisionLocP bf hn q σ e m d i j
          (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v) =
          collisionLocP bf hn q σ e m d i j
            (coinUpdateP w (.inl a) v) := by rw [hloc]
      _ = collisionLocP bf hn q σ e m d i j w :=
        collisionLoc_terminal_updateP bf hn q σ e m d i j w a v
  · calc
      collisionLocP bf hn q σ e m d i j
          (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v) =
          collisionLocP bf hn q σ e m d i j
            (coinUpdateP w (.inr ⟨z, b⟩) v) := by rw [hloc]
      _ = collisionLocP bf hn q σ e m d i j w :=
        coinObs_collisionLoc_response_update_eqP bf hn q σ e m hE
          w z b v s y hsel d i j cell k hcell hright hk

theorem collisionCost_self_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap) (v : BitString n) :
    costAt bf (coinObsP hn q σ e m
        (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v)) d i j =
      costAt bf (coinObsP hn q σ e m w) d i j := by
  rcases collisionLoc_certificateP bf hn q σ e m d i j w with
    ⟨a, hloc⟩ | ⟨cell, s, k, z, y, b, hcell, hright, hsel, hk, hloc⟩
  · rw [hloc]
    exact coinObs_costAt_terminalP bf hn q σ e m w a v d i j
  · rw [hloc]
    exact coinObs_costAt_response_update_eqP bf hn q σ e m hE
      w z b v s y hsel d i j cell k hcell hright hk

theorem collisionCell_self_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap) (v : BitString n) :
    collisionCellAt bf (coinObsP hn q σ e m
        (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v)) d i j =
      collisionCellAt bf (coinObsP hn q σ e m w) d i j := by
  rcases collisionLoc_certificateP bf hn q σ e m d i j w with
    ⟨a, hloc⟩ | ⟨cell, s, k, z, y, b, hcell, hright, hsel, hk, hloc⟩
  · rw [hloc]
    apply collisionCellAt_congr_entriesP bf hn
    · exact wellFormed_augRnd q σ e m (coinKeyP hn w)
    · exact wellFormed_augRnd q σ e m
        (coinKeyP hn (coinUpdateP w (.inl a) v))
    · exact coinObs_entries_terminalP hn q σ e m w a v
  · rw [hloc, hcell]
    exact coinObs_collisionCellAt_update_eqP bf hn q σ e m hE
      w z b v s y hsel d i j cell k hcell hright hk

theorem pairCollision_cell_valuesP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (hn : 0 < n) (i j : ℕ)
    (cell : CollisionCell)
    (hcell : collisionCellAt bf o d i j = some cell)
    (hcoll : pairCollision bf o d i j) :
    originValueP bf o d cell.origins.1 =
      originValueP bf o d cell.origins.2 := by
  obtain ⟨p, hp⟩ := hcoll
  have hpcell := p.cell_at_eq_some
  rw [hcell] at hpcell
  have heq : p.cell = cell := (Option.some.inj hpcell).symm
  have horig : (p.left.1, p.right.1) = cell.origins :=
    p.cell_origins.symm.trans (congrArg CollisionCell.origins heq)
  have hvalues := (p.collides_iffP hn).mp hp
  have hleft : p.left.1 = cell.origins.1 := by
    simpa using congrArg Prod.fst horig
  have hright : p.right.1 = cell.origins.2 := by
    simpa using congrArg Prod.snd horig
  rw [hleft, hright] at hvalues
  exact hvalues

@[simp] theorem coinObs_hbar_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) :
    (coinObsP hn q σ e m (coinUpdateP w (.inl false) v)).2.1.1 = v := by
  simp [coinObsP, augRnd, coinUpdateP]

@[simp] theorem coinObs_L_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) :
    (coinObsP hn q σ e m (coinUpdateP w (.inl true) v)).2.1.2 = v := by
  simp [coinObsP, augRnd, coinUpdateP]

theorem coinObs_response_eqP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y)) :
    rndFun (coinKeyP hn w).1 z = y := by
  exact answered_functionEvaluatorP
    (Budget (n := n) (cap := cap) (tcap := tcap) q σ)
    (budget_prefixClosed q σ) (rndFun (coinKeyP hn w).1) e m
    (z, y) (by
      simpa [coinObsP, augRnd, rndDDS] using
        (List.mem_iff_getElem?.2 ⟨s, hsel⟩))

theorem coinObs_zip_getP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y)) :
    (((transcriptEntries (coinObsP hn q σ e m w).1).zip
        (coinObsP hn q σ e m w).2.2)[s]?) =
      some ((z, y),
        (⟨padLen n z.2.2.1.val - z.2.2.1.val,
          (coinKeyP hn w).2.2 z⟩ : Σ width : ℕ, BitString width)) := by
  simp only [coinObsP, augRnd] at hsel ⊢
  rw [List.getElem?_zip_eq_some]
  refine ⟨hsel, ?_⟩
  simp [List.getElem?_map, hsel]

theorem blockValue_headP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries o.1).zip o.2.2)[s]?) = some (entry, D)) :
    blockValueP bf o d s 0 =
      if d then mmP bf o.2.1.1 entry else uuP bf o.2.1.1 entry := by
  cases d <;> simp [blockValueP, hzip]

theorem blockValue_tail_inputP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (s k : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries o.1).zip o.2.2)[s]?) = some (entry, D)) :
    blockValueP bf o true s (k + 1) =
      ssP bf o.2.1.1 o.2.1.2 entry ^^^ bin n (k + 1) := by
  simp [blockValueP, hzip]

theorem blockValue_tail_outputP (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (s k : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries o.1).zip o.2.2)[s]?) = some (entry, D))
    (hk : k < (yBlocksP entry D).length) :
    blockValueP bf o false s (k + 1) = (yBlocksP entry D).get ⟨k, hk⟩ := by
  rw [blockValueP]
  simp only [hzip, ↓reduceIte, Nat.add_sub_cancel]
  exact List.getD_eq_getElem _ _ hk

theorem coinKey_leftover_terminalP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (a : Bool) (v : BitString n) :
    (coinKeyP hn (coinUpdateP w (.inl a) v)).2.2 =
      (coinKeyP hn w).2.2 := by
  classical
  funext z
  unfold coinKeyP coinUpdateP rndKeyCoinEquivP packCoinBlocksP
    rndKeyBlockEquivP
  change ((queryCoinsEquivP hn z).symm
      (fun b => Function.update w (.inl a) v (.inr ⟨z, b⟩))).2 =
    ((queryCoinsEquivP hn z).symm (fun b => w (.inr ⟨z, b⟩))).2
  congr 2
  funext b
  rw [Function.update_of_ne]
  simp

theorem coinObs_zip_terminalP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (a : Bool) (v : BitString n) :
    (transcriptEntries
        (coinObsP hn q σ e m (coinUpdateP w (.inl a) v)).1).zip
          (coinObsP hn q σ e m (coinUpdateP w (.inl a) v)).2.2 =
      (transcriptEntries (coinObsP hn q σ e m w).1).zip
        (coinObsP hn q σ e m w).2.2 := by
  have htable := coinKey_table_terminalP hn w a v
  have hleft := coinKey_leftover_terminalP hn w a v
  simp only [coinObsP, augRnd]
  rw [htable, hleft]

theorem coinObs_entry_update_getP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y)) :
    (transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)).1)[s]? =
      some (z, rndFun (coinKeyP hn
        (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z) := by
  let o := coinObsP hn q σ e m w
  let o' := coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)
  have hnew := coinObs_entries_update_prefixP hn q σ e m hE
    w z b v s y hsel
  have hsold : s < (transcriptEntries o.1).length :=
    (List.getElem?_eq_some_iff.mp (by simpa [o] using hsel)).choose
  have htakeLen :
      ((transcriptEntries (coinObsP hn q σ e m w).1).take s).length = s := by
    simpa [o, List.length_take] using Nat.min_eq_left (Nat.le_of_lt hsold)
  have htakeget : ((transcriptEntries o'.1).take (s + 1))[s]? =
      some (z, rndFun (coinKeyP hn
        (coinUpdateP w (.inr ⟨z, b⟩) v)).1 z) := by
    rw [hnew, List.getElem?_append_right (by omega), htakeLen]
    simp
  simpa [o', List.getElem?_take] using htakeget

def queryTailMaskP (z : TQ n cap tcap) (k : ℕ) : BitString n :=
  (z.2.2.2[n; z.2.2.1.val] ∥
    (0 : BitString (padLen n z.2.2.1.val - z.2.2.1.val)))[n * k; n]

theorem sub_cat_xorP (x y : BitString a) (D : BitString b) (s l : ℕ) :
    ((x ^^^ y) ∥ D)[s; l] =
      (x ∥ (0 : BitString b))[s; l] ^^^ (y ∥ D)[s; l] := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  simp only [substring, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor,
    Bits.Facts.getLsbD_cat, BitVec.getLsbD_zero]
  by_cases h : s + p < a <;> simp [h, hp]

@[simp] theorem coinKey_response_head_updateP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap) (v : BitString n) :
    ((coinKeyP hn (coinUpdateP w
      (.inr ⟨z, ⟨0, by simp [queryChargeP]⟩⟩) v)).1 z)[0; n] = v := by
  rw [coinKey_response_headP]
  simp [coinUpdateP]

theorem yBlocks_coin_updateP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (k : Fin (numBlocks n z.2.2.1.val)) (v : BitString n) :
    let b : Fin (queryChargeP z) :=
      ⟨k.val + 1, by simp [queryChargeP]; omega⟩
    let w' := coinUpdateP w (.inr ⟨z, b⟩) v
    let D : Σ width : ℕ, BitString width :=
      ⟨padLen n z.2.2.1.val - z.2.2.1.val, (coinKeyP hn w').2.2 z⟩
    (yBlocksP (z, rndFun (coinKeyP hn w').1 z) D).get
        ⟨k.val, by simpa [yBlocksP] using k.isLt⟩ =
      queryTailMaskP z k.val ^^^ v := by
  dsimp only
  let b : Fin (queryChargeP z) :=
    ⟨k.val + 1, by simp [queryChargeP]; omega⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  have hcoin := coinKey_response_tail_blockP hn w' z k
  have hcoin' :
      (((coinKeyP hn w').1 z)[n; z.2.2.1.val] ∥
        (coinKeyP hn w').2.2 z)[n * k.val; n] = v := by
    simpa [blocksTake, b, w', coinUpdateP] using hcoin
  rcases z with ⟨dir, T, j, Q⟩
  cases dir
  · simp only [yBlocksP, plainPartsP, cipherPartsP, rndFun, queryTailMaskP,
      blocksTake, List.get_ofFn]
    have hform := sub_cat_xorP
      (x := Q[n; j.val])
      (y := ((coinKeyP hn w').1 (.fwd, T, ⟨j, Q⟩))[n; j.val])
      (D := (coinKeyP hn w').2.2 (.fwd, T, ⟨j, Q⟩))
      (s := n * k.val) (l := n)
    rw [hcoin'] at hform
    simpa using hform
  · simp only [yBlocksP, plainPartsP, cipherPartsP, rndFun, queryTailMaskP,
      blocksTake, List.get_ofFn]
    have hform := sub_cat_xorP
      (x := Q[n; j.val])
      (y := ((coinKeyP hn w').1 (.inv, T, ⟨j, Q⟩))[n; j.val])
      (D := (coinKeyP hn w').2.2 (.inv, T, ⟨j, Q⟩))
      (s := n * k.val) (l := n)
    rw [hcoin'] at hform
    simpa [BitVec.xor_comm] using hform

def plainMessageP (entry : TQ n cap tcap × TM n cap) : TM n cap :=
  match entry.1.1 with
  | .fwd => entry.1.2.2
  | .inv => entry.2

def cipherMessageP (entry : TQ n cap tcap × TM n cap) : TM n cap :=
  match entry.1.1 with
  | .fwd => entry.2
  | .inv => entry.1.2.2

theorem pinnedIO_eq_messagesP (entry : TQ n cap tcap × TM n cap) :
    TweakablePRP.pinnedIO entry.1 entry.2 =
      (plainMessageP entry, cipherMessageP entry) := by
  rcases entry with ⟨⟨dir, T, M⟩, C⟩
  cases dir <;> rfl

theorem message_lengthsP (entry : TQ n cap tcap × TM n cap)
    (hmatch : entry.2.1 = entry.1.2.2.1) :
    (plainMessageP entry).1 = entry.1.2.2.1 ∧
      (cipherMessageP entry).1 = entry.1.2.2.1 := by
  rcases entry with ⟨⟨dir, T, M⟩, C⟩
  cases dir
  · exact ⟨rfl, hmatch⟩
  · exact ⟨hmatch, rfl⟩

theorem pinnedIO_fwdP (x : TQ n cap tcap) (y : TM n cap)
    (hdir : x.1 = .fwd) :
    TweakablePRP.pinnedIO x y = (x.2.2, y) := by
  rcases x with ⟨dir, T, M⟩
  cases dir <;> simp_all [TweakablePRP.pinnedIO]

theorem pinnedIO_invP (x : TQ n cap tcap) (y : TM n cap)
    (hdir : x.1 = .inv) :
    TweakablePRP.pinnedIO x y = (y, x.2.2) := by
  rcases x with ⟨dir, T, M⟩
  cases dir <;> simp_all [TweakablePRP.pinnedIO]

theorem transcriptOfPairs_query_getP
    (l : List (TQ n cap tcap × TM n cap)) (i : Fin l.length) :
    (TweakablePRP.transcriptOfPairs l).1.get i = (l.get i).1 := by
  simp [TweakablePRP.transcriptOfPairs, List.Vector.get]

theorem transcriptOfPairs_response_getP
    (l : List (TQ n cap tcap × TM n cap)) (i : Fin l.length) :
    (TweakablePRP.transcriptOfPairs l).2.get i = (l.get i).2 := by
  simp [TweakablePRP.transcriptOfPairs, List.Vector.get]

theorem later_input_share_falseP
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap))
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (t : List (TQ n cap tcap × Option (TM n cap)))
    (hcon : ∀ k (hk : k < t.length),
      e (PFunDDS.transcriptOutputs (t.take k)) = some t[k].1)
    (r s : ℕ) (hrs : r < s)
    (er es : TQ n cap tcap × TM n cap)
    (hr : (PFunDDS.answeredEntries t)[r]? = some er)
    (hs : (PFunDDS.answeredEntries t)[s]? = some es)
    (hmr : er.2.1 = er.1.2.2.1)
    (hms : es.2.1 = es.1.2.2.1)
    (hT : er.1.2.1 = es.1.2.1)
    (hshare :
      (es.1.1 = .fwd ∧ plainMessageP er = plainMessageP es) ∨
        (es.1.1 = .inv ∧ cipherMessageP er = cipherMessageP es)) :
    False := by
  obtain ⟨pre, post, ht, hanswered⟩ :=
    answeredEntries_get_decomposeP t s es hs
  subst t
  let v : TM n cap :=
    match es.1.1 with
    | .fwd => cipherMessageP er
    | .inv => plainMessageP er
  let t' := pre ++ [(es.1, some v)]
  have hcon' : ∀ k (hk : k < t'.length),
      e (PFunDDS.transcriptOutputs (t'.take k)) = some t'[k].1 := by
    intro k hk
    have hk' : k ≤ pre.length := by
      simpa [t'] using hk
    by_cases hlt : k < pre.length
    · have hold := hcon k (by simp; omega)
      simpa [t', List.take_append_of_le_length (Nat.le_of_lt hlt),
        List.getElem_append_left hlt] using hold
    · have hkEq : k = pre.length := by omega
      subst k
      have hold := hcon pre.length (by simp)
      simpa [t'] using hold
  have hnp : TweakablePRP.NPList (PFunDDS.answeredEntries t') :=
    hE t' hcon'
  have hslen : s < (PFunDDS.answeredEntries
      (pre ++ (es.1, some es.2) :: post)).length :=
    (List.getElem?_eq_some_iff.mp hs).choose
  have hpreAnsLen : (PFunDDS.answeredEntries pre).length = s := by
    rw [hanswered, List.length_take, Nat.min_eq_left (Nat.le_of_lt hslen)]
  have hrpre : (PFunDDS.answeredEntries pre)[r]? = some er := by
    rw [hanswered]
    simpa [List.getElem?_take, hrs] using hr
  let pairs := PFunDDS.answeredEntries pre ++ [(es.1, v)]
  have hnp' : TweakablePRP.NPList pairs := by
    simpa [pairs, t', PFunDDS.answeredEntries] using hnp
  let rr : Fin pairs.length :=
    ⟨r, by simp [pairs, hpreAnsLen]; omega⟩
  let ss : Fin pairs.length :=
    ⟨s, by simp [pairs, hpreAnsLen]⟩
  have hrlt : r < (PFunDDS.answeredEntries pre).length := by
    rw [hpreAnsLen]
    exact hrs
  have hrget : (PFunDDS.answeredEntries pre)[r] = er := by
    rw [List.getElem?_eq_getElem hrlt] at hrpre
    exact Option.some.inj hrpre
  have hgetr : pairs.get rr = er := by
    rw [List.get_eq_getElem]
    simp [pairs, rr, List.getElem_append_left hrlt, hrget]
  have hgets : pairs.get ss = (es.1, v) := by
    rw [List.get_eq_getElem]
    simp [pairs, ss, hpreAnsLen]
  have hvlen : v.1 = es.1.2.2.1 := by
    obtain ⟨hplainLen, hcipherLen⟩ := message_lengthsP er hmr
    rcases hshare with ⟨hdir, hP⟩ | ⟨hdir, hC⟩
    · calc
        v.1 = (cipherMessageP er).1 := by simp [v, hdir]
        _ = (plainMessageP er).1 := hcipherLen.trans hplainLen.symm
        _ = (plainMessageP es).1 := congrArg Sigma.fst hP
        _ = es.1.2.2.1 := (message_lengthsP es hms).1
    · calc
        v.1 = (plainMessageP er).1 := by simp [v, hdir]
        _ = (cipherMessageP er).1 := hplainLen.trans hcipherLen.symm
        _ = (cipherMessageP es).1 := congrArg Sigma.fst hC
        _ = es.1.2.2.1 := (message_lengthsP es hms).2
  have hpins : TweakablePRP.pinnedIO es.1 v =
      TweakablePRP.pinnedIO er.1 er.2 := by
    rw [pinnedIO_eq_messagesP er]
    rcases hshare with ⟨hdir, hP⟩ | ⟨hdir, hC⟩
    · rw [pinnedIO_fwdP es.1 v hdir]
      apply Prod.ext
      · have hplain := (pinnedIO_fwdP es.1 es.2 hdir).symm.trans
          (pinnedIO_eq_messagesP es)
        exact (congrArg Prod.fst hplain).trans hP.symm
      · simp [v, hdir]
    · rw [pinnedIO_invP es.1 v hdir]
      apply Prod.ext
      · simp [v, hdir]
      · have hcipher := (pinnedIO_invP es.1 es.2 hdir).symm.trans
          (pinnedIO_eq_messagesP es)
        exact (congrArg Prod.snd hcipher).trans hC.symm
  have heq : rr = ss := hnp'.2 rr ss
    (by rw [transcriptOfPairs_query_getP, transcriptOfPairs_query_getP,
      hgetr, hgets]; exact hT)
    (by rw [transcriptOfPairs_response_getP, transcriptOfPairs_query_getP,
      hgetr]; exact hmr)
    (by rw [transcriptOfPairs_response_getP, transcriptOfPairs_query_getP,
      hgets]; exact hvlen)
    (by rw [transcriptOfPairs_query_getP, transcriptOfPairs_response_getP,
      transcriptOfPairs_query_getP, transcriptOfPairs_response_getP,
      hgetr, hgets]; exact hpins.symm)
  exact (Nat.ne_of_lt hrs) (congrArg Fin.val heq)

theorem prop1_cardP (bf : Hash.BlockField F n)
    (T : Tweak tcap) (M : BitString k) (g : BitString n)
    (hcap : 2 * T.len + 3 < 2 ^ n) :
    (Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T M = g).card ≤ Poly.d n T.len k := by
  letI := Classical.decEq F
  have h := Poly.Facts.prop1 bf T M g hcap
  rw [Dist.uniform_mass_eq_card_filter, Bits.Facts.card_Str] at h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T M = g).card : ℝ) ≤ Poly.d n T.len k := by
    exact (div_le_div_iff_of_pos_right hpos).mp (by simpa using h)
  exact_mod_cast hcast

theorem prop2_cardP (bf : Hash.BlockField F n)
    (hcap : 2 * tcap + 3 < 2 ^ n)
    (T₁ : Tweak tcap) (M₁ : BitString k₁) (T₂ : Tweak tcap) (M₂ : BitString k₂)
    (hne : ((T₁, ⟨k₁, M₁⟩) : Tweak tcap × Σ k : ℕ, BitString k) ≠
      (T₂, ⟨k₂, M₂⟩)) (g : BitString n) :
    (Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T₁ M₁ ^^^ hashBits bf hbar T₂ M₂ = g).card ≤
        max (Poly.d n T₁.len k₁) (Poly.d n T₂.len k₂) := by
  letI := Classical.decEq F
  have h := Poly.Facts.prop2 bf hcap T₁ M₁ T₂ M₂ hne g
  rw [Dist.uniform_mass_eq_card_filter, Bits.Facts.card_Str] at h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T₁ M₁ ^^^ hashBits bf hbar T₂ M₂ = g).card : ℝ) ≤
      max (Poly.d n T₁.len k₁) (Poly.d n T₂.len k₂) := by
    exact (div_le_div_iff_of_pos_right hpos).mp (by simpa using h)
  exact_mod_cast hcast

theorem prop3_cardP (bf : Hash.BlockField F n)
    (T : Tweak tcap) (M : BitString k) (g : BitString n)
    (hcap : 2 * T.len + 3 < 2 ^ n) :
    (Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T M ^^^ hbar = g).card ≤ Poly.d n T.len k := by
  letI := Classical.decEq F
  have h := Poly.Facts.prop3 bf T M g hcap
  rw [Dist.uniform_mass_eq_card_filter, Bits.Facts.card_Str] at h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((Finset.univ.filter fun hbar : BitString n =>
      hashBits bf hbar T M ^^^ hbar = g).card : ℝ) ≤ Poly.d n T.len k := by
    exact (div_le_div_iff_of_pos_right hpos).mp (by simpa using h)
  exact_mod_cast hcast

theorem xor_right_cancelP {x y c : BitString n} (h : x ^^^ c = y ^^^ c) :
    x = y := by
  have h' := congrArg (fun z => z ^^^ c) h
  simpa [BitVec.xor_assoc] using h'

theorem xor_left_cancelP {x y c : BitString n} (h : c ^^^ x = c ^^^ y) :
    x = y := by
  apply xor_right_cancelP (c := c)
  calc
    x ^^^ c = c ^^^ x := BitVec.xor_comm _ _
    _ = c ^^^ y := h
    _ = y ^^^ c := BitVec.xor_comm _ _

def plainHashInputP (entry : TQ n cap tcap × TM n cap) :
    Tweak tcap × Σ k : ℕ, BitString k :=
  (entry.1.2.1, ⟨entry.1.2.2.1.val, (plainPartsP entry).2⟩)

def cipherHashInputP (entry : TQ n cap tcap × TM n cap) :
    Tweak tcap × Σ k : ℕ, BitString k :=
  (entry.1.2.1, ⟨entry.1.2.2.1.val, (cipherPartsP entry).2⟩)

def evalHashInputP (bf : Hash.BlockField F n) (hbar : BitString n)
    (p : Tweak tcap × Σ k : ℕ, BitString k) : BitString n :=
  hashBits bf hbar p.1 p.2.2

theorem eval_plainHashInputP (bf : Hash.BlockField F n) (hbar : BitString n)
    (entry : TQ n cap tcap × TM n cap) :
    evalHashInputP bf hbar (plainHashInputP entry) =
      hashBits bf hbar entry.1.2.1 (plainPartsP entry).2 := rfl

theorem eval_cipherHashInputP (bf : Hash.BlockField F n) (hbar : BitString n)
    (entry : TQ n cap tcap × TM n cap) :
    evalHashInputP bf hbar (cipherHashInputP entry) =
      hashBits bf hbar entry.1.2.1 (cipherPartsP entry).2 := rfl

theorem plainMessage_eq_partsP (entry : TQ n cap tcap × TM n cap)
    (hmatch : entry.2.1 = entry.1.2.2.1) :
    plainMessageP entry =
      ⟨entry.1.2.2.1, (plainPartsP entry).1 ∥ (plainPartsP entry).2⟩ := by
  rcases entry with ⟨⟨dir, T, ⟨j, Q⟩⟩, ⟨j', Y⟩⟩
  cases dir
  · simp only [plainMessageP, plainPartsP]
    exact Sigma.ext rfl (by simpa using (Bits.Facts.cat_sub_sub Q).symm)
  · dsimp only at hmatch
    subst j'
    simp only [plainMessageP, plainPartsP]
    exact Sigma.ext rfl (by simpa using (Bits.Facts.cat_sub_sub Y).symm)

theorem cipherMessage_eq_partsP (entry : TQ n cap tcap × TM n cap)
    (hmatch : entry.2.1 = entry.1.2.2.1) :
    cipherMessageP entry =
      ⟨entry.1.2.2.1, (cipherPartsP entry).1 ∥ (cipherPartsP entry).2⟩ := by
  rcases entry with ⟨⟨dir, T, ⟨j, Q⟩⟩, ⟨j', Y⟩⟩
  cases dir
  · dsimp only at hmatch
    subst j'
    simp only [cipherMessageP, cipherPartsP]
    exact Sigma.ext rfl (by simpa using (Bits.Facts.cat_sub_sub Y).symm)
  · simp only [cipherMessageP, cipherPartsP]
    exact Sigma.ext rfl (by simpa using (Bits.Facts.cat_sub_sub Q).symm)

theorem plainMessage_eq_of_hash_input_mmP (bf : Hash.BlockField F n)
    (hbar : BitString n) (er es : TQ n cap tcap × TM n cap)
    (hmr : er.2.1 = er.1.2.2.1) (hms : es.2.1 = es.1.2.2.1)
    (hdesc : plainHashInputP er = plainHashInputP es)
    (hmm : mmP bf hbar er = mmP bf hbar es) :
    plainMessageP er = plainMessageP es := by
  have hhash := congrArg (evalHashInputP bf hbar) hdesc
  rw [eval_plainHashInputP, eval_plainHashInputP] at hhash
  have hhead : (plainPartsP er).1 = (plainPartsP es).1 := by
    unfold mmP at hmm
    rw [hhash] at hmm
    exact xor_right_cancelP (c :=
      hashBits bf hbar es.1.2.1 (plainPartsP es).2) hmm
  rw [plainMessage_eq_partsP er hmr, plainMessage_eq_partsP es hms]
  have htail := congrArg Prod.snd hdesc
  have hj : er.1.2.2.1 = es.1.2.2.1 :=
    Fin.ext (congrArg Sigma.fst htail)
  have hpair :
      ((plainPartsP er).1,
        (⟨er.1.2.2.1.val, (plainPartsP er).2⟩ : Σ k : ℕ, BitString k)) =
      ((plainPartsP es).1,
        (⟨es.1.2.2.1.val, (plainPartsP es).2⟩ : Σ k : ℕ, BitString k)) :=
    Prod.ext hhead htail
  have hcat := congrArg (fun p : BitString n × (Σ k : ℕ, BitString k) =>
      (⟨n + p.2.1, p.1 ∥ p.2.2⟩ : Σ w : ℕ, BitString w)) hpair
  have hbits : HEq
      ((plainPartsP er).1 ∥ (plainPartsP er).2)
      ((plainPartsP es).1 ∥ (plainPartsP es).2) :=
    (Sigma.ext_iff.mp hcat).2
  exact Sigma.ext hj hbits

theorem cipherMessage_eq_of_hash_input_uuP (bf : Hash.BlockField F n)
    (hbar : BitString n) (er es : TQ n cap tcap × TM n cap)
    (hmr : er.2.1 = er.1.2.2.1) (hms : es.2.1 = es.1.2.2.1)
    (hdesc : cipherHashInputP er = cipherHashInputP es)
    (huu : uuP bf hbar er = uuP bf hbar es) :
    cipherMessageP er = cipherMessageP es := by
  have hhash := congrArg (evalHashInputP bf hbar) hdesc
  rw [eval_cipherHashInputP, eval_cipherHashInputP] at hhash
  have hhead : (cipherPartsP er).1 = (cipherPartsP es).1 := by
    unfold uuP at huu
    rw [hhash] at huu
    exact xor_right_cancelP (c :=
      hashBits bf hbar es.1.2.1 (cipherPartsP es).2) huu
  rw [cipherMessage_eq_partsP er hmr, cipherMessage_eq_partsP es hms]
  have htail := congrArg Prod.snd hdesc
  have hj : er.1.2.2.1 = es.1.2.2.1 :=
    Fin.ext (congrArg Sigma.fst htail)
  have hpair :
      ((cipherPartsP er).1,
        (⟨er.1.2.2.1.val, (cipherPartsP er).2⟩ : Σ k : ℕ, BitString k)) =
      ((cipherPartsP es).1,
        (⟨es.1.2.2.1.val, (cipherPartsP es).2⟩ : Σ k : ℕ, BitString k)) :=
    Prod.ext hhead htail
  have hcat := congrArg (fun p : BitString n × (Σ k : ℕ, BitString k) =>
      (⟨n + p.2.1, p.1 ∥ p.2.2⟩ : Σ w : ℕ, BitString w)) hpair
  have hbits : HEq
      ((cipherPartsP er).1 ∥ (cipherPartsP er).2)
      ((cipherPartsP es).1 ∥ (cipherPartsP es).2) :=
    (Sigma.ext_iff.mp hcat).2
  exact Sigma.ext hj hbits

theorem coinObs_response_lengthP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some entry) :
    entry.2.1 = entry.1.2.2.1 := by
  have h := coinObs_response_eqP hn q σ e m w s entry.1 entry.2 hsel
  exact (congrArg Sigma.fst h).symm

theorem coinObs_raw_consistentP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) :
    ∀ k (hk : k < (coinObsP hn q σ e m w).1.length),
      e (PFunDDS.transcriptOutputs
        ((coinObsP hn q σ e m w).1.take k)) =
        some (coinObsP hn q σ e m w).1[k].1 := by
  simpa [coinObsP, augRnd, rndDDS] using
    (transcript_consistent
      (rndDDS n cap tcap q σ (coinKeyP hn w).1) e m).1.1

theorem plainHashInput_ne_of_mmP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (r s : ℕ) (hrs : r < s)
    (er es : TQ n cap tcap × TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some es)
    (hdir : es.1.1 = .fwd)
    (hmm : mmP bf (coinObsP hn q σ e m w).2.1.1 er =
      mmP bf (coinObsP hn q σ e m w).2.1.1 es) :
    plainHashInputP er ≠ plainHashInputP es := by
  intro hdesc
  have hmr := coinObs_response_lengthP hn q σ e m w r er hr
  have hms := coinObs_response_lengthP hn q σ e m w s es hs
  exact later_input_share_falseP e hE
    (coinObsP hn q σ e m w).1
    (coinObs_raw_consistentP hn q σ e m w)
    r s hrs er es hr hs hmr hms
    (congrArg (fun p => p.1) hdesc)
    (Or.inl ⟨hdir,
      plainMessage_eq_of_hash_input_mmP bf
        (coinObsP hn q σ e m w).2.1.1 er es hmr hms hdesc hmm⟩)

theorem cipherHashInput_ne_of_uuP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (r s : ℕ) (hrs : r < s)
    (er es : TQ n cap tcap × TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some es)
    (hdir : es.1.1 = .inv)
    (huu : uuP bf (coinObsP hn q σ e m w).2.1.1 er =
      uuP bf (coinObsP hn q σ e m w).2.1.1 es) :
    cipherHashInputP er ≠ cipherHashInputP es := by
  intro hdesc
  have hmr := coinObs_response_lengthP hn q σ e m w r er hr
  have hms := coinObs_response_lengthP hn q σ e m w s es hs
  exact later_input_share_falseP e hE
    (coinObsP hn q σ e m w).1
    (coinObs_raw_consistentP hn q σ e m w)
    r s hrs er es hr hs hmr hms
    (congrArg (fun p => p.1) hdesc)
    (Or.inr ⟨hdir,
      cipherMessage_eq_of_hash_input_uuP bf
        (coinObsP hn q σ e m w).2.1.1 er es hmr hms hdesc huu⟩)

theorem coinKey_leftover_offP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n)
    (x : TQ n cap tcap) (hx : x ≠ z) :
    (coinKeyP hn (coinUpdateP w (.inr ⟨z, b⟩) v)).2.2 x =
      (coinKeyP hn w).2.2 x := by
  classical
  unfold coinKeyP coinUpdateP rndKeyCoinEquivP packCoinBlocksP
    rndKeyBlockEquivP
  change ((queryCoinsEquivP hn x).symm
      (fun k => Function.update w (.inr ⟨z, b⟩) v (.inr ⟨x, k⟩))).2 =
    ((queryCoinsEquivP hn x).symm (fun k => w (.inr ⟨x, k⟩))).2
  congr 2
  funext k
  rw [Function.update_of_ne]
  intro heq
  have hxz : x = z := congrArg (fun p : CoinIndexP n cap tcap =>
    match p with
    | .inl _ => z
    | .inr idx => idx.1) heq
  exact hx hxz

theorem query_ne_of_beforeP
    (entries : List (TQ n cap tcap × TM n cap))
    (hnp : TweakablePRP.NPList entries)
    (r s : ℕ) (hrs : r < s)
    (er es : TQ n cap tcap × TM n cap)
    (hr : entries[r]? = some er) (hs : entries[s]? = some es) :
    er.1 ≠ es.1 := by
  have hnodup := query_nodup_of_npListP entries hnp
  rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
  have hslen : s < entries.length :=
    (List.getElem?_eq_some_iff.mp hs).choose
  intro heq
  apply hnodup r s hrs (by simpa using hslen)
  simp [List.getElem?_map, hr, hs, heq]

theorem coinObs_entry_before_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (r : ℕ) (hrs : r < s) (er : TQ n cap tcap × TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er) :
    (transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inr ⟨z, b⟩) v)).1)[r]? = some er := by
  have hp := coinObs_entries_update_prefixP hn q σ e m hE w z b v s y hs
  have hg := congrArg (fun l => l[r]?) hp
  have hslen : s < (transcriptEntries (coinObsP hn q σ e m w).1).length :=
    (List.getElem?_eq_some_iff.mp hs).choose
  have hrlen : r < (transcriptEntries (coinObsP hn q σ e m w).1).length :=
    lt_trans hrs hslen
  have hrget : (transcriptEntries (coinObsP hn q σ e m w).1)[r] = er := by
    rw [List.getElem?_eq_getElem hrlen] at hr
    exact Option.some.inj hr
  simp [List.getElem?_take, List.getElem?_append, hrs, hr,
    hrget, Nat.min_eq_left (Nat.le_of_lt hslen)] at hg
  exact hg.2

theorem coinObs_zip_before_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) (s : ℕ) (y : TM n cap)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (r : ℕ) (hrs : r < s) (er : TQ n cap tcap × TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er) :
    (((transcriptEntries (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)).1).zip
      (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)).2.2)[r]?) =
      some (er, (⟨padLen n er.1.2.2.1.val - er.1.2.2.1.val,
        (coinKeyP hn w).2.2 er.1⟩ : Σ width : ℕ, BitString width)) := by
  have hnp : TweakablePRP.NPList
      (transcriptEntries (coinObsP hn q σ e m w).1) :=
    hE _ (coinObs_raw_consistentP hn q σ e m w)
  have hne := query_ne_of_beforeP _ hnp r s hrs er (z, y) hr hs
  have hr' := coinObs_entry_before_updateP hn q σ e m hE
    w z b v s y hs r hrs er hr
  have hz := coinObs_zip_getP hn q σ e m
    (coinUpdateP w (.inr ⟨z, b⟩) v) r er.1 er.2 hr'
  rw [coinKey_leftover_offP hn w z b v er.1 hne] at hz
  exact hz

theorem coinKey_response_tail_head_updateP (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap) (v : BitString n) :
    ((coinKeyP hn (coinUpdateP w
      (.inr ⟨z, ⟨0, by simp [queryChargeP]⟩⟩) v)).1 z)[n; z.2.2.1.val] =
      ((coinKeyP hn w).1 z)[n; z.2.2.1.val] := by
  classical
  let b0 : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  change ((coinKeyP hn (coinUpdateP w (.inr ⟨z, b0⟩) v)).1 z)[
      n; z.2.2.1.val] = ((coinKeyP hn w).1 z)[n; z.2.2.1.val]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hk : p / n < numBlocks n z.2.2.1.val := by
    have hpPad : p < padLen n z.2.2.1.val :=
      lt_of_lt_of_le hp (le_padLen hn z.2.2.1.val)
    rw [padLen_eq_mul] at hpPad
    exact (Nat.div_lt_iff_lt_mul hn).2
      (by simpa [Nat.mul_comm] using hpPad)
  let k : Fin (numBlocks n z.2.2.1.val) := ⟨p / n, hk⟩
  let bt : Fin (queryChargeP z) :=
    ⟨k.val + 1, by simp [queryChargeP]; omega⟩
  have hbne : (Sum.inr ⟨z, bt⟩ : CoinIndexP n cap tcap) ≠
      Sum.inr ⟨z, b0⟩ := by
    intro h
    have hv := congrArg (fun c : CoinIndexP n cap tcap =>
      match c with
      | .inl _ => 0
      | .inr x => x.2.val) h
    simp [bt, b0] at hv
  have hnew := coinKey_response_tail_blockP hn
    (coinUpdateP w (.inr ⟨z, b0⟩) v) z k
  have hold := coinKey_response_tail_blockP hn w z k
  rw [show (⟨k.val + 1, by simp [queryChargeP]; omega⟩ :
      Fin (queryChargeP z)) = bt by rfl] at hnew hold
  rw [coinUpdateP, Function.update_of_ne hbne] at hnew
  have hblock := hnew.trans hold.symm
  have hbit := congrArg (fun x : BitString n => x.getLsbD (p % n)) hblock
  simp only [blocksTake, List.get_ofFn, substring,
    BitVec.getLsbD_extractLsb'] at hbit
  have hpmod : p % n < n := Nat.mod_lt p hn
  have hidx : n * (p / n) + p % n = p := by
    simpa [Nat.add_comm] using Nat.mod_add_div p n
  simpa [substring, BitVec.getLsbD_extractLsb', k, hpmod, hp, hidx] using hbit

@[simp] theorem coinObs_hbar_L_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) :
    (coinObsP hn q σ e m (coinUpdateP w (.inl true) v)).2.1.1 =
      (coinObsP hn q σ e m w).2.1.1 := by
  simp [coinObsP, augRnd, coinUpdateP]

@[simp] theorem coinObs_L_hbar_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) :
    (coinObsP hn q σ e m (coinUpdateP w (.inl false) v)).2.1.2 =
      (coinObsP hn q σ e m w).2.1.2 := by
  simp [coinObsP, augRnd, coinUpdateP]

theorem blockValue_head_hbar_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) (d : Bool) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries (coinObsP hn q σ e m w).1).zip
      (coinObsP hn q σ e m w).2.2)[s]?) = some (entry, D)) :
    blockValueP bf (coinObsP hn q σ e m
      (coinUpdateP w (.inl false) v)) d s 0 =
      if d then mmP bf v entry else uuP bf v entry := by
  have hzip' : (((transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inl false) v)).1).zip
      (coinObsP hn q σ e m (coinUpdateP w (.inl false) v)).2.2)[s]?) =
      some (entry, D) := by
    rw [coinObs_zip_terminalP hn q σ e m w false v]
    exact hzip
  rw [blockValue_headP bf _ d s entry D hzip']
  simp

theorem blockValue_head_L_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) (d : Bool) (s : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries (coinObsP hn q σ e m w).1).zip
      (coinObsP hn q σ e m w).2.2)[s]?) = some (entry, D)) :
    blockValueP bf (coinObsP hn q σ e m
      (coinUpdateP w (.inl true) v)) d s 0 =
      if d then mmP bf (coinObsP hn q σ e m w).2.1.1 entry
      else uuP bf (coinObsP hn q σ e m w).2.1.1 entry := by
  have hzip' : (((transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inl true) v)).1).zip
      (coinObsP hn q σ e m (coinUpdateP w (.inl true) v)).2.2)[s]?) =
      some (entry, D) := by
    rw [coinObs_zip_terminalP hn q σ e m w true v]
    exact hzip
  rw [blockValue_headP bf _ d s entry D hzip']
  simp

theorem blockValue_tail_input_L_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) (s k : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries (coinObsP hn q σ e m w).1).zip
      (coinObsP hn q σ e m w).2.2)[s]?) = some (entry, D)) :
    blockValueP bf (coinObsP hn q σ e m
      (coinUpdateP w (.inl true) v)) true s (k + 1) =
      mmP bf (coinObsP hn q σ e m w).2.1.1 entry ^^^
        uuP bf (coinObsP hn q σ e m w).2.1.1 entry ^^^ v ^^^
          bin n (k + 1) := by
  have hzip' : (((transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inl true) v)).1).zip
      (coinObsP hn q σ e m (coinUpdateP w (.inl true) v)).2.2)[s]?) =
      some (entry, D) := by
    rw [coinObs_zip_terminalP hn q σ e m w true v]
    exact hzip
  rw [blockValue_tail_inputP bf _ s k entry D hzip']
  simp [ssP]

theorem blockValue_tail_output_terminalP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (a : Bool) (v : BitString n) (s k : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries (coinObsP hn q σ e m w).1).zip
      (coinObsP hn q σ e m w).2.2)[s]?) = some (entry, D))
    (hk : k < (yBlocksP entry D).length) :
    blockValueP bf (coinObsP hn q σ e m
      (coinUpdateP w (.inl a) v)) false s (k + 1) =
      (yBlocksP entry D).get ⟨k, hk⟩ := by
  have hzip' : (((transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inl a) v)).1).zip
      (coinObsP hn q σ e m (coinUpdateP w (.inl a) v)).2.2)[s]?) =
      some (entry, D) := by
    rw [coinObs_zip_terminalP hn q σ e m w a v]
    exact hzip
  exact blockValue_tail_outputP bf _ s k entry D hzip' hk

theorem mm_response_head_invP (bf : Hash.BlockField F n) (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap) (v : BitString n)
    (hdir : z.1 = .inv) :
    mmP bf (coinKeyP hn w).2.1.1
      (z, rndFun (coinKeyP hn (coinUpdateP w
        (.inr ⟨z, ⟨0, by simp [queryChargeP]⟩⟩) v)).1 z) =
      v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
        ((coinKeyP hn w).1 z)[n; z.2.2.1.val] := by
  rcases z with ⟨dir, T, j, Q⟩
  cases dir
  · simp at hdir
  · simp only [mmP, plainPartsP, rndFun]
    rw [coinKey_response_head_updateP, coinKey_response_tail_head_updateP]

theorem uu_response_head_fwdP (bf : Hash.BlockField F n) (hn : 0 < n)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap) (v : BitString n)
    (hdir : z.1 = .fwd) :
    uuP bf (coinKeyP hn w).2.1.1
      (z, rndFun (coinKeyP hn (coinUpdateP w
        (.inr ⟨z, ⟨0, by simp [queryChargeP]⟩⟩) v)).1 z) =
      v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
        ((coinKeyP hn w).1 z)[n; z.2.2.1.val] := by
  rcases z with ⟨dir, T, j, Q⟩
  cases dir
  · simp only [uuP, cipherPartsP, rndFun]
    rw [coinKey_response_head_updateP, coinKey_response_tail_head_updateP]
  · simp at hdir

theorem collision_fiber_seedSeedP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j a b : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.seedSeed a b)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  let o := coinObsP hn q σ e m w
  have hlabels := collisionCellAt_labelsP bf o d i j (.seedSeed a b)
    (by simpa [o] using hcell)
  have hva := label_at_valid bf o d hn hlabels.2.1
  have hvb := label_at_valid bf o d hn hlabels.2.2
  have hbefore := collisionCellAt_beforeP bf o d hn i j (.seedSeed a b)
    (by simpa [o] using hcell)
  have hab : a = 0 ∧ b = 1 := by
    simp only [CollisionCell.origins, Origin.Valid] at hva hvb
    simp only [CollisionCell.origins, Origin.BeforeP] at hbefore
    omega
  rcases hab with ⟨rfl, rfl⟩
  cases d with
  | false =>
      have hloc : collisionLocP bf hn q σ e m false i j w = .inl true := by
        simp [collisionLocP, hcell]
      rw [costAt, hcell]
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Finset.card_le_one]
      intro v₁ hv₁ v₂ hv₂
      have hcoll₁ := (Finset.mem_filter.mp hv₁).2
      have hcoll₂ := (Finset.mem_filter.mp hv₂).2
      have hcell₁ : collisionCellAt bf
          (coinObsP hn q σ e m (coinUpdateP w (.inl true) v₁)) false i j =
          some (.seedSeed 0 1) := by
        rw [← hloc, collisionCell_self_updateP bf hn q σ e m hE, hcell]
      have hcell₂ : collisionCellAt bf
          (coinObsP hn q σ e m (coinUpdateP w (.inl true) v₂)) false i j =
          some (.seedSeed 0 1) := by
        rw [← hloc, collisionCell_self_updateP bf hn q σ e m hE, hcell]
      have heq₁ := pairCollision_cell_valuesP bf _ false hn i j
        (.seedSeed 0 1) hcell₁ (by simpa [coinBadValuesP, hloc] using hcoll₁)
      have heq₂ := pairCollision_cell_valuesP bf _ false hn i j
        (.seedSeed 0 1) hcell₂ (by simpa [coinBadValuesP, hloc] using hcoll₂)
      have heq₁' : (coinObsP hn q σ e m w).2.1.1 = v₁ := by
        simpa [CollisionCell.origins, originValueP] using heq₁
      have heq₂' : (coinObsP hn q σ e m w).2.1.1 = v₂ := by
        simpa [CollisionCell.origins, originValueP] using heq₂
      exact heq₁'.symm.trans heq₂'
  | true =>
      have hloc : collisionLocP bf hn q σ e m true i j w = .inl false := by
        simp [collisionLocP, hcell]
      rw [costAt, hcell]
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      simp only [↓reduceIte]
      have hz : (coinBadValuesP bf hn q σ e m true i j
          (collisionLocP bf hn q σ e m true i j) w).card = 0 := by
        rw [Finset.card_eq_zero]
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨v, hv⟩
        have hcoll := (Finset.mem_filter.mp hv).2
        have hcellv : collisionCellAt bf
            (coinObsP hn q σ e m (coinUpdateP w (.inl false) v)) true i j =
            some (.seedSeed 0 1) := by
          rw [← hloc, collisionCell_self_updateP bf hn q σ e m hE, hcell]
        have heq := pairCollision_cell_valuesP bf _ true hn i j
          (.seedSeed 0 1) hcellv (by simpa [coinBadValuesP, hloc] using hcoll)
        have h01 : (0 : ℕ) < 2 ^ n := by positivity
        have h11 : (1 : ℕ) < 2 ^ n :=
          Nat.one_lt_two_pow (by omega)
        exact (by omega : (0 : ℕ) ≠ 1)
          (Bits.Facts.bin_inj h01 h11 (by
            simpa [CollisionCell.origins, originValueP] using heq))
      omega

/-- Membership in the selected-coordinate fiber, rewritten as the semantic
collision equation for the cell already reconstructed at the base point. -/
theorem coinBadValues_cell_valuesP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap)
    (cell : CollisionCell)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j = some cell)
    {v : BitString n}
    (hv : v ∈ coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w) :
    originValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v)) d
        cell.origins.1 =
    originValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v)) d
        cell.origins.2 := by
  classical
  have hcoll := (Finset.mem_filter.mp hv).2
  have hcellv : collisionCellAt bf (coinObsP hn q σ e m
      (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v)) d i j =
      some cell := by
    rw [collisionCell_self_updateP bf hn q σ e m hE, hcell]
  exact pairCollision_cell_valuesP bf _ d hn i j cell hcellv hcoll

theorem collision_fiber_headSeedP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j s a : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.headSeed s a)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  have hbefore := collisionCellAt_beforeP bf
    (coinObsP hn q σ e m w) d hn i j (.headSeed s a) hcell
  simp [CollisionCell.origins, Origin.BeforeP] at hbefore

theorem collision_fiber_tailSeedP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (d : Bool) (i j s k a : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.tailSeed s k a)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  have hbefore := collisionCellAt_beforeP bf
    (coinObsP hn q σ e m w) d hn i j (.tailSeed s k a) hcell
  simp [CollisionCell.origins, Origin.BeforeP] at hbefore

theorem answered_get_of_entryP
    (o : AugObs n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y)) :
    (answered o)[s]? = some z := by
  rw [answered, ← PFunDDS.answeredEntries_map_fst]
  simp [List.getElem?_map, hsel]

theorem degOf_eq_of_entryP
    (o : AugObs n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y)) :
    degOf o s = Poly.d n z.2.1.len z.2.2.1.val := by
  simp [degOf, answered_get_of_entryP o s z y hsel]

theorem dirOf_eq_of_entryP
    (o : AugObs n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y)) :
    dirOf o s = match z.1 with
      | .fwd => true
      | .inv => false := by
  simp [dirOf, answered_get_of_entryP o s z y hsel]

theorem blockValue_tail_output_response_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s k : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hk : k < numBlocks n z.2.2.1.val) (v : BitString n) :
    let b : Fin (queryChargeP z) :=
      ⟨k + 1, by simp [queryChargeP]; omega⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) false s (k + 1) =
      queryTailMaskP z k ^^^ v := by
  dsimp only
  let k' : Fin (numBlocks n z.2.2.1.val) := ⟨k, hk⟩
  let b : Fin (queryChargeP z) :=
    ⟨k + 1, by simp [queryChargeP]; omega⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let y' := rndFun (coinKeyP hn w').1 z
  let D : Σ width : ℕ, BitString width :=
    ⟨padLen n z.2.2.1.val - z.2.2.1.val, (coinKeyP hn w').2.2 z⟩
  have hsel' :
      (transcriptEntries (coinObsP hn q σ e m w').1)[s]? = some (z, y') := by
    exact coinObs_entry_update_getP hn q σ e m hE w z b v s y hsel
  have hzip' :
      (((transcriptEntries (coinObsP hn q σ e m w').1).zip
        (coinObsP hn q σ e m w').2.2)[s]?) = some ((z, y'), D) := by
    exact coinObs_zip_getP hn q σ e m w' s z y' hsel'
  have hk' : k < (yBlocksP (z, y') D).length := by
    simpa [yBlocksP, k'] using k'.isLt
  rw [blockValue_tail_outputP bf _ s k (z, y') D hzip' hk']
  simpa [w', b, k', D, y'] using yBlocks_coin_updateP hn w z k' v

@[simp] theorem coinObs_hbar_response_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) :
    (coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)).2.1.1 =
      (coinObsP hn q σ e m w).2.1.1 := by
  simp [coinObsP, augRnd, coinUpdateP]

@[simp] theorem coinObs_L_response_updateP (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (z : TQ n cap tcap)
    (b : Fin (queryChargeP z)) (v : BitString n) :
    (coinObsP hn q σ e m (coinUpdateP w (.inr ⟨z, b⟩) v)).2.1.2 =
      (coinObsP hn q σ e m w).2.1.2 := by
  simp [coinObsP, augRnd, coinUpdateP]

theorem collision_fiber_seedTailP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j a s k : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.seedTail a s k)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  have hlabels := collisionCellAt_labelsP bf
    (coinObsP hn q σ e m w) d i j (.seedTail a s k) hcell
  obtain ⟨z, y, hsel, hkentry⟩ := label_block_query_receiptP bf
    (coinObsP hn q σ e m w) d hn j s (k + 1) hlabels.2.2
  have hk : k < numBlocks n z.2.2.1.val := by
    rw [entryCharge_eq_queryChargeP hn (z, y)] at hkentry
    simp [queryChargeP] at hkentry
    omega
  let b : Fin (queryChargeP z) :=
    ⟨k + 1, by simp [queryChargeP]; omega⟩
  cases d with
  | false =>
      have hloc : collisionLocP bf hn q σ e m false i j w = .inr ⟨z, b⟩ := by
        rw [show collisionLocP bf hn q σ e m false i j w =
            responseCoinAtP (coinObsP hn q σ e m w) s (k + 1) by
          simp [collisionLocP, hcell]]
        exact responseCoinAt_eq_inrP _ s (k + 1) z y hsel b.isLt
      rw [costAt, hcell]
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      rw [Finset.card_le_one]
      intro v₁ hv₁ v₂ hv₂
      have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
        i j w (.seedTail a s k) hcell hv₁
      have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
        i j w (.seedTail a s k) hcell hv₂
      rw [hloc] at heq₁ heq₂
      simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
      rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
        w s k z y hsel hk v₁] at heq₁
      rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
        w s k z y hsel hk v₂] at heq₂
      simp only [coinObs_hbar_response_updateP,
        coinObs_L_response_updateP] at heq₁ heq₂
      exact xor_left_cancelP (heq₁.symm.trans heq₂)
  | true =>
      have hloc : collisionLocP bf hn q σ e m true i j w = .inl true := by
        simp [collisionLocP, hcell]
      have hzip := coinObs_zip_getP hn q σ e m w s z y hsel
      rw [costAt, hcell]
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      rw [Finset.card_le_one]
      intro v₁ hv₁ v₂ hv₂
      have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE true
        i j w (.seedTail a s k) hcell hv₁
      have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE true
        i j w (.seedTail a s k) hcell hv₂
      rw [hloc] at heq₁ heq₂
      simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
      rw [blockValue_tail_input_L_updateP bf hn q σ e m
        w v₁ s k (z, y) _ hzip] at heq₁
      rw [blockValue_tail_input_L_updateP bf hn q σ e m
        w v₂ s k (z, y) _ hzip] at heq₂
      have hcancel := xor_right_cancelP (heq₁.symm.trans heq₂)
      have hcancel' := xor_left_cancelP (by
        simpa only [BitVec.xor_assoc] using hcancel)
      exact xor_left_cancelP hcancel'

theorem solve_right_xorP {a b x : BitString n} (h : a = b ^^^ x) :
    x = b ^^^ a := by
  calc
    x = b ^^^ (b ^^^ x) := by
      rw [← BitVec.xor_assoc]
      simp
    _ = b ^^^ a := congrArg (fun z => b ^^^ z) h.symm

theorem xor_self_eq_of_eq_xorP {v b x : BitString n} (h : v = b ^^^ x) :
    x ^^^ v = b := by
  rw [h]
  calc
    x ^^^ (b ^^^ x) = (b ^^^ x) ^^^ x := by
      rw [BitVec.xor_comm]
    _ = b := by simp [BitVec.xor_assoc]

theorem blockValue_head_response_fwd_output_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hdir : z.1 = .fwd) (v : BitString n) :
    let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) false s 0 =
      v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
        ((coinKeyP hn w).1 z)[n; z.2.2.1.val] := by
  dsimp only
  let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let y' := rndFun (coinKeyP hn w').1 z
  let D : Σ width : ℕ, BitString width :=
    ⟨padLen n z.2.2.1.val - z.2.2.1.val, (coinKeyP hn w').2.2 z⟩
  have hsel' :
      (transcriptEntries (coinObsP hn q σ e m w').1)[s]? = some (z, y') := by
    exact coinObs_entry_update_getP hn q σ e m hE w z b v s y hsel
  have hzip' :
      (((transcriptEntries (coinObsP hn q σ e m w').1).zip
        (coinObsP hn q σ e m w').2.2)[s]?) = some ((z, y'), D) := by
    exact coinObs_zip_getP hn q σ e m w' s z y' hsel'
  rw [blockValue_headP bf _ false s (z, y') D hzip']
  simp only [Bool.false_eq_true, ↓reduceIte,
    coinObs_hbar_response_updateP]
  simpa [w', y', b] using uu_response_head_fwdP bf hn w z v hdir

theorem blockValue_head_response_inv_input_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hdir : z.1 = .inv) (v : BitString n) :
    let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) true s 0 =
      v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
        ((coinKeyP hn w).1 z)[n; z.2.2.1.val] := by
  dsimp only
  let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let y' := rndFun (coinKeyP hn w').1 z
  let D : Σ width : ℕ, BitString width :=
    ⟨padLen n z.2.2.1.val - z.2.2.1.val, (coinKeyP hn w').2.2 z⟩
  have hsel' :
      (transcriptEntries (coinObsP hn q σ e m w').1)[s]? = some (z, y') := by
    exact coinObs_entry_update_getP hn q σ e m hE w z b v s y hsel
  have hzip' :
      (((transcriptEntries (coinObsP hn q σ e m w').1).zip
        (coinObsP hn q σ e m w').2.2)[s]?) = some ((z, y'), D) := by
    exact coinObs_zip_getP hn q σ e m w' s z y' hsel'
  rw [blockValue_headP bf _ true s (z, y') D hzip']
  simp only [↓reduceIte, coinObs_hbar_response_updateP]
  simpa [w', y', b] using mm_response_head_invP bf hn w z v hdir

theorem queryDir_eq_fwd_of_dirOf_trueP
    (o : AugObs n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y))
    (hdir : dirOf o s = true) : z.1 = .fwd := by
  have hm := (dirOf_eq_of_entryP o s z y hsel).symm.trans hdir
  cases hz : z.1
  · rfl
  · simp [hz] at hm

theorem queryDir_eq_inv_of_dirOf_falseP
    (o : AugObs n cap tcap) (s : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries o.1)[s]? = some (z, y))
    (hdir : dirOf o s = false) : z.1 = .inv := by
  have hm := (dirOf_eq_of_entryP o s z y hsel).symm.trans hdir
  cases hz : z.1
  · simp [hz] at hm
  · rfl

theorem xor_pair_rearrangeP {a b x y : BitString n}
    (h : a ^^^ x = b ^^^ y) : x ^^^ y = a ^^^ b := by
  have h' := congrArg (fun z => z ^^^ y) h
  have h'' : a ^^^ (x ^^^ y) = b := by
    simpa [BitVec.xor_assoc] using h'
  exact solve_right_xorP h''.symm

theorem blockValue_head_before_response_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (r s : ℕ) (hrs : r < s)
    (er : TQ n cap tcap × TM n cap) (z : TQ n cap tcap) (y : TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (b : Fin (queryChargeP z)) (v : BitString n) (d : Bool) :
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) d r 0 =
      if d then mmP bf (coinObsP hn q σ e m w).2.1.1 er
      else uuP bf (coinObsP hn q σ e m w).2.1.1 er := by
  have hzip := coinObs_zip_before_updateP hn q σ e m hE
    w z b v s y hs r hrs er hr
  rw [blockValue_headP bf _ d r er _ hzip]
  simp

theorem collision_fiber_seedHeadP (bf : Hash.BlockField F n)
    (hn : 0 < n) (hTcap : 2 * tcap + 3 < 2 ^ n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j a s : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.seedHead a s)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  let o := coinObsP hn q σ e m w
  have hlabels := collisionCellAt_labelsP bf o d i j (.seedHead a s)
    (by simpa [o] using hcell)
  have hva := label_at_valid bf o d hn hlabels.2.1
  obtain ⟨z, y, hsel, -⟩ := label_block_query_receiptP bf o d hn
    j s 0 hlabels.2.2
  have hsel' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y) := by
    simpa [o] using hsel
  have hzip := coinObs_zip_getP hn q σ e m w s z y hsel'
  have hdirz := dirOf_eq_of_entryP
    (coinObsP hn q σ e m w) s z y hsel'
  let b₀ : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  cases d with
  | false =>
      by_cases hg : dirOf (coinObsP hn q σ e m w) s = false
      · have hz : z.1 = .inv :=
          queryDir_eq_inv_of_dirOf_falseP _ s z y hsel' hg
        have hloc : collisionLocP bf hn q σ e m false i j w = .inl false := by
          simp [collisionLocP, hcell, hg]
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [degOf_eq_of_entryP _ s z y hsel']
        have ha : a = 0 ∨ a = 1 := by
          simp only [CollisionCell.origins, Origin.Valid] at hva
          omega
        rcases ha with rfl | rfl
        · refine le_trans (Finset.card_le_card ?_)
            (prop3_cardP bf z.2.1 z.2.2.2[n; z.2.2.1.val]
              z.2.2.2[0; n] (cap_of_tweak z.2.1 hTcap))
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          have heq := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.seedHead 0 s) hcell hv
          rw [hloc] at heq
          simp only [CollisionCell.origins, originValueP,
            Bool.false_eq_true, ↓reduceIte] at heq
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v false s (z, y) _ hzip] at heq
          simp only [Bool.false_eq_true, ↓reduceIte] at heq
          have heq' : v = z.2.2.2[0; n] ^^^
              hashBits bf v z.2.1 z.2.2.2[n; z.2.2.1.val] := by
            simpa [uuP, cipherPartsP, hz] using heq
          exact xor_self_eq_of_eq_xorP heq'
        · refine le_trans (Finset.card_le_card ?_)
            (prop1_cardP bf z.2.1 z.2.2.2[n; z.2.2.1.val]
              (z.2.2.2[0; n] ^^^ (coinObsP hn q σ e m w).2.1.2)
              (cap_of_tweak z.2.1 hTcap))
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          have heq := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.seedHead 1 s) hcell hv
          rw [hloc] at heq
          simp only [CollisionCell.origins, originValueP,
            Bool.false_eq_true, ↓reduceIte, coinObs_L_hbar_updateP] at heq
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v false s (z, y) _ hzip] at heq
          simp only [Bool.false_eq_true, ↓reduceIte] at heq
          have heq' : (coinObsP hn q σ e m w).2.1.2 =
              z.2.2.2[0; n] ^^^
                hashBits bf v z.2.1 z.2.2.2[n; z.2.2.1.val] := by
            simpa [uuP, cipherPartsP, hz] using heq
          exact solve_right_xorP heq'
      · have hg' : dirOf (coinObsP hn q σ e m w) s = true := by
          cases h : dirOf (coinObsP hn q σ e m w) s
          · exact (hg h).elim
          · rfl
        have hz : z.1 = .fwd :=
          queryDir_eq_fwd_of_dirOf_trueP _ s z y hsel' hg'
        have hloc : collisionLocP bf hn q σ e m false i j w = .inr ⟨z, b₀⟩ := by
          rw [show collisionLocP bf hn q σ e m false i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s 0 by
            simp [collisionLocP, hcell, hg]]
          exact responseCoinAt_eq_inrP _ s 0 z y hsel' b₀.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg', Bool.true_eq_false, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.seedHead a s) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.seedHead a s) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP,
          Bool.false_eq_true, ↓reduceIte] at heq₁ heq₂
        rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m
          hE w s z y hsel' hz v₁] at heq₁
        rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m
          hE w s z y hsel' hz v₂] at heq₂
        simp only [coinObs_hbar_response_updateP,
          coinObs_L_response_updateP] at heq₁ heq₂
        exact xor_right_cancelP (heq₁.symm.trans heq₂)
  | true =>
      by_cases hg : dirOf (coinObsP hn q σ e m w) s = true
      · have hz : z.1 = .fwd :=
          queryDir_eq_fwd_of_dirOf_trueP _ s z y hsel' hg
        have hloc : collisionLocP bf hn q σ e m true i j w = .inl false := by
          simp [collisionLocP, hcell, hg]
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [degOf_eq_of_entryP _ s z y hsel']
        refine le_trans (Finset.card_le_card ?_)
          (prop1_cardP bf z.2.1 z.2.2.2[n; z.2.2.1.val]
            (z.2.2.2[0; n] ^^^ bin n a)
            (cap_of_tweak z.2.1 hTcap))
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        have heq := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.seedHead a s) hcell hv
        rw [hloc] at heq
        simp only [CollisionCell.origins, originValueP, ↓reduceIte] at heq
        rw [blockValue_head_hbar_updateP bf hn q σ e m
          w v true s (z, y) _ hzip] at heq
        simp only [↓reduceIte] at heq
        have heq' : bin n a = z.2.2.2[0; n] ^^^
            hashBits bf v z.2.1 z.2.2.2[n; z.2.2.1.val] := by
          simpa [mmP, plainPartsP, hz] using heq
        exact solve_right_xorP heq'
      · have hg' : dirOf (coinObsP hn q σ e m w) s = false := by
          cases h : dirOf (coinObsP hn q σ e m w) s
          · rfl
          · exact (hg h).elim
        have hz : z.1 = .inv :=
          queryDir_eq_inv_of_dirOf_falseP _ s z y hsel' hg'
        have hloc : collisionLocP bf hn q σ e m true i j w = .inr ⟨z, b₀⟩ := by
          rw [show collisionLocP bf hn q σ e m true i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s 0 by
            simp [collisionLocP, hcell, hg]]
          exact responseCoinAt_eq_inrP _ s 0 z y hsel' b₀.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg', Bool.false_eq_true, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.seedHead a s) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.seedHead a s) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP, ↓reduceIte]
          at heq₁ heq₂
        rw [blockValue_head_response_inv_input_updateP bf hn q σ e m
          hE w s z y hsel' hz v₁] at heq₁
        rw [blockValue_head_response_inv_input_updateP bf hn q σ e m
          hE w s z y hsel' hz v₂] at heq₂
        exact xor_right_cancelP (heq₁.symm.trans heq₂)

theorem collision_fiber_headHeadP (bf : Hash.BlockField F n)
    (hn : 0 < n) (hTcap : 2 * tcap + 3 < 2 ^ n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j r s : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.headHead r s)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  let o := coinObsP hn q σ e m w
  have hlabels := collisionCellAt_labelsP bf o d i j (.headHead r s)
    (by simpa [o] using hcell)
  have hbefore := collisionCellAt_beforeP bf o d hn i j (.headHead r s)
    (by simpa [o] using hcell)
  have hrs : r < s := by
    simp only [CollisionCell.origins, Origin.BeforeP] at hbefore
    omega
  have hneRS : r ≠ s := Nat.ne_of_lt hrs
  obtain ⟨zr, yr, hr, -⟩ := label_block_query_receiptP bf o d hn
    i r 0 hlabels.2.1
  obtain ⟨zs, ys, hs, -⟩ := label_block_query_receiptP bf o d hn
    j s 0 hlabels.2.2
  have hr' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some (zr, yr) := by
    simpa [o] using hr
  have hs' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (zs, ys) := by
    simpa [o] using hs
  have hzipr := coinObs_zip_getP hn q σ e m w r zr yr hr'
  have hzips := coinObs_zip_getP hn q σ e m w s zs ys hs'
  let b₀ : Fin (queryChargeP zs) := ⟨0, by simp [queryChargeP]⟩
  cases d with
  | false =>
      by_cases hg : dirOf (coinObsP hn q σ e m w) s = false
      · have hz : zs.1 = .inv :=
          queryDir_eq_inv_of_dirOf_falseP _ s zs ys hs' hg
        have hloc : collisionLocP bf hn q σ e m false i j w = .inl false := by
          simp [collisionLocP, hcell, hneRS, hg]
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [degOf_eq_of_entryP _ r zr yr hr',
          degOf_eq_of_entryP _ s zs ys hs']
        let bad := coinBadValuesP bf hn q σ e m false i j
          (collisionLocP bf hn q σ e m false i j) w
        by_cases hempty : bad = ∅
        · simp [bad, hempty]
        · have hnon : bad.Nonempty := by
            by_contra hnempty
            exact hempty (Finset.not_nonempty_iff_eq_empty.mp hnempty)
          obtain ⟨v₀, hv₀⟩ := hnon
          have heq₀ := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.headHead r s) hcell (by simpa [bad] using hv₀)
          rw [hloc] at heq₀
          simp only [CollisionCell.origins, originValueP] at heq₀
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v₀ false r (zr, yr) _ hzipr] at heq₀
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v₀ false s (zs, ys) _ hzips] at heq₀
          simp only [Bool.false_eq_true, ↓reduceIte] at heq₀
          let w₀ := coinUpdateP w (.inl false) v₀
          have hentries := coinObs_entries_terminalP hn q σ e m w false v₀
          have hr₀ :
              (transcriptEntries (coinObsP hn q σ e m w₀).1)[r]? =
                some (zr, yr) := by
            simpa [w₀, hentries] using hr'
          have hs₀ :
              (transcriptEntries (coinObsP hn q σ e m w₀).1)[s]? =
                some (zs, ys) := by
            simpa [w₀, hentries] using hs'
          have hneq := cipherHashInput_ne_of_uuP bf hn q σ e m hE w₀
            r s hrs (zr, yr) (zs, ys) hr₀ hs₀ hz (by
              simpa [w₀] using heq₀)
          refine le_trans (Finset.card_le_card ?_)
            (prop2_cardP bf hTcap
              (cipherHashInputP (zr, yr)).1
              (cipherHashInputP (zr, yr)).2.2
              (cipherHashInputP (zs, ys)).1
              (cipherHashInputP (zs, ys)).2.2 hneq
              ((cipherPartsP (zr, yr)).1 ^^^ (cipherPartsP (zs, ys)).1))
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          have heq := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.headHead r s) hcell (by simpa [bad] using hv)
          rw [hloc] at heq
          simp only [CollisionCell.origins, originValueP] at heq
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v false r (zr, yr) _ hzipr] at heq
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v false s (zs, ys) _ hzips] at heq
          simp only [Bool.false_eq_true, ↓reduceIte] at heq
          exact (by
            simpa [uuP, cipherHashInputP, evalHashInputP] using
              (xor_pair_rearrangeP heq))
      · have hg' : dirOf (coinObsP hn q σ e m w) s = true := by
          cases h : dirOf (coinObsP hn q σ e m w) s
          · exact (hg h).elim
          · rfl
        have hz : zs.1 = .fwd :=
          queryDir_eq_fwd_of_dirOf_trueP _ s zs ys hs' hg'
        have hloc : collisionLocP bf hn q σ e m false i j w =
            .inr ⟨zs, b₀⟩ := by
          rw [show collisionLocP bf hn q σ e m false i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s 0 by
            simp [collisionLocP, hcell, hneRS, hg]]
          exact responseCoinAt_eq_inrP _ s 0 zs ys hs' b₀.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg', Bool.true_eq_false,
          ↓reduceIte, CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.headHead r s) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.headHead r s) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        rw [blockValue_head_before_response_updateP bf hn q σ e m hE
          w r s hrs (zr, yr) zs ys hr' hs' b₀ v₁ false] at heq₁
        rw [blockValue_head_before_response_updateP bf hn q σ e m hE
          w r s hrs (zr, yr) zs ys hr' hs' b₀ v₂ false] at heq₂
        rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m hE
          w s zs ys hs' hz v₁] at heq₁
        rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m hE
          w s zs ys hs' hz v₂] at heq₂
        simp only [Bool.false_eq_true, ↓reduceIte] at heq₁ heq₂
        exact xor_right_cancelP (heq₁.symm.trans heq₂)
  | true =>
      by_cases hg : dirOf (coinObsP hn q σ e m w) s = true
      · have hz : zs.1 = .fwd :=
          queryDir_eq_fwd_of_dirOf_trueP _ s zs ys hs' hg
        have hloc : collisionLocP bf hn q σ e m true i j w = .inl false := by
          simp [collisionLocP, hcell, hneRS, hg]
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [degOf_eq_of_entryP _ r zr yr hr',
          degOf_eq_of_entryP _ s zs ys hs']
        let bad := coinBadValuesP bf hn q σ e m true i j
          (collisionLocP bf hn q σ e m true i j) w
        by_cases hempty : bad = ∅
        · simp [bad, hempty]
        · have hnon : bad.Nonempty := by
            by_contra hnempty
            exact hempty (Finset.not_nonempty_iff_eq_empty.mp hnempty)
          obtain ⟨v₀, hv₀⟩ := hnon
          have heq₀ := coinBadValues_cell_valuesP bf hn q σ e m hE true
            i j w (.headHead r s) hcell (by simpa [bad] using hv₀)
          rw [hloc] at heq₀
          simp only [CollisionCell.origins, originValueP] at heq₀
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v₀ true r (zr, yr) _ hzipr] at heq₀
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v₀ true s (zs, ys) _ hzips] at heq₀
          simp only [↓reduceIte] at heq₀
          let w₀ := coinUpdateP w (.inl false) v₀
          have hentries := coinObs_entries_terminalP hn q σ e m w false v₀
          have hr₀ :
              (transcriptEntries (coinObsP hn q σ e m w₀).1)[r]? =
                some (zr, yr) := by
            simpa [w₀, hentries] using hr'
          have hs₀ :
              (transcriptEntries (coinObsP hn q σ e m w₀).1)[s]? =
                some (zs, ys) := by
            simpa [w₀, hentries] using hs'
          have hneq := plainHashInput_ne_of_mmP bf hn q σ e m hE w₀
            r s hrs (zr, yr) (zs, ys) hr₀ hs₀ hz (by
              simpa [w₀] using heq₀)
          refine le_trans (Finset.card_le_card ?_)
            (prop2_cardP bf hTcap
              (plainHashInputP (zr, yr)).1
              (plainHashInputP (zr, yr)).2.2
              (plainHashInputP (zs, ys)).1
              (plainHashInputP (zs, ys)).2.2 hneq
              ((plainPartsP (zr, yr)).1 ^^^ (plainPartsP (zs, ys)).1))
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          have heq := coinBadValues_cell_valuesP bf hn q σ e m hE true
            i j w (.headHead r s) hcell (by simpa [bad] using hv)
          rw [hloc] at heq
          simp only [CollisionCell.origins, originValueP] at heq
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v true r (zr, yr) _ hzipr] at heq
          rw [blockValue_head_hbar_updateP bf hn q σ e m
            w v true s (zs, ys) _ hzips] at heq
          simp only [↓reduceIte] at heq
          exact (by
            simpa [mmP, plainHashInputP, evalHashInputP] using
              (xor_pair_rearrangeP heq))
      · have hg' : dirOf (coinObsP hn q σ e m w) s = false := by
          cases h : dirOf (coinObsP hn q σ e m w) s
          · rfl
          · exact (hg h).elim
        have hz : zs.1 = .inv :=
          queryDir_eq_inv_of_dirOf_falseP _ s zs ys hs' hg'
        have hloc : collisionLocP bf hn q σ e m true i j w =
            .inr ⟨zs, b₀⟩ := by
          rw [show collisionLocP bf hn q σ e m true i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s 0 by
            simp [collisionLocP, hcell, hneRS, hg]]
          exact responseCoinAt_eq_inrP _ s 0 zs ys hs' b₀.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hg', Bool.false_eq_true,
          ↓reduceIte, CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.headHead r s) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.headHead r s) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        rw [blockValue_head_before_response_updateP bf hn q σ e m hE
          w r s hrs (zr, yr) zs ys hr' hs' b₀ v₁ true] at heq₁
        rw [blockValue_head_before_response_updateP bf hn q σ e m hE
          w r s hrs (zr, yr) zs ys hr' hs' b₀ v₂ true] at heq₂
        rw [blockValue_head_response_inv_input_updateP bf hn q σ e m hE
          w s zs ys hs' hz v₁] at heq₁
        rw [blockValue_head_response_inv_input_updateP bf hn q σ e m hE
          w s zs ys hs' hz v₂] at heq₂
        simp only [↓reduceIte] at heq₁ heq₂
        exact xor_right_cancelP (heq₁.symm.trans heq₂)

theorem blockValue_head_response_tail_inv_output_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s k : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hk : k < numBlocks n z.2.2.1.val) (hdir : z.1 = .inv)
    (v : BitString n) :
    let b : Fin (queryChargeP z) :=
      ⟨k + 1, by simp [queryChargeP]; omega⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) false s 0 =
      z.2.2.2[0; n] ^^^ hashBits bf
        (coinObsP hn q σ e m w).2.1.1 z.2.1
          z.2.2.2[n; z.2.2.1.val] := by
  dsimp only
  let b : Fin (queryChargeP z) :=
    ⟨k + 1, by simp [queryChargeP]; omega⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let y' := rndFun (coinKeyP hn w').1 z
  have hsel' := coinObs_entry_update_getP hn q σ e m hE
    w z b v s y hsel
  have hzip' := coinObs_zip_getP hn q σ e m w' s z y' (by
    simpa [w', y'] using hsel')
  rw [blockValue_headP bf _ false s (z, y') _ hzip']
  simp [uuP, cipherPartsP, hdir, w']

theorem blockValue_tail_output_response_head_fwd_update_eqP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s k : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hk : k < numBlocks n z.2.2.1.val) (hdir : z.1 = .fwd)
    (v₁ v₂ : BitString n) :
    let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v₁)) false s (k + 1) =
      blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v₂)) false s (k + 1) := by
  dsimp only
  let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  let w₁ := coinUpdateP w (.inr ⟨z, b⟩) v₁
  let w₂ := coinUpdateP w (.inr ⟨z, b⟩) v₂
  let y₁ := rndFun (coinKeyP hn w₁).1 z
  let y₂ := rndFun (coinKeyP hn w₂).1 z
  have hsel₁ := coinObs_entry_update_getP hn q σ e m hE
    w z b v₁ s y hsel
  have hsel₂ := coinObs_entry_update_getP hn q σ e m hE
    w z b v₂ s y hsel
  have hzip₁ := coinObs_zip_getP hn q σ e m w₁ s z y₁ (by
    simpa [w₁, y₁] using hsel₁)
  have hzip₂ := coinObs_zip_getP hn q σ e m w₂ s z y₂ (by
    simpa [w₂, y₂] using hsel₂)
  have hk₁ : k < (yBlocksP (z, y₁)
      ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₁).2.2 z⟩).length := by
    simpa [yBlocksP] using hk
  have hk₂ : k < (yBlocksP (z, y₂)
      ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₂).2.2 z⟩).length := by
    simpa [yBlocksP] using hk
  rw [blockValue_tail_outputP bf _ s k (z, y₁) _ hzip₁ hk₁]
  rw [blockValue_tail_outputP bf _ s k (z, y₂) _ hzip₂ hk₂]
  let k' : Fin (numBlocks n z.2.2.1.val) := ⟨k, hk⟩
  let bt : Fin (queryChargeP z) :=
    ⟨k + 1, by simp [queryChargeP]; omega⟩
  let idx : CoinIndexP n cap tcap := .inr ⟨z, bt⟩
  have hsame₁ : coinUpdateP w₁ idx (w₁ idx) = w₁ := by
    funext x
    simp [coinUpdateP]
  have hsame₂ : coinUpdateP w₂ idx (w₂ idx) = w₂ := by
    funext x
    simp [coinUpdateP]
  have hform₁ := yBlocks_coin_updateP hn w₁ z k' (w₁ idx)
  have hform₂ := yBlocks_coin_updateP hn w₂ z k' (w₂ idx)
  dsimp only at hform₁ hform₂
  have hbt : (⟨k'.val + 1, by simp [queryChargeP]; omega⟩ :
      Fin (queryChargeP z)) = bt := by rfl
  rw [hbt] at hform₁ hform₂
  have hsame₁' : coinUpdateP w₁ (.inr ⟨z, bt⟩) (w₁ idx) = w₁ := by
    simpa [idx] using hsame₁
  have hsame₂' : coinUpdateP w₂ (.inr ⟨z, bt⟩) (w₂ idx) = w₂ := by
    simpa [idx] using hsame₂
  rw [hsame₁'] at hform₁
  rw [hsame₂'] at hform₂
  have hne : idx ≠ (.inr ⟨z, b⟩ : CoinIndexP n cap tcap) := by
    intro heq
    have hv := congrArg (fun x : CoinIndexP n cap tcap =>
      match x with
      | .inl _ => 0
      | .inr p => p.2.val) heq
    simp [idx, bt, b] at hv
  have hoff₁ : w₁ idx = w idx := by
    simp [w₁, coinUpdateP, hne]
  have hoff₂ : w₂ idx = w idx := by
    simp [w₂, coinUpdateP, hne]
  have hform₁' :
      (yBlocksP (z, y₁) ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₁).2.2 z⟩).get ⟨k, hk₁⟩ =
        queryTailMaskP z k ^^^ w idx := by
    simpa [w₁, y₁, k', bt, idx, hoff₁] using hform₁
  have hform₂' :
      (yBlocksP (z, y₂) ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₂).2.2 z⟩).get ⟨k, hk₂⟩ =
        queryTailMaskP z k ^^^ w idx := by
    simpa [w₂, y₂, k', bt, idx, hoff₂] using hform₂
  exact hform₁'.trans hform₂'.symm

theorem collision_fiber_headTailP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j r s k : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.headTail r s k)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  let o := coinObsP hn q σ e m w
  have hlabels := collisionCellAt_labelsP bf o d i j (.headTail r s k)
    (by simpa [o] using hcell)
  have hbefore := collisionCellAt_beforeP bf o d hn i j (.headTail r s k)
    (by simpa [o] using hcell)
  have hrsle : r < s ∨ r = s := by
    simp only [CollisionCell.origins, Origin.BeforeP] at hbefore
    omega
  obtain ⟨zr, yr, hr, -⟩ := label_block_query_receiptP bf o d hn
    i r 0 hlabels.2.1
  obtain ⟨zs, ys, hs, hkentry⟩ := label_block_query_receiptP bf o d hn
    j s (k + 1) hlabels.2.2
  have hr' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some (zr, yr) := by
    simpa [o] using hr
  have hs' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (zs, ys) := by
    simpa [o] using hs
  have hk : k < numBlocks n zs.2.2.1.val := by
    rw [entryCharge_eq_queryChargeP hn (zs, ys)] at hkentry
    simp [queryChargeP] at hkentry
    omega
  have hzipr := coinObs_zip_getP hn q σ e m w r zr yr hr'
  have hzips := coinObs_zip_getP hn q σ e m w s zs ys hs'
  let b₀ : Fin (queryChargeP zs) := ⟨0, by simp [queryChargeP]⟩
  let bt : Fin (queryChargeP zs) :=
    ⟨k + 1, by simp [queryChargeP]; omega⟩
  cases d with
  | true =>
      have hloc : collisionLocP bf hn q σ e m true i j w = .inl true := by
        simp [collisionLocP, hcell]
      rw [costAt, hcell]
      simp only [CollisionCell.bound, CollisionCell.Bound.cost]
      rw [Finset.card_le_one]
      intro v₁ hv₁ v₂ hv₂
      have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE true
        i j w (.headTail r s k) hcell hv₁
      have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE true
        i j w (.headTail r s k) hcell hv₂
      rw [hloc] at heq₁ heq₂
      simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
      rw [blockValue_head_L_updateP bf hn q σ e m
        w v₁ true r (zr, yr) _ hzipr] at heq₁
      rw [blockValue_head_L_updateP bf hn q σ e m
        w v₂ true r (zr, yr) _ hzipr] at heq₂
      rw [blockValue_tail_input_L_updateP bf hn q σ e m
        w v₁ s k (zs, ys) _ hzips] at heq₁
      rw [blockValue_tail_input_L_updateP bf hn q σ e m
        w v₂ s k (zs, ys) _ hzips] at heq₂
      simp only [↓reduceIte] at heq₁ heq₂
      have hcancel := xor_right_cancelP (heq₁.symm.trans heq₂)
      have hcancel' := xor_left_cancelP (by
        simpa only [BitVec.xor_assoc] using hcancel)
      exact xor_left_cancelP hcancel'
  | false =>
      by_cases hrs : r = s
      · subst r
        have hentry : (zr, yr) = (zs, ys) := by
          exact Option.some.inj (hr'.symm.trans hs')
        cases hentry
        by_cases hg : dirOf (coinObsP hn q σ e m w) s = true
        · have hz : zr.1 = .fwd :=
            queryDir_eq_fwd_of_dirOf_trueP _ s zr yr hs' hg
          have hloc : collisionLocP bf hn q σ e m false i j w =
              .inr ⟨zr, b₀⟩ := by
            rw [show collisionLocP bf hn q σ e m false i j w =
                responseCoinAtP (coinObsP hn q σ e m w) s 0 by
              simp [collisionLocP, hcell, hg]]
            exact responseCoinAt_eq_inrP _ s 0 zr yr hs' b₀.isLt
          rw [costAt, hcell]
          simp only [CollisionCell.bound, CollisionCell.Bound.cost]
          rw [Finset.card_le_one]
          intro v₁ hv₁ v₂ hv₂
          have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.headTail s s k) hcell hv₁
          have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.headTail s s k) hcell hv₂
          rw [hloc] at heq₁ heq₂
          simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
          rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m hE
            w s zr yr hs' hz v₁] at heq₁
          rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m hE
            w s zr yr hs' hz v₂] at heq₂
          have htail := blockValue_tail_output_response_head_fwd_update_eqP
            bf hn q σ e m hE w s k zr yr hs' hk hz v₁ v₂
          exact xor_right_cancelP (heq₁.trans (htail.trans heq₂.symm))
        · have hg' : dirOf (coinObsP hn q σ e m w) s = false := by
            cases h : dirOf (coinObsP hn q σ e m w) s
            · rfl
            · exact (hg h).elim
          have hz : zr.1 = .inv :=
            queryDir_eq_inv_of_dirOf_falseP _ s zr yr hs' hg'
          have hloc : collisionLocP bf hn q σ e m false i j w =
              .inr ⟨zr, bt⟩ := by
            rw [show collisionLocP bf hn q σ e m false i j w =
                responseCoinAtP (coinObsP hn q σ e m w) s (k + 1) by
              simp [collisionLocP, hcell, hg]]
            exact responseCoinAt_eq_inrP _ s (k + 1) zr yr hs' bt.isLt
          rw [costAt, hcell]
          simp only [CollisionCell.bound, CollisionCell.Bound.cost]
          rw [Finset.card_le_one]
          intro v₁ hv₁ v₂ hv₂
          have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.headTail s s k) hcell hv₁
          have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
            i j w (.headTail s s k) hcell hv₂
          rw [hloc] at heq₁ heq₂
          simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
          rw [blockValue_head_response_tail_inv_output_updateP bf hn q σ e m
            hE w s k zr yr hs' hk hz v₁] at heq₁
          rw [blockValue_head_response_tail_inv_output_updateP bf hn q σ e m
            hE w s k zr yr hs' hk hz v₂] at heq₂
          rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
            w s k zr yr hs' hk v₁] at heq₁
          rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
            w s k zr yr hs' hk v₂] at heq₂
          exact xor_left_cancelP (heq₁.symm.trans heq₂)
      · have hrs' : r < s := hrsle.resolve_right hrs
        have hloc : collisionLocP bf hn q σ e m false i j w =
            .inr ⟨zs, bt⟩ := by
          rw [show collisionLocP bf hn q σ e m false i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s (k + 1) by
            simp [collisionLocP, hcell, hrs]]
          exact responseCoinAt_eq_inrP _ s (k + 1) zs ys hs' bt.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.headTail r s k) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.headTail r s k) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        rw [blockValue_head_before_response_updateP bf hn q σ e m hE
          w r s hrs' (zr, yr) zs ys hr' hs' bt v₁ false] at heq₁
        rw [blockValue_head_before_response_updateP bf hn q σ e m hE
          w r s hrs' (zr, yr) zs ys hr' hs' bt v₂ false] at heq₂
        rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
          w s k zs ys hs' hk v₁] at heq₁
        rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
          w s k zs ys hs' hk v₂] at heq₂
        simp only [Bool.false_eq_true, ↓reduceIte] at heq₁ heq₂
        exact xor_left_cancelP (heq₁.symm.trans heq₂)

theorem blockValue_tail_output_before_response_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (r s k : ℕ) (hrs : r < s)
    (er : TQ n cap tcap × TM n cap) (z : TQ n cap tcap) (y : TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hk : k < numBlocks n er.1.2.2.1.val)
    (b : Fin (queryChargeP z)) (v : BitString n) :
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) false r (k + 1) =
      (yBlocksP er ⟨padLen n er.1.2.2.1.val - er.1.2.2.1.val,
        (coinKeyP hn w).2.2 er.1⟩).get ⟨k, by simpa [yBlocksP] using hk⟩ := by
  have hzip := coinObs_zip_before_updateP hn q σ e m hE
    w z b v s y hs r hrs er hr
  exact blockValue_tail_outputP bf _ r k er _ hzip
    (by simpa [yBlocksP] using hk)

theorem collision_fiber_tailHeadP (bf : Hash.BlockField F n)
    (hn : 0 < n) (hTcap : 2 * tcap + 3 < 2 ^ n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j r k s : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.tailHead r k s)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  let o := coinObsP hn q σ e m w
  have hlabels := collisionCellAt_labelsP bf o d i j (.tailHead r k s)
    (by simpa [o] using hcell)
  have hbefore := collisionCellAt_beforeP bf o d hn i j (.tailHead r k s)
    (by simpa [o] using hcell)
  have hrs : r < s := by
    simp only [CollisionCell.origins, Origin.BeforeP] at hbefore
    omega
  have hneRS : r ≠ s := Nat.ne_of_lt hrs
  obtain ⟨zr, yr, hr, hkrEntry⟩ := label_block_query_receiptP bf o d hn
    i r (k + 1) hlabels.2.1
  obtain ⟨zs, ys, hs, -⟩ := label_block_query_receiptP bf o d hn
    j s 0 hlabels.2.2
  have hr' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some (zr, yr) := by
    simpa [o] using hr
  have hs' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (zs, ys) := by
    simpa [o] using hs
  have hkr : k < numBlocks n zr.2.2.1.val := by
    rw [entryCharge_eq_queryChargeP hn (zr, yr)] at hkrEntry
    simp [queryChargeP] at hkrEntry
    omega
  have hzipr := coinObs_zip_getP hn q σ e m w r zr yr hr'
  have hzips := coinObs_zip_getP hn q σ e m w s zs ys hs'
  have hky : k < (yBlocksP (zr, yr)
      ⟨padLen n zr.2.2.1.val - zr.2.2.1.val,
        (coinKeyP hn w).2.2 zr⟩).length := by
    simpa [yBlocksP] using hkr
  let b₀ : Fin (queryChargeP zs) := ⟨0, by simp [queryChargeP]⟩
  cases d with
  | true =>
      have hloc : collisionLocP bf hn q σ e m true i j w = .inl true := by
        simp [collisionLocP, hcell, hneRS]
      rw [costAt, hcell]
      simp only [CollisionCell.bound, hneRS, ↓reduceIte,
        CollisionCell.Bound.cost]
      rw [Finset.card_le_one]
      intro v₁ hv₁ v₂ hv₂
      have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE true
        i j w (.tailHead r k s) hcell hv₁
      have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE true
        i j w (.tailHead r k s) hcell hv₂
      rw [hloc] at heq₁ heq₂
      simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
      rw [blockValue_tail_input_L_updateP bf hn q σ e m
        w v₁ r k (zr, yr) _ hzipr] at heq₁
      rw [blockValue_tail_input_L_updateP bf hn q σ e m
        w v₂ r k (zr, yr) _ hzipr] at heq₂
      rw [blockValue_head_L_updateP bf hn q σ e m
        w v₁ true s (zs, ys) _ hzips] at heq₁
      rw [blockValue_head_L_updateP bf hn q σ e m
        w v₂ true s (zs, ys) _ hzips] at heq₂
      simp only [↓reduceIte] at heq₁ heq₂
      have hcancel := xor_right_cancelP (heq₁.trans heq₂.symm)
      have hcancel' := xor_left_cancelP (by
        simpa only [BitVec.xor_assoc] using hcancel)
      exact xor_left_cancelP hcancel'
  | false =>
      by_cases hg : dirOf (coinObsP hn q σ e m w) s = false
      · have hz : zs.1 = .inv :=
          queryDir_eq_inv_of_dirOf_falseP _ s zs ys hs' hg
        have hloc : collisionLocP bf hn q σ e m false i j w = .inl false := by
          simp [collisionLocP, hcell, hneRS, hg]
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hneRS, Bool.false_eq_true,
          ↓reduceIte, hg,
          CollisionCell.Bound.cost]
        rw [degOf_eq_of_entryP _ s zs ys hs']
        refine le_trans (Finset.card_le_card ?_)
          (prop1_cardP bf zs.2.1 zs.2.2.2[n; zs.2.2.1.val]
            (zs.2.2.2[0; n] ^^^
              (yBlocksP (zr, yr) ⟨padLen n zr.2.2.1.val - zr.2.2.1.val,
                (coinKeyP hn w).2.2 zr⟩).get ⟨k, hky⟩)
            (cap_of_tweak zs.2.1 hTcap))
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        have heq := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailHead r k s) hcell hv
        rw [hloc] at heq
        simp only [CollisionCell.origins, originValueP] at heq
        rw [blockValue_tail_output_terminalP bf hn q σ e m
          w false v r k (zr, yr) _ hzipr hky] at heq
        rw [blockValue_head_hbar_updateP bf hn q σ e m
          w v false s (zs, ys) _ hzips] at heq
        simp only [Bool.false_eq_true, ↓reduceIte] at heq
        have heq' :
            (yBlocksP (zr, yr) ⟨padLen n zr.2.2.1.val - zr.2.2.1.val,
              (coinKeyP hn w).2.2 zr⟩).get ⟨k, hky⟩ =
              zs.2.2.2[0; n] ^^^
                hashBits bf v zs.2.1 zs.2.2.2[n; zs.2.2.1.val] := by
          simpa [uuP, cipherPartsP, hz] using heq
        exact solve_right_xorP heq'
      · have hg' : dirOf (coinObsP hn q σ e m w) s = true := by
          cases h : dirOf (coinObsP hn q σ e m w) s
          · exact (hg h).elim
          · rfl
        have hz : zs.1 = .fwd :=
          queryDir_eq_fwd_of_dirOf_trueP _ s zs ys hs' hg'
        have hloc : collisionLocP bf hn q σ e m false i j w =
            .inr ⟨zs, b₀⟩ := by
          rw [show collisionLocP bf hn q σ e m false i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s 0 by
            simp [collisionLocP, hcell, hneRS, hg]]
          exact responseCoinAt_eq_inrP _ s 0 zs ys hs' b₀.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hneRS, Bool.false_eq_true,
          ↓reduceIte, hg',
          Bool.true_eq_false, CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailHead r k s) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailHead r k s) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        rw [blockValue_tail_output_before_response_updateP bf hn q σ e m hE
          w r s k hrs (zr, yr) zs ys hr' hs' hkr b₀ v₁] at heq₁
        rw [blockValue_tail_output_before_response_updateP bf hn q σ e m hE
          w r s k hrs (zr, yr) zs ys hr' hs' hkr b₀ v₂] at heq₂
        rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m hE
          w s zs ys hs' hz v₁] at heq₁
        rw [blockValue_head_response_fwd_output_updateP bf hn q σ e m hE
          w s zs ys hs' hz v₂] at heq₂
        exact xor_right_cancelP (heq₁.symm.trans heq₂)

theorem blockValue_tail_input_hbar_updateP (bf : Hash.BlockField F n)
    (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (w : CoinBlocksP n cap tcap) (v : BitString n) (s k : ℕ)
    (entry : TQ n cap tcap × TM n cap) (D : Σ width : ℕ, BitString width)
    (hzip : (((transcriptEntries (coinObsP hn q σ e m w).1).zip
      (coinObsP hn q σ e m w).2.2)[s]?) = some (entry, D)) :
    blockValueP bf (coinObsP hn q σ e m
      (coinUpdateP w (.inl false) v)) true s (k + 1) =
      mmP bf v entry ^^^ uuP bf v entry ^^^
        (coinObsP hn q σ e m w).2.1.2 ^^^ bin n (k + 1) := by
  have hzip' : (((transcriptEntries (coinObsP hn q σ e m
      (coinUpdateP w (.inl false) v)).1).zip
      (coinObsP hn q σ e m (coinUpdateP w (.inl false) v)).2.2)[s]?) =
      some (entry, D) := by
    rw [coinObs_zip_terminalP hn q σ e m w false v]
    exact hzip
  rw [blockValue_tail_inputP bf _ s k entry D hzip']
  simp [ssP]

theorem blockValue_tail_input_before_response_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (r s k : ℕ) (hrs : r < s)
    (er : TQ n cap tcap × TM n cap) (z : TQ n cap tcap) (y : TM n cap)
    (hr : (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some er)
    (hs : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (b : Fin (queryChargeP z)) (v : BitString n) :
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) true r (k + 1) =
      ssP bf (coinObsP hn q σ e m w).2.1.1
        (coinObsP hn q σ e m w).2.1.2 er ^^^ bin n (k + 1) := by
  have hzip := coinObs_zip_before_updateP hn q σ e m hE
    w z b v s y hs r hrs er hr
  rw [blockValue_tail_inputP bf _ r k er _ hzip]
  simp [ssP]

theorem blockValue_tail_input_response_head_fwd_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s k : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hdir : z.1 = .fwd) (v : BitString n) :
    let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) true s (k + 1) =
      mmP bf (coinObsP hn q σ e m w).2.1.1 (z, y) ^^^
        (v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
          ((coinKeyP hn w).1 z)[n; z.2.2.1.val]) ^^^
        (coinObsP hn q σ e m w).2.1.2 ^^^ bin n (k + 1) := by
  dsimp only
  let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let y' := rndFun (coinKeyP hn w').1 z
  have hsel' := coinObs_entry_update_getP hn q σ e m hE
    w z b v s y hsel
  have hzip' := coinObs_zip_getP hn q σ e m w' s z y' (by
    simpa [w', y'] using hsel')
  rw [blockValue_tail_inputP bf _ s k (z, y') _ hzip']
  simp only [ssP]
  simp only [w', coinObs_hbar_response_updateP,
    coinObs_L_response_updateP]
  have huu := uu_response_head_fwdP bf hn w z v hdir
  rw [show uuP bf (coinObsP hn q σ e m w).2.1.1 (z, y') =
      v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
        ((coinKeyP hn w).1 z)[n; z.2.2.1.val] by
    simpa [w', y', b, coinObsP, augRnd] using huu]
  rcases z with ⟨dir, T, j, Q⟩
  cases dir
  · rfl
  · simp at hdir

theorem blockValue_tail_input_response_head_inv_updateP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s k : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hdir : z.1 = .inv) (v : BitString n) :
    let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v)) true s (k + 1) =
      (v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
          ((coinKeyP hn w).1 z)[n; z.2.2.1.val]) ^^^
        uuP bf (coinObsP hn q σ e m w).2.1.1 (z, y) ^^^
        (coinObsP hn q σ e m w).2.1.2 ^^^ bin n (k + 1) := by
  dsimp only
  let b : Fin (queryChargeP z) := ⟨0, by simp [queryChargeP]⟩
  let w' := coinUpdateP w (.inr ⟨z, b⟩) v
  let y' := rndFun (coinKeyP hn w').1 z
  have hsel' := coinObs_entry_update_getP hn q σ e m hE
    w z b v s y hsel
  have hzip' := coinObs_zip_getP hn q σ e m w' s z y' (by
    simpa [w', y'] using hsel')
  rw [blockValue_tail_inputP bf _ s k (z, y') _ hzip']
  simp only [ssP]
  simp only [w', coinObs_hbar_response_updateP,
    coinObs_L_response_updateP]
  have hmm := mm_response_head_invP bf hn w z v hdir
  rw [show mmP bf (coinObsP hn q σ e m w).2.1.1 (z, y') =
      v ^^^ hashBits bf (coinKeyP hn w).2.1.1 z.2.1
        ((coinKeyP hn w).1 z)[n; z.2.2.1.val] by
    simpa [w', y', b, coinObsP, augRnd] using hmm]
  rcases z with ⟨dir, T, j, Q⟩
  cases dir
  · simp at hdir
  · rfl

theorem blockValue_tail_output_response_tail_off_update_eqP
    (bf : Hash.BlockField F n) (hn : 0 < n) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (w : CoinBlocksP n cap tcap) (s k l : ℕ)
    (z : TQ n cap tcap) (y : TM n cap)
    (hsel : (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (z, y))
    (hk : k < numBlocks n z.2.2.1.val)
    (hl : l < numBlocks n z.2.2.1.val) (hne : k ≠ l)
    (v₁ v₂ : BitString n) :
    let b : Fin (queryChargeP z) :=
      ⟨l + 1, by simp [queryChargeP]; omega⟩
    blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v₁)) false s (k + 1) =
      blockValueP bf (coinObsP hn q σ e m
        (coinUpdateP w (.inr ⟨z, b⟩) v₂)) false s (k + 1) := by
  dsimp only
  let b : Fin (queryChargeP z) :=
    ⟨l + 1, by simp [queryChargeP]; omega⟩
  let w₁ := coinUpdateP w (.inr ⟨z, b⟩) v₁
  let w₂ := coinUpdateP w (.inr ⟨z, b⟩) v₂
  let y₁ := rndFun (coinKeyP hn w₁).1 z
  let y₂ := rndFun (coinKeyP hn w₂).1 z
  have hsel₁ := coinObs_entry_update_getP hn q σ e m hE
    w z b v₁ s y hsel
  have hsel₂ := coinObs_entry_update_getP hn q σ e m hE
    w z b v₂ s y hsel
  have hzip₁ := coinObs_zip_getP hn q σ e m w₁ s z y₁ (by
    simpa [w₁, y₁] using hsel₁)
  have hzip₂ := coinObs_zip_getP hn q σ e m w₂ s z y₂ (by
    simpa [w₂, y₂] using hsel₂)
  have hk₁ : k < (yBlocksP (z, y₁)
      ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₁).2.2 z⟩).length := by
    simpa [yBlocksP] using hk
  have hk₂ : k < (yBlocksP (z, y₂)
      ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₂).2.2 z⟩).length := by
    simpa [yBlocksP] using hk
  rw [blockValue_tail_outputP bf _ s k (z, y₁) _ hzip₁ hk₁]
  rw [blockValue_tail_outputP bf _ s k (z, y₂) _ hzip₂ hk₂]
  let k' : Fin (numBlocks n z.2.2.1.val) := ⟨k, hk⟩
  let bk : Fin (queryChargeP z) :=
    ⟨k + 1, by simp [queryChargeP]; omega⟩
  let idx : CoinIndexP n cap tcap := .inr ⟨z, bk⟩
  have hsame₁ : coinUpdateP w₁ idx (w₁ idx) = w₁ := by
    funext x
    simp [coinUpdateP]
  have hsame₂ : coinUpdateP w₂ idx (w₂ idx) = w₂ := by
    funext x
    simp [coinUpdateP]
  have hform₁ := yBlocks_coin_updateP hn w₁ z k' (w₁ idx)
  have hform₂ := yBlocks_coin_updateP hn w₂ z k' (w₂ idx)
  dsimp only at hform₁ hform₂
  have hbk : (⟨k'.val + 1, by simp [queryChargeP]; omega⟩ :
      Fin (queryChargeP z)) = bk := by rfl
  rw [hbk] at hform₁ hform₂
  have hsame₁' : coinUpdateP w₁ (.inr ⟨z, bk⟩) (w₁ idx) = w₁ := by
    simpa [idx] using hsame₁
  have hsame₂' : coinUpdateP w₂ (.inr ⟨z, bk⟩) (w₂ idx) = w₂ := by
    simpa [idx] using hsame₂
  rw [hsame₁'] at hform₁
  rw [hsame₂'] at hform₂
  have hneIdx : idx ≠ (.inr ⟨z, b⟩ : CoinIndexP n cap tcap) := by
    intro heq
    have hv := congrArg (fun x : CoinIndexP n cap tcap =>
      match x with
      | .inl _ => 0
      | .inr p => p.2.val) heq
    simp [idx, bk, b] at hv
    omega
  have hoff₁ : w₁ idx = w idx := by
    simp [w₁, coinUpdateP, hneIdx]
  have hoff₂ : w₂ idx = w idx := by
    simp [w₂, coinUpdateP, hneIdx]
  have hform₁' :
      (yBlocksP (z, y₁) ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₁).2.2 z⟩).get ⟨k, hk₁⟩ =
        queryTailMaskP z k ^^^ w idx := by
    simpa [w₁, y₁, k', bk, idx, hoff₁] using hform₁
  have hform₂' :
      (yBlocksP (z, y₂) ⟨padLen n z.2.2.1.val - z.2.2.1.val,
        (coinKeyP hn w₂).2.2 z⟩).get ⟨k, hk₂⟩ =
        queryTailMaskP z k ^^^ w idx := by
    simpa [w₂, y₂, k', bk, idx, hoff₂] using hform₂
  exact hform₁'.trans hform₂'.symm

theorem xor_affine_fwd_injP {a h L b v₁ v₂ : BitString n}
    (heq : a ^^^ (v₁ ^^^ h) ^^^ L ^^^ b =
      a ^^^ (v₂ ^^^ h) ^^^ L ^^^ b) : v₁ = v₂ := by
  exact xor_right_cancelP
    (xor_left_cancelP (xor_right_cancelP (xor_right_cancelP heq)))

theorem xor_affine_inv_injP {h u L b v₁ v₂ : BitString n}
    (heq : (v₁ ^^^ h) ^^^ u ^^^ L ^^^ b =
      (v₂ ^^^ h) ^^^ u ^^^ L ^^^ b) : v₁ = v₂ := by
  exact xor_right_cancelP
    (xor_right_cancelP (xor_right_cancelP (xor_right_cancelP heq)))

theorem bin_succ_ne_of_lt_leP {k l : ℕ} (hkl : k < l)
    (hl : l + 1 ≤ 2 ^ n) : bin n (k + 1) ≠ bin n (l + 1) := by
  have hk : k + 1 < 2 ^ n := by omega
  intro heq
  by_cases hlt : l + 1 < 2 ^ n
  · exact (by omega : k + 1 ≠ l + 1) (bin_inj hk hlt heq)
  · have hp : l + 1 = 2 ^ n := by omega
    have hz : bin n (l + 1) = 0 := by
      rw [hp]
      rw [← BitVec.toNat_inj, bin, BitVec.toNat_ofNat]
      exact Nat.mod_self _
    exact bin_ne_zero (by omega) hk (heq.trans hz)

theorem collision_fiber_tailTailP (bf : Hash.BlockField F n)
    (hn : 0 < n) (hMsg : MessageBlocksInRange n cap) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j r k s l : ℕ) (w : CoinBlocksP n cap tcap)
    (hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j =
      some (.tailTail r k s l)) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  let o := coinObsP hn q σ e m w
  have hlabels := collisionCellAt_labelsP bf o d i j (.tailTail r k s l)
    (by simpa [o] using hcell)
  have hbefore := collisionCellAt_beforeP bf o d hn i j (.tailTail r k s l)
    (by simpa [o] using hcell)
  have horder : r < s ∨ (r = s ∧ k < l) := by
    simp only [CollisionCell.origins, Origin.BeforeP] at hbefore
    omega
  obtain ⟨zr, yr, hr, hkrEntry⟩ := label_block_query_receiptP bf o d hn
    i r (k + 1) hlabels.2.1
  obtain ⟨zs, ys, hs, hlsEntry⟩ := label_block_query_receiptP bf o d hn
    j s (l + 1) hlabels.2.2
  have hr' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[r]? = some (zr, yr) := by
    simpa [o] using hr
  have hs' :
      (transcriptEntries (coinObsP hn q σ e m w).1)[s]? = some (zs, ys) := by
    simpa [o] using hs
  have hkr : k < numBlocks n zr.2.2.1.val := by
    rw [entryCharge_eq_queryChargeP hn (zr, yr)] at hkrEntry
    simp [queryChargeP] at hkrEntry
    omega
  have hls : l < numBlocks n zs.2.2.1.val := by
    rw [entryCharge_eq_queryChargeP hn (zs, ys)] at hlsEntry
    simp [queryChargeP] at hlsEntry
    omega
  have hzipr := coinObs_zip_getP hn q σ e m w r zr yr hr'
  have hzips := coinObs_zip_getP hn q σ e m w s zs ys hs'
  let b₀ : Fin (queryChargeP zs) := ⟨0, by simp [queryChargeP]⟩
  let bl : Fin (queryChargeP zs) :=
    ⟨l + 1, by simp [queryChargeP]; omega⟩
  cases d with
  | true =>
      by_cases hrs : r = s
      · subst r
        have hentry : (zr, yr) = (zs, ys) :=
          Option.some.inj (hr'.symm.trans hs')
        cases hentry
        have hkl : k < l := (horder.resolve_left (by omega)).2
        have hloc : collisionLocP bf hn q σ e m true i j w = .inl false := by
          simp [collisionLocP, hcell]
        rw [costAt, hcell]
        simp only [CollisionCell.bound, ↓reduceIte, CollisionCell.Bound.cost]
        have hz : (coinBadValuesP bf hn q σ e m true i j
            (collisionLocP bf hn q σ e m true i j) w).card = 0 := by
          rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
          rintro ⟨v, hv⟩
          have heq := coinBadValues_cell_valuesP bf hn q σ e m hE true
            i j w (.tailTail s k s l) hcell hv
          rw [hloc] at heq
          simp only [CollisionCell.origins, originValueP] at heq
          rw [blockValue_tail_input_hbar_updateP bf hn q σ e m
            w v s k (zr, yr) _ hzipr] at heq
          rw [blockValue_tail_input_hbar_updateP bf hn q σ e m
            w v s l (zr, yr) _ hzips] at heq
          have hcharge : entryCharge (zr, yr) ≤ 2 ^ n := by
            rw [entryCharge]
            exact hMsg zr.2.2.1
          have hlpow : l + 1 ≤ 2 ^ n := le_trans (Nat.le_of_lt hlsEntry) hcharge
          exact bin_succ_ne_of_lt_leP hkl hlpow (xor_left_cancelP heq)
        omega
      · have hrs' : r < s := horder.resolve_right (fun h => hrs h.1)
        have hloc : collisionLocP bf hn q σ e m true i j w =
            .inr ⟨zs, b₀⟩ := by
          rw [show collisionLocP bf hn q σ e m true i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s 0 by
            simp [collisionLocP, hcell, hrs]]
          exact responseCoinAt_eq_inrP _ s 0 zs ys hs' b₀.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hrs, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.tailTail r k s l) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE true
          i j w (.tailTail r k s l) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        rw [blockValue_tail_input_before_response_updateP bf hn q σ e m hE
          w r s k hrs' (zr, yr) zs ys hr' hs' b₀ v₁] at heq₁
        rw [blockValue_tail_input_before_response_updateP bf hn q σ e m hE
          w r s k hrs' (zr, yr) zs ys hr' hs' b₀ v₂] at heq₂
        cases hzs : zs.1 with
        | fwd =>
            rw [blockValue_tail_input_response_head_fwd_updateP bf hn q σ e m
              hE w s l zs ys hs' hzs v₁] at heq₁
            rw [blockValue_tail_input_response_head_fwd_updateP bf hn q σ e m
              hE w s l zs ys hs' hzs v₂] at heq₂
            exact xor_affine_fwd_injP (heq₁.symm.trans heq₂)
        | inv =>
            rw [blockValue_tail_input_response_head_inv_updateP bf hn q σ e m
              hE w s l zs ys hs' hzs v₁] at heq₁
            rw [blockValue_tail_input_response_head_inv_updateP bf hn q σ e m
              hE w s l zs ys hs' hzs v₂] at heq₂
            exact xor_affine_inv_injP (heq₁.symm.trans heq₂)
  | false =>
      by_cases hrs : r = s
      · subst r
        have hentry : (zr, yr) = (zs, ys) :=
          Option.some.inj (hr'.symm.trans hs')
        cases hentry
        have hkl : k < l := (horder.resolve_left (by omega)).2
        have hne : k ≠ l := Nat.ne_of_lt hkl
        have hloc : collisionLocP bf hn q σ e m false i j w =
            .inr ⟨zr, bl⟩ := by
          rw [show collisionLocP bf hn q σ e m false i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s (l + 1) by
            simp [collisionLocP, hcell]]
          exact responseCoinAt_eq_inrP _ s (l + 1) zr yr hs' bl.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, Bool.false_eq_true, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailTail s k s l) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailTail s k s l) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        have hleft := blockValue_tail_output_response_tail_off_update_eqP
          bf hn q σ e m hE w s k l zr yr hs' hkr hls hne v₁ v₂
        rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
          w s l zr yr hs' hls v₁] at heq₁
        rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
          w s l zr yr hs' hls v₂] at heq₂
        exact xor_left_cancelP (heq₁.symm.trans (hleft.trans heq₂))
      · have hrs' : r < s := horder.resolve_right (fun h => hrs h.1)
        have hloc : collisionLocP bf hn q σ e m false i j w =
            .inr ⟨zs, bl⟩ := by
          rw [show collisionLocP bf hn q σ e m false i j w =
              responseCoinAtP (coinObsP hn q σ e m w) s (l + 1) by
            simp [collisionLocP, hcell, hrs]]
          exact responseCoinAt_eq_inrP _ s (l + 1) zs ys hs' bl.isLt
        rw [costAt, hcell]
        simp only [CollisionCell.bound, hrs, Bool.false_eq_true, ↓reduceIte,
          CollisionCell.Bound.cost]
        rw [Finset.card_le_one]
        intro v₁ hv₁ v₂ hv₂
        have heq₁ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailTail r k s l) hcell hv₁
        have heq₂ := coinBadValues_cell_valuesP bf hn q σ e m hE false
          i j w (.tailTail r k s l) hcell hv₂
        rw [hloc] at heq₁ heq₂
        simp only [CollisionCell.origins, originValueP] at heq₁ heq₂
        rw [blockValue_tail_output_before_response_updateP bf hn q σ e m hE
          w r s k hrs' (zr, yr) zs ys hr' hs' hkr bl v₁] at heq₁
        rw [blockValue_tail_output_before_response_updateP bf hn q σ e m hE
          w r s k hrs' (zr, yr) zs ys hr' hs' hkr bl v₂] at heq₂
        rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
          w s l zs ys hs' hls v₁] at heq₁
        rw [blockValue_tail_output_response_updateP bf hn q σ e m hE
          w s l zs ys hs' hls v₂] at heq₂
        exact xor_left_cancelP (heq₁.symm.trans heq₂)

/-- Exhaustive dispatch over the structural collision table.  There is no
default collision cell: every constructor has to supply its fiber bound. -/
theorem collision_fiber_allP (bf : Hash.BlockField F n)
    (hn : 0 < n) (hTcap : 2 * tcap + 3 < 2 ^ n)
    (hMsg : MessageBlocksInRange n cap) (q σ : ℕ)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j : ℕ) (w : CoinBlocksP n cap tcap) :
    (coinBadValuesP bf hn q σ e m d i j
      (collisionLocP bf hn q σ e m d i j) w).card ≤
      costAt bf (coinObsP hn q σ e m w) d i j := by
  classical
  cases hcell : collisionCellAt bf (coinObsP hn q σ e m w) d i j with
  | none =>
      have hz : (coinBadValuesP bf hn q σ e m d i j
          (collisionLocP bf hn q σ e m d i j) w).card = 0 := by
        rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨v, hv⟩
        have hcoll := (Finset.mem_filter.mp hv).2
        have hnone : collisionCellAt bf (coinObsP hn q σ e m
            (coinUpdateP w (collisionLocP bf hn q σ e m d i j w) v)) d i j =
            none := by
          rw [collisionCell_self_updateP bf hn q σ e m hE, hcell]
        obtain ⟨p, -⟩ := hcoll
        have hpCell := p.cell_at_eq_some
        rw [hnone] at hpCell
        simp at hpCell
      rw [hz, costAt, hcell]
  | some cell =>
      cases cell with
      | seedSeed a b =>
          exact collision_fiber_seedSeedP bf hn q σ e m hE d i j a b w hcell
      | seedHead a s =>
          exact collision_fiber_seedHeadP bf hn hTcap q σ e m hE
            d i j a s w hcell
      | seedTail a s k =>
          exact collision_fiber_seedTailP bf hn q σ e m hE
            d i j a s k w hcell
      | headSeed s a =>
          exact collision_fiber_headSeedP bf hn q σ e m
            d i j s a w hcell
      | tailSeed s k a =>
          exact collision_fiber_tailSeedP bf hn q σ e m
            d i j s k a w hcell
      | headHead r s =>
          exact collision_fiber_headHeadP bf hn hTcap q σ e m hE
            d i j r s w hcell
      | headTail r s k =>
          exact collision_fiber_headTailP bf hn q σ e m hE
            d i j r s k w hcell
      | tailHead r k s =>
          exact collision_fiber_tailHeadP bf hn hTcap q σ e m hE
            d i j r k s w hcell
      | tailTail r k s l =>
          exact collision_fiber_tailTailP bf hn hMsg q σ e m hE
            d i j r k s l w hcell

set_option autoImplicit false

/-! #### The table summation

The fibre proof above establishes the cost of each exhaustive collision cell.
The remaining argument is purely finite counting.  We first identify the
positional square sum with the strict upper-triangle sum of the common label
layout, then split that layout into the two seeds and one block per answered
query.  The final three receipts are exactly the paper's resources:

* total query-block charge is at most sigma;
* total degree excess is at most sigma;
* the number of answered queries is at most q.

No non-pointless hypothesis enters this arithmetic layer. -/

private def pairSum {A : Type*} (f : A → A → ℕ) : List A → ℕ
  | [] => 0
  | x :: xs => (xs.map (f x)).sum + pairSum f xs

private def atPair {A : Type*} (f : A → A → ℕ) (xs : List A)
    (i j : ℕ) : ℕ :=
  if i < j then
    match xs[i]?, xs[j]? with
    | some x, some y => f x y
    | _, _ => 0
  else 0

private def rangePairSum {A : Type*} (f : A → A → ℕ)
    (xs : List A) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, atPair f xs i j

private theorem atPair_append_old {A : Type*} (f : A → A → ℕ)
    (xs : List A) (x : A) (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) :
    atPair f (xs ++ [x]) i j = atPair f xs i j := by
  simp [atPair, List.getElem?_append, hi, hj]

private theorem atPair_append_new {A : Type*} (f : A → A → ℕ)
    (xs : List A) (x : A) (i : ℕ) (hi : i < xs.length) :
    atPair f (xs ++ [x]) i xs.length =
      match xs[i]? with | some y => f y x | none => 0 := by
  simp [atPair, List.getElem?_append, hi]

private theorem atPair_append_back_zero {A : Type*} (f : A → A → ℕ)
    (xs : List A) (x : A) (j : ℕ) (hj : j ≤ xs.length) :
    atPair f (xs ++ [x]) xs.length j = 0 := by
  simp [atPair, show ¬ xs.length < j by omega]

private theorem sum_getElem?_map {A : Type*} (g : A → ℕ) (xs : List A) :
    (∑ i ∈ Finset.range xs.length,
      match xs[i]? with | some x => g x | none => 0) = (xs.map g).sum := by
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Fin.sum_ofFn]
  simpa [List.getElem?_eq_getElem] using
    congrArg List.sum (List.ofFn_comp' xs.get g)

private theorem pairSum_append_singleton {A : Type*} (f : A → A → ℕ)
    (xs : List A) (x : A) :
    pairSum f (xs ++ [x]) = pairSum f xs + (xs.map (fun y => f y x)).sum := by
  induction xs with
  | nil => simp [pairSum]
  | cons a xs ih =>
      simp [pairSum, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem range_atPair_exact {A : Type*} (f : A → A → ℕ) (xs : List A) :
    (∑ i ∈ Finset.range xs.length, ∑ j ∈ Finset.range xs.length,
      atPair f xs i j) = pairSum f xs := by
  induction xs using List.reverseRecOn with
  | nil => simp [pairSum]
  | append_singleton xs x ih =>
      rw [List.length_append, List.length_singleton,
        Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, pairSum_append_singleton]
      rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj =>
        atPair_append_old f xs x i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)))]
      rw [ih]
      rw [Finset.sum_congr rfl (fun i hi =>
        atPair_append_new f xs x i (Finset.mem_range.mp hi))]
      rw [sum_getElem?_map]
      have hback : (∑ j ∈ Finset.range xs.length,
          atPair f (xs ++ [x]) xs.length j) = 0 := by
        exact Finset.sum_eq_zero (fun j hj =>
          atPair_append_back_zero f xs x j
            (Nat.le_of_lt (Finset.mem_range.mp hj)))
      rw [hback]
      simp [atPair]

private theorem rangePairSum_succ_of_length_le {A : Type*} (f : A → A → ℕ)
    (xs : List A) (N : ℕ) (hN : xs.length ≤ N) :
    rangePairSum f xs (N + 1) = rangePairSum f xs N := by
  unfold rangePairSum
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  rw [Finset.sum_add_distrib]
  have hnone : xs[N]? = none := List.getElem?_eq_none hN
  simp [atPair, hnone]

private theorem rangePairSum_eq_pairSum {A : Type*} (f : A → A → ℕ)
    (xs : List A) (N : ℕ) (hN : xs.length ≤ N) :
    rangePairSum f xs N = pairSum f xs := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero =>
      simpa [rangePairSum] using range_atPair_exact f xs
  | succ k ih =>
      rw [Nat.add_succ, rangePairSum_succ_of_length_le f xs
        (xs.length + k) (Nat.le_add_right xs.length k)]
      exact ih (Nat.le_add_right xs.length k)

private theorem costAt_eq_atPair (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (d : Bool) (i j : ℕ) :
    costAt bf o d i j =
      atPair (cost d (degOf o) (dirOf o)) (labelsOf bf o d) i j := by
  unfold costAt collisionCellAt atPair labelAt labelsOf cost
  by_cases hij : i < j
  · simp only [hij, if_true]
    cases hi : (sideOf bf o d)[i]? <;>
      cases hj : (sideOf bf o d)[j]? <;> simp [hi, hj]
  · simp [hij]

private theorem sideCostSum_eq_pairSum (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (d : Bool) (N : ℕ)
    (hN : (labelsOf bf o d).length ≤ N) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, costAt bf o d i j) =
      pairSum (cost d (degOf o) (dirOf o)) (labelsOf bf o d) := by
  simp_rw [costAt_eq_atPair]
  exact rangePairSum_eq_pairSum _ _ _ hN

private def pairCost (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (a b : Origin) : ℕ :=
  cost true deg dir a b + cost false deg dir a b

private theorem sum_map_add {A : Type*} (f g : A → ℕ) (xs : List A) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem pairSum_add {A : Type*} (f g : A → A → ℕ) (xs : List A) :
    pairSum (fun x y => f x y + g x y) xs = pairSum f xs + pairSum g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [pairSum, sum_map_add, ih]
      omega

private theorem costSum_eq_pairSum (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (q σ : ℕ) (hn : 0 < n)
    (hbudget : Budget q σ (answered o)) :
    costSum bf o σ =
      pairSum (pairCost (degOf o) (dirOf o)) (labelsOf bf o true) := by
  have hsigma := sigmaM_le_of_budget bf o q σ hn hbudget
  have htrue : (labelsOf bf o true).length ≤ σ + 2 := by
    simpa [labelsOf] using
      (le_trans (length_sideOf_le bf o true hn) hsigma)
  have hfalse : (labelsOf bf o false).length ≤ σ + 2 := by
    simpa [labelsOf] using
      (le_trans (length_sideOf_le bf o false hn) hsigma)
  rw [costSum]
  simp_rw [Finset.sum_add_distrib]
  rw [sideCostSum_eq_pairSum bf o true (σ + 2) htrue,
    sideCostSum_eq_pairSum bf o false (σ + 2) hfalse]
  rw [labelsOf_eq bf o false hn, labelsOf_eq bf o true hn]
  exact (pairSum_add
    (cost true (degOf o) (dirOf o))
    (cost false (degOf o) (dirOf o)) _).symm

private def crossSum {A : Type*} (f : A → A → ℕ)
    (xs ys : List A) : ℕ :=
  (xs.map (fun x => (ys.map (f x)).sum)).sum

private theorem sum_map_append {A : Type*} (f : A → ℕ) (xs ys : List A) :
    ((xs ++ ys).map f).sum = (xs.map f).sum + (ys.map f).sum := by
  simp

private theorem crossSum_append_right {A : Type*} (f : A → A → ℕ)
    (xs ys zs : List A) :
    crossSum f xs (ys ++ zs) = crossSum f xs ys + crossSum f xs zs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [crossSum, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem pairSum_append {A : Type*} (f : A → A → ℕ)
    (xs ys : List A) :
    pairSum f (xs ++ ys) =
      pairSum f xs + crossSum f xs ys + pairSum f ys := by
  induction xs with
  | nil => simp [pairSum, crossSum]
  | cons x xs ih =>
      simp only [List.cons_append, pairSum, List.map_append, List.sum_append,
        crossSum, List.map_cons, List.sum_cons]
      rw [ih]
      rw [show (List.map (fun x => (List.map (f x) ys).sum) xs).sum =
        crossSum f xs ys by rfl]
      omega

private theorem pairCost_seedSeed (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (a b : ℕ) : pairCost deg dir (.seed a) (.seed b) = 1 := by
  simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
    CollisionCell.Bound.cost]

private theorem pairCost_seedBlock_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (a s k : ℕ) :
    pairCost deg dir (.seed a) (.block s k) ≤
      2 + if k = 0 then deg s - 1 else 0 := by
  cases k with
  | zero =>
      cases h : dir s <;>
        simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
          CollisionCell.Bound.cost, h] <;> omega
  | succ k =>
      simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
        CollisionCell.Bound.cost]

private theorem pairCost_sameBlock_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (s k l : ℕ) (hkl : k < l) :
    pairCost deg dir (.block s k) (.block s l) ≤ 2 := by
  cases k with
  | zero =>
      cases l with
      | zero => omega
      | succ l =>
          simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
            CollisionCell.Bound.cost]
  | succ k =>
      cases l with
      | zero => omega
      | succ l =>
          simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
            CollisionCell.Bound.cost]

private theorem pairCost_crossBlock_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (r s k l : ℕ) (hrs : r ≠ s) (hdr : 1 ≤ deg r) (hds : 1 ≤ deg s) :
    pairCost deg dir (.block r k) (.block s l) ≤
      2 + (if k = 0 ∧ l = 0 then (deg r - 1) + (deg s - 1) else 0) +
        (if k ≠ 0 ∧ l = 0 then deg s - 1 else 0) := by
  cases k with
  | zero =>
      cases l with
      | zero =>
          cases h : dir s <;>
            simp only [pairCost, cost, cellOfOrigins, CollisionCell.bound,
              CollisionCell.Bound.cost, hrs, h, Bool.false_eq_true,
              Bool.true_eq_false, ↓reduceIte, true_and, if_true,
              zero_ne_one, false_and, if_false]
          · have hm : max (deg r) (deg s) ≤
                (deg r - 1) + (deg s - 1) + 1 :=
              max_le (by omega) (by omega)
            omega
          · have hm : max (deg r) (deg s) ≤
                (deg r - 1) + (deg s - 1) + 1 :=
              max_le (by omega) (by omega)
            omega
      | succ l =>
          simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
            CollisionCell.Bound.cost]
  | succ k =>
      cases l with
      | zero =>
          cases h : dir s <;>
            simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
              CollisionCell.Bound.cost, hrs, h] <;> omega
      | succ l =>
          simp [pairCost, cost, cellOfOrigins, CollisionCell.bound,
            CollisionCell.Bound.cost, hrs]

private theorem sum_map_le_mul_length {A : Type*} (g : A → ℕ)
    (xs : List A) (C : ℕ) (hg : ∀ x ∈ xs, g x ≤ C) :
    (xs.map g).sum ≤ C * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hg
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ht := ih hg.2
      have hx := hg.1
      nlinarith

private theorem pairSum_le_choose_of_pairwise {A : Type*} (f : A → A → ℕ)
    (R : A → A → Prop) (xs : List A) (C : ℕ)
    (hpair : xs.Pairwise R) (hf : ∀ x y, R x y → f x y ≤ C) :
    pairSum f xs ≤ C * xs.length.choose 2 := by
  induction xs with
  | nil => simp [pairSum]
  | cons x xs ih =>
      rw [List.pairwise_cons] at hpair
      simp only [pairSum, List.length_cons]
      have hhead : (xs.map (f x)).sum ≤ C * xs.length := by
        exact sum_map_le_mul_length (f x) xs C
          (fun y hy => hf x y (hpair.1 y hy))
      have htail := ih hpair.2
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith

private def SameQueryBefore (s : ℕ) : Origin → Origin → Prop
  | .block r k, .block t l => r = s ∧ t = s ∧ k < l
  | _, _ => False

private theorem queryLabels_pairwise_same
    (entry : TQ n cap tcap × TM n cap) (s : ℕ) :
    (queryLabels entry s).Pairwise (SameQueryBefore s) := by
  rw [queryLabels, List.pairwise_map]
  simpa [SameQueryBefore] using
    (List.pairwise_lt_range : (List.range (entryCharge entry)).Pairwise (· < ·))

private theorem pairSum_queryLabels_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (entry : TQ n cap tcap × TM n cap) (s : ℕ) :
    pairSum (pairCost deg dir) (queryLabels entry s) ≤
      2 * (entryCharge entry).choose 2 := by
  have hmain := pairSum_le_choose_of_pairwise
    (pairCost deg dir) (SameQueryBefore s) (queryLabels entry s) 2
    (queryLabels_pairwise_same entry s) (by
      intro a b hab
      rcases a with a | ⟨r, k⟩ <;> rcases b with b | ⟨t, l⟩ <;>
        simp [SameQueryBefore] at hab
      rcases hab with ⟨hr, ht, hkl⟩
      simpa [hr, ht] using pairCost_sameBlock_le deg dir s k l hkl)
  simpa [queryLabels] using hmain

private theorem seedToQuerySum_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (a : ℕ) (entry : TQ n cap tcap × TM n cap) (s : ℕ) :
    ((queryLabels entry s).map (pairCost deg dir (.seed a))).sum ≤
      2 * entryCharge entry + (deg s - 1) := by
  have hm : entryCharge entry = 1 + numBlocks n entry.1.2.2.1.val := by
    rw [entryCharge, numBlocks_Msg_len entry.1.2.2 hn]
  rw [queryLabels, hm, range_map_succ]
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_apply]
  have hhead : pairCost deg dir (.seed a) (.block s 0) ≤
      2 + (deg s - 1) := by
    simpa using pairCost_seedBlock_le deg dir a s 0
  have htail :
      (((List.range (numBlocks n entry.1.2.2.1.val)).map
        (pairCost deg dir (.seed a) ∘ fun i => .block s (i + 1))).sum) ≤
        2 * numBlocks n entry.1.2.2.1.val := by
    simpa using sum_map_le_mul_length
      (pairCost deg dir (.seed a) ∘ fun i => .block s (i + 1))
      (List.range (numBlocks n entry.1.2.2.1.val)) 2 (by
        intro i hi
        simpa using pairCost_seedBlock_le deg dir a s (i + 1))
  omega

private theorem seedsToQueryCross_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (entry : TQ n cap tcap × TM n cap) (s : ℕ) :
    crossSum (pairCost deg dir) [.seed 0, .seed 1] (queryLabels entry s) ≤
      4 * entryCharge entry + 2 * (deg s - 1) := by
  simp only [crossSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  have h₀ := seedToQuerySum_le deg dir hn 0 entry s
  have h₁ := seedToQuerySum_le deg dir hn 1 entry s
  omega

private theorem headToQuerySum_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (r s : ℕ) (hrs : r ≠ s)
    (hdr : 1 ≤ deg r) (hds : 1 ≤ deg s)
    (entry : TQ n cap tcap × TM n cap) :
    ((queryLabels entry s).map (pairCost deg dir (.block r 0))).sum ≤
      2 * entryCharge entry + (deg r - 1) + (deg s - 1) := by
  have hm : entryCharge entry = 1 + numBlocks n entry.1.2.2.1.val := by
    rw [entryCharge, numBlocks_Msg_len entry.1.2.2 hn]
  rw [queryLabels, hm, range_map_succ]
  simp only [List.map_cons, List.sum_cons, List.map_map]
  have hhead : pairCost deg dir (.block r 0) (.block s 0) ≤
      2 + ((deg r - 1) + (deg s - 1)) := by
    simpa using pairCost_crossBlock_le deg dir r s 0 0 hrs hdr hds
  have htail :
      (((List.range (numBlocks n entry.1.2.2.1.val)).map
        (pairCost deg dir (.block r 0) ∘ fun i => .block s (i + 1))).sum) ≤
        2 * numBlocks n entry.1.2.2.1.val := by
    simpa using sum_map_le_mul_length
      (pairCost deg dir (.block r 0) ∘ fun i => .block s (i + 1))
      (List.range (numBlocks n entry.1.2.2.1.val)) 2 (by
        intro i hi
        simpa using pairCost_crossBlock_le deg dir r s 0 (i + 1)
          hrs hdr hds)
  omega

private theorem tailToQuerySum_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (r s k : ℕ) (hrs : r ≠ s)
    (hdr : 1 ≤ deg r) (hds : 1 ≤ deg s)
    (entry : TQ n cap tcap × TM n cap) :
    ((queryLabels entry s).map (pairCost deg dir (.block r (k + 1)))).sum ≤
      2 * entryCharge entry + (deg s - 1) := by
  have hm : entryCharge entry = 1 + numBlocks n entry.1.2.2.1.val := by
    rw [entryCharge, numBlocks_Msg_len entry.1.2.2 hn]
  rw [queryLabels, hm, range_map_succ]
  simp only [List.map_cons, List.sum_cons, List.map_map]
  have hhead : pairCost deg dir (.block r (k + 1)) (.block s 0) ≤
      2 + (deg s - 1) := by
    simpa using pairCost_crossBlock_le deg dir r s (k + 1) 0 hrs hdr hds
  have htail :
      (((List.range (numBlocks n entry.1.2.2.1.val)).map
        (pairCost deg dir (.block r (k + 1)) ∘
          fun i => .block s (i + 1))).sum) ≤
        2 * numBlocks n entry.1.2.2.1.val := by
    simpa using sum_map_le_mul_length
      (pairCost deg dir (.block r (k + 1)) ∘ fun i => .block s (i + 1))
      (List.range (numBlocks n entry.1.2.2.1.val)) 2 (by
        intro i hi
        simpa using pairCost_crossBlock_le deg dir r s (k + 1) (i + 1)
          hrs hdr hds)
  omega

private theorem queriesCross_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (r s : ℕ) (hrs : r ≠ s)
    (hdr : 1 ≤ deg r) (hds : 1 ≤ deg s)
    (er es : TQ n cap tcap × TM n cap) :
    crossSum (pairCost deg dir) (queryLabels er r) (queryLabels es s) ≤
      2 * entryCharge er * entryCharge es +
        (deg r - 1) + (deg s - 1) +
          (entryCharge er - 1) * (deg s - 1) := by
  have hmr : entryCharge er = 1 + numBlocks n er.1.2.2.1.val := by
    rw [entryCharge, numBlocks_Msg_len er.1.2.2 hn]
  rw [queryLabels, hmr, range_map_succ]
  simp only [crossSum, List.map_cons, List.sum_cons, List.map_map]
  have hhead := headToQuerySum_le deg dir hn r s hrs hdr hds es
  have htails :
      (((List.range (numBlocks n er.1.2.2.1.val)).map
        ((fun x => ((queryLabels es s).map (pairCost deg dir x)).sum) ∘
          fun k => .block r (k + 1))).sum) ≤
        (2 * entryCharge es + (deg s - 1)) *
          numBlocks n er.1.2.2.1.val := by
    simpa using sum_map_le_mul_length
      ((fun x => ((queryLabels es s).map (pairCost deg dir x)).sum) ∘
        fun k => .block r (k + 1))
      (List.range (numBlocks n er.1.2.2.1.val))
      (2 * entryCharge es + (deg s - 1)) (by
        intro k hk
        exact tailToQuerySum_le deg dir hn r s k hrs hdr hds es)
  rw [show 1 + numBlocks n er.1.2.2.1.val - 1 =
    numBlocks n er.1.2.2.1.val by omega]
  nlinarith

private abbrev CountEntry (n cap tcap : ℕ) :=
  (TQ n cap tcap × TM n cap) × (Σ w : ℕ, BitString w)

private def chargeSum : List (CountEntry n cap tcap) → ℕ
  | [] => 0
  | e :: es => entryCharge e.1 + chargeSum es

private def excessSumFrom (deg : ℕ → ℕ) :
    ℕ → List (CountEntry n cap tcap) → ℕ
  | _, [] => 0
  | s, _ :: es => (deg s - 1) + excessSumFrom deg (s + 1) es

private def StatsValid (deg : ℕ → ℕ) :
    ℕ → List (CountEntry n cap tcap) → Prop
  | _, [] => True
  | s, e :: es =>
      1 ≤ deg s ∧ entryCharge e.1 ≤ deg s ∧ StatsValid deg (s + 1) es

private theorem queryCrossLayout_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (er : TQ n cap tcap × TM n cap) (r start : ℕ)
    (hrs : r < start) (hdr : 1 ≤ deg r)
    (entries : List (CountEntry n cap tcap))
    (hvalid : StatsValid deg start entries) :
    crossSum (pairCost deg dir) (queryLabels er r)
        (queryLayoutFromP start entries) ≤
      2 * entryCharge er * chargeSum entries +
        entries.length * (deg r - 1) + excessSumFrom deg start entries +
          (entryCharge er - 1) * excessSumFrom deg start entries := by
  induction entries generalizing start with
  | nil => simp [queryLayoutFromP, crossSum, chargeSum, excessSumFrom]
  | cons es entries ih =>
      simp only [StatsValid] at hvalid
      rw [queryLayoutFromP, crossSum_append_right]
      have hlocal := queriesCross_le deg dir hn r start (Nat.ne_of_lt hrs)
        hdr hvalid.1 er es.1
      have hrest := ih (start + 1) (by omega) hvalid.2.2
      simp only [chargeSum, excessSumFrom, List.length_cons]
      nlinarith

private theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_succ_succ, Nat.choose_one_right, ih]
      ring

private theorem queryLayoutPairSum_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (start : ℕ) (entries : List (CountEntry n cap tcap))
    (hvalid : StatsValid deg start entries) :
    pairSum (pairCost deg dir) (queryLayoutFromP start entries) ≤
      2 * (chargeSum entries).choose 2 +
        (entries.length - 1) * excessSumFrom deg start entries +
          (excessSumFrom deg start entries).choose 2 := by
  induction entries generalizing start with
  | nil => simp [queryLayoutFromP, pairSum, chargeSum, excessSumFrom]
  | cons entry entries ih =>
      cases entries with
      | nil =>
          simp only [StatsValid] at hvalid
          have hwithin := pairSum_queryLabels_le deg dir entry.1 start
          simp only [queryLayoutFromP, List.append_nil, chargeSum,
            excessSumFrom, List.length_cons, List.length_nil,
            Nat.succ_sub_one, zero_mul, add_zero]
          omega
      | cons next rest =>
          simp only [StatsValid] at hvalid
          rw [queryLayoutFromP, pairSum_append]
          have hwithin := pairSum_queryLabels_le deg dir entry.1 start
          have hcross := queryCrossLayout_le deg dir hn entry.1 start (start + 1)
            (by omega) hvalid.1 (next :: rest) hvalid.2.2
          have htail := ih (start + 1) hvalid.2.2
          have hmle : entryCharge entry.1 - 1 ≤ deg start - 1 :=
            Nat.sub_le_sub_right hvalid.2.1 1
          have hprod : (entryCharge entry.1 - 1) *
                excessSumFrom deg (start + 1) (next :: rest) ≤
              (deg start - 1) *
                excessSumFrom deg (start + 1) (next :: rest) :=
            Nat.mul_le_mul_right _ hmle
          have hlength :
              excessSumFrom deg (start + 1) (next :: rest) +
                  ((next :: rest).length - 1) *
                    excessSumFrom deg (start + 1) (next :: rest) =
                (next :: rest).length *
                  excessSumFrom deg (start + 1) (next :: rest) := by
            simp only [List.length_cons, Nat.succ_sub_one]
            ring
          change pairSum (pairCost deg dir) (queryLabels entry.1 start) +
                crossSum (pairCost deg dir) (queryLabels entry.1 start)
                  (queryLayoutFromP (start + 1) (next :: rest)) +
                pairSum (pairCost deg dir)
                  (queryLayoutFromP (start + 1) (next :: rest)) ≤
              2 * (entryCharge entry.1 + chargeSum (next :: rest)).choose 2 +
                (next :: rest).length *
                  ((deg start - 1) +
                    excessSumFrom deg (start + 1) (next :: rest)) +
                ((deg start - 1) +
                  excessSumFrom deg (start + 1) (next :: rest)).choose 2
          rw [choose_two_add (entryCharge entry.1)
            (chargeSum (next :: rest))]
          rw [choose_two_add (deg start - 1)
            (excessSumFrom deg (start + 1) (next :: rest))]
          nlinarith

private theorem seedsToLayoutCross_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (start : ℕ) (entries : List (CountEntry n cap tcap)) :
    crossSum (pairCost deg dir) [.seed 0, .seed 1]
        (queryLayoutFromP start entries) ≤
      4 * chargeSum entries + 2 * excessSumFrom deg start entries := by
  induction entries generalizing start with
  | nil => simp [queryLayoutFromP, crossSum, chargeSum, excessSumFrom]
  | cons entry entries ih =>
      rw [queryLayoutFromP, crossSum_append_right]
      have hhead := seedsToQueryCross_le deg dir hn entry.1 start
      have htail := ih (start + 1)
      simp only [chargeSum, excessSumFrom]
      nlinarith

private theorem fullLayoutPairSum_le (deg : ℕ → ℕ) (dir : ℕ → Bool)
    (hn : 0 < n) (start : ℕ) (entries : List (CountEntry n cap tcap))
    (hvalid : StatsValid deg start entries) :
    pairSum (pairCost deg dir)
        (.seed 0 :: .seed 1 :: queryLayoutFromP start entries) ≤
      1 + 4 * chargeSum entries +
        2 * (chargeSum entries).choose 2 +
        2 * excessSumFrom deg start entries +
        (entries.length - 1) * excessSumFrom deg start entries +
        (excessSumFrom deg start entries).choose 2 := by
  change pairSum (pairCost deg dir)
      ([.seed 0, .seed 1] ++ queryLayoutFromP start entries) ≤ _
  rw [pairSum_append]
  have hseed : pairSum (pairCost deg dir) [.seed 0, .seed 1] = 1 := by
    simp [pairSum, pairCost_seedSeed]
  rw [hseed]
  have hcross := seedsToLayoutCross_le deg dir hn start entries
  have hqueries := queryLayoutPairSum_le deg dir hn start entries hvalid
  nlinarith

private theorem statsValid_of_get (deg : ℕ → ℕ) (start : ℕ)
    (entries : List (CountEntry n cap tcap))
    (h : ∀ i (hi : i < entries.length),
      1 ≤ deg (start + i) ∧ entryCharge entries[i].1 ≤ deg (start + i)) :
    StatsValid deg start entries := by
  induction entries generalizing start with
  | nil => simp [StatsValid]
  | cons entry entries ih =>
      simp only [StatsValid]
      have hzero := h 0 (by simp)
      refine ⟨by simpa using hzero.1, by simpa using hzero.2, ?_⟩
      apply ih (start + 1)
      intro i hi
      have hnext := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

private theorem polyDegree_eq_qBlocks (hn : 0 < n) (z : TQ n cap tcap) :
    Poly.d n z.2.1.len z.2.2.1.val = qBlocks z := by
  rw [Poly.d, qBlocks, numBlocks_Msg_len z.2.2 hn]
  omega

private theorem statsValid_actual (o : AugObs n cap tcap) (hn : 0 < n) :
    StatsValid (degOf o) 0
      ((transcriptEntries o.1).zip o.2.2) := by
  apply statsValid_of_get (degOf o) 0
  intro i hi
  have hix : i < (transcriptEntries o.1).length := by
    rw [List.length_zip] at hi
    omega
  have hsel : (transcriptEntries o.1)[i]? =
      some (transcriptEntries o.1)[i] := List.getElem?_eq_getElem hix
  have hdeg : degOf o i = qBlocks (transcriptEntries o.1)[i].1 :=
    (degOf_eq_of_entryP o i (transcriptEntries o.1)[i].1
      (transcriptEntries o.1)[i].2 hsel).trans
        (polyDegree_eq_qBlocks hn (transcriptEntries o.1)[i].1)
  have hentry :
      (((transcriptEntries o.1).zip o.2.2)[i]).1 =
        (transcriptEntries o.1)[i] := by
    rw [List.getElem_zip]
  have hmpos : 1 ≤ entryCharge (transcriptEntries o.1)[i] := by
    rw [entryCharge, numBlocks_Msg_len (transcriptEntries o.1)[i].1.2.2 hn]
    omega
  constructor
  · simp only [Nat.zero_add]
    rw [hdeg]
    exact le_trans hmpos (entryCharge_le_qBlocks (transcriptEntries o.1)[i])
  · simp only [Nat.zero_add]
    rw [hentry, hdeg]
    exact entryCharge_le_qBlocks (transcriptEntries o.1)[i]

private theorem chargeSum_eq_map_sum (entries : List (CountEntry n cap tcap)) :
    chargeSum entries = (entries.map (fun e => entryCharge e.1)).sum := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp [chargeSum, ih]

private theorem chargeSum_actual_le (o : AugObs n cap tcap) (q σ : ℕ)
    (hbudget : Budget q σ (answered o)) :
    chargeSum ((transcriptEntries o.1).zip o.2.2) ≤ σ := by
  rw [chargeSum_eq_map_sum]
  have hzip := sum_map_zip_le
    (entryCharge (n := n) (cap := cap) (tcap := tcap))
    (transcriptEntries o.1) o.2.2
  have hentry := sum_entryCharge_le (n := n) (cap := cap) (tcap := tcap)
    (transcriptEntries o.1)
  have hqueries : (transcriptEntries o.1).map (qBlocks ∘ Prod.fst) =
      (answered o).map qBlocks := by
    rw [answered, ← List.map_map, PFunDDS.answeredEntries_map_fst]
  rw [hqueries] at hentry
  exact hzip.trans (hentry.trans hbudget.2)

private theorem entriesLength_actual_le (o : AugObs n cap tcap) (q σ : ℕ)
    (hbudget : Budget q σ (answered o)) :
    ((transcriptEntries o.1).zip o.2.2).length ≤ q := by
  have hzip : ((transcriptEntries o.1).zip o.2.2).length ≤
      (transcriptEntries o.1).length := by
    rw [List.length_zip]
    omega
  have hlen : (transcriptEntries o.1).length = (answered o).length := by
    rw [answered, ← PFunDDS.answeredEntries_map_fst]
    simp
  rw [hlen] at hzip
  exact hzip.trans hbudget.1

private theorem excessSumFrom_le_map_sum_of_get (deg : ℕ → ℕ) (start : ℕ)
    (entries : List (CountEntry n cap tcap)) (b : CountEntry n cap tcap → ℕ)
    (h : ∀ i (hi : i < entries.length), deg (start + i) - 1 ≤ b entries[i]) :
    excessSumFrom deg start entries ≤ (entries.map b).sum := by
  induction entries generalizing start with
  | nil => simp [excessSumFrom]
  | cons entry entries ih =>
      have hzero := h 0 (by simp)
      have htail := ih (start + 1) (by
        intro i hi
        have hnext := h (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)
      simp only [excessSumFrom, List.map_cons, List.sum_cons]
      simpa using Nat.add_le_add hzero htail

private theorem excessSum_actual_le (o : AugObs n cap tcap) (q σ : ℕ)
    (hn : 0 < n) (hbudget : Budget q σ (answered o)) :
    excessSumFrom (degOf o) 0
        ((transcriptEntries o.1).zip o.2.2) ≤ σ := by
  let entries := (transcriptEntries o.1).zip o.2.2
  let b : CountEntry n cap tcap → ℕ := fun entry => qBlocks entry.1.1
  have hexcess : excessSumFrom (degOf o) 0 entries ≤
      (entries.map b).sum := by
    apply excessSumFrom_le_map_sum_of_get (degOf o) 0 entries b
    intro i hi
    have hix : i < (transcriptEntries o.1).length := by
      dsimp [entries] at hi
      rw [List.length_zip] at hi
      omega
    have hsel : (transcriptEntries o.1)[i]? =
        some (transcriptEntries o.1)[i] := List.getElem?_eq_getElem hix
    have hdeg : degOf o i = qBlocks (transcriptEntries o.1)[i].1 :=
      (degOf_eq_of_entryP o i (transcriptEntries o.1)[i].1
        (transcriptEntries o.1)[i].2 hsel).trans
          (polyDegree_eq_qBlocks hn (transcriptEntries o.1)[i].1)
    have hentry : entries[i].1 = (transcriptEntries o.1)[i] := by
      dsimp [entries]
      rw [List.getElem_zip]
    simp only [Nat.zero_add]
    dsimp only [b]
    rw [hentry, hdeg]
    omega
  have hzip := sum_map_zip_le (fun entry : TQ n cap tcap × TM n cap =>
      qBlocks entry.1) (transcriptEntries o.1) o.2.2
  have hqueries : (transcriptEntries o.1).map (qBlocks ∘ Prod.fst) =
      (answered o).map qBlocks := by
    rw [answered, ← List.map_map, PFunDDS.answeredEntries_map_fst]
  have hsum : (entries.map b).sum ≤ ((answered o).map qBlocks).sum := by
    dsimp [entries, b]
    rw [← hqueries]
    exact hzip
  simpa only [entries] using hexcess.trans (hsum.trans hbudget.2)

private theorem labelsOf_eq_fullLayout (bf : Hash.BlockField F n)
    (o : AugObs n cap tcap) (hn : 0 < n) :
    labelsOf bf o true =
      .seed 0 :: .seed 1 ::
        queryLayoutFromP 0 ((transcriptEntries o.1).zip o.2.2) := by
  rw [labelsOf_eq bf o true hn, queryLayoutFrom_eqP]

private theorem costSum_nat_le (bf : Hash.BlockField F n) (o : AugObs n cap tcap)
    (q σ : ℕ) (hn : 0 < n) (hbudget : Budget q σ (answered o)) :
    costSum bf o σ ≤
      1 + 4 * σ + 2 * σ.choose 2 + 2 * σ +
        (q - 1) * σ + σ.choose 2 := by
  let entries := (transcriptEntries o.1).zip o.2.2
  have hvalid : StatsValid (degOf o) 0 entries := by
    simpa only [entries] using statsValid_actual o hn
  have htable := fullLayoutPairSum_le (degOf o) (dirOf o) hn 0 entries hvalid
  have hM : chargeSum entries ≤ σ := by
    simpa only [entries] using chargeSum_actual_le o q σ hbudget
  have hA : excessSumFrom (degOf o) 0 entries ≤ σ := by
    simpa only [entries] using excessSum_actual_le o q σ hn hbudget
  have hN : entries.length ≤ q := by
    simpa only [entries] using entriesLength_actual_le o q σ hbudget
  have hMchoose : (chargeSum entries).choose 2 ≤ σ.choose 2 :=
    Nat.choose_le_choose 2 hM
  have hAchoose : (excessSumFrom (degOf o) 0 entries).choose 2 ≤
      σ.choose 2 := Nat.choose_le_choose 2 hA
  have hcross : (entries.length - 1) * excessSumFrom (degOf o) 0 entries ≤
      (q - 1) * σ :=
    Nat.mul_le_mul (Nat.sub_le_sub_right hN 1) hA
  rw [costSum_eq_pairSum bf o q σ hn hbudget,
    labelsOf_eq_fullLayout bf o hn]
  exact htable.trans (by omega)


/-! #### Closing the two paper obligations -/

/-- **§3.4.2's case analysis** (pp. 12–14, Figures 4 and 5).  Each pair's collision
mass is at most its table entry over `2ⁿ`.

Every case is `Dist.mass_le_of_fiber_bound` with a free coordinate and a solution count:

| paper | free coord | entry | supplied by |
|---|---|---|---|
| "exactly one value of `L` causes the equation to hold" | `L` | `1` | uniformity |
| "at most `dˢ` solutions to a particular polynomial" | `h̄` | `dˢ` | `Poly.Facts.prop1`, `prop3` |
| `MMʳ =? MMˢ`, "max where at most `max(dʳ,dˢ)`" | `h̄` | `max(dʳ,dˢ)` | `Poly.Facts.prop2` |
| `Sᵢˢ =? Sⱼˢ` "which is impossible" | — | `0` | `bin` injectivity |

The right-hand side is an **expectation**, and the reason matters for whoever proves this.
`degOf` and `dirOf` are functions of the observation, and the shape is *not* constant on the
support: a deterministic environment fixes query 1, but query 2 is `e(response 1)`, so the
queries — and hence every `dˢ`, `mˢ` — vary with the coins.  p. 11 warns about exactly this:

  > If we know the adversary's query `s`, then conditioning on that, we cannot treat the
  > response to query `r < s` as uniformly random; if the choice of later query depends on
  > the earlier response, knowing the later query is information about the earlier response.

So condition on a **prefix**, never on the shape.  For a pair spanning queries `r ≤ s`,
`costAt` is fixed by queries `r` and `s`, which are fixed by the responses *before* `s`; the
free coordinate is then either the response to query `s` or one of `h̄`, `L` — a separate
`RndKey` component, independent of everything.  Either way `Dist.mass_le_of_fiber_bound` applies
conditionally on that prefix, and averaging over prefixes gives the statement.

Conditioning on the whole shape instead would condition on *later* responses, which are not
independent of the free coordinate.  That is the trap p. 11 is pointing at. -/
theorem collAt_le_expected_cost (bf : Hash.BlockField F n)
    (hTcap : 2 * tcap + 3 < 2 ^ n) (hMsg : MessageBlocksInRange n cap)
    (q σ : ℕ) (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e)
    (d : Bool) (i j : ℕ) :
    collAt bf (augLawRnd n cap tcap q σ e m).val d i j
      ≤ (∑ o ∈ (augLawRnd n cap tcap q σ e m).val.support,
          (augLawRnd n cap tcap q σ e m).val o *
            (costAt bf o d i j : ℝ)) / 2 ^ n := by
  obtain ⟨hn₂, -⟩ := cap_bounds hTcap
  have hn : 0 < n := by omega
  refine collAt_le_expected_of_coin_fiberP bf hn q σ e m d i j
    (collisionLocP bf hn q σ e m d i j) ?_ ?_ ?_
  · intro w v
    exact collisionLoc_self_updateP bf hn q σ e m hE d i j w v
  · intro w v
    exact collisionCost_self_updateP bf hn q σ e m hE d i j w v
  · intro w
    exact collision_fiber_allP bf hn hTcap hMsg q σ e m hE d i j w

/-- **§3.4.2's summation** (pp. 15–16).  The table's total over all inferred pairs
is `2·C(σₘ,2) + c` with `c = c_b + c_f + c_w + c_a ≤ −1 + 2σ + 0 + ((q−1)σ + C(σ,2))`.

The four `c_•` are the four regions of `cost`: the seed block,
seed-against-query, within-query, and cross-query cells.  The theorem receives
the actual `Budget q σ (answered o)` fact, rather than only its weaker
`σₘ ≤ σ + 2` consequence, so its proof has exactly the paper's two arithmetic
inputs: at most `q` queries and `Σ_s dˢ ≤ σ`.  This is a pure table-counting
statement; non-pointlessness is used by the fibre proof above, not here. -/
theorem costSum_le (bf : Hash.BlockField F n) (o : AugObs n cap tcap) (q σ : ℕ)
    (hn : 0 < n) (hbudget : Budget q σ (answered o)) :
    (costSum bf o σ : ℝ)
      ≤ ((σ : ℝ) + 2) * ((σ : ℝ) + 1) - 1 + 2 * σ + ((q : ℝ) - 1) * σ
          + (σ : ℝ) * ((σ : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hlen := entriesLength_actual_le o 0 σ hbudget
    have hempty : (transcriptEntries o.1).zip o.2.2 = [] :=
      List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    have hcost : costSum bf o σ = 1 := by
      rw [costSum_eq_pairSum bf o 0 σ hn hbudget,
        labelsOf_eq_fullLayout bf o hn, hempty]
      simp [queryLayoutFromP, pairSum, pairCost_seedSeed]
    rw [hcost]
    rcases Nat.eq_zero_or_pos σ with rfl | hσ
    · norm_num
    · have hσr : (1 : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hσ
      have hprod : 0 ≤ (σ : ℝ) * ((σ : ℝ) - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [sq_nonneg (σ : ℝ)]
  · have hnat := costSum_nat_le bf o q σ hn hbudget
    have hreal : (costSum bf o σ : ℝ) ≤
        ((1 + 4 * σ + 2 * σ.choose 2 + 2 * σ +
          (q - 1) * σ + σ.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine hreal.trans_eq ?_
    have hchoose : (2 : ℝ) * (σ.choose 2 : ℝ) =
        (σ : ℝ) * ((σ : ℝ) - 1) := by
      exact_mod_cast two_mul_choose_two_int σ
    push_cast [Nat.cast_sub hq]
    nlinarith

/-- **§3.4.2's bad mass** (p. 17), for a no-pointless environment, proved
from the two obligations above. -/
theorem bad_probability_le (bf : Hash.BlockField F n) (q σ : ℕ)
    (hTcap : 2 * tcap + 3 < 2 ^ n) (hMsg : MessageBlocksInRange n cap)
    (e : PFunDDS.DDE (TQ n cap tcap) (TM n cap)) (m : ℕ)
    (hE : EnvAvoidsPointless (n := n) (cap := cap) (tcap := tcap) e) :
    probBad (augLawRnd n cap tcap q σ e m).val (Bad bf) ≤ badBound n q σ := by
  classical
  obtain ⟨hn2, -⟩ := cap_bounds hTcap
  have hn : 0 < n := by omega
  set law : Dist (AugObs n cap tcap) :=
    (augLawRnd n cap tcap q σ e m).val with hlaw
  have hnn : law.NonNeg := by
    rw [hlaw]
    exact (augLawRnd n cap tcap q σ e m).2.nonNeg
  have hw : law.weight = 1 := by
    rw [hlaw]
    exact (augLawRnd n cap tcap q σ e m).2.weight_eq
  have hbudget : ∀ o ∈ law.support, Budget q σ (answered o) :=
    fun o ho => budget_of_mem_support q σ e m o (by simpa [hlaw] using ho)
  have hsigma : ∀ o ∈ law.support, sigmaM bf o ≤ σ + 2 :=
    fun o ho => sigmaM_le_of_budget bf o q σ hn (hbudget o ho)
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  -- union bound, then the table, then the summation
  refine le_trans (probBad_le_sum_collAt bf law hnn σ hn hsigma) ?_
  have hstep : ∀ p ∈ (Finset.range (σ + 2)) ×ˢ (Finset.range (σ + 2)),
      collAt bf law true p.1 p.2 + collAt bf law false p.1 p.2
        ≤ (∑ o ∈ law.support, law o *
            ((costAt bf o true p.1 p.2 + costAt bf o false p.1 p.2 : ℕ) : ℝ)) / 2 ^ n := by
    intro p _
    have h1 := collAt_le_expected_cost bf hTcap hMsg q σ e m hE true p.1 p.2
    have h2 := collAt_le_expected_cost bf hTcap hMsg q σ e m hE false p.1 p.2
    have hcomb : (∑ o ∈ law.support, law o * ((costAt bf o true p.1 p.2 : ℕ) : ℝ))
        + (∑ o ∈ law.support, law o * ((costAt bf o false p.1 p.2 : ℕ) : ℝ))
        = ∑ o ∈ law.support, law o *
            ((costAt bf o true p.1 p.2 + costAt bf o false p.1 p.2 : ℕ) : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun o _ => by push_cast; ring
    rw [← hcomb, add_div]
    exact add_le_add (by simpa [hlaw] using h1) (by simpa [hlaw] using h2)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_div]
  rw [div_le_iff₀ hpos, badBound, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hpos),
    mul_one]
  -- exchange the two sums, then bound the integrand pointwise by `costSum_le`
  rw [Finset.sum_comm]
  calc ∑ o ∈ law.support, ∑ p ∈ (Finset.range (σ + 2)) ×ˢ (Finset.range (σ + 2)),
          law o * ((costAt bf o true p.1 p.2 + costAt bf o false p.1 p.2 : ℕ) : ℝ)
      = ∑ o ∈ law.support, law o * ((costSum bf o σ : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [costSum, ← Nat.cast_sum, Finset.sum_product]
    _ ≤ ∑ o ∈ law.support, law o * (((σ : ℝ) + 2) * ((σ : ℝ) + 1) - 1 + 2 * σ
          + ((q : ℝ) - 1) * σ + (σ : ℝ) * ((σ : ℝ) - 1) / 2) := by
        refine Finset.sum_le_sum fun o ho => ?_
        exact mul_le_mul_of_nonneg_left
          (costSum_le bf o q σ hn (hbudget o ho)) (hnn o)
    _ = ((σ : ℝ) + 2) * ((σ : ℝ) + 1) - 1 + 2 * σ + ((q : ℝ) - 1) * σ
          + (σ : ℝ) * ((σ : ℝ) - 1) / 2 := by
        rw [← Finset.sum_mul]
        show law.weight * _ = _
        rw [hw, one_mul]

/-- **§3.4's main lemma** (paper p. 17), about the paper's own quantity:

    Adv^{±rnd}_{HCTR2[Perm(n)]}(q, σ)  ≤  (3σ² + 2qσ + 7σ + 2)/2ⁿ⁺¹

`advRnd` ranges over the raw transcript laws of the two systems after the same
`budget q σ` domain filter.  Hence the at-most-query and block-cost facts are
support-local consequences of the resource, not environment premises.  The
separate no-pointless restriction remains only because the intermediate
`±rnd` endpoint is incoherent.  No augmented object appears in the statement. -/
theorem main_lemma_paper (bf : Hash.BlockField F n) (q σ : ℕ)
    (hTcap : 2 * tcap + 3 < 2 ^ n) (hMsg : MessageBlocksInRange n cap) :
    advRnd (cap := cap) (tcap := tcap) bf q σ ≤ mainBound n q σ := by
  -- Expand the paper advantage into the restricted family of transcript-law distances.
  rw [advRnd]
  -- Expose that restricted family as a supremum indexed by allowed `(environment, depth)` pairs.
  unfold restrictedLawFamilyAdvantage
  -- Bound the supremum pointwise; `Real.sSup_le` also asks that `mainBound` be nonnegative.
  refine Real.sSup_le ?_ (by rw [mainBound]; positivity)
  -- Fix one member of the supremum and unpack its environment `e`, depth `m`, and
  -- no-pointless certificate `hE`; `rfl` identifies the member with its distance.
  rintro _ ⟨⟨e, m⟩, hE, rfl⟩
  -- Record nonnegativity of the independent-response augmented law for the H theorem.
  have hAugRndnn : (augLawRnd n cap tcap q σ e m).val.NonNeg :=
    -- The bundled probability-law certificate supplies this fact directly.
    (augLawRnd n cap tcap q σ e m).2.nonNeg
  -- Record nonnegativity of the permutation augmented law for the H theorem.
  have hAugPermnn : (augLawPerm bf q σ e m).val.NonNeg :=
    -- Again this is a projection of the bundled probability-law certificate.
    (augLawPerm bf q σ e m).2.nonNeg
  -- First H obligation: at every supported good observation, the ideal mass is
  -- dominated by the corresponding real mass.
  have good_observation_dominance :
      -- Restrict the comparison to observations in the ideal law's support.
      ∀ o ∈ (augLawRnd n cap tcap q σ e m).val.support, ¬ Bad bf o →
        -- State the required pointwise likelihood dominance.
        (augLawRnd n cap tcap q σ e m).val o ≤
          (augLawPerm bf q σ e m).val o := by
    -- Fix a supported observation `o` and assume it is outside the bad cell.
    intro o ho hgood
    -- Apply the HCTR2 likelihood-ratio calculation on this good observation.
    exact good_ratio_holds bf q σ e m o ho
      -- Convert the environment certificate into the observation-local no-pointless fact.
      (nonPointless_of_mem_support q σ e m hE o ho) hgood
  -- Second H obligation: the ideal law assigns at most `mainBound` mass to `Bad`.
  have ideal_bad_probability :
      probBad (augLawRnd n cap tcap q σ e m).val (Bad bf) ≤ mainBound n q σ := by
    -- First prove the collision analysis's `badBound`, then identify it with the closed formula.
    calc
      -- The complete good/bad-transcript counting argument supplies the bad-event bound.
      probBad (augLawRnd n cap tcap q σ e m).val (Bad bf)
          ≤ badBound n q σ := bad_probability_le bf q σ hTcap hMsg e m hE
      -- The remaining step is the paper's elementary equality between the two formulas.
      _ = mainBound n q σ := badBound_eq_mainBound n q σ
  -- Compose augmentation data processing with the carrier-independent two-cell H theorem.
  calc
    -- Start with the ordinary transcript distance appearing in `advRnd`.
    δ (transcriptDist
        (PFunPDS.filterOf (budget q σ) (rnd n cap tcap).val) e m)
      (transcriptDist
        (PFunPDS.filterOf (budget q σ)
          (hctr2Perm (cap := cap) (tcap := tcap) bf).val) e m)
        -- Forgetting augmentation is deterministic post-processing, so DPI bounds this
        -- ordinary distance by the distance between the richer observation laws.
        ≤ δ (augLawRnd n cap tcap q σ e m).val
          (augLawPerm bf q σ e m).val :=
      -- This theorem packages the two projection identities and data processing.
      δ_le_δ_aug bf q σ e m
    -- Apply zero-defect H to bound the augmented-law distance by the chosen bad bound.
    _ ≤ mainBound n q σ :=
      δ_hTechnique_le_on_good_of_bad_le
        -- The independent-response augmented law is H's ideal distribution.
        (augLawRnd n cap tcap q σ e m).val
        -- The permutation augmented law is H's real distribution.
        (augLawPerm bf q σ e m).val
        -- `Bad` defines the two-cell partition; `mainBound` is the target bad-mass bound.
        (Bad bf) (mainBound n q σ) hAugPermnn hAugRndnn
        -- Discharge exactly H's two application-specific premises proved above.
        good_observation_dominance ideal_bad_probability

end MainLemma

/-! ## Paper §3.5 — Composition of the three comparisons (p. 17)

The declaration below is intentionally written top-down in Maurer's random-
systems notation.  It fixes a distinguisher for the two coherent endpoints,
normalizes that distinguisher to make no pointless queries, telescopes its
signed brackets through `HCTR2[Perm(n)]` and `±rnd`, and only then invokes the
three paper bounds.

Some referenced bridge theorems do not exist yet.  That is deliberate: this
headline theorem is the proof scaffold, and the resulting Lean errors are the
obligation ledger.  Do not replace those bridges by hypotheses or predeclare
helper lemmas merely to make the scaffold compile. -/

namespace FinalTheorem

open Bits Hash HCTR2 Sec MainLemma
open RandomSystems.CR18
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.PFunDDS

variable {F : Type} [Field F] {n cap tcap : ℕ}

/- Maurer's plain bracket `〈S | T〉(D)` is the signed advantage of `D`;
the existing bracket without `(D)` is its supremum over distinguishers. -/
local notation:max "〈" S " | " T "〉(" D ")" => advantage D S T

/-- **HCTR2's p. 17 theorem in Maurer's random-systems notation.**

This is deliberately a non-compiling top-down scaffold.  Each unresolved name
denotes the theorem that the corresponding paper step should provide; none is
smuggled into the statement as a hypothesis. -/
theorem hctr2_security {K : Type} [Fintype K] [Nonempty K]
    (bf : Hash.BlockField F n) (E : K → Perm n) (q σ : ℕ)
    (hTcap : 2 * tcap + 3 < 2 ^ n) (hMsg : MessageBlocksInRange n cap) :
    〈⌈budget q σ⌉ᵈ (hctr2E bf E).val |
        ⌈budget q σ⌉ᵈ (tprp n cap tcap).val〉 ≤
      〈⌈σ + 2⌉ (pmE E).val | ⌈σ + 2⌉ (pmPerm n).val〉 +
        ((3 * σ ^ 2 + 2 * q * σ + q ^ 2 + 7 * σ + 2 : ℕ) : ℝ) /
          (2 : ℝ) ^ (n + 1) := by
  let HCTR2E :=
    ⌈budget (n := n) (cap := cap) (tcap := tcap) q σ⌉ᵈ
      (hctr2E (cap := cap) (tcap := tcap) bf E).val
  let HCTR2Perm :=
    ⌈budget (n := n) (cap := cap) (tcap := tcap) q σ⌉ᵈ
      (hctr2Perm (cap := cap) (tcap := tcap) bf).val
  let pmRnd :=
    ⌈budget (n := n) (cap := cap) (tcap := tcap) q σ⌉ᵈ
      (rnd n cap tcap).val
  let pmTPRP :=
    ⌈budget (n := n) (cap := cap) (tcap := tcap) q σ⌉ᵈ
      (tprp n cap tcap).val
  change 〈HCTR2E | pmTPRP〉 ≤
    advPRP E (σ + 2) +
      ((3 * σ ^ 2 + 2 * q * σ + q ^ 2 + 7 * σ + 2 : ℕ) : ℝ) /
        (2 : ℝ) ^ (n + 1)
  refine maxAdvantage_le_of_forall_advantage_le ?_
  intro D hD
  -- Normalize only at the two coherent endpoints, then keep the same `D'`
  -- through the entire random-systems chain.
  obtain ⟨D', hD', hnonpointless, hsame⟩ :=
    exists_distinguisher_without_pointless_queries bf E q σ D hD
  calc
    〈HCTR2E | pmTPRP〉(D) = 〈HCTR2E | pmTPRP〉(D') := hsame
    -- Maurer's signed brackets telescope exactly for a fixed distinguisher.
    _ = 〈HCTR2E | HCTR2Perm〉(D') +
          (〈HCTR2Perm | pmRnd〉(D') + 〈pmRnd | pmTPRP〉(D')) := by
      unfold advantage
      ring
    -- Each bracket now lands in the corresponding paper-level quantity.
    _ ≤ advPRP E (σ + 2) +
          (advRnd (cap := cap) (tcap := tcap) bf q σ +
            (q.choose 2 : ℝ) / (2 : ℝ) ^ n) :=
      add_le_add
        (hctr2E_hctr2Perm_advantage_le_advPRP bf E q σ D' hD')
        (add_le_add
          (hctr2Perm_rnd_advantage_le_advRnd
            bf q σ D' hD' hnonpointless)
          (rnd_tprp_advantage_le_birthday
            (n := n) (cap := cap) (tcap := tcap)
            q σ D' hD' hnonpointless))
    -- This is exactly §3.4's main lemma, with no transcript machinery exposed.
    _ ≤ advPRP E (σ + 2) +
          (mainBound n q σ + (q.choose 2 : ℝ) / (2 : ℝ) ^ n) :=
      add_le_add_left
        (add_le_add_right
          (main_lemma_paper (cap := cap) (tcap := tcap)
            bf q σ hTcap hMsg)
          ((q.choose 2 : ℝ) / (2 : ℝ) ^ n))
        (advPRP E (σ + 2))
    -- Put the birthday term over the common denominator and use
    -- `2 * choose(q,2) ≤ q²`.
    _ ≤ advPRP E (σ + 2) +
          ((3 * σ ^ 2 + 2 * q * σ + q ^ 2 + 7 * σ + 2 : ℕ) : ℝ) /
            (2 : ℝ) ^ (n + 1) :=
      add_le_add_left (mainBound_add_birthday_le_securityBound n q σ) _

end FinalTheorem

end RandomSystems.HCTR2Final
