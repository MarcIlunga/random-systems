/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # HCTR2 bit-string layer

Paper §2.1 notation and field-free block decomposition. -/

namespace RandomSystems.HCTR2Final
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

/-- A message consists of its mandatory first block and the blocks needed for
its excess-length tail: `ceil((n+j)/n) = 1 + ceil(j/n)`. -/
theorem numBlocks_msg_len {n cap : ℕ} (hn : 0 < n) (m : Msg n cap) :
    numBlocks n m.len = 1 + numBlocks n m.1.val := by
  rw [Msg.len, numBlocks, numBlocks,
    show n + m.1.val + n - 1 = n + (m.1.val + n - 1) by omega,
    Nat.add_div_left _ hn]
  omega

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

/-- Concatenation is an equivalence between a pair of fixed-width strings and
their combined fixed-width string. -/
def concatEquiv (a b : ℕ) : BitString a × BitString b ≃ BitString (a + b) where
  toFun p := p.1 ∥ p.2
  invFun x := (x[0; a], x[a; b])
  left_inv p := by
    apply Prod.ext
    · exact sub_cat_left p.1 p.2
    · exact sub_cat_right p.1 p.2
  right_inv x := cat_sub_sub x

/-- Transport a bit string along an equality of its width indices. -/
def castEquiv {a b : ℕ} (h : a = b) : BitString a ≃ BitString b where
  toFun := BitVec.cast h
  invFun := BitVec.cast h.symm
  left_inv x := by subst b; rfl
  right_inv x := by subst b; rfl

/-- Read a block-aligned bit string as a family of fixed-width blocks. -/
def chunkFun (n m : ℕ) (x : BitString (n * m)) : Fin m → BitString n :=
  fun i => x[n * i.val; n]

theorem chunkFun_injective {n m : ℕ} (hn : 0 < n) :
    Function.Injective (chunkFun n m) := by
  intro x y hxy
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hi : p / n < m := by
    exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hp)
  have hb := congrFun hxy ⟨p / n, hi⟩
  have hbit := congrArg (fun z : BitString n => z.getLsbD (p % n)) hb
  simp only [chunkFun, substring, BitVec.getLsbD_extractLsb'] at hbit
  have hmod : p % n < n := Nat.mod_lt p hn
  have hidx : n * (p / n) + p % n = p := by
    simpa [Nat.add_comm] using Nat.mod_add_div p n
  simpa [hmod, hp, hidx] using hbit

/-- The canonical equivalence between an `n*m`-bit string and `m` independent
`n`-bit blocks. -/
noncomputable def chunkEquiv {n m : ℕ} (hn : 0 < n) :
    BitString (n * m) ≃ (Fin m → BitString n) :=
  Equiv.ofBijective (chunkFun n m)
    ((Fintype.bijective_iff_injective_and_card (chunkFun n m)).2
      ⟨chunkFun_injective hn, by
        rw [Fintype.card_fun, Fintype.card_fin, card_Str,
          card_Str, pow_mul]⟩)

@[simp] theorem chunkEquiv_apply {n m : ℕ} (hn : 0 < n)
    (x : BitString (n * m)) : chunkEquiv hn x = chunkFun n m x := rfl

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

end RandomSystems.HCTR2Final
