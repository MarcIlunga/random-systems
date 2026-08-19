/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

set_option maxRecDepth 4000

/-!
# The concrete POLYVAL field `GF(2¹²⁸) = F₂[X]/(x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1)` (Phase P3)

This file constructs the concrete field underlying the RFC-8452 POLYVAL hash used
by HCTR2 (ePrint 2021/1441), together with the paper's *degenerate-case* argument
(p.7): the collision polynomial can be of degree `1` only when `|T| = |M| = 0`, in
which case it is `x·h`, and *since `xⁿ⁻¹ ≠ 1` we have `xⁿ ≠ x`* — the fact that
eliminates the artificial `1 ≤ τ` hypothesis in a later wiring phase.

## Deliverables (see the phase brief)

* **D1** — `Nat`-encoded `F₂[X]` arithmetic (`f2Mul`, `f2Mod`, `f2MulMod`,
  `f2SqModIter`, `f2PowMod`, `f2Gcd`), all kernel-computable (`decide`-reducible),
  plus the `toPoly : ℕ → (ZMod 2)[X]` bridge and its homomorphism lemmas.
* **D2** — the Rabin irreducibility certificate for
  `mPolyval = x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1`.
* **D3** — the field `GF128`, the Montgomery-style unit `uPolyval = x⁻¹²⁸`, and the
  paper's `xGF_pow_n_ne_x`.
* **D4** — the **canonical** little-endian block encoding `gf128OfNat i =
  mk mPoly (toPoly i)` (paper p.4: bit `j` ↦ coefficient of `xʲ`), its additivity
  `gf128OfNat_xor`, injectivity `gf128OfNat_inj_of_lt`, the bijection
  `gf128FinEquiv`, and the payoff `gf128OfNat_two : bin 2 = x` — which pins the
  block↔bits identification to the power basis and makes the paper's p.7
  degenerate case (`xGF_mul_uPolyval_ne_one`) statable.

## Ledger

-- PHASE P3.D1 DONE: Nat-encoded F₂[X] arithmetic (f2Mul/f2Mod/f2MulMod/f2SqModIter/
--   f2PowMod/f2Gcd, all kernel-`decide`-reducible; toy degree-8 gate green) + the
--   `toPoly` bridge (toPoly_coeff, toPoly_xor/shiftLeft/two_pow, toPoly_f2Mul,
--   toPoly_f2Mod_congr, dvd_toPoly_f2Gcd) / FALLBACK: none
-- PHASE P3.D2 DONE: Rabin certificate — cert1 (`x^(2^128) ≡ x`), cert2 (gcd side)
--   both `by decide +kernel` (axiom-free); converse Rabin direction proved via
--   AdjoinRoot-as-finite-field (`irreducible_dvd_X_pow_pow_sub_X`, not in Mathlib);
--   `mPoly_irreducible` proved (no Fact hypothesis) / FALLBACK: none
-- PHASE P3.D3 DONE: GF128 field + Fintype + gf128_card = 2^128, xGF, uPolyval = x⁻¹²⁸,
--   the paper's `xGF_pow_n_ne_x` (p.7) / FALLBACK: none
-- PHASE P3.D4 DONE: canonical little-endian encoding gf128OfNat/gf128FinEquiv
--   (power basis, NOT Module.finBasis), gf128OfNat_two (`bin 2 = x`), and the
--   correctly-shaped degenerate obligation xGF_mul_uPolyval_ne_one.  Replaced
--   `degenerate_hash_poly_ne_X`, which omitted the dot unit `u`, did not match the
--   real obligation, and had zero consumers / FALLBACK: none
-- TODO(P3.D5): wire D4 into HCTR2Paper (`specBlockBits` → power basis) to drop
--   `htwPos` / `hτ : 1 ≤ τ` and restore the paper's full tweak space.
--
-- Kernel-reduction notes (for maintainers): `decide +kernel` (GMP-accelerated, NO
--   axiom, unlike `native_decide`) carries the 128-bit certificates in ~10s each.
--   Two traps: (i) the elaborator's `whnf` path times out — `+kernel` avoids it;
--   (ii) a large term (`f2SqModIter 64 …`, `X^(2^64)`, `f2Gcd …`) inside a goal
--   proved by `rw`, or a fuel-induction lemma applied at concrete literals, makes the
--   *kernel* re-reduce it (deep-recursion / OOM).  Cured by: pinning reduced values as
--   opaque equations (`cert_v64`, `cert2v`) used forward; doing char-2 on the *symbolic*
--   root power not on `X^(2^64)`; and stating `isUnit_of_f2Gcd_eq_one` over abstract `a b`.
-/

namespace RandomSystems.HTechnique.GF2Field

open Polynomial

/-! ## D1 — `Nat`-encoded `F₂[X]` arithmetic

We encode `f ∈ F₂[X]` as a `Nat`: bit `i` (i.e. `Nat.testBit n i`) is the coefficient
of `Xⁱ`.  Polynomial addition is `Nat.xor`; carry-less multiplication is shift-and-xor.
All functions are written with `Nat`-primitive `Bool` tests (`==`, `Nat.blt`) and
`cond`, so the Lean **kernel** reduces them via its GMP-accelerated `Nat` operations —
this is what lets the degree-128 certificates go through by `decide`. -/

/-- Carry-less multiplication accumulator: `f2MulAux fuel a b` Xes together `a <<< i`
for every set bit `i < fuel` of `b`.  `fuel` bounds the bit-recursion on `b`. -/
def f2MulAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    cond (b == 0) 0
      (let rest := f2MulAux fuel (a <<< 1) (b >>> 1)
       cond (b &&& 1 == 1) (a ^^^ rest) rest)

/-- Carry-less (`F₂[X]`) multiplication of the `Nat`-encoded polynomials `a`, `b`. -/
def f2Mul (a b : Nat) : Nat := f2MulAux (Nat.log2 b + 1) a b

/-- Polynomial remainder accumulator: repeatedly XOR the shifted modulus `m` to cancel
the top bit of `a`, until `deg a < deg m`.  `fuel` bounds the degree recursion. -/
def f2ModAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, m =>
    cond (Nat.blt (Nat.log2 a) (Nat.log2 m)) a
      (f2ModAux fuel (a ^^^ (m <<< (Nat.log2 a - Nat.log2 m))) m)

/-- `F₂[X]` remainder of `a` modulo `m`. -/
def f2Mod (a m : Nat) : Nat := f2ModAux (Nat.log2 a + 1) a m

/-- `a * b mod m` in `F₂[X]`. -/
def f2MulMod (a b m : Nat) : Nat := f2Mod (f2Mul a b) m

/-- `k`-fold squaring mod `m`: `f2SqModIter k a m = a^(2^k) mod m`. -/
def f2SqModIter : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | k + 1, a, m => f2SqModIter k (f2MulMod a a m) m

/-- Square-and-multiply `a^e mod m` in `F₂[X]`.  `fuel` bounds the recursion on `e`. -/
def f2PowModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 1
  | fuel + 1, a, e, m =>
    cond (e == 0) 1
      (let rest := f2PowModAux fuel (f2MulMod a a m) (e >>> 1) m
       cond (e &&& 1 == 1) (f2MulMod a rest m) rest)

/-- `a^e mod m` in `F₂[X]`. -/
def f2PowMod (a e m : Nat) : Nat := f2PowModAux (Nat.log2 e + 2) a e m

/-- Euclidean `F₂[X]` gcd, fuel-bounded on the (strictly decreasing) second argument. -/
def f2GcdAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b => cond (b == 0) a (f2GcdAux fuel b (f2Mod a b))

/-- `gcd(a, b)` in `F₂[X]` (returns the monic gcd; over `F₂` every nonzero poly is monic). -/
def f2Gcd (a b : Nat) : Nat := f2GcdAux (Nat.log2 a + Nat.log2 b + 2) a b

/-! ### Toy-scale kernel-reducibility sanity (protocol gate: `#eval` + degree-≤8 `decide`)

Modulus `x³ + x + 1 = 0b1011 = 11` is irreducible over `F₂` (`GF(8)`).  There
`x⁷ = 1`, so `x⁸ = x`, i.e. `f2SqModIter 3 2 11 = 2`, and the Rabin gcd side
condition `gcd(x^(2^1) − x mod m, m) = gcd(6, 11) = 1` holds.  These run in the
kernel by `decide`, proving the whole arithmetic core is kernel-reducible before we
scale to 128. -/

-- `#eval` sanity (evaluator, not kernel):
--   f2Mul 3 3 = 5   (x+1)² = x²+1
--   f2Mod 11 3 = ...  etc.  (see the `example`s below, which are the real gate.)

example : f2Mul 3 3 = 5 := by decide
example : f2Mod 11 2 = 1 := by decide            -- (x³+x+1) mod x = 1
example : f2SqModIter 3 2 11 = 2 := by decide     -- x^(2³) = x⁸ = x in GF(8)
example : f2Gcd (Nat.xor (f2SqModIter 1 2 11) 2) 11 = 1 := by decide

/-! ## D3 — the field `GF(2¹²⁸)`, the unit `u = x⁻¹²⁸`, and the paper's argument

The concrete POLYVAL modulus, as an honest `(ZMod 2)`-polynomial. -/

/-- `mPoly = x¹²⁸ + x¹²⁷ + x¹²⁶ + x¹²¹ + 1`, the POLYVAL reduction polynomial. -/
noncomputable def mPoly : (ZMod 2)[X] := X ^ 128 + X ^ 127 + X ^ 126 + X ^ 121 + 1

theorem mPoly_natDegree : mPoly.natDegree = 128 := by
  unfold mPoly; compute_degree!

theorem mPoly_monic : mPoly.Monic := by
  unfold mPoly; monicity!

theorem mPoly_ne_zero : mPoly ≠ 0 := mPoly_monic.ne_zero

/-! ### The `toPoly : ℕ → (ZMod 2)[X]` bridge

`toPoly n` is the polynomial whose coefficient of `Xⁱ` is bit `i` of `n`.  We
characterize it by its coefficients (`toPoly_coeff`) and then read off the
`Nat`-op ⇄ polynomial-op homomorphism lemmas by `Polynomial.ext`. -/

/-- The `Nat`-encoded polynomial `n`, as an honest `(ZMod 2)`-polynomial. -/
noncomputable def toPoly (n : Nat) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range (n + 1), (Polynomial.monomial i) (if n.testBit i then (1 : ZMod 2) else 0)

theorem toPoly_coeff (n j : Nat) :
    (toPoly n).coeff j = if n.testBit j then (1 : ZMod 2) else 0 := by
  rw [toPoly, Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) j (fun i => if n.testBit i then (1 : ZMod 2) else 0)]
  by_cases hj : j ∈ Finset.range (n + 1)
  · simp [hj]
  · rw [if_neg hj]
    rw [Finset.mem_range, not_lt] at hj
    have : n < 2 ^ j := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)
    rw [Nat.testBit_lt_two_pow this]; rfl

@[simp] theorem toPoly_zero : toPoly 0 = 0 := by
  ext j; rw [toPoly_coeff]; simp

@[simp] theorem toPoly_one : toPoly 1 = 1 := by
  ext j; rw [toPoly_coeff, Polynomial.coeff_one]
  rcases j with _ | j
  · simp
  · simp [Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem toPoly_two_pow (k : Nat) : toPoly (2 ^ k) = X ^ k := by
  ext j; rw [toPoly_coeff, Nat.testBit_two_pow, Polynomial.coeff_X_pow]
  by_cases h : k = j <;> simp [h, eq_comm]

theorem toPoly_two : toPoly 2 = X := by
  have := toPoly_two_pow 1; simpa using this

theorem toPoly_xor (a b : Nat) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext j
  rw [Polynomial.coeff_add, toPoly_coeff, toPoly_coeff, toPoly_coeff, Nat.testBit_xor]
  rcases a.testBit j <;> rcases b.testBit j <;> decide

theorem toPoly_shiftLeft (a k : Nat) : toPoly (a <<< k) = X ^ k * toPoly a := by
  ext j
  rw [toPoly_coeff, Nat.testBit_shiftLeft, Polynomial.coeff_X_pow_mul', toPoly_coeff]
  by_cases h : k ≤ j <;> simp [h]

/-- Low-bit decomposition: `toPoly b = (bit₀ b) + X · toPoly (b/2)`. -/
theorem toPoly_shift_decomp (b : Nat) :
    toPoly b = C (if b.testBit 0 then (1 : ZMod 2) else 0) + X * toPoly (b >>> 1) := by
  ext j
  rw [Polynomial.coeff_add, toPoly_coeff]
  rcases j with _ | k
  · rw [Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero, add_zero]
  · rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero k), Polynomial.coeff_X_mul, toPoly_coeff,
      zero_add, Nat.testBit_succ, Nat.shiftRight_one]

theorem toPoly_f2MulAux : ∀ (fuel a b : Nat), b < 2 ^ fuel →
    toPoly (f2MulAux fuel a b) = toPoly a * toPoly b := by
  intro fuel
  induction fuel with
  | zero => intro a b hb; interval_cases b; simp [f2MulAux]
  | succ fuel ih =>
    intro a b hb
    rw [f2MulAux]
    by_cases hb0 : b = 0
    · subst hb0; simp
    · have hcond : (b == 0) = false := by simp [hb0]
      rw [hcond, cond_false]
      have hbs : b >>> 1 < 2 ^ fuel := by
        rw [Nat.shiftRight_one, Nat.pow_succ] at *
        omega
      have hrest := ih (a <<< 1) (b >>> 1) hbs
      rw [toPoly_shiftLeft, pow_one] at hrest
      rw [toPoly_shift_decomp b]
      -- split on the low bit
      by_cases hbit : b.testBit 0
      · have : (b &&& 1 == 1) = true := by
          simp only [Nat.and_one_is_mod, beq_iff_eq]
          exact Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit
        simp only [this, cond_true, toPoly_xor, hrest, hbit, if_true, Polynomial.C_1]
        ring
      · have : (b &&& 1 == 1) = false := by
          simp only [Nat.and_one_is_mod, beq_eq_false_iff_ne]
          exact fun h => hbit (Nat.mod_two_eq_one_iff_testBit_zero.mp h)
        simp only [this, cond_false]
        rw [hrest, if_neg hbit, Polynomial.C_0, zero_add]
        ring

theorem toPoly_f2Mul (a b : Nat) : toPoly (f2Mul a b) = toPoly a * toPoly b := by
  apply toPoly_f2MulAux
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) b
  rwa [← Nat.log2_eq_log_two] at this

/-- The remainder step only changes `a` by a polynomial multiple of `m`. -/
theorem toPoly_f2ModAux_congr : ∀ (fuel a m : Nat),
    ∃ q, toPoly (f2ModAux fuel a m) = toPoly a + q * toPoly m := by
  intro fuel
  induction fuel with
  | zero => intro a m; exact ⟨0, by simp [f2ModAux]⟩
  | succ fuel ih =>
    intro a m
    rw [f2ModAux]
    by_cases hcond : Nat.blt (Nat.log2 a) (Nat.log2 m) = true
    · rw [hcond, cond_true]; exact ⟨0, by simp⟩
    · rw [Bool.not_eq_true] at hcond
      rw [hcond, cond_false]
      obtain ⟨q, hq⟩ := ih (a ^^^ (m <<< (Nat.log2 a - Nat.log2 m))) m
      refine ⟨X ^ (Nat.log2 a - Nat.log2 m) + q, ?_⟩
      rw [hq, toPoly_xor, toPoly_shiftLeft]
      ring

theorem toPoly_f2Mod_congr (a m : Nat) :
    ∃ q, toPoly (f2Mod a m) = toPoly a + q * toPoly m :=
  toPoly_f2ModAux_congr _ a m

/-- Common divisors descend through the remainder step. -/
theorem dvd_toPoly_f2Mod {g : (ZMod 2)[X]} {a m : Nat}
    (ha : g ∣ toPoly a) (hm : g ∣ toPoly m) : g ∣ toPoly (f2Mod a m) := by
  obtain ⟨q, hq⟩ := toPoly_f2Mod_congr a m
  rw [hq]; exact dvd_add ha (Dvd.dvd.mul_left hm q)

/-- Common divisors descend all the way through the Euclidean gcd. -/
theorem dvd_toPoly_f2GcdAux : ∀ (fuel a b : Nat) (g : (ZMod 2)[X]),
    g ∣ toPoly a → g ∣ toPoly b → g ∣ toPoly (f2GcdAux fuel a b) := by
  intro fuel
  induction fuel with
  | zero => intro a b g ha _; simpa [f2GcdAux] using ha
  | succ fuel ih =>
    intro a b g ha hb
    rw [f2GcdAux]
    by_cases hb0 : b = 0
    · subst hb0; simpa using ha
    · rw [show (b == 0) = false from by simp [hb0], cond_false]
      exact ih b (f2Mod a b) g hb (dvd_toPoly_f2Mod ha hb)

theorem dvd_toPoly_f2Gcd {g : (ZMod 2)[X]} {a b : Nat}
    (ha : g ∣ toPoly a) (hb : g ∣ toPoly b) : g ∣ toPoly (f2Gcd a b) :=
  dvd_toPoly_f2GcdAux _ a b g ha hb

/-! ## D2 — the Rabin irreducibility certificate

The POLYVAL modulus in the `Nat` encoding, and the machine-checked certificate. -/

/-- `mPolyval = x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1` in the `Nat` (bit) encoding. -/
def mPolyval : Nat := 2 ^ 128 + 2 ^ 127 + 2 ^ 126 + 2 ^ 121 + 1

set_option maxRecDepth 100000 in
theorem toPoly_mPolyval : toPoly mPolyval = mPoly := by
  have hxor : mPolyval = 2 ^ 128 ^^^ (2 ^ 127 ^^^ (2 ^ 126 ^^^ (2 ^ 121 ^^^ 1))) := by
    unfold mPolyval; decide +kernel
  rw [hxor, toPoly_xor, toPoly_xor, toPoly_xor, toPoly_xor,
    toPoly_two_pow, toPoly_two_pow, toPoly_two_pow, toPoly_two_pow, toPoly_one, mPoly]
  ring

set_option maxRecDepth 100000 in
/-- **Rabin certificate 1** — `x^(2¹²⁸) ≡ x  (mod mPolyval)` — kernel-checked. -/
theorem cert1 : f2SqModIter 128 2 mPolyval = 2 := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Rabin certificate 2** — `gcd(x^(2⁶⁴) − x mod mPolyval, mPolyval) = 1` — kernel-checked. -/
theorem cert2 : f2Gcd (Nat.xor (f2SqModIter 64 2 mPolyval) 2) mPolyval = 1 := by decide +kernel

/-- The reduced value of `x^(2⁶⁴) mod mPolyval` (kernel-computed).  Pinning this
concrete literal lets us reference `f2SqModIter 64 2 mPolyval` through the *opaque*
value equation `cert_v64` — so downstream `rw`-proofs never ask the kernel to
re-reduce the 64-fold squaring (which would blow its recursion budget). -/
def v64 : Nat := 110845319793653979113643960544696919372

set_option maxRecDepth 100000 in
/-- **Value certificate** — `x^(2⁶⁴) mod mPolyval = v64` — kernel-checked. -/
theorem cert_v64 : f2SqModIter 64 2 mPolyval = v64 := by decide +kernel

set_option maxRecDepth 100000 in
/-- Certificate 2 in the literal `v64` encoding (kernel-checked). -/
theorem cert2v : f2Gcd (v64 ^^^ 2) mPolyval = 1 := by decide +kernel

/-! ### The quotient bridge `F₂[X] → F₂[X]/(mPoly)`

Working in the quotient ring `AdjoinRoot mPoly` turns "mod `mPolyval`" into the
identity and reads the certificates off as polynomial divisibilities — no
Euclidean-remainder correctness proof needed, only the congruence `toPoly_f2Mod_congr`. -/

theorem mk_toPoly_mPolyval : AdjoinRoot.mk mPoly (toPoly mPolyval) = 0 := by
  rw [toPoly_mPolyval, AdjoinRoot.mk_self]

theorem mk_toPoly_f2Mod (a : Nat) :
    AdjoinRoot.mk mPoly (toPoly (f2Mod a mPolyval)) = AdjoinRoot.mk mPoly (toPoly a) := by
  obtain ⟨q, hq⟩ := toPoly_f2Mod_congr a mPolyval
  rw [hq, map_add, map_mul, mk_toPoly_mPolyval, mul_zero, add_zero]

theorem mk_toPoly_f2Mul (a b : Nat) :
    AdjoinRoot.mk mPoly (toPoly (f2Mul a b))
      = AdjoinRoot.mk mPoly (toPoly a) * AdjoinRoot.mk mPoly (toPoly b) := by
  rw [toPoly_f2Mul, map_mul]

theorem mk_toPoly_f2MulMod (a b : Nat) :
    AdjoinRoot.mk mPoly (toPoly (f2MulMod a b mPolyval))
      = AdjoinRoot.mk mPoly (toPoly a) * AdjoinRoot.mk mPoly (toPoly b) := by
  rw [f2MulMod, mk_toPoly_f2Mod, mk_toPoly_f2Mul]

theorem mk_toPoly_f2SqModIter (k a : Nat) :
    AdjoinRoot.mk mPoly (toPoly (f2SqModIter k a mPolyval))
      = (AdjoinRoot.mk mPoly (toPoly a)) ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp [f2SqModIter]
  | succ k ih =>
    rw [f2SqModIter, ih, mk_toPoly_f2MulMod]
    rw [← sq, ← pow_mul, ← pow_succ']

/-- The image of `x` in the quotient is `AdjoinRoot.root mPoly`. -/
theorem mk_toPoly_two : AdjoinRoot.mk mPoly (toPoly 2) = AdjoinRoot.root mPoly := by
  rw [toPoly_two, AdjoinRoot.mk_X]

/-- **From certificate 1**: `mPoly ∣ X^(2¹²⁸) − X`. -/
theorem mPoly_dvd_cert1 : mPoly ∣ (X ^ (2 ^ 128) - X : (ZMod 2)[X]) := by
  have hroot : (AdjoinRoot.root mPoly) ^ (2 ^ 128) = AdjoinRoot.root mPoly := by
    have h := mk_toPoly_f2SqModIter 128 2
    rw [cert1, mk_toPoly_two] at h
    exact h.symm
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hroot, sub_self]

/-- `mk (toPoly v64) = ρ^(2⁶⁴)` — the quotient image of the reduced iterate.  Proved
through the *opaque* `cert_v64`, so no `f2SqModIter` survives in the goal type. -/
theorem mk_toPoly_v64 :
    AdjoinRoot.mk mPoly (toPoly v64) = (AdjoinRoot.root mPoly) ^ (2 ^ 64) := by
  have h := mk_toPoly_f2SqModIter 64 2
  rw [cert_v64, mk_toPoly_two] at h
  exact h

/-- **From certificate 2** (congruence part): `mPoly ∣ toPoly (v64 ⊕ x) − (X^(2⁶⁴) − X)`.
Together with the gcd's divisor property this shows `mPoly` shares no factor with
`X^(2⁶⁴) − X`.  Everything is stated over the literal `v64` and the char-2 step runs
on the *symbolic*
root power `ρ^(2⁶⁴)` in the quotient — so the kernel never `npow`-expands `X^(2⁶⁴)`
nor re-reduces the 64-fold squaring. -/
theorem mPoly_dvd_cert2_congr :
    mPoly ∣ (toPoly (v64 ^^^ 2) - (X ^ (2 ^ 64) - X) : (ZMod 2)[X]) := by
  haveI : Nontrivial (AdjoinRoot mPoly) :=
    AdjoinRoot.nontrivial mPoly (by rw [degree_eq_natDegree mPoly_ne_zero, mPoly_natDegree]; decide)
  haveI : CharP (AdjoinRoot mPoly) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot mPoly)).injective 2
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_sub, map_pow, AdjoinRoot.mk_X,
      toPoly_xor, map_add, mk_toPoly_v64, mk_toPoly_two,
      CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]

/-! ### The converse Rabin direction (missing from Mathlib)

An irreducible `f` of degree `d ∣ 64` divides `X^(2⁶⁴) − X`, because
`AdjoinRoot f` is a finite field of cardinality `2^d`, so its root `ρ` satisfies
`ρ^(2⁶⁴) = ρ` (Frobenius, `d ∣ 64`), hence `f = minpoly ρ ∣ X^(2⁶⁴) − X`. -/
theorem irreducible_dvd_X_pow_pow_sub_X {f : (ZMod 2)[X]} (hf : Irreducible f)
    (hd : f.natDegree ∣ 64) : f ∣ (X ^ (2 ^ 64) - X : (ZMod 2)[X]) := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  haveI : FiniteDimensional (ZMod 2) (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf.ne_zero).finite
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 2)
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = 2 ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), (AdjoinRoot.powerBasis hf.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, ZMod.card]
  -- ρ^(2⁶⁴) = ρ
  have hrootpow : (AdjoinRoot.root f) ^ (2 ^ 64) = AdjoinRoot.root f := by
    have hfrob := FiniteField.pow_card_pow (K := AdjoinRoot f) (64 / f.natDegree)
      (AdjoinRoot.root f)
    rw [hcard, ← pow_mul, Nat.mul_div_cancel' hd] at hfrob
    exact hfrob
  -- f ∣ minpoly ρ ∣ (X^(2⁶⁴) − X)
  have hmin_dvd : minpoly (ZMod 2) (AdjoinRoot.root f) ∣ (X ^ (2 ^ 64) - X : (ZMod 2)[X]) := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, hrootpow, sub_self]
  have hf_dvd_min : f ∣ minpoly (ZMod 2) (AdjoinRoot.root f) := by
    rw [AdjoinRoot.minpoly_root hf.ne_zero]
    exact dvd_mul_right _ _
  exact hf_dvd_min.trans hmin_dvd

/-! ### Assembling the Rabin criterion → irreducibility -/

/-- Coprimality bridge: if the `Nat`-gcd of `a` and `b` is `1`, any common divisor of
`toPoly a` and `toPoly b` is a unit.  Stated for **abstract** `a b`, so `f2Gcd a b`
stays symbolic — the kernel never evaluates the Euclidean gcd; the concrete value is
supplied opaquely by `cert2v` at the call site. -/
theorem isUnit_of_f2Gcd_eq_one {a b : Nat} {g : (ZMod 2)[X]}
    (h : f2Gcd a b = 1) (hga : g ∣ toPoly a) (hgb : g ∣ toPoly b) : IsUnit g := by
  have hd := dvd_toPoly_f2Gcd hga hgb
  rw [h, toPoly_one] at hd
  exact isUnit_of_dvd_one hd

/-- **Certificate-2 consequence.** No factor of `mPoly` divides `X^(2⁶⁴) − X`:
any common divisor also divides `toPoly (v64 ⊕ x)` (via the congruence) and
`toPoly mPolyval = mPoly`, hence — by `cert2v` (`f2Gcd (v64 ⊕ x) mPolyval = 1`) — is a
unit. -/
theorem factor_isUnit_of_dvd_X64 {f : (ZMod 2)[X]}
    (h1 : f ∣ mPoly) (h2 : f ∣ (X ^ (2 ^ 64) - X : (ZMod 2)[X])) : IsUnit f := by
  have hdiff : f ∣ (toPoly (v64 ^^^ 2) - (X ^ (2 ^ 64) - X) : (ZMod 2)[X]) :=
    h1.trans mPoly_dvd_cert2_congr
  -- `f ∣ toPoly (v64 ⊕ x)` — cancel over an *opaque* `B := X^(2⁶⁴) − X` (`abel`, no `simp`),
  -- so the huge `X^(2⁶⁴)` is never `npow`-expanded.
  have hr : f ∣ toPoly (v64 ^^^ 2) := by
    set B := (X ^ (2 ^ 64) - X : (ZMod 2)[X])
    have h := dvd_add hdiff h2
    have e : toPoly (v64 ^^^ 2) - B + B = toPoly (v64 ^^^ 2) := by abel
    rwa [e] at h
  have hm : f ∣ toPoly mPolyval := by rw [toPoly_mPolyval]; exact h1
  exact isUnit_of_f2Gcd_eq_one cert2v hr hm

/-- **D2 conclusion / acceptance.** `mPoly = x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1` is irreducible
over `F₂`, by the Rabin criterion: certificate 1 forces every irreducible factor to
have degree a power of two dividing `128`; certificate 2 (with the converse Rabin
direction) rules out every degree properly dividing `128`; so the unique factor has
degree `128 = deg mPoly`, i.e. `mPoly` is (associate to) an irreducible. -/
theorem mPoly_irreducible : Irreducible mPoly := by
  have key : ∀ f, Irreducible f → f ∣ mPoly → f.natDegree = 128 := by
    intro f hf hfdvd
    have hcard : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card, ZMod.card]
    have h1 : f ∣ (X ^ (Nat.card (ZMod 2)) ^ 128 - X : (ZMod 2)[X]) := by
      rw [hcard]; exact hfdvd.trans mPoly_dvd_cert1
    have hdeg_dvd : f.natDegree ∣ 128 := hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X h1
    by_contra hne
    have hdvd64 : f.natDegree ∣ 64 := by
      have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
      rw [h128] at hdeg_dvd
      obtain ⟨m, hm, hfm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdeg_dvd
      have hm7 : m ≠ 7 := by rintro rfl; exact hne (hfm.trans (by norm_num))
      rw [hfm, show (64 : ℕ) = 2 ^ 6 from by norm_num]; exact pow_dvd_pow 2 (by omega)
    have h64 : f ∣ (X ^ (2 ^ 64) - X : (ZMod 2)[X]) := irreducible_dvd_X_pow_pow_sub_X hf hdvd64
    exact hf.not_isUnit (factor_isUnit_of_dvd_X64 hfdvd h64)
  have hnu : ¬ IsUnit mPoly := by
    intro h
    have h0 := Polynomial.degree_eq_zero_of_isUnit h
    rw [Polynomial.degree_eq_natDegree mPoly_ne_zero, mPoly_natDegree] at h0
    simp at h0
  obtain ⟨f, hf, hfdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu mPoly_ne_zero
  have hassoc : Associated f mPoly :=
    associated_of_dvd_of_natDegree_le hfdvd mPoly_ne_zero (by rw [key f hf hfdvd, mPoly_natDegree])
  exact hassoc.irreducible hf

/-- **Acceptance (brief form).** `Irreducible (toPoly mPolyval)` — the same statement in
the `Nat`-bridge encoding, via `toPoly mPolyval = mPoly`. -/
theorem mPolyval_irreducible : Irreducible (toPoly mPolyval) :=
  toPoly_mPolyval ▸ mPoly_irreducible

/-- The Rabin certificate discharges the field's standing hypothesis. -/
instance : Fact (Irreducible mPoly) := ⟨mPoly_irreducible⟩

section Field

/-- `GF(2¹²⁸) = F₂[X]/(mPoly)`. -/
abbrev GF128 := AdjoinRoot mPoly

noncomputable instance : FiniteDimensional (ZMod 2) GF128 :=
  (AdjoinRoot.powerBasis mPoly_ne_zero).finite

noncomputable instance : Fintype GF128 :=
  have : Finite GF128 := Module.finite_of_finite (ZMod 2)
  Fintype.ofFinite GF128

theorem gf128_finrank : Module.finrank (ZMod 2) GF128 = 128 := by
  rw [(AdjoinRoot.powerBasis mPoly_ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    mPoly_natDegree]

/-- **Acceptance.** `|GF(2¹²⁸)| = 2¹²⁸`. -/
theorem gf128_card : Fintype.card GF128 = 2 ^ 128 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), gf128_finrank, ZMod.card]

/-- The image of the indeterminate `x` in the field. -/
noncomputable def xGF : GF128 := AdjoinRoot.root mPoly

theorem minpoly_xGF : minpoly (ZMod 2) xGF = mPoly := by
  have := AdjoinRoot.minpoly_powerBasis_gen_of_monic mPoly_monic
  simpa [AdjoinRoot.powerBasis_gen, xGF] using this

theorem xGF_ne_zero : xGF ≠ 0 := by
  intro h
  have hd : (minpoly (ZMod 2) xGF).natDegree = 128 := by rw [minpoly_xGF, mPoly_natDegree]
  rw [h, minpoly.zero] at hd
  simp at hd

/-- The unit represented by `x` (a nonzero field element). -/
noncomputable def xUnit : GF128ˣ := (Ne.isUnit xGF_ne_zero).unit

/-- **The Montgomery unit** `u = x⁻¹²⁸`, as pinned by the POLYVAL dot-convention. -/
noncomputable def uPolyval : GF128ˣ := (xUnit ^ 128)⁻¹

theorem uPolyval_coe : (uPolyval : GF128) = (xGF ^ 128)⁻¹ := by
  simp [uPolyval, xUnit, Units.val_pow_eq_pow_val]

/-- **Acceptance / paper p.7.** The degenerate collision polynomial `x·h` is
nonzero because `xⁿ ≠ x` (equivalently `xⁿ⁻¹ ≠ 1`): if `x¹²⁸ = x`, then cancelling
the nonzero `x` gives `x¹²⁷ = 1`, so `x` is a root of `X¹²⁷ − 1`, forcing its
degree-128 minimal polynomial to divide a degree-127 polynomial — impossible. -/
theorem xGF_pow_n_ne_x : xGF ^ 128 ≠ xGF := by
  intro h
  -- cancel the nonzero `x`: `x¹²⁷ = 1`
  have h127 : xGF ^ 127 = 1 := by
    have hx : xGF ≠ 0 := xGF_ne_zero
    have : xGF ^ 127 * xGF = 1 * xGF := by
      rw [one_mul, ← pow_succ]; simpa using h
    exact mul_right_cancel₀ hx this
  -- `x` is a root of `X¹²⁷ - C 1`
  have hroot : (Polynomial.aeval xGF) (X ^ 127 - C 1 : (ZMod 2)[X]) = 0 := by
    simp [h127]
  have hdvd : minpoly (ZMod 2) xGF ∣ (X ^ 127 - C 1 : (ZMod 2)[X]) :=
    minpoly.dvd (ZMod 2) xGF hroot
  rw [minpoly_xGF] at hdvd
  -- degree contradiction: `128 = deg mPoly ≤ deg (X¹²⁷ - C 1) = 127`
  have hne : (X ^ 127 - C 1 : (ZMod 2)[X]) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C (1 : ZMod 2) (by norm_num)).ne_zero
  have hle : mPoly.natDegree ≤ (X ^ 127 - C 1 : (ZMod 2)[X]).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hne
  rw [mPoly_natDegree, Polynomial.natDegree_X_pow_sub_C] at hle
  omega

/-! ### The canonical little-endian block encoding

The paper (p.4) reads an `n`-bit block as a field element little-endian: bit `j`
is the coefficient of `xʲ`, so `001‖0ⁿ⁻³ ↦ x²`.  `toPoly` is exactly that map, so
`gf128OfNat i = mk mPoly (toPoly i)` is the spec's `bin`.  This pins the
block↔bits identification to the **power basis** `{1, x, …, x¹²⁷}` — unlike an
arbitrary `Module.finBasis`, under which `bin 2` is an unknown field element and
the paper's degenerate-case argument cannot even be stated. -/

/-- **The canonical little-endian block encoding** (paper p.4): the field element
whose power-basis coefficients are the bits of `i`. -/
noncomputable def gf128OfNat (i : ℕ) : GF128 := AdjoinRoot.mk mPoly (toPoly i)

/-- The encoding is additive: bit XOR ↦ field addition (`BlockBits.toBits_add`). -/
theorem gf128OfNat_xor (a b : ℕ) :
    gf128OfNat (a ^^^ b) = gf128OfNat a + gf128OfNat b := by
  unfold gf128OfNat; rw [toPoly_xor, map_add]

/-- **`bin 2 = x`** — the identity an arbitrary basis cannot supply, and the one
the paper's p.7 degenerate case is stated in terms of. -/
theorem gf128OfNat_two : gf128OfNat 2 = xGF := by
  unfold gf128OfNat xGF; rw [toPoly_two, AdjoinRoot.mk_X]

theorem toPoly_eq_zero_iff (i : ℕ) : toPoly i = 0 ↔ i = 0 := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq (fun j => ?_)
    have hc := toPoly_coeff i j
    rw [h, Polynomial.coeff_zero] at hc
    rw [Nat.zero_testBit]
    by_cases hb : i.testBit j
    · rw [if_pos hb] at hc; exact absurd hc.symm one_ne_zero
    · simpa using hb
  · rintro rfl; exact toPoly_zero

/-- In-range encodings stay below the modulus degree. -/
theorem toPoly_natDegree_lt (i : ℕ) (h : i < 2 ^ 128) : (toPoly i).natDegree < 128 := by
  have hle : (toPoly i).natDegree ≤ 127 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => ?_)
    have h128 : (2 : ℕ) ^ 128 ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbit : i.testBit N = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le h h128)
    rw [toPoly_coeff, if_neg (by simp [hbit])]
  omega

set_option maxRecDepth 10000 in
/-- The encoding is injective below `2¹²⁸`: a collision divides the degree-128
modulus by a polynomial of degree `< 128`, hence is zero. -/
theorem gf128OfNat_inj_of_lt {a b : ℕ} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : gf128OfNat a = gf128OfNat b) : a = b := by
  have h' : (AdjoinRoot.mk mPoly) (toPoly a) = (AdjoinRoot.mk mPoly) (toPoly b) := h
  have hdvd : mPoly ∣ toPoly a - toPoly b := AdjoinRoot.mk_eq_mk.mp h'
  rw [CharTwo.sub_eq_add, ← toPoly_xor] at hdvd
  have hlt : (toPoly (a ^^^ b)).natDegree < mPoly.natDegree := by
    rw [mPoly_natDegree]; exact toPoly_natDegree_lt _ (Nat.xor_lt_two_pow ha hb)
  exact Nat.xor_eq_zero_iff.mp ((toPoly_eq_zero_iff _).mp
    (eq_zero_of_dvd_of_natDegree_lt hdvd hlt))

theorem gf128OfNat_fin_bijective :
    Function.Bijective (fun i : Fin (2 ^ 128) => gf128OfNat i.val) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro i j hij
    exact Fin.val_injective (gf128OfNat_inj_of_lt i.isLt j.isLt hij)
  · rw [Fintype.card_fin, gf128_card]

/-- **The canonical block↔index bijection.**  Compose with the project's
`BitVec w ≃ Fin (2 ^ w)` to obtain `BlockBits GF128 128`; additivity comes from
`gf128OfNat_xor` and `BitVec.toNat_xor`. -/
noncomputable def gf128FinEquiv : Fin (2 ^ 128) ≃ GF128 :=
  Equiv.ofBijective _ gf128OfNat_fin_bijective

@[simp] theorem gf128FinEquiv_apply (i : Fin (2 ^ 128)) :
    gf128FinEquiv i = gf128OfNat i.val := rfl

/-- **The degenerate-case obligation (paper p.7), in the shape the hash actually
needs.**  At `|T| = |M| = 0` the block list collapses to `[bin 2]`, whose POLYVAL
polynomial is `C (bin 2 · u) · X`; `prop3`'s `+ X` perturbation leaves the
coefficient `bin 2 · u + 1`, nonzero in characteristic 2 exactly when
`bin 2 · u ≠ 1`.  With the canonical encoding `bin 2 = x` (`gf128OfNat_two`) and
the POLYVAL unit `u = x⁻¹²⁸` this *is* the paper's `xⁿ ≠ x` (`xGF_pow_n_ne_x`).

This replaces the former `degenerate_hash_poly_ne_X`, which was stated as
`C xGF * X + C g ≠ 0` — it never mentioned the dot unit `u`, so it did not match
the obligation and was consumed by nothing.

TODO(wiring): consume in `HCTR2Paper.lean` (`HCTR2Spec`) to drop the
`htwPos : 1 ≤ (tweakEnc t).length` hypothesis of
`specHashFamilyV`/`specHashFamilyVS`, and with it the `hτ : 1 ≤ τ` of
`hctr2_paper_theorem` — restoring the paper's full tweak space `𝒯`, which
includes the empty tweak. -/
theorem xGF_mul_uPolyval_ne_one : xGF * (uPolyval : GF128) ≠ 1 := by
  rw [uPolyval_coe, ← div_eq_mul_inv]
  intro h
  exact xGF_pow_n_ne_x
    ((div_eq_one_iff_eq (pow_ne_zero 128 xGF_ne_zero)).mp h).symm

end Field

end RandomSystems.HTechnique.GF2Field
