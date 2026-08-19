/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.UHFThenURF

/-!
# Universality of length-separated polynomial hashing

The obligation left by `polynomialHashUniversal` in
`RandomSystemsCC/Symmetric/UHFThenURF.lean`, stated standalone.
-/

namespace RandomSystemsCC.Symmetric.UHFThenURF

open RandomSystems (Dist)
open RandomSystems.HTechnique.HashThenPRF
open scoped BigOperators NNReal

universe u

variable {F : Type u}
variable [Fintype F] [DecidableEq F] [Nonempty F] [Field F]

/-! ### The hash as a polynomial

`polynomialHash · m` is the evaluation of an honest polynomial `hashPoly m`,
monic of degree `|m|`, whose lower coefficients are the message letters.  The
map `m ↦ hashPoly m` is injective — that is exactly what the terminal `1` at
degree `|m|` buys — so distinct messages give a nonzero difference polynomial
of degree at most `ell`, which has at most `ell` roots. -/

/-- The polynomial underlying `polynomialHash`. -/
noncomputable def hashPoly {ell : Nat} (m : BoundedMessage F ell) : Polynomial F :=
  Polynomial.X ^ m.1.val +
    ∑ i : Fin m.1.val, Polynomial.C (m.2 i) * Polynomial.X ^ i.val

omit [Fintype F] [DecidableEq F] [Nonempty F] in
@[simp]
theorem hashPoly_eval {ell : Nat} (m : BoundedMessage F ell) (key : F) :
    (hashPoly m).eval key = polynomialHash key m := by
  simp [hashPoly, polynomialHash, Polynomial.eval_finset_sum]

omit [Fintype F] [DecidableEq F] [Nonempty F] in
/-- The coefficients of `hashPoly m`, in one formula. -/
theorem hashPoly_coeff {ell : Nat} (m : BoundedMessage F ell) (k : Nat) :
    (hashPoly m).coeff k =
      (if k = m.1.val then 1 else 0) +
        ∑ i : Fin m.1.val, (if k = i.val then m.2 i else 0) := by
  simp [hashPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

omit [Fintype F] [DecidableEq F] [Nonempty F] in
/-- Above the message length the polynomial vanishes. -/
theorem hashPoly_coeff_of_gt {ell : Nat} (m : BoundedMessage F ell) {k : Nat}
    (hk : m.1.val < k) : (hashPoly m).coeff k = 0 := by
  rw [hashPoly_coeff]
  rw [if_neg (by omega)]
  rw [Finset.sum_eq_zero fun i _ => if_neg (by have := i.isLt; omega)]
  simp

omit [Fintype F] [DecidableEq F] [Nonempty F] in
/-- The terminal coefficient, at the message length, is `1`. -/
theorem hashPoly_coeff_len {ell : Nat} (m : BoundedMessage F ell) :
    (hashPoly m).coeff m.1.val = 1 := by
  rw [hashPoly_coeff, if_pos rfl]
  rw [Finset.sum_eq_zero fun i _ => if_neg (by have := i.isLt; omega)]
  simp

omit [Fintype F] [DecidableEq F] [Nonempty F] in
/-- Below the message length the coefficients are the message letters. -/
theorem hashPoly_coeff_of_lt {ell : Nat} (m : BoundedMessage F ell) {k : Nat}
    (hk : k < m.1.val) : (hashPoly m).coeff k = m.2 ⟨k, hk⟩ := by
  rw [hashPoly_coeff, if_neg (by omega), zero_add]
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin m.1.val)]
  · simp
  · intro i _ hi
    exact if_neg fun h => hi (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fintype F] [DecidableEq F] [Nonempty F] in
/-- `hashPoly m` has degree at most the message length. -/
theorem hashPoly_natDegree_le {ell : Nat} (m : BoundedMessage F ell) :
    (hashPoly m).natDegree ≤ m.1.val :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ h => hashPoly_coeff_of_gt m h

omit [Fintype F] [DecidableEq F] [Nonempty F] in
/-- **Length separation.**  Distinct bounded messages give distinct
polynomials: the terminal `1` pins down the length, and the remaining
coefficients pin down the letters. -/
theorem hashPoly_injective {ell : Nat} :
    Function.Injective (hashPoly (F := F) (ell := ell)) := by
  rintro ⟨n, f⟩ ⟨n', g⟩ hpoly
  have hlen : n.val = n'.val := by
    by_contra hne
    rcases Nat.lt_or_ge n.val n'.val with hlt | hge
    · have h0 : (hashPoly (⟨n, f⟩ : BoundedMessage F ell)).coeff n'.val = 0 :=
        hashPoly_coeff_of_gt _ hlt
      have h1 : (hashPoly (⟨n', g⟩ : BoundedMessage F ell)).coeff n'.val = 1 :=
        hashPoly_coeff_len _
      rw [hpoly, h1] at h0
      exact one_ne_zero h0
    · have hlt : n'.val < n.val := by omega
      have h0 : (hashPoly (⟨n', g⟩ : BoundedMessage F ell)).coeff n.val = 0 :=
        hashPoly_coeff_of_gt _ hlt
      have h1 : (hashPoly (⟨n, f⟩ : BoundedMessage F ell)).coeff n.val = 1 :=
        hashPoly_coeff_len _
      rw [← hpoly, h1] at h0
      exact one_ne_zero h0
  obtain rfl : n = n' := Fin.ext hlen
  have hfun : f = g := by
    funext i
    have hf : (hashPoly (⟨n, f⟩ : BoundedMessage F ell)).coeff i.val = f ⟨i.val, i.isLt⟩ :=
      hashPoly_coeff_of_lt _ i.isLt
    have hg : (hashPoly (⟨n, g⟩ : BoundedMessage F ell)).coeff i.val = g ⟨i.val, i.isLt⟩ :=
      hashPoly_coeff_of_lt _ i.isLt
    rw [hpoly, hg] at hf
    simpa using hf.symm
  exact congrArg _ hfun

/-- **Length-separated polynomial hashing is `ell / |F|`-universal.** -/
theorem polynomialHash_universal (ell : Nat)
    (m m' : BoundedMessage F ell) (hne : m ≠ m') :
    ((Dist.uniform F).mass fun key => polynomialHash key m = polynomialHash key m')
      ≤ (ell : NNReal) / (Fintype.card F : NNReal) := by
  classical
  set P : Polynomial F := hashPoly m - hashPoly m' with hP
  -- The difference polynomial is nonzero, of degree at most `ell`.
  have hPne : P ≠ 0 := sub_ne_zero.mpr fun h => hne (hashPoly_injective h)
  have hPdeg : P.natDegree ≤ ell := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (hashPoly_natDegree_le m).trans (Nat.lt_succ_iff.mp m.1.isLt)
    · exact (hashPoly_natDegree_le m').trans (Nat.lt_succ_iff.mp m'.1.isLt)
  -- The collision set is a set of roots of `P`, hence has at most `ell` elements.
  set Z : Finset F :=
    Finset.univ.filter fun key => polynomialHash key m = polynomialHash key m' with hZ
  have hsub : Z.val ⊆ P.roots := by
    intro key hkey
    have hkey' : polynomialHash key m = polynomialHash key m' := by
      have : key ∈ Z := hkey
      simpa [hZ] using this
    refine (Polynomial.mem_roots hPne).mpr ?_
    simp [Polynomial.IsRoot, hP, hkey']
  have hcard : Z.card ≤ ell :=
    (Polynomial.card_le_degree_of_subset_roots hsub).trans hPdeg
  -- Convert the count into the uniform mass.
  rw [Dist.uniform_mass_eq_card_filter]
  show (Z.card : NNReal) / (Fintype.card F : NNReal)
      ≤ (ell : NNReal) / (Fintype.card F : NNReal)
  -- `gcongr` discharges the numerator comparison from `hcard`, modulo the cast.
  gcongr

end RandomSystemsCC.Symmetric.UHFThenURF
