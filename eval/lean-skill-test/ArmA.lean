/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.UHFThenURF

/-!
# Universality of length-separated polynomial hashing

The obligation left by `polynomialHashUniversal` in
`RandomSystemsCC/Symmetric/UHFThenURF.lean`, stated standalone.

The argument is the textbook one, made honest about the length separation.
A bounded message `m` is turned into the coefficient vector `hashCoeff m` on
the *fixed* degree range `0, …, ell`: the message coefficients below the
length `|m|`, the separating `1` at degree `|m|`, and `0` above.  Two facts
about that vector do all the work: it computes the hash
(`polynomialHash_eq_sum_range`), and it determines the message
(`eq_of_hashCoeff_eq`) — the separating `1` is what pins the length down.
So for `m ≠ m'` the difference polynomial `hashDiffPoly m m'` is a nonzero
polynomial of degree at most `ell` whose roots are exactly the colliding
keys, and a nonzero polynomial over a field has at most `deg` roots.
-/

namespace RandomSystemsCC.Symmetric.UHFThenURF

open RandomSystems (Dist)
open RandomSystems.HTechnique.HashThenPRF
open scoped BigOperators NNReal

universe u

section Helpers

variable {F : Type u} [Field F] {ell : Nat}

/-! ## Coefficients of the length-separated hash polynomial -/

/-- The degree-`j` coefficient of the length-separated hash polynomial of `m`:
the message coefficients below the length, the separating `1` at the length,
and `0` above it. -/
def hashCoeff (m : BoundedMessage F ell) (j : Nat) : F :=
  if h : j < m.1.val then m.2 ⟨j, h⟩ else if j = m.1.val then 1 else 0

theorem hashCoeff_of_lt (m : BoundedMessage F ell) {j : Nat} (h : j < m.1.val) :
    hashCoeff m j = m.2 ⟨j, h⟩ :=
  dif_pos h

theorem hashCoeff_len (m : BoundedMessage F ell) : hashCoeff m m.1.val = 1 := by
  rw [hashCoeff, dif_neg (lt_irrefl _), if_pos rfl]

theorem hashCoeff_of_gt (m : BoundedMessage F ell) {j : Nat} (h : m.1.val < j) :
    hashCoeff m j = 0 := by
  rw [hashCoeff, dif_neg (Nat.not_lt.mpr h.le), if_neg h.ne']

/-- The hash is the evaluation of the coefficient vector on the *fixed* degree
range `0, …, ell`, independent of the message length. -/
theorem polynomialHash_eq_sum_range (key : F) (m : BoundedMessage F ell) :
    polynomialHash key m = ∑ j ∈ Finset.range (ell + 1), hashCoeff m j * key ^ j := by
  calc polynomialHash key m
      = ∑ j ∈ Finset.range (m.1.val + 1), hashCoeff m j * key ^ j := by
        change key ^ m.1.val + ∑ i : Fin m.1.val, m.2 i * key ^ i.val = _
        rw [Finset.sum_range_succ, hashCoeff_len, one_mul, add_comm]
        congr 1
        rw [← Fin.sum_univ_eq_sum_range (fun j => hashCoeff m j * key ^ j) m.1.val]
        exact Finset.sum_congr rfl fun i _ => by rw [hashCoeff_of_lt m i.isLt]
    _ = ∑ j ∈ Finset.range (ell + 1), hashCoeff m j * key ^ j := by
        refine Finset.sum_subset
          (Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.lt_succ_iff.mp m.1.isLt)))
          fun j _ hj => ?_
        rw [hashCoeff_of_gt m (Nat.not_lt.mp fun h => hj (Finset.mem_range.mpr h)), zero_mul]

/-- The coefficient vector on `0, …, ell` determines the bounded message: the
separating `1` pins the length down, and the coefficients below it are the
message. -/
theorem eq_of_hashCoeff_eq {m m' : BoundedMessage F ell}
    (h : ∀ j ≤ ell, hashCoeff m j = hashCoeff m' j) : m = m' := by
  have hlen : m.1.val = m'.1.val := by
    by_contra hne
    rcases Nat.lt_or_ge m.1.val m'.1.val with hlt | hge
    · -- reading the coefficient at the longer length gives `0 = 1`
      have hcoeff := h m'.1.val (Nat.lt_succ_iff.mp m'.1.isLt)
      rw [hashCoeff_of_gt m hlt, hashCoeff_len] at hcoeff
      exact zero_ne_one hcoeff
    · have hlt : m'.1.val < m.1.val := lt_of_le_of_ne hge fun e => hne e.symm
      have hcoeff := h m.1.val (Nat.lt_succ_iff.mp m.1.isLt)
      rw [hashCoeff_len, hashCoeff_of_gt m' hlt] at hcoeff
      exact one_ne_zero hcoeff
  obtain ⟨n, f⟩ := m
  obtain ⟨n', f'⟩ := m'
  have hn : n = n' := Fin.ext hlen
  subst hn
  congr 1
  funext i
  have hcoeff := h i.val (le_trans i.isLt.le (Nat.lt_succ_iff.mp n.isLt))
  rw [hashCoeff_of_lt _ i.isLt, hashCoeff_of_lt _ i.isLt] at hcoeff
  simpa using hcoeff

/-! ## The difference polynomial -/

/-- The polynomial whose roots are exactly the keys on which `m` and `m'`
collide. -/
noncomputable def hashDiffPoly (m m' : BoundedMessage F ell) : Polynomial F :=
  ∑ j ∈ Finset.range (ell + 1), Polynomial.monomial j (hashCoeff m j - hashCoeff m' j)

theorem hashDiffPoly_coeff (m m' : BoundedMessage F ell) {j : Nat} (hj : j ≤ ell) :
    (hashDiffPoly m m').coeff j = hashCoeff m j - hashCoeff m' j := by
  rw [hashDiffPoly, Polynomial.finset_sum_coeff]
  simp [Polynomial.coeff_monomial, Nat.lt_succ_iff.mpr hj]

theorem hashDiffPoly_natDegree_le (m m' : BoundedMessage F ell) :
    (hashDiffPoly m m').natDegree ≤ ell :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ hj =>
    (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem hashDiffPoly_ne_zero {m m' : BoundedMessage F ell} (hne : m ≠ m') :
    hashDiffPoly m m' ≠ 0 := by
  intro h0
  refine hne (eq_of_hashCoeff_eq fun j hj => ?_)
  have hcoeff := hashDiffPoly_coeff m m' hj
  rw [h0, Polynomial.coeff_zero] at hcoeff
  exact sub_eq_zero.mp hcoeff.symm

theorem eval_hashDiffPoly (key : F) (m m' : BoundedMessage F ell) :
    (hashDiffPoly m m').eval key = polynomialHash key m - polynomialHash key m' := by
  rw [hashDiffPoly, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial, sub_mul]
  rw [Finset.sum_sub_distrib, ← polynomialHash_eq_sum_range, ← polynomialHash_eq_sum_range]

/-! ## Counting the colliding keys -/

/-- At most `ell` keys make two distinct bounded messages collide. -/
theorem card_filter_polynomialHash_eq_le [Fintype F] [DecidableEq F]
    {m m' : BoundedMessage F ell} (hne : m ≠ m') :
    ((Finset.univ : Finset F).filter
        fun key => polynomialHash key m = polynomialHash key m').card ≤ ell := by
  have hsub : ((Finset.univ : Finset F).filter
      fun key => polynomialHash key m = polynomialHash key m')
      ⊆ (hashDiffPoly m m').roots.toFinset := by
    intro key hkey
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hashDiffPoly_ne_zero hne, ?_⟩
    change (hashDiffPoly m m').eval key = 0
    rw [eval_hashDiffPoly, (Finset.mem_filter.mp hkey).2, sub_self]
  calc ((Finset.univ : Finset F).filter
        fun key => polynomialHash key m = polynomialHash key m').card
      ≤ (hashDiffPoly m m').roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (hashDiffPoly m m').roots := Multiset.toFinset_card_le _
    _ ≤ (hashDiffPoly m m').natDegree := Polynomial.card_roots' _
    _ ≤ ell := hashDiffPoly_natDegree_le m m'

end Helpers

variable {F : Type u}
variable [Fintype F] [DecidableEq F] [Nonempty F] [Field F]

/-- **Length-separated polynomial hashing is `ell / |F|`-universal.** -/
theorem polynomialHash_universal (ell : Nat)
    (m m' : BoundedMessage F ell) (hne : m ≠ m') :
    ((Dist.uniform F).mass fun key => polynomialHash key m = polynomialHash key m')
      ≤ (ell : NNReal) / (Fintype.card F : NNReal) := by
  rw [Dist.uniform_mass_eq_card_filter]
  gcongr
  exact_mod_cast card_filter_polynomialHash_eq_le hne

end RandomSystemsCC.Symmetric.UHFThenURF
