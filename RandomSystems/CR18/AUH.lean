/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- PORTED from hctr2-verification HCTR2/Proofs/Concrete/AXU.lean:35-114
-- (+ inlined dependency chain HCTR2/Proofs/Concrete/PolyHash.lean:31-77,217-308)
-- — UPSTREAM-CANDIDATE landed 2026-06-11
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Card

/-!
# ε-almost-(XOR-)universal hashing (CR18 Def. 6.2 family)

This module formalizes the **almost-universal hash** layer of CR18 §6.2.

CR18 Definition 6.2 calls a keyed hash `H : 𝒦 × 𝒴 → {0,1}^n` **δ-almost-universal**
(δ-AUH) if for all distinct messages `y ≠ y'`, `Pr_K[H_K(y) = H_K(y')] ≤ δ`; the
XOR variant (**δ-AXU**) demands `Pr_K[H_K(y) ⊕ H_K(y') = c] ≤ δ` for *every*
constant `c`.  `EpsAXU H bound` below is the **count form** of δ-AXU,
specialized to key space a finite field `F` and fixed-length messages
`Fin k → F`: for distinct messages and any offset `c`, at most `bound` keys
satisfy `H h M - H h M' = c` — i.e. δ-AXU with `δ = bound / |F|`, with XOR
generalized to field subtraction (over `GF(2^n)`, the CR18 setting, subtraction
*is* XOR).  Since δ-AXU at `c = 0` is δ-AUH, every `EpsAXU` hash is in
particular a Def. 6.2 δ-AUH family.

The generic consequences ported here are the *structural* (key-independent)
collision-freeness facts a security proof consumes for affine evaluation points
`c + H_h(m)`:

* `EpsAXU.no_const_gap` — an ε-AXU hash with `bound < |F|` admits no
  key-independent constant gap between distinct messages;
* `no_structural_collision_of_epsAXU` — distinct-message affine points never
  collide simultaneously for every key;
* `structural_collision_eq_of_epsAXU` — a key-independent affine collision
  forces both messages and constants equal (the keystone reducing structural
  collisions to output collisions, which birthday arguments then bound).

The concrete instance is the **polynomial-evaluation hash** of CR18 Lemma 6.3:
`polyvalHash h m = Σ_{i<k} m_i · h^(i+1)` (the GHASH/POLYVAL shape — powers
start at `h¹`, no constant term) is ε-AXU with `bound = k`
(`polyval_isEpsAXU`), i.e. `δ(k) = k / |F|`, linear in the message length
exactly as in Lem. 6.3.  The root-counting dependency chain
(`polyHash`, `diffPoly`, `polyvalDiffPoly`, …, `card_polyval_point_collision_le`)
is inlined from the source's `PolyHash.lean`; the single mathematical fact doing
the work is Mathlib's `Polynomial.card_roots'`.

Not ported: the source's `hashKeyedPDS` (keyed hash *as a random system*,
CR18 §6.2.7) — it depends on the library `PDS.ofStatelessOracleDist` and
belongs with the PDS layer, not this Mathlib-only module.
-/

namespace RandomSystems.CR18

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## Polynomial-evaluation hash and its difference polynomial -/

/-- Polynomial-evaluation hash of a `k`-block message `m` under key `h`:
`H_h(m) = Σ_{i<k} m_i · h^i`.  This is the *toy* hash with a constant (`h⁰`)
term; the AXU instance below is the constant-term-free `polyvalHash`. -/
def polyHash {n : ℕ} (h : F) (m : Fin n → F) : F :=
  ∑ i : Fin n, m i * h ^ (i : ℕ)

/-- Difference polynomial whose roots are exactly the colliding keys for a pair
of messages: `Σ_{i<n} (m_i - m'_i) · X^i`. -/
noncomputable def diffPoly {n : ℕ} (m m' : Fin n → F) : F[X] :=
  ∑ i : Fin n, C (m i - m' i) * X ^ (i : ℕ)

/-- Evaluating the difference polynomial at the key recovers the hash gap. -/
theorem eval_diffPoly {n : ℕ} (m m' : Fin n → F) (h : F) :
    (diffPoly m m').eval h = polyHash h m - polyHash h m' := by
  unfold diffPoly polyHash
  rw [eval_finset_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [eval_mul, eval_C, eval_pow, eval_X, sub_mul]

/-- Distinct messages give a nonzero difference polynomial. -/
theorem diffPoly_ne_zero {n : ℕ} {m m' : Fin n → F} (hne : m ≠ m') :
    diffPoly m m' ≠ 0 := by
  intro hzero
  apply hne
  funext i
  have hcoeff : (diffPoly m m').coeff (i : ℕ) = m i - m' i := by
    rw [diffPoly, finset_sum_coeff, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_,
      coeff_C_mul_X_pow, if_pos rfl]
    intro j _ hji
    rw [coeff_C_mul_X_pow, if_neg (fun h => hji (Fin.ext h.symm))]
  rw [hzero, coeff_zero] at hcoeff
  exact sub_eq_zero.mp hcoeff.symm

/-- The degree of the difference polynomial is below the block count. -/
theorem natDegree_diffPoly_lt {n : ℕ} (hn : 0 < n) (m m' : Fin n → F) :
    (diffPoly m m').natDegree < n := by
  unfold diffPoly
  refine lt_of_le_of_lt (natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_lt]
  refine ⟨hn, fun i _ => ?_⟩
  exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)) i.isLt

/-! ## POLYVAL-shaped hash (no constant term)

Real GHASH/POLYVAL evaluates the message polynomial with powers starting at
`h¹`: `H_h(A_1,…,A_t) = Σ A_i h^i` has **no `h⁰` term**.  Removing the constant
term makes the collision gap of distinct messages a polynomial with zero
constant coefficient, which over a field larger than the block count can never
be a nonzero constant — the algebraic source of the unconditional ε-AXU
property. -/

/-- **POLYVAL/GHASH-shaped hash**: `H_h(m) = Σ_{i<n} m_i h^(i+1) = h · Σ m_i h^i`,
the message polynomial evaluated with powers starting at `h¹` (no constant
term). -/
def polyvalHash {n : ℕ} (h : F) (m : Fin n → F) : F := h * polyHash h m

/-- The POLYVAL gap polynomial `X · (Σ (m_i−m'_i) X^i)`: the `polyHash`
difference shifted up one degree, so its constant coefficient is zero. -/
noncomputable def polyvalDiffPoly {n : ℕ} (m m' : Fin n → F) : F[X] := X * diffPoly m m'

/-- The gap polynomial evaluates to the POLYVAL gap. -/
theorem eval_polyvalDiffPoly {n : ℕ} (m m' : Fin n → F) (h : F) :
    (polyvalDiffPoly m m').eval h = polyvalHash h m - polyvalHash h m' := by
  unfold polyvalDiffPoly polyvalHash
  rw [eval_mul, eval_X, eval_diffPoly, mul_sub]

/-- **No key-independent (structural) collision — the POLYVAL property.** Over a
field with more than `n` elements, distinct `n`-block messages have *no
constant gap*: there is no `c` with `H_h(m) − H_h(m') = c` for every key `h`.
The gap is a degree-`≤ n` polynomial with zero constant coefficient; were it the
constant `c` at all `|F| > n` points it would be the zero polynomial, forcing
`m = m'` and `c = 0`. -/
theorem polyvalHash_no_const_gap [Fintype F] {n : ℕ} (hn : n < Fintype.card F)
    {m m' : Fin n → F} (hne : m ≠ m') (c : F) :
    ¬ (∀ h : F, polyvalHash h m - polyvalHash h m' = c) := by
  intro hall
  have hvanish : ∀ x : F, (polyvalDiffPoly m m' - C c).eval x = 0 :=
    fun x => by rw [eval_sub, eval_polyvalDiffPoly, eval_C, hall x, sub_self]
  have hdeg : (polyvalDiffPoly m m' - C c).natDegree ≤ n := by
    have hn_pos : 0 < n :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne (funext (fun x => x.elim0)))
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · show (X * diffPoly m m').natDegree ≤ n
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X]
      have hdiff_lt := natDegree_diffPoly_lt hn_pos m m'
      omega
    · rw [natDegree_C]; exact Nat.zero_le _
  have hP_zero : polyvalDiffPoly m m' - C c = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id hvanish
      (lt_of_le_of_lt hdeg hn)
  rw [sub_eq_zero] at hP_zero
  have hc : c = 0 := by
    have h_eval0 := congrArg (Polynomial.eval 0) hP_zero
    simp only [eval_polyvalDiffPoly, polyvalHash, zero_mul, sub_self, eval_C] at h_eval0
    exact h_eval0.symm
  rw [hc, map_zero] at hP_zero
  unfold polyvalDiffPoly at hP_zero
  rw [mul_eq_zero] at hP_zero
  exact hP_zero.elim X_ne_zero (diffPoly_ne_zero hne)

/-- Degree bound for the POLYVAL gap polynomial: `≤ n` (one above `diffPoly`). -/
theorem natDegree_polyvalDiffPoly_le {n : ℕ} (hn_pos : 0 < n) (m m' : Fin n → F) :
    (polyvalDiffPoly m m').natDegree ≤ n := by
  show (X * diffPoly m m').natDegree ≤ n
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X]
  have hdiff_lt := natDegree_diffPoly_lt hn_pos m m'
  omega

/-- **POLYVAL is ε-AXU with no structural exception (count form).** For distinct
`n`-block messages and *any* affine constants `c, c'`, the number of keys with
`c + H_h(M) = c' + H_h(M')` is at most `n`.  Because the POLYVAL gap polynomial
has zero constant coefficient, the affine collision polynomial is never the
zero polynomial, so the count is just its root bound
(`Polynomial.card_roots'`). -/
theorem card_polyval_point_collision_le [Fintype F] [DecidableEq F] {n : ℕ}
    (hn : n < Fintype.card F) (c c' : F) {M M' : Fin n → F} (hne : M ≠ M') :
    (univ.filter (fun h => c + polyvalHash h M = c' + polyvalHash h M')).card ≤ n := by
  have hn_pos : 0 < n :=
    Nat.pos_of_ne_zero (by rintro rfl; exact hne (funext (fun x => x.elim0)))
  have hQ_ne : polyvalDiffPoly M M' - C (c' - c) ≠ 0 := by
    intro hQ0
    refine polyvalHash_no_const_gap hn hne (c' - c) (fun h => ?_)
    have h_eval := congrArg (Polynomial.eval h) hQ0
    rwa [eval_sub, eval_polyvalDiffPoly, eval_C, eval_zero, sub_eq_zero] at h_eval
  have hsub : (univ.filter (fun h => c + polyvalHash h M = c' + polyvalHash h M'))
      ⊆ (polyvalDiffPoly M M' - C (c' - c)).roots.toFinset := by
    intro h hh
    rw [Finset.mem_filter] at hh
    rw [Multiset.mem_toFinset, mem_roots']
    refine ⟨hQ_ne, ?_⟩
    rw [IsRoot.def, eval_sub, eval_polyvalDiffPoly, eval_C, sub_eq_zero]
    linear_combination hh.2
  calc (univ.filter (fun h => c + polyvalHash h M = c' + polyvalHash h M')).card
      ≤ (polyvalDiffPoly M M' - C (c' - c)).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (polyvalDiffPoly M M' - C (c' - c)).roots := Multiset.toFinset_card_le _
    _ ≤ (polyvalDiffPoly M M' - C (c' - c)).natDegree := card_roots' _
    _ ≤ n := (natDegree_sub_le _ _).trans (by
          rw [natDegree_C]
          exact max_le (natDegree_polyvalDiffPoly_le hn_pos M M') (Nat.zero_le _))

/-! ## ε-almost-XOR-universality (abstract, CR18 Def. 6.2) -/

section EpsAXU

variable [Fintype F] [DecidableEq F]

/-- **ε-almost-XOR-universal (CR18 Def. 6.2, count form).** For distinct
messages and any offset `c`, the number of keys with `H h M ⊖ H h M' = c` is at
most `bound` (the count form of `Pr_h[…] ≤ bound/|F|`; over `GF(2^n)`
subtraction is XOR).  This is the affine-collision property consumed by
quasi-random-function security proofs (e.g. HCTR2). -/
def EpsAXU {k : ℕ} (H : F → (Fin k → F) → F) (bound : ℕ) : Prop :=
  ∀ M M' : Fin k → F, M ≠ M' → ∀ c : F,
    (Finset.univ.filter (fun h => H h M - H h M' = c)).card ≤ bound

/-- **ε-AXU (bound `< |F|`) forbids structural collisions — the generic
discharge.** An ε-AXU hash with `bound < |F|` has no key-independent affine
collision on distinct messages: no offset `c` satisfies `H h M ⊖ H h M' = c`
for *every* key (a constant gap would force the colliding-key count to be
`|F| > bound`). -/
theorem EpsAXU.no_const_gap {k : ℕ} {H : F → (Fin k → F) → F} {bound : ℕ}
    (hAXU : EpsAXU H bound) (hbound : bound < Fintype.card F)
    {M M' : Fin k → F} (hne : M ≠ M') (c : F) :
    ¬ (∀ h : F, H h M - H h M' = c) := by
  intro hall
  have hcount : (Finset.univ.filter (fun h => H h M - H h M' = c)).card ≤ bound :=
    hAXU M M' hne c
  have hfull : (Finset.univ.filter (fun h => H h M - H h M' = c)) = Finset.univ :=
    Finset.filter_true_of_mem (fun h _ => hall h)
  rw [hfull, Finset.card_univ] at hcount
  omega

/-- **No structural (key-independent) collision between distinct affine
points — affine form of `no_const_gap`.** For evaluation points affine in the
hash, `ptᵢ(h) = cᵢ ⊕ H_h(mᵢ)`, an ε-AXU hash with `bound < |F|` guarantees that
two points with *distinct messages* `m ≠ m'` never collide simultaneously for
every key: there is no key-independent (structural) collision — with no
restriction on the adversary and no concrete hash. -/
theorem no_structural_collision_of_epsAXU {k : ℕ} {Hh : F → (Fin k → F) → F} {bound : ℕ}
    (hAXU : EpsAXU Hh bound) (hbound : bound < Fintype.card F)
    {c c' : F} {m m' : Fin k → F} (hm : m ≠ m') :
    ¬ (∀ h : F, c + Hh h m = c' + Hh h m') := fun hall =>
  EpsAXU.no_const_gap hAXU hbound hm (c' - c) (fun h => by linear_combination hall h)

/-- **Hash-aware structural collision ⟹ identical affine points (ε-AXU
keystone).** A *key-independent* collision of affine points `c ⊕ H_h(m)` and
`c' ⊕ H_h(m')` — i.e. one that holds for *every* key `h` — forces both the
hashed messages and the affine constants equal.  The message equality is
`no_structural_collision_of_epsAXU` (distinct messages cannot collide for all
keys); the constant equality then follows by cancelling the (now equal) hash
term at any key.  This is the bridge that turns ε-AXU structural
well-formedness into an *output-collision* event (equal messages with colliding
constants), which birthday families bound. -/
theorem structural_collision_eq_of_epsAXU {k : ℕ} {Hh : F → (Fin k → F) → F} {bound : ℕ}
    (hAXU : EpsAXU Hh bound) (hbound : bound < Fintype.card F)
    {c c' : F} {m m' : Fin k → F} (hcol : ∀ h : F, c + Hh h m = c' + Hh h m') :
    m = m' ∧ c = c' := by
  have hm : m = m' := by
    by_contra hne
    exact no_structural_collision_of_epsAXU hAXU hbound hne hcol
  subst hm
  exact ⟨rfl, add_right_cancel (hcol 0)⟩

/-! ## The POLYVAL instance (CR18 Lem. 6.3 shape) -/

/-- **POLYVAL is ε-AXU** with `bound = k` and *no* exception (needs only
`k < |F|`) — the CR18 Lemma 6.3 polynomial-hash instance of the abstract
interface, via `card_polyval_point_collision_le`. -/
theorem polyval_isEpsAXU {k : ℕ} (hk : k < Fintype.card F) :
    EpsAXU (fun h (m : Fin k → F) => polyvalHash h m) k := by
  intro M M' hne c
  have hrw : (Finset.univ.filter (fun h => polyvalHash h M - polyvalHash h M' = c))
      = Finset.univ.filter (fun h => (0:F) + polyvalHash h M = c + polyvalHash h M') := by
    apply Finset.filter_congr
    intro h _
    constructor <;> intro hh <;> linear_combination hh
  rw [hrw]
  exact card_polyval_point_collision_le hk 0 c hne

/-- **POLYVAL has no structural collisions (concrete discharge).** For the
concrete POLYVAL hash with `k < |F|`, two distinct-message affine points never
collide for every key — the abstract `no_structural_collision_of_epsAXU` at the
proved `polyval_isEpsAXU` instance (`bound = k < |F|`). -/
theorem polyval_no_structural_collision {k : ℕ} (hk : k < Fintype.card F)
    {c c' : F} {m m' : Fin k → F} (hm : m ≠ m') :
    ¬ (∀ h : F, c + polyvalHash h m = c' + polyvalHash h m') :=
  no_structural_collision_of_epsAXU (polyval_isEpsAXU hk) hk hm

end EpsAXU

end RandomSystems.CR18
