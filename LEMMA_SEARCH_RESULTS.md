# Lemma Search Results for `urpq_ge_urf_on_injective_transcript`

## Summary

For proving `urpq_ge_urf_on_injective_transcript` (URF.transcriptDist ≤ URPq.transcriptDist on injective transcripts), the following lemmas are available:

---

## 1. ✅ `Nat.descFactorial_le_pow` — FOUND

**Location:** `Mathlib.Data.Nat.Factorial.Basic`

**Signature:**
```lean
Nat.descFactorial_le_pow (n k : ℕ) : n.descFactorial k ≤ n ^ k
```

**Usage:** This is the key inequality showing `descFactorial(|X|, q) ≤ |X|^q`, which translates to:
- `1/|X|^q ≤ 1/descFactorial(|X|, q)` (for NNReal)
- Equivalently: `(|X| - q)! / |X|! ≤ |X|^(|X| - q) / |X|^|X|`

---

## 2. ✅ NNReal Division Lemmas — FOUND

### `div_le_div_iff₀`

**Location:** `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic`

**Signature:**
```lean
div_le_div_iff₀ {G₀ : Type u_3} [inst : CommGroupWithZero G₀] [inst_1 : PartialOrder G₀]
  [PosMulReflectLT G₀] {a b c d : G₀} :
  0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)
```

**Usage in codebase:** See `PRPPRFSwitching.lean:268`:
```lean
rw [div_eq_div_iff]
· simp only [one_mul]; exact_mod_cast h_fiber
· exact Nat.cast_ne_zero.mpr ...  -- b ≠ 0
· exact Nat.cast_ne_zero.mpr ...  -- d ≠ 0
```

**Alternative:** `div_eq_div_iff` (similar but uses `≠ 0` instead of `> 0`)

### `div_le_div_of_nonneg_right`

**Location:** Used in `CBCMAC.lean` and `PRPPRFSwitching.lean`

**Pattern:**
```lean
apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
```

For showing `a/c ≤ b/c` when `a ≤ b` and `c ≥ 0`.

---

## 3. ⚠️ `Finsupp.mapDomain` Fiber Counting — NO SPECIFIC LEMMA

**What exists:** General `Finsupp.mapDomain` lemmas in `Mathlib.Data.Finsupp.Basic`:
- `Finsupp.mapDomain_equiv_apply`
- `Finsupp.mapDomain_apply'`
- `Finsupp.mapDomain_congr`

**What's needed:** Manual fiber counting by:
1. Unfolding `transcriptDist` to `Dist.fTransform`
2. Unfolding `Dist.fTransform` to `Finsupp.mapDomain`
3. Computing `(Finsupp.mapDomain f dist) t` as `∑ s ∈ fiber, dist s`
4. Where `fiber = {s | f s = t}`

**Pattern from codebase:** See `PRPPRFSwitching.lean:242-253`:
```lean
show (Finsupp.mapDomain eval dist) y = _
rw [Finsupp.mapDomain_finset_sum]
simp only [Finsupp.mapDomain_single]
rw [Finsupp.coe_finset_sum, Finset.sum_apply]
simp only [Finsupp.single_apply]
rw [← Finset.sum_filter]
simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
-- Goal: ↑|fiber| / ↑|total| = target
```

---

## 4. ✅ Counting Functions with Prescribed Values — FOUND

### `Fintype.card_filter_piFinset_const_eq_of_mem`

**Location:** `Mathlib.Data.Fintype.BigOperators`

**Signature:**
```lean
Fintype.card_filter_piFinset_const_eq_of_mem {ι : Type u_4} {κ : Type u_5}
  [DecidableEq ι] [DecidableEq κ] [Fintype ι] (s : Finset κ) (i : ι) {x : κ} :
  x ∈ s →
    (Finset.filter (fun f => f i = x) (Fintype.piFinset fun _ => s)).card =
    s.card ^ (Fintype.card ι - 1)
```

**Interpretation:** The number of functions `ι → κ` mapping `i` to `x` (with all values in `s`) is `|s|^(|ι| - 1)`.

**Usage in codebase:** `PRPPRFSwitching.lean:116`:
```lean
have h := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset X) x₀
  (Finset.mem_univ y)
rw [Fintype.piFinset_univ, Finset.card_univ] at h
-- h : |{f : X → X | f x₀ = y}| = |X|^(|X| - 1)
```

**Multi-point version:** `Fintype.card_filter_piFinset_eq_of_mem` for dependent types.

---

## 5. ⚠️ Permutation Fiber Counting — NO DIRECT LEMMA

### What exists:

**`Fintype.card_perm`**
```lean
Fintype.card_perm : Fintype.card (Equiv.Perm X) = (Fintype.card X).factorial
```

### What's needed:

Count permutations extending a partial injection `{inputs[i] ↦ outputs[i] | i < q}`.

**Key insight:** This is `(|X| - q)!` — the number of ways to extend the partial map to a full permutation.

**No direct Mathlib lemma found.** But see:

### `card_statelessPerm` (already in URP.lean)

**Location:** `RandomSystems/Instances/URP.lean:112-124`

```lean
theorem card_statelessPerm (hq : 0 < q) :
    ((Finset.univ : Finset (DDS X X q)).filter isStatelessPerm).card =
    (Fintype.card X).factorial
```

**Proof strategy:** Use equivalence `statelessPermEquiv : {s // isStatelessPerm s} ≃ Equiv.Perm X`.

### Pattern for multi-point fiber counting:

From `PRPPRFSwitching.lean:147-200` (single-point case):
1. Define bijection between fibers via `Equiv.swap`
2. Show all fibers have equal size
3. Use partition: `|perms| = ∑ y, |fiber_y|`
4. Conclude: `|fiber_y| * |X| = |perms|`

**For multi-query case:**
- Fiber of stateless perms with `π(inputs[i]) = outputs[i]` for all `i < q`
- Size = `(|X| - q)!` (permute the remaining `|X| - q` elements)
- Total perms = `|X|!`
- Ratio = `(|X| - q)! / |X|!`

---

## 6. Key Patterns from Existing Code

### Casting with `exact_mod_cast`

**Usage:** Convert `ℕ` to `NNReal` while preserving inequalities:
```lean
have h_nat : a ≤ b  -- in ℕ
exact_mod_cast h_nat  -- goal: (a : NNReal) ≤ (b : NNReal)
```

### Zero checks for division

**Pattern:**
```lean
rw [div_le_div_iff₀ h_pos_b h_pos_d]
-- or
rw [div_eq_div_iff]
· exact_mod_cast h_cross_multiply
· exact Nat.cast_ne_zero.mpr h_b_ne_zero
· exact Nat.cast_ne_zero.mpr h_d_ne_zero
```

### Computing fiber cardinality

**Pattern from PRPPRFSwitching.lean:104-118:**
```lean
have h_fiber_card : (Finset.univ.filter (fun s => predicate s)).card = target := by
  rw [show ... = ... from by apply Finset.card_bij ...]
  have h := Fintype.card_filter_piFinset_const_eq_of_mem ...
  exact h
```

### Ratio simplification

**Pattern from PRPPRFSwitching.lean:123-136:**
```lean
rw [h_fiber_card, h_total_card]
push_cast
set n := (Fintype.card X : NNReal)
have h_pos : 0 < Fintype.card X := Fintype.card_pos
have h_ne : n ≠ 0 := Nat.cast_ne_zero.mpr h_pos.ne'
have h_pow_ne : n ^ k ≠ 0 := pow_ne_zero _ h_ne
have h_card_eq : Fintype.card X = k + 1 := by omega
rw [h_card_eq, pow_succ]
rw [show n ^ k / (n ^ k * n) = n ^ k * (n ^ k * n)⁻¹ from rfl]
rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h_pow_ne, one_mul]
```

---

## Recommended Proof Strategy

### For `urpq_ge_urf_on_injective_transcript`:

1. **Unfold to fiber ratios:**
   ```lean
   simp only [PDS.transcriptDist, Dist.fTransform]
   rw [Finsupp.mapDomain_finset_sum]
   -- Reduce to: |urf_fiber| / |DDS| ≤ |urpq_fiber| / |perms|
   ```

2. **Compute URF fiber size:**
   ```lean
   have h_urf_fiber : urf_fiber.card = Fintype.card X ^ (Fintype.card X - q) := by
     -- Use Fintype.card_filter_piFinset_const_eq_of_mem (multi-point version)
     -- or direct equivalence to function fiber
   ```

3. **Compute URPq fiber size:**
   ```lean
   have h_urpq_fiber : urpq_fiber.card = (Fintype.card X - q).factorial := by
     -- Manual counting: perms extending inputs → outputs
     -- Build equivalence to {π : Perm X | ∀ i, π(inputs[i]) = outputs[i]}
   ```

4. **Compute total sizes:**
   ```lean
   have h_dds_card : Fintype.card (DDS X X q) = Fintype.card X ^ Fintype.card X
   have h_perm_card : perms.card = (Fintype.card X).factorial := card_statelessPerm
   ```

5. **Apply division inequality:**
   ```lean
   rw [div_le_div_iff₀ h_dds_pos h_perm_pos]
   -- Goal: |X|^(|X|-q) * |X|! ≤ (|X|-q)! * |X|^|X|
   -- Rearrange: (|X|-q)! / |X|! ≤ |X|^(|X|-q) / |X|^|X|
   -- Simplify: (|X|-q)! / |X|! ≤ 1 / |X|^q
   -- Use: descFactorial |X| q / |X|! = (|X|-q)! / |X|!
   -- Apply: Nat.descFactorial_le_pow
   ```

6. **Key arithmetic:**
   ```lean
   have : (Fintype.card X).factorial =
          (Fintype.card X).descFactorial q * ((Fintype.card X) - q).factorial := by
     rw [Nat.descFactorial_eq_div, ← Nat.mul_div_assoc]
   rw [this]
   -- Reduce to: descFactorial |X| q ≤ |X|^q
   exact Nat.descFactorial_le_pow _ _
   ```

---

## Files to Reference

1. **`RandomSystems/Applications/PRPPRFSwitching.lean`** — q=1 case with similar fiber counting
2. **`RandomSystems/Applications/CTRMode.lean`** — multi-query fiber decomposition patterns
3. **`RandomSystems/Instances/URP.lean`** — `card_statelessPerm`, `statelessPermEquiv`
4. **`RandomSystems/Instances/URF.lean`** — DDS cardinality lemmas

---

## Key Mathlib Imports

```lean
import Mathlib.Data.Nat.Factorial.Basic          -- descFactorial_le_pow
import Mathlib.Data.Fintype.BigOperators         -- card_filter_piFinset_const_eq_of_mem
import Mathlib.Data.Fintype.Perm                 -- card_perm
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic  -- div_le_div_iff₀
```

---

## Summary of Findings

| Query | Status | Location |
|-------|--------|----------|
| `Nat.descFactorial_le_pow` | ✅ Found | `Mathlib.Data.Nat.Factorial.Basic` |
| NNReal division inequality | ✅ Found | `div_le_div_iff₀`, `div_eq_div_iff` |
| `Finsupp.mapDomain` fiber | ⚠️ Manual | Unfold to filter + sum |
| Multi-point function counting | ✅ Found | `Fintype.card_filter_piFinset_eq_of_mem` |
| Permutation fiber counting | ⚠️ Manual | Build equivalence, use `card_statelessPerm` |

**Bottom line:** All key lemmas exist or have been proved in the codebase. The main work is:
1. Connecting DDS fiber counting to Mathlib's function/permutation lemmas
2. Arithmetic manipulation to apply `descFactorial_le_pow`
