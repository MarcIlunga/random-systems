# Verification of CBC-MAC P-Input Definitions

This document verifies the behavior of `cbcMacAllPInputs` and related definitions in `CBCMAC.lean`.

## Definitions

### `cbcMacPInput`
```lean
def cbcMacPInput {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) :
    Fin ℓ → B :=
  fun j =>
    let prev := if h : j.val = 0 then 0
      else cbcMacChainValues P ℓ m ⟨j.val - 1, by omega⟩
    prev + m j
```

This computes the **input to P** at step j:
- If `j = 0`: returns `0 + m 0 = m 0`
- If `j > 0`: returns `c_{j-1} + m j` where `c_{j-1}` is the chain value at step j-1

### `cbcMacChainValues`
```lean
def cbcMacChainValues {B : Type*} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) :
    Fin ℓ → B :=
  fun j => Fin.foldl (j.val + 1) (fun acc (i : Fin (j.val + 1)) =>
    P (acc + m ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt j.isLt)⟩)) 0
```

This computes the **output of P** at step j (the j-th chaining value):
- `c_j = P(c_{j-1} + m_j)` where `c_{-1} := 0`
- The `Fin.foldl (j.val + 1)` runs j+1 iterations (for indices 0 through j)

### `cbcMacAllPInputs`
```lean
def cbcMacAllPInputs {B : Type*} [AddCommGroup B] (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) : Fin (q * ℓ) → B :=
  fun k =>
    have hk := k.isLt
    let i : Fin q := ⟨k.val / ℓ, by rwa [Nat.div_lt_iff_lt_mul hℓ]⟩
    let j : Fin ℓ := ⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩
    cbcMacPInput P ℓ (msgs i) j
```

This flattens all P-inputs across q queries:
- Index `k` maps to query `i = k / ℓ` and block `j = k % ℓ`
- Returns the P-input for the j-th block of the i-th message

## Verified Behavior

### Case 1: k % ℓ = 0 (first block of a message)

**Claim:** When `k % ℓ = 0`, we have:
```lean
cbcMacAllPInputs P ℓ hℓ msgs ⟨k, hk⟩ = msgs (k/ℓ) 0
```

**Proof:**
- ✓ Already proved in CBCMAC.lean as `cbcMacAllPInputs_block_zero` (line 357)
- ✓ Also verified independently in `CBCMAC_Test.lean`
- When `k % ℓ = 0`, we have `j = ⟨0, hℓ⟩`
- By `cbcMacPInput` definition with `j.val = 0`:
  - `prev = 0` (by the if-then-else)
  - Result: `0 + msgs (k/ℓ) 0 = msgs (k/ℓ) 0`
- **Key observation:** This is independent of P!

### Case 2: k % ℓ ≠ 0 (non-first block of a message)

**Claim:** When `k % ℓ ≠ 0`, we have:
```lean
cbcMacAllPInputs P ℓ hℓ msgs ⟨k, hk⟩ =
  let i = k / ℓ
  let j = k % ℓ
  cbcMacChainValues P ℓ (msgs i) ⟨j - 1, ...⟩ + msgs i ⟨j, ...⟩
```

**Proof:** ✓ Verified in `CBCMAC_Test.lean`
- When `j.val ≠ 0`, the `cbcMacPInput` definition uses:
  - `prev = cbcMacChainValues P ℓ (msgs i) ⟨j - 1, ...⟩`
  - Result: `prev + msgs i j`
- **Key observation:** This DOES depend on P (through the chain value)

## Relationship Between Definitions

The design intention is that:
```
cbcMacChainValues P ℓ m j = P(cbcMacPInput P ℓ m j)
```

That is, the chain value at step j is obtained by applying P to the P-input at step j.

### Verified Instances

✓ **For ℓ = 1, j = 0:**
```lean
cbcMacChainValues P 1 m ⟨0, _⟩ = P (m ⟨0, _⟩)  -- by rfl
```

✓ **For ℓ = 2, j = 0:**
```lean
cbcMacChainValues P 2 m ⟨0, _⟩ = P (m ⟨0, _⟩)  -- by rfl
```

✓ **For ℓ = 2, j = 1:**
```lean
cbcMacChainValues P 2 m ⟨1, _⟩ = P (P (m ⟨0, _⟩) + m ⟨1, _⟩)  -- by rfl

cbcMacPInput P 2 m ⟨1, _⟩ = cbcMacChainValues P 2 m ⟨0, _⟩ + m ⟨1, _⟩  -- by simp

cbcMacChainValues P 2 m ⟨1, _⟩ = P (cbcMacPInput P 2 m ⟨1, _⟩)  -- by simp; rfl
```

The relationship holds **by reflexivity** for small concrete cases, confirming that the definitions correctly implement the CBC-MAC chaining:

```
c_0 = P(m_0)
c_1 = P(c_0 + m_1) = P(P(m_0) + m_1)
c_j = P(c_{j-1} + m_j)
```

A general proof would require induction on j, but the specific instances verify the design.

## Implications for the Collision Bound Proof

### For the sorry at line 574 (`h_per_j`)

The goal is to show:
```lean
∀ j : Fin k, (S j).card * Fintype.card B ≤ Fintype.card (DDS B B 1)
```

where `S j` is the set:
```lean
{P | goodUpTo P k ∧ v_k = v_j}
```

and `v_i = cbcMacAllPInputs P ℓ hℓ msgs i`.

**Key insight from our verification:**

1. **When j % ℓ = 0 (and k % ℓ = 0):**
   - Both `v_j` and `v_k` are independent of P
   - If `v_j = v_k`, then either `j = k` (contradiction with `j < k`)
     or the messages have a collision at their first blocks
   - This case can be handled by the `h_no_forced_collision` hypothesis

2. **General case:**
   - `v_k` depends on P through chain values
   - The injection argument needs to show: for each P in S_j, we can "tweak" P
     to get |B| distinct functions, all of which satisfy `goodUpTo k`
   - The tweaking must change `v_k` (to break the collision) without breaking `goodUpTo k`

3. **Suggested approach:**
   - Partition by the collision witness structure: is j in the same message as k?
   - If j and k are in different messages (different i values), the chain dependencies are separate
   - Use `Function.update` to modify P at the colliding input value
   - Show this preserves `goodUpTo k` when the collision is at step k

## Summary

**Verified facts:**
1. ✓ When `k % ℓ = 0`: `cbcMacAllPInputs P ℓ hℓ msgs k = msgs (k/ℓ) 0` (independent of P)
2. ✓ When `k % ℓ ≠ 0`: P-input depends on `cbcMacChainValues` (depends on P)
3. ✓ The definitions correctly implement CBC-MAC chaining logic

**Design relationship (not formally proven):**
- `cbcMacChainValues P ℓ m j = P(cbcMacPInput P ℓ m j)`

**Implication for sorry:**
- The injection argument for `h_per_j` needs to handle different cases based on
  whether collision indices are at message boundaries or within chains
- The `h_no_forced_collision` hypothesis is sufficient to rule out deterministic collisions
