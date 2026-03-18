# Analysis of cbcMacAllPInputs Evaluation

## Question

What does `cbcMacAllPInputs P ℓ hℓ msgs ⟨k, hk⟩` evaluate to when `k % ℓ = 0`?

## Answer

**When `k % ℓ = 0`:**
```lean
cbcMacAllPInputs P ℓ hℓ msgs ⟨k, hk⟩ = msgs (k / ℓ) 0
```

**Crucially:** This value is **independent of P** (the permutation).

## Proof

This is already proved in CBCMAC.lean as theorem `cbcMacAllPInputs_block_zero` (line 357):

```lean
theorem cbcMacAllPInputs_block_zero {B : Type*} [AddCommGroup B]
    (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (a : Fin (q * ℓ))
    (ha : a.val % ℓ = 0) :
    cbcMacAllPInputs P ℓ hℓ msgs a =
    msgs ⟨a.val / ℓ, ...⟩ ⟨0, hℓ⟩ := by
  simp only [cbcMacAllPInputs, cbcMacPInput]
  simp [ha, zero_add]
```

## Step-by-Step Derivation

### 1. Expand cbcMacAllPInputs

Given `k` with `k % ℓ = 0`:

```lean
cbcMacAllPInputs P ℓ hℓ msgs k
= let i := ⟨k.val / ℓ, ...⟩
  let j := ⟨k.val % ℓ, ...⟩
  cbcMacPInput P ℓ (msgs i) j
```

Since `k % ℓ = 0`, we have `j = ⟨0, hℓ⟩`.

### 2. Expand cbcMacPInput at j = 0

```lean
cbcMacPInput P ℓ (msgs i) ⟨0, hℓ⟩
= let prev := if h : 0 = 0 then 0
              else cbcMacChainValues P ℓ (msgs i) ⟨0 - 1, ...⟩
  prev + msgs i ⟨0, hℓ⟩
```

The condition `0 = 0` is true, so:
```lean
= 0 + msgs i ⟨0, hℓ⟩
= msgs i 0
```

where `i = k / ℓ`.

### 3. Result

```lean
cbcMacAllPInputs P ℓ hℓ msgs k = msgs (k / ℓ) 0
```

This is **the first block of message k/ℓ**, regardless of what P is.

## Case: k % ℓ ≠ 0

When `k % ℓ ≠ 0`, the P-input **does depend on P**:

```lean
cbcMacAllPInputs P ℓ hℓ msgs k
= let i := k / ℓ
  let j := k % ℓ
  cbcMacChainValues P ℓ (msgs i) ⟨j - 1, ...⟩ + msgs i j
```

The `cbcMacChainValues` term depends on P because it computes:
```
c_{j-1} = P(...P(P(msgs i 0) + msgs i 1)... + msgs i (j-1))
```

## Relationship: Chain Values and P-Inputs

The definitions satisfy (verified by reflexivity for concrete cases):

```lean
cbcMacChainValues P ℓ m j = P (cbcMacPInput P ℓ m j)
```

That is:
- `cbcMacPInput P ℓ m j` computes the **input** to P at step j: `c_{j-1} + m_j`
- `cbcMacChainValues P ℓ m j` computes the **output** of P at step j: `c_j = P(c_{j-1} + m_j)`

This confirms the CBC-MAC chaining structure:
```
c_0 = P(0 + m_0) = P(m_0)
c_1 = P(c_0 + m_1)
c_j = P(c_{j-1} + m_j)
```

## Concrete Examples Verified

All of the following were verified to hold **by reflexivity** (rfl) or **by simp**:

1. ✓ `cbcMacPInput P ℓ m ⟨0, hℓ⟩ = 0 + m ⟨0, hℓ⟩`
2. ✓ `cbcMacAllPInputs P ℓ hℓ msgs k = msgs (k/ℓ) 0` when `k % ℓ = 0`
3. ✓ `cbcMacChainValues P 1 m ⟨0, _⟩ = P (m ⟨0, _⟩)`
4. ✓ `cbcMacChainValues P 2 m ⟨0, _⟩ = P (m ⟨0, _⟩)`
5. ✓ `cbcMacChainValues P 2 m ⟨1, _⟩ = P (P (m ⟨0, _⟩) + m ⟨1, _⟩)`
6. ✓ `cbcMacChainValues P 2 m ⟨1, _⟩ = P (cbcMacPInput P 2 m ⟨1, _⟩)`

## Implications for the Collision Bound Proof

### Context

The sorry at line 574 (`h_per_j`) in `cbcMac_step_collision_bound` needs to prove:

```lean
∀ j : Fin k, (S j).card * Fintype.card B ≤ Fintype.card (DDS B B 1)
```

where `S j` is:
```lean
{P | goodUpTo P k ∧ v_k = v_j}
```

and `v_i = cbcMacAllPInputs P ℓ hℓ msgs i`.

### Key Insights from This Analysis

1. **Block boundaries are special:**
   - When `j % ℓ = 0` and `k % ℓ = 0`, both `v_j` and `v_k` are independent of P
   - If `v_j = v_k` in this case, then `msgs (j/ℓ) 0 = msgs (k/ℓ) 0`
   - This is a deterministic collision that violates `h_no_forced_collision` (unless j = k)

2. **Within-chain dependencies:**
   - When indices are not at block boundaries, v_i depends on P through chain values
   - The dependency structure is: `v_k` depends on P's behavior at indices `< k` in the same message

3. **Cross-message independence:**
   - If j and k are in different messages (⌊j/ℓ⌋ ≠ ⌊k/ℓ⌋), their chain values are computed independently
   - This suggests the injection argument may factor by message index

### Suggested Proof Strategy for h_per_j

The proof needs to construct an injection from:
```
{(P, x) | P ∈ S_j, x ∈ B} → {P | goodUpTo P k}
```

**Intuition:** Given P with v_k = v_j, we can modify P at the colliding input to "fix" the collision,
and this gives us |B| distinct functions, all satisfying goodUpTo k.

**Challenge:** The modification must:
1. Change v_k (break the collision)
2. Preserve goodUpTo k (not create new collisions)
3. Be injective (different x values give different P')

The fact that v_k = v_j means the k-th P-input equals the j-th P-input.
Using `Function.update P (input_value) new_output` at the colliding input should work,
but the formal proof requires careful case analysis based on where j and k fall in the message structure.

## Test Files

- **CBCMAC_Test.lean**: Contains executable examples verifying the behavior
- **CBCMAC_VERIFICATION.md**: Full verification documentation with proofs
- **CBCMAC_ANALYSIS.md**: This file
