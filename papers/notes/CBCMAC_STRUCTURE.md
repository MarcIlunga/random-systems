# CBC-MAC P-Input Structure Visualization

## Overview

This document visualizes how `cbcMacAllPInputs P ℓ hℓ msgs k` computes P-inputs for CBC-MAC.

## Index Mapping

For q messages of ℓ blocks each, indices k ∈ Fin(q·ℓ) map to:
```
k → (message i = k / ℓ, block j = k % ℓ)
```

Example with q=3, ℓ=4 (12 total P-applications):

```
k  | i=k/4 | j=k%4 | Meaning
---|-------|-------|------------------
0  | 0     | 0     | Message 0, block 0
1  | 0     | 1     | Message 0, block 1
2  | 0     | 2     | Message 0, block 2
3  | 0     | 3     | Message 0, block 3
4  | 1     | 0     | Message 1, block 0 ← boundary
5  | 1     | 1     | Message 1, block 1
6  | 1     | 2     | Message 1, block 2
7  | 1     | 3     | Message 1, block 3
8  | 2     | 0     | Message 2, block 0 ← boundary
9  | 2     | 1     | Message 2, block 1
10 | 2     | 2     | Message 2, block 2
11 | 2     | 3     | Message 2, block 3
```

## P-Input Computation

### Case 1: j = 0 (message start, k % ℓ = 0)

```
v_k = cbcMacAllPInputs P ℓ hℓ msgs k
    = cbcMacPInput P ℓ (msgs i) 0
    = 0 + (msgs i) 0
    = (msgs i) 0                  ← INDEPENDENT OF P
```

**Examples:**
- v_0 = msgs 0 0  (first block of message 0)
- v_4 = msgs 1 0  (first block of message 1)
- v_8 = msgs 2 0  (first block of message 2)

### Case 2: j > 0 (within message, k % ℓ ≠ 0)

```
v_k = cbcMacAllPInputs P ℓ hℓ msgs k
    = cbcMacPInput P ℓ (msgs i) j
    = c_{i,j-1} + (msgs i) j      ← DEPENDS ON P
```

where `c_{i,j-1} = cbcMacChainValues P ℓ (msgs i) (j-1)` is computed via:
```
c_{i,0} = P((msgs i) 0)
c_{i,1} = P(c_{i,0} + (msgs i) 1)
c_{i,j} = P(c_{i,j-1} + (msgs i) j)
```

**Examples:**
- v_1 = c_{0,0} + msgs 0 1 = P(msgs 0 0) + msgs 0 1
- v_2 = c_{0,1} + msgs 0 2 = P(c_{0,0} + msgs 0 1) + msgs 0 2
- v_5 = c_{1,0} + msgs 1 1 = P(msgs 1 0) + msgs 1 1

## Chain Value Structure

For a single message (msgs i), the chain evolves:

```
Input to P     Chain value         P-Input for next block
━━━━━━━━━━     ━━━━━━━━━━━         ━━━━━━━━━━━━━━━━━━━━
(msgs i) 0 ──→ c_{i,0} = P(...)  ──→ (for v_{4i+1})

c_{i,0} + (msgs i) 1 ──→ c_{i,1} = P(...) ──→ (for v_{4i+2})

c_{i,1} + (msgs i) 2 ──→ c_{i,2} = P(...) ──→ (for v_{4i+3})

c_{i,2} + (msgs i) 3 ──→ c_{i,3} = P(...) = tag_i
```

**Key observation:** Each message's chain is independent until P-inputs are compared.

## Collision Structure

### Type A: Boundary-Boundary Collision (both k % ℓ = 0 and j % ℓ = 0)

```
v_j = (msgs j/ℓ) 0     (independent of P)
v_k = (msgs k/ℓ) 0     (independent of P)
```

If v_j = v_k, then this is a **forced collision** (deterministic).
- Ruled out by `h_no_forced_collision` (unless j = k)

### Type B: Boundary-Internal Collision (j % ℓ = 0, k % ℓ ≠ 0)

```
v_j = (msgs j/ℓ) 0                    (independent of P)
v_k = c_{k/ℓ, k%ℓ-1} + (msgs k/ℓ) (k%ℓ)  (depends on P)
```

The collision depends on P. Probability analysis:
- v_j is fixed
- v_k depends on a chain value c_{k/ℓ, k%ℓ-1}
- Under uniform P, conditioned on no prior collision, c_{k/ℓ, k%ℓ-1} is uniformly distributed
- So Pr[v_k = v_j | goodUpTo k] ≈ 1/|B|

### Type C: Internal-Internal Collision (both k % ℓ ≠ 0 and j % ℓ ≠ 0)

```
v_j = c_{j/ℓ, j%ℓ-1} + (msgs j/ℓ) (j%ℓ)  (depends on P)
v_k = c_{k/ℓ, k%ℓ-1} + (msgs k/ℓ) (k%ℓ)  (depends on P)
```

**Sub-case C1:** Different messages (j/ℓ ≠ k/ℓ)
- The chains are computed independently
- Both chain values are random under uniform P (conditioned on goodUpTo)

**Sub-case C2:** Same message (j/ℓ = k/ℓ, but j < k)
- v_k depends on c_{i, k%ℓ-1}
- c_{i, k%ℓ-1} depends on earlier blocks, including the block containing v_j
- Dependency is through the chain, but the final distribution is still uniform

## Injection Argument Sketch for h_per_j

For each witness j < k where collision could occur:

```
S_j = {P | goodUpTo P k ∧ v_k = v_j}
```

To show `|S_j| * |B| ≤ |DDS B B 1|`:

1. **Identify the collision witness:**
   - There exists input value u such that P(u) appears in the computation of v_k
   - The collision v_k = v_j means u equals some input computed from P's prior outputs

2. **Construct injection:**
   - For each (P, x) where P ∈ S_j and x ∈ B, define P' = Function.update P u x
   - P' changes P(u) from its original value to x
   - This breaks the collision at step k (changes v_k)

3. **Show injectivity:**
   - Different x values give different P' (by construction)
   - Different P ∈ S_j (with same x) give different P' (on other inputs)

4. **Show goodUpTo is preserved:**
   - This is the subtle part: need to verify that changing P(u) doesn't introduce
     new collisions among indices < k
   - Uses the fact that goodUpTo k means all v_i for i < k are distinct

The proof complexity comes from tracking which indices are affected by the change
and ensuring no new collisions are introduced.

## Dependency Graph Example (q=2, ℓ=3)

```
Message 0:
  v_0 = m[0,0]                         ← no P dependency
  v_1 = P(m[0,0]) + m[0,1]             ← depends on v_0
  v_2 = P(P(m[0,0]) + m[0,1]) + m[0,2] ← depends on v_0, v_1

Message 1:
  v_3 = m[1,0]                         ← no P dependency
  v_4 = P(m[1,0]) + m[1,1]             ← depends on v_3
  v_5 = P(P(m[1,0]) + m[1,1]) + m[1,2] ← depends on v_3, v_4
```

Cross-message collisions (e.g., v_2 = v_5) have no chaining dependency.
Within-message collisions (e.g., v_1 = v_2) have sequential dependency.

## Summary

- **Block boundaries (k % ℓ = 0):** P-input is INDEPENDENT of P
- **Within blocks (k % ℓ ≠ 0):** P-input DEPENDS on P through chain values
- **Cross-message chains:** Independent until P-inputs are compared
- **Collision types:** Boundary-boundary (forced), boundary-internal, internal-internal
- **Proof strategy:** Use `Function.update` to inject, verify goodUpTo preservation
