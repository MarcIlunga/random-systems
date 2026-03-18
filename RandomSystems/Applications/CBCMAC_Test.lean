/-
Test file for verifying cbcMacAllPInputs behavior
-/
import RandomSystems.Applications.CBCMAC

open RandomSystems.Applications

namespace Test

variable {B : Type*} [AddCommGroup B] [DecidableEq B]

-- Test 1: cbcMacPInput at j=0 returns 0 + m 0
example (P : B → B) (ℓ : ℕ) (hℓ : 0 < ℓ) (m : Fin ℓ → B) :
    cbcMacPInput P ℓ m ⟨0, hℓ⟩ = 0 + m ⟨0, hℓ⟩ := by
  simp [cbcMacPInput]

-- Test 2: cbcMacAllPInputs when k % ℓ = 0 gives msgs (k/ℓ) 0
example (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (k : Fin (q * ℓ))
    (hk_mod : k.val % ℓ = 0) :
    cbcMacAllPInputs P ℓ hℓ msgs k =
    msgs ⟨k.val / ℓ, by rwa [Nat.div_lt_iff_lt_mul hℓ]⟩ ⟨0, hℓ⟩ := by
  unfold cbcMacAllPInputs cbcMacPInput
  simp [hk_mod]

-- Test 3: Check that the definition unfolds correctly
-- Let's trace through what happens step by step
#check cbcMacAllPInputs
#check cbcMacPInput
#check cbcMacChainValues

-- Test 4: Understand what cbcMacChainValues computes
-- It should fold over [0..j], computing P(P(...P(0 + m₀)... + mⱼ₋₁) + mⱼ)
-- But the definition uses Fin.foldl (j.val + 1), which runs j+1 steps (indices 0..j)

-- Let's test what happens when k % ℓ ≠ 0
example (P : B → B) {q : ℕ} (ℓ : ℕ) (hℓ : 0 < ℓ)
    (msgs : Fin q → Fin ℓ → B) (k : Fin (q * ℓ))
    (hk_mod : k.val % ℓ ≠ 0) :
    cbcMacAllPInputs P ℓ hℓ msgs k =
    let i : Fin q := ⟨k.val / ℓ, by rwa [Nat.div_lt_iff_lt_mul hℓ]⟩
    let j : Fin ℓ := ⟨k.val % ℓ, Nat.mod_lt k.val hℓ⟩
    let prev := cbcMacChainValues P ℓ (msgs i) ⟨j.val - 1, by omega⟩
    prev + msgs i j := by
  unfold cbcMacAllPInputs cbcMacPInput
  simp [hk_mod]

-- Test 5: Understand the relationship between chain values and P-inputs
-- Looking at the definitions:
-- - cbcMacChainValues P ℓ m j computes the j-th output of the chain
-- - cbcMacPInput P ℓ m j computes the j-th INPUT to P
-- The question is: does cbcMacChainValues P ℓ m j = P(cbcMacPInput P ℓ m j)?

-- Let's check what cbcMacChainValues actually computes
#check @cbcMacChainValues
-- cbcMacChainValues.{u_1} {B : Type u_1} [AddCommGroup B] (P : B → B) (ℓ : ℕ) (m : Fin ℓ → B) : Fin ℓ → B

-- The definition: fun j => Fin.foldl (j.val + 1) (fun acc i => P (acc + m i)) 0
-- This runs j+1 iterations, applying P each time
-- So cbcMacChainValues P ℓ m j should give c_j (the j-th chaining value)

-- And cbcMacPInput P ℓ m j computes c_{j-1} + m_j (the input to get c_j)
-- So YES: cbcMacChainValues P ℓ m j = P(cbcMacPInput P ℓ m j)... but only if we can prove it!

-- Test 6: Verify the structure for ℓ = 1 (single block)
example (P : B → B) (m : Fin 1 → B) :
    cbcMacChainValues P 1 m ⟨0, by omega⟩ = P (m ⟨0, by omega⟩) := by
  rfl  -- Should work by definition

-- Test 7: Verify for ℓ = 2, j = 0
example (P : B → B) (m : Fin 2 → B) :
    cbcMacChainValues P 2 m ⟨0, by omega⟩ = P (m ⟨0, by omega⟩) := by
  rfl

-- Test 8: Verify for ℓ = 2, j = 1
example (P : B → B) (m : Fin 2 → B) :
    cbcMacChainValues P 2 m ⟨1, by omega⟩ =
    P (P (m ⟨0, by omega⟩) + m ⟨1, by omega⟩) := by
  rfl

-- Test 9: Verify cbcMacPInput for ℓ = 2, j = 1
example (P : B → B) (m : Fin 2 → B) :
    cbcMacPInput P 2 m ⟨1, by omega⟩ =
    cbcMacChainValues P 2 m ⟨0, by omega⟩ + m ⟨1, by omega⟩ := by
  simp [cbcMacPInput]

-- Test 10: Confirm the relationship for ℓ = 2, j = 1
example (P : B → B) (m : Fin 2 → B) :
    cbcMacChainValues P 2 m ⟨1, by omega⟩ =
    P (cbcMacPInput P 2 m ⟨1, by omega⟩) := by
  simp [cbcMacPInput]
  rfl

end Test
