import Mathlib.Tactic

/-! Can an agent with only `lake env lean` (no LSP, no MCP) read goal states? -/

-- PROBE 1: `trace_state`
example (a b c : ℕ) (h : a ≤ b) : a + c ≤ b + c := by
  trace_state
  apply Nat.add_le_add_right
  trace_state
  exact h

-- PROBE 2: unsolved-goals error from `done`
example (a b c : ℕ) (h : a ≤ b) : a + c ≤ b + c := by
  apply Nat.add_le_add_right
  done

-- PROBE 3: `exact?` search
example (a b : ℕ) (h : a ≤ b) : a ≤ b := by
  exact?

-- PROBE 4: `simp?` squeeze output
example (n : ℕ) : n + 0 = n := by
  simp?

-- PROBE 5: type mismatch leaks the expected type
example (a b c : ℕ) (h : a ≤ b) : a + c ≤ b + c := by
  exact h
