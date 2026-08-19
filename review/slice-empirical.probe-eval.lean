import RandomSystems.SumOfPermutationsTight

/-!  ADVERSARIAL REVIEW PROBE (review-only; not part of the library).

Slice `empirical`.  Direct evaluation of the repo's own definitions at small concrete
carriers, cross-checked against an independent enumeration
(`review/slice-empirical.brute-force-adaptive.py`).

Run with:  lake env lean review/slice-empirical.probe-eval.lean
-/

open RandomSystems.CR18.SoPTight

/-! ### 1. `sopEps` really evaluates to the claimed numbers -/
example : sopEps 2 2 = 1     := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 3 2 = 1/4   := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 4 2 = 1/9   := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 5 2 = 1/16  := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 4 3 = 1     := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 5 3 = 73/144 := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 6 3 = 29/100 := by norm_num [sopEps, Finset.sum_range_succ]
example (N : ℕ) : sopEps N 0 = 0 := by simp [sopEps]
example (N : ℕ) : sopEps N 1 = 0 := by norm_num [sopEps, Finset.sum_range_succ]
-- the `N = 1` division-by-zero quirk (Lean: x/0 = 0)
example : sopEps 1 2 = 0 := by norm_num [sopEps, Finset.sum_range_succ]
example : sopEps 1 3 = 1 := by norm_num [sopEps, Finset.sum_range_succ]

/-! ### 2. `goodCount d` — the surviving-pair count -/
-- expected: (N-d)!² · ∏_{k<d}(N-2k);  hits 0 as soon as 2k ≥ N for some k < d
#eval (goodCount (ZMod 2) 0, goodCount (ZMod 2) 1, goodCount (ZMod 2) 2)
        -- (4, 2, 0)
#eval (goodCount (ZMod 3) 0, goodCount (ZMod 3) 1, goodCount (ZMod 3) 2, goodCount (ZMod 3) 3)
        -- (36, 12, 3, 0)
#eval (goodCount (ZMod 4) 0, goodCount (ZMod 4) 1, goodCount (ZMod 4) 2, goodCount (ZMod 4) 3)
        -- (576, 144, 32, 0)
#eval (goodCount (ZMod 5) 0, goodCount (ZMod 5) 1, goodCount (ZMod 5) 2, goodCount (ZMod 5) 3)
        -- (14400, 2880, 540, 60)

/-! ### 3. The real system's transcript law: fiber counts of `sopFunction` -/
-- 2 queries over ZMod 3 (36 permutation pairs).  Expect 6 on the diagonal
-- (= N!²/(N(N-1))) and 3 off it (= N!²(N-2)/(N(N-1)²)).
#eval ((List.range 3).flatMap fun a => (List.range 3).map fun b =>
  ((a, b), (Finset.univ.filter (fun p : Equiv.Perm (ZMod 3) × Equiv.Perm (ZMod 3) =>
      sopFunction p 0 = (a : ZMod 3) ∧ sopFunction p 1 = (b : ZMod 3))).card))

-- 3 queries over ZMod 3: the support is exactly {y : y₀+y₁+y₂ = 0}
#eval ((List.range 3).flatMap fun a => (List.range 3).flatMap fun b => (List.range 3).map fun c =>
  ((a, b, c), (Finset.univ.filter (fun p : Equiv.Perm (ZMod 3) × Equiv.Perm (ZMod 3) =>
      sopFunction p 0 = (a : ZMod 3) ∧ sopFunction p 1 = (b : ZMod 3)
        ∧ sopFunction p 2 = (c : ZMod 3))).card))

-- 2 queries over ZMod 2: the two answers ALWAYS agree (the file docstring's remark)
#eval ((List.range 2).flatMap fun a => (List.range 2).map fun b =>
  ((a, b), (Finset.univ.filter (fun p : Equiv.Perm (ZMod 2) × Equiv.Perm (ZMod 2) =>
      sopFunction p 0 = (a : ZMod 2) ∧ sopFunction p 1 = (b : ZMod 2))).card))

-- 2 queries over ZMod 4 (576 pairs): 48 on the diagonal, 32 off it
#eval ((List.range 4).flatMap fun a => (List.range 4).map fun b =>
  ((a, b), (Finset.univ.filter (fun p : Equiv.Perm (ZMod 4) × Equiv.Perm (ZMod 4) =>
      sopFunction p 0 = (a : ZMod 4) ∧ sopFunction p 1 = (b : ZMod 4))).card))
