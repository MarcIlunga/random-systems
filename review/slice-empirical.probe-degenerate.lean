import RandomSystems.SumOfPermutationsTight

/-!  ADVERSARIAL REVIEW PROBE (review-only; not part of the library).

Slice `empirical` — DEGENERATE REGIMES.  `⌈q⌉` truncates at exactly `q` (no off-by-one in
either direction), `sopIdeal` is definitionally the library URF, and `⌈0⌉` collapses both
systems to the same object — so `Δ = 0` there, matching `sopEps N 0 = 0` exactly.

Run with:  lake env lean review/slice-empirical.probe-degenerate.lean
-/


open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.SoPTight
open scoped RandomSystems.CR18

universe u
variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] [AddCommGroup G]

/-! ### `sopIdeal` IS the uniform random function -/
omit [AddCommGroup G] in
theorem sopIdeal_eq_URF : (sopIdeal (G := G)) = PFunPDS.URF := rfl

/-! ### `⌈q⌉` truncates at exactly `q`: the `(q+1)`-st answer is `⊥` -/

omit [Nonempty G] [AddCommGroup G] in
/-- With the filter at `1`, the **second** query already returns `⊥`. -/
theorem second_answer_bot (f : G → G) (x0 x1 : G) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.filterQueries 1 (PFunDDS.functionEvaluator f)))
      [x0, x1] (List.cons_ne_nil _ _) = none := by
  simp [PFunDDS.output, PFunDDS.fullyDefined, PFunDDS.keptPrefix, PFunDDS.filterQueries,
    PFunDDS.filterDom, PFunDDS.functionEvaluator, PFunDDS.dom]

omit [Nonempty G] [AddCommGroup G] in
/-- With the filter at `2`, the **second** query is still answered. -/
theorem second_answer_ok (f : G → G) (x0 x1 : G) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f)))
      [x0, x1] (List.cons_ne_nil _ _) = some (f x1) := by
  simp [PFunDDS.output, PFunDDS.fullyDefined, PFunDDS.keptPrefix, PFunDDS.filterQueries,
    PFunDDS.filterDom, PFunDDS.functionEvaluator, PFunDDS.dom]

omit [Nonempty G] [AddCommGroup G] in
/-- With the filter at `2`, the **third** query returns `⊥`. -/
theorem third_answer_bot (f : G → G) (x0 x1 x2 : G) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f)))
      [x0, x1, x2] (List.cons_ne_nil _ _) = none := by
  simp [PFunDDS.output, PFunDDS.fullyDefined, PFunDDS.keptPrefix, PFunDDS.filterQueries,
    PFunDDS.filterDom, PFunDDS.functionEvaluator, PFunDDS.dom]

omit [Nonempty G] [AddCommGroup G] in
/-- With the filter at `0`, even the **first** query returns `⊥` — `⌈0⌉` is total blindness. -/
theorem first_answer_bot_of_zero (f : G → G) (x0 : G) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.filterQueries 0 (PFunDDS.functionEvaluator f)))
      [x0] (List.cons_ne_nil _ _) = none := by
  simp [PFunDDS.output, PFunDDS.fullyDefined, PFunDDS.keptPrefix, PFunDDS.filterQueries,
    PFunDDS.filterDom, PFunDDS.functionEvaluator, PFunDDS.dom]

/-! ### `⌈0⌉` collapses both systems to the same object, so `Δ = 0` there -/
theorem filterQueries_zero_eq :
    (⌈0⌉ (sopReal (G := G))) = (⌈0⌉ (sopIdeal (G := G))) := by
  have hR : (⌈0⌉ (sopReal (G := G)))
      = Dist.fTransform
          (fun _ : Equiv.Perm G × Equiv.Perm G =>
            PFunDDS.filterQueries 0 (PFunDDS.functionEvaluator (0 : G → G)))
          (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) := by
    rw [PFunPDS.filterQueries, sopReal, Dist.fTransform_comp]
    refine congrArg (fun h => Dist.fTransform h _) (funext fun p => ?_)
    apply Subtype.ext; funext l
    apply Part.ext'
    · simp [PFunDDS.filterQueries, PFunDDS.filterDom, PFunDDS.functionEvaluator, PFunDDS.dom]
    · intro h1 h2
      exfalso
      have : l.length ≤ 0 ∧ l ≠ [] := ⟨h1.2, h1.1⟩
      simp_all
  have hI : (⌈0⌉ (sopIdeal (G := G)))
      = Dist.fTransform
          (fun _ : G → G => PFunDDS.filterQueries 0 (PFunDDS.functionEvaluator (0 : G → G)))
          (Dist.uniform (G → G)) := by
    rw [PFunPDS.filterQueries, sopIdeal, Dist.fTransform_comp]
    refine congrArg (fun h => Dist.fTransform h _) (funext fun g => ?_)
    apply Subtype.ext; funext l
    apply Part.ext'
    · simp [PFunDDS.filterQueries, PFunDDS.filterDom, PFunDDS.functionEvaluator, PFunDDS.dom]
    · intro h1 h2
      exfalso
      have : l.length ≤ 0 ∧ l ≠ [] := ⟨h1.2, h1.1⟩
      simp_all
  classical
  have key : ∀ (A : Type u) (_ : Fintype A) (_ : Nonempty A) (c : PFunDDS.DDS G G),
      Dist.fTransform (fun _ : A => c) (Dist.uniform A) = Finsupp.single c 1 := by
    intro A _ _ c
    ext s
    rw [Dist.fTransform_apply_eq_mass, Finsupp.single_apply]
    by_cases h : c = s
    · subst h
      rw [if_pos rfl, Dist.mass_congr _ (fun _ => (by simp : (c = c) ↔ True)),
        Dist.mass_true]
      exact_mod_cast Dist.weight_uniform (A := A)
    · rw [if_neg h, Dist.mass_congr _ (fun _ => (by simp [h] : (c = s) ↔ False))]
      simp [Dist.mass]
  rw [hR, hI, key _ inferInstance inferInstance _, key _ inferInstance inferInstance _]
