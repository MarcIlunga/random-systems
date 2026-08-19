import RandomSystems.SumOfPermutationsTight

/-!  ADVERSARIAL REVIEW PROBE (review-only; not part of the library).

Positive semantic checks for the `sop-statement-and-semantics` slice:
  (1) `sopIdeal` *is* the library's URF, definitionally;
  (2) it is a random function in the sense of CR18 Def 3.15;
  (3) `sopReal` is the pushforward of the *product* uniform law, and
  (3b) the uniform law on the product really is the independent product of two uniforms;
  (4) `⌈q⌉` is `PFunPDS.filterQueries`, the filtered domain is exactly "nonempty, ≤ q",
      the kept prefix saturates at exactly `q`, queries 1..q get the honest answer and
      query q+1 and beyond get ⊥ in the completion the transcript actually uses;
  (5) the explicit bound `Δ ≤ sopEps (card H) q` that the `∃ ε` packaging hides;
  (6) non-vacuity: the ∀-H binder is instantiable at a concrete finite abelian group.

Run with:  lake env lean review/slice-sop-statement-and-semantics.probe-semantics.lean
-/

noncomputable section
namespace ReviewProbe2
open RandomSystems (Dist)
open RandomSystems.CR18
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv
universe u

-- (1) sopIdeal really *is* the library's URF (Def 3.15 uniform random function).
example {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] :
    SoPTight.sopIdeal (G := G) = PFunPDS.URF := rfl

-- (2) sopIdeal is a random function in the sense of CR18 Def 3.15.
example {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] :
    PFunPDS.IsRandomFunction (SoPTight.sopIdeal (G := G)) :=
  PFunPDS.ofFunDist_isRandomFunction _

-- (3) sopReal is the pushforward of the *product* uniform law = independent uniform perms.
example {G : Type u} [Fintype G] [DecidableEq G] [AddCommGroup G] :
    SoPTight.sopReal (G := G)
      = PFunPDS.ofFunDist (Dist.fTransform SoPTight.sopFunction
          (Dist.uniform (Equiv.Perm G × Equiv.Perm G))) := by
  rw [PFunPDS.ofFunDist, Dist.fTransform_comp]; rfl

-- (3b) the uniform law on the product really is the independent product of two uniforms.
example {G : Type u} [Fintype G] [DecidableEq G] :
    Dist.uniform (Equiv.Perm G × Equiv.Perm G)
      = Dist.prod (Dist.uniform (Equiv.Perm G)) (Dist.uniform (Equiv.Perm G)) := by
  ext p
  rw [Dist.uniform_apply, Dist.prod_apply, Dist.uniform_apply, Dist.uniform_apply,
    Fintype.card_prod]
  push_cast
  rw [div_mul_div_comm, one_mul]

-- (4) ⌈q⌉ is PFunPDS.filterQueries.
example (q : ℕ) {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] :
    (⌈q⌉ (SoPTight.sopIdeal (G := G))) = PFunPDS.filterQueries q SoPTight.sopIdeal := rfl

section Cap
variable {X Y : Type}

-- (4a) the filtered domain is exactly "nonempty and at most q queries" — `≤ q`, not `< q`
example (q : ℕ) (f : X → Y) (l : List X) :
    l ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
      ↔ (l ≠ [] ∧ l.length ≤ q) := by
  rw [PFunDDS.mem_dom_filterQueries, PFunDDS.dom_functionEvaluator]; exact Iff.rfl

-- (4b) inside the budget the answer is the honest one
example (q : ℕ) (f : X → Y) (l : List X) (x : X)
    (h : l ++ [x] ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) :
    PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) (l ++ [x]) h = f x := by
  rw [PFunDDS.output_filterQueries]; exact PFunDDS.functionEvaluator_output f l x h.1

-- (4c) keptPrefix of the filtered evaluator keeps exactly the first `min q |m|` queries
theorem kept_len (q : ℕ) (f : X → Y) (m : List X) :
    (PFunDDS.keptPrefix (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) m).length
      = min q m.length := by
  classical
  unfold PFunDDS.keptPrefix
  induction m using List.reverseRecOn with
  | nil => simp
  | append_singleton m x ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      split
      · rename_i hd
        have h2 := hd.2
        simp only [List.length_append, List.length_cons, List.length_nil, ih] at h2 ⊢
        omega
      · rename_i hd
        have : ¬ ((_ : List X) ++ [x] ≠ [] ∧
            (List.foldl (fun acc x => if acc ++ [x] ∈
              PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
              then acc ++ [x] else acc) [] m ++ [x]).length ≤ q) := hd
        simp only [List.length_append, List.length_cons, List.length_nil, ih, ne_eq,
          List.append_eq_nil_iff, not_and, not_le] at this ⊢
        have := this (by simp)
        omega

-- (4d) the (q+1)-st and every later query returns ⊥ in the completion the transcript uses …
example (q : ℕ) (f : X → Y) (l : List X) (hlen : q < l.length)
    (h : l ∈ PFunDDS.dom (PFunDDS.fullyDefined
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)))) :
    PFunDDS.output (PFunDDS.fullyDefined
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) l h = none := by
  classical
  rw [PFunDDS.output_fullyDefined]
  refine dif_neg fun hmem => ?_
  have h2 := hmem.2
  have h1 := kept_len q f l.dropLast
  simp only [List.length_append, List.length_cons, List.length_nil, h1,
    List.length_dropLast] at h2
  omega

-- (4e) … and every query up to the q-th returns the honest answer.
example (q : ℕ) (f : X → Y) (l : List X) (hne : l ≠ []) (hlen : l.length ≤ q)
    (h : l ∈ PFunDDS.dom (PFunDDS.fullyDefined
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)))) :
    PFunDDS.output (PFunDDS.fullyDefined
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) l h
      = some (f (l.getLast hne)) := by
  classical
  rw [PFunDDS.output_fullyDefined]
  have h1 := kept_len q f l.dropLast
  have hdl : l.dropLast.length = l.length - 1 := List.length_dropLast
  have hmem : (PFunDDS.keptPrefix (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
      l.dropLast ++ [l.getLast hne]) ∈
      PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := by
    refine ⟨List.append_ne_nil_of_right_ne_nil _ (by simp), ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil, h1, hdl]
    have : 0 < l.length := List.length_pos_iff.mpr hne
    omega
  rw [dif_pos hmem, PFunDDS.output_filterQueries, PFunDDS.functionEvaluator_output]

end Cap

-- (5) The content that is NOT exposed by the existential: the explicit bound.
theorem explicit_bound {H : Type u} [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H]
    (q : ℕ) :
    Δ(⌈q⌉ (SoPTight.sopReal (G := H)), ⌈q⌉ (SoPTight.sopIdeal (G := H)))
      ≤ SoPTight.sopEps (Fintype.card H) q := by
  calc Δ(⌈q⌉ (SoPTight.sopReal (G := H)), ⌈q⌉ (SoPTight.sopIdeal (G := H)))
      = Δ(⌈q⌉ PFunPDS.ignoreMBO (SoPTight.sopTightGame (G := H)),
          ⌈q⌉ (SoPTight.sopIdeal (G := H))) := by rw [SoPTight.sopTightGame_ignoreMBO]
    _ ≤ ((Real.toNNReal (SoPTight.sopEps (Fintype.card H) q) : NNReal) : ℝ) := by
        refine maxAdvantage_filterQueries_seededConditionCGame_le
          (Dist.uniform (Equiv.Perm H × Equiv.Perm H)) SoPTight.sopFunction SoPTight.sopTightBad
          (fun p => SoPTight.sopTightBad_monotone p) q SoPTight.sopIdeal _
          SoPTight.sopTight_condEquiv Dist.uniform_isProbDist SoPTight.sopIdeal_isProbDist
          SoPTight.sopIdeal_totalOnNonempty (fun w _ => ?_)
        exact (Real.le_toNNReal_iff_coe_le (SoPTight.sopEps_nonneg _ _)).mpr
          (SoPTight.mass_sopTightBad_le (blindQueryList w q) q (blindQueryList_length_le w q))
    _ = SoPTight.sopEps (Fintype.card H) q :=
        Real.coe_toNNReal _ (SoPTight.sopEps_nonneg _ _)

-- (6) non-vacuity: the ∀-H binder is instantiable at a concrete finite abelian group.
example (q : ℕ) :
    Δ(⌈q⌉ (SoPTight.sopReal (G := ZMod 5)), ⌈q⌉ (SoPTight.sopIdeal (G := ZMod 5)))
      ≤ SoPTight.sopEps 5 q := by
  have := explicit_bound (H := ZMod 5) q
  simpa using this

-- (7) sopEps really is below the birthday half-bound in the interesting window.
example : SoPTight.sopEps 100 10 < (1/2 : ℝ) * 10 ^ 2 / 100 := by
  unfold SoPTight.sopEps
  refine lt_of_le_of_lt (min_le_right _ _) ?_
  norm_num [Finset.sum_range_succ]

#print axioms explicit_bound
#print axioms RandomSystems.CR18.SoPTight.sop_randomness_expander_tight
#print axioms RandomSystems.CR18.SoPTight.sopTightGame_ignoreMBO
#print axioms RandomSystems.CR18.seededConditionCGame_ignoreMBO

end ReviewProbe2
