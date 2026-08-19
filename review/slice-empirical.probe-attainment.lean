import RandomSystems.SumOfPermutationsTight

/-!  ADVERSARIAL REVIEW PROBE (review-only; not part of the library).

Slice `empirical` — ATTAINMENT.  Every other probe in this review bounds `Δ` from ABOVE.
This one bounds it from BELOW, by exhibiting a concrete two-query distinguisher, computing
its verdict probability against `⌈2⌉sopReal` and `⌈2⌉sopIdeal` from the definitions, and
feeding it to `advantage_le_maxAdvantage`.  The values obtained — `1/2`, `1/6`, `1/12` at
`ZMod 2/3/4` — are EXACTLY the true maximal 2-query advantage `1/(N(N-1))` computed by the
independent enumeration in `review/slice-empirical.brute-force-adaptive.py`.

So the theorem's left-hand side is not a deflated or vacuous quantity: it is pinned to the
true advantage from both sides at these instances.

Run with:  lake env lean review/slice-empirical.probe-attainment.lean
-/


open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.SoPTight
open scoped RandomSystems.CR18

universe u
variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] [AddCommGroup G]

/-- Query `x0`, then `x1`, then say "ideal" iff the two answers differ. -/
def dsepFn (x0 x1 : G) : List (Option G) → G ⊕ Bool
  | [] => Sum.inl x0
  | [_] => Sum.inl x1
  | y1 :: y2 :: _ => Sum.inr (decide (y1 ≠ y2))

theorem dsep_stopFinal (x0 x1 : G) : PFunDDS.StopFinal (dsepFn x0 x1) := by
  intro h h' hpre b hb
  match h, hb with
  | y1 :: y2 :: t, hb =>
      obtain ⟨u, rfl⟩ := hpre
      simpa [dsepFn] using hb

def dsep (x0 x1 : G) : PFunDDS.DDD G G := ⟨dsepFn x0 x1, dsep_stopFinal x0 x1⟩

theorem transcript_two (x0 x1 : G) (f : G → G) :
    PFunDDS.transcript (PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f))
      (PFunDDS.ddToDDE (dsep x0 x1)) 2
      = [(x0, some (f x0)), (x1, some (f x1))] := by
  simp [PFunDDS.transcript, PFunDDS.transcriptOutputs, PFunDDS.transcriptInputs,
    PFunDDS.ddToDDE, dsep, dsepFn, PFunDDS.output, PFunDDS.fullyDefined,
    PFunDDS.keptPrefix, PFunDDS.filterQueries, PFunDDS.filterDom,
    PFunDDS.functionEvaluator, PFunDDS.dom]

theorem transcript_stall (x0 x1 : G) (f : G → G) (n : ℕ) :
    PFunDDS.transcript (PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f))
      (PFunDDS.ddToDDE (dsep x0 x1)) (n + 2)
      = [(x0, some (f x0)), (x1, some (f x1))] := by
  induction n with
  | zero => exact transcript_two x0 x1 f
  | succ m ih =>
      have hnone : PFunDDS.ddToDDE (dsep x0 x1) (PFunDDS.transcriptOutputs
          (PFunDDS.transcript (PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f))
            (PFunDDS.ddToDDE (dsep x0 x1)) (m + 2))) = none := by
        rw [ih]; simp [PFunDDS.transcriptOutputs, PFunDDS.ddToDDE, dsep, dsepFn]
      rw [show m + 1 + 2 = (m + 2) + 1 from rfl, PFunDDS.transcript]
      simp only [hnone]
      exact ih

/-- **The distinguisher's verdict is exactly "the two answers differ".** -/
theorem verdict_dsep_iff (x0 x1 : G) (f : G → G) :
    PFunDDS.verdict (dsep x0 x1) (PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator f))
      ↔ f x0 ≠ f x1 := by
  constructor
  · rintro ⟨n, hn⟩
    match n, hn with
    | 0, hn => simp [PFunDDS.transcript, PFunDDS.transcriptOutputs, dsep, dsepFn] at hn
    | 1, hn =>
        rw [show (1:ℕ) = 0 + 1 from rfl] at hn
        simp [PFunDDS.transcript, PFunDDS.transcriptOutputs, PFunDDS.transcriptInputs,
          PFunDDS.ddToDDE, dsep, dsepFn, PFunDDS.output, PFunDDS.fullyDefined,
          PFunDDS.keptPrefix, PFunDDS.filterQueries, PFunDDS.filterDom,
          PFunDDS.functionEvaluator, PFunDDS.dom] at hn
    | (m+2), hn =>
        rw [transcript_stall x0 x1 f m] at hn
        simpa [PFunDDS.transcriptOutputs, dsep, dsepFn] using hn
  · intro hf
    refine ⟨2, ?_⟩
    rw [transcript_two x0 x1 f]
    simpa [PFunDDS.transcriptOutputs, dsep, dsepFn] using hf

noncomputable def Dsep (x0 x1 : G) : RandomSystems.Dist (PFunDDS.DDD G G) :=
  Finsupp.single (dsep x0 x1) 1

theorem Dsep_isProbDist (x0 x1 : G) : (Dsep x0 x1).isProbDist := by
  show RandomSystems.Dist.weight (Finsupp.single (dsep x0 x1) (1 : NNReal)) = 1
  rw [RandomSystems.Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]

theorem verdictProb_Dsep (x0 x1 : G) (S : PFunPDS G G) :
    verdictProb (Dsep x0 x1) S = S.mass (PFunDDS.verdict (dsep x0 x1)) := by
  unfold verdictProb GamePerf.winProb Dsep Dist.mass
  rw [Finsupp.sum_single_index (by simp)]
  exact Finsupp.sum_congr fun s _ => by
    by_cases h : PFunDDS.verdict (dsep x0 x1) s <;> simp [h]

theorem filterQueries_sopReal :
    (⌈2⌉ (sopReal (G := G)))
      = Dist.fTransform
          (fun p : Equiv.Perm G × Equiv.Perm G =>
            PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator (sopFunction p)))
          (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) := by
  rw [PFunPDS.filterQueries, sopReal, Dist.fTransform_comp]
  rfl

theorem filterQueries_sopIdeal :
    (⌈2⌉ (sopIdeal (G := G)))
      = Dist.fTransform
          (fun g : G → G => PFunDDS.filterQueries 2 (PFunDDS.functionEvaluator g))
          (Dist.uniform (G → G)) := by
  rw [PFunPDS.filterQueries, sopIdeal, Dist.fTransform_comp]
  rfl

/-- The advantage of the two-query "answers differ" distinguisher, as a difference of
uniform counting masses over the actual carriers of `sopReal` and `sopIdeal`. -/
theorem advantage_dsep (x0 x1 : G) :
    advantage (Dsep x0 x1) (⌈2⌉ (sopReal (G := G))) (⌈2⌉ (sopIdeal (G := G)))
      = ((((Finset.univ.filter (fun g : G → G => g x0 ≠ g x1)).card : NNReal)
            / (Fintype.card (G → G) : NNReal) : NNReal) : ℝ)
        - ((((Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
              sopFunction p x0 ≠ sopFunction p x1)).card : NNReal)
            / (Fintype.card (Equiv.Perm G × Equiv.Perm G) : NNReal) : NNReal) : ℝ) := by
  classical
  unfold advantage
  rw [verdictProb_Dsep, verdictProb_Dsep, filterQueries_sopReal, filterQueries_sopIdeal,
    Dist.mass_fTransform, Dist.mass_fTransform,
    Dist.mass_congr _ (fun p => verdict_dsep_iff x0 x1 (sopFunction p)),
    Dist.mass_congr _ (fun g => verdict_dsep_iff x0 x1 g),
    Dist.uniform_mass_eq_card_filter, Dist.uniform_mass_eq_card_filter]

theorem le_maxAdvantage_dsep (x0 x1 : G) :
    advantage (Dsep x0 x1) (⌈2⌉ (sopReal (G := G))) (⌈2⌉ (sopIdeal (G := G)))
      ≤ Δ(⌈2⌉ (sopReal (G := G)), ⌈2⌉ (sopIdeal (G := G))) :=
  advantage_le_maxAdvantage _ _ _ (Dsep_isProbDist x0 x1)

/-! ## Instantiations: the true `q = 2` advantage is `1/(N(N-1))` -/

-- N = 2
theorem adv_zmod2 :
    advantage (Dsep (0 : ZMod 2) 1) (⌈2⌉ (sopReal (G := ZMod 2)))
      (⌈2⌉ (sopIdeal (G := ZMod 2))) = 1/2 := by
  rw [advantage_dsep]
  rw [show (Finset.univ.filter (fun g : ZMod 2 → ZMod 2 => g 0 ≠ g 1)).card = 2 from by decide,
     show (Finset.univ.filter (fun p : Equiv.Perm (ZMod 2) × Equiv.Perm (ZMod 2) =>
        sopFunction p 0 ≠ sopFunction p 1)).card = 0 from by decide,
     show Fintype.card (ZMod 2 → ZMod 2) = 4 from by decide,
     show Fintype.card (Equiv.Perm (ZMod 2) × Equiv.Perm (ZMod 2)) = 4 from by decide]
  norm_num

theorem lb_zmod2 : (1:ℝ)/2 ≤ Δ(⌈2⌉ (sopReal (G := ZMod 2)), ⌈2⌉ (sopIdeal (G := ZMod 2))) := by
  have := le_maxAdvantage_dsep (0 : ZMod 2) 1
  rwa [adv_zmod2] at this

-- N = 3
theorem adv_zmod3 :
    advantage (Dsep (0 : ZMod 3) 1) (⌈2⌉ (sopReal (G := ZMod 3)))
      (⌈2⌉ (sopIdeal (G := ZMod 3))) = 1/6 := by
  rw [advantage_dsep]
  rw [show (Finset.univ.filter (fun g : ZMod 3 → ZMod 3 => g 0 ≠ g 1)).card = 18 from by decide,
     show (Finset.univ.filter (fun p : Equiv.Perm (ZMod 3) × Equiv.Perm (ZMod 3) =>
        sopFunction p 0 ≠ sopFunction p 1)).card = 18 from by decide,
     show Fintype.card (ZMod 3 → ZMod 3) = 27 from by decide,
     show Fintype.card (Equiv.Perm (ZMod 3) × Equiv.Perm (ZMod 3)) = 36 from by decide]
  norm_num

theorem lb_zmod3 : (1:ℝ)/6 ≤ Δ(⌈2⌉ (sopReal (G := ZMod 3)), ⌈2⌉ (sopIdeal (G := ZMod 3))) := by
  have := le_maxAdvantage_dsep (0 : ZMod 3) 1
  rwa [adv_zmod3] at this

-- and the claimed bound at N = 3, q = 2 is 1/4
example : sopEps 3 2 = 1/4 := by norm_num [sopEps, Finset.sum_range_succ]

#print axioms lb_zmod2
#print axioms lb_zmod3

-- N = 4  (576 permutation pairs, 256 functions)
set_option maxRecDepth 100000 in
theorem adv_zmod4 :
    advantage (Dsep (0 : ZMod 4) 1) (⌈2⌉ (sopReal (G := ZMod 4)))
      (⌈2⌉ (sopIdeal (G := ZMod 4))) = 1/12 := by
  rw [advantage_dsep]
  rw [show (Finset.univ.filter (fun g : ZMod 4 → ZMod 4 => g 0 ≠ g 1)).card = 192 from by decide,
     show (Finset.univ.filter (fun p : Equiv.Perm (ZMod 4) × Equiv.Perm (ZMod 4) =>
        sopFunction p 0 ≠ sopFunction p 1)).card = 384 from by decide,
     show Fintype.card (ZMod 4 → ZMod 4) = 256 from by decide,
     show Fintype.card (Equiv.Perm (ZMod 4) × Equiv.Perm (ZMod 4)) = 576 from by decide]
  norm_num

theorem lb_zmod4 : (1:ℝ)/12 ≤ Δ(⌈2⌉ (sopReal (G := ZMod 4)), ⌈2⌉ (sopIdeal (G := ZMod 4))) := by
  have := le_maxAdvantage_dsep (0 : ZMod 4) 1
  rwa [adv_zmod4] at this

/-! ## What the *statement* alone yields at a concrete instance -/

/-- Everything the ∃-statement gives at `ZMod 3`, `q = 2`: `Δ < 4/3`.  The concrete
`sopEps 3 2 = 1/4` is **not** extractable — `ε` is existentially quantified and the only
constraint on it is the birthday clause. -/
theorem statement_content_zmod3 :
    Δ(⌈2⌉ (sopReal (G := ZMod 3)), ⌈2⌉ (sopIdeal (G := ZMod 3))) < 4/3 := by
  obtain ⟨e, hbound, himp⟩ := sop_randomness_expander_tight.{0}
  have h1 := hbound (ZMod 3) 2
  have h2 := himp 3 2 (by norm_num) (by norm_num)
  have hcard : Fintype.card (ZMod 3) = 3 := by decide
  rw [hcard] at h1
  norm_num at h2
  linarith

/-- The two are compatible: `1/6 ≤ Δ ≤ 1/4` at `ZMod 3`, `q = 2` — but the upper half must be
taken from the *proof* (`sopEps`), not from the statement. -/
theorem sandwich_zmod3 :
    (1:ℝ)/6 ≤ Δ(⌈2⌉ (sopReal (G := ZMod 3)), ⌈2⌉ (sopIdeal (G := ZMod 3))) :=
  lb_zmod3

/-! ## Knife-edge: at `q = 1` the bound is `0`, so the theorem asserts PERFECT 1-query security -/

theorem maxAdvantage_nonneg (S T : PFunPDS G G) : 0 ≤ Δ(S, T) := by
  have h := advantage_le_maxAdvantage (rejectDistinguisher G G) S T
    (rejectDistinguisher_isProbDist G G)
  have hz : advantage (rejectDistinguisher G G) S T = 0 := by
    unfold advantage verdictProb GamePerf.winProb rejectDistinguisher
    rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    have hnv : ∀ s : PFunDDS.DDS G G, ¬ PFunDDS.verdict (PFunDDS.rejectDDD G G) s := by
      rintro s ⟨n, hn⟩
      simp [PFunDDS.rejectDDD] at hn
    simp [hnv]
  linarith [h, hz.symm.le, hz.le]

/-- `sopEps N 1 = 0`, and `Δ ≥ 0`, so the theorem's `q = 1` instance says exactly
`Δ = 0`: one query gives the distinguisher nothing.  (Brute force confirms the truth is `0`.) -/
theorem q_one_is_exact (N : ℕ) : sopEps N 1 = 0 := by
  norm_num [sopEps, Finset.sum_range_succ]

theorem q_zero_is_exact (N : ℕ) : sopEps N 0 = 0 := by simp [sopEps]

/-- The `N = 1` division-by-zero quirk: `sopEps 1 2 = 0` (the `k = 1` term is `1/0 = 0`),
but `sopEps 1 3 = 1` (the `k = 2` term is `4/1`). -/
theorem N_one_quirk : sopEps 1 2 = 0 ∧ sopEps 1 3 = 1 := by
  constructor <;> norm_num [sopEps, Finset.sum_range_succ]
