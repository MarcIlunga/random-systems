/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TranscriptBranchDistance

/-!
# The hybrid bound: per-step answer distance sums to transcript distance

The standard "one step at a time" bound, in the thesis's own successor
calculus.  `transcriptDist_successor` (LanMau20 §4.2) splits a length-`n+1`
transcript law over its first answer, and
`delta_sum_cons_pushforwards_eq_sum_of_deltas_of_finite_answers`
(Lemma 2.5) makes `δ` additive across those branches:

  `δ(tr(S,e) (n+1), tr(T,e) (n+1)) = ∑_y δ(tr(S↑x↓y, e↑y) n, tr(T↑x↓y, e↑y) n)`.

So a relation `Good` that is *preserved by successors* and whose members have
their **first-answer laws** within `ε n · |S|` gives, by induction on the
remaining query budget,

  `δ(tr(S,e) n, tr(T,e) n) ≤ (∑_{i<n} ε i) · |S| + (|S| − |T|)`.

The weight defect `|S| − |T|` has to be carried: a successor transformation
splits the weight along the first answer, and the two sides' shares differ by
exactly the first-answer distance, so no relation between two systems whose
answer laws merely *approximate* each other can keep the weights equal.  At
the top it vanishes for equal-weight pairs.

`Adv` is a supremum of exactly the left-hand side over environments and
prefix lengths (thesis Def 2.26), so this bounds the optimal distinguishing
advantage — `adv_le_of_stepwise` — and hence, through `adv_eq_maxAdvantage_swap`,
the maximal distinguishing advantage `Δ(·,·)`.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-! ## The first-answer law -/

/-- The law of a system's **first answer** to `x`: the pushforward of `S`
along `s ↦ s⊥(x)`.  Its value at `y` is the weight of `S↑x↓y`
(`answerLaw_apply`), so it is the distribution the successor split of
`transcriptDist_successor` is indexed by. -/
noncomputable def answerLaw (S : PFunPDS X Y) (x : X) : Dist (Option Y) :=
  Dist.fTransform
    (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp)) S

theorem answerLaw_apply (S : PFunPDS X Y) (x : X) (y : Option Y) :
    answerLaw S x y = (successorTransform S x y).weight := by
  rw [weight_successorTransform, answerLaw, Dist.fTransform_apply_eq_mass]

theorem weight_answerLaw (S : PFunPDS X Y) (x : X) :
    (answerLaw S x).weight = S.weight :=
  Dist.weight_fTransform _ _

/-- Outside the realized answers the successor transformation is the zero
distribution — the branches the successor split may be padded with are
empty. -/
theorem successorTransform_eq_zero (S : PFunPDS X Y) (x : X) {y : Option Y}
    (hy : ∀ s ∈ S.support,
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) ≠ y) :
    successorTransform S x y = 0 := by
  classical
  -- The filtered law is pointwise zero, so no non-negativity is needed: off
  -- the support `S` already vanishes, and on it the filter rejects.
  unfold successorTransform
  rw [show (S.filter fun s =>
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y) = 0 from by
    refine Finsupp.ext fun s => ?_
    rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hs : s ∈ S.support
    · exact if_neg (hy s hs)
    · rw [Finsupp.notMem_support_iff.mp hs, ite_self]]
  simp [Dist.fTransform]

/-! ## Two degenerate transcript laws -/

/-- A stalled-at-the-start environment never fires, so every transcript
prefix is empty. -/
theorem transcript_eq_nil_of_stall {s : PFunDDS.DDS X Y} {e : PFunDDS.DDE X Y}
    (he : e [] = none) (n : ℕ) : PFunDDS.transcript s e n = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstall : e (PFunDDS.transcriptOutputs (PFunDDS.transcript s e n))
          = none := by
        rw [ih]
        exact he
      rw [transcript_succ_stall hstall, ih]

/-- Two point masses at `[]` are `δ`-apart by exactly their weight gap.

On the signed carrier the gap is spelled `max (|S| − |T|) 0` — which is what
the `NNReal` truncated subtraction denoted — and the right-hand law has to be
non-negative, since `δ` reads only `μ`'s support. -/
theorem delta_const_nil_fTransform (S T : PFunPDS X Y) (hT : T.NonNeg) :
    δ (Dist.fTransform (fun _ => ([] : List (X × Option Y))) S)
        (Dist.fTransform (fun _ => ([] : List (X × Option Y))) T)
      = max (S.weight - T.weight) 0 := by
  classical
  rw [δ_eq_sum_of_support_subset (hT.fTransform _)
    (show (Dist.fTransform (fun _ => ([] : List (X × Option Y))) S).support
        ⊆ ({[]} : Finset (List (X × Option Y))) from by
      intro a ha
      obtain ⟨-, -, hs⟩ := Dist.mem_support_fTransform _ _ ha
      simp [← hs])]
  rw [Finset.sum_singleton, Dist.fTransform_apply_eq_mass,
    Dist.fTransform_apply_eq_mass]
  congr 2 <;> exact (Dist.mass_congr _ fun _ => (iff_true _).mpr rfl).trans
    (Dist.mass_true _)

/-- The transcript law of a system whose environment never fires. -/
theorem transcriptDist_of_stall (S : PFunPDS X Y) {e : PFunDDS.DDE X Y}
    (he : e [] = none) (n : ℕ) :
    transcriptDist S e n
      = Dist.fTransform (fun _ => ([] : List (X × Option Y))) S :=
  congrArg (fun f => Dist.fTransform f S)
    (funext fun _ => transcript_eq_nil_of_stall he n)

theorem transcriptDist_zero (S : PFunPDS X Y) (e : PFunDDS.DDE X Y) :
    transcriptDist S e 0
      = Dist.fTransform (fun _ => ([] : List (X × Option Y))) S := rfl

/-! ## The successor split at a common answer set -/

open Classical in
/-- `transcriptDist_successor` with the branch index enlarged to any finset
containing the realized answers: the padding branches are empty. -/
theorem transcriptDist_successor_of_subset (S : PFunPDS X Y)
    (e : PFunDDS.DDE X Y) {x : X} (he : e [] = some x) (n : ℕ)
    {ys : Finset (Option Y)}
    (hys : S.support.image (fun s =>
        PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp)) ⊆ ys) :
    transcriptDist S e (n + 1)
      = ∑ y ∈ ys, Dist.fTransform (fun t => (x, y) :: t)
          (transcriptDist (successorTransform S x y)
            (PFunDDS.DDE.successor e y) n) := by
  rw [transcriptDist_successor S e he n]
  refine Finset.sum_subset hys fun y _ hy => ?_
  have hzero : successorTransform S x y = 0 :=
    successorTransform_eq_zero S x fun s hs hout =>
      hy (Finset.mem_image.mpr ⟨s, hs, hout⟩)
  rw [hzero]
  show Dist.fTransform _ (Dist.fTransform _ (0 : PFunPDS X Y)) = 0
  simp [Dist.fTransform]

/-! ## The hybrid -/

open Classical in
/-- **The hybrid bound.**  A relation `Good` closed under successor
transformations, whose members' first-answer laws are within `ε n · |S|`,
bounds every transcript distance by the partial sum of the `ε`'s plus the
weight defect.

`Good d S T` is read "`S` and `T` are partners at **depth** `d`", i.e. after
`d` queries have already been answered; `ε d` is the deviation the caller
allows at the step taken from that depth.  Depth rather than remaining budget
is the right index: the deviation of a lazily-sampled system typically grows
with the number of answers already fixed, and the remaining budget carries no
such information.

On the signed carrier the weight defect is `max (|S| − |T|) 0` — the `NNReal`
truncated subtraction spelled out — and both laws must be non-negative.  That
is not bookkeeping: with `|S| < |T|` an untruncated defect would claim
`δ ≤ (∑ ε)·|S| + (|S| − |T|)`, which the length-`0` transcript already
refutes.  `Dist.NonNeg` is the whole requirement; no weight is normalized, and
it is the invariant the induction can carry, since `successorTransform`
preserves it while `0 ≤ |·|` alone does not. -/
theorem delta_transcriptDist_le_of_stepwise
    (Good : ℕ → PFunPDS X Y → PFunPDS X Y → Prop) (ε : ℕ → NNReal)
    (hsucc : ∀ (d : ℕ) (S T : PFunPDS X Y), Good d S T →
      ∀ (x : X) (y : Option Y),
        Good (d + 1) (successorTransform S x y) (successorTransform T x y))
    (hstep : ∀ (d : ℕ) (S T : PFunPDS X Y), Good d S T →
      S.NonNeg → T.NonNeg → ∀ x : X,
      δ (answerLaw S x) (answerLaw T x)
        ≤ ε d * S.weight + max (S.weight - T.weight) 0) :
    ∀ (n d : ℕ) (S T : PFunPDS X Y), Good d S T → S.NonNeg → T.NonNeg →
      ∀ e : PFunDDS.DDE X Y,
      δ (transcriptDist S e n) (transcriptDist T e n)
        ≤ (∑ i ∈ Finset.Ico d (d + n), ε i) * S.weight
            + max (S.weight - T.weight) 0 := by
  have hsuccNonNeg : ∀ {A : PFunPDS X Y}, A.NonNeg → ∀ (x : X) (y : Option Y),
      (successorTransform A x y).NonNeg := by
    intro A hA x y
    unfold successorTransform
    refine Dist.NonNeg.fTransform (fun s => ?_) _
    rw [Finsupp.filter_apply]
    split
    · exact hA s
    · exact le_rfl
  intro n
  induction n with
  | zero =>
      intro d S T _ _ hT e
      rw [transcriptDist_zero, transcriptDist_zero,
        delta_const_nil_fTransform S T hT]
      simp
  | succ n ih =>
      intro d S T good hS hT e
      rcases hfire : e ([] : List (Option Y)) with _ | x
      · rw [transcriptDist_of_stall S hfire, transcriptDist_of_stall T hfire,
          delta_const_nil_fTransform S T hT]
        exact le_add_of_nonneg_left
          (mul_nonneg (NNReal.coe_nonneg _) hS.weight_nonneg)
      -- the common branch index: every answer either side can give
      set outS : PFunDDS.DDS X Y → Option Y := fun s =>
        PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp) with houtS
      set ys : Finset (Option Y) :=
        S.support.image outS ∪ T.support.image outS with hys
      rw [transcriptDist_successor_of_subset S e hfire n
          (Finset.subset_union_left (s₂ := T.support.image outS)),
        transcriptDist_successor_of_subset T e hfire n
          (Finset.subset_union_right (s₁ := S.support.image outS)),
        delta_sum_cons_pushforwards_eq_sum_of_deltas_of_finite_answers _ _ _ _
          (fun y _ => transcriptDist_nonNeg (hsuccNonNeg hT x y) _ _)]
      -- each branch by the induction hypothesis
      have hbranch : ∀ y ∈ ys,
          δ (transcriptDist (successorTransform S x y)
              (PFunDDS.DDE.successor e y) n)
            (transcriptDist (successorTransform T x y)
              (PFunDDS.DDE.successor e y) n)
          ≤ (∑ i ∈ Finset.Ico (d + 1) (d + 1 + n), ε i)
                * (successorTransform S x y).weight
              + max ((successorTransform S x y).weight
                  - (successorTransform T x y).weight) 0 := fun y _ =>
        ih _ _ _ (hsucc d S T good x y) (hsuccNonNeg hS x y)
          (hsuccNonNeg hT x y) _
      refine le_trans (Finset.sum_le_sum hbranch) ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      -- the branch weights sum to the system weight
      have hwS : ∑ y ∈ ys, (successorTransform S x y).weight = S.weight := by
        have : ∑ y ∈ ys, (answerLaw S x) y = (answerLaw S x).weight := by
          rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
          exact (Finset.sum_subset
            (fun y hy => Finset.mem_union_left _
              (by
                obtain ⟨s, hs, hsy⟩ := Dist.mem_support_fTransform _ _ hy
                exact Finset.mem_image.mpr ⟨s, hs, hsy⟩))
            fun y _ hy => Finsupp.notMem_support_iff.mp hy).symm
        simpa [answerLaw_apply, weight_answerLaw] using this
      -- the branch weight gaps sum to the first-answer distance
      have hgap : ∑ y ∈ ys, max ((successorTransform S x y).weight
          - (successorTransform T x y).weight) 0
          = δ (answerLaw S x) (answerLaw T x) := by
        rw [δ_eq_sum_of_support_subset
          (show (answerLaw T x).NonNeg from hT.fTransform _)
          (show (answerLaw S x).support ⊆ ys from fun y hy =>
            Finset.mem_union_left _
              (by
                obtain ⟨s, hs, hsy⟩ := Dist.mem_support_fTransform _ _ hy
                exact Finset.mem_image.mpr ⟨s, hs, hsy⟩))]
        exact Finset.sum_congr rfl fun y _ => by
          rw [answerLaw_apply, answerLaw_apply]
      have hsplit : ((∑ i ∈ Finset.Ico d (d + (n + 1)), ε i : NNReal) : ℝ)
          = (ε d : ℝ) + ((∑ i ∈ Finset.Ico (d + 1) (d + 1 + n), ε i : NNReal) : ℝ) := by
        rw [show d + (n + 1) = d + 1 + n from by omega,
          Finset.sum_eq_sum_Ico_succ_bot (show d < d + 1 + n by omega) _]
        push_cast
        ring
      rw [hwS, hgap, hsplit, add_mul]
      have hstepx := hstep d S T good hS hT x
      calc ((∑ i ∈ Finset.Ico (d + 1) (d + 1 + n), ε i : NNReal) : ℝ) * S.weight
              + δ (answerLaw S x) (answerLaw T x)
          ≤ ((∑ i ∈ Finset.Ico (d + 1) (d + 1 + n), ε i : NNReal) : ℝ) * S.weight
              + ((ε d : ℝ) * S.weight + max (S.weight - T.weight) 0) :=
            add_le_add le_rfl hstepx
        _ = (ε d : ℝ) * S.weight
              + ((∑ i ∈ Finset.Ico (d + 1) (d + 1 + n), ε i : NNReal) : ℝ) * S.weight
              + max (S.weight - T.weight) 0 := by ring

/-- **The hybrid bound on the maximal distinguishing advantage.**  `Δ(S, T)`
is `Adv T S` (thesis Def 2.26's remark, `adv_eq_maxAdvantage_swap`), a
supremum over environments and prefix lengths of exactly the transcript
distance `delta_transcriptDist_le_of_stepwise` bounds — so a per-step answer
bound on the pair `(T, S)` at depth `0` bounds the advantage.

Note the argument order: the distinguisher's signed advantage `Δ(S, T)` is
the excess of `T`'s transcript law over `S`'s, so the *first* argument of the
`Good` relation is the system being bounded from above. -/
theorem maxAdvantage_le_of_stepwise (S T : PFunPDS X Y)
    (Good : ℕ → PFunPDS X Y → PFunPDS X Y → Prop) (ε : ℕ → NNReal)
    (hsucc : ∀ (d : ℕ) (A B : PFunPDS X Y), Good d A B →
      ∀ (x : X) (y : Option Y),
        Good (d + 1) (successorTransform A x y) (successorTransform B x y))
    (hstep : ∀ (d : ℕ) (A B : PFunPDS X Y), Good d A B →
      A.NonNeg → B.NonNeg → ∀ x : X,
      δ (answerLaw A x) (answerLaw B x)
        ≤ ε d * A.weight + max (A.weight - B.weight) 0)
    (hgood : Good 0 T S) (hS : S.NonNeg) (hT : T.NonNeg)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ n : ℕ,
      ((∑ i ∈ Finset.range n, ε i : NNReal) : ℝ) * T.weight
        + max (T.weight - S.weight) 0 ≤ c) :
    Δ(S, T) ≤ c := by
  rw [← adv_eq_maxAdvantage_swap hT hS]
  unfold Adv
  refine Real.sSup_le ?_ hc0
  rintro a ⟨e, n, rfl⟩
  refine le_trans ?_ (hc n)
  have := delta_transcriptDist_le_of_stepwise Good ε hsucc hstep n 0 T S hgood
    hT hS e
  rw [Nat.zero_add, Finset.range_eq_Ico.symm] at this
  exact_mod_cast this

/-! ## Lazily sampled systems, and their successor calculus

The hybrid's hypotheses are about `successorTransform` and `answerLaw`, which
are transformations of the *distribution over deterministic systems*.  Every
system in this development that a hybrid is applied to is instead presented as
a **seeded history evaluator**: a seed `ω` drawn from a fixed law, and a
deterministic answer function `F ω` of the past queries and the current one.

For those the successor calculus collapses to two elementary operations on the
seed law — **shift** the answer function past the new query, and **condition**
the seed on having answered it — which is what makes the hybrid's hypotheses
computable.  It is the lazy-sampling view, and nothing here is specific to any
one construction. -/

/-- The deterministic system a seed determines: answer the last query of the
history by `F` applied to the earlier queries. -/
def seededDDS (F : List X → X → Y) : PFunDDS.DDS X Y :=
  PFunDDS.historyEvaluator fun l ne => F l.dropLast (l.getLast ne)

/-- `F` after the query `x` has been asked. -/
def shiftAnswers (x : X) (F : List X → X → Y) : List X → X → Y :=
  fun us u => F (x :: us) u

/-- A **lazily sampled system**: the law of `seededDDS (F ω)` over the seed. -/
noncomputable def seededLaw {Ω : Type*} (F : Ω → List X → X → Y) (μ : Dist Ω) :
    PFunPDS X Y :=
  Dist.fTransform (fun ω => seededDDS (F ω)) μ

theorem mem_dom_seededDDS (F : List X → X → Y) {l : List X} (hl : l ≠ []) :
    l ∈ PFunDDS.dom (seededDDS F) := by
  show l ∈ PFunDDS.dom (PFunDDS.historyEvaluator _)
  rw [PFunDDS.dom_historyEvaluator]
  exact hl

/-- The `⊥`-completion of a total history evaluator reads off its own
evaluation — the fact `EmulateRealization` keeps privately for its probes,
needed here for every lazily sampled system. -/
theorem output_fullyDefined_historyEvaluator
    {g : (l : List X) → l ≠ [] → Y} {l : List X} (hne : l ≠ [])
    (h : l ∈ PFunDDS.dom (PFunDDS.fullyDefined (PFunDDS.historyEvaluator g))) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.historyEvaluator g)) l h
      = some (g l hne) := by
  obtain ⟨l', x, rfl⟩ : ∃ l' x, l = l' ++ [x] :=
    ⟨l.dropLast, l.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hl' : l' ∈ PFunDDS.dom (PFunDDS.historyEvaluator g) ∨ l' = [] := by
    rcases eq_or_ne l' [] with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (by rw [PFunDDS.dom_historyEvaluator]; exact h0)
  have hnext : l' ++ [x] ∈ PFunDDS.dom (PFunDDS.historyEvaluator g) := by
    rw [PFunDDS.dom_historyEvaluator]
    simp
  rw [PFunDDS.output_fullyDefined_append_of_mem _ l' x hl' hnext,
    PFunDDS.historyEvaluator_output]

theorem output_seededDDS (F : List X → X → Y) (x : X) :
    PFunDDS.output (PFunDDS.fullyDefined (seededDDS F)) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some (F [] x) :=
  output_fullyDefined_historyEvaluator (g := fun l ne => F l.dropLast (l.getLast ne))
    (by simp) _

/-- The successor of a seeded system is the seeded system of the shifted
answer function: `s↑x` reads the same seed one query later. -/
theorem successor_seededDDS (F : List X → X → Y) (x : X) :
    PFunDDS.DDS.successor (seededDDS F) x = seededDDS (shiftAnswers x F) := by
  have hx : [x] ∈ PFunDDS.dom (seededDDS F) := mem_dom_seededDDS F (by simp)
  refine Subtype.ext (funext fun l => ?_)
  by_cases hl : l = []
  · subst hl
    have hL : (PFunDDS.DDS.successor (seededDDS F) x).1 [] = Part.none := by
      unfold PFunDDS.DDS.successor
      rw [if_pos hx]
      simp
    have hR : (seededDDS (shiftAnswers x F)).1 [] = Part.none :=
      Part.eq_none_iff'.mpr (by show ¬ (([] : List X) ≠ []); simp)
    rw [hL, hR]
  · rw [successor_apply_of_mem hx hl]
    refine Part.ext' (by
      show (x :: l ≠ []) ↔ (l ≠ [])
      simp [hl]) fun _ _ => ?_
    show F (x :: l).dropLast ((x :: l).getLast _)
        = shiftAnswers x F l.dropLast (l.getLast hl)
    rw [List.dropLast_cons_of_ne_nil hl, List.getLast_cons hl]
    rfl

open Classical in
/-- **The successor of a lazily sampled system**, at an answered value: shift
the answer function past `x` and condition the seed on having answered `v`. -/
theorem successorTransform_seededLaw {Ω : Type*} (F : Ω → List X → X → Y)
    (μ : Dist Ω) (x : X) (v : Y) :
    successorTransform (seededLaw F μ) x (some v)
      = seededLaw (fun ω => shiftAnswers x (F ω))
          (μ.filter fun ω => F ω [] x = v) := by
  refine Finsupp.ext fun s => ?_
  show Dist.fTransform (fun s' => PFunDDS.DDS.successor s' x)
      ((seededLaw F μ).filter _) s = _
  rw [Dist.fTransform_apply_eq_mass, mass_filter, seededLaw,
    Dist.mass_fTransform]
  show _ = Dist.fTransform (fun ω => seededDDS (shiftAnswers x (F ω)))
    (μ.filter _) s
  rw [Dist.fTransform_apply_eq_mass, mass_filter]
  refine Dist.mass_congr μ fun ω => ?_
  rw [successor_seededDDS, output_seededDDS]
  exact and_congr_right' ⟨fun h => Option.some.inj h, fun h => congrArg some h⟩

open Classical in
/-- A lazily sampled system never `⊥`-answers, so the `none` branch of the
successor split is empty. -/
theorem successorTransform_seededLaw_none {Ω : Type*} (F : Ω → List X → X → Y)
    (μ : Dist Ω) (x : X) :
    successorTransform (seededLaw F μ) x none = 0 := by
  refine successorTransform_eq_zero _ _ fun s hs => ?_
  obtain ⟨ω, -, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  rw [output_seededDDS]
  exact Option.some_ne_none _

/-- **The first-answer law of a lazily sampled system** is the pushforward of
the seed law along "what `F` answers to `x` on the empty history". -/
theorem answerLaw_seededLaw {Ω : Type*} (F : Ω → List X → X → Y) (μ : Dist Ω)
    (x : X) :
    answerLaw (seededLaw F μ) x
      = Dist.fTransform (fun ω => some (F ω [] x)) μ := by
  unfold answerLaw seededLaw
  rw [Dist.fTransform_comp]
  exact congrArg (Dist.fTransform · μ) (funext fun ω => output_seededDDS (F ω) x)

/-- The first-answer distance of two lazily sampled systems is the distance of
their next-answer laws — the pushforwards of the two seed laws under their
own answer functions.  This is the quantity a lazy-sampling argument actually
computes, so it is the shape `hstep` should be discharged in.

`hν` is the signed carrier's cost: reading `δ` back through the injection
`some` needs the right-hand law to be non-negative. -/
theorem delta_answerLaw_seededLaw {Ω Ω' : Type*} (F : Ω → List X → X → Y)
    (G : Ω' → List X → X → Y) (μ : Dist Ω) {ν : Dist Ω'} (hν : ν.NonNeg)
    (x : X) :
    δ (answerLaw (seededLaw F μ) x) (answerLaw (seededLaw G ν) x)
      = δ (Dist.fTransform (fun ω => F ω [] x) μ)
          (Dist.fTransform (fun ω => G ω [] x) ν) := by
  rw [answerLaw_seededLaw, answerLaw_seededLaw,
    show (fun ω => some (F ω [] x)) = Option.some ∘ fun ω => F ω [] x from rfl,
    show (fun ω => some (G ω [] x)) = Option.some ∘ fun ω => G ω [] x from rfl,
    ← Dist.fTransform_comp, ← Dist.fTransform_comp]
  exact δ_fTransform_eq_of_injective (fun _ _ h => Option.some.inj h) _
    (hν.fTransform _)

/-! ### The query budget

`⌈N⌉` truncates a system's domain to histories of length `≤ N`, which is not
itself a history evaluator — past the budget the system is *undefined*, not
answering.  The successor calculus survives the truncation with the budget as
one more index, and the exhausted system is where the hybrid's `ε` may be
taken to be `0`: both sides `⊥`-answer, so their first-answer laws differ by
exactly the weight defect the hybrid already carries. -/

/-- A lazily sampled system under a query budget. -/
def seededDDSUpTo (N : ℕ) (F : List X → X → Y) : PFunDDS.DDS X Y :=
  PFunDDS.filterQueries N (seededDDS F)

/-- The law of a budgeted lazily sampled system. -/
noncomputable def seededLawUpTo {Ω : Type*} (N : ℕ) (F : Ω → List X → X → Y)
    (μ : Dist Ω) : PFunPDS X Y :=
  Dist.fTransform (fun ω => seededDDSUpTo N (F ω)) μ

theorem filterQueries_seededLaw {Ω : Type*} (N : ℕ) (F : Ω → List X → X → Y)
    (μ : Dist Ω) :
    PFunPDS.filterQueries N (seededLaw F μ) = seededLawUpTo N F μ := by
  unfold PFunPDS.filterQueries seededLaw seededLawUpTo
  rw [Dist.fTransform_comp]
  rfl

theorem ne_nil_of_mem_dom_seededDDS (F : List X → X → Y) {l : List X}
    (h : l ∈ PFunDDS.dom (seededDDS F)) : l ≠ [] := by
  rw [seededDDS, PFunDDS.dom_historyEvaluator] at h
  exact h

theorem mem_dom_seededDDSUpTo (N : ℕ) (F : List X → X → Y) (l : List X) :
    l ∈ PFunDDS.dom (seededDDSUpTo N F) ↔ l ≠ [] ∧ l.length ≤ N := by
  rw [seededDDSUpTo, PFunDDS.mem_dom_filterQueries]
  exact and_congr_left' ⟨ne_nil_of_mem_dom_seededDDS F, mem_dom_seededDDS F⟩

theorem output_seededDDSUpTo_succ (N : ℕ) (F : List X → X → Y) (x : X) :
    PFunDDS.output (PFunDDS.fullyDefined (seededDDSUpTo (N + 1) F)) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some (F [] x) :=
  PFunDDS.output_fullyDefined_append_of_mem _ [] x (Or.inr rfl)
    ((mem_dom_seededDDSUpTo _ _ _).mpr ⟨by simp, by simp⟩)

theorem output_seededDDSUpTo_zero (F : List X → X → Y) (x : X) :
    PFunDDS.output (PFunDDS.fullyDefined (seededDDSUpTo 0 F)) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
  rw [PFunDDS.output_fullyDefined]
  exact dif_neg fun hmem =>
    absurd ((mem_dom_seededDDSUpTo 0 F _).mp hmem).2 (by simp)

/-- One query of the budget spent: the successor of a budgeted lazily sampled
system shifts the answer function and decrements the budget. -/
theorem successor_seededDDSUpTo_succ (N : ℕ) (F : List X → X → Y) (x : X) :
    PFunDDS.DDS.successor (seededDDSUpTo (N + 1) F) x
      = seededDDSUpTo N (shiftAnswers x F) := by
  have hx : [x] ∈ PFunDDS.dom (seededDDSUpTo (N + 1) F) :=
    (mem_dom_seededDDSUpTo _ _ _).mpr ⟨by simp, by simp⟩
  refine Subtype.ext (funext fun l => ?_)
  by_cases hl : l = []
  · subst hl
    have hL : (PFunDDS.DDS.successor (seededDDSUpTo (N + 1) F) x).1 []
        = Part.none := by
      unfold PFunDDS.DDS.successor
      rw [if_pos hx]
      simp
    have hR : (seededDDSUpTo N (shiftAnswers x F)).1 [] = Part.none :=
      Part.eq_none_iff'.mpr fun hdom =>
        absurd ((mem_dom_seededDDSUpTo N _ _).mp hdom).1 (by simp)
    rw [hL, hR]
  · rw [successor_apply_of_mem hx hl]
    refine Part.ext' ?_ fun _ _ => ?_
    · show (x :: l ≠ [] ∧ (x :: l).length ≤ N + 1) ↔ (l ≠ [] ∧ l.length ≤ N)
      simp [hl]
    · show F (x :: l).dropLast ((x :: l).getLast _)
          = shiftAnswers x F l.dropLast (l.getLast hl)
      rw [List.dropLast_cons_of_ne_nil hl, List.getLast_cons hl]
      rfl

/-- An exhausted budget: the system is nowhere defined, so it is its own
successor. -/
theorem successor_seededDDSUpTo_zero (F : List X → X → Y) (x : X) :
    PFunDDS.DDS.successor (seededDDSUpTo 0 F) x = seededDDSUpTo 0 F :=
  successor_of_not_mem fun hmem =>
    absurd ((mem_dom_seededDDSUpTo 0 F _).mp hmem).2 (by simp)

open Classical in
/-- **The successor of a budgeted lazily sampled system**, at an answered
value. -/
theorem successorTransform_seededLawUpTo {Ω : Type*} (N : ℕ)
    (F : Ω → List X → X → Y) (μ : Dist Ω) (x : X) (v : Y) :
    successorTransform (seededLawUpTo (N + 1) F μ) x (some v)
      = seededLawUpTo N (fun ω => shiftAnswers x (F ω))
          (μ.filter fun ω => F ω [] x = v) := by
  refine Finsupp.ext fun s => ?_
  show Dist.fTransform (fun s' => PFunDDS.DDS.successor s' x)
      ((seededLawUpTo (N + 1) F μ).filter _) s = _
  rw [Dist.fTransform_apply_eq_mass, mass_filter, seededLawUpTo,
    Dist.mass_fTransform]
  show _ = Dist.fTransform
    (fun ω => seededDDSUpTo N (shiftAnswers x (F ω))) (μ.filter _) s
  rw [Dist.fTransform_apply_eq_mass, mass_filter]
  refine Dist.mass_congr μ fun ω => ?_
  rw [successor_seededDDSUpTo_succ, output_seededDDSUpTo_succ]
  exact and_congr_right' ⟨fun h => Option.some.inj h, fun h => congrArg some h⟩

open Classical in
theorem successorTransform_seededLawUpTo_none {Ω : Type*} (N : ℕ)
    (F : Ω → List X → X → Y) (μ : Dist Ω) (x : X) :
    successorTransform (seededLawUpTo (N + 1) F μ) x none = 0 := by
  refine successorTransform_eq_zero _ _ fun s hs => ?_
  obtain ⟨ω, -, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  rw [output_seededDDSUpTo_succ]
  exact Option.some_ne_none _

open Classical in
/-- With the budget exhausted every query is `⊥`-answered, and the system is
unchanged. -/
theorem successorTransform_seededLawUpTo_zero {Ω : Type*}
    (F : Ω → List X → X → Y) (μ : Dist Ω) (x : X) :
    successorTransform (seededLawUpTo 0 F μ) x none = seededLawUpTo 0 F μ := by
  refine Finsupp.ext fun s => ?_
  show Dist.fTransform (fun s' => PFunDDS.DDS.successor s' x)
      ((seededLawUpTo 0 F μ).filter _) s = _
  rw [Dist.fTransform_apply_eq_mass, mass_filter, seededLawUpTo,
    Dist.mass_fTransform, Dist.fTransform_apply_eq_mass]
  refine Dist.mass_congr μ fun ω => ?_
  rw [successor_seededDDSUpTo_zero, output_seededDDSUpTo_zero]
  exact and_iff_left rfl

theorem answerLaw_seededLawUpTo_succ {Ω : Type*} (N : ℕ)
    (F : Ω → List X → X → Y) (μ : Dist Ω) (x : X) :
    answerLaw (seededLawUpTo (N + 1) F μ) x
      = Dist.fTransform (fun ω => some (F ω [] x)) μ := by
  unfold answerLaw seededLawUpTo
  rw [Dist.fTransform_comp]
  exact congrArg (Dist.fTransform · μ)
    (funext fun ω => output_seededDDSUpTo_succ N (F ω) x)

theorem answerLaw_seededLawUpTo_zero {Ω : Type*} (F : Ω → List X → X → Y)
    (μ : Dist Ω) (x : X) :
    answerLaw (seededLawUpTo 0 F μ) x
      = Dist.fTransform (fun _ => (none : Option Y)) μ := by
  unfold answerLaw seededLawUpTo
  rw [Dist.fTransform_comp]
  exact congrArg (Dist.fTransform · μ)
    (funext fun ω => output_seededDDSUpTo_zero (F ω) x)

/-- With the budget exhausted the first-answer laws are two point masses at
`⊥`, so their distance is the weight defect the hybrid already carries: past
the budget the caller may take `ε = 0`. -/
theorem delta_answerLaw_seededLawUpTo_zero {Ω Ω' : Type*}
    (F : Ω → List X → X → Y) (G : Ω' → List X → X → Y) (μ : Dist Ω)
    {ν : Dist Ω'} (hν : ν.NonNeg) (x : X) :
    δ (answerLaw (seededLawUpTo 0 F μ) x) (answerLaw (seededLawUpTo 0 G ν) x)
      = max (μ.weight - ν.weight) 0 := by
  classical
  rw [answerLaw_seededLawUpTo_zero, answerLaw_seededLawUpTo_zero,
    δ_eq_sum_of_support_subset (hν.fTransform _)
      (show (Dist.fTransform (fun _ => (none : Option Y)) μ).support
          ⊆ ({none} : Finset (Option Y)) from by
        intro a ha
        obtain ⟨-, -, hs⟩ := Dist.mem_support_fTransform _ _ ha
        simp [← hs]),
    Finset.sum_singleton, Dist.fTransform_apply_eq_mass,
    Dist.fTransform_apply_eq_mass]
  congr 2 <;> exact (Dist.mass_congr _ fun _ => (iff_true _).mpr rfl).trans
    (Dist.mass_true _)

/-- The first-answer distance of two budgeted lazily sampled systems, before
the budget is exhausted. -/
theorem delta_answerLaw_seededLawUpTo_succ {Ω Ω' : Type*} (N : ℕ)
    (F : Ω → List X → X → Y) (G : Ω' → List X → X → Y) (μ : Dist Ω)
    {ν : Dist Ω'} (hν : ν.NonNeg) (x : X) :
    δ (answerLaw (seededLawUpTo (N + 1) F μ) x)
        (answerLaw (seededLawUpTo (N + 1) G ν) x)
      = δ (Dist.fTransform (fun ω => F ω [] x) μ)
          (Dist.fTransform (fun ω => G ω [] x) ν) := by
  rw [answerLaw_seededLawUpTo_succ, answerLaw_seededLawUpTo_succ,
    show (fun ω => some (F ω [] x)) = Option.some ∘ fun ω => F ω [] x from rfl,
    show (fun ω => some (G ω [] x)) = Option.some ∘ fun ω => G ω [] x from rfl,
    ← Dist.fTransform_comp, ← Dist.fTransform_comp]
  exact δ_fTransform_eq_of_injective (fun _ _ h => Option.some.inj h) _
    (hν.fTransform _)

/-! ### Shifting past a whole history -/

/-- `F` after the queries `us` have been asked, in order. -/
def shiftAllAnswers (us : List X) (F : List X → X → Y) : List X → X → Y :=
  fun vs u => F (us ++ vs) u

@[simp] theorem shiftAllAnswers_nil (F : List X → X → Y) :
    shiftAllAnswers [] F = F := rfl

theorem shiftAllAnswers_apply_nil (us : List X) (F : List X → X → Y) (u : X) :
    shiftAllAnswers us F [] u = F us u := by
  show F (us ++ []) u = F us u
  rw [List.append_nil]

theorem shiftAnswers_shiftAllAnswers (us : List X) (x : X)
    (F : List X → X → Y) :
    shiftAnswers x (shiftAllAnswers us F) = shiftAllAnswers (us ++ [x]) F := by
  funext vs u
  show F (us ++ x :: vs) u = F (us ++ [x] ++ vs) u
  rw [List.append_assoc]
  rfl

/-! ### Exhausted systems

Past the query budget both sides are supported on nowhere-defined systems.
The hybrid still has to walk those levels — the environment may keep
querying — but they cost nothing beyond the weight defect. -/

/-- Every system in the support is nowhere defined. -/
def Exhausted (A : PFunPDS X Y) : Prop :=
  ∀ s ∈ A.support, ∀ l : List X, l ∉ PFunDDS.dom s

theorem exhausted_seededLawUpTo_zero {Ω : Type*} (F : Ω → List X → X → Y)
    (μ : Dist Ω) : Exhausted (seededLawUpTo 0 F μ) := by
  intro s hs l hl
  obtain ⟨ω, -, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  exact absurd ((mem_dom_seededDDSUpTo 0 (F ω) l).mp hl).2
    (by simpa using ((mem_dom_seededDDSUpTo 0 (F ω) l).mp hl).1)

theorem exhausted_zero : Exhausted (0 : PFunPDS X Y) := by
  intro s hs
  simp at hs

/-- A pushforward only sees the map on the support. -/
theorem fTransform_congr_on_support {A B : Type*} {f g : A → B} (μ : Dist A)
    (h : ∀ a ∈ μ.support, f a = g a) :
    Dist.fTransform f μ = Dist.fTransform g μ :=
  Finsupp.mapDomain_congr h

theorem answerLaw_of_exhausted {A : PFunPDS X Y} (hA : Exhausted A) (x : X) :
    answerLaw A x = Dist.fTransform (fun _ => (none : Option Y)) A :=
  fTransform_congr_on_support A fun s hs => by
    rw [PFunDDS.output_fullyDefined]
    exact dif_neg (hA s hs _)

open Classical in
theorem delta_answerLaw_of_exhausted {A B : PFunPDS X Y} (hA : Exhausted A)
    (hB : Exhausted B) (hBnn : B.NonNeg) (x : X) :
    δ (answerLaw A x) (answerLaw B x) = max (A.weight - B.weight) 0 := by
  rw [answerLaw_of_exhausted hA, answerLaw_of_exhausted hB,
    δ_eq_sum_of_support_subset (hBnn.fTransform _)
      (show (Dist.fTransform (fun _ => (none : Option Y)) A).support
          ⊆ ({none} : Finset (Option Y)) from by
        intro a ha
        obtain ⟨-, -, hs⟩ := Dist.mem_support_fTransform _ _ ha
        simp [← hs]),
    Finset.sum_singleton, Dist.fTransform_apply_eq_mass,
    Dist.fTransform_apply_eq_mass]
  congr 2 <;> exact (Dist.mass_congr _ fun _ => (iff_true _).mpr rfl).trans
    (Dist.mass_true _)

open Classical in
theorem exhausted_successorTransform {A : PFunPDS X Y} (hA : Exhausted A)
    (x : X) (y : Option Y) : Exhausted (successorTransform A x y) := by
  intro s hs l hl
  obtain ⟨s', hs', rfl⟩ := Dist.mem_support_fTransform _ _ hs
  rw [Finsupp.support_filter, Finset.mem_filter] at hs'
  rw [successor_of_not_mem (hA s' hs'.1 [x])] at hl
  exact hA s' hs'.1 l hl

/-! ## The lazy-sampling hybrid, packaged

Everything above, assembled into the theorem a lazy-sampling argument actually
wants: two seeded systems under a shared query budget `N`, an invariant `Inv`
the caller maintains along the interaction, and one obligation per step —
**the conditional next-answer laws are `ε d` apart**.  No successor
transformation, no transcript algebra, and no conditional equivalence appears
in the caller's obligations.

The `Inv` argument carries the conditioned seed laws explicitly, because that
is what a lazily sampled system's next answer is a function of: `μ'` is the
seed law given the interaction so far, and `Dist.fTransform (F · us x) μ'` is
the (sub-probability) law of the next answer. -/
open Classical in
theorem maxAdvantage_filterQueries_seededLaw_le {Ω Ω' : Type*} (N : ℕ)
    (F : Ω → List X → X → Y) (G : Ω' → List X → X → Y)
    {μ : Dist Ω} {ν : Dist Ω'} (hμ : μ.NonNeg) (hν : ν.NonNeg) (ε : ℕ → NNReal)
    (Inv : ℕ → List X → Dist Ω → Dist Ω' → Prop)
    (hinit : Inv 0 [] μ ν)
    (hnext : ∀ (d : ℕ) (us : List X) (μ' : Dist Ω) (ν' : Dist Ω'),
      Inv d us μ' ν' → ∀ (x : X) (v : Y),
        Inv (d + 1) (us ++ [x])
          (μ'.filter fun ω => F ω us x = v) (ν'.filter fun ω => G ω us x = v))
    (hdist : ∀ (d : ℕ) (us : List X) (μ' : Dist Ω) (ν' : Dist Ω'),
      Inv d us μ' ν' → d < N → ∀ x : X,
        δ (Dist.fTransform (fun ω => F ω us x) μ')
            (Dist.fTransform (fun ω => G ω us x) ν')
          ≤ ε d * μ'.weight + max (μ'.weight - ν'.weight) 0)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ n : ℕ, ((∑ i ∈ Finset.range n, ε i : NNReal) : ℝ) * μ.weight
        + max (μ.weight - ν.weight) 0 ≤ c) :
    Δ(PFunPDS.filterQueries N (seededLaw G ν),
      PFunPDS.filterQueries N (seededLaw F μ)) ≤ c := by
  classical
  -- the seed laws' non-negativity travels inside `Good`: the caller's `Inv`
  -- is unconstrained, and `Finsupp.filter` is what conditioning does to it.
  set Good : ℕ → PFunPDS X Y → PFunPDS X Y → Prop := fun d A B =>
    (Exhausted A ∧ Exhausted B) ∨
      (d < N ∧ ∃ (us : List X) (μ' : Dist Ω) (ν' : Dist Ω'),
        Inv d us μ' ν' ∧ μ'.NonNeg ∧ ν'.NonNeg ∧
          A = seededLawUpTo (N - d) (fun ω => shiftAllAnswers us (F ω)) μ' ∧
          B = seededLawUpTo (N - d) (fun ω => shiftAllAnswers us (G ω)) ν')
    with hGood
  have hsucc : ∀ (d : ℕ) (A B : PFunPDS X Y), Good d A B →
      ∀ (x : X) (y : Option Y),
        Good (d + 1) (successorTransform A x y) (successorTransform B x y) := by
    rintro d A B (⟨hA, hB⟩ | ⟨hlt, us, μ', ν', hinv, hμ', hν', rfl, rfl⟩) x y
    · exact Or.inl ⟨exhausted_successorTransform hA x y,
        exhausted_successorTransform hB x y⟩
    obtain ⟨k, hk⟩ : ∃ k, N - d = k + 1 := ⟨N - d - 1, by omega⟩
    rw [hk]
    cases y with
    | none =>
        rw [successorTransform_seededLawUpTo_none,
          successorTransform_seededLawUpTo_none]
        exact Or.inl ⟨exhausted_zero, exhausted_zero⟩
    | some v =>
        rw [successorTransform_seededLawUpTo, successorTransform_seededLawUpTo]
        simp only [shiftAnswers_shiftAllAnswers]
        have hshift : ∀ (H : List X → X → Y), shiftAllAnswers us H [] x = H us x :=
          fun H => shiftAllAnswers_apply_nil us H x
        simp only [hshift]
        rcases Nat.lt_or_ge (d + 1) N with hlt' | hge'
        · refine Or.inr ⟨hlt', us ++ [x], _, _,
            hnext d us μ' ν' hinv x v, hμ'.restrict _, hν'.restrict _, ?_, ?_⟩ <;>
          · congr 1
            omega
        · have hk0 : k = 0 := by omega
          subst hk0
          exact Or.inl ⟨exhausted_seededLawUpTo_zero _ _,
            exhausted_seededLawUpTo_zero _ _⟩
  have hstep : ∀ (d : ℕ) (A B : PFunPDS X Y), Good d A B →
      A.NonNeg → B.NonNeg → ∀ x : X,
      δ (answerLaw A x) (answerLaw B x)
        ≤ ε d * A.weight + max (A.weight - B.weight) 0 := by
    rintro d A B (⟨hA, hB⟩ | ⟨hlt, us, μ', ν', hinv, hμ', hν', rfl, rfl⟩)
      hAnn hBnn x
    · rw [delta_answerLaw_of_exhausted hA hB hBnn]
      exact le_add_of_nonneg_left
        (mul_nonneg (NNReal.coe_nonneg _) hAnn.weight_nonneg)
    obtain ⟨k, hk⟩ : ∃ k, N - d = k + 1 := ⟨N - d - 1, by omega⟩
    rw [hk, delta_answerLaw_seededLawUpTo_succ _ _ _ _ hν']
    have hshift : ∀ (H : List X → X → Y), shiftAllAnswers us H [] x = H us x :=
      fun H => shiftAllAnswers_apply_nil us H x
    simp only [hshift]
    have hwA : (seededLawUpTo (k + 1)
        (fun ω => shiftAllAnswers us (F ω)) μ').weight = μ'.weight :=
      Dist.weight_fTransform _ _
    have hwB : (seededLawUpTo (k + 1)
        (fun ω => shiftAllAnswers us (G ω)) ν').weight = ν'.weight :=
      Dist.weight_fTransform _ _
    rw [hwA, hwB]
    exact hdist d us μ' ν' hinv hlt x
  have hwT : (PFunPDS.filterQueries N (seededLaw F μ)).weight = μ.weight := by
    rw [filterQueries_seededLaw]
    exact Dist.weight_fTransform _ _
  have hwS : (PFunPDS.filterQueries N (seededLaw G ν)).weight = ν.weight := by
    rw [filterQueries_seededLaw]
    exact Dist.weight_fTransform _ _
  refine maxAdvantage_le_of_stepwise (PFunPDS.filterQueries N (seededLaw G ν))
    (PFunPDS.filterQueries N (seededLaw F μ)) Good ε hsucc hstep ?_
    ((hν.fTransform _).fTransform _) ((hμ.fTransform _).fTransform _) hc0
    fun n => by rw [hwT, hwS]; exact hc n
  rw [filterQueries_seededLaw, filterQueries_seededLaw]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Or.inl ⟨exhausted_seededLawUpTo_zero _ _,
      exhausted_seededLawUpTo_zero _ _⟩
  · exact Or.inr ⟨hN, [], μ, ν, hinit, hμ, hν, by simp, by simp⟩

end RandomSystems.CR18

