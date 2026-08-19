/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Distinguishing
import RandomSystems.Lemma415
import RandomSystems.Coupling

/-!
# Random systems as equivalence classes of PDS
(Lanzenberger, *Theory of Random Systems and Games*, Ch. 2; LM20; CR18 §3.6)

The consolidation of the three faces of identity at the PDS level:

* the **RV face** — a PDS is a distribution over DDS (thesis Def 2.14;
  the repository's `Dist` model, sub-distributions included);
* the **behavior face** — the successful-answer kernel of CR18 Definition
  3.19 and, separately, the cumulative observable `Option` behavior obtained
  through `s ↦ s⊥` in Definition 3.20; the latter records rejected queries as
  `⊥` and is the behavior notion equivalent to transcript laws for partial
  systems;
* the **metric face** — zero optimal distinguishing advantage
  (thesis Def 2.26).

A *random system* (thesis Notation 2.19) is an equivalence class of
PDS; "an equivalence class of PDS describes exactly a random system as
introduced in [Mau02]".  The keystone theorems posed here glue the
faces:

* `transcript_equivalent_of_nonadaptive_transcript_equivalent` — thesis
  Lemma 2.18;
* `behavior_equivalent_iff_transcript_equivalent` — the CR18 §3.6
  certificate relating cumulative observable behavior to transcript laws.
  Definitions 3.3 and 3.6--3.7 make rejected queries observable as `⊥` and
  delete them from the system history; Definition 3.20 supplies the cumulative
  viewpoint, and Lemma 3.2 supplies the transcript factorization.  The converse
  fixed-query extraction below is a proof for this explicit `Option` model, not
  a separately named theorem quoted from CR18;
* `adv_eq_maxAdvantage_swap` — thesis Def 2.26's remark: the transcript form
  of the advantage is the classical verdict-based `maxAdvantage`;
* `optimal_advantage_le_class_distance` — the data-processing direction from
  transcript advantage to static representative distance.

The arbitrary-mass layer is proof infrastructure: LanMau20 explicitly needs
subdistributions for successor systems in the induction proving Theorem 1.
The public random-system layer is `PFunPDS.Prob`, matching Maurer02's
conditional probability laws.  In particular, a joint distribution can have
the requested marginals only when their weights agree; Theorem 2's probability
interpretation is therefore exposed only at the normalized boundary.

The source attainment and coupling theorems assume a finite query alphabet, a
common DDS domain, and a uniform finite bound on answered-query depth.  The
unrestricted varying-domain strengthening is false: observable rejection can
distinguish domain patterns that the optimal transcript advantage cannot force
into one common representative coupling.  Consequently this file retains the
valid reconstruction and coupling infrastructure, but does not expose an
unrestricted attainment or random-system coupling endpoint.  The exact source
boundary and counterexample are recorded in `papers/notes/RS_SOURCE_CONTRACT.md`.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped PFunPDS

universe u v

variable {X : Type u} {Y : Type v}

/-! ### The statistical distance `δ` (thesis §2.2) -/

/-- Thesis Definition 2.4: the statistical distance
`δ(X, Y) := ∑ₐ max(0, X(a) − Y(a))`, in the `Finsupp`-native form (the
sum ranges over the support, no finiteness of the carrier is needed; on
a `Fintype` carrier it agrees with `statDist`).  Def 2.4's note: for
distributions of different weight `δ` is **not symmetric**; for equal
weight it is `½ ∑ₐ |X(a) − Y(a)|`. -/
noncomputable def δ {A : Type*} (μ ν : Dist A) : ℝ :=
  μ.sum fun a m => max (m - ν a) 0

/-- Every summand of `δ` is non-negative, so `δ` is. -/
theorem δ_nonneg {A : Type*} (μ ν : Dist A) : 0 ≤ δ μ ν :=
  Finset.sum_nonneg fun a _ => le_max_right _ _

/-- **`δ` and `statDist` are one metric at two generalities.**  Both are the one-sided
excess `∑ max (μ a − ν a) 0`; they differ only in the index set — `δ` sums over
`μ.support`, `statDist` over `(μ − ν).support` — and they agree exactly when `ν ≥ 0`,
because the cells `δ` omits are those with `μ a = 0`, where the summand is `max (−ν a) 0`.

This is thesis Def 2.4's own remark, and it is why the `statDist` H-technique family and the
`δ` one are not two hierarchies: either is a rewrite away from the other on any non-negative
law, which every transcript law is. -/
theorem statDist_eq_δ_of_nonneg {A : Type*} (μ ν : Dist A) (hν : ν.NonNeg) :
    RandomSystems.statDist μ ν = δ μ ν := by
  classical
  have h1 : ∀ a ∈ (μ - ν).support, a ∉ μ.support → max (μ a - ν a) 0 = 0 := by
    intro a _ ha
    rw [Finsupp.notMem_support_iff] at ha
    rw [ha, zero_sub, max_eq_right (neg_nonpos.mpr (hν a))]
  have h2 : ∀ a ∈ μ.support, a ∉ (μ - ν).support → max (μ a - ν a) 0 = 0 := by
    intro a _ ha
    rw [Finsupp.notMem_support_iff] at ha
    have h : μ a - ν a = 0 := by simpa using ha
    rw [h, max_self]
  have e1 : ∑ a ∈ (μ - ν).support ∩ μ.support, max (μ a - ν a) 0
      = RandomSystems.statDist μ ν :=
    Finset.sum_subset Finset.inter_subset_left
      (fun a ha hna => h1 a ha (fun hx => hna (Finset.mem_inter.mpr ⟨ha, hx⟩)))
  have e2 : ∑ a ∈ (μ - ν).support ∩ μ.support, max (μ a - ν a) 0 = δ μ ν := by
    rw [Finset.inter_comm]
    exact Finset.sum_subset Finset.inter_subset_left
      (fun a ha hna => h2 a ha (fun hx => hna (Finset.mem_inter.mpr ⟨ha, hx⟩)))
  rw [← e1, e2]

/-- Def 2.4's diagonal: `δ(X, X) = 0`. -/
theorem δ_self {A : Type*} (μ : Dist A) : δ μ μ = 0 := by
  unfold δ
  rw [Finsupp.sum]
  exact Finset.sum_eq_zero fun a _ => by simp

/-- Def 2.4's `δ` is dominated by the first argument's total weight (for
non-negative laws). -/
theorem δ_le_weight {A : Type*} {μ ν : Dist A} (hμ : μ.NonNeg) (hν : ν.NonNeg) :
    δ μ ν ≤ μ.weight := by
  unfold δ
  rw [Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_le_sum fun a _ => max_le (sub_le_self _ (hν a)) (hμ a)

/-- Def 2.4's `δ` as a mass difference: the one-sided excess of `μ`
over `ν` is the mass gap on the set where `μ` exceeds `ν` (for a non-negative
second law; a signed `ν` could hide excess off `μ`'s support). -/
theorem δ_eq_mass_sub_mass {A : Type*} (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) :
    (δ μ ν : ℝ) = ((μ.mass fun a => ν a < μ a : ℝ) : ℝ)
      - ((ν.mass fun a => ν a < μ a : ℝ) : ℝ) := by
  classical
  unfold δ Dist.mass
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum]
  dsimp only
  -- enlarge all three sums to the common support union; the summands
  -- are unified from the goal, so decidability instances never clash
  rw [Finset.sum_subset
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support),
    Finset.sum_subset
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support),
    Finset.sum_subset
      (Finset.subset_union_right : ν.support ⊆ μ.support ∪ ν.support)]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hP : ν a < μ a
    · rw [if_pos hP, if_pos hP, max_eq_left (sub_nonneg.mpr hP.le)]
    · rw [if_neg hP, if_neg hP, max_eq_right (sub_nonpos.mpr (not_lt.mp hP))]
      simp
  all_goals
    intro a _ ha
    have h0 := Finsupp.notMem_support_iff.mp ha
    first
      | (rw [h0]; exact max_eq_right (sub_nonpos.mpr (hν a)))
      | simp only [h0, ite_self]

/-- `δ` is non-increasing under pushforward (LanMau20 Lemma 3, the
data-processing step of Theorem 1): merging outcomes cannot increase
the one-sided excess. -/
theorem δ_fTransform_le {A B : Type*} (f : A → B) (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) :
    δ (Dist.fTransform f μ) (Dist.fTransform f ν) ≤ δ μ ν := by
  classical
  unfold δ
  rw [Finsupp.sum, Finsupp.sum]
  -- Extend the left sum from the pushforward's support to the image of
  -- `μ.support` (off the pushforward's support the summand vanishes only
  -- because `fTransform f ν` is non-negative there).
  have hνf : (Dist.fTransform f ν).NonNeg := hν.fTransform f
  have hsub : (Dist.fTransform f μ).support ⊆ μ.support.image f :=
    Finsupp.mapDomain_support
  rw [Finset.sum_subset hsub (fun y _ hy => by
    rw [Finsupp.notMem_support_iff.mp hy]
    exact max_eq_right (by simpa using hνf y))]
  have hmaps : ∀ a ∈ μ.support, f a ∈ μ.support.image f := by
    intro a ha
    exact Finset.mem_image_of_mem f ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps fun a => max (μ a - ν a) 0]
  refine Finset.sum_le_sum fun y _ => ?_
  have hμb : Dist.fTransform f μ y
      = ∑ a ∈ μ.support.filter fun a => f a = y, μ a := by
    rw [Dist.fTransform_apply_eq_mass]
    unfold Dist.mass
    rw [Finsupp.sum]
    exact (Finset.sum_filter (fun a => f a = y) fun a => μ a).symm
  have hνb : (∑ a ∈ μ.support.filter fun a => f a = y, ν a)
      ≤ Dist.fTransform f ν y := by
    rw [Dist.fTransform_apply_eq_mass]
    unfold Dist.mass
    rw [Finsupp.sum]
    calc (∑ a ∈ μ.support.filter fun a => f a = y, ν a)
        = ∑ a ∈ (μ.support.filter fun a => f a = y) ∩ ν.support, ν a := by
          refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
          intro a haf hani
          by_contra h0
          exact hani (Finset.mem_inter.mpr
            ⟨haf, Finsupp.mem_support_iff.mpr h0⟩)
      _ ≤ ∑ a ∈ ν.support, if f a = y then ν a else 0 := by
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun a _ _ => hν a
          intro a ha
          rw [Finset.mem_inter, Finset.mem_filter] at ha
          exact Finset.mem_filter.mpr ⟨ha.2, ha.1.2⟩
  refine max_le ?_ (Finset.sum_nonneg fun a _ => le_max_right _ _)
  calc Dist.fTransform f μ y - Dist.fTransform f ν y
      ≤ (∑ a ∈ μ.support.filter fun a => f a = y, μ a)
        - ∑ a ∈ μ.support.filter fun a => f a = y, ν a := by
        rw [hμb]
        exact sub_le_sub_left hνb _
    _ = ∑ a ∈ μ.support.filter fun a => f a = y, (μ a - ν a) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a ∈ μ.support.filter fun a => f a = y, max (μ a - ν a) 0 :=
        Finset.sum_le_sum fun a _ => le_max_left _ _

/-- Pushing both distributions forward along an **injection** preserves
the statistical distance (the prepend step of thesis Theorem 2.31's
proof): a left inverse of the injection is itself a pushforward, so
`δ_fTransform_le` applies in both directions. -/
theorem δ_fTransform_eq_of_injective {A B : Type*} {f : A → B}
    (hf : Function.Injective f) (μ : Dist A) {ν : Dist A} (hν : ν.NonNeg) :
    δ (Dist.fTransform f μ) (Dist.fTransform f ν) = δ μ ν := by
  refine le_antisymm (δ_fTransform_le f μ hν) ?_
  rcases isEmpty_or_nonempty A with h | h
  · have hμ : μ = 0 := Finsupp.ext fun a => (h.false a).elim
    have hν' : ν = 0 := Finsupp.ext fun a => (h.false a).elim
    subst hμ; subst hν'
    simp [δ_self]
  · calc δ μ ν
        = δ (Dist.fTransform (Function.invFun f) (Dist.fTransform f μ))
            (Dist.fTransform (Function.invFun f) (Dist.fTransform f ν)) := by
          rw [Dist.fTransform_comp, Dist.fTransform_comp,
            Function.invFun_comp hf]
          simp only [Dist.fTransform_id]
      _ ≤ δ (Dist.fTransform f μ) (Dist.fTransform f ν) :=
          δ_fTransform_le _ _ (hν.fTransform f)

/-! ### Common-factorization normalization

These definitions and theorems package the carrier-independent content of
"pointless-query" and similar normalizations.  They do not mention random
systems or transcripts: a family of pairs of laws loses no distinguishing
power when every pair is a common pushforward of a pair in the restricted
family. -/

/-- The supremum of `δ` over an arbitrary family of pairs of laws.  The index
may be environments, games, observations, or any other parameter. -/
noncomputable def lawFamilyAdvantage {I : Type*} {A : Type*}
    (P Q : I → Dist A) : ℝ :=
  sSup ((fun i => δ (P i) (Q i)) '' Set.univ)

/-- Restrict a law-family advantage to indices satisfying `Allowed`. -/
noncomputable def restrictedLawFamilyAdvantage {I : Type*} {A : Type*}
    (Allowed : I → Prop) (P Q : I → Dist A) : ℝ :=
  sSup ((fun i => δ (P i) (Q i)) '' {i | Allowed i})

/-- **Common-factorization DPI.**  If both laws at every source index are
pushforwards, along the same reconstruction map, of two laws in a target
family, then the source-family advantage is at most the target-family
advantage.  The two families may have different index types and different
outcome carriers.

The shared reconstruction map is load-bearing: two endpoint-specific maps do
not give a data-processing comparison. -/
theorem lawFamilyAdvantage_le_of_common_fTransform
    {I J A B : Type*}
    (P Q : I → Dist A) (P₀ Q₀ : J → Dist B)
    (hQ₀ : ∀ j, (Q₀ j).NonNeg)
    (hbounded : BddAbove ((fun j => δ (P₀ j) (Q₀ j)) '' Set.univ))
    (normalize : I → J) (reconstruct : I → B → A)
    (hP : ∀ i, P i = Dist.fTransform (reconstruct i) (P₀ (normalize i)))
    (hQ : ∀ i, Q i = Dist.fTransform (reconstruct i) (Q₀ (normalize i))) :
    lawFamilyAdvantage P Q ≤ lawFamilyAdvantage P₀ Q₀ := by
  unfold lawFamilyAdvantage
  refine RandomSystems.sSup_image_univ_le_of_forall _
    (RandomSystems.sSup_image_univ_nonneg_of_forall _ hbounded
      (fun j => δ_nonneg _ _)) ?_
  intro i
  rw [hP i, hQ i]
  exact (δ_fTransform_le (reconstruct i) _ (hQ₀ (normalize i))).trans
    (le_csSup hbounded ⟨normalize i, Set.mem_univ _, rfl⟩)

/-- Restricted form of `lawFamilyAdvantage_le_of_common_fTransform`: the
normalization is required to land in `Allowed`, so the right-hand supremum
ranges only over the allowed target indices. -/
theorem lawFamilyAdvantage_le_restricted_of_common_fTransform
    {I J A B : Type*}
    (Allowed : J → Prop) (P Q : I → Dist A) (P₀ Q₀ : J → Dist B)
    (hQ₀ : ∀ j, (Q₀ j).NonNeg)
    (hbounded : BddAbove
      ((fun j => δ (P₀ j) (Q₀ j)) '' {j | Allowed j}))
    (normalize : I → J) (hAllowed : ∀ i, Allowed (normalize i))
    (reconstruct : I → B → A)
    (hP : ∀ i, P i = Dist.fTransform (reconstruct i) (P₀ (normalize i)))
    (hQ : ∀ i, Q i = Dist.fTransform (reconstruct i) (Q₀ (normalize i))) :
    lawFamilyAdvantage P Q ≤ restrictedLawFamilyAdvantage Allowed P₀ Q₀ := by
  unfold lawFamilyAdvantage restrictedLawFamilyAdvantage
  refine RandomSystems.sSup_image_univ_le_of_forall _
    (Real.sSup_nonneg (by
      rintro x ⟨j, -, rfl⟩
      exact δ_nonneg _ _)) ?_
  intro i
  rw [hP i, hQ i]
  exact (δ_fTransform_le (reconstruct i) _ (hQ₀ (normalize i))).trans
    (le_csSup hbounded ⟨normalize i, hAllowed i, rfl⟩)

/-- Restricting the index set can only decrease a law-family advantage. -/
theorem restrictedLawFamilyAdvantage_le
    {I A : Type*} (Allowed : I → Prop) (P Q : I → Dist A)
    (hbounded : BddAbove ((fun i => δ (P i) (Q i)) '' Set.univ)) :
    restrictedLawFamilyAdvantage Allowed P Q ≤ lawFamilyAdvantage P Q := by
  unfold restrictedLawFamilyAdvantage lawFamilyAdvantage
  refine Real.sSup_le ?_ (RandomSystems.sSup_image_univ_nonneg_of_forall _
    hbounded (fun i => δ_nonneg _ _))
  rintro x ⟨i, -, rfl⟩
  exact le_csSup hbounded ⟨i, Set.mem_univ _, rfl⟩

/-- **Restriction is WLOG from a common factorization.**  If every index
normalizes into `Allowed`, and both endpoint laws are common pushforwards of
their laws at that normalized index, unrestricted and restricted advantages
are equal. -/
theorem lawFamilyAdvantage_eq_restricted_of_common_fTransform
    {I A : Type*}
    (Allowed : I → Prop) (P Q : I → Dist A)
    (hQ : ∀ i, (Q i).NonNeg)
    (hbounded : BddAbove ((fun i => δ (P i) (Q i)) '' Set.univ))
    (normalize : I → I) (hAllowed : ∀ i, Allowed (normalize i))
    (reconstruct : I → A → A)
    (hPfactor : ∀ i,
      P i = Dist.fTransform (reconstruct i) (P (normalize i)))
    (hQfactor : ∀ i,
      Q i = Dist.fTransform (reconstruct i) (Q (normalize i))) :
    lawFamilyAdvantage P Q = restrictedLawFamilyAdvantage Allowed P Q := by
  have hrestricted : BddAbove
      ((fun i => δ (P i) (Q i)) '' {i | Allowed i}) := by
    obtain ⟨c, hc⟩ := hbounded
    exact ⟨c, by
      rintro x ⟨i, -, rfl⟩
      exact hc ⟨i, Set.mem_univ _, rfl⟩⟩
  apply le_antisymm
  · exact lawFamilyAdvantage_le_restricted_of_common_fTransform
      Allowed P Q P Q hQ hrestricted normalize hAllowed reconstruct
      hPfactor hQfactor
  · exact restrictedLawFamilyAdvantage_le Allowed P Q hbounded

/-- Finsupp-native form of the classical optimal-coupling lemma.  The ambient
carrier need not be finite: the construction transports the two laws to the
finite subtype of their support union, couples them there, and pushes the
joint back along the subtype embedding. -/
theorem optimal_coupling_exists_finsupp {A : Type*} {μ ν : Dist A}
    (hμnn : μ.NonNeg) (hνnn : ν.NonNeg)
    (hw : μ.weight = ν.weight) :
    ∃ Z : Dist (A × A),
      Z.NonNeg ∧
      Dist.fTransform Prod.fst Z = μ ∧
      Dist.fTransform Prod.snd Z = ν ∧
      Z.mass (fun p => p.1 ≠ p.2) = δ μ ν := by
  classical
  let F : Finset A := μ.support ∪ ν.support
  let μF : Dist {a : A // a ∈ F} :=
    Dist.ofFiniteMassFunction fun a => μ a.1
  let νF : Dist {a : A // a ∈ F} :=
    Dist.ofFiniteMassFunction fun a => ν a.1
  have hμ : Dist.fTransform Subtype.val μF = μ := by
    apply Finsupp.ext
    intro a
    by_cases ha : a ∈ F
    · let aF : {a : A // a ∈ F} := ⟨a, ha⟩
      simpa [μF, aF] using
        Dist.fTransform_injective_apply μF Subtype.val
          Subtype.val_injective aF
    · have hnot : a ∉ μ.support := fun h =>
        ha (Finset.mem_union_left ν.support h)
      have hne : ∀ (z : {x : A // x ∈ F}), Subtype.val z ≠ a := by
        intro z hza
        exact ha (hza ▸ z.property)
      have hzero : Dist.fTransform Subtype.val μF a = 0 :=
        Dist.fTransform_apply_of_forall_ne μF Subtype.val a hne
      rw [hzero, Finsupp.notMem_support_iff.mp hnot]
  have hν : Dist.fTransform Subtype.val νF = ν := by
    apply Finsupp.ext
    intro a
    by_cases ha : a ∈ F
    · let aF : {a : A // a ∈ F} := ⟨a, ha⟩
      simpa [νF, aF] using
        Dist.fTransform_injective_apply νF Subtype.val
          Subtype.val_injective aF
    · have hnot : a ∉ ν.support := fun h =>
        ha (Finset.mem_union_right μ.support h)
      have hne : ∀ (z : {x : A // x ∈ F}), Subtype.val z ≠ a := by
        intro z hza
        exact ha (hza ▸ z.property)
      have hzero : Dist.fTransform Subtype.val νF a = 0 :=
        Dist.fTransform_apply_of_forall_ne νF Subtype.val a hne
      rw [hzero, Finsupp.notMem_support_iff.mp hnot]
  have hμFnn : μF.NonNeg := fun a => by
    simpa [μF] using hμnn a.1
  have hνFnn : νF.NonNeg := fun a => by
    simpa [νF] using hνnn a.1
  have hwF : μF.weight = νF.weight := by
    rw [← Dist.weight_fTransform Subtype.val μF,
      ← Dist.weight_fTransform Subtype.val νF, hμ, hν, hw]
  obtain ⟨C, hC⟩ := RandomSystems.optimal_coupling_exists hμFnn hνFnn hwF
  let pairVal : ({a : A // a ∈ F} × {a : A // a ∈ F}) → A × A :=
    fun p => (p.1.1, p.2.1)
  let Z : Dist (A × A) := Dist.fTransform pairVal C.joint
  have hfst : Dist.fTransform Prod.fst Z = μ := by
    calc
      Dist.fTransform Prod.fst Z =
          Dist.fTransform (Prod.fst ∘ pairVal) C.joint := by
            dsimp [Z]
            rw [Dist.fTransform_comp]
      _ = Dist.fTransform (Subtype.val ∘ Prod.fst) C.joint := rfl
      _ = Dist.fTransform Subtype.val
          (Dist.fTransform Prod.fst C.joint) := by
            rw [Dist.fTransform_comp]
      _ = μ := by rw [C.marginal_fst, hμ]
  have hsnd : Dist.fTransform Prod.snd Z = ν := by
    calc
      Dist.fTransform Prod.snd Z =
          Dist.fTransform (Prod.snd ∘ pairVal) C.joint := by
            dsimp [Z]
            rw [Dist.fTransform_comp]
      _ = Dist.fTransform (Subtype.val ∘ Prod.snd) C.joint := rfl
      _ = Dist.fTransform Subtype.val
          (Dist.fTransform Prod.snd C.joint) := by
            rw [Dist.fTransform_comp]
      _ = ν := by rw [C.marginal_snd, hν]
  have hmass : Z.mass (fun p => p.1 ≠ p.2) =
      C.joint.mass (fun p => p.1 ≠ p.2) := by
    dsimp [Z]
    rw [Dist.mass_fTransform]
    exact Dist.mass_congr C.joint fun p => by simp [pairVal]
  have hpr : C.joint.mass (fun p => p.1 ≠ p.2) = C.prDisagree := by
    rw [Dist.mass_eq_sum, RandomSystems.DistCoupling.prDisagree,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.1 ≠ p.2 <;> simp [hp]
  have hδF : δ μF νF = RandomSystems.statDist μF νF :=
    (statDist_eq_δ_of_nonneg μF νF hνFnn).symm
  have hδ : δ μ ν = RandomSystems.statDist μF νF := by
    rw [← hμ, ← hν, δ_fTransform_eq_of_injective Subtype.val_injective μF hνFnn,
      hδF]
  refine ⟨Z, C.nonneg.fTransform _, hfst, hsnd, ?_⟩
  rw [hmass, hpr, ← hC, ← hδ]

theorem δ_eq_sum_of_support_subset {A : Type*} {μ : Dist A}
    {ν : Dist A} (hν : ν.NonNeg) {s : Finset A} (hs : μ.support ⊆ s) :
    δ μ ν = ∑ a ∈ s, max (μ a - ν a) 0 := by
  unfold δ
  rw [Finsupp.sum]
  refine Finset.sum_subset hs fun a _ ha => ?_
  rw [Finsupp.notMem_support_iff.mp ha]
  exact max_eq_right (by simpa using hν a)

/-- LanMau20 Lemma 2: for families supported on pairwise disjoint cells
of a partition, the statistical distance is additive,
`δ(Σᵢ Xᵢ, Σᵢ Yᵢ) = Σᵢ δ(Xᵢ, Yᵢ)`. -/
theorem δ_sum_of_disjoint_support {A ι : Type*} [DecidableEq A]
    {t : Finset ι} (Xf Yf : ι → Dist A)
    (hYnn : ∀ i ∈ t, (Yf i).NonNeg)
    (hdisj : (t : Set ι).PairwiseDisjoint
      fun i => (Xf i).support ∪ (Yf i).support) :
    δ (∑ i ∈ t, Xf i) (∑ i ∈ t, Yf i) = ∑ i ∈ t, δ (Xf i) (Yf i) := by
  classical
  have hsub : (∑ i ∈ t, Xf i).support
      ⊆ t.biUnion fun i => (Xf i).support ∪ (Yf i).support :=
    (Finsupp.support_finset_sum).trans
      (Finset.biUnion_mono fun i _ => Finset.subset_union_left)
  have hsumY : (∑ i ∈ t, Yf i : Dist A).NonNeg := fun a => by
    rw [Finsupp.finset_sum_apply]
    exact Finset.sum_nonneg fun i hi => hYnn i hi a
  rw [δ_eq_sum_of_support_subset hsumY hsub, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [δ_eq_sum_of_support_subset (hYnn i hi)
    (Finset.subset_union_left (s₂ := (Yf i).support))]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hcell : ∀ (Zf : ι → Dist A),
      (∀ j, (Zf j).support ⊆ (Xf j).support ∪ (Yf j).support) →
      (∑ j ∈ t, Zf j) a = Zf i a := by
    intro Zf hZ
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_single_of_mem i hi fun j hj hne => ?_
    refine Finsupp.notMem_support_iff.mp fun hmem => ?_
    exact Finset.disjoint_left.mp
      (hdisj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) (Ne.symm hne))
      ha (hZ j hmem)
  rw [hcell Xf fun j => Finset.subset_union_left,
    hcell Yf fun j => Finset.subset_union_right]

/-! ### Transcript distributions and equivalence
(thesis Defs 2.12, 2.17; Lemma 2.18) -/

/-- Thesis Def 2.12, fn. 5: `tr(S, e)` is "the `tr(·,e)`-transformation
of the distribution `S`" — presented, like the underlying
`PFunDDS.transcript`, as the distribution of the length-`n` transcript
prefix, for each `n`. -/
noncomputable def transcriptDist (S : PFunPDS X Y) (e : PFunDDS.DDE X Y)
    (n : ℕ) : Dist (List (X × Option Y)) :=
  Dist.fTransform (fun s => PFunDDS.transcript s e n) S

/-! ### From a system's source law to its transcript law

The H-technique is **not about transcripts** — it is about a pair of distributions
(`δ_hTechnique_ratio`).  A transcript law is simply one such distribution, so H plugs in
directly rather than through a transcript-specific restatement.

`transcriptDist S e n` is already a pushforward of `S`.  When `S` is itself presented as a
pushforward of a master sample space — a `functionEvaluator`, a domain-filtered system,
anything built by `fTransform` — one more `fTransform_comp` makes the transcript law a
pushforward of that source law.  Extra coins are simply coordinates of the master sample
space.

An augmented transcript and the plain transcript are two observations on this same source.
Their only structural obligation is the pointwise equation saying that stripping the richer
observation recovers the plain one.  `Dist.fTransform_comp_eq_of_pointwise` turns that equation
into the corresponding law equality; arbitrary-map DPI then forgets the extra information. -/

/-- **A transcript law is a pushforward of whatever coins the system is presented over.** -/
theorem transcriptDist_fTransform {Ω : Type*} (p : Dist Ω) (ψ : Ω → PFunDDS.DDS X Y)
    (e : PFunDDS.DDE X Y) (n : ℕ) :
    transcriptDist (Dist.fTransform ψ p) e n
      = Dist.fTransform (fun ω => PFunDDS.transcript (ψ ω) e n) p := by
  rw [transcriptDist, Dist.fTransform_comp]
  rfl

/-- Transcript distributions of non-negative laws are non-negative. -/
theorem transcriptDist_nonNeg {S : PFunPDS X Y} (hS : S.NonNeg)
    (e : PFunDDS.DDE X Y) (n : ℕ) : (transcriptDist S e n).NonNeg :=
  hS.fTransform _

/-- Thesis Def 2.17: two PDS are **equivalent**, `S ≡ T`, if they have
the same transcript distribution in every deterministic environment.
(The thesis notes that probabilistic environments yield the same
notion.) -/
def Equivalent (S T : PFunPDS X Y) : Prop :=
  ∀ (e : PFunDDS.DDE X Y) (n : ℕ),
    transcriptDist S e n = transcriptDist T e n

/-! ### CR18 cumulative observable behavior

CR18 Definitions 3.3 and 3.6--3.7 do not interact with a partial DDS `s`
directly: the environment interacts with `s⊥`, observes `⊥`, and a rejected
query is deleted before the next query reaches `s`.  Consequently the complete
observable behavior of a partial system must retain `Option Y` histories.

The successful-history kernel `PFunPDS.behavior` predates that distinction.  It
records conditional laws only along histories whose answers all lie in `Y`.
For partial systems this **provably** loses correlations revealed by a
rejected query — kernel-checked as
`AttainmentCounterexample.behaviorEq_not_equivalent_counterexample`: let `a`
and `b` be distinct inputs, let `Y` be a singleton, and make every length-two
input undefined.  Compare a half/half mixture with domains `{[], [a], [b]}`
and `{[]}` against a half/half mixture with domains `{[], [a]}` and
`{[], [b]}`.  Both successful-history kernels give mass `1/2` at each
one-query input and zero for every successful continuation
(`four_pattern_behavior_eq`).  Yet fixed queries `a, b` produce `s⊥` answer
laws supported respectively on `(some, none)/(none, none)` and
`(some, none)/(none, some)` (`four_pattern_not_equivalent`).

`ObservableBehavior` is CR18 Definition 3.20's cumulative description applied
to the actual resource view `s⊥`.  Equal-length input/output sequences are
packed as a list of pairs.  This also includes the empty cumulative behavior,
whose mass is the law's total weight. -/

/-- CR18 Definition 3.20 on the observable `s⊥` resource view: the system-side
mass of an attempted-query/optional-answer history.  It is independent of the
environment; CR18 Lemma 3.2 multiplies it by the environment-consistency
indicator to obtain a transcript mass. -/
abbrev ObservableBehavior (X : Type u) (Y : Type v) :=
  List (X × Option Y) → ℝ

/-- The cumulative observable behavior of a PDS, including rejected queries
as `none` and CR18 Definition 3.3's skipped-query state semantics. -/
noncomputable def observableBehavior (S : PFunPDS X Y) :
    ObservableBehavior X Y :=
  fun t => S.mass fun s =>
    ∀ k (hk : k < t.length),
      (PFunDDS.fullyDefined s).1
        (PFunDDS.transcriptInputs (t.take (k + 1)))
        = Part.some (t[k].2)

/-- Two PDSs have the same cumulative observable behavior. -/
def ObservableBehaviorEq (S T : PFunPDS X Y) : Prop :=
  observableBehavior S = observableBehavior T

/-- Transcript equivalence preserves total mass.  At prefix length zero every
deterministic system produces the same empty transcript, so the transcript law's
weight is exactly the representative PDS's weight. -/
theorem weight_eq_of_equivalent {S T : PFunPDS X Y} (h : Equivalent S T) :
    S.weight = T.weight := by
  have h0 := congrArg Dist.weight (h (fun _ => none) 0)
  simpa [transcriptDist, Dist.weight_fTransform] using h0

/-- Thesis Def 2.14's common-domain clause (the thesis notation `dom(S) = D`):
every support atom of the law presents the single deterministic domain `D`.
The thesis builds the clause into its PDS carrier; the repository keeps the
carrier unrestricted (`PFunPDS` is any finite-support law, Def 2.1's
generality) and imposes the clause as a hypothesis exactly where the sources
need it (Theorems 2.31/2.32/2.37 and the strict-metric equality).  This is
the tree's one — and only — definition of the clause. -/
def PFunPDS.HasFixedDomain (S : PFunPDS X Y) (D : Set (List X)) : Prop :=
  ∀ s ∈ S.support, PFunDDS.dom s = D

/-- Thesis fn. 6: a **non-adaptive** environment chooses every query
independently of the previous outputs — `e(yⁱ)` depends only on the
length `i` of `yⁱ`. -/
def NonAdaptive (e : PFunDDS.DDE X Y) : Prop :=
  ∀ y y' : List (Option Y), y.length = y'.length → e y = e y'

section NonAdaptiveSuffices

open PFunDDS

/-- Def 3.7 at a deterministic environment, forward half of the
prefix-value factorization: the `n`-query transcript satisfies the
**environment-side** consistency (the replayed queries, and the
stall-or-query-bound condition) and the **system-side** consistency (the
`s⊥`-answers along the prefix). -/
theorem transcript_consistent (s : DDS X Y) (e : DDE X Y) (n : ℕ) :
    ((∀ k (hk : k < (transcript s e n).length),
        e (((transcript s e n).take k)↓ᵧ)
          = some ((transcript s e n)[k].1)) ∧
      ((transcript s e n).length = n ∨
        ((transcript s e n).length < n ∧
          e ((transcript s e n)↓ᵧ) = none))) ∧
    ∀ k (hk : k < (transcript s e n).length),
      (fullyDefined s).1 (((transcript s e n).take (k + 1))↓ₓ)
        = Part.some ((transcript s e n)[k].2) := by
  induction n with
  | zero =>
      exact ⟨⟨fun k hk => absurd hk (by simp), Or.inl rfl⟩,
        fun k hk => absurd hk (by simp)⟩
  | succ n ih =>
      obtain ⟨⟨hq, hlen⟩, hs⟩ := ih
      rcases he : e ((transcript s e n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall he]
        exact ⟨⟨hq, Or.inr ⟨by rcases hlen with h | ⟨h, -⟩ <;> omega, he⟩⟩,
          hs⟩
      · have hln : (transcript s e n).length = n := by
          rcases hlen with h | ⟨-, hstall⟩
          · exact h
          · rw [hstall] at he; cases he
        rw [transcript_succ_fire he]
        refine ⟨⟨?_, Or.inl (by simp [hln])⟩, ?_⟩
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (transcript s e n).length with hk' | hk'
          · rw [List.take_append_of_le_length (le_of_lt hk'),
              List.getElem_append_left hk']
            exact hq k hk'
          · have hkeq : k = (transcript s e n).length := by omega
            subst hkeq
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_concat_length]
            · exact he
            · rfl
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (transcript s e n).length with hk' | hk'
          · rw [List.take_append_of_le_length (by omega),
              List.getElem_append_left hk']
            exact hs k hk'
          · have hkeq : k = (transcript s e n).length := by omega
            subst hkeq
            rw [List.take_of_length_le (by
                rw [List.length_append, List.length_singleton]),
              List.getElem_concat_length, transcriptInputs_append]
            · exact (Part.some_get _).symm
            · rfl

/-- Def 3.7 at a deterministic environment, backward half: the two
consistency conditions reconstruct the transcript. -/
theorem transcript_eq_of_consistent (s : DDS X Y) (e : DDE X Y) :
    ∀ (n : ℕ) (t : List (X × Option Y)),
      (∀ k (hk : k < t.length), e ((t.take k)↓ᵧ) = some (t[k].1)) →
      (t.length = n ∨ (t.length < n ∧ e (t↓ᵧ) = none)) →
      (∀ k (hk : k < t.length),
        (fullyDefined s).1 ((t.take (k + 1))↓ₓ) = Part.some (t[k].2)) →
      transcript s e n = t := by
  intro n
  induction n with
  | zero =>
      intro t _ hlen _
      rcases hlen with h | ⟨h, -⟩
      · rw [List.eq_nil_of_length_eq_zero h]
        rfl
      · omega
  | succ n ih =>
      intro t hq hlen hs
      rcases hlen with hl | ⟨hl, hstall⟩
      · have hnlt : n < t.length := by omega
        have h1 : transcript s e n = t.take n := by
          refine ih (t.take n) ?_
            (Or.inl (by rw [List.length_take]; omega)) ?_
          · intro k hk
            rw [List.length_take] at hk
            have hk' : k < t.length := by omega
            rw [List.take_take, min_eq_left (by omega : k ≤ n),
              List.getElem_take]
            exact hq k hk'
          · intro k hk
            rw [List.length_take] at hk
            have hk' : k < t.length := by omega
            rw [List.take_take, min_eq_left (by omega : k + 1 ≤ n),
              List.getElem_take]
            exact hs k hk'
        have hfire : e ((transcript s e n)↓ᵧ) = some (t[n].1) := by
          rw [h1]
          exact hq n hnlt
        rw [transcript_succ_fire hfire, h1]
        have hval := hs n hnlt
        rw [take_succ_get' t n hnlt, transcriptInputs_append,
          List.get_eq_getElem] at hval
        have hout : output (fullyDefined s)
            (((t.take n))↓ₓ ++ [t[n].1])
            (by simp [fullyDefined, dom]) = t[n].2 := by
          apply Part.get_eq_of_mem
          rw [hval]
          exact Part.mem_some _
        conv_rhs => rw [← List.take_length (l := t), hl,
          take_succ_get' t n hnlt, List.get_eq_getElem]
        congr 1
        exact congrArg (fun p => [p]) (Prod.ext rfl hout)
      · have h1 : transcript s e n = t := by
          refine ih t hq ?_ hs
          rcases Nat.lt_or_ge t.length n with h | h
          · exact Or.inr ⟨h, hstall⟩
          · exact Or.inl (by omega)
        rw [transcript_succ_stall (by rw [h1]; exact hstall), h1]

/-- For an environment-consistent prefix value, the transcript equation
is exactly the system-side consistency — the deterministic Lemma 3.2:
the environment factor is an indicator, the system factor is
environment-free. -/
theorem transcript_eq_iff_of_consistent {e : DDE X Y} {n : ℕ}
    {t : List (X × Option Y)}
    (hq : ∀ k (hk : k < t.length), e ((t.take k)↓ᵧ) = some (t[k].1))
    (hlen : t.length = n ∨ (t.length < n ∧ e (t↓ᵧ) = none))
    (s : DDS X Y) :
    transcript s e n = t ↔
      ∀ k (hk : k < t.length),
        (fullyDefined s).1 ((t.take (k + 1))↓ₓ) = Part.some (t[k].2) := by
  constructor
  · intro h
    subst h
    exact (transcript_consistent s e n).2
  · exact transcript_eq_of_consistent s e n t hq hlen

/-- The **fixed-query-list environment**: play the queries of `q` by
position, then stop.  Non-adaptive by construction — the thesis's
fn. 6 witness class. -/
def playQueries (q : List X) : DDE X Y := fun ys => q[ys.length]?

theorem play_queries_is_nonadaptive (q : List X) :
    NonAdaptive (playQueries (Y := Y) q) := by
  intro y y' h
  unfold playQueries
  rw [h]

/-- Every prefix value is environment-consistent for its own
fixed-query-list environment at its own length. -/
theorem play_queries_is_consistent (t : List (X × Option Y)) :
    ∀ k (hk : k < t.length),
      playQueries (t↓ₓ) ((t.take k)↓ᵧ) = some (t[k].1) := by
  intro k hk
  unfold playQueries
  rw [transcriptOutputs_length, List.length_take, min_eq_left (le_of_lt hk),
    List.getElem?_eq_getElem (by rw [transcriptInputs_length]; exact hk)]
  simp [transcriptInputs]

/-- Thesis Lemma 2.18: for equivalence it suffices that the transcript
distributions agree under all **non-adaptive** deterministic
environments.  (The thesis states this for PDS with a common domain;
here domains are observable through the `⊥`-answers of `s⊥`.)

The proof is the deterministic Lemma 3.2 factorization
(`transcript_eq_iff_of_consistent`): at each prefix value `t` the fiber
mass factors into an environment-only indicator and the system-only
consistency mass, and the latter is extracted by the non-adaptive
fixed-query-list environment `playQueries t↓ₓ`. -/
theorem transcript_equivalent_of_nonadaptive_transcript_equivalent
    {S T : PFunPDS X Y}
    (h : ∀ e : PFunDDS.DDE X Y, NonAdaptive e →
      ∀ n, transcriptDist S e n = transcriptDist T e n) :
    Equivalent S T := by
  intro e n
  ext t
  simp only [transcriptDist]
  rw [Dist.fTransform_apply_eq_mass, Dist.fTransform_apply_eq_mass]
  by_cases hE : (∀ k (hk : k < t.length),
      e ((t.take k)↓ᵧ) = some ((t[k]).1)) ∧
      (t.length = n ∨ (t.length < n ∧ e (t↓ᵧ) = none))
  · have hkey := h (playQueries (Y := Y) (t↓ₓ))
      (play_queries_is_nonadaptive _) t.length
    have happ := congrArg (fun d => d t) hkey
    simp only [transcriptDist, Dist.fTransform_apply_eq_mass] at happ
    have hred : ∀ R : PFunPDS X Y,
        R.mass (fun s => PFunDDS.transcript s e n = t)
          = R.mass (fun s =>
              PFunDDS.transcript s (playQueries (t↓ₓ)) t.length = t) := by
      intro R
      refine congrArg R.mass (funext fun s => propext ?_)
      rw [transcript_eq_iff_of_consistent hE.1 hE.2 s,
        transcript_eq_iff_of_consistent (play_queries_is_consistent t)
          (Or.inl rfl) s]
    rw [hred S, hred T]
    exact_mod_cast happ
  · have hz : ∀ R : PFunPDS X Y,
        R.mass (fun s => PFunDDS.transcript s e n = t) = 0 := by
      intro R
      unfold Dist.mass
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg]
      intro hcontra
      subst hcontra
      exact hE ⟨(transcript_consistent s e n).1.1,
        (transcript_consistent s e n).1.2⟩
    rw [hz S, hz T]

end NonAdaptiveSuffices

/-- Complete observability for the explicit CR18 partial-system model.  The
implication from observable behavior to transcript laws is the deterministic
factorization behind CR18 Lemma 3.2: transcript mass is an environment-
consistency indicator times the environment-independent system mass.  CR18
omits that lemma's proof.  The converse below is a Lean reconstruction using
the fixed-query environment for an observable atom; for histories containing
`none`, it is a model-level extension of the paper's successful cumulative
presentation rather than a verbatim separately named CR18 theorem.

Unlike thesis Lemma 2.18's common-domain presentation, this theorem covers
CR18 Definitions 3.3 and 3.6--3.7 literally: `none` is observable and a rejected
query is omitted from the state seen by later queries. -/
theorem behavior_equivalent_iff_transcript_equivalent
    (S T : PFunPDS.Prob X Y) :
    ObservableBehaviorEq S.val T.val ↔ Equivalent S.val T.val := by
  constructor
  · intro hbehavior e n
    ext t
    simp only [transcriptDist, Dist.fTransform_apply_eq_mass]
    by_cases hconsistent :
        (∀ k (hk : k < t.length),
          e (PFunDDS.transcriptOutputs (t.take k)) = some (t[k].1)) ∧
        (t.length = n ∨
          (t.length < n ∧ e (PFunDDS.transcriptOutputs t) = none))
    · have hfactor : ∀ R : PFunPDS X Y,
          R.mass (fun s => PFunDDS.transcript s e n = t)
            = observableBehavior R t := by
        intro R
        unfold observableBehavior
        exact congrArg R.mass (funext fun s => propext
          (transcript_eq_iff_of_consistent hconsistent.1 hconsistent.2 s))
      rw [hfactor S.val, hfactor T.val, congrFun hbehavior t]
    · have hzero : ∀ R : PFunPDS X Y,
          R.mass (fun s => PFunDDS.transcript s e n = t) = 0 := by
        intro R
        exact Dist.mass_eq_zero_of_forall_not R fun s htranscript =>
          hconsistent (htranscript ▸ (transcript_consistent s e n).1)
      rw [hzero S.val, hzero T.val]
  · intro htranscript
    funext t
    have hlaw := congrArg (fun d => d t)
      (htranscript
        (playQueries (Y := Y) (PFunDDS.transcriptInputs t)) t.length)
    simp only [transcriptDist, Dist.fTransform_apply_eq_mass] at hlaw
    have hfactor : ∀ R : PFunPDS X Y,
        R.mass (fun s =>
          PFunDDS.transcript s
            (playQueries (PFunDDS.transcriptInputs t)) t.length = t)
          = observableBehavior R t := by
      intro R
      unfold observableBehavior
      exact congrArg R.mass (funext fun s => propext
        (transcript_eq_iff_of_consistent
          (play_queries_is_consistent t) (Or.inl rfl) s))
    rw [hfactor S.val, hfactor T.val] at hlaw
    exact hlaw

/-! ### The optimal distinguishing advantage (thesis Def 2.26) -/

/-- Thesis Def 2.26: the **optimal distinguishing advantage**,
`Adv(S, T) := sup_e δ(tr(S,e), tr(T,e))`, the supremum over all
deterministic environments (and all prefix lengths; the thesis's
compatibility requirement is absorbed by the `⊥`-totalization `s⊥`). -/
noncomputable def Adv (S T : PFunPDS X Y) : ℝ :=
  sSup {a : ℝ | ∃ (e : PFunDDS.DDE X Y) (n : ℕ),
    a = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)}

/-- **Zero-defect H, one-sided and carrier-free.**

`Bad` itself determines the two cells of `ideal.support`: a supported point is bad when
`Bad a`, and good otherwise.  Coverage and disjointness are therefore logic internal to the
theorem, not obligations for its caller.

At zero ratio defect, the only pointwise hypothesis is dominance on the good cell.  No
normalization or `ideal.weight ≤ 1` hypothesis is needed: every good-cell contribution to
`δ ideal real` is zero, while every bad-cell contribution is at most its ideal mass. -/
theorem δ_hTechnique_le_on_good {A : Type*} (ideal real : Dist A) (Bad : A → Prop)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_good : ∀ a ∈ ideal.support, ¬ Bad a → ideal a ≤ real a) :
    δ ideal real ≤ probBad ideal Bad := by
  classical
  have hterm : ∀ a ∈ ideal.support,
      max (ideal a - real a) 0 ≤ if Bad a then ideal a else 0 := by
    intro a ha
    by_cases hbad : Bad a
    · rw [if_pos hbad]
      exact max_le (sub_le_self _ (h_real_nonneg a)) (h_ideal_nonneg a)
    · rw [if_neg hbad]
      exact max_le (sub_nonpos.mpr (h_good a ha hbad)) le_rfl
  calc
    δ ideal real
        = ∑ a ∈ ideal.support, max (ideal a - real a) 0 := rfl
    _ ≤ ∑ a ∈ ideal.support, (if Bad a then ideal a else 0) :=
      Finset.sum_le_sum hterm
    _ = probBad ideal Bad := rfl

/-- The plug-in form of zero-defect two-cell H.  Applying it exposes exactly the two
application-specific obligations: dominance on the supported good cell and an upper bound
on the ideal bad mass. -/
theorem δ_hTechnique_le_on_good_of_bad_le {A : Type*}
    (ideal real : Dist A) (Bad : A → Prop) (beta : ℝ)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_good : ∀ a ∈ ideal.support, ¬ Bad a → ideal a ≤ real a)
    (h_bad : probBad ideal Bad ≤ beta) :
    δ ideal real ≤ beta :=
  le_trans
    (δ_hTechnique_le_on_good ideal real Bad h_real_nonneg h_ideal_nonneg h_good)
    h_bad

/-- **The ratio-form H-coefficient bound, one-sided and carrier-free.**

`RandomSystems.hTechnique_ratio` needs `[Fintype A]`, because it symmetrises
`statDist` (`statDist_symm_of_eq_weight`) and sums over `Finset.univ`.  The
one-sided `δ` needs neither: it already sums over `ideal.support`, and no weight
equality is required.  So this version applies on the transcript carrier
`List (X × Option Y)`, which is *not* a `Fintype` — and that carrier is exactly
what thesis Def 2.26's `Adv` is built from.

`B` determines the good/bad partition of `ideal.support` automatically.  Consequently the
ratio is required only at supported good points, exactly those that occur in the defining
sum for `δ`.  The weight bound pays for the nonzero defect; use
`δ_hTechnique_le_on_good` at `eps = 0`, where it is unnecessary. -/
theorem δ_hTechnique_ratio {A : Type*} (ideal real : Dist A) (B : A → Prop) (eps : NNReal)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a ∈ ideal.support, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    δ ideal real ≤ probBad ideal B + eps := by
  classical
  have hterm : ∀ a ∈ ideal.support,
      max (ideal a - real a) 0 ≤ (if B a then ideal a else 0) + (eps : ℝ) * ideal a := by
    intro a ha
    have hnn := mul_nonneg eps.coe_nonneg (h_ideal_nonneg a)
    by_cases hb : B a
    · rw [if_pos hb]
      have h1 := h_real_nonneg a
      have h2 := h_ideal_nonneg a
      exact max_le (by linarith) (by linarith)
    · rw [if_neg hb, zero_add]
      exact max_le (sub_le_mul_of_one_sub_mul_le (h_ratio a ha hb)) hnn
  calc δ ideal real
      = ∑ a ∈ ideal.support, max (ideal a - real a) 0 := rfl
    _ ≤ ∑ a ∈ ideal.support, ((if B a then ideal a else 0) + (eps : ℝ) * ideal a) :=
        Finset.sum_le_sum hterm
    _ = probBad ideal B + (eps : ℝ) * ideal.weight := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
    _ ≤ probBad ideal B + eps := by
        have h := mul_le_mul_of_nonneg_left h_ideal_le eps.coe_nonneg
        rw [mul_one] at h
        linarith

/-- The plug-in ratio form: besides law nonnegativity and the subdistribution weight fact,
the caller supplies exactly the support-local good ratio and the ideal bad-mass estimate. -/
theorem δ_hTechnique_ratio_of_bad_le {A : Type*}
    (ideal real : Dist A) (Bad : A → Prop) (eps : NNReal) (beta : ℝ)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a ∈ ideal.support, ¬ Bad a → (1 - eps) * ideal a ≤ real a)
    (h_bad : probBad ideal Bad ≤ beta) :
    δ ideal real ≤ beta + eps := by
  calc
    δ ideal real ≤ probBad ideal Bad + eps :=
      δ_hTechnique_ratio ideal real Bad eps h_real_nonneg h_ideal_nonneg h_ideal_le h_ratio
    _ ≤ beta + eps := by gcongr

/-! ### `NonNeg` is load-bearing — unlike `Fintype`, `DecidableEq`, weight equality

Three hypotheses the `statDist` H-family carried turned out to be spellings, not
mathematics, and were removed.  `NonNeg` is **not** one of them: both non-negativity
hypotheses of `δ_hTechnique_ratio` are necessary, and the two theorems below are the
receipts.  This is Def 2.1's signed carrier showing through — `Dist A = A →₀ ℝ` genuinely
admits negative mass, so the restriction is content (see also the `δ` docstring's remark
about `μ.support`). -/

/-- Dropping `ideal.NonNeg` makes the H bound **false**: at `ideal = −1` on a bad point,
`δ = 0` but `probBad = −1`. -/
theorem ideal_nonneg_necessary :
    ¬ (∀ (ideal real : Dist Unit) (B : Unit → Prop) (eps : NNReal),
        real.NonNeg → ideal.weight ≤ 1 →
        (∀ a ∈ ideal.support, ¬ B a → (1 - (eps : ℝ)) * ideal a ≤ real a) →
        δ ideal real ≤ probBad ideal B + eps) := by
  intro h
  have key := h (Finsupp.single () (-1)) 0 (fun _ => True) 0
    (fun _ => le_refl 0)
    (by simp [Dist.weight, Finsupp.sum, Finsupp.support_single_ne_zero]) (by simp)
  rw [show δ (Finsupp.single () (-1) : Dist Unit) 0 = 0 by
        simp [δ, Finsupp.sum, Finsupp.support_single_ne_zero],
      show probBad (Finsupp.single () (-1) : Dist Unit) (fun _ => True) = -1 by
        simp [probBad, Dist.mass, Finsupp.sum, Finsupp.support_single_ne_zero]] at key
  norm_num at key

/-- Dropping `real.NonNeg` makes it false too: at `real = −1` on a bad point, `δ = 2`
while `probBad = 1`. -/
theorem real_nonneg_necessary :
    ¬ (∀ (ideal real : Dist Unit) (B : Unit → Prop) (eps : NNReal),
        ideal.NonNeg → ideal.weight ≤ 1 →
        (∀ a ∈ ideal.support, ¬ B a → (1 - (eps : ℝ)) * ideal a ≤ real a) →
        δ ideal real ≤ probBad ideal B + eps) := by
  intro h
  have key := h (Finsupp.single () 1) (Finsupp.single () (-1)) (fun _ => True) 0
    (by intro a; simp)
    (by simp [Dist.weight, Finsupp.sum, Finsupp.support_single_ne_zero]) (by simp)
  rw [show δ (Finsupp.single () (1:ℝ) : Dist Unit) (Finsupp.single () (-1)) = 2 by
        simp [δ, Finsupp.sum, Finsupp.support_single_ne_zero]; norm_num,
      show probBad (Finsupp.single () (1:ℝ) : Dist Unit) (fun _ => True) = 1 by
        simp [probBad, Dist.mass, Finsupp.sum, Finsupp.support_single_ne_zero]] at key
  norm_num at key

/-- **H-technique followed by deterministic observation** — `δ`-native companion to
`StatDist.hTechnique_ratio_fTransform`, whose `[Fintype]`/`statDist` hypotheses no
transcript carrier can meet.

Prove the ratio on the richer law, then strip its observation.  This is
`δ_fTransform_le` (thesis Lemma 2.7) composed with `δ_hTechnique_ratio`.
There is no separate augmented H-technique: the theorem accepts arbitrary
carriers and an arbitrary deterministic map.

Note the ratio hypothesis lives on the **richer** law, which is the point: the bad event
and the good-transcript ratio are both easier there, because the extra information is
exactly what makes the collision structure visible. -/
theorem δ_hTechnique_ratio_fTransform {A B : Type*} (ideal real : Dist A) (f : A → B)
    (Bad : A → Prop) (eps : NNReal)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a ∈ ideal.support, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    δ (Dist.fTransform f ideal) (Dist.fTransform f real) ≤ probBad ideal Bad + eps :=
  calc
    δ (Dist.fTransform f ideal) (Dist.fTransform f real)
        ≤ δ ideal real := δ_fTransform_le f ideal h_real_nonneg
    _ ≤ probBad ideal Bad + eps :=
      δ_hTechnique_ratio ideal real Bad eps h_real_nonneg h_ideal_nonneg h_ideal_le h_ratio

/-- **Zero-defect H followed by any deterministic observation.**  This is the generic
augmentation/stripping rule at the H layer: prove support-local dominance on the richer
laws, then use data processing.  It has no product, transcript, or weight assumption. -/
theorem δ_hTechnique_le_on_good_fTransform {A B : Type*}
    (ideal real : Dist A) (f : A → B) (Bad : A → Prop)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_good : ∀ a ∈ ideal.support, ¬ Bad a → ideal a ≤ real a) :
    δ (Dist.fTransform f ideal) (Dist.fTransform f real) ≤ probBad ideal Bad :=
  calc
    δ (Dist.fTransform f ideal) (Dist.fTransform f real)
        ≤ δ ideal real := δ_fTransform_le f ideal h_real_nonneg
    _ ≤ probBad ideal Bad :=
      δ_hTechnique_le_on_good ideal real Bad h_real_nonneg h_ideal_nonneg h_good

/-! ### The `statDist` H-family, `Fintype`-free

With the bridge in hand the family follows from its `δ` form by one rewrite.  These
lemmas are strictly weaker in hypotheses than their `StatDist.lean` counterparts:
no `[Fintype]`, and — for the ratio form — no `real.weight = ideal.weight`.

The weight equality was never H's either.  `StatDist.hTechnique_ratio` needs it only to
apply `statDist_symm_of_eq_weight`, i.e. to flip `statDist real ideal` into
`statDist ideal real`.  Stating the bound in the orientation the technique actually proves
— **ideal first**, thesis Def 2.4's asymmetric `δ` — removes the need entirely. -/

/-- **H-technique on `statDist`** without `Fintype` and without weight equality. -/
theorem statDist_hTechnique_ratio {A : Type*} (ideal real : Dist A) (B : A → Prop)
    (eps : NNReal) (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a ∈ ideal.support, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist ideal real ≤ probBad ideal B + eps := by
  rw [statDist_eq_δ_of_nonneg ideal real h_real_nonneg]
  exact δ_hTechnique_ratio ideal real B eps h_real_nonneg h_ideal_nonneg h_ideal_le h_ratio

/-- **Zero-defect H on `statDist`**, without `Fintype`, normalization, or a weight bound. -/
theorem statDist_hTechnique_le_on_good {A : Type*}
    (ideal real : Dist A) (Bad : A → Prop)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_good : ∀ a ∈ ideal.support, ¬ Bad a → ideal a ≤ real a) :
    RandomSystems.statDist ideal real ≤ probBad ideal Bad := by
  rw [statDist_eq_δ_of_nonneg ideal real h_real_nonneg]
  exact δ_hTechnique_le_on_good ideal real Bad h_real_nonneg h_ideal_nonneg h_good

/-- **Data processing for `statDist`** without `Fintype` or `DecidableEq` — thesis Lemma
2.7 transported across the bridge. -/
theorem statDist_fTransform_le_of_nonneg {A B : Type*} (f : A → B) (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) :
    RandomSystems.statDist (Dist.fTransform f μ) (Dist.fTransform f ν)
      ≤ RandomSystems.statDist μ ν := by
  rw [statDist_eq_δ_of_nonneg _ _ (hν.fTransform f), statDist_eq_δ_of_nonneg _ _ hν]
  exact δ_fTransform_le f μ hν

/-- **H followed by deterministic observation on `statDist`**, `Fintype`-free: prove the
ratio on the richer law, then strip it.  The `δ` companion is
`δ_hTechnique_ratio_fTransform`. -/
theorem statDist_hTechnique_ratio_fTransform {A B : Type*} (ideal real : Dist A) (f : A → B)
    (Bad : A → Prop) (eps : NNReal) (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg) (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a ∈ ideal.support, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist (Dist.fTransform f ideal) (Dist.fTransform f real)
      ≤ probBad ideal Bad + eps :=
  le_trans (statDist_fTransform_le_of_nonneg f ideal h_real_nonneg)
    (statDist_hTechnique_ratio ideal real Bad eps h_real_nonneg h_ideal_nonneg
      h_ideal_le h_ratio)

/-- **The H-coefficient technique at thesis Def 2.26** — paper §3.3, stated on
`Adv` itself.

The hypotheses are per environment and prefix length, which is all §3.3 asks for;
there is no query bound, no verdict distinguisher, no `⊥`-elimination and no
fixed-query→adaptive transfer, because `Adv` is already a supremum of statistical
distances between transcript laws.

**Orientation.**  `Adv S T` is the one-sided excess *of `S` over `T`*, so `S` is
the **ideal** system here.  For HCTR2 that means `S = ±rnd` and `T =
HCTR2[Perm(n)]`, which is exactly how §3.3 orients its two bullets
(`Pr[Y = τ] ≤ Pr[X = τ]`, `Pr[Y ∈ 𝒯_bad] ≤ ε`, both about the ideal world `Y`). -/
theorem adv_le_of_ratio_of_good (S T : PFunPDS X Y)
    (Bad : List (X × Option Y) → Prop) (eps δb : NNReal)
    (h_real_nonneg : ∀ e n, (transcriptDist T e n).NonNeg)
    (h_ideal_nonneg : ∀ e n, (transcriptDist S e n).NonNeg)
    (h_ideal_le : ∀ e n, (transcriptDist S e n).weight ≤ 1)
    (h_ratio : ∀ e n a, a ∈ (transcriptDist S e n).support → ¬ Bad a →
      (1 - eps) * (transcriptDist S e n) a ≤ (transcriptDist T e n) a)
    (h_bad : ∀ e n, probBad (transcriptDist S e n) Bad ≤ δb) :
    Adv S T ≤ (δb : ℝ) + eps := by
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨e, n, rfl⟩
  exact δ_hTechnique_ratio_of_bad_le
    (transcriptDist S e n) (transcriptDist T e n) Bad eps (δb : ℝ)
    (h_real_nonneg e n) (h_ideal_nonneg e n) (h_ideal_le e n)
    (h_ratio e n) (h_bad e n)

/-- **Dominance-on-good form** at Def 2.26: the zero-defect two-cell H theorem.
The ideal weight bound disappears; only support-local good dominance and the ideal bad-mass
bound remain application-specific. -/
theorem adv_le_of_le_on_good (S T : PFunPDS X Y)
    (Bad : List (X × Option Y) → Prop) (δb : NNReal)
    (h_real_nonneg : ∀ e n, (transcriptDist T e n).NonNeg)
    (h_ideal_nonneg : ∀ e n, (transcriptDist S e n).NonNeg)
    (h_le : ∀ e n a, a ∈ (transcriptDist S e n).support → ¬ Bad a →
      (transcriptDist S e n) a ≤ (transcriptDist T e n) a)
    (h_bad : ∀ e n, probBad (transcriptDist S e n) Bad ≤ δb) :
    Adv S T ≤ (δb : ℝ) := by
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨e, n, rfl⟩
  exact δ_hTechnique_le_on_good_of_bad_le
    (transcriptDist S e n) (transcriptDist T e n) Bad (δb : ℝ)
    (h_real_nonneg e n) (h_ideal_nonneg e n) (h_le e n) (h_bad e n)

/-- Proof plumbing for Def 2.26's remark: rebuild the transcript prefix
from the answer history alone — the queries are the environment's own
replies, so the prefix is a function of the outputs.  A stalled
environment absorbs further answers (`replay_of_stall`), which is what
makes the accept-set distinguisher's verdict final. -/
def replay (e : PFunDDS.DDE X Y) (ys : List (Option Y)) :
    List (X × Option Y) :=
  ys.foldl (fun t y =>
    match e (PFunDDS.transcriptOutputs t) with
    | some x => t ++ [(x, y)]
    | none => t) []

section AcceptSet

open PFunDDS

private theorem foldl_eq_self_of_fix {α β : Type*} {f : α → β → α} {a : α}
    (hfix : ∀ c, f a c = a) : ∀ l : List β, List.foldl f a l = a := by
  intro l
  induction l with
  | nil => rfl
  | cons c l ih => rw [List.foldl_cons, hfix, ih]

/-- A stalled environment absorbs any further answers: the replay is
frozen. -/
theorem replay_eq_of_stall {e : PFunDDS.DDE X Y} {ys ys' : List (Option Y)}
    (h : e (PFunDDS.transcriptOutputs (replay e ys)) = none)
    (hpre : ys <+: ys') : replay e ys' = replay e ys := by
  obtain ⟨t, rfl⟩ := hpre
  unfold replay
  rw [List.foldl_append]
  refine foldl_eq_self_of_fix (fun y => ?_) t
  show (match e (PFunDDS.transcriptOutputs (replay e ys)) with
    | some x => replay e ys ++ [(x, y)]
    | none => replay e ys) = replay e ys
  rw [h]

/-- The replay is faithful on true transcripts: from the output
projection of `tr(s,e) k` it rebuilds `tr(s,e) k` itself. -/
theorem replay_transcript_outputs (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE X Y) :
    ∀ k : ℕ, replay e ((PFunDDS.transcript s e k)↓ᵧ)
      = PFunDDS.transcript s e k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rcases he : e ((PFunDDS.transcript s e k)↓ᵧ) with _ | x
      · rw [transcript_succ_stall he, ih]
      · rw [transcript_succ_fire he, transcriptOutputs_append]
        unfold replay
        rw [List.foldl_append, List.foldl_cons]
        show (match e (PFunDDS.transcriptOutputs (replay e _)) with
          | some x' => replay e _ ++ [(x', _)]
          | none => replay e _) = _
        rw [ih, he]

/-- The distinguisher of an environment (Def 2.26's remark): replay `e`
for at most `n` steps, then verdict by whether the observed prefix lies
in the accept set.  (The paper describes the object without naming
it.) -/
noncomputable def _root_.RandomSystems.CR18.PFunDDS.DDD.ofDDE
    (e : DDE X Y) (n : ℕ)
    (A : List (X × Option Y) → Bool) : DDD X Y :=
  ⟨fun ys =>
    if ys.length < n then
      match e ((replay e ys)↓ᵧ) with
      | some x => Sum.inl x
      | none => Sum.inr (A (replay e ys))
    else Sum.inr (A (replay e (ys.take n))), by
    intro ys ys' hpre b0 hb
    dsimp only at hb ⊢
    by_cases hlt : ys.length < n
    · rw [if_pos hlt] at hb
      rcases hm : e ((replay e ys)↓ᵧ) with _ | x <;> rw [hm] at hb
      · have hb' : A (replay e ys) = b0 := Sum.inr.inj hb
        have hys' : replay e ys' = replay e ys := replay_eq_of_stall hm hpre
        by_cases hlt' : ys'.length < n
        · rw [if_pos hlt', hys', hm, hb']
        · rw [if_neg hlt',
            replay_eq_of_stall hm (List.prefix_take_iff.mpr ⟨hpre, hlt.le⟩),
            hb']
      · exact absurd hb (by simp)
    · rw [if_neg hlt] at hb
      have hge : n ≤ ys.length := not_lt.mp hlt
      have htake : ys'.take n = ys.take n := by
        obtain ⟨t, rfl⟩ := hpre
        exact List.take_append_of_le_length hge
      rw [if_neg (not_lt.mpr (le_trans hge hpre.length_le)), htake]
      exact hb⟩

-- private copy (public original lives downstream in `CompatibleMetric`)
private theorem transcript_stall_of_length_lt' {s : DDS X Y} {e : DDE X Y} :
    ∀ {n : ℕ}, (transcript s e n).length < n →
      e ((transcript s e n)↓ᵧ) = none := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro hlen
      rcases he : e ((transcript s e n)↓ᵧ) with _ | x
      · rwa [transcript_succ_stall he]
      · exfalso
        rw [transcript_succ_fire he, List.length_append] at hlen
        have hstall := ih (by simpa using hlen)
        rw [hstall] at he
        simp at he

/-- The induced environment of `DDD.ofDDE`, in closed form: `e`'s own
move on the replayed prefix below the query bound, silence at the
bound. -/
theorem ddToDDE_ofDDE (e : DDE X Y) (n : ℕ)
    (A : List (X × Option Y) → Bool) (ys : List (Option Y)) :
    ddToDDE (DDD.ofDDE e n A) ys
      = if ys.length < n then e ((replay e ys)↓ᵧ) else none := by
  unfold ddToDDE DDD.ofDDE
  by_cases hlt : ys.length < n
  · rw [if_pos hlt]
    dsimp only
    rw [if_pos hlt]
    rcases e ((replay e ys)↓ᵧ) with _ | x <;> rfl
  · rw [if_neg hlt]
    dsimp only
    rw [if_neg hlt]

/-- Below the query bound, `DDD.ofDDE` generates `e`'s own transcript. -/
theorem transcript_ofDDE (e : DDE X Y) (n : ℕ)
    (A : List (X × Option Y) → Bool) (s : DDS X Y) :
    ∀ {k : ℕ}, k ≤ n →
      transcript s (ddToDDE (DDD.ofDDE e n A)) k = transcript s e k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hih := ih (Nat.le_of_succ_le hk)
      have hlen : ((transcript s e k)↓ᵧ).length < n := by
        rw [transcriptOutputs_length]
        exact lt_of_le_of_lt (transcript_length_le k) (Nat.lt_of_succ_le hk)
      have henv : ddToDDE (DDD.ofDDE e n A) ((transcript s e k)↓ᵧ)
          = e ((transcript s e k)↓ᵧ) := by
        rw [ddToDDE_ofDDE, if_pos hlen, replay_transcript_outputs]
      rcases he : e ((transcript s e k)↓ᵧ) with _ | x
      · rw [transcript_succ_stall (by rw [hih, henv]; exact he),
          transcript_succ_stall he, hih]
      · rw [transcript_succ_fire (by rw [hih, henv]; exact he),
          transcript_succ_fire he, hih]

/-- The verdict of `DDD.ofDDE e n A` is exactly `A` at `e`'s `n`-query
transcript — against every system. -/
theorem verdict_ofDDE_iff (e : DDE X Y) (n : ℕ)
    (A : List (X × Option Y) → Bool) (s : DDS X Y) :
    verdict (DDD.ofDDE e n A) s ↔ A (transcript s e n) = true := by
  have hstop : ddToDDE (DDD.ofDDE e n A)
      ((transcript s (ddToDDE (DDD.ofDDE e n A)) n)↓ᵧ) = none := by
    rw [transcript_ofDDE e n A s le_rfl, ddToDDE_ofDDE]
    rcases lt_or_ge (transcript s e n).length n with hlt | hge
    · rw [if_pos (by rwa [transcriptOutputs_length]),
        replay_transcript_outputs]
      exact transcript_stall_of_length_lt' hlt
    · rw [if_neg (by rw [transcriptOutputs_length]; omega)]
  -- the verdict value at the `n`-query history
  have hval : (DDD.ofDDE e n A).val
      ((transcript s (ddToDDE (DDD.ofDDE e n A)) n)↓ᵧ)
      = Sum.inr (A (transcript s e n)) := by
    rw [transcript_ofDDE e n A s le_rfl]
    show (if ((transcript s e n)↓ᵧ).length < n then _ else _) = _
    rcases lt_or_ge (transcript s e n).length n with hlt | hge
    · rw [if_pos (by rwa [transcriptOutputs_length]),
        replay_transcript_outputs,
        transcript_stall_of_length_lt' hlt]
    · rw [if_neg (by rw [transcriptOutputs_length]; omega),
        List.take_of_length_le
          (by rw [transcriptOutputs_length]; exact transcript_length_le n),
        replay_transcript_outputs]
  constructor
  · rintro ⟨k, hk⟩
    rcases le_total k n with hkn | hnk
    · rw [transcript_ofDDE e n A s hkn] at hk
      have hk2 : (if ((transcript s e k)↓ᵧ).length < n then
          match e ((replay e ((transcript s e k)↓ᵧ))↓ᵧ) with
          | some x => Sum.inl x
          | none => Sum.inr (A (replay e ((transcript s e k)↓ᵧ)))
          else Sum.inr (A (replay e (((transcript s e k)↓ᵧ).take n))))
          = Sum.inr true := hk
      by_cases hlt : ((transcript s e k)↓ᵧ).length < n
      · rw [if_pos hlt, replay_transcript_outputs] at hk2
        rcases he : e ((transcript s e k)↓ᵧ) with _ | x <;> rw [he] at hk2
        · rw [transcript_freeze he hkn]
          exact Sum.inr.inj hk2
        · exact absurd hk2 (by simp)
      · have hlen := transcript_length_le (s := s) (e := e) k
        rw [transcriptOutputs_length] at hlt
        have hkeq : k = n := le_antisymm hkn (le_trans (not_lt.mp hlt) hlen)
        subst hkeq
        rw [if_neg (by rwa [transcriptOutputs_length]),
          List.take_of_length_le (by rw [transcriptOutputs_length]; omega),
          replay_transcript_outputs] at hk2
        exact Sum.inr.inj hk2
    · rw [transcript_freeze hstop hnk, hval] at hk
      exact Sum.inr.inj hk
  · intro hA
    exact ⟨n, by rw [hval, hA]⟩

/-- Transcript prefixes are nested along the query count. -/
theorem transcript_prefix_of_le (s : DDS X Y) (e : DDE X Y) :
    ∀ {k n : ℕ}, k ≤ n → transcript s e k <+: transcript s e n := by
  intro k n
  induction n with
  | zero =>
      intro hk
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact List.prefix_refl _
  | succ n ih =>
      intro hk
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · refine (ih (Nat.lt_succ_iff.mp hlt)).trans ?_
        rcases he : e ((transcript s e n)↓ᵧ) with _ | x
        · rw [transcript_succ_stall he]
        · rw [transcript_succ_fire he]
          exact List.prefix_append _ _
      · obtain rfl : k = n + 1 := le_antisymm hk hge
        exact List.prefix_refl _

/-- Two total history evaluators have the same adaptive transcript whenever
their answers agree on every nonempty prefix of the first evaluator's final
query history.  This is the deterministic replay bridge used by
history-dependent tape couplings: the environment receives the same answer at
each prefix and therefore asks the same next query. -/
theorem transcript_historyEvaluator_eq_of_prefix_agree
    (left right : (history : List X) → history ≠ [] → Y)
    (environment : DDE X Y) (n : ℕ)
    (agree : ∀ history (nonempty : history ≠ []),
      history <+: transcriptInputs
        (transcript (historyEvaluator left) environment n) →
      left history nonempty = right history nonempty) :
    transcript (historyEvaluator left) environment n =
      transcript (historyEvaluator right) environment n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      let leftSystem := historyEvaluator left
      let rightSystem := historyEvaluator right
      have inputsPrefix :
          transcriptInputs (transcript leftSystem environment n) <+:
            transcriptInputs (transcript leftSystem environment (n + 1)) := by
        exact (transcript_prefix_of_le leftSystem environment
          (Nat.le_succ n)).map Prod.fst
      have prefixAgreement : ∀ history (nonempty : history ≠ []),
          history <+: transcriptInputs (transcript leftSystem environment n) →
          left history nonempty = right history nonempty := by
        intro history nonempty isPrefix
        exact agree history nonempty (isPrefix.trans inputsPrefix)
      have previousEqual :
          transcript leftSystem environment n =
            transcript rightSystem environment n := by
        simpa [leftSystem, rightSystem] using
          inductionHypothesis prefixAgreement
      cases queryStep : environment
          (transcriptOutputs (transcript leftSystem environment n)) with
      | none =>
          rw [transcript_succ_stall queryStep]
          have rightStall : environment
              (transcriptOutputs (transcript rightSystem environment n)) = none := by
            rw [← previousEqual]
            exact queryStep
          rw [transcript_succ_stall rightStall, previousEqual]
      | some query =>
          rw [transcript_succ_fire queryStep]
          have rightFire : environment
              (transcriptOutputs (transcript rightSystem environment n)) =
                some query := by
            rw [← previousEqual]
            exact queryStep
          rw [transcript_succ_fire rightFire, previousEqual]
          congr 2
          apply congrArg (fun answer => (query, answer))
          let prior := transcriptInputs (transcript rightSystem environment n)
          let history := prior ++ [query]
          have nonempty : history ≠ [] := by simp [history]
          have historyIsFull : history =
              transcriptInputs
                (transcript leftSystem environment (n + 1)) := by
            rw [transcript_succ_fire queryStep, transcriptInputs_append,
              previousEqual]
          have answerAgree : left history nonempty = right history nonempty :=
            agree history nonempty (historyIsFull ▸ List.prefix_refl _)
          have priorLeft : prior ∈ dom leftSystem ∨ prior = [] := by
            by_cases empty : prior = []
            · exact Or.inr empty
            · left
              change prior ≠ []
              exact empty
          have priorRight : prior ∈ dom rightSystem ∨ prior = [] := by
            by_cases empty : prior = []
            · exact Or.inr empty
            · left
              change prior ≠ []
              exact empty
          have nextLeft : history ∈ dom leftSystem := by
            change history ≠ []
            exact nonempty
          have nextRight : history ∈ dom rightSystem := by
            change history ≠ []
            exact nonempty
          rw [output_fullyDefined_append_of_mem leftSystem prior query
                priorLeft nextLeft,
            output_fullyDefined_append_of_mem rightSystem prior query
                priorRight nextRight,
            historyEvaluator_output, historyEvaluator_output]
          change some (left history nonempty) = some (right history nonempty)
          rw [answerAgree]

/-- Every length up to the `n`-query transcript's is attained at some
smaller query count, as its prefix. -/
theorem exists_transcript_eq_take (s : DDS X Y) (e : DDE X Y) :
    ∀ {n m : ℕ}, m ≤ (transcript s e n).length →
      ∃ j ≤ n, transcript s e j = (transcript s e n).take m := by
  intro n
  induction n with
  | zero =>
      intro m hm
      simp only [transcript_zero, List.length_nil, Nat.le_zero] at hm
      exact ⟨0, le_rfl, by simp [hm]⟩
  | succ n ih =>
      intro m hm
      rcases he : e ((transcript s e n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall he] at hm ⊢
        obtain ⟨j, hj, hje⟩ := ih hm
        exact ⟨j, le_trans hj (Nat.le_succ n), hje⟩
      · rw [transcript_succ_fire he] at hm ⊢
        rw [List.length_append, List.length_singleton] at hm
        rcases Nat.lt_or_ge m ((transcript s e n).length + 1) with hlt | hge
        · have hm' : m ≤ (transcript s e n).length := Nat.lt_succ_iff.mp hlt
          obtain ⟨j, hj, hje⟩ := ih hm'
          exact ⟨j, le_trans hj (Nat.le_succ n),
            by rw [List.take_append_of_le_length hm', hje]⟩
        · have hmeq : m = (transcript s e n).length + 1 := le_antisymm hm hge
          refine ⟨n + 1, le_rfl, ?_⟩
          rw [transcript_succ_fire he, hmeq,
            List.take_of_length_le (by
              rw [List.length_append, List.length_singleton])]

/-- The `n`-query transcript is a **function of** the `(n + 1)`-query
transcript: when the longer prefix fired in every round drop its last
entry, otherwise the environment has already stalled and the two
agree.  (Plumbing for `δ_transcriptDist_mono`.) -/
theorem transcript_eq_of_transcript_succ (s : DDS X Y) (e : DDE X Y)
    (n : ℕ) :
    transcript s e n =
      if (transcript s e (n + 1)).length = n + 1
      then (transcript s e (n + 1)).dropLast
      else transcript s e (n + 1) := by
  rcases he : e ((transcript s e n)↓ᵧ) with _ | x
  · rw [transcript_succ_stall he,
      if_neg (Nat.ne_of_lt (Nat.lt_succ_of_le (transcript_length_le n)))]
  · rcases Nat.lt_or_ge (transcript s e n).length n with hlt | hge
    · rw [transcript_stall_of_length_lt' hlt] at he
      simp at he
    · have hlen : (transcript s e n).length = n :=
        le_antisymm (transcript_length_le n) hge
      rw [transcript_succ_fire he,
        if_pos (by rw [List.length_append, List.length_singleton, hlen])]
      simp

/-- The per-environment advantage is monotone in the transcript length
(LanMau20 Theorem 1, the query-count comparison): the shorter
transcript is a
pushforward of the longer one, so `δ_fTransform_le` applies. -/
theorem δ_transcriptDist_mono (S : PFunPDS X Y) {T : PFunPDS X Y}
    (hTnn : T.NonNeg) (e : DDE X Y) :
    Monotone fun n => δ (transcriptDist S e n) (transcriptDist T e n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have key : ∀ R : PFunPDS X Y,
      transcriptDist R e n
        = Dist.fTransform
            (fun t : List (X × Option Y) =>
              if t.length = n + 1 then t.dropLast else t)
            (transcriptDist R e (n + 1)) := by
    intro R
    unfold transcriptDist
    rw [Dist.fTransform_comp]
    congr 1
    funext s
    exact transcript_eq_of_transcript_succ s e n
  show δ (transcriptDist S e n) (transcriptDist T e n)
    ≤ δ (transcriptDist S e (n + 1)) (transcriptDist T e (n + 1))
  rw [key S, key T]
  exact δ_fTransform_le _ _ (transcriptDist_nonNeg hTnn e (n + 1))

-- private copy (`Dist`-level plumbing, `Finsupp.mapDomain_congr`; to be
-- upstreamed into `Dist.lean` once that file is free to rebuild)
private theorem fTransform_congr_of_support {A B : Type*} {f g : A → B}
    (μ : Dist A) (h : ∀ a ∈ μ.support, f a = g a) :
    Dist.fTransform f μ = Dist.fTransform g μ := by
  show Finsupp.mapDomain f μ = Finsupp.mapDomain g μ
  exact Finsupp.mapDomain_congr h

/-- If every equal-transcript identification made by `(e, n)` on a
support superset `F` is also made by `(e', n')`, then the `(e', n')`
transcript distributions are pushforwards of the `(e, n)` ones — the
relabeling replays a choice of `(e, n)`-representative through
`(e', n')` — so the advantage can only drop (`δ_fTransform_le`). -/
private theorem δ_transcriptDist_le_of_transcript_eq_imp
    {S T : PFunPDS X Y} {F : Finset (DDS X Y)} (hTnn : T.NonNeg)
    (hS : S.support ⊆ F) (hT : T.support ⊆ F)
    {e e' : DDE X Y} {n n' : ℕ}
    (h : ∀ u ∈ F, ∀ v ∈ F, transcript u e n = transcript v e n →
      transcript u e' n' = transcript v e' n') :
    δ (transcriptDist S e' n') (transcriptDist T e' n')
      ≤ δ (transcriptDist S e n) (transcriptDist T e n) := by
  classical
  have hkey : ∀ R : PFunPDS X Y, R.support ⊆ F →
      transcriptDist R e' n'
        = Dist.fTransform (fun t : List (X × Option Y) =>
            if ht : ∃ u, u ∈ F ∧ transcript u e n = t
            then transcript ht.choose e' n' else t)
          (transcriptDist R e n) := by
    intro R hR
    unfold transcriptDist
    rw [Dist.fTransform_comp]
    refine fTransform_congr_of_support R fun s hs => ?_
    have hex : ∃ u, u ∈ F ∧ transcript u e n = transcript s e n :=
      ⟨s, hR hs, rfl⟩
    show transcript s e' n'
      = if ht : ∃ u, u ∈ F ∧ transcript u e n = transcript s e n
        then transcript ht.choose e' n' else transcript s e n
    rw [dif_pos hex]
    exact (h _ hex.choose_spec.1 s (hR hs) hex.choose_spec.2).symm
  rw [hkey S hS, hkey T hT]
  exact δ_fTransform_le _ _ (transcriptDist_nonNeg hTnn e n)

/-- **Attainment** (LanMau20 §4.2, in place of the paper's `q`-query
induction): the optimal advantage `Adv` is attained at some environment
and query count.  The `δ`-value at `(e, n)` is determined by the
equal-transcript partition induced on the finite support union — two
pairs inducing the same partition relabel into each other, by
`δ_transcriptDist_le_of_transcript_eq_imp` both ways — so the `Adv` set
is finite and its supremum is a member. -/
theorem exists_adv_eq_δ_transcriptDist (S : PFunPDS X Y) {T : PFunPDS X Y}
    (hTnn : T.NonNeg) :
    ∃ (e : DDE X Y) (n : ℕ),
      Adv S T = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ) := by
  classical
  set F : Finset (DDS X Y) := S.support ∪ T.support with hF
  have hS : S.support ⊆ F := Finset.subset_union_left
  have hT : T.support ⊆ F := Finset.subset_union_right
  set relOf : DDE X Y × ℕ → F → F → Prop := fun p u v =>
    transcript u.1 p.1 p.2 = transcript v.1 p.1 p.2 with hrel
  have hcongr : ∀ p q : DDE X Y × ℕ, relOf p = relOf q →
      δ (transcriptDist S p.1 p.2) (transcriptDist T p.1 p.2)
        = δ (transcriptDist S q.1 q.2) (transcriptDist T q.1 q.2) := by
    intro p q hpq
    refine le_antisymm
      (δ_transcriptDist_le_of_transcript_eq_imp hTnn hS hT
        fun u hu v hv huv => ?_)
      (δ_transcriptDist_le_of_transcript_eq_imp hTnn hS hT
        fun u hu v hv huv => ?_)
    · exact (congrFun (congrFun hpq ⟨u, hu⟩) ⟨v, hv⟩).mpr huv
    · exact (congrFun (congrFun hpq ⟨u, hu⟩) ⟨v, hv⟩).mp huv
  set g : (F → F → Prop) → ℝ := fun rel =>
    if hp : ∃ p : DDE X Y × ℕ, relOf p = rel
    then (δ (transcriptDist S hp.choose.1 hp.choose.2)
            (transcriptDist T hp.choose.1 hp.choose.2) : ℝ)
    else 0 with hg
  have hsub : {a : ℝ | ∃ (e : DDE X Y) (n : ℕ),
        a = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)}
      ⊆ Set.range g := by
    rintro a ⟨e, n, rfl⟩
    refine ⟨relOf (e, n), ?_⟩
    have hex : ∃ p : DDE X Y × ℕ, relOf p = relOf (e, n) := ⟨(e, n), rfl⟩
    simp only [hg]
    rw [dif_pos hex]
    exact_mod_cast hcongr hex.choose (e, n) hex.choose_spec
  have hfin : Set.Finite {a : ℝ | ∃ (e : DDE X Y) (n : ℕ),
      a = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)} :=
    (Set.finite_range g).subset hsub
  have hne : Set.Nonempty {a : ℝ | ∃ (e : DDE X Y) (n : ℕ),
      a = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)} :=
    ⟨_, (fun _ => none), 0, rfl⟩
  exact hne.csSup_mem hfin

open Classical in
/-- Against a system whose stop-witness lies under the query bound,
the verdict is a test on the `n`-query prefix value: some stage of it is a
stopped-with-`1` history. -/
theorem verdict_iff_exists_take {d : DDD X Y} {r : DDS X Y} {n : ℕ}
    (hwit : ∀ hv : verdict d r, Nat.find hv < n) :
    verdict d r ↔
      ∃ m ≤ (transcript r (ddToDDE d) n).length,
        d.val (((transcript r (ddToDDE d) n).take m)↓ᵧ) = Sum.inr true := by
  classical
  constructor
  · intro hv
    have hk := Nat.find_spec hv
    have hpre := transcript_prefix_of_le r (ddToDDE d)
      (le_of_lt (hwit hv))
    refine ⟨(transcript r (ddToDDE d) (Nat.find hv)).length,
      hpre.length_le, ?_⟩
    rw [← List.prefix_iff_eq_take.mp hpre]
    exact hk
  · rintro ⟨m, hm, hval⟩
    obtain ⟨j, -, hje⟩ := exists_transcript_eq_take r (ddToDDE d) hm
    exact ⟨j, by rw [hje]; exact hval⟩

/-- The verdict probability of a deterministic distinguisher is the
mass of its verdict set. -/
theorem verdictProb_single (d : DDD X Y) (R : PFunPDS X Y) :
    verdictProb (Finsupp.single d 1) R = R.mass (verdict d) := by
  classical
  unfold verdictProb GamePerf.winProb Dist.mass
  rw [Finsupp.sum_single_index (by simp)]
  refine Finsupp.sum_congr fun s _ => ?_
  by_cases hv : verdict d s
  · rw [if_pos hv, if_pos hv]
    ring
  · rw [if_neg hv, if_neg hv]
    ring

/-- The verdict probability of `DDD.ofDDE e n A` is the mass of the
accept set under the `n`-query transcript distribution. -/
theorem verdictProb_ofDDE (e : DDE X Y) (n : ℕ)
    (A : List (X × Option Y) → Bool) (R : PFunPDS X Y) :
    verdictProb (Finsupp.single (DDD.ofDDE e n A) 1) R
      = (transcriptDist R e n).mass fun t => A t = true := by
  classical
  unfold verdictProb GamePerf.winProb
  rw [Finsupp.sum_single_index (by simp)]
  rw [transcriptDist, Dist.mass_fTransform]
  unfold Dist.mass
  refine Finsupp.sum_congr fun s _ => ?_
  by_cases hA : A (transcript s e n) = true
  · rw [if_pos ((verdict_ofDDE_iff e n A s).mpr hA), if_pos hA]
    ring
  · rw [if_neg (fun hv => hA ((verdict_ofDDE_iff e n A s).mp hv)),
      if_neg hA]
    ring

end AcceptSet

/-- The verdict probability is linear in the distinguisher mixture. -/
theorem verdictProb_eq_sum_single (D : Dist (PFunDDS.DDD X Y))
    (R : PFunPDS X Y) :
    verdictProb D R = D.sum fun d dp =>
      dp * verdictProb (Finsupp.single d 1) R := by
  unfold verdictProb GamePerf.winProb
  refine Finsupp.sum_congr fun d _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun s _ => ?_
  ring

/-- The mass gap on any set is dominated by `δ` (Def 2.4): the excess
concentrates where `μ` exceeds `ν` (for a non-negative second law). -/
theorem mass_sub_mass_le_δ {A : Type*} (μ : Dist A) {ν : Dist A}
    (hν : ν.NonNeg) (P : A → Prop) :
    ((μ.mass P : ℝ) : ℝ) - ((ν.mass P : ℝ) : ℝ) ≤ (δ μ ν : ℝ) := by
  classical
  unfold δ Dist.mass
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum]
  rw [Finset.sum_subset
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support),
    Finset.sum_subset
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support),
    Finset.sum_subset
      (Finset.subset_union_right : ν.support ⊆ μ.support ∪ ν.support)]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    by_cases hP : P a
    · rw [if_pos hP, if_pos hP]
      exact le_max_left _ _
    · rw [if_neg hP, if_neg hP]
      simpa using le_max_right (μ a - ν a) 0
  all_goals
    intro a _ ha
    have h0 := Finsupp.notMem_support_iff.mp ha
    first
      | (rw [h0]; exact max_eq_right (sub_nonpos.mpr (hν a)))
      | simp only [h0, ite_self]

/-- The defining set of `Adv` is bounded above by the first system's
weight (`δ_le_weight` through the transcript pushforward), for
non-negative laws. -/
theorem bddAbove_adv_set {S T : PFunPDS X Y}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) :
    BddAbove {a : ℝ | ∃ (e : PFunDDS.DDE X Y) (n : ℕ),
      a = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)} := by
  refine ⟨(S.weight : ℝ), ?_⟩
  rintro x ⟨e, n, rfl⟩
  have h := δ_le_weight (transcriptDist_nonNeg hSnn e n)
    (transcriptDist_nonNeg hTnn e n)
  rw [transcriptDist, Dist.weight_fTransform] at h
  exact_mod_cast h

-- private copy (the public lemma lives downstream in `CompatibleMetric`)
private theorem maxAdvantage_nonneg' (S T : PFunPDS X Y) : 0 ≤ Δ(S, T) := by
  have hzero : advantage (rejectDistinguisher X Y) S T = 0 := by
    have hfalse : ∀ s : PFunDDS.DDS X Y,
        ¬ PFunDDS.verdict (PFunDDS.rejectDDD X Y) s := by
      rintro s ⟨n, hn⟩
      exact Bool.noConfusion (Sum.inr.inj hn)
    have hv : ∀ R : PFunPDS X Y,
        verdictProb (rejectDistinguisher X Y) R = 0 := by
      intro R
      unfold verdictProb GamePerf.winProb rejectDistinguisher
      rw [Finsupp.sum_single_index (by simp), Finsupp.sum]
      exact Finset.sum_eq_zero fun s _ => by
        rw [if_neg (hfalse s), mul_zero]
    unfold advantage
    rw [hv S, hv T]
    simp
  calc (0 : ℝ) = advantage (rejectDistinguisher X Y) S T := hzero.symm
    _ ≤ Δ(S, T) := advantage_le_maxAdvantage _ _ _
        (rejectDistinguisher_isProbDist X Y)

/-- The `≤` half of Def 2.26's remark: every transcript excess is
attained by its accept-set distinguisher. -/
theorem adv_le_maxAdvantage_swap (S : PFunPDS X Y) {T : PFunPDS X Y}
    (hTnn : T.NonNeg) : Adv S T ≤ Δ(T, S) := by
  classical
  refine Real.sSup_le ?_ (maxAdvantage_nonneg' T S)
  rintro x ⟨e, n, rfl⟩
  set A : List (X × Option Y) → Bool :=
    fun t => decide ((transcriptDist T e n) t < (transcriptDist S e n) t)
    with hA
  have hsingle : Dist.isProbDist
      (Finsupp.single (PFunDDS.DDD.ofDDE e n A) (1 : ℝ)) :=
    Dist.isProbDist_single _
  have hadv := advantage_le_maxAdvantage
    (Finsupp.single (PFunDDS.DDD.ofDDE e n A) 1) T S hsingle
  unfold advantage at hadv
  rw [verdictProb_ofDDE, verdictProb_ofDDE] at hadv
  have hpred : (fun t => A t = true)
      = fun t => (transcriptDist T e n) t < (transcriptDist S e n) t :=
    funext fun t => by rw [hA]; exact decide_eq_true_eq
  rw [hpred, ← δ_eq_mass_sub_mass _ (transcriptDist_nonNeg hTnn e n)] at hadv
  exact hadv

/-- Thesis Def 2.26, accompanying remark: "in the information-theoretic
setting, this is equivalent to the classical definition as the supremum
difference of the probability that a (probabilistic) distinguisher
outputs 1 when interacting with each system" — the verdict-based
`maxAdvantage`.

**Orientation.**  `Adv S T` is the one-sided `δ` excess *of `S` over
`T`*, attained by distinguishers scoring `S`; in the repository's signed
convention (`advantage D S T = Pr^{DT} − Pr^{DS}`) that supremum is
`Δ(T, S)`.  At sub-distribution weights the orientation is forced, not
cosmetic: for `S = 0` one has `Adv 0 T = 0` (the zero transcript
distribution has no excess) while `Δ(0, T) = T`'s weight (the
immediate-accept distinguisher) — so the naive pairing `Adv S T =
Δ(S, T)` is refutable.  For probability systems the two orientations
agree (`maxAdvantage_comm`). -/
theorem adv_eq_maxAdvantage_swap {S T : PFunPDS X Y}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) :
    Adv S T = Δ(T, S) := by
  classical
  refine le_antisymm (adv_le_maxAdvantage_swap S hTnn) ?_
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  have hd_bound : ∀ d ∈ D.support,
      ((verdictProb (Finsupp.single d 1) S : ℝ) : ℝ)
        - ((verdictProb (Finsupp.single d 1) T : ℝ) : ℝ)
        ≤ Adv S T := by
    intro d _
    set nd : ℕ := 1 + (S.support ∪ T.support).sup
      (fun r => if hv : PFunDDS.verdict d r then Nat.find hv else 0)
      with hnd
    have hwit : ∀ r ∈ S.support ∪ T.support,
        ∀ hv : PFunDDS.verdict d r, Nat.find hv < nd := by
      intro r hr hv
      have hle := Finset.le_sup (f := fun r =>
        if hv : PFunDDS.verdict d r then Nat.find hv else 0) hr
      dsimp only at hle
      rw [dif_pos hv] at hle
      omega
    have hmass : ∀ R : PFunPDS X Y, R.support ⊆ S.support ∪ T.support →
        R.mass (PFunDDS.verdict d)
          = (transcriptDist R (PFunDDS.ddToDDE d) nd).mass fun t =>
              ∃ m ≤ t.length,
                d.val (PFunDDS.transcriptOutputs (t.take m))
                  = Sum.inr true := by
      intro R hR
      rw [transcriptDist, Dist.mass_fTransform]
      unfold Dist.mass
      refine Finsupp.sum_congr fun r hr => ?_
      by_cases hv : PFunDDS.verdict d r
      · rw [if_pos hv,
          if_pos ((verdict_iff_exists_take (hwit r (hR hr))).mp hv)]
      · rw [if_neg hv, if_neg (fun hq =>
          hv ((verdict_iff_exists_take (hwit r (hR hr))).mpr hq))]
    rw [verdictProb_single, verdictProb_single,
      hmass S Finset.subset_union_left, hmass T Finset.subset_union_right]
    refine le_trans (mass_sub_mass_le_δ _ (transcriptDist_nonNeg hTnn _ _) _) ?_
    exact le_csSup (bddAbove_adv_set hSnn hTnn) ⟨PFunDDS.ddToDDE d, nd, rfl⟩
  unfold advantage
  rw [verdictProb_eq_sum_single D S, verdictProb_eq_sum_single D T,
    Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.sum_le_sum (g := fun d => ((D d : ℝ) : ℝ)
      * Adv S T) fun d hd => ?_) ?_
  · rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (hd_bound d hd) (hD.nonNeg d)
  · rw [← Finset.sum_mul]
    have hw : (∑ d ∈ D.support, ((D d : ℝ) : ℝ)) = 1 := by
      have hw0 : (D.sum fun _ w => w) = 1 := by
        rw [← Dist.weight_eq_finsupp_sum]
        exact hD.weight_eq
      rw [Finsupp.sum] at hw0
      exact hw0
    rw [hw, one_mul]

/-! ### Successor systems (LanMau20 §4.2, Notation 7) -/

section Successor

open Classical in
/-- LanMau20 Notation 7: the **successor system** `s↑x` "behaves like
`s` after the first query `x` has been input" — `s↑x(x̂ⁱ) := s(x‖x̂ⁱ)`
when `s` answers the first query `x`; the empty history stays outside
the domain.  When `x` is `⊥`-answered, CR18 Def 3.3's skip semantics
apply: `s⊥` deletes the undefined query and leaves the state of `s`
unchanged, so the successor is `s` itself. -/
noncomputable def _root_.PFunDDS.DDS.successor (s : PFunDDS.DDS X Y) (x : X) :
    PFunDDS.DDS X Y :=
  if [x] ∈ PFunDDS.dom s then
  ⟨fun l => if l = [] then Part.none else s.1 (x :: l), by
    constructor
    · intro h
      rw [PFun.mem_dom] at h
      simp at h
    · intro l₁ l₂ hpre hne h₂
      have h₂' : x :: l₂ ∈ s.1.Dom := by
        rw [PFun.mem_dom] at h₂ ⊢
        by_cases hl₂ : l₂ = []
        · rw [if_pos hl₂] at h₂
          simp at h₂
        · rwa [if_neg hl₂] at h₂
      rw [PFun.mem_dom]
      rw [if_neg hne, ← PFun.mem_dom]
      exact s.2.2 (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩)
        (List.cons_ne_nil x l₁) h₂'⟩
  else s

/-- LanMau20 Notation 7 for environments: the successor environment
`e↑y(ŷⁱ) := e(y‖ŷⁱ)` continues `e` after it has received the first
answer `y` (with the `s⊥`-semantics the answer alphabet is `Y ∪ {⊥}`,
so `y : Option Y`). -/
def _root_.PFunDDS.DDE.successor (e : PFunDDS.DDE X Y) (y : Option Y) :
    PFunDDS.DDE X Y :=
  fun ys => e (y :: ys)

open Classical in
/-- LanMau20 Notation 7: `S↑x↓y` is "the transformation of `S` with the
partial function `s ↦ s↑x↓y`", where `s↑x↓y` equals `s↑x` if `s(x) = y`
and is undefined otherwise — keep exactly the systems whose first
`s⊥`-answer to `x` is `y` (the ⊥-answer is an ordinary case of
`y : Option Y`), and step each survivor to its successor.  Its weight
is the probability that `S` answers `y` to the first query `x` — in
general a strict sub-distribution. -/
noncomputable def successorTransform (S : PFunPDS X Y) (x : X)
    (y : Option Y) : PFunPDS X Y :=
  Dist.fTransform (fun s => PFunDDS.DDS.successor s x)
    (S.filter fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = y)

/-- LanMau20 Notation 7 / CR18 Def 3.3: on a `⊥`-answered first query
the state is unchanged — `s↑x = s` when `s(x)` is undefined. -/
theorem successor_of_not_mem {s : PFunDDS.DDS X Y} {x : X}
    (hx : [x] ∉ PFunDDS.dom s) :
    PFunDDS.DDS.successor s x = s := by
  unfold PFunDDS.DDS.successor
  rw [if_neg hx]

/-- LanMau20 Notation 7 pointwise, answered case: on nonempty histories
`s↑x(x̂ⁱ) = s(x‖x̂ⁱ)`. -/
theorem successor_apply_of_mem {s : PFunDDS.DDS X Y} {x : X}
    (hx : [x] ∈ PFunDDS.dom s) {l : List X} (hl : l ≠ []) :
    (PFunDDS.DDS.successor s x).1 l = s.1 (x :: l) := by
  unfold PFunDDS.DDS.successor
  rw [if_pos hx]
  exact if_neg hl

/-- LanMau20 Notation 7 at the domain level, answered case: `s↑x` is
defined on a nonempty history exactly when `s` is defined on its
`x`-extension. -/
theorem mem_dom_successor_iff {s : PFunDDS.DDS X Y} {x : X}
    (hx : [x] ∈ PFunDDS.dom s) {m : List X} (hm : m ≠ []) :
    m ∈ PFunDDS.dom (PFunDDS.DDS.successor s x) ↔ x :: m ∈ PFunDDS.dom s :=
  iff_of_eq (congrArg Part.Dom (successor_apply_of_mem hx hm))

open Classical in
/-- CR18 Def 3.3's bookkeeping through one query: the kept prefix of
`x‖m` keeps `x` exactly when `s` answers it, and the remainder is the
kept prefix of the successor system `s↑x`. -/
theorem keptPrefix_successor (s : PFunDDS.DDS X Y) (x : X) (m : List X) :
    PFunDDS.keptPrefix s (x :: m)
      = (if [x] ∈ PFunDDS.dom s then [x] else [])
          ++ PFunDDS.keptPrefix (PFunDDS.DDS.successor s x) m := by
  by_cases hx : [x] ∈ PFunDDS.dom s
  · rw [if_pos hx]
    have haux : ∀ (m acc : List X),
        List.foldl (fun acc q =>
            if acc ++ [q] ∈ PFunDDS.dom s then acc ++ [q] else acc)
          (x :: acc) m
          = x :: List.foldl (fun acc q =>
              if acc ++ [q] ∈ PFunDDS.dom (PFunDDS.DDS.successor s x)
              then acc ++ [q] else acc) acc m := by
      intro m
      induction m with
      | nil => intro acc; rfl
      | cons q m ihm =>
          intro acc
          simp only [List.foldl_cons]
          have hstep : (if (x :: acc) ++ [q] ∈ PFunDDS.dom s
                then (x :: acc) ++ [q] else x :: acc)
              = x :: (if acc ++ [q] ∈ PFunDDS.dom (PFunDDS.DDS.successor s x)
                  then acc ++ [q] else acc) := by
            by_cases hq : acc ++ [q] ∈ PFunDDS.dom (PFunDDS.DDS.successor s x)
            · have hq' : (x :: acc) ++ [q] ∈ PFunDDS.dom s :=
                (mem_dom_successor_iff hx (by simp)).mp hq
              rw [if_pos hq', if_pos hq, List.cons_append]
            · have hq' : (x :: acc) ++ [q] ∉ PFunDDS.dom s := fun hmem =>
                hq ((mem_dom_successor_iff hx (by simp)).mpr hmem)
              rw [if_neg hq', if_neg hq]
          rw [hstep, ihm]
    simp only [PFunDDS.keptPrefix, List.foldl_cons, List.nil_append]
    rw [if_pos hx]
    exact haux m []
  · rw [if_neg hx, successor_of_not_mem hx, List.nil_append]
    simp only [PFunDDS.keptPrefix, List.foldl_cons, List.nil_append]
    rw [if_neg hx]

open Classical in
/-- The pointwise heart of the LanMau20 §4.2 decomposition: after the
first query `x`, the fully defined completion `s⊥` answers exactly as
`(s↑x)⊥` — on answered queries by Notation 7's shift, on `⊥`-answered
queries by CR18 Def 3.3's skip semantics. -/
theorem output_fullyDefined_successor (s : PFunDDS.DDS X Y) (x : X) {l : List X}
    (h : l ∈ PFunDDS.dom (PFunDDS.fullyDefined (PFunDDS.DDS.successor s x)))
    (h' : x :: l ∈ PFunDDS.dom (PFunDDS.fullyDefined s)) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.DDS.successor s x)) l h
      = PFunDDS.output (PFunDDS.fullyDefined s) (x :: l) h' := by
  have hl : l ≠ [] := by
    have hmem := h
    rw [PFunDDS.dom_fullyDefined] at hmem
    exact hmem
  by_cases hx : [x] ∈ PFunDDS.dom s
  · have key : ∀ (c : List X), c ≠ [] →
        (if hcand : c ∈ PFunDDS.dom (PFunDDS.DDS.successor s x) then
          some (PFunDDS.output (PFunDDS.DDS.successor s x) c hcand)
        else none)
          = (if hcand : x :: c ∈ PFunDDS.dom s then
              some (PFunDDS.output s (x :: c) hcand)
            else none) := by
      intro c hc
      by_cases hmem : c ∈ PFunDDS.dom (PFunDDS.DDS.successor s x)
      · rw [dif_pos hmem, dif_pos ((mem_dom_successor_iff hx hc).mp hmem)]
        refine congrArg some (Part.mem_unique ?_ (Part.get_mem _))
        rw [← successor_apply_of_mem hx hc]
        exact Part.get_mem hmem
      · rw [dif_neg hmem,
          dif_neg fun hmem' => hmem ((mem_dom_successor_iff hx hc).mpr hmem')]
    simp only [PFunDDS.output_fullyDefined, List.dropLast_cons_of_ne_nil hl,
      List.getLast_cons hl, keptPrefix_successor, if_pos hx,
      List.cons_append]
    exact key (PFunDDS.keptPrefix (PFunDDS.DDS.successor s x) l.dropLast
      ++ [l.getLast hl]) (by simp)
  · simp only [PFunDDS.output_fullyDefined, List.dropLast_cons_of_ne_nil hl,
      List.getLast_cons hl, keptPrefix_successor, successor_of_not_mem hx,
      if_neg hx, List.nil_append]

/-- CR18 Def 3.7 through LanMau20 §4.2: one transcript step splits off
the head entry `(x, s⊥(x))` and continues as the transcript of the
successor system against the successor environment. -/
theorem transcript_successor (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE X Y) {x : X}
    (he : e [] = some x) (n : ℕ) :
    PFunDDS.transcript s e (n + 1)
      = (x, PFunDDS.output (PFunDDS.fullyDefined s) [x]
            (by rw [PFunDDS.dom_fullyDefined]; simp)) ::
          PFunDDS.transcript (PFunDDS.DDS.successor s x)
            (PFunDDS.DDE.successor e
              (PFunDDS.output (PFunDDS.fullyDefined s) [x]
                (by rw [PFunDDS.dom_fullyDefined]; simp))) n := by
  have key : ∀ y₀ : Option Y,
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y₀ →
      ∀ m : ℕ, PFunDDS.transcript s e (m + 1)
        = (x, y₀) :: PFunDDS.transcript (PFunDDS.DDS.successor s x)
            (PFunDDS.DDE.successor e y₀) m := by
    intro y₀ hy₀ m
    induction m with
    | zero =>
        have h0 : e (PFunDDS.transcriptOutputs (PFunDDS.transcript s e 0))
            = some x := he
        rw [transcript_succ_fire h0, ← hy₀]
        rfl
    | succ m ih =>
        cases hfire : PFunDDS.DDE.successor e y₀
            (PFunDDS.transcriptOutputs (PFunDDS.transcript
              (PFunDDS.DDS.successor s x) (PFunDDS.DDE.successor e y₀) m)) with
        | none =>
            have hstall : e (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s e (m + 1))) = none := by
              rw [ih]; exact hfire
            rw [transcript_succ_stall hstall, transcript_succ_stall hfire]
            exact ih
        | some x' =>
            have hfire' : e (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s e (m + 1))) = some x' := by
              rw [ih]; exact hfire
            rw [transcript_succ_fire hfire', transcript_succ_fire hfire]
            simp only [ih, PFunDDS.transcriptInputs, List.map_cons,
              List.cons_append]
            rw [(output_fullyDefined_successor s x
              (l := List.map Prod.fst (PFunDDS.transcript
                (PFunDDS.DDS.successor s x) (PFunDDS.DDE.successor e y₀) m)
                ++ [x'])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              (by rw [PFunDDS.dom_fullyDefined]; simp)).symm]
  exact key _ rfl n

/-- Fibering an event mass over the values of a statistic: if `V`
covers the image of `g` on the support, the mass of `P` splits into the
masses of `P` on the fibers `g = v`. -/
private theorem mass_eq_sum_mass_fiber {A B : Type*} (μ : Dist A)
    (P : A → Prop) (g : A → B) (V : Finset B)
    (hV : ∀ a ∈ μ.support, g a ∈ V) :
    μ.mass P = ∑ v ∈ V, μ.mass fun a => P a ∧ g a = v := by
  unfold Dist.mass
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_eq_single_of_mem (g a) (hV a ha)
    fun v _ hv => if_neg fun hc => hv (hc.2.symm)]
  by_cases hP : P a
  · rw [if_pos hP, if_pos (show P a ∧ g a = g a from ⟨hP, rfl⟩)]
  · rw [if_neg hP, if_neg (show ¬(P a ∧ g a = g a) from fun hc => hP hc.1)]

/-- `Dist.mass_restrict` restated against `Finsupp.filter` with the
caller's decidability instance, so it rewrites filter-shaped statements
(Dist.lean's statement policy). -/
theorem mass_filter {A : Type*} (X : Dist A) (P Q : A → Prop)
    [DecidablePred P] :
    Dist.mass (X.filter P) Q = X.mass fun a => Q a ∧ P a := by
  unfold Dist.mass
  simp only [Finsupp.sum, Finsupp.support_filter, Finsupp.filter_apply]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

open Classical in
/-- LanMau20 §4.2, the Lemma 2 step of Theorem 1 at the transcript
level: the length-`(n+1)` transcript distribution partitions over the
first answer `y` — each summand is the cons-pushforward by `(x, y)` of
the length-`n` transcript distribution of the successor transformation
`S↑x↓y` against the successor environment `e↑y`. -/
theorem transcriptDist_successor (S : PFunPDS X Y) (e : PFunDDS.DDE X Y)
    {x : X} (he : e [] = some x) (n : ℕ) :
    transcriptDist S e (n + 1)
      = ∑ y ∈ S.support.image (fun s =>
            PFunDDS.output (PFunDDS.fullyDefined s) [x]
              (by rw [PFunDDS.dom_fullyDefined]; simp)),
          Dist.fTransform (fun t => (x, y) :: t)
            (transcriptDist (successorTransform S x y)
              (PFunDDS.DDE.successor e y) n) := by
  refine Finsupp.ext fun t => ?_
  rw [Finsupp.finset_sum_apply]
  refine Eq.trans (Dist.fTransform_apply_eq_mass _ _ _) ?_
  refine Eq.trans (mass_eq_sum_mass_fiber S _
    (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp)) _
    fun s hs => Finset.mem_image_of_mem _ hs) ?_
  refine Finset.sum_congr rfl fun y hy => ?_
  refine Eq.trans ?_ (Dist.fTransform_apply_eq_mass _ _ _).symm
  refine Eq.trans ?_ (Dist.mass_fTransform _ _ _).symm
  refine Eq.trans ?_ (Dist.mass_fTransform _ _ _).symm
  refine Eq.trans ?_ (mass_filter S _ _).symm
  refine Dist.mass_congr S fun s => ?_
  beta_reduce
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [transcript_successor s e he n, h2] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [transcript_successor s e he n, h2]
    exact h1

open Classical in
/-- LanMau20 Notation 7's weight remark: the weight of `S↑x↓y` is the
probability that `S`'s first answer to `x` is `y` — in general the
transformation produces a strict sub-distribution. -/
theorem weight_successorTransform (S : PFunPDS X Y) (x : X) (y : Option Y) :
    (successorTransform S x y).weight
      = S.mass fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp) = y := by
  refine Eq.trans (Dist.weight_fTransform _ _) ?_
  refine Eq.trans (Dist.mass_true _).symm ?_
  refine Eq.trans (mass_filter S _ _) ?_
  refine Dist.mass_congr S fun s => ?_
  beta_reduce
  exact iff_of_eq (true_and _)

/-! ### Prepending an initial query (thesis §2.4.2, Theorem 2.31 step 3) -/

/-- Thesis §2.4.2 (proof of Theorem 2.31, step 3): **prepend** an
initial query — `prepend x y s` answers the first query `x` with `y`
and then continues as `s`.  The answered case `y = some v` is the
paper construction: domain `{[x]} ∪ x‖dom s`, value `v` at `[x]`,
`s`'s value beyond, undefined at every other first query.  The
`⊥`-answer case `y = none` has no paper analogue (the thesis totalizes
over a finite alphabet): by CR18 Def 3.3's skip semantics a `⊥` at `x`
leaves the state unchanged, so the continuation is `s` itself,
unshifted, with the `x`-headed part of the domain carved out —
validity forces the carving, since `[x] ∉ dom` propagates to every
`x`-headed history by prefix closure. -/
def _root_.PFunDDS.DDS.prepend (x : X) (y : Option Y)
    (s : PFunDDS.DDS X Y) : PFunDDS.DDS X Y :=
  match y with
  | some v =>
      ⟨fun l => match l with
        | [] => Part.none
        | [x'] => ⟨x' = x, fun _ => v⟩
        | x' :: c :: m =>
            ⟨x' = x ∧ (s.1 (c :: m)).Dom, fun h => (s.1 (c :: m)).get h.2⟩,
       by
        constructor
        · exact fun h => h
        · intro l₁ l₂ hpre hne hdom
          obtain ⟨u, rfl⟩ := hpre
          cases l₁ with
          | nil => exact absurd rfl hne
          | cons a m =>
              cases m with
              | nil =>
                  cases u with
                  | nil => exact hdom
                  | cons c u' => exact hdom.1
              | cons c m' =>
                  exact ⟨hdom.1, s.2.2
                    (List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append m' u⟩)
                    (List.cons_ne_nil c m') hdom.2⟩⟩
  | none =>
      PFunDDS.filterDom (fun l => l.head? ≠ some x)
        (fun l₁ l₂ hpre h2 => by
          obtain ⟨u, rfl⟩ := hpre
          cases l₁ with
          | nil => simp
          | cons a m => exact h2)
        s

/-- The prepended query is answered: `[x] ∈ dom (prepend x y s)` for
`y = some v`. -/
theorem singleton_mem_dom_prepend_some (x : X) (v : Y) (s : PFunDDS.DDS X Y) :
    [x] ∈ PFunDDS.dom (PFunDDS.DDS.prepend x (some v) s) :=
  rfl

/-- The prepended query is `⊥`-answered: `[x] ∉ dom (prepend x none s)`. -/
theorem singleton_not_mem_dom_prepend_none (x : X) (s : PFunDDS.DDS X Y) :
    [x] ∉ PFunDDS.dom (PFunDDS.DDS.prepend x none s) :=
  fun h => h.2 rfl

/-- Thesis §2.4.2 step 3, answered case: the domain of `prepend x (some v) s`
is `{[x]} ∪ x‖dom s`. -/
theorem dom_prepend_some (x : X) (v : Y) (s : PFunDDS.DDS X Y) :
    PFunDDS.dom (PFunDDS.DDS.prepend x (some v) s)
      = {l : List X | l = [x] ∨ ∃ m ∈ PFunDDS.dom s, l = x :: m} := by
  ext l
  rcases l with _ | ⟨a, _ | ⟨c, m⟩⟩
  · exact iff_of_false (fun h => h)
      (by rintro (h | ⟨m, _, h⟩) <;> simp at h)
  · show a = x ↔ _
    constructor
    · rintro rfl
      exact Or.inl rfl
    · rintro (h | ⟨m', hm', h⟩) <;> exact (List.cons_eq_cons.mp h).1
  · show a = x ∧ (s.1 (c :: m)).Dom ↔ _
    constructor
    · rintro ⟨rfl, hD⟩
      exact Or.inr ⟨c :: m, hD, rfl⟩
    · rintro (h | ⟨m', hm', h⟩)
      · exact absurd h (by simp)
      · exact ⟨(List.cons_eq_cons.mp h).1,
          by rw [(List.cons_eq_cons.mp h).2]; exact hm'⟩

/-- Thesis §2.4.2 step 3, `⊥`-answer case: prepending a `⊥` carves the
`x`-headed histories out of the domain and keeps the rest. -/
theorem dom_prepend_none (x : X) (s : PFunDDS.DDS X Y) :
    PFunDDS.dom (PFunDDS.DDS.prepend x none s)
      = {l ∈ PFunDDS.dom s | l.head? ≠ some x} :=
  rfl

/-- CR18 Def 3.3 skip semantics, prepend side: on a system that does
not answer `x`, prepending the `⊥`-answer at `x` carves nothing —
`prepend x none s = s`.  (Every use site has this hypothesis for free:
a PDS equivalent to a `⊥`-branch successor transformation puts all its
mass on atoms that do not answer `x`.) -/
theorem prepend_none_of_not_mem {s : PFunDDS.DDS X Y} {x : X}
    (hx : [x] ∉ PFunDDS.dom s) :
    PFunDDS.DDS.prepend x none s = s := by
  refine Subtype.ext (funext fun l => ?_)
  refine Part.ext' ?_ fun h₁ h₂ => rfl
  show (s.1 l).Dom ∧ l.head? ≠ some x ↔ (s.1 l).Dom
  refine and_iff_left_of_imp fun hD heq => ?_
  cases l with
  | nil => simp at heq
  | cons a m =>
      have ha : a = x := Option.some.inj heq
      exact hx (PFunDDS.prefix_closed s
        (List.cons_prefix_cons.mpr ⟨ha.symm, List.nil_prefix⟩)
        (List.cons_ne_nil x []) hD)

/-- Thesis §2.4.2 step 3, the inversion law: after prepending `(x, v)`
the successor at `x` recovers `s` — `(prepend x (some v) s)↑x = s`. -/
theorem successor_prepend (x : X) (v : Y) (s : PFunDDS.DDS X Y) :
    PFunDDS.DDS.successor (PFunDDS.DDS.prepend x (some v) s) x = s := by
  refine Subtype.ext (funext fun l => ?_)
  cases l with
  | nil =>
      refine Part.ext'
        (iff_of_false (PFunDDS.empty_not_mem _) (PFunDDS.empty_not_mem s))
        fun h₁ _ => absurd h₁ (PFunDDS.empty_not_mem _)
  | cons a m =>
      rw [successor_apply_of_mem (singleton_mem_dom_prepend_some x v s)
        (List.cons_ne_nil a m)]
      refine Part.ext' ?_ fun h₁ h₂ => rfl
      show x = x ∧ (s.1 (a :: m)).Dom ↔ (s.1 (a :: m)).Dom
      exact and_iff_right rfl

/-- The inversion law in the `⊥`-answer case: the prepended `⊥` is a
skipped query (CR18 Def 3.3), so the successor at `x` recovers `s`
whenever `s` does not answer `x`. -/
theorem successor_prepend_none {s : PFunDDS.DDS X Y} {x : X}
    (hx : [x] ∉ PFunDDS.dom s) :
    PFunDDS.DDS.successor (PFunDDS.DDS.prepend x none s) x = s := by
  rw [prepend_none_of_not_mem hx, successor_of_not_mem hx]

/-- Thesis §2.4.2 step 3: the prepended system's first `s⊥`-answer to
`x` is exactly the prepended answer `y` (the `⊥` case included). -/
theorem output_fullyDefined_prepend (x : X) (y : Option Y)
    (s : PFunDDS.DDS X Y) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.DDS.prepend x y s)) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = y := by
  cases y with
  | some v =>
      exact PFunDDS.output_fullyDefined_append_of_mem
        (PFunDDS.DDS.prepend x (some v) s) [] x (Or.inr rfl)
        (singleton_mem_dom_prepend_some x v s)
  | none =>
      simp only [PFunDDS.output_fullyDefined]
      split
      · rename_i hmem
        exact absurd hmem (singleton_not_mem_dom_prepend_none x s)
      · rfl

/-- Thesis §2.4.2 step 3: prepending an **answered** query is injective
(`(prepend x (some v))↑x` is a left inverse), so its pushforward
preserves `δ`.  Prepending a `⊥` is *not* injective: validity forbids
storing the carved `x`-branch, so systems differing only there are
identified — on the systems the proof feeds it (`[x] ∉ dom s`) it is
the identity (`prepend_none_of_not_mem`). -/
theorem prepend_injective (x : X) (v : Y) :
    Function.Injective (PFunDDS.DDS.prepend x (some v)) :=
  Function.LeftInverse.injective
    (g := fun s => PFunDDS.DDS.successor s x)
    fun s => successor_prepend x v s

/-- Thesis §2.4.2 step 3 at the distribution level: `S′ₓᵧ` is the
`prepend x y`-transformation of a rebuilt representative. -/
noncomputable def prependTransform (S : PFunPDS X Y) (x : X)
    (y : Option Y) : PFunPDS X Y :=
  Dist.fTransform (PFunDDS.DDS.prepend x y) S

/-- On a PDS all of whose atoms `⊥`-answer `x`, prepending the
`⊥`-answer is the identity transformation. -/
theorem prependTransform_of_forall_not_mem {S : PFunPDS X Y} {x : X}
    (h : ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s) :
    prependTransform S x none = S :=
  Eq.trans (fTransform_congr_of_support (g := id) S
    fun s hs => prepend_none_of_not_mem (h s hs)) (Dist.fTransform_id S)

open Classical in
/-- Thesis §2.4.2 step 3, the round trip: `(S′ₓᵧ)↑x↓y = S` — the
successor transformation at `(x, y)` undoes the prepend
transformation.  Every prepended atom answers `y` first
(`output_fullyDefined_prepend`), so the filter keeps everything, and
the successor inverts the prepend atom-wise.  The `⊥`-answer case
needs the (use-site-free) hypothesis that no atom of `S` answers `x`. -/
theorem successorTransform_prependTransform (S : PFunPDS X Y) (x : X)
    (y : Option Y) (h : y = none → ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s) :
    successorTransform (prependTransform S x y) x y = S := by
  unfold successorTransform prependTransform
  have hfil : (Dist.fTransform (PFunDDS.DDS.prepend x y) S).filter
      (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y)
      = Dist.fTransform (PFunDDS.DDS.prepend x y) S := by
    refine Finsupp.ext fun t => ?_
    rw [Finsupp.filter_apply]
    by_cases ht : t ∈ (Dist.fTransform (PFunDDS.DDS.prepend x y) S).support
    · obtain ⟨s', hs', rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support ht)
      rw [if_pos (output_fullyDefined_prepend x y s')]
    · rw [Finsupp.notMem_support_iff.mp ht]
      exact ite_self 0
  rw [hfil, Dist.fTransform_comp]
  refine Eq.trans (fTransform_congr_of_support (g := id) S ?_)
    (Dist.fTransform_id S)
  intro s hs
  show PFunDDS.DDS.successor (PFunDDS.DDS.prepend x y s) x = s
  cases y with
  | some v => exact successor_prepend x v s
  | none => exact successor_prepend_none (h rfl s hs)

/-- Thesis §2.4.2 step 3: the prepend transformation preserves the
statistical distance (answered case; injectivity + `δ_fTransform_eq_of_injective`). -/
theorem δ_prependTransform (S : PFunPDS X Y) {T : PFunPDS X Y}
    (hTnn : T.NonNeg) (x : X) (v : Y) :
    δ (prependTransform S x (some v)) (prependTransform T x (some v))
      = δ S T :=
  δ_fTransform_eq_of_injective (prepend_injective x v) S hTnn

/-- The `⊥`-answer case of `δ_prependTransform`: on PDS whose atoms all
`⊥`-answer `x`, the prepend transformation is the identity, so `δ` is
trivially preserved. -/
theorem δ_prependTransform_none {S T : PFunPDS X Y} {x : X}
    (hS : ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s)
    (hT : ∀ t ∈ T.support, [x] ∉ PFunDDS.dom t) :
    δ (prependTransform S x none) (prependTransform T x none) = δ S T := by
  rw [prependTransform_of_forall_not_mem hS,
    prependTransform_of_forall_not_mem hT]

/-! ### Per-x reassembly (thesis §2.4.2, Theorem 2.31 steps 4–5) -/

/-- Distinct first answers give distinct prepended atoms: the first
`s⊥`-answer at `x` is part of the atom (`output_fullyDefined_prepend`),
whatever the continuations.  In particular a `⊥`-class atom never
collides with an answered-class atom (their domains differ at `[x]`),
and two answered classes never collide however their continuations
overlap. -/
theorem prepend_ne_of_ne {x : X} {y y' : Option Y} (h : y ≠ y')
    (s s' : PFunDDS.DDS X Y) :
    PFunDDS.DDS.prepend x y s ≠ PFunDDS.DDS.prepend x y' s' := by
  intro heq
  have h1 := output_fullyDefined_prepend x y s
  simp only [heq] at h1
  exact h (h1.symm.trans (output_fullyDefined_prepend x y' s'))

open Classical in
/-- The support of a prepend transformation consists of prepended
atoms. -/
theorem support_prependTransform_subset {S : PFunPDS X Y} {x : X}
    {y : Option Y} :
    (prependTransform S x y).support
      ⊆ S.support.image (PFunDDS.DDS.prepend x y) :=
  Finsupp.mapDomain_support

open Classical in
/-- Thesis §2.4.2 step 4: the classes of the per-`x` reassembly have
pairwise disjoint supports — every atom carries its first answer. -/
theorem pairwiseDisjoint_support_prependTransform
    (Sf Tf : Option Y → PFunPDS X Y) (x : X) (ys : Finset (Option Y)) :
    (↑ys : Set (Option Y)).PairwiseDisjoint fun y =>
      (prependTransform (Sf y) x y).support
        ∪ (prependTransform (Tf y) x y).support := by
  intro y _ y' _ hne
  refine Finset.disjoint_left.mpr fun t ht ht' => ?_
  have h1 : ∃ s, t = PFunDDS.DDS.prepend x y s := by
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (support_prependTransform_subset h)
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (support_prependTransform_subset h)
      exact ⟨s, rfl⟩
  have h2 : ∃ s', t = PFunDDS.DDS.prepend x y' s' := by
    rcases Finset.mem_union.mp ht' with h | h
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (support_prependTransform_subset h)
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (support_prependTransform_subset h)
      exact ⟨s, rfl⟩
  obtain ⟨s, rfl⟩ := h1
  obtain ⟨s', heq⟩ := h2
  exact prepend_ne_of_ne hne s s' heq

open Classical in
/-- Thesis §2.4.2 step 4 (LanMau20 Lemma 2 again): the statistical
distance of per-`x` reassemblies is the sum of the per-answer
distances — the classes are support-disjoint, prepending an answered
query preserves `δ` by injectivity, and the `⊥`-class prepend is the
identity on its pass-through support. -/
theorem δ_sum_prependTransform (Sf Tf : Option Y → PFunPDS X Y) (x : X)
    (ys : Finset (Option Y))
    (hTnn : ∀ y, (Tf y).NonNeg)
    (hS : none ∈ ys → ∀ s ∈ (Sf none).support, [x] ∉ PFunDDS.dom s)
    (hT : none ∈ ys → ∀ t ∈ (Tf none).support, [x] ∉ PFunDDS.dom t) :
    δ (∑ y ∈ ys, prependTransform (Sf y) x y)
        (∑ y ∈ ys, prependTransform (Tf y) x y)
      = ∑ y ∈ ys, δ (Sf y) (Tf y) := by
  refine Eq.trans (δ_sum_of_disjoint_support _ _
    (fun y _ => (hTnn y).fTransform _)
    (pairwiseDisjoint_support_prependTransform Sf Tf x ys)) ?_
  refine Finset.sum_congr rfl fun y hy => ?_
  cases y with
  | none => exact δ_prependTransform_none (hS hy) (hT hy)
  | some v => exact δ_prependTransform (Sf (some v)) (hTnn (some v)) x v

/-- The prepend transformation preserves weight (it is a pushforward). -/
theorem weight_prependTransform (S : PFunPDS X Y) (x : X) (y : Option Y) :
    (prependTransform S x y).weight = S.weight :=
  Dist.weight_fTransform _ _

private theorem weight_finset_sum {A : Type*} {ι : Type*} (t : Finset ι)
    (Rf : ι → Dist A) :
    (∑ i ∈ t, Rf i).weight = ∑ i ∈ t, (Rf i).weight := by
  rw [Dist.weight_eq_finsupp_sum,
    ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Finset.sum_congr rfl fun i _ => (Dist.weight_eq_finsupp_sum _).symm

/-- Thesis §2.4.2 step 5's bookkeeping: the reassembled PDS carries the
total weight of its classes. -/
theorem weight_sum_prependTransform (Sf : Option Y → PFunPDS X Y) (x : X)
    (ys : Finset (Option Y)) :
    (∑ y ∈ ys, prependTransform (Sf y) x y).weight
      = ∑ y ∈ ys, (Sf y).weight := by
  rw [weight_finset_sum]
  exact Finset.sum_congr rfl fun y _ => weight_prependTransform (Sf y) x y

open Classical in
private theorem successorTransform_finset_sum {ι : Type*} (t : Finset ι)
    (Rf : ι → PFunPDS X Y) (x : X) (y : Option Y) :
    successorTransform (∑ i ∈ t, Rf i) x y
      = ∑ i ∈ t, successorTransform (Rf i) x y := by
  show Finsupp.mapDomain (fun s => PFunDDS.DDS.successor s x)
      (Finsupp.filter (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y) (∑ i ∈ t, Rf i))
    = ∑ i ∈ t, Finsupp.mapDomain (fun s => PFunDDS.DDS.successor s x)
        (Finsupp.filter (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp) = y) (Rf i))
  rw [Finsupp.filter_sum, Finsupp.mapDomain_finset_sum]

open Classical in
/-- A prepended class answers only its own `y`: at any other first
answer the successor transformation of the class vanishes. -/
theorem successorTransform_prependTransform_of_ne {S : PFunPDS X Y}
    {x : X} {y y' : Option Y} (h : y ≠ y') :
    successorTransform (prependTransform S x y) x y' = 0 := by
  unfold successorTransform prependTransform
  have hfil : (Dist.fTransform (PFunDDS.DDS.prepend x y) S).filter
      (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y')
      = 0 := by
    refine Finsupp.ext fun t => ?_
    rw [Finsupp.filter_apply]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_cases ht : t ∈ (Dist.fTransform (PFunDDS.DDS.prepend x y) S).support
    · obtain ⟨s', _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support ht)
      rw [if_neg fun hP =>
        h ((output_fullyDefined_prepend x y s').symm.trans hP)]
    · rw [Finsupp.notMem_support_iff.mp ht, ite_self]
  rw [hfil]
  exact Finsupp.mapDomain_zero

open Classical in
/-- Thesis §2.4.2 step 5: the successor transformation at `(x, y)`
recovers the `y`-class of the per-`x` reassembly — the other classes
vanish and the `(x, y)`-round trip undoes the prepend. -/
theorem successorTransform_sum_prependTransform
    (Sf : Option Y → PFunPDS X Y) (x : X) (ys : Finset (Option Y))
    {y : Option Y} (hy : y ∈ ys)
    (hnone : y = none → ∀ s ∈ (Sf none).support, [x] ∉ PFunDDS.dom s) :
    successorTransform (∑ y' ∈ ys, prependTransform (Sf y') x y') x y
      = Sf y := by
  rw [successorTransform_finset_sum]
  rw [Finset.sum_eq_single_of_mem y hy
    fun y' _ hne => successorTransform_prependTransform_of_ne hne]
  exact successorTransform_prependTransform (Sf y) x y
    fun h => by subst h; exact hnone rfl

private theorem fTransform_zero {A B : Type*} (f : A → B) :
    Dist.fTransform f (0 : Dist A) = 0 :=
  Finsupp.mapDomain_zero

private theorem transcriptDist_finset_sum {ι : Type*} (t : Finset ι)
    (Rf : ι → PFunPDS X Y) (e : PFunDDS.DDE X Y) (n : ℕ) :
    transcriptDist (∑ i ∈ t, Rf i) e n
      = ∑ i ∈ t, transcriptDist (Rf i) e n := by
  show Finsupp.mapDomain (fun s => PFunDDS.transcript s e n) (∑ i ∈ t, Rf i)
    = ∑ i ∈ t, Finsupp.mapDomain (fun s => PFunDDS.transcript s e n) (Rf i)
  rw [Finsupp.mapDomain_finset_sum]

open Classical in
/-- Thesis §2.4.2 step 6 ingredient, per class: the transcript
distribution of one prepended class, in an environment opening with
`x`, is the `(x, y)`-cons pushforward of the class representative's
transcript distribution in the successor environment
(`transcriptDist_successor` read backwards through the round trip). -/
theorem transcriptDist_prependTransform (S : PFunPDS X Y) {x : X}
    (y : Option Y) {e : PFunDDS.DDE X Y} (he : e [] = some x)
    (hnone : y = none → ∀ s ∈ S.support, [x] ∉ PFunDDS.dom s) (n : ℕ) :
    transcriptDist (prependTransform S x y) e (n + 1)
      = Dist.fTransform (fun t => (x, y) :: t)
          (transcriptDist S (PFunDDS.DDE.successor e y) n) := by
  rcases eq_or_ne S 0 with rfl | hS0
  · simp only [prependTransform, transcriptDist, fTransform_zero]
  · have hne : (prependTransform S x y).support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      cases y with
      | none =>
          rw [prependTransform_of_forall_not_mem (hnone rfl)]
          exact hS0
      | some v =>
          intro h0
          exact hS0 ((Finsupp.mapDomain_injective (prepend_injective x v))
            (h0.trans Finsupp.mapDomain_zero.symm))
    rw [transcriptDist_successor (prependTransform S x y) e he n]
    have himg : (prependTransform S x y).support.image
        (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp)) = {y} := by
      refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨hne.image _, ?_⟩
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨s', _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support ht)
      exact output_fullyDefined_prepend x y s'
    rw [himg, Finset.sum_singleton,
      successorTransform_prependTransform S x y hnone]

open Classical in
/-- Thesis §2.4.2 step 6 ingredient: in an environment opening with
`x`, the transcript distribution of the per-`x` reassembly decomposes
into the per-answer cons-pushforwards of the class representatives'
transcript distributions in the successor environments. -/
theorem transcriptDist_sum_prependTransform
    (Sf : Option Y → PFunPDS X Y) (x : X) (ys : Finset (Option Y))
    {e : PFunDDS.DDE X Y} (he : e [] = some x)
    (hnone : none ∈ ys → ∀ s ∈ (Sf none).support, [x] ∉ PFunDDS.dom s)
    (n : ℕ) :
    transcriptDist (∑ y ∈ ys, prependTransform (Sf y) x y) e (n + 1)
      = ∑ y ∈ ys, Dist.fTransform (fun t => (x, y) :: t)
          (transcriptDist (Sf y) (PFunDDS.DDE.successor e y) n) := by
  rw [transcriptDist_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  exact transcriptDist_prependTransform (Sf y) y he
    (fun h => by subst h; exact hnone hy) n

/-! ### Overlap calculus (thesis Lemma 2.3's common part)

Private copies of `Dist`-level plumbing, to be upstreamed into
`Dist.lean` once that file is free to rebuild. -/

/-- Thesis Lemma 2.3: the **common part** of two distributions, the
pointwise minimum (as a `Finsupp.zipWith`). -/
private noncomputable def commonPart {A : Type*} (μ ν : Dist A) : Dist A :=
  Finsupp.zipWith min (min_self 0) μ ν

private theorem commonPart_apply {A : Type*} (μ ν : Dist A) (a : A) :
    commonPart μ ν a = min (μ a) (ν a) :=
  Finsupp.zipWith_apply

private theorem commonPart_le_left {A : Type*} (μ ν : Dist A) (a : A) :
    commonPart μ ν a ≤ μ a := by
  rw [commonPart_apply]
  exact min_le_left _ _

private theorem commonPart_le_right {A : Type*} (μ ν : Dist A) (a : A) :
    commonPart μ ν a ≤ ν a := by
  rw [commonPart_apply]
  exact min_le_right _ _

private theorem commonPart_comm {A : Type*} (μ ν : Dist A) :
    commonPart μ ν = commonPart ν μ := by
  refine Finsupp.ext fun a => ?_
  rw [commonPart_apply, commonPart_apply, min_comm]

open Classical in
private theorem single_nonNeg {A : Type*} {c : ℝ} (hc : 0 ≤ c) (a : A) :
    RandomSystems.Dist.NonNeg (Finsupp.single a c : Dist A) := by
  intro a'
  classical
  rw [Finsupp.single_apply]
  split
  · exact hc
  · exact le_refl 0

private theorem commonPart_nonNeg {A : Type*} {μ ν : Dist A}
    (hμ : μ.NonNeg) (hν : ν.NonNeg) : (commonPart μ ν).NonNeg := fun a => by
  rw [commonPart_apply]
  exact le_min (hμ a) (hν a)

private theorem sub_nonNeg_of_le {A : Type*} {μ ν : Dist A} (h : μ ≤ ν) :
    Dist.NonNeg (ν - μ : Dist A) := fun a => by
  rw [Finsupp.sub_apply]
  exact sub_nonneg.mpr (Finsupp.le_def.mp h a)

private theorem add_sub_cancel_finsupp {A : Type*} (μ ν : Dist A) :
    μ + (ν - μ) = ν := by
  refine Finsupp.ext fun a => ?_
  simp

private theorem weight_commonPart {A : Type*} [DecidableEq A]
    (μ ν : Dist A) :
    (commonPart μ ν).weight
      = ∑ a ∈ μ.support ∪ ν.support, min (μ a) (ν a) := by
  rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
  refine Eq.trans (Finset.sum_subset Finsupp.support_zipWith
    fun a _ ha => Finsupp.notMem_support_iff.mp ha) ?_
  exact Finset.sum_congr rfl fun a _ => commonPart_apply μ ν a

/-- Thesis Lemma 2.3: the **excess** of `μ` over `ν`, the pointwise
truncated difference `max (μ a - ν a) 0` (spelled out over `ℝ`; over
`ℝ≥0` this was the truncating subtraction). -/
private noncomputable def excess {A : Type*} (μ ν : Dist A) : Dist A :=
  Finsupp.zipWith (fun m n => max (m - n) 0) (by simp) μ ν

private theorem excess_apply {A : Type*} (μ ν : Dist A) (a : A) :
    excess μ ν a = max (μ a - ν a) 0 :=
  Finsupp.zipWith_apply

/-- Thesis Lemma 2.3's split: `μ = (common part) + (excess)`. -/
private theorem commonPart_add_excess {A : Type*} (μ ν : Dist A) :
    commonPart μ ν + excess μ ν = μ := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.add_apply, commonPart_apply, excess_apply]
  rcases le_total (ν a) (μ a) with h | h
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]

/-- The overlap formula: the one-sided statistical distance is the
first weight minus the weight of the common part
(`δ μ ν = Σ (μ − ν)⁺ = |μ| − Σ min`), for a non-negative second law. -/
private theorem δ_eq_weight_sub_weight_commonPart {A : Type*}
    (μ : Dist A) {ν : Dist A} (hν : ν.NonNeg) :
    (δ μ ν : ℝ) = (μ.weight : ℝ) - ((commonPart μ ν).weight : ℝ) := by
  classical
  have hw : μ.weight = ∑ a ∈ μ.support ∪ ν.support, μ a := by
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_left
      fun a _ ha => Finsupp.notMem_support_iff.mp ha
  rw [δ_eq_sum_of_support_subset hν
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support),
    hw, weight_commonPart μ ν, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases le_total (ν a) (μ a) with h | h
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring

/-- Trimming: scaling a sub-distribution scales its weight. -/
private theorem weight_smul {A : Type*} (c : ℝ) (μ : Dist A) :
    (c • μ).weight = c * μ.weight := by
  rw [Dist.weight_eq_finsupp_sum, Dist.weight_eq_finsupp_sum,
    Finsupp.sum_smul_index fun _ => rfl]
  simp only [Finsupp.sum, smul_eq_mul]
  rw [Finset.mul_sum]

/-- Trimming: scaling both sub-distributions by a non-negative factor
scales the statistical distance. -/
private theorem δ_smul {A : Type*} {c : ℝ} (hc : 0 ≤ c) (μ ν : Dist A) :
    δ (c • μ) (c • ν) = c * δ μ ν := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp [δ, zero_smul, Finsupp.sum_zero_index]
  · unfold δ
    rw [Finsupp.sum, Finsupp.sum,
      Finsupp.support_smul_eq (ne_of_gt hcpos), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_sub, mul_max_of_nonneg _ _ hc, mul_zero]

/-! ### Gluing per-query slices (thesis §2.4.2, footnote 8) -/

/-- Thesis §2.4.2 footnote 8, arbitrary-`X` form: **glue** a family of
systems along their first queries — `glue g` behaves on every
`x`-headed history exactly as `g x` does.  This is the tuple-atom
constructor of the cross-`x` joint: a glued atom selects one per-`x`
slice for each first query, and no product over `X` is ever formed. -/
def _root_.PFunDDS.DDS.glue (g : X → PFunDDS.DDS X Y) : PFunDDS.DDS X Y :=
  ⟨fun l => match l with
    | [] => Part.none
    | x :: m => (g x).1 (x :: m),
   by
    constructor
    · exact fun h => h
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨u, rfl⟩ := hpre
      cases l₁ with
      | nil => exact absurd rfl hne
      | cons a m =>
          exact (g a).2.2
            (List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append m u⟩)
            (List.cons_ne_nil a m) hdom⟩

/-- The glued system consults the `x`-slice on `x`-headed histories. -/
theorem glue_apply_cons (g : X → PFunDDS.DDS X Y) (x : X) (m : List X) :
    (PFunDDS.DDS.glue g).1 (x :: m) = (g x).1 (x :: m) :=
  rfl

/-- Membership in the glued domain is per-slice. -/
theorem cons_mem_dom_glue (g : X → PFunDDS.DDS X Y) (x : X) (m : List X) :
    x :: m ∈ PFunDDS.dom (PFunDDS.DDS.glue g)
      ↔ x :: m ∈ PFunDDS.dom (g x) :=
  Iff.rfl

/-- The glued system's first `s⊥`-answer to `x` is the `x`-slice's
first answer — unconditionally (the `⊥` case included). -/
theorem output_fullyDefined_glue (g : X → PFunDDS.DDS X Y) (x : X) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.DDS.glue g)) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp)
      = PFunDDS.output (PFunDDS.fullyDefined (g x)) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) :=
  rfl

/-- Thesis §2.4.2 footnote 8, answered case: after an answered first
query `x` the glued system continues as the `x`-slice's successor. -/
theorem successor_glue (g : X → PFunDDS.DDS X Y) (x : X)
    (hx : [x] ∈ PFunDDS.dom (g x)) :
    PFunDDS.DDS.successor (PFunDDS.DDS.glue g) x
      = PFunDDS.DDS.successor (g x) x := by
  unfold PFunDDS.DDS.successor
  rw [if_pos (show [x] ∈ PFunDDS.dom (PFunDDS.DDS.glue g) from hx),
    if_pos hx]
  rfl

/-- CR18 Def 3.3 skip semantics at the joint: a `⊥`-answered first
query leaves the whole glued state unchanged (`glue g`, not `g x` —
the joint must keep its other branches alive for requeries). -/
theorem successor_glue_of_not_mem (g : X → PFunDDS.DDS X Y) (x : X)
    (hx : [x] ∉ PFunDDS.dom (g x)) :
    PFunDDS.DDS.successor (PFunDDS.DDS.glue g) x = PFunDDS.DDS.glue g :=
  successor_of_not_mem fun h => hx h

/-- Milestone-2 compatibility: a glued family of prepended slices
answers the prescribed first answer at every first query. -/
theorem output_fullyDefined_glue_prepend (yf : X → Option Y)
    (sf : X → PFunDDS.DDS X Y) (x : X) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.DDS.glue
        (fun x' => PFunDDS.DDS.prepend x' (yf x') (sf x')))) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = yf x :=
  (output_fullyDefined_glue _ x).trans
    (output_fullyDefined_prepend x (yf x) (sf x))

/-- Milestone-2 compatibility, answered case: the successor of a glued
prepended family at an answered first query recovers the prescribed
continuation slice. -/
theorem successor_glue_prepend (yf : X → Option Y)
    (sf : X → PFunDDS.DDS X Y) (x : X) {v : Y} (hv : yf x = some v) :
    PFunDDS.DDS.successor (PFunDDS.DDS.glue
        (fun x' => PFunDDS.DDS.prepend x' (yf x') (sf x'))) x
      = sf x := by
  rw [successor_glue _ x
    (by rw [hv]; exact singleton_mem_dom_prepend_some x v (sf x))]
  rw [hv]
  exact successor_prepend x v (sf x)

/-! ### Cross-query joint groundwork (thesis Lemma 2.33) -/

/-- CR18 Def 3.3: the first `s⊥`-answer to `x` is `⊥` exactly on
systems that do not answer `x`. -/
theorem output_fullyDefined_eq_none_iff {s : PFunDDS.DDS X Y} {x : X} :
    PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none
      ↔ [x] ∉ PFunDDS.dom s := by
  constructor
  · intro h hx
    have hsome := PFunDDS.output_fullyDefined_append_of_mem s [] x
      (Or.inr rfl) hx
    exact Option.some_ne_none _ ((h.symm.trans hsome).symm)
  · intro hx
    simp only [PFunDDS.output_fullyDefined]
    split
    · rename_i hmem
      exact absurd hmem hx
    · rfl

open Classical in
/-- The `⊥`-marginal of **any** PDS is its pass-through filter: the
skip-aware successor is the identity on atoms that do not answer `x`,
so no separate `⊥`-branch representative ever exists or is needed —
`S↑x↓⊥` is `S` restricted to the atoms that `⊥`-answer `x`. -/
theorem successorTransform_none_eq_filter (S : PFunPDS X Y) (x : X) :
    successorTransform S x none
      = S.filter fun s => [x] ∉ PFunDDS.dom s := by
  unfold successorTransform
  have hfil : S.filter (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = none)
      = S.filter fun s => [x] ∉ PFunDDS.dom s := by
    refine Finsupp.ext fun s => ?_
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hs : [x] ∈ PFunDDS.dom s
    · rw [if_neg fun h => output_fullyDefined_eq_none_iff.mp h hs,
        if_neg fun h => h hs]
    · rw [if_pos (output_fullyDefined_eq_none_iff.mpr hs), if_pos hs]
  rw [hfil]
  refine Eq.trans (fTransform_congr_of_support (g := id) _
    fun s hs => successor_of_not_mem ?_) (Dist.fTransform_id _)
  have hs' : s ∈ S.support.filter fun s => [x] ∉ PFunDDS.dom s := by
    rw [← Finsupp.support_filter]
    exact hs
  exact (Finset.mem_filter.mp hs').2

/-- The **empty system**: undefined on every history.  It is the inert
`x`-slice of a `⊥`-choice in a cross-query glue atom — `glue` only
consults its `x`-branch, which is empty. -/
def _root_.PFunDDS.DDS.empty : PFunDDS.DDS X Y :=
  ⟨fun _ => Part.none, ⟨fun h => h, fun _ _ h => h⟩⟩

/-- The empty system answers nothing. -/
theorem not_mem_dom_empty (l : List X) :
    l ∉ PFunDDS.dom (PFunDDS.DDS.empty (X := X) (Y := Y)) :=
  fun h => h

/-- A glue atom with an empty `x`-slice `⊥`-answers `x`. -/
theorem output_fullyDefined_glue_empty (g : X → PFunDDS.DDS X Y) (x : X)
    (hg : g x = PFunDDS.DDS.empty) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.DDS.glue g)) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
  rw [output_fullyDefined_glue g x]
  exact output_fullyDefined_eq_none_iff.mpr (by rw [hg]; exact not_mem_dom_empty [x])

-- Further private copies of `Dist`-level plumbing for the cross-query
-- joint (to be upstreamed into `Dist.lean` once it is free to rebuild).

private theorem weight_add {A : Type*} (μ ν : Dist A) :
    (μ + ν).weight = μ.weight + ν.weight := by
  rw [Dist.weight_eq_finsupp_sum, Dist.weight_eq_finsupp_sum,
    Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

theorem eq_zero_of_weight_eq_zero {A : Type*} {μ : Dist A}
    (hnn : μ.NonNeg) (h : μ.weight = 0) : μ = 0 := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra ha
  have hle : μ a ≤ μ.weight := by
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.single_le_sum (fun a' _ => hnn a')
      (Finsupp.mem_support_iff.mpr ha)
  rw [h] at hle
  exact ha (le_antisymm hle (hnn a))

private theorem weight_tsub_of_le {A : Type*} {μ ν : Dist A} (_h : ν ≤ μ) :
    (μ - ν).weight = μ.weight - ν.weight := by
  refine eq_sub_of_add_eq ?_
  rw [← weight_add, sub_add_cancel]

private theorem fTransform_smul {A B : Type*} (f : A → B) (c : ℝ)
    (μ : Dist A) :
    Dist.fTransform f (c • μ) = c • Dist.fTransform f μ := by
  show Finsupp.mapDomain f (c • μ) = c • Finsupp.mapDomain f μ
  exact Finsupp.mapDomain_smul c μ

private theorem mass_eq_eq_apply {A : Type*} (μ : Dist A) (a : A) :
    μ.mass (fun a' => a' = a) = μ a := by
  refine Eq.trans (Dist.fTransform_apply_eq_mass id μ a).symm ?_
  rw [Dist.fTransform_id]

private theorem fTransform_fst_prod {A B : Type*} (μ : Dist A)
    (ν : Dist B) :
    Dist.fTransform Prod.fst (Dist.prod μ ν) = ν.weight • μ := by
  classical
  refine Finsupp.ext fun a => ?_
  rw [Dist.fTransform_apply_eq_mass, Finsupp.smul_apply, smul_eq_mul,
    mass_prod_eq_double_sum]
  dsimp only
  have hinner : ∀ (a' : A) (wa : ℝ),
      (ν.sum fun _ wb => if a' = a then wa * wb else 0)
        = if a' = a then wa * ν.weight else 0 := by
    intro a' wa
    by_cases h : a' = a
    · simp only [if_pos h, Dist.weight_eq_finsupp_sum, Finsupp.sum]
      rw [Finset.mul_sum]
    · simp only [if_neg h]
      exact Finset.sum_const_zero
  refine Eq.trans (Finsupp.sum_congr
    (g2 := fun a' wa => if a' = a then wa * ν.weight else 0)
    fun a' _ => hinner a' (μ a')) ?_
  simp only [Finsupp.sum]
  rw [Finset.sum_ite_eq' μ.support a (fun a' => μ a' * ν.weight)]
  by_cases h : a ∈ μ.support
  · rw [if_pos h, mul_comm]
  · rw [if_neg h, Finsupp.notMem_support_iff.mp h, mul_zero]

private theorem fTransform_snd_prod {A B : Type*} (μ : Dist A)
    (ν : Dist B) :
    Dist.fTransform Prod.snd (Dist.prod μ ν) = μ.weight • ν := by
  classical
  refine Finsupp.ext fun z => ?_
  rw [Dist.fTransform_apply_eq_mass, Finsupp.smul_apply, smul_eq_mul,
    mass_prod_eq_double_sum]
  dsimp only
  have hinner : ∀ (wa : ℝ),
      (ν.sum fun z' wb => if z' = z then wa * wb else 0) = wa * ν z := by
    intro wa
    simp only [Finsupp.sum]
    rw [Finset.sum_ite_eq' ν.support z (fun z' => wa * ν z')]
    by_cases h : z ∈ ν.support
    · rw [if_pos h]
    · rw [if_neg h, Finsupp.notMem_support_iff.mp h, mul_zero]
  refine Eq.trans (Finsupp.sum_congr (g2 := fun _ wa => wa * ν z)
    fun a' _ => hinner (μ a')) ?_
  simp only [Finsupp.sum]
  rw [← Finset.sum_mul, Dist.weight_eq_finsupp_sum, Finsupp.sum]

private theorem filter_fTransform {A B : Type*} (g : A → B) (μ : Dist A)
    (P : B → Prop) [DecidablePred P] [DecidablePred fun a => P (g a)] :
    (Dist.fTransform g μ).filter P
      = Dist.fTransform g (μ.filter fun a => P (g a)) := by
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.filter_apply, Dist.fTransform_apply_eq_mass,
    Dist.fTransform_apply_eq_mass,
    show Dist.mass (Finsupp.filter (fun a => P (g a)) μ)
        (fun a => g a = z) = μ.mass fun a => g a = z ∧ P (g a) from
      mass_filter μ _ _]
  by_cases hz : P z
  · rw [if_pos hz]
    exact Dist.mass_congr μ fun a =>
      ⟨fun h => ⟨h, h.symm ▸ hz⟩, And.left⟩
  · rw [if_neg hz]
    exact (Dist.mass_eq_zero_of_forall_not μ
      (P := fun a => g a = z ∧ P (g a))
      fun a h => hz (h.1 ▸ h.2)).symm

private theorem δ_add_add_left {A : Type*} {ρ ν : Dist A} (μ : Dist A)
    (hρ : ρ.NonNeg) (hν : ν.NonNeg) :
    δ (ρ + μ) (ρ + ν) = δ μ ν := by
  classical
  have hρν : (ρ + ν : Dist A).NonNeg := fun a => by
    rw [Finsupp.add_apply]
    exact add_nonneg (hρ a) (hν a)
  rw [δ_eq_sum_of_support_subset hρν
      (Finset.subset_union_left :
        (ρ + μ).support ⊆ (ρ + μ).support ∪ μ.support),
    δ_eq_sum_of_support_subset hν
      (Finset.subset_union_right :
        μ.support ⊆ (ρ + μ).support ∪ μ.support)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.add_apply, Finsupp.add_apply, add_sub_add_left_eq_sub]

private theorem weight_sub_weight_le_δ {A : Type*} (μ : Dist A)
    {ν : Dist A} (hνnn : ν.NonNeg) :
    (μ.weight : ℝ) - (ν.weight : ℝ) ≤ (δ μ ν : ℝ) := by
  classical
  have hμ : μ.weight = ∑ a ∈ μ.support ∪ ν.support, μ a := by
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_left
      fun a _ ha => Finsupp.notMem_support_iff.mp ha
  have hν : ν.weight = ∑ a ∈ μ.support ∪ ν.support, ν a := by
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    refine Finset.sum_subset Finset.subset_union_right
      fun a _ ha => Finsupp.notMem_support_iff.mp ha
  rw [δ_eq_sum_of_support_subset hνnn
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support),
    hμ, hν, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun a _ => le_max_left _ _

private theorem fTransform_add {A B : Type*} (f : A → B) (μ ν : Dist A) :
    Dist.fTransform f (μ + ν)
      = Dist.fTransform f μ + Dist.fTransform f ν := by
  show Finsupp.mapDomain f (μ + ν) = _
  exact Finsupp.mapDomain_add

private theorem weight_single {A : Type*} (a : A) (c : ℝ) :
    Dist.weight (Finsupp.single a c : Dist A) = c := by
  rw [Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_single_index rfl

/-- Thesis Lemma 2.33's joint, list form: the iterated normalized
independent coupling of a per-class family of equal-weight
sub-distributions, as one distribution over choice profiles (`d` is
the inert profile value outside the coupled classes). -/
private noncomputable def jointProfileList {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (D : I → Dist CH) : List I → Dist (I → CH)
  | [] => Finsupp.single (fun _ => d) u
  | i :: l => u⁻¹ •
      Dist.fTransform (fun cp : CH × (I → CH) => Function.update cp.2 i cp.1)
        (Dist.prod (D i) (jointProfileList u d D l))

private theorem jointProfileList_weight {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (D : I → Dist CH) :
    ∀ l : List I, (∀ j ∈ l, (D j).weight = u) →
      (jointProfileList u d D l).weight = u := by
  intro l
  induction l with
  | nil => intro _; exact weight_single _ u
  | cons j l ih =>
      intro hw
      simp only [jointProfileList]
      rw [weight_smul, Dist.weight_fTransform, Dist.weight_prod,
        hw j (by simp), ih fun k hk => hw k (by simp [hk])]
      rcases eq_or_ne u 0 with rfl | hu
      · simp
      · have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
        push_cast
        rw [← mul_assoc, inv_mul_cancel₀ hu', one_mul]

private theorem jointProfileList_marginal {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (D : I → Dist CH) :
    ∀ l : List I, (∀ j ∈ l, (D j).NonNeg) →
      (∀ j ∈ l, (D j).weight = u) → ∀ i ∈ l,
      Dist.fTransform (fun p => p i) (jointProfileList u d D l) = D i := by
  intro l
  induction l with
  | nil => intro _ _ i hi; simp at hi
  | cons j l ih =>
      intro hDnn hw i hmem
      have hend : u⁻¹ • u • D i = D i := by
        rcases eq_or_ne u 0 with rfl | hu
        · rw [eq_zero_of_weight_eq_zero (hDnn i hmem) (by
            simpa using hw i hmem), smul_zero, smul_zero]
        · rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
      simp only [jointProfileList]
      rw [fTransform_smul, Dist.fTransform_comp]
      by_cases hij : i = j
      · subst hij
        have hfun : ((fun p : I → CH => p i)
            ∘ fun cp : CH × (I → CH) => Function.update cp.2 i cp.1)
            = Prod.fst := by
          funext cp
          exact Function.update_self i cp.1 cp.2
        rw [hfun, fTransform_fst_prod,
          jointProfileList_weight u d D l fun k hk => hw k (by simp [hk])]
        exact hend
      · have hi : i ∈ l := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h hij
          · exact h
        have hfun : ((fun p : I → CH => p i)
            ∘ fun cp : CH × (I → CH) => Function.update cp.2 j cp.1)
            = (fun p : I → CH => p i) ∘ Prod.snd := by
          funext cp
          exact Function.update_of_ne hij cp.1 cp.2
        rw [hfun, ← Dist.fTransform_comp, fTransform_snd_prod,
          fTransform_smul,
          ih (fun k hk => hDnn k (by simp [hk]))
            (fun k hk => hw k (by simp [hk])) i hi,
          hw j (by simp)]
        exact hend

/-- Thesis Lemma 2.33's joint over the class Finset. -/
private noncomputable def jointProfile {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Dist CH) :
    Dist (I → CH) :=
  jointProfileList u d D C.toList

private theorem jointProfile_weight {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Dist CH)
    (hw : ∀ j ∈ C, (D j).weight = u) :
    (jointProfile u d C D).weight = u :=
  jointProfileList_weight u d D C.toList
    fun j hj => hw j (Finset.mem_toList.mp hj)

private theorem jointProfile_marginal {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Dist CH)
    (hDnn : ∀ j ∈ C, (D j).NonNeg)
    (hw : ∀ j ∈ C, (D j).weight = u) {i : I} (hi : i ∈ C) :
    Dist.fTransform (fun p => p i) (jointProfile u d C D) = D i :=
  jointProfileList_marginal u d D C.toList
    (fun j hj => hDnn j (Finset.mem_toList.mp hj))
    (fun j hj => hw j (Finset.mem_toList.mp hj)) i
    (Finset.mem_toList.mpr hi)

private theorem jointProfileList_nonNeg {I CH : Type*} [DecidableEq I]
    {u : ℝ} (hu : 0 ≤ u) (d : CH) (D : I → Dist CH) :
    ∀ l : List I, (∀ j ∈ l, (D j).NonNeg) →
      (jointProfileList u d D l).NonNeg := by
  intro l
  induction l with
  | nil => intro _; exact single_nonNeg hu _
  | cons j l ih =>
      intro hD p
      simp only [jointProfileList]
      rw [Finsupp.smul_apply, smul_eq_mul]
      refine mul_nonneg (inv_nonneg.mpr hu) ?_
      exact (((hD j (by simp)).prod
        (ih fun k hk => hD k (by simp [hk]))).fTransform _) p

private theorem jointProfile_nonNeg {I CH : Type*} [DecidableEq I]
    {u : ℝ} (hu : 0 ≤ u) (d : CH) (C : Finset I) {D : I → Dist CH}
    (hD : ∀ j ∈ C, (D j).NonNeg) : (jointProfile u d C D).NonNeg :=
  jointProfileList_nonNeg hu d D C.toList
    fun j hj => hD j (Finset.mem_toList.mp hj)

/-- One per-class choice, as an `x`-slice: an answered choice `(v, a)`
prepends `(x ↦ v)` to the continuation `a`; a `⊥`-choice is the empty
slice. -/
private def sliceOf (c : Option (Y × PFunDDS.DDS X Y)) (x : X) :
    PFunDDS.DDS X Y :=
  match c with
  | some (v, a) => PFunDDS.DDS.prepend x (some v) a
  | none => PFunDDS.DDS.empty

/-- Thesis §2.4.2 footnote 8: the tuple atom of the cross-query joint —
glue the slices selected by a choice profile, one per class. -/
private def glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × PFunDDS.DDS X Y)) : PFunDDS.DDS X Y :=
  PFunDDS.DDS.glue fun x => sliceOf (p (cls x)) x

/-- The continuation selected by a choice (the `⊥`-choice selects the
inert empty system). -/
private def contOf (c : Option (Y × PFunDDS.DDS X Y)) : PFunDDS.DDS X Y :=
  (Option.map Prod.snd c).getD PFunDDS.DDS.empty

private theorem output_fullyDefined_glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × PFunDDS.DDS X Y)) (x : X) :
    PFunDDS.output (PFunDDS.fullyDefined (glueProfile cls p)) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp)
      = Option.map Prod.fst (p (cls x)) := by
  refine (output_fullyDefined_glue _ x).trans ?_
  rcases hp : p (cls x) with _ | ⟨v, a⟩
  · simp only [sliceOf, Option.map_none]
    exact output_fullyDefined_eq_none_iff.mpr (not_mem_dom_empty [x])
  · simp only [sliceOf, Option.map_some]
    exact output_fullyDefined_prepend x (some v) a

private theorem successor_glueProfile_some {I : Type*} {cls : X → I}
    {p : I → Option (Y × PFunDDS.DDS X Y)} {x : X} {v : Y}
    {a : PFunDDS.DDS X Y} (hp : p (cls x) = some (v, a)) :
    PFunDDS.DDS.successor (glueProfile cls p) x = a := by
  have hmem : [x] ∈ PFunDDS.dom (sliceOf (p (cls x)) x) := by
    rw [hp]
    exact singleton_mem_dom_prepend_some x v a
  refine Eq.trans (successor_glue _ x hmem) ?_
  have hkey : PFunDDS.DDS.successor (sliceOf (p (cls x)) x) x = a := by
    rw [hp]
    exact successor_prepend x v a
  exact hkey

open Classical in
/-- The engine of the cross-query joint's marginals: the
`(x, some v)`-successor transformation of a glued-profile pushforward
is the continuation-pushforward of the `v`-filtered `cls x`-marginal
of the profile distribution. -/
private theorem successorTransform_fTransform_glueProfile {I : Type*}
    (cls : X → I) (ρ : Dist (I → Option (Y × PFunDDS.DDS X Y)))
    (x : X) (v : Y) :
    successorTransform (Dist.fTransform (glueProfile cls) ρ) x (some v)
      = Dist.fTransform contOf
          ((Dist.fTransform (fun p => p (cls x)) ρ).filter
            fun c => Option.map Prod.fst c = some v) := by
  unfold successorTransform
  have hfil : (Dist.fTransform (glueProfile cls) ρ).filter
      (fun t => PFunDDS.output (PFunDDS.fullyDefined t) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some v)
      = Dist.fTransform (glueProfile cls)
          (ρ.filter fun p => Option.map Prod.fst (p (cls x)) = some v) := by
    rw [filter_fTransform]
    refine congrArg (Dist.fTransform (glueProfile cls)) ?_
    refine Finsupp.ext fun p => ?_
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hp : Option.map Prod.fst (p (cls x)) = some v
    · rw [if_pos hp,
        if_pos ((output_fullyDefined_glueProfile cls p x).trans hp)]
    · rw [if_neg hp, if_neg fun h => hp
        ((output_fullyDefined_glueProfile cls p x).symm.trans h)]
  rw [hfil, Dist.fTransform_comp,
    filter_fTransform (fun p => p (cls x)) ρ
      (fun c => Option.map Prod.fst c = some v),
    Dist.fTransform_comp]
  refine fTransform_congr_of_support _ fun p hp => ?_
  have hQ : Option.map Prod.fst (p (cls x)) = some v := by
    have hp' : p ∈ (ρ.filter fun q =>
        Option.map Prod.fst (q (cls x)) = some v).support := hp
    rw [Finsupp.support_filter] at hp'
    exact (Finset.mem_filter.mp hp').2
  rcases hc : p (cls x) with _ | ⟨v', a⟩
  · rw [hc] at hQ
    exact absurd hQ (by simp)
  · rw [hc] at hQ
    obtain rfl : v' = v := by simpa using hQ
    show PFunDDS.DDS.successor (glueProfile cls p) x = contOf (p (cls x))
    rw [hc]
    exact successor_glueProfile_some hc

private theorem filter_of_forall_not {A : Type*} (μ : Dist A)
    (P : A → Prop) [DecidablePred P] (h : ∀ a, ¬ P a) :
    μ.filter P = 0 := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.filter_apply, if_neg (h a), Finsupp.coe_zero, Pi.zero_apply]

private theorem filter_of_forall {A : Type*} (μ : Dist A)
    (P : A → Prop) [DecidablePred P] (h : ∀ a, P a) :
    μ.filter P = μ := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.filter_apply, if_pos (h a)]

private theorem fTransform_finset_sum {A B : Type*} {ι : Type*}
    (t : Finset ι) (f : A → B) (Rf : ι → Dist A) :
    Dist.fTransform f (∑ i ∈ t, Rf i)
      = ∑ i ∈ t, Dist.fTransform f (Rf i) := by
  show Finsupp.mapDomain f (∑ i ∈ t, Rf i)
    = ∑ i ∈ t, Finsupp.mapDomain f (Rf i)
  rw [Finsupp.mapDomain_finset_sum]

/-- Thesis Lemma 2.33 packaging: one side's per-class data as a
distribution over choices — each answered branch `B v` tagged with its
answer `v`, plus the `⊥`-choice carrying the pass-through mass `β`. -/
private noncomputable def classChoiceDist (vs : Finset Y)
    (B : Y → PFunPDS X Y) (β : ℝ) :
    Dist (Option (Y × PFunDDS.DDS X Y)) :=
  (∑ v ∈ vs, Dist.fTransform (fun s => some (v, s)) (B v))
    + Finsupp.single none β

private theorem weight_classChoiceDist (vs : Finset Y)
    (B : Y → PFunPDS X Y) (β : ℝ) :
    (classChoiceDist vs B β).weight = (∑ v ∈ vs, (B v).weight) + β := by
  unfold classChoiceDist
  rw [weight_add, weight_finset_sum, weight_single]
  refine congrArg (· + β) ?_
  exact Finset.sum_congr rfl fun v _ => Dist.weight_fTransform _ _

open Classical in
private theorem contOf_filter_classChoiceDist_of_mem {vs : Finset Y}
    {B : Y → PFunPDS X Y} {β : ℝ} {v : Y} (hv : v ∈ vs) :
    Dist.fTransform contOf ((classChoiceDist vs B β).filter
        fun c => Option.map Prod.fst c = some v)
      = B v := by
  have hside : ∀ v' ∈ vs, v' ≠ v →
      Dist.fTransform contOf ((Dist.fTransform
        (fun s : PFunDDS.DDS X Y => some (v', s)) (B v')).filter
          fun c => Option.map Prod.fst c = some v) = 0 := by
    intro v' _ hne
    rw [filter_fTransform, filter_of_forall_not _ _ fun s => by simp [hne],
      fTransform_zero, fTransform_zero]
  unfold classChoiceDist
  rw [Finsupp.filter_add, Finsupp.filter_sum,
    Finsupp.filter_single_of_neg
      (p := fun c => Option.map Prod.fst c = some v) (by simp),
    add_zero, fTransform_finset_sum,
    Finset.sum_eq_single_of_mem v hv hside, filter_fTransform,
    filter_of_forall _ _ fun s => by simp, Dist.fTransform_comp,
    show (contOf ∘ fun s : PFunDDS.DDS X Y => some (v, s)) = id from
      funext fun s => rfl, Dist.fTransform_id]

open Classical in
private theorem contOf_filter_classChoiceDist_of_not_mem {vs : Finset Y}
    {B : Y → PFunPDS X Y} {β : ℝ} {v : Y} (hv : v ∉ vs) :
    Dist.fTransform contOf ((classChoiceDist vs B β).filter
        fun c => Option.map Prod.fst c = some v)
      = 0 := by
  unfold classChoiceDist
  rw [Finsupp.filter_add, Finsupp.filter_sum,
    Finsupp.filter_single_of_neg
      (p := fun c => Option.map Prod.fst c = some v) (by simp),
    add_zero, fTransform_finset_sum]
  refine Eq.trans (Finset.sum_congr rfl fun v' hv' => ?_)
    Finset.sum_const_zero
  have hne : v' ≠ v := fun h => hv (h ▸ hv')
  rw [filter_fTransform, filter_of_forall_not _ _ fun s => by simp [hne],
    fTransform_zero, fTransform_zero]

open Classical in
private theorem filter_none_classChoiceDist (vs : Finset Y)
    (B : Y → PFunPDS X Y) (β : ℝ) :
    (classChoiceDist vs B β).filter
        (fun c => Option.map Prod.fst c = none)
      = Finsupp.single none β := by
  unfold classChoiceDist
  rw [Finsupp.filter_add, Finsupp.filter_sum,
    Finsupp.filter_single_of_pos
      (p := fun c => Option.map Prod.fst c = none) (by simp)]
  refine Eq.trans (congrArg (· + Finsupp.single none β) ?_) (zero_add _)
  refine Eq.trans (Finset.sum_congr rfl fun v' _ => ?_)
    Finset.sum_const_zero
  rw [filter_fTransform, filter_of_forall_not _ _ fun s => by simp,
    fTransform_zero]

open Classical in
/-- Thesis Lemma 2.33, the marginal half at the `A`-level: for any
shared summand `E ≤ A` of uniform weight, the `(x, some v)`-marginal of
the glued joint `E`-part + excess-part recovers the `v`-slice of the
class's own choice distribution. -/
private theorem successorTransform_crossJoint {I : Type*} (cls : X → I)
    (C : Finset I) (E A : I → Dist (Option (Y × PFunDDS.DDS X Y)))
    (u w : ℝ)
    (hEnn : ∀ i ∈ C, (E i).NonNeg)
    (hE : ∀ i ∈ C, (E i).weight = u)
    (hA : ∀ i ∈ C, (A i).weight = w) (hle : ∀ i ∈ C, E i ≤ A i)
    {x : X} (hx : cls x ∈ C) (v : Y) :
    successorTransform (Dist.fTransform (glueProfile cls)
        (jointProfile u none C E
          + jointProfile (w - u) none C fun i => A i - E i))
      x (some v)
      = Dist.fTransform contOf
          ((A (cls x)).filter fun c => Option.map Prod.fst c = some v) := by
  have hX' : ∀ j ∈ C, Dist.weight (A j - E j) = w - u := by
    intro j hj
    rw [weight_tsub_of_le (hle j hj), hA j hj, hE j hj]
  rw [successorTransform_fTransform_glueProfile, fTransform_add,
    jointProfile_marginal u none C E hEnn hE hx,
    jointProfile_marginal (w - u) none C _
      (fun j hj => sub_nonNeg_of_le (hle j hj)) hX' hx,
    add_sub_cancel_finsupp]

/-- One side's per-class choice distribution, from the branch data
(thesis Lemma 2.33; the `⊥`-choice carries the pass-through mass
`w − Σ_v |B i v|`). -/
private noncomputable def choiceOf (vs : Finset Y) (B : Y → PFunPDS X Y)
    (w : ℝ) : Dist (Option (Y × PFunDDS.DDS X Y)) :=
  classChoiceDist vs B (w - ∑ v ∈ vs, (B v).weight)

/-- The per-class overlap: the weight of the common part of the two
sides' choice distributions. -/
private noncomputable def overlapOf {I : Type*} (vs : I → Finset Y)
    (Bs Bt : I → Y → PFunPDS X Y) (wS wT : ℝ) (i : I) : ℝ :=
  Dist.weight (commonPart (choiceOf (vs i) (Bs i) wS)
    (choiceOf (vs i) (Bt i) wT))

/-- The shared trimmed common part: the per-class common part scaled
down to the uniform weight `τ` (thesis Lemma 2.33's trim). -/
private noncomputable def trimOf {I : Type*} (vs : I → Finset Y)
    (Bs Bt : I → Y → PFunPDS X Y) (wS wT : ℝ) (τ : ℝ) (i : I) :
    Dist (Option (Y × PFunDDS.DDS X Y)) :=
  (τ / overlapOf vs Bs Bt wS wT i) •
    commonPart (choiceOf (vs i) (Bs i) wS) (choiceOf (vs i) (Bt i) wT)

private theorem classChoiceDist_nonNeg {vs : Finset Y}
    {B : Y → PFunPDS X Y} {β : ℝ}
    (hB : ∀ v ∈ vs, (B v).NonNeg) (hβ : 0 ≤ β) :
    (classChoiceDist vs B β).NonNeg := fun c => by
  unfold classChoiceDist
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
  exact add_nonneg
    (Finset.sum_nonneg fun v hv => ((hB v hv).fTransform _) c)
    (single_nonNeg hβ _ c)

private theorem choiceOf_nonNeg {vs : Finset Y} {B : Y → PFunPDS X Y}
    {w : ℝ} (hB : ∀ v ∈ vs, (B v).NonNeg)
    (hw : ∑ v ∈ vs, (B v).weight ≤ w) : (choiceOf vs B w).NonNeg :=
  classChoiceDist_nonNeg hB (sub_nonneg.mpr hw)

private theorem overlapOf_nonneg {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {i : I}
    (hBs : ∀ v ∈ vs i, (Bs i v).NonNeg) (hBt : ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    0 ≤ overlapOf vs Bs Bt wS wT i :=
  (commonPart_nonNeg (choiceOf_nonNeg hBs hwS)
    (choiceOf_nonNeg hBt hwT)).weight_nonneg

private theorem trimOf_nonNeg {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    {i : I}
    (hBs : ∀ v ∈ vs i, (Bs i v).NonNeg) (hBt : ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    (trimOf vs Bs Bt wS wT τ i).NonNeg := fun c => by
  unfold trimOf
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact mul_nonneg
    (div_nonneg hτ (overlapOf_nonneg hBs hBt hwS hwT))
    (commonPart_nonNeg (choiceOf_nonNeg hBs hwS) (choiceOf_nonNeg hBt hwT) c)

open Classical in
/-- Thesis Lemma 2.33, the joint of one side: the shared trimmed part
`E` plus the side's own excess `D − E`, glued into profile atoms.  Both
sides instantiate `E` with the **same** trim term, which is what makes
their joints share the coupled mass. -/
private noncomputable def crossJointOf {I : Type*} (cls : X → I)
    (C : Finset I) (D E : I → Dist (Option (Y × PFunDDS.DDS X Y)))
    (w τ : ℝ) : PFunPDS X Y :=
  Dist.fTransform (glueProfile cls)
    (jointProfile τ none C E
      + jointProfile (w - τ) none C fun i => D i - E i)

private theorem weight_choiceOf {vs : Finset Y} {B : Y → PFunPDS X Y}
    {w : ℝ} (_hw : ∑ v ∈ vs, (B v).weight ≤ w) :
    (choiceOf vs B w).weight = w := by
  unfold choiceOf
  rw [weight_classChoiceDist]
  ring

private theorem div_overlapOf_le_one {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ overlapOf vs Bs Bt wS wT i) :
    τ / overlapOf vs Bs Bt wS wT i ≤ 1 :=
  div_le_one_of_le₀ hτ (le_trans hτ0 hτ)

private theorem trimOf_le_left {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ overlapOf vs Bs Bt wS wT i)
    (hSnn : (choiceOf (vs i) (Bs i) wS).NonNeg)
    (hTnn : (choiceOf (vs i) (Bt i) wT).NonNeg) :
    trimOf vs Bs Bt wS wT τ i ≤ choiceOf (vs i) (Bs i) wS := by
  refine Finsupp.le_def.mpr fun c => ?_
  unfold trimOf
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact le_trans
    (mul_le_of_le_one_left (commonPart_nonNeg hSnn hTnn c)
      (div_overlapOf_le_one hτ0 hτ))
    (commonPart_le_left (choiceOf (vs i) (Bs i) wS)
      (choiceOf (vs i) (Bt i) wT) c)

private theorem trimOf_le_right {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ overlapOf vs Bs Bt wS wT i)
    (hSnn : (choiceOf (vs i) (Bs i) wS).NonNeg)
    (hTnn : (choiceOf (vs i) (Bt i) wT).NonNeg) :
    trimOf vs Bs Bt wS wT τ i ≤ choiceOf (vs i) (Bt i) wT := by
  refine Finsupp.le_def.mpr fun c => ?_
  unfold trimOf
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact le_trans
    (mul_le_of_le_one_left (commonPart_nonNeg hSnn hTnn c)
      (div_overlapOf_le_one hτ0 hτ))
    (commonPart_le_right (choiceOf (vs i) (Bs i) wS)
      (choiceOf (vs i) (Bt i) wT) c)

private theorem weight_trimOf {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ overlapOf vs Bs Bt wS wT i) :
    Dist.weight (trimOf vs Bs Bt wS wT τ i) = τ := by
  unfold trimOf
  rw [weight_smul]
  show τ / overlapOf vs Bs Bt wS wT i * overlapOf vs Bs Bt wS wT i = τ
  rcases eq_or_ne (overlapOf vs Bs Bt wS wT i) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact (le_antisymm (hτ.trans h0.le) hτ0).symm
  · exact div_mul_cancel₀ τ h0

private theorem weight_le_weight {A : Type*} {μ ν : Dist A} (h : μ ≤ ν) :
    μ.weight ≤ ν.weight := by
  classical
  rw [Dist.weight_eq_finsupp_sum, Dist.weight_eq_finsupp_sum,
    Finsupp.sum, Finsupp.sum,
    Finset.sum_subset
      (Finset.subset_union_left : μ.support ⊆ μ.support ∪ ν.support)
      (fun a _ ha => Finsupp.notMem_support_iff.mp ha),
    Finset.sum_subset
      (Finset.subset_union_right : ν.support ⊆ μ.support ∪ ν.support)
      (fun a _ ha => Finsupp.notMem_support_iff.mp ha)]
  exact Finset.sum_le_sum fun a _ => Finsupp.le_def.mp h a


private theorem overlapOf_le_left {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {i : I}
    (hwS : ∑ v ∈ vs i, (Bs i v).weight ≤ wS) :
    overlapOf vs Bs Bt wS wT i ≤ wS := by
  refine le_trans (weight_le_weight
    (Finsupp.le_def.mpr (commonPart_le_left _ _))) ?_
  rw [weight_choiceOf hwS]

private theorem overlap_of_le_right {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {i : I}
    (hwT : ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    overlapOf vs Bs Bt wS wT i ≤ wT := by
  refine le_trans (weight_le_weight
    (Finsupp.le_def.mpr (commonPart_le_right _ _))) ?_
  rw [weight_choiceOf hwT]

open Classical in
/-- Thesis Lemma 2.33, marginal preservation (`S`-side, answered
case): the `(x, some v)`-marginal of the `S`-joint recovers the
prescribed branch representative — cleanly, both for `v` in the class
(`= Bs (cls x) v`) and outside (`= 0`, next lemma). -/
private theorem successorTransform_crossJointOf_left {I : Type*}
    {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∈ vs (cls x)) :
    successorTransform (crossJointOf cls C
        (fun i => choiceOf (vs i) (Bs i) wS)
        (trimOf vs Bs Bt wS wT τ) wS τ) x (some v)
      = Bs (cls x) v := by
  unfold crossJointOf
  rw [successorTransform_crossJoint cls C _ _ τ wS
    (fun i hi => trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => weight_trimOf hτ0 (hτ i hi))
    (fun i hi => weight_choiceOf (hwS i hi))
    (fun i hi => trimOf_le_left hτ0 (hτ i hi)
      (choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact contOf_filter_classChoiceDist_of_mem hv

open Classical in
private theorem successorTransform_crossJointOf_left_of_not_mem
    {I : Type*} {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∉ vs (cls x)) :
    successorTransform (crossJointOf cls C
        (fun i => choiceOf (vs i) (Bs i) wS)
        (trimOf vs Bs Bt wS wT τ) wS τ) x (some v)
      = 0 := by
  unfold crossJointOf
  rw [successorTransform_crossJoint cls C _ _ τ wS
    (fun i hi => trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => weight_trimOf hτ0 (hτ i hi))
    (fun i hi => weight_choiceOf (hwS i hi))
    (fun i hi => trimOf_le_left hτ0 (hτ i hi)
      (choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact contOf_filter_classChoiceDist_of_not_mem hv

open Classical in
/-- Thesis Lemma 2.33, marginal preservation (`T`-side, answered
case) — with the **same** shared trim term as the `S`-side. -/
private theorem successorTransform_crossJointOf_right {I : Type*}
    {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∈ vs (cls x)) :
    successorTransform (crossJointOf cls C
        (fun i => choiceOf (vs i) (Bt i) wT)
        (trimOf vs Bs Bt wS wT τ) wT τ) x (some v)
      = Bt (cls x) v := by
  unfold crossJointOf
  rw [successorTransform_crossJoint cls C _ _ τ wT
    (fun i hi => trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => weight_trimOf hτ0 (hτ i hi))
    (fun i hi => weight_choiceOf (hwT i hi))
    (fun i hi => trimOf_le_right hτ0 (hτ i hi)
      (choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact contOf_filter_classChoiceDist_of_mem hv

open Classical in
private theorem successor_transform_cross_joint_of_right_of_not_mem
    {I : Type*} {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∉ vs (cls x)) :
    successorTransform (crossJointOf cls C
        (fun i => choiceOf (vs i) (Bt i) wT)
        (trimOf vs Bs Bt wS wT τ) wT τ) x (some v)
      = 0 := by
  unfold crossJointOf
  rw [successorTransform_crossJoint cls C _ _ τ wT
    (fun i hi => trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => weight_trimOf hτ0 (hτ i hi))
    (fun i hi => weight_choiceOf (hwT i hi))
    (fun i hi => trimOf_le_right hτ0 (hτ i hi)
      (choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact contOf_filter_classChoiceDist_of_not_mem hv

open Classical in
/-- The joint carries the side's full weight. -/
private theorem weight_crossJointOf {I : Type*} {cls : X → I}
    {C : Finset I} (D E : I → Dist (Option (Y × PFunDDS.DDS X Y)))
    {w τ : ℝ} (hE : ∀ i ∈ C, (E i).weight = τ)
    (hD : ∀ i ∈ C, (D i).weight = w) (hle : ∀ i ∈ C, E i ≤ D i)
    (_hτw : τ ≤ w) :
    Dist.weight (crossJointOf cls C D E w τ) = w := by
  unfold crossJointOf
  rw [Dist.weight_fTransform, weight_add,
    jointProfile_weight τ none C E hE,
    jointProfile_weight (w - τ) none C _ fun j hj => by
      rw [weight_tsub_of_le (hle j hj), hD j hj, hE j hj]]
  ring

open Classical in
/-- A cross-query joint is honest whenever its shared part and both excess
parts are honest.  This was implicit when `Dist` used nonnegative
coefficients; it is an explicit invariant on the signed carrier. -/
private theorem crossJointOf_nonNeg {I : Type*} {cls : X → I}
    {C : Finset I} (D E : I → Dist (Option (Y × PFunDDS.DDS X Y)))
    {w τ : ℝ} (hD : ∀ i ∈ C, (D i).NonNeg)
    (hE : ∀ i ∈ C, (E i).NonNeg) (hle : ∀ i ∈ C, E i ≤ D i)
    (hτ0 : 0 ≤ τ) (hτw : τ ≤ w) :
    (crossJointOf cls C D E w τ).NonNeg := by
  unfold crossJointOf
  refine Dist.NonNeg.fTransform ?_ _
  intro p
  rw [Finsupp.add_apply]
  exact add_nonneg
    (jointProfile_nonNeg hτ0 none C hE p)
    (jointProfile_nonNeg (sub_nonneg.mpr hτw) none C
      (fun i hi => sub_nonNeg_of_le (hle i hi)) p)

open Classical in
private theorem jointProfileList_support_default {I CH : Type*}
    [DecidableEq I] (u : ℝ) (d : CH) (D : I → Dist CH) :
    ∀ (l : List I) (p : I → CH),
      p ∈ (jointProfileList u d D l).support → ∀ i, i ∉ l → p i = d := by
  intro l
  induction l with
  | nil =>
      intro p hp i _
      have hmem := Finsupp.support_single_subset hp
      rw [Finset.mem_singleton] at hmem
      rw [hmem]
  | cons j l ih =>
      intro p hp i hi
      simp only [jointProfileList] at hp
      have hp' := Finsupp.mapDomain_support (Finsupp.support_smul hp)
      obtain ⟨⟨c, q⟩, hcq, rfl⟩ := Finset.mem_image.mp hp'
      have hq : q ∈ (jointProfileList u d D l).support := by
        rw [Finsupp.mem_support_iff, Dist.prod_apply] at hcq
        exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hcq).2
      have hij : i ≠ j := fun h => hi (by simp [h])
      have hil : i ∉ l := fun h => hi (by simp [h])
      show Function.update q j c i = d
      rw [Function.update_of_ne hij]
      exact ih q hq i hil

open Classical in
/-- The retraction of `glueProfile`: read a profile back off a system
by probing one representative query of each realized class (the first
answer and the successor there). -/
private noncomputable def profileOf {I : Type*} (cls : X → I)
    (t : PFunDDS.DDS X Y) (i : I) : Option (Y × PFunDDS.DDS X Y) :=
  if h : ∃ x, cls x = i then
    Option.map (fun v => (v, PFunDDS.DDS.successor t (Classical.choose h)))
      (PFunDDS.output (PFunDDS.fullyDefined t) [Classical.choose h]
        (by rw [PFunDDS.dom_fullyDefined]; simp))
  else none

open Classical in
private theorem profileOf_glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × PFunDDS.DDS X Y))
    (hout : ∀ i, ¬(∃ x, cls x = i) → p i = none) :
    profileOf cls (glueProfile cls p) = p := by
  funext i
  unfold profileOf
  split
  · rename_i h
    have hx₀ : cls (Classical.choose h) = i := Classical.choose_spec h
    rw [output_fullyDefined_glueProfile cls p (Classical.choose h), hx₀]
    rcases hc : p i with _ | ⟨v, a⟩
    · rfl
    · simp only [Option.map_some]
      rw [successor_glueProfile_some (show p (cls (Classical.choose h))
          = some (v, a) by rw [hx₀]; exact hc)]
  · rename_i h
    exact (hout i h).symm

open Classical in
private theorem fTransform_profileOf_glueProfile {I : Type*}
    (cls : X → I) (ρ : Dist (I → Option (Y × PFunDDS.DDS X Y)))
    (hsupp : ∀ p ∈ ρ.support, ∀ i, ¬(∃ x, cls x = i) → p i = none) :
    Dist.fTransform (profileOf cls)
        (Dist.fTransform (glueProfile cls) ρ) = ρ := by
  rw [Dist.fTransform_comp]
  refine Eq.trans (fTransform_congr_of_support (g := id) ρ
    fun p hp => profileOf_glueProfile cls p (hsupp p hp))
    (Dist.fTransform_id ρ)

open Classical in
/-- The joints' profile distributions put no choice outside `C`. -/
private theorem add_jointProfile_support_default {I : Type*}
    [DecidableEq I] (u u' : ℝ) (C : Finset I)
    (E F : I → Dist (Option (Y × PFunDDS.DDS X Y))) :
    ∀ p ∈ (jointProfile u none C E + jointProfile u' none C F).support,
      ∀ i, i ∉ C → p i = none := by
  intro p hp i hi
  have hi' : i ∉ C.toList := fun h => hi (Finset.mem_toList.mp h)
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
  · exact jointProfileList_support_default u none E C.toList p h i hi'
  · exact jointProfileList_support_default u' none F C.toList p h i hi'

private theorem δ_tsub_tsub {A : Type*} {μ ν E : Dist A}
    (hE : E.NonNeg) (h₂ : E ≤ ν) : δ (μ - E) (ν - E) = δ μ ν := by
  classical
  have hν : ν.NonNeg := fun a => le_trans (hE a) (Finsupp.le_def.mp h₂ a)
  rw [δ_eq_sum_of_support_subset (sub_nonNeg_of_le h₂)
      (Finset.subset_union_left :
        (μ - E).support ⊆ (μ - E).support ∪ μ.support),
    δ_eq_sum_of_support_subset hν
      (Finset.subset_union_right :
        μ.support ⊆ (μ - E).support ∪ μ.support)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.sub_apply, Finsupp.sub_apply, sub_sub_sub_cancel_right]

open Classical in
/-- Thesis Lemma 2.33, the δ half: the two joints attain the
`S`-oriented divergence `wS − min_{i ∈ C} overlap_i`
(`= max_{i ∈ C} (wS − overlap_i)`).  The `T`-oriented dual holds by
swapping the sides (with `commonPart_comm` for the shared trim); it is
not needed downstream and not proven here. -/
private theorem δ_crossJointOf {I : Type*} {cls : X → I} {C : Finset I}
    {vs : I → Finset Y} {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ}
    (hC : C.Nonempty) (hreal : ∀ i ∈ C, ∃ x, cls x = i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    (δ (crossJointOf cls C (fun i => choiceOf (vs i) (Bs i) wS)
          (trimOf vs Bs Bt wS wT (C.inf' hC (overlapOf vs Bs Bt wS wT)))
          wS (C.inf' hC (overlapOf vs Bs Bt wS wT)))
        (crossJointOf cls C (fun i => choiceOf (vs i) (Bt i) wT)
          (trimOf vs Bs Bt wS wT (C.inf' hC (overlapOf vs Bs Bt wS wT)))
          wT (C.inf' hC (overlapOf vs Bs Bt wS wT))) : ℝ)
      = (wS : ℝ) - (C.inf' hC (overlapOf vs Bs Bt wS wT) : ℝ) := by
  set τ := C.inf' hC (overlapOf vs Bs Bt wS wT) with hτdef
  set E := trimOf vs Bs Bt wS wT τ with hEdef
  set DS := fun i => choiceOf (vs i) (Bs i) wS with hDSdef
  set DT := fun i => choiceOf (vs i) (Bt i) wT with hDTdef
  have hτle : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i :=
    fun i hi => Finset.inf'_le _ hi
  have hDSnn : ∀ i ∈ C, (DS i).NonNeg :=
    fun i hi => choiceOf_nonNeg (hBs i hi) (hwS i hi)
  have hDTnn : ∀ i ∈ C, (DT i).NonNeg :=
    fun i hi => choiceOf_nonNeg (hBt i hi) (hwT i hi)
  have hτ0 : 0 ≤ τ := by
    rw [hτdef]
    exact Finset.le_inf' hC _ fun j hj =>
      overlapOf_nonneg (hBs j hj) (hBt j hj) (hwS j hj) (hwT j hj)
  have hτwS : τ ≤ wS := by
    obtain ⟨i, hi⟩ := hC
    exact (hτle i hi).trans (overlapOf_le_left (hwS i hi))
  have hEnn : ∀ i ∈ C, (E i).NonNeg := fun i hi =>
    trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi)
  have hEw : ∀ i ∈ C, Dist.weight (E i) = τ :=
    fun i hi => weight_trimOf hτ0 (hτle i hi)
  have hDSw : ∀ i ∈ C, Dist.weight (DS i) = wS :=
    fun i hi => weight_choiceOf (hwS i hi)
  have hDTw : ∀ i ∈ C, Dist.weight (DT i) = wT :=
    fun i hi => weight_choiceOf (hwT i hi)
  have hleS : ∀ i ∈ C, E i ≤ DS i := fun i hi =>
    trimOf_le_left hτ0 (hτle i hi) (hDSnn i hi) (hDTnn i hi)
  have hleT : ∀ i ∈ C, E i ≤ DT i := fun i hi =>
    trimOf_le_right hτ0 (hτle i hi) (hDSnn i hi) (hDTnn i hi)
  have hXw : ∀ i ∈ C, Dist.weight (DS i - E i) = wS - τ := fun i hi => by
    rw [weight_tsub_of_le (hleS i hi), hDSw i hi, hEw i hi]
  have hYw : ∀ i ∈ C, Dist.weight (DT i - E i) = wT - τ := fun i hi => by
    rw [weight_tsub_of_le (hleT i hi), hDTw i hi, hEw i hi]
  have hwTτ : 0 ≤ (wT : ℝ) - τ := by
    obtain ⟨i, hi⟩ := hC
    have := weight_le_weight (hleT i hi)
    rw [hEw i hi, hDTw i hi] at this
    linarith
  have hTside : (jointProfile τ none C E
      + jointProfile (wT - τ) none C fun i => DT i - E i).NonNeg := fun p => by
    rw [Finsupp.add_apply]
    exact add_nonneg
      (jointProfile_nonNeg hτ0 none C hEnn p)
      (jointProfile_nonNeg hwTτ none C
        (fun j hj => sub_nonNeg_of_le (hleT j hj)) p)
  have hTside' : (jointProfile (wT - τ) none C fun i => DT i - E i).NonNeg :=
    jointProfile_nonNeg hwTτ none C fun j hj => sub_nonNeg_of_le (hleT j hj)
  have hJρ : δ (crossJointOf cls C DS E wS τ) (crossJointOf cls C DT E wT τ)
      = δ (jointProfile τ none C E
            + jointProfile (wS - τ) none C fun i => DS i - E i)
          (jointProfile τ none C E
            + jointProfile (wT - τ) none C fun i => DT i - E i) := by
    refine le_antisymm (δ_fTransform_le (glueProfile cls) _ hTside) ?_
    have hS := fTransform_profileOf_glueProfile cls
      (jointProfile τ none C E
        + jointProfile (wS - τ) none C fun i => DS i - E i)
      fun p hp i hnx => add_jointProfile_support_default τ (wS - τ) C _ _
        p hp i fun hiC => hnx (hreal i hiC)
    have hT := fTransform_profileOf_glueProfile cls
      (jointProfile τ none C E
        + jointProfile (wT - τ) none C fun i => DT i - E i)
      fun p hp i hnx => add_jointProfile_support_default τ (wT - τ) C _ _
        p hp i fun hiC => hnx (hreal i hiC)
    rw [← hS, ← hT]
    exact δ_fTransform_le (profileOf cls) _ (hTside.fTransform _)
  have hρδ : δ (jointProfile τ none C E
        + jointProfile (wS - τ) none C fun i => DS i - E i)
      (jointProfile τ none C E
        + jointProfile (wT - τ) none C fun i => DT i - E i)
      = δ (jointProfile (wS - τ) none C fun i => DS i - E i)
          (jointProfile (wT - τ) none C fun i => DT i - E i) :=
    δ_add_add_left _ (jointProfile_nonNeg hτ0 none C hEnn) hTside'
  obtain ⟨i₀, hi₀, hτeq⟩ :=
    Finset.exists_mem_eq_inf' hC (overlapOf vs Bs Bt wS wT)
  rw [← hτdef] at hτeq
  have hlow : δ (DS i₀) (DT i₀)
      ≤ δ (jointProfile (wS - τ) none C fun i => DS i - E i)
          (jointProfile (wT - τ) none C fun i => DT i - E i) := by
    have hkey := δ_fTransform_le (fun p => p i₀)
      (jointProfile (wS - τ) none C fun i => DS i - E i)
      hTside'
    rw [jointProfile_marginal (wS - τ) none C _
        (fun j hj => sub_nonNeg_of_le (hleS j hj)) hXw hi₀,
      jointProfile_marginal (wT - τ) none C _
        (fun j hj => sub_nonNeg_of_le (hleT j hj)) hYw hi₀,
      δ_tsub_tsub (hEnn i₀ hi₀) (hleT i₀ hi₀)] at hkey
    exact hkey
  have hval : (δ (DS i₀) (DT i₀) : ℝ)
      = (wS : ℝ) - (overlapOf vs Bs Bt wS wT i₀ : ℝ) := by
    have hδw := δ_eq_weight_sub_weight_commonPart (DS i₀) (hDTnn i₀ hi₀)
    rw [hDSw i₀ hi₀] at hδw
    exact hδw
  have hwSτ : 0 ≤ (wS : ℝ) - τ := by linarith
  have hSside' : (jointProfile (wS - τ) none C fun i => DS i - E i).NonNeg :=
    jointProfile_nonNeg hwSτ none C fun j hj => sub_nonNeg_of_le (hleS j hj)
  rw [hJρ, hρδ]
  refine le_antisymm ?_ ?_
  · exact (δ_le_weight hSside' hTside').trans
      (le_of_eq (jointProfile_weight (wS - τ) none C _ hXw))
  · calc (wS : ℝ) - (τ : ℝ)
        = (wS : ℝ) - (overlapOf vs Bs Bt wS wT i₀ : ℝ) := by rw [hτeq]
      _ = (δ (DS i₀) (DT i₀) : ℝ) := hval.symm
      _ ≤ _ := by exact_mod_cast hlow

open Classical in
private theorem filter_ans_fTransform_glueProfile {I : Type*}
    (cls : X → I) (ρ : Dist (I → Option (Y × PFunDDS.DDS X Y)))
    (x : X) (y₀ : Option Y) :
    (Dist.fTransform (glueProfile cls) ρ).filter
      (fun t => PFunDDS.output (PFunDDS.fullyDefined t) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = y₀)
      = Dist.fTransform (glueProfile cls)
          (ρ.filter fun p => Option.map Prod.fst (p (cls x)) = y₀) := by
  rw [filter_fTransform]
  refine congrArg (Dist.fTransform (glueProfile cls)) ?_
  refine Finsupp.ext fun p => ?_
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hp : Option.map Prod.fst (p (cls x)) = y₀
  · rw [if_pos hp,
      if_pos ((output_fullyDefined_glueProfile cls p x).trans hp)]
  · rw [if_neg hp, if_neg fun h => hp
      ((output_fullyDefined_glueProfile cls p x).symm.trans h)]

open Classical in
private theorem weight_filter_marginal {I : Type*} (cls : X → I)
    (ρ : Dist (I → Option (Y × PFunDDS.DDS X Y))) (x : X)
    (y₀ : Option Y) :
    Dist.weight (ρ.filter fun p => Option.map Prod.fst (p (cls x)) = y₀)
      = Dist.weight ((Dist.fTransform (fun p => p (cls x)) ρ).filter
          fun c => Option.map Prod.fst c = y₀) := by
  rw [filter_fTransform, Dist.weight_fTransform]

open Classical in
/-- Thesis Lemma 2.33, the `⊥`-bookkeeping (`S`-side): the joint's
`⊥`-marginal weight at any query of a participating class is exactly
the class's pass-through mass — no `⊥`-branch representative exists or
is needed (`successorTransform_none_eq_filter`); milestone 4 recurses
on the joint's own `⊥`-filter. -/
private theorem weight_successorTransform_none_crossJointOf {I : Type*}
    {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) :
    Dist.weight (successorTransform (crossJointOf cls C
        (fun i => choiceOf (vs i) (Bs i) wS)
        (trimOf vs Bs Bt wS wT τ) wS τ) x none)
      = wS - ∑ v ∈ vs (cls x), (Bs (cls x) v).weight := by
  have htleS : ∀ j ∈ C, trimOf vs Bs Bt wS wT τ j ≤ choiceOf (vs j) (Bs j) wS :=
    fun j hj => trimOf_le_left hτ0 (hτ j hj)
      (choiceOf_nonNeg (hBs j hj) (hwS j hj))
      (choiceOf_nonNeg (hBt j hj) (hwT j hj))
  have hX' : ∀ j ∈ C, Dist.weight
      (choiceOf (vs j) (Bs j) wS - trimOf vs Bs Bt wS wT τ j)
      = wS - τ := by
    intro j hj
    rw [weight_tsub_of_le (htleS j hj),
      weight_choiceOf (hwS j hj), weight_trimOf hτ0 (hτ j hj)]
  unfold successorTransform crossJointOf
  rw [Dist.weight_fTransform, filter_ans_fTransform_glueProfile,
    Dist.weight_fTransform, weight_filter_marginal, fTransform_add,
    jointProfile_marginal τ none C _
      (fun i hi => trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
      (fun i hi => weight_trimOf hτ0 (hτ i hi)) hx,
    jointProfile_marginal (wS - τ) none C _
      (fun j hj => sub_nonNeg_of_le (htleS j hj)) hX' hx,
    add_sub_cancel_finsupp]
  have hfin : Finsupp.filter (fun c => Option.map Prod.fst c = none)
      ((fun i => choiceOf (vs i) (Bs i) wS) (cls x))
      = Finsupp.single none
          (wS - ∑ v ∈ vs (cls x), (Bs (cls x) v).weight) :=
    filter_none_classChoiceDist (vs (cls x)) (Bs (cls x)) _
  rw [hfin, weight_single]

open Classical in
private theorem weight_successor_transform_none_cross_joint_of_right
    {I : Type*} {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PFunPDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) :
    Dist.weight (successorTransform (crossJointOf cls C
        (fun i => choiceOf (vs i) (Bt i) wT)
        (trimOf vs Bs Bt wS wT τ) wT τ) x none)
      = wT - ∑ v ∈ vs (cls x), (Bt (cls x) v).weight := by
  have htleT : ∀ j ∈ C, trimOf vs Bs Bt wS wT τ j ≤ choiceOf (vs j) (Bt j) wT :=
    fun j hj => trimOf_le_right hτ0 (hτ j hj)
      (choiceOf_nonNeg (hBs j hj) (hwS j hj))
      (choiceOf_nonNeg (hBt j hj) (hwT j hj))
  have hY' : ∀ j ∈ C, Dist.weight
      (choiceOf (vs j) (Bt j) wT - trimOf vs Bs Bt wS wT τ j)
      = wT - τ := by
    intro j hj
    rw [weight_tsub_of_le (htleT j hj),
      weight_choiceOf (hwT j hj), weight_trimOf hτ0 (hτ j hj)]
  unfold successorTransform crossJointOf
  rw [Dist.weight_fTransform, filter_ans_fTransform_glueProfile,
    Dist.weight_fTransform, weight_filter_marginal, fTransform_add,
    jointProfile_marginal τ none C _
      (fun i hi => trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
      (fun i hi => weight_trimOf hτ0 (hτ i hi)) hx,
    jointProfile_marginal (wT - τ) none C _
      (fun j hj => sub_nonNeg_of_le (htleT j hj)) hY' hx,
    add_sub_cancel_finsupp]
  have hfin : Finsupp.filter (fun c => Option.map Prod.fst c = none)
      ((fun i => choiceOf (vs i) (Bt i) wT) (cls x))
      = Finsupp.single none
          (wT - ∑ v ∈ vs (cls x), (Bt (cls x) v).weight) :=
    filter_none_classChoiceDist (vs (cls x)) (Bt (cls x)) _
  rw [hfin, weight_single]

open Classical in
private theorem pairwise_disjoint_support_tagged_branches
    (Bs Bt : Y → PFunPDS X Y) (vs : Finset Y) :
    (↑vs : Set Y).PairwiseDisjoint fun v =>
      (Dist.fTransform (fun s => some (v, s)) (Bs v)).support ∪
        (Dist.fTransform (fun s => some (v, s)) (Bt v)).support := by
  intro v _ v' _ hvv'
  refine Finset.disjoint_left.mpr fun c hc hc' => ?_
  have hshape : ∀ {z : Y},
      c ∈ (Dist.fTransform (fun s => some (z, s)) (Bs z)).support ∪
          (Dist.fTransform (fun s => some (z, s)) (Bt z)).support →
      ∃ s, c = some (z, s) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support hz)
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support hz)
      exact ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := hshape hc
  obtain ⟨t, ht⟩ := hshape hc'
  exact hvv' (congrArg Prod.fst (Option.some.inj (hs.symm.trans ht)))

open Classical in
private theorem delta_choice_of_eq_sum_of_branch_deltas_of_exact_weight
    {vs : Finset Y} {Bs Bt : Y → PFunPDS X Y} {wS wT : ℝ}
    (hBt : ∀ v ∈ vs, (Bt v).NonNeg)
    (hwS : ∑ v ∈ vs, (Bs v).weight = wS)
    (hwT : ∑ v ∈ vs, (Bt v).weight = wT) :
    δ (choiceOf vs Bs wS) (choiceOf vs Bt wT) =
      ∑ v ∈ vs, δ (Bs v) (Bt v) := by
  classical
  unfold choiceOf classChoiceDist
  rw [← hwS, ← hwT]
  simp only [sub_self, Finsupp.single_zero, add_zero]
  rw [show (∑ v ∈ vs, Dist.fTransform (fun s => some (v, s)) (Bs v))
        = ∑ v ∈ vs, Dist.fTransform
            (fun s : PFunDDS.DDS X Y => (some (v, s) : Option (Y × PFunDDS.DDS X Y)))
            ((fun v => Bs v) v) from rfl,
    δ_sum_of_disjoint_support _ _
      (fun v hv => (hBt v hv).fTransform _)
      (pairwise_disjoint_support_tagged_branches Bs Bt vs)]
  exact Finset.sum_congr rfl fun v hv =>
    δ_fTransform_eq_of_injective
      (f := fun s : PFunDDS.DDS X Y => some (v, s))
      (fun _ _ h => congrArg Prod.snd (Option.some.inj h)) (Bs v) (hBt v hv)

open Classical in
private theorem support_cross_joint_rejects_of_class_not_mem
    {I : Type*} {cls : X → I} {C : Finset I}
    (D E : I → Dist (Option (Y × PFunDDS.DDS X Y)))
    (w τ : ℝ) {x : X} (hx : cls x ∉ C) :
    ∀ s ∈ (crossJointOf cls C D E w τ).support,
      [x] ∉ PFunDDS.dom s := by
  intro s hs
  unfold crossJointOf at hs
  obtain ⟨p, hp, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  apply output_fullyDefined_eq_none_iff.mp
  rw [output_fullyDefined_glueProfile]
  have hpnone := add_jointProfile_support_default τ (w - τ) C E
    (fun i => D i - E i) p hp (cls x) hx
  simp [hpnone]

/-- The source-shaped output of thesis Lemma 2.33 / LanMau20 Lemma 6.

The participating classes are finite, every left branch family reassembles to
the common left weight `wS`, and every right branch family reassembles to the
possibly different common right weight `wT`.  The joint systems expose the
prescribed successor marginals, reject queries outside the participating
classes, and attain the largest per-class sum of branch distances. -/
structure FiniteClassJointWitness {I : Type*} (cls : X → I) (C : Finset I)
    (vs : I → Finset Y) (Bs Bt : I → Y → PFunPDS X Y)
    (wS wT : ℝ) where
  left : PFunPDS X Y
  right : PFunPDS X Y
  left_nonNeg : left.NonNeg
  right_nonNeg : right.NonNeg
  chosen : I
  chosen_mem : chosen ∈ C
  left_weight : left.weight = wS
  right_weight : right.weight = wT
  left_successor_of_mem : ∀ {x v}, cls x ∈ C → v ∈ vs (cls x) →
    successorTransform left x (some v) = Bs (cls x) v
  right_successor_of_mem : ∀ {x v}, cls x ∈ C → v ∈ vs (cls x) →
    successorTransform right x (some v) = Bt (cls x) v
  left_successor_of_not_mem : ∀ {x v}, cls x ∈ C → v ∉ vs (cls x) →
    successorTransform left x (some v) = 0
  right_successor_of_not_mem : ∀ {x v}, cls x ∈ C → v ∉ vs (cls x) →
    successorTransform right x (some v) = 0
  left_successor_none : ∀ {x}, cls x ∈ C →
    successorTransform left x none = 0
  right_successor_none : ∀ {x}, cls x ∈ C →
    successorTransform right x none = 0
  left_rejects_of_class_not_mem : ∀ {x}, cls x ∉ C →
    ∀ s ∈ left.support, [x] ∉ PFunDDS.dom s
  right_rejects_of_class_not_mem : ∀ {x}, cls x ∉ C →
    ∀ t ∈ right.support, [x] ∉ PFunDDS.dom t
  delta_eq_selected_sum :
    (δ left right : ℝ) =
      ∑ v ∈ vs chosen, (δ (Bs chosen v) (Bt chosen v) : ℝ)
  branch_sum_le_delta : ∀ i ∈ C,
    (∑ v ∈ vs i, (δ (Bs i v) (Bt i v) : ℝ)) ≤
      (δ left right : ℝ)

open Classical in
/-- Thesis Lemma 2.33 / LanMau20 Lemma 6 specialized to finite
first-query classes.  The two sides may have different common weights; only
the weights within each side are required to agree. -/
theorem exists_finite_class_joint_witness_of_common_side_weights
    {I : Type*} (cls : X → I) (C : Finset I) (hC : C.Nonempty)
    (hreal : ∀ i ∈ C, ∃ x, cls x = i) (vs : I → Finset Y)
    (Bs Bt : I → Y → PFunPDS X Y) (wS wT : ℝ)
    (hBsnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBtnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight = wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight = wT) :
    Nonempty (FiniteClassJointWitness cls C vs Bs Bt wS wT) := by
  let τ := C.inf' hC (overlapOf vs Bs Bt wS wT)
  let E := trimOf vs Bs Bt wS wT τ
  let S' := crossJointOf cls C (fun i => choiceOf (vs i) (Bs i) wS)
    E wS τ
  let T' := crossJointOf cls C (fun i => choiceOf (vs i) (Bt i) wT)
    E wT τ
  have hτle : ∀ i ∈ C, τ ≤ overlapOf vs Bs Bt wS wT i :=
    fun i hi => Finset.inf'_le _ hi
  have hτ0 : 0 ≤ τ :=
    Finset.le_inf' hC _ fun j hj =>
      overlapOf_nonneg (hBsnn j hj) (hBtnn j hj) (hwS j hj).le (hwT j hj).le
  have hτwS : τ ≤ wS := by
    obtain ⟨i, hi⟩ := hC
    exact (hτle i hi).trans (overlapOf_le_left (hwS i hi).le)
  have hτwT : τ ≤ wT := by
    obtain ⟨i, hi⟩ := hC
    exact (hτle i hi).trans (overlap_of_le_right (hwT i hi).le)
  have hSw : S'.weight = wS := by
    dsimp [S', E]
    exact weight_crossJointOf _ _
      (fun i hi => weight_trimOf hτ0 (hτle i hi))
      (fun i hi => weight_choiceOf (hwS i hi).le)
      (fun i hi => trimOf_le_left hτ0 (hτle i hi)
        (choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτwS
  have hTw : T'.weight = wT := by
    dsimp [T', E]
    exact weight_crossJointOf _ _
      (fun i hi => weight_trimOf hτ0 (hτle i hi))
      (fun i hi => weight_choiceOf (hwT i hi).le)
      (fun i hi => trimOf_le_right hτ0 (hτle i hi)
        (choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτwT
  have hSnn : S'.NonNeg := by
    dsimp [S', E]
    exact crossJointOf_nonNeg _ _
      (fun i hi => choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
      (fun i hi => trimOf_nonNeg hτ0 (hBsnn i hi) (hBtnn i hi)
        (hwS i hi).le (hwT i hi).le)
      (fun i hi => trimOf_le_left hτ0 (hτle i hi)
        (choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτ0 hτwS
  have hTnn : T'.NonNeg := by
    dsimp [T', E]
    exact crossJointOf_nonNeg _ _
      (fun i hi => choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)
      (fun i hi => trimOf_nonNeg hτ0 (hBsnn i hi) (hBtnn i hi)
        (hwS i hi).le (hwT i hi).le)
      (fun i hi => trimOf_le_right hτ0 (hτle i hi)
        (choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτ0 hτwT
  obtain ⟨i₀, hi₀, hτeq⟩ :=
    Finset.exists_mem_eq_inf' hC (overlapOf vs Bs Bt wS wT)
  have hτeq' : overlapOf vs Bs Bt wS wT i₀ = τ := by
    simpa [τ] using hτeq.symm
  have hcross : (δ S' T' : ℝ) = (wS : ℝ) - (τ : ℝ) := by
    simpa [S', T', E, τ] using
      δ_crossJointOf (cls := cls) (vs := vs) (Bs := Bs) (Bt := Bt)
        (wS := wS) (wT := wT) hC hreal hBsnn hBtnn
        (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le)
  have hbranch : ∀ i ∈ C,
      (∑ v ∈ vs i, (δ (Bs i v) (Bt i v) : ℝ)) =
        (wS : ℝ) - (overlapOf vs Bs Bt wS wT i : ℝ) := by
    intro i hi
    have hδ := δ_eq_weight_sub_weight_commonPart
      (choiceOf (vs i) (Bs i) wS)
      (choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)
    rw [weight_choiceOf (hwS i hi).le,
      delta_choice_of_eq_sum_of_branch_deltas_of_exact_weight
        (hBtnn i hi) (hwS i hi) (hwT i hi)] at hδ
    simpa [overlapOf] using hδ
  refine ⟨{
    left := S'
    right := T'
    left_nonNeg := hSnn
    right_nonNeg := hTnn
    chosen := i₀
    chosen_mem := hi₀
    left_weight := hSw
    right_weight := hTw
    left_successor_of_mem := ?_
    right_successor_of_mem := ?_
    left_successor_of_not_mem := ?_
    right_successor_of_not_mem := ?_
    left_successor_none := ?_
    right_successor_none := ?_
    left_rejects_of_class_not_mem := ?_
    right_rejects_of_class_not_mem := ?_
    delta_eq_selected_sum := ?_
    branch_sum_le_delta := ?_
  }⟩
  · intro x v hx hv
    simpa [S', E] using successorTransform_crossJointOf_left
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x v hx hv
    simpa [T', E] using successorTransform_crossJointOf_right
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x v hx hv
    simpa [S', E] using successorTransform_crossJointOf_left_of_not_mem
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x v hx hv
    simpa [T', E] using successor_transform_cross_joint_of_right_of_not_mem
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x hx
    have hnn : (successorTransform S' x none).NonNeg := by
      dsimp [S', E]
      unfold successorTransform crossJointOf
      refine Dist.NonNeg.fTransform ?_ _
      intro t
      rw [Finsupp.filter_apply]
      split
      · refine Dist.NonNeg.fTransform (fun p => ?_) _ t
        rw [Finsupp.add_apply]
        refine add_nonneg
          (jointProfile_nonNeg hτ0 none C (fun j hj =>
            trimOf_nonNeg hτ0 (hBsnn j hj) (hBtnn j hj)
              (hwS j hj).le (hwT j hj).le) p) ?_
        refine jointProfile_nonNeg (by
            have := hτwS
            push_cast
            linarith) none C
          (fun j hj => sub_nonNeg_of_le (trimOf_le_left hτ0 (hτle j hj)
            (choiceOf_nonNeg (hBsnn j hj) (hwS j hj).le)
            (choiceOf_nonNeg (hBtnn j hj) (hwT j hj).le))) p
      · exact le_refl 0
    apply eq_zero_of_weight_eq_zero hnn
    rw [show Dist.weight (successorTransform S' x none) =
        wS - ∑ v ∈ vs (cls x), (Bs (cls x) v).weight by
      simpa [S', E] using weight_successorTransform_none_crossJointOf
        hτ0 hτle hBsnn hBtnn
        (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx,
      hwS (cls x) hx, sub_self]
  · intro x hx
    have hnn : (successorTransform T' x none).NonNeg := by
      dsimp [T', E]
      unfold successorTransform crossJointOf
      refine Dist.NonNeg.fTransform ?_ _
      intro t
      rw [Finsupp.filter_apply]
      split
      · refine Dist.NonNeg.fTransform (fun p => ?_) _ t
        rw [Finsupp.add_apply]
        refine add_nonneg
          (jointProfile_nonNeg hτ0 none C (fun j hj =>
            trimOf_nonNeg hτ0 (hBsnn j hj) (hBtnn j hj)
              (hwS j hj).le (hwT j hj).le) p) ?_
        refine jointProfile_nonNeg (by
            have := hτwT
            push_cast
            linarith) none C
          (fun j hj => sub_nonNeg_of_le (trimOf_le_right hτ0 (hτle j hj)
            (choiceOf_nonNeg (hBsnn j hj) (hwS j hj).le)
            (choiceOf_nonNeg (hBtnn j hj) (hwT j hj).le))) p
      · exact le_refl 0
    apply eq_zero_of_weight_eq_zero hnn
    rw [show Dist.weight (successorTransform T' x none) =
        wT - ∑ v ∈ vs (cls x), (Bt (cls x) v).weight by
      simpa [T', E] using weight_successor_transform_none_cross_joint_of_right
        hτ0 hτle hBsnn hBtnn
        (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx,
      hwT (cls x) hx, sub_self]
  · intro x hx
    simpa [S', E] using support_cross_joint_rejects_of_class_not_mem
      (X := X) (Y := Y) (cls := cls)
      (fun i => choiceOf (vs i) (Bs i) wS) E wS τ hx
  · intro x hx
    simpa [T', E] using support_cross_joint_rejects_of_class_not_mem
      (X := X) (Y := Y) (cls := cls)
      (fun i => choiceOf (vs i) (Bt i) wT) E wT τ hx
  · calc
      (δ S' T' : ℝ) = (wS : ℝ) - (τ : ℝ) := hcross
      _ = (wS : ℝ) - (overlapOf vs Bs Bt wS wT i₀ : ℝ) := by
        rw [hτeq']
      _ = ∑ v ∈ vs i₀, (δ (Bs i₀ v) (Bt i₀ v) : ℝ) :=
        (hbranch i₀ hi₀).symm
  · intro i hi
    calc
      (∑ v ∈ vs i, (δ (Bs i v) (Bt i v) : ℝ)) =
          (wS : ℝ) - (overlapOf vs Bs Bt wS wT i : ℝ) :=
        hbranch i hi
      _ ≤ (wS : ℝ) - (τ : ℝ) := by
        exact sub_le_sub_left (by exact_mod_cast hτle i hi) _
      _ = (δ S' T' : ℝ) := hcross.symm

/-! ### Interval layouts (thesis Lemma 2.33, piece indexing;
milestone-4 stage A, design per papers/notes/THM231_ATTAINMENT.md §5) -/

/-- A **layout** is a list of (value, mass) entries presenting a
sub-distribution laid out along an interval; values may repeat (an
atom's mass may be split into a common block and an excess block).
`layoutDist` is the distribution a layout presents. -/
private noncomputable def layoutDist {α : Type*} (L : List (α × ℝ)) :
    Dist α :=
  (L.map fun e => Finsupp.single e.1 e.2).sum

private def layoutTotal {α : Type*} (L : List (α × ℝ)) : ℝ :=
  (L.map Prod.snd).sum

/-- The cut positions of a layout: all prefix sums, `0` and the total
included. -/
private def layoutCuts {α : Type*} (L : List (α × ℝ)) :
    List ℝ :=
  (List.range (L.length + 1)).map fun k => layoutTotal (L.take k)

/-- The value a layout shows at position `u` (the first entry whose
cumulative interval contains `u`; the default `d` beyond the total). -/
private noncomputable def valueAt {α : Type*} (d : α) :
    List (α × ℝ) → ℝ → α
  | [], _ => d
  | e :: L, u => if u < e.2 then e.1 else valueAt d L (u - e.2)

private theorem layoutDist_nil {α : Type*} :
    layoutDist ([] : List (α × ℝ)) = 0 :=
  rfl

private theorem layoutDist_cons {α : Type*} (e : α × ℝ)
    (L : List (α × ℝ)) :
    layoutDist (e :: L) = Finsupp.single e.1 e.2 + layoutDist L := by
  unfold layoutDist
  rw [List.map_cons, List.sum_cons]

private theorem layoutTotal_nil {α : Type*} :
    layoutTotal ([] : List (α × ℝ)) = 0 :=
  rfl

private theorem layoutTotal_cons {α : Type*} (e : α × ℝ)
    (L : List (α × ℝ)) :
    layoutTotal (e :: L) = e.2 + layoutTotal L := by
  unfold layoutTotal
  rw [List.map_cons, List.sum_cons]

private theorem weight_layoutDist {α : Type*} (L : List (α × ℝ)) :
    Dist.weight (layoutDist L) = layoutTotal L := by
  induction L with
  | nil =>
      rw [layoutDist_nil, layoutTotal_nil, Dist.weight_eq_finsupp_sum]
      exact Finsupp.sum_zero_index
  | cons e L ih =>
      rw [layoutDist_cons, weight_add, weight_single, ih,
        layoutTotal_cons]

private theorem zero_mem_layoutCuts {α : Type*} (L : List (α × ℝ)) :
    0 ∈ layoutCuts L := by
  unfold layoutCuts
  refine List.mem_map.mpr ⟨0, ?_, rfl⟩
  exact List.mem_range.mpr (Nat.succ_pos _)

private theorem total_mem_layoutCuts {α : Type*}
    (L : List (α × ℝ)) :
    layoutTotal L ∈ layoutCuts L := by
  unfold layoutCuts
  refine List.mem_map.mpr ⟨L.length, ?_, ?_⟩
  · exact List.mem_range.mpr (Nat.lt_succ_self _)
  · rw [List.take_length]

/-- The piecewise reassembly of a layout along a cut list: one point
mass per consecutive-cut piece, at the layout's value there. -/
private noncomputable def pieceDist {α : Type*} (d : α)
    (L : List (α × ℝ)) : List ℝ → Dist α
  | u :: u' :: us => Finsupp.single (valueAt d L u) (u' - u)
      + pieceDist d L (u' :: us)
  | _ => 0

private theorem sorted_head_le {l : List ℝ}
    (hs : l.Pairwise (· ≤ ·)) (hne : l ≠ []) :
    ∀ u ∈ l, l.head hne ≤ u := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
      intro u hu
      rw [List.head_cons]
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact le_refl _
      · exact (List.pairwise_cons.mp hs).1 u hu'

private theorem sorted_le_getLast {l : List ℝ}
    (hs : l.Pairwise (· ≤ ·)) (hne : l ≠ []) :
    ∀ u ∈ l, u ≤ l.getLast hne := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a l ih =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · cases l with
        | nil => exact le_of_eq rfl
        | cons a' l' =>
            rw [List.getLast_cons (List.cons_ne_nil a' l')]
            exact le_trans ((List.pairwise_cons.mp hs).1 a' (by simp))
              (ih (List.pairwise_cons.mp hs).2 (List.cons_ne_nil a' l')
                a' (by simp))
      · cases l with
        | nil => simp at hu'
        | cons a' l' =>
            rw [List.getLast_cons (List.cons_ne_nil a' l')]
            exact ih (List.pairwise_cons.mp hs).2 (List.cons_ne_nil a' l')
              u hu'

private theorem pieceDist_append {α : Type*} (d : α)
    (L : List (α × ℝ)) :
    ∀ (A : List ℝ) (c : ℝ) (B : List ℝ),
      pieceDist d L (A ++ c :: B)
        = pieceDist d L (A ++ [c]) + pieceDist d L (c :: B) := by
  intro A
  induction A with
  | nil =>
      intro c B
      simp only [List.nil_append, pieceDist]
      rw [zero_add]
  | cons a A' ih =>
      intro c B
      cases A' with
      | nil =>
          simp only [List.cons_append, List.nil_append, pieceDist]
          rw [add_zero]
      | cons a' A'' =>
          have ih' := ih c B
          simp only [List.cons_append] at ih' ⊢
          simp only [pieceDist]
          rw [ih', add_assoc]

/-- All pieces inside the first entry's interval show that entry's
value; their masses telescope. -/
private theorem pieceDist_const {α : Type*} (d : α) (e : α × ℝ)
    (L' : List (α × ℝ)) :
    ∀ (vs : List ℝ) (hne : vs ≠ []), vs.Pairwise (· ≤ ·) →
      (∀ u ∈ vs.dropLast, u < e.2) →
      pieceDist d (e :: L') vs
        = Finsupp.single e.1 (vs.getLast hne - vs.head hne) := by
  intro vs
  induction vs with
  | nil => intro hne; exact absurd rfl hne
  | cons u vs ih =>
      intro hne hsort hlt
      cases vs with
      | nil =>
          simp only [pieceDist, List.getLast_singleton, List.head_cons,
            sub_self, Finsupp.single_zero]
      | cons u' vs' =>
          have hu : u < e.2 := hlt u (by simp [List.dropLast_cons_of_ne_nil])
          have htail := (List.pairwise_cons.mp hsort).2
          have hlt' : ∀ z ∈ (u' :: vs').dropLast, z < e.2 := by
            intro z hz
            refine hlt z ?_
            rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil u' vs')]
            exact List.mem_cons_of_mem u hz
          simp only [pieceDist]
          rw [ih (List.cons_ne_nil u' vs') htail hlt',
            valueAt, if_pos hu, List.getLast_cons (List.cons_ne_nil u' vs'),
            List.head_cons, List.head_cons, ← Finsupp.single_add]
          refine congrArg _ ?_
          ring

/-- Pieces past the first entry's interval shift into the tail
layout. -/
private theorem pieceDist_shift {α : Type*} (d : α) (e : α × ℝ)
    (L' : List (α × ℝ)) :
    ∀ vs : List ℝ, (∀ u ∈ vs, e.2 ≤ u) →
      pieceDist d (e :: L') vs
        = pieceDist d L' (vs.map (· - e.2)) := by
  intro vs
  induction vs with
  | nil => intro _; rfl
  | cons u vs ih =>
      intro hge
      cases vs with
      | nil => rfl
      | cons u' vs' =>
          have ih' := ih fun z hz => hge z (List.mem_cons_of_mem u hz)
          simp only [List.map_cons] at ih'
          simp only [pieceDist, List.map_cons]
          rw [← ih', valueAt, if_neg (not_lt.mpr (hge u (by simp))),
            tsub_tsub_tsub_cancel_right (hge u (by simp))]

private theorem pieceDist_nil_layout {α : Type*} (d : α) :
    ∀ us : List ℝ, (∀ u ∈ us, u = 0) →
      pieceDist d ([] : List (α × ℝ)) us = 0 := by
  intro us
  induction us with
  | nil => intro _; rfl
  | cons u vs ih =>
      intro hz
      cases vs with
      | nil => rfl
      | cons u' vs' =>
          simp only [pieceDist]
          have hm : u' - u = 0 := by
            rw [hz u' (by simp), hz u (by simp), sub_self]
          rw [hm, Finsupp.single_zero, zero_add]
          exact ih fun z hz' => hz z (List.mem_cons_of_mem u hz')

private theorem pairwise_map_tsub {m : ℝ} {l : List ℝ}
    (hge : ∀ u ∈ l, m ≤ u) (hpw : l.Pairwise (· < ·)) :
    (l.map (· - m)).Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons]
      refine List.pairwise_cons.mpr
        ⟨?_, ih (fun u hu => hge u (List.mem_cons_of_mem a hu))
          (List.pairwise_cons.mp hpw).2⟩
      intro z hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      exact tsub_lt_tsub_right_of_le (hge a (by simp))
        ((List.pairwise_cons.mp hpw).1 u hu)

private theorem getLast_map_tsub (m : ℝ) :
    ∀ (l : List ℝ) (hne : l ≠ []) (hne' : l.map (· - m) ≠ []),
      (l.map (· - m)).getLast hne' = l.getLast hne - m := by
  intro l
  induction l with
  | nil => intro hne _; exact absurd rfl hne
  | cons a l ih =>
      intro hne hne'
      cases l with
      | nil => rfl
      | cons a' l' =>
          show ((a - m) :: (a' :: l').map (· - m)).getLast (by simp)
            = (a :: a' :: l').getLast hne - m
          rw [List.getLast_cons (by simp : (a' :: l').map (· - m) ≠ []),
            List.getLast_cons (List.cons_ne_nil a' l')]
          exact ih (List.cons_ne_nil a' l') (by simp)

private theorem getLast_append_cons {α : Type*} :
    ∀ (A : List α) (c : α) (B : List α) (hne : A ++ c :: B ≠ []),
      (A ++ c :: B).getLast hne
        = (c :: B).getLast (List.cons_ne_nil c B) := by
  intro A
  induction A with
  | nil => intro c B hne; rfl
  | cons a A' ih =>
      intro c B hne
      show (a :: (A' ++ c :: B)).getLast (by simp)
        = (c :: B).getLast (List.cons_ne_nil c B)
      rw [List.getLast_cons (by simp : A' ++ c :: B ≠ [])]
      exact ih c B (by simp)

private theorem layoutCuts_cons {α : Type*} (e : α × ℝ)
    (L : List (α × ℝ)) :
    layoutCuts (e :: L) = 0 :: (layoutCuts L).map (e.2 + ·) := by
  unfold layoutCuts
  rw [show (e :: L).length + 1 = (L.length + 1) + 1 from rfl,
    List.range_succ_eq_map, List.map_cons, List.map_map, List.map_map]
  congr 1

/-- Stage-A reconstruction (thesis Lemma 2.33, piece indexing): a
strictly sorted cut list from `0` to the total that refines a layout's
cuts reassembles the layout's distribution piece by piece. -/
private theorem layoutTotal_nonneg {α : Type*} :
    ∀ {L : List (α × ℝ)}, (∀ e ∈ L, 0 ≤ e.2) → 0 ≤ layoutTotal L := by
  intro L
  induction L with
  | nil => intro _; rw [layoutTotal_nil]
  | cons e L ih =>
      intro hL
      rw [layoutTotal_cons]
      exact add_nonneg (hL e (by simp))
        (ih fun z hz => hL z (List.mem_cons_of_mem e hz))

private theorem layoutCuts_nonneg {α : Type*} {L : List (α × ℝ)}
    (hL : ∀ e ∈ L, 0 ≤ e.2) : ∀ c ∈ layoutCuts L, 0 ≤ c := by
  intro c hc
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
  exact layoutTotal_nonneg fun e he => hL e ((List.take_sublist k L).mem he)

private theorem pieceDist_eq_layoutDist {α : Type*} (d : α) :
    ∀ (L : List (α × ℝ)) (hL : ∀ e ∈ L, 0 ≤ e.2)
      (us : List ℝ) (hne : us ≠ []),
      us.Pairwise (· < ·) → us.head hne = 0 →
      us.getLast hne = layoutTotal L →
      (∀ c ∈ layoutCuts L, c ∈ us) →
      pieceDist d L us = layoutDist L := by
  intro L
  induction L with
  | nil =>
      intro _ us hne hsort hhead hlast _
      rw [layoutDist_nil]
      refine pieceDist_nil_layout d us fun u hu => ?_
      refine le_antisymm ?_ ?_
      · have hle := sorted_le_getLast (hsort.imp le_of_lt) hne u hu
        rw [hlast, layoutTotal_nil] at hle
        exact hle
      · have hge := sorted_head_le (hsort.imp le_of_lt) hne u hu
        rw [hhead] at hge
        exact hge
  | cons e L' ih =>
      intro hL us hne hsort hhead hlast hcuts
      have hL' : ∀ z ∈ L', 0 ≤ z.2 := fun z hz => hL z (List.mem_cons_of_mem e hz)
      have hm : e.2 ∈ us := by
        refine hcuts e.2 ?_
        have h1 : layoutTotal ((e :: L').take 1) = e.2 := by
          rw [List.take_succ_cons, List.take_zero, layoutTotal_cons,
            layoutTotal_nil, add_zero]
        rw [← h1]
        exact List.mem_map.mpr
          ⟨1, List.mem_range.mpr (by rw [List.length_cons]; omega), rfl⟩
      obtain ⟨A, B', hsplit⟩ := List.append_of_mem hm
      subst hsplit
      have hAlt : ∀ u ∈ A, u < e.2 :=
        fun u hu => (List.pairwise_append.mp hsort).2.2 u hu e.2 (by simp)
      have hAm_ne : A ++ [e.2] ≠ [] := by simp
      rw [pieceDist_append d (e :: L') A e.2 B']
      have hleft : pieceDist d (e :: L') (A ++ [e.2])
          = Finsupp.single e.1 e.2 := by
        have hs1 : (A ++ [e.2]).Pairwise (· ≤ ·) := by
          refine List.Pairwise.imp le_of_lt ?_
          refine List.pairwise_append.mpr
            ⟨(List.pairwise_append.mp hsort).1,
              List.pairwise_singleton _ _, fun a ha c hc => ?_⟩
          rw [List.mem_singleton.mp hc]
          exact hAlt a ha
        have hdl : ∀ u ∈ (A ++ [e.2]).dropLast, u < e.2 := by
          rw [List.dropLast_concat]
          exact hAlt
        rw [pieceDist_const d e L' (A ++ [e.2]) hAm_ne hs1 hdl]
        have hgl : (A ++ [e.2]).getLast hAm_ne = e.2 :=
          List.getLast_concat
        have hhd : (A ++ [e.2]).head hAm_ne = 0 := by
          cases A with
          | nil => simpa using hhead
          | cons a A'' => simpa using hhead
        rw [hgl, hhd, tsub_zero]
      have hBge : ∀ u ∈ e.2 :: B', e.2 ≤ u := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact le_refl _
        · exact le_of_lt ((List.pairwise_cons.mp
            (List.pairwise_append.mp hsort).2.1).1 u hu')
      have hright : pieceDist d (e :: L') (e.2 :: B')
          = layoutDist L' := by
        rw [pieceDist_shift d e L' (e.2 :: B') hBge]
        refine ih hL' ((e.2 :: B').map (· - e.2)) (by simp) ?_ ?_ ?_ ?_
        · exact pairwise_map_tsub hBge
            (List.pairwise_append.mp hsort).2.1
        · simp
        · rw [getLast_map_tsub e.2 (e.2 :: B') (List.cons_ne_nil e.2 B')
            (by simp)]
          have h4 : (e.2 :: B').getLast (List.cons_ne_nil e.2 B')
              = layoutTotal (e :: L') := by
            rw [← hlast]
            exact (getLast_append_cons A e.2 B' hne).symm
          rw [h4, layoutTotal_cons, add_sub_cancel_left]
        · intro c hc
          have h1 : e.2 + c ∈ layoutCuts (e :: L') := by
            rw [layoutCuts_cons]
            exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
          have hc0 : 0 ≤ c := layoutCuts_nonneg hL' c hc
          have h3 : e.2 + c ∈ e.2 :: B' := by
            rcases List.mem_append.mp (hcuts _ h1) with h | h
            · exact absurd (hAlt _ h) (not_lt.mpr (by linarith))
            · exact h
          exact List.mem_map.mpr ⟨e.2 + c, h3, by rw [add_sub_cancel_left]⟩
      rw [hleft, hright, layoutDist_cons]

private theorem layoutDist_append {α : Type*}
    (L₁ L₂ : List (α × ℝ)) :
    layoutDist (L₁ ++ L₂) = layoutDist L₁ + layoutDist L₂ := by
  unfold layoutDist
  rw [List.map_append, List.sum_append]

private theorem layoutTotal_append {α : Type*}
    (L₁ L₂ : List (α × ℝ)) :
    layoutTotal (L₁ ++ L₂) = layoutTotal L₁ + layoutTotal L₂ := by
  unfold layoutTotal
  rw [List.map_append, List.sum_append]

open Classical in
private theorem layoutDist_map_apply {α : Type*} (f : α → ℝ) :
    ∀ (os : List α), os.Nodup → ∀ a : α,
      layoutDist (os.map fun c => (c, f c)) a
        = if a ∈ os then f a else 0 := by
  intro os
  induction os with
  | nil =>
      intro _ a
      rw [List.map_nil, layoutDist_nil, if_neg (List.not_mem_nil),
        Finsupp.coe_zero, Pi.zero_apply]
  | cons c os' ih =>
      intro hn a
      rw [List.map_cons, layoutDist_cons, Finsupp.add_apply,
        ih (List.nodup_cons.mp hn).2 a, Finsupp.single_apply]
      by_cases hac : a = c
      · subst hac
        rw [if_pos rfl, if_neg (List.nodup_cons.mp hn).1, add_zero,
          if_pos (show a ∈ a :: os' by simp)]
      · rw [if_neg fun h => hac h.symm, zero_add]
        by_cases hmem : a ∈ os'
        · rw [if_pos hmem, if_pos (List.mem_cons_of_mem c hmem)]
        · rw [if_neg hmem,
            if_neg fun h => hmem ((List.mem_cons.mp h).resolve_left hac)]

/-- The common-first canonical layout of a pair along an enumeration:
all common blocks `min (μ c) (ν c)` first (in a shared order for both
sides), then the `μ`-side excess blocks. -/
private noncomputable def commonFirstLayout {α : Type*} (os : List α)
    (μ ν : Dist α) : List (α × ℝ) :=
  (os.map fun c => (c, min (μ c) (ν c)))
    ++ os.map fun c => (c, max (μ c - ν c) 0)

private theorem commonFirstLayout_entry_nonneg {α : Type*} {os : List α}
    {μ ν : Dist α} (hμ : μ.NonNeg) (hν : ν.NonNeg) :
    ∀ e ∈ commonFirstLayout os μ ν, 0 ≤ e.2 := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
    exact le_min (hμ c) (hν c)
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
    exact le_max_right _ _

open Classical in
private theorem layoutDist_commonFirstLayout {α : Type*} {os : List α}
    (hn : os.Nodup) {μ ν : Dist α}
    (hsupp : ∀ a ∈ μ.support, a ∈ os) :
    layoutDist (commonFirstLayout os μ ν) = μ := by
  refine Finsupp.ext fun a => ?_
  unfold commonFirstLayout
  rw [layoutDist_append, Finsupp.add_apply,
    layoutDist_map_apply _ os hn a, layoutDist_map_apply _ os hn a]
  by_cases hmem : a ∈ os
  · rw [if_pos hmem, if_pos hmem]
    rcases le_total (ν a) (μ a) with h | h
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]
  · rw [if_neg hmem, if_neg hmem, add_zero]
    exact (Finsupp.notMem_support_iff.mp fun h => hmem (hsupp a h)).symm

private theorem layoutTotal_commonFirstLayout {α : Type*} {os : List α}
    (hn : os.Nodup) {μ ν : Dist α}
    (hsupp : ∀ a ∈ μ.support, a ∈ os) :
    layoutTotal (commonFirstLayout os μ ν) = μ.weight := by
  rw [← weight_layoutDist, layoutDist_commonFirstLayout hn hsupp]

private theorem layoutTotal_map_snd {α : Type*} (os : List α)
    (f : α → ℝ) :
    layoutTotal (os.map fun c => (c, f c)) = (os.map f).sum := by
  unfold layoutTotal
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left fun c _ => rfl)

open Classical in
/-- The mixed subsums of a distribution: all partial masses over
subsets of the support.  Every cut position of the node's layouts is
built from finitely many of these. -/
private noncomputable def subsums {α : Type*} (μ : Dist α) :
    Finset ℝ :=
  μ.support.powerset.image fun G => ∑ a ∈ G, μ a

open Classical in
private theorem zero_mem_subsums {α : Type*} (μ : Dist α) :
    0 ∈ subsums μ := by
  refine Finset.mem_image.mpr
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), Finset.sum_empty⟩

open Classical in
private theorem finset_sum_mem_subsums {α : Type*} (μ : Dist α)
    (K : Finset α) :
    ∑ a ∈ K, μ a ∈ subsums μ := by
  refine Finset.mem_image.mpr ⟨K ∩ μ.support,
    Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
  refine Finset.sum_subset Finset.inter_subset_left fun a haK hnot => ?_
  exact Finsupp.notMem_support_iff.mp
    fun hs => hnot (Finset.mem_inter.mpr ⟨haK, hs⟩)

open Classical in
/-- The universal cut set of a node pair (thesis §2.4.2's separation
values, subsum-closure form): sums `a + c + (e − f)` of mixed subsums
of the two sides.  Every per-`x` layout cut lies here, uniformly in
`x`. -/
private noncomputable def nodeCuts {α : Type*} (μ ν : Dist α) :
    Finset ℝ :=
  ((subsums μ ×ˢ subsums ν) ×ˢ subsums μ ×ˢ subsums ν).image
    fun q => q.1.1 + q.1.2 + max (q.2.1 - q.2.2) 0

open Classical in
private theorem mem_nodeCuts {α : Type*} {μ ν : Dist α}
    {a c e f : ℝ} (ha : a ∈ subsums μ) (hc : c ∈ subsums ν)
    (he : e ∈ subsums μ) (hf : f ∈ subsums ν) (hfe : f ≤ e) :
    a + c + (e - f) ∈ nodeCuts μ ν := by
  refine Finset.mem_image.mpr ⟨((a, c), (e, f)), ?_, ?_⟩
  · simp only [Finset.mem_product]
    exact ⟨⟨ha, hc⟩, he, hf⟩
  · dsimp only
    rw [max_eq_left (sub_nonneg.mpr hfe)]

open Classical in
private theorem list_sum_min_split {α : Type*} (μ ν : Dist α) :
    ∀ l : List α, l.Nodup →
      ∃ K₁ K₂ : Finset α, K₁ ⊆ l.toFinset ∧ K₂ ⊆ l.toFinset ∧
        (l.map fun c => min (μ c) (ν c)).sum
          = (∑ a ∈ K₁, μ a) + ∑ a ∈ K₂, ν a := by
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, ∅, by simp, by simp, by simp⟩
  | cons c l ih =>
      intro hn
      obtain ⟨K₁, K₂, h₁, h₂, hsum⟩ := ih (List.nodup_cons.mp hn).2
      have hc₁ : c ∉ K₁ := fun h =>
        (List.nodup_cons.mp hn).1 (by have := h₁ h; simpa using this)
      have hc₂ : c ∉ K₂ := fun h =>
        (List.nodup_cons.mp hn).1 (by have := h₂ h; simpa using this)
      rw [List.map_cons, List.sum_cons]
      rcases min_choice (μ c) (ν c) with hmin | hmin
      · refine ⟨insert c K₁, K₂, ?_, ?_, ?_⟩
        · rw [List.toFinset_cons]
          exact Finset.insert_subset_insert c h₁
        · rw [List.toFinset_cons]
          exact h₂.trans (Finset.subset_insert c _)
        · rw [hmin, hsum, Finset.sum_insert hc₁, add_assoc]
      · refine ⟨K₁, insert c K₂, ?_, ?_, ?_⟩
        · rw [List.toFinset_cons]
          exact h₁.trans (Finset.subset_insert c _)
        · rw [List.toFinset_cons]
          exact Finset.insert_subset_insert c h₂
        · rw [hmin, hsum, Finset.sum_insert hc₂, add_left_comm]

open Classical in
private theorem list_sum_tsub_split {α : Type*} (μ ν : Dist α) :
    ∀ l : List α, l.Nodup →
      ∃ K : Finset α, K ⊆ l.toFinset ∧
        ((l.map fun c => max (μ c - ν c) 0).sum
            = (∑ a ∈ K, μ a) - ∑ a ∈ K, ν a)
          ∧ (∑ a ∈ K, ν a) ≤ ∑ a ∈ K, μ a := by
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | cons c l ih =>
      intro hn
      obtain ⟨K, hK, hsum, hle⟩ := ih (List.nodup_cons.mp hn).2
      have hcK : c ∉ K := fun h =>
        (List.nodup_cons.mp hn).1 (by have := hK h; simpa using this)
      rw [List.map_cons, List.sum_cons]
      rcases le_total (ν c) (μ c) with h | h
      · refine ⟨insert c K, ?_, ?_, ?_⟩
        · rw [List.toFinset_cons]
          exact Finset.insert_subset_insert c hK
        · rw [hsum, Finset.sum_insert hcK, Finset.sum_insert hcK,
            max_eq_left (sub_nonneg.mpr h)]
          ring
        · rw [Finset.sum_insert hcK, Finset.sum_insert hcK]
          exact add_le_add h hle
      · refine ⟨K, ?_, ?_, hle⟩
        · rw [List.toFinset_cons]
          exact hK.trans (Finset.subset_insert c _)
        · rw [max_eq_right (sub_nonpos.mpr h), zero_add, hsum]

private theorem take_length_add_append {α : Type*} :
    ∀ (l₁ l₂ : List α) (j : ℕ),
      (l₁ ++ l₂).take (l₁.length + j) = l₁ ++ l₂.take j := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ j; simp
  | cons a l₁ ih =>
      intro l₂ j
      simp only [List.cons_append, List.length_cons]
      rw [show l₁.length + 1 + j = (l₁.length + j) + 1 by omega,
        List.take_succ_cons, ih]

open Classical in
/-- Stage-A containment (the separation-value finiteness): every cut of
a common-first layout lies in the node's universal cut set — uniformly
in the enumeration, hence uniformly in the query `x` at use sites. -/
private theorem layoutCuts_commonFirstLayout_subset {α : Type*}
    {os : List α} (hn : os.Nodup) (μ ν : Dist α) :
    ∀ u ∈ layoutCuts (commonFirstLayout os μ ν), u ∈ nodeCuts μ ν := by
  intro u hu
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hu
  rcases le_total k os.length with hk' | hk'
  · have htake : (commonFirstLayout os μ ν).take k
        = (os.take k).map fun c => (c, min (μ c) (ν c)) := by
      unfold commonFirstLayout
      rw [List.take_append_of_le_length (by simpa using hk'),
        List.map_take]
    rw [htake, layoutTotal_map_snd]
    obtain ⟨K₁, K₂, _, _, hsum⟩ := list_sum_min_split μ ν (os.take k)
      ((List.take_sublist k os).nodup hn)
    rw [hsum]
    simpa using mem_nodeCuts (finset_sum_mem_subsums μ K₁)
      (finset_sum_mem_subsums ν K₂) (zero_mem_subsums μ)
      (zero_mem_subsums ν) (le_refl 0)
  · obtain ⟨j, hj⟩ : ∃ j, k = os.length + j := ⟨k - os.length, by omega⟩
    subst hj
    have hsplit : (commonFirstLayout os μ ν).take (os.length + j)
        = (os.map fun c => (c, min (μ c) (ν c)))
          ++ (os.take j).map fun c => (c, max (μ c - ν c) 0) := by
      unfold commonFirstLayout
      rw [show os.length + j
            = (os.map fun c => (c, min (μ c) (ν c))).length + j by
          rw [List.length_map],
        take_length_add_append, List.map_take]
    rw [hsplit, layoutTotal_append, layoutTotal_map_snd,
      layoutTotal_map_snd]
    obtain ⟨K₁, K₂, _, _, hsum₁⟩ := list_sum_min_split μ ν os hn
    obtain ⟨K, _, hsum₂, hKle⟩ := list_sum_tsub_split μ ν
      (os.take j) ((List.take_sublist _ os).nodup hn)
    rw [hsum₁, hsum₂]
    exact mem_nodeCuts (finset_sum_mem_subsums μ K₁)
      (finset_sum_mem_subsums ν K₂) (finset_sum_mem_subsums μ K)
      (finset_sum_mem_subsums ν K) hKle

open Classical in
/-- The overlap of a pair is itself a node-cut value (`Σ min` over the
joint support) — this is what makes the per-`x` overlap values range in
a finite set. -/
private theorem weight_commonPart_mem_nodeCuts {α : Type*}
    (μ ν : Dist α) :
    Dist.weight (commonPart μ ν) ∈ nodeCuts μ ν := by
  rw [weight_commonPart μ ν,
    show ∑ a ∈ μ.support ∪ ν.support, min (μ a) (ν a)
        = ((μ.support ∪ ν.support).toList.map
            fun c => min (μ c) (ν c)).sum from ?_]
  · obtain ⟨K₁, K₂, _, _, hsum⟩ := list_sum_min_split μ ν
      (μ.support ∪ ν.support).toList (Finset.nodup_toList _)
    rw [hsum]
    simpa using mem_nodeCuts (finset_sum_mem_subsums μ K₁)
      (finset_sum_mem_subsums ν K₂) (zero_mem_subsums μ)
      (zero_mem_subsums ν) (le_refl 0)
  · rw [← List.sum_toFinset _ (Finset.nodup_toList _),
      Finset.toList_toFinset]

/-- A function into a finite value set attains its minimum: the
`τ`-witness of the cross-query joint, with no `sInf` and no order on
the index. -/
private theorem exists_min_of_mem_finset {γ : Type*} [Nonempty γ]
    (f : γ → ℝ) (F : Finset ℝ) (hf : ∀ x, f x ∈ F) :
    ∃ x₀, ∀ x, f x₀ ≤ f x := by
  classical
  obtain ⟨x⟩ := ‹Nonempty γ›
  have hne : (F.filter fun v => ∃ x, f x = v).Nonempty :=
    ⟨f x, Finset.mem_filter.mpr ⟨hf x, x, rfl⟩⟩
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image _ id hne
  obtain ⟨x₀, hx₀⟩ := (Finset.mem_filter.mp hv).2
  refine ⟨x₀, fun z => ?_⟩
  rw [hx₀]
  exact hmin _ (Finset.mem_filter.mpr ⟨hf z, z, rfl⟩)

/-! ### ⊥-pattern stratification (milestone-4 stage B;
THM231_ATTAINMENT.md §4 addendum: cross-query correlations involving
`⊥` are observable, so node joints must be stratified by pattern) -/

open Classical in
/-- Any sub-distribution is the sum of its fibers under a statistic:
the distribution-level form of the fiber partition. -/
private theorem eq_sum_filter_fiber {A B : Type*} (μ : Dist A)
    (g : A → B) :
    μ = ∑ v ∈ μ.support.image g, μ.filter fun a => g a = v := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.finset_sum_apply]
  by_cases ha : a ∈ μ.support
  · rw [Finset.sum_eq_single_of_mem (g a) (Finset.mem_image_of_mem g ha)
      fun v _ hv => by
        rw [Finsupp.filter_apply, if_neg fun h => hv h.symm]]
    rw [Finsupp.filter_apply, if_pos rfl]
  · rw [Finsupp.notMem_support_iff.mp ha]
    symm
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Finsupp.filter_apply]
    by_cases h : g a = v
    · rw [if_pos h, Finsupp.notMem_support_iff.mp ha]
    · rw [if_neg h]

open Classical in
/-- Distinct fibers of a statistic have disjoint supports (used with
the `⊥`-pattern as the statistic: distinct-pattern cells never share
atoms, on either side). -/
private theorem support_filter_fiber_disjoint {A B : Type*}
    (μ ν : Dist A) (g : A → B) {v v' : B} (hne : v ≠ v') :
    Disjoint (μ.filter fun a => g a = v).support
      (ν.filter fun a => g a = v').support := by
  refine Finset.disjoint_left.mpr fun a ha ha' => ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at ha ha'
  exact hne (ha.2 ▸ ha'.2)

/-- The ⊥-pattern of an atom: which first queries it answers. -/
private def pattern (s : PFunDDS.DDS X Y) : X → Prop :=
  fun x => [x] ∈ PFunDDS.dom s

/-- A glued profile atom's ⊥-pattern is exactly the answered-choice
pattern of its profile — the joint's pattern is by construction the
profile's, which is what makes pattern-stratified joints
pattern-faithful. -/
private theorem pattern_glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × PFunDDS.DDS X Y)) (x : X) :
    pattern (glueProfile cls p) x ↔ (p (cls x)).isSome = true := by
  unfold pattern glueProfile
  rw [cons_mem_dom_glue]
  rcases hp : p (cls x) with _ | ⟨v, a⟩
  · exact iff_of_false (not_mem_dom_empty [x]) (by simp)
  · exact iff_of_true (singleton_mem_dom_prepend_some x v a) rfl

/-! ### The fuel-indexed value set (milestone-4 stage B0;
THM231_ATTAINMENT.md §5 correction: the separation values close
bottom-up along the fuel, not node-locally) -/

open Classical in
/-- B0 monotonicity, filter form: filtering keeps original masses on a
smaller support, so its subsums are among the original subsums. -/
private theorem subsums_filter_subset {A : Type*} (μ : Dist A)
    (P : A → Prop) [DecidablePred P] :
    subsums (μ.filter P) ⊆ subsums μ := by
  intro u hu
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hu
  rw [show ∑ a ∈ G, (μ.filter P) a = ∑ a ∈ G, μ a from
    Finset.sum_congr rfl fun a ha => by
      rw [Finsupp.filter_apply, if_pos ?_]
      have hmem := Finset.mem_powerset.mp hG ha
      rw [Finsupp.support_filter, Finset.mem_filter] at hmem
      exact hmem.2]
  exact finset_sum_mem_subsums μ G

open Classical in
/-- B0 monotonicity, pushforward form: pushforward masses are fiber
sums of original masses, so subset sums of the image are subset sums
of the source.  With the filter form this bounds every
`successorTransform` pair's subsums inside the node pair's. -/
private theorem subsums_fTransform_subset {A B : Type*} (f : A → B)
    (μ : Dist A) :
    subsums (Dist.fTransform f μ) ⊆ subsums μ := by
  intro u hu
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hu
  have hval : ∑ b' ∈ G, Dist.fTransform f μ b'
      = ∑ a ∈ μ.support.filter (fun a => f a ∈ G), μ a := by
    rw [Finset.sum_congr rfl
      fun b' _ => Dist.fTransform_apply_eq_mass f μ b']
    unfold Dist.mass
    simp only [Finsupp.sum]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq G (f a) fun _ => μ a]
  rw [hval]
  exact finset_sum_mem_subsums μ _

open Classical in
/-- Bounded-arity sums of a value set (arity ≤ the node's support
size bounds every subset sum the construction forms). -/
private noncomputable def sumsUpTo : ℕ → Finset ℝ → Finset ℝ
  | 0, _ => {0}
  | k + 1, W =>
      ((W ×ˢ sumsUpTo k W).image fun q => q.1 + q.2) ∪ sumsUpTo k W

open Classical in
/-- Pairwise truncated differences. -/
private noncomputable def tsubPairs (W : Finset ℝ) :
    Finset ℝ :=
  (W ×ˢ W).image fun q => max (q.1 - q.2) 0

open Classical in
/-- One closure round: truncated differences of bounded-arity sums over
the set enriched by its pairwise `tsub`s (`0`, the set itself, sums,
`tsub`s, piece masses, and the `a + c + (e − f)` node-cut shape — whose
inner truncation is NOT absorbed by an outer one in `ℝ≥0` — are all
instances). -/
private noncomputable def cutRound (N : ℕ) (W : Finset ℝ) :
    Finset ℝ :=
  ((sumsUpTo N (insert 0 (W ∪ tsubPairs W)))
      ×ˢ sumsUpTo N (insert 0 (W ∪ tsubPairs W))).image
    fun q => max (q.1 - q.2) 0

open Classical in
/-- The fuel-indexed universal value set: `n` closure rounds over the
node pair's subsums.  Every mass and every cut the depth-`n` rebuild
produces lies here (the invariant carried in the rebuild induction). -/
private noncomputable def cutClosure (N : ℕ) :
    ℕ → Finset ℝ → Finset ℝ
  | 0, V => insert 0 V
  | n + 1, V => cutRound N (cutClosure N n V)

open Classical in
private theorem sumsUpTo_mono {k : ℕ} :
    ∀ {W W' : Finset ℝ}, W ⊆ W' → sumsUpTo k W ⊆ sumsUpTo k W' := by
  induction k with
  | zero => intro W W' _; exact Finset.Subset.refl _
  | succ k ih =>
      intro W W' h
      refine Finset.union_subset_union ?_ (ih h)
      exact Finset.image_subset_image (Finset.product_subset_product h (ih h))

open Classical in
private theorem tsubPairs_mono {W W' : Finset ℝ} (h : W ⊆ W') :
    tsubPairs W ⊆ tsubPairs W' :=
  Finset.image_subset_image (Finset.product_subset_product h h)

open Classical in
private theorem cutRound_mono (N : ℕ) {W W' : Finset ℝ}
    (h : W ⊆ W') : cutRound N W ⊆ cutRound N W' := by
  unfold cutRound
  refine Finset.image_subset_image (Finset.product_subset_product ?_ ?_)
    <;> exact sumsUpTo_mono (Finset.insert_subset_insert 0
      (Finset.union_subset_union h (tsubPairs_mono h)))

open Classical in
private theorem cutClosure_mono (N : ℕ) :
    ∀ (n : ℕ) {V V' : Finset ℝ}, V ⊆ V' →
      cutClosure N n V ⊆ cutClosure N n V' := by
  intro n
  induction n with
  | zero => intro V V' h; exact Finset.insert_subset_insert 0 h
  | succ n ih => intro V V' h; exact cutRound_mono N (ih h)

open Classical in
private theorem zero_mem_sumsUpTo (k : ℕ) (W : Finset ℝ) :
    0 ∈ sumsUpTo k W := by
  induction k with
  | zero => exact Finset.mem_singleton_self 0
  | succ k ih => exact Finset.mem_union_right _ ih

open Classical in
private theorem sumsUpTo_subset_succ (k : ℕ) (W : Finset ℝ) :
    sumsUpTo k W ⊆ sumsUpTo (k + 1) W :=
  Finset.subset_union_right

open Classical in
private theorem sumsUpTo_mono_arity {k k' : ℕ} (h : k ≤ k')
    (W : Finset ℝ) : sumsUpTo k W ⊆ sumsUpTo k' W := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (sumsUpTo_subset_succ _ W)

open Classical in
private theorem add_mem_sumsUpTo {W : Finset ℝ} {w z : ℝ}
    {k : ℕ} (hw : w ∈ W) (hz : z ∈ sumsUpTo k W) :
    w + z ∈ sumsUpTo (k + 1) W :=
  Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨(w, z), Finset.mem_product.mpr ⟨hw, hz⟩, rfl⟩)

open Classical in
private theorem mem_sumsUpTo_of_mem {W : Finset ℝ} {w : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hw : w ∈ W) : w ∈ sumsUpTo k W := by
  refine sumsUpTo_mono_arity hk W ?_
  have := add_mem_sumsUpTo hw (zero_mem_sumsUpTo 0 W)
  rwa [add_zero] at this

open Classical in
private theorem self_subset_cutRound {N : ℕ} (hN : 1 ≤ N)
    (W : Finset ℝ) (hW : ∀ v ∈ W, 0 ≤ v) : W ⊆ cutRound N W := by
  intro w hw
  refine Finset.mem_image.mpr ⟨(w, 0), Finset.mem_product.mpr
    ⟨mem_sumsUpTo_of_mem hN (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hw)), zero_mem_sumsUpTo N _⟩, by
        dsimp only
        rw [sub_zero, max_eq_left (hW w hw)]⟩

private theorem cutRound_nonneg (N : ℕ) (W : Finset ℝ) :
    ∀ z ∈ cutRound N W, 0 ≤ z := by
  intro z hz
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
  exact le_max_right _ _

open Classical in
private theorem zero_mem_cutRound (N : ℕ) (W : Finset ℝ) :
    0 ∈ cutRound N W :=
  Finset.mem_image.mpr ⟨(0, 0), Finset.mem_product.mpr
    ⟨zero_mem_sumsUpTo N _, zero_mem_sumsUpTo N _⟩, by simp⟩

open Classical in
private theorem cutClosure_nonneg {N : ℕ} (n : ℕ) {V : Finset ℝ}
    (hV : ∀ v ∈ V, 0 ≤ v) : ∀ z ∈ cutClosure N n V, 0 ≤ z := by
  cases n with
  | zero =>
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | h
      · exact le_refl 0
      · exact hV z h
  | succ n => exact cutRound_nonneg N _

private theorem cutClosure_subset_succ {N : ℕ} (hN : 1 ≤ N) (n : ℕ)
    {V : Finset ℝ} (hV : ∀ v ∈ V, 0 ≤ v) :
    cutClosure N n V ⊆ cutClosure N (n + 1) V :=
  self_subset_cutRound hN _ (cutClosure_nonneg n hV)

open Classical in
private theorem subset_cutClosure {N : ℕ} (hN : 1 ≤ N) (n : ℕ)
    {V : Finset ℝ} (hV : ∀ v ∈ V, 0 ≤ v) : V ⊆ cutClosure N n V := by
  induction n with
  | zero => exact Finset.subset_insert 0 V
  | succ n ih => exact ih.trans (cutClosure_subset_succ hN n hV)

open Classical in
/-- The node-cut shape is absorbed by one closure round: with both
sides' subsums inside `W` and arity at least `3`, every
`a + c + (e − f)` lands in `cutRound N W`. -/
private theorem subsums_nonneg {A : Type*} {μ : Dist A}
    (hμ : μ.NonNeg) : ∀ z ∈ subsums μ, 0 ≤ z := by
  intro z hz
  obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.sum_nonneg fun a _ => hμ a

open Classical in
private theorem nodeCuts_subset_cutRound {N : ℕ} (hN : 3 ≤ N)
    {W : Finset ℝ} {A : Type*} {μ ν : Dist A}
    (hμnn : μ.NonNeg) (hνnn : ν.NonNeg)
    (hμ : subsums μ ⊆ W) (hν : subsums ν ⊆ W) :
    nodeCuts μ ν ⊆ cutRound N W := by
  intro u hu
  obtain ⟨⟨⟨a, c⟩, e, f⟩, hq, rfl⟩ := Finset.mem_image.mp hu
  simp only [Finset.mem_product] at hq
  obtain ⟨⟨ha, hc⟩, he, hf⟩ := hq
  have hW₁ : ∀ {z : ℝ}, z ∈ W →
      z ∈ insert 0 (W ∪ tsubPairs W) :=
    fun hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)
  have hef : max (e - f) 0 ∈ insert 0 (W ∪ tsubPairs W) :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(e, f),
        Finset.mem_product.mpr ⟨hμ he, hν hf⟩, rfl⟩))
  have hz₁ := add_mem_sumsUpTo hef (zero_mem_sumsUpTo 0 _)
  have hz₂ := add_mem_sumsUpTo (hW₁ (hν hc)) hz₁
  have hz₃ := add_mem_sumsUpTo (hW₁ (hμ ha)) hz₂
  refine Finset.mem_image.mpr ⟨(a + (c + (max (e - f) 0 + 0)), 0),
    Finset.mem_product.mpr
      ⟨sumsUpTo_mono_arity hN _ hz₃, zero_mem_sumsUpTo N _⟩, ?_⟩
  dsimp only
  rw [sub_zero, add_zero, ← add_assoc,
    max_eq_left (by
      have h1 := subsums_nonneg hμnn a ha
      have h2 := subsums_nonneg hνnn c hc
      have h3 : (0 : ℝ) ≤ max (e - f) 0 := le_max_right _ _
      linarith)]

/-! ### The interval joint (milestone-4 stage B: piece-indexed
profiles replace `jointProfile`; one point mass per piece) -/

private theorem fTransform_single {A B : Type*} (f : A → B) (a : A)
    (m : ℝ) :
    Dist.fTransform f (Finsupp.single a m) = Finsupp.single (f a) m := by
  show Finsupp.mapDomain f _ = _
  exact Finsupp.mapDomain_single

open Classical in
/-- The profile distribution of a per-query layout family along a cut
list: one deterministic profile per piece, reading each query's layout
at the piece's position. -/
private noncomputable def profileDist
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) :
    List ℝ → Dist (X → Option (Y × PFunDDS.DDS X Y))
  | u :: u' :: us =>
      Finsupp.single (fun x => valueAt none (Lf x) u) (u' - u)
        + profileDist Lf (u' :: us)
  | _ => 0

open Classical in
/-- Every query marginal of the profile distribution is the piecewise
reassembly of that query's layout. -/
private theorem fTransform_eval_profileDist
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) (x : X) :
    ∀ us : List ℝ,
      Dist.fTransform (fun p => p x) (profileDist Lf us)
        = pieceDist none (Lf x) us := by
  intro us
  induction us with
  | nil => exact fTransform_zero _
  | cons u vs ih =>
      cases vs with
      | nil => exact fTransform_zero _
      | cons u' vs' =>
          simp only [profileDist, pieceDist]
          rw [fTransform_add, fTransform_single, ih]

open Classical in
/-- Stage B: the **interval joint** of a per-query family of choice
layouts along a universal cut list — the piece-indexed tuple assembly
of thesis Lemma 2.33 (THM231_ATTAINMENT.md §5). -/
private theorem profileDist_nonNeg
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) :
    ∀ us : List ℝ, us.Pairwise (· ≤ ·) →
      (profileDist Lf us).NonNeg := by
  intro us
  induction us with
  | nil =>
      intro _ p
      exact le_refl 0
  | cons u vs ih =>
      intro hsort
      cases vs with
      | nil =>
          intro p
          exact le_refl 0
      | cons u' vs' =>
          intro p
          show 0 ≤ (Finsupp.single (fun x => valueAt none (Lf x) u)
              (u' - u) + profileDist Lf (u' :: vs')) p
          rw [Finsupp.add_apply]
          exact add_nonneg
            (single_nonNeg (sub_nonneg.mpr
              ((List.pairwise_cons.mp hsort).1 u' (by simp))) _ p)
            (ih (List.pairwise_cons.mp hsort).2 p)

private noncomputable def intervalJoint
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    (us : List ℝ) : PFunPDS X Y :=
  Dist.fTransform (glueProfile id) (profileDist Lf us)

open Classical in
/-- The interval joint's answered marginals: at every query whose
layout the cut list refines, the `(x, some v)`-marginal is the
`v`-slice of that query's own layout distribution. -/
private theorem successorTransform_intervalJoint
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    (us : List ℝ) {x : X} (v : Y) (hLf : ∀ e ∈ Lf x, 0 ≤ e.2)
    (hne : us ≠ [])
    (hsort : us.Pairwise (· < ·)) (hhead : us.head hne = 0)
    (hlast : us.getLast hne = layoutTotal (Lf x))
    (hcuts : ∀ c ∈ layoutCuts (Lf x), c ∈ us) :
    successorTransform (intervalJoint Lf us) x (some v)
      = Dist.fTransform contOf ((layoutDist (Lf x)).filter
          fun c => Option.map Prod.fst c = some v) := by
  unfold intervalJoint
  have hid : Dist.fTransform
      (fun p : X → Option (Y × PFunDDS.DDS X Y) => p (id x))
      (profileDist Lf us) = pieceDist none (Lf x) us :=
    fTransform_eval_profileDist Lf x us
  rw [successorTransform_fTransform_glueProfile id (profileDist Lf us)
      x v, hid,
    pieceDist_eq_layoutDist none (Lf x) hLf us hne hsort hhead hlast hcuts]

private theorem valueAt_append_lt {α : Type*} (d : α) :
    ∀ (P R : List (α × ℝ)) (u : ℝ), 0 ≤ u → u < layoutTotal P →
      valueAt d (P ++ R) u = valueAt d P u := by
  intro P
  induction P with
  | nil =>
      intro R u hu0 hu
      rw [layoutTotal_nil] at hu
      exact absurd hu (not_lt.mpr hu0)
  | cons e P ih =>
      intro R u hu0 hu
      simp only [List.cons_append, valueAt]
      by_cases h : u < e.2
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        rw [layoutTotal_cons] at hu
        exact ih R (u - e.2) (sub_nonneg.mpr (not_lt.mp h)) (by linarith)

open Classical in
/-- C4, shared region: below every query's common-block total, the two
sides' common-first layouts read the same choice — the piece profiles
agree, hence the glue atoms coincide (the sharing of the joint). -/
private theorem profile_eq_of_lt_common
    (Ax Bx : X → Dist (Option (Y × PFunDDS.DDS X Y)))
    (os : X → List (Option (Y × PFunDDS.DDS X Y))) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : ∀ x, u < layoutTotal ((os x).map fun c =>
      (c, min (Ax x c) (Bx x c)))) :
    (fun x => valueAt none (commonFirstLayout (os x) (Ax x) (Bx x)) u)
      = fun x =>
          valueAt none (commonFirstLayout (os x) (Bx x) (Ax x)) u := by
  funext x
  have hswap : ((os x).map fun c => (c, min (Bx x c) (Ax x c)))
      = (os x).map fun c => (c, min (Ax x c) (Bx x c)) :=
    List.map_congr_left fun c _ => by rw [min_comm]
  unfold commonFirstLayout
  rw [hswap, valueAt_append_lt none _ _ u hu0 (hu x),
    valueAt_append_lt none _ _ u hu0 (hu x)]

private theorem profileDist_append
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) :
    ∀ (A : List ℝ) (c : ℝ) (B : List ℝ),
      profileDist Lf (A ++ c :: B)
        = profileDist Lf (A ++ [c]) + profileDist Lf (c :: B) := by
  intro A
  induction A with
  | nil =>
      intro c B
      simp only [List.nil_append, profileDist]
      rw [zero_add]
  | cons a A' ih =>
      intro c B
      cases A' with
      | nil =>
          simp only [List.cons_append, List.nil_append, profileDist]
          rw [add_zero]
      | cons a' A'' =>
          have ih' := ih c B
          simp only [List.cons_append] at ih' ⊢
          simp only [profileDist]
          rw [ih', add_assoc]

/-- Piece profiles that agree at every left endpoint give equal profile
distributions (applied with `profile_eq_of_lt_common` on the shared
region's cut prefix). -/
private theorem profileDist_congr
    (LfS LfT : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) :
    ∀ us : List ℝ,
      (∀ u ∈ us.dropLast,
        (fun x => valueAt none (LfS x) u)
          = fun x => valueAt none (LfT x) u) →
      profileDist LfS us = profileDist LfT us := by
  intro us
  induction us with
  | nil => intro _; rfl
  | cons u vs ih =>
      intro hagree
      cases vs with
      | nil => rfl
      | cons u' vs' =>
          simp only [profileDist]
          rw [hagree u (by simp [List.dropLast_cons_of_ne_nil]),
            ih fun z hz => hagree z (by
              rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil u' vs')]
              exact List.mem_cons_of_mem u hz)]

private theorem weight_profileDist
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) :
    ∀ (us : List ℝ) (hne : us ≠ []), us.Pairwise (· ≤ ·) →
      Dist.weight (profileDist Lf us)
        = us.getLast hne - us.head hne := by
  intro us
  induction us with
  | nil => intro hne; exact absurd rfl hne
  | cons u vs ih =>
      intro hne hsort
      cases vs with
      | nil =>
          simp only [profileDist, List.getLast_singleton, List.head_cons,
            sub_self]
          rw [Dist.weight_eq_finsupp_sum]
          exact Finsupp.sum_zero_index
      | cons u' vs' =>
          simp only [profileDist]
          rw [weight_add, weight_single,
            ih (List.cons_ne_nil u' vs') (List.pairwise_cons.mp hsort).2,
            List.getLast_cons (List.cons_ne_nil u' vs'), List.head_cons,
            List.head_cons]
          ring

open Classical in
/-- The interval joint carries the cut list's full span as weight. -/
private theorem weight_intervalJoint
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    (us : List ℝ) (hne : us ≠ []) (hsort : us.Pairwise (· ≤ ·)) :
    Dist.weight (intervalJoint Lf us)
      = us.getLast hne - us.head hne := by
  unfold intervalJoint
  rw [Dist.weight_fTransform]
  exact weight_profileDist Lf us hne hsort

/-! ### Per-node assembly (milestone-4 stage B: the rebuild's one-step
data — cell answer sets, rebuilt choice distributions, layouts, and
the sorted universal cut list) -/

open Classical in
/-- The answered values of a cell pair at a query: every `some`-answer
of a support atom on either side. -/
private noncomputable def cellVals (S T : PFunPDS X Y) (x : X) :
    Finset Y :=
  ((S.support ∪ T.support).image fun s =>
    PFunDDS.output (PFunDDS.fullyDefined s) [x]
      (by rw [PFunDDS.dom_fullyDefined]; simp)).biUnion Option.toFinset

open Classical in
private theorem mem_cellVals {S T : PFunPDS X Y} {x : X} {v : Y} :
    v ∈ cellVals S T x ↔ ∃ s ∈ S.support ∪ T.support,
      PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
  unfold cellVals
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨y, hy, hv⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨s, hs, ?_⟩
    rcases hout : PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | v'
    · rw [hout] at hv
      simp at hv
    · rw [hout] at hv
      simp only [Option.toFinset_some, Finset.mem_singleton] at hv
      rw [hv]
  · rintro ⟨s, hs, hout⟩
    exact ⟨some v, Finset.mem_image.mpr ⟨s, hs, hout⟩, by simp⟩

open Classical in
/-- One side's rebuilt choice distribution at a query: the answered
branches are the recursive rebuilds (the `rec` parameter), the
`⊥`-choice carries the side's pass-through mass. -/
private noncomputable def nodeChoice
    (rec : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (Sc : PFunPDS X Y) (x : X) :
    Dist (Option (Y × PFunDDS.DDS X Y)) :=
  classChoiceDist (cellVals S T x)
    (fun v => rec (successorTransform S x (some v))
      (successorTransform T x (some v)))
    (Dist.weight (successorTransform Sc x none))

open Classical in
/-- The per-query layout family of a cell pair under a rebuild
parameter: common blocks first, on a shared support enumeration. -/
private noncomputable def nodeLayout
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (x : X) :
    List (Option (Y × PFunDDS.DDS X Y) × ℝ) :=
  commonFirstLayout
    ((nodeChoice recS S T S x).support
      ∪ (nodeChoice recT S T T x).support).toList
    (nodeChoice recS S T S x) (nodeChoice recT S T T x)

private theorem sort_pairwise_lt (U : Finset ℝ) :
    (U.sort (· ≤ ·)).Pairwise (· < ·) := by
  have h1 : (U.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    Finset.pairwise_sort ..
  have h2 : (U.sort (· ≤ ·)).Pairwise (· ≠ ·) :=
    Finset.sort_nodup ..
  exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2

open Classical in
/-- The T-side layout of the node, on the **same** support enumeration
as the S-side (`nodeLayout`), with the choice roles swapped — the
shared common blocks align by `min_comm` (C4). -/
private noncomputable def nodeLayoutT
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (x : X) :
    List (Option (Y × PFunDDS.DDS X Y) × ℝ) :=
  commonFirstLayout
    ((nodeChoice recS S T S x).support
      ∪ (nodeChoice recT S T T x).support).toList
    (nodeChoice recT S T T x) (nodeChoice recS S T S x)

open Classical in
/-- Per-node marginal recovery, S-side answered case: under the cut
refinement hypotheses, the joint's `(x, some v)`-marginal is exactly
the recursively rebuilt branch. -/
private theorem successorTransform_nodeJoint_some
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (us : List ℝ) {x : X} {v : Y}
    (hne : us ≠ []) (hsort : us.Pairwise (· < ·))
    (hhead : us.head hne = 0)
    (hlast : us.getLast hne = layoutTotal (nodeLayout recS recT S T x))
    (hcuts : ∀ c ∈ layoutCuts (nodeLayout recS recT S T x), c ∈ us)
    (hLf : ∀ e ∈ nodeLayout recS recT S T x, 0 ≤ e.2)
    (hv : v ∈ cellVals S T x) :
    successorTransform (intervalJoint (nodeLayout recS recT S T) us)
      x (some v)
      = recS (successorTransform S x (some v))
          (successorTransform T x (some v)) := by
  rw [successorTransform_intervalJoint _ us v hLf hne hsort hhead hlast
      hcuts,
    show layoutDist (nodeLayout recS recT S T x)
        = nodeChoice recS S T S x from
      layoutDist_commonFirstLayout (Finset.nodup_toList _)
        fun a ha => Finset.mem_toList.mpr (Finset.mem_union_left _ ha)]
  exact contOf_filter_classChoiceDist_of_mem hv

open Classical in
private theorem successorTransform_nodeJoint_of_not_mem
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (us : List ℝ) {x : X} {v : Y}
    (hne : us ≠ []) (hsort : us.Pairwise (· < ·))
    (hhead : us.head hne = 0)
    (hlast : us.getLast hne = layoutTotal (nodeLayout recS recT S T x))
    (hcuts : ∀ c ∈ layoutCuts (nodeLayout recS recT S T x), c ∈ us)
    (hLf : ∀ e ∈ nodeLayout recS recT S T x, 0 ≤ e.2)
    (hv : v ∉ cellVals S T x) :
    successorTransform (intervalJoint (nodeLayout recS recT S T) us)
      x (some v) = 0 := by
  rw [successorTransform_intervalJoint _ us v hLf hne hsort hhead hlast
      hcuts,
    show layoutDist (nodeLayout recS recT S T x)
        = nodeChoice recS S T S x from
      layoutDist_commonFirstLayout (Finset.nodup_toList _)
        fun a ha => Finset.mem_toList.mpr (Finset.mem_union_left _ ha)]
  exact contOf_filter_classChoiceDist_of_not_mem hv

open Classical in
/-- Per-node marginal recovery, T-side answered case (same cut list,
same enumeration, swapped roles). -/
private theorem successorTransform_nodeJointT_some
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (us : List ℝ) {x : X} {v : Y}
    (hne : us ≠ []) (hsort : us.Pairwise (· < ·))
    (hhead : us.head hne = 0)
    (hlast : us.getLast hne = layoutTotal (nodeLayoutT recS recT S T x))
    (hcuts : ∀ c ∈ layoutCuts (nodeLayoutT recS recT S T x), c ∈ us)
    (hLf : ∀ e ∈ nodeLayoutT recS recT S T x, 0 ≤ e.2)
    (hv : v ∈ cellVals S T x) :
    successorTransform (intervalJoint (nodeLayoutT recS recT S T) us)
      x (some v)
      = recT (successorTransform S x (some v))
          (successorTransform T x (some v)) := by
  rw [successorTransform_intervalJoint _ us v hLf hne hsort hhead hlast
      hcuts,
    show layoutDist (nodeLayoutT recS recT S T x)
        = nodeChoice recT S T T x from
      layoutDist_commonFirstLayout (Finset.nodup_toList _)
        fun a ha => Finset.mem_toList.mpr (Finset.mem_union_right _ ha)]
  exact contOf_filter_classChoiceDist_of_mem hv

private theorem head_eq_zero_of_sorted {l : List ℝ} (hne : l ≠ [])
    (hsort : l.Pairwise (· ≤ ·)) (hnn : ∀ u ∈ l, 0 ≤ u) (h0 : 0 ∈ l) :
    l.head hne = 0 := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a l' =>
      rcases List.mem_cons.mp h0 with h | h
      · exact h.symm
      · exact le_antisymm ((List.pairwise_cons.mp hsort).1 0 h)
          (hnn a (by simp))

private theorem getLast_eq_of_sorted {l : List ℝ} (hne : l ≠ [])
    (hsort : l.Pairwise (· ≤ ·)) {w : ℝ} (hw : w ∈ l)
    (hub : ∀ u ∈ l, u ≤ w) : l.getLast hne = w :=
  le_antisymm (hub _ (List.getLast_mem hne))
    (sorted_le_getLast hsort hne w hw)

open Classical in
/-- The universal cut list of a node side: the given cut set trimmed
to `[0, w]`, with `0` and `w` adjoined, sorted. -/
private noncomputable def usOf (w : ℝ) (U : Finset ℝ) :
    List ℝ :=
  (insert 0 (insert w (U.filter (· ≤ w)))).sort (· ≤ ·)

open Classical in
private theorem usOf_ne_nil (w : ℝ) (U : Finset ℝ) :
    usOf w U ≠ [] :=
  List.ne_nil_of_mem ((Finset.mem_sort _).mpr (Finset.mem_insert_self 0 _))

open Classical in
private theorem usOf_pairwise (w : ℝ) (U : Finset ℝ) :
    (usOf w U).Pairwise (· < ·) :=
  sort_pairwise_lt _

open Classical in
private theorem usOf_nonneg {w : ℝ} (hw : 0 ≤ w) {U : Finset ℝ}
    (hU : ∀ u ∈ U, 0 ≤ u) : ∀ u ∈ usOf w U, 0 ≤ u := by
  intro u hu
  rcases Finset.mem_insert.mp ((Finset.mem_sort _).mp hu) with rfl | h
  · exact le_refl 0
  · rcases Finset.mem_insert.mp h with rfl | h'
    · exact hw
    · exact hU u (Finset.mem_filter.mp h').1

open Classical in
private theorem usOf_head {w : ℝ} (hw : 0 ≤ w) {U : Finset ℝ}
    (hU : ∀ u ∈ U, 0 ≤ u) :
    (usOf w U).head (usOf_ne_nil w U) = 0 :=
  head_eq_zero_of_sorted _ (Finset.pairwise_sort ..)
    (usOf_nonneg hw hU)
    ((Finset.mem_sort _).mpr (Finset.mem_insert_self 0 _))

open Classical in
private theorem usOf_getLast {w : ℝ} (hw : 0 ≤ w) (U : Finset ℝ) :
    (usOf w U).getLast (usOf_ne_nil w U) = w := by
  refine getLast_eq_of_sorted _ (Finset.pairwise_sort ..)
    ((Finset.mem_sort _).mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_self w _))) ?_
  intro u hu
  rcases Finset.mem_insert.mp ((Finset.mem_sort _).mp hu) with rfl | h
  · exact hw
  · rcases Finset.mem_insert.mp h with rfl | h'
    · exact le_refl _
    · exact (Finset.mem_filter.mp h').2

open Classical in
private theorem mem_usOf {w c : ℝ} {U : Finset ℝ}
    (hc : c ∈ U) (hcw : c ≤ w) : c ∈ usOf w U :=
  (Finset.mem_sort _).mpr (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hc, hcw⟩)))

open Classical in
/-- The node's cut set, both sides: the finiteness carrier (the
`boundedSums` invariant supplies finiteness; the construction is
well-defined regardless). -/
private noncomputable def nodeCutFinset
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) : Finset ℝ :=
  if h : {u | ∃ x, u ∈ layoutCuts (nodeLayout recS recT S T x)
      ∨ u ∈ layoutCuts (nodeLayoutT recS recT S T x)}.Finite
  then h.toFinset else ∅

open Classical in
/-- Thesis §2.4.2, the **rebuild**: the fuel-indexed attainment pair —
leaves at fuel `0`, and at each step the pattern-stratified sum of
per-cell interval joints of the recursively rebuilt branch data
(THM231_ATTAINMENT.md §4–5). -/
private noncomputable def rebuild :
    ℕ → PFunPDS X Y → PFunPDS X Y → PFunPDS X Y × PFunPDS X Y
  | 0, S, T => (S, T)
  | n + 1, S, T =>
      let recS := fun S' T' => (rebuild n S' T').1
      let recT := fun S' T' => (rebuild n S' T').2
      let cellS := fun σ : X → Prop => S.filter fun s => pattern s = σ
      let cellT := fun σ : X → Prop => T.filter fun s => pattern s = σ
      let U := fun σ => nodeCutFinset recS recT (cellS σ) (cellT σ)
      ((S.support ∪ T.support).image pattern).sum fun σ =>
        (intervalJoint (nodeLayout recS recT (cellS σ) (cellT σ))
            (usOf (Dist.weight (cellS σ)) (U σ)),
          intervalJoint (nodeLayoutT recS recT (cellS σ) (cellT σ))
            (usOf (Dist.weight (cellT σ)) (U σ)))

private theorem filter_nonNeg {A : Type*} {μ : Dist A}
    (hμ : μ.NonNeg) (P : A → Prop) [DecidablePred P] :
    RandomSystems.Dist.NonNeg (μ.filter P) := by
  intro a
  rw [Finsupp.filter_apply]
  split
  · exact hμ a
  · exact le_refl 0

open Classical in
private theorem successorTransform_nonNeg {S : PFunPDS X Y}
    (hS : S.NonNeg) (x : X) (y : Option Y) :
    (successorTransform S x y).NonNeg := by
  unfold successorTransform
  exact (filter_nonNeg hS _).fTransform _

open Classical in
private theorem intervalJoint_nonNeg
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    {us : List ℝ} (hsort : us.Pairwise (· ≤ ·)) :
    (intervalJoint Lf us).NonNeg := by
  unfold intervalJoint
  exact (profileDist_nonNeg Lf us hsort).fTransform _

open Classical in
/-- The rebuilt pair is an honest (pointwise non-negative) pair of laws
whenever the inputs are: the leaves are the inputs, and every step is a
pattern-indexed sum of interval joints along sorted cut lists. -/
private theorem rebuild_nonNeg :
    ∀ (n : ℕ) (S T : PFunPDS X Y), S.NonNeg → T.NonNeg →
      (rebuild n S T).1.NonNeg ∧ (rebuild n S T).2.NonNeg := by
  intro n
  cases n with
  | zero => intro S T hS hT; exact ⟨hS, hT⟩
  | succ n =>
      intro S T _ _
      constructor
      · show RandomSystems.Dist.NonNeg
          (((S.support ∪ T.support).image pattern).sum fun σ =>
            (intervalJoint _ _, intervalJoint _ _)).1
        rw [Prod.fst_sum]
        intro r
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_nonneg fun σ _ => ?_
        exact intervalJoint_nonNeg _
          ((usOf_pairwise _ _).imp le_of_lt) r
      · show RandomSystems.Dist.NonNeg
          (((S.support ∪ T.support).image pattern).sum fun σ =>
            (intervalJoint _ _, intervalJoint _ _)).2
        rw [Prod.snd_sum]
        intro r
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_nonneg fun σ _ => ?_
        exact intervalJoint_nonNeg _
          ((usOf_pairwise _ _).imp le_of_lt) r

open Classical in
private theorem nodeChoice_nonNeg
    {rec : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {S T Sc : PFunPDS X Y} (x : X)
    (hrec : ∀ v ∈ cellVals S T x,
      (rec (successorTransform S x (some v))
        (successorTransform T x (some v))).NonNeg)
    (hSc : Sc.NonNeg) : (nodeChoice rec S T Sc x).NonNeg := by
  unfold nodeChoice
  exact classChoiceDist_nonNeg (fun v hv => hrec v hv)
    ((successorTransform_nonNeg hSc x none).weight_nonneg)

open Classical in
private theorem nodeCutFinset_nonneg
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {S T : PFunPDS X Y}
    (hSnn : ∀ x, (nodeChoice recS S T S x).NonNeg)
    (hTnn : ∀ x, (nodeChoice recT S T T x).NonNeg) :
    ∀ u ∈ nodeCutFinset recS recT S T, 0 ≤ u := by
  intro u hu
  unfold nodeCutFinset at hu
  by_cases hfin : {u | ∃ x,
      u ∈ layoutCuts (nodeLayout recS recT S T x)
        ∨ u ∈ layoutCuts (nodeLayoutT recS recT S T x)}.Finite
  · rw [dif_pos hfin] at hu
    obtain ⟨x, h | h⟩ := hfin.mem_toFinset.mp hu
    · exact layoutCuts_nonneg
        (commonFirstLayout_entry_nonneg (hSnn x) (hTnn x)) u h
    · exact layoutCuts_nonneg
        (commonFirstLayout_entry_nonneg (hTnn x) (hSnn x)) u h
  · rw [dif_neg hfin] at hu
    exact absurd hu (Finset.notMem_empty u)

open Classical in
/-- The answer-mass partition at a query: the answered branch weights
over the cell's value set plus the `⊥`-branch weight exhaust the
side's weight. -/
private theorem sum_weight_successorTransform (P S T : PFunPDS X Y)
    (x : X) (hsub : P.support ⊆ S.support ∪ T.support) :
    (∑ v ∈ cellVals S T x,
        Dist.weight (successorTransform P x (some v)))
      + Dist.weight (successorTransform P x none) = P.weight := by
  have hV : ∀ s ∈ P.support,
      (fun s' => PFunDDS.output (PFunDDS.fullyDefined s') [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp)) s
        ∈ insert none ((cellVals S T x).image some) := by
    intro s hs
    beta_reduce
    rcases hout : PFunDDS.output (PFunDDS.fullyDefined s) [x]
        (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | v
    · exact Finset.mem_insert_self none _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, ?_, rfl⟩)
      exact mem_cellVals.mpr ⟨s, hsub hs, hout⟩
  have hpart : P.weight
      = P.mass (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp) = none)
        + ∑ v ∈ cellVals S T x,
            P.mass fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
    rw [← Dist.mass_true (X := P),
      mass_eq_sum_mass_fiber P _ _ _ hV, Finset.sum_insert (by simp)]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Dist.mass_congr P fun s => iff_of_eq (true_and _)
    · rw [Finset.sum_image fun v _ v' _ h => Option.some.inj h]
      exact Finset.sum_congr rfl fun v _ =>
        Dist.mass_congr P fun s => iff_of_eq (true_and _)
  rw [Finset.sum_congr rfl fun v _ =>
      weight_successorTransform P x (some v),
    weight_successorTransform P x none, hpart, add_comm]

open Classical in
/-- F1, S-side: under weight preservation of the rebuild parameter,
every query's layout total is the cell's full S-weight. -/
private theorem layoutTotal_nodeLayout
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (x : X)
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (hrec : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      Dist.weight (recS S' T') = Dist.weight S') :
    layoutTotal (nodeLayout recS recT S T x) = Dist.weight S := by
  unfold nodeLayout
  rw [layoutTotal_commonFirstLayout (Finset.nodup_toList _)
    fun a ha => Finset.mem_toList.mpr (Finset.mem_union_left _ ha)]
  show Dist.weight (nodeChoice recS S T S x) = Dist.weight S
  unfold nodeChoice
  rw [weight_classChoiceDist,
    Finset.sum_congr rfl fun v _ => hrec _ _
      (successorTransform_nonNeg hSnn x _)
      (successorTransform_nonNeg hTnn x _)]
  exact sum_weight_successorTransform S S T x Finset.subset_union_left

open Classical in
/-- F1, T-side. -/
private theorem layoutTotal_nodeLayoutT
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (x : X)
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (hrec : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      Dist.weight (recT S' T') = Dist.weight T') :
    layoutTotal (nodeLayoutT recS recT S T x) = Dist.weight T := by
  unfold nodeLayoutT
  rw [layoutTotal_commonFirstLayout (Finset.nodup_toList _)
    fun a ha => Finset.mem_toList.mpr (Finset.mem_union_right _ ha)]
  show Dist.weight (nodeChoice recT S T T x) = Dist.weight T
  unfold nodeChoice
  rw [weight_classChoiceDist,
    Finset.sum_congr rfl fun v _ => hrec _ _
      (successorTransform_nonNeg hSnn x _)
      (successorTransform_nonNeg hTnn x _)]
  exact sum_weight_successorTransform T S T x Finset.subset_union_right

open Classical in
/-- Multiples of one mass value, capped by the weight (multiplicity
`≤ ⌈w₀/m⌉`: equal masses on distinct atoms are genuine multiplicity,
approved amendment to the V_n closure). -/
private noncomputable def multiplesUpTo (w₀ m : ℝ) :
    Finset ℝ :=
  (Finset.range (⌈(w₀ / m : ℝ)⌉₊ + 1)).image fun k : ℕ => (k : ℝ) * m

open Classical in
/-- All weight-capped multiplicity sums over a value set: the finite
overapproximation of every subset sum of any distribution whose masses
lie in `W` and whose weight is at most `w₀`. -/
private noncomputable def boundedSums (W : Finset ℝ) (w₀ : ℝ) :
    Finset ℝ :=
  W.toList.foldr
    (fun m acc => (multiplesUpTo w₀ m ×ˢ acc).image fun q => q.1 + q.2)
    {0}

open Classical in
/-- The fuel-indexed universal value set (THM231_ATTAINMENT.md §5,
amended): each round closes under weight-capped multiplicity sums and
one cut round — every mass and every cut the depth-`n` rebuild
produces is invariantly inside. -/
private noncomputable def valueSet :
    ℕ → Finset ℝ → ℝ → Finset ℝ
  | 0, V, _ => insert 0 V
  | n + 1, V, w₀ =>
      boundedSums (cutRound 3 (boundedSums (valueSet n V w₀) w₀)) w₀

open Classical in
/-- The counting lemma, family form: any finite sum of `W`-values
capped by `w₀` is a weight-capped multiplicity sum — group the index
set by value; each value's multiplicity is at most `⌈w₀/m⌉` because
the group total is below the cap. -/
private theorem sum_mem_boundedSums {ι : Type*} {t : Finset ι}
    {f : ι → ℝ} {W : Finset ℝ} {w₀ : ℝ} (hf : ∀ i ∈ t, 0 ≤ f i)
    (hW : ∀ i ∈ t, f i ∈ W) (hw : ∑ i ∈ t, f i ≤ w₀) :
    (∑ i ∈ t, f i) ∈ boundedSums W w₀ := by
  suffices h : ∀ (l : List ℝ) (G' : Finset ι), G' ⊆ t →
      (∀ i ∈ G', f i ∈ l) →
      (∑ i ∈ G', f i) ∈ l.foldr (fun m acc =>
        (multiplesUpTo w₀ m ×ˢ acc).image fun q => q.1 + q.2) {0} by
    exact h W.toList t (Finset.Subset.refl t)
      fun i hi => Finset.mem_toList.mpr (hW i hi)
  intro l
  induction l with
  | nil =>
      intro G' _ hvals
      have hempty : G' = ∅ :=
        Finset.eq_empty_of_forall_notMem fun i hi =>
          List.not_mem_nil (hvals i hi)
      rw [hempty, Finset.sum_empty]
      exact Finset.mem_singleton_self 0
  | cons m l' ih =>
      intro G' hsub hvals
      rw [← Finset.sum_filter_add_sum_filter_not G' fun i => f i = m]
      have hconst : ∑ i ∈ G'.filter (fun i => f i = m), f i
          = (G'.filter fun i => f i = m).card • m := by
        rw [← Finset.sum_const]
        exact Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
      refine Finset.mem_image.mpr
        ⟨(∑ i ∈ G'.filter fun i => f i = m, f i,
          ∑ i ∈ G'.filter fun i => ¬ f i = m, f i),
          Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
      · rw [hconst]
        rcases eq_or_ne m 0 with rfl | hm
        · rw [smul_zero]
          unfold multiplesUpTo
          exact Finset.mem_image.mpr
            ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩
        · rcases le_or_gt m 0 with hmle | hmpos
          · -- a negative value is never attained by a non-negative family
            have hempty : (G'.filter fun i => f i = m) = ∅ := by
              refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
              obtain ⟨hiG, hval⟩ := Finset.mem_filter.mp hi
              exact absurd (hval ▸ hf i (hsub hiG))
                (not_le.mpr (lt_of_le_of_ne hmle hm))
            rw [hempty, Finset.card_empty, zero_smul]
            unfold multiplesUpTo
            exact Finset.mem_image.mpr
              ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩
          have hle : ((G'.filter fun i => f i = m).card : ℝ) * m
              ≤ w₀ := by
            rw [← nsmul_eq_mul, ← hconst]
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (fun i hi _ => hf i (hsub hi))) ?_
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i hi _ => hf i hi)) hw
          have hdiv : ((G'.filter fun i => f i = m).card : ℝ)
              ≤ w₀ / m := by
            rw [le_div_iff₀ hmpos]
            exact hle
          have hcard_le : (G'.filter fun i => f i = m).card
              ≤ ⌈(w₀ / m : ℝ)⌉₊ :=
            calc (G'.filter fun i => f i = m).card
                = ⌈(((G'.filter fun i => f i = m).card : ℕ) : ℝ)⌉₊ :=
                  (Nat.ceil_natCast _).symm
              _ ≤ ⌈(w₀ / m : ℝ)⌉₊ := Nat.ceil_mono hdiv
          have hmem : ((G'.filter fun i => f i = m).card : ℝ) * m
              ∈ multiplesUpTo w₀ m := by
            unfold multiplesUpTo
            exact Finset.mem_image.mpr
              ⟨(G'.filter fun i => f i = m).card,
                Finset.mem_range.mpr (Nat.lt_succ_of_le hcard_le), rfl⟩
          rw [nsmul_eq_mul]
          exact hmem
      · refine ih _ ((Finset.filter_subset _ _).trans hsub) fun i hi => ?_
        obtain ⟨hiG, hine⟩ := Finset.mem_filter.mp hi
        rcases List.mem_cons.mp (hvals i hiG) with h | h
        · exact absurd h hine
        · exact h

open Classical in
/-- The counting lemma, distribution form. -/
private theorem subsums_subset_boundedSums {A : Type*} {μ : Dist A}
    {W : Finset ℝ} {w₀ : ℝ} (hμ : μ.NonNeg)
    (hW : ∀ a ∈ μ.support, μ a ∈ W) (hw : μ.weight ≤ w₀) :
    subsums μ ⊆ boundedSums W w₀ := by
  intro u hu
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hu
  have hGsupp := Finset.mem_powerset.mp hG
  have hsw : (∑ a ∈ μ.support, μ a) = μ.weight :=
    (Dist.weight_eq_finsupp_sum μ).symm
  refine sum_mem_boundedSums (fun a _ => hμ a)
    (fun a ha => hW a (hGsupp ha)) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsupp
    (fun a _ _ => hμ a)) ?_
  exact le_trans (le_of_eq hsw) hw

open Classical in
private theorem zero_mem_boundedSums (W : Finset ℝ) {w₀ : ℝ}
    (hw₀ : 0 ≤ w₀) : (0 : ℝ) ∈ boundedSums W w₀ := by
  have h := sum_mem_boundedSums (t := (∅ : Finset ℕ)) (f := fun _ => 0)
    (W := W) (w₀ := w₀)
    (fun i hi => absurd hi (Finset.notMem_empty i))
    (fun i hi => absurd hi (Finset.notMem_empty i)) (by simpa using hw₀)
  simpa using h

private theorem boundedSums_nonneg {W : Finset ℝ}
    (hW : ∀ v ∈ W, 0 ≤ v) {w₀ : ℝ} :
    ∀ z ∈ boundedSums W w₀, 0 ≤ z := by
  suffices h : ∀ ws : List ℝ, (∀ v ∈ ws, 0 ≤ v) →
      ∀ z ∈ ws.foldr (fun m acc =>
        (multiplesUpTo w₀ m ×ˢ acc).image fun q => q.1 + q.2) {0},
      (0 : ℝ) ≤ z by
    exact h W.toList fun v hv => hW v (Finset.mem_toList.mp hv)
  intro ws
  induction ws with
  | nil =>
      intro _ z hz
      rw [Finset.mem_singleton.mp hz]
  | cons m l ih =>
      intro hnn z hz
      obtain ⟨⟨q₁, q₂⟩, hq, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hq
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h₁
      exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg k) (hnn m (by simp)))
        (ih (fun v hv => hnn v (List.mem_cons_of_mem m hv)) q₂ h₂)

private theorem valueSet_nonneg {V : Finset ℝ}
    (hV : ∀ v ∈ V, 0 ≤ v) (w₀ : ℝ) :
    ∀ (K : ℕ), ∀ z ∈ valueSet K V w₀, 0 ≤ z := by
  intro K
  cases K with
  | zero =>
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | h
      · exact le_refl 0
      · exact hV z h
  | succ K => exact boundedSums_nonneg (cutRound_nonneg 3 _)

open Classical in
/-- Capped values transport into their own bounded-sum closure (the
`k = 1` multiplicity witness). -/
private theorem mem_boundedSums_of_mem {W : Finset ℝ}
    {w₀ v : ℝ} (hv0 : 0 ≤ v) (hv : v ∈ W) (hcap : v ≤ w₀) :
    v ∈ boundedSums W w₀ := by
  have h := sum_mem_boundedSums (t := ({0} : Finset ℕ)) (f := fun _ => v)
    (W := W) (w₀ := w₀) (fun _ _ => hv0) (fun _ _ => hv)
    (by simpa using hcap)
  simpa using h

open Classical in
/-- Value-restricted level monotonicity of the fuel-indexed value set:
capped values survive a closure round (each stage keeps them by its
self-inclusion).  Unrestricted monotonicity is false — `cutRound` sums
can exceed the cap — but every value the invariant transports is a
mass, hence capped. -/
private theorem mem_valueSet_succ {V : Finset ℝ} {w₀ v : ℝ}
    (hV : ∀ z ∈ V, 0 ≤ z)
    {n : ℕ} (hv0 : 0 ≤ v) (hv : v ∈ valueSet n V w₀) (hcap : v ≤ w₀) :
    v ∈ valueSet (n + 1) V w₀ := by
  show v ∈ boundedSums (cutRound 3 (boundedSums (valueSet n V w₀) w₀)) w₀
  refine mem_boundedSums_of_mem hv0 ?_ hcap
  refine self_subset_cutRound (by omega) _
    (boundedSums_nonneg (valueSet_nonneg hV w₀ n)) ?_
  exact mem_boundedSums_of_mem hv0 hv hcap

open Classical in
private theorem mem_valueSet_of_le {V : Finset ℝ} {w₀ v : ℝ}
    (hV : ∀ z ∈ V, 0 ≤ z)
    {n n' : ℕ} (hn : n ≤ n') (hv0 : 0 ≤ v) (hv : v ∈ valueSet n V w₀)
    (hcap : v ≤ w₀) : v ∈ valueSet n' V w₀ := by
  induction hn with
  | refl => exact hv
  | step _ ih => exact mem_valueSet_succ hV hv0 ih hcap

open Classical in
/-- Every event mass is a subsum (the fiber's subset sum). -/
private theorem mass_mem_subsums {A : Type*} (μ : Dist A)
    (P : A → Prop) : μ.mass P ∈ subsums μ := by
  have hmass : μ.mass P = ∑ a ∈ μ.support.filter P, μ a := by
    unfold Dist.mass
    simp only [Finsupp.sum]
    rw [Finset.sum_filter]
  rw [hmass]
  exact finset_sum_mem_subsums μ _

open Classical in
/-- Every point mass is a subsum (the singleton subset sum). -/
private theorem apply_mem_subsums {A : Type*} (μ : Dist A) (a : A) :
    μ a ∈ subsums μ := by
  have h := finset_sum_mem_subsums μ {a}
  rwa [Finset.sum_singleton] at h

private theorem list_sum_apply {A : Type*} (l : List (Dist A)) (a : A) :
    l.sum a = (l.map fun μ => μ a).sum := by
  induction l with
  | nil => rfl
  | cons μ l ih =>
      rw [List.sum_cons, Finsupp.add_apply, ih, List.map_cons,
        List.sum_cons]

private theorem sum_apply_le_weight {A : Type*} {μ : Dist A}
    (hμ : μ.NonNeg) (G : Finset A) : (∑ a ∈ G, μ a) ≤ μ.weight := by
  classical
  have hsplit : (∑ a ∈ G, μ a) = ∑ a ∈ G ∩ μ.support, μ a := by
    symm
    refine Finset.sum_subset Finset.inter_subset_left
      fun a haG hnot => ?_
    exact Finsupp.notMem_support_iff.mp
      fun hs => hnot (Finset.mem_inter.mpr ⟨haG, hs⟩)
  rw [hsplit]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    Finset.inter_subset_right (fun a _ _ => hμ a)) ?_
  exact le_of_eq (Dist.weight_eq_finsupp_sum μ).symm

open Classical in
/-- Subset sums of a profile distribution decompose into a
range-indexed family of piece masses (`0` for skipped pieces). -/
private theorem profileDist_sum_family
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    {Us : Finset ℝ} :
    ∀ us : List ℝ, us.Pairwise (· ≤ ·) → (∀ u ∈ us, u ∈ Us) →
      ∀ G : Finset (X → Option (Y × PFunDDS.DDS X Y)),
        ∃ (k : ℕ) (f : ℕ → ℝ),
          (∀ i ∈ Finset.range k, 0 ≤ f i)
          ∧ (∀ i ∈ Finset.range k, f i ∈ insert 0 (tsubPairs Us))
          ∧ (∑ i ∈ Finset.range k, f i)
              = ∑ p ∈ G, profileDist Lf us p := by
  intro us
  induction us with
  | nil =>
      intro _ _ G
      refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
      rw [Finset.range_zero, Finset.sum_empty]
      symm
      refine Finset.sum_eq_zero fun p _ => ?_
      rfl
  | cons u vs ih =>
      intro hsort hUs G
      cases vs with
      | nil =>
          refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
          rw [Finset.range_zero, Finset.sum_empty]
          symm
          refine Finset.sum_eq_zero fun p _ => ?_
          rfl
      | cons u' vs' =>
          obtain ⟨k, f, hf0, hf, hsum⟩ :=
            ih (List.pairwise_cons.mp hsort).2
              (fun z hz => hUs z (List.mem_cons_of_mem u hz)) G
          refine ⟨k + 1, fun i => if i = 0
            then (if (fun x => valueAt none (Lf x) u) ∈ G
              then u' - u else 0)
            else f (i - 1), ?_, ?_, ?_⟩
          · intro i hi
            beta_reduce
            by_cases h0 : i = 0
            · rw [if_pos h0]
              by_cases hq : (fun x => valueAt none (Lf x) u) ∈ G
              · rw [if_pos hq]
                exact sub_nonneg.mpr
                  ((List.pairwise_cons.mp hsort).1 u' (by simp))
              · rw [if_neg hq]
            · rw [if_neg h0]
              refine hf0 (i - 1) (Finset.mem_range.mpr ?_)
              have := Finset.mem_range.mp hi
              omega
          · intro i hi
            beta_reduce
            by_cases h0 : i = 0
            · rw [if_pos h0]
              by_cases hq : (fun x => valueAt none (Lf x) u) ∈ G
              · rw [if_pos hq]
                refine Finset.mem_insert_of_mem ?_
                refine Finset.mem_image.mpr ⟨(u', u),
                  Finset.mem_product.mpr
                    ⟨hUs u' (by simp), hUs u (by simp)⟩, ?_⟩
                dsimp only
                rw [max_eq_left (sub_nonneg.mpr
                  ((List.pairwise_cons.mp hsort).1 u' (by simp)))]
              · rw [if_neg hq]
                exact Finset.mem_insert_self 0 _
            · rw [if_neg h0]
              refine hf (i - 1) (Finset.mem_range.mpr ?_)
              have := Finset.mem_range.mp hi
              omega
          · rw [Finset.sum_range_succ']
            have hshift : ∀ i ∈ Finset.range k,
                (if i + 1 = 0
                  then (if (fun x => valueAt none (Lf x) u) ∈ G
                    then u' - u else 0)
                  else f (i + 1 - 1)) = f i := fun i _ => by
              rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
            rw [Finset.sum_congr rfl hshift, hsum, if_pos rfl]
            have hdist : ∀ p, profileDist Lf (u :: u' :: vs') p
                = Finsupp.single (fun x => valueAt none (Lf x) u)
                    (u' - u) p + profileDist Lf (u' :: vs') p := by
              intro p
              rw [show profileDist Lf (u :: u' :: vs')
                  = Finsupp.single (fun x => valueAt none (Lf x) u)
                      (u' - u) + profileDist Lf (u' :: vs') from rfl,
                Finsupp.add_apply]
            rw [Finset.sum_congr rfl fun p _ => hdist p,
              Finset.sum_add_distrib, add_comm]
            refine congrArg₂ (· + ·) ?_ rfl
            symm
            rw [Finset.sum_congr rfl fun p _ => Finsupp.single_apply]
            exact Finset.sum_ite_eq G _ fun _ => u' - u

open Classical in
/-- Subset sums of a profile distribution are weight-capped
multiplicity sums of piece masses (each piece mass is a truncated
difference of cut values). -/
private theorem subsums_profileDist_subset
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    {Us : Finset ℝ} {w₀ : ℝ} (us : List ℝ)
    (hsort : us.Pairwise (· ≤ ·))
    (hUs : ∀ u ∈ us, u ∈ Us)
    (hnn : (profileDist Lf us).NonNeg)
    (hw : Dist.weight (profileDist Lf us) ≤ w₀) :
    subsums (profileDist Lf us)
      ⊆ boundedSums (insert 0 (tsubPairs Us)) w₀ := by
  intro z hz
  obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨k, f, hf0, hf, hsum⟩ := profileDist_sum_family Lf us hsort hUs G
  rw [← hsum]
  refine sum_mem_boundedSums hf0 hf ?_
  rw [hsum]
  exact le_trans (sum_apply_le_weight hnn G) hw

open Classical in
/-- Every point mass of an interval joint is a weight-capped
multiplicity sum of piece masses. -/
private theorem apply_intervalJoint_mem_boundedSums
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    {Us : Finset ℝ} {w₀ : ℝ} (us : List ℝ)
    (hsort : us.Pairwise (· ≤ ·))
    (hUs : ∀ u ∈ us, u ∈ Us)
    (hw : Dist.weight (profileDist Lf us) ≤ w₀)
    (r : PFunDDS.DDS X Y) :
    intervalJoint Lf us r
      ∈ boundedSums (insert 0 (tsubPairs Us)) w₀ := by
  refine subsums_profileDist_subset Lf us hsort hUs
    (profileDist_nonNeg Lf us hsort) hw ?_
  exact subsums_fTransform_subset (glueProfile id) (profileDist Lf us)
    (apply_mem_subsums (intervalJoint Lf us) r)

open Classical in
/-- The point masses of a choice distribution: a tagged branch mass,
the `⊥`-mass, or `0`. -/
private theorem apply_classChoiceDist_mem {vs : Finset Y}
    {B : Y → PFunPDS X Y} {β : ℝ} {W : Finset ℝ}
    (hB : ∀ v ∈ vs, ∀ a, B v a ∈ W) (hβ : β ∈ W) (h0 : 0 ∈ W) :
    ∀ c, classChoiceDist vs B β c ∈ W := by
  intro c
  unfold classChoiceDist
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
  rcases c with _ | ⟨v, a⟩
  · rw [Finset.sum_eq_zero fun v _ =>
      Dist.fTransform_apply_of_forall_ne _ _ _ fun a => by simp,
      Finsupp.single_eq_same, zero_add]
    exact hβ
  · rw [Finsupp.single_apply, if_neg (by simp), add_zero]
    by_cases hv : v ∈ vs
    · rw [Finset.sum_eq_single_of_mem v hv fun v' _ hne =>
        Dist.fTransform_apply_of_forall_ne _ _ _ fun a' => by
          simp [hne]]
      rw [show (some (v, a) : Option (Y × PFunDDS.DDS X Y))
          = (fun s => some (v, s)) a from rfl,
        Dist.fTransform_injective_apply (B v) _
          (fun a₁ a₂ h => by simpa using h) a]
      exact hB v hv a
    · rw [Finset.sum_eq_zero fun v' hv' =>
        Dist.fTransform_apply_of_forall_ne _ _ _ fun a' => by
          simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
          intro hveq
          exact absurd (hveq ▸ hv') hv]
      exact h0

open Classical in
/-- The cuts chain at invariant levels: every per-query layout cut of
the node lands in one cut round over the bounded sums of the choice
masses (`A3` containment + the counting lemma + the shape
absorption). -/
private theorem layoutCuts_nodeLayout_mem
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {S T : PFunPDS X Y} {W : Finset ℝ} {w₀ : ℝ}
    (hSnn : ∀ x, (nodeChoice recS S T S x).NonNeg)
    (hTnn : ∀ x, (nodeChoice recT S T T x).NonNeg)
    (hS : ∀ x c, nodeChoice recS S T S x c ∈ W)
    (hT : ∀ x c, nodeChoice recT S T T x c ∈ W)
    (hwS : ∀ x, Dist.weight (nodeChoice recS S T S x) ≤ w₀)
    (hwT : ∀ x, Dist.weight (nodeChoice recT S T T x) ≤ w₀) (x : X) :
    (∀ u ∈ layoutCuts (nodeLayout recS recT S T x),
        u ∈ cutRound 3 (boundedSums W w₀))
      ∧ ∀ u ∈ layoutCuts (nodeLayoutT recS recT S T x),
          u ∈ cutRound 3 (boundedSums W w₀) := by
  constructor
  · intro u hu
    refine nodeCuts_subset_cutRound (le_refl 3) (hSnn x) (hTnn x)
      (subsums_subset_boundedSums (hSnn x) (fun c _ => hS x c) (hwS x))
      (subsums_subset_boundedSums (hTnn x) (fun c _ => hT x c) (hwT x))
      (layoutCuts_commonFirstLayout_subset (Finset.nodup_toList _)
        _ _ u hu)
  · intro u hu
    refine nodeCuts_subset_cutRound (le_refl 3) (hTnn x) (hSnn x)
      (subsums_subset_boundedSums (hTnn x) (fun c _ => hT x c) (hwT x))
      (subsums_subset_boundedSums (hSnn x) (fun c _ => hS x c) (hwS x))
      (layoutCuts_commonFirstLayout_subset (Finset.nodup_toList _)
        _ _ u hu)

open Classical in
/-- The dite discharge: with choice masses bounded, the node's cut set
is finite and `nodeCutFinset` contains every layout cut of every
query, both sides. -/
private theorem mem_nodeCutFinset
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {S T : PFunPDS X Y} {W : Finset ℝ} {w₀ : ℝ}
    (hSnn : ∀ x, (nodeChoice recS S T S x).NonNeg)
    (hTnn : ∀ x, (nodeChoice recT S T T x).NonNeg)
    (hS : ∀ x c, nodeChoice recS S T S x c ∈ W)
    (hT : ∀ x c, nodeChoice recT S T T x c ∈ W)
    (hwS : ∀ x, Dist.weight (nodeChoice recS S T S x) ≤ w₀)
    (hwT : ∀ x, Dist.weight (nodeChoice recT S T T x) ≤ w₀) :
    (∀ x, ∀ u ∈ layoutCuts (nodeLayout recS recT S T x),
        u ∈ nodeCutFinset recS recT S T)
      ∧ ∀ x, ∀ u ∈ layoutCuts (nodeLayoutT recS recT S T x),
          u ∈ nodeCutFinset recS recT S T := by
  have hfin : {u | ∃ x, u ∈ layoutCuts (nodeLayout recS recT S T x)
      ∨ u ∈ layoutCuts (nodeLayoutT recS recT S T x)}.Finite := by
    refine Set.Finite.subset
      (Finset.finite_toSet (cutRound 3 (boundedSums W w₀))) ?_
    rintro u ⟨x, hu | hu⟩
    · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).1 u hu
    · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).2 u hu
  constructor
  · intro x u hu
    unfold nodeCutFinset
    rw [dif_pos hfin]
    exact hfin.mem_toFinset.mpr ⟨x, Or.inl hu⟩
  · intro x u hu
    unfold nodeCutFinset
    rw [dif_pos hfin]
    exact hfin.mem_toFinset.mpr ⟨x, Or.inr hu⟩

private theorem weight_zero_dist {A : Type*} :
    Dist.weight (0 : Dist A) = 0 := by
  rw [Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_zero_index

open Classical in
private theorem filter_fiber_eq_zero {A B : Type*} {μ : Dist A}
    {g : A → B} {v : B} (hv : v ∉ μ.support.image g) :
    (μ.filter fun a => g a = v) = 0 := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hval : g a = v
  · rw [if_pos hval]
    by_contra hne
    exact hv (Finset.mem_image.mpr
      ⟨a, Finsupp.mem_support_iff.mpr hne, hval⟩)
  · rw [if_neg hval]

open Classical in
/-- The fiber weights of a statistic partition the weight, over any
covering index set. -/
private theorem weight_sum_filter_fiber {A B : Type*} (μ : Dist A)
    (g : A → B) (t : Finset B) (ht : μ.support.image g ⊆ t) :
    ∑ v ∈ t, Dist.weight (μ.filter fun a => g a = v) = μ.weight := by
  have hsplit := eq_sum_filter_fiber μ g
  calc ∑ v ∈ t, Dist.weight (μ.filter fun a => g a = v)
      = ∑ v ∈ μ.support.image g,
          Dist.weight (μ.filter fun a => g a = v) := by
        symm
        refine Finset.sum_subset ht fun v _ hv => ?_
        rw [filter_fiber_eq_zero hv, weight_zero_dist]
    _ = Dist.weight (∑ v ∈ μ.support.image g,
          μ.filter fun a => g a = v) := (weight_finset_sum _ _).symm
    _ = μ.weight := by rw [← hsplit]

open Classical in
/-- Weight preservation of the rebuild — **invariant-free**: the
interval joint's weight is its cut span (`weight_intervalJoint`),
which `usOf` pins to the cell weight regardless of the branch data, so
both sides' weights survive every fuel step. -/
private theorem weight_rebuild :
    ∀ (n : ℕ) {S T : PFunPDS X Y}, S.NonNeg → T.NonNeg →
      Dist.weight (rebuild n S T).1 = S.weight
        ∧ Dist.weight (rebuild n S T).2 = T.weight := by
  intro n
  induction n with
  | zero => intro S T _ _; exact ⟨rfl, rfl⟩
  | succ n _ =>
      intro S T hSnn hTnn
      have hcSnn : ∀ σ : X → Prop,
          RandomSystems.Dist.NonNeg (S.filter fun s => pattern s = σ) :=
        fun σ => filter_nonNeg hSnn _
      have hcTnn : ∀ σ : X → Prop,
          RandomSystems.Dist.NonNeg (T.filter fun s => pattern s = σ) :=
        fun σ => filter_nonNeg hTnn _
      have hchS : ∀ σ x, (nodeChoice (fun S' T' => (rebuild n S' T').1)
          (S.filter fun s => pattern s = σ)
          (T.filter fun s => pattern s = σ)
          (S.filter fun s => pattern s = σ) x).NonNeg := fun σ x =>
        nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)).1) (hcSnn σ)
      have hchT : ∀ σ x, (nodeChoice (fun S' T' => (rebuild n S' T').2)
          (S.filter fun s => pattern s = σ)
          (T.filter fun s => pattern s = σ)
          (T.filter fun s => pattern s = σ) x).NonNeg := fun σ x =>
        nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)).2) (hcTnn σ)
      constructor
      · show Dist.weight (((S.support ∪ T.support).image pattern).sum
            fun σ => (_, _)).1 = S.weight
        rw [Prod.fst_sum]
        dsimp only
        rw [weight_finset_sum]
        rw [Finset.sum_congr rfl fun σ _ => weight_intervalJoint _ _
          (usOf_ne_nil _ _) ((usOf_pairwise _ _).imp le_of_lt)]
        rw [Finset.sum_congr rfl fun σ _ => by
          rw [usOf_getLast ((hcSnn σ).weight_nonneg),
            usOf_head ((hcSnn σ).weight_nonneg)
              (nodeCutFinset_nonneg (hchS σ) (hchT σ)), sub_zero]]
        exact weight_sum_filter_fiber S pattern _
          (Finset.image_subset_image Finset.subset_union_left)
      · show Dist.weight (((S.support ∪ T.support).image pattern).sum
            fun σ => (_, _)).2 = T.weight
        rw [Prod.snd_sum]
        dsimp only
        rw [weight_finset_sum]
        rw [Finset.sum_congr rfl fun σ _ => weight_intervalJoint _ _
          (usOf_ne_nil _ _) ((usOf_pairwise _ _).imp le_of_lt)]
        rw [Finset.sum_congr rfl fun σ _ => by
          rw [usOf_getLast ((hcTnn σ).weight_nonneg),
            usOf_head ((hcTnn σ).weight_nonneg)
              (nodeCutFinset_nonneg (hchS σ) (hchT σ)), sub_zero]]
        exact weight_sum_filter_fiber T pattern _
          (Finset.image_subset_image Finset.subset_union_right)

private theorem le_list_sum {l : List ℝ} (h0 : ∀ v ∈ l, 0 ≤ v) {v : ℝ}
    (hv : v ∈ l) : v ≤ l.sum := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
      rw [List.sum_cons]
      have hl0 : ∀ z ∈ l, (0 : ℝ) ≤ z :=
        fun z hz => h0 z (List.mem_cons_of_mem a hz)
      rcases List.mem_cons.mp hv with rfl | h
      · exact le_add_of_nonneg_right
          (List.sum_nonneg fun z hz => hl0 z hz)
      · exact le_trans (ih hl0 h) (le_add_of_nonneg_left (h0 a (by simp)))

open Classical in
/-- Bounded-sum membership, elimination form: every element flattens
into a plain list of `W`-values. -/
private theorem mem_boundedSums_elim {W : Finset ℝ}
    {w₀ z : ℝ} (hz : z ∈ boundedSums W w₀) :
    ∃ l : List ℝ, (∀ v ∈ l, v ∈ W) ∧ l.sum = z := by
  suffices h : ∀ (ws : List ℝ), (∀ v ∈ ws, v ∈ W) →
      ∀ z', z' ∈ ws.foldr (fun m acc =>
        (multiplesUpTo w₀ m ×ˢ acc).image fun q => q.1 + q.2) {0} →
      ∃ l : List ℝ, (∀ v ∈ l, v ∈ W) ∧ l.sum = z' by
    exact h W.toList (fun v hv => Finset.mem_toList.mp hv) z hz
  intro ws
  induction ws with
  | nil =>
      intro _ z' hz'
      refine ⟨[], by simp, ?_⟩
      rw [List.sum_nil, Finset.mem_singleton.mp hz']
  | cons m ws ih =>
      intro hws z' hz'
      obtain ⟨⟨c, z''⟩, hq, rfl⟩ := Finset.mem_image.mp hz'
      obtain ⟨hc, hz''⟩ := Finset.mem_product.mp hq
      obtain ⟨l', hl', hsum'⟩ :=
        ih (fun v hv => hws v (List.mem_cons_of_mem m hv)) z'' hz''
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      refine ⟨List.replicate k m ++ l', ?_, ?_⟩
      · intro v hv
        rcases List.mem_append.mp hv with h | h
        · rw [List.eq_of_mem_replicate h]
          exact hws m (by simp)
        · exact hl' v h
      · rw [List.sum_append, List.sum_replicate, hsum',
          nsmul_eq_mul]

private theorem list_sum_eq_range_sum (l : List ℝ) :
    l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_comm]

open Classical in
/-- Capped transport of bounded sums along a value-conditional
inclusion: the flattened values are each below the total, hence
capped, hence transportable. -/
private theorem mem_boundedSums_of_forall_mem {W W' : Finset ℝ}
    {w₀ z : ℝ} (hW0 : ∀ v ∈ W, 0 ≤ v)
    (hWW : ∀ v ∈ W, v ≤ w₀ → v ∈ W')
    (hz : z ∈ boundedSums W w₀) (hcap : z ≤ w₀) :
    z ∈ boundedSums W' w₀ := by
  obtain ⟨l, hl, rfl⟩ := mem_boundedSums_elim hz
  have hl0 : ∀ v ∈ l, (0 : ℝ) ≤ v := fun v hv => hW0 v (hl v hv)
  rw [list_sum_eq_range_sum]
  refine sum_mem_boundedSums (fun i hi => ?_) (fun i hi => ?_) ?_
  · rcases lt_or_ge i l.length with hlen | hlen
    · have hmem : l.getD i 0 ∈ l := by
        rw [List.getD_eq_getElem l 0 hlen]
        exact l.getElem_mem hlen
      exact hl0 _ hmem
    · rw [List.getD_eq_default l 0 (by omega)]
  · rcases lt_or_ge i l.length with hlen | hlen
    · have hmem : l.getD i 0 ∈ l := by
        rw [List.getD_eq_getElem l 0 hlen]
        exact l.getElem_mem hlen
      refine hWW _ (hl _ hmem) ?_
      exact le_trans (le_list_sum hl0 hmem) hcap
    · rw [List.getD_eq_default l 0 (by omega)]
      exact absurd (Finset.mem_range.mp hi) (by omega)
  · rw [← list_sum_eq_range_sum]
    exact hcap

open Classical in
private theorem tsub_mem_cutRound {N : ℕ} (hN : 1 ≤ N)
    {W : Finset ℝ} {a c : ℝ} (ha : a ∈ W) (hc : c ∈ W) :
    max (a - c) 0 ∈ cutRound N W := by
  refine Finset.mem_image.mpr ⟨(a, c), Finset.mem_product.mpr
    ⟨?_, ?_⟩, rfl⟩
  · exact mem_sumsUpTo_of_mem hN (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ ha))
  · exact mem_sumsUpTo_of_mem hN (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hc))

open Classical in
private theorem zero_mem_valueSet (K : ℕ) (V : Finset ℝ)
    {w₀ : ℝ} (hw₀ : 0 ≤ w₀) : 0 ∈ valueSet K V w₀ := by
  cases K with
  | zero => exact Finset.mem_insert_self 0 V
  | succ K => exact zero_mem_boundedSums _ hw₀

private theorem apply_le_weight {A : Type*} {μ : Dist A}
    (hμ : μ.NonNeg) (a : A) :
    μ a ≤ μ.weight := by
  have h := sum_apply_le_weight hμ {a}
  rwa [Finset.sum_singleton] at h

open Classical in
private theorem weight_mem_subsums {A : Type*} (μ : Dist A) :
    μ.weight ∈ subsums μ := by
  have h := finset_sum_mem_subsums μ μ.support
  rwa [show (∑ a ∈ μ.support, μ a) = μ.weight from
    (Dist.weight_eq_finsupp_sum μ).symm] at h

open Classical in
private theorem weight_filter_le {A : Type*} {μ : Dist A}
    (hμ : μ.NonNeg) (P : A → Prop) [DecidablePred P] :
    Dist.weight (μ.filter P) ≤ μ.weight := by
  refine weight_le_weight (Finsupp.le_def.mpr fun a => ?_)
  rw [Finsupp.filter_apply]
  by_cases h : P a
  · rw [if_pos h]
  · rw [if_neg h]
    exact hμ a

open Classical in
/-- One closure round absorbs a capped bounded sum over the previous
level. -/
private theorem mem_valueSet_round {V : Finset ℝ} {w₀ z : ℝ}
    (hV : ∀ v ∈ V, 0 ≤ v)
    {K : ℕ} (hz : z ∈ boundedSums (valueSet K V w₀) w₀)
    (hcap : z ≤ w₀) : z ∈ valueSet (K + 1) V w₀ := by
  show z ∈ boundedSums
    (cutRound 3 (boundedSums (valueSet K V w₀) w₀)) w₀
  refine mem_boundedSums_of_forall_mem
    (valueSet_nonneg hV w₀ K) (fun v hv hvcap => ?_) hz hcap
  exact self_subset_cutRound (by omega) _
    (boundedSums_nonneg (valueSet_nonneg hV w₀ K))
    (mem_boundedSums_of_mem (valueSet_nonneg hV w₀ K v hv) hv hvcap)

open Classical in
/-- The bound extraction companion of `mem_nodeCutFinset`: the cut
Finset itself sits inside one cut round over the choice-mass level. -/
private theorem nodeCutFinset_subset
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {S T : PFunPDS X Y} {W : Finset ℝ} {w₀ : ℝ}
    (hSnn : ∀ x, (nodeChoice recS S T S x).NonNeg)
    (hTnn : ∀ x, (nodeChoice recT S T T x).NonNeg)
    (hS : ∀ x c, nodeChoice recS S T S x c ∈ W)
    (hT : ∀ x c, nodeChoice recT S T T x c ∈ W)
    (hwS : ∀ x, Dist.weight (nodeChoice recS S T S x) ≤ w₀)
    (hwT : ∀ x, Dist.weight (nodeChoice recT S T T x) ≤ w₀) :
    nodeCutFinset recS recT S T ⊆ cutRound 3 (boundedSums W w₀) := by
  have hfin : {u | ∃ x, u ∈ layoutCuts (nodeLayout recS recT S T x)
      ∨ u ∈ layoutCuts (nodeLayoutT recS recT S T x)}.Finite := by
    refine Set.Finite.subset
      (Finset.finite_toSet (cutRound 3 (boundedSums W w₀))) ?_
    rintro u ⟨x, hu | hu⟩
    · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).1 u hu
    · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).2 u hu
  intro u hu
  unfold nodeCutFinset at hu
  rw [dif_pos hfin] at hu
  obtain ⟨x, h | h⟩ := hfin.mem_toFinset.mp hu
  · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).1 u h
  · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).2 u h

private theorem layoutCuts_le_total {α : Type*}
    {L : List (α × ℝ)} (hL : ∀ e ∈ L, 0 ≤ e.2) {u : ℝ}
    (hu : u ∈ layoutCuts L) :
    u ≤ layoutTotal L := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hu
  calc layoutTotal (L.take k)
      ≤ layoutTotal (L.take k) + layoutTotal (L.drop k) :=
        le_add_of_nonneg_right (layoutTotal_nonneg
          fun e he => hL e ((List.drop_sublist k L).mem he))
    _ = layoutTotal L := by rw [← layoutTotal_append, List.take_append_drop]

open Classical in
/-- Every node-cut value is capped by the weight bound (cuts are
prefix sums of layouts whose totals are the choice weights). -/
private theorem nodeCutFinset_le
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {S T : PFunPDS X Y} {W : Finset ℝ} {w₀ : ℝ}
    (hSnn : ∀ x, (nodeChoice recS S T S x).NonNeg)
    (hTnn : ∀ x, (nodeChoice recT S T T x).NonNeg)
    (hS : ∀ x c, nodeChoice recS S T S x c ∈ W)
    (hT : ∀ x c, nodeChoice recT S T T x c ∈ W)
    (hwS : ∀ x, Dist.weight (nodeChoice recS S T S x) ≤ w₀)
    (hwT : ∀ x, Dist.weight (nodeChoice recT S T T x) ≤ w₀) :
    ∀ u ∈ nodeCutFinset recS recT S T, u ≤ w₀ := by
  have hfin : {u | ∃ x, u ∈ layoutCuts (nodeLayout recS recT S T x)
      ∨ u ∈ layoutCuts (nodeLayoutT recS recT S T x)}.Finite := by
    refine Set.Finite.subset
      (Finset.finite_toSet (cutRound 3 (boundedSums W w₀))) ?_
    rintro u ⟨x, hu | hu⟩
    · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).1 u hu
    · exact (layoutCuts_nodeLayout_mem hSnn hTnn hS hT hwS hwT x).2 u hu
  intro u hu
  unfold nodeCutFinset at hu
  rw [dif_pos hfin] at hu
  have htotS : ∀ x, layoutTotal (nodeLayout recS recT S T x)
      = Dist.weight (nodeChoice recS S T S x) := by
    intro x
    unfold nodeLayout
    rw [layoutTotal_commonFirstLayout (Finset.nodup_toList _)
      fun a ha => Finset.mem_toList.mpr (Finset.mem_union_left _ ha)]
  have htotT : ∀ x, layoutTotal (nodeLayoutT recS recT S T x)
      = Dist.weight (nodeChoice recT S T T x) := by
    intro x
    unfold nodeLayoutT
    rw [layoutTotal_commonFirstLayout (Finset.nodup_toList _)
      fun a ha => Finset.mem_toList.mpr (Finset.mem_union_right _ ha)]
  obtain ⟨x, h | h⟩ := hfin.mem_toFinset.mp hu
  · exact le_trans (le_of_eq_of_le (a := u) rfl
      (htotS x ▸ layoutCuts_le_total
        (commonFirstLayout_entry_nonneg (hSnn x) (hTnn x)) h)) (hwS x)
  · exact le_trans (le_of_eq_of_le (a := u) rfl
      (htotT x ▸ layoutCuts_le_total
        (commonFirstLayout_entry_nonneg (hTnn x) (hSnn x)) h)) (hwT x)

open Classical in
/-- The step core of the masses invariant: one cell joint's point
masses climb exactly two levels above the choice-mass level (one round
for the node-cut shape, one for the piece truncations). -/
private theorem apply_cellJoint_mem
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {Sc Tc : PFunPDS X Y} {V : Finset ℝ} {w₀ : ℝ} {C : ℕ}
    (hV : ∀ v ∈ V, 0 ≤ v)
    (hchSnn : ∀ x, (nodeChoice recS Sc Tc Sc x).NonNeg)
    (hchTnn : ∀ x, (nodeChoice recT Sc Tc Tc x).NonNeg)
    (hchoiceS : ∀ x c, nodeChoice recS Sc Tc Sc x c ∈ valueSet C V w₀)
    (hchoiceT : ∀ x c, nodeChoice recT Sc Tc Tc x c ∈ valueSet C V w₀)
    (hwchS : ∀ x, Dist.weight (nodeChoice recS Sc Tc Sc x) ≤ w₀)
    (hwchT : ∀ x, Dist.weight (nodeChoice recT Sc Tc Tc x) ≤ w₀)
    {w : ℝ} (hw0 : 0 ≤ w) (hwcap : w ≤ w₀)
    (hwval : w ∈ valueSet (C + 1) V w₀)
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    (r : PFunDDS.DDS X Y) :
    intervalJoint Lf
        (usOf w (nodeCutFinset recS recT Sc Tc)) r
      ∈ valueSet (C + 2) V w₀ := by
  have hw₀ : (0 : ℝ) ≤ w₀ := le_trans hw0 hwcap
  have hUnn := nodeCutFinset_nonneg hchSnn hchTnn
  have hraw : intervalJoint Lf
      (usOf w (nodeCutFinset recS recT Sc Tc)) r
      ∈ boundedSums (insert 0 (tsubPairs (insert 0
        (insert w (nodeCutFinset recS recT Sc Tc)))))
        w₀ := by
    refine apply_intervalJoint_mem_boundedSums _ _
      ((usOf_pairwise _ _).imp le_of_lt)
      (fun u hu => ?_) ?_ r
    · have hmem := (Finset.mem_sort _).mp hu
      rcases Finset.mem_insert.mp hmem with rfl | h
      · exact Finset.mem_insert_self 0 _
      · rcases Finset.mem_insert.mp h with rfl | h'
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_filter.mp h').1)
    · rw [weight_profileDist _ _ (usOf_ne_nil _ _)
        ((usOf_pairwise _ _).imp le_of_lt), usOf_getLast hw0,
        usOf_head hw0 hUnn, sub_zero]
      exact hwcap
  have hlift : ∀ z ∈ insert 0
      (insert w (nodeCutFinset recS recT Sc Tc)),
      (0 ≤ z ∧ z ∈ valueSet (C + 1) V w₀) ∧ z ≤ w₀ := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact ⟨⟨le_refl 0, zero_mem_valueSet _ _ hw₀⟩, hw₀⟩
    · rcases Finset.mem_insert.mp hz' with rfl | hz''
      · exact ⟨⟨hw0, hwval⟩, hwcap⟩
      · have hcap := nodeCutFinset_le hchSnn hchTnn
          hchoiceS hchoiceT hwchS hwchT z hz''
        refine ⟨⟨hUnn z hz'', ?_⟩, hcap⟩
        exact mem_boundedSums_of_mem (hUnn z hz'')
          (nodeCutFinset_subset hchSnn hchTnn
            hchoiceS hchoiceT hwchS hwchT hz'')
          hcap
  have hpos : ∀ z ∈ insert 0
      (insert w (nodeCutFinset recS recT Sc Tc)), 0 ≤ z :=
    fun z hz => (hlift z hz).1.1
  refine mem_boundedSums_of_forall_mem
    (fun v hv => ?nonneg) (fun v hv hvcap => ?_) hraw ?_
  case nonneg =>
    rcases Finset.mem_insert.mp hv with rfl | hv'
    · exact le_refl 0
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hv'
      exact le_max_right _ _
  · show v ∈ cutRound 3 (boundedSums (valueSet (C + 1) V w₀) w₀)
    rcases Finset.mem_insert.mp hv with rfl | hv'
    · exact zero_mem_cutRound _ _
    · obtain ⟨⟨a, c⟩, hac, rfl⟩ := Finset.mem_image.mp hv'
      obtain ⟨ha, hc⟩ := Finset.mem_product.mp hac
      obtain ⟨haV, hacap⟩ := hlift a ha
      obtain ⟨hcV, hccap⟩ := hlift c hc
      exact tsub_mem_cutRound (by omega)
        (mem_boundedSums_of_mem haV.1 haV.2 hacap)
        (mem_boundedSums_of_mem hcV.1 hcV.2 hccap)
  · refine le_trans (apply_le_weight (intervalJoint_nonNeg _
      ((usOf_pairwise _ _).imp le_of_lt)) r) ?_
    rw [weight_intervalJoint _ _ (usOf_ne_nil _ _)
      ((usOf_pairwise _ _).imp le_of_lt), usOf_getLast hw0,
      usOf_head hw0 hUnn, sub_zero]
    exact hwcap

open Classical in
/-- Branch masses climb one level (fiber sums of node masses, one
counting round). -/
private theorem branch_masses_mem {P : PFunPDS X Y}
    {V : Finset ℝ} {w₀ : ℝ} {K : ℕ} (hV : ∀ v ∈ V, 0 ≤ v)
    (hPnn : P.NonNeg)
    (hP : ∀ a, P a ∈ valueSet K V w₀) (hwP : P.weight ≤ w₀)
    (x : X) (y : Option Y) (r : PFunDDS.DDS X Y) :
    (successorTransform P x y) r ∈ valueSet (K + 1) V w₀ := by
  have h1 : (successorTransform P x y) r ∈ subsums P :=
    subsums_filter_subset P _ (subsums_fTransform_subset _ _
      (apply_mem_subsums (successorTransform P x y) r))
  have hwb : Dist.weight (successorTransform P x y) ≤ P.weight := by
    show Dist.weight (Dist.fTransform _ (P.filter _)) ≤ P.weight
    rw [Dist.weight_fTransform]
    exact weight_filter_le hPnn _
  refine mem_valueSet_round hV ?_
    (le_trans (apply_le_weight (successorTransform_nonNeg hPnn x y) r)
      (le_trans hwb hwP))
  exact subsums_subset_boundedSums hPnn (fun a _ => hP a) hwP h1

open Classical in
private theorem branch_weight_le {P : PFunPDS X Y} {w₀ : ℝ}
    (hPnn : P.NonNeg)
    (hwP : P.weight ≤ w₀) (x : X) (y : Option Y) :
    Dist.weight (successorTransform P x y) ≤ w₀ := by
  show Dist.weight (Dist.fTransform _ (P.filter _)) ≤ w₀
  rw [Dist.weight_fTransform]
  exact le_trans (weight_filter_le hPnn _) hwP

open Classical in
/-- **The masses invariant** (THM231_ATTAINMENT.md §5): every point
mass of the depth-`n` rebuild lies in the fuel-indexed value set, four
closure rounds per fuel step. -/
private theorem rebuild_masses (V : Finset ℝ) (w₀ : ℝ)
    (hV : ∀ v ∈ V, 0 ≤ v) :
    ∀ (n K : ℕ) (S T : PFunPDS X Y), S.NonNeg → T.NonNeg →
      (∀ a, S a ∈ valueSet K V w₀) → (∀ a, T a ∈ valueSet K V w₀) →
      S.weight ≤ w₀ → T.weight ≤ w₀ →
      (∀ a, (rebuild n S T).1 a ∈ valueSet (K + 4 * n) V w₀)
        ∧ ∀ a, (rebuild n S T).2 a ∈ valueSet (K + 4 * n) V w₀ := by
  intro n
  induction n with
  | zero =>
      intro K S T _ _ hS hT _ _
      exact ⟨fun a => hS a, fun a => hT a⟩
  | succ n ih =>
      intro K S T hSnn hTnn hS hT hwS hwT
      have hw₀ : (0 : ℝ) ≤ w₀ := le_trans hSnn.weight_nonneg hwS
      have hcSnn : ∀ σ : X → Prop,
          RandomSystems.Dist.NonNeg (S.filter fun s => pattern s = σ) :=
        fun σ => filter_nonNeg hSnn _
      have hcTnn : ∀ σ : X → Prop,
          RandomSystems.Dist.NonNeg (T.filter fun s => pattern s = σ) :=
        fun σ => filter_nonNeg hTnn _
      have hchSnn : ∀ (σ : X → Prop) x,
          (nodeChoice (fun S' T' => (rebuild n S' T').1)
            (S.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ)
            (S.filter fun s => pattern s = σ) x).NonNeg := fun σ x =>
        nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)).1) (hcSnn σ)
      have hchTnn : ∀ (σ : X → Prop) x,
          (nodeChoice (fun S' T' => (rebuild n S' T').2)
            (S.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ) x).NonNeg := fun σ x =>
        nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)).2) (hcTnn σ)
      have hcellS : ∀ (σ : X → Prop) (a : PFunDDS.DDS X Y),
          (S.filter fun s => pattern s = σ) a ∈ valueSet K V w₀ := by
        intro σ a
        rw [Finsupp.filter_apply]
        by_cases h : pattern a = σ
        · rw [if_pos h]; exact hS a
        · rw [if_neg h]; exact zero_mem_valueSet _ _ hw₀
      have hcellT : ∀ (σ : X → Prop) (a : PFunDDS.DDS X Y),
          (T.filter fun s => pattern s = σ) a ∈ valueSet K V w₀ := by
        intro σ a
        rw [Finsupp.filter_apply]
        by_cases h : pattern a = σ
        · rw [if_pos h]; exact hT a
        · rw [if_neg h]; exact zero_mem_valueSet _ _ hw₀
      have hwcS : ∀ σ : X → Prop,
          Dist.weight (S.filter fun s => pattern s = σ) ≤ w₀ :=
        fun σ => le_trans (weight_filter_le hSnn _) hwS
      have hwcT : ∀ σ : X → Prop,
          Dist.weight (T.filter fun s => pattern s = σ) ≤ w₀ :=
        fun σ => le_trans (weight_filter_le hTnn _) hwT
      have hchS : ∀ (σ : X → Prop) (x : X) c,
          nodeChoice (fun S' T' => (rebuild n S' T').1)
            (S.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ)
            (S.filter fun s => pattern s = σ) x c
            ∈ valueSet (K + 1 + 4 * n) V w₀ := by
        intro σ x c
        unfold nodeChoice
        refine apply_classChoiceDist_mem (fun v _ a => ?_) ?_
          (zero_mem_valueSet _ _ hw₀) c
        · exact (ih (K + 1) _ _
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)
            (branch_masses_mem hV (hcSnn σ) (hcellS σ) (hwcS σ) x (some v))
            (branch_masses_mem hV (hcTnn σ) (hcellT σ) (hwcT σ) x (some v))
            (branch_weight_le (hcSnn σ) (hwcS σ) x (some v))
            (branch_weight_le (hcTnn σ) (hwcT σ) x (some v))).1 a
        · refine mem_valueSet_of_le hV (by omega) ?_ (mem_valueSet_round hV
            (subsums_subset_boundedSums (hcSnn σ) (fun a _ => hcellS σ a)
              (hwcS σ) (subsums_filter_subset _ _
                (subsums_fTransform_subset _ _
                  (weight_mem_subsums _))))
            (branch_weight_le (hcSnn σ) (hwcS σ) x none))
            (branch_weight_le (hcSnn σ) (hwcS σ) x none)
          exact (successorTransform_nonNeg (hcSnn σ) x none).weight_nonneg
      have hchT : ∀ (σ : X → Prop) (x : X) c,
          nodeChoice (fun S' T' => (rebuild n S' T').2)
            (S.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ) x c
            ∈ valueSet (K + 1 + 4 * n) V w₀ := by
        intro σ x c
        unfold nodeChoice
        refine apply_classChoiceDist_mem (fun v _ a => ?_) ?_
          (zero_mem_valueSet _ _ hw₀) c
        · exact (ih (K + 1) _ _
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)
            (branch_masses_mem hV (hcSnn σ) (hcellS σ) (hwcS σ) x (some v))
            (branch_masses_mem hV (hcTnn σ) (hcellT σ) (hwcT σ) x (some v))
            (branch_weight_le (hcSnn σ) (hwcS σ) x (some v))
            (branch_weight_le (hcTnn σ) (hwcT σ) x (some v))).2 a
        · refine mem_valueSet_of_le hV (by omega) ?_ (mem_valueSet_round hV
            (subsums_subset_boundedSums (hcTnn σ) (fun a _ => hcellT σ a)
              (hwcT σ) (subsums_filter_subset _ _
                (subsums_fTransform_subset _ _
                  (weight_mem_subsums _))))
            (branch_weight_le (hcTnn σ) (hwcT σ) x none))
            (branch_weight_le (hcTnn σ) (hwcT σ) x none)
          exact (successorTransform_nonNeg (hcTnn σ) x none).weight_nonneg
      have hwchS : ∀ (σ : X → Prop) (x : X),
          Dist.weight (nodeChoice (fun S' T' => (rebuild n S' T').1)
            (S.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ)
            (S.filter fun s => pattern s = σ) x) ≤ w₀ := by
        intro σ x
        unfold nodeChoice
        rw [weight_classChoiceDist,
          Finset.sum_congr rfl fun v _ => (weight_rebuild n
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)).1,
          sum_weight_successorTransform _ _ _ x
            Finset.subset_union_left]
        exact hwcS σ
      have hwchT : ∀ (σ : X → Prop) (x : X),
          Dist.weight (nodeChoice (fun S' T' => (rebuild n S' T').2)
            (S.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ)
            (T.filter fun s => pattern s = σ) x) ≤ w₀ := by
        intro σ x
        unfold nodeChoice
        rw [weight_classChoiceDist,
          Finset.sum_congr rfl fun v _ => (weight_rebuild n
            (successorTransform_nonNeg (hcSnn σ) x _)
            (successorTransform_nonNeg (hcTnn σ) x _)).2,
          sum_weight_successorTransform _ _ _ x
            Finset.subset_union_right]
        exact hwcT σ
      have hwvS : ∀ σ : X → Prop,
          Dist.weight (S.filter fun s => pattern s = σ)
            ∈ valueSet (K + 1 + 4 * n + 1) V w₀ := by
        intro σ
        refine mem_valueSet_of_le hV (by omega)
          (hcSnn σ).weight_nonneg (mem_valueSet_round hV
          (subsums_subset_boundedSums (hcSnn σ)
            (fun a _ => hcellS σ a) (hwcS σ)
            (weight_mem_subsums _)) (hwcS σ)) (hwcS σ)
      have hwvT : ∀ σ : X → Prop,
          Dist.weight (T.filter fun s => pattern s = σ)
            ∈ valueSet (K + 1 + 4 * n + 1) V w₀ := by
        intro σ
        refine mem_valueSet_of_le hV (by omega)
          (hcTnn σ).weight_nonneg (mem_valueSet_round hV
          (subsums_subset_boundedSums (hcTnn σ)
            (fun a _ => hcellT σ a) (hwcT σ)
            (weight_mem_subsums _)) (hwcT σ)) (hwcT σ)
      have hdef : rebuild (n + 1) S T
          = ((S.support ∪ T.support).image pattern).sum fun σ =>
              (intervalJoint (nodeLayout
                    (fun S' T' => (rebuild n S' T').1)
                    (fun S' T' => (rebuild n S' T').2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (S.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun S' T' => (rebuild n S' T').1)
                      (fun S' T' => (rebuild n S' T').2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ))),
                intervalJoint (nodeLayoutT
                    (fun S' T' => (rebuild n S' T').1)
                    (fun S' T' => (rebuild n S' T').2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (T.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun S' T' => (rebuild n S' T').1)
                      (fun S' T' => (rebuild n S' T').2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))) := rfl
      constructor
      · intro a
        have hcap : (rebuild (n + 1) S T).1 a ≤ w₀ :=
          le_trans (apply_le_weight (rebuild_nonNeg (n + 1) S T hSnn hTnn).1 a)
            (le_trans (le_of_eq (weight_rebuild (n + 1) hSnn hTnn).1) hwS)
        have hform : (rebuild (n + 1) S T).1 a
            = ∑ σ ∈ (S.support ∪ T.support).image pattern,
                (intervalJoint (nodeLayout
                    (fun S' T' => (rebuild n S' T').1)
                    (fun S' T' => (rebuild n S' T').2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (S.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun S' T' => (rebuild n S' T').1)
                      (fun S' T' => (rebuild n S' T').2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))) a := by
          rw [hdef, Prod.fst_sum, Finsupp.finset_sum_apply]
        rw [show K + 4 * (n + 1) = K + 1 + 4 * n + 2 + 1 from by omega,
          hform]
        refine mem_valueSet_round hV
          (sum_mem_boundedSums (fun σ _ => ?_) (fun σ _ => ?_) ?_) ?_
        · exact intervalJoint_nonNeg _
            ((usOf_pairwise _ _).imp le_of_lt) a
        · exact apply_cellJoint_mem hV (hchSnn σ) (hchTnn σ)
            (hchS σ) (hchT σ) (hwchS σ)
            (hwchT σ) (hcSnn σ).weight_nonneg (hwcS σ) (hwvS σ) _ a
        · rw [← hform]; exact hcap
        · rw [← hform]; exact hcap
      · intro a
        have hcap : (rebuild (n + 1) S T).2 a ≤ w₀ :=
          le_trans (apply_le_weight (rebuild_nonNeg (n + 1) S T hSnn hTnn).2 a)
            (le_trans (le_of_eq (weight_rebuild (n + 1) hSnn hTnn).2) hwT)
        have hform : (rebuild (n + 1) S T).2 a
            = ∑ σ ∈ (S.support ∪ T.support).image pattern,
                (intervalJoint (nodeLayoutT
                    (fun S' T' => (rebuild n S' T').1)
                    (fun S' T' => (rebuild n S' T').2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (T.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun S' T' => (rebuild n S' T').1)
                      (fun S' T' => (rebuild n S' T').2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))) a := by
          rw [hdef, Prod.snd_sum, Finsupp.finset_sum_apply]
        rw [show K + 4 * (n + 1) = K + 1 + 4 * n + 2 + 1 from by omega,
          hform]
        refine mem_valueSet_round hV
          (sum_mem_boundedSums (fun σ _ => ?_) (fun σ _ => ?_) ?_) ?_
        · exact intervalJoint_nonNeg _
            ((usOf_pairwise _ _).imp le_of_lt) a
        · exact apply_cellJoint_mem hV (hchSnn σ) (hchTnn σ)
            (hchS σ) (hchT σ) (hwchS σ)
            (hwchT σ) (hcTnn σ).weight_nonneg (hwcT σ) (hwvT σ) _ a
        · rw [← hform]; exact hcap
        · rw [← hform]; exact hcap

/-! ### Equivalence of the rebuild (milestone-4 stage (iii)) -/

private theorem fTransform_const {A B : Type*} (c : B) (μ : Dist A) :
    Dist.fTransform (fun _ => c) μ = Finsupp.single c μ.weight := by
  classical
  refine Finsupp.ext fun z => ?_
  rw [Dist.fTransform_apply_eq_mass, Finsupp.single_apply]
  by_cases h : c = z
  · rw [if_pos h]
    subst h
    refine Eq.trans (Dist.mass_congr μ fun a => ?_) (Dist.mass_true μ)
    exact iff_of_true rfl trivial
  · rw [if_neg h]
    exact Dist.mass_eq_zero_of_forall_not μ fun a => h

/-- Fuel-`0` transcripts carry only the weight. -/
private theorem transcriptDist_zero (R : PFunPDS X Y)
    (e : PFunDDS.DDE X Y) :
    transcriptDist R e 0 = Finsupp.single [] R.weight := by
  show Dist.fTransform (fun _ => ([] : List (X × Option Y))) R = _
  exact fTransform_const _ R

private theorem transcript_eq_nil_of_stall {e : PFunDDS.DDE X Y}
    (he : e [] = none) (s : PFunDDS.DDS X Y) :
    ∀ m, PFunDDS.transcript s e m = [] := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [transcript_succ_stall (by rw [ih]; exact he), ih]

/-- A stalled environment sees only the weight at every fuel. -/
private theorem transcriptDist_stall {e : PFunDDS.DDE X Y}
    (he : e [] = none) (R : PFunPDS X Y) (m : ℕ) :
    transcriptDist R e m = Finsupp.single [] R.weight := by
  show Dist.fTransform _ R = _
  refine Eq.trans (fTransform_congr_of_support
    (g := fun _ => ([] : List (X × Option Y))) R
    fun s _ => transcript_eq_nil_of_stall he s m) ?_
  exact fTransform_const _ R

open Classical in
private theorem mass_ne_zero_of_mem {A : Type*} {μ : Dist A}
    (hμ : μ.NonNeg)
    {P : A → Prop} {s : A} (hs : s ∈ μ.support) (hP : P s) :
    μ.mass P ≠ 0 := by
  intro h0
  refine Finsupp.mem_support_iff.mp hs ?_
  refine le_antisymm ?_ (hμ s)
  rw [← h0]
  unfold Dist.mass
  simp only [Finsupp.sum]
  have hle : μ s = if P s then μ s else 0 := by rw [if_pos hP]
  rw [hle]
  refine Finset.single_le_sum (f := fun a => if P a then μ a else 0)
    (fun a _ => ?_) hs
  by_cases h : P a
  · simpa [h] using hμ a
  · simp [h]

open Classical in
/-- Answer-image membership is exactly nonvanishing of the successor
branch weight — so equal branch weights give equal answer images. -/
private theorem mem_image_ans_iff {R : PFunPDS X Y} (hR : R.NonNeg)
    {x : X} {y : Option Y} :
    y ∈ R.support.image (fun s =>
        PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp))
      ↔ Dist.weight (successorTransform R x y) ≠ 0 := by
  rw [weight_successorTransform]
  constructor
  · rintro hy h0
    obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hy
    exact mass_ne_zero_of_mem hR hs hans h0
  · intro hmass
    by_contra hy
    refine hmass ?_
    unfold Dist.mass
    simp only [Finsupp.sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg fun hans => hy (Finset.mem_image.mpr ⟨s, hs, hans⟩)]

open Classical in
/-- A first `Option`-answer occurs in the support image exactly when its
successor subdistribution has nonzero weight.  This is the public semantic
form used by the source-bounded attainment induction to compare answer
partitions without assuming a finite answer alphabet. -/
theorem first_answer_mem_support_image_iff_successor_weight_ne_zero
    {R : PFunPDS X Y} (hR : R.NonNeg) {x : X} {y : Option Y} :
    y ∈ R.support.image (fun s =>
        PFunDDS.output (PFunDDS.fullyDefined s) [x]
          (by rw [PFunDDS.dom_fullyDefined]; simp)) ↔
      Dist.weight (successorTransform R x y) ≠ 0 :=
  mem_image_ans_iff hR

private theorem valueAt_mem {α : Type*} (d : α) :
    ∀ (L : List (α × ℝ)) (u : ℝ),
      valueAt d L u = d ∨ ∃ e ∈ L, valueAt d L u = e.1 := by
  intro L
  induction L with
  | nil => intro u; exact Or.inl rfl
  | cons e L ih =>
      intro u
      show (if u < e.2 then e.1 else valueAt d L (u - e.2)) = d ∨ _
      by_cases h : u < e.2
      · rw [if_pos h]
        exact Or.inr ⟨e, by simp, by rw [valueAt, if_pos h]⟩
      · rw [if_neg h]
        rcases ih (u - e.2) with h' | ⟨e', he', hval⟩
        · exact Or.inl h'
        · refine Or.inr ⟨e', List.mem_cons_of_mem e he', ?_⟩
          rw [valueAt, if_neg h]
          exact hval

private theorem valueAt_lt_total {α : Type*} (d : α) :
    ∀ (L : List (α × ℝ)) (u : ℝ), 0 ≤ u → u < layoutTotal L →
      ∃ e ∈ L, e.2 ≠ 0 ∧ valueAt d L u = e.1 := by
  intro L
  induction L with
  | nil =>
      intro u hu0 hu
      rw [layoutTotal_nil] at hu
      exact absurd hu (not_lt.mpr hu0)
  | cons e L ih =>
      intro u hu0 hu
      by_cases h : u < e.2
      · refine ⟨e, by simp, ?_, ?_⟩
        · intro h0
          rw [h0] at h
          exact absurd hu0 (not_le.mpr h)
        · show (if u < e.2 then e.1 else _) = e.1
          rw [if_pos h]
      · obtain ⟨e', he', hne', hval⟩ := ih (u - e.2)
          (sub_nonneg.mpr (not_lt.mp h)) (by
          rw [layoutTotal_cons] at hu
          linarith)
        refine ⟨e', List.mem_cons_of_mem e he', hne', ?_⟩
        show (if u < e.2 then e.1 else valueAt d L (u - e.2)) = e'.1
        rw [if_neg h]
        exact hval

open Classical in
private theorem classChoiceDist_apply_none {vs : Finset Y}
    {B : Y → PFunPDS X Y} {β : ℝ} :
    classChoiceDist vs B β none = β := by
  unfold classChoiceDist
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply,
    Finset.sum_eq_zero fun v _ =>
      Dist.fTransform_apply_of_forall_ne _ _ _ fun a => by simp,
    Finsupp.single_eq_same, zero_add]

open Classical in
/-- Profile-distribution atoms are piece profiles (read at some left
endpoint of the cut list). -/
private theorem profileDist_support_subset
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ)) :
    ∀ us : List ℝ, ∀ p ∈ (profileDist Lf us).support,
      ∃ u ∈ us.dropLast, p = fun x => valueAt none (Lf x) u := by
  intro us
  induction us with
  | nil => intro p hp; simp [profileDist] at hp
  | cons u vs ih =>
      intro p hp
      cases vs with
      | nil => simp [profileDist] at hp
      | cons u' vs' =>
          rw [show profileDist Lf (u :: u' :: vs')
              = Finsupp.single (fun x => valueAt none (Lf x) u)
                  (u' - u) + profileDist Lf (u' :: vs') from rfl] at hp
          rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
          · have := Finsupp.support_single_subset h
            rw [Finset.mem_singleton] at this
            exact ⟨u, by
              rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil u' vs')]
              exact List.mem_cons_self .., this⟩
          · obtain ⟨z, hz, hzp⟩ := ih p h
            refine ⟨z, ?_, hzp⟩
            rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil u' vs')]
            exact List.mem_cons_of_mem u hz

private theorem dropLast_lt_getLast {l : List ℝ}
    (hsort : l.Pairwise (· < ·)) (hne : l ≠ []) :
    ∀ z ∈ l.dropLast, z < l.getLast hne := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a l ih =>
      intro z hz
      cases l with
      | nil => simp at hz
      | cons a' l' =>
          rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil a' l')]
            at hz
          rw [List.getLast_cons (List.cons_ne_nil a' l')]
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact (List.pairwise_cons.mp hsort).1 _
              (List.getLast_mem (List.cons_ne_nil a' l'))
          · exact ih (List.pairwise_cons.mp hsort).2
              (List.cons_ne_nil a' l') z hz'

open Classical in
/-- A cell that never answers `x` has no answered values there. -/
private theorem cellVals_eq_empty {Sc Tc : PFunPDS X Y} {x : X}
    (hcell : ∀ s ∈ Sc.support ∪ Tc.support, [x] ∉ PFunDDS.dom s) :
    cellVals Sc Tc x = ∅ := by
  unfold cellVals
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨y, hy, hvy⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  rw [output_fullyDefined_eq_none_iff.mpr (hcell s hs)] at hvy
  simp at hvy

open Classical in
/-- A cell all of whose atoms answer `x` has no `⊥`-mass there. -/
private theorem weight_successorTransform_none_eq_zero
    {Sc : PFunPDS X Y} {x : X}
    (hcell : ∀ s ∈ Sc.support, [x] ∈ PFunDDS.dom s) :
    Dist.weight (successorTransform Sc x none) = 0 := by
  rw [weight_successorTransform]
  unfold Dist.mass
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [if_neg fun hans =>
    output_fullyDefined_eq_none_iff.mp hans (hcell s hs)]

private theorem mem_commonFirstLayout {α : Type*} {os : List α}
    {A B : Dist α} {e : α × ℝ}
    (he : e ∈ commonFirstLayout os A B) :
    (∃ c ∈ os, e = (c, min (A c) (B c)))
      ∨ ∃ c ∈ os, e = (c, max (A c - B c) 0) := by
  unfold commonFirstLayout at he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨c, hc, rfl⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨c, hc, rfl⟩

open Classical in
private theorem classChoiceDist_empty {B : Y → PFunPDS X Y}
    {β : ℝ} :
    classChoiceDist ∅ B β = Finsupp.single none β := by
  unfold classChoiceDist
  rw [Finset.sum_empty, zero_add]

open Classical in
/-- Below the total, a layout of choices with no `⊥`-mass on either
side reads an answered choice. -/
private theorem valueAt_commonFirstLayout_isSome
    {os : List (Option (Y × PFunDDS.DDS X Y))}
    {A B : Dist (Option (Y × PFunDDS.DDS X Y))}
    (hA : A none = 0) (hB : B none = 0) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u < layoutTotal (commonFirstLayout os A B)) :
    (valueAt none (commonFirstLayout os A B) u).isSome = true := by
  obtain ⟨e, he, hne, hval⟩ := valueAt_lt_total none _ u hu0 hu
  rw [hval]
  rcases mem_commonFirstLayout he with ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩
  · rcases c with _ | vv
    · exact absurd (show min (A none) (B none) = 0 by
        rw [hA, hB]; exact min_self 0) hne
    · rfl
  · rcases c with _ | vv
    · exact absurd (show max (A none - B none) 0 = 0 by
        rw [hA, hB]; simp) hne
    · rfl

/-- With only `⊥`-choices in the enumeration, every position reads
`⊥`. -/
private theorem valueAt_commonFirstLayout_none {α : Type*}
    {os : List (Option α)} {A B : Dist (Option α)}
    (hos : ∀ c ∈ os, c = none) (u : ℝ) :
    valueAt none (commonFirstLayout os A B) u = none := by
  rcases valueAt_mem none (commonFirstLayout os A B) u with h
    | ⟨e, he, hval⟩
  · exact h
  · rw [hval]
    rcases mem_commonFirstLayout he with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact hos c hc
    · exact hos c hc

open Classical in
/-- E4a, S-side: cell joints are pattern-faithful — every atom of a
same-pattern cell's joint has exactly that pattern. -/
private theorem pattern_cellJoint_S
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {Sc Tc : PFunPDS X Y} {σ : X → Prop}
    (hScnn : Sc.NonNeg) (hTcnn : Tc.NonNeg)
    (hrecnnS : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      (recS S' T').NonNeg)
    (hrecnnT : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      (recT S' T').NonNeg)
    (hrecS : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      Dist.weight (recS S' T') = Dist.weight S')
    (hcS : ∀ s ∈ Sc.support, pattern s = σ)
    (hcT : ∀ s ∈ Tc.support, pattern s = σ) :
    ∀ r ∈ (intervalJoint (nodeLayout recS recT Sc Tc)
        (usOf (Dist.weight Sc)
          (nodeCutFinset recS recT Sc Tc))).support,
      pattern r = σ := by
  have hchSnn : ∀ x, (nodeChoice recS Sc Tc Sc x).NonNeg := fun x =>
    nodeChoice_nonNeg x (fun v _ => hrecnnS _ _
      (successorTransform_nonNeg hScnn x _)
      (successorTransform_nonNeg hTcnn x _)) hScnn
  have hchTnn : ∀ x, (nodeChoice recT Sc Tc Tc x).NonNeg := fun x =>
    nodeChoice_nonNeg x (fun v _ => hrecnnT _ _
      (successorTransform_nonNeg hScnn x _)
      (successorTransform_nonNeg hTcnn x _)) hTcnn
  intro r hr
  obtain ⟨p, hp, rfl⟩ :=
    Finset.mem_image.mp (Finsupp.mapDomain_support hr)
  obtain ⟨u, hu, rfl⟩ := profileDist_support_subset _ _ p hp
  have hu0 : 0 ≤ u :=
    usOf_nonneg hScnn.weight_nonneg (nodeCutFinset_nonneg hchSnn hchTnn)
      u (List.mem_of_mem_dropLast hu)
  have hult : u < Dist.weight Sc := by
    have h := dropLast_lt_getLast (usOf_pairwise _ _)
      (usOf_ne_nil _ _) u hu
    rwa [usOf_getLast hScnn.weight_nonneg] at h
  funext x'
  refine propext (Iff.trans (pattern_glueProfile id _ x') ?_)
  by_cases hσ : σ x'
  · refine iff_of_true ?_ hσ
    have hAnone : nodeChoice recS Sc Tc Sc x' none = 0 := by
      refine Eq.trans classChoiceDist_apply_none ?_
      exact weight_successorTransform_none_eq_zero fun s hs =>
        (iff_of_eq (congrFun (hcS s hs) x')).mpr hσ
    have hBnone : nodeChoice recT Sc Tc Tc x' none = 0 := by
      refine Eq.trans classChoiceDist_apply_none ?_
      exact weight_successorTransform_none_eq_zero fun s hs =>
        (iff_of_eq (congrFun (hcT s hs) x')).mpr hσ
    have htot : layoutTotal (nodeLayout recS recT Sc Tc x')
        = Dist.weight Sc :=
      layoutTotal_nodeLayout recS recT Sc Tc x' hScnn hTcnn hrecS
    exact valueAt_commonFirstLayout_isSome hAnone hBnone hu0
      (htot.symm ▸ hult)
  · refine iff_of_false ?_ hσ
    have hcells : ∀ s ∈ Sc.support ∪ Tc.support,
        [x'] ∉ PFunDDS.dom s := by
      intro s hs hdom
      rcases Finset.mem_union.mp hs with h | h
      · exact hσ ((iff_of_eq (congrFun (hcS s h) x')).mp hdom)
      · exact hσ ((iff_of_eq (congrFun (hcT s h) x')).mp hdom)
    have hCS : nodeChoice recS Sc Tc Sc x' = Finsupp.single none
        (Dist.weight (successorTransform Sc x' none)) := by
      show classChoiceDist (cellVals Sc Tc x') _ _ = _
      rw [cellVals_eq_empty hcells]
      exact classChoiceDist_empty
    have hCT : nodeChoice recT Sc Tc Tc x' = Finsupp.single none
        (Dist.weight (successorTransform Tc x' none)) := by
      show classChoiceDist (cellVals Sc Tc x') _ _ = _
      rw [cellVals_eq_empty hcells]
      exact classChoiceDist_empty
    have hos : ∀ c ∈ ((nodeChoice recS Sc Tc Sc x').support
        ∪ (nodeChoice recT Sc Tc Tc x').support).toList, c = none := by
      intro c hc
      rcases Finset.mem_union.mp (Finset.mem_toList.mp hc) with h | h
      · rw [hCS] at h
        have hmem := Finsupp.support_single_subset h
        rwa [Finset.mem_singleton] at hmem
      · rw [hCT] at h
        have hmem := Finsupp.support_single_subset h
        rwa [Finset.mem_singleton] at hmem
    intro hsome
    have hval := valueAt_commonFirstLayout_none
      (A := nodeChoice recS Sc Tc Sc x')
      (B := nodeChoice recT Sc Tc Tc x') hos u
    refine absurd ?_ (by simp :
      ¬ (none : Option (Y × PFunDDS.DDS X Y)).isSome = true)
    rw [← hval]
    exact hsome

open Classical in
/-- E4a, T-side. -/
private theorem pattern_cellJoint_T
    {recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y}
    {Sc Tc : PFunPDS X Y} {σ : X → Prop}
    (hScnn : Sc.NonNeg) (hTcnn : Tc.NonNeg)
    (hrecnnS : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      (recS S' T').NonNeg)
    (hrecnnT : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      (recT S' T').NonNeg)
    (hrecT : ∀ S' T' : PFunPDS X Y, S'.NonNeg → T'.NonNeg →
      Dist.weight (recT S' T') = Dist.weight T')
    (hcS : ∀ s ∈ Sc.support, pattern s = σ)
    (hcT : ∀ s ∈ Tc.support, pattern s = σ) :
    ∀ r ∈ (intervalJoint (nodeLayoutT recS recT Sc Tc)
        (usOf (Dist.weight Tc)
          (nodeCutFinset recS recT Sc Tc))).support,
      pattern r = σ := by
  have hchSnn : ∀ x, (nodeChoice recS Sc Tc Sc x).NonNeg := fun x =>
    nodeChoice_nonNeg x (fun v _ => hrecnnS _ _
      (successorTransform_nonNeg hScnn x _)
      (successorTransform_nonNeg hTcnn x _)) hScnn
  have hchTnn : ∀ x, (nodeChoice recT Sc Tc Tc x).NonNeg := fun x =>
    nodeChoice_nonNeg x (fun v _ => hrecnnT _ _
      (successorTransform_nonNeg hScnn x _)
      (successorTransform_nonNeg hTcnn x _)) hTcnn
  intro r hr
  obtain ⟨p, hp, rfl⟩ :=
    Finset.mem_image.mp (Finsupp.mapDomain_support hr)
  obtain ⟨u, hu, rfl⟩ := profileDist_support_subset _ _ p hp
  have hu0 : 0 ≤ u :=
    usOf_nonneg hTcnn.weight_nonneg (nodeCutFinset_nonneg hchSnn hchTnn)
      u (List.mem_of_mem_dropLast hu)
  have hult : u < Dist.weight Tc := by
    have h := dropLast_lt_getLast (usOf_pairwise _ _)
      (usOf_ne_nil _ _) u hu
    rwa [usOf_getLast hTcnn.weight_nonneg] at h
  funext x'
  refine propext (Iff.trans (pattern_glueProfile id _ x') ?_)
  by_cases hσ : σ x'
  · refine iff_of_true ?_ hσ
    have hAnone : nodeChoice recT Sc Tc Tc x' none = 0 := by
      refine Eq.trans classChoiceDist_apply_none ?_
      exact weight_successorTransform_none_eq_zero fun s hs =>
        (iff_of_eq (congrFun (hcT s hs) x')).mpr hσ
    have hBnone : nodeChoice recS Sc Tc Sc x' none = 0 := by
      refine Eq.trans classChoiceDist_apply_none ?_
      exact weight_successorTransform_none_eq_zero fun s hs =>
        (iff_of_eq (congrFun (hcS s hs) x')).mpr hσ
    have htot : layoutTotal (nodeLayoutT recS recT Sc Tc x')
        = Dist.weight Tc :=
      layoutTotal_nodeLayoutT recS recT Sc Tc x' hScnn hTcnn hrecT
    exact valueAt_commonFirstLayout_isSome hAnone hBnone hu0
      (htot.symm ▸ hult)
  · refine iff_of_false ?_ hσ
    have hcells : ∀ s ∈ Sc.support ∪ Tc.support,
        [x'] ∉ PFunDDS.dom s := by
      intro s hs hdom
      rcases Finset.mem_union.mp hs with h | h
      · exact hσ ((iff_of_eq (congrFun (hcS s h) x')).mp hdom)
      · exact hσ ((iff_of_eq (congrFun (hcT s h) x')).mp hdom)
    have hCS : nodeChoice recS Sc Tc Sc x' = Finsupp.single none
        (Dist.weight (successorTransform Sc x' none)) := by
      show classChoiceDist (cellVals Sc Tc x') _ _ = _
      rw [cellVals_eq_empty hcells]
      exact classChoiceDist_empty
    have hCT : nodeChoice recT Sc Tc Tc x' = Finsupp.single none
        (Dist.weight (successorTransform Tc x' none)) := by
      show classChoiceDist (cellVals Sc Tc x') _ _ = _
      rw [cellVals_eq_empty hcells]
      exact classChoiceDist_empty
    have hos : ∀ c ∈ ((nodeChoice recS Sc Tc Sc x').support
        ∪ (nodeChoice recT Sc Tc Tc x').support).toList, c = none := by
      intro c hc
      rcases Finset.mem_union.mp (Finset.mem_toList.mp hc) with h | h
      · rw [hCS] at h
        have hmem := Finsupp.support_single_subset h
        rwa [Finset.mem_singleton] at hmem
      · rw [hCT] at h
        have hmem := Finsupp.support_single_subset h
        rwa [Finset.mem_singleton] at hmem
    intro hsome
    have hval := valueAt_commonFirstLayout_none
      (A := nodeChoice recT Sc Tc Tc x')
      (B := nodeChoice recS Sc Tc Sc x') hos u
    refine absurd ?_ (by simp :
      ¬ (none : Option (Y × PFunDDS.DDS X Y)).isSome = true)
    rw [← hval]
    exact hsome

open Classical in
private theorem filter_eq_self_of_support {A : Type*} {μ : Dist A}
    {P : A → Prop} [DecidablePred P] (h : ∀ a ∈ μ.support, P a) :
    μ.filter P = μ := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.filter_apply]
  by_cases ha : a ∈ μ.support
  · rw [if_pos (h a ha)]
  · rw [Finsupp.notMem_support_iff.mp ha]
    exact ite_self 0

open Classical in
private theorem filter_eq_zero_of_support {A : Type*} {μ : Dist A}
    {P : A → Prop} [DecidablePred P] (h : ∀ a ∈ μ.support, ¬ P a) :
    μ.filter P = 0 := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases ha : a ∈ μ.support
  · rw [if_neg (h a ha)]
  · rw [Finsupp.notMem_support_iff.mp ha]
    exact ite_self 0

open Classical in
/-- Filtering a same-pattern cell by the `⊥`-at-`x` predicate is all
or nothing. -/
private theorem filter_cell_pattern {μ : Dist (PFunDDS.DDS X Y)}
    {σ : X → Prop} {x : X}
    (hcell : ∀ s ∈ μ.support, pattern s = σ) :
    μ.filter (fun s => [x] ∉ PFunDDS.dom s)
      = if σ x then 0 else μ := by
  by_cases hσ : σ x
  · rw [if_pos hσ]
    refine filter_eq_zero_of_support fun s hs hdom => ?_
    exact hdom ((iff_of_eq (congrFun (hcell s hs) x)).mpr hσ)
  · rw [if_neg hσ]
    refine filter_eq_self_of_support fun s hs hdom => ?_
    exact hσ ((iff_of_eq (congrFun (hcell s hs) x)).mp hdom)

open Classical in
/-- The pattern cells of a `⊥`-filtered node: unchanged for patterns
not answering `x`, empty otherwise. -/
private theorem filter_pattern_of_filter_not_dom
    {μ : Dist (PFunDDS.DDS X Y)} {σ : X → Prop} {x : X} :
    (μ.filter fun s => [x] ∉ PFunDDS.dom s).filter
        (fun s => pattern s = σ)
      = if σ x then 0
        else μ.filter fun s => pattern s = σ := by
  have hcomm : ∀ a : PFunDDS.DDS X Y,
      ((μ.filter fun s => [x] ∉ PFunDDS.dom s).filter
        fun s => pattern s = σ) a
      = if pattern a = σ ∧ [x] ∉ PFunDDS.dom a then μ a else 0 := by
    intro a
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases h1 : pattern a = σ
    · by_cases h2 : [x] ∉ PFunDDS.dom a
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2, if_neg fun h => h2 h.2]
    · rw [if_neg h1, if_neg fun h => h1 h.1]
  by_cases hσ : σ x
  · rw [if_pos hσ]
    refine Finsupp.ext fun a => ?_
    rw [hcomm a, Finsupp.coe_zero, Pi.zero_apply]
    by_cases h1 : pattern a = σ ∧ [x] ∉ PFunDDS.dom a
    · exact absurd ((iff_of_eq (congrFun h1.1 x)).mpr hσ) h1.2
    · rw [if_neg h1]
  · rw [if_neg hσ]
    refine Finsupp.ext fun a => ?_
    rw [hcomm a, Finsupp.filter_apply]
    by_cases h1 : pattern a = σ
    · rw [if_pos h1, if_pos ⟨h1, fun hdom =>
        hσ ((iff_of_eq (congrFun h1 x)).mp hdom)⟩]
    · rw [if_neg h1, if_neg fun h => h1 h.1]

open Classical in
private theorem intervalJoint_usOf_zero
    (Lf : X → List (Option (Y × PFunDDS.DDS X Y) × ℝ))
    (U : Finset ℝ) (hU : ∀ u ∈ U, 0 ≤ u) :
    intervalJoint Lf (usOf 0 U) = 0 := by
  refine eq_zero_of_weight_eq_zero
    (intervalJoint_nonNeg _ ((usOf_pairwise _ _).imp le_of_lt)) ?_
  rw [weight_intervalJoint _ _ (usOf_ne_nil _ _)
    ((usOf_pairwise _ _).imp le_of_lt), usOf_getLast (le_refl 0),
    usOf_head (le_refl 0) hU, sub_zero]

open Classical in
private theorem mem_support_filter_iff {A : Type*} {μ : Dist A}
    {P : A → Prop} [DecidablePred P] {a : A} :
    a ∈ (μ.filter P).support ↔ a ∈ μ.support ∧ P a := by
  rw [Finsupp.support_filter, Finset.mem_filter]

private theorem sum_ite_zero_eq_sum_filter_not {ι M : Type*}
    [AddCommMonoid M] (t : Finset ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → M) :
    (∑ σ ∈ t, if P σ then 0 else f σ)
      = ∑ σ ∈ t.filter fun σ => ¬ P σ, f σ := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : P σ
  · rw [if_pos h, if_neg (not_not_intro h)]
  · rw [if_neg h, if_pos h]

open Classical in
/-- E4b: the `⊥`-filter of a rebuilt node **is** the rebuild of the
`⊥`-filtered node — the self-similarity that lets the equivalence
induction recurse on filtered pairs at lower fuel. -/
private theorem filter_rebuild_succ (n : ℕ) {S T : PFunPDS X Y}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) (x : X) :
    ((rebuild (n + 1) S T).1).filter (fun r => [x] ∉ PFunDDS.dom r)
      = (rebuild (n + 1) (S.filter fun s => [x] ∉ PFunDDS.dom s)
          (T.filter fun s => [x] ∉ PFunDDS.dom s)).1 := by
  have hdefL : rebuild (n + 1) S T
      = ((S.support ∪ T.support).image pattern).sum fun σ =>
          ((intervalJoint (nodeLayout
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (S.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))),
            (intervalJoint (nodeLayoutT
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (T.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ))))) := rfl
  have hdefR : rebuild (n + 1) (S.filter fun s => [x] ∉ PFunDDS.dom s) (T.filter fun s => [x] ∉ PFunDDS.dom s)
      = (((S.filter fun s => [x] ∉ PFunDDS.dom s).support ∪ (T.filter fun s => [x] ∉ PFunDDS.dom s).support).image
          pattern).sum fun σ =>
          ((intervalJoint (nodeLayout
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                    ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                  (usOf (Dist.weight ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                      ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)))),
            (intervalJoint (nodeLayoutT
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                    ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                  (usOf (Dist.weight ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                      ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))))) := rfl
  rw [hdefL, hdefR, Prod.fst_sum, Prod.fst_sum, Finsupp.filter_sum]
  dsimp only
  refine Eq.trans (Finset.sum_congr rfl fun σ _ =>
    filter_cell_pattern (pattern_cellJoint_S
      (filter_nonNeg hSnn _) (filter_nonNeg hTnn _)
      (fun A B hA hB => (rebuild_nonNeg n A B hA hB).1)
      (fun A B hA hB => (rebuild_nonNeg n A B hA hB).2)
      (fun A B hA hB => (weight_rebuild n hA hB).1)
      (fun s hs => (mem_support_filter_iff.mp hs).2)
      (fun s hs => (mem_support_filter_iff.mp hs).2))) ?_
  rw [sum_ite_zero_eq_sum_filter_not]
  have hidx : (((S.filter fun s => [x] ∉ PFunDDS.dom s).support ∪ (T.filter fun s => [x] ∉ PFunDDS.dom s).support).image
        pattern)
      = ((S.support ∪ T.support).image pattern).filter
          fun σ => ¬ σ x := by
    ext σ
    rw [Finset.mem_filter]
    constructor
    · intro hmem'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hmem'
      rcases Finset.mem_union.mp hs with h | h
      · obtain ⟨h1, h2⟩ := mem_support_filter_iff.mp h
        exact ⟨Finset.mem_image_of_mem _
          (Finset.mem_union_left _ h1), h2⟩
      · obtain ⟨h1, h2⟩ := mem_support_filter_iff.mp h
        exact ⟨Finset.mem_image_of_mem _
          (Finset.mem_union_right _ h1), h2⟩
    · rintro ⟨hmem, hnx⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hmem
      rcases Finset.mem_union.mp hs with h | h
      · exact Finset.mem_image_of_mem _ (Finset.mem_union_left _
          (mem_support_filter_iff.mpr ⟨h, hnx⟩))
      · exact Finset.mem_image_of_mem _ (Finset.mem_union_right _
          (mem_support_filter_iff.mpr ⟨h, hnx⟩))
  rw [hidx]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hnx : ¬ σ x := (Finset.mem_filter.mp hσ).2
  have hceS : (S.filter fun s => [x] ∉ PFunDDS.dom s).filter (fun s => pattern s = σ)
      = S.filter fun s => pattern s = σ := by
    have h := filter_pattern_of_filter_not_dom (μ := S) (σ := σ)
      (x := x)
    rwa [if_neg hnx] at h
  have hceT : (T.filter fun s => [x] ∉ PFunDDS.dom s).filter (fun s => pattern s = σ)
      = T.filter fun s => pattern s = σ := by
    have h := filter_pattern_of_filter_not_dom (μ := T) (σ := σ)
      (x := x)
    rwa [if_neg hnx] at h
  rw [hceS, hceT]

open Classical in
/-- E4b: the `⊥`-filter of a rebuilt node **is** the rebuild of the
`⊥`-filtered node — the self-similarity that lets the equivalence
induction recurse (T-side) on filtered pairs at lower fuel. -/
private theorem filter_rebuild_succ_snd (n : ℕ) {S T : PFunPDS X Y}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) (x : X) :
    ((rebuild (n + 1) S T).2).filter (fun r => [x] ∉ PFunDDS.dom r)
      = (rebuild (n + 1) (S.filter fun s => [x] ∉ PFunDDS.dom s)
          (T.filter fun s => [x] ∉ PFunDDS.dom s)).2 := by
  have hdefL : rebuild (n + 1) S T
      = ((S.support ∪ T.support).image pattern).sum fun σ =>
          ((intervalJoint (nodeLayout
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (S.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))),
            (intervalJoint (nodeLayoutT
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (T.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ))))) := rfl
  have hdefR : rebuild (n + 1) (S.filter fun s => [x] ∉ PFunDDS.dom s) (T.filter fun s => [x] ∉ PFunDDS.dom s)
      = (((S.filter fun s => [x] ∉ PFunDDS.dom s).support ∪ (T.filter fun s => [x] ∉ PFunDDS.dom s).support).image
          pattern).sum fun σ =>
          ((intervalJoint (nodeLayout
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                    ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                  (usOf (Dist.weight ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                      ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)))),
            (intervalJoint (nodeLayoutT
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                    ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                  (usOf (Dist.weight ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      ((S.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ)
                      ((T.filter fun s => [x] ∉ PFunDDS.dom s).filter fun s => pattern s = σ))))) := rfl
  rw [hdefL, hdefR, Prod.snd_sum, Prod.snd_sum, Finsupp.filter_sum]
  dsimp only
  refine Eq.trans (Finset.sum_congr rfl fun σ _ =>
    filter_cell_pattern (pattern_cellJoint_T
      (filter_nonNeg hSnn _) (filter_nonNeg hTnn _)
      (fun A B hA hB => (rebuild_nonNeg n A B hA hB).1)
      (fun A B hA hB => (rebuild_nonNeg n A B hA hB).2)
      (fun A B hA hB => (weight_rebuild n hA hB).2)
      (fun s hs => (mem_support_filter_iff.mp hs).2)
      (fun s hs => (mem_support_filter_iff.mp hs).2))) ?_
  rw [sum_ite_zero_eq_sum_filter_not]
  have hidx : (((S.filter fun s => [x] ∉ PFunDDS.dom s).support ∪ (T.filter fun s => [x] ∉ PFunDDS.dom s).support).image
        pattern)
      = ((S.support ∪ T.support).image pattern).filter
          fun σ => ¬ σ x := by
    ext σ
    rw [Finset.mem_filter]
    constructor
    · intro hmem'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hmem'
      rcases Finset.mem_union.mp hs with h | h
      · obtain ⟨h1, h2⟩ := mem_support_filter_iff.mp h
        exact ⟨Finset.mem_image_of_mem _
          (Finset.mem_union_left _ h1), h2⟩
      · obtain ⟨h1, h2⟩ := mem_support_filter_iff.mp h
        exact ⟨Finset.mem_image_of_mem _
          (Finset.mem_union_right _ h1), h2⟩
    · rintro ⟨hmem, hnx⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hmem
      rcases Finset.mem_union.mp hs with h | h
      · exact Finset.mem_image_of_mem _ (Finset.mem_union_left _
          (mem_support_filter_iff.mpr ⟨h, hnx⟩))
      · exact Finset.mem_image_of_mem _ (Finset.mem_union_right _
          (mem_support_filter_iff.mpr ⟨h, hnx⟩))
  rw [hidx]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hnx : ¬ σ x := (Finset.mem_filter.mp hσ).2
  have hceS : (S.filter fun s => [x] ∉ PFunDDS.dom s).filter (fun s => pattern s = σ)
      = S.filter fun s => pattern s = σ := by
    have h := filter_pattern_of_filter_not_dom (μ := S) (σ := σ)
      (x := x)
    rwa [if_neg hnx] at h
  have hceT : (T.filter fun s => [x] ∉ PFunDDS.dom s).filter (fun s => pattern s = σ)
      = T.filter fun s => pattern s = σ := by
    have h := filter_pattern_of_filter_not_dom (μ := T) (σ := σ)
      (x := x)
    rwa [if_neg hnx] at h
  rw [hceS, hceT]

open Classical in
/-- E5's hypothesis package: for any cell pair, `rebuild_masses` at the
canonical seed discharges the cut-membership hypotheses of the R2
marginal recovery, both sides. -/
private theorem nodeCutFinset_package (n : ℕ) {Sc Tc : PFunPDS X Y}
    (hScnn : Sc.NonNeg) (hTcnn : Tc.NonNeg) :
    (∀ x : X, ∀ u ∈ layoutCuts (nodeLayout
        (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2)
        Sc Tc x),
      u ∈ nodeCutFinset (fun A B => (rebuild n A B).1)
        (fun A B => (rebuild n A B).2) Sc Tc)
    ∧ ∀ x : X, ∀ u ∈ layoutCuts (nodeLayoutT
        (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2)
        Sc Tc x),
      u ∈ nodeCutFinset (fun A B => (rebuild n A B).1)
        (fun A B => (rebuild n A B).2) Sc Tc := by
  set V₀ : Finset ℝ :=
    Sc.support.image Sc ∪ Tc.support.image Tc with hV₀
  set w₀ : ℝ := Sc.weight + Tc.weight with hw₀
  have hScm : ∀ a, Sc a ∈ valueSet 0 V₀ w₀ := by
    intro a
    by_cases ha : a ∈ Sc.support
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image_of_mem Sc ha))
    · rw [Finsupp.notMem_support_iff.mp ha]
      exact Finset.mem_insert_self 0 _
  have hTcm : ∀ a, Tc a ∈ valueSet 0 V₀ w₀ := by
    intro a
    by_cases ha : a ∈ Tc.support
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem Tc ha))
    · rw [Finsupp.notMem_support_iff.mp ha]
      exact Finset.mem_insert_self 0 _
  have hwSc : Sc.weight ≤ w₀ :=
    le_add_of_nonneg_right hTcnn.weight_nonneg
  have hwTc : Tc.weight ≤ w₀ :=
    le_add_of_nonneg_left hScnn.weight_nonneg
  have hw₀nn : (0 : ℝ) ≤ w₀ := le_trans hScnn.weight_nonneg hwSc
  have hV₀nn : ∀ v ∈ V₀, (0 : ℝ) ≤ v := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
      exact hScnn a
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
      exact hTcnn a
  have hch : (∀ x c, nodeChoice (fun A B => (rebuild n A B).1)
        Sc Tc Sc x c ∈ valueSet (1 + 4 * n) V₀ w₀)
      ∧ ∀ x c, nodeChoice (fun A B => (rebuild n A B).2)
        Sc Tc Tc x c ∈ valueSet (1 + 4 * n) V₀ w₀ := by
    constructor
    · intro x c
      unfold nodeChoice
      refine apply_classChoiceDist_mem (fun v _ a => ?_) ?_
        (zero_mem_valueSet _ _ hw₀nn) c
      · exact (rebuild_masses V₀ w₀ hV₀nn n 1 _ _
          (successorTransform_nonNeg hScnn x _)
          (successorTransform_nonNeg hTcnn x _)
          (branch_masses_mem hV₀nn hScnn hScm hwSc x (some v))
          (branch_masses_mem hV₀nn hTcnn hTcm hwTc x (some v))
          (branch_weight_le hScnn hwSc x (some v))
          (branch_weight_le hTcnn hwTc x (some v))).1 a
      · refine mem_valueSet_of_le hV₀nn (by omega)
          (successorTransform_nonNeg hScnn x none).weight_nonneg
          (mem_valueSet_round hV₀nn
          (subsums_subset_boundedSums hScnn (fun a _ => hScm a) hwSc
            (subsums_filter_subset _ _ (subsums_fTransform_subset _ _
              (weight_mem_subsums _))))
          (branch_weight_le hScnn hwSc x none))
          (branch_weight_le hScnn hwSc x none)
    · intro x c
      unfold nodeChoice
      refine apply_classChoiceDist_mem (fun v _ a => ?_) ?_
        (zero_mem_valueSet _ _ hw₀nn) c
      · exact (rebuild_masses V₀ w₀ hV₀nn n 1 _ _
          (successorTransform_nonNeg hScnn x _)
          (successorTransform_nonNeg hTcnn x _)
          (branch_masses_mem hV₀nn hScnn hScm hwSc x (some v))
          (branch_masses_mem hV₀nn hTcnn hTcm hwTc x (some v))
          (branch_weight_le hScnn hwSc x (some v))
          (branch_weight_le hTcnn hwTc x (some v))).2 a
      · refine mem_valueSet_of_le hV₀nn (by omega)
          (successorTransform_nonNeg hTcnn x none).weight_nonneg
          (mem_valueSet_round hV₀nn
          (subsums_subset_boundedSums hTcnn (fun a _ => hTcm a) hwTc
            (subsums_filter_subset _ _ (subsums_fTransform_subset _ _
              (weight_mem_subsums _))))
          (branch_weight_le hTcnn hwTc x none))
          (branch_weight_le hTcnn hwTc x none)
  have hwch : (∀ x, Dist.weight (nodeChoice
        (fun A B => (rebuild n A B).1) Sc Tc Sc x) ≤ w₀)
      ∧ ∀ x, Dist.weight (nodeChoice
        (fun A B => (rebuild n A B).2) Sc Tc Tc x) ≤ w₀ := by
    constructor
    · intro x
      unfold nodeChoice
      rw [weight_classChoiceDist,
        Finset.sum_congr rfl fun v _ => (weight_rebuild n
          (successorTransform_nonNeg hScnn x _)
          (successorTransform_nonNeg hTcnn x _)).1,
        sum_weight_successorTransform _ _ _ x Finset.subset_union_left]
      exact hwSc
    · intro x
      unfold nodeChoice
      rw [weight_classChoiceDist,
        Finset.sum_congr rfl fun v _ => (weight_rebuild n
          (successorTransform_nonNeg hScnn x _)
          (successorTransform_nonNeg hTcnn x _)).2,
        sum_weight_successorTransform _ _ _ x
          Finset.subset_union_right]
      exact hwTc
  have hchSnn : ∀ x, (nodeChoice (fun A B => (rebuild n A B).1)
      Sc Tc Sc x).NonNeg := fun x =>
    nodeChoice_nonNeg x (fun v _ =>
      (rebuild_nonNeg n _ _
        (successorTransform_nonNeg hScnn x _)
        (successorTransform_nonNeg hTcnn x _)).1) hScnn
  have hchTnn : ∀ x, (nodeChoice (fun A B => (rebuild n A B).2)
      Sc Tc Tc x).NonNeg := fun x =>
    nodeChoice_nonNeg x (fun v _ =>
      (rebuild_nonNeg n _ _
        (successorTransform_nonNeg hScnn x _)
        (successorTransform_nonNeg hTcnn x _)).2) hTcnn
  exact mem_nodeCutFinset hchSnn hchTnn hch.1 hch.2 hwch.1 hwch.2


open Classical in
/-- Per-node marginal recovery, T-side unanswered case: no cell value,
no marginal. -/
private theorem successorTransform_nodeJointT_of_not_mem
    (recS recT : PFunPDS X Y → PFunPDS X Y → PFunPDS X Y)
    (S T : PFunPDS X Y) (us : List ℝ) {x : X} {v : Y}
    (hne : us ≠ []) (hsort : us.Pairwise (· < ·))
    (hhead : us.head hne = 0)
    (hlast : us.getLast hne = layoutTotal (nodeLayoutT recS recT S T x))
    (hcuts : ∀ c ∈ layoutCuts (nodeLayoutT recS recT S T x), c ∈ us)
    (hLf : ∀ e ∈ nodeLayoutT recS recT S T x, 0 ≤ e.2)
    (hv : v ∉ cellVals S T x) :
    successorTransform (intervalJoint (nodeLayoutT recS recT S T) us)
      x (some v) = 0 := by
  rw [successorTransform_intervalJoint _ us v hLf hne hsort hhead hlast
      hcuts,
    show layoutDist (nodeLayoutT recS recT S T x)
        = nodeChoice recT S T T x from
      layoutDist_commonFirstLayout (Finset.nodup_toList _)
        fun a ha => Finset.mem_toList.mpr (Finset.mem_union_right _ ha)]
  exact contOf_filter_classChoiceDist_of_not_mem hv

open Classical in
/-- A cell answering `v` on neither side has no `v`-marginal. -/
private theorem successorTransform_eq_zero_of_not_mem_cellVals
    {Sc Tc μ : PFunPDS X Y} {x : X} {v : Y}
    (hv : v ∉ cellVals Sc Tc x)
    (hsub : μ.support ⊆ Sc.support ∪ Tc.support) :
    successorTransform μ x (some v) = 0 := by
  unfold successorTransform
  rw [filter_eq_zero_of_support fun s hs hout =>
    hv (mem_cellVals.mpr ⟨s, hsub hs, hout⟩)]
  exact Finsupp.mapDomain_zero

private theorem rebuild_zero_zero (n : ℕ) :
    rebuild n (0 : PFunPDS X Y) 0 = (0, 0) := by
  have h0 : RandomSystems.Dist.NonNeg (0 : PFunPDS X Y) :=
    fun _ => le_refl 0
  refine Prod.ext
    (eq_zero_of_weight_eq_zero (rebuild_nonNeg n 0 0 h0 h0).1 ?_)
    (eq_zero_of_weight_eq_zero (rebuild_nonNeg n 0 0 h0 h0).2 ?_)
  · rw [(weight_rebuild n h0 h0).1]; exact weight_zero_dist
  · rw [(weight_rebuild n h0 h0).2]; exact weight_zero_dist

open Classical in
/-- `eq_sum_filter_fiber` over any covering index set (missing fibers
are zero). -/
private theorem eq_sum_filter_fiber_of_subset {A B : Type*} (μ : Dist A)
    (g : A → B) {t : Finset B} (ht : μ.support.image g ⊆ t) :
    μ = ∑ v ∈ t, μ.filter fun a => g a = v :=
  Eq.trans (eq_sum_filter_fiber μ g)
    (Finset.sum_subset ht fun _ _ hv => filter_fiber_eq_zero hv)

open Classical in
/-- E5's per-cell marginal engine, S-side, unconditional in `v`: for a
cell value this is the R2 recovery; otherwise both sides vanish. -/
private theorem successorTransform_cellJoint_some (n : ℕ)
    {Sc Tc : PFunPDS X Y} (hScnn : Sc.NonNeg) (hTcnn : Tc.NonNeg)
    (x : X) (v : Y) :
    successorTransform
      (intervalJoint (nodeLayout (fun A B => (rebuild n A B).1)
          (fun A B => (rebuild n A B).2) Sc Tc)
        (usOf (Dist.weight Sc)
          (nodeCutFinset (fun A B => (rebuild n A B).1)
            (fun A B => (rebuild n A B).2) Sc Tc))) x (some v)
      = (rebuild n (successorTransform Sc x (some v))
          (successorTransform Tc x (some v))).1 := by
  have hlast : (usOf (Dist.weight Sc)
        (nodeCutFinset (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2) Sc Tc)).getLast
          (usOf_ne_nil _ _)
      = layoutTotal (nodeLayout (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2)
          Sc Tc x) := by
    rw [usOf_getLast hScnn.weight_nonneg]
    exact (layoutTotal_nodeLayout _ _ Sc Tc x hScnn hTcnn
      fun A B hA hB => (weight_rebuild n hA hB).1).symm
  have hcuts : ∀ c ∈ layoutCuts (nodeLayout (fun A B => (rebuild n A B).1)
        (fun A B => (rebuild n A B).2) Sc Tc x),
      c ∈ usOf (Dist.weight Sc)
        (nodeCutFinset (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2) Sc Tc) := by
    intro c hc
    refine mem_usOf ((nodeCutFinset_package n hScnn hTcnn).1 x c hc) ?_
    have hLnn' : ∀ e ∈ nodeLayout (fun A B => (rebuild n A B).1)
        (fun A B => (rebuild n A B).2) Sc Tc x, (0 : ℝ) ≤ e.2 :=
      commonFirstLayout_entry_nonneg
        (nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg hScnn x _)
            (successorTransform_nonNeg hTcnn x _)).1) hScnn)
        (nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg hScnn x _)
            (successorTransform_nonNeg hTcnn x _)).2) hTcnn)
    have h := layoutCuts_le_total hLnn' hc
    rwa [layoutTotal_nodeLayout _ _ Sc Tc x hScnn hTcnn
      fun A B hA hB => (weight_rebuild n hA hB).1] at h
  have hchSnn : ∀ x', (nodeChoice (fun A B => (rebuild n A B).1)
      Sc Tc Sc x').NonNeg := fun x' =>
    nodeChoice_nonNeg x' (fun v _ =>
      (rebuild_nonNeg n _ _
        (successorTransform_nonNeg hScnn x' _)
        (successorTransform_nonNeg hTcnn x' _)).1) hScnn
  have hchTnn : ∀ x', (nodeChoice (fun A B => (rebuild n A B).2)
      Sc Tc Tc x').NonNeg := fun x' =>
    nodeChoice_nonNeg x' (fun v _ =>
      (rebuild_nonNeg n _ _
        (successorTransform_nonNeg hScnn x' _)
        (successorTransform_nonNeg hTcnn x' _)).2) hTcnn
  have hLnn : ∀ e ∈ nodeLayout (fun A B => (rebuild n A B).1)
      (fun A B => (rebuild n A B).2) Sc Tc x, (0 : ℝ) ≤ e.2 :=
    commonFirstLayout_entry_nonneg (hchSnn x) (hchTnn x)
  by_cases hv : v ∈ cellVals Sc Tc x
  · exact successorTransform_nodeJoint_some _ _ Sc Tc _
      (usOf_ne_nil _ _) (usOf_pairwise _ _)
      (usOf_head hScnn.weight_nonneg
        (nodeCutFinset_nonneg (hchSnn) (hchTnn))) hlast
      hcuts hLnn hv
  · rw [successorTransform_nodeJoint_of_not_mem _ _ Sc Tc _
        (usOf_ne_nil _ _) (usOf_pairwise _ _)
        (usOf_head hScnn.weight_nonneg
          (nodeCutFinset_nonneg (hchSnn) (hchTnn))) hlast
        hcuts hLnn hv,
      successorTransform_eq_zero_of_not_mem_cellVals hv
        Finset.subset_union_left,
      successorTransform_eq_zero_of_not_mem_cellVals hv
        Finset.subset_union_right,
      rebuild_zero_zero]

open Classical in
/-- E5's per-cell marginal engine, T-side. -/
private theorem successorTransform_cellJointT_some (n : ℕ)
    {Sc Tc : PFunPDS X Y} (hScnn : Sc.NonNeg) (hTcnn : Tc.NonNeg)
    (x : X) (v : Y) :
    successorTransform
      (intervalJoint (nodeLayoutT (fun A B => (rebuild n A B).1)
          (fun A B => (rebuild n A B).2) Sc Tc)
        (usOf (Dist.weight Tc)
          (nodeCutFinset (fun A B => (rebuild n A B).1)
            (fun A B => (rebuild n A B).2) Sc Tc))) x (some v)
      = (rebuild n (successorTransform Sc x (some v))
          (successorTransform Tc x (some v))).2 := by
  have hlast : (usOf (Dist.weight Tc)
        (nodeCutFinset (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2) Sc Tc)).getLast
          (usOf_ne_nil _ _)
      = layoutTotal (nodeLayoutT (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2)
          Sc Tc x) := by
    rw [usOf_getLast hTcnn.weight_nonneg]
    exact (layoutTotal_nodeLayoutT _ _ Sc Tc x hScnn hTcnn
      fun A B hA hB => (weight_rebuild n hA hB).2).symm
  have hcuts : ∀ c ∈ layoutCuts (nodeLayoutT (fun A B => (rebuild n A B).1)
        (fun A B => (rebuild n A B).2) Sc Tc x),
      c ∈ usOf (Dist.weight Tc)
        (nodeCutFinset (fun A B => (rebuild n A B).1) (fun A B => (rebuild n A B).2) Sc Tc) := by
    intro c hc
    refine mem_usOf ((nodeCutFinset_package n hScnn hTcnn).2 x c hc) ?_
    have hLnn' : ∀ e ∈ nodeLayoutT (fun A B => (rebuild n A B).1)
        (fun A B => (rebuild n A B).2) Sc Tc x, (0 : ℝ) ≤ e.2 :=
      commonFirstLayout_entry_nonneg
        (nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg hScnn x _)
            (successorTransform_nonNeg hTcnn x _)).2) hTcnn)
        (nodeChoice_nonNeg x (fun v _ =>
          (rebuild_nonNeg n _ _
            (successorTransform_nonNeg hScnn x _)
            (successorTransform_nonNeg hTcnn x _)).1) hScnn)
    have h := layoutCuts_le_total hLnn' hc
    rwa [layoutTotal_nodeLayoutT _ _ Sc Tc x hScnn hTcnn
      fun A B hA hB => (weight_rebuild n hA hB).2] at h
  have hchSnn : ∀ x', (nodeChoice (fun A B => (rebuild n A B).1)
      Sc Tc Sc x').NonNeg := fun x' =>
    nodeChoice_nonNeg x' (fun v _ =>
      (rebuild_nonNeg n _ _
        (successorTransform_nonNeg hScnn x' _)
        (successorTransform_nonNeg hTcnn x' _)).1) hScnn
  have hchTnn : ∀ x', (nodeChoice (fun A B => (rebuild n A B).2)
      Sc Tc Tc x').NonNeg := fun x' =>
    nodeChoice_nonNeg x' (fun v _ =>
      (rebuild_nonNeg n _ _
        (successorTransform_nonNeg hScnn x' _)
        (successorTransform_nonNeg hTcnn x' _)).2) hTcnn
  have hLnn : ∀ e ∈ nodeLayoutT (fun A B => (rebuild n A B).1)
      (fun A B => (rebuild n A B).2) Sc Tc x, (0 : ℝ) ≤ e.2 :=
    commonFirstLayout_entry_nonneg (hchTnn x) (hchSnn x)
  by_cases hv : v ∈ cellVals Sc Tc x
  · exact successorTransform_nodeJointT_some _ _ Sc Tc _
      (usOf_ne_nil _ _) (usOf_pairwise _ _)
      (usOf_head hTcnn.weight_nonneg
        (nodeCutFinset_nonneg (hchSnn) (hchTnn))) hlast
      hcuts hLnn hv
  · rw [successorTransform_nodeJointT_of_not_mem _ _ Sc Tc _
        (usOf_ne_nil _ _) (usOf_pairwise _ _)
        (usOf_head hTcnn.weight_nonneg
          (nodeCutFinset_nonneg (hchSnn) (hchTnn))) hlast
        hcuts hLnn hv,
      successorTransform_eq_zero_of_not_mem_cellVals hv
        Finset.subset_union_left,
      successorTransform_eq_zero_of_not_mem_cellVals hv
        Finset.subset_union_right,
      rebuild_zero_zero]

open Classical in
/-- E5's summed marginal engine, S-side: the answered marginal of the
depth-`n + 1` rebuild is the pattern-cell sum of depth-`n` rebuilds of
the true branch pairs. -/
private theorem successorTransform_rebuild_some (n : ℕ)
    {S T : PFunPDS X Y} (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (x : X) (v : Y) :
    successorTransform (rebuild (n + 1) S T).1 x (some v)
      = ∑ σ ∈ (S.support ∪ T.support).image pattern,
          (rebuild n
            (successorTransform (S.filter fun s => pattern s = σ)
              x (some v))
            (successorTransform (T.filter fun s => pattern s = σ)
              x (some v))).1 := by
  have hdefL : rebuild (n + 1) S T
      = ((S.support ∪ T.support).image pattern).sum fun σ =>
          ((intervalJoint (nodeLayout
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (S.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))),
            (intervalJoint (nodeLayoutT
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (T.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ))))) := rfl
  rw [hdefL, Prod.fst_sum]
  dsimp only
  rw [successorTransform_finset_sum]
  exact Finset.sum_congr rfl fun σ _ =>
    successorTransform_cellJoint_some n
      (filter_nonNeg hSnn _) (filter_nonNeg hTnn _) x v

open Classical in
/-- E5's summed marginal engine, T-side. -/
private theorem successorTransform_rebuild_someT (n : ℕ)
    {S T : PFunPDS X Y} (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (x : X) (v : Y) :
    successorTransform (rebuild (n + 1) S T).2 x (some v)
      = ∑ σ ∈ (S.support ∪ T.support).image pattern,
          (rebuild n
            (successorTransform (S.filter fun s => pattern s = σ)
              x (some v))
            (successorTransform (T.filter fun s => pattern s = σ)
              x (some v))).2 := by
  have hdefL : rebuild (n + 1) S T
      = ((S.support ∪ T.support).image pattern).sum fun σ =>
          ((intervalJoint (nodeLayout
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (S.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ)))),
            (intervalJoint (nodeLayoutT
                    (fun A B => (rebuild n A B).1)
                    (fun A B => (rebuild n A B).2)
                    (S.filter fun s => pattern s = σ)
                    (T.filter fun s => pattern s = σ))
                  (usOf (Dist.weight (T.filter fun s => pattern s = σ))
                    (nodeCutFinset (fun A B => (rebuild n A B).1)
                      (fun A B => (rebuild n A B).2)
                      (S.filter fun s => pattern s = σ)
                      (T.filter fun s => pattern s = σ))))) := rfl
  rw [hdefL, Prod.snd_sum]
  dsimp only
  rw [successorTransform_finset_sum]
  exact Finset.sum_congr rfl fun σ _ =>
    successorTransform_cellJointT_some n
      (filter_nonNeg hSnn _) (filter_nonNeg hTnn _) x v


open Classical in
/-- **Stage (iii): the equivalence conjunct of Theorem 2.31's
attainment.**  At every fuel, both components of the rebuild are
behaviorally equivalent to their originals: every transcript
distribution at every depth agrees.  Outer induction on the rebuild
fuel (the answered branches recurse at lower fuel through the marginal
engines), inner induction on the transcript depth (the `⊥` branch
recurses at the same fuel through the filter self-similarity). -/
private theorem rebuild_equivalent :
    ∀ (n m : ℕ) (S T : PFunPDS X Y), S.NonNeg → T.NonNeg →
      ∀ e : PFunDDS.DDE X Y,
      transcriptDist (rebuild n S T).1 e m = transcriptDist S e m
        ∧ transcriptDist (rebuild n S T).2 e m
            = transcriptDist T e m := by
  intro n
  induction n with
  | zero => intro m S T _ _ e; exact ⟨rfl, rfl⟩
  | succ n ihn =>
      intro m
      induction m with
      | zero =>
          intro S T hSnn hTnn e
          constructor
          · rw [transcriptDist_zero, transcriptDist_zero,
              (weight_rebuild (n + 1) hSnn hTnn).1]
          · rw [transcriptDist_zero, transcriptDist_zero,
              (weight_rebuild (n + 1) hSnn hTnn).2]
      | succ m ihm =>
          intro S T hSnn hTnn e
          rcases he : e [] with _ | x
          · constructor
            · rw [transcriptDist_stall he, transcriptDist_stall he,
                (weight_rebuild (n + 1) hSnn hTnn).1]
            · rw [transcriptDist_stall he, transcriptDist_stall he,
                (weight_rebuild (n + 1) hSnn hTnn).2]
          · have hwy1 : ∀ y, Dist.weight
                (successorTransform (rebuild (n + 1) S T).1 x y)
                = Dist.weight (successorTransform S x y) := by
              intro y
              rcases y with _ | v
              · rw [successorTransform_none_eq_filter,
                  successorTransform_none_eq_filter,
                  filter_rebuild_succ n hSnn hTnn x,
                  (weight_rebuild (n + 1)
                    (filter_nonNeg hSnn _) (filter_nonNeg hTnn _)).1]
              · rw [successorTransform_rebuild_some n hSnn hTnn x v,
                  weight_finset_sum,
                  Finset.sum_congr rfl fun σ _ =>
                    (weight_rebuild n
                      (successorTransform_nonNeg (filter_nonNeg hSnn _) x _)
                      (successorTransform_nonNeg (filter_nonNeg hTnn _) x _)).1,
                  ← weight_finset_sum,
                  ← successorTransform_finset_sum,
                  ← eq_sum_filter_fiber_of_subset S pattern
                    (Finset.image_subset_image
                      Finset.subset_union_left)]
            have hwy2 : ∀ y, Dist.weight
                (successorTransform (rebuild (n + 1) S T).2 x y)
                = Dist.weight (successorTransform T x y) := by
              intro y
              rcases y with _ | v
              · rw [successorTransform_none_eq_filter,
                  successorTransform_none_eq_filter,
                  filter_rebuild_succ_snd n hSnn hTnn x,
                  (weight_rebuild (n + 1)
                    (filter_nonNeg hSnn _) (filter_nonNeg hTnn _)).2]
              · rw [successorTransform_rebuild_someT n hSnn hTnn x v,
                  weight_finset_sum,
                  Finset.sum_congr rfl fun σ _ =>
                    (weight_rebuild n
                      (successorTransform_nonNeg (filter_nonNeg hSnn _) x _)
                      (successorTransform_nonNeg (filter_nonNeg hTnn _) x _)).2,
                  ← weight_finset_sum,
                  ← successorTransform_finset_sum,
                  ← eq_sum_filter_fiber_of_subset T pattern
                    (Finset.image_subset_image
                      Finset.subset_union_right)]
            have himg1 : ((rebuild (n + 1) S T).1).support.image
                  (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
                    (by rw [PFunDDS.dom_fullyDefined]; simp))
                = S.support.image
                  (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
                    (by rw [PFunDDS.dom_fullyDefined]; simp)) := by
              ext y
              rw [mem_image_ans_iff (rebuild_nonNeg (n + 1) S T hSnn hTnn).1,
                mem_image_ans_iff hSnn, hwy1 y]
            have himg2 : ((rebuild (n + 1) S T).2).support.image
                  (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
                    (by rw [PFunDDS.dom_fullyDefined]; simp))
                = T.support.image
                  (fun s => PFunDDS.output (PFunDDS.fullyDefined s) [x]
                    (by rw [PFunDDS.dom_fullyDefined]; simp)) := by
              ext y
              rw [mem_image_ans_iff (rebuild_nonNeg (n + 1) S T hSnn hTnn).2,
                mem_image_ans_iff hTnn, hwy2 y]
            constructor
            · rw [transcriptDist_successor _ e he m,
                transcriptDist_successor S e he m, himg1]
              refine Finset.sum_congr rfl fun y _ => congrArg _ ?_
              rcases y with _ | v
              · rw [successorTransform_none_eq_filter,
                  successorTransform_none_eq_filter,
                  filter_rebuild_succ n hSnn hTnn x]
                exact (ihm _ _ (filter_nonNeg hSnn _) (filter_nonNeg hTnn _) _).1
              · rw [successorTransform_rebuild_some n hSnn hTnn x v,
                  transcriptDist_finset_sum,
                  Finset.sum_congr rfl fun σ _ => (ihn m _ _
                    (successorTransform_nonNeg (filter_nonNeg hSnn _) x _)
                    (successorTransform_nonNeg (filter_nonNeg hTnn _) x _) _).1,
                  ← transcriptDist_finset_sum,
                  ← successorTransform_finset_sum,
                  ← eq_sum_filter_fiber_of_subset S pattern
                    (Finset.image_subset_image
                      Finset.subset_union_left)]
            · rw [transcriptDist_successor _ e he m,
                transcriptDist_successor T e he m, himg2]
              refine Finset.sum_congr rfl fun y _ => congrArg _ ?_
              rcases y with _ | v
              · rw [successorTransform_none_eq_filter,
                  successorTransform_none_eq_filter,
                  filter_rebuild_succ_snd n hSnn hTnn x]
                exact (ihm _ _ (filter_nonNeg hSnn _) (filter_nonNeg hTnn _) _).2
              · rw [successorTransform_rebuild_someT n hSnn hTnn x v,
                  transcriptDist_finset_sum,
                  Finset.sum_congr rfl fun σ _ => (ihn m _ _
                    (successorTransform_nonNeg (filter_nonNeg hSnn _) x _)
                    (successorTransform_nonNeg (filter_nonNeg hTnn _) x _) _).2,
                  ← transcriptDist_finset_sum,
                  ← successorTransform_finset_sum,
                  ← eq_sum_filter_fiber_of_subset T pattern
                    (Finset.image_subset_image
                      Finset.subset_union_right)]

end Successor


/-! ### The distance of equivalence classes
(thesis Defs 2.27/2.28, Theorem 2.31) -/

/-- Thesis Def 2.28: the **distance** of two random systems — the
infimum statistical distance over representatives of the equivalence
classes, `Δ(S,T) := inf_{S' ∈ [S], T' ∈ [T]} δ(S', T')`.  A *static*
quantity: no distinguisher and no interaction appears.

Representatives range over **honest** (pointwise non-negative) laws: on
the `NNReal` carrier this was structural; over the signed carrier a signed
representative would break the data-processing step (`δ_fTransform_le` is
false for a signed second argument), so the non-negativity clause is part
of Def 2.28's meaning. -/
noncomputable def Δ (S T : PFunPDS X Y) : ℝ :=
  sInf {a : ℝ | ∃ S' T' : PFunPDS X Y,
    S'.NonNeg ∧ T'.NonNeg ∧
    Equivalent S' S ∧ Equivalent T' T ∧ a = (δ S' T' : ℝ)}

private lemma class_distance_values_nonempty {S T : PFunPDS X Y}
    (hS : S.NonNeg) (hT : T.NonNeg) :
    {a : ℝ | ∃ S' T' : PFunPDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' S ∧ Equivalent T' T ∧ a = (δ S' T' : ℝ)}.Nonempty :=
  ⟨(δ S T : ℝ), S, T, hS, hT, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

private lemma class_distance_values_bounded_below (S T : PFunPDS X Y) :
    BddBelow {a : ℝ | ∃ S' T' : PFunPDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' S ∧ Equivalent T' T ∧ a = (δ S' T' : ℝ)} :=
  ⟨0, by rintro a ⟨S', T', -, -, -, -, rfl⟩; exact δ_nonneg S' T'⟩

/-- Thesis Theorem 2.31, the easy direction (LanMau20's Lemma 3 step):
for any representatives the transcript transformation can only lose
statistical distance, so the advantage is dominated by the distance of
the equivalence classes. -/
theorem optimal_advantage_le_class_distance {S T : PFunPDS X Y}
    (hS : S.NonNeg) (hT : T.NonNeg) :
    Adv S T ≤ Δ S T := by
  refine le_csInf (class_distance_values_nonempty hS hT) ?_
  rintro c ⟨S', T', hS'nn, hT'nn, hS', hT', rfl⟩
  refine csSup_le ⟨_, (fun _ => none), 0, rfl⟩ ?_
  rintro a ⟨e, n, rfl⟩
  rw [← hS' e n, ← hT' e n]
  have h := δ_fTransform_le (fun s => PFunDDS.transcript s e n) S' hT'nn
  simp only [transcriptDist]
  exact_mod_cast h

/-- Equivalence forces zero advantage — the weight-safe direction of the
`ε = 0` consolidation (its converse is weight-sensitive, Def 2.4). -/
theorem adv_eq_zero_of_equivalent {S T : PFunPDS X Y}
    (h : Equivalent S T) : Adv S T = 0 := by
  unfold Adv
  have hset : {a : ℝ | ∃ (e : PFunDDS.DDE X Y) (n : ℕ),
      a = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)}
      = {(0 : ℝ)} := by
    ext a
    constructor
    · rintro ⟨e, n, rfl⟩
      rw [Set.mem_singleton_iff, h e n, δ_self]
    · rintro rfl
      exact ⟨fun _ => none, 0, by rw [h (fun _ => none) 0, δ_self]⟩
  rw [hset, csSup_singleton]

end RandomSystems.CR18
