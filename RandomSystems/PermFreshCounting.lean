/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Counting

/-!
# Fresh-value counting for a pair of permutations

Lazy sampling, as a counting statement.  A pair of uniform permutations queried on a finite
set `Q` and then on one *fresh* input `x ∉ Q` behaves like this: conditioned on the values
already handed out on `Q`, the new pair of values `(π₁ x, π₂ x)` is uniform on the product of
the two unused sets.  `card_fresh_pair_refine` is that fact in the form a counting argument
wants it — no conditional probabilities, just a cardinality identity:

if the fresh-pair predicate `R` admits **exactly `m`** available witnesses whatever the
already-used sets are, then refining any restriction-invariant event `P` by `R` multiplies its
count by `m` and divides it by `(N − |Q|)²`.

The companion `canonSubset` is a canonical subset of prescribed cardinality: the *choice* is
irrelevant to every argument that only needs the count, so it is made once, here, by choice.

Both are protocol-independent, and are used by the beyond-birthday sum-of-permutations bound
(`RandomSystems.SumOfPermutationsTight`), where `R` is "the fresh pair lands in a balanced
subset of the unused product".
-/

noncomputable section

namespace RandomSystems.CR18.Counting

open Finset

/-! ## A canonical subset of prescribed cardinality -/

variable {α : Type*}

/-- A canonical `m`-element subset of `s`, for `m ≤ s.card` (and `s` itself otherwise).

Which elements get picked is deliberately unspecified: the balanced-fiber arguments this
serves depend on the *cardinality* only, so pinning down a selection rule would be noise. -/
def canonSubset (s : Finset α) (m : ℕ) : Finset α :=
  if h : m ≤ s.card then (Finset.exists_subset_card_eq h).choose else s

theorem canonSubset_subset (s : Finset α) (m : ℕ) : canonSubset s m ⊆ s := by
  unfold canonSubset
  by_cases h : m ≤ s.card
  · rw [dif_pos h]
    exact (Finset.exists_subset_card_eq h).choose_spec.1
  · rw [dif_neg h]

theorem canonSubset_card (s : Finset α) {m : ℕ} (h : m ≤ s.card) :
    (canonSubset s m).card = m := by
  unfold canonSubset
  rw [dif_pos h]
  exact (Finset.exists_subset_card_eq h).choose_spec.2

/-! ## The permutation-pair fiber over a prescribed restriction -/

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- Restrictions of a permutation to a finset are injective. -/
theorem restrict_perm_injective (Q : Finset X) (π : Equiv.Perm X) :
    Function.Injective (fun z : ↥Q => π z.1) :=
  fun _ _ hab => Subtype.ext (π.injective hab)

/-- The pair-of-permutations fiber over a prescribed pair of restrictions to `Q`.  Both
components are `card_perm_fiber_finset`, and the pair count is their product. -/
theorem card_permPair_restrict (Q : Finset X) (f g : ↥Q → X)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
        (∀ z : ↥Q, p.1 z.1 = f z) ∧ (∀ z : ↥Q, p.2 z.1 = g z))).card
      = (Fintype.card X - Q.card).factorial * (Fintype.card X - Q.card).factorial := by
  classical
  have hsplit : (Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
        (∀ z : ↥Q, p.1 z.1 = f z) ∧ (∀ z : ↥Q, p.2 z.1 = g z)))
      = (Finset.univ.filter (fun π : Equiv.Perm X => ∀ z : ↥Q, π z.1 = f z))
        ×ˢ (Finset.univ.filter (fun π : Equiv.Perm X => ∀ z : ↥Q, π z.1 = g z)) := by
    ext p
    simp [Finset.mem_product, Finset.mem_filter]
  have hf' : (Finset.univ.filter (fun π : Equiv.Perm X => ∀ z : ↥Q, π z.1 = f z)).card
      = (Fintype.card X - Q.card).factorial := by
    simpa using card_perm_fiber_finset Q ⟨f, hf⟩
  have hg' : (Finset.univ.filter (fun π : Equiv.Perm X => ∀ z : ↥Q, π z.1 = g z)).card
      = (Fintype.card X - Q.card).factorial := by
    simpa using card_perm_fiber_finset Q ⟨g, hg⟩
  rw [hsplit, Finset.card_product, hf', hg']

/-! ## The fresh-pair refinement, one fiber at a time -/

/-- The available-pair set at a state: the product of the two unused sets. -/
def availPairs (U V : Finset X) : Finset (X × X) :=
  (Finset.univ \ U) ×ˢ (Finset.univ \ V)

theorem mem_availPairs {U V : Finset X} {uv : X × X} :
    uv ∈ availPairs U V ↔ uv.1 ∉ U ∧ uv.2 ∉ V := by
  simp [availPairs, Finset.mem_product]

/-- **One fiber of the fresh-pair refinement.**  Inside the class of pairs agreeing with `p₀`
on `Q`, the fresh pair `(π₁ x, π₂ x)` ranges over the available product uniformly, so an
`R`-refinement with `m` available witnesses has count `m · ((N−|Q|−1)!)²` against the fiber's
`((N−|Q|)!)²`. -/
theorem card_fresh_pair_fiber
    (Q : Finset X) (x : X) (hx : x ∉ Q) (hkn : Q.card < Fintype.card X)
    (p₀ : Equiv.Perm X × Equiv.Perm X)
    (R : X → X → Prop) [∀ u v, Decidable (R u v)] (m : ℕ)
    (hm : ((availPairs (Q.image p₀.1) (Q.image p₀.2)).filter (fun uv => R uv.1 uv.2)).card = m) :
    (Fintype.card X - Q.card) * (Fintype.card X - Q.card) *
        ((Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
          (∀ z : ↥Q, p.1 z.1 = p₀.1 z.1) ∧ (∀ z : ↥Q, p.2 z.1 = p₀.2 z.1))).filter
            (fun p => R (p.1 x) (p.2 x))).card
      = m * (Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
          (∀ z : ↥Q, p.1 z.1 = p₀.1 z.1) ∧ (∀ z : ↥Q, p.2 z.1 = p₀.2 z.1))).card := by
  classical
  set n := Fintype.card X with hn
  set k := Q.card with hk
  set U := Q.image p₀.1 with hU
  set V := Q.image p₀.2 with hV
  set Fib : Finset (Equiv.Perm X × Equiv.Perm X) :=
    Finset.univ.filter (fun p => (∀ z : ↥Q, p.1 z.1 = p₀.1 z.1) ∧ (∀ z : ↥Q, p.2 z.1 = p₀.2 z.1))
    with hFib
  -- the fiber count
  have hFibcard : Fib.card = (n - k).factorial * (n - k).factorial :=
    card_permPair_restrict Q _ _ (restrict_perm_injective Q p₀.1) (restrict_perm_injective Q p₀.2)
  -- membership in the fiber transports the used sets and forces freshness
  have hmemU : ∀ p ∈ Fib, Q.image p.1 = U ∧ Q.image p.2 = V := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨Finset.image_congr (fun z hz => h₁ ⟨z, hz⟩),
      Finset.image_congr (fun z hz => h₂ ⟨z, hz⟩)⟩
  have hfresh : ∀ p ∈ Fib, p.1 x ∉ U ∧ p.2 x ∉ V := by
    intro p hp
    obtain ⟨hi₁, hi₂⟩ := hmemU p hp
    constructor
    · rw [← hi₁]
      intro hmem
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hmem
      exact hx (p.1.injective hzx ▸ hz)
    · rw [← hi₂]
      intro hmem
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hmem
      exact hx (p.2.injective hzx ▸ hz)
  -- the extension of the state by one fresh pair
  have hins : (insert x Q).card = k + 1 := by rw [Finset.card_insert_of_notMem hx]
  have hextend : ∀ u v : X, u ∉ U → v ∉ V →
      (Fib.filter (fun p => p.1 x = u ∧ p.2 x = v)).card
        = (n - (k + 1)).factorial * (n - (k + 1)).factorial := by
    intro u v hu hv
    set f : ↥(insert x Q) → X := fun z => if z.1 = x then u else p₀.1 z.1 with hf
    set g : ↥(insert x Q) → X := fun z => if z.1 = x then v else p₀.2 z.1 with hg
    have hfinj : Function.Injective f := by
      intro a b hab
      by_cases ha : a.1 = x
      · by_cases hb : b.1 = x
        · exact Subtype.ext (ha.trans hb.symm)
        · exfalso
          simp only [hf, if_pos ha, if_neg hb] at hab
          refine hu ?_
          rw [hU, hab]
          exact Finset.mem_image_of_mem _
            ((Finset.mem_insert.mp b.2).resolve_left hb)
      · by_cases hb : b.1 = x
        · exfalso
          simp only [hf, if_neg ha, if_pos hb] at hab
          refine hu ?_
          rw [hU, ← hab]
          exact Finset.mem_image_of_mem _
            ((Finset.mem_insert.mp a.2).resolve_left ha)
        · simp only [hf, if_neg ha, if_neg hb] at hab
          exact Subtype.ext (p₀.1.injective hab)
    have hginj : Function.Injective g := by
      intro a b hab
      by_cases ha : a.1 = x
      · by_cases hb : b.1 = x
        · exact Subtype.ext (ha.trans hb.symm)
        · exfalso
          simp only [hg, if_pos ha, if_neg hb] at hab
          refine hv ?_
          rw [hV, hab]
          exact Finset.mem_image_of_mem _
            ((Finset.mem_insert.mp b.2).resolve_left hb)
      · by_cases hb : b.1 = x
        · exfalso
          simp only [hg, if_neg ha, if_pos hb] at hab
          refine hv ?_
          rw [hV, ← hab]
          exact Finset.mem_image_of_mem _
            ((Finset.mem_insert.mp a.2).resolve_left ha)
        · simp only [hg, if_neg ha, if_neg hb] at hab
          exact Subtype.ext (p₀.2.injective hab)
    have hset : Fib.filter (fun p => p.1 x = u ∧ p.2 x = v)
        = Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
            (∀ z : ↥(insert x Q), p.1 z.1 = f z) ∧ (∀ z : ↥(insert x Q), p.2 z.1 = g z)) := by
      ext p
      simp only [hFib, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, hu', hv'⟩
        refine ⟨fun z => ?_, fun z => ?_⟩
        · rcases Finset.mem_insert.mp z.2 with hz | hz
          · simp only [hf, if_pos hz]
            rw [show p.1 z.1 = p.1 x from by rw [hz], hu']
          · simp only [hf, if_neg (show z.1 ≠ x from fun h => hx (h ▸ hz))]
            exact h₁ ⟨z.1, hz⟩
        · rcases Finset.mem_insert.mp z.2 with hz | hz
          · simp only [hg, if_pos hz]
            rw [show p.2 z.1 = p.2 x from by rw [hz], hv']
          · simp only [hg, if_neg (show z.1 ≠ x from fun h => hx (h ▸ hz))]
            exact h₂ ⟨z.1, hz⟩
      · rintro ⟨h₁, h₂⟩
        have hxmem : x ∈ insert x Q := Finset.mem_insert_self x Q
        refine ⟨⟨fun z => ?_, fun z => ?_⟩, ?_, ?_⟩
        · have := h₁ ⟨z.1, Finset.mem_insert_of_mem z.2⟩
          simpa [hf, if_neg (show z.1 ≠ x from fun h => hx (h ▸ z.2))] using this
        · have := h₂ ⟨z.1, Finset.mem_insert_of_mem z.2⟩
          simpa [hg, if_neg (show z.1 ≠ x from fun h => hx (h ▸ z.2))] using this
        · have := h₁ ⟨x, hxmem⟩
          simpa [hf] using this
        · have := h₂ ⟨x, hxmem⟩
          simpa [hg] using this
    rw [hset, card_permPair_restrict (insert x Q) f g hfinj hginj, hins]
  -- fiber the `R`-refinement over the fresh pair
  have hRcount : (Fib.filter (fun p => R (p.1 x) (p.2 x))).card
      = m * ((n - (k + 1)).factorial * (n - (k + 1)).factorial) := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : Equiv.Perm X × Equiv.Perm X => (p.1 x, p.2 x))
      (t := (Finset.univ : Finset (X × X))) (fun p _ => Finset.mem_univ _)]
    have hterm : ∀ uv : X × X,
        ((Fib.filter (fun p => R (p.1 x) (p.2 x))).filter
            (fun p => (p.1 x, p.2 x) = uv)).card
          = if uv ∈ (availPairs U V).filter (fun uv => R uv.1 uv.2)
              then (n - (k + 1)).factorial * (n - (k + 1)).factorial else 0 := by
      intro uv
      by_cases hR : R uv.1 uv.2
      · by_cases hav : uv ∈ availPairs U V
        · rw [if_pos (Finset.mem_filter.mpr ⟨hav, hR⟩)]
          have heq : (Fib.filter (fun p => R (p.1 x) (p.2 x))).filter
              (fun p => (p.1 x, p.2 x) = uv)
              = Fib.filter (fun p => p.1 x = uv.1 ∧ p.2 x = uv.2) := by
            rw [Finset.filter_filter]
            refine Finset.filter_congr ?_
            intro p _
            constructor
            · rintro ⟨_, h⟩
              exact ⟨(Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
            · rintro ⟨h₁, h₂⟩
              refine ⟨by rw [h₁, h₂]; exact hR, by rw [h₁, h₂]⟩
          rw [heq]
          exact hextend uv.1 uv.2 (mem_availPairs.mp hav).1 (mem_availPairs.mp hav).2
        · rw [if_neg (fun h => hav (Finset.mem_filter.mp h).1)]
          refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem ?_)
          intro p hp
          obtain ⟨hp₁, hp₂⟩ := Finset.mem_filter.mp hp
          have hpFib := (Finset.mem_filter.mp hp₁).1
          obtain ⟨hf₁, hf₂⟩ := hfresh p hpFib
          refine hav (mem_availPairs.mpr ?_)
          rw [← (Prod.ext_iff.mp hp₂).1, ← (Prod.ext_iff.mp hp₂).2]
          exact ⟨hf₁, hf₂⟩
      · have hnot : uv ∉ (availPairs U V).filter (fun uv => R uv.1 uv.2) :=
          fun h => hR (Finset.mem_filter.mp h).2
        rw [if_neg hnot]
        refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem ?_)
        intro p hp
        obtain ⟨hp₁, hp₂⟩ := Finset.mem_filter.mp hp
        refine hR ?_
        rw [← (Prod.ext_iff.mp hp₂).1, ← (Prod.ext_iff.mp hp₂).2]
        exact (Finset.mem_filter.mp hp₁).2
    rw [Finset.sum_congr rfl (fun uv _ => hterm uv), Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, hm]
    ring
  -- assemble: `(n−k)·(n−k)·((n−k−1)!)² = ((n−k)!)²`
  have hfac : (n - k) * (n - k - 1).factorial = (n - k).factorial := by
    obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
    rw [hj]
    simp [Nat.factorial_succ]
  have hnk1 : n - (k + 1) = n - k - 1 := by omega
  rw [hRcount, hFibcard, hnk1]
  calc (n - k) * (n - k) * (m * ((n - k - 1).factorial * (n - k - 1).factorial))
      = m * (((n - k) * (n - k - 1).factorial) * ((n - k) * (n - k - 1).factorial)) := by ring
    _ = m * ((n - k).factorial * (n - k).factorial) := by rw [hfac]

/-! ## The fresh-pair refinement -/

/-- **Lazy sampling for a pair of permutations, as a count.**

`P` is any event determined by the values of the two permutations on `Q` (`hP`).  `R` is a
predicate on the fresh pair of values, read against the two used-value sets, which has
**exactly `m`** available witnesses whatever the used sets are (`hm`).  Then

`(N − |Q|)² · #{p : P p ∧ R (fresh values of p)} = m · #{p : P p}`.

This is the only place the lazy-sampling structure of a uniform permutation is used: the
fresh values are uniform on the unused product, so refining by `R` costs the ratio
`m / (N − |Q|)²` and nothing else. -/
theorem card_fresh_pair_refine
    (Q : Finset X) (x : X) (hx : x ∉ Q)
    (P : Equiv.Perm X × Equiv.Perm X → Prop) [DecidablePred P]
    (hP : ∀ p p' : Equiv.Perm X × Equiv.Perm X,
      (∀ z ∈ Q, p.1 z = p'.1 z) → (∀ z ∈ Q, p.2 z = p'.2 z) → P p → P p')
    (R : Finset X → Finset X → X → X → Prop)
    [∀ U V u v, Decidable (R U V u v)]
    (m : ℕ)
    (hm : ∀ p : Equiv.Perm X × Equiv.Perm X,
      ((availPairs (Q.image p.1) (Q.image p.2)).filter
        (fun uv => R (Q.image p.1) (Q.image p.2) uv.1 uv.2)).card = m) :
    (Fintype.card X - Q.card) * (Fintype.card X - Q.card) *
        (Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
          P p ∧ R (Q.image p.1) (Q.image p.2) (p.1 x) (p.2 x))).card
      = m * (Finset.univ.filter P).card := by
  classical
  have hkn : Q.card < Fintype.card X := by
    have hss : Q ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr fun h => hx ?_
      rw [h]
      exact Finset.mem_univ x
    simpa using Finset.card_lt_card hss
  set ρ : Equiv.Perm X × Equiv.Perm X → (↥Q → X) × (↥Q → X) :=
    fun p => (fun z => p.1 z.1, fun z => p.2 z.1) with hρ
  have hfibsum : ∀ (A : Equiv.Perm X × Equiv.Perm X → Prop) (_ : DecidablePred A),
      (Finset.univ.filter A).card
        = ∑ σ : (↥Q → X) × (↥Q → X),
            ((Finset.univ.filter A).filter (fun p => ρ p = σ)).card :=
    fun A _ => Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (ρ p))
  rw [hfibsum _ inferInstance, hfibsum P inferInstance, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  set Fib : Finset (Equiv.Perm X × Equiv.Perm X) :=
    Finset.univ.filter (fun p => ρ p = σ) with hFib
  have hcomm : ∀ (A : Equiv.Perm X × Equiv.Perm X → Prop) (_ : DecidablePred A),
      (Finset.univ.filter A).filter (fun p => ρ p = σ) = Fib.filter A := by
    intro A _
    rw [hFib, Finset.filter_filter, Finset.filter_filter]
    exact Finset.filter_congr (fun p _ => by exact and_comm)
  rw [hcomm _ inferInstance, hcomm P inferInstance]
  rcases Finset.eq_empty_or_nonempty Fib with hemp | ⟨p₀, hp₀⟩
  · rw [hemp]
    simp
  -- everything is constant along the fiber
  have hρ₀ : ρ p₀ = σ := (Finset.mem_filter.mp hp₀).2
  have hres : ∀ p ∈ Fib, (∀ z ∈ Q, p.1 z = p₀.1 z) ∧ (∀ z ∈ Q, p.2 z = p₀.2 z) := by
    intro p hp
    have hpρ : ρ p = ρ p₀ := ((Finset.mem_filter.mp hp).2).trans hρ₀.symm
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have := congrFun (congrArg Prod.fst hpρ) ⟨z, hz⟩
      simpa [hρ] using this
    · have := congrFun (congrArg Prod.snd hpρ) ⟨z, hz⟩
      simpa [hρ] using this
  have himage : ∀ p ∈ Fib, Q.image p.1 = Q.image p₀.1 ∧ Q.image p.2 = Q.image p₀.2 := by
    intro p hp
    exact ⟨Finset.image_congr (fun z hz => (hres p hp).1 z hz),
      Finset.image_congr (fun z hz => (hres p hp).2 z hz)⟩
  have hFibeq : Fib = Finset.univ.filter (fun p : Equiv.Perm X × Equiv.Perm X =>
      (∀ z : ↥Q, p.1 z.1 = p₀.1 z.1) ∧ (∀ z : ↥Q, p.2 z.1 = p₀.2 z.1)) := by
    ext p
    simp only [hFib, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      have := hres p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      exact ⟨fun z => this.1 z.1 z.2, fun z => this.2 z.1 z.2⟩
    · rintro ⟨h₁, h₂⟩
      rw [← hρ₀]
      exact Prod.ext (funext fun z => h₁ z) (funext fun z => h₂ z)
  by_cases hP₀ : P p₀
  · have hfilterP : Fib.filter P = Fib :=
      Finset.filter_true_of_mem fun p hp =>
        hP p₀ p (fun z hz => ((hres p hp).1 z hz).symm)
          (fun z hz => ((hres p hp).2 z hz).symm) hP₀
    have hfilterPR : Fib.filter (fun p => P p ∧ R (Q.image p.1) (Q.image p.2) (p.1 x) (p.2 x))
        = Fib.filter (fun p => R (Q.image p₀.1) (Q.image p₀.2) (p.1 x) (p.2 x)) := by
      refine Finset.filter_congr fun p hp => ?_
      rw [(himage p hp).1, (himage p hp).2]
      exact ⟨fun h => h.2, fun h => ⟨hP p₀ p (fun z hz => ((hres p hp).1 z hz).symm)
        (fun z hz => ((hres p hp).2 z hz).symm) hP₀, h⟩⟩
    rw [hfilterP, hfilterPR, hFibeq]
    exact card_fresh_pair_fiber Q x hx hkn p₀ _ m (hm p₀)
  · have h₁ : Fib.filter P = ∅ :=
      Finset.filter_false_of_mem fun p hp h =>
        hP₀ (hP p p₀ (hres p hp).1 (hres p hp).2 h)
    have h₂ : Fib.filter (fun p => P p ∧ R (Q.image p.1) (Q.image p.2) (p.1 x) (p.2 x)) = ∅ :=
      Finset.filter_false_of_mem fun p hp h =>
        hP₀ (hP p p₀ (hres p hp).1 (hres p hp).2 h.1)
    rw [h₁, h₂]
    simp

end RandomSystems.CR18.Counting
