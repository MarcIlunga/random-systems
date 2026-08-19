/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Coupling
import Mathlib.GroupTheory.Perm.Finite

/-!
# Coordinate swaps between two finite tables

The common-representative proofs for programmed random functions exchange a
coordinate of one complete table with a coordinate of another.  This module
packages that operation as an honest permutation of the product carrier.  No
algebraic structure on the table values is required.
-/

noncomputable section

namespace RandomSystems

universe u v w

variable {D : Type u} {E : Type v} {A : Type w}

/-- Exchange `left d` and `right e`, leaving every other coordinate fixed. -/
def coordinateSwap [DecidableEq D] [DecidableEq E] (d : D) (e : E) :
    Equiv.Perm ((D → A) × (E → A)) where
  toFun tables :=
    (Function.update tables.1 d (tables.2 e),
      Function.update tables.2 e (tables.1 d))
  invFun tables :=
    (Function.update tables.1 d (tables.2 e),
      Function.update tables.2 e (tables.1 d))
  left_inv tables := by
    apply Prod.ext
    · funext point
      by_cases hit : point = d <;> simp [Function.update, hit]
    · funext point
      by_cases hit : point = e <;> simp [Function.update, hit]
  right_inv tables := by
    apply Prod.ext
    · funext point
      by_cases hit : point = d <;> simp [Function.update, hit]
    · funext point
      by_cases hit : point = e <;> simp [Function.update, hit]

@[simp]
theorem coordinateSwap_fst_apply [DecidableEq D] [DecidableEq E]
    (d : D) (e : E) (tables : (D → A) × (E → A)) :
    (coordinateSwap d e tables).1 d = tables.2 e := by
  simp [coordinateSwap]

@[simp]
theorem coordinateSwap_snd_apply [DecidableEq D] [DecidableEq E]
    (d : D) (e : E) (tables : (D → A) × (E → A)) :
    (coordinateSwap d e tables).2 e = tables.1 d := by
  simp [coordinateSwap]

theorem coordinateSwap_fst_apply_of_ne [DecidableEq D] [DecidableEq E]
    (d d' : D) (e : E) (hne : d' ≠ d)
    (tables : (D → A) × (E → A)) :
    (coordinateSwap d e tables).1 d' = tables.1 d' := by
  simp [coordinateSwap, hne]

theorem coordinateSwap_snd_apply_of_ne [DecidableEq D] [DecidableEq E]
    (d : D) (e e' : E) (hne : e' ≠ e)
    (tables : (D → A) × (E → A)) :
    (coordinateSwap d e tables).2 e' = tables.2 e' := by
  simp [coordinateSwap, hne]

/-- Apply a list of coordinate exchanges in list order.  Composition of
permutations makes this a permutation even before any freshness hypotheses
are imposed. -/
def coordinateSwaps [DecidableEq D] [DecidableEq E] :
    List (D × E) → Equiv.Perm ((D → A) × (E → A))
  | [] => Equiv.refl _
  | pair :: rest =>
      (coordinateSwap pair.1 pair.2).trans (coordinateSwaps rest)

@[simp]
theorem coordinateSwaps_nil [DecidableEq D] [DecidableEq E]
    (tables : (D → A) × (E → A)) :
    coordinateSwaps ([] : List (D × E)) tables = tables := by
  rfl

@[simp]
theorem coordinateSwaps_cons [DecidableEq D] [DecidableEq E]
    (pair : D × E) (rest : List (D × E))
    (tables : (D → A) × (E → A)) :
    coordinateSwaps (pair :: rest) tables =
      coordinateSwaps rest (coordinateSwap pair.1 pair.2 tables) := by
  rfl

theorem coordinateSwaps_fst_apply_of_not_mem [DecidableEq D] [DecidableEq E]
    (pairs : List (D × E)) (d : D)
    (tables : (D → A) × (E → A))
    (fresh : d ∉ pairs.map Prod.fst) :
    (coordinateSwaps pairs tables).1 d = tables.1 d := by
  induction pairs generalizing tables with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
      simp only [List.map_cons, List.mem_cons, not_or] at fresh
      rw [coordinateSwaps_cons, inductionHypothesis _ fresh.2,
        coordinateSwap_fst_apply_of_ne pair.1 d pair.2 fresh.1]

theorem coordinateSwaps_snd_apply_of_not_mem [DecidableEq D] [DecidableEq E]
    (pairs : List (D × E)) (e : E)
    (tables : (D → A) × (E → A))
    (fresh : e ∉ pairs.map Prod.snd) :
    (coordinateSwaps pairs tables).2 e = tables.2 e := by
  induction pairs generalizing tables with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
      simp only [List.map_cons, List.mem_cons, not_or] at fresh
      rw [coordinateSwaps_cons, inductionHypothesis _ fresh.2,
        coordinateSwap_snd_apply_of_ne pair.1 pair.2 e fresh.1]

/-- At each left coordinate named exactly once, a family of disjoint swaps
reads the original value from its paired right coordinate. -/
theorem coordinateSwaps_get_fst [DecidableEq D] [DecidableEq E]
    (pairs : List (D × E))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    (sndNodup : (pairs.map Prod.snd).Nodup)
    (i : Fin pairs.length) (tables : (D → A) × (E → A)) :
    (coordinateSwaps pairs tables).1 (pairs.get i).1 =
      tables.2 (pairs.get i).2 := by
  induction pairs generalizing tables with
  | nil => exact Fin.elim0 i
  | cons pair rest inductionHypothesis =>
      rw [coordinateSwaps_cons]
      simp only [List.map_cons, List.nodup_cons] at fstNodup sndNodup
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · change
          (coordinateSwaps rest (coordinateSwap pair.1 pair.2 tables)).1 pair.1 =
            tables.2 pair.2
        rw [coordinateSwaps_fst_apply_of_not_mem rest pair.1 _ fstNodup.1,
          coordinateSwap_fst_apply]
      · change
          (coordinateSwaps rest (coordinateSwap pair.1 pair.2 tables)).1
              (rest.get j).1 = tables.2 (rest.get j).2
        rw [inductionHypothesis fstNodup.2 sndNodup.2 j]
        rw [coordinateSwap_snd_apply_of_ne]
        intro equal
        apply sndNodup.1
        rw [List.mem_map]
        exact ⟨rest.get j, List.get_mem rest j, equal⟩

/-- Symmetric coordinate equation for the right table. -/
theorem coordinateSwaps_get_snd [DecidableEq D] [DecidableEq E]
    (pairs : List (D × E))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    (sndNodup : (pairs.map Prod.snd).Nodup)
    (i : Fin pairs.length) (tables : (D → A) × (E → A)) :
    (coordinateSwaps pairs tables).2 (pairs.get i).2 =
      tables.1 (pairs.get i).1 := by
  induction pairs generalizing tables with
  | nil => exact Fin.elim0 i
  | cons pair rest inductionHypothesis =>
      rw [coordinateSwaps_cons]
      simp only [List.map_cons, List.nodup_cons] at fstNodup sndNodup
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · change
          (coordinateSwaps rest (coordinateSwap pair.1 pair.2 tables)).2 pair.2 =
            tables.1 pair.1
        rw [coordinateSwaps_snd_apply_of_not_mem rest pair.2 _ sndNodup.1,
          coordinateSwap_snd_apply]
      · change
          (coordinateSwaps rest (coordinateSwap pair.1 pair.2 tables)).2
              (rest.get j).2 = tables.1 (rest.get j).1
        rw [inductionHypothesis fstNodup.2 sndNodup.2 j]
        rw [coordinateSwap_fst_apply_of_ne]
        intro equal
        apply fstNodup.1
        rw [List.mem_map]
        exact ⟨rest.get j, List.get_mem rest j, equal⟩

/-- Membership form of `coordinateSwaps_get_fst`. -/
theorem coordinateSwaps_fst_apply_of_mem [DecidableEq D] [DecidableEq E]
    (pairs : List (D × E))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    (sndNodup : (pairs.map Prod.snd).Nodup)
    (pair : D × E) (member : pair ∈ pairs)
    (tables : (D → A) × (E → A)) :
    (coordinateSwaps pairs tables).1 pair.1 = tables.2 pair.2 := by
  obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
  rw [← equal]
  exact coordinateSwaps_get_fst pairs fstNodup sndNodup index tables

/-- Membership form of `coordinateSwaps_get_snd`. -/
theorem coordinateSwaps_snd_apply_of_mem [DecidableEq D] [DecidableEq E]
    (pairs : List (D × E))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    (sndNodup : (pairs.map Prod.snd).Nodup)
    (pair : D × E) (member : pair ∈ pairs)
    (tables : (D → A) × (E → A)) :
    (coordinateSwaps pairs tables).2 pair.2 = tables.1 pair.1 := by
  obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
  rw [← equal]
  exact coordinateSwaps_get_snd pairs fstNodup sndNodup index tables

/-! ## Partial uniform matchings

A history-dependent coupling often specifies a map only on the retained
seeds.  On a finite carrier, injectivity there is enough: the partial matching
extends to a permutation of the whole carrier, and the coupling lemma charges
only the complement of the retained set. -/

/-- Extend a map that is injective on a finite retained set to a permutation
of the ambient carrier.  Outside the retained set the extension is arbitrary;
the companion theorem below is the only property applications should use. -/
noncomputable def extendInjOnToPerm {Ω : Type*} [Fintype Ω]
    (matchSeed : Ω → Ω) (good : Ω → Prop)
    (injective : Set.InjOn matchSeed {seed | good seed}) :
    Equiv.Perm Ω := by
  classical
  let imageGood : Ω → Prop := fun target =>
    ∃ source, good source ∧ matchSeed source = target
  let restricted : {seed // good seed} → {seed // imageGood seed} :=
    fun seed => ⟨matchSeed seed.1, seed.1, seed.2, rfl⟩
  have restrictedInjective : Function.Injective restricted := by
    intro left right equal
    apply Subtype.ext
    apply injective left.2 right.2
    exact congrArg Subtype.val equal
  have restrictedSurjective : Function.Surjective restricted := by
    intro target
    obtain ⟨source, sourceGood, sourceImage⟩ := target.2
    refine ⟨⟨source, sourceGood⟩, ?_⟩
    apply Subtype.ext
    exact sourceImage
  exact (Equiv.ofBijective restricted
    ⟨restrictedInjective, restrictedSurjective⟩).extendSubtype

/-- The finite permutation extension agrees with the supplied matching on
every retained seed. -/
theorem extendInjOnToPerm_apply_of_good {Ω : Type*} [Fintype Ω]
    (matchSeed : Ω → Ω) (good : Ω → Prop)
    (injective : Set.InjOn matchSeed {seed | good seed})
    (seed : Ω) (seedGood : good seed) :
    extendInjOnToPerm matchSeed good injective seed = matchSeed seed := by
  classical
  unfold extendInjOnToPerm
  rw [Equiv.extendSubtype_apply_of_mem]
  · rfl
  · exact seedGood

/-- An injective matching on a retained subset of a finite uniform carrier
bounds the distance between two deterministic observations by the discarded
uniform mass. -/
theorem statDist_fTransform_uniform_le_compl_mass_of_injOn
    {Ω T : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype T] [Nonempty T] [DecidableEq T]
    (real ideal : Ω → T) (matchSeed : Ω → Ω) (good : Ω → Prop)
    (injective : Set.InjOn matchSeed {seed | good seed})
    (agree : ∀ seed, good seed → real seed = ideal (matchSeed seed)) :
    statDist
        (Dist.fTransform real (Dist.uniform Ω))
        (Dist.fTransform ideal (Dist.uniform Ω)) ≤
      (Dist.uniform Ω).mass (fun seed => ¬ good seed) := by
  classical
  let permutation : Equiv.Perm Ω :=
    extendInjOnToPerm matchSeed good injective
  have permutationOnGood : ∀ seed, good seed →
      permutation seed = matchSeed seed := by
    intro seed seedGood
    exact extendInjOnToPerm_apply_of_good matchSeed good injective seed seedGood
  let joint : Dist (T × T) :=
    Dist.fTransform
      (fun seed : Ω => (real seed, ideal (permutation seed)))
      (Dist.uniform Ω)
  let coupling : DistCoupling
      (Dist.fTransform real (Dist.uniform Ω))
      (Dist.fTransform ideal (Dist.uniform Ω)) :=
    { joint := joint
      nonneg := Dist.uniform_nonNeg.fTransform _
      marginal_fst := by
        unfold joint
        rw [Dist.fTransform_comp]
        rfl
      marginal_snd := by
        unfold joint
        rw [Dist.fTransform_comp]
        calc
          Dist.fTransform (ideal ∘ permutation) (Dist.uniform Ω) =
              Dist.fTransform ideal
                (Dist.fTransform permutation (Dist.uniform Ω)) := by
            rw [Dist.fTransform_comp]
          _ = Dist.fTransform ideal (Dist.uniform Ω) := by
            rw [Dist.fTransform_equiv_uniform permutation] }
  have disagreeMass : coupling.prDisagree =
      (Dist.uniform Ω).mass
        (fun seed => real seed ≠ ideal (permutation seed)) := by
    have couplingDisagreementEqMass : coupling.prDisagree =
        coupling.joint.mass (fun pair => pair.1 ≠ pair.2) := by
      rw [Dist.mass_eq_sum, DistCoupling.prDisagree, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro pair _
      by_cases different : pair.1 ≠ pair.2 <;> simp [different]
    rw [couplingDisagreementEqMass]
    unfold coupling joint
    exact Dist.mass_fTransform _ _ _
  calc
    statDist
          (Dist.fTransform real (Dist.uniform Ω))
          (Dist.fTransform ideal (Dist.uniform Ω)) ≤
        coupling.prDisagree := coupling_bound coupling
    _ = (Dist.uniform Ω).mass
          (fun seed => real seed ≠ ideal (permutation seed)) := disagreeMass
    _ ≤ (Dist.uniform Ω).mass (fun seed => ¬ good seed) := by
      apply Dist.mass_mono Dist.uniform_nonNeg
      intro seed mismatch seedGood
      apply mismatch
      rw [permutationOnGood seed seedGood]
      exact agree seed seedGood

/-- Target-oriented form of the partial uniform matching lemma.  Here the
retained seeds belong to the ideal/target carrier and `recoverSeed` maps them
back to real/source seeds.  This is useful when the bad event is simplest to
measure in the ideal experiment. -/
theorem statDist_fTransform_uniform_le_compl_mass_of_reverse_injOn
    {Ω T : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype T] [Nonempty T] [DecidableEq T]
    (real ideal : Ω → T) (recoverSeed : Ω → Ω) (good : Ω → Prop)
    (injective : Set.InjOn recoverSeed {seed | good seed})
    (agree : ∀ target, good target →
      real (recoverSeed target) = ideal target) :
    statDist
        (Dist.fTransform real (Dist.uniform Ω))
        (Dist.fTransform ideal (Dist.uniform Ω)) ≤
      (Dist.uniform Ω).mass (fun target => ¬ good target) := by
  have reverseBound :=
    statDist_fTransform_uniform_le_compl_mass_of_injOn
      ideal real recoverSeed good injective
      (fun target targetGood => (agree target targetGood).symm)
  have realProbability :
      (Dist.fTransform real (Dist.uniform Ω)).isProbDist :=
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist
  have idealProbability :
      (Dist.fTransform ideal (Dist.uniform Ω)).isProbDist :=
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist
  rw [statDist_symm_of_eq_weight
    (Dist.fTransform real (Dist.uniform Ω))
    (Dist.fTransform ideal (Dist.uniform Ω)) (by
      rw [realProbability.weight_eq, idealProbability.weight_eq])]
  exact reverseBound

end RandomSystems
