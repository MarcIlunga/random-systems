import RandomSystems.PDS

/-!
# Static compression-graph join bound for SequenceHash

After the conditional-equivalence blind reduction, the critical chaining
values are independent uniform coordinates and the directly queried roots are
fixed.  A graph join has exactly one of three witnesses:

* a critical value hits the public IV;
* two critical values coincide; or
* a critical value hits a directly queried root.

`JoinDescriptor` is built directly from these three witness spaces.  The mass
proof eliminates its nested sums without a wildcard, so changing the event's
semantic alternatives creates a new Lean proof obligation.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

universe u

variable {C : Type u}

/-- Finite union bound for real-valued nonnegative distributions.  This local
form follows the migrated `Dist.mass : Real` API and does not depend on the
older switching-lemma compatibility layer. -/
theorem mass_biUnion_le_nonNeg {A W : Type*}
    {distribution : RandomSystems.Dist A}
    (nonnegative : distribution.NonNeg) (witnesses : Finset W)
    (event : W → A → Prop) :
    distribution.mass (fun sample => ∃ witness ∈ witnesses, event witness sample) ≤
      ∑ witness ∈ witnesses, distribution.mass (event witness) := by
  classical
  induction witnesses using Finset.induction_on with
  | empty =>
      rw [Dist.mass_eq_zero_of_forall_not]
      · simp
      · simp
  | @insert witness witnesses fresh ih =>
      calc
        distribution.mass
              (fun sample => ∃ current ∈ insert witness witnesses,
                event current sample) =
            distribution.mass
              (fun sample => event witness sample ∨
                ∃ current ∈ witnesses, event current sample) := by
          apply Dist.mass_congr
          intro sample
          simp
        _ ≤ distribution.mass (event witness) +
              distribution.mass
                (fun sample => ∃ current ∈ witnesses, event current sample) :=
            Dist.mass_or_le nonnegative _ _
        _ ≤ distribution.mass (event witness) +
              ∑ current ∈ witnesses, distribution.mass (event current) := by
            gcongr
        _ = ∑ current ∈ insert witness witnesses,
              distribution.mass (event current) := by
            rw [Finset.sum_insert fresh]

/-- Strict pairs of critical-value coordinates. -/
abbrev CriticalPair (s : ℕ) :=
  { pair : Fin s × Fin s // pair.1 < pair.2 }

/-- Native witnesses for the three ways a sampled critical value can join an
existing graph component.  The right-associated sum is intentional: ordinary
`cases` produces one proof obligation per semantic witness family. -/
abbrev JoinDescriptor (roots : Finset C) (s : ℕ) :=
  Fin s ⊕ (CriticalPair s ⊕ ({ root : C // root ∈ roots } × Fin s))

/-- The elementary equality attached to a join witness. -/
def JoinDescriptor.Holds (iv : C) (roots : Finset C) (s : ℕ)
    (values : Fin s → C) : JoinDescriptor roots s → Prop
  | .inl i => values i = iv
  | .inr (.inl pair) => values pair.1.1 = values pair.1.2
  | .inr (.inr rootAndIndex) => values rootAndIndex.2 = rootAndIndex.1.1

/-- The static join event after adaptivity has been removed. -/
def StaticJoin (iv : C) (roots : Finset C) (s : ℕ)
    (values : Fin s → C) : Prop :=
  ∃ witness : JoinDescriptor roots s,
    JoinDescriptor.Holds iv roots s values witness

/-- The strict coordinate-pair space has cardinality `s choose 2`. -/
theorem card_criticalPair (s : ℕ) :
    Fintype.card (CriticalPair s) = Nat.choose s 2 := by
  classical
  let equivalence :
      { pair : Fin s × Fin s // pair.1 < pair.2 } ≃
        Sigma (fun j : Fin s => Fin j.1) :=
    { toFun := fun pair => ⟨pair.1.2, ⟨pair.1.1.1, pair.2⟩⟩
      invFun := fun pair =>
        ⟨(⟨pair.2.1, Nat.lt_trans pair.2.2 pair.1.2⟩, pair.1), pair.2.2⟩
      left_inv := by
        intro pair
        rcases pair with ⟨⟨i, j⟩, hij⟩
        simp
      right_inv := by
        intro pair
        rcases pair with ⟨j, i⟩
        simp }
  rw [Fintype.card_congr equivalence, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Fin.sum_univ_eq_sum_range (f := fun n : ℕ => n)] at ih ⊢
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
      simp [Nat.add_comm]

/-- Number of value vectors in which two distinct coordinates agree. -/
theorem card_criticalPair_eq {s : ℕ} (left right : Fin s)
    (distinct : left ≠ right) [Fintype C] [DecidableEq C] :
    ((Finset.univ : Finset (Fin s → C)).filter
        (fun values => values left = values right)).card =
      Fintype.card C ^ (s - 1) := by
  classical
  rw [← Fintype.card_subtype]
  let equivalence :
      { values : Fin s → C // values left = values right } ≃
        ({ index : Fin s // index ≠ right } → C) :=
    { toFun := fun values index => values.1 index.1
      invFun := fun values =>
        ⟨fun index =>
          if equal : index = right then values ⟨left, distinct⟩
          else values ⟨index, equal⟩, by
            dsimp only
            rw [dif_neg distinct, dif_pos rfl]⟩
      left_inv := fun values => by
        apply Subtype.ext
        funext index
        dsimp only
        by_cases equal : index = right
        · rw [dif_pos equal, equal]
          exact values.2
        · rw [dif_neg equal]
      right_inv := fun values => by
        funext index
        dsimp only
        rw [dif_neg index.2] }
  rw [Fintype.card_congr equivalence, Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_subtype_eq]

/-- Two distinct coordinates of a uniform value vector agree with probability
exactly `1 / N`, on the migrated real-mass API. -/
theorem uniform_criticalPair_mass
    [Fintype C] [DecidableEq C] [Nonempty C]
    {s : ℕ} (left right : Fin s) (distinct : left ≠ right) :
    (Dist.uniform (Fin s → C)).mass
        (fun values => values left = values right) =
      1 / (Fintype.card C : ℝ) := by
  classical
  have one_le_s : 1 ≤ s := by
    have := left.2
    omega
  rw [Dist.uniform_mass_eq_card_filter,
    card_criticalPair_eq left right distinct,
    Fintype.card_fun, Fintype.card_fin]
  have card_ne_zero : (Fintype.card C : ℝ) ≠ 0 := by
    positivity
  simp only [Nat.cast_pow]
  have power_succ :
      (Fintype.card C : ℝ) ^ s =
        (Fintype.card C : ℝ) ^ (s - 1) * Fintype.card C := by
    rw [← pow_succ, Nat.sub_add_cancel one_le_s]
  rw [power_succ]
  field_simp

/-- The witness count is the paper numerator: one IV target for each
coordinate, one target for each earlier coordinate, and one target for each
fixed loose root. -/
theorem card_joinDescriptor (roots : Finset C) (s : ℕ) :
    Fintype.card (JoinDescriptor roots s) =
      Nat.choose (s + 1) 2 + roots.card * s := by
  classical
  simp only [JoinDescriptor, Fintype.card_sum, Fintype.card_fin,
    card_criticalPair, Fintype.card_prod, Fintype.card_coe]
  rw [Nat.choose_succ_succ]
  simp [Nat.add_comm, Nat.add_left_comm]

/-- Every single join descriptor is one equality against an independent
uniform coordinate, and therefore has mass exactly `1 / N`.  The proof has
three generated branches and no catch-all branch. -/
theorem uniform_joinDescriptor_mass
    [Fintype C] [DecidableEq C] [Nonempty C]
    (iv : C) (roots : Finset C) (s : ℕ)
    (witness : JoinDescriptor roots s) :
    (Dist.uniform (Fin s → C)).mass
        (fun values => JoinDescriptor.Holds iv roots s values witness) =
      1 / (Fintype.card C : ℝ) := by
  classical
  cases witness with
  | inl index =>
      simp only [JoinDescriptor.Holds]
      simpa only [one_div] using uniform_mass_eval index iv
  | inr remaining =>
      cases remaining with
      | inl pair =>
          simp only [JoinDescriptor.Holds]
          exact uniform_criticalPair_mass pair.1.1 pair.1.2
            (ne_of_lt pair.2)
      | inr rootAndIndex =>
          simp only [JoinDescriptor.Holds]
          simpa only [one_div] using
            uniform_mass_eval rootAndIndex.2 rootAndIndex.1.1

/-- Logical exhaustiveness receipt for the join event.  Eliminating the
descriptor produces precisely the IV, live/live, and loose-root cases. -/
theorem staticJoin_cases (iv : C) (roots : Finset C) (s : ℕ)
    (values : Fin s → C) (join : StaticJoin iv roots s values) :
    (∃ index : Fin s, values index = iv) ∨
      (∃ pair : CriticalPair s, values pair.1.1 = values pair.1.2) ∨
      (∃ root ∈ roots, ∃ index : Fin s, values index = root) := by
  rcases join with ⟨witness, holds⟩
  cases witness with
  | inl index =>
      exact Or.inl ⟨index, holds⟩
  | inr remaining =>
      cases remaining with
      | inl pair =>
          exact Or.inr (Or.inl ⟨pair, holds⟩)
      | inr rootAndIndex =>
          exact Or.inr (Or.inr
            ⟨rootAndIndex.1.1, rootAndIndex.1.2,
              rootAndIndex.2, holds⟩)

/-- Exact finite union bound for a fixed loose-root set. -/
theorem uniform_staticJoin_mass_le
    [Fintype C] [DecidableEq C] [Nonempty C]
    (iv : C) (roots : Finset C) (s : ℕ) :
    (Dist.uniform (Fin s → C)).mass (StaticJoin iv roots s) ≤
      ((Nat.choose (s + 1) 2 + roots.card * s : ℕ) : ℝ) /
        (Fintype.card C : ℝ) := by
  classical
  let distribution := Dist.uniform (Fin s → C)
  have eventEquality :
      distribution.mass (StaticJoin iv roots s) =
        distribution.mass (fun values =>
          ∃ witness ∈ (Finset.univ : Finset (JoinDescriptor roots s)),
            JoinDescriptor.Holds iv roots s values witness) := by
    apply Dist.mass_congr
    intro values
    simp only [StaticJoin, Finset.mem_univ, true_and]
  rw [eventEquality]
  calc
    distribution.mass (fun values =>
          ∃ witness ∈ (Finset.univ : Finset (JoinDescriptor roots s)),
            JoinDescriptor.Holds iv roots s values witness) ≤
        ∑ witness ∈ (Finset.univ : Finset (JoinDescriptor roots s)),
          distribution.mass
            (fun values => JoinDescriptor.Holds iv roots s values witness) :=
      mass_biUnion_le_nonNeg Dist.uniform_nonNeg _ _
    _ = ∑ _witness ∈ (Finset.univ : Finset (JoinDescriptor roots s)),
          1 / (Fintype.card C : ℝ) := by
      apply Finset.sum_congr rfl
      intro witness _member
      exact uniform_joinDescriptor_mass iv roots s witness
    _ = (Fintype.card (JoinDescriptor roots s) : ℝ) /
          (Fintype.card C : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = ((Nat.choose (s + 1) 2 + roots.card * s : ℕ) : ℝ) /
          (Fintype.card C : ℝ) := by
      rw [card_joinDescriptor]

/-- Budget form of the join bound.  At most `q` fixed loose roots replace the
actual root count by `q`. -/
theorem uniform_staticJoin_mass_le_budget
    [Fintype C] [DecidableEq C] [Nonempty C]
    (iv : C) (roots : Finset C) (s q : ℕ)
    (rootBudget : roots.card ≤ q) :
    (Dist.uniform (Fin s → C)).mass (StaticJoin iv roots s) ≤
      ((Nat.choose (s + 1) 2 + q * s : ℕ) : ℝ) /
        (Fintype.card C : ℝ) := by
  refine (uniform_staticJoin_mass_le iv roots s).trans ?_
  have numeratorBound :
      Nat.choose (s + 1) 2 + roots.card * s ≤
        Nat.choose (s + 1) 2 + q * s := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right s rootBudget)
      (Nat.choose (s + 1) 2)
  gcongr

/-- Probability-capped budget form, ready for the final bad-event sum. -/
theorem uniform_staticJoin_mass_le_min
    [Fintype C] [DecidableEq C] [Nonempty C]
    (iv : C) (roots : Finset C) (s q : ℕ)
    (rootBudget : roots.card ≤ q) :
    (Dist.uniform (Fin s → C)).mass (StaticJoin iv roots s) ≤
      min 1
        (((Nat.choose (s + 1) 2 + q * s : ℕ) : ℝ) /
          (Fintype.card C : ℝ)) := by
  apply le_min
  · calc
      (Dist.uniform (Fin s → C)).mass (StaticJoin iv roots s) ≤
          (Dist.uniform (Fin s → C)).weight :=
        Dist.mass_le_weight Dist.uniform_nonNeg _
      _ = 1 := Dist.uniform_isProbDist.weight_eq
  · exact uniform_staticJoin_mass_le_budget iv roots s q rootBudget

end MDSimulator
end RandomSystemsModel
end SequenceHash
