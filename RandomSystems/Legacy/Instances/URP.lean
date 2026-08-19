/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.PDS
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Uniform Random Permutation (URP)

The uniform random permutation is the PDS that assigns equal weight
to every (X, X)-DDS whose first-query function is a bijection.

Moved into the `Legacy` tree on 2026-07-28: this is the bounded-model URP
(over `Legacy.PDS`), consumed only by `Legacy.Applications`; the live
switching development uses `Instances.URFfunEval` and the PFun-native laws.
Declaration namespace unchanged (`RandomSystems.Instances`).

For q = 1, this is the uniform distribution over all permutations X → X.
For general q, a "stateless permutation DDS" applies a fixed permutation
π to each current input, ignoring history.

## Main Definitions

* `URP` — the uniform random permutation PDS (q = 1 case)
* `isStatelessPerm` — predicate: DDS responds via a fixed permutation
* `ofPerm` — build a stateless-perm DDS from `Equiv.Perm X`
* `statelessPermEquiv` — bijection between stateless-perm DDS and `Perm X`
* `URPq` — the general-q URP: uniform over stateless-perm DDS
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Instances

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A single-query DDS is a permutation if its first-query function is bijective. -/
def DDS.isPermutation (s : DDS X X 1) : Prop :=
  Function.Bijective (s.firstQuery Nat.zero_lt_one)

instance (s : DDS X X 1) : Decidable (DDS.isPermutation s) := by
  unfold DDS.isPermutation Function.Bijective Function.Injective Function.Surjective
  exact inferInstance

/-- The Uniform Random Permutation (single-query case):
uniform distribution over all bijective DDS.

Assigns mass `1 / |{permutations}|` to each permutation and 0 to
non-permutations. -/
def URP [Fintype (DDS X X 1)] : PDS X X 1 where
  dist := by
    let perms := (Finset.univ : Finset (DDS X X 1)).filter DDS.isPermutation
    exact perms.sum (fun s => Finsupp.single s ((1 : NNReal) / perms.card))

/-! ### General-q URP -/

variable {q : ℕ}

/-- A q-query DDS is a stateless permutation if there exists a fixed
permutation `π : Equiv.Perm X` such that every response is `π` applied
to the current (last) input, ignoring history. -/
def isStatelessPerm (s : DDS X X q) : Prop :=
  ∃ π : Equiv.Perm X, ∀ (i : Fin q) (inputs : Fin (i.val + 1) → X),
    s.respond i inputs = π (inputs ⟨i, Nat.lt_succ_iff.mpr le_rfl⟩)

instance isStatelessPerm.decidable (s : DDS X X q) : Decidable (isStatelessPerm s) :=
  Classical.dec _

/-- Build a stateless-perm DDS from a permutation: at each query,
apply `π` to the current input. -/
def ofPerm (π : Equiv.Perm X) : DDS X X q where
  respond := fun i inputs => π (inputs ⟨i, Nat.lt_succ_iff.mpr le_rfl⟩)

omit [Fintype X] [DecidableEq X] in
theorem ofPerm_isStatelessPerm (π : Equiv.Perm X) :
    isStatelessPerm (ofPerm π : DDS X X q) :=
  ⟨π, fun _ _ => rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- A stateless-perm DDS equals `ofPerm π` for the witnessing permutation. -/
theorem isStatelessPerm_eq_ofPerm (s : DDS X X q) (hs : isStatelessPerm s) :
    s = ofPerm hs.choose := by
  apply DDS.ext; funext i inputs
  simp only [ofPerm]
  exact hs.choose_spec i inputs

omit [Fintype X] [DecidableEq X] in
/-- `ofPerm` is injective: distinct permutations give distinct DDS (when q > 0). -/
theorem ofPerm_injective (hq : 0 < q) :
    Function.Injective (ofPerm (X := X) (q := q)) := by
  intro π₁ π₂ h
  have := congr_arg DDS.respond h
  simp only [ofPerm] at this
  ext x
  have := congr_fun (congr_fun this ⟨0, hq⟩) (fun _ => x)
  simpa using this

/-- The equivalence between stateless-perm DDS and permutations (when q > 0). -/
def statelessPermEquiv (hq : 0 < q) :
    {s : DDS X X q // isStatelessPerm s} ≃ Equiv.Perm X where
  toFun s := s.prop.choose
  invFun π := ⟨ofPerm π, ofPerm_isStatelessPerm π⟩
  left_inv s := by
    simp only
    ext : 1
    exact (isStatelessPerm_eq_ofPerm s.val s.prop).symm
  right_inv π := by
    simp only
    have h : isStatelessPerm (ofPerm π : DDS X X q) := ofPerm_isStatelessPerm π
    exact ofPerm_injective hq (isStatelessPerm_eq_ofPerm (ofPerm π) h).symm

/-- The number of stateless-perm DDS equals `|X|!`. -/
theorem card_statelessPerm (hq : 0 < q) :
    ((Finset.univ : Finset (DDS X X q)).filter isStatelessPerm).card =
    (Fintype.card X).factorial := by
  have h1 : ((Finset.univ : Finset (DDS X X q)).filter isStatelessPerm).card =
      Fintype.card {s : DDS X X q // isStatelessPerm s} := by
    rw [← Finset.card_univ (α := {s : DDS X X q // isStatelessPerm s})]
    apply Finset.card_bij
      (fun (s : DDS X X q) (hs : s ∈ (Finset.univ.filter isStatelessPerm)) =>
        (⟨s, (Finset.mem_filter.mp hs).2⟩ : {s : DDS X X q // isStatelessPerm s}))
      (fun _ _ => Finset.mem_univ _)
      (fun s₁ _ s₂ _ h => by exact congrArg Subtype.val h)
      (fun ⟨s, hs⟩ _ => ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩)
  rw [h1, Fintype.card_congr (statelessPermEquiv hq), Fintype.card_perm]

/-- General-q URP: uniform distribution over stateless-perm DDS.

Assigns mass `1 / |X|!` to each stateless-perm DDS and 0 to others. -/
def URPq [Fintype (DDS X X q)] : PDS X X q where
  dist := by
    let perms := (Finset.univ : Finset (DDS X X q)).filter isStatelessPerm
    exact perms.sum (fun s => Finsupp.single s ((1 : NNReal) / perms.card))

end RandomSystems.Instances
