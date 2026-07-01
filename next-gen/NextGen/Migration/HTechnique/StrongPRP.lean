/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.FunctionEvaluator
import NextGen.Migration.HTechnique.SecurityDefs

/-!
# Strong and tweakable PRP law-level models

This module replaces the old H-technique strong/tweakable PRP scaffold with
concrete CR18 law-level systems.  The old source `advSPRP` accepted both the
real system and the ideal system as free inputs.  That is not the migrated
shape: the ideal must be constructed from the message space, as a sampled
permutation viewed through `PFunDDS.functionEvaluator`.

The definitions here are model objects, not proof shortcuts:

* `QueryDir` is the forward/inverse query tag;
* `strongPermFunction` turns one permutation into a two-sided oracle;
* `forwardOnly` is the Def. 3.6 forward-only transcript representation used to
  reduce two-sided permutation constraints to ordinary permutation constraints;
* `strongURP` samples a uniform permutation and embeds that oracle as a
  law-level CR18 PDS;
* `tweakableURP` and `tweakableStrongURP` sample an independent permutation per
  tweak;
* `advSPRP`, `advTPRP`, and `advTSPRP` are source-facing advantage names whose
  ideals are constructed internally.
-/

noncomputable section

open scoped RandomSystems.CR18

namespace NextGen
namespace Migration
namespace HTechnique

universe u v

/-- Source model object: query direction for a strong permutation oracle. -/
inductive QueryDir where
  | fwd : QueryDir
  | inv : QueryDir
  deriving DecidableEq, Inhabited

instance : Fintype QueryDir :=
  ⟨{QueryDir.fwd, QueryDir.inv}, by
    intro d
    cases d <;> simp⟩

/-- Source model object: a permutation viewed as a two-sided oracle. -/
def strongPermFunction {X : Type u} (π : Equiv.Perm X) : QueryDir × X → X :=
  fun q =>
    match q.1 with
    | QueryDir.fwd => π q.2
    | QueryDir.inv => π.symm q.2

/-- Source model object: forward-only representation of a single strong
permutation query (Jha-Nandi Def. 3.6).  A forward query records `(x,y)`, while
an inverse query records the equivalent forward constraint `(y,x)`. -/
def forwardOnly {X : Type u} (δ : QueryDir) (x y : X) : X × X :=
  match δ with
  | QueryDir.fwd => (x, y)
  | QueryDir.inv => (y, x)

/-- Source model object: forward-only representation of a full strong
permutation transcript. -/
def forwardOnlyTranscript {X : Type u} {q : Nat}
    (δs : Fin q → QueryDir) (xs ys : Fin q → X) : Fin q → X × X :=
  fun i => forwardOnly (δs i) (xs i) (ys i)

/-- Source model object: a tweak-indexed permutation family viewed as a
forward-only tweakable permutation oracle. -/
def tweakablePermFunction {T : Type u} {X : Type v}
    (π : T → Equiv.Perm X) : T × X → X :=
  fun q => (π q.1) q.2

/-- Source model object: a tweak-indexed permutation family viewed as a
two-sided tweakable permutation oracle. -/
def tweakableStrongPermFunction {T : Type u} {X : Type v}
    (π : T → Equiv.Perm X) : QueryDir × T × X → X :=
  fun q =>
    match q.1 with
    | QueryDir.fwd => (π q.2.1) q.2.2
    | QueryDir.inv => (π q.2.1).symm q.2.2

/-- Support predicate for two-sided oracle consistency. -/
def StrongPermConsistent {X : Type u} (f : QueryDir × X → X) : Prop :=
  (∀ x : X, f (QueryDir.inv, f (QueryDir.fwd, x)) = x) ∧
    (∀ x : X, f (QueryDir.fwd, f (QueryDir.inv, x)) = x)

/-- Support predicate for per-tweak two-sided oracle consistency. -/
def TweakableStrongPermConsistent {T : Type u} {X : Type v}
    (f : QueryDir × T × X → X) : Prop :=
  (∀ (t : T) (x : X), f (QueryDir.inv, t, f (QueryDir.fwd, t, x)) = x) ∧
    (∀ (t : T) (x : X), f (QueryDir.fwd, t, f (QueryDir.inv, t, x)) = x)

@[simp]
theorem strongPermFunction_fwd {X : Type u} (π : Equiv.Perm X) (x : X) :
    strongPermFunction π (QueryDir.fwd, x) = π x :=
  rfl

@[simp]
theorem strongPermFunction_inv {X : Type u} (π : Equiv.Perm X) (x : X) :
    strongPermFunction π (QueryDir.inv, x) = π.symm x :=
  rfl

@[simp]
theorem forwardOnly_fwd {X : Type u} (x y : X) :
    forwardOnly QueryDir.fwd x y = (x, y) :=
  rfl

@[simp]
theorem forwardOnly_inv {X : Type u} (x y : X) :
    forwardOnly QueryDir.inv x y = (y, x) :=
  rfl

@[simp]
theorem forwardOnly_involutive {X : Type u} (δ : QueryDir) (x y : X) :
    let p := forwardOnly δ x y
    forwardOnly δ p.1 p.2 = (x, y) := by
  cases δ <;> simp [forwardOnly]

/-- Source model fact: a two-sided permutation query is equivalent to the
ordinary forward constraint induced by `forwardOnly` (Jha-Nandi Eq. 7). -/
theorem forwardOnly_perm_iff {X : Type u}
    (π : Equiv.Perm X) (δ : QueryDir) (x y : X) :
    (match δ with
     | QueryDir.fwd => π x = y
     | QueryDir.inv => π.symm x = y) ↔
    π (forwardOnly δ x y).1 = (forwardOnly δ x y).2 := by
  cases δ
  · simp [forwardOnly]
  · simp only [forwardOnly]
    constructor
    · rintro rfl
      exact π.apply_symm_apply x
    · intro h
      rw [← h]
      exact π.symm_apply_apply y

/-- Source model fact: `strongPermFunction` satisfies a query exactly when the
underlying permutation satisfies the corresponding forward-only constraint. -/
theorem strongPermFunction_eq_iff {X : Type u}
    (π : Equiv.Perm X) (δ : QueryDir) (x y : X) :
    strongPermFunction π (δ, x) = y ↔
      π (forwardOnly δ x y).1 = (forwardOnly δ x y).2 := by
  cases δ
  · simp [strongPermFunction]
  · simpa [strongPermFunction] using forwardOnly_perm_iff π QueryDir.inv x y

@[simp]
theorem tweakablePermFunction_apply {T : Type u} {X : Type v}
    (π : T → Equiv.Perm X) (t : T) (x : X) :
    tweakablePermFunction π (t, x) = (π t) x :=
  rfl

@[simp]
theorem tweakableStrongPermFunction_fwd {T : Type u} {X : Type v}
    (π : T → Equiv.Perm X) (t : T) (x : X) :
    tweakableStrongPermFunction π (QueryDir.fwd, t, x) = (π t) x :=
  rfl

@[simp]
theorem tweakableStrongPermFunction_inv {T : Type u} {X : Type v}
    (π : T → Equiv.Perm X) (t : T) (x : X) :
    tweakableStrongPermFunction π (QueryDir.inv, t, x) = (π t).symm x :=
  rfl

/-- Source model fact: every oracle obtained from a permutation is two-sided
consistent. -/
theorem strongPermFunction_consistent {X : Type u} (π : Equiv.Perm X) :
    StrongPermConsistent (strongPermFunction π) := by
  constructor <;> intro x <;> simp [strongPermFunction]

/-- Source model fact: every oracle obtained from tweak-indexed permutations is
per-tweak two-sided consistent. -/
theorem tweakableStrongPermFunction_consistent {T : Type u} {X : Type v}
    (π : T → Equiv.Perm X) :
    TweakableStrongPermConsistent (tweakableStrongPermFunction π) := by
  constructor <;> intro t x <;> simp [tweakableStrongPermFunction]

/-- Source model object: ideal strong random permutation, as a law-level CR18
PDS over forward/inverse queries. -/
noncomputable def strongURP {X : Type u} [Fintype X] [DecidableEq X] :
    ProbPDS (QueryDir × X) X :=
  RandomSystems.CR18.PFunPDS.Prob.functionEvaluator
    (⟨RandomSystems.Dist.uniform (Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : Equiv.Perm X => strongPermFunction π)

/-- Source model object: ideal tweakable random permutation, as a law-level CR18
PDS over `(tweak, input)` queries. -/
noncomputable def tweakableURP {T : Type u} {X : Type v}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X] :
    ProbPDS (T × X) X :=
  RandomSystems.CR18.PFunPDS.Prob.functionEvaluator
    (⟨RandomSystems.Dist.uniform (T → Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : T → Equiv.Perm X => tweakablePermFunction π)

/-- Source model object: ideal tweakable strong random permutation, as a
law-level CR18 PDS over `(direction, tweak, input)` queries. -/
noncomputable def tweakableStrongURP {T : Type u} {X : Type v}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X] :
    ProbPDS (QueryDir × T × X) X :=
  RandomSystems.CR18.PFunPDS.Prob.functionEvaluator
    (⟨RandomSystems.Dist.uniform (T → Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : T → Equiv.Perm X => tweakableStrongPermFunction π)

/-- Support fact: the ideal strong random permutation is q-step-total. -/
theorem strongURP_KStepTotal {X : Type u} [Fintype X] [DecidableEq X] (q : Nat) :
    (strongURP (X := X)).KStepTotal q := by
  exact RandomSystems.CR18.functionEvaluatorProb_KStepTotal
    (⟨RandomSystems.Dist.uniform (Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : Equiv.Perm X => strongPermFunction π)
    q

/-- Support fact: the ideal tweakable random permutation is q-step-total. -/
theorem tweakableURP_KStepTotal {T : Type u} {X : Type v}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X] (q : Nat) :
    (tweakableURP (T := T) (X := X)).KStepTotal q := by
  exact RandomSystems.CR18.functionEvaluatorProb_KStepTotal
    (⟨RandomSystems.Dist.uniform (T → Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : T → Equiv.Perm X => tweakablePermFunction π)
    q

/-- Support fact: the ideal tweakable strong random permutation is q-step-total. -/
theorem tweakableStrongURP_KStepTotal {T : Type u} {X : Type v}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X] (q : Nat) :
    (tweakableStrongURP (T := T) (X := X)).KStepTotal q := by
  exact RandomSystems.CR18.functionEvaluatorProb_KStepTotal
    (⟨RandomSystems.Dist.uniform (T → Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : T → Equiv.Perm X => tweakableStrongPermFunction π)
    q

/-- Support fact: the ideal strong random permutation is total on every
nonempty input history in its support. -/
theorem strongURP_totalOnNonempty {X : Type u} [Fintype X] [DecidableEq X] :
    RandomSystems.CR18.CondEquiv.TotalOnNonempty
      (strongURP (X := X)).val := by
  exact RandomSystems.CR18.functionEvaluatorProb_totalOnNonempty
    (⟨RandomSystems.Dist.uniform (Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : Equiv.Perm X => strongPermFunction π)

/-- Support fact: the ideal tweakable random permutation is total on every
nonempty input history in its support. -/
theorem tweakableURP_totalOnNonempty {T : Type u} {X : Type v}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X] :
    RandomSystems.CR18.CondEquiv.TotalOnNonempty
      (tweakableURP (T := T) (X := X)).val := by
  exact RandomSystems.CR18.functionEvaluatorProb_totalOnNonempty
    (⟨RandomSystems.Dist.uniform (T → Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : T → Equiv.Perm X => tweakablePermFunction π)

/-- Support fact: the ideal tweakable strong random permutation is total on
every nonempty input history in its support. -/
theorem tweakableStrongURP_totalOnNonempty {T : Type u} {X : Type v}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X] :
    RandomSystems.CR18.CondEquiv.TotalOnNonempty
      (tweakableStrongURP (T := T) (X := X)).val := by
  exact RandomSystems.CR18.functionEvaluatorProb_totalOnNonempty
    (⟨RandomSystems.Dist.uniform (T → Equiv.Perm X),
      RandomSystems.Dist.uniform_isProbDist⟩)
    (fun π : T → Equiv.Perm X => tweakableStrongPermFunction π)

/-- Source-facing adaptive SPRP advantage on the migrated law-level surface.
The ideal is constructed internally as `strongURP`; it is not a theorem input. -/
noncomputable def advSPRP {X : Type u} {q : Nat}
    [Fintype X] [DecidableEq X] [FiniteTranscriptSpace (QueryDir × X) X q]
    (F : ProbPDS (QueryDir × X) X) : ℝ :=
  SecurityDefs.Adv (q := q) F (strongURP (X := X))

/-- Source-facing adaptive tweakable-PRP advantage on the migrated law-level
surface.  The ideal is constructed internally as `tweakableURP`. -/
noncomputable def advTPRP {T : Type u} {X : Type v} {q : Nat}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X]
    [FiniteTranscriptSpace (T × X) X q]
    (F : ProbPDS (T × X) X) : ℝ :=
  SecurityDefs.Adv (q := q) F (tweakableURP (T := T) (X := X))

/-- Source-facing adaptive tweakable-SPRP advantage on the migrated law-level
surface.  The ideal is constructed internally as `tweakableStrongURP`. -/
noncomputable def advTSPRP {T : Type u} {X : Type v} {q : Nat}
    [Fintype T] [DecidableEq T] [Fintype X] [DecidableEq X]
    [FiniteTranscriptSpace (QueryDir × T × X) X q]
    (F : ProbPDS (QueryDir × T × X) X) : ℝ :=
  SecurityDefs.Adv (q := q) F (tweakableStrongURP (T := T) (X := X))

end HTechnique
end Migration
end NextGen
