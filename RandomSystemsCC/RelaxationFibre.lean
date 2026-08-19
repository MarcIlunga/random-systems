/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Projection-induced relaxations, abstractly (Jost, Ch. 5 §5.3)

Every relaxation in Jost's §5.3 is the **fibre of a projection**: `R^{P]}`
(Definition 5.3.2) is `{S | until_P(S) = until_P(R)}`, `R^{[P}` (Definition
5.3.7) is `{S | from_P(S) = from_P(R)}`, and `R^{[P₁,P₂]}` (Definition 5.3.11)
is `{S | until_{P₂}(from_{P₁}(S)) = until_{P₂}(from_{P₁}(R))}`.  All three are
`fibre` below, at three different projections.  Note that these are equalities
of projected *systems*, not indistinguishabilities: the relaxations are unions
of kernel classes of set maps and nothing more.

This module is the part of the story that needs no system algebra at all, and
its point is **negative**.

## What is settled here

* `fibre`, `fibreComp` (the two-fold composite `(R^{p})^{q}`, spelled as Jost
  spells it — a union of fibres over the members of a fibre) and `fibreChain`
  (Theorem 5.3.12's `R^{φ₁·φ₂⋯φₙ}`).
* `fibreComp_swap_of_eq_fibre`: **the collapse in one order implies it in the
  other.**  If `(R^{p})^{q} = fibre r R` for every `R`, then
  `(R^{q})^{p} = fibre r R` for every `R`, because a fibre relation is
  symmetric and `(A;B)ᵗ = Bᵗ;Aᵗ = B;A` for symmetric `A`, `B`.  This halves the
  work of any concrete collapse proof: one order suffices.
* `iUnion_fibreChain_eq_fibre`: given the two-fold collapse, Theorem 5.3.12's
  union over `n ∈ ℕ` of the alternating composites **collapses at `n = 2`**, and
  the further relaxations Jost's three-fold composites apply are redundant.
* `Blocked.fibreComp_ne_fibre` and `Blocked.fibreComp_ne_swap`: **two
  idempotent retractions can commute as functions while their fibre relations
  fail to permute.**  Three elements suffice.

The last item is why the question Jost leaves open (p. 101, "it is an
interesting open question whether the two respective relaxations actually
commute") cannot be answered at this level.  `until_P` and `from_P` are
idempotent, and Jost proves the two *projections* commute
(p. 101, `from_{P₁}(until_{P₂}(R)) = until_{P₂}(from_{P₁}(R))`); `Blocked`
exhibits an `f` and a `g` with exactly those two properties for which the
collapse fails and the two orders of composite genuinely differ.  So no
argument from the retraction calculus alone can decide the question: the answer
has to come from what the systems are, which is
`RandomSystemsCC.IntervalRelaxation`.
-/

namespace RandomSystemsCC.IntervalWise

universe ua ub uc ud

/-! ## Fibres of projections -/

section Fibre

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud}

/-- **The relaxation induced by a projection.**  Jost's `R^{P]}` (Definition
5.3.2), `R^{[P}` (Definition 5.3.7) and `R^{[P₁,P₂]}` (Definition 5.3.11) are
this set at three different projections. -/
def fibre (project : α → β) (R : α) : Set α := {S | project S = project R}

@[simp] theorem mem_fibre {project : α → β} {R S : α} :
    S ∈ fibre project R ↔ project S = project R := Iff.rfl

theorem self_mem_fibre (project : α → β) (R : α) : R ∈ fibre project R := rfl

/-- A fibre relation is symmetric — the one fact the swap theorem below needs. -/
theorem mem_fibre_comm {project : α → β} {R S : α} :
    S ∈ fibre project R ↔ R ∈ fibre project S :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- **The two-fold composite `(R^{p})^{q}`**: relax along `p`, then relax every
member of the result along `q`.  Written as the union of fibres that Jost's
specification-level statements are, rather than as a relation composition. -/
def fibreComp (p : α → β) (q : α → γ) (R : α) : Set α := ⋃ T ∈ fibre p R, fibre q T

theorem mem_fibreComp {p : α → β} {q : α → γ} {R S : α} :
    S ∈ fibreComp p q R ↔ ∃ T, p T = p R ∧ q S = q T := by
  simp [fibreComp, fibre]

/-- The inner relaxation is contained in the composite: take `T := S`. -/
theorem fibre_subset_fibreComp (p : α → β) (q : α → γ) (R : α) :
    fibre p R ⊆ fibreComp p q R := fun _ hS => mem_fibreComp.2 ⟨_, hS, rfl⟩

/-- The outer relaxation is contained in the composite: take `T := R`. -/
theorem fibre_subset_fibreComp' (p : α → β) (q : α → γ) (R : α) :
    fibre q R ⊆ fibreComp p q R := fun _ hS => mem_fibreComp.2 ⟨R, rfl, hS⟩

/-- **The collapse in one order gives the collapse in the other.**

If the two-fold composite `(·^{p})^{q}` is the fibre of a single projection `r`
at every point, then so is `(·^{q})^{p}`, hence the two composites agree and the
two relaxations commute.  The proof is the transpose identity for symmetric
relations and uses nothing about `p`, `q`, `r` — in particular no idempotence and
no commutation.

Consequence for a concrete development: proving the collapse in Jost's printed
`until ∘ from` orientation suffices; the mirror statement is free. -/
theorem fibreComp_swap_of_eq_fibre {p : α → β} {q : α → γ} {r : α → δ}
    (collapse : ∀ R : α, fibreComp p q R = fibre r R) (R : α) :
    fibreComp q p R = fibre r R := by
  ext S
  constructor
  · intro hS
    obtain ⟨T, hqT, hpS⟩ := mem_fibreComp.1 hS
    have : R ∈ fibreComp p q S := mem_fibreComp.2 ⟨T, hpS.symm, hqT.symm⟩
    exact (mem_fibre.1 ((collapse S).subset this)).symm
  · intro hS
    have : R ∈ fibreComp p q S := (collapse S).symm.subset (mem_fibre.2 (mem_fibre.1 hS).symm)
    obtain ⟨T, hpT, hqR⟩ := mem_fibreComp.1 this
    exact mem_fibreComp.2 ⟨T, hqR.symm, hpT.symm⟩

/-- **Jost's `R^{φ₁·φ₂⋯φₙ}`** (Theorem 5.3.12): apply the relaxations in the
order listed, `false` selecting `p` and `true` selecting `q`.  Jost's statement
quantifies over all `n` and all words in `{P₂], [P₁}`, which is exactly a
`List Bool` here. -/
def fibreChain (p : α → β) (q : α → γ) : List Bool → α → Set α
  | [], R => {R}
  | step :: rest, R => ⋃ T ∈ (if step then fibre q R else fibre p R), fibreChain p q rest T

@[simp] theorem fibreChain_nil (p : α → β) (q : α → γ) (R : α) :
    fibreChain p q [] R = {R} := rfl

theorem fibreChain_pair (p : α → β) (q : α → γ) (R : α) :
    fibreChain p q [false, true] R = fibreComp p q R := by
  ext S
  simp [fibreChain, fibreComp]

/-- Every alternating composite is contained in the single fibre, once the
two-fold composite is. -/
theorem fibreChain_subset_fibre {p : α → β} {q : α → γ} {r : α → δ}
    (collapse : ∀ R : α, fibreComp p q R = fibre r R) :
    ∀ (steps : List Bool) (R : α), fibreChain p q steps R ⊆ fibre r R := by
  have hp : ∀ T S : α, S ∈ fibre p T → S ∈ fibre r T := fun T S hS =>
    (collapse T).subset (fibre_subset_fibreComp p q T hS)
  have hq : ∀ T S : α, S ∈ fibre q T → S ∈ fibre r T := fun T S hS =>
    (collapse T).subset (fibre_subset_fibreComp' p q T hS)
  intro steps
  induction steps with
  | nil => intro R S hS; simp only [fibreChain_nil, Set.mem_singleton_iff] at hS; simp [hS]
  | cons step rest ih =>
      intro R S hS
      simp only [fibreChain, Set.mem_iUnion, exists_prop] at hS
      obtain ⟨T, hT, hST⟩ := hS
      have step_le : T ∈ fibre r R := by
        cases step with
        | false => exact hp R T (by simpa using hT)
        | true => exact hq R T (by simpa using hT)
      have := ih T hST
      exact mem_fibre.2 ((mem_fibre.1 this).trans (mem_fibre.1 step_le))

/-- **Theorem 5.3.12's union collapses at `n = 2`.**  Given the two-fold
collapse, the union over all `n` of all alternating composites is already the
single fibre — so the three-fold composites Jost's theorem exhibits
(`((R^{[P₁})^{P₂]})^{[P₁}` and `((R^{P₂]})^{[P₁})^{P₂]}`) apply a redundant outer
relaxation. -/
theorem iUnion_fibreChain_eq_fibre {p : α → β} {q : α → γ} {r : α → δ}
    (collapse : ∀ R : α, fibreComp p q R = fibre r R) (R : α) :
    (⋃ steps : List Bool, fibreChain p q steps R) = fibre r R := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun steps => fibreChain_subset_fibre collapse steps R) ?_
  intro S hS
  exact Set.mem_iUnion.2 ⟨[false, true], by rw [fibreChain_pair]; exact (collapse R).symm.subset hS⟩

/-- **The specification-level relaxation**: Jost's `𝓡^{p}`, the union of the
member relaxations. -/
def specFibre (p : α → β) (spec : Set α) : Set α := ⋃ R ∈ spec, fibre p R

theorem mem_specFibre {p : α → β} {spec : Set α} {S : α} :
    S ∈ specFibre p spec ↔ ∃ R ∈ spec, p S = p R := by
  simp [specFibre, fibre]

/-- **The collapse at the specification level.**  A resource-level fibre identity
does not by itself give the specification-level one — the union has to be moved
across the composite — but the two-fold collapse is all the input needed, and
this is where the argument lives once and for all. -/
theorem specFibre_specFibre_of_collapse {p : α → β} {q : α → γ} {r : α → δ}
    (collapse : ∀ R : α, fibreComp p q R = fibre r R) (spec : Set α) :
    specFibre q (specFibre p spec) = specFibre r spec := by
  ext S
  simp only [mem_specFibre]
  constructor
  · rintro ⟨T, ⟨R, memR, hT⟩, hS⟩
    exact ⟨R, memR, mem_fibre.1 ((collapse R).subset (mem_fibreComp.2 ⟨T, hT, hS⟩))⟩
  · rintro ⟨R, memR, hS⟩
    obtain ⟨T, hT, hS'⟩ := mem_fibreComp.1 ((collapse R).symm.subset (mem_fibre.2 hS))
    exact ⟨T, ⟨R, memR, hT⟩, hS'⟩

/-- **The collapse descends to any quotient the three projections factor
through.**  Nothing beyond that factorization is needed: a class lies in the
lifted composite exactly when one — equivalently every — representative lies in
the composite downstairs, because the middle term of the composite may be chosen
among representatives.  So the *only* obstruction to reading a fibre collapse on
a quotient carrier is well-definedness of the projections on it. -/
theorem fibreComp_quotient_eq_fibre {s : Setoid α} {p : α → β} {q : α → γ} {r : α → δ}
    {liftP : Quotient s → β} {liftQ : Quotient s → γ} {liftR : Quotient s → δ}
    (factorP : ∀ x : α, liftP (Quotient.mk s x) = p x)
    (factorQ : ∀ x : α, liftQ (Quotient.mk s x) = q x)
    (factorR : ∀ x : α, liftR (Quotient.mk s x) = r x)
    (collapse : ∀ R : α, fibreComp p q R = fibre r R) (R : Quotient s) :
    fibreComp liftP liftQ R = fibre liftR R := by
  induction R using Quotient.inductionOn with
  | _ a =>
    ext Y
    induction Y using Quotient.inductionOn with
    | _ x =>
      constructor
      · intro member
        obtain ⟨T, hT, hx⟩ := mem_fibreComp.1 member
        obtain ⟨t, rfl⟩ := Quotient.exists_rep T
        rw [factorP, factorP] at hT
        rw [factorQ, factorQ] at hx
        refine mem_fibre.2 ?_
        rw [factorR, factorR]
        exact mem_fibre.1 ((collapse a).subset (mem_fibreComp.2 ⟨t, hT, hx⟩))
      · intro member
        have base : r x = r a := by
          have := mem_fibre.1 member
          rwa [factorR, factorR] at this
        obtain ⟨t, hT, hx⟩ := mem_fibreComp.1 ((collapse a).symm.subset (mem_fibre.2 base))
        exact mem_fibreComp.2 ⟨Quotient.mk s t, by rw [factorP, factorP]; exact hT,
          by rw [factorQ, factorQ]; exact hx⟩

end Fibre

/-! ## The retraction calculus cannot decide the question

Two idempotent self-maps of `Fin 3` that commute, whose fibre relations
nevertheless fail to permute.  This is the negative half of this module: it
bounds from below what a proof of Jost's open question has to use. -/

namespace Blocked

/-- Collapses `0` onto `1`, fixes `2`.  Fibres: `{0, 1}` and `{2}`. -/
def f : Fin 3 → Fin 3 := fun i => if i = 2 then 2 else 1

/-- Fixes `0`, collapses `2` onto `1`.  Fibres: `{0}` and `{1, 2}`. -/
def g : Fin 3 → Fin 3 := fun i => if i = 0 then 0 else 1

theorem f_idempotent : ∀ i, f (f i) = f i := by decide

theorem g_idempotent : ∀ i, g (g i) = g i := by decide

/-- The two maps commute — the abstract shadow of Jost's p. 101 observation
that the from-projection and the until-projection commute. -/
theorem f_comm_g : ∀ i, f (g i) = g (f i) := by decide

/-- The composite projection is constant, so its fibre through any point is
everything. -/
theorem gf_const : ∀ i, g (f i) = 1 := by decide

theorem fibre_comp_projection (R : Fin 3) : fibre (g ∘ f) R = Set.univ := by
  ext S
  simp only [fibre, Function.comp_apply, Set.mem_setOf_eq, Set.mem_univ,
    gf_const S, gf_const R]

/-- **The collapse fails abstractly.**  `0` lies in the fibre of the composite
projection through `2` but not in the two-fold composite `(2^{f})^{g}`, because
`f T = f 2` forces `T = 2` and `g 0 ≠ g 2`. -/
theorem fibreComp_ne_fibre : fibreComp f g 2 ≠ fibre (g ∘ f) 2 := by
  intro h
  have mem : (0 : Fin 3) ∈ fibreComp f g 2 := by
    rw [h, fibre_comp_projection]; trivial
  obtain ⟨T, hfT, hg0⟩ := mem_fibreComp.1 mem
  revert hfT hg0
  revert T
  decide

/-- **The two orders of composite genuinely differ**, so the fibre relations of
`f` and `g` do not permute even though `f` and `g` do. -/
theorem fibreComp_ne_swap : fibreComp g f 2 ≠ fibreComp f g 2 := by
  intro h
  have mem : (0 : Fin 3) ∈ fibreComp g f 2 := mem_fibreComp.2 ⟨1, by decide, by decide⟩
  rw [h] at mem
  obtain ⟨T, hfT, hg0⟩ := mem_fibreComp.1 mem
  revert hfT hg0
  revert T
  decide

end Blocked

end RandomSystemsCC.IntervalWise
