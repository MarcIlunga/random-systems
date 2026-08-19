/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SwitchingLemma
import RandomSystems.FilterDomNormalization
import RandomSystems.AbsorbDPI

/-!
# Sum of two independent random permutations

The classical sum-of-permutations (XoP) construction: sample two independent uniform
permutations `π₁, π₂` of a finite abelian group `G` and answer a query `x` with
`π₁ x + π₂ x`.  The claim is that this is indistinguishable from a uniform random
function `G → G`.

## The proof

Conditional equivalence (CR18 Thm 4.17), through the packaged seed-indexed endpoint
`maxAdvantage_filterQueries_seededConditionCGame_le`.

For a *fixed* permutation `π` the map `f ↦ (x ↦ π x + f x)` is a bijection of `G → G`, so
`π + f` is a uniform random function: the game's seed evaluator **is** the ideal system
(`sopGame_ignoreMBO`).  The monitored bad event is a collision of the sampled `f` on two
distinct queried inputs (`seededHashCollision`); off it, `f`'s restriction to the queried
set is distributed exactly like a uniform permutation's, so the answers are exactly
`sopReal`'s (`sop_condEquiv`).  The blind reduction then leaves the plain birthday mass of
a uniform random function on a fixed schedule.

The conditional equivalence runs in this direction — game on the *ideal* side, `sopReal` as
the conditionally-equivalent target — and not the reverse: conditioning on a seed event can
only reweight inside the support, and `sopReal`'s answer law has strictly smaller support
than uniform (in `ℤ/2` with two distinct queries, `π₁x₁ + π₂x₁ = π₁x₂ + π₂x₂` always).  No
bad event on `(π₁, π₂)` can therefore make the real system's conditioned law uniform.
`Δ` is symmetric on probability systems, so the direction costs nothing.
-/

noncomputable section

namespace RandomSystems.CR18.SoP

open RandomSystems (Dist)
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

universe u

variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] [AddCommGroup G]

/-- The sum-of-permutations function determined by a pair of permutations:
`x ↦ π₁ x + π₂ x`. -/
def sopFunction (p : Equiv.Perm G × Equiv.Perm G) : G → G :=
  fun x => p.1 x + p.2 x

/-- **The real system** `XoP`: two independent uniform permutations, queried as the
function `x ↦ π₁ x + π₂ x`. -/
def sopReal : PFunPDS G G :=
  Dist.fTransform
    (fun p : Equiv.Perm G × Equiv.Perm G => PFunDDS.functionEvaluator (sopFunction p))
    (Dist.uniform (Equiv.Perm G × Equiv.Perm G))

/-- **The ideal system**: a uniform random function `G → G`. -/
def sopIdeal : PFunPDS G G :=
  Dist.fTransform PFunDDS.functionEvaluator (Dist.uniform (G → G))

/-! ## The monitored game -/

/-- The game's seed: a uniform permutation together with an independent uniform random
function.  Replacing the second uniform permutation of `sopReal` by a uniform *function*
is the whole content of the reduction. -/
def sopSeed : Dist (Equiv.Perm G × (G → G)) :=
  Dist.prod (Dist.uniform (Equiv.Perm G)) (Dist.uniform (G → G))

/-- The game's evaluator `x ↦ π x + f x`. -/
def sopMidFunction (p : Equiv.Perm G × (G → G)) : G → G :=
  fun x => p.1 x + p.2 x

/-- **The bad event**: the sampled function collides on two distinct queried inputs.  This
is the library's ready-made seeded-hash collision, with the hash being the sampled function
itself. -/
abbrev sopBad (p : Equiv.Perm G × (G → G)) (l : List G) : Prop :=
  seededHashCollision (fun r : Equiv.Perm G × (G → G) => r.2) p l

/-- The monitored condition-C game: the ideal system, watched for a collision of its
hidden uniform function on the queried inputs. -/
def sopGame : PFunPDS G (G × Bool) :=
  seededConditionCGame (sopSeed (G := G)) sopMidFunction sopBad

/-! ## The seed law -/

/-- Adding an independent uniform permutation to a uniform random function leaves a uniform
random function: the seed evaluator's law is the ideal law. -/
theorem fTransform_sopMidFunction :
    Dist.fTransform (sopMidFunction (G := G)) (sopSeed (G := G)) = Dist.uniform (G → G) := by
  classical
  -- `(π, f) ↦ (π, π + f)` is a bijection of the seed space; the evaluator is its second
  -- projection, and a uniform product projects to uniform.
  let e : (Equiv.Perm G × (G → G)) ≃ (Equiv.Perm G × (G → G)) :=
    { toFun := fun p => (p.1, fun x => p.1 x + p.2 x)
      invFun := fun p => (p.1, fun x => -p.1 x + p.2 x)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hcomp : (sopMidFunction (G := G)) = Prod.snd ∘ e := rfl
  rw [sopSeed, Dist.prod_uniform, hcomp, ← Dist.fTransform_comp, Dist.fTransform_equiv_uniform,
    Dist.fTransform_snd_uniform]

/-- Stripping the monitor bit from the game returns the **ideal** system. -/
theorem sopGame_ignoreMBO : PFunPDS.ignoreMBO (sopGame (G := G)) = sopIdeal := by
  rw [sopGame, seededConditionCGame_ignoreMBO, fTransform_sopMidFunction]
  rfl

/-! ## Standing side conditions -/

omit [AddCommGroup G] in
theorem sopSeed_isProbDist : (sopSeed (G := G)).isProbDist :=
  Dist.prod_isProbDist _ _ Dist.uniform_isProbDist Dist.uniform_isProbDist

omit [Nonempty G] in
theorem sopReal_isProbDist : (sopReal (G := G)).isProbDist := by
  unfold sopReal
  cr18_prob

omit [AddCommGroup G] in
theorem sopIdeal_isProbDist : (sopIdeal (G := G)).isProbDist := by
  unfold sopIdeal
  cr18_prob

omit [Nonempty G] in
theorem sopReal_totalOnNonempty : CondEquiv.TotalOnNonempty (sopReal (G := G)) :=
  CondEquiv.totalOnNonempty_fTransform_historyEvaluator _
    (fun p l h => sopFunction p (l.getLast h))

/-! ## Conditional equivalence -/

/-- **The fiber factorization — the whole content of condition C.**

Over the queried set `S`, the seed mass of "the answers realize the assignment `a`, and the
sampled function has not yet collided" equals the real system's mass of "the answers realize
`a`", times the not-yet-collided normalizer.

It is the URF/URP fiber identity `uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn`
— a uniform function conditioned to be injective on `S` has a uniform permutation's fiber law
— integrated over the *independent* permutation component of the seed.  The permutation
component is what a converter-based reduction would have to absorb by hand; here it is just
the first coordinate of a product, and `mass_prod_congr_fiber` integrates it. -/
theorem sopSeed_mass_agree_and_good (S : Finset G) (a : ↥S → G) (l : List G)
    (hl : ∀ x, x ∈ l ↔ x ∈ S) :
    (sopSeed (G := G)).mass
        (fun p => (∀ s : ↥S, sopMidFunction p ↑s = a s) ∧ ¬ sopBad p l)
      = (Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
            (fun g => ∀ s : ↥S, sopFunction g ↑s = a s)
        * (sopSeed (G := G)).mass (fun p => ¬ sopBad p l) := by
  classical
  -- the not-yet-collided normalizer, constant in the sampled permutation
  set C : NNReal := (Dist.uniform (G → G)).mass (fun f => Set.InjOn f (fun x => x ∈ S))
  -- "not yet bad" is injectivity of the sampled function on the queried set
  have hbad : ∀ p : Equiv.Perm G × (G → G),
      (¬ sopBad p l) ↔ Set.InjOn p.2 (fun x => x ∈ S) := by
    intro p
    constructor
    · intro h x hx y hy hxy
      by_contra hne
      exact h ⟨x, (hl x).2 hx, y, (hl y).2 hy, hne, hxy⟩
    · rintro h ⟨x, hx, y, hy, hne, heq⟩
      exact hne (h ((hl x).1 hx) ((hl y).1 hy) heq)
  -- agreement with `a` pins the second seed component against the first
  have hagree : ∀ π σ : G → G,
      (∀ s : ↥S, π ↑s + σ ↑s = a s) ↔ (∀ s : ↥S, σ ↑s = a s - π ↑s) :=
    fun π σ => forall_congr' fun s => by rw [eq_sub_iff_add_eq, add_comm]
  have hleft : (sopSeed (G := G)).mass
        (fun p => (∀ s : ↥S, sopMidFunction p ↑s = a s) ∧ ¬ sopBad p l)
      = (Dist.prod (Dist.uniform (Equiv.Perm G)) (Dist.uniform (G → G))).mass
          (fun p => (∀ s : ↥S, p.2 ↑s = a s - p.1 ↑s) ∧
            Set.InjOn p.2 (fun x => x ∈ S)) := by
    rw [sopSeed]
    exact Dist.mass_congr _ fun p => and_congr (hagree _ _) (hbad p)
  have hfiber : ∀ π : Equiv.Perm G,
      (Dist.uniform (G → G)).mass
          (fun f => (∀ s : ↥S, f ↑s = a s - π ↑s) ∧ Set.InjOn f (fun x => x ∈ S))
        = (Dist.uniform (Equiv.Perm G)).mass (fun σ => ∀ s : ↥S, σ ↑s = a s - π ↑s) * C :=
    fun π => uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn S (fun s => a s - π ↑s)
  have hright : (sopSeed (G := G)).mass (fun p => ¬ sopBad p l) = C := by
    rw [sopSeed, Dist.mass_congr _ hbad,
      Dist.mass_prod_snd (Dist.uniform (Equiv.Perm G)) (Dist.uniform (G → G))
        (fun f => Set.InjOn f (fun x => x ∈ S)),
      show (Dist.uniform (Equiv.Perm G)).weight = 1 from Dist.uniform_isProbDist, one_mul]
  rw [hleft, hright,
    mass_prod_congr_fiber (Dist.uniform (Equiv.Perm G)) (Dist.uniform (G → G))
      (Dist.uniform (Equiv.Perm G)) _ (fun π σ => ∀ s : ↥S, σ ↑s = a s - π ↑s) C hfiber,
    Dist.prod_uniform]
  exact congrArg (· * C) (Dist.mass_congr _ fun g => (hagree g.1 g.2).symm)

/-- **Condition C for the sum of permutations.**  Until the hidden uniform function
collides on two distinct queried inputs, its answers are exactly those of a second
independent uniform permutation, so the game's conditioned law is `sopReal`'s. -/
theorem sop_condEquiv : (sopGame (G := G)) |≡ (sopReal (G := G)) := by
  classical
  refine condEquiv_of_transcript_mass_reductions (sopGame (G := G)) sopReal
    (sopSeed (G := G)) (Dist.uniform (Equiv.Perm G × Equiv.Perm G))
    sopMidFunction sopFunction (fun p l => ¬ sopBad p l)
    (fun {xs} hne => ?_)
    (fun ys xs => massY_fTransform_lastQuery _ _ ys xs)
    (fun ys xs => ?_)
    (fun xs a => ?_)
    (hT := sopReal_isProbDist) (hTot := sopReal_totalOnNonempty)
  · -- the not-yet-bad normalizer is the seed event
    unfold sopGame seededConditionCGame
    rw [CondEquiv.massAfalse_fTransform_historyEvaluator _ _ _ hne]
    exact Dist.mass_congr _ fun p => by simp
  · -- the joint "answers match ∧ not yet bad" law is the seed event
    unfold sopGame seededConditionCGame
    refine (massYAfalse_fTransform_lastQuery (sopSeed (G := G)) sopMidFunction
      (fun p l => decide (sopBad p l)) ?_ ys xs).trans ?_
    · intro p l₁ l₂ hpre hb
      simpa using seededHashCollision_monotone _ p hpre (by simpa using hb)
    · exact Dist.mass_congr _ fun p => by simp
  · -- the fiber factorization: the URF/URP fiber identity, integrated over the
    -- independent permutation component of the seed
    exact sopSeed_mass_agree_and_good xs.toList.toFinset a xs.toList
      (fun x => List.mem_toFinset.symm)

/-! ## The fixed-schedule bad mass -/

omit [AddCommGroup G] in
/-- **The counting leaf.**  On a fixed query schedule of at most `q` inputs the sampled
uniform function collides with probability at most the birthday pair-union bound. -/
theorem mass_sopBad_le (l : List G) (q : ℕ) (hlen : l.length ≤ q) :
    (sopSeed (G := G)).mass (fun p => sopBad p l) ≤ pairCollisionUnionBound G q := by
  -- the bad event only sees the sampled function, so the permutation marginalizes away
  have hproj : (fun p : Equiv.Perm G × (G → G) => sopBad p l)
      = (fun p : Equiv.Perm G × (G → G) =>
          seededHashCollision (fun g : G → G => g) p.2 l) := rfl
  rw [sopSeed, hproj, Dist.mass_prod_snd (Dist.uniform (Equiv.Perm G)) (Dist.uniform (G → G))
      (fun f => seededHashCollision (fun g : G → G => g) f l),
    show (Dist.uniform (Equiv.Perm G)).weight = 1 from Dist.uniform_isProbDist, one_mul]
  exact uniform_mass_listCollision_le_pairCollisionUnionBound l q hlen

/-! ## The bound -/

/-- **The sum of two independent random permutations is a randomness expander.**

For at most `q` queries, the XoP construction is indistinguishable from a uniform random
function up to `q² / |G|`. -/
theorem sop_randomness_expander (q : ℕ) :
    Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G))) ≤
      ((q : ℝ) ^ 2) / (Fintype.card G : ℝ) := by
  calc Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G)))
      = Δ(⌈q⌉ (sopIdeal (G := G)), ⌈q⌉ (sopReal (G := G))) := by
        exact maxAdvantage_comm (by cr18_prob; exact sopReal_isProbDist)
          (by cr18_prob; exact sopIdeal_isProbDist)
    _ = Δ(⌈q⌉ PFunPDS.ignoreMBO (sopGame (G := G)), ⌈q⌉ (sopReal (G := G))) := by
        rw [sopGame_ignoreMBO]
    _ ≤ (pairCollisionUnionBound G q : ℝ) :=
        maxAdvantage_filterQueries_seededConditionCGame_le (sopSeed (G := G)) sopMidFunction
          sopBad (fun p => seededHashCollision_monotone _ p) q sopReal
          (pairCollisionUnionBound G q) sop_condEquiv sopSeed_isProbDist sopReal_isProbDist
          sopReal_totalOnNonempty
          (fun w _ => mass_sopBad_le (blindQueryList w q) q (blindQueryList_length_le w q))
    _ ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card G : ℝ) :=
        pairCollisionUnionBound_le_birthday G q
    _ ≤ ((q : ℝ) ^ 2) / (Fintype.card G : ℝ) := by
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))]
        nlinarith [sq_nonneg (q : ℝ)]

end RandomSystems.CR18.SoP
