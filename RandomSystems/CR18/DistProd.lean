/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist
import RandomSystems.CR18.Game

-- PORTED from hctr2-verification HCTR2/Proofs/CR18/Sketch.lean:392-422 — UPSTREAM-CANDIDATE landed 2026-06-11

/-!
# Independent product of a dependent family of distributions

GAP-7 of the HCTR2 [CR18] development: the **independent product** of finitely
many finite-support sub-distributions over a *dependent* family of alphabets
`A : Fin u → Type*`.  This is absent from the `Dist` library and is needed by
the Dist-level parallel composition of systems (`parPDS` downstream): the
product distribution *is* independence, by construction.

## Main declarations

* `RandomSystems.Dist.pi` — the product `Dist (∀ i, A i)` of a dependent family
  `d : ∀ i, Dist (A i)`, placing mass `∏ i, d i (f i)` on the tuple `f`.
* `RandomSystems.CR18.Def49.pi_const_eq_independentCopies` — GAP-7b bridge: on
  CONSTANT families, `Dist.pi` agrees with the library's proven
  `Def49.independentCopies`, so its `independentCopies_apply` /
  `independentCopies_marginal` lemmas transfer directly.  The genuinely new
  upstream content of `Dist.pi` is the dependent-family case (per-user
  alphabets).
-/

open scoped Classical

noncomputable section

namespace RandomSystems

namespace Dist

/-- Independent product of a dependent family of finite-support
(sub-)distributions: `pi d` places mass `∏ i, d i (f i)` on the tuple `f`.
Independence holds by construction — the joint mass factors as the product of
the marginal masses. -/
def pi {u : ℕ} {A : Fin u → Type*} (d : ∀ i, Dist (A i)) :
    Dist (∀ i, A i) :=
  ⟨(Fintype.piFinset fun i => (d i).support).filter fun f => (∏ i, d i (f i)) ≠ 0,
   fun f => ∏ i, d i (f i),
   fun f => by
     constructor
     · exact fun hf => (Finset.mem_filter.mp hf).2
     · intro hf
       refine Finset.mem_filter.mpr
         ⟨Fintype.mem_piFinset.mpr fun i => Finsupp.mem_support_iff.mpr ?_, hf⟩
       exact Finset.prod_ne_zero_iff.mp hf i (Finset.mem_univ i)⟩

/-- The defining product formula for `Dist.pi`: the mass of a tuple is the
product of the per-coordinate masses. -/
@[simp]
theorem pi_apply {u : ℕ} {A : Fin u → Type*} (d : ∀ i, Dist (A i)) (f : ∀ i, A i) :
    pi d f = ∏ i, d i (f i) :=
  rfl

end Dist

namespace CR18

namespace Def49

/-- GAP-7b (REUSE bridge): on CONSTANT families `Dist.pi` IS the library's
proven `independentCopies` — its `independentCopies_apply` /
`independentCopies_marginal` lemmas then serve the product directly.  GAP-7's
genuinely-new upstream content is only the DEPENDENT-family case. -/
theorem pi_const_eq_independentCopies {α : Type*} [DecidableEq α] (u : ℕ) (d : Dist α) :
    Dist.pi (fun _ : Fin u => d) = independentCopies u d := by
  ext g
  rw [independentCopies_apply]
  rfl

end Def49

end CR18

end RandomSystems

end
