/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CausalApply

/-!
# CR18 §4.7.2 — Reductions by a Converter

A converter `c` is, by CR18 §3.4.6, its **action on systems** — a function `c : DDS X Y → DDS U V`
(the genuine application `CausalApply.applyG cstep` is one, `applyGc cstep` below). Maurer's
juxtaposition is then exactly Lean's function application and composition, *no special notation*:

| CR18 | here |
| --- | --- |
| `cg` (converter applied to game) | `c g` |
| `wc` (winner transformed by converter) | `w ∘ c` |
| `ρ_C : w ↦ wc` (the reduction function) | `rhoC c = (· ∘ c)` |
| `cs`/`CG`, `WC` (probabilistic) | `c g` / `Dist.fTransform c G`, `Dist.fTransform (rhoC c) W` |

CR18 §4.7.2 then states

> `ω(wc, g) = ω(w, cg)`    (4.9)     and, as `ρ_C`,     `CG = G ρ_C`    (4.10).

With a winner read as its winning functional (`DDS U V → α`, `ω(w, g) = w g`), `wc = w ∘ c` and
`cg = c g`, so (4.9) `(w ∘ c) g = w (c g)` and (4.10) `gamePerf (c g) = gamePerf g ∘ rhoC c` are `rfl`
— the "trivial reduction equality", on the genuine converter, with no new structure or notation.
-/

namespace RandomSystems

open RandomSystems (Dist)

/-- Summing a function additive in the weight against a pushforward pulls back along the map
(`Dist.fTransform = Finsupp.mapDomain`), support-based / `Fintype`-free. -/
theorem Dist.fTransform_finsuppSum {A B : Type*} (f : A → B) (X : Dist A)
    (h : B → ℝ → ℝ) (h0 : ∀ b, h b 0 = 0)
    (hadd : ∀ b w₁ w₂, h b (w₁ + w₂) = h b w₁ + h b w₂) :
    (Dist.fTransform f X).sum h = X.sum (fun a w => h (f a) w) :=
  Finsupp.sum_mapDomain_index h0 hadd

namespace CR18.CausalApply

variable {U X Y V α : Type*}

/-- The genuine converter application as a converter (its action on systems, CR18 §3.4.6):
`applyGc cstep g = applyG cstep g` is the game `cg`. -/
noncomputable def applyGc (cstep : U → List Y → X ⊕ V) : PFunDDS.DDS X Y → PFunDDS.DDS U V :=
  fun g => applyG cstep g.1

variable (c : PFunDDS.DDS X Y → PFunDDS.DDS U V)

/-- CR18 §4.7.2: the reduction function `ρ^C : w ↦ wc = w ∘ c`. -/
def rhoC (w : PFunDDS.DDS U V → α) : PFunDDS.DDS X Y → α := w ∘ c

/-- `ρ[c]` is Maurer's reduction function `ρ^C` (Lean can't superscript a variable). -/
scoped notation:max "ρ[" c "]" => rhoC c

/-- A game read as its performance function on winners, `G : w ↦ ω(w, g) = w g`; `G = gamePerf g`,
`CG = gamePerf (c g)`. -/
def gamePerf {S : Type*} (g : S) : (S → α) → α := fun w => w g

/-- **CR18 (4.9): `ω(wc, g) = ω(w, cg)`** — with `wc = ρ[c] w` and `cg = c g`. -/
@[simp] theorem rhoC_apply (w : PFunDDS.DDS U V → α) (g : PFunDDS.DDS X Y) :
    ρ[c] w g = w (c g) := rfl

/-- **CR18 (4.10): `CG = G ρ^C`** — `CG = gamePerf (c g)`, `G = gamePerf g`, `ρ^C = ρ[c]`, composed
as functions. -/
theorem perf_eq (g : PFunDDS.DDS X Y) :
    gamePerf (α := α) (c g) = gamePerf g ∘ ρ[c] :=
  rfl

/-- CR18 Definition 4.5 winning probability: `ω(W, G) = ∑_{w,g} W(w)·G(g)·⟦w g⟧`. -/
noncomputable def winProb {S : Type*} (W : Dist (S → Bool)) (G : Dist S) : ℝ :=
  W.sum fun w wp => G.sum fun g gp => wp * gp * (if w g then 1 else 0)

/-- **CR18 (4.9)/(4.10), probabilistic: `ω(W, CG) = ω(WC, G)`.** Here `CG = Dist.fTransform c G` is the
converter applied to a probabilistic game and `WC = Dist.fTransform ρ[c] W` is `ρ^C` applied to a
probabilistic winner — (4.9) (which is `rfl`) pushed through `Dist.fTransform` on both sides. -/
theorem winProb_apply (W : Dist (PFunDDS.DDS U V → Bool)) (G : Dist (PFunDDS.DDS X Y)) :
    winProb W (Dist.fTransform c G) = winProb (Dist.fTransform ρ[c] W) G := by
  unfold winProb
  rw [Dist.fTransform_finsuppSum (rhoC c) W
        (fun w' wp => G.sum fun g gp => wp * gp * (if w' g then 1 else 0))
        (fun _ => by simp) (fun _ _ _ => by simp only [Finsupp.sum, add_mul, Finset.sum_add_distrib])]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [Dist.fTransform_finsuppSum c G
        (fun g' gp => W w * gp * (if w g' then 1 else 0))
        (fun _ => by ring) (fun _ _ _ => by ring)]
  rfl

end CR18.CausalApply
end RandomSystems
