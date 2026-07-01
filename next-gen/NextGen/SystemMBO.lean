/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.PDS

/-!
# CR18 Definition 4.18 — `S⁻` (strip the MBO), next-gen / function-based

For an `(X, Y × Bool)`-system `S` with a monotone binary output (the `Bool` is the MBO `A`),
`S⁻` is the `(X, Y)`-system obtained by **ignoring the MBO** — `p^{S⁻}_{Yᵢ|XⁱYⁱ⁻¹} = p^S_{Yᵢ|XⁱYⁱ⁻¹}`.

Function-based: a system *is* its partial function `List X →. (Y × Bool)`; stripping just post-composes
the output with `Prod.fst`. `Part.map` preserves the domain, so validity (Def 3.1's domain conditions)
is preserved *definitionally* — no proof obligation. At the probabilistic layer it is the pushforward
`Dist.fTransform` of the deterministic strip. No struct, no `DecidableEq`.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-- CR18 Definition 4.18 (deterministic): strip the MBO bit from a deterministic system's output,
post-composing the partial function with `Prod.fst`. Validity is preserved (same domain). -/
def PFunDDS.stripMBO (s : PFunDDS.DDS X (Y × Bool)) : PFunDDS.DDS X Y :=
  ⟨fun l => (s.1 l).map Prod.fst, s.2⟩

@[simp] theorem PFunDDS.stripMBO_dom (s : PFunDDS.DDS X (Y × Bool)) :
    (PFunDDS.stripMBO s).1.Dom = s.1.Dom := rfl

/-- **Support lemma forced by formalization; candidate for upstream.** Stripping
the MBO from a paired history evaluator drops the Boolean component. -/
theorem PFunDDS.stripMBO_historyEvaluator_pair
    (g : (l : List X) → l ≠ [] → Y) (b : (l : List X) → l ≠ [] → Bool) :
    PFunDDS.stripMBO (PFunDDS.historyEvaluator (fun l hne => (g l hne, b l hne))) =
      PFunDDS.historyEvaluator g := by
  rfl

/-- CR18 Definition 4.18: `S⁻`, the `(X, Y)`-PDS obtained from an `(X, Y × Bool)`-PDS `S` by ignoring
the MBO — the pushforward of `S` along the deterministic strip. -/
noncomputable def PFunPDS.stripMBO (S : PFunPDS X (Y × Bool)) : PFunPDS X Y :=
  Dist.fTransform PFunDDS.stripMBO S

@[inherit_doc PFunPDS.stripMBO] scoped notation:max S "⁻" => PFunPDS.stripMBO S

end RandomSystems.CR18
