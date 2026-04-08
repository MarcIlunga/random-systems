/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DistSimpAttr
import RandomSystems.Dist

/-!
# `dist_simp` — Curated Simp Set for Distributions

Tags `Dist` lemmas with the `@[dist_simp]` attribute.
Use as `simp only [dist_simp]`.

## Included (terms get smaller/simpler)

- Weight: `weight_fTransform`, `weight_prod`, `weight_uniform`
- Uniform: `uniform_apply`, `prod_uniform`
- Composition: `fTransform_comp`, `fTransform_bijection_uniform`,
  `fTransform_equiv_uniform`, `fTransform_fst_uniform`, `fTransform_snd_uniform`
- Predicate: `evalPred_eq_evalSet`

## Excluded (too expansive — use `rw`)

- `fTransform_apply_eq_sum`, `transcriptDist_apply_eq_sum`
-/

open RandomSystems.Dist in
attribute [dist_simp]
  evalPred_eq_evalSet
  uniform_apply
  weight_uniform
  weight_fTransform
  weight_prod
  prod_uniform
  fTransform_comp
  fTransform_bijection_uniform
  fTransform_equiv_uniform
  fTransform_fst_uniform
  fTransform_snd_uniform
