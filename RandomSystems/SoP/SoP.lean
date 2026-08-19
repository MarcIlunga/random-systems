/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.SoP1
import RandomSystems.SoP.SoP2

/-!
# Sum-of-permutations proof index

This module contains no proof.  It exports the two deliberately separate
constructions:

* `RandomSystems.SoP.SoP1`: one permutation on `X × Fin 2`, summed across
  the two points over each input;
* `RandomSystems.SoP.SoP2`: two independent permutations on the same group,
  summed pointwise.

The small generic intersection of their proof infrastructure lives in
`RandomSystems.SoP.Common`.
-/
