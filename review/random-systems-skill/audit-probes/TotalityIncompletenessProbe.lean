import RandomSystems.CBCMAC
import RandomSystems.TotalityTactics

open RandomSystems.CR18

namespace RandomSystems.CR18

universe u

variable {M X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X] [Fintype M] [DecidableEq M]

-- This proposition has a named proof (`cbcReal_totalOnNonempty`) in the
-- imported module, but is intentionally not registered in `cr18_total`.
example (bf : M → List X) : CondEquiv.TotalOnNonempty (cbcReal bf) := by
  cr18_total

-- Likewise `cbcReal_isProbDist` proves this goal, but `cr18_prob` is only a
-- fixed simplification bundle and does not discover that theorem.
example (bf : M → List X) : (cbcReal bf).isProbDist := by
  cr18_prob

end RandomSystems.CR18
