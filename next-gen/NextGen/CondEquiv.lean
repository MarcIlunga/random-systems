/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import NextGen.PDS
import NextGen.GameEquivalence
import NextGen.SystemMBO

/-!
# CR18 Definition 4.19 — conditional equivalence `Ŝ |≡ T` (next-gen, function-based)

For a **game** `Ŝ` (an `(X, Y × Bool)`-system whose `Bool` is the monotone binary output `A`,
`false = 0 = not won`) and a plain `(X, Y)`-system `T`, CR18 Definition 4.19 (eq. (4.38)) says `Ŝ` is
**conditionally equivalent** to `T`, written `Ŝ |≡ T`, iff the cumulative `Yⁱ`-output distribution of
`Ŝ` **conditioned on the MBO event `Aᵢ = 0`** equals the cumulative output distribution of `T`:

> `p^{Ŝ}_{Yⁱ | Xⁱ, Aᵢ=0}(yⁱ, xⁱ) = p^T_{Yⁱ | Xⁱ}(yⁱ, xⁱ)`.   (4.38)

To avoid division — and to honour CR18 footnote 29 ("equal for all arguments for which they are both
defined") — we state this in **cross-multiplied** (division-free) form, guarded by the two normalizers:

> `massYAfalse Ŝ i yⁱ xⁱ · massDom T xⁱ = massY T i yⁱ xⁱ · massAfalse Ŝ xⁱ`.

Everything is built from `Dist.mass` over a prefix-match predicate (`cumulativeBehavior`, Def 3.20):
no new probability machinery, and **no `DecidableEq`** — conditioning is not a decidability fact, it is
the classical `Dist.mass` over a `Prop`-valued event.

The `T`-side cumulative mass reuses `PFunPDS.cumulativeBehavior` (`bᶜ(T)`, Def 3.20, PDS.lean) verbatim.
The game-side pre-winning cumulative mass is the **same** `Dist.mass` prefix-match predicate, additionally
requiring every prefix MBO bit to be `false` — exactly the not-yet-won region of `prewinBehavior`
(GameEquivalence.lean), stated as a single `Dist.mass` to avoid a telescoping proof.

This ports the MATH/PROOF-STRUCTURE of the legacy struct development (Indist.lean:2303–2424) to the
next-gen PFun API: `PFunPDS = Dist (PFunDDS.DDS …)`, output read via `PFunDDS.output`, on `Vector` args.
-/

namespace RandomSystems.CR18.CondEquiv

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Game-side masses (the `Aᵢ = 0` numerator and the `Aᵢ = 0` normalizer) -/

/-- **CR18 Def 4.19 / eq. (4.38), game numerator** `p^{Ŝ}_{Yⁱ, Aᵢ=0 | Xⁱ}(yⁱ, xⁱ)` (unnormalized):
the cumulative probability, over the choice of deterministic `s ← Ŝ`, that on input transcript `xⁱ` the
game produces the visible output transcript `yⁱ` **and has not won by round `i`** (every prefix MBO bit
is `false`).

This is exactly the not-yet-won region of `prewinBehavior` (Def 4.15, GameEquivalence.lean) cumulated:
the *same* `Dist.mass` prefix-match predicate as `cumulativeBehavior` (Def 3.20), reading the `Y`
component (`.1`) of each prefix output against `yⁱ` and additionally requiring its MBO bit (`.2`) to be
`false`. Stated as one `Dist.mass` to avoid a telescoping proof. No `DecidableEq`. -/
noncomputable def massYAfalse (Shat : PFunPDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) : NNReal :=
  let ysl := ys.toList
  let xsl := xs.toList
  Dist.mass Shat (fun s =>
    ∀ k : Fin ysl.length,
      ∃ h : xsl.take (k.1 + 1) ∈ PFunDDS.dom s,
        (PFunDDS.output s (xsl.take (k.1 + 1)) h).1 = ysl.get k ∧
        (PFunDDS.output s (xsl.take (k.1 + 1)) h).2 = false)

/-- **CR18 Def 4.19, game normalizer** `p^{Ŝ}_{Aᵢ=0 | Xⁱ}(xⁱ)` (unnormalized): the total weight of
deterministic games `s ← Ŝ` for which `xⁱ` is in `s`'s domain and the MBO bit at `xⁱ` is `false`. -/
noncomputable def massAfalse (Shat : PFunPDS X (Y × Bool)) (xs : List X) : NNReal :=
  Dist.mass Shat (fun s =>
    ∃ h : xs ∈ PFunDDS.dom s, (PFunDDS.output s xs h).2 = false)

/-! ### Plain-system masses (reuse the next-gen cumulative behavior) -/

/-- **CR18 Def 4.19, plain numerator** `p^T_{Yⁱ | Xⁱ}(yⁱ, xⁱ)` (unnormalized): the `T`-side cumulative
output mass, reusing `PFunPDS.cumulativeBehavior` (`bᶜ(T)`, Def 3.20) verbatim. -/
noncomputable def massY (T : PFunPDS X Y) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) : NNReal :=
  PFunPDS.cumulativeBehavior T i (ys, xs)

/-- **CR18 Def 4.19, plain normalizer** `p^T_{Xⁱ}(xⁱ)` (unnormalized): the total weight of deterministic
systems `t ← T` for which `xⁱ` is in `t`'s domain — the normalizer for `T`'s conditional output
distribution at history `xⁱ`. -/
noncomputable def massDom (T : PFunPDS X Y) (xs : List X) : NNReal :=
  Dist.mass T (fun t => xs ∈ PFunDDS.dom t)

/-! ### Support-totality side condition (Maurer's "defined on the histories under discussion") -/

/-- CR18: the paper treats systems as defined on the histories under discussion. In the PFun partial
model, the corresponding support condition is that every realization in `T`'s support accepts every
nonempty input history. -/
def TotalOnNonempty (T : PFunPDS X Y) : Prop :=
  ∀ t ∈ T.support, ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom t

/-! ### CR18 Definition 4.19: conditional equivalence -/

/-- **CR18 Definition 4.19 (probabilistic layer)**: a game `Ŝ` (an `(X, Y × Bool)`-system) is
**conditionally equivalent** to a plain `(X, Y)`-system `T`, written `Ŝ |≡ T`, iff for every nonempty
input history `xⁱ` and visible output transcript `yⁱ` of the same length, the cumulative `Yⁱ`-output
distribution of `Ŝ` **conditioned on the MBO event `Aᵢ = 0`** equals the cumulative output distribution
of `T` (eq. (4.38)):

> `p^{Ŝ}_{Yⁱ | Xⁱ, Aᵢ=0}(yⁱ, xⁱ) = p^T_{Yⁱ | Xⁱ}(yⁱ, xⁱ)`.

Stated **cross-multiplied** (division-free), guarded by the two non-vanishing normalizers
(`massAfalse Ŝ xⁱ ≠ 0` and `massDom T xⁱ ≠ 0`):

> `massYAfalse Ŝ i yⁱ xⁱ · massDom T xⁱ = massY T i yⁱ xⁱ · massAfalse Ŝ xⁱ`,

which is equivalent to
`massYAfalse Ŝ i yⁱ xⁱ / massAfalse Ŝ xⁱ = massY T i yⁱ xⁱ / massDom T xⁱ`
wherever both denominators are nonzero — exactly the equality of the two conditional distributions, and
the cross-multiplied form is CR18 eq. (4.38) read at the unnormalized-mass level. No `DecidableEq`. -/
def CondEquiv (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) : Prop :=
  ∀ (i : ℕ) (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)),
    massAfalse Shat xs.toList ≠ 0 → massDom T xs.toList ≠ 0 →
      massYAfalse Shat i ys xs * massDom T xs.toList =
        massY T i ys xs * massAfalse Shat xs.toList

@[inherit_doc CondEquiv] scoped notation:50 Shat " |≡ " T => CondEquiv Shat T

/-! ### The `T`-side normalizer is `1` on Maurer's total systems -/

/-- On Maurer's total systems (every support realization accepts every nonempty history), the `T`-side
normalizer `massDom T xⁱ` is the full weight, hence `1` for a probability distribution: the conditioning
is vacuous on the histories under discussion. -/
theorem massDom_eq_weight_of_totalOnNonempty (T : PFunPDS X Y)
    (hTot : TotalOnNonempty T) {xs : List X} (hxs : xs ≠ []) :
    massDom T xs = T.weight := by
  classical
  unfold massDom Dist.mass Dist.weight
  refine Finsupp.sum_congr fun t ht => ?_
  rw [if_pos (hTot t ht xs hxs)]

/-- On Maurer's total systems, the `T`-side normalizer is `1` for a probability distribution `T`: the
conditioning event holds on all of support, so `massDom T xⁱ = |T| = 1`. -/
theorem massDom_eq_one_of_totalOnNonempty (T : PFunPDS X Y)
    (hT : T.isProbDist) (hTot : TotalOnNonempty T) {xs : List X} (hxs : xs ≠ []) :
    massDom T xs = 1 := by
  rw [massDom_eq_weight_of_totalOnNonempty T hTot hxs]; exact hT

end RandomSystems.CR18.CondEquiv
