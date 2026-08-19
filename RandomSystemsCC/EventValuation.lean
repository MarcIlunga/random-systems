/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCrypto.EventAlgebra
import RandomSystems.Dist

/-!
# Event mass as a lattice valuation (GegMau26 §4.9, §5 item 3)

`AbstractCrypto.LatticeValuation` encodes GegMau26's proposal for "probability
beyond σ-algebras" — `m ⊥ = 0`, monotone, modular — and proves the transfer that
turns an order inequality between events into a numerical estimate.  Until now
it had **no instance**: nothing in either package exhibited a valuation, so the
transfer could not be applied to anything.

This module supplies the instance the RS side wants, `Dist.mass` on the event
lattice `A → Prop`, and restates the two transfers in `Dist.mass` vocabulary.

## What is actually used, which is not what the paper says

GegMau26 §4.9 justifies "`e ⪯ f ∨ g ⟹ Pr(e) ≤ Pr(f) + Pr(g)`" *by the
additivity of `Pr`*.  Additivity is not what the step needs and not what it
uses.  The step is **monotonicity** (`Dist.mass_mono`, which needs
`Dist.NonNeg`) followed by **finite sub-additivity** (`Dist.mass_or_le`, same
layer) — and sub-additivity is itself a strict weakening of additivity, obtained
from modularity by discarding the non-negative overlap term.  A genuinely
additive `Pr` is more than the inequality consumes; nothing below asks for one.

## Layer (`DESIGN.md` §12)

The `LatticeValuation` *bundle* sits at `Dist.NonNeg`, and only one of its three
fields is responsible: `map_bot` and `modular` (`Dist.mass_or_add_mass_and`) are
signed-layer identities, while `mono` fails on the signed carrier — a single
point of negative mass makes a larger event lighter.  No normalization is used
anywhere here, so a sub- or super-normalized non-negative law is a valuation
just as much as a probability distribution is; GegMau26's `m(⊤) = 1` is exactly
the field `AbstractCrypto.LatticeValuation` deliberately omits.

## Placement

`lakefile.lean` confines the AbstractCrypto dependency to `RandomSystemsCC/`,
so this bridge cannot live beside `Dist.mass` in `RandomSystems/`.  Its two
mathematical ingredients do live there, at their own tower level:
`Dist.mass_or_add_mass_and` (modularity, signed) and `Dist.mass_mono`
(`NonNeg`).  Only the wiring is here.

## References

* [B. Gegier, U. Maurer, *Event Algebras and Applications to Cryptography*,
  ePrint 2026/1071][GegMau26], §4.9 (the transfer), §5 item 3 (lattice
  valuations).
-/

namespace RandomSystemsCC.Events

open AbstractCrypto
open RandomSystems (Dist)

variable {A : Type*}

/-- **Event mass is a lattice valuation** (GegMau26 §5, item 3) on the event
lattice `A → Prop`, whose `⊥`/`⊓`/`⊔`/`≤` are falsity, conjunction, disjunction
and implication.

`Dist.NonNeg` is the weakest layer at which this is true, and it is
monotonicity that needs it: `map_bot` and `modular` hold for arbitrary signed
laws.  Normalization is not used — `AbstractCrypto.LatticeValuation` has no
`m ⊤ = 1` field, so sub-distributions qualify. -/
noncomputable def massValuation {X : Dist A} (hX : X.NonNeg) :
    LatticeValuation (A → Prop) ℝ where
  toFun := X.mass
  map_bot := Dist.mass_eq_zero_of_forall_not X (fun _ h => h)
  mono := fun _P _Q h => Dist.mass_mono hX fun a hp => h a hp
  modular := fun P Q => Dist.mass_or_add_mass_and X P Q

@[simp]
theorem massValuation_apply {X : Dist A} (hX : X.NonNeg) (P : A → Prop) :
    massValuation hX P = X.mass P :=
  rfl

/-- **The GegMau26 §4.9 transfer, in `Dist.mass` vocabulary**: an event implied
by a disjunction is charged at most the sum of the two disjuncts' masses.

The paper attributes this to additivity of `Pr`; what it uses is monotonicity
then finite sub-additivity, which is why `Dist.NonNeg` — and no normalization —
is the whole hypothesis.  The event hypothesis is an *order* inequality in the
event lattice, so an inequality proved abstractly in
`AbstractCrypto.EventAlgebra` discharges it directly. -/
theorem mass_le_add_of_le_sup {X : Dist A} (hX : X.NonNeg) {e f g : A → Prop}
    (h : e ≤ f ⊔ g) : X.mass e ≤ X.mass f + X.mass g :=
  (massValuation hX).le_add_of_le_sup h

/-- **The `Finset`-indexed GegMau26 transfer**, in `Dist.mass` vocabulary: an
event implied by a finite join is charged at most the sum of the joined events'
masses.

This is the shape the universal event inequalities of
`AbstractCrypto.EventAlgebra` (its Lemmas 3 and 4) are stated in — joins indexed
by a parameter set — so it is the form that turns one of them into a probability
estimate.  It differs from `Dist.mass_exists_le`, the tree's native `Finset`
union bound, in taking a lattice-order hypothesis rather than a pointwise
existential, which is precisely what makes an abstractly-proved event inequality
usable. -/
theorem mass_le_sum_of_le_finsetSup {ι : Type*} {X : Dist A} (hX : X.NonNeg)
    {s : Finset ι} {e : A → Prop} {f : ι → A → Prop} (h : e ≤ s.sup f) :
    X.mass e ≤ ∑ i ∈ s, X.mass (f i) :=
  (massValuation hX).le_sum_of_le_finsetSup h

end RandomSystemsCC.Events
