/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Advantage
import RandomSystems.Legacy.Equiv

/-!
# Advantage/Delta lemmas depending on PDS equivalence

These advantage results genuinely depend on `RandomSystems.Equiv` (the `≡ₚ`
relation): `delta` (the infimum statistical distance over equivalent pairs) and
the equivalence-transport lemmas.  They were split out of `Advantage.lean` so the
core advantage definitions (`advantage`, `advantageAdaptive`, their triangle and
pointwise lemmas) do **not** depend on `Equiv` — consumers that need only the core
advantage (e.g. the HCTR2 `Concrete` proof tree) then do not pull `Equiv` onto
their import path.

Moved verbatim from `Advantage.lean`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- The advantage respects PDS equivalence: if S ≡ S' and T ≡ T',
then Adv(S, T) = Adv(S', T').

This is why advantage is well-defined on random systems. -/
theorem advantage_respects_equiv [Fintype X]
    {S S' T T' : PDS X Y q}
    (hS : S ≡ₚ S') (hT : T ≡ₚ T') :
    advantage S T = advantage S' T' := by
  simp only [advantage]
  congr 1
  ext inputs
  rw [hS inputs, hT inputs]

/-- The infimum statistical distance (Delta) between two PDS.

Paper Definition 12:
  Δ(S, T) := inf_{S'≡S, T'≡T} δ(S'.dist, T'.dist)

We use `sInf` over the set of values, avoiding the need for
`Fintype (PDS X Y q)` or decidability of equivalence. -/
def delta (S T : PDS X Y q) : NNReal :=
  sInf { d : NNReal | ∃ (S' : PDS X Y q) (T' : PDS X Y q),
    (S ≡ₚ S') ∧ (T ≡ₚ T') ∧ statDist S'.dist T'.dist = d }

/-- Δ(S, T) ≤ δ(S.dist, T.dist) — the trivial representative.

Taking S' = S and T' = T gives this bound. -/
theorem delta_le_statDist (S T : PDS X Y q) :
    delta S T ≤ statDist S.dist T.dist := by
  apply csInf_le
  · exact ⟨0, fun _ ⟨_, _, _, _, hd⟩ => hd ▸ zero_le _⟩
  · exact ⟨S, T, PDS.equiv_refl S, PDS.equiv_refl T, rfl⟩

/-- Δ(S, S) = 0 — a system has zero delta with itself. -/
theorem delta_self (S : PDS X Y q) : delta S S = 0 := by
  apply le_antisymm
  · calc delta S S ≤ statDist S.dist S.dist := delta_le_statDist S S
    _ = 0 := statDist_self S.dist
  · exact zero_le _

/-- Transport a security bound across equivalence.

If `Adv(S, T) ≤ ε` and `S ≡ S'`, `T ≡ T'`, then `Adv(S', T') ≤ ε`. -/
theorem transport_security_bound [Fintype X]
    {S S' T T' : PDS X Y q}
    (hS : S ≡ₚ S') (hT : T ≡ₚ T')
    {ε : NNReal} (h : advantage S T ≤ ε) :
    advantage S' T' ≤ ε := by
  rw [← advantage_respects_equiv hS hT]
  exact h

end RandomSystems
