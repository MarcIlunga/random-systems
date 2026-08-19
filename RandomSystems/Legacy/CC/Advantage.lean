/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.CC.Resource
import RandomSystems.Legacy.Advantage
import RandomSystems.Legacy.AdvantageEquiv

/-!
# Constructive Cryptography: Resource Advantage

Lean 4 formalization of the distinguishing advantage for CC resources,
lifting the PDS-level advantage (Definition 11) to multi-interface resources.

## Main Definitions

* `resourceAdvantage` — the advantage between two CC resources (max over interfaces)

## Main Results

* `resourceAdvantage_self` — Adv(R, R) = 0
* `resourceAdvantage_triangle` — triangle inequality
* `resourceAdvantage_respects_equiv` — well-defined on equivalence classes
* `compose_context_nonexpansive` — converter application doesn't amplify advantage

## Design Notes

The resource-level advantage is the maximum over all interfaces of the
per-interface PDS advantage. This corresponds to the CC metric where a
distinguisher chooses which interface to probe.

References:
- Maurer, "Constructive Cryptography — A New Paradigm" (2011), Section 2
- Maurer-Renner, "Abstract Cryptography" (2011), Definition 14
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

namespace CC

variable {n : ℕ}
  {X Y : Fin n → Type*} {q : Fin n → ℕ}
  [inst : ∀ i, Fintype (DDS (X i) (Y i) (q i))]
  [instT : ∀ i, Fintype (Transcript (X i) (Y i) (q i))]
  [instD : ∀ i, DecidableEq (Transcript (X i) (Y i) (q i))]
  [instX : ∀ i, Fintype (X i)]

/-- Per-interface advantage as a function. -/
def interfaceAdvantage
    (R S : CCResource X Y q) (i : Fin n) : NNReal :=
  advantage (R i) (S i)

/-- The distinguishing advantage between two CC resources.

This is the maximum over all interfaces of the per-interface advantage:
  Adv(R, S) := max_i Adv(Rᵢ, Sᵢ)

A distinguisher can probe any single interface, so the best
advantage is the best over all interfaces. -/
def resourceAdvantage
    (R S : CCResource X Y q) : NNReal :=
  Finset.sup Finset.univ (interfaceAdvantage R S)

/-- Each interface advantage is bounded by the resource advantage. -/
theorem interfaceAdvantage_le_resourceAdvantage
    (R S : CCResource X Y q) (i : Fin n) :
    interfaceAdvantage R S i ≤ resourceAdvantage R S :=
  Finset.le_sup (f := interfaceAdvantage R S) (Finset.mem_univ i)

/-- `Adv(R, R) = 0`. A resource is perfectly indistinguishable from itself. -/
theorem resourceAdvantage_self (R : CCResource X Y q) :
    resourceAdvantage R R = 0 := by
  simp only [resourceAdvantage]
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact le_of_eq (show interfaceAdvantage R R i = 0 from advantage_self (R i))
  · exact zero_le _

/-- The resource advantage respects resource equivalence.

If R ≡ᵣ R' and S ≡ᵣ S', then Adv(R, S) = Adv(R', S'). -/
theorem resourceAdvantage_respects_equiv
    {R R' S S' : CCResource X Y q}
    (hR : R ≡ᵣ R') (hS : S ≡ᵣ S') :
    resourceAdvantage R S = resourceAdvantage R' S' := by
  simp only [resourceAdvantage]
  congr 1; ext i
  exact_mod_cast advantage_respects_equiv (hR i) (hS i)

/-- Triangle inequality for resource advantage.

  Adv(R, U) ≤ Adv(R, S) + Adv(S, U) -/
theorem resourceAdvantage_triangle
    (R S U : CCResource X Y q) :
    resourceAdvantage R U ≤ resourceAdvantage R S + resourceAdvantage S U := by
  simp only [resourceAdvantage]
  apply Finset.sup_le
  intro i _
  have h_rs := interfaceAdvantage_le_resourceAdvantage R S i
  have h_su := interfaceAdvantage_le_resourceAdvantage S U i
  calc interfaceAdvantage R U i
      = advantage (R i) (U i) := rfl
    _ ≤ advantage (R i) (S i) + advantage (S i) (U i) :=
        advantage_triangle (R i) (S i) (U i)
    _ = interfaceAdvantage R S i + interfaceAdvantage S U i := rfl
    _ ≤ _ := add_le_add h_rs h_su

/-- A converter at interface `i` does not amplify the advantage.

  Adv(αⁱR, αⁱS) ≤ Adv(R, S)

This is the metric compatibility axiom (non-expansiveness):
converters can only reduce distinguishability, never increase it.

Maurer 2011, Definition 1: d(αⁱR, αⁱS) ≤ d(R, S). -/
theorem compose_context_nonexpansive
    (i : Fin n) (conv : Converter (X i) (Y i) (q i))
    (conv_nonexpansive : ∀ (S T : PDS (X i) (Y i) (q i)),
      advantage (conv.apply S) (conv.apply T) ≤ advantage S T)
    (R S : CCResource X Y q) :
    resourceAdvantage (applyConverter i conv R) (applyConverter i conv S) ≤
    resourceAdvantage R S := by
  simp only [resourceAdvantage]
  apply Finset.sup_le
  intro k _
  have h_orig := interfaceAdvantage_le_resourceAdvantage R S k
  show interfaceAdvantage (applyConverter i conv R) (applyConverter i conv S) k ≤ _
  simp only [interfaceAdvantage, applyConverter]
  by_cases hik : k = i
  · subst hik
    rw [Function.update_self, Function.update_self]
    calc advantage (conv.apply (R k)) (conv.apply (S k))
        ≤ advantage (R k) (S k) := conv_nonexpansive _ _
      _ ≤ _ := h_orig
  · rw [Function.update_of_ne hik, Function.update_of_ne hik]
    exact h_orig

/-- Transport a resource security bound across equivalence. -/
theorem transport_resource_security
    {R R' S S' : CCResource X Y q}
    (hR : R ≡ᵣ R') (hS : S ≡ᵣ S')
    {ε : NNReal} (h : resourceAdvantage R S ≤ ε) :
    resourceAdvantage R' S' ≤ ε := by
  rw [← resourceAdvantage_respects_equiv hR hS]
  exact h

end CC

end RandomSystems
