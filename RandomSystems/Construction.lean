/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Advantage
import RandomSystems.Equiv

/-!
# Constructions

Lean 4 formalization of Definition 13 from Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `Construction` — a map from n-tuples of PDS to a single PDS that
  respects equivalence

## Main Results

* `construction_advantage_bound` — hybrid argument: with a black-box reduction
  hypothesis, the advantage is bounded by the sum of component advantages
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- A construction: a map from n-tuples of PDS to a PDS that respects equivalence.

Paper Definition 13: C : PDS^n → PDS such that
  Sᵢ ≡ Sᵢ' for all i ⟹ C(S₁,...,Sₙ) ≡ C(S₁',...,Sₙ') -/
structure Construction
    {X' Y' : Type*} {q' : ℕ}
    [Fintype (DDS X' Y' q')]
    [Fintype (Transcript X' Y' q')]
    [DecidableEq (Transcript X' Y' q')]
    (n : ℕ) where
  /-- The construction map. -/
  apply : (Fin n → PDS X Y q) → PDS X' Y' q'
  /-- The construction respects equivalence. -/
  respects_equiv :
    ∀ (Ss Ts : Fin n → PDS X Y q),
    (∀ i, Ss i ≡ₚ Ts i) →
    apply Ss ≡ₚ apply Ts

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)] in
/-- Telescope inequality: d(0, n) ≤ ∑_{k<n} d(k, k+1) when d satisfies triangle inequality. -/
private lemma telescope_ineq
    (d : ℕ → ℕ → NNReal)
    (h_self : ∀ k, d k k = 0)
    (h_tri : ∀ a b c, d a c ≤ d a b + d b c) (n : ℕ) :
    d 0 n ≤ ∑ k ∈ Finset.range n, d k (k + 1) := by
  induction n with
  | zero => simp [h_self]
  | succ n ih =>
    calc d 0 (n + 1)
        ≤ d 0 n + d n (n + 1) := h_tri 0 n (n + 1)
      _ ≤ (∑ k ∈ Finset.range n, d k (k + 1)) + d n (n + 1) := by gcongr
      _ = ∑ k ∈ Finset.range (n + 1), d k (k + 1) :=
          (Finset.sum_range_succ _ n).symm

/-- The advantage of a construction is bounded by the sum of
component advantages, assuming a black-box reduction property.

  Adv(C(S₁,...,Sₙ), C(T₁,...,Tₙ)) ≤ ∑ᵢ Adv(Sᵢ, Tᵢ)

The proof uses the standard hybrid argument:
  H(k) := C(T₁,...,Tₖ, Sₖ₊₁,...,Sₙ)
  Adv(C(Ss), C(Ts)) ≤ ∑ₖ Adv(H(k), H(k+1)) ≤ ∑ₖ Adv(Sₖ, Tₖ) -/
theorem construction_advantage_bound
    {X' Y' : Type*} {q' : ℕ}
    [Fintype (DDS X' Y' q')]
    [Fintype (Transcript X' Y' q')]
    [DecidableEq (Transcript X' Y' q')]
    [Fintype X'] [Fintype X]
    {n : ℕ} (C : @Construction X Y q _ _ _ X' Y' q' _ _ _ n)
    (black_box_reduction : ∀ (i : Fin n) (ctx : Fin n → PDS X Y q)
      (S T : PDS X Y q),
      advantage (C.apply (Function.update ctx i S))
                (C.apply (Function.update ctx i T))
      ≤ advantage S T)
    (Ss Ts : Fin n → PDS X Y q) :
    advantage (C.apply Ss) (C.apply Ts) ≤
    ∑ i : Fin n, advantage (Ss i) (Ts i) := by
  -- Define hybrid: H(k) = C(T₁,...,Tₖ, Sₖ₊₁,...,Sₙ)
  let H : ℕ → PDS X' Y' q' := fun k =>
    C.apply (fun i : Fin n => if i.val < k then Ts i else Ss i)
  -- H(0) = C(Ss): definitional since ¬(i.val < 0) for Nat
  have h0 : H 0 = C.apply Ss := rfl
  -- H(n) = C(Ts): all i.val < n for Fin n
  have hn : H n = C.apply Ts := by
    show C.apply _ = C.apply Ts
    congr 1; funext ⟨i, hi⟩; simp [show i < n from hi]
  -- Each step: H(k) → H(k+1) replaces component k from Ss to Ts
  have h_step : ∀ k (hk : k < n),
      advantage (H k) (H (k + 1)) ≤ advantage (Ss ⟨k, hk⟩) (Ts ⟨k, hk⟩) := by
    intro k hk
    let ctx : Fin n → PDS X Y q :=
      fun i => if i.val < k then Ts i else Ss i
    -- H(k) = C(update ctx k (Ss k)): ctx already has Ss at position k
    have hHk : H k = C.apply (Function.update ctx ⟨k, hk⟩ (Ss ⟨k, hk⟩)) := by
      show C.apply ctx = C.apply (Function.update ctx ⟨k, hk⟩ (Ss ⟨k, hk⟩))
      congr 1
      have : ctx ⟨k, hk⟩ = Ss ⟨k, hk⟩ := by simp [ctx]
      rw [← this, Function.update_eq_self]
    -- H(k+1) = C(update ctx k (Ts k))
    have hHk1 : H (k + 1) = C.apply (Function.update ctx ⟨k, hk⟩ (Ts ⟨k, hk⟩)) := by
      show C.apply _ = C.apply (Function.update ctx ⟨k, hk⟩ (Ts ⟨k, hk⟩))
      congr 1; funext ⟨i, hi⟩
      simp only [Function.update_apply]
      by_cases hik : (⟨i, hi⟩ : Fin n) = ⟨k, hk⟩
      · -- i = k: LHS gives Ts (since k < k+1), RHS gives Ts via update
        have : i = k := Fin.mk.inj hik
        subst this; simp
      · -- i ≠ k: update doesn't change, compare if conditions
        simp only [hik, ite_false, ctx]
        have hne : i ≠ k := fun h => hik (Fin.ext h)
        by_cases h' : i < k
        · simp [h', show i < k + 1 by omega]
        · simp [h', show ¬(i < k + 1) by omega]
    rw [hHk, hHk1]
    exact black_box_reduction ⟨k, hk⟩ ctx _ _
  -- Bridge function for sum conversion
  let G : ℕ → NNReal := fun k =>
    if h : k < n then advantage (Ss ⟨k, h⟩) (Ts ⟨k, h⟩) else 0
  -- Telescope + step bounds + sum conversion
  calc advantage (C.apply Ss) (C.apply Ts)
      = advantage (H 0) (H n) := by rw [h0, hn]
    _ ≤ ∑ k ∈ Finset.range n, advantage (H k) (H (k + 1)) :=
        telescope_ineq (fun a b => advantage (H a) (H b))
          (fun k => advantage_self (H k))
          (fun a b c => advantage_triangle (H a) (H b) (H c)) n
    _ ≤ ∑ k ∈ Finset.range n, G k := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [G, dif_pos (Finset.mem_range.mp hk)]
        exact h_step k (Finset.mem_range.mp hk)
    _ = ∑ i : Fin n, advantage (Ss i) (Ts i) := by
        rw [Finset.sum_fin_eq_sum_range]

end RandomSystems
