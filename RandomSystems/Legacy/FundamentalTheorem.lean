/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Advantage
import RandomSystems.Coupling
import RandomSystems.Legacy.Successor
import RandomSystems.Legacy.AdvantageEquiv

/-!
# Fundamental Theorem: Δ = Adv

Lean 4 formalization of Theorem 1 from Lanzenberger-Maurer (TCC 2020).

## Main Results

* `delta_eq_advantage` — **Theorem 1**: Δ(S, T) = Adv(S, T)

## Proof Strategy

The proof proceeds by induction on the query count `q`:

**Base case** (q = 0): Both Δ and Adv are trivially 0.

**Inductive step** (q → q+1): Use the successor operation.
  1. Fix the first query input x. The advantage decomposes:
     Adv(S, T) = sup_x [δ of first output + Adv of successors]
  2. By induction, Adv(S^{↑x↓y}, T^{↑x↓y}) = Δ(S^{↑x↓y}, T^{↑x↓y})
  3. Combine using the partition lemma (Lemma 2) and coupling (Lemma 4)
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

section EasyDirection

variable {X Y : Type*} {q : ℕ}
  [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- **Adv ≤ Δ** (easy direction of Theorem 1).

For any S' ≡ S and T' ≡ T, by Lemma 3 (data processing inequality):
  δ(S', T') ≥ δ(tr(S', e), tr(T', e)) = δ(tr(S, e), tr(T, e))
for any environment e. Taking inf over S',T' and sup over e gives
  Δ(S, T) ≥ Adv(S, T).

Paper proof (p. 17): "Observe that Δ(S,T) ≥ Adv(S,T), since we have for any
environment e and any S' ∈ [S] and T' ∈ [T]:
  δ(S',T') ≥ δ(tr(S',e), tr(T',e)) = δ(tr(S,e), tr(T,e))." -/
theorem advantage_le_delta
    (S T : PDS X Y q) :
    advantage S T ≤ delta S T := by
  simp only [advantage, delta]
  apply Finset.sup_le
  intro inputs _
  apply le_csInf
  · exact ⟨_, S, T, PDS.equiv_refl S, PDS.equiv_refl T, rfl⟩
  · intro d ⟨S', T', hS, hT, hd⟩
    rw [← hd]
    calc statDist (S.transcriptDist inputs) (T.transcriptDist inputs)
        = statDist (S'.transcriptDist inputs) (T'.transcriptDist inputs) := by
          rw [hS inputs, hT inputs]
      _ ≤ statDist S'.dist T'.dist :=
          statDist_fTransform_le S'.dist T'.dist (fun s => DDS.transcript s inputs)

end EasyDirection

/-! ## Constructive direction: exists_equiv_achieving_advantage

The hard direction of Theorem 1 requires constructing, for any PDS S and T,
equivalent S' ≡ S and T' ≡ T with δ(S'.dist, T'.dist) = Adv(S, T).

The proof is by induction on q. Since q appears in type-class instances
(Fintype (DDS X Y q), etc.), we use `DDS.instFintype` which derives
the Fintype instance from `[Fintype X] [DecidableEq X] [Fintype Y]`
for any q. -/

/-- DDS X Y 0 is a subsingleton: with no queries, all DDS are equal. -/
private instance dds_zero_subsingleton {X Y : Type*} : Subsingleton (DDS X Y 0) :=
  ⟨fun s t => by ext i; exact Fin.elim0 i⟩

/-- Any function from a subsingleton type is injective. -/
private theorem injective_of_subsingleton {A B : Type*} [Subsingleton A]
    (f : A → B) : Function.Injective f :=
  fun _ _ _ => Subsingleton.elim _ _

/-- **Base case**: For q = 0, advantage S T = statDist S.dist T.dist.

All DDS X Y 0 are equal (no queries to distinguish). The transcript
function from DDS to transcripts is injective (trivially, from a
subsingleton), so fTransform preserves statDist exactly. -/
theorem exists_equiv_achieving_advantage_zero
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype (DDS X Y 0)]
    [Fintype (Transcript X Y 0)]
    [DecidableEq (Transcript X Y 0)]
    (S T : PDS X Y 0) :
    ∃ (S' : PDS X Y 0) (T' : PDS X Y 0),
      (S ≡ₚ S') ∧ (T ≡ₚ T') ∧ statDist S'.dist T'.dist = advantage S T := by
  refine ⟨S, T, PDS.equiv_refl S, PDS.equiv_refl T, ?_⟩
  simp only [advantage, PDS.transcriptDist]
  apply le_antisymm
  · apply Finset.le_sup_of_le (Finset.mem_univ Fin.elim0)
    rw [statDist_fTransform_injective S.dist T.dist _
      (injective_of_subsingleton _)]
  · apply Finset.sup_le; intro inputs _
    exact statDist_fTransform_le S.dist T.dist _

/-- Helper for `exists_equiv_achieving_advantage` with derived instances, suitable
for induction on q.

**Key construction**: For any PDS S and T, there exist equivalent
S' ≡ S and T' ≡ T such that δ(S'.dist, T'.dist) = Adv(S, T).

This is the constructive content of Theorem 1. The proof proceeds
by induction on q, using the successor operation and optimal coupling.

Paper proof (pp. 17-18): At each level, use the optimal coupling of the
successor systems (by IH) to reconstruct DDS distributions that achieve
the advantage as their statistical distance.

The inductive step requires:
1. Advantage decomposition via the successor partition (Lemma 2)
2. PDS reconstruction from optimal successor families (DDS.reconstruct)
3. Joint distribution construction from marginals (Lemma 6 of the paper) -/
private theorem exists_equiv_achieving_advantage_ind
    {X Y : Type*}
    [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (q : ℕ) (S T : @PDS X Y q DDS.instFintype) :
    ∃ (S' T' : @PDS X Y q DDS.instFintype),
      (S ≡ₚ S') ∧ (T ≡ₚ T') ∧ statDist S'.dist T'.dist = advantage S T := by
  induction q with
  | zero =>
    refine ⟨S, T, PDS.equiv_refl S, PDS.equiv_refl T, ?_⟩
    simp only [advantage, PDS.transcriptDist]
    apply le_antisymm
    · apply Finset.le_sup_of_le (Finset.mem_univ Fin.elim0)
      rw [statDist_fTransform_injective S.dist T.dist _
        (injective_of_subsingleton _)]
    · apply Finset.sup_le; intro inputs _
      exact statDist_fTransform_le S.dist T.dist _
  | succ n ih =>
    -- By IH, for each (x,y), get optimal successors
    have h_succ : ∀ (x : X) (y : Y),
        ∃ (S'xy T'xy : @PDS X Y n DDS.instFintype),
          (S.successor x y ≡ₚ S'xy) ∧ (T.successor x y ≡ₚ T'xy) ∧
          statDist S'xy.dist T'xy.dist =
            advantage (S.successor x y) (T.successor x y) :=
      fun x y => ih (S.successor x y) (T.successor x y)
    -- The construction from pp. 17-18 of the paper:
    -- 1. For each (x,y), let S_xy, T_xy be the optimal successors from h_succ
    -- 2. Prepend first query x→y to get S'_xy (q-query PDS)
    -- 3. Sum over y: S'_x := ∑_y S'_xy
    -- 4. Use Lemma 6 to combine into joint S'
    -- 5. Show δ(S', T') = max_x ∑_y δ(S_xy, T_xy)
    --    = max_x ∑_y advantage(S.successor x y, T.successor x y)
    --    = advantage S T  (by advantage decomposition)
    --
    -- This requires:
    -- a. PDS reconstruction from successor families
    -- b. Lemma 6 (joint distribution from marginals)
    -- c. Advantage decomposition: advantage S T = max_x ∑_y advantage(succ)
    --    (which itself uses the equivalence of adaptive/non-adaptive advantage)
    sorry

theorem exists_equiv_achieving_advantage
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (S T : @PDS X Y q DDS.instFintype) :
    ∃ (S' T' : @PDS X Y q DDS.instFintype),
      (S ≡ₚ S') ∧ (T ≡ₚ T') ∧ statDist S'.dist T'.dist = advantage S T :=
  exists_equiv_achieving_advantage_ind q S T

/-! ## Combining both directions -/

/-- **Δ ≤ Adv** (hard direction of Theorem 1).

Paper proof (pp. 17-18): By induction on q, construct S' ≡ S and T' ≡ T
such that δ(S', T') = sup_e δ(tr(S, e), tr(T, e)). -/
theorem delta_le_advantage
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (S T : @PDS X Y q DDS.instFintype) :
    delta S T ≤ advantage S T := by
  obtain ⟨S', T', hS, hT, hd⟩ := exists_equiv_achieving_advantage S T
  calc delta S T
      ≤ statDist S'.dist T'.dist := by
        apply csInf_le
        · exact ⟨0, fun _ ⟨_, _, _, _, hd⟩ => hd ▸ zero_le _⟩
        · exact ⟨S', T', hS, hT, rfl⟩
    _ = advantage S T := hd

/-- **Theorem 1**: Δ(S, T) = Adv(S, T).

The central result of Lanzenberger-Maurer (TCC 2020):
The infimum statistical distance over equivalent PDS representatives
equals the supremum distinguishing advantage over all environments.

This means one can prove indistinguishability by exhibiting a coupling
of deterministic systems, without reasoning about adaptive environments.

**Proof sketch** (by induction on q):
- q = 0: trivial
- q+1: decompose via successor operation, apply IH to each
  successor pair, recombine using the partition lemma -/
theorem delta_eq_advantage
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (S T : @PDS X Y q DDS.instFintype) :
    delta S T = advantage S T :=
  le_antisymm (delta_le_advantage S T) (advantage_le_delta S T)

end RandomSystems
