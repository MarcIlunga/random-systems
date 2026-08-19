/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepConverter

/-!
# The honest cascade equation (CR18 Definition 3.11 via Definition 3.9)

`cascadeViaConverter_eq_cascade` in `PFunConverter.lean` is `rfl` because its
LHS is *defined* as the native cascade — the "redefine the converter side to
force `rfl`" smell (DESIGN §10.1(2)).  This module proves the honest
statement: the cascade converter, presented as a Def 3.8 object and applied
by Def 3.9 to the paired-access system, **equals** the native DDS-level
cascade:

`(ofStep cascadeStep) ·ᶜ cascadeAccess S T  =  S ⊲ₚ T`.

The key structural observation: over the paired-access system the cascade
converter is *outer-memoryless* (fixed inner arity 2, no cross-round
memory), so it factors through `DDC.ofStep` and the realization theorem
`apply_ofStep` — the proof is a `driveG`/`driveOuter` computation against
`cascadeAccess`, not a transcript argument.
-/

namespace RandomSystems.CR18

namespace PFunConverter

open scoped PFunDDS

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The cascade converter's protocol, per round: forward the outer input to
the left system, feed its answer to the right system, answer the right
system's reply outside.  Total (as `ofStep` requires); the catch-all branch
covers answer shapes the paired-access system never produces. -/
def cascadeStep : X → List (Y ⊕ Z) → ((X ⊕ Y) ⊕ Z) := fun u ys =>
  match ys with
  | [] => Sum.inl (Sum.inl u)
  | [Sum.inl y] => Sum.inl (Sum.inr y)
  | [Sum.inl _, Sum.inr z] => Sum.inr z
  | _ => Sum.inl (Sum.inl u)

/-! ### `cascadeMiddle` bookkeeping -/

theorem cascadeMiddle_singleton (S : PFunDDS.DDS X Y) (x : X)
    (h : [x] ∈ PFunDDS.dom S) :
    PFunDDS.cascadeMiddle S [x] h = [PFunDDS.output S [x] h] := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    have hj : j = 0 := by
      simp only [PFunDDS.cascadeMiddle_length, List.length_singleton] at hj₁
      omega
    subst hj
    rw [PFunDDS.cascadeMiddle_getElem]
    simp only [List.getElem_cons_zero]
    exact PFunDDS.output_congr S (by simp) _ h

theorem cascadeMiddle_snoc (S : PFunDDS.DDS X Y) {l : List X} {x : X}
    (hl : l ∈ PFunDDS.dom S) (h : l ++ [x] ∈ PFunDDS.dom S) :
    PFunDDS.cascadeMiddle S (l ++ [x]) h
      = PFunDDS.cascadeMiddle S l hl ++ [PFunDDS.output S (l ++ [x]) h] := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    rw [PFunDDS.cascadeMiddle_getElem, List.getElem_append]
    split
    · rename_i hjl
      rw [PFunDDS.cascadeMiddle_getElem]
      refine PFunDDS.output_congr S ?_ _ _
      refine List.take_append_of_le_length ?_
      simp only [PFunDDS.cascadeMiddle_length] at hjl
      omega
    · rename_i hjl
      have hj : j = l.length := by
        simp only [PFunDDS.cascadeMiddle_length] at hjl
        simp only [PFunDDS.cascadeMiddle_length, List.length_append,
          List.length_singleton] at hj₁
        omega
      subst hj
      simp only [PFunDDS.cascadeMiddle_length, Nat.sub_self,
        List.getElem_cons_zero]
      refine PFunDDS.output_congr S ?_ _ _
      exact List.take_of_length_le (by simp)

/-! ### Evaluating the paired-access system -/

theorem cascadeLeftHistory_snoc_inl (p : List (X ⊕ Y)) (x : X) :
    cascadeLeftHistory (p ++ [Sum.inl x]) = cascadeLeftHistory p ++ [x] := by
  rw [cascadeLeftHistory_append]
  rfl

theorem cascadeLeftHistory_snoc_inr (p : List (X ⊕ Y)) (y : Y) :
    cascadeLeftHistory (p ++ [Sum.inr y]) = cascadeLeftHistory p := by
  rw [cascadeLeftHistory_append]
  simp [cascadeLeftHistory]

theorem cascadeRightHistory_snoc_inl (p : List (X ⊕ Y)) (x : X) :
    cascadeRightHistory (p ++ [Sum.inl x]) = cascadeRightHistory p := by
  rw [cascadeRightHistory_append]
  simp [cascadeRightHistory]

theorem cascadeRightHistory_snoc_inr (p : List (X ⊕ Y)) (y : Y) :
    cascadeRightHistory (p ++ [Sum.inr y]) = cascadeRightHistory p ++ [y] := by
  rw [cascadeRightHistory_append]
  rfl

/-- The paired-access system's value on a left query, as an equation. -/
theorem cascadeAccess_eval_inl (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ⊕ Y)} {x : X}
    (hp : p = [] ∨ p ∈ PFunDDS.dom (cascadeAccess S T))
    (hL : cascadeLeftHistory p ++ [x] ∈ PFunDDS.dom S) :
    (cascadeAccess S T).1 (p ++ [Sum.inl x])
      = Part.some (Sum.inl
          (PFunDDS.output S (cascadeLeftHistory p ++ [x]) hL)) := by
  have hlast : (p ++ [Sum.inl x]).getLast? = some (Sum.inl x) := by simp
  have hLfull : cascadeLeftHistory (p ++ [Sum.inl x]) ∈ PFunDDS.dom S := by
    rw [cascadeLeftHistory_snoc_inl]
    exact hL
  have hstep : cascadeAccessStep S T (p ++ [Sum.inl x]) := by
    simp only [cascadeAccessStep, hlast]
    exact hLfull
  have hdom : p ++ [Sum.inl x] ∈ PFunDDS.dom (cascadeAccess S T) :=
    cascadeAccess_dom_snoc S T hp hstep
  have hout := cascadeAccess_output_inl S T hdom hlast hLfull
  rw [← Part.some_get hdom]
  refine congrArg Part.some ?_
  refine hout.trans (congrArg Sum.inl ?_)
  exact PFunDDS.output_congr S (cascadeLeftHistory_snoc_inl p x) hLfull hL

/-- The paired-access system's value on a right query, as an equation. -/
theorem cascadeAccess_eval_inr (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ⊕ Y)} {y : Y}
    (hp : p = [] ∨ p ∈ PFunDDS.dom (cascadeAccess S T))
    (hR : cascadeRightHistory p ++ [y] ∈ PFunDDS.dom T) :
    (cascadeAccess S T).1 (p ++ [Sum.inr y])
      = Part.some (Sum.inr
          (PFunDDS.output T (cascadeRightHistory p ++ [y]) hR)) := by
  have hlast : (p ++ [Sum.inr y]).getLast? = some (Sum.inr y) := by simp
  have hRfull : cascadeRightHistory (p ++ [Sum.inr y]) ∈ PFunDDS.dom T := by
    rw [cascadeRightHistory_snoc_inr]
    exact hR
  have hstep : cascadeAccessStep S T (p ++ [Sum.inr y]) := by
    simp only [cascadeAccessStep, hlast]
    exact hRfull
  have hdom : p ++ [Sum.inr y] ∈ PFunDDS.dom (cascadeAccess S T) :=
    cascadeAccess_dom_snoc S T hp hstep
  have hout := cascadeAccess_output_inr S T hdom hlast hRfull
  rw [← Part.some_get hdom]
  refine congrArg Part.some ?_
  refine hout.trans (congrArg Sum.inr ?_)
  exact PFunDDS.output_congr T (cascadeRightHistory_snoc_inr p y) hRfull hR

/-- Membership destructor for a left query. -/
theorem cascadeAccess_mem_inl_elim (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ⊕ Y)} {x : X} {a : Y ⊕ Z}
    (ha : a ∈ (cascadeAccess S T).1 (p ++ [Sum.inl x])) :
    ∃ hL : cascadeLeftHistory p ++ [x] ∈ PFunDDS.dom S,
      a = Sum.inl (PFunDDS.output S (cascadeLeftHistory p ++ [x]) hL) := by
  have hdom : p ++ [Sum.inl x] ∈ PFunDDS.dom (cascadeAccess S T) :=
    Part.dom_iff_mem.mpr ⟨a, ha⟩
  have hlast : (p ++ [Sum.inl x]).getLast? = some (Sum.inl x) := by simp
  have hstep : cascadeAccessStep S T (p ++ [Sum.inl x]) :=
    hdom.2 (p ++ [Sum.inl x]) (by simp) (List.prefix_refl _)
  have hLfull : cascadeLeftHistory (p ++ [Sum.inl x]) ∈ PFunDDS.dom S := by
    simpa only [cascadeAccessStep, hlast] using hstep
  have hL : cascadeLeftHistory p ++ [x] ∈ PFunDDS.dom S := by
    rw [← cascadeLeftHistory_snoc_inl]
    exact hLfull
  refine ⟨hL, ?_⟩
  have hp' : p = [] ∨ p ∈ PFunDDS.dom (cascadeAccess S T) := by
    rcases List.eq_nil_or_concat p with rfl | ⟨p', a', rfl⟩
    · exact Or.inl rfl
    · right
      refine ⟨by simp, ?_⟩
      intro q hqne hq
      exact hdom.2 q hqne (hq.trans (List.prefix_append _ _))
  have hval : (cascadeAccess S T).1 (p ++ [Sum.inl x])
      = Part.some (Sum.inl
          (PFunDDS.output S (cascadeLeftHistory p ++ [x]) hL)) :=
    cascadeAccess_eval_inl S T hp' hL
  rw [hval, Part.mem_some_iff] at ha
  exact ha

/-- Membership destructor for a right query. -/
theorem cascadeAccess_mem_inr_elim (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ⊕ Y)} {y : Y} {a : Y ⊕ Z}
    (ha : a ∈ (cascadeAccess S T).1 (p ++ [Sum.inr y])) :
    ∃ hR : cascadeRightHistory p ++ [y] ∈ PFunDDS.dom T,
      a = Sum.inr (PFunDDS.output T (cascadeRightHistory p ++ [y]) hR) := by
  have hdom : p ++ [Sum.inr y] ∈ PFunDDS.dom (cascadeAccess S T) :=
    Part.dom_iff_mem.mpr ⟨a, ha⟩
  have hlast : (p ++ [Sum.inr y]).getLast? = some (Sum.inr y) := by simp
  have hstep : cascadeAccessStep S T (p ++ [Sum.inr y]) :=
    hdom.2 (p ++ [Sum.inr y]) (by simp) (List.prefix_refl _)
  have hRfull : cascadeRightHistory (p ++ [Sum.inr y]) ∈ PFunDDS.dom T := by
    simpa only [cascadeAccessStep, hlast] using hstep
  have hR : cascadeRightHistory p ++ [y] ∈ PFunDDS.dom T := by
    rw [← cascadeRightHistory_snoc_inr]
    exact hRfull
  refine ⟨hR, ?_⟩
  have hp' : p = [] ∨ p ∈ PFunDDS.dom (cascadeAccess S T) := by
    rcases List.eq_nil_or_concat p with rfl | ⟨p', a', rfl⟩
    · exact Or.inl rfl
    · right
      refine ⟨by simp, ?_⟩
      intro q hqne hq
      exact hdom.2 q hqne (hq.trans (List.prefix_append _ _))
  have hval : (cascadeAccess S T).1 (p ++ [Sum.inr y])
      = Part.some (Sum.inr
          (PFunDDS.output T (cascadeRightHistory p ++ [y]) hR)) :=
    cascadeAccess_eval_inr S T hp' hR
  rw [hval, Part.mem_some_iff] at ha
  exact ha

/-! ### One cascade round -/

/-- One cascade round, computed: query left, feed the answer right, exit with
the right answer; the inner history grows by the woven pair. -/
theorem driveG_cascadeStep_round (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {xs : List (X ⊕ Y)} {u : X}
    (hxs : xs = [] ∨ xs ∈ PFunDDS.dom (cascadeAccess S T))
    (hL : cascadeLeftHistory xs ++ [u] ∈ PFunDDS.dom S)
    (hT : cascadeRightHistory xs ++
        [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL] ∈ PFunDDS.dom T)
    (n : ℕ) :
    CausalApply.driveG (cascadeStep u) (cascadeAccess S T).1 (n + 1 + 1 + 1)
        xs []
      = Part.some
          (PFunDDS.output T (cascadeRightHistory xs ++
            [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL]) hT,
           xs ++ [Sum.inl u,
             Sum.inr (PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL)]) := by
  have h1 := cascadeAccess_eval_inl S T hxs hL
  have hdom₁ : xs ++ [Sum.inl u] ∈ PFunDDS.dom (cascadeAccess S T) := by
    rw [PFunDDS.dom_def, PFun.mem_dom]
    exact ⟨_, by rw [h1]; exact Part.mem_some _⟩
  have hR₁ : cascadeRightHistory (xs ++ [Sum.inl u]) ++
      [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL] ∈ PFunDDS.dom T := by
    rw [cascadeRightHistory_snoc_inl]
    exact hT
  have h2 := cascadeAccess_eval_inr S T (p := xs ++ [Sum.inl u])
    (Or.inr hdom₁) hR₁
  show ((cascadeAccess S T).1 (xs ++ [Sum.inl u])).bind
      (fun y => CausalApply.driveG (cascadeStep u) (cascadeAccess S T).1
        (n + 1 + 1) (xs ++ [Sum.inl u]) ([] ++ [y])) = _
  rw [h1, Part.bind_some]
  show ((cascadeAccess S T).1 ((xs ++ [Sum.inl u]) ++
      [Sum.inr (PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL)])).bind
      (fun y => CausalApply.driveG (cascadeStep u) (cascadeAccess S T).1
        (n + 1) ((xs ++ [Sum.inl u]) ++
          [Sum.inr (PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL)])
        ([Sum.inl (PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL)]
          ++ [y])) = _
  rw [h2, Part.bind_some]
  show Part.some (_, (xs ++ [Sum.inl u]) ++ [_]) = _
  rw [List.append_assoc]
  refine congrArg Part.some (Prod.ext ?_ rfl)
  exact PFunDDS.output_congr T (by rw [cascadeRightHistory_snoc_inl]) hR₁ hT

/-- One cascade round, destructed. -/
theorem driveG_cascadeStep_elim (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {u : X} {xs : List (X ⊕ Y)} {fuel : ℕ} {p : Z × List (X ⊕ Y)}
    (hp : p ∈ CausalApply.driveG (cascadeStep u) (cascadeAccess S T).1 fuel
      xs []) :
    ∃ (hL : cascadeLeftHistory xs ++ [u] ∈ PFunDDS.dom S)
      (hT : cascadeRightHistory xs ++
        [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL] ∈ PFunDDS.dom T),
      p = (PFunDDS.output T (cascadeRightHistory xs ++
            [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL]) hT,
           xs ++ [Sum.inl u,
             Sum.inr (PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL)]) := by
  rcases fuel with _ | fuel
  · simp [CausalApply.driveG] at hp
  · simp only [CausalApply.driveG, cascadeStep] at hp
    rw [Part.mem_bind_iff] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    obtain ⟨hL, rfl⟩ := cascadeAccess_mem_inl_elim S T ha₁
    simp only [List.nil_append] at hp
    rcases fuel with _ | fuel
    · simp [CausalApply.driveG] at hp
    · simp only [CausalApply.driveG, cascadeStep] at hp
      rw [Part.mem_bind_iff] at hp
      obtain ⟨a₂, ha₂, hp⟩ := hp
      obtain ⟨hR₁, rfl⟩ := cascadeAccess_mem_inr_elim S T ha₂
      have hT : cascadeRightHistory xs ++
          [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hL]
            ∈ PFunDDS.dom T := by
        rw [← cascadeRightHistory_snoc_inl (p := xs) (x := u)]
        exact hR₁
      rcases fuel with _ | fuel
      · simp [CausalApply.driveG] at hp
      · simp only [CausalApply.driveG, cascadeStep,
          List.cons_append, List.nil_append, Part.mem_some_iff] at hp
        refine ⟨hL, hT, ?_⟩
        rw [hp]
        refine Prod.ext ?_ (by simp [List.append_assoc])
        exact PFunDDS.output_congr T
          (by rw [cascadeRightHistory_snoc_inl]) hR₁ hT

/-! ### The outer fold and the honest cascade equation -/

/-- Generalized snoc for `cascadeMiddle`, absorbing the empty-prefix case. -/
theorem cascadeMiddle_snoc' (S : PFunDDS.DDS X Y) {l : List X} {x : X}
    (hl : l ∈ PFunDDS.dom S ∨ l = []) (h : l ++ [x] ∈ PFunDDS.dom S)
    (prev : List Y)
    (hprev : ∀ hd : l ∈ PFunDDS.dom S, prev = PFunDDS.cascadeMiddle S l hd)
    (hprevnil : l = [] → prev = []) :
    PFunDDS.cascadeMiddle S (l ++ [x]) h
      = prev ++ [PFunDDS.output S (l ++ [x]) h] := by
  rcases hl with hd | hnil
  · rw [hprev hd, ← cascadeMiddle_snoc S hd h]
  · subst hnil
    rw [hprevnil rfl]
    simp only [List.nil_append] at h ⊢
    exact cascadeMiddle_singleton S x h

theorem append_pair_eq (xs : List (X ⊕ Y)) (a b : X ⊕ Y) :
    xs ++ [a, b] = (xs ++ [a]) ++ [b] := by
  simp

/-- Forward run of the cascade converter over a whole outer history. -/
theorem driveOuter_cascadeStep_of_dom (S : PFunDDS.DDS X Y)
    (T : PFunDDS.DDS Y Z) :
    ∀ (rest : List X) (xs : List (X ⊕ Y)),
      (xs = [] ∨ xs ∈ PFunDDS.dom (cascadeAccess S T)) →
      (cascadeLeftHistory xs ∈ PFunDDS.dom S ∨ cascadeLeftHistory xs = []) →
      (∀ h : cascadeLeftHistory xs ∈ PFunDDS.dom S,
        cascadeRightHistory xs
          = PFunDDS.cascadeMiddle S (cascadeLeftHistory xs) h) →
      (cascadeLeftHistory xs = [] → cascadeRightHistory xs = []) →
      ((∃ hS : cascadeLeftHistory xs ++ rest ∈ PFunDDS.dom S,
          PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS
            ∈ PFunDDS.dom T) ∨ rest = []) →
      ∃ vs xs',
        (vs, xs') ∈ CausalApply.driveOuter cascadeStep
          (cascadeAccess S T).1 3 xs rest ∧
        ∀ (hS : cascadeLeftHistory xs ++ rest ∈ PFunDDS.dom S)
          (hT : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS
            ∈ PFunDDS.dom T),
          rest ≠ [] →
            vs.getLast? = some (PFunDDS.output T
              (PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS) hT) := by
  intro rest
  induction rest with
  | nil =>
      intro xs _ _ _ _ _
      exact ⟨[], xs, by simp [CausalApply.driveOuter],
        fun _ _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs hxs hSpre hRinv hRnil hfull
      obtain ⟨hSfull, hTfull⟩ : ∃ hS : cascadeLeftHistory xs ++ u :: rest
          ∈ PFunDDS.dom S,
          PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ u :: rest) hS
            ∈ PFunDDS.dom T := by
        rcases hfull with h | h
        · exact h
        · exact absurd h (by simp)
      have hS₁ : cascadeLeftHistory xs ++ [u] ∈ PFunDDS.dom S :=
        PFunDDS.prefix_closed S ⟨rest, by simp⟩ (by simp) hSfull
      have hT₁ : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          ∈ PFunDDS.dom T :=
        PFunDDS.prefix_closed T
          (PFunDDS.cascadeMiddle_prefix S hS₁ hSfull ⟨rest, by simp⟩)
          (PFunDDS.cascadeMiddle_ne_nil S _ hS₁) hTfull
      have hmid : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          = cascadeRightHistory xs
            ++ [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hS₁] :=
        cascadeMiddle_snoc' S hSpre hS₁ _ hRinv hRnil
      have hTround : cascadeRightHistory xs
          ++ [PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hS₁]
            ∈ PFunDDS.dom T := by
        rw [← hmid]
        exact hT₁
      set y₁ := PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hS₁ with hy₁
      set xs' := xs ++ [Sum.inl u, Sum.inr y₁] with hxs'def
      have hround := driveG_cascadeStep_round S T hxs hS₁ hTround 0
      -- domain of the extended access history
      have hstep₁ : cascadeAccessStep S T (xs ++ [Sum.inl u]) := by
        simp only [cascadeAccessStep,
          show (xs ++ [Sum.inl u]).getLast? = some (Sum.inl u) from by simp]
        rw [cascadeLeftHistory_snoc_inl]
        exact hS₁
      have hdom₁ : xs ++ [Sum.inl u] ∈ PFunDDS.dom (cascadeAccess S T) :=
        cascadeAccess_dom_snoc S T hxs hstep₁
      have hstep₂ : cascadeAccessStep S T ((xs ++ [Sum.inl u]) ++ [Sum.inr y₁]) := by
        simp only [cascadeAccessStep,
          show ((xs ++ [Sum.inl u]) ++ [Sum.inr y₁]).getLast?
            = some (Sum.inr y₁) from by simp]
        rw [cascadeRightHistory_snoc_inr, cascadeRightHistory_snoc_inl]
        exact hTround
      have hdomxs' : xs' ∈ PFunDDS.dom (cascadeAccess S T) := by
        rw [hxs'def, append_pair_eq]
        exact cascadeAccess_dom_snoc S T (Or.inr hdom₁) hstep₂
      -- invariants at the extended history
      have hLxs' : cascadeLeftHistory xs' = cascadeLeftHistory xs ++ [u] := by
        rw [hxs'def, append_pair_eq, cascadeLeftHistory_snoc_inr,
          cascadeLeftHistory_snoc_inl]
      have hRxs' : cascadeRightHistory xs' = cascadeRightHistory xs ++ [y₁] := by
        rw [hxs'def, append_pair_eq, cascadeRightHistory_snoc_inr,
          cascadeRightHistory_snoc_inl]
      have hSpre' : cascadeLeftHistory xs' ∈ PFunDDS.dom S
          ∨ cascadeLeftHistory xs' = [] := by
        rw [hLxs']
        exact Or.inl hS₁
      have hRinv' : ∀ h : cascadeLeftHistory xs' ∈ PFunDDS.dom S,
          cascadeRightHistory xs'
            = PFunDDS.cascadeMiddle S (cascadeLeftHistory xs') h := by
        intro h
        rw [hRxs', ← hmid]
        exact PFunDDS.cascadeMiddle_congr S hLxs'.symm hS₁ h
      have hRnil' : cascadeLeftHistory xs' = [] → cascadeRightHistory xs' = [] := by
        intro h
        rw [hLxs'] at h
        exact absurd h (by simp)
      have hlist : cascadeLeftHistory xs' ++ rest
          = cascadeLeftHistory xs ++ u :: rest := by
        rw [hLxs', List.append_assoc]
        rfl
      have hSfull' : cascadeLeftHistory xs' ++ rest ∈ PFunDDS.dom S := by
        rw [hlist]
        exact hSfull
      have hfull' : (∃ hS : cascadeLeftHistory xs' ++ rest ∈ PFunDDS.dom S,
          PFunDDS.cascadeMiddle S (cascadeLeftHistory xs' ++ rest) hS
            ∈ PFunDDS.dom T) ∨ rest = [] := by
        refine Or.inl ⟨hSfull', ?_⟩
        rw [PFunDDS.cascadeMiddle_congr S hlist hSfull' hSfull]
        exact hTfull
      obtain ⟨vs', xs'', hmem', hlast'⟩ :=
        ih xs' (Or.inr hdomxs') hSpre' hRinv' hRnil' hfull'
      refine ⟨PFunDDS.output T (cascadeRightHistory xs ++ [y₁]) hTround :: vs',
        xs'', ?_, ?_⟩
      · show _ ∈ (CausalApply.driveG (cascadeStep u) (cascadeAccess S T).1 3
            xs []).bind _
        rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, hround, Part.bind_some]
        rw [Part.mem_map_iff]
        exact ⟨(vs', xs''), hmem', rfl⟩
      · intro hS hT hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := CausalApply.driveOuter_length cascadeStep
                (cascadeAccess S T).1 3 xs' rest hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
            refine congrArg some ?_
            refine PFunDDS.output_congr T ?_ hTround hT
            rw [← hmid]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := CausalApply.driveOuter_length cascadeStep
                (cascadeAccess S T).1 3 xs' rest hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have hS' : cascadeLeftHistory xs' ++ rest ∈ PFunDDS.dom S :=
              hSfull'
            have hT' : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs' ++ rest)
                hS' ∈ PFunDDS.dom T := by
              rw [PFunDDS.cascadeMiddle_congr S hlist hS' hSfull]
              exact hTfull
            have hlast'' := hlast' hS' hT' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            refine congrArg some ?_
            refine PFunDDS.output_congr T ?_ hT' hT
            exact PFunDDS.cascadeMiddle_congr S hlist hS' hS

/-- Backward run analysis of the cascade converter. -/
theorem driveOuter_cascadeStep_mem_imp (S : PFunDDS.DDS X Y)
    (T : PFunDDS.DDS Y Z) :
    ∀ (rest : List X) (xs : List (X ⊕ Y)) {fuel : ℕ}
      {r : List Z × List (X ⊕ Y)},
      (cascadeLeftHistory xs ∈ PFunDDS.dom S ∨ cascadeLeftHistory xs = []) →
      (∀ h : cascadeLeftHistory xs ∈ PFunDDS.dom S,
        cascadeRightHistory xs
          = PFunDDS.cascadeMiddle S (cascadeLeftHistory xs) h) →
      (cascadeLeftHistory xs = [] → cascadeRightHistory xs = []) →
      r ∈ CausalApply.driveOuter cascadeStep (cascadeAccess S T).1 fuel xs rest →
      rest ≠ [] →
      ∃ (hS : cascadeLeftHistory xs ++ rest ∈ PFunDDS.dom S)
        (hT : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS
          ∈ PFunDDS.dom T),
        r.1.getLast? = some (PFunDDS.output T
          (PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS) hT) := by
  intro rest
  induction rest with
  | nil =>
      intro xs fuel r _ _ _ _ hne
      exact absurd rfl hne
  | cons u rest ih =>
      intro xs fuel r hSpre hRinv hRnil hr _
      simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hS₁, hTround, rfl⟩ := driveG_cascadeStep_elim S T hr₁
      set y₁ := PFunDDS.output S (cascadeLeftHistory xs ++ [u]) hS₁ with hy₁
      set xs' := xs ++ [Sum.inl u, Sum.inr y₁] with hxs'def
      have hmid : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          = cascadeRightHistory xs ++ [y₁] :=
        cascadeMiddle_snoc' S hSpre hS₁ _ hRinv hRnil
      have hT₁ : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          ∈ PFunDDS.dom T := by
        rw [hmid]
        exact hTround
      have hLxs' : cascadeLeftHistory xs' = cascadeLeftHistory xs ++ [u] := by
        rw [hxs'def, append_pair_eq, cascadeLeftHistory_snoc_inr,
          cascadeLeftHistory_snoc_inl]
      have hRxs' : cascadeRightHistory xs' = cascadeRightHistory xs ++ [y₁] := by
        rw [hxs'def, append_pair_eq, cascadeRightHistory_snoc_inr,
          cascadeRightHistory_snoc_inl]
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [CausalApply.driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨hS₁, hT₁, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some ?_
          refine PFunDDS.output_congr T hmid.symm hTround hT₁
      | cons r0 rs0 =>
          have hSpre' : cascadeLeftHistory xs' ∈ PFunDDS.dom S
              ∨ cascadeLeftHistory xs' = [] := by
            rw [hLxs']
            exact Or.inl hS₁
          have hRinv' : ∀ h : cascadeLeftHistory xs' ∈ PFunDDS.dom S,
              cascadeRightHistory xs'
                = PFunDDS.cascadeMiddle S (cascadeLeftHistory xs') h := by
            intro h
            rw [hRxs', ← hmid]
            exact PFunDDS.cascadeMiddle_congr S hLxs'.symm hS₁ h
          have hRnil' : cascadeLeftHistory xs' = []
              → cascadeRightHistory xs' = [] := by
            intro h
            rw [hLxs'] at h
            exact absurd h (by simp)
          obtain ⟨hS', hT', hlast'⟩ :=
            ih xs' hSpre' hRinv' hRnil' hrr (by simp [hrest])
          have hlist : cascadeLeftHistory xs' ++ rest
              = cascadeLeftHistory xs ++ u :: rest := by
            rw [hLxs', List.append_assoc]
            rfl
          have hS : cascadeLeftHistory xs ++ u :: rest ∈ PFunDDS.dom S := by
            rw [← hlist]
            exact hS'
          have hT : PFunDDS.cascadeMiddle S (cascadeLeftHistory xs ++ u :: rest)
              hS ∈ PFunDDS.dom T := by
            rw [← PFunDDS.cascadeMiddle_congr S hlist hS' hS]
            exact hT'
          rw [← hrest]
          refine ⟨hS, hT, ?_⟩
          have hlenrr := CausalApply.driveOuter_length cascadeStep
            (cascadeAccess S T).1 fuel xs' rest hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              refine congrArg some ?_
              refine PFunDDS.output_congr T ?_ hT' hT
              exact PFunDDS.cascadeMiddle_congr S hlist hS' hS

/-- Membership characterization of the native cascade. -/
theorem mem_cascade_iff (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    (l : List X) (z : Z) :
    z ∈ (PFunDDS.cascade S T).1 l ↔
      ∃ (hS : l ∈ PFunDDS.dom S)
        (hT : PFunDDS.cascadeMiddle S l hS ∈ PFunDDS.dom T),
        z = PFunDDS.output T (PFunDDS.cascadeMiddle S l hS) hT := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.choose, h.choose_spec, rfl⟩
  · rintro ⟨hS, hT, rfl⟩
    refine ⟨⟨hS, hT⟩, ?_⟩
    exact PFunDDS.output_congr T
      (PFunDDS.cascadeMiddle_congr S rfl _ hS) _ hT

/-- **The honest cascade equation (CR18 Def 3.11 via Def 3.9).**  The cascade
converter, as a Def 3.8 object applied by Def 3.9 to the paired-access
system, *is* the native DDS-level cascade — replacing the `rfl`-by-definition
`cascadeViaConverter_eq_cascade` with a genuine converter equation. -/
theorem apply_cascadeStep (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z) :
    DDC.apply (DDC.ofStep (cascadeStep (X := X) (Y := Y) (Z := Z)))
        (cascadeAccess S T)
      = PFunDDS.cascade S T := by
  rw [show DDC.apply (DDC.ofStep (cascadeStep (X := X) (Y := Y) (Z := Z)))
      (cascadeAccess S T)
    = CausalApply.applyG cascadeStep (cascadeAccess S T).1 from
    DDC.apply_ofStep _ _]
  apply Subtype.ext
  funext us
  apply Part.ext
  intro z
  rw [CausalApply.applyG_toPFun, CausalApply.mem_applyRaw, mem_cascade_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := CausalApply.driveOuter_length cascadeStep
        (cascadeAccess S T).1 fuel [] [] hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨hS, hT, hout⟩ := driveOuter_cascadeStep_mem_imp S T us []
      (Or.inr rfl) (fun h => absurd h (PFunDDS.empty_not_mem S))
      (fun _ => rfl) hr hne
    rw [hlast] at hout
    have hz := Option.some.inj hout
    refine ⟨by simpa [cascadeLeftHistory] using hS, ?_, ?_⟩
    · rw [← PFunDDS.cascadeMiddle_congr S
        (by simp [cascadeLeftHistory] : cascadeLeftHistory
          ([] : List (X ⊕ Y)) ++ us = us) hS _]
      exact hT
    · rw [hz]
      refine PFunDDS.output_congr T ?_ hT _
      exact PFunDDS.cascadeMiddle_congr S (by simp [cascadeLeftHistory]) hS _
  · rintro ⟨hS, hT, rfl⟩
    have hne : us ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem S hS
    have hS0 : cascadeLeftHistory ([] : List (X ⊕ Y)) ++ us
        ∈ PFunDDS.dom S := by
      simpa [cascadeLeftHistory] using hS
    have hT0 : PFunDDS.cascadeMiddle S
        (cascadeLeftHistory ([] : List (X ⊕ Y)) ++ us) hS0
          ∈ PFunDDS.dom T := by
      rw [PFunDDS.cascadeMiddle_congr S
        (by simp [cascadeLeftHistory]) hS0 hS]
      exact hT
    obtain ⟨vs, xs', hmem, hlast⟩ := driveOuter_cascadeStep_of_dom S T us []
      (Or.inl rfl) (Or.inr rfl) (fun h => absurd h (PFunDDS.empty_not_mem S))
      (fun _ => rfl) (Or.inl ⟨hS0, hT0⟩)
    refine ⟨3, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    refine ⟨(vs, xs'), hmem, ?_⟩
    rw [hlast hS0 hT0 hne]
    refine congrArg some ?_
    refine PFunDDS.output_congr T ?_ hT0 hT
    exact PFunDDS.cascadeMiddle_congr S (by simp [cascadeLeftHistory]) hS0 hS

end PFunConverter

end RandomSystems.CR18
