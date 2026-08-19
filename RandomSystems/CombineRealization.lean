/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepConverter

/-!
# The honest output-combine equation (CR18 Definition 3.12 via Definition 3.9)

Companion to `CascadeRealization.lean`, closing DESIGN §10.1(2) for the
`comb⋆` converter: the output-combine converter, presented as a Def 3.8
object and applied by Def 3.9 to the parallel of the two systems, **equals**
the native DDS-level combine:

`(ofStep (combineStep op)) ·ᶜ [pair S T]ₚ  =  S ⋆ₚ[op] T`.

Per round the converter queries both components with the outer input and
answers the combined outputs — fixed arity 2, outer-memoryless, so it
factors through `apply_ofStep` and the proof is a `driveG` computation
against `parallel (Combine.pair S T)`.
-/

namespace RandomSystems.CR18

namespace PFunConverter

open scoped PFunDDS

universe u v

variable {X : Type u} {Y : Type v}

@[simp] theorem pair_zero (S T : PFunDDS.DDS X Y) :
    Combine.pair S T 0 = S := by
  simp [Combine.pair]

@[simp] theorem pair_one (S T : PFunDDS.DDS X Y) :
    Combine.pair S T 1 = T := by
  simp [Combine.pair]

/-- The combine converter's protocol, per round: query the left component,
query the right component, answer the combined outputs.  Total; the
catch-all branch is junk the parallel access never produces. -/
def combineStep (op : Y → Y → Y) :
    X → List (Σ _ : Fin 2, Y) → (Σ _ : Fin 2, X) ⊕ Y := fun x ys =>
  match ys with
  | [] => Sum.inl ⟨0, x⟩
  | [_] => Sum.inl ⟨1, x⟩
  | a :: b :: _ => Sum.inr (op a.2 b.2)

/-! ### Evaluating the parallel access system -/

/-- The parallel system's value on a tagged query, as an equation. -/
theorem pairAccess_eval (S T : PFunDDS.DDS X Y) (i : Fin 2)
    {h : List (Σ _ : Fin 2, X)} {x : X}
    (hp : h = [] ∨ h ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)))
    (hd : PFunDDS.restrict i h ++ [x] ∈ PFunDDS.dom (Combine.pair S T i)) :
    (PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨i, x⟩])
      = Part.some ⟨i, PFunDDS.output (Combine.pair S T i)
          (PFunDDS.restrict i h ++ [x]) hd⟩ := by
  have hdom : h ++ [⟨i, x⟩]
      ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)) := by
    refine ⟨by simp, ?_⟩
    intro j
    by_cases hji : j = i
    · subst hji
      rw [PFunDDS.restrict_concat_self]
      exact Or.inr hd
    · rw [PFunDDS.restrict_concat_ne (fun hij => hji hij.symm)]
      rcases hp with rfl | hpd
      · exact Or.inl (PFunDDS.restrict_nil j)
      · exact hpd.2 j
  have hlast : (h ++ [(⟨i, x⟩ : Σ _ : Fin 2, X)]).getLast?
      = some ⟨i, x⟩ := by simp
  have hout := PFunDDS.parallel_output (Combine.pair S T) _ hdom hlast
  rw [← Part.some_get hdom]
  refine congrArg Part.some ?_
  refine hout.trans ?_
  refine congrArg (Sigma.mk i) ?_
  exact PFunDDS.output_congr _ (PFunDDS.restrict_concat_self i x h) _ hd

/-- Membership destructor for a tagged query. -/
theorem pairAccess_mem_elim (S T : PFunDDS.DDS X Y) (i : Fin 2)
    {h : List (Σ _ : Fin 2, X)} {x : X} {a : Σ _ : Fin 2, Y}
    (ha : a ∈ (PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨i, x⟩])) :
    ∃ hd : PFunDDS.restrict i h ++ [x] ∈ PFunDDS.dom (Combine.pair S T i),
      a = ⟨i, PFunDDS.output (Combine.pair S T i)
        (PFunDDS.restrict i h ++ [x]) hd⟩ := by
  have hdom : h ++ [⟨i, x⟩]
      ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)) :=
    Part.dom_iff_mem.mpr ⟨a, ha⟩
  have hd : PFunDDS.restrict i h ++ [x]
      ∈ PFunDDS.dom (Combine.pair S T i) := by
    rcases hdom.2 i with hempty | hdomi
    · exfalso
      rw [PFunDDS.restrict_concat_self] at hempty
      simp at hempty
    · rw [PFunDDS.restrict_concat_self] at hdomi
      exact hdomi
  refine ⟨hd, ?_⟩
  have hp : h = [] ∨ h ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)) := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h', a', rfl⟩
    · exact Or.inl rfl
    · rw [List.concat_eq_append]
      rw [List.concat_eq_append] at hdom
      right
      refine ⟨by simp, ?_⟩
      intro j
      rcases hdom.2 j with hempty | hdomj
      · left
        have hpre := PFunDDS.restrict_prefix j
          (List.prefix_append (h' ++ [a']) [(⟨i, x⟩ : Σ _ : Fin 2, X)])
        rw [hempty] at hpre
        exact List.prefix_nil.mp hpre
      · by_cases hne : PFunDDS.restrict j (h' ++ [a']) = []
        · exact Or.inl hne
        · exact Or.inr (PFunDDS.prefix_closed _
            (PFunDDS.restrict_prefix j (List.prefix_append _ _)) hne hdomj)
  have hval := pairAccess_eval S T i hp hd
  rw [hval, Part.mem_some_iff] at ha
  exact ha

/-- Output transport along an equality of systems. -/
theorem output_congr_system {S₁ S₂ : PFunDDS.DDS X Y} (hS : S₁ = S₂)
    (l : List X) (h₁ : l ∈ PFunDDS.dom S₁) :
    PFunDDS.output S₁ l h₁ = PFunDDS.output S₂ l (hS ▸ h₁) := by
  subst hS
  rfl

theorem pairAccess_eval_left (S T : PFunDDS.DDS X Y)
    {h : List (Σ _ : Fin 2, X)} {u : X}
    (hp : h = [] ∨ h ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)))
    (hdS : PFunDDS.restrict 0 h ++ [u] ∈ PFunDDS.dom S) :
    (PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨0, u⟩])
      = Part.some ⟨0, PFunDDS.output S (PFunDDS.restrict 0 h ++ [u]) hdS⟩ := by
  have hd' : PFunDDS.restrict 0 h ++ [u]
      ∈ PFunDDS.dom (Combine.pair S T 0) := by
    rw [pair_zero]
    exact hdS
  rw [pairAccess_eval S T 0 hp hd']
  exact congrArg Part.some (congrArg (Sigma.mk 0)
    (output_congr_system (pair_zero S T) _ hd'))

theorem pairAccess_eval_right (S T : PFunDDS.DDS X Y)
    {h : List (Σ _ : Fin 2, X)} {u : X}
    (hp : h = [] ∨ h ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)))
    (hdT : PFunDDS.restrict 1 h ++ [u] ∈ PFunDDS.dom T) :
    (PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨1, u⟩])
      = Part.some ⟨1, PFunDDS.output T (PFunDDS.restrict 1 h ++ [u]) hdT⟩ := by
  have hd' : PFunDDS.restrict 1 h ++ [u]
      ∈ PFunDDS.dom (Combine.pair S T 1) := by
    rw [pair_one]
    exact hdT
  rw [pairAccess_eval S T 1 hp hd']
  exact congrArg Part.some (congrArg (Sigma.mk 1)
    (output_congr_system (pair_one S T) _ hd'))

theorem pairAccess_mem_elim_left (S T : PFunDDS.DDS X Y)
    {h : List (Σ _ : Fin 2, X)} {u : X} {a : Σ _ : Fin 2, Y}
    (ha : a ∈ (PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨0, u⟩])) :
    ∃ hdS : PFunDDS.restrict 0 h ++ [u] ∈ PFunDDS.dom S,
      a = ⟨0, PFunDDS.output S (PFunDDS.restrict 0 h ++ [u]) hdS⟩ := by
  obtain ⟨hd, rfl⟩ := pairAccess_mem_elim S T 0 ha
  refine ⟨by rw [← pair_zero (S := S) (T := T)]; exact hd, ?_⟩
  exact congrArg (Sigma.mk 0) (output_congr_system (pair_zero S T) _ hd)

theorem pairAccess_mem_elim_right (S T : PFunDDS.DDS X Y)
    {h : List (Σ _ : Fin 2, X)} {u : X} {a : Σ _ : Fin 2, Y}
    (ha : a ∈ (PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨1, u⟩])) :
    ∃ hdT : PFunDDS.restrict 1 h ++ [u] ∈ PFunDDS.dom T,
      a = ⟨1, PFunDDS.output T (PFunDDS.restrict 1 h ++ [u]) hdT⟩ := by
  obtain ⟨hd, rfl⟩ := pairAccess_mem_elim S T 1 ha
  refine ⟨by rw [← pair_one (S := S) (T := T)]; exact hd, ?_⟩
  exact congrArg (Sigma.mk 1) (output_congr_system (pair_one S T) _ hd)

/-! ### One combine round -/

theorem restrict_zero_pair_snoc (h : List (Σ _ : Fin 2, X)) (u : X) :
    PFunDDS.restrict (0 : Fin 2) (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
      = PFunDDS.restrict 0 h ++ [u] := by
  rw [PFunDDS.restrict_concat_ne (by decide : (1 : Fin 2) ≠ 0),
    PFunDDS.restrict_concat_self]

theorem restrict_one_pair_snoc (h : List (Σ _ : Fin 2, X)) (u : X) :
    PFunDDS.restrict (1 : Fin 2) (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
      = PFunDDS.restrict 1 h ++ [u] := by
  rw [PFunDDS.restrict_concat_self,
    PFunDDS.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]

/-- One combine round, computed. -/
theorem driveG_combineStep_round (op : Y → Y → Y) (S T : PFunDDS.DDS X Y)
    {h : List (Σ _ : Fin 2, X)} {u : X}
    (hp : h = [] ∨ h ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)))
    (hdS : PFunDDS.restrict 0 h ++ [u] ∈ PFunDDS.dom S)
    (hdT : PFunDDS.restrict 1 h ++ [u] ∈ PFunDDS.dom T) (n : ℕ) :
    CausalApply.driveG (combineStep op u)
        (PFunDDS.parallel (Combine.pair S T)).1 (n + 1 + 1 + 1) h []
      = Part.some
          (op (PFunDDS.output S (PFunDDS.restrict 0 h ++ [u]) hdS)
            (PFunDDS.output T (PFunDDS.restrict 1 h ++ [u]) hdT),
           (h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) := by
  have h1 := pairAccess_eval_left S T hp hdS
  have hdom₁ : h ++ [⟨0, u⟩]
      ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)) := by
    rw [PFunDDS.dom_def, PFun.mem_dom]
    exact ⟨_, by rw [h1]; exact Part.mem_some _⟩
  have hdT₁ : PFunDDS.restrict 1 (h ++ [⟨0, u⟩]) ++ [u] ∈ PFunDDS.dom T := by
    rw [PFunDDS.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]
    exact hdT
  have h2 := pairAccess_eval_right S T (h := h ++ [⟨0, u⟩]) (Or.inr hdom₁) hdT₁
  show ((PFunDDS.parallel (Combine.pair S T)).1 (h ++ [⟨0, u⟩])).bind
      (fun y => CausalApply.driveG (combineStep op u)
        (PFunDDS.parallel (Combine.pair S T)).1 (n + 1 + 1)
        (h ++ [⟨0, u⟩]) ([] ++ [y])) = _
  rw [h1, Part.bind_some]
  show ((PFunDDS.parallel (Combine.pair S T)).1
      ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])).bind
      (fun y => CausalApply.driveG (combineStep op u)
        (PFunDDS.parallel (Combine.pair S T)).1 (n + 1)
        ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
        ([⟨0, PFunDDS.output S (PFunDDS.restrict 0 h ++ [u]) hdS⟩] ++ [y]))
    = _
  rw [h2, Part.bind_some]
  show Part.some (op _ _, (h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) = _
  refine congrArg Part.some (Prod.ext ?_ rfl)
  refine congrArg (op _) ?_
  exact PFunDDS.output_congr T
    (by rw [PFunDDS.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]) hdT₁ hdT

/-- One combine round, destructed. -/
theorem driveG_combineStep_elim (op : Y → Y → Y) (S T : PFunDDS.DDS X Y)
    {u : X} {h : List (Σ _ : Fin 2, X)} {fuel : ℕ}
    {p : Y × List (Σ _ : Fin 2, X)}
    (hp : p ∈ CausalApply.driveG (combineStep op u)
      (PFunDDS.parallel (Combine.pair S T)).1 fuel h []) :
    ∃ (hdS : PFunDDS.restrict 0 h ++ [u] ∈ PFunDDS.dom S)
      (hdT : PFunDDS.restrict 1 h ++ [u] ∈ PFunDDS.dom T),
      p = (op (PFunDDS.output S (PFunDDS.restrict 0 h ++ [u]) hdS)
            (PFunDDS.output T (PFunDDS.restrict 1 h ++ [u]) hdT),
           (h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) := by
  rcases fuel with _ | fuel
  · simp [CausalApply.driveG] at hp
  · simp only [CausalApply.driveG, combineStep] at hp
    rw [Part.mem_bind_iff] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    obtain ⟨hdS, rfl⟩ := pairAccess_mem_elim_left S T ha₁
    simp only [List.nil_append] at hp
    rcases fuel with _ | fuel
    · simp [CausalApply.driveG] at hp
    · simp only [CausalApply.driveG, combineStep] at hp
      rw [Part.mem_bind_iff] at hp
      obtain ⟨a₂, ha₂, hp⟩ := hp
      obtain ⟨hdT₁, rfl⟩ := pairAccess_mem_elim_right S T ha₂
      have hdT : PFunDDS.restrict 1 h ++ [u] ∈ PFunDDS.dom T := by
        rw [← PFunDDS.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)
          (x := u) (l := h)]
        exact hdT₁
      rcases fuel with _ | fuel
      · simp [CausalApply.driveG] at hp
      · simp only [CausalApply.driveG, combineStep, List.cons_append,
          List.nil_append, Part.mem_some_iff] at hp
        refine ⟨hdS, hdT, ?_⟩
        rw [hp]
        refine Prod.ext ?_ rfl
        refine congrArg (op _) ?_
        exact PFunDDS.output_congr T
          (by rw [PFunDDS.restrict_concat_ne
            (by decide : (0 : Fin 2) ≠ 1)]) hdT₁ hdT

/-! ### The outer fold and the honest combine equation -/

/-- Forward run of the combine converter over a whole outer history. -/
theorem driveOuter_combineStep_of_dom (op : Y → Y → Y)
    (S T : PFunDDS.DDS X Y) :
    ∀ (rest : List X) (h : List (Σ _ : Fin 2, X)),
      (h = [] ∨ h ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T))) →
      PFunDDS.restrict 1 h = PFunDDS.restrict 0 h →
      ((PFunDDS.restrict 0 h ++ rest ∈ PFunDDS.dom S ∧
        PFunDDS.restrict 0 h ++ rest ∈ PFunDDS.dom T) ∨ rest = []) →
      ∃ vs h',
        (vs, h') ∈ CausalApply.driveOuter (combineStep op)
          (PFunDDS.parallel (Combine.pair S T)).1 3 h rest ∧
        ∀ (hS : PFunDDS.restrict 0 h ++ rest ∈ PFunDDS.dom S)
          (hT : PFunDDS.restrict 0 h ++ rest ∈ PFunDDS.dom T),
          rest ≠ [] →
            vs.getLast? = some (op
              (PFunDDS.output S (PFunDDS.restrict 0 h ++ rest) hS)
              (PFunDDS.output T (PFunDDS.restrict 0 h ++ rest) hT)) := by
  intro rest
  induction rest with
  | nil =>
      intro h _ _ _
      exact ⟨[], h, by simp [CausalApply.driveOuter],
        fun _ _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro h hph hsym hfull
      obtain ⟨hSfull, hTfull⟩ : PFunDDS.restrict 0 h ++ u :: rest
          ∈ PFunDDS.dom S ∧
          PFunDDS.restrict 0 h ++ u :: rest ∈ PFunDDS.dom T := by
        rcases hfull with hf | hf
        · exact hf
        · exact absurd hf (by simp)
      have hdS₁ : PFunDDS.restrict 0 h ++ [u] ∈ PFunDDS.dom S :=
        PFunDDS.prefix_closed S ⟨rest, by simp⟩ (by simp) hSfull
      have hdT₁ : PFunDDS.restrict 1 h ++ [u] ∈ PFunDDS.dom T := by
        rw [hsym]
        exact PFunDDS.prefix_closed T ⟨rest, by simp⟩ (by simp) hTfull
      have hround := driveG_combineStep_round op S T hph hdS₁ hdT₁ 0
      -- domain of the extended access history
      have h1 := pairAccess_eval_left S T hph hdS₁
      have hdom₁ : h ++ [⟨0, u⟩]
          ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)) := by
        rw [PFunDDS.dom_def, PFun.mem_dom]
        exact ⟨_, by rw [h1]; exact Part.mem_some _⟩
      have hdT₁' : PFunDDS.restrict 1 (h ++ [⟨0, u⟩]) ++ [u]
          ∈ PFunDDS.dom T := by
        rw [PFunDDS.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]
        exact hdT₁
      have h2 := pairAccess_eval_right S T (h := h ++ [⟨0, u⟩])
        (Or.inr hdom₁) hdT₁'
      have hdom₂ : (h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]
          ∈ PFunDDS.dom (PFunDDS.parallel (Combine.pair S T)) := by
        rw [PFunDDS.dom_def, PFun.mem_dom]
        exact ⟨_, by rw [h2]; exact Part.mem_some _⟩
      -- invariants at the extended history
      have hR0 : PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
          = PFunDDS.restrict 0 h ++ [u] := restrict_zero_pair_snoc h u
      have hR1 : PFunDDS.restrict 1 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
          = PFunDDS.restrict 1 h ++ [u] := restrict_one_pair_snoc h u
      have hsym' : PFunDDS.restrict 1 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
          = PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) := by
        rw [hR0, hR1, hsym]
      have hfull' : (PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) ++ rest
            ∈ PFunDDS.dom S ∧
          PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) ++ rest
            ∈ PFunDDS.dom T) ∨ rest = [] := by
        refine Or.inl ⟨?_, ?_⟩
        · rw [hR0, List.append_assoc]
          simpa using hSfull
        · rw [hR0, List.append_assoc]
          simpa using hTfull
      obtain ⟨vs', h'', hmem', hlast'⟩ := ih ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
        (Or.inr hdom₂) hsym' hfull'
      refine ⟨op (PFunDDS.output S (PFunDDS.restrict 0 h ++ [u]) hdS₁)
        (PFunDDS.output T (PFunDDS.restrict 1 h ++ [u]) hdT₁) :: vs',
        h'', ?_, ?_⟩
      · show _ ∈ (CausalApply.driveG (combineStep op u)
            (PFunDDS.parallel (Combine.pair S T)).1 3 h []).bind _
        rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, hround, Part.bind_some]
        rw [Part.mem_map_iff]
        exact ⟨(vs', h''), hmem', rfl⟩
      · intro hS hT hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := CausalApply.driveOuter_length (combineStep op)
                (PFunDDS.parallel (Combine.pair S T)).1 3 _ rest hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
            refine congrArg some ?_
            refine congrArg₂ op ?_ ?_
            · exact PFunDDS.output_congr S rfl hdS₁ hS
            · refine PFunDDS.output_congr T ?_ hdT₁ hT
              rw [hsym]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := CausalApply.driveOuter_length (combineStep op)
                (PFunDDS.parallel (Combine.pair S T)).1 3 _ rest hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have hlist : PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
                ++ rest = PFunDDS.restrict 0 h ++ u :: rest := by
              rw [hR0, List.append_assoc]
              rfl
            have hS' : PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
                ++ rest ∈ PFunDDS.dom S := by
              rw [hlist]
              exact hS
            have hT' : PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
                ++ rest ∈ PFunDDS.dom T := by
              rw [hlist]
              exact hT
            have hlast'' := hlast' hS' hT' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            refine congrArg some ?_
            refine congrArg₂ op ?_ ?_
            · exact PFunDDS.output_congr S hlist hS' hS
            · exact PFunDDS.output_congr T hlist hT' hT

/-- Backward run analysis of the combine converter. -/
theorem driveOuter_combineStep_mem_imp (op : Y → Y → Y)
    (S T : PFunDDS.DDS X Y) :
    ∀ (rest : List X) (h : List (Σ _ : Fin 2, X)) {fuel : ℕ}
      {r : List Y × List (Σ _ : Fin 2, X)},
      PFunDDS.restrict 1 h = PFunDDS.restrict 0 h →
      r ∈ CausalApply.driveOuter (combineStep op)
        (PFunDDS.parallel (Combine.pair S T)).1 fuel h rest →
      rest ≠ [] →
      ∃ (hS : PFunDDS.restrict 0 h ++ rest ∈ PFunDDS.dom S)
        (hT : PFunDDS.restrict 0 h ++ rest ∈ PFunDDS.dom T),
        r.1.getLast? = some (op
          (PFunDDS.output S (PFunDDS.restrict 0 h ++ rest) hS)
          (PFunDDS.output T (PFunDDS.restrict 0 h ++ rest) hT)) := by
  intro rest
  induction rest with
  | nil =>
      intro h fuel r _ _ hne
      exact absurd rfl hne
  | cons u rest ih =>
      intro h fuel r hsym hr _
      simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hdS₁, hdT₁, rfl⟩ := driveG_combineStep_elim op S T hr₁
      have hR0 := restrict_zero_pair_snoc h u
      have hR1 := restrict_one_pair_snoc h u
      have hsym' : PFunDDS.restrict 1 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
          = PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩]) := by
        rw [hR0, hR1, hsym]
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [CausalApply.driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨hdS₁, by rw [hsym] at hdT₁; exact hdT₁, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some ?_
          refine congrArg₂ op ?_ ?_
          · exact PFunDDS.output_congr S rfl hdS₁ _
          · exact PFunDDS.output_congr T (by rw [hsym]) hdT₁ _
      | cons r0 rs0 =>
          obtain ⟨hS', hT', hlast'⟩ := ih ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
            hsym' hrr (by simp [hrest])
          have hlist : PFunDDS.restrict 0 ((h ++ [⟨0, u⟩]) ++ [⟨1, u⟩])
              ++ rest = PFunDDS.restrict 0 h ++ u :: rest := by
            rw [hR0, List.append_assoc]
            rfl
          rw [← hrest]
          have hS : PFunDDS.restrict 0 h ++ u :: rest ∈ PFunDDS.dom S := by
            rw [← hlist]
            exact hS'
          have hT : PFunDDS.restrict 0 h ++ u :: rest ∈ PFunDDS.dom T := by
            rw [← hlist]
            exact hT'
          refine ⟨hS, hT, ?_⟩
          have hlenrr := CausalApply.driveOuter_length (combineStep op)
            (PFunDDS.parallel (Combine.pair S T)).1 fuel _ rest hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              refine congrArg some (congrArg₂ op ?_ ?_)
              · exact PFunDDS.output_congr S hlist hS' hS
              · exact PFunDDS.output_congr T hlist hT' hT

/-- Membership characterization of the native combine. -/
theorem mem_combine_iff (op : Y → Y → Y) (S T : PFunDDS.DDS X Y)
    (l : List X) (y : Y) :
    y ∈ (PFunDDS.combine op S T).1 l ↔
      ∃ (hS : l ∈ PFunDDS.dom S) (hT : l ∈ PFunDDS.dom T),
        y = op (PFunDDS.output S l hS) (PFunDDS.output T l hT) := by
  constructor
  · rintro ⟨⟨hS, hT⟩, rfl⟩
    exact ⟨hS, hT, rfl⟩
  · rintro ⟨hS, hT, rfl⟩
    exact ⟨⟨hS, hT⟩, rfl⟩

/-- **The honest output-combine equation (CR18 Def 3.12 via Def 3.9).**  The
combine converter, as a Def 3.8 object applied by Def 3.9 to the parallel of
the two systems, *is* the native DDS-level combine — replacing the
`rfl`-by-definition `combineViaConverter_eq_combine` with a genuine converter
equation. -/
theorem apply_combineStep (op : Y → Y → Y) (S T : PFunDDS.DDS X Y) :
    DDC.apply (DDC.ofStep (combineStep op))
        (PFunDDS.parallel (Combine.pair S T))
      = PFunDDS.combine op S T := by
  rw [show DDC.apply (DDC.ofStep (combineStep op))
      (PFunDDS.parallel (Combine.pair S T))
    = CausalApply.applyG (combineStep op)
        (PFunDDS.parallel (Combine.pair S T)).1 from DDC.apply_ofStep _ _]
  apply Subtype.ext
  funext us
  apply Part.ext
  intro y
  rw [CausalApply.applyG_toPFun, CausalApply.mem_applyRaw, mem_combine_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := CausalApply.driveOuter_length (combineStep op)
        (PFunDDS.parallel (Combine.pair S T)).1 fuel [] [] hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨hS, hT, hout⟩ := driveOuter_combineStep_mem_imp op S T us []
      rfl hr hne
    rw [hlast] at hout
    have hy := Option.some.inj hout
    exact ⟨hS, hT, hy⟩
  · rintro ⟨hS, hT, rfl⟩
    have hne : us ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem S hS
    obtain ⟨vs, h', hmem, hlast⟩ := driveOuter_combineStep_of_dom op S T us []
      (Or.inl rfl) rfl (Or.inl ⟨hS, hT⟩)
    refine ⟨3, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    exact ⟨(vs, h'), hmem, hlast hS hT hne⟩

end PFunConverter

end RandomSystems.CR18
