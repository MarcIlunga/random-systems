/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ProtocolRealization
import RandomSystems.StepConverter
import RandomSystems.ComposeRealization

/-!
# Outer-memoryless step converters in the protocol-function carrier

An outer-memoryless converter (CR18 Def 3.8; the class realized by
`PFunConverter.DDC.ofStep` at the DDC carrier) is presented by a protocol
step function `step : U → List Y → X ⊕ V` together with its per-round
inner-query budget `cnt : U → ℕ` (the boundary condition
`step u ys = Sum.inl _ ↔ ys.length < cnt u`).  This file lifts that class
one carrier level up, to `PFunConverter.ProtocolFn`:

* **`PFunConverter.ProtocolFn.ofStep step cnt`** — the step function as a
  protocol function on cumulative histories: the current round is the last
  outer message, its answer segment is what remains after discounting the
  `Σ cnt` consumed by the previous rounds, and the move is `step` on the
  sequenced segment (silent on any improper `⊥` answer).
* **`apply_ofStep_eq_applyG`** — the coherence with CR18 Def 3.9: the
  protocol-function application `PFunConverter.apply` of `ofStep step cnt`
  is `CausalApply.applyG step` — the ProtocolFn-carrier counterpart of the
  DDC-carrier realization theorem `PFunConverter.DDC.apply_ofStep`.
* **`IsOfStep`** — the class as a predicate (membership is extensional —
  a property of the converter, not of its presentation), with the
  transport `IsOfStep.apply_eq_applyG`, the totality engine `ofStep_dom`
  (an `ofStep` converter never goes silent on a proper history), and the
  separation `not_isOfStep_queryLimitFn` (a budget-style converter is
  genuinely outside the class).

The proof is the round/outer drive simulation on the drop-offset
invariant: within a round the ν-side answer segment is the `some`-image of
the `applyG`-side one, and each outer round re-opens on the empty segment.

The final section lifts the restriction the name records.  Outer-memorylessness
is a property of *this constructor*, not of the carrier and not of CR18
Def 3.8, so **`PFunConverter.ProtocolFn.ofHistoryStep`** stands beside `ofStep`
with the outer history passed to `step` and the round count indexed by the
outer prefix; `isDDC_ofHistoryStep` is the Def 3.8 membership, and
`ofStep_eq_ofHistoryStep` exhibits `ofStep` as its history-ignoring instance.
-/

namespace RandomSystems.CR18

/-! ### The proper-segment and block-weight calculus -/

/-- Sequencing a proper segment. -/
theorem mapM_id_map_some {Y : Type*} (l : List Y) :
    (l.map some).mapM id = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- A sequenced segment is proper. -/
theorem eq_map_some_of_mapM_id_eq_some {Y : Type*} :
    ∀ {l : List (Option Y)} {l' : List Y}, l.mapM id = some l' →
      l = l'.map some := by
  intro l
  induction l with
  | nil =>
      intro l' h
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      rfl
  | cons a t ih =>
      intro l' h
      rw [List.mapM_cons] at h
      cases a with
      | none => simp at h
      | some x =>
          cases hmt : t.mapM (m := Option) id with
          | none => simp [hmt] at h
          | some bs =>
              simp only [hmt] at h
              simp at h
              subst h
              simp [ih hmt]

/-- Splitting a weight sum at the last element. -/
theorem sum_map_dropLast_getLast {γ : Type*} (f : γ → ℕ) {A : List γ}
    (hne : A ≠ []) :
    (A.map f).sum = (A.dropLast.map f).sum + f (A.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  simp

/-- The last-round offset of an extended history dominates the weight of
the delivered prefix. -/
theorem sum_map_dropLast_append_cons {γ : Type*} (f : γ → ℕ) (A : List γ)
    (w : γ) (l : List γ) :
    ((A ++ w :: l).dropLast.map f).sum
      = (A.map f).sum + ((w :: l).dropLast.map f).sum := by
  rw [List.dropLast_append_cons, List.map_append, List.sum_append]

namespace PFunConverter.ProtocolFn

open scoped PFunDDS

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- **The outer-memoryless step converter** (CR18 Def 3.8), in the
protocol-function carrier — the ProtocolFn presentation of the
`PFunConverter.DDC.ofStep` class: at outer messages `us` and cumulative
inner answers `ys` (in the `Y ∪ {⊥}` alphabet of CR18 Def 3.8), the
current round is the last message, its answer segment is what is left
after discounting the `Σ cnt` consumed by the previous rounds, and the
move is `step` on the sequenced segment — the converter is silent unless
every consumed answer is proper (`List.mapM id` sequences the segment). -/
def ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ) :
    PFunConverter.ProtocolFn U V X Y := fun p =>
  if h : p.1 ≠ [] then
    match (p.2.drop ((p.1.dropLast.map cnt).sum)).mapM id with
    | some ys => Part.some (step (p.1.getLast h) ys)
    | none => Part.none
  else Part.none

/-- `ofStep`'s move at a pair, computed: the `mapM` sequencing of the
dropped segment decides between the `step` move and silence. -/
theorem ofStep_apply (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    {us : List U} (hne : us ≠ []) (ys : List (Option Y)) :
    ofStep step cnt (us, ys) =
      match (ys.drop ((us.dropLast.map cnt).sum)).mapM id with
      | some ysY => Part.some (step (us.getLast hne) ysY)
      | none => Part.none := by
  unfold ofStep
  rw [dif_pos (show (us, ys).1 ≠ [] from hne)]

/-- `ofStep`'s move at a proper answer list, computed. -/
theorem ofStep_apply_map_some (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    {A : List U} (hne : A ≠ []) (l : List Y) :
    ofStep step cnt (A, l.map some)
      = Part.some (step (A.getLast hne)
          (l.drop ((A.dropLast.map cnt).sum))) := by
  rw [ofStep_apply step cnt hne (l.map some), ← List.map_drop,
    mapM_id_map_some]

/-- `ofStep`'s membership, characterized: the dropped segment sequences
and the move is `step` on it. -/
theorem mem_ofStep_iff (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    {A : List U} (hne : A ≠ []) (ys : List (Option Y)) (mv : X ⊕ V) :
    mv ∈ ofStep step cnt (A, ys) ↔
      ∃ ysY : List Y,
        ys.drop ((A.dropLast.map cnt).sum) = ysY.map some ∧
          mv = step (A.getLast hne) ysY := by
  rw [ofStep_apply step cnt hne ys]
  cases hseg : (ys.drop ((A.dropLast.map cnt).sum)).mapM id with
  | none =>
      constructor
      · intro hm
        simp at hm
      · rintro ⟨ysY, hdrop, -⟩
        rw [hdrop, mapM_id_map_some] at hseg
        simp at hseg
  | some l =>
      have hl := eq_map_some_of_mapM_id_eq_some hseg
      constructor
      · intro hm
        rw [Part.mem_some_iff] at hm
        exact ⟨l, hl, hm⟩
      · rintro ⟨ysY, hdrop, rfl⟩
        rw [Part.mem_some_iff]
        have hxl : ysY = l :=
          List.map_injective_iff.mpr (Option.some_injective Y)
            (hdrop.symm.trans hl)
        rw [hxl]

/-- Sum dichotomy through the boundary condition: an `inr` move means the
round budget is exhausted. -/
theorem not_lt_cnt_of_eq_inr {step : U → List Y → X ⊕ V} {cnt : U → ℕ}
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    {u : U} {ys : List Y} {v : V} (h : step u ys = Sum.inr v) :
    ¬ ys.length < cnt u := by
  intro hlt
  obtain ⟨x, hx⟩ := (hcnt u ys).mpr hlt
  rw [h] at hx
  simp at hx

/-- Round simulation, forward: a `drive (ofStep step cnt)` run from an
all-proper segment under the round budget is a `driveG step` run of the
segment's `some`-values, consumes exactly the round's budget, and keeps
the inner history inside the system's domain. -/
theorem driveG_of_drive_ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {us : List U} (hne : us ≠ []) {xs : List X}
      {ys : List (Option Y)} {ysY : List Y} {r : V × List X × List (Option Y)},
      ys.drop ((us.dropLast.map cnt).sum) = ysY.map some →
      (us.dropLast.map cnt).sum ≤ ys.length →
      ys.length ≤ (us.dropLast.map cnt).sum + cnt (us.getLast hne) →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r ∈ PFunConverter.drive (ofStep step cnt) S fuel us xs ys →
      ∃ Δ : List (Option Y), r.2.2 = ys ++ Δ ∧
        r.2.2.length = (us.dropLast.map cnt).sum + cnt (us.getLast hne) ∧
        (r.2.1 ∈ PFunDDS.dom S ∨ r.2.1 = []) ∧
        (r.1, r.2.1) ∈ CausalApply.driveG (step (us.getLast hne)) S.1
          fuel xs ysY := by
  have hmapM : ∀ l : List Y, (l.map some).mapM id = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  intro fuel
  induction fuel with
  | zero =>
      intro us hne xs ys ysY r _ _ _ _ h
      simp [PFunConverter.drive] at h
  | succ n ih =>
      intro us hne xs ys ysY r hseg hoff hupper hxs h
      have hlen' : ys.length - (us.dropLast.map cnt).sum = ysY.length := by
        have hl := congrArg List.length hseg
        simpa only [List.length_drop, List.length_map] using hl
      have hOf : ofStep step cnt (us, ys)
          = Part.some (step (us.getLast hne) ysY) := by
        rw [ofStep_apply step cnt hne ys, hseg, hmapM ysY]
      rcases PFunConverter.drive_succ_elim h with ⟨x, hm, h'⟩ | ⟨v, hm, rfl⟩
      · rw [hOf, Part.mem_some_iff] at hm
        have hc : ysY.length < cnt (us.getLast hne) :=
          (hcnt _ ysY).mp ⟨x, hm.symm⟩
        rcases hout : PFunDDS.output (S⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · -- improper answer: `ofStep` goes silent at the extended pair,
          -- the continued drive has no result
          exfalso
          rw [hout] at h'
          have hnone : ofStep step cnt (us, ys ++ [none]) = Part.none := by
            rw [ofStep_apply step cnt hne (ys ++ [none]),
              List.drop_append_of_le_length hoff, hseg]
            simp
          rcases n with _ | n'
          · simp [PFunConverter.drive] at h'
          · rcases PFunConverter.drive_succ_elim h' with
              ⟨x₂, hm₂, -⟩ | ⟨v₂, hm₂, -⟩ <;>
            · rw [hnone] at hm₂
              simp at hm₂
        · rw [hout] at h'
          obtain ⟨hnext, houtS⟩ :=
            PFunDDS.mem_of_output_fullyDefined_append_eq_some S xs x hxs hout
          have hseg' : (ys ++ [some y]).drop ((us.dropLast.map cnt).sum)
              = (ysY ++ [y]).map some := by
            rw [List.drop_append_of_le_length hoff, hseg]
            simp
          obtain ⟨Δ, hΔ, hlen, hdomf, hg⟩ := ih hne hseg'
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (Or.inl hnext) h'
          refine ⟨some y :: Δ, ?_, ?_, hdomf, ?_⟩
          · rw [hΔ]; simp
          · exact hlen
          · simp only [CausalApply.driveG]
            rw [← hm, Part.mem_bind_iff]
            refine ⟨y, ?_, hg⟩
            show y ∈ S.1 (xs ++ [x])
            rw [← houtS]
            exact Part.get_mem hnext
      · rw [hOf, Part.mem_some_iff] at hm
        have hc : ¬ ysY.length < cnt (us.getLast hne) :=
          not_lt_cnt_of_eq_inr hcnt hm.symm
        refine ⟨[], by simp, by dsimp only; omega, hxs, ?_⟩
        simp only [CausalApply.driveG]
        rw [← hm]
        exact Part.mem_some _

/-- Round simulation, backward. -/
theorem drive_ofStep_of_driveG (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {us : List U} (hne : us ≠ []) {xs : List X}
      {ys : List (Option Y)} {ysY : List Y} {r' : V × List X},
      ys.drop ((us.dropLast.map cnt).sum) = ysY.map some →
      (us.dropLast.map cnt).sum ≤ ys.length →
      ys.length ≤ (us.dropLast.map cnt).sum + cnt (us.getLast hne) →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r' ∈ CausalApply.driveG (step (us.getLast hne)) S.1 fuel xs ysY →
      ∃ Δ : List (Option Y),
        (ys ++ Δ).length = (us.dropLast.map cnt).sum + cnt (us.getLast hne) ∧
        (r'.2 ∈ PFunDDS.dom S ∨ r'.2 = []) ∧
        (r'.1, r'.2, ys ++ Δ) ∈
          PFunConverter.drive (ofStep step cnt) S fuel us xs ys := by
  have hmapM : ∀ l : List Y, (l.map some).mapM id = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  intro fuel
  induction fuel with
  | zero =>
      intro us hne xs ys ysY r' _ _ _ _ h
      simp [CausalApply.driveG] at h
  | succ n ih =>
      intro us hne xs ys ysY r' hseg hoff hupper hxs h
      have hlen' : ys.length - (us.dropLast.map cnt).sum = ysY.length := by
        have hl := congrArg List.length hseg
        simpa only [List.length_drop, List.length_map] using hl
      have hOf : ofStep step cnt (us, ys)
          = Part.some (step (us.getLast hne) ysY) := by
        rw [ofStep_apply step cnt hne ys, hseg, hmapM ysY]
      simp only [CausalApply.driveG] at h
      rcases hstep : step (us.getLast hne) ysY with x | v <;>
        rw [hstep] at h
      · rw [Part.mem_bind_iff] at h
        obtain ⟨y, hy, h'⟩ := h
        have hc : ysY.length < cnt (us.getLast hne) :=
          (hcnt _ ysY).mp ⟨x, hstep⟩
        have hnext : xs ++ [x] ∈ PFunDDS.dom S :=
          Part.dom_iff_mem.mpr ⟨y, hy⟩
        have hout : PFunDDS.output (S⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
          rw [PFunDDS.output_fullyDefined_append_of_mem S xs x hxs hnext]
          exact congrArg some (Part.get_eq_of_mem hy hnext)
        have hseg' : (ys ++ [some y]).drop ((us.dropLast.map cnt).sum)
            = (ysY ++ [y]).map some := by
          rw [List.drop_append_of_le_length hoff, hseg]
          simp
        obtain ⟨Δ, hlen, hdomf, hnu⟩ := ih hne hseg'
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (Or.inl hnext) h'
        refine ⟨some y :: Δ, ?_, hdomf, ?_⟩
        · simpa [List.append_assoc] using hlen
        · have hm : Sum.inl x ∈ ofStep step cnt (us, ys) := by
            rw [hOf, Part.mem_some_iff, hstep]
          have hnu' : (r'.1, r'.2, ys ++ some y :: Δ) ∈
              PFunConverter.drive (ofStep step cnt) S n us (xs ++ [x])
                (ys ++ [some y]) := by
            simpa [List.append_assoc] using hnu
          refine PFunConverter.drive_mem_query (ofStep step cnt) S hm ?_
          rw [hout]
          exact hnu'
      · rw [Part.mem_some_iff] at h
        subst h
        have hc : ¬ ysY.length < cnt (us.getLast hne) :=
          not_lt_cnt_of_eq_inr hcnt hstep
        have hm : Sum.inr v ∈ ofStep step cnt (us, ys) := by
          rw [hOf, Part.mem_some_iff, hstep]
        exact ⟨[], by simp only [List.length_append, List.length_nil]; omega,
          hxs,
          by simpa using PFunConverter.drive_mem_answer (ofStep step cnt) S hm n⟩

/-- Outer simulation, forward: the cumulative drive of `ofStep` is the
per-round drive of `step`, on the exactly-consumed invariant (each round
opens on an empty segment, so the `some`-image invariant of the round
bridge is trivially re-established). -/
theorem driveOuter_of_driveOuter_ofStep (step : U → List Y → X ⊕ V)
    (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    (S : PFunDDS.DDS X Y) :
    ∀ {rest : List U} {fuel : ℕ} {usPre : List U} {xs : List X}
      {ys : List (Option Y)} {r : List V × List X × List (Option Y)},
      (usPre.map cnt).sum = ys.length →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r ∈ PFunConverter.driveOuter (ofStep step cnt) S fuel usPre xs ys rest →
      (r.1, r.2.1) ∈ CausalApply.driveOuter step S.1 fuel xs rest := by
  intro rest
  induction rest with
  | nil =>
      intro fuel usPre xs ys r _ _ h
      simp only [PFunConverter.driveOuter, Part.mem_some_iff] at h
      subst h
      simp [CausalApply.driveOuter]
  | cons u rest ih =>
      intro fuel usPre xs ys r hinv hxs h
      simp only [PFunConverter.driveOuter, Part.mem_bind_iff,
        Part.mem_map_iff] at h
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := h
      have hseg : ys.drop (((usPre ++ [u]).dropLast.map cnt).sum)
          = ([] : List Y).map some := by
        rw [List.dropLast_concat, hinv, List.drop_length]
        rfl
      obtain ⟨Δ, hΔ, hlen, hdomf, hg⟩ :=
        driveG_of_drive_ofStep step cnt hcnt S (by simp) hseg
          (by simp [hinv])
          (by simp [hinv])
          hxs hr₁
      rw [List.getLast_append_singleton] at hg
      have hinv' : ((usPre ++ [u]).map cnt).sum = r₁.2.2.length := by
        rw [hlen, List.dropLast_concat, List.getLast_append_singleton]
        simp [hinv]
      have hrest := ih hinv' hdomf hrr
      simp only [CausalApply.driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r₁.1, r₁.2.1), hg, (rr.1, rr.2.1), hrest, rfl⟩

/-- Outer simulation, backward. -/
theorem driveOuter_ofStep_of_driveOuter (step : U → List Y → X ⊕ V)
    (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    (S : PFunDDS.DDS X Y) :
    ∀ {rest : List U} {fuel : ℕ} {usPre : List U} {xs : List X}
      {ys : List (Option Y)} {r' : List V × List X},
      (usPre.map cnt).sum = ys.length →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r' ∈ CausalApply.driveOuter step S.1 fuel xs rest →
      ∃ Δ : List (Option Y), (r'.1, r'.2, ys ++ Δ) ∈
        PFunConverter.driveOuter (ofStep step cnt) S fuel usPre xs ys rest := by
  intro rest
  induction rest with
  | nil =>
      intro fuel usPre xs ys r' _ _ h
      simp only [CausalApply.driveOuter, Part.mem_some_iff] at h
      subst h
      exact ⟨[], by simp [PFunConverter.driveOuter]⟩
  | cons u rest ih =>
      intro fuel usPre xs ys r' hinv hxs h
      simp only [CausalApply.driveOuter, Part.mem_bind_iff,
        Part.mem_map_iff] at h
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := h
      have hr₁' : r₁ ∈ CausalApply.driveG
          (step ((usPre ++ [u]).getLast (by simp))) S.1 fuel xs [] := by
        rwa [List.getLast_append_singleton]
      have hseg : ys.drop (((usPre ++ [u]).dropLast.map cnt).sum)
          = ([] : List Y).map some := by
        rw [List.dropLast_concat, hinv, List.drop_length]
        rfl
      obtain ⟨Δ, hlen, hdomf, hnu⟩ :=
        drive_ofStep_of_driveG step cnt hcnt S (by simp) hseg
          (by simp [hinv])
          (by simp [hinv])
          hxs hr₁'
      have hinv' : ((usPre ++ [u]).map cnt).sum = (ys ++ Δ).length := by
        rw [hlen, List.dropLast_concat, List.getLast_append_singleton]
        simp [hinv]
      obtain ⟨Δ', hnu'⟩ := ih hinv' hdomf hrr
      refine ⟨Δ ++ Δ', ?_⟩
      simp only [PFunConverter.driveOuter, Part.mem_bind_iff,
        Part.mem_map_iff]
      exact ⟨(r₁.1, r₁.2, ys ++ Δ), hnu,
        (rr.1, rr.2, (ys ++ Δ) ++ Δ'), hnu',
        by simp [List.append_assoc]⟩

/-- **The step-converter coherence** (CR18 Def 3.9 at the ProtocolFn
carrier): the protocol function `ofStep step cnt`, applied by the
transcript equations, is the `applyG`-application of `step` to the
system's raw function — against every system.  The ProtocolFn-carrier
counterpart of `PFunConverter.DDC.apply_ofStep`. -/
theorem apply_ofStep_eq_applyG (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    (S : PFunDDS.DDS X Y) :
    PFunConverter.apply (ofStep step cnt) S
      = CausalApply.applyG step S.1 := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (PFunConverter.apply (ofStep step cnt) S).1
      = PFunConverter.applyRaw (ofStep step cnt) S from rfl,
    show (CausalApply.applyG step S.1).1
      = CausalApply.applyRaw step S.1 from rfl,
    PFunConverter.mem_applyRaw, CausalApply.mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [PFunConverter.mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hg := driveOuter_of_driveOuter_ofStep step cnt hcnt S (by simp)
      (Or.inr rfl) hr
    exact ⟨fuel, (CausalApply.mem_applyRawAt_iff _ _ _ _ _).mpr
      ⟨(r.1, r.2.1), hg, hlast⟩⟩
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.mem_applyRawAt_iff] at hv
    obtain ⟨r', hr', hlast⟩ := hv
    obtain ⟨Δ, hnu⟩ := driveOuter_ofStep_of_driveOuter step cnt hcnt S
      (usPre := []) (ys := []) (by simp) (Or.inr rfl) hr'
    exact ⟨fuel, (PFunConverter.mem_applyRawAt_iff _ _ _ _ _).mpr
      ⟨(r'.1, r'.2, [] ++ Δ), hnu, hlast⟩⟩

/-! ### The canonical simple protocol is the one-query step protocol -/

private theorem simpleFn_eq_ofStep_on_reach
    (c : U → X) (d : Y → V) {p : List U × List (Option Y)}
    (reachable : PFunConverter.Reach (PFunConverter.simpleFn c d) p) :
    PFunConverter.simpleFn c d p =
      ofStep (PFunConverter.DDC.simpleStep c d) (fun _ => 1) p := by
  rcases p with ⟨us, ys⟩
  have shape := (PFunConverter.reach_simpleFn_iff c d (us, ys)).mp reachable
  dsimp only at shape ⊢
  simp only [PFunConverter.simpleFn, ofStep]
  have nonempty : us ≠ [] := by
    rcases shape with pending | answered
    · exact List.ne_nil_of_length_pos (by omega)
    · exact List.ne_nil_of_length_pos (by omega)
  rw [dif_pos nonempty]
  have offsetSum :
      (us.dropLast.map (fun _ => 1)).sum = us.length - 1 := by
    simp
  rw [offsetSum]
  rcases shape with pending | answered
  · rw [dif_pos pending.1]
    have offset : us.length - 1 = ys.length := by omega
    rw [offset, List.drop_length]
    simp [PFunConverter.DDC.simpleStep]
  · rw [dif_neg (by omega), dif_pos ⟨answered.1, by omega⟩]
    have offset : us.length - 1 = ys.length - 1 := by omega
    have ysNonempty : ys ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    rw [offset, List.drop_length_sub_one ysNonempty]
    generalize lastEquation : ys.getLast ysNonempty = last
    cases last with
    | none => simp
    | some answer => simp [PFunConverter.DDC.simpleStep]

private theorem reach_ofStep_imp_reach_simpleFn
    (c : U → X) (d : Y → V) {p : List U × List (Option Y)}
    (reachable : PFunConverter.Reach
      (ofStep (PFunConverter.DDC.simpleStep c d) (fun _ => 1)) p) :
    PFunConverter.Reach (PFunConverter.simpleFn c d) p := by
  induction reachable with
  | first input => exact PFunConverter.Reach.first input
  | answer reachable query answer induction =>
      exact PFunConverter.Reach.answer induction
        (simpleFn_eq_ofStep_on_reach c d induction ▸ query) answer
  | next reachable output input induction =>
      exact PFunConverter.Reach.next induction
        (simpleFn_eq_ofStep_on_reach c d induction ▸ output) input

/-- The elementary `simpleFn c d` presentation is trace-equivalent to the
canonical one-query outer-memoryless step presentation. -/
theorem traceEquiv_simpleFn_ofStep (c : U → X) (d : Y → V) :
    PFunConverter.TraceEquiv (PFunConverter.simpleFn c d)
      (ofStep (PFunConverter.DDC.simpleStep c d) (fun _ => 1)) := by
  apply PFunConverter.traceEquiv_of_eqOn_reach
  · intro pair reachable
    exact simpleFn_eq_ofStep_on_reach c d reachable
  · intro pair reachable
    exact (simpleFn_eq_ofStep_on_reach c d
      (reach_ofStep_imp_reach_simpleFn c d reachable)).symm

/-- Protocol-function application of a simple converter agrees with the
paper-facing DDC simple converter on every deterministic system. -/
theorem apply_simpleFn_eq_simple_apply (c : U → X) (d : Y → V)
    (system : PFunDDS.DDS X Y) :
    PFunConverter.apply (PFunConverter.simpleFn c d) system =
      PFunConverter.DDC.apply (PFunConverter.DDC.simple c d) system := by
  calc
    PFunConverter.apply (PFunConverter.simpleFn c d) system =
        PFunConverter.DDC.apply
          (PFunConverter.toDDC (PFunConverter.simpleFn c d)) system :=
      (PFunConverter.apply_toDDC _ _).symm
    _ = PFunConverter.DDC.apply
        (PFunConverter.toDDC
          (ofStep (PFunConverter.DDC.simpleStep c d) (fun _ => 1))) system :=
      PFunConverter.apply_toDDC_congr
        (traceEquiv_simpleFn_ofStep c d) system
    _ = PFunConverter.apply
        (ofStep (PFunConverter.DDC.simpleStep c d) (fun _ => 1)) system :=
      PFunConverter.apply_toDDC _ _
    _ = CausalApply.applyG (PFunConverter.DDC.simpleStep c d) system.val := by
      apply apply_ofStep_eq_applyG
      intro input answers
      constructor
      · rintro ⟨query, queryEquation⟩
        cases answers with
        | nil => simp
        | cons answer rest =>
            simp [PFunConverter.DDC.simpleStep] at queryEquation
      · intro short
        have answersEmpty : answers = [] :=
          List.eq_nil_of_length_eq_zero (by omega)
        subst answersEmpty
        exact ⟨c input, rfl⟩
    _ = PFunConverter.DDC.apply
        (PFunConverter.DDC.simple c d) system := by
      exact (PFunConverter.DDC.apply_ofStep
        (PFunConverter.DDC.simpleStep c d) system).symm

/-! ### The outer-memoryless class, semantically -/

/-- **The outer-memoryless class** (CR18 Def 3.8), as a predicate on
protocol functions: `α` *is* an outer-memoryless step converter — some
step function and round budget, satisfying the boundary condition,
present it via `ofStep`.  Naming follows Mathlib's `IsUnit` pattern
(`IsUnit a ↔ ∃ u : Mˣ, ↑u = a`), taken off our own constructor `ofStep`
— flagged for user review.

Level choice: `ProtocolFn` equality is funext-extensional (these are
partial functions on history pairs), so membership is a property of the
converter term's *denotation*, not of its syntax — any
differently-written term denoting the same partial function is in the
class, and the difference between a step-style and a budget-style
*presentation* is already moot at this level.  The still-coarser
action-level class (`∀ S, PFunConverter.apply α S =
PFunConverter.apply (ofStep step cnt) S`, or up to `≡`) is future work
and deliberately not defined here. -/
def IsOfStep (α : PFunConverter.ProtocolFn U V X Y) : Prop :=
  ∃ (step : U → List Y → X ⊕ V) (cnt : U → ℕ),
    (∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u) ∧
      α = ofStep step cnt

/-- Class membership buys the automation: an `IsOfStep` protocol
function computes, under the transcript-equation `apply`, as
`CausalApply.applyG` of some step function — `apply_ofStep_eq_applyG`
transported through the membership witness. -/
theorem IsOfStep.apply_eq_applyG {α : PFunConverter.ProtocolFn U V X Y}
    (h : IsOfStep α) :
    ∃ step : U → List Y → X ⊕ V, ∀ S : PFunDDS.DDS X Y,
      PFunConverter.apply α S = CausalApply.applyG step S.1 := by
  obtain ⟨step, cnt, hcnt, rfl⟩ := h
  exact ⟨step, fun S => apply_ofStep_eq_applyG step cnt hcnt S⟩

/-- An `ofStep` converter is never silent at a nonempty outer history
whose inner answers are all proper: the dropped segment always
sequences, so the move is a `Part.some`.  This is the engine of the
class separations — budget-style converters (`θ`, `queryLimitFn`) go
silent over budget on exactly such pairs. -/
theorem ofStep_dom (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    {us : List U} (hne : us ≠ []) (ysY : List Y) :
    (ofStep step cnt (us, ysY.map some)).Dom := by
  have hmapM : ∀ l : List Y, (l.map some).mapM id = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [ofStep_apply step cnt hne (ysY.map some), ← List.map_drop, hmapM]
  trivial

/-- **`queryLimitFn` is genuinely outside the outer-memoryless class**
(the claim of the `ProtocolFn` module docstring, proved): over budget
the `[q]` filter goes *silent* on an all-proper history, where every
`ofStep` converter still moves (`ofStep_dom`).  Nondegeneracy: an outer
query and an inner answer must exist to build the over-budget pair. -/
theorem not_isOfStep_queryLimitFn [Nonempty X] [Nonempty Y] (q : ℕ) :
    ¬ IsOfStep (PFunConverter.queryLimitFn (X := X) (Y := Y) q) := by
  rintro ⟨step, cnt, -, heq⟩
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hdom : (PFunConverter.queryLimitFn q
      (List.replicate q x₀ ++ [x₀], (List.replicate q y₀).map some)).Dom := by
    rw [heq]
    exact ofStep_dom step cnt (by simp) _
  have hnone : PFunConverter.queryLimitFn q
      (List.replicate q x₀ ++ [x₀], (List.replicate q y₀).map some)
      = Part.none := by
    unfold PFunConverter.queryLimitFn
    split_ifs with h1 h2
    · exact absurd h1.2 (by
        simp only [List.length_append, List.length_replicate,
          List.length_cons, List.length_nil]
        omega)
    · exact absurd h2.1 (by
        simp only [List.length_append, List.length_replicate,
          List.length_cons, List.length_nil, List.length_map]
        omega)
    · rfl
  rw [hnone] at hdom
  exact Part.not_none_dom hdom

/-! ### `ofStep` converters are DDCs (CR18 Def 3.8)

The two Def 3.8 clauses for the outer-memoryless class: the tree
bookkeeping of a step converter (under the boundary condition) confines
a `⊥` answer to the open round's segment, where the `mapM` sequencing
refuses — and a uniform bound on the round budgets bounds the query
streaks. -/

/-- Tree bookkeeping of a step converter: every tree pair has consumed
at least the completed rounds' budgets, and a `⊥` can only sit in the
open round's segment. -/
theorem reach_ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    {p : List U × List (Option Y)}
    (hr : PFunConverter.Reach (ofStep step cnt) p) :
    (p.1.dropLast.map cnt).sum ≤ p.2.length ∧
      (none ∈ p.2 →
        none ∈ p.2.drop ((p.1.dropLast.map cnt).sum)) := by
  induction hr with
  | first u => exact ⟨by simp, by simp⟩
  | answer hrp hx y ih =>
      rename_i us ys x
      have ih1 : (us.dropLast.map cnt).sum ≤ ys.length := ih.1
      have ih2 : none ∈ ys →
          none ∈ ys.drop ((us.dropLast.map cnt).sum) := ih.2
      obtain ⟨ysY, hdrop, -⟩ :=
        (mem_ofStep_iff step cnt hrp.ne_nil ys _).mp hx
      constructor
      · show (us.dropLast.map cnt).sum ≤ (ys ++ [y]).length
        simp only [List.length_append, List.length_singleton]
        omega
      · show none ∈ ys ++ [y] →
            none ∈ (ys ++ [y]).drop ((us.dropLast.map cnt).sum)
        intro hn
        rcases List.mem_append.mp hn with hn' | hn'
        · exfalso
          have hseg := ih2 hn'
          rw [hdrop] at hseg
          simp at hseg
        · have hy : y = none := (List.mem_singleton.mp hn').symm
          subst hy
          rw [List.drop_append_of_le_length ih1]
          simp
  | next hrp hv u ih =>
      rename_i us ys v
      have ih1 : (us.dropLast.map cnt).sum ≤ ys.length := ih.1
      have ih2 : none ∈ ys →
          none ∈ ys.drop ((us.dropLast.map cnt).sum) := ih.2
      obtain ⟨ysY, hdrop, hval⟩ :=
        (mem_ofStep_iff step cnt hrp.ne_nil ys _).mp hv
      have hge : ¬ ysY.length < cnt (us.getLast hrp.ne_nil) :=
        not_lt_cnt_of_eq_inr hcnt hval.symm
      have hlY : ysY.length
          = ys.length - (us.dropLast.map cnt).sum := by
        have hl := congrArg List.length hdrop
        simp only [List.length_drop, List.length_map] at hl
        omega
      have hsplitA : (us.map cnt).sum
          = (us.dropLast.map cnt).sum + cnt (us.getLast hrp.ne_nil) :=
        sum_map_dropLast_getLast cnt hrp.ne_nil
      constructor
      · show ((us ++ [u]).dropLast.map cnt).sum ≤ ys.length
        rw [List.dropLast_concat]
        omega
      · show none ∈ ys →
            none ∈ ys.drop (((us ++ [u]).dropLast.map cnt).sum)
        intro hn
        exfalso
        have hseg := ih2 hn
        rw [hdrop] at hseg
        simp at hseg

/-- A step converter never moves past a `⊥` (Def 3.8's input-alphabet
clause). -/
theorem answersInY_ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u) :
    PFunConverter.AnswersInY (ofStep step cnt) := by
  intro p hr hn hd
  obtain ⟨-, h2⟩ := reach_ofStep step cnt hcnt hr
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  obtain ⟨ysY, hdrop, -⟩ :=
    (mem_ofStep_iff step cnt hr.ne_nil p.2 m).mp hm
  have hseg := h2 hn
  rw [hdrop] at hseg
  simp at hseg

/-- Uniformly bounded budgets bound a step converter's query streaks
(Def 3.8's finite-bound clause). -/
theorem answersWithin_ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    {L : ℕ} (hLb : ∀ u, cnt u ≤ L) :
    PFunConverter.AnswersWithin (ofStep step cnt) (L + 1) := by
  intro p hr ext hlen hall
  have h1 := (reach_ofStep step cnt hcnt hr).1
  obtain ⟨xL, hxL⟩ := hall L (by omega)
  obtain ⟨ysY, hdrop, hval⟩ :=
    (mem_ofStep_iff step cnt hr.ne_nil (p.2 ++ ext.take L) _).mp hxL
  have hlt := (hcnt _ _).mp ⟨xL, hval.symm⟩
  have hcL := hLb (p.1.getLast hr.ne_nil)
  have hlY := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append, List.length_take,
    List.length_map] at hlY
  omega

/-- **`ofStep` converters are DDCs** (CR18 Def 3.8): the boundary
condition delivers the input-alphabet clause, a uniform budget bound the
finite-bound clause. -/
theorem isDDC_ofStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    (hL : ∃ L, ∀ u, cnt u ≤ L) :
    PFunConverter.IsDDC (ofStep step cnt) := by
  obtain ⟨L, hLb⟩ := hL
  exact ⟨answersInY_ofStep step cnt hcnt, L + 1,
    answersWithin_ofStep step cnt hcnt hLb⟩

/-! ### Filter exchange: an inner query limit against a step converter

`comp (ofStep step cnt) (queryLimitFn r)` is characterized against the
bare `ofStep step cnt`: at every *replay-consistent* pair within the
outer weight budget `(us.map cnt).sum ≤ r`, the `[r]` filter is
invisible — an inner query limit pulls through an outer-memoryless step
converter as an outer weight filter.  Consistency is three-fold: the
consumed answers cover all completed rounds
(`(us.dropLast.map cnt).sum ≤ |ysDone|`), do not overrun the current one
(`|ysDone| ≤ (us.map cnt).sum`), **and the pre-offset part of `ysDone`
is all-proper** — the filter replays *every* answer and stalls on `⊥`,
while `ofStep` drops the completed rounds unseen, so a junk answer in an
earlier round genuinely separates the two.  At inconsistent pairs the
equation fails; gated composition (`comp_congr_right_of_gate`) only ever
consults consistent ones. -/

/-- The replay walker (forward direction of the filter exchange): from a
mid-replay state of the `ofStep`/`[r]` stack over a proper answer list
within the budget, the flat replay reaches the one-move value `ofStep`
computes directly — each consumed answer costs one forwarded query, and
the budget `r` covers them all. -/
private theorem compGo_ofStep_queryLimitFn_walk
    (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    {r : ℕ} {us : List U} (hne : us ≠ []) {ysX : List Y}
    (hwt : (us.map cnt).sum ≤ r)
    (hoff : (us.dropLast.map cnt).sum ≤ ysX.length)
    (hupper : ysX.length ≤ (us.map cnt).sum) :
    ∀ (n : ℕ) (usAct usRest : List U) (t : ℕ) (qs : List X),
      us = usAct ++ usRest → ∀ _hAne : usAct ≠ [],
      (usAct.dropLast.map cnt).sum ≤ t →
      t ≤ (usAct.map cnt).sum →
      t ≤ ysX.length → qs.length = t →
      (ysX.length - t) + usRest.length ≤ n →
      ∃ fuel,
        step (us.getLast hne) (ysX.drop ((us.dropLast.map cnt).sum))
          ∈ PFunConverter.compGo (ofStep step cnt)
              (PFunConverter.queryLimitFn r) fuel
              usAct usRest ((ysX.take t).map some) qs
              ((ysX.take t).map some) ((ysX.drop t).map some) false := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro usAct usRest t qs hsplit hAne hofft htwt htK hqs hmeas
  have hsplitA : (usAct.map cnt).sum
      = (usAct.dropLast.map cnt).sum + cnt (usAct.getLast hAne) :=
    sum_map_dropLast_getLast cnt hAne
  have hOfval := ofStep_apply_map_some step cnt hAne (ysX.take t)
  have hseglen : ((ysX.take t).drop ((usAct.dropLast.map cnt).sum)).length
      = t - (usAct.dropLast.map cnt).sum := by
    simp only [List.length_drop, List.length_take]
    omega
  by_cases hround : t < (usAct.map cnt).sum
  · -- mid-round: `ofStep` queries
    obtain ⟨x, hx⟩ := (hcnt (usAct.getLast hAne)
        ((ysX.take t).drop ((usAct.dropLast.map cnt).sum))).mpr
      (by rw [hseglen]; omega)
    have hmOf : Sum.inl x ∈ ofStep step cnt (usAct, (ysX.take t).map some) := by
      rw [hOfval, Part.mem_some_iff, hx]
    by_cases htlt : t < ysX.length
    · -- an answer is available: forward, consume, relay, recurse
      have hmQ : Sum.inl x ∈ PFunConverter.queryLimitFn r
          (qs ++ [x], (ysX.take t).map some) := by
        have h1 : (qs ++ [x]).length = ((ysX.take t).map some).length + 1 := by
          simp only [List.length_append, List.length_singleton,
            List.length_map, List.length_take]
          omega
        have h2 : (qs ++ [x]).length ≤ r := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hm := PFunConverter.queryLimitFn_inl_mem r h1 h2
        rwa [List.getLast_append_singleton] at hm
      have hget : (ysX.take (t + 1)).map some
          = (ysX.take t).map some ++ [some (ysX[t]'htlt)] := by
        rw [← List.take_concat_get' ysX t htlt, List.map_append]
        simp only [List.map_cons, List.map_nil]
      have hmR : Sum.inr (ysX[t]'htlt) ∈ PFunConverter.queryLimitFn r
          (qs ++ [x], (ysX.take (t + 1)).map some) := by
        refine PFunConverter.queryLimitFn_inr_mem r ?_ ?_ ?_ ?_
        · simp only [List.length_append, List.length_singleton,
            List.length_map, List.length_take]
          omega
        · simp only [List.length_map, List.length_take]
          omega
        · simp only [List.length_append, List.length_singleton]
          omega
        · simp only [hget]
          exact List.getLast_append_singleton _
      obtain ⟨f, hf⟩ := ih (n - 1) (by
          rcases usRest with _ | ⟨w, rest⟩ <;>
            simp only [List.length_nil, List.length_cons] at hmeas <;> omega)
        usAct usRest (t + 1) (qs ++ [x]) hsplit hAne (by omega) (by omega)
        (by omega) (by simp [hqs]) (by
          rcases usRest with _ | ⟨w, rest⟩ <;>
            simp only [List.length_nil, List.length_cons] at hmeas ⊢ <;>
            omega)
      refine ⟨f + 3, ?_⟩
      apply PFunConverter.compGo_mem_query2 hmOf
      rw [show (ysX.drop t).map some
          = some (ysX[t]'htlt) :: (ysX.drop (t + 1)).map some by
        rw [List.drop_eq_getElem_cons htlt]
        simp only [List.map_cons]]
      apply PFunConverter.compGo_mem_consume hmQ
      rw [← hget]
      apply PFunConverter.compGo_mem_answer1 hmR
      rw [← hget]
      exact hf
    · -- base answers exhausted mid-round: the pending query exits
      have htKe : t = ysX.length := by omega
      have hrest : usRest = [] := by
        rcases usRest with _ | ⟨w, rest⟩
        · rfl
        · exfalso
          have hoff' := hoff
          rw [hsplit, sum_map_dropLast_append_cons] at hoff'
          omega
      subst hrest
      rw [List.append_nil] at hsplit
      subst hsplit
      subst htKe
      simp only [List.take_length] at hmOf hx
      have hxval : step (us.getLast hne)
          (ysX.drop ((us.dropLast.map cnt).sum)) = Sum.inl x := hx
      rw [hxval]
      have hmQ : Sum.inl x ∈ PFunConverter.queryLimitFn r
          (qs ++ [x], ysX.map some) := by
        have h1 : (qs ++ [x]).length = (ysX.map some).length + 1 := by
          simp only [List.length_append, List.length_singleton,
            List.length_map]
          omega
        have h2 : (qs ++ [x]).length ≤ r := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hm := PFunConverter.queryLimitFn_inl_mem r h1 h2
        rwa [List.getLast_append_singleton] at hm
      refine ⟨2, ?_⟩
      simp only [List.take_length, List.drop_length, List.map_nil]
      apply PFunConverter.compGo_mem_query2 hmOf
      exact PFunConverter.compGo_mem_exit1 hmQ
  · -- round complete: `ofStep` answers
    have htwtA : t = (usAct.map cnt).sum := by omega
    rcases hcs : step (usAct.getLast hAne)
        ((ysX.take t).drop ((usAct.dropLast.map cnt).sum)) with x | v
    · exact absurd ((hcnt _ _).mp ⟨x, hcs⟩) (by rw [hseglen]; omega)
    · have hmOf : Sum.inr v ∈ ofStep step cnt
          (usAct, (ysX.take t).map some) := by
        rw [hOfval, Part.mem_some_iff, hcs]
      rcases usRest with _ | ⟨w, rest⟩
      · -- all rounds complete: the final answer exits
        rw [List.append_nil] at hsplit
        subst hsplit
        have hKt : t = ysX.length := by omega
        subst hKt
        simp only [List.take_length] at hmOf hcs
        have hval : step (us.getLast hne)
            (ysX.drop ((us.dropLast.map cnt).sum)) = Sum.inr v := hcs
        rw [hval]
        refine ⟨1, ?_⟩
        simp only [List.take_length, List.drop_length, List.map_nil]
        exact PFunConverter.compGo_mem_exit2 hmOf
      · -- deliver the next message
        obtain ⟨f, hf⟩ := ih (n - 1) (by
            simp only [List.length_cons] at hmeas
            omega)
          (usAct ++ [w]) rest t qs (by rw [hsplit]; simp) (by simp)
          (by rw [List.dropLast_concat]; omega)
          (by rw [List.map_append, List.sum_append]; omega)
          htK hqs (by simp only [List.length_cons] at hmeas; omega)
        exact ⟨f + 1, PFunConverter.compGo_mem_advance hmOf hf⟩

/-- The replay extractor (backward direction of the filter exchange): a
converged flat replay of the `ofStep`/`[r]` stack from a consistent
mid-state computes `ofStep`'s own one-move value at the full pair — each
`[r]` relay certifies the consumed answer proper, and the exits land
exactly on `ofStep`'s move. -/
private theorem compGo_ofStep_queryLimitFn_extract
    (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    {r : ℕ} {us : List U} {ysDone : List (Option Y)} :
    ∀ (fuel : ℕ) (usAct usRest : List U) (t : ℕ) (qs : List X)
      (ytX : List Y) (mv : X ⊕ V),
      us = usAct ++ usRest → ∀ _hAne : usAct ≠ [],
      (usAct.dropLast.map cnt).sum ≤ t →
      t ≤ (usAct.map cnt).sum →
      t ≤ ysDone.length → qs.length = t → ytX.length = t →
      ysDone.take t = ytX.map some →
      mv ∈ PFunConverter.compGo (ofStep step cnt)
        (PFunConverter.queryLimitFn r) fuel usAct usRest (ytX.map some) qs
        (ytX.map some) (ysDone.drop t) false →
      mv ∈ ofStep step cnt (us, ysDone) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro usAct usRest t qs ytX mv hsplit hAne hofft htwt htK hqs hyt htake h
  have hsplitA : (usAct.map cnt).sum
      = (usAct.dropLast.map cnt).sum + cnt (usAct.getLast hAne) :=
    sum_map_dropLast_getLast cnt hAne
  have hOfval := ofStep_apply_map_some step cnt hAne ytX
  have hseglen : (ytX.drop ((usAct.dropLast.map cnt).sum)).length
      = t - (usAct.dropLast.map cnt).sum := by
    simp only [List.length_drop]
    omega
  rcases fuel with _ | f
  · simp [PFunConverter.compGo] at h
  rcases PFunConverter.compGo_elim2 h with
    ⟨x, hmOf, h'⟩ | ⟨z, w, rest, hmOf, hwr, h'⟩ |
    ⟨z, hmOf, hwr, hyr, hmv⟩
  · -- `ofStep` queries
    rw [hOfval, Part.mem_some_iff] at hmOf
    have hlt : t - (usAct.dropLast.map cnt).sum
        < cnt (usAct.getLast hAne) := by
      have hl := (hcnt (usAct.getLast hAne) _).mp ⟨x, hmOf.symm⟩
      rwa [hseglen] at hl
    rcases f with _ | f₂
    · simp [PFunConverter.compGo] at h'
    rcases PFunConverter.compGo_elim1 h' with
      ⟨v, hmQ, -⟩ | ⟨x', y, rest', hmQ, hyr, h''⟩ |
      ⟨x', hmQ, hyr, hwr, hmv⟩
    · -- `[r]` cannot answer at a query-pending pair
      exfalso
      obtain ⟨hlen, -⟩ := PFunConverter.queryLimitFn_inr_inv hmQ
      simp only [List.length_append, List.length_singleton,
        List.length_map] at hlen
      omega
    · -- `[r]` forwards and an answer is consumed
      have hlt' : t < ysDone.length := by
        have hl := congrArg List.length hyr
        simp only [List.length_drop, List.length_cons] at hl
        omega
      rw [List.drop_eq_getElem_cons hlt'] at hyr
      injection hyr with hy1 hy2
      subst hy1
      subst hy2
      rcases f₂ with _ | f₃
      · simp [PFunConverter.compGo] at h''
      rcases PFunConverter.compGo_elim1 h'' with
        ⟨v, hmQ2, h'''⟩ | ⟨x'', y₂, rest₂, hmQ2, -, -⟩ |
        ⟨x'', hmQ2, -, -, -⟩
      · -- the relay certifies the consumed answer proper
        obtain ⟨-, -, h0, hgl⟩ := PFunConverter.queryLimitFn_inr_inv hmQ2
        rw [List.getLast_append_singleton] at hgl
        have hcomb : ytX.map some ++ [some v] = (ytX ++ [v]).map some := by
          simp only [List.map_append, List.map_cons, List.map_nil]
        have htake' : ysDone.take (t + 1) = (ytX ++ [v]).map some := by
          rw [← List.take_concat_get' ysDone t hlt', htake, hgl, hcomb]
        rw [hgl, hcomb] at h'''
        exact ih f₃ (by omega) usAct usRest (t + 1) (qs ++ [x])
          (ytX ++ [v]) mv hsplit hAne (by omega) (by omega) (by omega)
          (by simp [hqs]) (by simp [hyt]) htake' h'''
      · exfalso
        obtain ⟨hlen2, -⟩ := PFunConverter.queryLimitFn_inl_inv hmQ2
        simp only [List.length_append, List.length_singleton,
          List.length_map] at hlen2
        omega
      · exfalso
        obtain ⟨hlen2, -⟩ := PFunConverter.queryLimitFn_inl_inv hmQ2
        simp only [List.length_append, List.length_singleton,
          List.length_map] at hlen2
        omega
    · -- base exhausted: the pending query exits as the composite's value
      have htlen : t = ysDone.length := by
        have hl := congrArg List.length hyr
        simp only [List.length_drop, List.length_nil] at hl
        omega
      obtain ⟨hne2, hval⟩ := PFunConverter.queryLimitFn_inl_val hmQ
      rw [List.getLast_append_singleton] at hval
      subst hwr
      rw [List.append_nil] at hsplit
      subst hsplit
      have hfull : ysDone = ytX.map some := by
        rw [← htake, htlen, List.take_length]
      subst hmv
      subst hval
      rw [hfull, hOfval, Part.mem_some_iff]
      exact hmOf
  · -- `ofStep` answers, the next message is delivered
    rw [hOfval, Part.mem_some_iff] at hmOf
    have hge := not_lt_cnt_of_eq_inr hcnt hmOf.symm
    rw [hseglen] at hge
    subst hwr
    exact ih f (by omega) (usAct ++ [w]) rest t qs ytX mv
      (by rw [hsplit]; simp) (by simp)
      (by rw [List.dropLast_concat]; omega)
      (by rw [List.map_append, List.sum_append]; omega)
      htK hqs hyt htake h'
  · -- all rounds complete: the final answer is `ofStep`'s move
    have htlen : t = ysDone.length := by
      have hl := congrArg List.length hyr
      simp only [List.length_drop, List.length_nil] at hl
      omega
    subst hwr
    rw [List.append_nil] at hsplit
    subst hsplit
    have hfull : ysDone = ytX.map some := by
      rw [← htake, htlen, List.take_length]
    subst hmv
    rw [hfull, hOfval, Part.mem_some_iff]
    rw [hOfval, Part.mem_some_iff] at hmOf
    exact hmOf

/-- **Filter exchange** (CR18 §6.2.3's "the filter is irrelevant", made
generic): at a replay-consistent pair within the outer weight budget,
the inner query limit `[r]` composed behind an outer-memoryless step
converter is invisible — the filtered composite has exactly the step
converter's one-move value.  Consistency includes the pre-offset
properness of the answers (see the section docstring); at inconsistent
pairs the two sides genuinely differ. -/
theorem comp_ofStep_queryLimitFn_apply
    (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u)
    {r : ℕ} {A : List U} (hAne : A ≠ []) {ysDone : List (Option Y)}
    (hoff : (A.dropLast.map cnt).sum ≤ ysDone.length)
    (hupper : ysDone.length ≤ (A.map cnt).sum)
    (hwt : (A.map cnt).sum ≤ r)
    (hproper : ∃ preY : List Y,
      ysDone.take ((A.dropLast.map cnt).sum) = preY.map some) :
    PFunConverter.comp (ofStep step cnt) (PFunConverter.queryLimitFn r)
      (A, ysDone) = ofStep step cnt (A, ysDone) := by
  obtain ⟨preY, hpre⟩ := hproper
  have hpreLen : preY.length = (A.dropLast.map cnt).sum := by
    have hl := congrArg List.length hpre
    simp only [List.length_take, List.length_map] at hl
    omega
  apply Part.ext
  intro mv
  rcases A with _ | ⟨u₀, usT⟩
  · exact absurd rfl hAne
  rw [PFunConverter.mem_comp_cons]
  constructor
  · rintro ⟨fuel, h⟩
    exact compGo_ofStep_queryLimitFn_extract step cnt hcnt
      fuel [u₀] usT 0 [] [] mv rfl (by simp) (by simp) (by simp)
      (by simp) rfl rfl rfl h
  · intro hmem
    obtain ⟨segY, hdrop, hval⟩ :=
      (mem_ofStep_iff step cnt hAne ysDone mv).mp hmem
    have hdropX : (preY ++ segY).drop
        (((u₀ :: usT).dropLast.map cnt).sum) = segY := by
      rw [← hpreLen]
      exact List.drop_left
    have hfull : ysDone = (preY ++ segY).map some := by
      conv_lhs => rw [← List.take_append_drop
        (((u₀ :: usT).dropLast.map cnt).sum) ysDone]
      rw [hpre, hdrop, List.map_append]
    have hlenX : (preY ++ segY).length = ysDone.length := by
      rw [hfull]
      simp
    obtain ⟨fuel, hrun⟩ := compGo_ofStep_queryLimitFn_walk step cnt hcnt
      (us := u₀ :: usT) hAne (ysX := preY ++ segY) hwt (by omega)
      (by omega) (ysDone.length + usT.length) [u₀] usT 0 [] rfl
      (by simp) (by simp) (by simp) (by simp) rfl (by omega)
    rw [hdropX] at hrun
    refine ⟨fuel, ?_⟩
    rw [hfull]
    rw [hval]
    exact hrun

/-! ### History-aware step converters

`ofStep` hands its step function only the *current* outer message
(`p.1.getLast`), so an `ofStep` converter cannot count its own outer
invocations, carry a sequence number, or hold any session state.  Nothing in
the carrier requires that: `PFunConverter.ProtocolFn` takes the whole outer
history, and CR18 Def 3.8 (`PFunConverter.IsDDC`) constrains only the `⊥`
discipline and the length of query streaks — neither clause forbids memory.

`ofHistoryStep` is the constructor at the carrier's actual strength, beside
`ofStep` and purely additive to it: `step` receives the whole outer history
`us` (with its nonemptiness, which is what `us.getLast` and any "which round
am I in?" test need), and the per-round inner-query count is generalized from
`cnt : U → ℕ` to `cnt : List U → ℕ` — the count of the round *ending at* an
outer prefix, so the number of inner queries a round spends may itself depend
on the history.  Round boundaries become the prefix sum `roundOffset`, and
`ofStep` is recovered exactly — by raw function equality, not merely up to
`PFunConverter.TraceEquiv` — at the history-ignoring instance
(`ofStep_eq_ofHistoryStep`). -/

/-- **The round offset of an outer history**: the number of inner answers
consumed by the rounds *already completed* at outer history `us` — the sum of
the per-round counts over the nonempty proper prefixes of `us`, i.e. over the
rounds ending at `us.take 1, …, us.take (us.length - 1)`.  The
history-indexed counterpart of `ofStep`'s `(us.dropLast.map cnt).sum`, which
it reproduces whenever `cnt` reads only its argument's last message
(`roundOffset_memoryless`).

Only two facts about it are ever used below — `roundOffset_of_length_le_one`
(the opening round has consumed nothing) and `roundOffset_concat` (a further
outer message adds exactly the count of the round it closes) — and together
they replace `ofStep`'s `sum_map_dropLast_getLast` splitting step in every
proof of this section.  `cnt []` is never consulted (the sum is empty at
`us = []`), so the count needs no junk convention at the empty history. -/
def roundOffset (cnt : List U → ℕ) (us : List U) : ℕ :=
  ((List.range (us.length - 1)).map fun i => cnt (us.take (i + 1))).sum

/-- At the opening round nothing has been consumed. -/
theorem roundOffset_of_length_le_one (cnt : List U → ℕ) {us : List U}
    (h : us.length ≤ 1) : roundOffset cnt us = 0 := by
  have hz : us.length - 1 = 0 := by omega
  simp [roundOffset, hz]

/-- A further outer message closes the round ending at `us`, adding exactly
that round's own count to the offset. -/
theorem roundOffset_concat (cnt : List U → ℕ) {us : List U} (hne : us ≠ [])
    (u : U) : roundOffset cnt (us ++ [u]) = roundOffset cnt us + cnt us := by
  obtain ⟨m, hm⟩ : ∃ m, us.length = m + 1 :=
    ⟨us.length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
  simp only [roundOffset, List.length_append, List.length_singleton, hm,
    Nat.add_sub_cancel]
  rw [List.range_succ, List.map_append, List.sum_append]
  congr 1
  · congr 1
    refine List.map_congr_left ?_
    intro i hi
    rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    rw [List.take_append_of_le_length (by omega), ← hm, List.take_length]

/-- **The history-aware step converter** (CR18 Def 3.8), in the
protocol-function carrier: at outer messages `us` and cumulative inner
answers `ys` (in the `Y ∪ {⊥}` alphabet of Def 3.8), the current round is the
one opened by the last message, its answer segment is what is left after
discounting the `roundOffset` consumed by the completed rounds, and the move
is `step` applied to **the whole outer history** and the sequenced segment —
silent unless every answer of the open round is proper (`List.mapM id`
sequences the segment).

Identical to `ofStep` except in the two places where memory lives: `step`
sees `us`, not `us.getLast`, and the round count is indexed by the outer
prefix.  `step` takes the nonemptiness proof rather than returning junk at
`[]`: at every pair a converter is ever consulted at the outer history is
nonempty (`PFunConverter.Reach.ne_nil`), so the proof is always available, it
is exactly what `us.getLast` needs, and carrying it lets `ofStep` be
specialized (`ofStep_eq_ofHistoryStep`) with no junk value and hence no
`Inhabited`/`Nonempty` side condition on `X ⊕ V`.  Cost: a converter with no
use for the proof writes `fun us _ ys => …`. -/
def ofHistoryStep (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ) : PFunConverter.ProtocolFn U V X Y := fun p =>
  if h : p.1 ≠ [] then
    match (p.2.drop (roundOffset cnt p.1)).mapM id with
    | some ys => Part.some (step p.1 h ys)
    | none => Part.none
  else Part.none

/-- `ofHistoryStep`'s move at a pair, computed (the twin of
`ofStep_apply`). -/
theorem ofHistoryStep_apply (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) (ys : List (Option Y)) :
    ofHistoryStep step cnt (us, ys) =
      match (ys.drop (roundOffset cnt us)).mapM id with
      | some ysY => Part.some (step us hne ysY)
      | none => Part.none := by
  unfold ofHistoryStep
  rw [dif_pos (show (us, ys).1 ≠ [] from hne)]

/-- `ofHistoryStep`'s move at a proper answer list, computed (the twin of
`ofStep_apply_map_some`). -/
theorem ofHistoryStep_apply_map_some
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    {us : List U} (hne : us ≠ []) (l : List Y) :
    ofHistoryStep step cnt (us, l.map some)
      = Part.some (step us hne (l.drop (roundOffset cnt us))) := by
  rw [ofHistoryStep_apply step cnt hne (l.map some), ← List.map_drop,
    mapM_id_map_some]

/-- `ofHistoryStep`'s membership, characterized (the twin of
`mem_ofStep_iff`): the dropped segment sequences and the move is `step` on
the history and that segment. -/
theorem mem_ofHistoryStep_iff (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) (ys : List (Option Y))
    (mv : X ⊕ V) :
    mv ∈ ofHistoryStep step cnt (us, ys) ↔
      ∃ ysY : List Y,
        ys.drop (roundOffset cnt us) = ysY.map some ∧ mv = step us hne ysY := by
  rw [ofHistoryStep_apply step cnt hne ys]
  cases hseg : (ys.drop (roundOffset cnt us)).mapM id with
  | none =>
      constructor
      · intro hm
        simp at hm
      · rintro ⟨ysY, hdrop, -⟩
        rw [hdrop, mapM_id_map_some] at hseg
        simp at hseg
  | some l =>
      have hl := eq_map_some_of_mapM_id_eq_some hseg
      constructor
      · intro hm
        rw [Part.mem_some_iff] at hm
        exact ⟨l, hl, hm⟩
      · rintro ⟨ysY, hdrop, rfl⟩
        rw [Part.mem_some_iff]
        have hxl : ysY = l :=
          List.map_injective_iff.mpr (Option.some_injective Y)
            (hdrop.symm.trans hl)
        rw [hxl]

/-- A history-aware step converter is never silent at a nonempty outer
history whose inner answers are all proper (the twin of `ofStep_dom`). -/
theorem ofHistoryStep_dom (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) (ysY : List Y) :
    (ofHistoryStep step cnt (us, ysY.map some)).Dom := by
  rw [ofHistoryStep_apply_map_some step cnt hne ysY]
  trivial

/-- Sum dichotomy through the history-indexed boundary condition: an `inr`
move means the round's budget is exhausted.  (The memoryless
`not_lt_cnt_of_eq_inr` cannot be instantiated here — its `step` does not take
the nonemptiness proof this one's does.) -/
theorem not_lt_cnt_of_eq_inr_hist
    {step : (us : List U) → us ≠ [] → List Y → X ⊕ V} {cnt : List U → ℕ}
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    {us : List U} (hne : us ≠ []) {ys : List Y} {v : V}
    (h : step us hne ys = Sum.inr v) : ¬ ys.length < cnt us := by
  intro hlt
  obtain ⟨x, hx⟩ := (hcnt us hne ys).mpr hlt
  rw [h] at hx
  simp at hx

/-- Tree bookkeeping of a history-aware step converter (the twin of
`reach_ofStep`): every tree pair has consumed at least the completed rounds'
counts, and a `⊥` can only sit in the open round's segment. -/
theorem reach_ofHistoryStep (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    {p : List U × List (Option Y)}
    (hr : PFunConverter.Reach (ofHistoryStep step cnt) p) :
    roundOffset cnt p.1 ≤ p.2.length ∧
      (none ∈ p.2 → none ∈ p.2.drop (roundOffset cnt p.1)) := by
  induction hr with
  | first u =>
      exact ⟨by simp [roundOffset_of_length_le_one cnt (us := [u]) (by simp)],
        by simp⟩
  | answer hrp hx y ih =>
      rename_i us ys x
      have hne : us ≠ [] := hrp.ne_nil
      have ih1 : roundOffset cnt us ≤ ys.length := ih.1
      have ih2 : none ∈ ys → none ∈ ys.drop (roundOffset cnt us) := ih.2
      obtain ⟨ysY, hdrop, -⟩ :=
        (mem_ofHistoryStep_iff step cnt hne ys _).mp hx
      refine ⟨?_, ?_⟩
      · show roundOffset cnt us ≤ (ys ++ [y]).length
        simp only [List.length_append, List.length_singleton]
        omega
      · show none ∈ ys ++ [y] → none ∈ (ys ++ [y]).drop (roundOffset cnt us)
        intro hn
        rcases List.mem_append.mp hn with hn' | hn'
        · exfalso
          have hseg := ih2 hn'
          rw [hdrop] at hseg
          simp at hseg
        · have hy : y = none := (List.mem_singleton.mp hn').symm
          subst hy
          rw [List.drop_append_of_le_length ih1]
          simp
  | next hrp hv u ih =>
      rename_i us ys v
      have hne : us ≠ [] := hrp.ne_nil
      have ih1 : roundOffset cnt us ≤ ys.length := ih.1
      have ih2 : none ∈ ys → none ∈ ys.drop (roundOffset cnt us) := ih.2
      obtain ⟨ysY, hdrop, hval⟩ :=
        (mem_ofHistoryStep_iff step cnt hne ys _).mp hv
      have hge : ¬ ysY.length < cnt us :=
        not_lt_cnt_of_eq_inr_hist hcnt hne hval.symm
      have hlY : ysY.length = ys.length - roundOffset cnt us := by
        have hl := congrArg List.length hdrop
        simp only [List.length_drop, List.length_map] at hl
        omega
      refine ⟨?_, ?_⟩
      · show roundOffset cnt (us ++ [u]) ≤ ys.length
        rw [roundOffset_concat cnt hne]
        omega
      · show none ∈ ys → none ∈ ys.drop (roundOffset cnt (us ++ [u]))
        intro hn
        exfalso
        have hseg := ih2 hn
        rw [hdrop] at hseg
        simp at hseg

/-- A history-aware step converter never moves past a `⊥` (Def 3.8's
input-alphabet clause; the twin of `answersInY_ofStep`). -/
theorem answersInY_ofHistoryStep
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us) :
    PFunConverter.AnswersInY (ofHistoryStep step cnt) := by
  intro p hr hn hd
  obtain ⟨-, h2⟩ := reach_ofHistoryStep step cnt hcnt hr
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  obtain ⟨ysY, hdrop, -⟩ :=
    (mem_ofHistoryStep_iff step cnt hr.ne_nil p.2 m).mp hm
  have hseg := h2 hn
  rw [hdrop] at hseg
  simp at hseg

/-- Uniformly bounded round counts bound a history-aware step converter's
query streaks (Def 3.8's finite-bound clause; the twin of
`answersWithin_ofStep`). -/
theorem answersWithin_ofHistoryStep
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    {L : ℕ} (hLb : ∀ us, cnt us ≤ L) :
    PFunConverter.AnswersWithin (ofHistoryStep step cnt) (L + 1) := by
  intro p hr ext hlen hall
  have h1 := (reach_ofHistoryStep step cnt hcnt hr).1
  obtain ⟨xL, hxL⟩ := hall L (by omega)
  obtain ⟨ysY, hdrop, hval⟩ :=
    (mem_ofHistoryStep_iff step cnt hr.ne_nil (p.2 ++ ext.take L) _).mp hxL
  have hlt := (hcnt _ hr.ne_nil _).mp ⟨xL, hval.symm⟩
  have hcL := hLb p.1
  have hlY := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append, List.length_take,
    List.length_map] at hlY
  omega

/-- **`ofHistoryStep` converters are DDCs** (CR18 Def 3.8) — the history-aware
twin of `isDDC_ofStep`, on the same two inputs: the boundary condition
delivers the input-alphabet clause, a uniform bound on the round counts the
finite-bound clause.

The uniformity is not slack introduced by the history indexing:
`PFunConverter.AnswersWithin` asks for a single bound `B` good at *every* pair
of the trace tree, so a bound that varied with the history would not close
that clause.  Memory itself stays unconstrained — what Def 3.8 bounds is the
length of query streaks, and nothing else.

The hypothesis `hL` is nevertheless stronger than CR18 Def 3.8's *prose*,
which asks only that the converter invoke the system finitely often at each
reachable pair: an unbounded `cnt` still satisfies
`PFunConverter.AnswersEventually`, and even
`PFunConverter.AnswersWithinDepth` whenever `cnt` is bounded on each length
of outer history.  `PFunConverter.roundGrowthFn` inhabits that gap.  What
consumes the uniform reading is not this construction but the fuel
accounting in `EmulateRealization.lean`; see the `AnswersWithinDepth`
docstring. -/
theorem isDDC_ofHistoryStep (step : (us : List U) → us ≠ [] → List Y → X ⊕ V)
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (hL : ∃ L, ∀ us, cnt us ≤ L) :
    PFunConverter.IsDDC (ofHistoryStep step cnt) := by
  obtain ⟨L, hLb⟩ := hL
  exact ⟨answersInY_ofHistoryStep step cnt hcnt, L + 1,
    answersWithin_ofHistoryStep step cnt hcnt hLb⟩

/-- A history-indexed count that reads only its argument's last message has
`ofStep`'s round offset. -/
theorem roundOffset_memoryless (cnt : U → ℕ) (us : List U) :
    roundOffset (fun vs => vs.getLast?.elim 0 cnt) us
      = (us.dropLast.map cnt).sum := by
  induction us using List.reverseRecOn with
  | nil => simp [roundOffset]
  | append_singleton A a ih =>
      rcases eq_or_ne A [] with rfl | hA
      · simp [roundOffset_of_length_le_one]
      · rw [roundOffset_concat _ hA, ih, List.dropLast_concat,
          sum_map_dropLast_getLast cnt hA]
        congr 1
        rw [List.getLast?_eq_some_getLast hA]
        rfl

/-- **`ofStep` is the history-ignoring special case** — the receipt that the
class was extended, not forked.  The outer-memoryless constructor *is*
`ofHistoryStep` at the step that reads only the history's last message and
the count that reads only that message, and the identification is raw
function equality — not merely `PFunConverter.TraceEquiv` — so every existing
use of `ofStep` is literally an instance of the general constructor. -/
theorem ofStep_eq_ofHistoryStep (step : U → List Y → X ⊕ V) (cnt : U → ℕ) :
    ofStep step cnt
      = ofHistoryStep (fun us hne ys => step (us.getLast hne) ys)
          (fun us => us.getLast?.elim 0 cnt) := by
  funext p
  unfold ofStep ofHistoryStep
  split_ifs with h
  · rw [roundOffset_memoryless]
  · rfl

/-! ### Silence inside a round: the partial history-step constructor

`ofHistoryStep`'s `step` returns `X ⊕ V`, so a converter built with it always
moves once its open round's answers are proper.  CR18 §3.4.3 does not require
that — Def 3.8 constrains only the `⊥` discipline and the length of query
streaks — and `ProtocolFn` is a *partial* function precisely so that a
converter may decline to move.  `ofHistoryStepPartial` is `ofHistoryStep` with
that freedom restored: `step` returns `Option (X ⊕ V)`, and `none` is silence.

The construction that needs it is the one-sided lift of a converter over a
parallel composition (Jost Prop. 2.2.3's second clause).  There the open
round's answer segment is located by *position*, so it may carry an answer
from the wrong component; no total map re-tags it (that would need a map
between the two components' output alphabets), and the honest move is to
decline.  Silence stalls the round forever, which is exactly what keeps
`roundOffset` aligned with the answers actually consumed.

Accordingly the boundary condition weakens from an equivalence to a
conditional one — *whenever it moves at all, it queries exactly while its
budget lasts* — and that is still enough for both Def 3.8 clauses:
`AnswersWithin` needs the forward half (never query past the budget) and
`AnswersInY` the backward half (never answer before it, or a round would
close early and the offset would over-drop). -/

/-- **The history-aware step converter that may go silent**: `ofHistoryStep`
with `step` valued in `Option (X ⊕ V)`, `none` meaning "no move here".  Round
location, the offset bookkeeping and the `⊥` discipline are unchanged. -/
def ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) : PFunConverter.ProtocolFn U V X Y := fun p =>
  if h : p.1 ≠ [] then
    match (p.2.drop (roundOffset cnt p.1)).mapM id with
    | some ys => Part.ofOption (step p.1 h ys)
    | none => Part.none
  else Part.none

/-- `ofHistoryStepPartial`'s move at a pair, computed. -/
theorem ofHistoryStepPartial_apply
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) (ys : List (Option Y)) :
    ofHistoryStepPartial step cnt (us, ys) =
      match (ys.drop (roundOffset cnt us)).mapM id with
      | some ysY => Part.ofOption (step us hne ysY)
      | none => Part.none := by
  unfold ofHistoryStepPartial
  rw [dif_pos (show (us, ys).1 ≠ [] from hne)]

/-- `ofHistoryStepPartial`'s membership, characterized: the dropped segment
sequences and `step` *moves* to `mv` on the history and that segment. -/
theorem mem_ofHistoryStepPartial_iff
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) (ys : List (Option Y))
    (mv : X ⊕ V) :
    mv ∈ ofHistoryStepPartial step cnt (us, ys) ↔
      ∃ ysY : List Y,
        ys.drop (roundOffset cnt us) = ysY.map some ∧
          step us hne ysY = some mv := by
  rw [ofHistoryStepPartial_apply step cnt hne ys]
  cases hseg : (ys.drop (roundOffset cnt us)).mapM id with
  | none =>
      constructor
      · intro hm
        simp at hm
      · rintro ⟨ysY, hdrop, -⟩
        rw [hdrop, mapM_id_map_some] at hseg
        simp at hseg
  | some l =>
      have hl := eq_map_some_of_mapM_id_eq_some hseg
      constructor
      · intro hm
        exact ⟨l, hl, Part.mem_ofOption.mp hm⟩
      · rintro ⟨ysY, hdrop, hmv⟩
        have hysY : ysY = l :=
          List.map_injective_iff.mpr (Option.some_injective Y)
            (hdrop.symm.trans hl)
        subst hysY
        exact Part.mem_ofOption.mpr hmv

/-- Sum dichotomy through the conditional boundary condition: an `inr` move
means the round's budget is exhausted. -/
theorem not_lt_cnt_of_eq_inr_hist_partial
    {step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V)}
    {cnt : List U → ℕ}
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    {us : List U} (hne : us ≠ []) {ys : List Y} {v : V}
    (h : step us hne ys = some (Sum.inr v)) : ¬ ys.length < cnt us := by
  intro hlt
  obtain ⟨x, hx⟩ := (hcnt us hne ys _ h).mpr hlt
  simp at hx

/-- Tree bookkeeping of a silent-capable step converter (the twin of
`reach_ofHistoryStep`): every tree pair has consumed at least the completed
rounds' counts, and a `⊥` can only sit in the open round's segment. -/
theorem reach_ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    {p : List U × List (Option Y)}
    (hr : PFunConverter.Reach (ofHistoryStepPartial step cnt) p) :
    roundOffset cnt p.1 ≤ p.2.length ∧
      (none ∈ p.2 → none ∈ p.2.drop (roundOffset cnt p.1)) := by
  induction hr with
  | first u =>
      exact ⟨by simp [roundOffset_of_length_le_one cnt (us := [u]) (by simp)],
        by simp⟩
  | answer hrp hx y ih =>
      rename_i us ys x
      have hne : us ≠ [] := hrp.ne_nil
      have ih1 : roundOffset cnt us ≤ ys.length := ih.1
      have ih2 : none ∈ ys → none ∈ ys.drop (roundOffset cnt us) := ih.2
      obtain ⟨ysY, hdrop, -⟩ :=
        (mem_ofHistoryStepPartial_iff step cnt hne ys _).mp hx
      refine ⟨?_, ?_⟩
      · show roundOffset cnt us ≤ (ys ++ [y]).length
        simp only [List.length_append, List.length_singleton]
        omega
      · show none ∈ ys ++ [y] → none ∈ (ys ++ [y]).drop (roundOffset cnt us)
        intro hn
        rcases List.mem_append.mp hn with hn' | hn'
        · exfalso
          have hseg := ih2 hn'
          rw [hdrop] at hseg
          simp at hseg
        · have hy : y = none := (List.mem_singleton.mp hn').symm
          subst hy
          rw [List.drop_append_of_le_length ih1]
          simp
  | next hrp hv u ih =>
      rename_i us ys v
      have hne : us ≠ [] := hrp.ne_nil
      have ih1 : roundOffset cnt us ≤ ys.length := ih.1
      have ih2 : none ∈ ys → none ∈ ys.drop (roundOffset cnt us) := ih.2
      obtain ⟨ysY, hdrop, hval⟩ :=
        (mem_ofHistoryStepPartial_iff step cnt hne ys _).mp hv
      have hge : ¬ ysY.length < cnt us :=
        not_lt_cnt_of_eq_inr_hist_partial hcnt hne hval
      have hlY : ysY.length = ys.length - roundOffset cnt us := by
        have hl := congrArg List.length hdrop
        simp only [List.length_drop, List.length_map] at hl
        omega
      refine ⟨?_, ?_⟩
      · show roundOffset cnt (us ++ [u]) ≤ ys.length
        rw [roundOffset_concat cnt hne]
        omega
      · show none ∈ ys → none ∈ ys.drop (roundOffset cnt (us ++ [u]))
        intro hn
        exfalso
        have hseg := ih2 hn
        rw [hdrop] at hseg
        simp at hseg

/-- A silent-capable step converter never moves past a `⊥`. -/
theorem answersInY_ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us)) :
    PFunConverter.AnswersInY (ofHistoryStepPartial step cnt) := by
  intro p hr hn hd
  obtain ⟨-, h2⟩ := reach_ofHistoryStepPartial step cnt hcnt hr
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  obtain ⟨ysY, hdrop, -⟩ :=
    (mem_ofHistoryStepPartial_iff step cnt hr.ne_nil p.2 m).mp hm
  have hseg := h2 hn
  rw [hdrop] at hseg
  simp at hseg

/-- Uniformly bounded round counts bound a silent-capable step converter's
query streaks. -/
theorem answersWithin_ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    {L : ℕ} (hLb : ∀ us, cnt us ≤ L) :
    PFunConverter.AnswersWithin (ofHistoryStepPartial step cnt) (L + 1) := by
  intro p hr ext hlen hall
  have h1 := (reach_ofHistoryStepPartial step cnt hcnt hr).1
  obtain ⟨xL, hxL⟩ := hall L (by omega)
  obtain ⟨ysY, hdrop, hval⟩ :=
    (mem_ofHistoryStepPartial_iff step cnt hr.ne_nil (p.2 ++ ext.take L) _).mp hxL
  have hlt := (hcnt _ hr.ne_nil _ _ hval).mp ⟨xL, rfl⟩
  have hcL := hLb p.1
  have hlY := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append, List.length_take,
    List.length_map] at hlY
  omega

/-- **Silent-capable `ofHistoryStep` converters are DDCs** (CR18 Def 3.8).
The boundary condition is conditional — *whenever it moves, it queries
exactly while its budget lasts* — because silence is now a third option;
that is still both clauses' worth of information. -/
theorem isDDC_ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (hL : ∃ L, ∀ us, cnt us ≤ L) :
    PFunConverter.IsDDC (ofHistoryStepPartial step cnt) := by
  obtain ⟨L, hLb⟩ := hL
  exact ⟨answersInY_ofHistoryStepPartial step cnt hcnt, L + 1,
    answersWithin_ofHistoryStepPartial step cnt hcnt hLb⟩

/-- **`ofHistoryStep` is the never-silent special case** — the receipt that
the class was extended, not forked, in the shape of `ofStep_eq_ofHistoryStep`:
raw function equality, not merely `PFunConverter.TraceEquiv`. -/
theorem ofHistoryStep_eq_ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ) :
    ofHistoryStep step cnt
      = ofHistoryStepPartial (fun us hne ys => some (step us hne ys)) cnt := by
  funext p
  unfold ofHistoryStep ofHistoryStepPartial
  split_ifs with h
  · split <;> rfl
  · rfl

/-- …and the Def 3.8 membership travels with it: `isDDC_ofHistoryStep` is
`isDDC_ofHistoryStepPartial` at the everywhere-defined step, where the
conditional boundary condition collapses to the original equivalence. -/
example (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (hL : ∃ L, ∀ us, cnt us ≤ L) :
    PFunConverter.IsDDC (ofHistoryStep step cnt) := by
  rw [ofHistoryStep_eq_ofHistoryStepPartial]
  refine isDDC_ofHistoryStepPartial _ cnt (fun us hne ys mv hmv => ?_) hL
  rw [Option.some_inj] at hmv
  subst hmv
  exact hcnt us hne ys

/-! ### The stateful coherence: `apply (ofHistoryStep step cnt) = applyGH step`

The history-aware twin of `apply_ofStep_eq_applyG`, on the same two-layer simulation and the same
drop-offset invariant — with `ofStep`'s `(us.dropLast.map cnt).sum` replaced throughout by
`roundOffset cnt us` and `cnt (us.getLast hne)` by `cnt us`.

The bookkeeping the history indexing actually costs is confined to the outer layer.  `ofHistoryStep`
locates the open round by `roundOffset cnt p.1` — an offset into the *cumulative* answer list — while
`CausalApply.driveOuterH` consumes answers as it goes and restarts each round at `[]`.  The
invariant that reconciles them is the one carried below: at the outer prefix `usPre` with cumulative
answers `ys`,

  `∀ u, roundOffset cnt (usPre ++ [u]) = ys.length`

("everything delivered so far is exactly what the completed rounds consumed").  The `∀ u` only
avoids naming a total-offset function: `roundOffset cnt (usPre ++ [u])` sums `cnt` over the proper
nonempty prefixes of `usPre ++ [u]`, every one of them a prefix of `usPre`, so the quantified
statement is one statement repeated, not a stronger hypothesis.  It re-establishes itself by
`roundOffset_concat`, and it is what makes each round open on an empty segment, so the round-level
bridge's `some`-image hypothesis is trivially available. -/

/-- Round simulation, forward (the twin of `driveG_of_drive_ofStep`): a
`drive (ofHistoryStep step cnt)` run from an all-proper segment under the round's own budget is a
`driveG (step us hne)` run of the segment's `some`-values, consumes exactly that budget, and keeps
the inner history inside the system's domain. -/
theorem driveG_of_drive_ofHistoryStep
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {us : List U} (hne : us ≠ []) {xs : List X}
      {ys : List (Option Y)} {ysY : List Y} {r : V × List X × List (Option Y)},
      ys.drop (roundOffset cnt us) = ysY.map some →
      roundOffset cnt us ≤ ys.length →
      ys.length ≤ roundOffset cnt us + cnt us →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r ∈ PFunConverter.drive (ofHistoryStep step cnt) S fuel us xs ys →
      ∃ Δ : List (Option Y), r.2.2 = ys ++ Δ ∧
        r.2.2.length = roundOffset cnt us + cnt us ∧
        (r.2.1 ∈ PFunDDS.dom S ∨ r.2.1 = []) ∧
        (r.1, r.2.1) ∈ CausalApply.driveG (step us hne) S.1 fuel xs ysY := by
  intro fuel
  induction fuel with
  | zero =>
      intro us hne xs ys ysY r _ _ _ _ h
      simp [PFunConverter.drive] at h
  | succ n ih =>
      intro us hne xs ys ysY r hseg hoff hupper hxs h
      have hlen' : ys.length - roundOffset cnt us = ysY.length := by
        have hl := congrArg List.length hseg
        simpa only [List.length_drop, List.length_map] using hl
      have hOf : ofHistoryStep step cnt (us, ys) = Part.some (step us hne ysY) := by
        rw [ofHistoryStep_apply step cnt hne ys, hseg, mapM_id_map_some ysY]
      rcases PFunConverter.drive_succ_elim h with ⟨x, hm, h'⟩ | ⟨v, hm, rfl⟩
      · rw [hOf, Part.mem_some_iff] at hm
        have hc : ysY.length < cnt us := (hcnt us hne ysY).mp ⟨x, hm.symm⟩
        rcases hout : PFunDDS.output (S⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · exfalso
          rw [hout] at h'
          have hnone : ofHistoryStep step cnt (us, ys ++ [none]) = Part.none := by
            rw [ofHistoryStep_apply step cnt hne (ys ++ [none]),
              List.drop_append_of_le_length hoff, hseg]
            simp
          rcases n with _ | n'
          · simp [PFunConverter.drive] at h'
          · rcases PFunConverter.drive_succ_elim h' with ⟨x₂, hm₂, -⟩ | ⟨v₂, hm₂, -⟩ <;>
            · rw [hnone] at hm₂
              simp at hm₂
        · rw [hout] at h'
          obtain ⟨hnext, houtS⟩ :=
            PFunDDS.mem_of_output_fullyDefined_append_eq_some S xs x hxs hout
          have hseg' : (ys ++ [some y]).drop (roundOffset cnt us) = (ysY ++ [y]).map some := by
            rw [List.drop_append_of_le_length hoff, hseg]
            simp
          obtain ⟨Δ, hΔ, hlen, hdomf, hg⟩ := ih hne hseg'
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (Or.inl hnext) h'
          refine ⟨some y :: Δ, ?_, hlen, hdomf, ?_⟩
          · rw [hΔ]; simp
          · simp only [CausalApply.driveG]
            rw [← hm, Part.mem_bind_iff]
            refine ⟨y, ?_, hg⟩
            show y ∈ S.1 (xs ++ [x])
            rw [← houtS]
            exact Part.get_mem hnext
      · rw [hOf, Part.mem_some_iff] at hm
        have hc : ¬ ysY.length < cnt us := not_lt_cnt_of_eq_inr_hist hcnt hne hm.symm
        refine ⟨[], by simp, by dsimp only; omega, hxs, ?_⟩
        simp only [CausalApply.driveG]
        rw [← hm]
        exact Part.mem_some _

/-- Round simulation, backward (the twin of `drive_ofStep_of_driveG`). -/
theorem drive_ofHistoryStep_of_driveG
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {us : List U} (hne : us ≠ []) {xs : List X}
      {ys : List (Option Y)} {ysY : List Y} {r' : V × List X},
      ys.drop (roundOffset cnt us) = ysY.map some →
      roundOffset cnt us ≤ ys.length →
      ys.length ≤ roundOffset cnt us + cnt us →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r' ∈ CausalApply.driveG (step us hne) S.1 fuel xs ysY →
      ∃ Δ : List (Option Y),
        (ys ++ Δ).length = roundOffset cnt us + cnt us ∧
        (r'.2 ∈ PFunDDS.dom S ∨ r'.2 = []) ∧
        (r'.1, r'.2, ys ++ Δ) ∈
          PFunConverter.drive (ofHistoryStep step cnt) S fuel us xs ys := by
  intro fuel
  induction fuel with
  | zero =>
      intro us hne xs ys ysY r' _ _ _ _ h
      simp [CausalApply.driveG] at h
  | succ n ih =>
      intro us hne xs ys ysY r' hseg hoff hupper hxs h
      have hlen' : ys.length - roundOffset cnt us = ysY.length := by
        have hl := congrArg List.length hseg
        simpa only [List.length_drop, List.length_map] using hl
      have hOf : ofHistoryStep step cnt (us, ys) = Part.some (step us hne ysY) := by
        rw [ofHistoryStep_apply step cnt hne ys, hseg, mapM_id_map_some ysY]
      simp only [CausalApply.driveG] at h
      rcases hstep : step us hne ysY with x | v <;> rw [hstep] at h
      · rw [Part.mem_bind_iff] at h
        obtain ⟨y, hy, h'⟩ := h
        have hc : ysY.length < cnt us := (hcnt us hne ysY).mp ⟨x, hstep⟩
        have hnext : xs ++ [x] ∈ PFunDDS.dom S := Part.dom_iff_mem.mpr ⟨y, hy⟩
        have hout : PFunDDS.output (S⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
          rw [PFunDDS.output_fullyDefined_append_of_mem S xs x hxs hnext]
          exact congrArg some (Part.get_eq_of_mem hy hnext)
        have hseg' : (ys ++ [some y]).drop (roundOffset cnt us) = (ysY ++ [y]).map some := by
          rw [List.drop_append_of_le_length hoff, hseg]
          simp
        obtain ⟨Δ, hlen, hdomf, hnu⟩ := ih hne hseg'
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (Or.inl hnext) h'
        refine ⟨some y :: Δ, ?_, hdomf, ?_⟩
        · simpa [List.append_assoc] using hlen
        · have hm : Sum.inl x ∈ ofHistoryStep step cnt (us, ys) := by
            rw [hOf, Part.mem_some_iff, hstep]
          have hnu' : (r'.1, r'.2, ys ++ some y :: Δ) ∈
              PFunConverter.drive (ofHistoryStep step cnt) S n us (xs ++ [x])
                (ys ++ [some y]) := by
            simpa [List.append_assoc] using hnu
          refine PFunConverter.drive_mem_query (ofHistoryStep step cnt) S hm ?_
          rw [hout]
          exact hnu'
      · rw [Part.mem_some_iff] at h
        subst h
        have hc : ¬ ysY.length < cnt us := not_lt_cnt_of_eq_inr_hist hcnt hne hstep
        have hm : Sum.inr v ∈ ofHistoryStep step cnt (us, ys) := by
          rw [hOf, Part.mem_some_iff, hstep]
        exact ⟨[], by simp only [List.length_append, List.length_nil]; omega, hxs,
          by simpa using
            PFunConverter.drive_mem_answer (ofHistoryStep step cnt) S hm n⟩

/-- Outer simulation, forward (the twin of `driveOuter_of_driveOuter_ofStep`): the cumulative drive
of `ofHistoryStep` is the history-aware per-round drive of `step`, on the exactly-consumed
invariant.  The ν-side outer prefix `usPre` is literally `driveOuterH`'s consumed prefix `done`. -/
theorem driveOuterH_of_driveOuter_ofHistoryStep
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (S : PFunDDS.DDS X Y) :
    ∀ {rest : List U} {fuel : ℕ} {usPre : List U} {xs : List X}
      {ys : List (Option Y)} {r : List V × List X × List (Option Y)},
      (∀ u : U, roundOffset cnt (usPre ++ [u]) = ys.length) →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r ∈ PFunConverter.driveOuter (ofHistoryStep step cnt) S fuel usPre xs ys rest →
      (r.1, r.2.1) ∈ CausalApply.driveOuterH step S.1 fuel usPre xs rest := by
  intro rest
  induction rest with
  | nil =>
      intro fuel usPre xs ys r _ _ h
      simp only [PFunConverter.driveOuter, Part.mem_some_iff] at h
      subst h
      simp [CausalApply.driveOuterH]
  | cons u rest ih =>
      intro fuel usPre xs ys r hinv hxs h
      simp only [PFunConverter.driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := h
      have hseg : ys.drop (roundOffset cnt (usPre ++ [u])) = ([] : List Y).map some := by
        rw [hinv u, List.drop_length]
        rfl
      obtain ⟨Δ, hΔ, hlen, hdomf, hg⟩ :=
        driveG_of_drive_ofHistoryStep step cnt hcnt S (us := usPre ++ [u]) (by simp) hseg
          (by rw [hinv u]) (by rw [hinv u]; omega) hxs hr₁
      have hinv' : ∀ u' : U, roundOffset cnt ((usPre ++ [u]) ++ [u']) = r₁.2.2.length := by
        intro u'
        rw [roundOffset_concat cnt (by simp) u']
        exact hlen.symm
      have hrest := ih hinv' hdomf hrr
      simp only [CausalApply.driveOuterH, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r₁.1, r₁.2.1), hg, (rr.1, rr.2.1), hrest, rfl⟩

/-- Outer simulation, backward (the twin of `driveOuter_ofStep_of_driveOuter`). -/
theorem driveOuter_ofHistoryStep_of_driveOuterH
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (S : PFunDDS.DDS X Y) :
    ∀ {rest : List U} {fuel : ℕ} {usPre : List U} {xs : List X}
      {ys : List (Option Y)} {r' : List V × List X},
      (∀ u : U, roundOffset cnt (usPre ++ [u]) = ys.length) →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r' ∈ CausalApply.driveOuterH step S.1 fuel usPre xs rest →
      ∃ Δ : List (Option Y), (r'.1, r'.2, ys ++ Δ) ∈
        PFunConverter.driveOuter (ofHistoryStep step cnt) S fuel usPre xs ys rest := by
  intro rest
  induction rest with
  | nil =>
      intro fuel usPre xs ys r' _ _ h
      simp only [CausalApply.driveOuterH, Part.mem_some_iff] at h
      subst h
      exact ⟨[], by simp [PFunConverter.driveOuter]⟩
  | cons u rest ih =>
      intro fuel usPre xs ys r' hinv hxs h
      simp only [CausalApply.driveOuterH, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := h
      have hseg : ys.drop (roundOffset cnt (usPre ++ [u])) = ([] : List Y).map some := by
        rw [hinv u, List.drop_length]
        rfl
      obtain ⟨Δ, hlen, hdomf, hnu⟩ :=
        drive_ofHistoryStep_of_driveG step cnt hcnt S (us := usPre ++ [u]) (by simp) hseg
          (by rw [hinv u]) (by rw [hinv u]; omega) hxs hr₁
      have hinv' : ∀ u' : U, roundOffset cnt ((usPre ++ [u]) ++ [u']) = (ys ++ Δ).length := by
        intro u'
        rw [roundOffset_concat cnt (by simp) u']
        exact hlen.symm
      obtain ⟨Δ', hnu'⟩ := ih hinv' hdomf hrr
      refine ⟨Δ ++ Δ', ?_⟩
      simp only [PFunConverter.driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r₁.1, r₁.2, ys ++ Δ), hnu,
        (rr.1, rr.2, (ys ++ Δ) ++ Δ'), hnu', by simp [List.append_assoc]⟩

/-- **The stateful step-converter coherence** (CR18 Def 3.9 at the ProtocolFn carrier): the protocol
function `ofHistoryStep step cnt`, applied by the transcript equations, is the history-aware
`CausalApply.applyGH` application of `step` to the system's raw function — against every system.

This is the fast path.  `PFunConverter.apply` already accepts an arbitrary `ProtocolFn`, so a
stateful converter was applicable all along; what was missing was the recursive drive that
*computes* it, and this equation is the licence to compute with it.  It subsumes
`apply_ofStep_eq_applyG` — see `apply_ofStep_eq_applyG_of_hist` for the derivation. -/
theorem apply_ofHistoryStep_eq_applyGH
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (S : PFunDDS.DDS X Y) :
    PFunConverter.apply (ofHistoryStep step cnt) S = CausalApply.applyGH step S.1 := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (PFunConverter.apply (ofHistoryStep step cnt) S).1
      = PFunConverter.applyRaw (ofHistoryStep step cnt) S from rfl,
    show (CausalApply.applyGH step S.1).1 = CausalApply.applyRawH step S.1 from rfl,
    PFunConverter.mem_applyRaw, CausalApply.mem_applyRawH]
  have hinv0 : ∀ u : U, roundOffset cnt (([] : List U) ++ [u]) = ([] : List (Option Y)).length :=
    fun u => roundOffset_of_length_le_one cnt (by simp)
  constructor
  · rintro ⟨fuel, hv⟩
    rw [PFunConverter.mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hg := driveOuterH_of_driveOuter_ofHistoryStep step cnt hcnt S hinv0 (Or.inr rfl) hr
    exact ⟨fuel, (CausalApply.mem_applyRawAtH_iff _ _ _ _ _).mpr ⟨(r.1, r.2.1), hg, hlast⟩⟩
  · rintro ⟨fuel, hv⟩
    rw [CausalApply.mem_applyRawAtH_iff] at hv
    obtain ⟨r', hr', hlast⟩ := hv
    obtain ⟨Δ, hnu⟩ := driveOuter_ofHistoryStep_of_driveOuterH step cnt hcnt S
      (usPre := []) (ys := []) hinv0 (Or.inr rfl) hr'
    exact ⟨fuel, (PFunConverter.mem_applyRawAt_iff _ _ _ _ _).mpr
      ⟨(r'.1, r'.2, [] ++ Δ), hnu, hlast⟩⟩

/-- **Receipt: the outer-memoryless coherence is an instance of the stateful one.**
`apply_ofStep_eq_applyG` re-derived from `apply_ofHistoryStep_eq_applyGH` by specializing the
constructor (`ofStep_eq_ofHistoryStep`) and the drive (`CausalApply.applyG_eq_applyGH`) at the same
history-ignoring step — so the two coherence theorems are one theorem and the fast path is one
mechanism, not two.  (`apply_ofStep_eq_applyG` itself is kept as proved: it predates this section
and its own simulation lemmas are used elsewhere.) -/
theorem apply_ofStep_eq_applyG_of_hist (step : U → List Y → X ⊕ V) (cnt : U → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u) (S : PFunDDS.DDS X Y) :
    PFunConverter.apply (ofStep step cnt) S = CausalApply.applyG step S.1 := by
  rw [ofStep_eq_ofHistoryStep step cnt, CausalApply.applyG_eq_applyGH]
  refine apply_ofHistoryStep_eq_applyGH _ _ (fun us hne ys => ?_) S
  show (∃ x, step (us.getLast hne) ys = Sum.inl x) ↔ ys.length < us.getLast?.elim 0 cnt
  rw [hcnt (us.getLast hne) ys, List.getLast?_eq_some_getLast hne]
  exact Iff.rfl

end PFunConverter.ProtocolFn

end RandomSystems.CR18
