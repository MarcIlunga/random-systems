/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystemParallel
import RandomSystems.StrictContext

/-!
# Parallel composition on strict contextual behavior

The strict contextual quotient (`StrictContext.System`) is the fibre of the
RS-to-AC resource carrier, so installing Abstract Cryptography's parallel
axis there requires parallel composition to respect **strict** equivalence
and the **strict** metric.  Neither fact follows from the CR18-side results
(`equivalent_par`, `maxAdvantage_par_le`): the strict relation is coarser
than transcript equivalence and the strict metric is only *bounded* by `Δ`
(`AttainmentCounterexample` refutes the converse), so Maurer's eq. (3) for
`Δ` transfers nothing to `maxEDist`.  This module proves the strict facts
directly.

The engine is **fixed-component absorption**: for a fixed deterministic
component `t`, "run in parallel with `t`" is itself a deterministic
discrete converter (`parFixedRightFn t`, mirror `parFixedLeftFn s`), and
applying it is literally `PFunDDS.par · t`
(`apply_parFixedRightFn`).  A strict test on a composition therefore
absorbs the fixed component (`StrictContext.absorb`), giving the two
fixed-component hops of Maurer11 Definition 3 for the strict metric, hence

* `StrictContext.maxEDist_par_le` — eq. (3), `‖`-non-expansion, on the
  strict metric;
* `StrictContext.equivalent_par` — the zero-radius case: parallel
  composition descends to the strict quotient;
* `StrictContext.System.parallel` — the induced operation on strict
  behavior, with `System.edist_parallel_le`.

Unlike the raw tagged parallel converter `PFunConverter.par` — which is
**not** a Def 3.8 citizen (an untagged `⊥` answer cannot be attributed, so
its query streaks are unbounded at reachable junk pairs) — the
fixed-component converters attribute answers by *count*: every left outer
input forwards exactly one query to the resource, so the `k`-th inner
answer belongs to the `k`-th left outer input.  Both converters are
therefore honest `IsDDC` objects with streak bound `2`.
-/

namespace RandomSystems.CR18

open scoped PFunDDS

namespace PFunConverter

/-! ## The fixed-component converters -/

section ParFixed

variable {X Y X' Y' : Type*}

/-- The queries a composite history routes to the left component. -/
abbrev leftQueries (ws : List (X ⊕ X')) : List X :=
  ws.filterMap Sum.getLeft?

/-- The queries a composite history routes to the right component. -/
abbrev rightQueries (ws : List (X ⊕ X')) : List X' :=
  ws.filterMap Sum.getRight?

/-- **Parallel composition with a fixed right component, as a converter.**
The converter presents the composite interface `(X ⊕ X', Y ⊕ Y')` upward
while its resource interface is the left component `(X, Y)`; the right
component is the fixed deterministic `t`, simulated internally.  A left
outer input forwards its query to the resource and relays the (proper)
answer; a right outer input consults `t` on the projected right history
and diverges exactly where `t` does.  Attribution is by count: the `k`-th
inner answer answers the `k`-th left outer input, which is what makes the
converter a Def 3.8 citizen where the raw tagged parallel is not. -/
def parFixedRightFn (t : PFunDDS.DDS X' Y') :
    ProtocolFn (X ⊕ X') (Y ⊕ Y') X Y := fun p =>
  if p.2.all Option.isSome then
    match p.1.getLast? with
    | some (Sum.inl x) =>
        if (leftQueries p.1).length = p.2.length + 1 then
          Part.some (Sum.inl x)
        else if h : (leftQueries p.1).length = p.2.length ∧ p.2 ≠ [] then
          match p.2.getLast h.2 with
          | some y => Part.some (Sum.inr (Sum.inl y))
          | none => Part.none
        else Part.none
    | some (Sum.inr _) =>
        if (leftQueries p.1).length = p.2.length then
          (t.1 (rightQueries p.1)).map fun y' => Sum.inr (Sum.inr y')
        else Part.none
    | none => Part.none
  else Part.none

variable {t : PFunDDS.DDS X' Y'}

/-- Any defined move certifies that every recorded answer is proper. -/
theorem parFixedRightFn_prop {ws : List (X ⊕ X')} {ys : List (Option Y)}
    {m : X ⊕ (Y ⊕ Y')} (h : m ∈ parFixedRightFn t (ws, ys)) :
    ∀ oy ∈ ys, oy.isSome := by
  unfold parFixedRightFn at h
  dsimp only at h
  by_cases hall : ys.all Option.isSome
  · exact List.all_eq_true.mp hall
  · rw [if_neg hall] at h
    simp at h

theorem parFixedRightFn_inl_inv {ws : List (X ⊕ X')}
    {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ parFixedRightFn t (ws, ys)) :
    ws.getLast? = some (Sum.inl x) ∧
      (leftQueries ws).length = ys.length + 1 ∧
      ∀ oy ∈ ys, oy.isSome := by
  have hprop := parFixedRightFn_prop h
  unfold parFixedRightFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split at h
  · rename_i x₀ hgl
    split_ifs at h with hpend hans
    · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
      subst h
      exact ⟨hgl, hpend, hprop⟩
    · split at h
      · simp at h
      · simp at h
    · simp at h
  · rename_i x₀ hgl
    split_ifs at h with hbal
    · rw [Part.mem_map_iff] at h
      obtain ⟨y', -, hy'⟩ := h
      simp at hy'
    · simp at h
  · simp at h

theorem parFixedRightFn_inr_inl_inv {ws : List (X ⊕ X')}
    {ys : List (Option Y)} {y : Y}
    (h : Sum.inr (Sum.inl y) ∈ parFixedRightFn t (ws, ys)) :
    (∃ x, ws.getLast? = some (Sum.inl x)) ∧
      (leftQueries ws).length = ys.length ∧
      ∃ hne : ys ≠ [], ys.getLast hne = some y := by
  have hprop := parFixedRightFn_prop h
  unfold parFixedRightFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split at h
  · rename_i x₀ hgl
    split_ifs at h with hpend hans
    · simp at h
    · split at h
      · rename_i y₀ hy₀
        simp only [Part.mem_some_iff, Sum.inr.injEq, Sum.inl.injEq] at h
        subst h
        exact ⟨⟨x₀, hgl⟩, hans.1, hans.2, hy₀⟩
      · simp at h
    · simp at h
  · rename_i x₀ hgl
    split_ifs at h with hbal
    · rw [Part.mem_map_iff] at h
      obtain ⟨y', -, hy'⟩ := h
      simp at hy'
    · simp at h
  · simp at h

theorem parFixedRightFn_inr_inr_inv {ws : List (X ⊕ X')}
    {ys : List (Option Y)} {y' : Y'}
    (h : Sum.inr (Sum.inr y') ∈ parFixedRightFn t (ws, ys)) :
    (∃ x', ws.getLast? = some (Sum.inr x')) ∧
      (leftQueries ws).length = ys.length ∧
      y' ∈ t.1 (rightQueries ws) := by
  have hprop := parFixedRightFn_prop h
  unfold parFixedRightFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split at h
  · rename_i x₀ hgl
    split_ifs at h with hpend hans
    · simp at h
    · split at h
      · simp at h
      · simp at h
    · simp at h
  · rename_i x₀ hgl
    split_ifs at h with hbal
    · rw [Part.mem_map_iff] at h
      obtain ⟨y₀, hy₀, hmap⟩ := h
      simp only [Sum.inr.injEq] at hmap
      subst hmap
      exact ⟨⟨x₀, hgl⟩, hbal, hy₀⟩
    · simp at h
  · simp at h

theorem parFixedRightFn_inl_mem (t : PFunDDS.DDS X' Y')
    {ws : List (X ⊕ X')} {ys : List (Option Y)} {x : X}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hpend : (leftQueries ws).length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, oy.isSome) :
    Sum.inl x ∈ parFixedRightFn t (ws, ys) := by
  unfold parFixedRightFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), hgl]
  dsimp only
  rw [if_pos hpend]
  exact Part.mem_some _

theorem parFixedRightFn_inr_inl_mem (t : PFunDDS.DDS X' Y')
    {ws : List (X ⊕ X')} {ys : List (Option Y)} {x : X} {y : Y}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hbal : (leftQueries ws).length = ys.length)
    (hne : ys ≠ []) (hy : ys.getLast hne = some y)
    (hprop : ∀ oy ∈ ys, oy.isSome) :
    Sum.inr (Sum.inl y) ∈ parFixedRightFn t (ws, ys) := by
  unfold parFixedRightFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), hgl]
  dsimp only
  rw [if_neg (by omega), dif_pos ⟨hbal, hne⟩, hy]
  exact Part.mem_some _

theorem parFixedRightFn_inr_inr_mem (t : PFunDDS.DDS X' Y')
    {ws : List (X ⊕ X')} {ys : List (Option Y)} {x' : X'} {y' : Y'}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hbal : (leftQueries ws).length = ys.length)
    (hy' : y' ∈ t.1 (rightQueries ws))
    (hprop : ∀ oy ∈ ys, oy.isSome) :
    Sum.inr (Sum.inr y') ∈ parFixedRightFn t (ws, ys) := by
  unfold parFixedRightFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), hgl]
  dsimp only
  rw [if_pos hbal, Part.mem_map_iff]
  exact ⟨y', hy', rfl⟩

/-- The fixed-right-component converter never moves past a `⊥`. -/
theorem answersInY_parFixedRightFn (t : PFunDDS.DDS X' Y') :
    AnswersInY (parFixedRightFn (X := X) (Y := Y) t) := by
  rintro ⟨ws, ys⟩ - hnone hdom
  rw [Part.dom_iff_mem] at hdom
  obtain ⟨m, hm⟩ := hdom
  exact absurd (parFixedRightFn_prop hm none hnone) (by simp)

/-- The fixed-right-component converter never opens a streak of two
queries: a query pins the count one ahead of the answers, which the next
answer destroys. -/
theorem answersWithin_parFixedRightFn (t : PFunDDS.DDS X' Y') :
    AnswersWithin (parFixedRightFn (X := X) (Y := Y) t) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  have h0 := (parFixedRightFn_inl_inv hx0).2.1
  have h1 := (parFixedRightFn_inl_inv hx1).2.1
  simp only [List.take_zero, List.append_nil] at h0
  simp only [List.length_append, List.length_take] at h1
  omega

/-- `parFixedRightFn t` is a deterministic discrete converter. -/
theorem isDDC_parFixedRightFn (t : PFunDDS.DDS X' Y') :
    IsDDC (parFixedRightFn (X := X) (Y := Y) t) :=
  ⟨answersInY_parFixedRightFn t, 2, answersWithin_parFixedRightFn t⟩

end ParFixed

/-! ## The realization: applying the fixed-component converter is `par` -/

section ParFixedApply

variable {X Y X' Y' : Type*}

/-- Membership in the raw parallel composition, destructed to the two
component guards and the routed answer. -/
theorem mem_par_toPFun_iff (s : PFunDDS.DDS X Y) (t : PFunDDS.DDS X' Y')
    (l : List (X ⊕ X')) (m : Y ⊕ Y') :
    m ∈ (PFunDDS.par s t).1 l ↔
      (leftQueries l ≠ [] → (s.1 (leftQueries l)).Dom) ∧
      (rightQueries l ≠ [] → (t.1 (rightQueries l)).Dom) ∧
      ((∃ x, l.getLast? = some (Sum.inl x) ∧
          m ∈ (s.1 (leftQueries l)).map Sum.inl) ∨
        (∃ x', l.getLast? = some (Sum.inr x') ∧
          m ∈ (t.1 (rightQueries l)).map Sum.inr)) := by
  show m ∈ Part.assert _ _ ↔ _
  simp only [Part.mem_assert_iff]
  constructor
  · rintro ⟨hL, hR, hm⟩
    refine ⟨hL, hR, ?_⟩
    revert hm
    split
    · rename_i x hgl
      intro hm
      exact Or.inl ⟨x, hgl, hm⟩
    · rename_i x' hgl
      intro hm
      exact Or.inr ⟨x', hgl, hm⟩
    · intro hm
      simp at hm
  · rintro ⟨hL, hR, hm⟩
    refine ⟨hL, hR, ?_⟩
    rcases hm with ⟨x, hgl, hm⟩ | ⟨x', hgl, hm⟩ <;> rw [hgl] <;> exact hm

variable {t : PFunDDS.DDS X' Y'} {s : PFunDDS.DDS X Y}

/-- An improper recorded answer kills the drive of the fixed-component
converter. -/
private theorem drive_parFixedRight_none_dead {fuel : ℕ}
    {ws : List (X ⊕ X')} {xs : List X} {ys : List (Option Y)}
    {p : (Y ⊕ Y') × List X × List (Option Y)} :
    p ∉ drive (parFixedRightFn t) s fuel ws xs (ys ++ [none]) := by
  intro hp
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x, hm, -⟩ | ⟨v, hm, -⟩
    · exact absurd (parFixedRightFn_prop hm none (by simp)) (by simp)
    · exact absurd (parFixedRightFn_prop hm none (by simp)) (by simp)

/-- One left round of the fixed-component drive, destructed: the query is
forwarded, the answer is proper, and the round relays it. -/
theorem drive_parFixedRight_left_round_elim
    {ws : List (X ⊕ X')} {x : X} {ys : List (Option Y)} {fuel : ℕ}
    {xs : List X} {p : (Y ⊕ Y') × List X × List (Option Y)}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hpend : (leftQueries ws).length = ys.length + 1)
    (hp : p ∈ drive (parFixedRightFn t) s fuel ws xs ys) :
    ∃ y : Y,
      PFunDDS.output (s⊥) (xs ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y ∧
      p = (Sum.inl y, xs ++ [x], ys ++ [some y]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x₁, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hgl₁, -, -⟩ := parFixedRightFn_inl_inv hm
      rw [hgl] at hgl₁
      have hx : x = x₁ := Sum.inl.inj (Option.some.inj hgl₁)
      subst hx
      rcases hout : PFunDDS.output (s⊥) (xs ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
      · rw [hout] at hp'
        exact absurd hp' drive_parFixedRight_none_dead
      · rw [hout] at hp'
        rcases fuel with _ | fuel
        · simp [drive] at hp'
        · rcases drive_succ_elim hp' with ⟨x₂, hm₂, -⟩ | ⟨v₂, hm₂, rfl⟩
          · obtain ⟨-, hpend₂, -⟩ := parFixedRightFn_inl_inv hm₂
            simp only [List.length_append, List.length_singleton] at hpend₂
            omega
          · rcases v₂ with y₂ | y₂'
            · obtain ⟨-, -, hne₂, hy₂⟩ := parFixedRightFn_inr_inl_inv hm₂
              rw [List.getLast_append_singleton (l := ys)] at hy₂
              obtain rfl : y = y₂ := Option.some.inj hy₂
              exact ⟨y, rfl, rfl⟩
            · obtain ⟨⟨x₂', hgl₂⟩, -, -⟩ := parFixedRightFn_inr_inr_inv hm₂
              rw [hgl] at hgl₂
              exact absurd (Option.some.inj hgl₂) (by simp)
    · rcases v with y | y'
      · obtain ⟨-, hbal, -, -⟩ := parFixedRightFn_inr_inl_inv hm
        omega
      · obtain ⟨⟨x', hgl'⟩, -, -⟩ := parFixedRightFn_inr_inr_inv hm
        rw [hgl] at hgl'
        exact absurd (Option.some.inj hgl') (by simp)

/-- One left round of the fixed-component drive, constructed from a proper
system answer. -/
theorem drive_parFixedRight_left_round_mem
    {ws : List (X ⊕ X')} {x : X} {ys : List (Option Y)} {xs : List X}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hpend : (leftQueries ws).length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, oy.isSome) {y : Y}
    (hy : PFunDDS.output (s⊥) (xs ++ [x])
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some y) :
    (Sum.inl y, xs ++ [x], ys ++ [some y]) ∈
      drive (parFixedRightFn t) s 2 ws xs ys := by
  have hm : Sum.inl x ∈ parFixedRightFn t (ws, ys) :=
    parFixedRightFn_inl_mem t hgl hpend hprop
  refine drive_mem_query (parFixedRightFn t) s hm ?_
  rw [hy]
  have hm₂ : Sum.inr (Sum.inl y) ∈ parFixedRightFn t (ws, ys ++ [some y]) := by
    refine parFixedRightFn_inr_inl_mem t hgl (by simp [hpend])
      (by simp) ?_ ?_
    · rw [List.getLast_append_singleton]
    · intro oy hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hprop oy hmem
      · rw [List.mem_singleton.mp hmem]
        rfl
  exact drive_mem_answer (parFixedRightFn t) s hm₂ 0

/-- One right round of the fixed-component drive, destructed: no query is
made and the answer is the fixed component's. -/
theorem drive_parFixedRight_right_round_elim
    {ws : List (X ⊕ X')} {x' : X'} {ys : List (Option Y)} {fuel : ℕ}
    {xs : List X} {p : (Y ⊕ Y') × List X × List (Option Y)}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hp : p ∈ drive (parFixedRightFn t) s fuel ws xs ys) :
    ∃ y' : Y', y' ∈ t.1 (rightQueries ws) ∧ p = (Sum.inr y', xs, ys) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x₁, hm, -⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hgl₁, -, -⟩ := parFixedRightFn_inl_inv hm
      rw [hgl] at hgl₁
      exact absurd (Option.some.inj hgl₁).symm (by simp)
    · rcases v with y | y'
      · obtain ⟨⟨x₁, hgl₁⟩, -, -⟩ := parFixedRightFn_inr_inl_inv hm
        rw [hgl] at hgl₁
        exact absurd (Option.some.inj hgl₁).symm (by simp)
      · obtain ⟨-, -, hy'⟩ := parFixedRightFn_inr_inr_inv hm
        exact ⟨y', hy', rfl⟩

/-- One right round of the fixed-component drive, constructed from a
defined fixed-component answer. -/
theorem drive_parFixedRight_right_round_mem
    {ws : List (X ⊕ X')} {x' : X'} {ys : List (Option Y)} {xs : List X}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hbal : (leftQueries ws).length = ys.length)
    (hprop : ∀ oy ∈ ys, oy.isSome) {y' : Y'}
    (hy' : y' ∈ t.1 (rightQueries ws)) :
    (Sum.inr y', xs, ys) ∈ drive (parFixedRightFn t) s 2 ws xs ys :=
  drive_mem_answer (parFixedRightFn t) s
    (parFixedRightFn_inr_inr_mem t hgl hbal hy' hprop) 1

@[simp]
theorem leftQueries_concat_inl (l : List (X ⊕ X')) (x : X) :
    leftQueries (l ++ [Sum.inl x]) = leftQueries l ++ [x] := by
  simp [leftQueries]

@[simp]
theorem leftQueries_concat_inr (l : List (X ⊕ X')) (x' : X') :
    leftQueries (l ++ [Sum.inr x']) = leftQueries l := by
  simp [leftQueries]

@[simp]
theorem rightQueries_concat_inl (l : List (X ⊕ X')) (x : X) :
    rightQueries (l ++ [Sum.inl x]) = rightQueries l := by
  simp [rightQueries]

@[simp]
theorem rightQueries_concat_inr (l : List (X ⊕ X')) (x' : X') :
    rightQueries (l ++ [Sum.inr x']) = rightQueries l ++ [x'] := by
  simp [rightQueries]

theorem leftQueries_append (l₁ l₂ : List (X ⊕ X')) :
    leftQueries (l₁ ++ l₂) = leftQueries l₁ ++ leftQueries l₂ :=
  List.filterMap_append

theorem rightQueries_append (l₁ l₂ : List (X ⊕ X')) :
    rightQueries (l₁ ++ l₂) = rightQueries l₁ ++ rightQueries l₂ :=
  List.filterMap_append

/-- Forward realization: on a history admitted by the composition, the
fixed-component drive completes, threads the left projection as its inner
history, and its last answer is the composition's. -/
theorem driveOuter_parFixedRight_of_dom (t : PFunDDS.DDS X' Y')
    (s : PFunDDS.DDS X Y) :
    ∀ (rest ws : List (X ⊕ X')) (ys : List (Option Y)),
      (leftQueries ws).length = ys.length →
      (∀ oy ∈ ys, oy.isSome) →
      (leftQueries (ws ++ rest) ∈ PFunDDS.dom s ∨
        leftQueries (ws ++ rest) = []) →
      (rightQueries (ws ++ rest) ∈ PFunDDS.dom t ∨
        rightQueries (ws ++ rest) = []) →
      ∃ vs ys',
        (vs, leftQueries (ws ++ rest), ys') ∈
          driveOuter (parFixedRightFn t) s 2 ws (leftQueries ws) ys rest ∧
        ∀ _ : rest ≠ [], ∃ v, vs.getLast? = some v ∧
          v ∈ (PFunDDS.par s t).1 (ws ++ rest) := by
  intro rest
  induction rest with
  | nil =>
      intro ws ys _ _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro ws ys hlen hprop hLdom hRdom
      have hgl : (ws ++ [u]).getLast? = some u := by
        simp
      cases u with
      | inl x =>
          -- the forwarded query is admitted by the left component
          have hLpre : leftQueries ws ++ [x] <+:
              leftQueries (ws ++ (Sum.inl x :: rest)) := by
            rw [show ws ++ (Sum.inl x :: rest) = (ws ++ [Sum.inl x]) ++ rest
                by simp, leftQueries_append, leftQueries_concat_inl]
            exact List.prefix_append _ _
          have hnext : leftQueries ws ++ [x] ∈ PFunDDS.dom s := by
            rcases hLdom with hmem | hnil
            · exact PFunDDS.prefix_closed s hLpre (by simp) hmem
            · exact absurd (List.prefix_nil.mp (hnil ▸ hLpre)) (by simp)
          have hxs : leftQueries ws ∈ PFunDDS.dom s ∨ leftQueries ws = [] := by
            rcases eq_or_ne (leftQueries ws) [] with hnil | hne
            · exact Or.inr hnil
            · exact Or.inl (PFunDDS.prefix_closed s ⟨[x], rfl⟩ hne hnext)
          have hout : PFunDDS.output (s⊥) (leftQueries ws ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              = some (PFunDDS.output s (leftQueries ws ++ [x]) hnext) :=
            PFunDDS.output_fullyDefined_append_of_mem s (leftQueries ws) x
              hxs hnext
          have hround := drive_parFixedRight_left_round_mem
            (t := t) (s := s) (ws := ws ++ [Sum.inl x]) (ys := ys)
            (xs := leftQueries ws) hgl (by simp [hlen]) hprop hout
          set y := PFunDDS.output s (leftQueries ws ++ [x]) hnext with hydef
          obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (ws ++ [Sum.inl x])
            (ys ++ [some y]) (by simp [hlen])
            (by
              intro oy hmem
              rcases List.mem_append.mp hmem with hm | hm
              · exact hprop oy hm
              · rw [List.mem_singleton.mp hm]; rfl)
            (by simpa [List.append_assoc] using hLdom)
            (by simpa [List.append_assoc] using hRdom)
          rw [leftQueries_concat_inl] at hmem'
          refine ⟨Sum.inl y :: vs', ys'', ?_, ?_⟩
          · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(Sum.inl y, leftQueries ws ++ [x], ys ++ [some y]),
              hround, (vs', leftQueries (ws ++ (Sum.inl x :: rest)), ys''),
              ?_, rfl⟩
            rw [show ws ++ (Sum.inl x :: rest) = (ws ++ [Sum.inl x]) ++ rest
                by simp]
            exact hmem'
          · intro _
            cases hvs : vs' with
            | nil =>
                have hrest : rest = [] := by
                  have hlen' := driveOuter_length (parFixedRightFn t) s 2 hmem'
                  rw [hvs] at hlen'
                  exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
                subst hrest
                refine ⟨Sum.inl y, by rw [List.getLast?_singleton], ?_⟩
                rw [mem_par_toPFun_iff]
                refine ⟨?_, ?_, ?_⟩
                · intro _
                  show (s.1 (leftQueries (ws ++ [Sum.inl x]))).Dom
                  rw [leftQueries_concat_inl]
                  exact hnext
                · intro hne'
                  show (t.1 (rightQueries (ws ++ [Sum.inl x]))).Dom
                  rw [rightQueries_concat_inl]
                  rw [show ws ++ ([Sum.inl x] : List _) = ws ++ [Sum.inl x]
                    from rfl, rightQueries_concat_inl] at hne'
                  rcases hRdom with hmem | hnil
                  · rw [show ws ++ (Sum.inl x :: ([] : List _))
                        = ws ++ [Sum.inl x] from rfl,
                      rightQueries_concat_inl] at hmem
                    exact hmem
                  · rw [show ws ++ (Sum.inl x :: ([] : List _))
                        = ws ++ [Sum.inl x] from rfl,
                      rightQueries_concat_inl] at hnil
                    exact absurd hnil hne'
                · refine Or.inl ⟨x, by simp, ?_⟩
                  rw [Part.mem_map_iff]
                  refine ⟨y, ?_, rfl⟩
                  show y ∈ s.1 (leftQueries (ws ++ ([Sum.inl x] : List _)))
                  rw [leftQueries_concat_inl]
                  exact hydef ▸ Part.get_mem hnext
            | cons v0 vs0 =>
                have hrest : rest ≠ [] := by
                  have hlen' := driveOuter_length (parFixedRightFn t) s 2 hmem'
                  rw [hvs] at hlen'
                  intro hnil
                  rw [hnil] at hlen'
                  simp at hlen'
                obtain ⟨v, hvlast, hvmem⟩ := hlast' hrest
                rw [hvs] at hvlast
                refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                simpa [List.append_assoc] using hvmem
      | inr x' =>
          -- the fixed component is defined on the projected right history
          have hRpre : rightQueries ws ++ [x'] <+:
              rightQueries (ws ++ (Sum.inr x' :: rest)) := by
            rw [show ws ++ (Sum.inr x' :: rest) = (ws ++ [Sum.inr x']) ++ rest
                by simp, rightQueries_append, rightQueries_concat_inr]
            exact List.prefix_append _ _
          have hnext : rightQueries ws ++ [x'] ∈ PFunDDS.dom t := by
            rcases hRdom with hmem | hnil
            · exact PFunDDS.prefix_closed t hRpre (by simp) hmem
            · exact absurd (List.prefix_nil.mp (hnil ▸ hRpre)) (by simp)
          set y' := PFunDDS.output t (rightQueries ws ++ [x']) hnext with hy'def
          have hy'mem : y' ∈ t.1 (rightQueries (ws ++ [Sum.inr x'])) := by
            rw [rightQueries_concat_inr]
            exact hy'def ▸ Part.get_mem hnext
          have hround := drive_parFixedRight_right_round_mem
            (t := t) (s := s) (ws := ws ++ [Sum.inr x']) (ys := ys)
            (xs := leftQueries ws) hgl (by simp [hlen]) hprop hy'mem
          obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (ws ++ [Sum.inr x']) ys
            (by simp [hlen]) hprop
            (by simpa [List.append_assoc] using hLdom)
            (by simpa [List.append_assoc] using hRdom)
          rw [leftQueries_concat_inr] at hmem'
          refine ⟨Sum.inr y' :: vs', ys'', ?_, ?_⟩
          · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(Sum.inr y', leftQueries ws, ys), hround,
              (vs', leftQueries (ws ++ (Sum.inr x' :: rest)), ys''), ?_, rfl⟩
            rw [show ws ++ (Sum.inr x' :: rest) = (ws ++ [Sum.inr x']) ++ rest
                by simp]
            exact hmem'
          · intro _
            cases hvs : vs' with
            | nil =>
                have hrest : rest = [] := by
                  have hlen' := driveOuter_length (parFixedRightFn t) s 2 hmem'
                  rw [hvs] at hlen'
                  exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
                subst hrest
                refine ⟨Sum.inr y', by rw [List.getLast?_singleton], ?_⟩
                rw [mem_par_toPFun_iff]
                refine ⟨?_, fun _ => ?_, ?_⟩
                · intro hne'
                  show (s.1 (leftQueries (ws ++ [Sum.inr x']))).Dom
                  rw [leftQueries_concat_inr]
                  rw [show ws ++ ([Sum.inr x'] : List _) = ws ++ [Sum.inr x']
                    from rfl, leftQueries_concat_inr] at hne'
                  rcases hLdom with hmem | hnil
                  · rw [show ws ++ (Sum.inr x' :: ([] : List _))
                        = ws ++ [Sum.inr x'] from rfl,
                      leftQueries_concat_inr] at hmem
                    exact hmem
                  · rw [show ws ++ (Sum.inr x' :: ([] : List _))
                        = ws ++ [Sum.inr x'] from rfl,
                      leftQueries_concat_inr] at hnil
                    exact absurd hnil hne'
                · show (t.1 (rightQueries (ws ++ ([Sum.inr x'] : List _)))).Dom
                  rw [rightQueries_concat_inr]
                  exact hnext
                · refine Or.inr ⟨x', by simp, ?_⟩
                  rw [Part.mem_map_iff]
                  exact ⟨y', hy'mem, rfl⟩
            | cons v0 vs0 =>
                have hrest : rest ≠ [] := by
                  have hlen' := driveOuter_length (parFixedRightFn t) s 2 hmem'
                  rw [hvs] at hlen'
                  intro hnil
                  rw [hnil] at hlen'
                  simp at hlen'
                obtain ⟨v, hvlast, hvmem⟩ := hlast' hrest
                rw [hvs] at hvlast
                refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                simpa [List.append_assoc] using hvmem

/-- Backward realization: every completed fixed-component run certifies
both component domains, threads the left projection, and its last answer
is the composition's. -/
theorem driveOuter_parFixedRight_mem_imp (t : PFunDDS.DDS X' Y')
    (s : PFunDDS.DDS X Y) :
    ∀ (rest ws : List (X ⊕ X')) (ys : List (Option Y)) {fuel : ℕ}
      {r : List (Y ⊕ Y') × List X × List (Option Y)},
      (leftQueries ws).length = ys.length →
      (∀ oy ∈ ys, oy.isSome) →
      (leftQueries ws ∈ PFunDDS.dom s ∨ leftQueries ws = []) →
      (rightQueries ws ∈ PFunDDS.dom t ∨ rightQueries ws = []) →
      r ∈ driveOuter (parFixedRightFn t) s fuel ws (leftQueries ws) ys rest →
      r.2.1 = leftQueries (ws ++ rest) ∧
      (rest ≠ [] → ∃ v, r.1.getLast? = some v ∧
        v ∈ (PFunDDS.par s t).1 (ws ++ rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro ws ys fuel r _ _ _ _ hr
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro ws ys fuel r hlen hprop hLdom hRdom hr
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      have hgl : (ws ++ [u]).getLast? = some u := by simp
      cases u with
      | inl x =>
          obtain ⟨y, hout, rfl⟩ := drive_parFixedRight_left_round_elim
            (ws := ws ++ [Sum.inl x]) hgl (by simp [hlen]) hr₁
          obtain ⟨hnext, houtS⟩ :=
            PFunDDS.mem_of_output_fullyDefined_append_eq_some s
              (leftQueries ws) x hLdom hout
          have hprop' : ∀ oy ∈ ys ++ [some y], oy.isSome := by
            intro oy hmem
            rcases List.mem_append.mp hmem with hm | hm
            · exact hprop oy hm
            · rw [List.mem_singleton.mp hm]; rfl
          have hrr' : rr ∈ driveOuter (parFixedRightFn t) s fuel
              (ws ++ [Sum.inl x]) (leftQueries (ws ++ [Sum.inl x]))
              (ys ++ [some y]) rest := by
            rw [leftQueries_concat_inl]
            exact hrr
          obtain ⟨hthread, hcond⟩ := ih (ws ++ [Sum.inl x]) (ys ++ [some y])
            (by simp [hlen]) hprop'
            (by rw [leftQueries_concat_inl]; exact Or.inl hnext)
            (by rw [rightQueries_concat_inl]; exact hRdom) hrr'
          refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
          cases hrest : rest with
          | nil =>
              subst hrest
              simp only [driveOuter, Part.mem_some_iff] at hrr'
              subst hrr'
              refine ⟨Sum.inl y, by rw [List.getLast?_singleton], ?_⟩
              rw [mem_par_toPFun_iff]
              refine ⟨?_, ?_, ?_⟩
              · intro _
                show (s.1 (leftQueries (ws ++ [Sum.inl x]))).Dom
                rw [leftQueries_concat_inl]
                exact hnext
              · intro hne'
                rw [show ws ++ (Sum.inl x :: ([] : List _))
                      = ws ++ [Sum.inl x] from rfl,
                  rightQueries_concat_inl] at hne' ⊢
                rcases hRdom with hmem | hnil
                · exact hmem
                · exact absurd hnil hne'
              · refine Or.inl ⟨x, by simp, ?_⟩
                rw [Part.mem_map_iff]
                refine ⟨y, ?_, rfl⟩
                show y ∈ s.1 (leftQueries (ws ++ ([Sum.inl x] : List _)))
                rw [leftQueries_concat_inl]
                exact houtS ▸ Part.get_mem hnext
          | cons r0 rs0 =>
              obtain ⟨v, hvlast, hvmem⟩ := hcond (by simp [hrest])
              have hlenrr := driveOuter_length (parFixedRightFn t) s fuel hrr'
              cases hrr1 : rr.1 with
              | nil =>
                  rw [hrr1] at hlenrr
                  simp [hrest] at hlenrr
              | cons v0 vs0 =>
                  rw [hrr1] at hvlast
                  refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                  rw [hrest] at hvmem
                  simpa [List.append_assoc] using hvmem
      | inr x' =>
          obtain ⟨y', hy', rfl⟩ := drive_parFixedRight_right_round_elim
            (ws := ws ++ [Sum.inr x']) hgl hr₁
          have hRnext : rightQueries (ws ++ [Sum.inr x'])
              ∈ PFunDDS.dom t :=
            Part.dom_iff_mem.mpr ⟨y', hy'⟩
          have hrr' : rr ∈ driveOuter (parFixedRightFn t) s fuel
              (ws ++ [Sum.inr x']) (leftQueries (ws ++ [Sum.inr x'])) ys
              rest := by
            rw [leftQueries_concat_inr]
            exact hrr
          obtain ⟨hthread, hcond⟩ := ih (ws ++ [Sum.inr x']) ys
            (by simp [hlen]) hprop
            (by rw [leftQueries_concat_inr]; exact hLdom)
            (Or.inl hRnext) hrr'
          refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
          cases hrest : rest with
          | nil =>
              subst hrest
              simp only [driveOuter, Part.mem_some_iff] at hrr'
              subst hrr'
              refine ⟨Sum.inr y', by rw [List.getLast?_singleton], ?_⟩
              rw [mem_par_toPFun_iff]
              refine ⟨?_, fun _ => ?_, ?_⟩
              · intro hne'
                rw [show ws ++ (Sum.inr x' :: ([] : List _))
                      = ws ++ [Sum.inr x'] from rfl,
                  leftQueries_concat_inr] at hne' ⊢
                rcases hLdom with hmem | hnil
                · exact hmem
                · exact absurd hnil hne'
              · show (t.1 (rightQueries (ws ++ [Sum.inr x']))).Dom
                exact hRnext
              · refine Or.inr ⟨x', by simp, ?_⟩
                rw [Part.mem_map_iff]
                exact ⟨y', hy', rfl⟩
          | cons r0 rs0 =>
              obtain ⟨v, hvlast, hvmem⟩ := hcond (by simp [hrest])
              have hlenrr := driveOuter_length (parFixedRightFn t) s fuel hrr'
              cases hrr1 : rr.1 with
              | nil =>
                  rw [hrr1] at hlenrr
                  simp [hrest] at hlenrr
              | cons v0 vs0 =>
                  rw [hrr1] at hvlast
                  refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                  rw [hrest] at hvmem
                  simpa [List.append_assoc] using hvmem

/-- **The fixed-component realization**: applying the fixed-right-component
converter to `s` *is* the parallel composition `s ‖ t`.  This is what lets
a strict test absorb a fixed component of a composition. -/
theorem apply_parFixedRightFn (t : PFunDDS.DDS X' Y') (s : PFunDDS.DDS X Y) :
    apply (parFixedRightFn t) s = PFunDDS.par s t := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (apply (parFixedRightFn t) s).1
      = applyRaw (parFixedRightFn t) s from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (parFixedRightFn t) s fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    have hr' : r ∈ driveOuter (parFixedRightFn t) s fuel []
        (leftQueries ([] : List (X ⊕ X'))) [] us := by
      simpa [leftQueries] using hr
    obtain ⟨-, hcond⟩ := driveOuter_parFixedRight_mem_imp t s us [] []
      (by simp [leftQueries]) (by simp)
      (Or.inr (by simp [leftQueries])) (Or.inr (by simp [rightQueries])) hr'
    obtain ⟨v', hv'last, hv'mem⟩ := hcond hne
    rw [hlast] at hv'last
    obtain rfl : v = v' := Option.some.inj hv'last
    simpa using hv'mem
  · intro hv
    have hne : us ≠ [] := by
      rintro rfl
      rw [mem_par_toPFun_iff] at hv
      rcases hv.2.2 with ⟨x, hgl, -⟩ | ⟨x', hgl, -⟩ <;> simp at hgl
    have hv' := hv
    rw [mem_par_toPFun_iff] at hv'
    obtain ⟨hL, hR, -⟩ := hv'
    have hLdom : leftQueries us ∈ PFunDDS.dom s ∨ leftQueries us = [] := by
      rcases eq_or_ne (leftQueries us) [] with hnil | hne'
      · exact Or.inr hnil
      · exact Or.inl (hL hne')
    have hRdom : rightQueries us ∈ PFunDDS.dom t ∨ rightQueries us = [] := by
      rcases eq_or_ne (rightQueries us) [] with hnil | hne'
      · exact Or.inr hnil
      · exact Or.inl (hR hne')
    obtain ⟨vs, ys', hmem, hval⟩ := driveOuter_parFixedRight_of_dom t s us
      [] [] (by simp [leftQueries]) (by simp)
      (by simpa using hLdom) (by simpa using hRdom)
    obtain ⟨v₀, hlast, hv₀⟩ := hval hne
    obtain rfl : v₀ = v := Part.mem_unique (by simpa using hv₀) hv
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, leftQueries (([] : List (X ⊕ X')) ++ us), ys'), ?_, hlast⟩
    simpa [leftQueries] using hmem

end ParFixedApply

/-! ## The mirror: fixed left component -/

section ParFixedLeft

variable {X Y X' Y' : Type*}

/-- **Parallel composition with a fixed left component, as a converter.**
Mirror of `parFixedRightFn`: the resource interface is the right
component `(X', Y')`, the left component is the fixed deterministic `s`. -/
def parFixedLeftFn (s : PFunDDS.DDS X Y) :
    ProtocolFn (X ⊕ X') (Y ⊕ Y') X' Y' := fun p =>
  if p.2.all Option.isSome then
    match p.1.getLast? with
    | some (Sum.inl _) =>
        if (rightQueries p.1).length = p.2.length then
          (s.1 (leftQueries p.1)).map fun y => Sum.inr (Sum.inl y)
        else Part.none
    | some (Sum.inr x') =>
        if (rightQueries p.1).length = p.2.length + 1 then
          Part.some (Sum.inl x')
        else if h : (rightQueries p.1).length = p.2.length ∧ p.2 ≠ [] then
          match p.2.getLast h.2 with
          | some y' => Part.some (Sum.inr (Sum.inr y'))
          | none => Part.none
        else Part.none
    | none => Part.none
  else Part.none

variable {s : PFunDDS.DDS X Y}

/-- Any defined move certifies that every recorded answer is proper. -/
theorem parFixedLeftFn_prop {ws : List (X ⊕ X')} {ys : List (Option Y')}
    {m : X' ⊕ (Y ⊕ Y')} (h : m ∈ parFixedLeftFn s (ws, ys)) :
    ∀ oy ∈ ys, oy.isSome := by
  unfold parFixedLeftFn at h
  dsimp only at h
  by_cases hall : ys.all Option.isSome
  · exact List.all_eq_true.mp hall
  · rw [if_neg hall] at h
    simp at h

theorem parFixedLeftFn_inl_inv {ws : List (X ⊕ X')}
    {ys : List (Option Y')} {x' : X'}
    (h : Sum.inl x' ∈ parFixedLeftFn s (ws, ys)) :
    ws.getLast? = some (Sum.inr x') ∧
      (rightQueries ws).length = ys.length + 1 ∧
      ∀ oy ∈ ys, oy.isSome := by
  have hprop := parFixedLeftFn_prop h
  unfold parFixedLeftFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split at h
  · rename_i x₀ hgl
    split_ifs at h with hbal
    · rw [Part.mem_map_iff] at h
      obtain ⟨y, -, hy⟩ := h
      simp at hy
    · simp at h
  · rename_i x₀ hgl
    split_ifs at h with hpend hans
    · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
      subst h
      exact ⟨hgl, hpend, hprop⟩
    · split at h
      · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem parFixedLeftFn_inr_inr_inv {ws : List (X ⊕ X')}
    {ys : List (Option Y')} {y' : Y'}
    (h : Sum.inr (Sum.inr y') ∈ parFixedLeftFn s (ws, ys)) :
    (∃ x', ws.getLast? = some (Sum.inr x')) ∧
      (rightQueries ws).length = ys.length ∧
      ∃ hne : ys ≠ [], ys.getLast hne = some y' := by
  have hprop := parFixedLeftFn_prop h
  unfold parFixedLeftFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split at h
  · rename_i x₀ hgl
    split_ifs at h with hbal
    · rw [Part.mem_map_iff] at h
      obtain ⟨y, -, hy⟩ := h
      simp at hy
    · simp at h
  · rename_i x₀ hgl
    split_ifs at h with hpend hans
    · simp at h
    · split at h
      · rename_i y₀ hy₀
        simp only [Part.mem_some_iff, Sum.inr.injEq] at h
        subst h
        exact ⟨⟨x₀, hgl⟩, hans.1, hans.2, hy₀⟩
      · simp at h
    · simp at h
  · simp at h

theorem parFixedLeftFn_inr_inl_inv {ws : List (X ⊕ X')}
    {ys : List (Option Y')} {y : Y}
    (h : Sum.inr (Sum.inl y) ∈ parFixedLeftFn s (ws, ys)) :
    (∃ x, ws.getLast? = some (Sum.inl x)) ∧
      (rightQueries ws).length = ys.length ∧
      y ∈ s.1 (leftQueries ws) := by
  have hprop := parFixedLeftFn_prop h
  unfold parFixedLeftFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split at h
  · rename_i x₀ hgl
    split_ifs at h with hbal
    · rw [Part.mem_map_iff] at h
      obtain ⟨y₀, hy₀, hmap⟩ := h
      simp only [Sum.inr.injEq, Sum.inl.injEq] at hmap
      subst hmap
      exact ⟨⟨x₀, hgl⟩, hbal, hy₀⟩
    · simp at h
  · rename_i x₀ hgl
    split_ifs at h with hpend hans
    · simp at h
    · split at h
      · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem parFixedLeftFn_inl_mem (s : PFunDDS.DDS X Y)
    {ws : List (X ⊕ X')} {ys : List (Option Y')} {x' : X'}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hpend : (rightQueries ws).length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, oy.isSome) :
    Sum.inl x' ∈ parFixedLeftFn s (ws, ys) := by
  unfold parFixedLeftFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), hgl]
  dsimp only
  rw [if_pos hpend]
  exact Part.mem_some _

theorem parFixedLeftFn_inr_inr_mem (s : PFunDDS.DDS X Y)
    {ws : List (X ⊕ X')} {ys : List (Option Y')} {x' : X'} {y' : Y'}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hbal : (rightQueries ws).length = ys.length)
    (hne : ys ≠ []) (hy' : ys.getLast hne = some y')
    (hprop : ∀ oy ∈ ys, oy.isSome) :
    Sum.inr (Sum.inr y') ∈ parFixedLeftFn s (ws, ys) := by
  unfold parFixedLeftFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), hgl]
  dsimp only
  rw [if_neg (by omega), dif_pos ⟨hbal, hne⟩, hy']
  exact Part.mem_some _

theorem parFixedLeftFn_inr_inl_mem (s : PFunDDS.DDS X Y)
    {ws : List (X ⊕ X')} {ys : List (Option Y')} {x : X} {y : Y}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hbal : (rightQueries ws).length = ys.length)
    (hy : y ∈ s.1 (leftQueries ws))
    (hprop : ∀ oy ∈ ys, oy.isSome) :
    Sum.inr (Sum.inl y) ∈ parFixedLeftFn s (ws, ys) := by
  unfold parFixedLeftFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), hgl]
  dsimp only
  rw [if_pos hbal, Part.mem_map_iff]
  exact ⟨y, hy, rfl⟩

/-- The fixed-left-component converter never moves past a `⊥`. -/
theorem answersInY_parFixedLeftFn (s : PFunDDS.DDS X Y) :
    AnswersInY (parFixedLeftFn (X' := X') (Y' := Y') s) := by
  rintro ⟨ws, ys⟩ - hnone hdom
  rw [Part.dom_iff_mem] at hdom
  obtain ⟨m, hm⟩ := hdom
  exact absurd (parFixedLeftFn_prop hm none hnone) (by simp)

/-- The fixed-left-component converter never opens a streak of two
queries. -/
theorem answersWithin_parFixedLeftFn (s : PFunDDS.DDS X Y) :
    AnswersWithin (parFixedLeftFn (X' := X') (Y' := Y') s) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  have h0 := (parFixedLeftFn_inl_inv hx0).2.1
  have h1 := (parFixedLeftFn_inl_inv hx1).2.1
  simp only [List.take_zero, List.append_nil] at h0
  simp only [List.length_append, List.length_take] at h1
  omega

/-- `parFixedLeftFn s` is a deterministic discrete converter. -/
theorem isDDC_parFixedLeftFn (s : PFunDDS.DDS X Y) :
    IsDDC (parFixedLeftFn (X' := X') (Y' := Y') s) :=
  ⟨answersInY_parFixedLeftFn s, 2, answersWithin_parFixedLeftFn s⟩

variable {t : PFunDDS.DDS X' Y'}

/-- An improper recorded answer kills the drive of the fixed-left
converter. -/
private theorem drive_parFixedLeft_none_dead {fuel : ℕ}
    {ws : List (X ⊕ X')} {xs : List X'} {ys : List (Option Y')}
    {p : (Y ⊕ Y') × List X' × List (Option Y')} :
    p ∉ drive (parFixedLeftFn s) t fuel ws xs (ys ++ [none]) := by
  intro hp
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x, hm, -⟩ | ⟨v, hm, -⟩
    · exact absurd (parFixedLeftFn_prop hm none (by simp)) (by simp)
    · exact absurd (parFixedLeftFn_prop hm none (by simp)) (by simp)

/-- One right round of the fixed-left drive, destructed. -/
theorem drive_parFixedLeft_right_round_elim
    {ws : List (X ⊕ X')} {x' : X'} {ys : List (Option Y')} {fuel : ℕ}
    {xs : List X'} {p : (Y ⊕ Y') × List X' × List (Option Y')}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hpend : (rightQueries ws).length = ys.length + 1)
    (hp : p ∈ drive (parFixedLeftFn s) t fuel ws xs ys) :
    ∃ y' : Y',
      PFunDDS.output (t⊥) (xs ++ [x'])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y' ∧
      p = (Sum.inr y', xs ++ [x'], ys ++ [some y']) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x₁, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hgl₁, -, -⟩ := parFixedLeftFn_inl_inv hm
      rw [hgl] at hgl₁
      have hx : x' = x₁ := Sum.inr.inj (Option.some.inj hgl₁)
      subst hx
      rcases hout : PFunDDS.output (t⊥) (xs ++ [x'])
          (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y'
      · rw [hout] at hp'
        exact absurd hp' drive_parFixedLeft_none_dead
      · rw [hout] at hp'
        rcases fuel with _ | fuel
        · simp [drive] at hp'
        · rcases drive_succ_elim hp' with ⟨x₂, hm₂, -⟩ | ⟨v₂, hm₂, rfl⟩
          · obtain ⟨-, hpend₂, -⟩ := parFixedLeftFn_inl_inv hm₂
            simp only [List.length_append, List.length_singleton] at hpend₂
            omega
          · rcases v₂ with y₂ | y₂'
            · obtain ⟨⟨x₂, hgl₂⟩, -, -⟩ := parFixedLeftFn_inr_inl_inv hm₂
              rw [hgl] at hgl₂
              exact absurd (Option.some.inj hgl₂) (by simp)
            · obtain ⟨-, -, hne₂, hy₂⟩ := parFixedLeftFn_inr_inr_inv hm₂
              rw [List.getLast_append_singleton (l := ys)] at hy₂
              obtain rfl : y' = y₂' := Option.some.inj hy₂
              exact ⟨y', rfl, rfl⟩
    · rcases v with y | y'
      · obtain ⟨⟨x₁, hgl₁⟩, -, -⟩ := parFixedLeftFn_inr_inl_inv hm
        rw [hgl] at hgl₁
        exact absurd (Option.some.inj hgl₁) (by simp)
      · obtain ⟨-, hbal, -, -⟩ := parFixedLeftFn_inr_inr_inv hm
        omega

/-- One right round of the fixed-left drive, constructed. -/
theorem drive_parFixedLeft_right_round_mem
    {ws : List (X ⊕ X')} {x' : X'} {ys : List (Option Y')} {xs : List X'}
    (hgl : ws.getLast? = some (Sum.inr x'))
    (hpend : (rightQueries ws).length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, oy.isSome) {y' : Y'}
    (hy' : PFunDDS.output (t⊥) (xs ++ [x'])
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some y') :
    (Sum.inr y', xs ++ [x'], ys ++ [some y']) ∈
      drive (parFixedLeftFn s) t 2 ws xs ys := by
  have hm : Sum.inl x' ∈ parFixedLeftFn s (ws, ys) :=
    parFixedLeftFn_inl_mem s hgl hpend hprop
  refine drive_mem_query (parFixedLeftFn s) t hm ?_
  rw [hy']
  have hm₂ : Sum.inr (Sum.inr y')
      ∈ parFixedLeftFn s (ws, ys ++ [some y']) := by
    refine parFixedLeftFn_inr_inr_mem s hgl (by simp [hpend])
      (by simp) ?_ ?_
    · rw [List.getLast_append_singleton]
    · intro oy hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hprop oy hmem
      · rw [List.mem_singleton.mp hmem]
        rfl
  exact drive_mem_answer (parFixedLeftFn s) t hm₂ 0

/-- One left round of the fixed-left drive, destructed. -/
theorem drive_parFixedLeft_left_round_elim
    {ws : List (X ⊕ X')} {x : X} {ys : List (Option Y')} {fuel : ℕ}
    {xs : List X'} {p : (Y ⊕ Y') × List X' × List (Option Y')}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hp : p ∈ drive (parFixedLeftFn s) t fuel ws xs ys) :
    ∃ y : Y, y ∈ s.1 (leftQueries ws) ∧ p = (Sum.inl y, xs, ys) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x₁, hm, -⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hgl₁, -, -⟩ := parFixedLeftFn_inl_inv hm
      rw [hgl] at hgl₁
      exact absurd (Option.some.inj hgl₁).symm (by simp)
    · rcases v with y | y'
      · obtain ⟨-, -, hy⟩ := parFixedLeftFn_inr_inl_inv hm
        exact ⟨y, hy, rfl⟩
      · obtain ⟨⟨x₁, hgl₁⟩, -, -⟩ := parFixedLeftFn_inr_inr_inv hm
        rw [hgl] at hgl₁
        exact absurd (Option.some.inj hgl₁).symm (by simp)

/-- One left round of the fixed-left drive, constructed. -/
theorem drive_parFixedLeft_left_round_mem
    {ws : List (X ⊕ X')} {x : X} {ys : List (Option Y')} {xs : List X'}
    (hgl : ws.getLast? = some (Sum.inl x))
    (hbal : (rightQueries ws).length = ys.length)
    (hprop : ∀ oy ∈ ys, oy.isSome) {y : Y}
    (hy : y ∈ s.1 (leftQueries ws)) :
    (Sum.inl y, xs, ys) ∈ drive (parFixedLeftFn s) t 2 ws xs ys :=
  drive_mem_answer (parFixedLeftFn s) t
    (parFixedLeftFn_inr_inl_mem s hgl hbal hy hprop) 1

/-- Forward realization for the fixed-left converter. -/
theorem driveOuter_parFixedLeft_of_dom (s : PFunDDS.DDS X Y)
    (t : PFunDDS.DDS X' Y') :
    ∀ (rest ws : List (X ⊕ X')) (ys : List (Option Y')),
      (rightQueries ws).length = ys.length →
      (∀ oy ∈ ys, oy.isSome) →
      (leftQueries (ws ++ rest) ∈ PFunDDS.dom s ∨
        leftQueries (ws ++ rest) = []) →
      (rightQueries (ws ++ rest) ∈ PFunDDS.dom t ∨
        rightQueries (ws ++ rest) = []) →
      ∃ vs ys',
        (vs, rightQueries (ws ++ rest), ys') ∈
          driveOuter (parFixedLeftFn s) t 2 ws (rightQueries ws) ys rest ∧
        ∀ _ : rest ≠ [], ∃ v, vs.getLast? = some v ∧
          v ∈ (PFunDDS.par s t).1 (ws ++ rest) := by
  intro rest
  induction rest with
  | nil =>
      intro ws ys _ _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro ws ys hlen hprop hLdom hRdom
      have hgl : (ws ++ [u]).getLast? = some u := by
        simp
      cases u with
      | inr x' =>
          have hRpre : rightQueries ws ++ [x'] <+:
              rightQueries (ws ++ (Sum.inr x' :: rest)) := by
            rw [show ws ++ (Sum.inr x' :: rest) = (ws ++ [Sum.inr x']) ++ rest
                by simp, rightQueries_append, rightQueries_concat_inr]
            exact List.prefix_append _ _
          have hnext : rightQueries ws ++ [x'] ∈ PFunDDS.dom t := by
            rcases hRdom with hmem | hnil
            · exact PFunDDS.prefix_closed t hRpre (by simp) hmem
            · exact absurd (List.prefix_nil.mp (hnil ▸ hRpre)) (by simp)
          have hxs : rightQueries ws ∈ PFunDDS.dom t ∨
              rightQueries ws = [] := by
            rcases eq_or_ne (rightQueries ws) [] with hnil | hne
            · exact Or.inr hnil
            · exact Or.inl (PFunDDS.prefix_closed t ⟨[x'], rfl⟩ hne hnext)
          have hout : PFunDDS.output (t⊥) (rightQueries ws ++ [x'])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              = some (PFunDDS.output t (rightQueries ws ++ [x']) hnext) :=
            PFunDDS.output_fullyDefined_append_of_mem t (rightQueries ws) x'
              hxs hnext
          have hround := drive_parFixedLeft_right_round_mem
            (s := s) (t := t) (ws := ws ++ [Sum.inr x']) (ys := ys)
            (xs := rightQueries ws) hgl (by simp [hlen]) hprop hout
          set y' := PFunDDS.output t (rightQueries ws ++ [x']) hnext
            with hy'def
          obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (ws ++ [Sum.inr x'])
            (ys ++ [some y']) (by simp [hlen])
            (by
              intro oy hmem
              rcases List.mem_append.mp hmem with hm | hm
              · exact hprop oy hm
              · rw [List.mem_singleton.mp hm]; rfl)
            (by simpa [List.append_assoc] using hLdom)
            (by simpa [List.append_assoc] using hRdom)
          rw [rightQueries_concat_inr] at hmem'
          refine ⟨Sum.inr y' :: vs', ys'', ?_, ?_⟩
          · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(Sum.inr y', rightQueries ws ++ [x'], ys ++ [some y']),
              hround, (vs', rightQueries (ws ++ (Sum.inr x' :: rest)), ys''),
              ?_, rfl⟩
            rw [show ws ++ (Sum.inr x' :: rest) = (ws ++ [Sum.inr x']) ++ rest
                by simp]
            exact hmem'
          · intro _
            cases hvs : vs' with
            | nil =>
                have hrest : rest = [] := by
                  have hlen' := driveOuter_length (parFixedLeftFn s) t 2 hmem'
                  rw [hvs] at hlen'
                  exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
                subst hrest
                refine ⟨Sum.inr y', by rw [List.getLast?_singleton], ?_⟩
                rw [mem_par_toPFun_iff]
                refine ⟨?_, ?_, ?_⟩
                · intro hne'
                  show (s.1 (leftQueries (ws ++ [Sum.inr x']))).Dom
                  rw [leftQueries_concat_inr]
                  rw [show ws ++ ([Sum.inr x'] : List _) = ws ++ [Sum.inr x']
                    from rfl, leftQueries_concat_inr] at hne'
                  rcases hLdom with hmem | hnil
                  · rw [show ws ++ (Sum.inr x' :: ([] : List _))
                        = ws ++ [Sum.inr x'] from rfl,
                      leftQueries_concat_inr] at hmem
                    exact hmem
                  · rw [show ws ++ (Sum.inr x' :: ([] : List _))
                        = ws ++ [Sum.inr x'] from rfl,
                      leftQueries_concat_inr] at hnil
                    exact absurd hnil hne'
                · intro _
                  show (t.1 (rightQueries (ws ++ [Sum.inr x']))).Dom
                  rw [rightQueries_concat_inr]
                  exact hnext
                · refine Or.inr ⟨x', by simp, ?_⟩
                  rw [Part.mem_map_iff]
                  refine ⟨y', ?_, rfl⟩
                  show y' ∈ t.1 (rightQueries (ws ++ ([Sum.inr x'] : List _)))
                  rw [rightQueries_concat_inr]
                  exact hy'def ▸ Part.get_mem hnext
            | cons v0 vs0 =>
                have hrest : rest ≠ [] := by
                  have hlen' := driveOuter_length (parFixedLeftFn s) t 2 hmem'
                  rw [hvs] at hlen'
                  intro hnil
                  rw [hnil] at hlen'
                  simp at hlen'
                obtain ⟨v, hvlast, hvmem⟩ := hlast' hrest
                rw [hvs] at hvlast
                refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                simpa [List.append_assoc] using hvmem
      | inl x =>
          have hLpre : leftQueries ws ++ [x] <+:
              leftQueries (ws ++ (Sum.inl x :: rest)) := by
            rw [show ws ++ (Sum.inl x :: rest) = (ws ++ [Sum.inl x]) ++ rest
                by simp, leftQueries_append, leftQueries_concat_inl]
            exact List.prefix_append _ _
          have hnext : leftQueries ws ++ [x] ∈ PFunDDS.dom s := by
            rcases hLdom with hmem | hnil
            · exact PFunDDS.prefix_closed s hLpre (by simp) hmem
            · exact absurd (List.prefix_nil.mp (hnil ▸ hLpre)) (by simp)
          set y := PFunDDS.output s (leftQueries ws ++ [x]) hnext with hydef
          have hymem : y ∈ s.1 (leftQueries (ws ++ [Sum.inl x])) := by
            rw [leftQueries_concat_inl]
            exact hydef ▸ Part.get_mem hnext
          have hround := drive_parFixedLeft_left_round_mem
            (s := s) (t := t) (ws := ws ++ [Sum.inl x]) (ys := ys)
            (xs := rightQueries ws) hgl (by simp [hlen]) hprop hymem
          obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (ws ++ [Sum.inl x]) ys
            (by simp [hlen]) hprop
            (by simpa [List.append_assoc] using hLdom)
            (by simpa [List.append_assoc] using hRdom)
          rw [rightQueries_concat_inl] at hmem'
          refine ⟨Sum.inl y :: vs', ys'', ?_, ?_⟩
          · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(Sum.inl y, rightQueries ws, ys), hround,
              (vs', rightQueries (ws ++ (Sum.inl x :: rest)), ys''), ?_, rfl⟩
            rw [show ws ++ (Sum.inl x :: rest) = (ws ++ [Sum.inl x]) ++ rest
                by simp]
            exact hmem'
          · intro _
            cases hvs : vs' with
            | nil =>
                have hrest : rest = [] := by
                  have hlen' := driveOuter_length (parFixedLeftFn s) t 2 hmem'
                  rw [hvs] at hlen'
                  exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
                subst hrest
                refine ⟨Sum.inl y, by rw [List.getLast?_singleton], ?_⟩
                rw [mem_par_toPFun_iff]
                refine ⟨fun _ => ?_, ?_, ?_⟩
                · show (s.1 (leftQueries (ws ++ [Sum.inl x]))).Dom
                  rw [leftQueries_concat_inl]
                  exact hnext
                · intro hne'
                  show (t.1 (rightQueries (ws ++ [Sum.inl x]))).Dom
                  rw [rightQueries_concat_inl]
                  rw [show ws ++ ([Sum.inl x] : List _) = ws ++ [Sum.inl x]
                    from rfl, rightQueries_concat_inl] at hne'
                  rcases hRdom with hmem | hnil
                  · rw [show ws ++ (Sum.inl x :: ([] : List _))
                        = ws ++ [Sum.inl x] from rfl,
                      rightQueries_concat_inl] at hmem
                    exact hmem
                  · rw [show ws ++ (Sum.inl x :: ([] : List _))
                        = ws ++ [Sum.inl x] from rfl,
                      rightQueries_concat_inl] at hnil
                    exact absurd hnil hne'
                · refine Or.inl ⟨x, by simp, ?_⟩
                  rw [Part.mem_map_iff]
                  exact ⟨y, hymem, rfl⟩
            | cons v0 vs0 =>
                have hrest : rest ≠ [] := by
                  have hlen' := driveOuter_length (parFixedLeftFn s) t 2 hmem'
                  rw [hvs] at hlen'
                  intro hnil
                  rw [hnil] at hlen'
                  simp at hlen'
                obtain ⟨v, hvlast, hvmem⟩ := hlast' hrest
                rw [hvs] at hvlast
                refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                simpa [List.append_assoc] using hvmem

/-- Backward realization for the fixed-left converter. -/
theorem driveOuter_parFixedLeft_mem_imp (s : PFunDDS.DDS X Y)
    (t : PFunDDS.DDS X' Y') :
    ∀ (rest ws : List (X ⊕ X')) (ys : List (Option Y')) {fuel : ℕ}
      {r : List (Y ⊕ Y') × List X' × List (Option Y')},
      (rightQueries ws).length = ys.length →
      (∀ oy ∈ ys, oy.isSome) →
      (leftQueries ws ∈ PFunDDS.dom s ∨ leftQueries ws = []) →
      (rightQueries ws ∈ PFunDDS.dom t ∨ rightQueries ws = []) →
      r ∈ driveOuter (parFixedLeftFn s) t fuel ws (rightQueries ws) ys rest →
      r.2.1 = rightQueries (ws ++ rest) ∧
      (rest ≠ [] → ∃ v, r.1.getLast? = some v ∧
        v ∈ (PFunDDS.par s t).1 (ws ++ rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro ws ys fuel r _ _ _ _ hr
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro ws ys fuel r hlen hprop hLdom hRdom hr
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      have hgl : (ws ++ [u]).getLast? = some u := by simp
      cases u with
      | inr x' =>
          obtain ⟨y', hout, rfl⟩ := drive_parFixedLeft_right_round_elim
            (ws := ws ++ [Sum.inr x']) hgl (by simp [hlen]) hr₁
          obtain ⟨hnext, houtT⟩ :=
            PFunDDS.mem_of_output_fullyDefined_append_eq_some t
              (rightQueries ws) x' hRdom hout
          have hprop' : ∀ oy ∈ ys ++ [some y'], oy.isSome := by
            intro oy hmem
            rcases List.mem_append.mp hmem with hm | hm
            · exact hprop oy hm
            · rw [List.mem_singleton.mp hm]; rfl
          have hrr' : rr ∈ driveOuter (parFixedLeftFn s) t fuel
              (ws ++ [Sum.inr x']) (rightQueries (ws ++ [Sum.inr x']))
              (ys ++ [some y']) rest := by
            rw [rightQueries_concat_inr]
            exact hrr
          obtain ⟨hthread, hcond⟩ := ih (ws ++ [Sum.inr x']) (ys ++ [some y'])
            (by simp [hlen]) hprop'
            (by rw [leftQueries_concat_inr]; exact hLdom)
            (by rw [rightQueries_concat_inr]; exact Or.inl hnext) hrr'
          refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
          cases hrest : rest with
          | nil =>
              subst hrest
              simp only [driveOuter, Part.mem_some_iff] at hrr'
              subst hrr'
              refine ⟨Sum.inr y', by rw [List.getLast?_singleton], ?_⟩
              rw [mem_par_toPFun_iff]
              refine ⟨?_, fun _ => ?_, ?_⟩
              · intro hne'
                rw [show ws ++ (Sum.inr x' :: ([] : List _))
                      = ws ++ [Sum.inr x'] from rfl,
                  leftQueries_concat_inr] at hne' ⊢
                rcases hLdom with hmem | hnil
                · exact hmem
                · exact absurd hnil hne'
              · show (t.1 (rightQueries (ws ++ [Sum.inr x']))).Dom
                rw [rightQueries_concat_inr]
                exact hnext
              · refine Or.inr ⟨x', by simp, ?_⟩
                rw [Part.mem_map_iff]
                refine ⟨y', ?_, rfl⟩
                show y' ∈ t.1 (rightQueries (ws ++ ([Sum.inr x'] : List _)))
                rw [rightQueries_concat_inr]
                exact houtT ▸ Part.get_mem hnext
          | cons r0 rs0 =>
              obtain ⟨v, hvlast, hvmem⟩ := hcond (by simp [hrest])
              have hlenrr := driveOuter_length (parFixedLeftFn s) t fuel hrr'
              cases hrr1 : rr.1 with
              | nil =>
                  rw [hrr1] at hlenrr
                  simp [hrest] at hlenrr
              | cons v0 vs0 =>
                  rw [hrr1] at hvlast
                  refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                  rw [hrest] at hvmem
                  simpa [List.append_assoc] using hvmem
      | inl x =>
          obtain ⟨y, hy, rfl⟩ := drive_parFixedLeft_left_round_elim
            (ws := ws ++ [Sum.inl x]) hgl hr₁
          have hLnext : leftQueries (ws ++ [Sum.inl x]) ∈ PFunDDS.dom s :=
            Part.dom_iff_mem.mpr ⟨y, hy⟩
          have hrr' : rr ∈ driveOuter (parFixedLeftFn s) t fuel
              (ws ++ [Sum.inl x]) (rightQueries (ws ++ [Sum.inl x])) ys
              rest := by
            rw [rightQueries_concat_inl]
            exact hrr
          obtain ⟨hthread, hcond⟩ := ih (ws ++ [Sum.inl x]) ys
            (by simp [hlen]) hprop
            (Or.inl hLnext)
            (by rw [rightQueries_concat_inl]; exact hRdom) hrr'
          refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
          cases hrest : rest with
          | nil =>
              subst hrest
              simp only [driveOuter, Part.mem_some_iff] at hrr'
              subst hrr'
              refine ⟨Sum.inl y, by rw [List.getLast?_singleton], ?_⟩
              rw [mem_par_toPFun_iff]
              refine ⟨fun _ => ?_, ?_, ?_⟩
              · show (s.1 (leftQueries (ws ++ [Sum.inl x]))).Dom
                exact hLnext
              · intro hne'
                rw [show ws ++ (Sum.inl x :: ([] : List _))
                      = ws ++ [Sum.inl x] from rfl,
                  rightQueries_concat_inl] at hne' ⊢
                rcases hRdom with hmem | hnil
                · exact hmem
                · exact absurd hnil hne'
              · refine Or.inl ⟨x, by simp, ?_⟩
                rw [Part.mem_map_iff]
                exact ⟨y, hy, rfl⟩
          | cons r0 rs0 =>
              obtain ⟨v, hvlast, hvmem⟩ := hcond (by simp [hrest])
              have hlenrr := driveOuter_length (parFixedLeftFn s) t fuel hrr'
              cases hrr1 : rr.1 with
              | nil =>
                  rw [hrr1] at hlenrr
                  simp [hrest] at hlenrr
              | cons v0 vs0 =>
                  rw [hrr1] at hvlast
                  refine ⟨v, by rw [List.getLast?_cons_cons, hvlast], ?_⟩
                  rw [hrest] at hvmem
                  simpa [List.append_assoc] using hvmem

/-- **The mirror fixed-component realization**: applying the
fixed-left-component converter to `t` *is* the parallel composition
`s ‖ t`. -/
theorem apply_parFixedLeftFn (s : PFunDDS.DDS X Y) (t : PFunDDS.DDS X' Y') :
    apply (parFixedLeftFn s) t = PFunDDS.par s t := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (apply (parFixedLeftFn s) t).1
      = applyRaw (parFixedLeftFn s) t from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (parFixedLeftFn s) t fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    have hr' : r ∈ driveOuter (parFixedLeftFn s) t fuel []
        (rightQueries ([] : List (X ⊕ X'))) [] us := by
      simpa [rightQueries] using hr
    obtain ⟨-, hcond⟩ := driveOuter_parFixedLeft_mem_imp s t us [] []
      (by simp [rightQueries]) (by simp)
      (Or.inr (by simp [leftQueries])) (Or.inr (by simp [rightQueries])) hr'
    obtain ⟨v', hv'last, hv'mem⟩ := hcond hne
    rw [hlast] at hv'last
    obtain rfl : v = v' := Option.some.inj hv'last
    simpa using hv'mem
  · intro hv
    have hne : us ≠ [] := by
      rintro rfl
      rw [mem_par_toPFun_iff] at hv
      rcases hv.2.2 with ⟨x, hgl, -⟩ | ⟨x', hgl, -⟩ <;> simp at hgl
    have hv' := hv
    rw [mem_par_toPFun_iff] at hv'
    obtain ⟨hL, hR, -⟩ := hv'
    have hLdom : leftQueries us ∈ PFunDDS.dom s ∨ leftQueries us = [] := by
      rcases eq_or_ne (leftQueries us) [] with hnil | hne'
      · exact Or.inr hnil
      · exact Or.inl (hL hne')
    have hRdom : rightQueries us ∈ PFunDDS.dom t ∨ rightQueries us = [] := by
      rcases eq_or_ne (rightQueries us) [] with hnil | hne'
      · exact Or.inr hnil
      · exact Or.inl (hR hne')
    obtain ⟨vs, ys', hmem, hval⟩ := driveOuter_parFixedLeft_of_dom s t us
      [] [] (by simp [rightQueries]) (by simp)
      (by simpa using hLdom) (by simpa using hRdom)
    obtain ⟨v₀, hlast, hv₀⟩ := hval hne
    obtain rfl : v₀ = v := Part.mem_unique (by simpa using hv₀) hv
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, rightQueries (([] : List (X ⊕ X')) ++ us), ys'), ?_, hlast⟩
    simpa [rightQueries] using hmem

end ParFixedLeft

/-! ## Component embeddings: one interface of a composition, interrogated

`embedInlFn` presents the left interface `(X, Y)` upward over the
composite resource interface `(X ⊕ X', Y ⊕ Y')`: it relabels queries into
the left tag and relays properly tagged left answers.  Applying it to a
composition recovers the left component exactly
(`apply_embedInlFn_par`) — the one-sided decoupling lemmas make the right
component invisible along all-left histories.  These converters give the
strict cancellation law for `‖` (`equivalent_left_of_par_equivalent`),
which is what makes the parallel decomposition of a strict behavior
unique. -/

section EmbedComponent

variable {X Y X' Y' : Type*}

/-- Interrogate the left component of a composition. -/
def embedInlFn : ProtocolFn X Y (X ⊕ X') (Y ⊕ Y') := fun p =>
  if p.2.all fun oy => (oy.bind Sum.getLeft?).isSome then
    if hq : p.1.length = p.2.length + 1 then
      Part.some (Sum.inl (Sum.inl (p.1.getLast (by
        apply List.ne_nil_of_length_pos
        omega))))
    else if h : p.1.length = p.2.length ∧ 0 < p.2.length then
      match p.2.getLast (List.ne_nil_of_length_pos h.2) with
      | some (Sum.inl y) => Part.some (Sum.inr y)
      | _ => Part.none
    else Part.none
  else Part.none

/-- Interrogate the right component of a composition. -/
def embedInrFn : ProtocolFn X' Y' (X ⊕ X') (Y ⊕ Y') := fun p =>
  if p.2.all fun oy => (oy.bind Sum.getRight?).isSome then
    if hq : p.1.length = p.2.length + 1 then
      Part.some (Sum.inl (Sum.inr (p.1.getLast (by
        apply List.ne_nil_of_length_pos
        omega))))
    else if h : p.1.length = p.2.length ∧ 0 < p.2.length then
      match p.2.getLast (List.ne_nil_of_length_pos h.2) with
      | some (Sum.inr y') => Part.some (Sum.inr y')
      | _ => Part.none
    else Part.none
  else Part.none

theorem embedInlFn_prop {us : List X} {ys : List (Option (Y ⊕ Y'))}
    {m : (X ⊕ X') ⊕ Y}
    (h : m ∈ embedInlFn (X' := X') (Y' := Y') (us, ys)) :
    ∀ oy ∈ ys, (oy.bind Sum.getLeft?).isSome := by
  unfold embedInlFn at h
  dsimp only at h
  by_cases hall : ys.all fun oy => (oy.bind Sum.getLeft?).isSome
  · exact List.all_eq_true.mp hall
  · rw [if_neg hall] at h
    simp at h

theorem embedInrFn_prop {us : List X'} {ys : List (Option (Y ⊕ Y'))}
    {m : (X ⊕ X') ⊕ Y'}
    (h : m ∈ embedInrFn (X := X) (Y := Y) (us, ys)) :
    ∀ oy ∈ ys, (oy.bind Sum.getRight?).isSome := by
  unfold embedInrFn at h
  dsimp only at h
  by_cases hall : ys.all fun oy => (oy.bind Sum.getRight?).isSome
  · exact List.all_eq_true.mp hall
  · rw [if_neg hall] at h
    simp at h

theorem embedInlFn_inl_inv {us : List X} {ys : List (Option (Y ⊕ Y'))}
    {q : X ⊕ X'}
    (h : Sum.inl q ∈ embedInlFn (X' := X') (Y' := Y') (us, ys)) :
    ∃ hne : us ≠ [],
      q = Sum.inl (us.getLast hne) ∧ us.length = ys.length + 1 := by
  have hprop := embedInlFn_prop h
  unfold embedInlFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split_ifs at h with hq ha
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨List.ne_nil_of_length_pos (by omega), h, hq⟩
  · split at h
    · simp at h
    · simp at h
  · simp at h

theorem embedInlFn_inr_inv {us : List X} {ys : List (Option (Y ⊕ Y'))}
    {y : Y}
    (h : Sum.inr y ∈ embedInlFn (X' := X') (Y' := Y') (us, ys)) :
    us.length = ys.length ∧ ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some (Sum.inl y) := by
  have hprop := embedInlFn_prop h
  unfold embedInlFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split_ifs at h with hq ha
  · simp at h
  · split at h
    · rename_i y₀ hy₀
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      subst h
      exact ⟨ha.1, ha.2, hy₀⟩
    · simp at h
  · simp at h

theorem embedInrFn_inl_inv {us : List X'} {ys : List (Option (Y ⊕ Y'))}
    {q : X ⊕ X'}
    (h : Sum.inl q ∈ embedInrFn (X := X) (Y := Y) (us, ys)) :
    ∃ hne : us ≠ [],
      q = Sum.inr (us.getLast hne) ∧ us.length = ys.length + 1 := by
  have hprop := embedInrFn_prop h
  unfold embedInrFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split_ifs at h with hq ha
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨List.ne_nil_of_length_pos (by omega), h, hq⟩
  · split at h
    · simp at h
    · simp at h
  · simp at h

theorem embedInrFn_inr_inv {us : List X'} {ys : List (Option (Y ⊕ Y'))}
    {y' : Y'}
    (h : Sum.inr y' ∈ embedInrFn (X := X) (Y := Y) (us, ys)) :
    us.length = ys.length ∧ ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some (Sum.inr y') := by
  have hprop := embedInrFn_prop h
  unfold embedInrFn at h
  dsimp only at h
  rw [if_pos (List.all_eq_true.mpr hprop)] at h
  split_ifs at h with hq ha
  · simp at h
  · split at h
    · rename_i y₀ hy₀
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      subst h
      exact ⟨ha.1, ha.2, hy₀⟩
    · simp at h
  · simp at h

theorem embedInlFn_inl_mem {us : List X} {ys : List (Option (Y ⊕ Y'))}
    (hlen : us.length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, (oy.bind Sum.getLeft?).isSome) :
    Sum.inl (Sum.inl (us.getLast (by
        apply List.ne_nil_of_length_pos
        omega)))
      ∈ embedInlFn (X' := X') (Y' := Y') (us, ys) := by
  unfold embedInlFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), dif_pos hlen]
  exact Part.mem_some _

theorem embedInlFn_inr_mem {us : List X} {ys : List (Option (Y ⊕ Y'))}
    (hlen : us.length = ys.length) (h0 : 0 < ys.length)
    (hprop : ∀ oy ∈ ys, (oy.bind Sum.getLeft?).isSome) {y : Y}
    (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some (Sum.inl y)) :
    Sum.inr y ∈ embedInlFn (X' := X') (Y' := Y') (us, ys) := by
  unfold embedInlFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), dif_neg (by omega),
    dif_pos ⟨hlen, h0⟩, hy]
  exact Part.mem_some _

theorem embedInrFn_inl_mem {us : List X'} {ys : List (Option (Y ⊕ Y'))}
    (hlen : us.length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, (oy.bind Sum.getRight?).isSome) :
    Sum.inl (Sum.inr (us.getLast (by
        apply List.ne_nil_of_length_pos
        omega)))
      ∈ embedInrFn (X := X) (Y := Y) (us, ys) := by
  unfold embedInrFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), dif_pos hlen]
  exact Part.mem_some _

theorem embedInrFn_inr_mem {us : List X'} {ys : List (Option (Y ⊕ Y'))}
    (hlen : us.length = ys.length) (h0 : 0 < ys.length)
    (hprop : ∀ oy ∈ ys, (oy.bind Sum.getRight?).isSome) {y' : Y'}
    (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some (Sum.inr y')) :
    Sum.inr y' ∈ embedInrFn (X := X) (Y := Y) (us, ys) := by
  unfold embedInrFn
  dsimp only
  rw [if_pos (List.all_eq_true.mpr hprop), dif_neg (by omega),
    dif_pos ⟨hlen, h0⟩, hy]
  exact Part.mem_some _

theorem answersInY_embedInlFn :
    AnswersInY (embedInlFn (X := X) (Y := Y) (X' := X') (Y' := Y')) := by
  rintro ⟨us, ys⟩ - hnone hdom
  rw [Part.dom_iff_mem] at hdom
  obtain ⟨m, hm⟩ := hdom
  exact absurd (embedInlFn_prop hm none hnone) (by simp)

theorem answersInY_embedInrFn :
    AnswersInY (embedInrFn (X := X) (Y := Y) (X' := X') (Y' := Y')) := by
  rintro ⟨us, ys⟩ - hnone hdom
  rw [Part.dom_iff_mem] at hdom
  obtain ⟨m, hm⟩ := hdom
  exact absurd (embedInrFn_prop hm none hnone) (by simp)

theorem answersWithin_embedInlFn :
    AnswersWithin (embedInlFn (X := X) (Y := Y) (X' := X') (Y' := Y')) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  obtain ⟨-, -, h0⟩ := embedInlFn_inl_inv hx0
  obtain ⟨-, -, h1⟩ := embedInlFn_inl_inv hx1
  simp only [List.take_zero, List.append_nil] at h0
  simp only [List.length_append, List.length_take] at h1
  omega

theorem answersWithin_embedInrFn :
    AnswersWithin (embedInrFn (X := X) (Y := Y) (X' := X') (Y' := Y')) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  obtain ⟨-, -, h0⟩ := embedInrFn_inl_inv hx0
  obtain ⟨-, -, h1⟩ := embedInrFn_inl_inv hx1
  simp only [List.take_zero, List.append_nil] at h0
  simp only [List.length_append, List.length_take] at h1
  omega

theorem isDDC_embedInlFn :
    IsDDC (embedInlFn (X := X) (Y := Y) (X' := X') (Y' := Y')) :=
  ⟨answersInY_embedInlFn, 2, answersWithin_embedInlFn⟩

theorem isDDC_embedInrFn :
    IsDDC (embedInrFn (X := X) (Y := Y) (X' := X') (Y' := Y')) :=
  ⟨answersInY_embedInrFn, 2, answersWithin_embedInrFn⟩

variable {r : PFunDDS.DDS X Y} {u : PFunDDS.DDS X' Y'}

/-- One embedding round against a composition, destructed: the answer is a
properly tagged left answer of the composition's completion. -/
theorem drive_embedInl_round_elim
    {us : List X} {ys : List (Option (Y ⊕ Y'))} {fuel : ℕ}
    {xs : List (X ⊕ X')} {p : Y × List (X ⊕ X') × List (Option (Y ⊕ Y'))}
    (hlen : us.length = ys.length + 1)
    (hp : p ∈ drive embedInlFn (PFunDDS.par r u) fuel us xs ys) :
    ∃ (hne : us ≠ []) (y : Y),
      PFunDDS.output ((PFunDDS.par r u)⊥) (xs ++ [Sum.inl (us.getLast hne)])
        (by rw [PFunDDS.dom_fullyDefined]; simp)
        = some (Sum.inl y) ∧
      p = (y, xs ++ [Sum.inl (us.getLast hne)],
        ys ++ [some (Sum.inl y)]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨q, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hne, rfl, -⟩ := embedInlFn_inl_inv hm
      rcases hout : PFunDDS.output ((PFunDDS.par r u)⊥)
          (xs ++ [Sum.inl (us.getLast hne)])
          (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | jy
      · rw [hout] at hp'
        rcases fuel with _ | fuel
        · simp [drive] at hp'
        · rcases drive_succ_elim hp' with ⟨q₂, hm₂, -⟩ | ⟨v₂, hm₂, -⟩ <;>
            exact absurd (embedInlFn_prop hm₂ none (by simp)) (by simp)
      · rcases jy with y | y'
        · rw [hout] at hp'
          rcases fuel with _ | fuel
          · simp [drive] at hp'
          · rcases drive_succ_elim hp' with ⟨q₂, hm₂, -⟩ | ⟨v₂, hm₂, rfl⟩
            · obtain ⟨-, -, hlen₂⟩ := embedInlFn_inl_inv hm₂
              simp only [List.length_append, List.length_singleton] at hlen₂
              omega
            · obtain ⟨-, h0, hy₂⟩ := embedInlFn_inr_inv hm₂
              rw [List.getLast_append_singleton (l := ys)] at hy₂
              have : y = v₂ := by
                have := Option.some.inj hy₂
                exact Sum.inl.inj this
              subst this
              exact ⟨hne, y, hout, rfl⟩
        · rw [hout] at hp'
          rcases fuel with _ | fuel
          · simp [drive] at hp'
          · rcases drive_succ_elim hp' with ⟨q₂, hm₂, -⟩ | ⟨v₂, hm₂, -⟩ <;>
              exact absurd (embedInlFn_prop hm₂ (some (Sum.inr y'))
                (by simp)) (by simp)
    · obtain ⟨hlen', -⟩ := embedInlFn_inr_inv hm
      omega

/-- One embedding round against a composition, constructed. -/
theorem drive_embedInl_round_mem
    {us : List X} {ys : List (Option (Y ⊕ Y'))} {xs : List (X ⊕ X')}
    (hlen : us.length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, (oy.bind Sum.getLeft?).isSome)
    {y : Y} (hne : us ≠ [])
    (hy : PFunDDS.output ((PFunDDS.par r u)⊥)
        (xs ++ [Sum.inl (us.getLast hne)])
        (by rw [PFunDDS.dom_fullyDefined]; simp)
      = some (Sum.inl y)) :
    (y, xs ++ [Sum.inl (us.getLast hne)], ys ++ [some (Sum.inl y)]) ∈
      drive embedInlFn (PFunDDS.par r u) 2 us xs ys := by
  have hm : Sum.inl (Sum.inl (us.getLast hne))
      ∈ embedInlFn (X' := X') (Y' := Y') (us, ys) :=
    embedInlFn_inl_mem hlen hprop
  refine drive_mem_query embedInlFn (PFunDDS.par r u) hm ?_
  rw [hy]
  have hm₂ : Sum.inr y
      ∈ embedInlFn (X' := X') (Y' := Y') (us, ys ++ [some (Sum.inl y)]) := by
    refine embedInlFn_inr_mem (by simp [hlen]) (by simp) ?_ ?_
    · intro oy hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hprop oy hmem
      · rw [List.mem_singleton.mp hmem]
        rfl
    · rw [List.getLast_append_singleton]
  exact drive_mem_answer embedInlFn (PFunDDS.par r u) hm₂ 0

/-- One embedding round against a composition, right side, destructed. -/
theorem drive_embedInr_round_elim
    {us : List X'} {ys : List (Option (Y ⊕ Y'))} {fuel : ℕ}
    {xs : List (X ⊕ X')} {p : Y' × List (X ⊕ X') × List (Option (Y ⊕ Y'))}
    (hlen : us.length = ys.length + 1)
    (hp : p ∈ drive embedInrFn (PFunDDS.par r u) fuel us xs ys) :
    ∃ (hne : us ≠ []) (y' : Y'),
      PFunDDS.output ((PFunDDS.par r u)⊥) (xs ++ [Sum.inr (us.getLast hne)])
        (by rw [PFunDDS.dom_fullyDefined]; simp)
        = some (Sum.inr y') ∧
      p = (y', xs ++ [Sum.inr (us.getLast hne)],
        ys ++ [some (Sum.inr y')]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨q, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hne, rfl, -⟩ := embedInrFn_inl_inv hm
      rcases hout : PFunDDS.output ((PFunDDS.par r u)⊥)
          (xs ++ [Sum.inr (us.getLast hne)])
          (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | jy
      · rw [hout] at hp'
        rcases fuel with _ | fuel
        · simp [drive] at hp'
        · rcases drive_succ_elim hp' with ⟨q₂, hm₂, -⟩ | ⟨v₂, hm₂, -⟩ <;>
            exact absurd (embedInrFn_prop hm₂ none (by simp)) (by simp)
      · rcases jy with y | y'
        · rw [hout] at hp'
          rcases fuel with _ | fuel
          · simp [drive] at hp'
          · rcases drive_succ_elim hp' with ⟨q₂, hm₂, -⟩ | ⟨v₂, hm₂, -⟩ <;>
              exact absurd (embedInrFn_prop hm₂ (some (Sum.inl y))
                (by simp)) (by simp)
        · rw [hout] at hp'
          rcases fuel with _ | fuel
          · simp [drive] at hp'
          · rcases drive_succ_elim hp' with ⟨q₂, hm₂, -⟩ | ⟨v₂, hm₂, rfl⟩
            · obtain ⟨-, -, hlen₂⟩ := embedInrFn_inl_inv hm₂
              simp only [List.length_append, List.length_singleton] at hlen₂
              omega
            · obtain ⟨-, h0, hy₂⟩ := embedInrFn_inr_inv hm₂
              rw [List.getLast_append_singleton (l := ys)] at hy₂
              have : y' = v₂ := by
                have := Option.some.inj hy₂
                exact Sum.inr.inj this
              subst this
              exact ⟨hne, y', hout, rfl⟩
    · obtain ⟨hlen', -⟩ := embedInrFn_inr_inv hm
      omega

/-- One embedding round against a composition, right side, constructed. -/
theorem drive_embedInr_round_mem
    {us : List X'} {ys : List (Option (Y ⊕ Y'))} {xs : List (X ⊕ X')}
    (hlen : us.length = ys.length + 1)
    (hprop : ∀ oy ∈ ys, (oy.bind Sum.getRight?).isSome)
    {y' : Y'} (hne : us ≠ [])
    (hy : PFunDDS.output ((PFunDDS.par r u)⊥)
        (xs ++ [Sum.inr (us.getLast hne)])
        (by rw [PFunDDS.dom_fullyDefined]; simp)
      = some (Sum.inr y')) :
    (y', xs ++ [Sum.inr (us.getLast hne)], ys ++ [some (Sum.inr y')]) ∈
      drive embedInrFn (PFunDDS.par r u) 2 us xs ys := by
  have hm : Sum.inl (Sum.inr (us.getLast hne))
      ∈ embedInrFn (X := X) (Y := Y) (us, ys) :=
    embedInrFn_inl_mem hlen hprop
  refine drive_mem_query embedInrFn (PFunDDS.par r u) hm ?_
  rw [hy]
  have hm₂ : Sum.inr y'
      ∈ embedInrFn (X := X) (Y := Y) (us, ys ++ [some (Sum.inr y')]) := by
    refine embedInrFn_inr_mem (by simp [hlen]) (by simp) ?_ ?_
    · intro oy hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hprop oy hmem
      · rw [List.mem_singleton.mp hmem]
        rfl
    · rw [List.getLast_append_singleton]
  exact drive_mem_answer embedInrFn (PFunDDS.par r u) hm₂ 0

/-- Forward realization: on a left-component history admitted by `r`, the
embedding drive completes with `r`'s answers. -/
theorem driveOuter_embedInl_of_dom (r : PFunDDS.DDS X Y)
    (u : PFunDDS.DDS X' Y') :
    ∀ (rest l : List X) (ys : List (Option (Y ⊕ Y'))),
      l.length = ys.length →
      (∀ oy ∈ ys, (oy.bind Sum.getLeft?).isSome) →
      (l ++ rest ∈ PFunDDS.dom r ∨ rest = []) →
      (l ∈ PFunDDS.dom r ∨ l = []) →
      ∃ vs ys',
        (vs, (l ++ rest).map Sum.inl, ys') ∈
          driveOuter embedInlFn (PFunDDS.par r u) 2 l (l.map Sum.inl) ys
            rest ∧
        ∀ (h : l ++ rest ∈ PFunDDS.dom r), rest ≠ [] →
          vs.getLast? = some (PFunDDS.output r (l ++ rest) h) := by
  intro rest
  induction rest with
  | nil =>
      intro l ys _ _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun _ hne => absurd rfl hne⟩
  | cons x rest ih =>
      intro l ys hlen hprop hdom hl
      have hdom' : l ++ x :: rest ∈ PFunDDS.dom r := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hnext : l ++ [x] ∈ PFunDDS.dom r :=
        PFunDDS.prefix_closed r ⟨rest, by simp⟩ (by simp) hdom'
      have hout : PFunDDS.output (r⊥) (l ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (PFunDDS.output r (l ++ [x]) hnext) :=
        PFunDDS.output_fullyDefined_append_of_mem r l x hl hnext
      have hgl : (l ++ [x]).getLast (by simp) = x :=
        List.getLast_append_singleton l
      -- the composite completion answers with the relabeled left answer
      have hy' : PFunDDS.output ((PFunDDS.par r u)⊥)
          (l.map Sum.inl ++ [Sum.inl ((l ++ [x]).getLast (by simp))])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (Sum.inl (PFunDDS.output r (l ++ [x]) hnext)) := by
        have hlist : l.map (Sum.inl : X → X ⊕ X')
              ++ [Sum.inl ((l ++ [x]).getLast (by simp))]
            = (l ++ [x]).map Sum.inl := by
          rw [hgl]
          simp
        refine (PFunDDS.output_congr ((PFunDDS.par r u)⊥) hlist
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).trans ?_
        rw [PFunDDS.output_fullyDefined_par_map_inl r u (by simp), hout]
        rfl
      have hround := drive_embedInl_round_mem (r := r) (u := u)
        (us := l ++ [x]) (ys := ys) (xs := l.map Sum.inl)
        (by simp [hlen]) hprop (by simp) hy'
      rw [hgl] at hround
      obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (l ++ [x])
        (ys ++ [some (Sum.inl (PFunDDS.output r (l ++ [x]) hnext))])
        (by simp [hlen])
        (by
          intro oy hmem
          rcases List.mem_append.mp hmem with hm | hm
          · exact hprop oy hm
          · rw [List.mem_singleton.mp hm]
            rfl)
        (Or.inl (by simpa [List.append_assoc] using hdom'))
        (Or.inl hnext)
      refine ⟨PFunDDS.output r (l ++ [x]) hnext :: vs', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        refine ⟨(PFunDDS.output r (l ++ [x]) hnext,
          l.map Sum.inl ++ [Sum.inl x],
          ys ++ [some (Sum.inl (PFunDDS.output r (l ++ [x]) hnext))]),
          hround, (vs', ((l ++ [x]) ++ rest).map Sum.inl, ys''), ?_, ?_⟩
        · rw [show l.map (Sum.inl : X → X ⊕ X') ++ [Sum.inl x]
              = (l ++ [x]).map Sum.inl by simp]
          exact hmem'
        · simp [List.append_assoc]
      · intro h _
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length embedInlFn (PFunDDS.par r u)
                2 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length embedInlFn (PFunDDS.par r u)
                2 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have h' : (l ++ [x]) ++ rest ∈ PFunDDS.dom r := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg some (PFunDDS.output_congr r (by simp) h' h)

/-- Backward realization: every completed embedding run against a
composition certifies the left component's domain and answers. -/
theorem driveOuter_embedInl_mem_imp (r : PFunDDS.DDS X Y)
    (u : PFunDDS.DDS X' Y') :
    ∀ (rest l : List X) (ys : List (Option (Y ⊕ Y'))) {fuel : ℕ}
      {res : List Y × List (X ⊕ X') × List (Option (Y ⊕ Y'))},
      l.length = ys.length →
      (∀ oy ∈ ys, (oy.bind Sum.getLeft?).isSome) →
      (l ∈ PFunDDS.dom r ∨ l = []) →
      res ∈ driveOuter embedInlFn (PFunDDS.par r u) fuel l (l.map Sum.inl)
        ys rest →
      res.2.1 = (l ++ rest).map Sum.inl ∧
        (rest ≠ [] → ∃ h : l ++ rest ∈ PFunDDS.dom r,
          res.1.getLast? = some (PFunDDS.output r (l ++ rest) h)) := by
  intro rest
  induction rest with
  | nil =>
      intro l ys fuel res _ _ _ hres
      simp only [driveOuter, Part.mem_some_iff] at hres
      subst hres
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons x rest ih =>
      intro l ys fuel res hlen hprop hl hres
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hres
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hres
      obtain ⟨hne₁, y, hy, rfl⟩ := drive_embedInl_round_elim
        (by simp [hlen]) hr₁
      have hgl : (l ++ [x]).getLast hne₁ = x :=
        List.getLast_append_singleton l
      rw [hgl] at hrr hy
      -- the composite's proper left answer certifies the left domain
      have hyr : PFunDDS.output (r⊥) (l ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
        have hlist : l.map (Sum.inl : X → X ⊕ X') ++ [Sum.inl x]
            = (l ++ [x]).map Sum.inl := by simp
        have hy₂ := (PFunDDS.output_congr ((PFunDDS.par r u)⊥) hlist.symm
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).trans hy
        rw [PFunDDS.output_fullyDefined_par_map_inl r u (by simp)] at hy₂
        rcases hout : PFunDDS.output (r⊥) (l ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y₀
        · rw [hout] at hy₂
          simp at hy₂
        · rw [hout] at hy₂
          simp only [Option.map_some] at hy₂
          exact congrArg some (Sum.inl.inj (Option.some.inj hy₂))
      obtain ⟨hnext, houtR⟩ :=
        PFunDDS.mem_of_output_fullyDefined_append_eq_some r l x hl hyr
      have hrr' : rr ∈ driveOuter embedInlFn (PFunDDS.par r u) fuel
          (l ++ [x]) ((l ++ [x]).map Sum.inl)
          (ys ++ [some (Sum.inl y)]) rest := by
        rw [show (l ++ [x]).map (Sum.inl : X → X ⊕ X')
            = l.map Sum.inl ++ [Sum.inl x] by simp]
        exact hrr
      obtain ⟨hthread, hcond⟩ := ih (l ++ [x]) (ys ++ [some (Sum.inl y)])
        (by simp [hlen])
        (by
          intro oy hmem
          rcases List.mem_append.mp hmem with hm | hm
          · exact hprop oy hm
          · rw [List.mem_singleton.mp hm]
            rfl)
        (Or.inl hnext) hrr'
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr'
          subst hrr'
          refine ⟨by simpa using hnext, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some ?_
          rw [PFunDDS.output_congr r (l₂ := l ++ [x]) (by simp) _ hnext,
            houtR]
      | cons r0 rs0 =>
          obtain ⟨h', hlast'⟩ := hcond (by simp [hrest])
          refine ⟨by simpa [List.append_assoc, hrest] using h', ?_⟩
          have hlenrr := driveOuter_length embedInlFn (PFunDDS.par r u)
            fuel hrr'
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              exact congrArg some
                (PFunDDS.output_congr r (by simp [hrest]) h' _)

/-- **Left recovery**: interrogating the left interface of a composition
recovers the left component exactly. -/
theorem apply_embedInlFn_par (r : PFunDDS.DDS X Y) (u : PFunDDS.DDS X' Y') :
    apply embedInlFn (PFunDDS.par r u) = r := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro v
  rw [show (apply embedInlFn (PFunDDS.par r u)).1
      = applyRaw embedInlFn (PFunDDS.par r u) from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨res, hres, hlast⟩ := hv
    have hne : l ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length embedInlFn (PFunDDS.par r u) fuel hres
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    have hres' : res ∈ driveOuter embedInlFn (PFunDDS.par r u) fuel []
        (([] : List X).map Sum.inl) [] l := by
      simpa using hres
    obtain ⟨-, hcond⟩ := driveOuter_embedInl_mem_imp r u l [] []
      rfl (by simp) (Or.inr rfl) hres'
    obtain ⟨h, hout⟩ := hcond hne
    rw [hlast] at hout
    have hv' := Option.some.inj hout
    have hdl : l ∈ PFunDDS.dom r := by simpa using h
    refine ⟨hdl, ?_⟩
    show PFunDDS.output r l _ = v
    rw [hv']
    exact PFunDDS.output_congr r (by simp) _ (by simpa using h)
  · rintro ⟨hd, rfl⟩
    have hdom : l ∈ PFunDDS.dom r := hd
    have hne : l ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem r hdom
    obtain ⟨vs, ys', hmem, hlast⟩ :=
      driveOuter_embedInl_of_dom r u l [] [] rfl (by simp)
        (Or.inl (by simpa using hdom)) (Or.inr rfl)
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, (([] : List X) ++ l).map Sum.inl, ys'),
      by simpa using hmem, ?_⟩
    rw [hlast (by simpa using hdom) hne]
    exact congrArg some (PFunDDS.output_congr r (by simp) _ hd)

/-- Forward realization, right side. -/
theorem driveOuter_embedInr_of_dom (r : PFunDDS.DDS X Y)
    (u : PFunDDS.DDS X' Y') :
    ∀ (rest l : List X') (ys : List (Option (Y ⊕ Y'))),
      l.length = ys.length →
      (∀ oy ∈ ys, (oy.bind Sum.getRight?).isSome) →
      (l ++ rest ∈ PFunDDS.dom u ∨ rest = []) →
      (l ∈ PFunDDS.dom u ∨ l = []) →
      ∃ vs ys',
        (vs, (l ++ rest).map Sum.inr, ys') ∈
          driveOuter embedInrFn (PFunDDS.par r u) 2 l (l.map Sum.inr) ys
            rest ∧
        ∀ (h : l ++ rest ∈ PFunDDS.dom u), rest ≠ [] →
          vs.getLast? = some (PFunDDS.output u (l ++ rest) h) := by
  intro rest
  induction rest with
  | nil =>
      intro l ys _ _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun _ hne => absurd rfl hne⟩
  | cons x rest ih =>
      intro l ys hlen hprop hdom hl
      have hdom' : l ++ x :: rest ∈ PFunDDS.dom u := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hnext : l ++ [x] ∈ PFunDDS.dom u :=
        PFunDDS.prefix_closed u ⟨rest, by simp⟩ (by simp) hdom'
      have hout : PFunDDS.output (u⊥) (l ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (PFunDDS.output u (l ++ [x]) hnext) :=
        PFunDDS.output_fullyDefined_append_of_mem u l x hl hnext
      have hgl : (l ++ [x]).getLast (by simp) = x :=
        List.getLast_append_singleton l
      have hy' : PFunDDS.output ((PFunDDS.par r u)⊥)
          (l.map Sum.inr ++ [Sum.inr ((l ++ [x]).getLast (by simp))])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (Sum.inr (PFunDDS.output u (l ++ [x]) hnext)) := by
        have hlist : l.map (Sum.inr : X' → X ⊕ X')
              ++ [Sum.inr ((l ++ [x]).getLast (by simp))]
            = (l ++ [x]).map Sum.inr := by
          rw [hgl]
          simp
        refine (PFunDDS.output_congr ((PFunDDS.par r u)⊥) hlist
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).trans ?_
        rw [PFunDDS.output_fullyDefined_par_map_inr r u (by simp), hout]
        rfl
      have hround := drive_embedInr_round_mem (r := r) (u := u)
        (us := l ++ [x]) (ys := ys) (xs := l.map Sum.inr)
        (by simp [hlen]) hprop (by simp) hy'
      rw [hgl] at hround
      obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (l ++ [x])
        (ys ++ [some (Sum.inr (PFunDDS.output u (l ++ [x]) hnext))])
        (by simp [hlen])
        (by
          intro oy hmem
          rcases List.mem_append.mp hmem with hm | hm
          · exact hprop oy hm
          · rw [List.mem_singleton.mp hm]
            rfl)
        (Or.inl (by simpa [List.append_assoc] using hdom'))
        (Or.inl hnext)
      refine ⟨PFunDDS.output u (l ++ [x]) hnext :: vs', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        refine ⟨(PFunDDS.output u (l ++ [x]) hnext,
          l.map Sum.inr ++ [Sum.inr x],
          ys ++ [some (Sum.inr (PFunDDS.output u (l ++ [x]) hnext))]),
          hround, (vs', ((l ++ [x]) ++ rest).map Sum.inr, ys''), ?_, ?_⟩
        · rw [show l.map (Sum.inr : X' → X ⊕ X') ++ [Sum.inr x]
              = (l ++ [x]).map Sum.inr by simp]
          exact hmem'
        · simp [List.append_assoc]
      · intro h _
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length embedInrFn (PFunDDS.par r u)
                2 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length embedInrFn (PFunDDS.par r u)
                2 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have h' : (l ++ [x]) ++ rest ∈ PFunDDS.dom u := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg some (PFunDDS.output_congr u (by simp) h' h)

/-- Backward realization, right side. -/
theorem driveOuter_embedInr_mem_imp (r : PFunDDS.DDS X Y)
    (u : PFunDDS.DDS X' Y') :
    ∀ (rest l : List X') (ys : List (Option (Y ⊕ Y'))) {fuel : ℕ}
      {res : List Y' × List (X ⊕ X') × List (Option (Y ⊕ Y'))},
      l.length = ys.length →
      (∀ oy ∈ ys, (oy.bind Sum.getRight?).isSome) →
      (l ∈ PFunDDS.dom u ∨ l = []) →
      res ∈ driveOuter embedInrFn (PFunDDS.par r u) fuel l (l.map Sum.inr)
        ys rest →
      res.2.1 = (l ++ rest).map Sum.inr ∧
        (rest ≠ [] → ∃ h : l ++ rest ∈ PFunDDS.dom u,
          res.1.getLast? = some (PFunDDS.output u (l ++ rest) h)) := by
  intro rest
  induction rest with
  | nil =>
      intro l ys fuel res _ _ _ hres
      simp only [driveOuter, Part.mem_some_iff] at hres
      subst hres
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons x rest ih =>
      intro l ys fuel res hlen hprop hl hres
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hres
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hres
      obtain ⟨hne₁, y', hy, rfl⟩ := drive_embedInr_round_elim
        (by simp [hlen]) hr₁
      have hgl : (l ++ [x]).getLast hne₁ = x :=
        List.getLast_append_singleton l
      rw [hgl] at hrr hy
      have hyu : PFunDDS.output (u⊥) (l ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some y' := by
        have hlist : l.map (Sum.inr : X' → X ⊕ X') ++ [Sum.inr x]
            = (l ++ [x]).map Sum.inr := by simp
        have hy₂ := (PFunDDS.output_congr ((PFunDDS.par r u)⊥) hlist.symm
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).trans hy
        rw [PFunDDS.output_fullyDefined_par_map_inr r u (by simp)] at hy₂
        rcases hout : PFunDDS.output (u⊥) (l ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y₀
        · rw [hout] at hy₂
          simp at hy₂
        · rw [hout] at hy₂
          simp only [Option.map_some] at hy₂
          exact congrArg some (Sum.inr.inj (Option.some.inj hy₂))
      obtain ⟨hnext, houtU⟩ :=
        PFunDDS.mem_of_output_fullyDefined_append_eq_some u l x hl hyu
      have hrr' : rr ∈ driveOuter embedInrFn (PFunDDS.par r u) fuel
          (l ++ [x]) ((l ++ [x]).map Sum.inr)
          (ys ++ [some (Sum.inr y')]) rest := by
        rw [show (l ++ [x]).map (Sum.inr : X' → X ⊕ X')
            = l.map Sum.inr ++ [Sum.inr x] by simp]
        exact hrr
      obtain ⟨hthread, hcond⟩ := ih (l ++ [x]) (ys ++ [some (Sum.inr y')])
        (by simp [hlen])
        (by
          intro oy hmem
          rcases List.mem_append.mp hmem with hm | hm
          · exact hprop oy hm
          · rw [List.mem_singleton.mp hm]
            rfl)
        (Or.inl hnext) hrr'
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr'
          subst hrr'
          refine ⟨by simpa using hnext, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some ?_
          rw [PFunDDS.output_congr u (l₂ := l ++ [x]) (by simp) _ hnext,
            houtU]
      | cons r0 rs0 =>
          obtain ⟨h', hlast'⟩ := hcond (by simp [hrest])
          refine ⟨by simpa [List.append_assoc, hrest] using h', ?_⟩
          have hlenrr := driveOuter_length embedInrFn (PFunDDS.par r u)
            fuel hrr'
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              exact congrArg some
                (PFunDDS.output_congr u (by simp [hrest]) h' _)

/-- **Right recovery**: interrogating the right interface of a composition
recovers the right component exactly. -/
theorem apply_embedInrFn_par (r : PFunDDS.DDS X Y) (u : PFunDDS.DDS X' Y') :
    apply embedInrFn (PFunDDS.par r u) = u := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro v
  rw [show (apply embedInrFn (PFunDDS.par r u)).1
      = applyRaw embedInrFn (PFunDDS.par r u) from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨res, hres, hlast⟩ := hv
    have hne : l ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length embedInrFn (PFunDDS.par r u) fuel hres
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    have hres' : res ∈ driveOuter embedInrFn (PFunDDS.par r u) fuel []
        (([] : List X').map Sum.inr) [] l := by
      simpa using hres
    obtain ⟨-, hcond⟩ := driveOuter_embedInr_mem_imp r u l [] []
      rfl (by simp) (Or.inr rfl) hres'
    obtain ⟨h, hout⟩ := hcond hne
    rw [hlast] at hout
    have hv' := Option.some.inj hout
    have hdl : l ∈ PFunDDS.dom u := by simpa using h
    refine ⟨hdl, ?_⟩
    show PFunDDS.output u l _ = v
    rw [hv']
    exact PFunDDS.output_congr u (by simp) _ (by simpa using h)
  · rintro ⟨hd, rfl⟩
    have hdom : l ∈ PFunDDS.dom u := hd
    have hne : l ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem u hdom
    obtain ⟨vs, ys', hmem, hlast⟩ :=
      driveOuter_embedInr_of_dom r u l [] [] rfl (by simp)
        (Or.inl (by simpa using hdom)) (Or.inr rfl)
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, (([] : List X') ++ l).map Sum.inr, ys'),
      by simpa using hmem, ?_⟩
    rw [hlast (by simpa using hdom) hne]
    exact congrArg some (PFunDDS.output_congr u (by simp) _ hd)

end EmbedComponent

end PFunConverter

/-! ## The strict fixed-component hops and `‖`-non-expansion -/

namespace StrictContext

open PFunConverter
open scoped Classical

variable {X Y X' Y' : Type*}

/-- Absorb a fixed deterministic right component into a strict test on the
composition. -/
noncomputable def absorbParRight (test : Test (X ⊕ X') (Y ⊕ Y')) (t : PFunDDS.DDS X' Y') :
    Test X Y :=
  absorb test ⟨parFixedRightFn t, isDDC_parFixedRightFn t⟩

/-- Absorb a fixed deterministic left component into a strict test on the
composition. -/
noncomputable def absorbParLeft (test : Test (X ⊕ X') (Y ⊕ Y')) (s : PFunDDS.DDS X Y) :
    Test X' Y' :=
  absorb test ⟨parFixedLeftFn s, isDDC_parFixedLeftFn s⟩

/-- Strict observation of a composition with a fixed right component is
strict observation through the absorbed test. -/
theorem observe_par_fixed_right (test : Test (X ⊕ X') (Y ⊕ Y'))
    (s : PFunDDS.DDS X Y) (t : PFunDDS.DDS X' Y') :
    observe test (PFunDDS.par s t) = observe (absorbParRight test t) s := by
  rw [← apply_parFixedRightFn t s]
  exact observe_absorb test ⟨parFixedRightFn t, isDDC_parFixedRightFn t⟩ s

/-- Strict observation of a composition with a fixed left component is
strict observation through the absorbed test. -/
theorem observe_par_fixed_left (test : Test (X ⊕ X') (Y ⊕ Y'))
    (s : PFunDDS.DDS X Y) (t : PFunDDS.DDS X' Y') :
    observe test (PFunDDS.par s t) = observe (absorbParLeft test s) t := by
  rw [← apply_parFixedLeftFn s t]
  exact observe_absorb test ⟨parFixedLeftFn s, isDDC_parFixedLeftFn s⟩ t

/-- Acceptance of a parallel composition, decomposed as the right
component's mixture of absorbed acceptances. -/
theorem acceptMass_par_right_mixture (test : Test (X ⊕ X') (Y ⊕ Y'))
    (S : PFunPDS X Y) (T : PFunPDS X' Y') :
    acceptMass test (S.par T) =
      T.sum fun t wt => wt * acceptMass (absorbParRight test t) S := by
  unfold acceptMass PFunPDS.par
  rw [Dist.mass_fTransform]
  rw [Dist.mass_congr (Dist.prod S T)
    (Q := fun p => true ∈ observe (absorbParRight test p.2) p.1)
    (fun p => by rw [observe_par_fixed_right])]
  rw [show (Dist.prod S T).mass
        (fun p => true ∈ observe (absorbParRight test p.2) p.1)
      = S.sum fun s ws => T.sum fun t wt =>
          if true ∈ observe (absorbParRight test t) s then ws * wt else 0
    from Dist.mass_prod_eq_double_sum S T _]
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun t _ => ?_
  unfold Dist.mass
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun s _ => ?_
  by_cases h : true ∈ observe (absorbParRight test t) s
  · rw [if_pos h, if_pos h, mul_comm]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Acceptance of a parallel composition, decomposed as the left
component's mixture of absorbed acceptances. -/
theorem acceptMass_par_left_mixture (test : Test (X ⊕ X') (Y ⊕ Y'))
    (S : PFunPDS X Y) (T : PFunPDS X' Y') :
    acceptMass test (S.par T) =
      S.sum fun s ws => ws * acceptMass (absorbParLeft test s) T := by
  unfold acceptMass PFunPDS.par
  rw [Dist.mass_fTransform]
  rw [Dist.mass_congr (Dist.prod S T)
    (Q := fun p => true ∈ observe (absorbParLeft test p.1) p.2)
    (fun p => by rw [observe_par_fixed_left])]
  rw [show (Dist.prod S T).mass
        (fun p => true ∈ observe (absorbParLeft test p.1) p.2)
      = S.sum fun s ws => T.sum fun t wt =>
          if true ∈ observe (absorbParLeft test s) t then ws * wt else 0
    from Dist.mass_prod_eq_double_sum S T _]
  refine Finsupp.sum_congr fun s _ => ?_
  unfold Dist.mass
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun t _ => ?_
  by_cases h : true ∈ observe (absorbParLeft test s) t
  · rw [if_pos h, if_pos h, mul_comm]
  · rw [if_neg h, if_neg h, mul_zero]

private theorem nnreal_edist_add_add_le (a b c d : NNReal) :
    edist (a + c) (b + d) ≤ edist a b + edist c d := by
  rw [edist_dist, edist_dist, edist_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
  apply ENNReal.ofReal_le_ofReal
  rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.dist_eq]
  push_cast
  calc |(a : ℝ) + c - (b + d)| = |((a : ℝ) - b) + ((c : ℝ) - d)| := by
        ring_nf
    _ ≤ |(a : ℝ) - b| + |(c : ℝ) - d| := abs_add_le _ _

private theorem nnreal_edist_mul_left (w a b : NNReal) :
    edist (w * a) (w * b) ≤ (w : ENNReal) * edist a b := by
  rw [edist_dist, edist_dist, NNReal.dist_eq, NNReal.dist_eq,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  rw [show (w : ℝ) * a - w * b = w * ((a : ℝ) - b) by ring, abs_mul,
    abs_of_nonneg (by positivity)]

private theorem edist_sum_le_sum_edist {ι : Type*} (I : Finset ι)
    (f g : ι → ℝ) :
    edist (∑ i ∈ I, f i) (∑ i ∈ I, g i) ≤ ∑ i ∈ I, edist (f i) (g i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      exact (edist_add_add_le _ _ _ _).trans
        (add_le_add le_rfl ih)

private theorem edist_mul_left_ofReal (w a b : ℝ) (hw : 0 ≤ w) :
    edist (w * a) (w * b) = ENNReal.ofReal w * edist a b := by
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← mul_sub,
    abs_mul, abs_of_nonneg hw, ENNReal.ofReal_mul hw]

/-- Mixtures with common non-negative weights separate: the distance of two
`W`-mixtures is at most the mixture of the distances. -/
private theorem edist_weighted_sum_le {ι : Type*} {W : Dist ι}
    (hW : W.NonNeg) (a b : ι → ℝ) :
    edist (W.sum fun i w => w * a i) (W.sum fun i w => w * b i) ≤
      ∑ i ∈ W.support, ENNReal.ofReal (W i) * edist (a i) (b i) := by
  rw [Finsupp.sum, Finsupp.sum]
  exact (edist_sum_le_sum_edist W.support _ _).trans
    (Finset.sum_le_sum fun i _ =>
      le_of_eq (edist_mul_left_ofReal _ _ _ (hW i)))

/-- **The right-fixed hop of Maurer11 eq. (3), strict metric**: replacing
the left component cannot cost more than its own strict distance when the
fixed right component is normalized. -/
theorem maxEDist_par_fixed_right_le (S S' : PFunPDS X Y)
    (T : PFunPDS X' Y') (hT : T.isProbDist) :
    maxEDist (S.par T) (S'.par T) ≤ maxEDist S S' := by
  refine iSup_le fun test => ?_
  rw [acceptMass_par_right_mixture, acceptMass_par_right_mixture]
  refine (edist_weighted_sum_le hT.nonNeg _ _).trans ?_
  calc ∑ t ∈ T.support, ENNReal.ofReal (T t) *
        edist (acceptMass (absorbParRight test t) S)
          (acceptMass (absorbParRight test t) S')
      ≤ ∑ t ∈ T.support, ENNReal.ofReal (T t) * maxEDist S S' := by
        gcongr with t ht
        exact le_iSup (fun current : Test X Y =>
          edist (acceptMass current S) (acceptMass current S'))
          (absorbParRight test t)
    _ = (∑ t ∈ T.support, ENNReal.ofReal (T t)) * maxEDist S S' := by
        rw [Finset.sum_mul]
    _ = ENNReal.ofReal T.weight * maxEDist S S' := by
        rw [Dist.weight_eq_finsupp_sum, Finsupp.sum,
          ENNReal.ofReal_sum_of_nonneg fun t _ => hT.nonNeg t]
    _ = maxEDist S S' := by
        rw [hT.2]
        simp

/-- **The left-fixed hop of Maurer11 eq. (3), strict metric**. -/
theorem maxEDist_par_fixed_left_le (S : PFunPDS X Y) (hS : S.isProbDist)
    (T T' : PFunPDS X' Y') :
    maxEDist (S.par T) (S.par T') ≤ maxEDist T T' := by
  refine iSup_le fun test => ?_
  rw [acceptMass_par_left_mixture, acceptMass_par_left_mixture]
  refine (edist_weighted_sum_le hS.nonNeg _ _).trans ?_
  calc ∑ s ∈ S.support, ENNReal.ofReal (S s) *
        edist (acceptMass (absorbParLeft test s) T)
          (acceptMass (absorbParLeft test s) T')
      ≤ ∑ s ∈ S.support, ENNReal.ofReal (S s) * maxEDist T T' := by
        gcongr with s hs
        exact le_iSup (fun current : Test X' Y' =>
          edist (acceptMass current T) (acceptMass current T'))
          (absorbParLeft test s)
    _ = (∑ s ∈ S.support, ENNReal.ofReal (S s)) * maxEDist T T' := by
        rw [Finset.sum_mul]
    _ = ENNReal.ofReal S.weight * maxEDist T T' := by
        rw [Dist.weight_eq_finsupp_sum, Finsupp.sum,
          ENNReal.ofReal_sum_of_nonneg fun s _ => hS.nonNeg s]
    _ = maxEDist T T' := by
        rw [hS.2]
        simp

/-- **Maurer11 §4.4 Definition 3 / eq. (3) for the strict contextual
metric**: parallel composition is `‖`-non-expanding.  This is a new fact,
not a transfer of `maxAdvantage_par_le`: the strict metric is only bounded
by `Δ`, never equal to it. -/
theorem maxEDist_par_le (S S' : PFunPDS X Y) (T T' : PFunPDS X' Y')
    (hS' : S'.isProbDist) (hT : T.isProbDist) :
    maxEDist (S.par T) (S'.par T') ≤ maxEDist S S' + maxEDist T T' :=
  (max_edist_triangle (S.par T) (S'.par T) (S'.par T')).trans
    (add_le_add (maxEDist_par_fixed_right_le S S' T hT)
      (maxEDist_par_fixed_left_le S' hS' T T'))

/-- Parallel composition preserves **strict** contextual equivalence — the
zero-radius case of `maxEDist_par_le`, and the congruence that descends
`‖` to the strict behavioral quotient.  (The CR18 transcript-level
`equivalent_par` does not imply this: strict equivalence is coarser.) -/
theorem equivalent_par {S S' : PFunPDS X Y} {T T' : PFunPDS X' Y'}
    (hS' : S'.isProbDist) (hT : T.isProbDist)
    (hS : Equivalent S S') (hT' : Equivalent T T') :
    Equivalent (S.par T) (S'.par T') := by
  rw [← max_edist_eq_zero_iff] at hS hT' ⊢
  refine le_antisymm ?_ (zero_le _)
  calc maxEDist (S.par T) (S'.par T')
      ≤ maxEDist S S' + maxEDist T T' := maxEDist_par_le S S' T T' hS' hT
    _ = 0 := by rw [hS, hT', add_zero]

namespace System

/-- Parallel composition of strict behaviors: `PFunPDS.Prob.parallel`
descends through the strict quotient by `equivalent_par`. -/
noncomputable def parallel (left : System X Y) (right : System X' Y') :
    System (X ⊕ X') (Y ⊕ Y') :=
  Quotient.liftOn₂ left right
    (fun left right => ofProb (PFunPDS.Prob.parallel left right))
    (fun _leftA rightA leftB _rightB hleft hright =>
      Quotient.sound
        (equivalent_par leftB.property rightA.property hleft hright))

@[simp]
theorem parallel_ofProb (left : PFunPDS.Prob X Y)
    (right : PFunPDS.Prob X' Y') :
    parallel (ofProb left) (ofProb right) =
      ofProb (PFunPDS.Prob.parallel left right) :=
  rfl

/-- `‖`-non-expansion on strict behavior (Maurer11 Definition 3). -/
theorem edist_parallel_le (left left' : System X Y)
    (right right' : System X' Y') :
    edist (parallel left right) (parallel left' right') ≤
      edist left left' + edist right right' := by
  induction left using Quotient.inductionOn with
  | _ leftR =>
      induction left' using Quotient.inductionOn with
      | _ leftR' =>
          induction right using Quotient.inductionOn with
          | _ rightR =>
              induction right' using Quotient.inductionOn with
              | _ rightR' =>
                  exact maxEDist_par_le leftR.val leftR'.val rightR.val
                    rightR'.val leftR'.property rightR.property

end System

/-! ### Cancellation: the parallel decomposition of strict behavior is
unique -/

/-- Interrogating the left interface marginalizes the composition to its
left component, scaled by the right weight. -/
theorem applyLaw_embedInl_par (S : PFunPDS X Y) (T : PFunPDS X' Y') :
    applyLaw embedInlFn (S.par T) = T.weight • S := by
  unfold applyLaw PFunPDS.par
  rw [Dist.fTransform_comp]
  rw [show (fun s => PFunConverter.apply embedInlFn s) ∘
        (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
          PFunDDS.par p.1 p.2)
      = fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => id p.1 from
    funext fun p => apply_embedInlFn_par p.1 p.2]
  rw [fTransform_fst_prod_smul id S T, Dist.fTransform_id]

/-- Interrogating the right interface marginalizes the composition to its
right component, scaled by the left weight. -/
theorem applyLaw_embedInr_par (S : PFunPDS X Y) (T : PFunPDS X' Y') :
    applyLaw embedInrFn (S.par T) = S.weight • T := by
  unfold applyLaw PFunPDS.par
  rw [Dist.fTransform_comp]
  rw [show (fun s => PFunConverter.apply embedInrFn s) ∘
        (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
          PFunDDS.par p.1 p.2)
      = fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => id p.2 from
    funext fun p => apply_embedInrFn_par p.1 p.2]
  rw [fTransform_snd_prod_smul id S T, Dist.fTransform_id]

/-- **Left cancellation** for strict equivalence of compositions of
probability systems: a strict test on one component embeds into the
composition. -/
theorem equivalent_left_of_par_equivalent {S S' : PFunPDS X Y}
    {T T' : PFunPDS X' Y'} (hT : T.isProbDist) (hT' : T'.isProbDist)
    (h : Equivalent (S.par T) (S'.par T')) : Equivalent S S' := by
  intro E
  have key := h (absorb E ⟨embedInlFn, isDDC_embedInlFn⟩)
  rw [← accept_mass_apply E ⟨embedInlFn, isDDC_embedInlFn⟩ (S.par T),
    ← accept_mass_apply E ⟨embedInlFn, isDDC_embedInlFn⟩ (S'.par T')] at key
  rw [show (⟨embedInlFn, isDDC_embedInlFn⟩ :
      {alpha : ProtocolFn X Y (X ⊕ X') (Y ⊕ Y') //
        PFunConverter.IsDDC alpha}).val = embedInlFn from rfl] at key
  rw [applyLaw_embedInl_par, applyLaw_embedInl_par, hT.2, hT'.2,
    one_smul, one_smul] at key
  exact key

/-- **Right cancellation** for strict equivalence of compositions of
probability systems. -/
theorem equivalent_right_of_par_equivalent {S S' : PFunPDS X Y}
    {T T' : PFunPDS X' Y'} (hS : S.isProbDist) (hS' : S'.isProbDist)
    (h : Equivalent (S.par T) (S'.par T')) : Equivalent T T' := by
  intro E
  have key := h (absorb E ⟨embedInrFn, isDDC_embedInrFn⟩)
  rw [← accept_mass_apply E ⟨embedInrFn, isDDC_embedInrFn⟩ (S.par T),
    ← accept_mass_apply E ⟨embedInrFn, isDDC_embedInrFn⟩ (S'.par T')] at key
  rw [show (⟨embedInrFn, isDDC_embedInrFn⟩ :
      {alpha : ProtocolFn X' Y' (X ⊕ X') (Y ⊕ Y') //
        PFunConverter.IsDDC alpha}).val = embedInrFn from rfl] at key
  rw [applyLaw_embedInr_par, applyLaw_embedInr_par, hS.2, hS'.2,
    one_smul, one_smul] at key
  exact key

namespace System

universe u v

/-- Interrogating the left interface of a parallel strict behavior
recovers the left component. -/
theorem apply_embedInl_parallel (left : System X Y) (right : System X' Y') :
    apply ⟨embedInlFn, isDDC_embedInlFn⟩ (parallel left right) = left := by
  induction left using Quotient.inductionOn with
  | _ leftR =>
      induction right using Quotient.inductionOn with
      | _ rightR =>
          show ofProb ⟨applyLaw embedInlFn (leftR.val.par rightR.val), _⟩
            = ofProb leftR
          apply congrArg
          apply Subtype.ext
          show applyLaw embedInlFn (leftR.val.par rightR.val) = leftR.val
          rw [applyLaw_embedInl_par, rightR.property.2, one_smul]

/-- Interrogating the right interface of a parallel strict behavior
recovers the right component. -/
theorem apply_embedInr_parallel (left : System X Y) (right : System X' Y') :
    apply ⟨embedInrFn, isDDC_embedInrFn⟩ (parallel left right) = right := by
  induction left using Quotient.inductionOn with
  | _ leftR =>
      induction right using Quotient.inductionOn with
      | _ rightR =>
          show ofProb ⟨applyLaw embedInrFn (leftR.val.par rightR.val), _⟩
            = ofProb rightR
          apply congrArg
          apply Subtype.ext
          show applyLaw embedInrFn (leftR.val.par rightR.val) = rightR.val
          rw [applyLaw_embedInr_par, leftR.property.2, one_smul]

/-! Transport of a strict behavior along an alphabet *equality* used to live
here (`castEq`, with its isometry and injectivity).  It is deleted, not
retained: `HasSumCode` now states its alphabet laws as equivalences, so the
heterogeneous resource carrier transports along `System.relabel`
(`RandomSystems.StrictRelabel`) instead, and that was `castEq`'s only
consumer.  An equality-only transport is also strictly weaker — it cannot
carry any signature whose alphabets distribute up to isomorphism only, which
is what excluded the event-augmented alphabet from `∥`. -/

/-- **The parallel decomposition of a strict behavior is unique** — the
AC modeling invariant for products: behavior, not presentation, is the
resource, componentwise. -/
theorem parallel_inj {left left' : System X Y} {right right' : System X' Y'}
    (h : parallel left right = parallel left' right') :
    left = left' ∧ right = right' := by
  induction left using Quotient.inductionOn with
  | _ leftR =>
      induction left' using Quotient.inductionOn with
      | _ leftR' =>
          induction right using Quotient.inductionOn with
          | _ rightR =>
              induction right' using Quotient.inductionOn with
              | _ rightR' =>
                  have hpar : Equivalent
                      (leftR.val.par rightR.val)
                      (leftR'.val.par rightR'.val) := Quotient.exact h
                  exact ⟨Quotient.sound
                      (equivalent_left_of_par_equivalent
                        rightR.property rightR'.property hpar),
                    Quotient.sound
                      (equivalent_right_of_par_equivalent
                        leftR.property leftR'.property hpar)⟩

end System

end StrictContext

end RandomSystems.CR18
