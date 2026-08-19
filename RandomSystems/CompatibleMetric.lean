/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ComposeRealization
import RandomSystems.EmulateRealization
import RandomSystems.Distinguishing
import RandomSystems.RandomSystem
import RandomSystems.AbsorbDPI
import RandomSystems.SemanticRegistry

/-!
# The compatible pseudo-metric obligations (Maurer11 §4.4, Definition 2)

Maurer11 Definition 2: a pseudo-metric `d` on `Φ` is **compatible** with
the cryptographic algebra `⟨Φ, Σ⟩` if

* eq. (3): `d(R‖R′, S‖S′) ≤ d(R, S) + d(R′, S′)`, and
* eq. (4): `d(αⁱR, αⁱS) ≤ d(R, S)`

(MauRen16 Definition 2 calls this **non-expanding**).  This file poses
these obligations for the distinguisher metric `Δ` of random systems,
together with the operations the statements need, none of which existed
at the binary/probabilistic level:

* CR18 Definition 3.4 (binary form, fn. 20's merged interface as the
  tagged sum): the parallel composition `s‖t` of deterministic systems,
  and its probabilistic lift through `Dist.prod` ("the parallel
  composition of independent systems");
* MauRen11 fn. 22: the neutral converter `1` as an actual system
  (`idFn` — the always-forward protocol function), with Def 14 (ii)
  posed as `apply_idFn`;
* MauRen11 §6.2: the parallel composition `α‖β` of converters
  (`par`), routing by tag, with its defining law
  `(α‖β)(R‖S) = αR ‖ βS` proved as
  `apply_parallel_eq_parallel_apply` (fn. 23: off
  `‖`-shaped histories the values are junk in the sense of the
  trace-tree discipline);
* converter application lifted to probabilistic systems
  (`PFunPDS.apply`, the pushforward — "applying a converter simply
  creates a random system");
* the elementary facts of the distinguisher metric the instantiation
  consumes: symmetry and, for probability systems, the bound `Δ ≤ 1`.

-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

-- `PFunDDS.par` (CR18 Definition 3.4, binary form) now lives upstream in
-- `EmulateRealization.lean`, with the resource-emulation kept-scan core.

namespace PFunConverter

variable {X Y X' Y' U V U' V' : Type*}

/-- The neutral converter `1` (MauRen11 Def 14 (ii); fn. 22: "it may be
reasonable to assume that `1` is an actual system, for example by
forwarding all messages"): the protocol function that forwards each
outer query inside and relays each answer back outside. -/
def idFn : ProtocolFn X Y X Y := fun p =>
  if h : p.1.length = p.2.length + 1 then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2) with
    | some y => Part.some (Sum.inr y)
    | none => Part.none
  else Part.none

/-- The neutral converter is the identity instance of the simple converter
(MauRen11 fn. 22 read through DESIGN §10.5's worked example). -/
theorem idFn_eq_simpleFn :
    (idFn : ProtocolFn X Y X Y) = simpleFn id id := rfl

/-- CR18 Def 3.8, input-alphabet clause, for the neutral converter: `idFn`
relays only proper answers — it is silent at every reachable `⊥`-pair. -/
theorem answersInY_idFn : AnswersInY (idFn : ProtocolFn X Y X Y) := by
  rw [idFn_eq_simpleFn]
  intro p hre hnone hdom
  rw [reach_simpleFn_iff] at hre
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp hdom
  rcases hre with ⟨hlen, hsome⟩ | ⟨hlen, hpos, hsome⟩
  · have := hsome none hnone
    simp at this
  · cases m with
    | inl x =>
        have h1 := simpleFn_inl_inv hm
        omega
    | inr v =>
        obtain ⟨h1, h0, y, hy, -⟩ := simpleFn_inr_inv hm
        rw [← List.dropLast_append_getLast
          (List.ne_nil_of_length_pos h0)] at hnone
        rcases List.mem_append.mp hnone with hmem | hmem
        · have := hsome none hmem
          simp at this
        · rw [List.mem_singleton] at hmem
          have hcontra := hmem.trans hy
          simp at hcontra

/-- CR18 Def 3.8, finite-bound clause, for the neutral converter: `idFn`
has inner arity one — no reachable pair opens two consecutive queries. -/
theorem answersWithin_idFn : AnswersWithin (idFn : ProtocolFn X Y X Y) 2 := by
  intro p _ ext hlen hchain
  obtain ⟨x₀, h₀⟩ := hchain 0 (by omega)
  obtain ⟨x₁, h₁⟩ := hchain 1 (by omega)
  rw [idFn_eq_simpleFn] at h₀ h₁
  have e₀ := simpleFn_inl_inv h₀
  have e₁ := simpleFn_inl_inv h₁
  simp only [List.length_append, List.length_take] at e₀ e₁
  omega

/-- **The neutral converter is a CR18 Def 3.8 converter** (MauRen11
fn. 22): both clauses hold, with query-streak bound `2`. -/
theorem isDDC_idFn : IsDDC (idFn : ProtocolFn X Y X Y) :=
  ⟨answersInY_idFn, 2, answersWithin_idFn⟩

/-- The neutral converter closes every round it opens (CR18 §6.2.3's
condition, vacuously — it has no budget to breach). -/
theorem stopsReplying_idFn : StopsReplying (idFn : ProtocolFn X Y X Y) := by
  rw [idFn_eq_simpleFn]
  exact stopsReplying_simpleFn id id

/-- **MauRen11 Def 16 membership of the neutral converter** (fn. 22):
`1` is emulable, so eq. (4) non-expansion holds for it
(`maxAdvantage_apply_le`). -/
theorem emulable_idFn : Emulable (idFn : ProtocolFn X Y X Y) := by
  rw [idFn_eq_simpleFn]
  exact emulable_simpleFn id id

/-- `drive` consults the converter only at the fixed outer history:
converters agreeing there drive identically. -/
theorem drive_congr {α α' : ProtocolFn U V X Y} {S : PFunDDS.DDS X Y}
    {us : List U} (h : ∀ ys, α (us, ys) = α' (us, ys)) :
    ∀ (fuel : ℕ) (xs : List X) (ys : List (Option Y)),
      drive α S fuel us xs ys = drive α' S fuel us xs ys := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; rfl
  | succ n ih =>
      intro xs ys
      simp only [drive, h ys]
      refine congrArg (Part.bind _) (funext fun m => ?_)
      cases m with
      | inl x => exact ih (xs ++ [x]) _
      | inr v => rfl

/-- `driveOuter` consults the converter only along prefixes of the
outer history. -/
theorem driveOuter_congr {α α' : ProtocolFn U V X Y} {S : PFunDDS.DDS X Y}
    {fuel : ℕ} :
    ∀ (rest usPre : List U) (xs : List X) (ys : List (Option Y)),
      (∀ us' (ys' : List (Option Y)), us' <+: usPre ++ rest →
        α (us', ys') = α' (us', ys')) →
      driveOuter α S fuel usPre xs ys rest
        = driveOuter α' S fuel usPre xs ys rest := by
  intro rest
  induction rest with
  | nil => intro usPre xs ys _; rfl
  | cons u rest ih =>
      intro usPre xs ys h
      simp only [driveOuter]
      rw [drive_congr (fun ys' => h (usPre ++ [u]) ys'
        ⟨rest, by simp⟩) fuel xs ys]
      refine congrArg (Part.bind _) (funext fun r => ?_)
      rw [ih (usPre ++ [u]) r.2.1 r.2.2 (fun us' ys' hpre =>
        h us' ys' (by simpa [List.append_assoc] using hpre))]

/-- Under the outer length, the neutral converter **is** the `[q]`
filter: the budget never binds. -/
theorem idFn_eq_queryLimitFn_of_le {q : ℕ} {us : List X}
    {ys : List (Option Y)}
    (h : us.length ≤ q) : idFn (us, ys) = queryLimitFn q (us, ys) := by
  simp only [idFn, queryLimitFn]
  by_cases h1 : us.length = ys.length + 1
  · rw [dif_pos h1,
      dif_pos (show us.length = ys.length + 1 ∧ us.length ≤ q from ⟨h1, h⟩)]
  · by_cases h2 : us.length = ys.length ∧ 0 < ys.length
    · rw [dif_neg h1, dif_pos h2,
        dif_neg (show ¬(us.length = ys.length + 1 ∧ us.length ≤ q) from
          fun hc => h1 hc.1),
        dif_pos (show us.length = ys.length ∧ 0 < ys.length ∧ us.length ≤ q
          from ⟨h2.1, h2.2, h⟩)]
      rfl
    · rw [dif_neg h1, dif_neg h2,
        dif_neg (show ¬(us.length = ys.length + 1 ∧ us.length ≤ q) from
          fun hc => h1 hc.1),
        dif_neg (show ¬(us.length = ys.length ∧ 0 < ys.length ∧
          us.length ≤ q) from fun hc => h2 ⟨hc.1, hc.2.1⟩)]

/-- MauRen11 Def 14 (ii): `1ⁱR = R` — the neutral converter attaches
trivially.  Pointwise at an outer history `us` the budget of
`[us.length]` never binds, so `1` drives exactly as that filter — and a
filter at full slack is the identity. -/
theorem apply_idFn (S : PFunDDS.DDS X Y) :
    apply idFn S = S := by
  apply Subtype.ext
  funext us
  have hdo : ∀ fuel : ℕ,
      driveOuter idFn S fuel [] [] [] us
        = driveOuter (queryLimitFn us.length) S fuel [] [] [] us :=
    fun fuel => driveOuter_congr us [] [] []
      (fun us' ys' hpre => idFn_eq_queryLimitFn_of_le
        (by simpa using hpre.length_le))
  apply Part.ext
  intro v
  rw [show (apply idFn S).1 = applyRaw idFn S from rfl]
  have hmem : v ∈ applyRaw idFn S us
      ↔ v ∈ applyRaw (queryLimitFn us.length) S us := by
    rw [mem_applyRaw, mem_applyRaw]
    refine exists_congr fun fuel => ?_
    rw [mem_applyRawAt_iff, mem_applyRawAt_iff, hdo fuel]
  rw [hmem,
    show applyRaw (queryLimitFn us.length) S
      = (apply (queryLimitFn us.length) S).1 from rfl,
    apply_queryLimitFn us.length S]
  show (∃ h : (S.1 us).Dom ∧ us.length ≤ us.length, (S.1 us).get h.1 = v)
      ↔ v ∈ S.1 us
  constructor
  · rintro ⟨⟨hd, -⟩, rfl⟩
    exact Part.get_mem hd
  · intro hv
    exact ⟨⟨Part.dom_iff_mem.mpr ⟨v, hv⟩, le_rfl⟩, Part.get_eq_of_mem hv _⟩

-- `PFunConverter.par` (MauRen11 §6.2) now lives upstream in
-- `EmulateRealization.lean`, with the attribution-fold machinery.

/-- Reinsert the left and right output streams according to the tagged
outer-query history.  The fallback clauses are unreachable when the stream
lengths come from `driveOuter`; keeping the function total avoids adding
operational state to the mathematical construction. -/
private def parallel_outputs :
    List (U ⊕ U') → List V → List V' → List (V ⊕ V')
  | [], _, _ => []
  | Sum.inl _ :: ws, v :: vs, vs' =>
      Sum.inl v :: parallel_outputs ws vs vs'
  | Sum.inr _ :: ws, vs, v' :: vs' =>
      Sum.inr v' :: parallel_outputs ws vs vs'
  | _ :: _, _, _ => []

/-- A completed component round leaves a reachable converter pair whose
last move is the returned outer answer, and whose attributed inner answers
are all proper. -/
private def closed_outer_anchor (α : ProtocolFn U V X Y)
    (us : List U) (ys : List (Option Y)) : Prop :=
  ∃ v, Reach α (us, ys) ∧ Sum.inr v ∈ α (us, ys) ∧
    ∀ oy ∈ ys, oy.isSome

/-- Before a component has received its first tagged outer query its anchor
is empty; afterwards every successful round leaves a `closed_outer_anchor`. -/
private def ready_outer_anchor (α : ProtocolFn U V X Y)
    (us : List U) (ys : List (Option Y)) : Prop :=
  (us = [] ∧ ys = []) ∨ closed_outer_anchor α us ys

/-- An undefined converter pair cannot produce a successful round. -/
private theorem drive_has_no_result_when_converter_undefined
    {α : ProtocolFn U V X Y} {s : PFunDDS.DDS X Y}
    {us : List U} {ys : List (Option Y)} (h : ¬ (α (us, ys)).Dom)
    (fuel : ℕ) (xs : List X) (r : V × List X × List (Option Y)) :
    r ∉ drive α s fuel us xs ys := by
  intro hr
  cases fuel with
  | zero => simpa [drive] using hr
  | succ fuel =>
      simp only [drive, Part.mem_bind_iff] at hr
      obtain ⟨m, hm, -⟩ := hr
      exact h (Part.dom_iff_mem.mpr ⟨m, hm⟩)

/-- Under the CR18 input-alphabet condition, a successful round ends at a
closed anchor: an unattributed `none` cannot be crossed. -/
private theorem drive_ends_at_closed_outer_anchor
    {α : ProtocolFn U V X Y} {s : PFunDDS.DDS X Y}
    (hα : AnswersInY α) :
    ∀ {fuel : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
      {r : V × List X × List (Option Y)},
      Reach α (us, ys) → (∀ oy ∈ ys, oy.isSome) →
      r ∈ drive α s fuel us xs ys →
      closed_outer_anchor α us r.2.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro us xs ys r _ _ hr
      simpa [drive] using hr
  | succ fuel ih =>
      intro us xs ys r hre hproper hr
      rcases drive_succ_elim hr with ⟨x, hx, hnext⟩ | ⟨v, hv, rfl⟩
      · rcases hout : PFunDDS.output (PFunDDS.fullyDefined s) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · exfalso
          rw [hout] at hnext
          exact drive_has_no_result_when_converter_undefined
            (hα _ (Reach.answer hre hx none) (by simp)) fuel _ _ hnext
        · rw [hout] at hnext
          refine ih (Reach.answer hre hx (some y)) ?_ hnext
          intro oy hoy
          rcases List.mem_append.mp hoy with hoy | hoy
          · exact hproper oy hoy
          · rw [List.mem_singleton.mp hoy]
            rfl
      · exact ⟨v, hre, hv, hproper⟩

/-- Opening the next component round turns either the initial empty anchor or
a previously closed anchor into a reachable pair. -/
private theorem ready_outer_anchor_opens_next
    {α : ProtocolFn U V X Y} {us : List U} {ys : List (Option Y)}
    (h : ready_outer_anchor α us ys) (u : U) :
    Reach α (us ++ [u], ys) ∧ ∀ oy ∈ ys, oy.isSome := by
  rcases h with ⟨rfl, rfl⟩ | ⟨v, hre, hv, hproper⟩
  · exact ⟨Reach.first u, by simp⟩
  · exact ⟨Reach.next hre hv u, hproper⟩

/-- Every successful run of the tagged parallel converter projects to one
successful run of each component.  The terminal histories are related by the
CR18 kept-query scan and by the answer-attribution folds; the visible outputs
are exactly reinterleaved by their outer tags. -/
private theorem parallel_outer_run_projects
    {α : ProtocolFn U V X Y} {β : ProtocolFn U' V' X' Y'}
    {s : PFunDDS.DDS X Y} {t : PFunDDS.DDS X' Y'} :
    ∀ {rest : List (U ⊕ U')} {ws_pre : List (U ⊕ U')}
      {jxs : List (X ⊕ X')} {jys : List (Option (Y ⊕ Y'))}
      {lxs : List X} {lys : List (Option Y)}
      {rxs : List X'} {rys : List (Option Y')}
      {fuel : ℕ}
      {result : List (V ⊕ V') × List (X ⊕ X') ×
        List (Option (Y ⊕ Y'))},
      PFunDDS.keptPrefix s (jxs.filterMap Sum.getLeft?) =
          PFunDDS.keptPrefix s lxs →
      attribute_left_answers jys = lys →
      PFunDDS.keptPrefix t (jxs.filterMap Sum.getRight?) =
          PFunDDS.keptPrefix t rxs →
      attribute_right_answers jys = rys →
      result ∈ driveOuter (par α β) (PFunDDS.par s t)
        fuel ws_pre jxs jys rest →
      ∃ (left_fuel : ℕ)
        (left_result : List V × List X × List (Option Y))
        (right_fuel : ℕ)
        (right_result : List V' × List X' × List (Option Y')),
        left_result ∈ driveOuter α s left_fuel
          (ws_pre.filterMap Sum.getLeft?) lxs lys
          (rest.filterMap Sum.getLeft?) ∧
        right_result ∈ driveOuter β t right_fuel
          (ws_pre.filterMap Sum.getRight?) rxs rys
          (rest.filterMap Sum.getRight?) ∧
        result.1 = parallel_outputs rest left_result.1 right_result.1 ∧
        PFunDDS.keptPrefix s (result.2.1.filterMap Sum.getLeft?) =
          PFunDDS.keptPrefix s left_result.2.1 ∧
        attribute_left_answers result.2.2 = left_result.2.2 ∧
        PFunDDS.keptPrefix t (result.2.1.filterMap Sum.getRight?) =
          PFunDDS.keptPrefix t right_result.2.1 ∧
        attribute_right_answers result.2.2 = right_result.2.2 := by
  intro rest
  induction rest with
  | nil =>
      intro ws_pre jxs jys lxs lys rxs rys fuel result
        hleft_x hleft_y hright_x hright_y hresult
      simp only [driveOuter, Part.mem_some_iff] at hresult
      subst result
      refine ⟨0, ([], lxs, lys), 0, ([], rxs, rys), ?_, ?_, rfl,
        hleft_x, hleft_y, hright_x, hright_y⟩
      · simp [driveOuter]
      · simp [driveOuter]
  | cons w rest ih =>
      intro ws_pre jxs jys lxs lys rxs rys fuel result
        hleft_x hleft_y hright_x hright_y hresult
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hresult
      obtain ⟨round_result, hround, tail_result, htail, rfl⟩ := hresult
      rcases round_result with ⟨joint_value, joint_xs, joint_ys⟩
      cases w with
      | inl u =>
          obtain ⟨v, round_fuel, left_xs, left_ys, hvalue, hleft_round,
              hleft_x', hleft_y', hright_x_same, hright_y_same⟩ :=
            drive_parallel_left_projects (s := s) (t := t)
              (show (ws_pre ++ [Sum.inl u]).getLast? = some (Sum.inl u) by simp)
              hleft_x hleft_y hround
          change joint_value = Sum.inl v at hvalue
          subst joint_value
          have hright_x' :
              PFunDDS.keptPrefix t (joint_xs.filterMap Sum.getRight?) =
                PFunDDS.keptPrefix t rxs := by
            rw [hright_x_same]
            exact hright_x
          have hright_y' : attribute_right_answers joint_ys = rys := by
            rw [hright_y_same]
            exact hright_y
          obtain ⟨tail_left_fuel, tail_left, tail_right_fuel, tail_right,
              htail_left, htail_right, htail_outputs, htail_left_x,
              htail_left_y, htail_right_x, htail_right_y⟩ :=
            ih (ws_pre := ws_pre ++ [Sum.inl u])
              hleft_x' hleft_y' hright_x' hright_y' htail
          let left_fuel := max round_fuel tail_left_fuel
          have hleft_round' := drive_mono_le α s
            (Nat.le_max_left round_fuel tail_left_fuel) hleft_round
          have htail_left' := driveOuter_mono_le α s
            (Nat.le_max_right round_fuel tail_left_fuel) htail_left
          have hleft_run :
              (v :: tail_left.1, tail_left.2) ∈
                driveOuter α s left_fuel
                  (ws_pre.filterMap Sum.getLeft?) lxs lys
                  ((Sum.inl u :: rest).filterMap Sum.getLeft?) := by
            simp only [List.filterMap, Sum.getLeft?, driveOuter,
              Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(v, left_xs, left_ys), ?_, tail_left, ?_, rfl⟩
            · simpa [left_fuel, List.filterMap_append] using hleft_round'
            · simpa [left_fuel, List.filterMap_append] using htail_left'
          have hright_run :
              tail_right ∈ driveOuter β t tail_right_fuel
                (ws_pre.filterMap Sum.getRight?) rxs rys
                ((Sum.inl u :: rest).filterMap Sum.getRight?) := by
            simpa [List.filterMap_append] using htail_right
          refine ⟨left_fuel, (v :: tail_left.1, tail_left.2),
            tail_right_fuel, tail_right, hleft_run, hright_run, ?_,
            htail_left_x, htail_left_y, htail_right_x, htail_right_y⟩
          simp only [parallel_outputs]
          rw [htail_outputs]
      | inr u =>
          obtain ⟨v, round_fuel, right_xs, right_ys, hvalue, hright_round,
              hright_x', hright_y', hleft_x_same, hleft_y_same⟩ :=
            drive_parallel_right_projects (s := s) (t := t)
              (show (ws_pre ++ [Sum.inr u]).getLast? = some (Sum.inr u) by simp)
              hright_x hright_y hround
          change joint_value = Sum.inr v at hvalue
          subst joint_value
          have hleft_x' :
              PFunDDS.keptPrefix s (joint_xs.filterMap Sum.getLeft?) =
                PFunDDS.keptPrefix s lxs := by
            rw [hleft_x_same]
            exact hleft_x
          have hleft_y' : attribute_left_answers joint_ys = lys := by
            rw [hleft_y_same]
            exact hleft_y
          obtain ⟨tail_left_fuel, tail_left, tail_right_fuel, tail_right,
              htail_left, htail_right, htail_outputs, htail_left_x,
              htail_left_y, htail_right_x, htail_right_y⟩ :=
            ih (ws_pre := ws_pre ++ [Sum.inr u])
              hleft_x' hleft_y' hright_x' hright_y' htail
          let right_fuel := max round_fuel tail_right_fuel
          have hright_round' := drive_mono_le β t
            (Nat.le_max_left round_fuel tail_right_fuel) hright_round
          have htail_right' := driveOuter_mono_le β t
            (Nat.le_max_right round_fuel tail_right_fuel) htail_right
          have hright_run :
              (v :: tail_right.1, tail_right.2) ∈
                driveOuter β t right_fuel
                  (ws_pre.filterMap Sum.getRight?) rxs rys
                  ((Sum.inr u :: rest).filterMap Sum.getRight?) := by
            simp only [List.filterMap, Sum.getRight?, driveOuter,
              Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(v, right_xs, right_ys), ?_, tail_right, ?_, rfl⟩
            · simpa [right_fuel, List.filterMap_append] using hright_round'
            · simpa [right_fuel, List.filterMap_append] using htail_right'
          have hleft_run :
              tail_left ∈ driveOuter α s tail_left_fuel
                (ws_pre.filterMap Sum.getLeft?) lxs lys
                ((Sum.inr u :: rest).filterMap Sum.getLeft?) := by
            simpa [List.filterMap_append] using htail_left
          refine ⟨tail_left_fuel, tail_left, right_fuel,
            (v :: tail_right.1, tail_right.2), hleft_run, hright_run, ?_,
            htail_left_x, htail_left_y, htail_right_x, htail_right_y⟩
          simp only [parallel_outputs]
          rw [htail_outputs]

/-- Conversely, two component runs reassemble into a successful tagged
parallel run.  `AnswersInY` is used only by the one-round lifting lemmas: it
prevents a component from moving beyond an untagged `none`, which cannot be
assigned to either side by the attribution fold. -/
private theorem component_outer_runs_lift_to_parallel
    {α : ProtocolFn U V X Y} {β : ProtocolFn U' V' X' Y'}
    {s : PFunDDS.DDS X Y} {t : PFunDDS.DDS X' Y'}
    (hα : AnswersInY α) (hβ : AnswersInY β) :
    ∀ {rest : List (U ⊕ U')} {ws_pre : List (U ⊕ U')}
      {jxs : List (X ⊕ X')} {jys : List (Option (Y ⊕ Y'))}
      {lxs : List X} {lys : List (Option Y)}
      {rxs : List X'} {rys : List (Option Y')}
      {left_fuel : ℕ}
      {left_result : List V × List X × List (Option Y)}
      {right_fuel : ℕ}
      {right_result : List V' × List X' × List (Option Y')},
      PFunDDS.keptPrefix s (jxs.filterMap Sum.getLeft?) =
          PFunDDS.keptPrefix s lxs →
      attribute_left_answers jys = lys →
      PFunDDS.keptPrefix t (jxs.filterMap Sum.getRight?) =
          PFunDDS.keptPrefix t rxs →
      attribute_right_answers jys = rys →
      ready_outer_anchor α (ws_pre.filterMap Sum.getLeft?) lys →
      ready_outer_anchor β (ws_pre.filterMap Sum.getRight?) rys →
      left_result ∈ driveOuter α s left_fuel
        (ws_pre.filterMap Sum.getLeft?) lxs lys
        (rest.filterMap Sum.getLeft?) →
      right_result ∈ driveOuter β t right_fuel
        (ws_pre.filterMap Sum.getRight?) rxs rys
        (rest.filterMap Sum.getRight?) →
      ∃ (joint_fuel : ℕ)
        (joint_result : List (V ⊕ V') × List (X ⊕ X') ×
          List (Option (Y ⊕ Y'))),
        joint_result ∈ driveOuter (par α β) (PFunDDS.par s t)
          joint_fuel ws_pre jxs jys rest ∧
        joint_result.1 = parallel_outputs rest left_result.1 right_result.1 ∧
        PFunDDS.keptPrefix s (joint_result.2.1.filterMap Sum.getLeft?) =
          PFunDDS.keptPrefix s left_result.2.1 ∧
        attribute_left_answers joint_result.2.2 = left_result.2.2 ∧
        PFunDDS.keptPrefix t (joint_result.2.1.filterMap Sum.getRight?) =
          PFunDDS.keptPrefix t right_result.2.1 ∧
        attribute_right_answers joint_result.2.2 = right_result.2.2 := by
  intro rest
  induction rest with
  | nil =>
      intro ws_pre jxs jys lxs lys rxs rys left_fuel left_result
        right_fuel right_result hleft_x hleft_y hright_x hright_y
        _ _ hleft hright
      simp only [List.filterMap_nil, driveOuter, Part.mem_some_iff] at hleft hright
      subst left_result
      subst right_result
      refine ⟨0, ([], jxs, jys), ?_, rfl, hleft_x, hleft_y,
        hright_x, hright_y⟩
      simp [driveOuter]
  | cons w rest ih =>
      intro ws_pre jxs jys lxs lys rxs rys left_fuel left_result
        right_fuel right_result hleft_x hleft_y hright_x hright_y
        hleft_ready hright_ready hleft hright
      cases w with
      | inl u =>
          simp only [List.filterMap, Sum.getLeft?, driveOuter,
            Part.mem_bind_iff, Part.mem_map_iff] at hleft
          obtain ⟨left_round, hleft_round, left_tail, hleft_tail, rfl⟩ := hleft
          rcases left_round with ⟨left_value, left_xs, left_ys⟩
          obtain ⟨hleft_reach, hleft_proper⟩ :=
            ready_outer_anchor_opens_next hleft_ready u
          have hleft_reach' : Reach α
              ((ws_pre ++ [Sum.inl u]).filterMap Sum.getLeft?, lys) := by
            simpa [List.filterMap_append] using hleft_reach
          have hleft_round' : (left_value, left_xs, left_ys) ∈
              drive α s left_fuel
                ((ws_pre ++ [Sum.inl u]).filterMap Sum.getLeft?) lxs lys := by
            simpa [List.filterMap_append] using hleft_round
          have hleft_closed : closed_outer_anchor α
              (ws_pre.filterMap Sum.getLeft? ++ [u]) left_ys :=
            drive_ends_at_closed_outer_anchor hα hleft_reach hleft_proper
              hleft_round
          obtain ⟨joint_round_fuel, joint_xs, joint_ys, hjoint_round,
              hjoint_left_x, hjoint_left_y, hjoint_right_x_same,
              hjoint_right_y_same⟩ :=
            drive_left_lifts_to_parallel (s := s) (t := t)
              (ws := ws_pre ++ [Sum.inl u]) (jxs := jxs) (jys := jys)
              (xs := lxs) (ys := lys) hα
              (show (ws_pre ++ [Sum.inl u]).getLast? = some (Sum.inl u) by simp)
              hleft_reach' hleft_proper hleft_x hleft_y hleft_round'
          have hjoint_right_x :
              PFunDDS.keptPrefix t (joint_xs.filterMap Sum.getRight?) =
                PFunDDS.keptPrefix t rxs := by
            rw [hjoint_right_x_same]
            exact hright_x
          have hjoint_right_y : attribute_right_answers joint_ys = rys := by
            rw [hjoint_right_y_same]
            exact hright_y
          have hleft_tail' : left_tail ∈ driveOuter α s left_fuel
              ((ws_pre ++ [Sum.inl u]).filterMap Sum.getLeft?)
              left_xs left_ys (rest.filterMap Sum.getLeft?) := by
            simpa [List.filterMap_append] using hleft_tail
          have hright' : right_result ∈ driveOuter β t right_fuel
              ((ws_pre ++ [Sum.inl u]).filterMap Sum.getRight?)
              rxs rys (rest.filterMap Sum.getRight?) := by
            simpa [List.filterMap_append] using hright
          have hleft_ready' : ready_outer_anchor α
              ((ws_pre ++ [Sum.inl u]).filterMap Sum.getLeft?) left_ys := by
            simpa [List.filterMap_append] using Or.inr hleft_closed
          have hright_ready' : ready_outer_anchor β
              ((ws_pre ++ [Sum.inl u]).filterMap Sum.getRight?) rys := by
            simpa [List.filterMap_append] using hright_ready
          obtain ⟨joint_tail_fuel, joint_tail, hjoint_tail,
              hjoint_tail_outputs, hjoint_tail_left_x,
              hjoint_tail_left_y, hjoint_tail_right_x,
              hjoint_tail_right_y⟩ :=
            ih hjoint_left_x hjoint_left_y hjoint_right_x hjoint_right_y
              hleft_ready' hright_ready' hleft_tail' hright'
          let joint_fuel := max joint_round_fuel joint_tail_fuel
          have hjoint_round' := drive_mono_le (par α β) (PFunDDS.par s t)
            (Nat.le_max_left joint_round_fuel joint_tail_fuel) hjoint_round
          have hjoint_tail' := driveOuter_mono_le (par α β) (PFunDDS.par s t)
            (Nat.le_max_right joint_round_fuel joint_tail_fuel) hjoint_tail
          have hjoint_run :
              (Sum.inl left_value :: joint_tail.1, joint_tail.2) ∈
                driveOuter (par α β) (PFunDDS.par s t) joint_fuel
                  ws_pre jxs jys (Sum.inl u :: rest) := by
            simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
            exact ⟨(Sum.inl left_value, joint_xs, joint_ys),
              by simpa [joint_fuel] using hjoint_round', joint_tail,
              by simpa [joint_fuel] using hjoint_tail', rfl⟩
          refine ⟨joint_fuel,
            (Sum.inl left_value :: joint_tail.1, joint_tail.2),
            hjoint_run, ?_, hjoint_tail_left_x, hjoint_tail_left_y,
            hjoint_tail_right_x, hjoint_tail_right_y⟩
          simp only [parallel_outputs]
          rw [hjoint_tail_outputs]
      | inr u =>
          simp only [List.filterMap, Sum.getRight?, driveOuter,
            Part.mem_bind_iff, Part.mem_map_iff] at hright
          obtain ⟨right_round, hright_round, right_tail, hright_tail, rfl⟩ :=
            hright
          rcases right_round with ⟨right_value, right_xs, right_ys⟩
          obtain ⟨hright_reach, hright_proper⟩ :=
            ready_outer_anchor_opens_next hright_ready u
          have hright_reach' : Reach β
              ((ws_pre ++ [Sum.inr u]).filterMap Sum.getRight?, rys) := by
            simpa [List.filterMap_append] using hright_reach
          have hright_round' : (right_value, right_xs, right_ys) ∈
              drive β t right_fuel
                ((ws_pre ++ [Sum.inr u]).filterMap Sum.getRight?) rxs rys := by
            simpa [List.filterMap_append] using hright_round
          have hright_closed : closed_outer_anchor β
              (ws_pre.filterMap Sum.getRight? ++ [u]) right_ys :=
            drive_ends_at_closed_outer_anchor hβ hright_reach hright_proper
              hright_round
          obtain ⟨joint_round_fuel, joint_xs, joint_ys, hjoint_round,
              hjoint_right_x, hjoint_right_y, hjoint_left_x_same,
              hjoint_left_y_same⟩ :=
            drive_right_lifts_to_parallel (s := s) (t := t)
              (ws := ws_pre ++ [Sum.inr u]) (jxs := jxs) (jys := jys)
              (xs := rxs) (ys := rys) hβ
              (show (ws_pre ++ [Sum.inr u]).getLast? = some (Sum.inr u) by simp)
              hright_reach' hright_proper hright_x hright_y hright_round'
          have hjoint_left_x :
              PFunDDS.keptPrefix s (joint_xs.filterMap Sum.getLeft?) =
                PFunDDS.keptPrefix s lxs := by
            rw [hjoint_left_x_same]
            exact hleft_x
          have hjoint_left_y : attribute_left_answers joint_ys = lys := by
            rw [hjoint_left_y_same]
            exact hleft_y
          have hright_tail' : right_tail ∈ driveOuter β t right_fuel
              ((ws_pre ++ [Sum.inr u]).filterMap Sum.getRight?)
              right_xs right_ys (rest.filterMap Sum.getRight?) := by
            simpa [List.filterMap_append] using hright_tail
          have hleft' : left_result ∈ driveOuter α s left_fuel
              ((ws_pre ++ [Sum.inr u]).filterMap Sum.getLeft?)
              lxs lys (rest.filterMap Sum.getLeft?) := by
            simpa [List.filterMap_append] using hleft
          have hright_ready' : ready_outer_anchor β
              ((ws_pre ++ [Sum.inr u]).filterMap Sum.getRight?) right_ys := by
            simpa [List.filterMap_append] using Or.inr hright_closed
          have hleft_ready' : ready_outer_anchor α
              ((ws_pre ++ [Sum.inr u]).filterMap Sum.getLeft?) lys := by
            simpa [List.filterMap_append] using hleft_ready
          obtain ⟨joint_tail_fuel, joint_tail, hjoint_tail,
              hjoint_tail_outputs, hjoint_tail_left_x,
              hjoint_tail_left_y, hjoint_tail_right_x,
              hjoint_tail_right_y⟩ :=
            ih hjoint_left_x hjoint_left_y hjoint_right_x hjoint_right_y
              hleft_ready' hright_ready' hleft' hright_tail'
          let joint_fuel := max joint_round_fuel joint_tail_fuel
          have hjoint_round' := drive_mono_le (par α β) (PFunDDS.par s t)
            (Nat.le_max_left joint_round_fuel joint_tail_fuel) hjoint_round
          have hjoint_tail' := driveOuter_mono_le (par α β) (PFunDDS.par s t)
            (Nat.le_max_right joint_round_fuel joint_tail_fuel) hjoint_tail
          have hjoint_run :
              (Sum.inr right_value :: joint_tail.1, joint_tail.2) ∈
                driveOuter (par α β) (PFunDDS.par s t) joint_fuel
                  ws_pre jxs jys (Sum.inr u :: rest) := by
            simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
            exact ⟨(Sum.inr right_value, joint_xs, joint_ys),
              by simpa [joint_fuel] using hjoint_round', joint_tail,
              by simpa [joint_fuel] using hjoint_tail', rfl⟩
          refine ⟨joint_fuel,
            (Sum.inr right_value :: joint_tail.1, joint_tail.2),
            hjoint_run, ?_, hjoint_tail_left_x, hjoint_tail_left_y,
            hjoint_tail_right_x, hjoint_tail_right_y⟩
          simp only [parallel_outputs]
          rw [hjoint_tail_outputs]

/-- With one component output for each projected query, reinterleaving
preserves the joint outer-history length. -/
private theorem parallel_outputs_length
    (ws : List (U ⊕ U')) (vs : List V) (vs' : List V')
    (hleft : vs.length = (ws.filterMap Sum.getLeft?).length)
    (hright : vs'.length = (ws.filterMap Sum.getRight?).length) :
    (parallel_outputs ws vs vs').length = ws.length := by
  induction ws generalizing vs vs' with
  | nil => simp [parallel_outputs]
  | cons w ws ih =>
      cases w with
      | inl u =>
          cases vs with
          | nil => simp at hleft
          | cons v vs =>
              have hleft_tail :
                  vs.length = (ws.filterMap Sum.getLeft?).length := by
                simpa using hleft
              have hright_tail :
                  vs'.length = (ws.filterMap Sum.getRight?).length := by
                simpa using hright
              simpa only [parallel_outputs, List.length_cons, Nat.succ.injEq]
                using ih vs vs' hleft_tail hright_tail
      | inr u =>
          cases vs' with
          | nil => simp at hright
          | cons v vs' =>
              have hleft_tail :
                  vs.length = (ws.filterMap Sum.getLeft?).length := by
                simpa using hleft
              have hright_tail :
                  vs'.length = (ws.filterMap Sum.getRight?).length := by
                simpa using hright
              simpa only [parallel_outputs, List.length_cons, Nat.succ.injEq]
                using ih vs vs' hleft_tail hright_tail

private theorem left_projection_ne_nil_of_get_last_inl
    {ws : List (U ⊕ U')} {u : U}
    (hlast : ws.getLast? = some (Sum.inl u)) :
    ws.filterMap Sum.getLeft? ≠ [] := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  simp

private theorem right_projection_ne_nil_of_get_last_inr
    {ws : List (U ⊕ U')} {u : U'}
    (hlast : ws.getLast? = some (Sum.inr u)) :
    ws.filterMap Sum.getRight? ≠ [] := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  simp

/-- The total reinterleaver's last output is selected by the last outer
query tag.  The length hypotheses are exactly the `driveOuter_length`
invariants; they rule out the deliberately unreachable fallback clauses. -/
private theorem parallel_outputs_get_last
    (ws : List (U ⊕ U')) (vs : List V) (vs' : List V')
    (hleft : vs.length = (ws.filterMap Sum.getLeft?).length)
    (hright : vs'.length = (ws.filterMap Sum.getRight?).length) :
    (parallel_outputs ws vs vs').getLast? =
      match ws.getLast? with
      | none => none
      | some (Sum.inl _) => vs.getLast?.map Sum.inl
      | some (Sum.inr _) => vs'.getLast?.map Sum.inr := by
  induction ws generalizing vs vs' with
  | nil => simp [parallel_outputs]
  | cons w ws ih =>
      cases w with
      | inl u =>
          cases vs with
          | nil => simp at hleft
          | cons v vs =>
              have hleft_tail :
                  vs.length = (ws.filterMap Sum.getLeft?).length := by
                simpa using hleft
              have hright_tail :
                  vs'.length = (ws.filterMap Sum.getRight?).length := by
                simpa using hright
              cases ws with
              | nil =>
                  have hvs : vs = [] := List.length_eq_zero_iff.mp (by
                    simpa using hleft_tail)
                  subst vs
                  simp [parallel_outputs]
              | cons w ws =>
                  have htail := ih vs vs' hleft_tail hright_tail
                  have hout_ne : parallel_outputs (w :: ws) vs vs' ≠ [] := by
                    apply List.ne_nil_of_length_pos
                    rw [parallel_outputs_length (w :: ws) vs vs'
                      hleft_tail hright_tail]
                    simp
                  cases hout : parallel_outputs (w :: ws) vs vs' with
                  | nil => exact (hout_ne hout).elim
                  | cons output outputs =>
                      change
                        (Sum.inl v :: parallel_outputs (w :: ws) vs vs').getLast? =
                          match (Sum.inl u :: w :: ws).getLast? with
                          | none => none
                          | some (Sum.inl _) => (v :: vs).getLast?.map Sum.inl
                          | some (Sum.inr _) => vs'.getLast?.map Sum.inr
                      cases htail_tag : (w :: ws).getLast? with
                      | none => simp at htail_tag
                      | some tag =>
                          cases tag with
                          | inl last_u =>
                              have hvs_ne : vs ≠ [] := by
                                apply List.ne_nil_of_length_pos
                                rw [hleft_tail]
                                exact List.length_pos_of_ne_nil
                                  (left_projection_ne_nil_of_get_last_inl
                                    htail_tag)
                              cases vs with
                              | nil => exact (hvs_ne rfl).elim
                              | cons tail_value tail_values =>
                                  simpa only [hout, List.getLast?_cons_cons,
                                    htail_tag] using htail
                          | inr last_u =>
                              simpa only [hout, List.getLast?_cons_cons,
                                htail_tag] using htail
      | inr u =>
          cases vs' with
          | nil => simp at hright
          | cons v vs' =>
              have hleft_tail :
                  vs.length = (ws.filterMap Sum.getLeft?).length := by
                simpa using hleft
              have hright_tail :
                  vs'.length = (ws.filterMap Sum.getRight?).length := by
                simpa using hright
              cases ws with
              | nil =>
                  have hvs' : vs' = [] := List.length_eq_zero_iff.mp (by
                    simpa using hright_tail)
                  subst vs'
                  simp [parallel_outputs]
              | cons w ws =>
                  have htail := ih vs vs' hleft_tail hright_tail
                  have hout_ne : parallel_outputs (w :: ws) vs vs' ≠ [] := by
                    apply List.ne_nil_of_length_pos
                    rw [parallel_outputs_length (w :: ws) vs vs'
                      hleft_tail hright_tail]
                    simp
                  cases hout : parallel_outputs (w :: ws) vs vs' with
                  | nil => exact (hout_ne hout).elim
                  | cons output outputs =>
                      change
                        (Sum.inr v :: parallel_outputs (w :: ws) vs vs').getLast? =
                          match (Sum.inr u :: w :: ws).getLast? with
                          | none => none
                          | some (Sum.inl _) => vs.getLast?.map Sum.inl
                          | some (Sum.inr _) => (v :: vs').getLast?.map Sum.inr
                      cases htail_tag : (w :: ws).getLast? with
                      | none => simp at htail_tag
                      | some tag =>
                          cases tag with
                          | inl last_u =>
                              simpa only [hout, List.getLast?_cons_cons,
                                htail_tag] using htail
                          | inr last_u =>
                              have hvs_ne : vs' ≠ [] := by
                                apply List.ne_nil_of_length_pos
                                rw [hright_tail]
                                exact List.length_pos_of_ne_nil
                                  (right_projection_ne_nil_of_get_last_inr
                                    htail_tag)
                              cases vs' with
                              | nil => exact (hvs_ne rfl).elim
                              | cons tail_value tail_values =>
                                  simpa only [hout, List.getLast?_cons_cons,
                                    htail_tag] using htail

/-- A completed outer run whose output stream ends in `v` witnesses
membership in converter application. -/
private theorem drive_outer_last_mem_apply
    (alpha : ProtocolFn U V X Y) (s : PFunDDS.DDS X Y)
    {fuel : ℕ} {us : List U}
    {result : List V × List X × List (Option Y)} {v : V}
    (hrun : result ∈ driveOuter alpha s fuel [] [] [] us)
    (hlast : result.1.getLast? = some v) :
    v ∈ (apply alpha s).1 us := by
  change v ∈ applyRaw alpha s us
  rw [mem_applyRaw]
  refine ⟨fuel, ?_⟩
  rw [mem_applyRawAt_iff]
  exact ⟨result, hrun, hlast⟩

/-- A successful run over a nonempty outer history makes the corresponding
application defined. -/
private theorem drive_outer_nonempty_gives_apply_dom
    (alpha : ProtocolFn U V X Y) (s : PFunDDS.DDS X Y)
    {fuel : ℕ} {us : List U}
    {result : List V × List X × List (Option Y)}
    (hrun : result ∈ driveOuter alpha s fuel [] [] [] us)
    (hne : us ≠ []) : ((apply alpha s).1 us).Dom := by
  have hresult_ne : result.1 ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [driveOuter_length alpha s fuel hrun]
    exact List.length_pos_of_ne_nil hne
  exact Part.dom_iff_mem.mpr ⟨result.1.getLast hresult_ne,
    drive_outer_last_mem_apply alpha s hrun
      (List.getLast?_eq_some_getLast hresult_ne)⟩

/-- Membership in converter application exposes the finite-fuel outer run
which produced it. -/
private theorem apply_member_has_outer_run
    (alpha : ProtocolFn U V X Y) (s : PFunDDS.DDS X Y)
    {us : List U} {v : V} (hmem : v ∈ (apply alpha s).1 us) :
    ∃ (fuel : ℕ) (result : List V × List X × List (Option Y)),
      result ∈ driveOuter alpha s fuel [] [] [] us ∧
      result.1.getLast? = some v := by
  change v ∈ applyRaw alpha s us at hmem
  rw [mem_applyRaw] at hmem
  obtain ⟨fuel, hmem⟩ := hmem
  rw [mem_applyRawAt_iff] at hmem
  obtain ⟨result, hrun, hlast⟩ := hmem
  exact ⟨fuel, result, hrun, hlast⟩

/-- The conditional domain premise used by parallel composition supplies a
component outer run.  The empty projection has the canonical empty run. -/
private theorem outer_run_exists_of_apply_dom
    (alpha : ProtocolFn U V X Y) (s : PFunDDS.DDS X Y) (us : List U)
    (hdom : us ≠ [] → ((apply alpha s).1 us).Dom) :
    ∃ (fuel : ℕ) (result : List V × List X × List (Option Y)),
      result ∈ driveOuter alpha s fuel [] [] [] us := by
  by_cases hne : us = []
  · subst us
    exact ⟨0, ([], [], []), by simp [driveOuter]⟩
  · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp (hdom hne)
    obtain ⟨fuel, result, hrun, -⟩ :=
      apply_member_has_outer_run alpha s hv
    exact ⟨fuel, result, hrun⟩

/-- Membership in the tagged parallel system, with its two conditional
domain guards made explicit. -/
private theorem mem_parallel_system_iff
    (s : PFunDDS.DDS X Y) (t : PFunDDS.DDS X' Y')
    (ws : List (X ⊕ X')) (value : Y ⊕ Y') :
    value ∈ (PFunDDS.par s t).1 ws ↔
      ((ws.filterMap Sum.getLeft? ≠ []) →
        (s.1 (ws.filterMap Sum.getLeft?)).Dom) ∧
      ((ws.filterMap Sum.getRight? ≠ []) →
        (t.1 (ws.filterMap Sum.getRight?)).Dom) ∧
      value ∈ (match ws.getLast? with
        | some (Sum.inl _) =>
            (s.1 (ws.filterMap Sum.getLeft?)).map Sum.inl
        | some (Sum.inr _) =>
            (t.1 (ws.filterMap Sum.getRight?)).map Sum.inr
        | none => Part.none) := by
  show value ∈ Part.assert _ _ ↔ _
  rw [Part.mem_assert_iff]
  constructor
  · rintro ⟨hleft, hmem⟩
    rw [Part.mem_assert_iff] at hmem
    obtain ⟨hright, hmem⟩ := hmem
    exact ⟨hleft, hright, hmem⟩
  · rintro ⟨hleft, hright, hmem⟩
    exact ⟨hleft, Part.mem_assert_iff.mpr ⟨hright, hmem⟩⟩

/-- MauRen11 §6.2, the law defining parallel composition of converters:
`(α‖β)(R‖S) = αR ‖ βS`.  `AnswersInY` is the exact input-alphabet
condition needed in the reverse direction: an untagged `none` has no side
for the attribution folds, so a component may not continue past it. -/
theorem apply_parallel_eq_parallel_apply
    (α : ProtocolFn U V X Y) (β : ProtocolFn U' V' X' Y')
    (s : PFunDDS.DDS X Y) (t : PFunDDS.DDS X' Y')
    (hα : AnswersInY α) (hβ : AnswersInY β) :
    apply (par α β) (PFunDDS.par s t) =
      PFunDDS.par (apply α s) (apply β t) := by
  apply Subtype.ext
  funext ws
  apply Part.ext
  intro joint_value
  change joint_value ∈ applyRaw (par α β) (PFunDDS.par s t) ws ↔
    joint_value ∈ (PFunDDS.par (apply α s) (apply β t)).1 ws
  constructor
  · intro hjoint
    rw [mem_applyRaw] at hjoint
    obtain ⟨joint_fuel, hjoint⟩ := hjoint
    rw [mem_applyRawAt_iff] at hjoint
    obtain ⟨joint_result, hjoint_run, hjoint_last⟩ := hjoint
    obtain ⟨left_fuel, left_result, right_fuel, right_result,
        hleft_run, hright_run, hjoint_outputs, _, _, _, _⟩ :=
      parallel_outer_run_projects (s := s) (t := t)
        (rest := ws) (ws_pre := []) (jxs := []) (jys := [])
        (lxs := []) (lys := []) (rxs := []) (rys := [])
        rfl rfl rfl rfl hjoint_run
    rw [mem_parallel_system_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro hne
      exact drive_outer_nonempty_gives_apply_dom α s hleft_run hne
    · intro hne
      exact drive_outer_nonempty_gives_apply_dom β t hright_run hne
    · have hleft_length := driveOuter_length α s left_fuel hleft_run
      have hright_length := driveOuter_length β t right_fuel hright_run
      have hlast := parallel_outputs_get_last ws left_result.1 right_result.1
        hleft_length hright_length
      rw [← hjoint_outputs, hjoint_last] at hlast
      cases hws : ws.getLast? with
      | none =>
          rw [hws] at hlast
          simp at hlast
      | some tag =>
          cases tag with
          | inl u =>
              rw [hws] at hlast
              cases hleft_last : left_result.1.getLast? with
              | none =>
                  rw [hleft_last] at hlast
                  simp at hlast
              | some left_value =>
                  rw [hleft_last] at hlast
                  simp only [Option.map_some, Option.some.injEq] at hlast
                  subst joint_value
                  change Sum.inl left_value ∈
                    ((apply α s).1 (ws.filterMap Sum.getLeft?)).map Sum.inl
                  rw [Part.mem_map_iff]
                  exact ⟨left_value,
                    drive_outer_last_mem_apply α s hleft_run hleft_last, rfl⟩
          | inr u =>
              rw [hws] at hlast
              cases hright_last : right_result.1.getLast? with
              | none =>
                  rw [hright_last] at hlast
                  simp at hlast
              | some right_value =>
                  rw [hright_last] at hlast
                  simp only [Option.map_some, Option.some.injEq] at hlast
                  subst joint_value
                  change Sum.inr right_value ∈
                    ((apply β t).1 (ws.filterMap Sum.getRight?)).map Sum.inr
                  rw [Part.mem_map_iff]
                  exact ⟨right_value,
                    drive_outer_last_mem_apply β t hright_run hright_last, rfl⟩
  · intro hparallel
    rw [mem_parallel_system_iff] at hparallel
    obtain ⟨hleft_dom, hright_dom, hparallel_last⟩ := hparallel
    obtain ⟨left_fuel, left_result, hleft_run⟩ :=
      outer_run_exists_of_apply_dom α s (ws.filterMap Sum.getLeft?) hleft_dom
    obtain ⟨right_fuel, right_result, hright_run⟩ :=
      outer_run_exists_of_apply_dom β t (ws.filterMap Sum.getRight?) hright_dom
    obtain ⟨joint_fuel, joint_result, hjoint_run, hjoint_outputs,
        _, _, _, _⟩ :=
      component_outer_runs_lift_to_parallel (s := s) (t := t) hα hβ
        (rest := ws) (ws_pre := []) (jxs := []) (jys := [])
        (lxs := []) (lys := []) (rxs := []) (rys := [])
        rfl rfl rfl rfl (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
        hleft_run hright_run
    rw [mem_applyRaw]
    refine ⟨joint_fuel, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨joint_result, hjoint_run, ?_⟩
    have hleft_length := driveOuter_length α s left_fuel hleft_run
    have hright_length := driveOuter_length β t right_fuel hright_run
    have hlast := parallel_outputs_get_last ws left_result.1 right_result.1
      hleft_length hright_length
    rw [← hjoint_outputs] at hlast
    cases hws : ws.getLast? with
    | none =>
        exfalso
        rw [hws] at hparallel_last
        simpa using hparallel_last
    | some tag =>
        cases tag with
        | inl u =>
            rw [hws, Part.mem_map_iff] at hparallel_last
            obtain ⟨left_value, hleft_value_mem, hleft_tag⟩ := hparallel_last
            have hleft_ne := left_projection_ne_nil_of_get_last_inl hws
            have hleft_result_ne : left_result.1 ≠ [] := by
              apply List.ne_nil_of_length_pos
              rw [driveOuter_length α s left_fuel hleft_run]
              exact List.length_pos_of_ne_nil hleft_ne
            let run_value := left_result.1.getLast hleft_result_ne
            have hrun_last : left_result.1.getLast? = some run_value :=
              List.getLast?_eq_some_getLast hleft_result_ne
            have hrun_mem : run_value ∈
                (apply α s).1 (ws.filterMap Sum.getLeft?) :=
              drive_outer_last_mem_apply α s hleft_run hrun_last
            have hvalue_eq : run_value = left_value :=
              Part.mem_unique hrun_mem hleft_value_mem
            rw [hws, hrun_last] at hlast
            simp only [Option.map_some] at hlast
            calc
              joint_result.1.getLast? = some (Sum.inl run_value) := hlast
              _ = some (Sum.inl left_value) := by rw [hvalue_eq]
              _ = some joint_value := congrArg some hleft_tag
        | inr u =>
            rw [hws, Part.mem_map_iff] at hparallel_last
            obtain ⟨right_value, hright_value_mem, hright_tag⟩ := hparallel_last
            have hright_ne := right_projection_ne_nil_of_get_last_inr hws
            have hright_result_ne : right_result.1 ≠ [] := by
              apply List.ne_nil_of_length_pos
              rw [driveOuter_length β t right_fuel hright_run]
              exact List.length_pos_of_ne_nil hright_ne
            let run_value := right_result.1.getLast hright_result_ne
            have hrun_last : right_result.1.getLast? = some run_value :=
              List.getLast?_eq_some_getLast hright_result_ne
            have hrun_mem : run_value ∈
                (apply β t).1 (ws.filterMap Sum.getRight?) :=
              drive_outer_last_mem_apply β t hright_run hrun_last
            have hvalue_eq : run_value = right_value :=
              Part.mem_unique hrun_mem hright_value_mem
            rw [hws, hrun_last] at hlast
            simp only [Option.map_some] at hlast
            calc
              joint_result.1.getLast? = some (Sum.inr run_value) := hlast
              _ = some (Sum.inr right_value) := by rw [hvalue_eq]
              _ = some joint_value := congrArg some hright_tag

end PFunConverter

namespace PFunPDS

variable {X Y X' Y' U V : Type*}

/-- Parallel composition of probabilistic systems: the independent
product of the component distributions (fn. 20), pushed through the
deterministic parallel composition. -/
noncomputable def par (S : PFunPDS X Y) (T : PFunPDS X' Y') :
    PFunPDS (X ⊕ X') (Y ⊕ Y') :=
  Dist.fTransform (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
    PFunDDS.par p.1 p.2) (Dist.prod S T)

/-- Parallel composition preserves probability mass. -/
theorem isProbDist_par {S : PFunPDS X Y} {T : PFunPDS X' Y'}
    (hS : S.isProbDist) (hT : T.isProbDist) :
    (S.par T).isProbDist := by
  unfold par
  exact Dist.fTransform_isProbDist _ (Dist.prod_isProbDist _ _ hS hT)

/-- Converter application lifted to probabilistic systems: the
pushforward of the deterministic `apply` — "applying a converter
simply creates a random system." -/
@[rs_rule "rs.distribution.apply" rs_distribution random_systems]
noncomputable def apply (α : PFunConverter.ProtocolFn U V X Y)
    (S : PFunPDS X Y) : PFunPDS U V :=
  Dist.fTransform (fun s => PFunConverter.apply α s) S

/-- Converter application preserves and reflects probability mass (for a
non-negative law; over the signed carrier the unconditional `↔` is false). -/
theorem isProbDist_apply_iff (α : PFunConverter.ProtocolFn U V X Y)
    {S : PFunPDS X Y} (hS : S.NonNeg) :
    (apply α S).isProbDist ↔ S.isProbDist := by
  unfold apply
  exact Dist.isProbDist_fTransform _ hS

end PFunPDS

/-! ### CR18 §4.10.1 normalization: truncation and the verdict flip

The symmetry of `Δ` for probability systems is the verdict-flip
argument, and the flip decides the complement only against a
distinguisher that always stops.  §4.10.1's WLOG supplies the stopping:
truncate the distinguisher at a query budget `q` beyond every verdict
witness on the (finite) supports — truncation changes no verdict there,
always stops, and its flip complements exactly. -/

namespace PFunDDS

variable {X Y : Type*}

/-- The **verdict-flipped distinguisher** (CR18 §4.10.2): same queries,
negated verdict bit. -/
def flipDDD (d : DDD X Y) : DDD X Y :=
  ⟨fun h => (d.val h).map id not, by
    intro h h' hpre b hb
    have hb' : Sum.map id not (d.val h) = Sum.inr b := hb
    show Sum.map id not (d.val h') = Sum.inr b
    rcases hd : d.val h with x | b₀ <;> rw [hd] at hb'
    · exact absurd hb' (by simp)
    · rw [d.property hpre b₀ hd]
      exact hb'⟩

/-- Flipping the verdict does not change the queries. -/
theorem ddToDDE_flipDDD (d : DDD X Y) :
    ddToDDE (flipDDD d) = ddToDDE d := by
  funext h
  show (match Sum.map id not (d.val h) with
      | Sum.inl x => some x | Sum.inr _ => none)
    = (match d.val h with | Sum.inl x => some x | Sum.inr _ => none)
  rcases d.val h with x | b <;> rfl

/-- CR18 §4.10.1 **truncation**: run `d` unchanged while fewer than `q`
answers have arrived; once `q` answers are in, stop — with `d`'s bit if
`d` had already stopped by the `q`-prefix, with `0` otherwise. -/
def truncDDD (q : ℕ) (d : DDD X Y) : DDD X Y :=
  ⟨fun h =>
    if h.length < q then d.val h
    else match d.val (h.take q) with
      | Sum.inl _ => Sum.inr false
      | Sum.inr b => Sum.inr b, by
    intro h h' hpre b hb
    dsimp only at hb ⊢
    by_cases hlt : h.length < q
    · rw [if_pos hlt] at hb
      by_cases hlt' : h'.length < q
      · rw [if_pos hlt']
        exact d.property hpre b hb
      · rw [if_neg hlt']
        have hpre' : h <+: h'.take q :=
          List.prefix_take_iff.mpr ⟨hpre, le_of_lt hlt⟩
        rw [d.property hpre' b hb]
    · have hge : q ≤ h.length := not_lt.mp hlt
      rw [if_neg hlt] at hb
      rw [if_neg (not_lt.mpr (le_trans hge hpre.length_le))]
      have htake : h'.take q = h.take q := by
        obtain ⟨t, rfl⟩ := hpre
        exact List.take_append_of_le_length hge
      rw [htake]
      exact hb⟩

theorem truncDDD_val_of_lt {q : ℕ} {d : DDD X Y} {h : List (Option Y)}
    (hlt : h.length < q) : (truncDDD q d).val h = d.val h := by
  show (if h.length < q then d.val h
      else match d.val (h.take q) with
        | Sum.inl _ => Sum.inr false
        | Sum.inr b => Sum.inr b) = d.val h
  exact if_pos hlt

theorem truncDDD_val_of_ge {q : ℕ} {d : DDD X Y} {h : List (Option Y)}
    (hge : q ≤ h.length) :
    (truncDDD q d).val h =
      match d.val (h.take q) with
      | Sum.inl _ => Sum.inr false
      | Sum.inr b => Sum.inr b := by
  show (if h.length < q then d.val h
      else match d.val (h.take q) with
        | Sum.inl _ => Sum.inr false
        | Sum.inr b => Sum.inr b) = _
  exact if_neg (not_lt.mpr hge)

/-- Below the budget the truncation queries exactly as `d` does. -/
theorem ddToDDE_truncDDD_of_lt {q : ℕ} {d : DDD X Y} {h : List (Option Y)}
    (hlt : h.length < q) :
    ddToDDE (truncDDD q d) h = ddToDDE d h := by
  unfold ddToDDE
  rw [truncDDD_val_of_lt hlt]

/-- At the budget the truncation has stopped. -/
theorem ddToDDE_truncDDD_of_ge {q : ℕ} {d : DDD X Y} {h : List (Option Y)}
    (hge : q ≤ h.length) :
    ddToDDE (truncDDD q d) h = none := by
  refine ddToDDE_eq_none_iff.mpr ?_
  rw [truncDDD_val_of_ge hge]
  rcases d.val (h.take q) with x | b
  exacts [⟨false, rfl⟩, ⟨b, rfl⟩]

/-- Under the budget, `d` and its truncation generate the same
transcript. -/
theorem transcript_truncDDD (q : ℕ) (d : DDD X Y) (s : DDS X Y) :
    ∀ {n : ℕ}, n ≤ q →
      transcript s (ddToDDE (truncDDD q d)) n = transcript s (ddToDDE d) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hih := ih (Nat.le_of_succ_le hn)
      have hlen : ((transcript s (ddToDDE d) n)↓ᵧ).length < q := by
        rw [transcriptOutputs_length]
        exact lt_of_le_of_lt (transcript_length_le n) (Nat.lt_of_succ_le hn)
      have henv : ddToDDE (truncDDD q d) ((transcript s (ddToDDE d) n)↓ᵧ)
          = ddToDDE d ((transcript s (ddToDDE d) n)↓ᵧ) :=
        ddToDDE_truncDDD_of_lt hlen
      rcases he : ddToDDE d ((transcript s (ddToDDE d) n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall (by rw [hih, henv]; exact he),
          transcript_succ_stall he, hih]
      · rw [transcript_succ_fire (by rw [hih, henv]; exact he),
          transcript_succ_fire he, hih]

/-- A transcript shorter than its fuel has stalled. -/
theorem transcript_stall_of_length_lt {s : DDS X Y} {e : DDE X Y} :
    ∀ {n : ℕ}, (transcript s e n).length < n → e ((transcript s e n)↓ᵧ) = none := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro hlen
      rcases he : e ((transcript s e n)↓ᵧ) with _ | x
      · rwa [transcript_succ_stall he]
      · exfalso
        rw [transcript_succ_fire he, List.length_append] at hlen
        have hstall := ih (by simpa using hlen)
        rw [hstall] at he
        simp at he

/-- The truncation has stalled by fuel `q` — against every system. -/
theorem ddToDDE_truncDDD_stall (q : ℕ) (d : DDD X Y) (s : DDS X Y) :
    ddToDDE (truncDDD q d)
      ((transcript s (ddToDDE (truncDDD q d)) q)↓ᵧ) = none := by
  rcases lt_or_ge (transcript s (ddToDDE (truncDDD q d)) q).length q with hlt | hge
  · exact transcript_stall_of_length_lt hlt
  · exact ddToDDE_truncDDD_of_ge (by rwa [transcriptOutputs_length])

/-- Truncation preserves a verdict whose witness fits under the
budget. -/
theorem verdict_truncDDD_of_lt {q n : ℕ} {d : DDD X Y} {s : DDS X Y}
    (hn : n < q)
    (hwit : d.val ((transcript s (ddToDDE d) n)↓ᵧ) = Sum.inr true) :
    verdict (truncDDD q d) s := by
  refine ⟨n, ?_⟩
  rw [transcript_truncDDD q d s (le_of_lt hn),
    truncDDD_val_of_lt (by
      rw [transcriptOutputs_length]
      exact lt_of_le_of_lt (transcript_length_le n) hn)]
  exact hwit

/-- A truncated verdict comes from a verdict of `d`. -/
theorem verdict_of_verdict_truncDDD {q : ℕ} {d : DDD X Y} {s : DDS X Y}
    (h : verdict (truncDDD q d) s) : verdict d s := by
  obtain ⟨n, hn⟩ := h
  have hstop := ddToDDE_truncDDD_stall q d s
  -- reduce the witness fuel to `min n q` via the freeze at the stall
  have hn' : (truncDDD q d).val
      ((transcript s (ddToDDE (truncDDD q d)) (min n q))↓ᵧ) = Sum.inr true := by
    rcases le_total n q with hnq | hqn
    · rwa [min_eq_left hnq]
    · rw [min_eq_right hqn]
      rwa [transcript_freeze hstop hqn] at hn
  have hmq : min n q ≤ q := min_le_right n q
  rw [transcript_truncDDD q d s hmq] at hn'
  by_cases hlt : ((transcript s (ddToDDE d) (min n q))↓ᵧ).length < q
  · rw [truncDDD_val_of_lt hlt] at hn'
    exact ⟨min n q, hn'⟩
  · have hge : q ≤ ((transcript s (ddToDDE d) (min n q))↓ᵧ).length := not_lt.mp hlt
    rw [truncDDD_val_of_ge hge] at hn'
    rcases hd : d.val (((transcript s (ddToDDE d) (min n q))↓ᵧ).take q) with x | b <;>
      rw [hd] at hn'
    · exact absurd hn' (by simp)
    · have hb : b = true := by simpa using hn'
      have hlen : ((transcript s (ddToDDE d) (min n q))↓ᵧ).length = q :=
        le_antisymm (by
          rw [transcriptOutputs_length]
          exact le_trans (transcript_length_le _) hmq) hge
      rw [List.take_of_length_le (le_of_eq hlen)] at hd
      exact ⟨min n q, by rw [hd, hb]⟩

/-- Against **every** system, the flip of a truncation decides the
complement: the truncated run stalls by fuel `q`, and the two verdicts
are the two readings of the stall bit. -/
theorem verdict_flipDDD_truncDDD_iff (q : ℕ) (d : DDD X Y) (s : DDS X Y) :
    verdict (flipDDD (truncDDD q d)) s ↔ ¬ verdict (truncDDD q d) s := by
  classical
  have hstop := ddToDDE_truncDDD_stall q d s
  have hstopF : ddToDDE (flipDDD (truncDDD q d))
      ((transcript s (ddToDDE (flipDDD (truncDDD q d))) q)↓ᵧ) = none := by
    rw [ddToDDE_flipDDD]; exact hstop
  rw [Cache.verdict_iff_at_stall _ s q hstop,
    Cache.verdict_iff_at_stall _ s q hstopF, ddToDDE_flipDDD]
  obtain ⟨b₀, hb₀⟩ := ddToDDE_eq_none_iff.mp hstop
  show (Sum.map id not ((truncDDD q d).val
      ((transcript s (ddToDDE (truncDDD q d)) q)↓ᵧ)) = Sum.inr true) ↔ _
  rw [hb₀]
  cases b₀ <;> simp

end PFunDDS

/-- Winning probability depends on the predicate only through its
values on the two supports. -/
theorem GamePerf.winProb_congr_support {Winner Game : Type*}
    {win win' : Winner → Game → Prop} (W : Dist Winner) (G : Dist Game)
    (h : ∀ w ∈ W.support, ∀ g ∈ G.support, (win w g ↔ win' w g)) :
    GamePerf.winProb win W G = GamePerf.winProb win' W G := by
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun w hw => Finsupp.sum_congr fun g hg => ?_
  classical
  by_cases hwin : win w g
  · rw [if_pos hwin, if_pos ((h w hw g hg).mp hwin)]
  · rw [if_neg hwin, if_neg fun h' => hwin ((h w hw g hg).mpr h')]

/-! ### Definition 2: the compatibility of the distinguisher metric -/

variable {X Y X' Y' U V : Type*}

/-- Maurer11 §4.4 Definition 2, eq. (4) (MauRen16 Definition 2:
**non-expanding**): connecting a converter cannot increase the
distance — `d(αⁱR, αⁱS) ≤ d(R, S)`. -/
@[rs_rule "rs.emulable.nonexpanding" distance_bound random_systems]
theorem maxAdvantage_apply_le (α : PFunConverter.ProtocolFn U V X Y)
    {S T : PFunPDS X Y} (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PFunConverter.Emulable α) :
    Δ(PFunPDS.apply α S, PFunPDS.apply α T) ≤ Δ(S, T) := by
  rw [← adv_eq_maxAdvantage_swap
      (show (PFunPDS.apply α T).NonNeg from hTnn.fTransform _)
      (show (PFunPDS.apply α S).NonNeg from hSnn.fTransform _),
    ← adv_eq_maxAdvantage_swap hTnn hSnn]
  refine csSup_le ⟨_, ⟨(fun _ => none), 0, rfl⟩⟩ ?_
  rintro x ⟨e, n, rfl⟩
  obtain ⟨e', m, g, hg⟩ := h e n
  rw [show PFunPDS.apply α T
      = Dist.fTransform (fun s => PFunConverter.apply α s) T from rfl,
    show PFunPDS.apply α S
      = Dist.fTransform (fun s => PFunConverter.apply α s) S from rfl,
    PFunConverter.transcriptDist_fTransform_of_transcript_eq hg T,
    PFunConverter.transcriptDist_fTransform_of_transcript_eq hg S]
  refine le_trans ?_ (le_csSup (bddAbove_adv_set hTnn hSnn) ⟨e', m, rfl⟩)
  exact δ_fTransform_le g _ (transcriptDist_nonNeg hSnn _ _)

/-- The distinguisher metric satisfies the triangle inequality: the
per-distinguisher advantage telescopes through any middle system. -/
private theorem maxAdvantage_le_add_maxAdvantage (A B C : PFunPDS X Y) :
    Δ(A, C) ≤ Δ(A, B) + Δ(B, C) := by
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  have h : advantage D A C = advantage D A B + advantage D B C := by
    unfold advantage
    ring
  rw [h]
  exact add_le_add (advantage_le_maxAdvantage D A B hD)
    (advantage_le_maxAdvantage D B C hD)

/-- Maurer11 §4.4 Definition 2, eq. (3): putting a resource in parallel
cannot increase the distance —
`d(R‖R′, S‖S′) ≤ d(R, S) + d(R′, S′)` — for **probability systems**
(thesis Def 2.4's weight-sensitivity: at super-probability weights the
fixed component's weight scales the advantage and eq. (3) is refutable;
the general-weight scaled form is a separate library item). -/
theorem maxAdvantage_par_le (S T : PFunPDS X Y) (S' T' : PFunPDS X' Y')
    (_hS : S.isProbDist) (hT : T.isProbDist)
    (hS' : S'.isProbDist) (_hT' : T'.isProbDist) :
    Δ(S.par S', T.par T') ≤ Δ(S, T) + Δ(S', T') := by
  refine (maxAdvantage_le_add_maxAdvantage (S.par S') (T.par S')
    (T.par T')).trans (add_le_add ?_ ?_)
  · rw [show S.par S' = Dist.fTransform
        (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => PFunDDS.par p.1 p.2)
        (Dist.prod S S') from rfl,
      show T.par S' = Dist.fTransform
        (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => PFunDDS.par p.1 p.2)
        (Dist.prod T S') from rfl]
    exact PFunDDS.maxAdvantage_par_fixed_right_le _hS.nonNeg hT.nonNeg S' hS'
  · rw [show T.par S' = Dist.fTransform
        (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => PFunDDS.par p.1 p.2)
        (Dist.prod T S') from rfl,
      show T.par T' = Dist.fTransform
        (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => PFunDDS.par p.1 p.2)
        (Dist.prod T T') from rfl]
    exact PFunDDS.maxAdvantage_par_fixed_left_le T hT hS'.nonNeg _hT'.nonNeg

/-- The distinguisher metric is symmetric **for probability systems**
(the verdict-flipped distinguisher).  The hypotheses are necessary:
thesis Def 2.4 notes that at different weights the statistical distance
— hence the advantage — is not symmetric. -/
theorem maxAdvantage_comm {S T : PFunPDS X Y}
    (hS : S.isProbDist) (hT : T.isProbDist) :
    Δ(S, T) = Δ(T, S) := by
  -- the one-sided swap, for arbitrary probability systems
  have swap : ∀ A B : PFunPDS X Y, A.isProbDist → B.isProbDist →
      Δ(B, A) ≤ Δ(A, B) := by
    intro A B hA hB
    refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
    classical
    -- a query budget beyond every verdict witness on the supports
    obtain ⟨q, hq⟩ : ∃ q : ℕ, ∀ d ∈ D.support, ∀ s ∈ A.support ∪ B.support,
        ∀ hv : PFunDDS.verdict d s, Nat.find hv < q := by
      refine ⟨(D.support ×ˢ (A.support ∪ B.support)).sup
        (fun p => if h : PFunDDS.verdict p.1 p.2 then Nat.find h + 1 else 0),
        fun d hd s hs hv => ?_⟩
      have hmem : (d, s) ∈ D.support ×ˢ (A.support ∪ B.support) :=
        Finset.mem_product.mpr ⟨hd, hs⟩
      have hle := Finset.le_sup (f := fun p =>
          if h : PFunDDS.verdict p.1 p.2 then Nat.find h + 1 else 0) hmem
      dsimp only at hle
      rw [dif_pos hv] at hle
      omega
    set D' := Dist.fTransform (PFunDDS.truncDDD q) D with hD'def
    set E := Dist.fTransform (fun d => PFunDDS.flipDDD (PFunDDS.truncDDD q d)) D
      with hEdef
    -- truncation changes no verdict probability on the supports
    have htr : ∀ R : PFunPDS X Y, R.support ⊆ A.support ∪ B.support →
        verdictProb D' R = verdictProb D R := by
      intro R hR
      unfold verdictProb
      rw [hD'def, winProb_fTransform_left]
      refine GamePerf.winProb_congr_support D R fun d hd s hs => ?_
      exact ⟨PFunDDS.verdict_of_verdict_truncDDD,
        fun hv => PFunDDS.verdict_truncDDD_of_lt (hq d hd s (hR hs) hv)
          (Nat.find_spec hv)⟩
    -- the flip complements the truncated verdict probability
    have hcompl : ∀ R : PFunPDS X Y, R.isProbDist →
        (verdictProb E R : ℝ) = 1 - (verdictProb D' R : ℝ) := by
      intro R hR
      have h1 : verdictProb E R + verdictProb D' R = D.weight * R.weight := by
        unfold verdictProb
        rw [hEdef, hD'def, winProb_fTransform_left, winProb_fTransform_left,
          GamePerf.winProb_congr_left D R
            (fun d _ s => PFunDDS.verdict_flipDDD_truncDDD_iff q d s),
          add_comm]
        exact GamePerf.winProb_add_compl
          (fun d s => PFunDDS.verdict (PFunDDS.truncDDD q d) s) D R
      have h1' : (verdictProb E R : ℝ) + (verdictProb D' R : ℝ) = 1 := by
        have := h1
        rw [hD.weight_eq, hR.weight_eq] at this
        simpa using this
      linarith
    -- the flipped truncation swaps the advantage
    have hEp : E.isProbDist := Dist.fTransform_isProbDist _ hD
    have hswap : advantage D B A = advantage E A B := by
      unfold advantage
      rw [hcompl A hA, hcompl B hB,
        htr A Finset.subset_union_left, htr B Finset.subset_union_right]
      ring
    rw [hswap]
    exact advantage_le_maxAdvantage E A B hEp
  exact le_antisymm (swap T S hT hS) (swap S T hS hT)

/-- For probability systems the advantage is at most `1`. -/
theorem maxAdvantage_le_one {S T : PFunPDS X Y}
    (_hS : S.isProbDist) (hT : T.isProbDist) :
    Δ(S, T) ≤ 1 := by
  apply Real.sSup_le _ zero_le_one
  rintro x ⟨D, hD, rfl⟩
  have h1 : verdictProb D T ≤ T.weight :=
    GamePerf.winProb_le_weight PFunDDS.verdict D hD hT.nonNeg
  have h1' : (verdictProb D T : ℝ) ≤ 1 := by
    calc (verdictProb D T : ℝ) ≤ (T.weight : ℝ) := h1
    _ = 1 := hT.weight_eq
  have h0 : (0 : ℝ) ≤ (verdictProb D S : ℝ) :=
    GamePerf.winProb_nonneg _ hD.nonNeg _hS.nonNeg
  unfold advantage
  linarith

/-- The immediate-reject distinguisher's verdict ignores the system, so
its advantage vanishes. -/
theorem advantage_rejectDistinguisher (S T : PFunPDS X Y) :
    advantage (rejectDistinguisher X Y) S T = 0 := by
  have hfalse : ∀ s : PFunDDS.DDS X Y,
      ¬ PFunDDS.verdict (PFunDDS.rejectDDD X Y) s := by
    rintro s ⟨n, hn⟩
    exact Bool.noConfusion (Sum.inr.inj hn)
  have hzero : ∀ R : PFunPDS X Y,
      verdictProb (rejectDistinguisher X Y) R = 0 := by
    intro R
    unfold verdictProb GamePerf.winProb rejectDistinguisher
    rw [Finsupp.sum_single_index (by simp)]
    rw [Finsupp.sum]
    exact Finset.sum_eq_zero fun s _ => by
      rw [if_neg (hfalse s), mul_zero]
  unfold advantage
  rw [hzero S, hzero T]
  simp

/-- fn. 13: pseudo-metrics are `ℝ⁺`-valued — the advantage is
nonnegative (witnessed by the immediate-reject distinguisher). -/
theorem maxAdvantage_nonneg (S T : PFunPDS X Y) : 0 ≤ Δ(S, T) := by
  calc (0 : ℝ) = advantage (rejectDistinguisher X Y) S T :=
        (advantage_rejectDistinguisher S T).symm
    _ ≤ Δ(S, T) := le_csSup (bddAbove_advantage_image S T)
        ⟨_, rejectDistinguisher_isProbDist X Y, rfl⟩

/-- The diagonal of the distinguisher metric vanishes. -/
theorem maxAdvantage_self (S : PFunPDS X Y) : Δ(S, S) = 0 :=
  le_antisymm (maxAdvantage_self_le_zero S) (maxAdvantage_nonneg S S)

/-! ### Congruence of the operations with equivalence -/

/-- Converter application preserves equivalence: the environment
absorbs the converter (`⟨E, αS⟩ ≡ ⟨αᵀE, S⟩`, DESIGN §10.5's
transcript-law factorization).  The metric detour is unavailable here:
by thesis Def 2.4's weight-sensitivity, zero distance does not recover
equivalence at sub-distribution generality. -/
@[rs_rule "rs.emulable.congr" equivalence random_systems]
theorem equivalent_apply (α : PFunConverter.ProtocolFn U V X Y)
    {S T : PFunPDS X Y} (hab : PFunConverter.Emulable α)
    (h : Equivalent S T) :
    Equivalent (PFunPDS.apply α S) (PFunPDS.apply α T) := by
  intro e n
  obtain ⟨e', m, g, hg⟩ := hab e n
  rw [show PFunPDS.apply α S
      = Dist.fTransform (fun s => PFunConverter.apply α s) S from rfl,
    show PFunPDS.apply α T
      = Dist.fTransform (fun s => PFunConverter.apply α s) T from rfl,
    PFunConverter.transcriptDist_fTransform_of_transcript_eq hg S,
    PFunConverter.transcriptDist_fTransform_of_transcript_eq hg T,
    h e' m]

/-- Parallel composition preserves equivalence (fn. 20): an environment
of the composition induces environments of the components. -/
theorem equivalent_par {S S' : PFunPDS X Y} {T T' : PFunPDS X' Y'}
    (hS : Equivalent S S') (hT : Equivalent T T') :
    Equivalent (S.par T) (S'.par T') := by
  intro e n
  rw [show S.par T = Dist.fTransform
      (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => PFunDDS.par p.1 p.2)
      (Dist.prod S T) from rfl,
    show S'.par T' = Dist.fTransform
      (fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' => PFunDDS.par p.1 p.2)
      (Dist.prod S' T') from rfl]
  exact (PFunDDS.transcriptDist_par_congr_left T hS e n).trans
    (PFunDDS.transcriptDist_par_congr_right S' hT e n)

/-! ### One-sided decoupling of the parallel composition

On all-left histories the right-hand guard of `par` is vacuous, so the
`⊥`-totalization of `s‖u` answers exactly as the relabeled totalization
of `s` — independently of `u`.  (Mirror lemmas for the right side.)
This is what lets a single-interface environment interrogate one
component of a composition. -/

namespace PFunDDS

variable {X Y X' Y' : Type*}

/-- On an all-left nonempty history, `s‖u` is the relabeled `s`. -/
theorem par_map_inl (s : DDS X Y) (u : DDS X' Y') {l : List X}
    (hl : l ≠ []) :
    (par s u).1 (l.map Sum.inl) = (s.1 l).map Sum.inl := by
  have hleft : (l.map (Sum.inl : X → X ⊕ X')).filterMap Sum.getLeft? = l := by
    simp [List.filterMap_map]
  have hright : (l.map (Sum.inl : X → X ⊕ X')).filterMap Sum.getRight?
      = ([] : List X') := by
    simp [List.filterMap_map]
  have hlast : (l.map (Sum.inl : X → X ⊕ X')).getLast?
      = some (Sum.inl (l.getLast hl)) := by
    rw [List.getLast?_map, List.getLast?_eq_some_getLast hl, Option.map_some]
  show Part.assert _ _ = _
  apply Part.ext
  intro v
  simp only [Part.mem_assert_iff, hleft, hright, hlast]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    have hdom : (s.1 l).Dom := by
      have hmap : ((s.1 l).map Sum.inl).Dom := Part.dom_iff_mem.mpr ⟨v, h⟩
      exact hmap
    exact ⟨fun _ => hdom, fun h' => absurd rfl h', h⟩

/-- The kept prefix of `s‖u` along an all-left history is the relabeled
kept prefix of `s`. -/
theorem keptPrefix_par_map_inl (s : DDS X Y) (u : DDS X' Y') (l : List X) :
    keptPrefix (par s u) (l.map Sum.inl) = (keptPrefix s l).map Sum.inl := by
  classical
  unfold keptPrefix
  suffices h : ∀ acc : List X,
      List.foldl (fun acc x => if acc ++ [x] ∈ dom (par s u)
          then acc ++ [x] else acc) (acc.map Sum.inl) (l.map Sum.inl)
        = (List.foldl (fun acc x => if acc ++ [x] ∈ dom s
            then acc ++ [x] else acc) acc l).map Sum.inl by
    simpa using h []
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hmap : acc.map Sum.inl ++ [Sum.inl x]
          = (acc ++ [x]).map (Sum.inl : X → X ⊕ X') := by simp
      have hdom : acc.map Sum.inl ++ [Sum.inl x] ∈ dom (par s u)
          ↔ acc ++ [x] ∈ dom s := by
        rw [hmap]
        show ((par s u).1 _).Dom ↔ (s.1 (acc ++ [x])).Dom
        rw [par_map_inl s u (by simp)]
        exact Iff.rfl
      by_cases hd : acc ++ [x] ∈ dom s
      · rw [if_pos (hdom.mpr hd), if_pos hd, hmap]
        exact ih (acc ++ [x])
      · rw [if_neg (fun hc => hd (hdom.mp hc)), if_neg hd]
        exact ih acc

/-- The `⊥`-totalization of `s‖u` on an all-left history answers as the
relabeled totalization of `s` — independently of `u`. -/
theorem output_fullyDefined_par_map_inl (s : DDS X Y) (u : DDS X' Y')
    {l : List X} (hl : l ≠ []) :
    output (fullyDefined (par s u)) (l.map Sum.inl)
        (by rw [dom_fullyDefined]; simpa using hl)
      = (output (fullyDefined s) l
          (by rw [dom_fullyDefined]; exact hl)).map Sum.inl := by
  rw [output_fullyDefined, output_fullyDefined]
  dsimp only
  have hdrop : (l.map (Sum.inl : X → X ⊕ X')).dropLast
      = l.dropLast.map Sum.inl := (List.map_dropLast ..).symm
  have hlastl : (l.map (Sum.inl : X → X ⊕ X')).getLast (by simpa using hl)
      = Sum.inl (l.getLast hl) := List.getLast_map ..
  have hcand : keptPrefix (par s u) (l.map Sum.inl).dropLast
        ++ [(l.map (Sum.inl : X → X ⊕ X')).getLast (by simpa using hl)]
      = (keptPrefix s l.dropLast ++ [l.getLast hl]).map Sum.inl := by
    rw [hdrop, keptPrefix_par_map_inl, hlastl, List.map_append, List.map_cons,
      List.map_nil]
  have hdomiff : keptPrefix (par s u) (l.map Sum.inl).dropLast
        ++ [(l.map (Sum.inl : X → X ⊕ X')).getLast (by simpa using hl)]
        ∈ dom (par s u)
      ↔ keptPrefix s l.dropLast ++ [l.getLast hl] ∈ dom s := by
    rw [hcand]
    show ((par s u).1 _).Dom ↔ (s.1 _).Dom
    rw [par_map_inl s u (by simp)]
    exact Iff.rfl
  by_cases hd : keptPrefix s l.dropLast ++ [l.getLast hl] ∈ dom s
  · rw [dif_pos hd, dif_pos (hdomiff.mpr hd), Option.map_some]
    refine congrArg some ?_
    refine (output_congr (par s u) hcand _ ?_).trans ?_
    · show ((par s u).1 _).Dom
      rw [par_map_inl s u (by simp)]
      exact hd
    · apply Part.get_eq_of_mem
      rw [par_map_inl s u (by simp)]
      exact Part.mem_map _ (Part.get_mem _)
  · rw [dif_neg hd, dif_neg (fun hc => hd (hdomiff.mp hc))]
    rfl

/-- On an all-right nonempty history, `s‖u` is the relabeled `u`. -/
theorem par_map_inr (s : DDS X Y) (u : DDS X' Y') {l : List X'}
    (hl : l ≠ []) :
    (par s u).1 (l.map Sum.inr) = (u.1 l).map Sum.inr := by
  have hleft : (l.map (Sum.inr : X' → X ⊕ X')).filterMap Sum.getLeft?
      = ([] : List X) := by
    simp [List.filterMap_map]
  have hright : (l.map (Sum.inr : X' → X ⊕ X')).filterMap Sum.getRight? = l := by
    simp [List.filterMap_map]
  have hlast : (l.map (Sum.inr : X' → X ⊕ X')).getLast?
      = some (Sum.inr (l.getLast hl)) := by
    rw [List.getLast?_map, List.getLast?_eq_some_getLast hl, Option.map_some]
  show Part.assert _ _ = _
  apply Part.ext
  intro v
  simp only [Part.mem_assert_iff, hleft, hright, hlast]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    have hdom : (u.1 l).Dom := by
      have hmap : ((u.1 l).map Sum.inr).Dom := Part.dom_iff_mem.mpr ⟨v, h⟩
      exact hmap
    exact ⟨fun h' => absurd rfl h', fun _ => hdom, h⟩

/-- The kept prefix of `s‖u` along an all-right history is the relabeled
kept prefix of `u`. -/
theorem keptPrefix_par_map_inr (s : DDS X Y) (u : DDS X' Y') (l : List X') :
    keptPrefix (par s u) (l.map Sum.inr) = (keptPrefix u l).map Sum.inr := by
  classical
  unfold keptPrefix
  suffices h : ∀ acc : List X',
      List.foldl (fun acc x => if acc ++ [x] ∈ dom (par s u)
          then acc ++ [x] else acc) (acc.map Sum.inr) (l.map Sum.inr)
        = (List.foldl (fun acc x => if acc ++ [x] ∈ dom u
            then acc ++ [x] else acc) acc l).map Sum.inr by
    simpa using h []
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hmap : acc.map Sum.inr ++ [Sum.inr x]
          = (acc ++ [x]).map (Sum.inr : X' → X ⊕ X') := by simp
      have hdom : acc.map Sum.inr ++ [Sum.inr x] ∈ dom (par s u)
          ↔ acc ++ [x] ∈ dom u := by
        rw [hmap]
        show ((par s u).1 _).Dom ↔ (u.1 (acc ++ [x])).Dom
        rw [par_map_inr s u (by simp)]
        exact Iff.rfl
      by_cases hd : acc ++ [x] ∈ dom u
      · rw [if_pos (hdom.mpr hd), if_pos hd, hmap]
        exact ih (acc ++ [x])
      · rw [if_neg (fun hc => hd (hdom.mp hc)), if_neg hd]
        exact ih acc

/-- The `⊥`-totalization of `s‖u` on an all-right history answers as the
relabeled totalization of `u` — independently of `s`. -/
theorem output_fullyDefined_par_map_inr (s : DDS X Y) (u : DDS X' Y')
    {l : List X'} (hl : l ≠ []) :
    output (fullyDefined (par s u)) (l.map Sum.inr)
        (by rw [dom_fullyDefined]; simpa using hl)
      = (output (fullyDefined u) l
          (by rw [dom_fullyDefined]; exact hl)).map Sum.inr := by
  rw [output_fullyDefined, output_fullyDefined]
  dsimp only
  have hdrop : (l.map (Sum.inr : X' → X ⊕ X')).dropLast
      = l.dropLast.map Sum.inr := (List.map_dropLast ..).symm
  have hlastl : (l.map (Sum.inr : X' → X ⊕ X')).getLast (by simpa using hl)
      = Sum.inr (l.getLast hl) := List.getLast_map ..
  have hcand : keptPrefix (par s u) (l.map Sum.inr).dropLast
        ++ [(l.map (Sum.inr : X' → X ⊕ X')).getLast (by simpa using hl)]
      = (keptPrefix u l.dropLast ++ [l.getLast hl]).map Sum.inr := by
    rw [hdrop, keptPrefix_par_map_inr, hlastl, List.map_append, List.map_cons,
      List.map_nil]
  have hdomiff : keptPrefix (par s u) (l.map Sum.inr).dropLast
        ++ [(l.map (Sum.inr : X' → X ⊕ X')).getLast (by simpa using hl)]
        ∈ dom (par s u)
      ↔ keptPrefix u l.dropLast ++ [l.getLast hl] ∈ dom u := by
    rw [hcand]
    show ((par s u).1 _).Dom ↔ (u.1 _).Dom
    rw [par_map_inr s u (by simp)]
    exact Iff.rfl
  by_cases hd : keptPrefix u l.dropLast ++ [l.getLast hl] ∈ dom u
  · rw [dif_pos hd, dif_pos (hdomiff.mpr hd), Option.map_some]
    refine congrArg some ?_
    refine (output_congr (par s u) hcand _ ?_).trans ?_
    · show ((par s u).1 _).Dom
      rw [par_map_inr s u (by simp)]
      exact hd
    · apply Part.get_eq_of_mem
      rw [par_map_inr s u (by simp)]
      exact Part.mem_map _ (Part.get_mem _)
  · rw [dif_neg hd, dif_neg (fun hc => hd (hdomiff.mp hc))]
    rfl

/-- A left environment, embedded at the composition's interface: project
the answers to the left alphabet, relabel the queries. -/
def embedDDEInl (e : DDE X Y) : DDE (X ⊕ X') (Y ⊕ Y') := fun ys =>
  (e (ys.map fun oy => oy.bind Sum.getLeft?)).map Sum.inl

/-- A right environment, embedded at the composition's interface. -/
def embedDDEInr (e : DDE X' Y') : DDE (X ⊕ X') (Y ⊕ Y') := fun ys =>
  (e (ys.map fun oy => oy.bind Sum.getRight?)).map Sum.inr

/-- Under an embedded left environment, the transcript of `s‖u` is the
relabeled transcript of `s` — for every `u`. -/
theorem transcript_par_embedDDEInl (s : DDS X Y) (u : DDS X' Y')
    (e : DDE X Y) (n : ℕ) :
    transcript (par s u) (embedDDEInl (X' := X') (Y' := Y') e) n
      = (transcript s e n).map
          fun p => ((Sum.inl p.1 : X ⊕ X'), p.2.map Sum.inl) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hbind : ∀ oy : Option Y,
          (oy.map (Sum.inl : Y → Y ⊕ Y')).bind Sum.getLeft? = oy := by
        rintro (_ | y) <;> rfl
      have henv : embedDDEInl (X' := X') (Y' := Y') e
          ((transcript (par s u) (embedDDEInl e) n)↓ᵧ)
          = (e ((transcript s e n)↓ᵧ)).map Sum.inl := by
        rw [ih]
        unfold embedDDEInl
        congr 1
        simp [transcriptOutputs, List.map_map, Function.comp_def, hbind]
      rcases he : e ((transcript s e n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall (by rw [henv, he]; rfl),
          transcript_succ_stall he, ih]
      · rw [transcript_succ_fire (x := Sum.inl x) (by rw [henv, he]; rfl),
          transcript_succ_fire he, ih, List.map_append]
        congr 1
        have hinp : ((transcript s e n).map
            fun p => ((Sum.inl p.1 : X ⊕ X'),
              (p.2.map Sum.inl : Option (Y ⊕ Y'))))↓ₓ
              ++ [Sum.inl x]
            = ((transcript s e n)↓ₓ ++ [x]).map Sum.inl := by
          simp [transcriptInputs, List.map_map, Function.comp_def]
        refine congrArg (fun o => [((Sum.inl x : X ⊕ X'), o)]) ?_
        refine (output_congr (fullyDefined (par s u)) hinp _ ?_).trans ?_
        · rw [dom_fullyDefined]
          simp
        · exact output_fullyDefined_par_map_inl s u (by simp)

/-- Under an embedded right environment, the transcript of `s‖u` is the
relabeled transcript of `u` — for every `s`. -/
theorem transcript_par_embedDDEInr (s : DDS X Y) (u : DDS X' Y')
    (e : DDE X' Y') (n : ℕ) :
    transcript (par s u) (embedDDEInr (X := X) (Y := Y) e) n
      = (transcript u e n).map
          fun p => ((Sum.inr p.1 : X ⊕ X'), p.2.map Sum.inr) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hbind : ∀ oy : Option Y',
          (oy.map (Sum.inr : Y' → Y ⊕ Y')).bind Sum.getRight? = oy := by
        rintro (_ | y) <;> rfl
      have henv : embedDDEInr (X := X) (Y := Y) e
          ((transcript (par s u) (embedDDEInr e) n)↓ᵧ)
          = (e ((transcript u e n)↓ᵧ)).map Sum.inr := by
        rw [ih]
        unfold embedDDEInr
        congr 1
        simp [transcriptOutputs, List.map_map, Function.comp_def, hbind]
      rcases he : e ((transcript u e n)↓ᵧ) with _ | x
      · rw [transcript_succ_stall (by rw [henv, he]; rfl),
          transcript_succ_stall he, ih]
      · rw [transcript_succ_fire (x := Sum.inr x) (by rw [henv, he]; rfl),
          transcript_succ_fire he, ih, List.map_append]
        congr 1
        have hinp : ((transcript u e n).map
            fun p => ((Sum.inr p.1 : X ⊕ X'),
              (p.2.map Sum.inr : Option (Y ⊕ Y'))))↓ₓ
              ++ [Sum.inr x]
            = ((transcript u e n)↓ₓ ++ [x]).map Sum.inr := by
          simp [transcriptInputs, List.map_map, Function.comp_def]
        refine congrArg (fun o => [((Sum.inr x : X ⊕ X'), o)]) ?_
        refine (output_congr (fullyDefined (par s u)) hinp _ ?_).trans ?_
        · rw [dom_fullyDefined]
          simp
        · exact output_fullyDefined_par_map_inr s u (by simp)

end PFunDDS

/-! ### Recovery of the components of a parallel composition -/

/-- Pushforward commutes with scaling. -/
theorem fTransform_smul {A B : Type*} (f : A → B) (c : ℝ)
    (v : Dist A) :
    Dist.fTransform f (c • v) = c • Dist.fTransform f v := by
  show Finsupp.mapDomain f (c • v) = c • Finsupp.mapDomain f v
  rw [Finsupp.mapDomain_smul]

/-- The transcript distribution is linear in the system. -/
theorem transcriptDist_smul (c : ℝ) (S : PFunPDS X Y)
    (e : PFunDDS.DDE X Y) (n : ℕ) :
    transcriptDist (c • S) e n = c • transcriptDist S e n :=
  fTransform_smul _ c S

/-- A nonzero non-negative sub-distribution has positive weight. -/
theorem weight_pos_of_ne_zero {A : Type*} {R : Dist A}
    (hRnn : R.NonNeg) (hR : R ≠ 0) :
    0 < R.weight := by
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hR
  have ha' : R a ≠ 0 := by simpa using ha
  have hle : R a ≤ R.weight := by
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.single_le_sum (fun a' _ => hRnn a')
      (Finsupp.mem_support_iff.mpr ha')
  exact lt_of_lt_of_le (lt_of_le_of_ne (hRnn a) (Ne.symm ha')) hle

/-- Marginal of a pushforward through the first component: the other
factor contributes its weight.  (`Fintype`-free, via `mass_prod_and`;
distinct from `Theorem417.fTransform_fst_prod`, its probability-weight
special case.) -/
theorem fTransform_fst_prod_smul {A B C : Type*} (f : A → C)
    (S : Dist A) (T : Dist B) :
    Dist.fTransform (fun p : A × B => f p.1) (Dist.prod S T)
      = T.weight • Dist.fTransform f S := by
  refine Finsupp.ext fun c => ?_
  rw [Dist.fTransform_apply_eq_mass, Finsupp.smul_apply,
    Dist.fTransform_apply_eq_mass, smul_eq_mul]
  have hP : (Dist.prod S T).mass (fun p => f p.1 = c)
      = (Dist.prod S T).mass
          (fun p => (fun a => f a = c) p.1 ∧ (fun _ : B => True) p.2) :=
    congrArg _ (funext fun p => propext (by simp))
  rw [hP, Dist.mass_prod_and S T (fun a => f a = c) (fun _ : B => True),
    Dist.mass_true, mul_comm]

/-- Marginal of a pushforward through the second component. -/
theorem fTransform_snd_prod_smul {A B C : Type*} (f : B → C)
    (S : Dist A) (T : Dist B) :
    Dist.fTransform (fun p : A × B => f p.2) (Dist.prod S T)
      = S.weight • Dist.fTransform f T := by
  refine Finsupp.ext fun c => ?_
  rw [Dist.fTransform_apply_eq_mass, Finsupp.smul_apply,
    Dist.fTransform_apply_eq_mass, smul_eq_mul]
  have hP : (Dist.prod S T).mass (fun p => f p.2 = c)
      = (Dist.prod S T).mass
          (fun p => (fun _ : A => True) p.1 ∧ (fun b => f b = c) p.2) :=
    congrArg _ (funext fun p => propext (by simp))
  rw [hP, Dist.mass_prod_and S T (fun _ : A => True) (fun b => f b = c),
    Dist.mass_true]

/-- One-sided marginal extraction: under an embedded left environment,
the composition's transcript distribution is the relabeled left
transcript distribution, scaled by the right weight. -/
theorem transcriptDist_par_embedDDEInl (S : PFunPDS X Y) (T : PFunPDS X' Y')
    (e : PFunDDS.DDE X Y) (n : ℕ) :
    transcriptDist (S.par T) (PFunDDS.embedDDEInl e) n
      = T.weight • Dist.fTransform
          (List.map fun p : X × Option Y =>
            ((Sum.inl p.1 : X ⊕ X'), (p.2.map Sum.inl : Option (Y ⊕ Y'))))
          (transcriptDist S e n) := by
  unfold transcriptDist PFunPDS.par
  rw [Dist.fTransform_comp, Dist.fTransform_comp,
    show ((fun w => PFunDDS.transcript w (PFunDDS.embedDDEInl e) n)
        ∘ fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
          PFunDDS.par p.1 p.2)
      = fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
          List.map (fun q : X × Option Y => ((Sum.inl q.1 : X ⊕ X'),
            (q.2.map Sum.inl : Option (Y ⊕ Y'))))
            (PFunDDS.transcript p.1 e n) from
      funext fun p => PFunDDS.transcript_par_embedDDEInl p.1 p.2 e n]
  exact fTransform_fst_prod_smul
    (fun s => List.map (fun q : X × Option Y => ((Sum.inl q.1 : X ⊕ X'),
      (q.2.map Sum.inl : Option (Y ⊕ Y')))) (PFunDDS.transcript s e n)) S T

/-- One-sided marginal extraction, right side. -/
theorem transcriptDist_par_embedDDEInr (S : PFunPDS X Y) (T : PFunPDS X' Y')
    (e : PFunDDS.DDE X' Y') (n : ℕ) :
    transcriptDist (S.par T) (PFunDDS.embedDDEInr e) n
      = S.weight • Dist.fTransform
          (List.map fun p : X' × Option Y' =>
            ((Sum.inr p.1 : X ⊕ X'), (p.2.map Sum.inr : Option (Y ⊕ Y'))))
          (transcriptDist T e n) := by
  unfold transcriptDist PFunPDS.par
  rw [Dist.fTransform_comp, Dist.fTransform_comp,
    show ((fun w => PFunDDS.transcript w (PFunDDS.embedDDEInr e) n)
        ∘ fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
          PFunDDS.par p.1 p.2)
      = fun p : PFunDDS.DDS X Y × PFunDDS.DDS X' Y' =>
          List.map (fun q : X' × Option Y' => ((Sum.inr q.1 : X ⊕ X'),
            (q.2.map Sum.inr : Option (Y ⊕ Y'))))
            (PFunDDS.transcript p.2 e n) from
      funext fun p => PFunDDS.transcript_par_embedDDEInr p.1 p.2 e n]
  exact fTransform_snd_prod_smul
    (fun u => List.map (fun q : X' × Option Y' => ((Sum.inr q.1 : X ⊕ X'),
      (q.2.map Sum.inr : Option (Y ⊕ Y')))) (PFunDDS.transcript u e n)) S T

/-- The components of a parallel composition are recoverable
behaviorally, **up to scaling**: an environment may interrogate one
side only, recovering each component's behavior scaled by the other's
total weight; and the independent product forgets exactly one scalar
(`prod (c•S) (c⁻¹•T) = prod S T` — thesis Def 2.14's sub-distribution
generality, which LM20 needs for the successor operator).  The
choice-based `parC` of the instantiation survives this ambiguity
because protocol-function actions are `fTransform`s, hence linear, so
the scalar cancels inside `par`.

The nonzero hypotheses are necessary: with `S = 0` both compositions
are the zero distribution regardless of the other components, so a
weight-1 `S'` could never be recovered. -/
theorem equivalent_of_par_equivalent {S S' : PFunPDS X Y}
    {T T' : PFunPDS X' Y'}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (hS'nn : S'.NonNeg) (hT'nn : T'.NonNeg)
    (hS : S ≠ 0) (hT : T ≠ 0)
    (h : Equivalent (S.par T) (S'.par T')) :
    ∃ c : ℝ, 0 < c ∧
      Equivalent S' (c • S) ∧ Equivalent (c • T') T := by
  have hSw : 0 < S.weight := weight_pos_of_ne_zero hSnn hS
  have hTw : 0 < T.weight := weight_pos_of_ne_zero hTnn hT
  -- the composition weights agree
  have hweq : S.weight * T.weight = S'.weight * T'.weight := by
    have hw := congrArg Dist.weight (h (fun _ => none) 0)
    simpa [transcriptDist, Dist.weight_fTransform, PFunPDS.par,
      Dist.weight_prod] using hw
  have hS'w : 0 < S'.weight := by
    rcases eq_or_lt_of_le hS'nn.weight_nonneg with hz | hz
    · exfalso
      rw [← hz, zero_mul] at hweq
      exact absurd hweq (ne_of_gt (mul_pos hSw hTw))
    · exact hz
  have hT'w : 0 < T'.weight := by
    rcases eq_or_lt_of_le hT'nn.weight_nonneg with hz | hz
    · exfalso
      rw [← hz, mul_zero] at hweq
      exact absurd hweq (ne_of_gt (mul_pos hSw hTw))
    · exact hz
  -- left extraction
  have hL : ∀ (e : PFunDDS.DDE X Y) (n : ℕ),
      T.weight • transcriptDist S e n
        = T'.weight • transcriptDist S' e n := by
    intro e n
    have hinj : Function.Injective
        (List.map fun p : X × Option Y =>
          ((Sum.inl p.1 : X ⊕ X'), (p.2.map Sum.inl : Option (Y ⊕ Y')))) :=
      List.map_injective_iff.mpr fun p q hpq => by
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpq
        exact Prod.ext (Sum.inl_injective h1)
          (Option.map_injective Sum.inl_injective h2)
    have hh := h (PFunDDS.embedDDEInl e) n
    rw [transcriptDist_par_embedDDEInl, transcriptDist_par_embedDDEInl,
      ← fTransform_smul, ← fTransform_smul] at hh
    exact Finsupp.mapDomain_injective hinj hh
  -- right extraction
  have hR : ∀ (e : PFunDDS.DDE X' Y') (n : ℕ),
      S.weight • transcriptDist T e n
        = S'.weight • transcriptDist T' e n := by
    intro e n
    have hinj : Function.Injective
        (List.map fun p : X' × Option Y' =>
          ((Sum.inr p.1 : X ⊕ X'), (p.2.map Sum.inr : Option (Y ⊕ Y')))) :=
      List.map_injective_iff.mpr fun p q hpq => by
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpq
        exact Prod.ext (Sum.inr_injective h1)
          (Option.map_injective Sum.inr_injective h2)
    have hh := h (PFunDDS.embedDDEInr e) n
    rw [transcriptDist_par_embedDDEInr, transcriptDist_par_embedDDEInr,
      ← fTransform_smul, ← fTransform_smul] at hh
    exact Finsupp.mapDomain_injective hinj hh
  refine ⟨T.weight / T'.weight, div_pos hTw hT'w, ?_, ?_⟩
  · intro e n
    rw [transcriptDist_smul]
    have h1 := congrArg (fun d => (T'.weight)⁻¹ • d) (hL e n)
    simp only [smul_smul] at h1
    rw [inv_mul_cancel₀ (ne_of_gt hT'w), one_smul] at h1
    rw [← h1]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  · intro e n
    rw [transcriptDist_smul]
    have h1 := congrArg (fun d => (S'.weight)⁻¹ • d) (hR e n)
    simp only [smul_smul] at h1
    rw [inv_mul_cancel₀ (ne_of_gt hS'w), one_smul] at h1
    have hc1 : T.weight / T'.weight * (S'.weight⁻¹ * S.weight) = 1 := by
      rw [mul_comm S'.weight⁻¹ S.weight, ← div_eq_mul_inv, div_mul_div_comm,
        mul_comm T.weight S.weight, hweq, mul_comm T'.weight S'.weight,
        div_self (ne_of_gt (mul_pos hS'w hT'w))]
    rw [← h1, smul_smul, hc1, one_smul]

end RandomSystems.CR18
