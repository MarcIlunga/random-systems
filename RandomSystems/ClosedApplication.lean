/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization

/-!
# Closed-form application of budgeted step converters

Converter application in this library is a **fuel-indexed iteration followed by
a limit**: `PFunConverter.applyRaw α S = eventual (fun fuel => applyRawAt α S
fuel …)`, with `drive`/`driveOuter` recursing on the fuel.  Nothing about a
general `α` computes, so every law about `apply` is re-derived by a fuel
induction.  The one closed form in the tree is the *non-interactive* case,
`PFunConverter.DDC.simple_apply` — `d ∘ S ∘ map c`, domains included.

This file generalizes that to **interactive** converters with a bounded,
exactly-known per-round call count: `ofHistoryStepPartial step cnt` (and its
never-silent instance `ofHistoryStep step cnt`), whose boundary condition says
that a round makes exactly `cnt us` inner calls whenever it moves at all.  For
those, application is a *finite composite*, by structural recursion on the
budget:

* `roundRun` — recursion on the remaining budget `n`: consult `step`, take the
  issued query, append `S⊥`'s answer, `n` times.
* `roundOut` — run the whole budget `cnt us`, then read the closing outer answer
  off `step`.
* `outerRun` — a fold over the outer history threading the inner history, one
  `roundOut` per outer message.
* `closedAnswer` — the applied system's answer: the last outer answer of the
  fold.

`applyRaw_ofHistoryStepPartial` / `apply_ofHistoryStepPartial_val` /
`apply_ofHistoryStep_val` are the closed form; no fixed point, no fuel, and no
`eventual` on the right-hand side.

### The two design decisions

**Partiality.**  `S⊥` answers `⊥` off `dom S`, so a round can stall part-way;
`ofHistoryStepPartial`'s `step` may also decline to move.  Both are recorded as
`Option`, and the statement is `Part.ofOption`-valued: `Part.ofOption none =
Part.none` is *exactly* where the applied system is undefined, so the closed
form is unconditional — **no totality hypothesis on `S`**.  (This is the
stronger choice: the library's `KStepTotal`/`TotalOnNonempty` live on the
probabilistic carrier `PFunPDS`, not on `PFunDDS.DDS`, so a totality hypothesis
here would have to be the inline `∀ l ≠ [], l ∈ dom S` of
`PFunDDS.eq_historyEvaluator_of_total`; a caller who has it discharges the
`Option` locally with `sysAnswer_of_ne_nil`, and loses nothing.)

**Formulation.**  The equation is about `PFunConverter.applyRaw` / the raw
function of `PFunConverter.apply` *directly*, at a fixed outer history — so a
caller computes `apply α S us` without ever mentioning `fuel`, and without
routing through `CausalApply.applyG` or any other bridge.

### What is load-bearing

The boundary condition `hcnt` is not decoration.  `ofHistoryStepPartial` locates
the open round's answer segment by the *arithmetic* offset `roundOffset cnt us`,
computed from `cnt` alone; only `hcnt` makes the actual number of queries a
round issues agree with `cnt us`, and hence makes that offset point at the
round's own answers.  It is exactly what turns the fuel recursion into a
structural recursion on `cnt us`.

The fuel bound is per-history and needs no uniform ceiling on `cnt`: for the
outer history `us`, any `fuel > Σ_{vs <+: us} cnt vs` runs every round to
completion.  (Contrast `EmulateRealization.applyRaw_dom`, which needs a uniform
`AnswersWithin` bound, proves only definedness, and exposes no fuel.)

`simple_apply_of_closedAnswer` is the receipt: `PFunConverter.DDC.simple_apply`'s
statement, re-derived from the closed form at the memoryless `cnt ≡ 1` instance.
-/

namespace RandomSystems.CR18

namespace PFunConverter.ProtocolFn

open scoped PFunDDS

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- **One round, by structural recursion on the remaining budget** `n`: consult
`step` on the answers `seg` collected so far, take the issued query, append the
Def 3.3 completion's answer to both histories, repeat.  `none` is a stall — the
converter went silent, or (under the boundary condition, the only other way)
`S⊥` answered `⊥`; either way the applied system is undefined there.  A closing
`Sum.inr` inside the budget also reads as a stall, which the boundary condition
`hcnt` rules out. -/
noncomputable def roundRun
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (S : PFunDDS.DDS X Y) (us : List U) (hne : us ≠ []) :
    ℕ → List X → List Y → Option (List X × List Y)
  | 0, xs, seg => some (xs, seg)
  | n + 1, xs, seg =>
      ((step us hne seg).bind Sum.getLeft?).bind fun x =>
        (PFunConverter.sysAnswer S (xs ++ [x])).bind fun y =>
          roundRun step S us hne n (xs ++ [x]) (seg ++ [y])

@[simp] theorem roundRun_zero
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (S : PFunDDS.DDS X Y) (us : List U) (hne : us ≠ []) (xs : List X)
    (seg : List Y) :
    roundRun step S us hne 0 xs seg = some (xs, seg) := rfl

theorem roundRun_succ
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (S : PFunDDS.DDS X Y) (us : List U) (hne : us ≠ []) (n : ℕ) (xs : List X)
    (seg : List Y) :
    roundRun step S us hne (n + 1) xs seg =
      ((step us hne seg).bind Sum.getLeft?).bind fun x =>
        (PFunConverter.sysAnswer S (xs ++ [x])).bind fun y =>
          roundRun step S us hne n (xs ++ [x]) (seg ++ [y]) := rfl

/-- Lengths: `n` further queries append `n` inner messages and `n` answers. -/
theorem roundRun_length
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (S : PFunDDS.DDS X Y) (us : List U) (hne : us ≠ []) :
    ∀ (n : ℕ) {xs : List X} {seg : List Y} {r : List X × List Y},
      roundRun step S us hne n xs seg = some r →
        r.1.length = xs.length + n ∧ r.2.length = seg.length + n := by
  intro n
  induction n with
  | zero => intro xs seg r h; cases h; simp
  | succ n ih =>
      intro xs seg r h
      rw [roundRun_succ, Option.bind_eq_some_iff] at h
      obtain ⟨x, -, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨y, -, h⟩ := h
      obtain ⟨h1, h2⟩ := ih h
      simp only [List.length_append, List.length_singleton] at h1 h2
      exact ⟨by omega, by omega⟩

/-- **The round's outcome**: spend the whole budget `cnt us`, then read the
closing outer answer off `step` — the outer answer together with the inner
history the round leaves behind. -/
noncomputable def roundOut
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) (us : List U) (hne : us ≠ [])
    (xs : List X) : Option (V × List X) :=
  (roundRun step S us hne (cnt us) xs []).bind fun p =>
    ((step us hne p.2).bind Sum.getRight?).map fun v => (v, p.1)

/-- A completed round has spent exactly its budget. -/
theorem roundOut_length
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) (us : List U) (hne : us ≠ [])
    {xs : List X} {r : V × List X}
    (h : roundOut step cnt S us hne xs = some r) :
    r.2.length = xs.length + cnt us := by
  rw [roundOut, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, hclose⟩ := h
  have hlen := (roundRun_length step S us hne _ hp).1
  rw [Option.map_eq_some_iff] at hclose
  obtain ⟨v, -, rfl⟩ := hclose
  simpa using hlen

/-- **The outer fold**: one `roundOut` per outer message, threading the inner
history and collecting the outer answers.  `usPre` is the outer prefix already
consumed, so the round opened by `u` is the one at outer history `usPre ++ [u]`
— which is what a history-aware `step` and `cnt` are indexed by. -/
noncomputable def outerRun
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) :
    List U → List U → List X → Option (List V × List X)
  | _, [], xs => some ([], xs)
  | usPre, u :: rest, xs =>
      (roundOut step cnt S (usPre ++ [u]) (by simp) xs).bind fun p =>
        (outerRun step cnt S (usPre ++ [u]) rest p.2).map fun q =>
          (p.1 :: q.1, q.2)

@[simp] theorem outerRun_nil
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) (usPre : List U) (xs : List X) :
    outerRun step cnt S usPre [] xs = some ([], xs) := rfl

theorem outerRun_cons
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) (usPre : List U) (u : U)
    (rest : List U) (xs : List X) :
    outerRun step cnt S usPre (u :: rest) xs =
      (roundOut step cnt S (usPre ++ [u]) (by simp) xs).bind fun p =>
        (outerRun step cnt S (usPre ++ [u]) rest p.2).map fun q =>
          (p.1 :: q.1, q.2) := rfl

/-- **The closed-form answer** of the applied system at an outer history: run
the fold from empty histories and read the last outer answer.  `none` at the
empty history (the applied system, like every DDS, is undefined there). -/
noncomputable def closedAnswer
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) (us : List U) : Option V :=
  (outerRun step cnt S [] us []).bind fun p => p.1.getLast?

/-! ### The round bridge -/

/-- One unrolling of `PFunConverter.drive`, as an equation. -/
private theorem drive_succ (α : PFunConverter.ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) (fuel : ℕ) (us : List U) (xs : List X)
    (ys : List (Option Y)) :
    PFunConverter.drive α S (fuel + 1) us xs ys =
      (α (us, ys)).bind fun m =>
        match m with
        | Sum.inl x =>
            PFunConverter.drive α S fuel us (xs ++ [x])
              (ys ++ [PFunDDS.output (S⊥) (xs ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp)])
        | Sum.inr v => Part.some (v, xs, ys) := rfl

/-- A silent converter kills the drive outright. -/
private theorem drive_eq_none_of_silent (α : PFunConverter.ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) {fuel : ℕ} (hfuel : fuel ≠ 0) {us : List U}
    {xs : List X} {ys : List (Option Y)} (h : α (us, ys) = Part.none) :
    PFunConverter.drive α S fuel us xs ys = Part.none := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  rw [drive_succ, h, Part.bind_none]

/-- The converter's move at a pair whose open segment is proper. -/
private theorem ofHistoryStepPartial_at_segment
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) {ys : List (Option Y)}
    {segY : List Y} (hseg : ys.drop (roundOffset cnt us) = segY.map some) :
    ofHistoryStepPartial step cnt (us, ys) = Part.ofOption (step us hne segY) := by
  rw [ofHistoryStepPartial_apply step cnt hne, hseg, mapM_id_map_some]

/-- …and its silence at a pair whose open segment carries a `⊥`. -/
private theorem ofHistoryStepPartial_eq_none_of_bot
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) {us : List U} (hne : us ≠ []) {ys : List (Option Y)}
    {segY : List Y} (hseg : ys.drop (roundOffset cnt us) = segY.map some ++ [none]) :
    ofHistoryStepPartial step cnt (us, ys) = Part.none := by
  rw [Part.eq_none_iff]
  intro mv hmv
  obtain ⟨ysY, hdrop, -⟩ :=
    (mem_ofHistoryStepPartial_iff step cnt hne ys mv).mp hmv
  rw [hseg] at hdrop
  have : (none : Option Y) ∈ ysY.map some := by
    rw [← hdrop]; simp
  simp at this

/-- **The round, in closed form.**  Inside the round opened at outer history
`us`, with `segY` the answers it has already collected and `n` queries of
budget left, the fuel-indexed `drive` is the `n`-fold `roundRun` composite. -/
private theorem drive_round
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (S : PFunDDS.DDS X Y) {us : List U} (hne : us ≠ []) :
    ∀ (n fuel : ℕ) (xs : List X) (segY : List Y),
      segY.length + n = cnt us →
      roundOffset cnt us + segY.length = xs.length →
      (PFunConverter.sysAnswers S xs).drop (roundOffset cnt us) = segY.map some →
      n < fuel →
      PFunConverter.drive (ofHistoryStepPartial step cnt) S fuel us xs
          (PFunConverter.sysAnswers S xs)
        = Part.ofOption ((roundRun step S us hne n xs segY).bind fun p =>
            ((step us hne p.2).bind Sum.getRight?).map fun v =>
              (v, p.1, PFunConverter.sysAnswers S p.1)) := by
  intro n
  induction n with
  | zero =>
      intro fuel xs segY hbud hlen hseg hf
      obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
      rw [drive_succ, ofHistoryStepPartial_at_segment step cnt hne hseg,
        roundRun_zero, Option.bind_some]
      cases hstep : step us hne segY with
      | none => simp [Part.bind_none]
      | some mv =>
          cases mv with
          | inl x =>
              exact absurd ((hcnt us hne segY _ hstep).mp ⟨x, rfl⟩) (by omega)
          | inr v => simp [Part.bind_some]
  | succ n ih =>
      intro fuel xs segY hbud hlen hseg hf
      obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
      have hltbud : segY.length < cnt us := by omega
      have hoff : roundOffset cnt us ≤ (PFunConverter.sysAnswers S xs).length := by
        rw [PFunConverter.sysAnswers_length]; omega
      rw [drive_succ, ofHistoryStepPartial_at_segment step cnt hne hseg,
        roundRun_succ]
      cases hstep : step us hne segY with
      | none => simp [Part.bind_none]
      | some mv =>
          cases mv with
          | inr v =>
              exact absurd ((hcnt us hne segY _ hstep).mpr hltbud) (by simp)
          | inl x =>
              rw [show (Part.ofOption (some (Sum.inl x)) : Part (X ⊕ V))
                  = Part.some (Sum.inl x) from rfl, Part.bind_some]
              dsimp only
              rw [PFunConverter.sysAnswers_concat_output S xs x
                (by rw [PFunDDS.dom_fullyDefined]; simp)]
              simp only [Option.bind_some, Sum.getLeft?_inl]
              have hcat := PFunConverter.sysAnswers_concat S xs x
              cases hy : PFunConverter.sysAnswer S (xs ++ [x]) with
              | none =>
                  simp only [Option.bind_none]
                  refine drive_eq_none_of_silent _ S (by omega) ?_
                  refine ofHistoryStepPartial_eq_none_of_bot step cnt hne
                    (segY := segY) ?_
                  rw [hcat, hy, List.drop_append_of_le_length hoff, hseg]
              | some y =>
                  simp only [Option.bind_some]
                  refine ih m (xs ++ [x]) (segY ++ [y]) (by simp; omega)
                    (by simp; omega) ?_ (by omega)
                  rw [hcat, hy, List.drop_append_of_le_length hoff, hseg]
                  simp

/-- The round bridge, packaged: a round that opens on an aligned inner history
is exactly `roundOut`. -/
private theorem drive_roundOut
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (S : PFunDDS.DDS X Y) {us : List U} (hne : us ≠ []) (xs : List X)
    {fuel : ℕ} (hfuel : cnt us < fuel)
    (hlen : roundOffset cnt us = xs.length) :
    PFunConverter.drive (ofHistoryStepPartial step cnt) S fuel us xs
        (PFunConverter.sysAnswers S xs)
      = Part.ofOption ((roundOut step cnt S us hne xs).map fun p =>
          (p.1, p.2, PFunConverter.sysAnswers S p.2)) := by
  rw [drive_round step cnt hcnt S hne (cnt us) fuel xs [] (by simp) (by simpa using hlen)
    (by
      refine List.drop_eq_nil_of_le ?_
      rw [PFunConverter.sysAnswers_length, hlen]) hfuel]
  congr 1
  simp [roundOut, Option.map_bind, Option.map_map, Function.comp_def]

/-! ### The outer fold -/

/-- One unrolling of `PFunConverter.driveOuter`, as an equation. -/
private theorem driveOuter_cons (α : PFunConverter.ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) (fuel : ℕ) (usPre : List U) (xs : List X)
    (ys : List (Option Y)) (u : U) (rest : List U) :
    PFunConverter.driveOuter α S fuel usPre xs ys (u :: rest) =
      (PFunConverter.drive α S fuel (usPre ++ [u]) xs ys).bind fun r =>
        (PFunConverter.driveOuter α S fuel (usPre ++ [u]) r.2.1 r.2.2 rest).map
          fun rr => (r.1 :: rr.1, rr.2) := rfl

/-- **The outer fold, in closed form.** -/
private theorem driveOuter_closed
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (S : PFunDDS.DDS X Y) :
    ∀ (rest usPre : List U) (fuel : ℕ) (xs : List X),
      (∀ vs : List U, vs <+: usPre ++ rest → cnt vs < fuel) →
      (∀ u : U, roundOffset cnt (usPre ++ [u]) = xs.length) →
      PFunConverter.driveOuter (ofHistoryStepPartial step cnt) S fuel usPre xs
          (PFunConverter.sysAnswers S xs) rest
        = Part.ofOption ((outerRun step cnt S usPre rest xs).map fun q =>
            (q.1, q.2, PFunConverter.sysAnswers S q.2)) := by
  intro rest
  induction rest with
  | nil => intro usPre fuel xs _ _; rfl
  | cons u rest ih =>
      intro usPre fuel xs hfuel hoff
      have hne : usPre ++ [u] ≠ [] := by simp
      rw [driveOuter_cons, outerRun_cons,
        drive_roundOut step cnt hcnt S hne xs
          (hfuel _ ⟨rest, by simp⟩) (hoff u)]
      cases hr : roundOut step cnt S (usPre ++ [u]) hne xs with
      | none => simp
      | some p =>
          have hlen : p.2.length = xs.length + cnt (usPre ++ [u]) :=
            roundOut_length step cnt S (usPre ++ [u]) hne hr
          rw [show (Part.ofOption
              (Option.map (fun p => (p.1, p.2, PFunConverter.sysAnswers S p.2))
                (some p)) : Part (V × List X × List (Option Y)))
              = Part.some (p.1, p.2, PFunConverter.sysAnswers S p.2) from rfl,
            Part.bind_some, Option.bind_some,
            ih (usPre ++ [u]) fuel p.2 (by simpa using hfuel)
              (fun u' => by
                rw [roundOffset_concat cnt hne u', hoff u, hlen]),
            ← CausalApply.ofOption_map, Option.map_map, Option.map_map]
          rfl

/-! ### The closed form -/

private theorem applyRawAt_closed
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (S : PFunDDS.DDS X Y) (us : List U) {fuel : ℕ}
    (hfuel : ∀ vs : List U, vs <+: us → cnt vs < fuel) :
    PFunConverter.applyRawAt (ofHistoryStepPartial step cnt) S fuel us
      = Part.ofOption (closedAnswer step cnt S us) := by
  have hdo := driveOuter_closed step cnt hcnt S us [] fuel []
    (by simpa using hfuel)
    (fun u => by
      simpa using roundOffset_of_length_le_one cnt (us := [] ++ [u]) (by simp))
  rw [PFunConverter.sysAnswers_nil] at hdo
  simp only [PFunConverter.applyRawAt, closedAnswer, hdo]
  cases ho : outerRun step cnt S [] us [] with
  | none => simp
  | some p =>
      rw [show (Part.ofOption
          (Option.map (fun q => (q.1, q.2, PFunConverter.sysAnswers S q.2))
            (some p)) : Part (List V × List X × List (Option Y)))
          = Part.some (p.1, p.2, PFunConverter.sysAnswers S p.2) from rfl,
        Part.bind_some, Option.bind_some]
      cases p.1.getLast? with
      | none => rfl
      | some v => rfl

/-- **Closed-form application of a budgeted history-step converter.**

Applying `ofHistoryStepPartial step cnt` — the CR18 Def 3.8 converter whose
round at outer history `us` issues exactly `cnt us` inner queries whenever it
moves at all — to *any* system `S` is a finite composite: `cnt us` copies of the
system's Def 3.3 completion `S⊥` interleaved with `step`, folded over the outer
history.  No fixed point, no fuel; the `Option` records where the composite
stalls (a `⊥` from `S⊥`, or silence from `step`), which is exactly where the
applied system is undefined. -/
theorem applyRaw_ofHistoryStepPartial
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (S : PFunDDS.DDS X Y) (us : List U) :
    PFunConverter.applyRaw (ofHistoryStepPartial step cnt) S us
      = Part.ofOption (closedAnswer step cnt S us) := by
  have hbound : ∀ f : ℕ, (us.inits.map cnt).sum + 1 ≤ f →
      ∀ vs : List U, vs <+: us → cnt vs < f := by
    intro f hf vs hvs
    have hmem : cnt vs ∈ us.inits.map cnt :=
      List.mem_map.mpr ⟨vs, (List.mem_inits vs us).mpr hvs, rfl⟩
    have := List.single_le_sum (l := us.inits.map cnt)
      (fun x _ => Nat.zero_le x) _ hmem
    omega
  apply Part.ext
  intro v
  rw [PFunConverter.mem_applyRaw]
  constructor
  · rintro ⟨f, hv⟩
    have hv' := PFunConverter.applyRawAt_mono_le
      (ofHistoryStepPartial step cnt) S (le_max_left f ((us.inits.map cnt).sum + 1)) hv
    rwa [applyRawAt_closed step cnt hcnt S us (hbound _ (le_max_right _ _))] at hv'
  · intro hv
    exact ⟨(us.inits.map cnt).sum + 1, by
      rw [applyRawAt_closed step cnt hcnt S us (hbound _ le_rfl)]; exact hv⟩

/-- The closed form as a statement about `PFunConverter.apply`: the applied
system's value at an outer history, computed, with no `fuel` in sight. -/
theorem apply_ofHistoryStepPartial_val
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y) (mv : X ⊕ V),
      step us hne ys = some mv → ((∃ x, mv = Sum.inl x) ↔ ys.length < cnt us))
    (S : PFunDDS.DDS X Y) (us : List U) :
    (PFunConverter.apply (ofHistoryStepPartial step cnt) S).1 us
      = Part.ofOption (closedAnswer step cnt S us) :=
  applyRaw_ofHistoryStepPartial step cnt hcnt S us

/-- The never-silent instance: `ofHistoryStep` under the original (unconditional)
boundary condition. -/
theorem apply_ofHistoryStep_val
    (step : (us : List U) → us ≠ [] → List Y → X ⊕ V) (cnt : List U → ℕ)
    (hcnt : ∀ (us : List U) (hne : us ≠ []) (ys : List Y),
      (∃ x, step us hne ys = Sum.inl x) ↔ ys.length < cnt us)
    (S : PFunDDS.DDS X Y) (us : List U) :
    (PFunConverter.apply (ofHistoryStep step cnt) S).1 us
      = Part.ofOption
          (closedAnswer (fun us hne ys => some (step us hne ys)) cnt S us) := by
  rw [ofHistoryStep_eq_ofHistoryStepPartial]
  refine apply_ofHistoryStepPartial_val _ cnt (fun vs hne ys mv hmv => ?_) S us
  rw [Option.some_inj] at hmv
  subst hmv
  exact hcnt vs hne ys

/-! ### Receipt: `simple_apply` is the `cnt ≡ 1`, memoryless instance

Maurer's simple converter `simple c d` (`PFunConverter.DDC.simple`) is the
`ofStep` converter at `cnt ≡ 1`, hence — through `ofStep_eq_ofHistoryStep` and
`ofHistoryStep_eq_ofHistoryStepPartial` — an instance of the closed form above.
Evaluating that instance reproduces `PFunConverter.DDC.simple_apply` *from the
general theorem*: the one-query round is a single copy of `S⊥`, the outer fold
grows the inner history by `map c`, and prefix closure of `S` collapses the
round-by-round domain conditions to the single condition
`us.map c ∈ dom S`. -/

/-- The outer fold answers exactly once per outer message. -/
theorem outerRun_length
    (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
    (cnt : List U → ℕ) (S : PFunDDS.DDS X Y) :
    ∀ (rest usPre : List U) (xs : List X) {r : List V × List X},
      outerRun step cnt S usPre rest xs = some r → r.1.length = rest.length := by
  intro rest
  induction rest with
  | nil => intro usPre xs r h; cases h; simp
  | cons u rest ih =>
      intro usPre xs r h
      rw [outerRun_cons, Option.bind_eq_some_iff] at h
      obtain ⟨p, -, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      simp [ih (usPre ++ [u]) p.2 hq]

/-- `S⊥`'s answer at a history in `dom S` is the system's own. -/
private theorem sysAnswer_append_eq_some (S : PFunDDS.DDS X Y) {xs : List X}
    {x : X} (hxs : xs ∈ PFunDDS.dom S ∨ xs = [])
    (h : xs ++ [x] ∈ PFunDDS.dom S) :
    PFunConverter.sysAnswer S (xs ++ [x])
      = some (PFunDDS.output S (xs ++ [x]) h) := by
  rw [PFunConverter.sysAnswer_of_ne_nil S (by simp)
    (by rw [PFunDDS.dom_fullyDefined]; simp)]
  exact PFunDDS.output_fullyDefined_append_of_mem S xs x hxs h

/-- …and a proper answer witnesses membership. -/
private theorem mem_dom_of_sysAnswer_append (S : PFunDDS.DDS X Y) {xs : List X}
    {x : X} {y : Y} (hxs : xs ∈ PFunDDS.dom S ∨ xs = [])
    (h : PFunConverter.sysAnswer S (xs ++ [x]) = some y) :
    ∃ hd : xs ++ [x] ∈ PFunDDS.dom S, PFunDDS.output S (xs ++ [x]) hd = y := by
  rw [PFunConverter.sysAnswer_of_ne_nil S (by simp)
    (by rw [PFunDDS.dom_fullyDefined]; simp)] at h
  exact PFunDDS.mem_of_output_fullyDefined_append_eq_some S xs x hxs h

/-- A one-query round of the simple converter: forward `c u`, return `d y`. -/
private theorem roundOut_simple (c : U → X) (d : Y → V) (S : PFunDDS.DDS X Y)
    {cnt : List U → ℕ} (hcnt1 : ∀ vs : List U, vs ≠ [] → cnt vs = 1)
    (vs : List U) (hne : vs ≠ []) (xs : List X) :
    roundOut (fun us hne ys =>
        some (PFunConverter.DDC.simpleStep c d (us.getLast hne) ys)) cnt S vs hne xs
      = (PFunConverter.sysAnswer S (xs ++ [c (vs.getLast hne)])).map
          fun y => (d y, xs ++ [c (vs.getLast hne)]) := by
  rw [roundOut, hcnt1 vs hne, roundRun_succ]
  simp only [PFunConverter.DDC.simpleStep, Option.bind_some, Sum.getLeft?_inl,
    List.nil_append, roundRun_zero]
  cases hy : PFunConverter.sysAnswer S (xs ++ [c (vs.getLast hne)]) with
  | none => simp
  | some y => simp

/-- The simple converter's outer fold, evaluated: the closed form's answer at a
nonempty outer history is `d (S (map c history))`, domains included. -/
private theorem closedAnswer_simple_aux (c : U → X) (d : Y → V)
    (S : PFunDDS.DDS X Y) {cnt : List U → ℕ}
    (hcnt1 : ∀ vs : List U, vs ≠ [] → cnt vs = 1) :
    ∀ (rest usPre : List U) (xs : List X),
      (xs ∈ PFunDDS.dom S ∨ xs = []) → rest ≠ [] →
      Part.ofOption ((outerRun (fun us hne ys =>
            some (PFunConverter.DDC.simpleStep c d (us.getLast hne) ys))
          cnt S usPre rest xs).bind fun p => p.1.getLast?)
        = (S.1 (xs ++ rest.map c)).map d := by
  intro rest
  induction rest with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons u rest ih =>
      intro usPre xs hxs _
      have hne : usPre ++ [u] ≠ [] := by simp
      have hlastu : (usPre ++ [u]).getLast hne = u := by simp
      rw [outerRun_cons, roundOut_simple c d S hcnt1 (usPre ++ [u]) hne xs, hlastu]
      cases hy : PFunConverter.sysAnswer S (xs ++ [c u]) with
      | none =>
          have hnd : xs ++ [c u] ∉ PFunDDS.dom S := fun hd => by
            rw [sysAnswer_append_eq_some S hxs hd] at hy; simp at hy
          have hnd' : S.1 (xs ++ (u :: rest).map c) = Part.none := by
            refine Part.eq_none_iff'.mpr fun hdom => hnd ?_
            exact PFunDDS.prefix_closed S (l₂ := xs ++ (u :: rest).map c)
              ⟨rest.map c, by simp⟩ (by simp) hdom
          rw [hnd']
          simp
      | some y =>
          obtain ⟨hd, rfl⟩ := mem_dom_of_sysAnswer_append S hxs hy
          simp only [Option.map_some, Option.bind_some]
          rcases rest with _ | ⟨u2, rest2⟩
          · have hS : S.1 (xs ++ [c u]) = Part.some (PFunDDS.output S (xs ++ [c u]) hd) :=
              Part.eq_some_iff.mpr (Part.get_mem hd)
            simp [hS]
          · have hkey : ∀ (o : Option (List V × List X)),
                (∀ r, o = some r → r.1.length = (u2 :: rest2).length) →
                ((Option.map
                    (fun q => (d (PFunDDS.output S (xs ++ [c u]) hd) :: q.1, q.2)) o).bind
                    fun p => p.1.getLast?)
                  = o.bind fun q => q.1.getLast? := by
              rintro (_ | q) hq
              · rfl
              · have hlen := hq q rfl
                cases hq1 : q.1 with
                | nil => rw [hq1] at hlen; simp at hlen
                | cons b l => simp [hq1]
            rw [hkey _ (fun r hr => outerRun_length _ cnt S _ _ _ hr)]
            rw [ih (usPre ++ [u]) (xs ++ [c u]) (Or.inl hd) (by simp)]
            simp

/-- **The specialisation receipt.**  `PFunConverter.DDC.simple_apply`'s
statement — Maurer's simple converter applied to an arbitrary system is
`map d ∘ S ∘ map c`, domains included — *derived from* the closed form at the
memoryless `cnt ≡ 1` instance. -/
theorem simple_apply_of_closedAnswer (c : U → X) (d : Y → V)
    (S : PFunDDS.DDS X Y) (us : List U) :
    (PFunConverter.DDC.apply (PFunConverter.DDC.simple c d) S).1 us
      = (S.1 (us.map c)).map d := by
  have hcnt1 : ∀ vs : List U, vs ≠ [] →
      (fun vs : List U => vs.getLast?.elim 0 (fun _ : U => 1)) vs = 1 := by
    intro vs hvs
    cases hg : vs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hvs
    | some a => simp [hg]
  have hcntH : ∀ (vs : List U) (hne : vs ≠ []) (ys : List Y),
      (∃ x, PFunConverter.DDC.simpleStep c d (vs.getLast hne) ys = Sum.inl x) ↔
        ys.length < (fun vs : List U => vs.getLast?.elim 0 (fun _ : U => 1)) vs := by
    intro vs hne ys
    rw [hcnt1 vs hne]
    cases ys with
    | nil => exact ⟨fun _ => by simp, fun _ => ⟨c (vs.getLast hne), rfl⟩⟩
    | cons y t =>
        constructor
        · rintro ⟨x, hx⟩; simp [PFunConverter.DDC.simpleStep] at hx
        · intro h; simp at h
  rw [PFunConverter.DDC.simple, PFunConverter.DDC.apply_ofStep,
    ← apply_ofStep_eq_applyG (PFunConverter.DDC.simpleStep c d) (fun _ => 1)
      (fun u ys => by
        cases ys with
        | nil => exact ⟨fun _ => by simp, fun _ => ⟨c u, rfl⟩⟩
        | cons y t =>
            constructor
            · rintro ⟨x, hx⟩; simp [PFunConverter.DDC.simpleStep] at hx
            · intro h; simp at h),
    ofStep_eq_ofHistoryStep, apply_ofHistoryStep_val _ _ hcntH]
  rcases us with _ | ⟨u, rest⟩
  · have hnil : S.1 (List.map c ([] : List U)) = Part.none :=
      Part.eq_none_iff'.mpr fun hdom => PFunDDS.empty_not_mem S hdom
    rw [hnil]
    simp [closedAnswer]
  · rw [closedAnswer,
      closedAnswer_simple_aux c d S hcnt1 (u :: rest) [] [] (Or.inr rfl) (by simp)]
    simp

open scoped PFunConverter.DDC in
/-- The receipt, in `PFunConverter.DDC.simple_apply`'s own notation. -/
example (c : U → X) (d : Y → V) (S : PFunDDS.DDS X Y) (us : List U) :
    (PFunConverter.DDC.simple c d ·ᶜ S).1 us = (S.1 (us.map c)).map d :=
  simple_apply_of_closedAnswer c d S us

end PFunConverter.ProtocolFn

end RandomSystems.CR18
