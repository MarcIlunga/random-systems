/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ProtocolFn

/-!
# The ν-level realization theorem (DESIGN §10.5)

`apply α S` is the **transcript-equation application** of a protocol
function `α : List U × List (Option Y) →. X ⊕ V` to a system `S`: the unique
causal solution of

`x̂ⱼ = α(active outer prefix, ŷ^{j−1})`,  `ŷⱼ = S⊥(x̂^j)`,

realized function-natively as a finite unrolling (`drive`, fuel = the
unrolling counter, hidden by `eventual`) — the ν-level generalization of
`CausalApply.applyG`, with the converter now seeing the *full* history
(cross-round memory: `[q]`, blind `b`, copying `T̃`, CTR all live here).
Per CR18 Def 3.9 the queries are answered by the Def 3.3 completion `S⊥`
(`Y ∪ {⊥}`), so the drive never stalls on the system: partiality comes from
α alone.

The **realization theorem** `apply_toDDC`:

`DDC.apply (toDDC α) S = apply α S`

— CR18 Def 3.9 applied to the canonical Def 3.8 object of α *is* the
transcript-equation solution.  Same two simulations as `apply_ofStep`
(StepConverter.lean), with the round state `(u, ys)` of the outer-memoryless
case replaced by the parse `ParsesTo α l (us, ys)` of the full history; both
sides thread the *same* `S⊥`-answers, so the answer histories coincide on
the nose and no liveness invariant is needed.

As the first cross-round instance, the `[q]` filter is computed:
`apply (queryLimitFn q) S = PFunDDS.filterQueries q S`, hence
`DDC.apply (toDDC (queryLimitFn q)) S = filterQueries q S` — and combining
with the pre-existing operational theorem, the old `[q]ᶠ` DDC and
`toDDC (queryLimitFn q)` are **apply-equal** representatives of the same
converter, retiring the need for `queryLimit`-style bespoke trace proofs.
-/

namespace RandomSystems.CR18

namespace PFunConverter

open scoped PFunDDS

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ### The transcript-equation driver -/

/-- One-round unrolling of the transcript equations from the pair
`(us, ys)` with inner history `xs`: consult α; a query is answered by the
Def 3.3 completion `S⊥` (`⊥` when the extended inner history falls out of
`dom S`) and both histories grow; an answer exits with the final histories.
The system side never stalls — partiality comes from α alone. -/
noncomputable def drive (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    ℕ → List U → List X → List (Option Y) → Part (V × List X × List (Option Y))
  | 0, _, _, _ => Part.none
  | fuel + 1, us, xs, ys =>
      (α (us, ys)).bind fun m =>
        match m with
        | Sum.inl x =>
            drive α S fuel us (xs ++ [x])
              (ys ++ [PFunDDS.output (S⊥) (xs ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp)])
        | Sum.inr v => Part.some (v, xs, ys)

/-- Membership constructor: a query step. -/
theorem drive_mem_query (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {us : List U} {xs : List X} {ys : List (Option Y)} {x : X}
    (hm : Sum.inl x ∈ α (us, ys))
    {fuel : ℕ} {r : V × List X × List (Option Y)}
    (h : r ∈ drive α S fuel us (xs ++ [x])
      (ys ++ [PFunDDS.output (S⊥) (xs ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp)])) :
    r ∈ drive α S (fuel + 1) us xs ys := by
  simp only [drive, Part.mem_bind_iff]
  exact ⟨Sum.inl x, hm, h⟩

/-- Membership constructor: an answer step. -/
theorem drive_mem_answer (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {us : List U} {xs : List X} {ys : List (Option Y)} {v : V}
    (hm : Sum.inr v ∈ α (us, ys)) (fuel : ℕ) :
    (v, xs, ys) ∈ drive α S (fuel + 1) us xs ys := by
  simp only [drive, Part.mem_bind_iff]
  exact ⟨Sum.inr v, hm, Part.mem_some_iff.mpr rfl⟩

/-- Membership destructor: one unrolling step. -/
theorem drive_succ_elim {α : ProtocolFn U V X Y} {S : PFunDDS.DDS X Y}
    {fuel : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
    {r : V × List X × List (Option Y)}
    (h : r ∈ drive α S (fuel + 1) us xs ys) :
    (∃ x, Sum.inl x ∈ α (us, ys) ∧
        r ∈ drive α S fuel us (xs ++ [x])
          (ys ++ [PFunDDS.output (S⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp)])) ∨
      (∃ v, Sum.inr v ∈ α (us, ys) ∧ r = (v, xs, ys)) := by
  simp only [drive, Part.mem_bind_iff] at h
  obtain ⟨m, hm, h⟩ := h
  cases m with
  | inl x => exact Or.inl ⟨x, hm, h⟩
  | inr v =>
      simp only [Part.mem_some_iff] at h
      exact Or.inr ⟨v, hm, h⟩

theorem drive_mono (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
      {r : V × List X × List (Option Y)},
      r ∈ drive α S fuel us xs ys → r ∈ drive α S (fuel + 1) us xs ys := by
  intro fuel
  induction fuel with
  | zero => intro us xs ys r h; simp [drive] at h
  | succ n ih =>
      intro us xs ys r h
      rcases drive_succ_elim h with ⟨x, hm, h⟩ | ⟨v, hm, rfl⟩
      · exact drive_mem_query α S hm (ih h)
      · exact drive_mem_answer α S hm (n + 1)

theorem drive_mono_le (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {fuel fuel' : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
    {r : V × List X × List (Option Y)} (hle : fuel ≤ fuel')
    (h : r ∈ drive α S fuel us xs ys) : r ∈ drive α S fuel' us xs ys := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact drive_mono α S ih

/-- The outer fold: consume the remaining outer inputs, growing the active
outer prefix and threading the inner histories. -/
noncomputable def driveOuter (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    (fuel : ℕ) :
    List U → List X → List (Option Y) → List U →
      Part (List V × List X × List (Option Y))
  | _, xs, ys, [] => Part.some ([], xs, ys)
  | usPre, xs, ys, u :: rest =>
      (drive α S fuel (usPre ++ [u]) xs ys).bind fun r =>
        (driveOuter α S fuel (usPre ++ [u]) r.2.1 r.2.2 rest).map fun rr =>
          (r.1 :: rr.1, rr.2)

theorem driveOuter_length (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    (fuel : ℕ) :
    ∀ {rest : List U} {usPre : List U} {xs : List X} {ys : List (Option Y)}
      {r : List V × List X × List (Option Y)},
      r ∈ driveOuter α S fuel usPre xs ys rest → r.1.length = rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro usPre xs ys r h
      simp only [driveOuter, Part.mem_some_iff] at h
      subst h
      simp
  | cons u rest ih =>
      intro usPre xs ys r h
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _, rr, hrr, rfl⟩ := h
      simp [ih hrr]

theorem driveOuter_mono (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {fuel : ℕ} :
    ∀ {rest : List U} {usPre : List U} {xs : List X} {ys : List (Option Y)}
      {r : List V × List X × List (Option Y)},
      r ∈ driveOuter α S fuel usPre xs ys rest →
        r ∈ driveOuter α S (fuel + 1) usPre xs ys rest := by
  intro rest
  induction rest with
  | nil => intro usPre xs ys r h; simpa [driveOuter] using h
  | cons u rest ih =>
      intro usPre xs ys r h
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h ⊢
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := h
      exact ⟨r₁, drive_mono α S hr₁, rr, ih hrr, rfl⟩

theorem driveOuter_mono_le (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {fuel fuel' : ℕ} {rest usPre : List U} {xs : List X} {ys : List (Option Y)}
    {r : List V × List X × List (Option Y)} (hle : fuel ≤ fuel')
    (h : r ∈ driveOuter α S fuel usPre xs ys rest) :
    r ∈ driveOuter α S fuel' usPre xs ys rest := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact driveOuter_mono α S ih

/-- The per-fuel applied raw function: replay from empty histories, answer
with the last round's output. -/
noncomputable def applyRawAt (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    (fuel : ℕ) :
    PFunDDS.Raw U V :=
  fun us => (driveOuter α S fuel [] [] [] us).bind fun r =>
    match r.1.getLast? with
    | some v => Part.some v
    | none => Part.none

theorem mem_applyRawAt_iff (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    (fuel : ℕ) (us : List U) (v : V) :
    v ∈ applyRawAt α S fuel us ↔
      ∃ r ∈ driveOuter α S fuel [] [] [] us, r.1.getLast? = some v := by
  simp only [applyRawAt, Part.mem_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  cases r.1.getLast? with
  | none => simp
  | some w => simp [Part.mem_some_iff, eq_comm]

theorem applyRawAt_mono_le (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {fuel fuel' : ℕ} {us : List U} {v : V} (hle : fuel ≤ fuel')
    (h : v ∈ applyRawAt α S fuel us) : v ∈ applyRawAt α S fuel' us := by
  rw [mem_applyRawAt_iff] at h ⊢
  obtain ⟨r, hr, hlast⟩ := h
  exact ⟨r, driveOuter_mono_le α S hle hr, hlast⟩

/-- The fuel-free applied raw function: eventual value of the unrolling. -/
noncomputable def applyRaw (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    PFunDDS.Raw U V :=
  fun us => CausalApply.eventual fun fuel => applyRawAt α S fuel us

theorem mem_applyRaw (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    (us : List U) (v : V) :
    v ∈ applyRaw α S us ↔ ∃ fuel, v ∈ applyRawAt α S fuel us :=
  CausalApply.mem_eventual
    (hmono := fun hle hw => applyRawAt_mono_le α S hle hw)

/-- Split of the outer fold over concatenation (validity engine). -/
theorem driveOuter_append (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    (fuel : ℕ) :
    ∀ (a b : List U) (usPre : List U) (xs : List X) (ys : List (Option Y)),
      driveOuter α S fuel usPre xs ys (a ++ b) =
        (driveOuter α S fuel usPre xs ys a).bind fun ra =>
          (driveOuter α S fuel (usPre ++ a) ra.2.1 ra.2.2 b).map fun rb =>
            (ra.1 ++ rb.1, rb.2) := by
  intro a
  induction a with
  | nil =>
      intro b usPre xs ys
      simp only [List.nil_append, driveOuter, Part.bind_some, List.append_nil]
      refine (Part.map_id' ?_ _).symm
      intro rb
      rfl
  | cons u rest ih =>
      intro b usPre xs ys
      simp only [List.cons_append, driveOuter, ih, Part.bind_assoc,
        Part.bind_map, Part.map_bind, Part.map_map, Function.comp_def,
        List.cons_append, List.append_assoc, List.nil_append]

/-- **The transcript-equation application** (fuel-free): the ν-level
generalization of `CausalApply.applyG` — a valid `DDS U V`, partial exactly
where the equations do not solve. -/
noncomputable def apply (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    PFunDDS.DDS U V :=
  ⟨applyRaw α S, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]
      rintro ⟨v, hv⟩
      rw [mem_applyRaw] at hv
      obtain ⟨fuel, hv⟩ := hv
      rw [mem_applyRawAt_iff] at hv
      obtain ⟨r, hr, hlast⟩ := hv
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      simp at hlast
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨t, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      rw [mem_applyRaw] at hv
      obtain ⟨fuel, hv⟩ := hv
      rw [mem_applyRawAt_iff] at hv
      obtain ⟨r, hr, _⟩ := hv
      rw [driveOuter_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _⟩ := hr
      have hlen : ra.1.length = l₁.length := driveOuter_length α S fuel hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil
        apply hne
        apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      rw [mem_applyRaw]
      refine ⟨fuel, ?_⟩
      rw [mem_applyRawAt_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]⟩

@[simp] theorem apply_toPFun (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    (apply α S).1 = applyRaw α S := rfl

/-! ### Successful-driver reachability and invariant-indexed congruence -/

/-- **Successful-driver reachability**: from a reachable pair, a successful
`drive` run ends at a reachable pair whose move is the delivered outer
answer. -/
theorem drive_result_reachable (α : ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) :
    ∀ (fuel : ℕ) (us : List U) (xs : List X) (ys : List (Option Y))
      (r : V × List X × List (Option Y)),
      Reach α (us, ys) →
        r ∈ drive α S fuel us xs ys →
        Reach α (us, r.2.2) ∧ Sum.inr r.1 ∈ α (us, r.2.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro us xs ys r _ member
      simp [drive] at member
  | succ fuel induction =>
      intro us xs ys r reachable member
      rcases drive_succ_elim member with
        ⟨x, queryMember, nextMember⟩ | ⟨v, answerMember, rfl⟩
      · exact induction _ _ _ _
          (Reach.answer reachable queryMember _) nextMember
      · exact ⟨reachable, answerMember⟩

/-- **Invariant-indexed application congruence**: two protocol functions that
agree on reachable pairs satisfying an invariant preserved by the resource's
Def 3.3 completions apply equally.  The conclusion is equality only after
application to the resource — the raw trace trees may differ off the
invariant. -/
theorem apply_eq_of_reachable_invariant (α β : ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y)
    (invariant : List U → List (Option Y) → Prop)
    (startRound :
      ∀ (us : List U) (ys : List (Option Y)) (u : U),
        ((us = [] ∧ ys = []) ∨
          ∃ v, Reach α (us, ys) ∧ Sum.inr v ∈ α (us, ys) ∧ invariant us ys) →
        Reach α (us ++ [u], ys) ∧ invariant (us ++ [u]) ys)
    (completeInvariant :
      ∀ (us : List U) (xs : List X) (ys : List (Option Y)) (x : X),
        Reach α (us, ys) →
        invariant us ys →
        Sum.inl x ∈ α (us, ys) →
        invariant us
          (ys ++ [PFunDDS.output (PFunDDS.fullyDefined S) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp)]))
    (agree :
      ∀ (us : List U) (ys : List (Option Y)),
        Reach α (us, ys) → invariant us ys → α (us, ys) = β (us, ys)) :
    apply α S = apply β S := by
  have driveInvariant :
      ∀ (fuel : ℕ) (us : List U) (xs : List X) (ys : List (Option Y))
        (r : V × List X × List (Option Y)),
        Reach α (us, ys) →
        invariant us ys →
        r ∈ drive α S fuel us xs ys →
        invariant us r.2.2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro us xs ys r _ _ member
        simp [drive] at member
    | succ fuel induction =>
        intro us xs ys r reachable valid member
        rcases drive_succ_elim member with
          ⟨x, queryMember, nextMember⟩ | ⟨v, answerMember, rfl⟩
        · exact induction _ _ _ _
            (Reach.answer reachable queryMember _)
            (completeInvariant us xs ys x reachable valid queryMember)
            nextMember
        · exact valid
  have driveIff :
      ∀ (fuel : ℕ) (us : List U) (xs : List X) (ys : List (Option Y))
        (r : V × List X × List (Option Y)),
        Reach α (us, ys) →
        invariant us ys →
        (r ∈ drive α S fuel us xs ys ↔ r ∈ drive β S fuel us xs ys) := by
    intro fuel
    induction fuel with
    | zero =>
        intro us xs ys r _ _
        rfl
    | succ fuel induction =>
        intro us xs ys r reachable valid
        have equation := agree us ys reachable valid
        constructor
        · intro member
          rcases drive_succ_elim member with
            ⟨x, queryMember, nextMember⟩ | ⟨v, answerMember, rfl⟩
          · have rightQuery : Sum.inl x ∈ β (us, ys) :=
              equation ▸ queryMember
            apply drive_mem_query _ S rightQuery
            exact (induction _ _ _ _
              (Reach.answer reachable queryMember _)
              (completeInvariant us xs ys x reachable valid
                queryMember)).mp nextMember
          · apply drive_mem_answer _ S _ fuel
            exact equation ▸ answerMember
        · intro member
          rcases drive_succ_elim member with
            ⟨x, rightQuery, nextMember⟩ | ⟨v, rightAnswer, rfl⟩
          · have queryMember : Sum.inl x ∈ α (us, ys) :=
              equation.symm ▸ rightQuery
            apply drive_mem_query _ S queryMember
            exact (induction _ _ _ _
              (Reach.answer reachable queryMember _)
              (completeInvariant us xs ys x reachable valid
                queryMember)).mpr nextMember
          · apply drive_mem_answer _ S _ fuel
            exact equation.symm ▸ rightAnswer
  have outerIff :
      ∀ (rest : List U) (fuel : ℕ) (us : List U) (xs : List X)
        (ys : List (Option Y))
        (r : List V × List X × List (Option Y)),
        ((us = [] ∧ ys = []) ∨
          ∃ v, Reach α (us, ys) ∧ Sum.inr v ∈ α (us, ys) ∧ invariant us ys) →
        (r ∈ driveOuter α S fuel us xs ys rest ↔
          r ∈ driveOuter β S fuel us xs ys rest) := by
    intro rest
    induction rest with
    | nil =>
        intro fuel us xs ys r _
        rfl
    | cons u rest induction =>
        intro fuel us xs ys r ready
        obtain ⟨reachable, valid⟩ := startRound us ys u ready
        constructor
        · intro member
          rw [driveOuter, Part.mem_bind_iff] at member
          rcases member with ⟨round, roundMember, mappedTail⟩
          rw [Part.mem_map_iff] at mappedTail
          obtain ⟨tail, tailMember, rfl⟩ := mappedTail
          have rightRound :=
            (driveIff fuel (us ++ [u]) xs ys round reachable
              valid).mp roundMember
          obtain ⟨finalReachable, answerMember⟩ :=
            drive_result_reachable α S fuel (us ++ [u]) xs ys round
              reachable roundMember
          have finalValid :=
            driveInvariant fuel (us ++ [u]) xs ys round reachable valid
              roundMember
          have nextReady :
              ((us ++ [u] = [] ∧ round.2.2 = []) ∨
                ∃ v, Reach α (us ++ [u], round.2.2) ∧
                  Sum.inr v ∈ α (us ++ [u], round.2.2) ∧
                  invariant (us ++ [u]) round.2.2) :=
            Or.inr ⟨round.1, finalReachable, answerMember, finalValid⟩
          rw [driveOuter.eq_2]
          apply Part.mem_bind rightRound
          apply Part.mem_map _
          exact (induction fuel (us ++ [u]) round.2.1 round.2.2 tail
            nextReady).mp tailMember
        · intro member
          rw [driveOuter.eq_2, Part.mem_bind_iff] at member
          rcases member with ⟨round, rightRound, mappedTail⟩
          rw [Part.mem_map_iff] at mappedTail
          obtain ⟨tail, rightTail, rfl⟩ := mappedTail
          have roundMember :=
            (driveIff fuel (us ++ [u]) xs ys round reachable
              valid).mpr rightRound
          obtain ⟨finalReachable, answerMember⟩ :=
            drive_result_reachable α S fuel (us ++ [u]) xs ys round
              reachable roundMember
          have finalValid :=
            driveInvariant fuel (us ++ [u]) xs ys round reachable valid
              roundMember
          have nextReady :
              ((us ++ [u] = [] ∧ round.2.2 = []) ∨
                ∃ v, Reach α (us ++ [u], round.2.2) ∧
                  Sum.inr v ∈ α (us ++ [u], round.2.2) ∧
                  invariant (us ++ [u]) round.2.2) :=
            Or.inr ⟨round.1, finalReachable, answerMember, finalValid⟩
          rw [driveOuter.eq_2]
          apply Part.mem_bind roundMember
          apply Part.mem_map _
          exact (induction fuel (us ++ [u]) round.2.1 round.2.2 tail
            nextReady).mpr rightTail
  apply Subtype.ext
  funext us
  change applyRaw α S us = applyRaw β S us
  apply Part.ext
  intro v
  rw [mem_applyRaw, mem_applyRaw]
  apply exists_congr
  intro fuel
  rw [mem_applyRawAt_iff, mem_applyRawAt_iff]
  apply exists_congr
  intro r
  apply and_congr
  · exact outerIff us fuel [] [] [] r (Or.inl ⟨rfl, rfl⟩)
  · rfl

/-! ### Parse-extension lemmas and move inversion -/

theorem parsesTo_singleton (α : ProtocolFn U V X Y) (u : U) :
    ParsesTo α [Sum.inl (InLabel.outside, u)] ([u], []) := rfl

theorem parsesTo_snoc_out {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} (h : ParsesTo α l (us, ys)) {v : V}
    (hv : Sum.inr v ∈ α (us, ys)) (u : U) :
    ParsesTo α (l ++ [Sum.inl (InLabel.outside, u)]) (us ++ [u], ys) := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u₀⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · show ParsesToAux α ([u₀], [])
          (rest ++ [Sum.inl (InLabel.outside, u)]) (us ++ [u], ys)
        rw [parsesToAux_append]
        exact ⟨(us, ys), h, ⟨v, hv⟩, rfl⟩
      · exact h.elim
      · exact h.elim

theorem parsesTo_snoc_in {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} (h : ParsesTo α l (us, ys)) {x : X}
    (hx : Sum.inl x ∈ α (us, ys)) (y : Option Y) :
    ParsesTo α (l ++ [Sum.inr (InLabel.inside, y)]) (us, ys ++ [y]) := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u₀⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · show ParsesToAux α ([u₀], [])
          (rest ++ [Sum.inr (InLabel.inside, y)]) (us, ys ++ [y])
        rw [parsesToAux_append]
        exact ⟨(us, ys), h, ⟨x, hx⟩, rfl⟩
      · exact h.elim
      · exact h.elim

theorem mem_toDDC_of_parses {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} {m : X ⊕ V}
    (hp : ParsesTo α l (us, ys)) (hm : m ∈ α (us, ys)) :
    DDC.moveOf m ∈ (toDDC α).1 l :=
  (mem_toDDCRaw_iff α l _).mpr ⟨(us, ys), hp, m, hm, rfl⟩

theorem toDDC_move_inv {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} {o : DDC.COut V X}
    (hp : ParsesTo α l (us, ys)) (ho : o ∈ (toDDC α).1 l) :
    ∃ m ∈ α (us, ys), o = DDC.moveOf m := by
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at ho
  obtain ⟨p', hp', m, hm, rfl⟩ := ho
  obtain rfl : p' = (us, ys) := parsesTo_unique hp' hp
  exact ⟨m, hm, rfl⟩

theorem moveOf_eq_out_iff {m : X ⊕ V} {v : V} :
    DDC.moveOf m = Sum.inl (InLabel.outside, v) ↔ m = Sum.inr v := by
  cases m <;> simp

theorem moveOf_eq_in_iff {m : X ⊕ V} {x : X} :
    DDC.moveOf m = Sum.inr (InLabel.inside, x) ↔ m = Sum.inl x := by
  cases m <;> simp

theorem connStep_toDDC_not_mem (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y)
    {st : List (DDC.CIn U Y) × List X}
    (h : ∀ p, ¬ ParsesTo α st.1 p)
    (o : (V × (List (DDC.CIn U Y) × List X)) ⊕ (List (DDC.CIn U Y) × List X)) :
    o ∉ DDC.connStep (toDDC α) S st := by
  intro ho
  rw [DDC.connStep, Part.mem_bind_iff] at ho
  obtain ⟨o', ho', -⟩ := ho
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at ho'
  obtain ⟨p, hp, -⟩ := ho'
  exact h p hp

/-! ### The inner round: `resolve` against `toDDC α` ↔ `drive`

Both sides consult the same `S⊥` (Def 3.3) on the same inner history, so the
answer lists coincide on the nose — no liveness invariant is threaded. -/

theorem resolve_toDDC_of_drive (α : ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) :
    ∀ {fuel : ℕ} {l : List (DDC.CIn U Y)} {us : List U} {xs : List X}
      {ys : List (Option Y)} {p : V × List X × List (Option Y)},
      ParsesTo α l (us, ys) →
      p ∈ drive α S fuel us xs ys →
      ∃ l', ParsesTo α l' (us, p.2.2) ∧ Sum.inr p.1 ∈ α (us, p.2.2) ∧
        (p.1, (l', p.2.1)) ∈ DDC.resolve (toDDC α) S (l, xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro l us xs ys p _ hp
      simp [drive] at hp
  | succ n ih =>
      intro l us xs ys p hparse hp
      simp only [drive, Part.mem_bind_iff] at hp
      obtain ⟨m, hm, hp⟩ := hp
      cases m with
      | inr v =>
          simp only [Part.mem_some_iff] at hp
          subst hp
          refine ⟨l, hparse, hm, ?_⟩
          exact DDC.resolve_out (toDDC α) S
            (by simpa using mem_toDDC_of_parses hparse hm)
      | inl x =>
          have hquery : Sum.inr (InLabel.inside, x) ∈ (toDDC α).1 l := by
            simpa using mem_toDDC_of_parses hparse hm
          obtain ⟨l', h1, h2, hres⟩ := ih
            (parsesTo_snoc_in hparse hm
              (PFunDDS.output (S⊥) (xs ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp))) hp
          refine ⟨l', h1, h2, ?_⟩
          rw [DDC.resolve_in (toDDC α) S hquery]
          exact hres

theorem drive_of_resolve_toDDC (α : ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y)
    {st : List (DDC.CIn U Y) × List X}
    {r : V × (List (DDC.CIn U Y) × List X)}
    (hr : r ∈ DDC.resolve (toDDC α) S st) :
    ∀ (us : List U) (ys : List (Option Y)), ParsesTo α st.1 (us, ys) →
      ∃ fuel ys',
        (r.1, r.2.2, ys') ∈ drive α S fuel us st.2 ys ∧
        ParsesTo α r.2.1 (us, ys') ∧ Sum.inr r.1 ∈ α (us, ys') := by
  refine PFun.fixInduction hr (C := fun st₀ =>
      ∀ (us : List U) (ys : List (Option Y)),
      ParsesTo α st₀.1 (us, ys) →
      ∃ fuel ys',
        (r.1, r.2.2, ys') ∈ drive α S fuel us st₀.2 ys ∧
        ParsesTo α r.2.1 (us, ys') ∧ Sum.inr r.1 ∈ α (us, ys')) ?_
  intro st₀ hfix IH us ys hparse
  rw [PFun.mem_fix_iff] at hfix
  rcases hfix with hstop | ⟨st₁, hstep₁, hrec⟩
  · rw [DDC.connStep_mem_inl] at hstop
    obtain ⟨hmove, hsteq⟩ := hstop
    obtain ⟨m, hm, hmv⟩ := toDDC_move_inv hparse hmove
    have hm' : m = Sum.inr r.1 := moveOf_eq_out_iff.mp hmv.symm
    subst hm'
    refine ⟨1, ys, ?_, ?_, hm⟩
    · simp only [drive, Part.mem_bind_iff]
      refine ⟨Sum.inr r.1, hm, ?_⟩
      simp only [Part.mem_some_iff]
      rw [hsteq]
    · rw [hsteq]
      exact hparse
  · have hstep₁' := hstep₁
    rw [DDC.connStep_mem_inr] at hstep₁'
    obtain ⟨x, hquery, hst₁⟩ := hstep₁'
    obtain ⟨m, hm, hmv⟩ := toDDC_move_inv hparse hquery
    have hm' : m = Sum.inl x := moveOf_eq_in_iff.mp hmv.symm
    subst hm'
    have hparse₁ : ParsesTo α st₁.1
        (us, ys ++ [PFunDDS.output (S⊥) (st₀.2 ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp)]) := by
      rw [hst₁]
      exact parsesTo_snoc_in hparse hm _
    obtain ⟨fuel, ys', hdrive, hp1, hp2⟩ := IH st₁ hstep₁ us _ hparse₁
    refine ⟨fuel + 1, ys', ?_, hp1, hp2⟩
    simp only [drive, Part.mem_bind_iff]
    refine ⟨Sum.inl x, hm, ?_⟩
    have hst₁2 : st₁.2 = st₀.2 ++ [x] := by rw [hst₁]
    rw [hst₁2] at hdrive
    exact hdrive

/-! ### The outer fold and the realization theorem -/

theorem driveFrom_toDDC_of_driveOuter (α : ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) {fuel : ℕ} :
    ∀ {rest : List U} {l : List (DDC.CIn U Y)} {usPre : List U}
      {xs : List X} {ys : List (Option Y)}
      {p : List V × List X × List (Option Y)},
      (l = [] ∧ usPre = [] ∧ ys = [] ∨
        (ParsesTo α l (usPre, ys) ∧ ∃ v, Sum.inr v ∈ α (usPre, ys))) →
      p ∈ driveOuter α S fuel usPre xs ys rest →
      ∃ l', (p.1, (l', p.2.1)) ∈ DDC.driveFrom (toDDC α) S (l, xs) rest := by
  intro rest
  induction rest with
  | nil =>
      intro l usPre xs ys p _ hp
      simp only [driveOuter, Part.mem_some_iff] at hp
      subst hp
      exact ⟨l, by simp [DDC.driveFrom]⟩
  | cons u rest ih =>
      intro l usPre xs ys p hready hp
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hp
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hp
      have hparse : ParsesTo α (l ++ [Sum.inl (InLabel.outside, u)])
          (usPre ++ [u], ys) := by
        rcases hready with ⟨rfl, rfl, rfl⟩ | ⟨hp', v, hv⟩
        · simpa using parsesTo_singleton α u
        · exact parsesTo_snoc_out hp' hv u
      obtain ⟨l₁, hp1, hv1, hres⟩ :=
        resolve_toDDC_of_drive α S hparse hr₁
      obtain ⟨l₂, htail⟩ := ih (Or.inr ⟨hp1, r₁.1, hv1⟩) hrr
      refine ⟨l₂, ?_⟩
      simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r₁.1, (l₁, r₁.2.1)), hres, (rr.1, (l₂, rr.2.1)), htail, rfl⟩

theorem driveOuter_of_driveFrom_toDDC (α : ProtocolFn U V X Y)
    (S : PFunDDS.DDS X Y) :
    ∀ {rest : List U} {l : List (DDC.CIn U Y)} {usPre : List U}
      {xs : List X} {ys : List (Option Y)}
      {q : List V × (List (DDC.CIn U Y) × List X)},
      (l = [] ∧ usPre = [] ∧ ys = [] ∨
        (ParsesTo α l (usPre, ys) ∧ ∃ v, Sum.inr v ∈ α (usPre, ys))) →
      q ∈ DDC.driveFrom (toDDC α) S (l, xs) rest →
      ∃ fuel ys', (q.1, q.2.2, ys') ∈ driveOuter α S fuel usPre xs ys rest := by
  intro rest
  induction rest with
  | nil =>
      intro l usPre xs ys q _ hq
      simp only [DDC.driveFrom, Part.mem_some_iff] at hq
      subst hq
      exact ⟨0, ys, by simp [driveOuter]⟩
  | cons u rest ih =>
      intro l usPre xs ys q hready hq
      simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at hq
      obtain ⟨r, hres, rr, htail, rfl⟩ := hq
      have hparse : ParsesTo α (l ++ [Sum.inl (InLabel.outside, u)])
          (usPre ++ [u], ys) := by
        rcases hready with ⟨rfl, rfl, rfl⟩ | ⟨hp', v, hv⟩
        · simpa using parsesTo_singleton α u
        · exact parsesTo_snoc_out hp' hv u
      obtain ⟨fuel₁, ys₁, hdrive, hp1, hp2⟩ :=
        drive_of_resolve_toDDC α S hres (usPre ++ [u]) ys hparse
      obtain ⟨fuel₂, ys₂, htail₂⟩ := ih (Or.inr ⟨hp1, r.1, hp2⟩) htail
      refine ⟨max fuel₁ fuel₂, ys₂, ?_⟩
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r.1, r.2.2, ys₁),
        drive_mono_le α S (le_max_left _ _) hdrive,
        (rr.1, rr.2.2, ys₂),
        driveOuter_mono_le α S (le_max_right _ _) htail₂, rfl⟩

/-- **The ν-level realization theorem** (DESIGN §10.5): CR18 Def 3.9 applied
to the canonical Def 3.8 object of a protocol function *is* the
transcript-equation solution — for arbitrary converters, cross-round memory
included.  Subsumes `apply_ofStep` conceptually (the outer-memoryless case)
and turns converter equations into `drive` computations. -/
theorem apply_toDDC (α : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    DDC.apply (toDDC α) S = apply α S := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (DDC.apply (toDDC α) S).1 = DDC.applyRaw (toDDC α) S from rfl,
    show (apply α S).1 = applyRaw α S from rfl,
    DDC.mem_apply_iff, mem_applyRaw]
  constructor
  · rintro ⟨r, hr, hlast⟩
    obtain ⟨fuel, ys', hmem⟩ := driveOuter_of_driveFrom_toDDC α S
      (Or.inl ⟨rfl, rfl, rfl⟩) hr
    exact ⟨fuel, (mem_applyRawAt_iff α S fuel us v).mpr
      ⟨(r.1, r.2.2, ys'), hmem, hlast⟩⟩
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hmem, hlast⟩ := hv
    obtain ⟨l', hr⟩ := driveFrom_toDDC_of_driveOuter α S
      (Or.inl ⟨rfl, rfl, rfl⟩) hmem
    exact ⟨(r.1, (l', r.2.1)), hr, hlast⟩

/-! ### Prefix-closed restrictions

The identity restriction converter realizes the corresponding deterministic
domain restriction.  This is the general mechanism behind both `[q]` and
history-dependent restrictions such as CBC's `θr`. -/

section RestrictionInstance

variable {X : Type z} {Y : Type v}

theorem restrictionFn_inl_elim {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ restrictionFn P (us, ys)) :
    ∃ hne : us ≠ [],
      x = us.getLast hne ∧ us.length = ys.length + 1 ∧ P us := by
  have hshape := restrictionFn_inl_inv h
  obtain ⟨hne, hvalue⟩ := restrictionFn_inl_val h
  exact ⟨hne, hvalue, hshape⟩

theorem restrictionFn_inr_elim {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {v : Y}
    (h : Sum.inr v ∈ restrictionFn P (us, ys)) :
    ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some v ∧
        us.length = ys.length ∧ P us := by
  obtain ⟨hlen, hP, h0, hy⟩ := restrictionFn_inr_inv h
  exact ⟨h0, hy, hlen, hP⟩

/-- One admitted restriction round, destructed. -/
theorem drive_restrictionFn_round_elim
    {P : List X → Prop} [DecidablePred P] {S : PFunDDS.DDS X Y}
    {us : List X} {ys : List (Option Y)} {fuel : ℕ} {xs : List X}
    {p : Y × List X × List (Option Y)}
    (hlen : us.length = ys.length + 1)
    (hp : p ∈ drive (restrictionFn P) S fuel us xs ys) :
    ∃ (hne : us ≠ []) (y : Y), P us ∧
      PFunDDS.output (S⊥) (xs ++ [us.getLast hne])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y ∧
      p = (y, xs ++ [us.getLast hne], ys ++ [some y]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hne, rfl, -, hP⟩ := restrictionFn_inl_elim hm
      rcases fuel with _ | fuel
      · simp [drive] at hp'
      · rcases drive_succ_elim hp' with ⟨x₂, hm₂, hp''⟩ | ⟨v₂, hm₂, rfl⟩
        · obtain ⟨hshape, -⟩ := restrictionFn_inl_inv hm₂
          exfalso
          simp only [List.length_append, List.length_singleton] at hshape
          omega
        · obtain ⟨h0, hv₂, -, -⟩ := restrictionFn_inr_elim hm₂
          rw [List.getLast_append_singleton] at hv₂
          refine ⟨hne, v₂, hP, hv₂, ?_⟩
          rw [hv₂]
    · obtain ⟨-, -, hshape, -⟩ := restrictionFn_inr_elim hm
      exfalso
      omega

/-- One admitted restriction round, constructed from a proper system answer. -/
theorem drive_restrictionFn_round_mem
    (P : List X → Prop) [DecidablePred P] (S : PFunDDS.DDS X Y)
    {us : List X} {ys : List (Option Y)}
    (hlen : us.length = ys.length + 1) (hP : P us)
    (xs : List X) {y : Y} (hne : us ≠ [])
    (hy : PFunDDS.output (S⊥) (xs ++ [us.getLast hne])
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some y) :
    (y, xs ++ [us.getLast hne], ys ++ [some y]) ∈
      drive (restrictionFn P) S 2 us xs ys := by
  have hm : Sum.inl (us.getLast hne) ∈ restrictionFn P (us, ys) :=
    restrictionFn_inl_mem P hlen hP
  refine drive_mem_query (restrictionFn P) S hm ?_
  rw [hy]
  have hm₂ : Sum.inr y ∈ restrictionFn P (us, ys ++ [some y]) := by
    refine restrictionFn_inr_mem P (by simp [hlen]) (by simp) hP ?_
    rw [List.getLast_append_singleton]
  exact drive_mem_answer (restrictionFn P) S hm₂ 0

/-- Forward realization of an admitted outer history. -/
theorem driveOuter_restrictionFn_of_dom
    (P : List X → Prop) [DecidablePred P] (hP : PrefixClosed P)
    (S : PFunDDS.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)),
      xs.length = ys.length →
      P (xs ++ rest) →
      (xs ++ rest ∈ PFunDDS.dom S ∨ rest = []) →
      ∃ vs ys',
        (vs, xs ++ rest, ys') ∈
          driveOuter (restrictionFn P) S 2 xs xs ys rest ∧
        ∀ (h : xs ++ rest ∈ PFunDDS.dom S), rest ≠ [] →
          vs.getLast? = some (PFunDDS.output S (xs ++ rest) h) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys hlen hadmit hdom
      have hdom' : xs ++ u :: rest ∈ PFunDDS.dom S := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hxs : xs ∈ PFunDDS.dom S ∨ xs = [] := by
        rcases eq_or_ne xs [] with h | h
        · exact Or.inr h
        · exact Or.inl (PFunDDS.prefix_closed S ⟨u :: rest, rfl⟩ h hdom')
      have hnext : xs ++ [u] ∈ PFunDDS.dom S :=
        PFunDDS.prefix_closed S ⟨rest, by simp⟩ (by simp) hdom'
      have hadmitNext : P (xs ++ [u]) :=
        hP ⟨rest, by simp⟩ hadmit
      have hout : PFunDDS.output (S⊥) (xs ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (PFunDDS.output S (xs ++ [u]) hnext) :=
        PFunDDS.output_fullyDefined_append_of_mem S xs u hxs hnext
      have hgl : (xs ++ [u]).getLast (by simp) = u :=
        List.getLast_append_singleton xs
      have hy' : PFunDDS.output (S⊥) (xs ++ [(xs ++ [u]).getLast (by simp)])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (PFunDDS.output S (xs ++ [u]) hnext) :=
        (PFunDDS.output_congr (S⊥) (by rw [hgl])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).trans hout
      have hround := drive_restrictionFn_round_mem P S (us := xs ++ [u])
        (ys := ys) (by simp [hlen]) hadmitNext xs (by simp) hy'
      rw [hgl] at hround
      obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (xs ++ [u])
        (ys ++ [some (PFunDDS.output S (xs ++ [u]) hnext)]) (by simp [hlen])
        (by simpa [List.append_assoc] using hadmit)
        (Or.inl (by simpa [List.append_assoc] using hdom'))
      refine ⟨PFunDDS.output S (xs ++ [u]) hnext :: vs', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(PFunDDS.output S (xs ++ [u]) hnext, xs ++ [u],
          ys ++ [some (PFunDDS.output S (xs ++ [u]) hnext)]), hround,
          (vs', (xs ++ [u]) ++ rest, ys''), hmem', by simp [List.append_assoc]⟩
      · intro h hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length (restrictionFn P) S 2 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length (restrictionFn P) S 2 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have h' : (xs ++ [u]) ++ rest ∈ PFunDDS.dom S := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg some (PFunDDS.output_congr S (by simp) h' h)

/-- Backward realization: every defined nonempty run certifies both the
underlying system domain and the restriction predicate. -/
theorem driveOuter_restrictionFn_mem_imp
    (P : List X → Prop) [DecidablePred P] (S : PFunDDS.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)) {fuel : ℕ}
      {r : List Y × List X × List (Option Y)},
      xs.length = ys.length →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r ∈ driveOuter (restrictionFn P) S fuel xs xs ys rest →
      r.2.1 = xs ++ rest ∧
        (rest ≠ [] → P (xs ++ rest) ∧
          ∃ h : xs ++ rest ∈ PFunDDS.dom S,
            r.1.getLast? = some (PFunDDS.output S (xs ++ rest) h)) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys fuel r _ _ hr
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys fuel r hlen hxs hr
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hne₁, y, hadmit₁, hy, rfl⟩ :=
        drive_restrictionFn_round_elim (by simp [hlen]) hr₁
      have hgl : (xs ++ [u]).getLast hne₁ = u :=
        List.getLast_append_singleton xs
      rw [hgl] at hrr
      have hy' : PFunDDS.output (S⊥) (xs ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some y :=
        ((PFunDDS.output_congr (S⊥) (by rw [hgl])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).symm).trans hy
      obtain ⟨hnext, houtS⟩ :=
        PFunDDS.mem_of_output_fullyDefined_append_eq_some S xs u hxs hy'
      obtain ⟨hthread, hcond⟩ := ih (xs ++ [u]) (ys ++ [some y])
        (by simp [hlen]) (Or.inl hnext) hrr
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨by simpa using hadmit₁, by simpa using hnext, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some ?_
          rw [PFunDDS.output_congr S (l₂ := xs ++ [u]) (by simp) _ hnext,
            houtS]
      | cons r0 rs0 =>
          obtain ⟨hadmit', h', hlast'⟩ := hcond (by simp [hrest])
          refine ⟨by simpa [List.append_assoc, hrest] using hadmit',
            by simpa [List.append_assoc, hrest] using h', ?_⟩
          have hlenrr := driveOuter_length (restrictionFn P) S fuel hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              exact congrArg some
                (PFunDDS.output_congr S (by simp [hrest]) h' _)

/-- The transcript-equation application of the identity restriction converter
is exactly the corresponding DDS domain restriction. -/
theorem apply_restrictionFn
    (P : List X → Prop) [DecidablePred P] (hP : PrefixClosed P)
    (S : PFunDDS.DDS X Y) :
    apply (restrictionFn P) S = PFunDDS.filterDom P hP S := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (apply (restrictionFn P) S).1 =
      applyRaw (restrictionFn P) S from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (restrictionFn P) S fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨-, hcond⟩ :=
      driveOuter_restrictionFn_mem_imp P S us [] [] rfl (Or.inr rfl) hr
    obtain ⟨hadmit, h, hout⟩ := hcond hne
    rw [hlast] at hout
    have hv' := Option.some.inj hout
    refine ⟨⟨h, hadmit⟩, ?_⟩
    show PFunDDS.output S us _ = v
    rw [hv']
    exact PFunDDS.output_congr S (by simp) _ h
  · rintro ⟨⟨hd, hadmit⟩, rfl⟩
    have hdom : us ∈ PFunDDS.dom S := hd
    have hne : us ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem S hdom
    obtain ⟨vs, ys', hmem, hlast⟩ :=
      driveOuter_restrictionFn_of_dom P hP S us [] [] rfl
        (by simpa using hadmit) (Or.inl (by simpa using hdom))
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, [] ++ us, ys'), hmem, ?_⟩
    rw [hlast (by simpa using hdom) hne]
    exact congrArg some (PFunDDS.output_congr S (by simp) _ hd)

end RestrictionInstance

/-! ### The `[q]` instance: the first cross-round converter, computed

`queryLimitFn q` (a round counter — outside every `ofStep` class) applied by
the transcript equations *is* the canonical CR18 Def 3.10 restriction
`filterQueries q`.  Combined with the pre-existing operational theorem, the
old `[q]ᶠ` DDC and `toDDC (queryLimitFn q)` are apply-equal representatives
of the same converter — the bespoke trace proof is retired as the "factors
through lengths" instance of the realization theorem. -/

section QueryLimitInstance

variable {X : Type z} {Y : Type v}

theorem queryLimitFn_inl_elim {q : ℕ} {us : List X} {ys : List (Option Y)}
    {x : X} (h : Sum.inl x ∈ queryLimitFn q (us, ys)) :
    ∃ hne : us ≠ [],
      x = us.getLast hne ∧ us.length = ys.length + 1 ∧ us.length ≤ q := by
  have hlen := queryLimitFn_inl_inv h
  refine ⟨by apply List.ne_nil_of_length_pos; omega, ?_, hlen⟩
  have hval : queryLimitFn q (us, ys) = Part.some (Sum.inl (us.getLast (by
      apply List.ne_nil_of_length_pos; omega))) := by
    simp only [queryLimitFn]
    rw [dif_pos hlen]
  rw [hval, Part.mem_some_iff] at h
  exact Sum.inl.inj h

theorem queryLimitFn_inr_elim {q : ℕ} {us : List X} {ys : List (Option Y)}
    {v : Y} (h : Sum.inr v ∈ queryLimitFn q (us, ys)) :
    ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some v ∧
        us.length = ys.length ∧ us.length ≤ q := by
  obtain ⟨h1, h3, h0, hy⟩ := queryLimitFn_inr_inv h
  exact ⟨h0, hy, h1, h3⟩

/-- One `[q]` round, destructed: forward the last outer input, return the
system's (proper, `some`) answer, budget respected — an improper answer `⊥`
silences the round, so a completed round certifies someness. -/
theorem drive_queryLimitFn_round_elim {q : ℕ} {S : PFunDDS.DDS X Y}
    {us : List X} {ys : List (Option Y)} {fuel : ℕ} {xs : List X}
    {p : Y × List X × List (Option Y)}
    (hlen : us.length = ys.length + 1)
    (hp : p ∈ drive (queryLimitFn q) S fuel us xs ys) :
    ∃ (hne : us ≠ []) (y : Y), us.length ≤ q ∧
      PFunDDS.output (S⊥) (xs ++ [us.getLast hne])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y ∧
      p = (y, xs ++ [us.getLast hne], ys ++ [some y]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hne, rfl, -, hq⟩ := queryLimitFn_inl_elim hm
      rcases fuel with _ | fuel
      · simp [drive] at hp'
      · rcases drive_succ_elim hp' with ⟨x₂, hm₂, hp''⟩ | ⟨v₂, hm₂, rfl⟩
        · obtain ⟨h2, -⟩ := queryLimitFn_inl_inv hm₂
          exfalso
          simp only [List.length_append, List.length_singleton] at h2
          omega
        · obtain ⟨h0, hv₂, -, -⟩ := queryLimitFn_inr_elim hm₂
          rw [List.getLast_append_singleton] at hv₂
          refine ⟨hne, v₂, hq, hv₂, ?_⟩
          rw [hv₂]
    · obtain ⟨-, -, h2, -⟩ := queryLimitFn_inr_elim hm
      exfalso
      omega

/-- One `[q]` round, constructed (from a someness witness for the `S⊥`
answer). -/
theorem drive_queryLimitFn_round_mem (q : ℕ) (S : PFunDDS.DDS X Y)
    {us : List X} {ys : List (Option Y)} (hlen : us.length = ys.length + 1)
    (hq : us.length ≤ q) (xs : List X) {y : Y} (hne : us ≠ [])
    (hy : PFunDDS.output (S⊥) (xs ++ [us.getLast hne])
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some y) :
    (y, xs ++ [us.getLast hne], ys ++ [some y]) ∈
      drive (queryLimitFn q) S 2 us xs ys := by
  have hm : Sum.inl (us.getLast hne) ∈ queryLimitFn q (us, ys) :=
    queryLimitFn_inl_mem q hlen hq
  refine drive_mem_query (queryLimitFn q) S hm ?_
  rw [hy]
  have hm₂ : Sum.inr y ∈ queryLimitFn q (us, ys ++ [some y]) := by
    refine queryLimitFn_inr_mem q (by simp [hlen]) (by simp) hq ?_
    rw [List.getLast_append_singleton]
  exact drive_mem_answer (queryLimitFn q) S hm₂ 0

/-- Forward run of `[q]` over a whole outer history (fuel 2 suffices). -/
theorem driveOuter_queryLimitFn_of_dom (q : ℕ) (S : PFunDDS.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)),
      xs.length = ys.length →
      xs.length + rest.length ≤ q →
      (xs ++ rest ∈ PFunDDS.dom S ∨ rest = []) →
      ∃ vs ys',
        (vs, xs ++ rest, ys') ∈
          driveOuter (queryLimitFn q) S 2 xs xs ys rest ∧
        ∀ (h : xs ++ rest ∈ PFunDDS.dom S), rest ≠ [] →
          vs.getLast? = some (PFunDDS.output S (xs ++ rest) h) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys hlen hbudget hdom
      have hdom' : xs ++ u :: rest ∈ PFunDDS.dom S := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hxs : xs ∈ PFunDDS.dom S ∨ xs = [] := by
        rcases eq_or_ne xs [] with h | h
        · exact Or.inr h
        · exact Or.inl (PFunDDS.prefix_closed S ⟨u :: rest, rfl⟩ h hdom')
      have hnext : xs ++ [u] ∈ PFunDDS.dom S :=
        PFunDDS.prefix_closed S ⟨rest, by simp⟩ (by simp) hdom'
      have hout : PFunDDS.output (S⊥) (xs ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (PFunDDS.output S (xs ++ [u]) hnext) :=
        PFunDDS.output_fullyDefined_append_of_mem S xs u hxs hnext
      have hgl : (xs ++ [u]).getLast (by simp) = u :=
        List.getLast_append_singleton xs
      have hy' : PFunDDS.output (S⊥) (xs ++ [(xs ++ [u]).getLast (by simp)])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          = some (PFunDDS.output S (xs ++ [u]) hnext) :=
        (PFunDDS.output_congr (S⊥) (by rw [hgl])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).trans hout
      have hround := drive_queryLimitFn_round_mem q S (us := xs ++ [u])
        (ys := ys) (by simp [hlen])
        (by
          simp only [List.length_cons] at hbudget
          simp only [List.length_append, List.length_singleton]
          omega)
        xs (by simp) hy'
      rw [hgl] at hround
      have hbudget' : (xs ++ [u]).length + rest.length ≤ q := by
        simp only [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hbudget
        omega
      obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (xs ++ [u])
        (ys ++ [some (PFunDDS.output S (xs ++ [u]) hnext)]) (by simp [hlen])
        hbudget' (Or.inl (by simpa [List.append_assoc] using hdom'))
      refine ⟨PFunDDS.output S (xs ++ [u]) hnext :: vs', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(PFunDDS.output S (xs ++ [u]) hnext, xs ++ [u],
          ys ++ [some (PFunDDS.output S (xs ++ [u]) hnext)]), hround,
          (vs', (xs ++ [u]) ++ rest, ys''), hmem', by simp [List.append_assoc]⟩
      · intro h hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length (queryLimitFn q) S 2 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length (queryLimitFn q) S 2 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have h' : (xs ++ [u]) ++ rest ∈ PFunDDS.dom S := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg some (PFunDDS.output_congr S (by simp) h' h)

/-- Backward run analysis of `[q]`: a defined run certifies the domain
membership round by round (the `some`-witness of each completed round is
cashed through `S⊥`, anchored at an in-dom-or-empty inner history). -/
theorem driveOuter_queryLimitFn_mem_imp (q : ℕ) (S : PFunDDS.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)) {fuel : ℕ}
      {r : List Y × List X × List (Option Y)},
      xs.length = ys.length →
      (xs ∈ PFunDDS.dom S ∨ xs = []) →
      r ∈ driveOuter (queryLimitFn q) S fuel xs xs ys rest →
      r.2.1 = xs ++ rest ∧
        (rest ≠ [] → xs.length + rest.length ≤ q ∧
          ∃ h : xs ++ rest ∈ PFunDDS.dom S,
            r.1.getLast? = some (PFunDDS.output S (xs ++ rest) h)) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys fuel r _ _ hr
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys fuel r hlen hxs hr
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hne₁, y, hq₁, hy, rfl⟩ :=
        drive_queryLimitFn_round_elim (by simp [hlen]) hr₁
      have hgl : (xs ++ [u]).getLast hne₁ = u :=
        List.getLast_append_singleton xs
      rw [hgl] at hrr
      have hy' : PFunDDS.output (S⊥) (xs ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some y :=
        ((PFunDDS.output_congr (S⊥) (by rw [hgl])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
          (by rw [PFunDDS.dom_fullyDefined]; simp)).symm).trans hy
      obtain ⟨hnext, houtS⟩ :=
        PFunDDS.mem_of_output_fullyDefined_append_eq_some S xs u hxs hy'
      obtain ⟨hthread, hcond⟩ := ih (xs ++ [u]) (ys ++ [some y])
        (by simp [hlen]) (Or.inl hnext) hrr
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨?_, by simpa using hnext, ?_⟩
          · simp only [List.length_cons, List.length_nil]
            simp only [List.length_append, List.length_singleton] at hq₁
            omega
          · rw [List.getLast?_singleton]
            refine congrArg some ?_
            rw [PFunDDS.output_congr S (l₂ := xs ++ [u]) (by simp) _ hnext,
              houtS]
      | cons r0 rs0 =>
          obtain ⟨hbudget', h', hlast'⟩ := hcond (by simp [hrest])
          rw [hrest] at hbudget'
          refine ⟨?_, by simpa [List.append_assoc, hrest] using h', ?_⟩
          · simp only [List.length_append, List.length_cons,
              List.length_nil] at hbudget' ⊢
            omega
          · have hlenrr := driveOuter_length (queryLimitFn q) S fuel hrr
            cases hrr1 : rr.1 with
            | nil =>
                rw [hrr1] at hlenrr
                simp [hrest] at hlenrr
            | cons v0 vs0 =>
                rw [hrr1] at hlast'
                rw [List.getLast?_cons_cons, hlast']
                exact congrArg some
                  (PFunDDS.output_congr S (by simp [hrest]) h' _)

/-- **The `[q]` filter, computed by the transcript equations**: the ν-level
application of the round-counter protocol function is exactly CR18
Def 3.10's canonical restriction.  Out-of-dom queries answer `⊥`, on which
`queryLimitFn` is silent — the drive has no result, matching the restricted
domain. -/
theorem apply_queryLimitFn (q : ℕ) (S : PFunDDS.DDS X Y) :
    apply (queryLimitFn q) S = PFunDDS.filterQueries q S := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (apply (queryLimitFn q) S).1
      = applyRaw (queryLimitFn q) S from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (queryLimitFn q) S fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨-, hcond⟩ :=
      driveOuter_queryLimitFn_mem_imp q S us [] [] rfl (Or.inr rfl) hr
    obtain ⟨hbudget, h, hout⟩ := hcond hne
    rw [hlast] at hout
    have hv' := Option.some.inj hout
    refine ⟨⟨h, by simpa using hbudget⟩, ?_⟩
    show PFunDDS.output S us _ = v
    rw [hv']
    exact PFunDDS.output_congr S (by simp) _ h
  · rintro ⟨⟨hd, hq⟩, rfl⟩
    have hdom : us ∈ PFunDDS.dom S := hd
    have hne : us ≠ [] := by
      rintro rfl
      exact PFunDDS.empty_not_mem S hdom
    obtain ⟨vs, ys', hmem, hlast⟩ :=
      driveOuter_queryLimitFn_of_dom q S us [] [] rfl (by simpa using hq)
        (Or.inl (by simpa using hdom))
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, [] ++ us, ys'), hmem, ?_⟩
    rw [hlast (by simpa using hdom) hne]
    exact congrArg some (PFunDDS.output_congr S (by simp) _ hd)

/-- Def 3.9 applied to the canonical `[q]` object = Def 3.10's restriction. -/
theorem apply_toDDC_queryLimitFn (q : ℕ) (S : PFunDDS.DDS X Y) :
    DDC.apply (toDDC (queryLimitFn q)) S = PFunDDS.filterQueries q S := by
  rw [apply_toDDC, apply_queryLimitFn]

/-- **Two representatives, one converter**: the old operational `[q]ᶠ` DDC
and the canonical `toDDC (queryLimitFn q)` are apply-equal — both realize
`filterQueries q`.  This retires `queryLimit`-style bespoke trace proofs: the
ν route re-proves the same theorem as an instance of `apply_toDDC`. -/
theorem queryLimit_apply_eq_toDDC (q : ℕ) (S : PFunDDS.DDS X Y) :
    DDC.apply (queryLimit q : Filter X Y) S
      = DDC.apply (toDDC (queryLimitFn q)) S := by
  rw [apply_toDDC_queryLimitFn]
  exact queryLimit_filter_apply_eq_filterQueries q S

end QueryLimitInstance

/-! ### `toNu` and the round-trip: junk-free ν ≅ normalized DDC

`toNu α` reads an arbitrary Def 3.8 DDC back as a protocol function: its
value at a pair is the DDC's move at the pair's canonical trace (the
interleaving the DDC itself dictates, `DDCTrace`).  The round-trip
`toNu (toDDC ν) = normalize ν` says the ν-world is exactly the junk-free
quotient of the DDC-world. -/

section ToNu

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- The canonical trace of a pair under an arbitrary DDC: outer inputs and
inner answers (`⊥` included — the Def 3.8 alphabet) delivered in the order
the DDC's own moves dictate. -/
inductive DDCTrace (α : DDC U V X Y) :
    List (DDC.CIn U Y) → List U × List (Option Y) → Prop
  | first (u : U) : DDCTrace α [Sum.inl (InLabel.outside, u)] ([u], [])
  | next {c us ys v} (ht : DDCTrace α c (us, ys))
      (hv : Sum.inl (InLabel.outside, v) ∈ α.1 c) (u : U) :
      DDCTrace α (c ++ [Sum.inl (InLabel.outside, u)]) (us ++ [u], ys)
  | answer {c us ys x} (ht : DDCTrace α c (us, ys))
      (hx : Sum.inr (InLabel.inside, x) ∈ α.1 c) (y : Option Y) :
      DDCTrace α (c ++ [Sum.inr (InLabel.inside, y)]) (us, ys ++ [y])

/-- Decode a converter-output move back to a protocol move (partial inverse
of `DDC.moveOf`; junk labels have no decoding). -/
def fromCOut : DDC.COut V X → Part (X ⊕ V)
  | Sum.inl (InLabel.outside, v) => Part.some (Sum.inr v)
  | Sum.inr (InLabel.inside, x) => Part.some (Sum.inl x)
  | _ => Part.none

@[simp] theorem fromCOut_moveOf (m : X ⊕ V) :
    fromCOut (DDC.moveOf m) = Part.some m := by
  cases m <;> rfl

/-- **A DDC as a protocol function**: the move at the pair's canonical
trace. -/
noncomputable def toNu (α : DDC U V X Y) : ProtocolFn U V X Y := fun p =>
  Part.assert (∃ c, DDCTrace α c p) fun h =>
    (α.1 h.choose).bind fromCOut

/-- Canonical traces of `toDDC ν` are ν-parses. -/
theorem ddcTrace_toDDC_parses {ν : ProtocolFn U V X Y}
    {c : List (DDC.CIn U Y)} {p : List U × List (Option Y)}
    (h : DDCTrace (toDDC ν) c p) : ParsesTo ν c p := by
  induction h with
  | first u => exact parsesTo_singleton ν u
  | next ht hv u ih =>
      rw [toDDC_toPFun, mem_toDDCRaw_iff] at hv
      obtain ⟨q, hq, mm, hmm, heq⟩ := hv
      obtain rfl := parsesTo_unique hq ih
      have hmv : mm = Sum.inr _ := moveOf_eq_out_iff.mp heq.symm
      subst hmv
      exact parsesTo_snoc_out ih hmm u
  | answer ht hx y ih =>
      rw [toDDC_toPFun, mem_toDDCRaw_iff] at hx
      obtain ⟨q, hq, mm, hmm, heq⟩ := hx
      obtain rfl := parsesTo_unique hq ih
      have hmv : mm = Sum.inl _ := moveOf_eq_in_iff.mp heq.symm
      subst hmv
      exact parsesTo_snoc_in ih hmm y

/-- Every reachable pair has a canonical trace, both as a ν-parse and as a
`toDDC ν`-trace. -/
theorem reach_toDDC_trace {ν : ProtocolFn U V X Y}
    {p : List U × List (Option Y)} (h : Reach ν p) :
    ∃ c, ParsesTo ν c p ∧ DDCTrace (toDDC ν) c p := by
  induction h with
  | first u => exact ⟨_, parsesTo_singleton ν u, DDCTrace.first u⟩
  | answer hr hx y ih =>
      rename_i q x
      obtain ⟨c, hp, ht⟩ := ih
      refine ⟨_, parsesTo_snoc_in hp hx y, DDCTrace.answer (x := x) ht ?_ y⟩
      simpa [DDC.moveOf] using mem_toDDC_of_parses hp hx
  | next hr hv u ih =>
      rename_i q v
      obtain ⟨c, hp, ht⟩ := ih
      refine ⟨_, parsesTo_snoc_out hp hv u, DDCTrace.next (v := v) ht ?_ u⟩
      simpa [DDC.moveOf] using mem_toDDC_of_parses hp hv

/-- **The round-trip**: reading the canonical Def 3.8 object of ν back as a
protocol function yields exactly ν's junk-free normalization — the ν-world
is the junk-free quotient of the DDC-world. -/
theorem toNu_toDDC (ν : ProtocolFn U V X Y) :
    toNu (toDDC ν) = normalize ν := by
  funext p
  apply Part.ext
  intro m
  simp only [toNu, Part.mem_assert_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨hex, o, ho, hfrom⟩
    have hp₀ : ParsesTo ν hex.choose p :=
      ddcTrace_toDDC_parses hex.choose_spec
    rw [toDDC_toPFun, mem_toDDCRaw_iff] at ho
    obtain ⟨q, hq, mm, hmm, rfl⟩ := ho
    obtain rfl := parsesTo_unique hq hp₀
    rw [fromCOut_moveOf, Part.mem_some_iff] at hfrom
    subst hfrom
    exact (mem_normalize_iff ν _ _).mpr ⟨hmm, hq.reach⟩
  · intro hm
    obtain ⟨hmem, hreach⟩ := (mem_normalize_iff ν p m).mp hm
    obtain ⟨c, hp, ht⟩ := reach_toDDC_trace hreach
    refine ⟨⟨c, ht⟩, ?_⟩
    have hp₀ : ParsesTo ν
        (Exists.choose (⟨c, ht⟩ : ∃ c, DDCTrace (toDDC ν) c p)) p :=
      ddcTrace_toDDC_parses
        (Exists.choose_spec (⟨c, ht⟩ : ∃ c, DDCTrace (toDDC ν) c p))
    exact ⟨DDC.moveOf m, mem_toDDC_of_parses hp₀ hmem,
      by rw [fromCOut_moveOf]; exact Part.mem_some _⟩

/-- Junk-free protocol functions round-trip on the nose. -/
theorem toNu_toDDC_of_junkFree {ν : ProtocolFn U V X Y} (h : JunkFree ν) :
    toNu (toDDC ν) = ν := by
  rw [toNu_toDDC, normalize_eq_self_of_junkFree h]

end ToNu

/-! ### Drive congruence: application sees a protocol only where the drive goes

The trace tree (`Reach`) quantifies over *every* answer, because a converter does
not know the system it will meet.  A single application does know: `drive`
consults `ν` at `(us, ys)` where `ys` is exactly the list of answers **this**
system gave to the queries `ν` has issued so far.  Two protocol functions that
agree at every pair one application actually visits therefore have the same
application at that system, even when they are not `TraceEquiv` — the tree
distinguishes them on answers the system never produces.

`DriveReach ν S us xs` is that visited set, indexed by the outer history and the
issued inner history; the answer history is recovered from the latter by
`sysAnswers`, which is the invariant `drive` maintains.

This is what lets a *count-attributing* converter (`ofHistoryStepPartial`, silent
on an answer it cannot attribute — Def 3.8's citizen) be evaluated by the law of
the *tag-filtering* one (`PFunConverter.par`, which is not one): against a
tag-faithful system the two never disagree. -/

section DriveCongruence

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- The system's own answer to an inner history, in Def 3.3's completion —
exactly the value `drive` appends.  Def 3.3's completion is defined on nonempty
histories only, and `drive` only ever consults it at one (`xs ++ [x]`); the
empty case is a junk value never reached. -/
noncomputable def sysAnswer (S : PFunDDS.DDS X Y) (xs : List X) : Option Y :=
  if h : xs ≠ [] then
    PFunDDS.output (S⊥) xs (by rw [PFunDDS.dom_fullyDefined]; exact h)
  else none

theorem sysAnswer_of_ne_nil (S : PFunDDS.DDS X Y) {xs : List X} (hne : xs ≠ [])
    (h : xs ∈ PFunDDS.dom (S⊥)) : sysAnswer S xs = PFunDDS.output (S⊥) xs h := by
  rw [sysAnswer, dif_pos hne]

/-- The answer history a system produces along an inner history: the invariant
`drive` threads in its third argument. -/
noncomputable def sysAnswers (S : PFunDDS.DDS X Y) (xs : List X) :
    List (Option Y) :=
  (List.range xs.length).map fun k => sysAnswer S (xs.take (k + 1))

@[simp]
theorem sysAnswers_nil (S : PFunDDS.DDS X Y) : sysAnswers S [] = [] := by
  simp [sysAnswers]

@[simp]
theorem sysAnswers_length (S : PFunDDS.DDS X Y) (xs : List X) :
    (sysAnswers S xs).length = xs.length := by
  simp [sysAnswers]

/-- The system's answer depends on the inner history only through its value —
the transport that the dependent `PFunDDS.output` proof argument blocks `rw`
from doing. -/
theorem sysAnswer_congr (S : PFunDDS.DDS X Y) {xs xs' : List X} (h : xs = xs') :
    sysAnswer S xs = sysAnswer S xs' := by
  subst h; rfl

/-- One further query appends exactly one further system answer. -/
theorem sysAnswers_concat (S : PFunDDS.DDS X Y) (xs : List X) (x : X) :
    sysAnswers S (xs ++ [x]) = sysAnswers S xs ++ [sysAnswer S (xs ++ [x])] := by
  simp only [sysAnswers, List.length_append, List.length_singleton,
    List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left ?_
    intro k hk
    rw [List.mem_range] at hk
    exact sysAnswer_congr S (List.take_append_of_le_length (by omega))
  · exact congrArg (fun value => [value])
      (sysAnswer_congr S (List.take_of_length_le (by simp)))

/-- The append form `drive` actually produces. -/
theorem sysAnswers_concat_output (S : PFunDDS.DDS X Y) (xs : List X) (x : X)
    (h : xs ++ [x] ∈ PFunDDS.dom (S⊥)) :
    sysAnswers S xs ++ [PFunDDS.output (S⊥) (xs ++ [x]) h] =
      sysAnswers S (xs ++ [x]) := by
  rw [sysAnswers_concat, sysAnswer_of_ne_nil S (by simp) h]

/-- **The pairs one application visits**: the outer history `us` and the inner
history `xs` that `ν` has issued against `S`.  A query extends `xs`; an outer
answer extends `us`.  The answer history never appears — it is `sysAnswers S xs`
throughout, which is precisely the difference from `Reach`. -/
inductive DriveReach (ν : ProtocolFn U V X Y) (S : PFunDDS.DDS X Y) :
    List U → List X → Prop
  | start (u : U) : DriveReach ν S [u] []
  | query {us : List U} {xs : List X} {x : X} (h : DriveReach ν S us xs)
      (hx : Sum.inl x ∈ ν (us, sysAnswers S xs)) : DriveReach ν S us (xs ++ [x])
  | next {us : List U} {xs : List X} {v : V} (h : DriveReach ν S us xs)
      (hv : Sum.inr v ∈ ν (us, sysAnswers S xs)) (u : U) :
      DriveReach ν S (us ++ [u]) xs

/-- A completed round leaves the visited set intact and exposes the answer move
that closed it. -/
theorem drive_mem_driveReach {ν : ProtocolFn U V X Y} {S : PFunDDS.DDS X Y} :
    ∀ {fuel : ℕ} {us : List U} {xs : List X}
      {r : V × List X × List (Option Y)},
      DriveReach ν S us xs → r ∈ drive ν S fuel us xs (sysAnswers S xs) →
        r.2.2 = sysAnswers S r.2.1 ∧ DriveReach ν S us r.2.1 ∧
          Sum.inr r.1 ∈ ν (us, sysAnswers S r.2.1) := by
  intro fuel
  induction fuel with
  | zero => intro us xs r _ h; simp [drive] at h
  | succ n ih =>
      intro us xs r hreach h
      rcases drive_succ_elim h with ⟨x, hm, h⟩ | ⟨v, hm, rfl⟩
      · rw [sysAnswers_concat_output S xs x
          (by rw [PFunDDS.dom_fullyDefined]; simp)] at h
        exact ih (DriveReach.query hreach hm) h
      · exact ⟨rfl, hreach, hm⟩

/-- The drive cannot tell two protocols apart at a visited pair. -/
theorem drive_congr_of_driveReach {ν ν' : ProtocolFn U V X Y} {S : PFunDDS.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) :
    ∀ (fuel : ℕ) (us : List U) (xs : List X), DriveReach ν S us xs →
      drive ν S fuel us xs (sysAnswers S xs) =
        drive ν' S fuel us xs (sysAnswers S xs) := by
  intro fuel
  induction fuel with
  | zero => intro us xs _; rfl
  | succ n ih =>
      intro us xs hreach
      have hstep := agree us xs hreach
      have hcat : ∀ x : X, (sysAnswers S xs ++
          [PFunDDS.output (S⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp)]) =
          sysAnswers S (xs ++ [x]) :=
        fun x => sysAnswers_concat_output S xs x _
      apply Part.ext
      intro r
      constructor
      · intro hr
        rcases drive_succ_elim hr with ⟨x, hm, hr'⟩ | ⟨v, hm, rfl⟩
        · refine drive_mem_query ν' S (by rwa [← hstep]) ?_
          rw [hcat x] at hr' ⊢
          rwa [← ih us (xs ++ [x]) (DriveReach.query hreach hm)]
        · exact drive_mem_answer ν' S (by rwa [← hstep]) n
      · intro hr
        rcases drive_succ_elim hr with ⟨x, hm, hr'⟩ | ⟨v, hm, rfl⟩
        · rw [← hstep] at hm
          refine drive_mem_query ν S hm ?_
          rw [hcat x] at hr' ⊢
          rwa [ih us (xs ++ [x]) (DriveReach.query hreach hm)]
        · rw [← hstep] at hm
          exact drive_mem_answer ν S hm n

/-- …and neither can the outer fold. -/
theorem driveOuter_congr_of_driveReach {ν ν' : ProtocolFn U V X Y} {S : PFunDDS.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) (fuel : ℕ) :
    ∀ (rest usPre : List U) (xs : List X),
      (∀ u, DriveReach ν S (usPre ++ [u]) xs) →
      driveOuter ν S fuel usPre xs (sysAnswers S xs) rest =
        driveOuter ν' S fuel usPre xs (sysAnswers S xs) rest := by
  intro rest
  induction rest with
  | nil => intro usPre xs _; rfl
  | cons u rest ih =>
      intro usPre xs hreach
      have hround := drive_congr_of_driveReach agree fuel (usPre ++ [u]) xs (hreach u)
      apply Part.ext
      intro result
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      constructor
      · rintro ⟨r, hr, rr, hrr, hres⟩
        obtain ⟨hys, hxs, hlast⟩ := drive_mem_driveReach (hreach u) hr
        refine ⟨r, hround ▸ hr, rr, ?_, hres⟩
        rw [hys] at hrr ⊢
        rwa [← ih (usPre ++ [u]) r.2.1
          (fun u' => DriveReach.next hxs hlast u')]
      · rintro ⟨r, hr, rr, hrr, hres⟩
        rw [← hround] at hr
        obtain ⟨hys, hxs, hlast⟩ := drive_mem_driveReach (hreach u) hr
        refine ⟨r, hr, rr, ?_, hres⟩
        rw [hys] at hrr ⊢
        rwa [ih (usPre ++ [u]) r.2.1
          (fun u' => DriveReach.next hxs hlast u')]

/-- **Application is a drive invariant**: protocols agreeing on every pair the
application visits apply identically, `TraceEquiv` or not. -/
theorem applyRaw_congr_of_driveReach {ν ν' : ProtocolFn U V X Y}
    {S : PFunDDS.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) :
    applyRaw ν S = applyRaw ν' S := by
  funext us
  apply Part.ext
  intro value
  rw [mem_applyRaw, mem_applyRaw]
  refine exists_congr fun fuel => ?_
  rw [mem_applyRawAt_iff, mem_applyRawAt_iff]
  have hfold := driveOuter_congr_of_driveReach agree fuel us [] []
    (fun u => by simpa using DriveReach.start (ν := ν) (S := S) u)
  simp only [sysAnswers_nil] at hfold
  rw [hfold]

@[inherit_doc applyRaw_congr_of_driveReach]
theorem apply_congr_of_driveReach {ν ν' : ProtocolFn U V X Y}
    {S : PFunDDS.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) :
    apply ν S = apply ν' S :=
  Subtype.ext (applyRaw_congr_of_driveReach agree)

end DriveCongruence

end PFunConverter

end RandomSystems.CR18
