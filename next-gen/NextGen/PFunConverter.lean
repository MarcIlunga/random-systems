/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.PFunDDS
import NextGen.PFunFix

/-!
# PFun-native deterministic discrete converters

This module gives the PFun-native version of CR18 §3.4.2 / Definition 3.8.
It is kept separate from the existing operational `CR18.Converter` module.
-/

namespace RandomSystems.CR18

universe u v w z

namespace PFunConverter

open scoped PFunDDS

/-! ### CR18 §3.4.2 / Definition 3.8 -/

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- Converter-side labels. -/
inductive InLabel : Type where
  | inside
  | outside

scoped infixr:30 " ∪ₜ " => Sum

/-- CR18 Definition 3.8: a deterministic discrete converter converting an
`(X,Y)`-DDS into a `(U,V)`-DDS is just a DDS over the converter alphabets. -/
abbrev DDC (U : Type u) (V : Type w) (X : Type z) (Y : Type v) :
    Type (max (max u v) (max w z)) :=
  PFunDDS.DDS
    ((InLabel × U) ∪ₜ (InLabel × Option Y))
    ((InLabel × V) ∪ₜ (InLabel × X))

/-! ### CR18 §3.4.2 / Definition 3.9 -/

namespace DDC

/-! #### Function-native realization of CR18 Definition 3.9

Maurer (Def 3.9) describes `αs` purely by *connection rules* and then notes:
"We do not give a completely formal definition of the application of a converter
to a system. Formally, one would have to show that the described object `αs` is
indeed a `(U,V)`-DDS. Intuitively, this is obvious."

We realize `αs` as exactly that missing object — a partial function (Def 3.2),
built by *function composition*, with no operational driver. The inner
converter/system interaction is the **least fixed point** of a single connection
step (`PFun.fix`); the outer round structure is ordinary structural recursion on
the outside input history. Maurer's two connection rules then *are* the
fixed-point lemmas `PFun.fix_stop` (output `(out,v)`) and `PFun.fix_fwd_eq`
(query `(in,x)`), recorded below as `resolve_out` and `resolve_in`.

Per Def 3.8 a converter has "a finite upper bound on the number of consecutive
`(in,x)` outputs". We keep that as a *predicate* on converters (a property, never
part of the converter's type); a converter without it still yields a partial
`αs`, undefined exactly where the inner loop never reaches an `(out,v)`. -/

/-- The converter-input alphabet `U ∪ (Y ∪ {⊥})` of CR18 Def 3.8. -/
abbrev CIn (U : Type u) (Y : Type v) : Type (max u v) :=
  (InLabel × U) ∪ₜ (InLabel × Option Y)

/-- The converter-output alphabet `({out} × V) ∪ ({in} × X)` of CR18 Def 3.8. -/
abbrev COut (V : Type w) (X : Type z) : Type (max w z) :=
  (InLabel × V) ∪ₜ (InLabel × X)

/-- CR18 Def 3.9, one connection step over the hidden
`(converter-history, system-history)` state:
* `α` outputs `(out, v)` ⟹ stop with `v` (histories unchanged);
* `α` outputs `(in, x)` ⟹ feed `x` to `s⊥` and continue with the answer;
* otherwise (α undefined, or an off-interface label) ⟹ undefined. -/
noncomputable def connStep (α : DDC U V X Y) (S : PFunDDS.DDS X Y) :
    (List (CIn U Y) × List X) →.
      (V × (List (CIn U Y) × List X)) ⊕ (List (CIn U Y) × List X) :=
  fun st =>
    (α.1 st.1).bind fun o =>
      match o with
      | Sum.inl (InLabel.outside, v) => Part.some (Sum.inl (v, st))
      | Sum.inr (InLabel.inside, x) =>
          Part.some (Sum.inr
            (st.1 ++ [Sum.inr (InLabel.inside,
                PFunDDS.output (S⊥) (st.2 ++ [x])
                  (by rw [PFunDDS.dom_fullyDefined]; simp))],
             st.2 ++ [x]))
      | _ => Part.none

/-- CR18 Def 3.9 inner resolution: the least fixed point of `connStep`. A genuine
partial function `(history) →. V`, undefined exactly when the inner loop never
reaches an `(out, v)`. -/
noncomputable def resolve (α : DDC U V X Y) (S : PFunDDS.DDS X Y) :
    (List (CIn U Y) × List X) →. (V × (List (CIn U Y) × List X)) :=
  (connStep α S).fix

/-- CR18 Def 3.9 **output rule**, which is exactly `PFun.fix_stop`: when `α`
outputs `(out, v)` on the current converter history, the inner resolution returns
`v` with the histories unchanged. -/
theorem resolve_out (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    {c : List (CIn U Y)} {xs : List X} {v : V}
    (h : Sum.inl (InLabel.outside, v) ∈ α.1 c) :
    (v, (c, xs)) ∈ resolve α S (c, xs) := by
  refine PFun.fix_stop (f := connStep α S) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

/-- CR18 Def 3.9 **query rule**, which is exactly `PFun.fix_fwd_eq`: when `α`
outputs `(in, x)`, the inner resolution continues from the converter history
extended by `s⊥`'s answer to `x`. -/
theorem resolve_in (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    {c : List (CIn U Y)} {xs : List X} {x : X}
    (h : Sum.inr (InLabel.inside, x) ∈ α.1 c) :
    resolve α S (c, xs) =
      resolve α S
        (c ++ [Sum.inr (InLabel.inside,
            PFunDDS.output (S⊥) (xs ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp))], xs ++ [x]) := by
  refine PFun.fix_fwd_eq (f := connStep α S) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

/-- CR18 Def 3.9 outer iteration: feed the outside inputs `us` to the converter
one after another, threading the hidden histories through `resolve`, and collect
the outside outputs. This is ordinary structural recursion on `us`; the only
fixed point is the inner `resolve`. -/
noncomputable def driveFrom (α : DDC U V X Y) (S : PFunDDS.DDS X Y) :
    (List (CIn U Y) × List X) → List U →. (List V × (List (CIn U Y) × List X))
  | st, [] => Part.some ([], st)
  | st, u :: rest =>
      (resolve α S (st.1 ++ [Sum.inl (InLabel.outside, u)], st.2)).bind
        fun r => (driveFrom α S r.2 rest).map fun rr => (r.1 :: rr.1, rr.2)

/-- The applied system as a raw partial function `List U →. V`: replay the whole
interaction from empty histories and return the output of the last round. -/
noncomputable def applyRaw (α : DDC U V X Y) (S : PFunDDS.DDS X Y) :
    PFunDDS.Raw U V :=
  fun us => (driveFrom α S ([], []) us).bind fun r =>
    match r.1.getLast? with
    | some v => Part.some v
    | none => Part.none

/-- Each completed round produces exactly one outside output. -/
theorem driveFrom_length (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    (st : List (CIn U Y) × List X) (us : List U)
    {r : List V × (List (CIn U Y) × List X)} (h : r ∈ driveFrom α S st us) :
    r.1.length = us.length := by
  induction us generalizing st r with
  | nil =>
      simp only [driveFrom, Part.mem_some_iff] at h
      subst h; simp
  | cons u rest ih =>
      simp only [driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _hr', rr, hrr, rfl⟩ := h
      simp [ih r'.2 hrr]

/-- The outer iteration splits over a concatenation of outside histories: drive
the prefix, then drive the suffix from the resulting state. -/
theorem driveFrom_append (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    (st : List (CIn U Y) × List X) (a b : List U) :
    driveFrom α S st (a ++ b) =
      (driveFrom α S st a).bind fun ra =>
        (driveFrom α S ra.2 b).map fun rb => (ra.1 ++ rb.1, rb.2) := by
  induction a generalizing st with
  | nil =>
      simp only [List.nil_append, driveFrom, Part.bind_some]
      refine (Part.map_id' ?_ _).symm
      intro rb; rfl
  | cons u rest ih =>
      simp only [List.cons_append, driveFrom, ih, Part.bind_assoc, Part.bind_map,
        Part.map_bind, Part.map_map, Function.comp_def, List.cons_append]

/-- CR18 Definition 3.9: the applied converter `αs`, realized as the partial
function `applyRaw α S`. The `Valid` proof (Maurer's "one would have to show αs
is a `(U,V)`-DDS") is discharged from the structural driver lemmas. -/
noncomputable def apply (α : DDC U V X Y) (S : PFunDDS.DDS X Y) :
    PFunDDS.DDS U V :=
  ⟨applyRaw α S, by
    refine ⟨?_, ?_⟩
    · -- the empty outside history produces no output
      rw [PFun.mem_dom]
      rintro ⟨v, hv⟩
      simp [applyRaw, driveFrom] at hv
    · -- domain is closed under nonempty prefixes
      intro l₁ l₂ hpre hne hdom
      obtain ⟨suf, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      simp only [applyRaw, Part.mem_bind_iff] at hv
      obtain ⟨r, hr, _hvr⟩ := hv
      rw [driveFrom_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _hr2⟩ := hr
      have hlen : ra.1.length = l₁.length := driveFrom_length α S ([], []) l₁ hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil
        apply hne
        apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      simp only [applyRaw, Part.mem_bind_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]
      exact Part.mem_some _⟩

/-- The applied system is exactly the raw partial function `applyRaw`. -/
@[simp]
theorem apply_toPFun (α : DDC U V X Y) (S : PFunDDS.DDS X Y) :
    (apply α S).1 = applyRaw α S := rfl

/-- Membership characterization of `αs`: the outside history `us` yields `v`
exactly when replaying it produces a final output list ending in `v`. This is
the function-native replacement for the old `ApplicationGraph` relation. -/
theorem mem_apply_iff (α : DDC U V X Y) (S : PFunDDS.DDS X Y)
    (us : List U) (v : V) :
    v ∈ applyRaw α S us ↔
      ∃ r ∈ driveFrom α S ([], []) us, r.1.getLast? = some v := by
  simp only [applyRaw, Part.mem_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  cases r.1.getLast? with
  | none => simp
  | some w => simp [Part.mem_some_iff, eq_comm]

/-- CR18 Definition 3.9 notation: `α ·ᶜ S` is the DDS obtained by applying
the deterministic converter `α` to the DDS `S`.

The subscript distinguishes converter application from cascade notation `⊲`
and probabilistic converter composition notation `·ₚ`. -/
scoped notation:70 α " ·ᶜ " S => apply α S

end DDC

/-! ### CR18 §3.4.3: filters -/

/-- CR18 §3.4.3: a filter is a converter from `(X,Y)` systems to `(X,Y)`
systems. -/
abbrev Filter (X : Type z) (Y : Type v) : Type (max z v) :=
  DDC X Y X Y

namespace Filter

/-- Applying a filter to a DDS is the converter application from Definition 3.9,
specialized to filters. -/
noncomputable abbrev apply (φ : Filter X Y) (S : PFunDDS.DDS X Y) :
    PFunDDS.DDS X Y :=
  DDC.apply φ S

end Filter

def queryLimitOutputFrom (q : Nat) :
    Nat → Bool →
    List (((InLabel × X) ∪ₜ (InLabel × Option Y))) →
    Option (((InLabel × Y) ∪ₜ (InLabel × X)))
  | used, true, Sum.inl (InLabel.outside, x) :: rest =>
      if used < q then
        match rest with
        | [] => some (Sum.inr (InLabel.inside, x))
        | _ :: _ => queryLimitOutputFrom q (used + 1) false rest
      else
        none
  | used, false, Sum.inr (InLabel.inside, some y) :: rest =>
      match rest with
      | [] => some (Sum.inl (InLabel.outside, y))
      | _ :: _ => queryLimitOutputFrom q used true rest
  | _, _, _ => none

theorem queryLimitOutputFrom_prefix (q : Nat) :
    ∀ (l t : List (((InLabel × X) ∪ₜ (InLabel × Option Y)))) (used : Nat)
      (ready : Bool),
      l ≠ [] →
      (queryLimitOutputFrom (X := X) (Y := Y) q used ready (l ++ t)).isSome →
      (queryLimitOutputFrom (X := X) (Y := Y) q used ready l).isSome := by
  intro l
  induction l with
  | nil =>
      intro t used ready hne _
      exact False.elim (hne rfl)
  | cons a rest ih =>
      intro t used ready _ hsome
      cases ready
      · cases a with
        | inl p =>
            cases p with
            | mk side x =>
                cases side <;> simp [queryLimitOutputFrom] at hsome ⊢
        | inr p =>
            cases p with
            | mk side oy =>
                cases side <;> cases oy <;> simp [queryLimitOutputFrom] at hsome ⊢
                · cases rest with
                  | nil => simp
                  | cons b rest =>
                      exact ih t used true (by simp) hsome
      · cases a with
        | inl p =>
            cases p with
            | mk side x =>
                cases side
                · simp [queryLimitOutputFrom] at hsome ⊢
                · by_cases hlt : used < q
                  · simp [queryLimitOutputFrom, hlt] at hsome ⊢
                    cases rest with
                    | nil => simp
                    | cons b rest =>
                        exact ih t (used + 1) false (by simp) hsome
                  · simp [queryLimitOutputFrom, hlt] at hsome
        | inr p =>
            cases p with
            | mk side oy =>
                cases side <;> cases oy <;> simp [queryLimitOutputFrom] at hsome ⊢

/-- CR18 Definition 3.10: `[q]` restricts access to at most `q` queries.

As a DDC, `[q]` forwards the first `q` outside inputs to the inside system and
relays defined inside replies back outside. On the `(q+1)`-st outside input it
is undefined. -/
def queryLimit (q : Nat) : Filter X Y :=
  ⟨(fun l : List (((InLabel × X) ∪ₜ (InLabel × Option Y))) =>
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true l).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true l).get h⟩ :
        Part (((InLabel × Y) ∪ₜ (InLabel × X))))),
    ⟨by simp [queryLimitOutputFrom], by
      intro l₁ l₂ hp hne hdom
      rcases hp with ⟨t, rfl⟩
      exact queryLimitOutputFrom_prefix (X := X) (Y := Y) q l₁ t 0 true hne hdom⟩⟩

/-- Alternating converter-side history produced by completed `[q]ᶠ` rounds.

UPSTREAM-CANDIDATE: trace normal form for proving that the operational query-limit converter realizes
the canonical DDS-level `PFunDDS.filterQueries`. -/
def queryLimitTrace : List (X × Y) → List (DDC.CIn X Y)
  | [] => []
  | (x, y) :: t =>
      Sum.inl (InLabel.outside, x) :: Sum.inr (InLabel.inside, some y) :: queryLimitTrace t

theorem queryLimitTrace_append_single (t : List (X × Y)) (x : X) (y : Y) :
    queryLimitTrace (t ++ [(x, y)]) =
      queryLimitTrace t ++ [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, some y)] := by
  induction t with
  | nil => simp [queryLimitTrace]
  | cons p t ih =>
      cases p with
      | mk x0 y0 => simp [queryLimitTrace, ih]

theorem queryLimitOutputFrom_trace_query_from
    (q used : Nat) (t : List (X × Y)) (x : X) :
    queryLimitOutputFrom (X := X) (Y := Y) q used true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) =
      if used + t.length < q then some (Sum.inr (InLabel.inside, x)) else none := by
  induction t generalizing used with
  | nil => by_cases h : used < q <;> simp [queryLimitTrace, queryLimitOutputFrom, h]
  | cons p t ih =>
      cases p with
      | mk x0 y0 =>
          by_cases h : used < q
          · have hne : queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)] ≠ [] := by simp
            cases hrest : queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)] with
            | nil => exact False.elim (hne hrest)
            | cons head tail =>
                have hrec := ih (used + 1)
                rw [hrest] at hrec
                simpa [queryLimitTrace, queryLimitOutputFrom, h, hrest, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using hrec
          · simp [queryLimitTrace, queryLimitOutputFrom, h]
            omega

theorem queryLimitOutputFrom_trace_query (q : Nat) (t : List (X × Y)) (x : X) :
    queryLimitOutputFrom (X := X) (Y := Y) q 0 true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) =
      if t.length < q then some (Sum.inr (InLabel.inside, x)) else none := by
  simpa using queryLimitOutputFrom_trace_query_from (X := X) (Y := Y) q 0 t x

theorem queryLimitOutputFrom_trace_reply_from
    (q used : Nat) (t : List (X × Y)) (x : X) (y : Y) :
    queryLimitOutputFrom (X := X) (Y := Y) q used true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, some y)]) =
      if used + t.length < q then some (Sum.inl (InLabel.outside, y)) else none := by
  induction t generalizing used with
  | nil => by_cases h : used < q <;> simp [queryLimitTrace, queryLimitOutputFrom, h]
  | cons p t ih =>
      cases p with
      | mk x0 y0 =>
          by_cases h : used < q
          · have hne :
              queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                Sum.inr (InLabel.inside, some y)] ≠ [] := by simp
            cases hrest :
                queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                  Sum.inr (InLabel.inside, some y)] with
            | nil => exact False.elim (hne hrest)
            | cons head tail =>
                have hrec := ih (used + 1)
                rw [hrest] at hrec
                simpa [queryLimitTrace, queryLimitOutputFrom, h, hrest, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using hrec
          · simp [queryLimitTrace, queryLimitOutputFrom, h]
            omega

theorem queryLimitOutputFrom_trace_reply
    (q : Nat) (t : List (X × Y)) (x : X) (y : Y) :
    queryLimitOutputFrom (X := X) (Y := Y) q 0 true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, some y)]) =
      if t.length < q then some (Sum.inl (InLabel.outside, y)) else none := by
  simpa using queryLimitOutputFrom_trace_reply_from (X := X) (Y := Y) q 0 t x y

theorem queryLimitOutputFrom_trace_reply_none_from
    (q used : Nat) (t : List (X × Y)) (x : X) :
    queryLimitOutputFrom (X := X) (Y := Y) q used true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, none)]) = none := by
  induction t generalizing used with
  | nil => by_cases h : used < q <;> simp [queryLimitTrace, queryLimitOutputFrom, h]
  | cons p t ih =>
      cases p with
      | mk x0 y0 =>
          by_cases h : used < q
          · have hne :
              queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                Sum.inr (InLabel.inside, none)] ≠ [] := by simp
            cases hrest :
                queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                  Sum.inr (InLabel.inside, none)] with
            | nil => exact False.elim (hne hrest)
            | cons head tail =>
                have hrec := ih (used + 1)
                rw [hrest] at hrec
                simpa [queryLimitTrace, queryLimitOutputFrom, h, hrest, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using hrec
          · simp [queryLimitTrace, queryLimitOutputFrom, h]

theorem queryLimit_trace_query_mem_iff
    (q : Nat) (t : List (X × Y)) (x : X)
    (o : ((InLabel × Y) ∪ₜ (InLabel × X))) :
    o ∈ (queryLimit q : Filter X Y).1
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) ↔
      t.length < q ∧ o = Sum.inr (InLabel.inside, x) := by
  change o ∈
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)])).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)])).get h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × X))) ↔
      t.length < q ∧ o = Sum.inr (InLabel.inside, x)
  rw [queryLimitOutputFrom_trace_query]
  by_cases h : t.length < q <;> simp [h, eq_comm]

theorem queryLimit_trace_reply_mem_iff
    (q : Nat) (t : List (X × Y)) (x : X) (y : Y)
    (o : ((InLabel × Y) ∪ₜ (InLabel × X))) :
    o ∈ (queryLimit q : Filter X Y).1
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, some y)]) ↔
      t.length < q ∧ o = Sum.inl (InLabel.outside, y) := by
  change o ∈
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, some y)])).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, some y)])).get h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × X))) ↔
      t.length < q ∧ o = Sum.inl (InLabel.outside, y)
  rw [queryLimitOutputFrom_trace_reply]
  by_cases h : t.length < q <;> simp [h, eq_comm]

theorem queryLimit_trace_reply_none_not_mem
    (q : Nat) (t : List (X × Y)) (x : X)
    (o : ((InLabel × Y) ∪ₜ (InLabel × X))) :
    o ∉ (queryLimit q : Filter X Y).1
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, none)]) := by
  change o ∉
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, none)])).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, none)])).get h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × X)))
  rw [queryLimitOutputFrom_trace_reply_none_from]
  simp

-- UPSTREAM-CANDIDATE: generic `fullyDefined`/`keptPrefix` API for CR18 Def 3.3.
theorem output_fullyDefined_append_keptPrefix_of_mem
    (S : PFunDDS.DDS X Y) (l : List X) (x : X)
    (hnext : PFunDDS.keptPrefix S l ++ [x] ∈ PFunDDS.dom S) :
    PFunDDS.output S⊥ (l ++ [x]) (by
      rw [PFunDDS.dom_fullyDefined]
      simp) =
      some (PFunDDS.output S (PFunDDS.keptPrefix S l ++ [x]) hnext) := by
  rw [PFunDDS.output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  rw [hdrop, hlast]
  dsimp
  have hnextRaw : PFunDDS.keptPrefix S l ++ [x] ∈ PFun.Dom S.1 := by
    simpa [PFunDDS.dom, PFunDDS.toPFun] using hnext
  rw [dif_pos hnextRaw]

theorem queryLimit_resolve_round_mem_imp
    (q : Nat) (S : PFunDDS.DDS X Y) (t : List (X × Y)) (xs : List X) (x : X)
    {r : Y × (List (DDC.CIn X Y) × List X)}
    (hr : r ∈ DDC.resolve (queryLimit q : Filter X Y) S
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], xs)) :
    ∃ y, t.length < q ∧
      PFunDDS.output S⊥ (xs ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y ∧
      r = (y, (queryLimitTrace (t ++ [(x, y)]), xs ++ [x])) := by
  rw [DDC.resolve, PFun.mem_fix_iff] at hr
  rcases hr with hstop | hstep
  · rw [DDC.connStep, Part.mem_bind_iff] at hstop
    obtain ⟨o, ho, hsum⟩ := hstop
    rw [queryLimit_trace_query_mem_iff] at ho
    obtain ⟨_, rfl⟩ := ho
    simp at hsum
  · obtain ⟨a', hconn, hrec⟩ := hstep
    rw [DDC.connStep, Part.mem_bind_iff] at hconn
    obtain ⟨o, ho, hsum⟩ := hconn
    rw [queryLimit_trace_query_mem_iff] at ho
    obtain ⟨hbudget, rfl⟩ := ho
    simp at hsum
    subst a'
    rw [PFun.mem_fix_iff] at hrec
    rcases hrec with hstop2 | hstep2
    · rw [DDC.connStep, Part.mem_bind_iff] at hstop2
      obtain ⟨o, ho, hsum2⟩ := hstop2
      simp at ho
      split at ho
      · rename_i hcand
        rw [queryLimit_trace_reply_mem_iff] at ho
        obtain ⟨_, rfl⟩ := ho
        simp at hsum2
        subst r
        have hcand' : PFunDDS.keptPrefix S xs ++ [x] ∈ PFunDDS.dom S := by
          simpa [PFunDDS.dom, List.dropLast_concat, List.getLast_concat] using hcand
        refine ⟨PFunDDS.output S (PFunDDS.keptPrefix S xs ++ [x]) hcand',
          hbudget, ?_, ?_⟩
        · exact output_fullyDefined_append_keptPrefix_of_mem S xs x hcand'
        · have hcand'' : PFunDDS.keptPrefix S xs ++ [x] ∈ PFunDDS.dom S := by
            simpa [PFunDDS.dom, List.dropLast_concat, List.getLast_concat] using hcand
          have houtEq :
              PFunDDS.output S (PFunDDS.keptPrefix S xs ++ [x]) hcand'' =
                PFunDDS.output S (PFunDDS.keptPrefix S xs ++ [x]) hcand' := by
            exact PFunDDS.output_congr S rfl hcand'' hcand'
          rw [dif_pos hcand]
          apply Prod.ext
          · exact PFunDDS.output_congr S rfl _ hcand'
          · apply Prod.ext
            · rw [queryLimitTrace_append_single]
            · rfl
      · exact False.elim (queryLimit_trace_reply_none_not_mem q t x o ho)
    · obtain ⟨a', hconn2, _hrec2⟩ := hstep2
      rw [DDC.connStep, Part.mem_bind_iff] at hconn2
      obtain ⟨o, ho, hsum2⟩ := hconn2
      simp at ho
      split at ho
      · rw [queryLimit_trace_reply_mem_iff] at ho
        obtain ⟨_, rfl⟩ := ho
        simp at hsum2
      · exact False.elim (queryLimit_trace_reply_none_not_mem q t x o ho)

theorem queryLimit_resolve_round
    (q : Nat) (S : PFunDDS.DDS X Y) (t : List (X × Y)) (xs : List X) (x : X) (y : Y)
    (hbudget : t.length < q)
    (hout : PFunDDS.output S⊥ (xs ++ [x]) (by
        rw [PFunDDS.dom_fullyDefined]
        simp) = some y) :
    (y, (queryLimitTrace (t ++ [(x, y)]), xs ++ [x])) ∈
      DDC.resolve (queryLimit q : Filter X Y) S
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], xs) := by
  have hquery : Sum.inr (InLabel.inside, x) ∈
      (queryLimit q : Filter X Y).1 (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) := by
    simp [queryLimit, queryLimitOutputFrom_trace_query, hbudget]
  rw [DDC.resolve_in (queryLimit q : Filter X Y) S hquery]
  simpa [hout, queryLimitTrace_append_single, List.append_assoc] using
    (DDC.resolve_out (queryLimit q : Filter X Y) S
      (c := queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
        Sum.inr (InLabel.inside, some y)])
      (xs := xs ++ [x])
      (v := y)
      (by
        simp [queryLimit, queryLimitOutputFrom_trace_reply, hbudget]))

theorem queryLimit_driveFrom_suffix_apply
    (q : Nat) (S : PFunDDS.DDS X Y) :
    ∀ (rest pref : List X) (t : List (X × Y))
      (_ : t.length = pref.length)
      (_ : pref ∈ PFunDDS.dom S ∨ pref = [])
      (hfull : pref ++ rest ∈ PFunDDS.dom S)
      (_ : pref.length + rest.length ≤ q)
      (_ : rest ≠ []),
      ∃ r ∈ DDC.driveFrom (queryLimit q : Filter X Y) S (queryLimitTrace t, pref) rest,
        r.1.getLast? = some (PFunDDS.output S (pref ++ rest) hfull) := by
  intro rest
  induction rest with
  | nil =>
      intro _pref _t _htlen _hpref _hfull _hbudget hne
      exact False.elim (hne rfl)
  | cons x rest ih =>
      intro pref t htlen hpref hfull hbudget _hne
      have hnext : pref ++ [x] ∈ PFunDDS.dom S := by
        exact PFunDDS.prefix_closed S (by simp) (by simp) hfull
      have hbudgetRound : t.length < q := by
        rw [htlen]
        simp at hbudget
        omega
      let y := PFunDDS.output S (pref ++ [x]) hnext
      have hout : PFunDDS.output S⊥ (pref ++ [x]) (by
          rw [PFunDDS.dom_fullyDefined]
          simp) = some y := by
        exact PFunDDS.output_fullyDefined_append_of_mem S pref x hpref hnext
      have hround : (y, (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])) ∈
          DDC.resolve (queryLimit q : Filter X Y) S
            (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], pref) := by
        exact queryLimit_resolve_round q S t pref x y hbudgetRound hout
      cases rest with
      | nil =>
          refine ⟨([y], (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), ?_, ?_⟩
          · simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(y, (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), hround,
              ([], (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), ?_, ?_⟩
            · simp
            · rfl
          · simp [y]
      | cons x' rest' =>
          have htlen' : (t ++ [(x, y)]).length = (pref ++ [x]).length := by
            simp [htlen]
          have hpref' : pref ++ [x] ∈ PFunDDS.dom S ∨ pref ++ [x] = [] := Or.inl hnext
          have hfull' : (pref ++ [x]) ++ x' :: rest' ∈ PFunDDS.dom S := by
            simpa [List.append_assoc] using hfull
          have hbudget' : (pref ++ [x]).length + (x' :: rest').length ≤ q := by
            simp at hbudget ⊢
            omega
          obtain ⟨rtail, htail, hlast⟩ :=
            ih (pref ++ [x]) (t ++ [(x, y)]) htlen' hpref' hfull' hbudget' (by simp)
          have hlast' :
              rtail.1.getLast? = some (PFunDDS.output S (pref ++ x :: x' :: rest') hfull) := by
            rw [hlast]
            congr 1
            exact PFunDDS.output_congr S (by simp [List.append_assoc]) hfull' hfull
          refine ⟨(y :: rtail.1, rtail.2), ?_, ?_⟩
          · change (y :: rtail.1, rtail.2) ∈
              (DDC.resolve (queryLimit q) S
                (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], pref)).bind
                (fun r => (DDC.driveFrom (queryLimit q) S r.2 (x' :: rest')).map
                  fun rr => (r.1 :: rr.1, rr.2))
            refine Part.mem_bind_iff.mpr
              ⟨(y, (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), hround, ?_⟩
            rw [Part.mem_map_iff]
            exact ⟨rtail, htail, rfl⟩
          · cases hys : rtail.1 with
            | nil => simp [hys] at hlast'
            | cons y0 ys => simpa [hys] using hlast'

theorem queryLimit_driveFrom_suffix_apply_mem_imp
    (q : Nat) (S : PFunDDS.DDS X Y) :
    ∀ (rest pref : List X) (t : List (X × Y))
      (_ : t.length = pref.length)
      (_ : pref ∈ PFunDDS.dom S ∨ pref = [])
      {r : List Y × (List (DDC.CIn X Y) × List X)} {y : Y},
      r ∈ DDC.driveFrom (queryLimit q : Filter X Y) S (queryLimitTrace t, pref) rest →
      r.1.getLast? = some y →
      ∃ hfull : pref ++ rest ∈ PFunDDS.dom S,
        pref.length + rest.length ≤ q ∧
          y = PFunDDS.output S (pref ++ rest) hfull := by
  intro rest
  induction rest with
  | nil =>
      intro pref t htlen hpref r y hr hlast
      simp [DDC.driveFrom] at hr
      subst r
      simp at hlast
  | cons x rest ih =>
      intro pref t htlen hpref r y hr hlast
      simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨rround, hround, rtail, htail, rfl⟩ := hr
      obtain ⟨y0, hbudgetRound, houtFD, hroundEq⟩ :=
        queryLimit_resolve_round_mem_imp q S t pref x hround
      subst rround
      obtain ⟨hnext, houtS⟩ :=
        PFunDDS.mem_of_output_fullyDefined_append_eq_some S pref x hpref houtFD
      cases rest with
      | nil =>
          simp [DDC.driveFrom] at htail
          subst rtail
          simp at hlast
          refine ⟨by simpa using hnext, ?_, ?_⟩
          · rw [htlen] at hbudgetRound
            simp at hbudgetRound ⊢
            omega
          · rw [← hlast, ← houtS]
      | cons x' rest' =>
          have htailLast : rtail.1.getLast? = some y := by
            have hlenTail :=
              DDC.driveFrom_length (queryLimit q : Filter X Y) S
                (queryLimitTrace (t ++ [(x, y0)]), pref ++ [x]) (x' :: rest') htail
            cases hys : rtail.1 with
            | nil => simp [hys] at hlenTail
            | cons y1 ys => simpa [hys] using hlast
          have htlen' : (t ++ [(x, y0)]).length = (pref ++ [x]).length := by
            simp [htlen]
          have hpref' : pref ++ [x] ∈ PFunDDS.dom S ∨ pref ++ [x] = [] := Or.inl hnext
          obtain ⟨hfull', hbudget', houtFinal⟩ :=
            ih (pref ++ [x]) (t ++ [(x, y0)]) htlen' hpref' htail htailLast
          let hfull : pref ++ x :: x' :: rest' ∈ PFunDDS.dom S := by
            simpa [List.append_assoc] using hfull'
          refine ⟨hfull, ?_, ?_⟩
          · simp at hbudget' ⊢
            omega
          · rw [houtFinal]
            exact PFunDDS.output_congr S (by simp [List.append_assoc]) hfull' hfull

theorem queryLimit_applyRaw_mem_of_dom
    (q : Nat) (S : PFunDDS.DDS X Y) {l : List X}
    (hdom : l ∈ PFunDDS.dom S) (hbudget : l.length ≤ q) :
    PFunDDS.output S l hdom ∈ DDC.applyRaw (queryLimit q : Filter X Y) S l := by
  have hne : l ≠ [] := by
    intro hl
    exact PFunDDS.empty_not_mem S (by simpa [hl] using hdom)
  obtain ⟨r, hr, hlast⟩ :=
    queryLimit_driveFrom_suffix_apply q S l [] [] rfl (Or.inr rfl) hdom
      (by simpa using hbudget) hne
  exact (DDC.mem_apply_iff (queryLimit q : Filter X Y) S l (PFunDDS.output S l hdom)).mpr
    ⟨r, hr, hlast⟩

theorem queryLimit_applyRaw_mem_iff
    (q : Nat) (S : PFunDDS.DDS X Y) (l : List X) (y : Y) :
    y ∈ DDC.applyRaw (queryLimit q : Filter X Y) S l ↔
      ∃ hdom : l ∈ PFunDDS.dom S,
        l.length ≤ q ∧ PFunDDS.output S l hdom = y := by
  constructor
  · intro hy
    obtain ⟨r, hr, hlast⟩ :=
      (DDC.mem_apply_iff (queryLimit q : Filter X Y) S l y).mp hy
    obtain ⟨hdom, hbudget, hout⟩ :=
      queryLimit_driveFrom_suffix_apply_mem_imp q S l [] [] rfl (Or.inr rfl) hr hlast
    exact ⟨hdom, by simpa using hbudget, hout.symm⟩
  · rintro ⟨hdom, hbudget, hout⟩
    rw [← hout]
    exact queryLimit_applyRaw_mem_of_dom q S hdom hbudget

/-- CR18 notation for Definition 3.10. Use `([q]ᶠ) S` for `[q]S`. -/
scoped notation "[" q "]ᶠ" => queryLimit q

/-- Explicit query-count filter notation. This is an alias for `[q]ᶠ`; the
double brackets avoid confusion with Lean list notation when reading code. -/
scoped notation "⟦" q "⟧ᶠ" => queryLimit q

@[simp]
theorem queryCountFilter_notation (q : Nat) :
    (⟦q⟧ᶠ : Filter X Y) = ([q]ᶠ : Filter X Y) :=
  rfl

/-- CR18 §3.4.3 / Definition 3.10: the DDS obtained by applying the query
filter `[q]` is the canonical DDS-level restriction `PFunDDS.filterQueries q`.
The converter object is `[q]ᶠ`; this name records its induced action on systems. -/
abbrev queryLimitApply (q : Nat) (S : PFunDDS.DDS X Y) : PFunDDS.DDS X Y :=
  PFunDDS.filterQueries q S

/-- The converter-facing `[q]` action and the canonical DDS-level query filter are
the same operation. -/
@[simp] theorem queryLimitApply_eq_filterQueries (q : Nat) (S : PFunDDS.DDS X Y) :
    queryLimitApply q S = PFunDDS.filterQueries q S :=
  rfl

/-- CR18 Definition 3.10, operational form: applying the query-limit converter `[q]ᶠ`
to a DDS realizes the canonical DDS-level query restriction. -/
@[simp] theorem queryLimit_filter_apply_eq_filterQueries
    (q : Nat) (S : PFunDDS.DDS X Y) :
    Filter.apply (queryLimit q : Filter X Y) S = PFunDDS.filterQueries q S := by
  apply Subtype.ext
  funext l
  apply Part.ext'
  · constructor
    · intro hleft
      have hleftMem :
          ((Filter.apply (queryLimit q : Filter X Y) S).1 l).get hleft ∈
            DDC.applyRaw (queryLimit q : Filter X Y) S l := by
        simpa [Filter.apply, DDC.apply_toPFun] using
          (Part.get_mem hleft)
      obtain ⟨hdom, hbudget, _hout⟩ :=
        (queryLimit_applyRaw_mem_iff q S l
          (((Filter.apply (queryLimit q : Filter X Y) S).1 l).get hleft)).mp hleftMem
      exact ⟨hdom, hbudget⟩
    · intro hright
      have hdom : l ∈ PFunDDS.dom S := hright.1
      have hbudget : l.length ≤ q := hright.2
      change (DDC.applyRaw (queryLimit q : Filter X Y) S l).Dom
      rw [Part.dom_iff_mem]
      exact ⟨PFunDDS.output S l hdom, by
        exact queryLimit_applyRaw_mem_of_dom q S hdom hbudget⟩
  · intro h₁ h₂
    have hleftMem :
        ((Filter.apply (queryLimit q : Filter X Y) S).1 l).get h₁ ∈
          DDC.applyRaw (queryLimit q : Filter X Y) S l := by
      simpa [Filter.apply, DDC.apply_toPFun] using
        (Part.get_mem h₁)
    obtain ⟨hdom, _hbudget, houtLeft⟩ :=
      (queryLimit_applyRaw_mem_iff q S l
        (((Filter.apply (queryLimit q : Filter X Y) S).1 l).get h₁)).mp hleftMem
    have hrightDom : l ∈ PFunDDS.dom (PFunDDS.filterQueries q S) := h₂
    have hrightBase : l ∈ PFunDDS.dom S :=
      ((PFunDDS.mem_dom_filterQueries q S l).mp hrightDom).1
    calc
      ((Filter.apply (queryLimit q : Filter X Y) S).1 l).get h₁
          = PFunDDS.output S l hdom := houtLeft.symm
      _ = PFunDDS.output S l hrightBase := PFunDDS.output_congr S rfl hdom hrightBase
      _ = ((PFunDDS.filterQueries q S).1 l).get h₂ := by
            rfl

@[simp]
theorem queryLimitApply_dom (q : Nat) (S : PFunDDS.DDS X Y) (l : List X) :
    l ∈ PFunDDS.dom (queryLimitApply q S) ↔
      l ∈ PFunDDS.dom S ∧ l.length ≤ q :=
  PFunDDS.mem_dom_filterQueries q S l

@[simp]
theorem queryLimitApply_output (q : Nat) (S : PFunDDS.DDS X Y)
    (l : List X) (h : l ∈ PFunDDS.dom (queryLimitApply q S)) :
    PFunDDS.output (queryLimitApply q S) l h =
      PFunDDS.output S l ((queryLimitApply_dom q S l).mp h).1 :=
  rfl

/-- CR18 Definition 3.10: `[q]S` is undefined on every DDS input history with
more than `q` queries. -/
theorem queryLimitApply_undefined_of_length_gt (q : Nat) (S : PFunDDS.DDS X Y)
    {l : List X} (hlen : q < l.length) :
    l ∉ PFunDDS.dom (queryLimitApply q S) := by
  intro h
  exact (not_le_of_gt hlen) ((queryLimitApply_dom q S l).mp h).2

/-- CR18 Definition 3.10, paper-facing form: `[q]S` is undefined at the
`(q+1)`-st query. -/
theorem queryLimitApply_undefined_at_query_succ (q : Nat) (S : PFunDDS.DDS X Y)
    {l : List X} (hlen : l.length = q + 1) :
    l ∉ PFunDDS.dom (queryLimitApply q S) := by
  apply queryLimitApply_undefined_of_length_gt q S
  omega

theorem queryLimit_first_query_output (q : Nat) (x : X) (h : 0 < q) :
    PFunDDS.output (([q]ᶠ : Filter X Y)) [Sum.inl (InLabel.outside, x)]
      (by
        change (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          [Sum.inl (InLabel.outside, x)]).isSome
        simp [queryLimitOutputFrom, h]) =
      Sum.inr (InLabel.inside, x) :=
  by simp [PFunDDS.output, queryLimit, queryLimitOutputFrom, h]

theorem queryLimit_first_query_undefined (x : X) :
    [Sum.inl (InLabel.outside, x)] ∉
      PFunDDS.dom (([0]ᶠ : Filter X Y)) := by
  change ¬ (queryLimitOutputFrom (X := X) (Y := Y) 0 0 true
    [Sum.inl (InLabel.outside, x)]).isSome
  simp [queryLimitOutputFrom]

theorem queryLimit_reply_output (q : Nat) (x : X) (y : Y) (h : 0 < q) :
    PFunDDS.output (([q]ᶠ : Filter X Y))
      [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, some y)]
      (by
        change (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, some y)]).isSome
        simp [queryLimitOutputFrom, h]) =
      Sum.inl (InLabel.outside, y) :=
  by simp [PFunDDS.output, queryLimit, queryLimitOutputFrom, h]

end PFunConverter

/-! ### CR18 §3.4.4 / Definition 3.11: cascade -/

namespace PFunDDS

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Internal construction for CR18 Definition 3.11: the list
`[S(x₁), S(x₁,x₂), ..., S(x₁,...,xₖ)]`. The paper names its entries `yⱼ`;
the public API below exposes only cascade itself. -/
def cascadeMiddle (S : DDS X Y) (l : List X) (h : l ∈ dom S) : List Y :=
  (List.finRange l.length).map fun j =>
    output S (l.take (j.val + 1)) (by
      have hprefix : l.take (j.val + 1) <+: l := List.take_prefix (j.val + 1) l
      have hle : j.val + 1 ≤ l.length := Nat.succ_le_of_lt j.isLt
      have hne : l.take (j.val + 1) ≠ [] := by
        intro hnil
        have hlen : (l.take (j.val + 1)).length = j.val + 1 := by
          rw [List.length_take, Nat.min_eq_left hle]
        simp [hnil] at hlen
      exact prefix_closed S hprefix hne h)

@[simp]
theorem cascadeMiddle_length (S : DDS X Y) (l : List X) (h : l ∈ dom S) :
    (cascadeMiddle S l h).length = l.length := by
  simp [cascadeMiddle]

theorem cascadeMiddle_getElem (S : DDS X Y) (l : List X) (h : l ∈ dom S)
    (j : Nat) (hj : j < (cascadeMiddle S l h).length) :
    (cascadeMiddle S l h)[j] =
      output S (l.take (j + 1))
        (prefix_closed S (List.take_prefix (j + 1) l)
          (by
            have hjl : j < l.length := by simpa [cascadeMiddle] using hj
            have hlen : (l.take (j + 1)).length = j + 1 := by
              rw [List.length_take, Nat.min_eq_left (by omega)]
            intro hnil
            simp [hnil] at hlen) h) := by
  simp only [cascadeMiddle, List.getElem_map, List.getElem_finRange, Fin.cast_mk]

theorem cascadeMiddle_congr (S : DDS X Y) {l₁ l₂ : List X} (hl : l₁ = l₂)
    (h₁ : l₁ ∈ dom S) (h₂ : l₂ ∈ dom S) :
    cascadeMiddle S l₁ h₁ = cascadeMiddle S l₂ h₂ := by
  subst hl
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    rw [cascadeMiddle_getElem S l₁ h₁ j hj₁]

theorem cascadeMiddle_prefix (S : DDS X Y) {l₁ l₂ : List X}
    (h₁ : l₁ ∈ dom S) (h₂ : l₂ ∈ dom S) (hp : l₁ <+: l₂) :
    cascadeMiddle S l₁ h₁ <+: cascadeMiddle S l₂ h₂ := by
  have hlen : l₁.length ≤ l₂.length := hp.length_le
  refine List.prefix_iff_eq_take.2 ?_
  apply List.ext_getElem
  · rw [cascadeMiddle_length, List.length_take, cascadeMiddle_length, Nat.min_eq_left hlen]
  · intro j hj1 hj2
    have hj1' : j < l₁.length := by
      have : j < (cascadeMiddle S l₁ h₁).length := hj1
      rwa [cascadeMiddle_length] at this
    have hj2' : j < l₂.length := by omega
    rw [cascadeMiddle_getElem S l₁ h₁ j hj1]
    rw [List.getElem_take]
    rw [cascadeMiddle_getElem S l₂ h₂ j (by rw [cascadeMiddle_length]; exact hj2')]
    have htake : l₁.take (j + 1) = l₂.take (j + 1) := by
      have hpt : l₁.take (j + 1) <+: l₂.take (j + 1) := hp.take (j + 1)
      have hlen1 : (l₁.take (j + 1)).length = j + 1 := by
        rw [List.length_take]
        omega
      have hlen2 : (l₂.take (j + 1)).length = j + 1 := by
        rw [List.length_take]
        omega
      exact List.IsPrefix.eq_of_length_le hpt (by rw [hlen1, hlen2])
    exact output_congr S htake _ _

theorem cascadeMiddle_ne_nil (S : DDS X Y) (l : List X) (h : l ∈ dom S) :
    cascadeMiddle S l h ≠ [] := by
  intro hnil
  have hlen : (cascadeMiddle S l h).length = 0 := by simp [hnil]
  rw [cascadeMiddle_length] at hlen
  have hl : l = [] := List.length_eq_zero_iff.mp hlen
  exact empty_not_mem S (by simpa [hl] using h)

/-- CR18 Definition 3.11: native DDS-level cascade. -/
noncomputable def cascade (S : DDS X Y) (T : DDS Y Z) : DDS X Z :=
  ⟨(fun l : List X =>
      (⟨∃ hS : l ∈ dom S, cascadeMiddle S l hS ∈ dom T,
        fun h =>
          output T (cascadeMiddle S l (Classical.choose h))
            (Classical.choose_spec h)⟩ : Part Z)),
    ⟨by
      intro h
      rcases h with ⟨hS, _⟩
      exact empty_not_mem S hS,
    by
      intro l₁ l₂ hp hne hdom
      rcases hdom with ⟨hS₂, hT₂⟩
      let hS₁ : l₁ ∈ dom S := prefix_closed S hp hne hS₂
      exact ⟨hS₁,
        prefix_closed T (cascadeMiddle_prefix S hS₁ hS₂ hp)
          (cascadeMiddle_ne_nil S l₁ hS₁) hT₂⟩⟩⟩

/-- PFun-native CR18 cascade notation. The subscript avoids colliding with the
existing compatibility-layer `⊲` notation. -/
scoped infixl:70 " ⊲ₚ " => cascade

/-! ### CR18 §3.4.5 / Definition 3.12: output-combine -/

variable {Y' : Type v}

/-- CR18 Definition 3.12: combine the outputs of two `(X,Y)` DDSs.

The combined DDS is defined exactly where both systems are defined, and on such
a history returns `op (S l) (T l)`. -/
def combine (op : Y' → Y' → Y') (S T : DDS X Y') : DDS X Y' :=
  ⟨(fun l : List X =>
      (⟨l ∈ dom S ∧ l ∈ dom T,
        fun h => op (output S l h.1) (output T l h.2)⟩ : Part Y')),
    ⟨by
      intro h
      exact empty_not_mem S h.1,
    by
      intro l₁ l₂ hp hne hdom
      exact ⟨prefix_closed S hp hne hdom.1,
        prefix_closed T hp hne hdom.2⟩⟩⟩

/-- PFun-native CR18 output-combine notation. The operation is explicit because
Lean has no ambient meaning for Maurer's schematic `⋆`. -/
scoped notation:70 S:71 " ⋆ₚ[" op "] " T:70 => combine op S T

@[simp]
theorem combine_dom (op : Y' → Y' → Y') (S T : DDS X Y') (l : List X) :
    l ∈ dom (combine op S T) ↔ l ∈ dom S ∧ l ∈ dom T :=
  Iff.rfl

@[simp]
theorem combine_output (op : Y' → Y' → Y') (S T : DDS X Y')
    (l : List X) (h : l ∈ dom (combine op S T)) :
    output (combine op S T) l h =
      op (output S l ((combine_dom op S T l).mp h).1)
        (output T l ((combine_dom op S T l).mp h).2) :=
  rfl

end PFunDDS

namespace PFunConverter

variable {X : Type z} {Y : Type v} {Z : Type w}

namespace Cascade

/-- One local prefix phase of the CR18 `casc` converter. -/
def stepOutput?
    : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z)))) →
      Option (((InLabel × Z) ∪ₜ (InLabel × (X ∪ₜ Y))))
  | [] => none
  | Sum.inl (InLabel.outside, x) :: rest =>
      match rest with
      | [] => some (Sum.inr (InLabel.inside, Sum.inl x))
      | Sum.inr (InLabel.inside, some (Sum.inl y)) :: rest' =>
          match rest' with
          | [] => some (Sum.inr (InLabel.inside, Sum.inr y))
          | Sum.inr (InLabel.inside, some (Sum.inr z)) :: rest'' =>
              match rest'' with
              | [] => some (Sum.inl (InLabel.outside, z))
              | Sum.inl (InLabel.outside, _) :: _ => stepOutput? rest''
              | _ => none
          | _ => none
      | _ => none
  | _ => none

/-- Accepted converter histories for `casc`: every nonempty prefix is in the
right phase of the three-step protocol. -/
def Valid (l : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))) : Prop :=
  l ≠ [] ∧ ∀ p, p ≠ [] → p <+: l → (stepOutput? p).isSome

theorem valid_prefix
    {l₁ l₂ : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))}
    (hp : l₁ <+: l₂) (hne : l₁ ≠ []) (h : Valid l₂) :
    Valid l₁ := by
  exact ⟨hne, fun p hpne hpp => h.2 p hpne (List.IsPrefix.trans hpp hp)⟩

def roundsTrace :
    List (X × Y × Z) →
      List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))
  | [] => []
  | (x, y, z) :: r =>
      Sum.inl (InLabel.outside, x) ::
      Sum.inr (InLabel.inside, some (Sum.inl y)) ::
      Sum.inr (InLabel.inside, some (Sum.inr z)) ::
      roundsTrace r

def roundsInner : List (X × Y × Z) → List (X ∪ₜ Y)
  | [] => []
  | (x, y, _) :: r => Sum.inl x :: Sum.inr y :: roundsInner r

def roundsInputs (r : List (X × Y × Z)) : List X :=
  r.map fun p => p.1

def roundsMiddle (r : List (X × Y × Z)) : List Y :=
  r.map fun p => p.2.1

def roundsOutputs (r : List (X × Y × Z)) : List Z :=
  r.map fun p => p.2.2

theorem roundsTrace_append (r₁ r₂ : List (X × Y × Z)) :
    roundsTrace (r₁ ++ r₂) = roundsTrace r₁ ++ roundsTrace r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [roundsTrace, ih]

theorem roundsInner_append (r₁ r₂ : List (X × Y × Z)) :
    roundsInner (r₁ ++ r₂) = roundsInner r₁ ++ roundsInner r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [roundsInner, ih]

theorem roundsInputs_append (r₁ r₂ : List (X × Y × Z)) :
    roundsInputs (r₁ ++ r₂) = roundsInputs r₁ ++ roundsInputs r₂ := by
  simp [roundsInputs, List.map_append]

theorem roundsMiddle_append (r₁ r₂ : List (X × Y × Z)) :
    roundsMiddle (r₁ ++ r₂) = roundsMiddle r₁ ++ roundsMiddle r₂ := by
  simp [roundsMiddle, List.map_append]

theorem roundsOutputs_append (r₁ r₂ : List (X × Y × Z)) :
    roundsOutputs (r₁ ++ r₂) = roundsOutputs r₁ ++ roundsOutputs r₂ := by
  simp [roundsOutputs, List.map_append]

theorem stepOutput?_roundsTrace_append (r : List (X × Y × Z))
    {x : X}
    {tail : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))}
    (htail : tail.head? = some (Sum.inl (InLabel.outside, x))) :
    stepOutput? (X := X) (Y := Y) (Z := Z) (roundsTrace r ++ tail) =
      stepOutput? (X := X) (Y := Y) (Z := Z) tail := by
  induction r with
  | nil =>
      simp [roundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      obtain ⟨x', rest', heq⟩ :
          ∃ (x' : X)
            (rest' : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))),
            roundsTrace r ++ tail = Sum.inl (InLabel.outside, x') :: rest' := by
        cases r with
        | nil =>
            cases tail with
            | nil =>
                simp at htail
            | cons i tl =>
                have hi : i = Sum.inl (InLabel.outside, x) := by
                  simpa using htail
                exact ⟨x, tl, by simp [roundsTrace, hi]⟩
        | cons q r' =>
            obtain ⟨a', b', c'⟩ := q
            exact ⟨a',
              Sum.inr (InLabel.inside, some (Sum.inl b')) ::
              Sum.inr (InLabel.inside, some (Sum.inr c')) ::
              (roundsTrace r' ++ tail), by simp [roundsTrace]⟩
      rw [show roundsTrace ((a, b, c) :: r) ++ tail =
          Sum.inl (InLabel.outside, a) ::
          Sum.inr (InLabel.inside, some (Sum.inl b)) ::
          Sum.inr (InLabel.inside, some (Sum.inr c)) ::
          (roundsTrace r ++ tail) from by simp [roundsTrace], heq]
      rw [show stepOutput? (X := X) (Y := Y) (Z := Z)
            (Sum.inl (InLabel.outside, a) ::
            Sum.inr (InLabel.inside, some (Sum.inl b)) ::
            Sum.inr (InLabel.inside, some (Sum.inr c)) ::
            Sum.inl (InLabel.outside, x') :: rest') =
          stepOutput? (X := X) (Y := Y) (Z := Z)
            (Sum.inl (InLabel.outside, x') :: rest') from by
        simp [stepOutput?]]
      rw [← heq]
      exact ih

end Cascade

/-- CR18 Definition 3.11: the deterministic converter `casc`, with outside
interface `(X,Z)` and inner parallel access to `(X,Y)` and `(Y,Z)` systems. -/
def cascadeConverter : DDC X Z (X ∪ₜ Y) (Y ∪ₜ Z) :=
  ⟨(fun l : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z)))) =>
      (⟨Cascade.Valid l,
        fun h => (Cascade.stepOutput? l).get (h.2 l h.1 (List.prefix_refl l))⟩ :
        Part (((InLabel × Z) ∪ₜ (InLabel × (X ∪ₜ Y)))))),
    ⟨by simp [Cascade.Valid], by
      intro l₁ l₂ hp hne hdom
      exact Cascade.valid_prefix hp hne hdom⟩⟩

/-- CR18 notation for the `casc` converter. -/
scoped notation "cascᶜ" => cascadeConverter

/-- Projection of the inner parallel-access history to the left system. -/
def cascadeLeftHistory (l : List (X ∪ₜ Y)) : List X :=
  l.filterMap fun q =>
    match q with
    | Sum.inl x => some x
    | Sum.inr _ => none

/-- Projection of the inner parallel-access history to the right system. -/
def cascadeRightHistory (l : List (X ∪ₜ Y)) : List Y :=
  l.filterMap fun q =>
    match q with
    | Sum.inl _ => none
    | Sum.inr y => some y

theorem cascadeLeftHistory_append (l₁ l₂ : List (X ∪ₜ Y)) :
    cascadeLeftHistory (l₁ ++ l₂) =
      cascadeLeftHistory l₁ ++ cascadeLeftHistory l₂ :=
  List.filterMap_append

theorem cascadeRightHistory_append (l₁ l₂ : List (X ∪ₜ Y)) :
    cascadeRightHistory (l₁ ++ l₂) =
      cascadeRightHistory l₁ ++ cascadeRightHistory l₂ :=
  List.filterMap_append

theorem cascadeLeftHistory_roundsInner (r : List (X × Y × Z)) :
    cascadeLeftHistory (Cascade.roundsInner r) = Cascade.roundsInputs r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [Cascade.roundsInner, Cascade.roundsInputs, cascadeLeftHistory]
      simpa [cascadeLeftHistory, Cascade.roundsInputs] using ih

theorem cascadeRightHistory_roundsInner (r : List (X × Y × Z)) :
    cascadeRightHistory (Cascade.roundsInner r) = Cascade.roundsMiddle r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [Cascade.roundsInner, Cascade.roundsMiddle, cascadeRightHistory]
      simpa [cascadeRightHistory, Cascade.roundsMiddle] using ih

/-- Local domain condition for the inner DDS giving `casc` parallel access to
`S` and `T`. -/
def cascadeAccessStep (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    (p : List (X ∪ₜ Y)) : Prop :=
  match p.getLast? with
  | some (Sum.inl _) => cascadeLeftHistory p ∈ PFunDDS.dom S
  | some (Sum.inr _) => cascadeRightHistory p ∈ PFunDDS.dom T
  | none => False

/-- The single inner DDS representing parallel access to `S` and `T` for
`casc[S,T]`. -/
noncomputable def cascadeAccess (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z) :
    PFunDDS.DDS (X ∪ₜ Y) (Y ∪ₜ Z) :=
  ⟨(fun l : List (X ∪ₜ Y) =>
      (⟨l ≠ [] ∧ ∀ p, p ≠ [] → p <+: l → cascadeAccessStep S T p,
        fun h =>
          match hlast : l.getLast? with
          | some (Sum.inl _) =>
              Sum.inl (PFunDDS.output S (cascadeLeftHistory l) (by
                simpa [cascadeAccessStep, hlast] using h.2 l h.1 (List.prefix_refl l)))
          | some (Sum.inr _) =>
              Sum.inr (PFunDDS.output T (cascadeRightHistory l) (by
                simpa [cascadeAccessStep, hlast] using h.2 l h.1 (List.prefix_refl l)))
          | none =>
              False.elim (h.1 (List.getLast?_eq_none_iff.mp hlast))⟩ :
        Part (Y ∪ₜ Z))),
    ⟨by simp, by
      intro l₁ l₂ hp hne hdom
      exact ⟨hne, fun p hpne hpp => hdom.2 p hpne (List.IsPrefix.trans hpp hp)⟩⟩⟩

theorem cascadeAccess_dom_snoc (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ∪ₜ Y)} {a : X ∪ₜ Y}
    (hp : p = [] ∨ p ∈ PFunDDS.dom (cascadeAccess S T))
    (hstep : cascadeAccessStep S T (p ++ [a])) :
    p ++ [a] ∈ PFunDDS.dom (cascadeAccess S T) := by
  refine ⟨by simp, ?_⟩
  intro q hqne hqpre
  rcases List.prefix_concat_iff.mp hqpre with hq | hq
  · subst hq
    exact hstep
  · rcases hp with rfl | hp
    · exact absurd (List.prefix_nil.mp hq) hqne
    · exact hp.2 q hqne hq

theorem cascadeAccess_output_inl (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ∪ₜ Y)} (h : p ∈ PFunDDS.dom (cascadeAccess S T)) {x : X}
    (hlast : p.getLast? = some (Sum.inl x))
    (hL : cascadeLeftHistory p ∈ PFunDDS.dom S) :
    PFunDDS.output (cascadeAccess S T) p h =
      Sum.inl (PFunDDS.output S (cascadeLeftHistory p) hL) := by
  simp [cascadeAccess, PFunDDS.output]
  split <;> rename_i heq
  · rfl
  · rw [hlast] at heq
    cases heq
  · rw [hlast] at heq
    cases heq

theorem cascadeAccess_output_inr (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z)
    {p : List (X ∪ₜ Y)} (h : p ∈ PFunDDS.dom (cascadeAccess S T)) {y : Y}
    (hlast : p.getLast? = some (Sum.inr y))
    (hR : cascadeRightHistory p ∈ PFunDDS.dom T) :
    PFunDDS.output (cascadeAccess S T) p h =
      Sum.inr (PFunDDS.output T (cascadeRightHistory p) hR) := by
  simp [cascadeAccess, PFunDDS.output]
  split <;> rename_i heq
  · rw [hlast] at heq
    cases heq
  · rfl
  · rw [hlast] at heq
    cases heq

/-- CR18 §3.4.4 converter-side construction: `casc[S,T]`.

At the paper-facing PFun layer, converter application is the mathematical
partial function induced by the converter. For the cascade converter this is
the native cascade partial function itself; the raw labeled-history converter
above is only a representation of the same converter, not the abstraction used
to state Definition 3.11. -/
noncomputable def cascadeViaConverter
    (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z) : PFunDDS.DDS X Z :=
  PFunDDS.cascade S T

scoped notation "cascᶜ[" S "," T "]" => cascadeViaConverter S T

/-- CR18 Definition 3.11, DDS-level converter equation:
`casc[S,T] = S ⊲ T`. -/
theorem cascadeViaConverter_eq_cascade
    (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z) :
    cascadeViaConverter S T = PFunDDS.cascade S T := by
  rfl

/-! ### CR18 §3.4.5 / Definition 3.12: output-combine converter -/

namespace Combine

/-- One local prefix phase of the CR18 `comb⋆` converter. -/
def stepOutput? (op : Y → Y → Y) :
    List ((InLabel × X) ∪ₜ (InLabel × Option (Sigma (fun _ : Fin 2 => Y)))) →
      Option ((InLabel × Y) ∪ₜ (InLabel × Sigma (fun _ : Fin 2 => X)))
  | [] => none
  | Sum.inl (InLabel.outside, x) :: rest =>
      match rest with
      | [] => some (Sum.inr (InLabel.inside, ⟨(0 : Fin 2), x⟩))
      | Sum.inr (InLabel.inside, some ⟨i₁, y₁⟩) :: rest' =>
          if i₁ = (0 : Fin 2) then
            match rest' with
            | [] => some (Sum.inr (InLabel.inside, ⟨(1 : Fin 2), x⟩))
            | Sum.inr (InLabel.inside, some ⟨i₂, y₂⟩) :: rest'' =>
                if i₂ = (1 : Fin 2) then
                  match rest'' with
                  | [] => some (Sum.inl (InLabel.outside, op y₁ y₂))
                  | Sum.inl (InLabel.outside, _) :: _ => stepOutput? op rest''
                  | _ => none
                else
                  none
            | _ => none
          else
            none
      | _ => none
  | _ => none

/-- Accepted converter histories for `comb⋆`: every nonempty prefix is in the
right phase of the three-step protocol. -/
def Valid (op : Y → Y → Y)
    (l : List ((InLabel × X) ∪ₜ
      (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))) :
    Prop :=
  (stepOutput? (X := X) op l).isSome

theorem valid_prefix (op : Y → Y → Y)
    {l₁ l₂ : List ((InLabel × X) ∪ₜ
      (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))}
    (hp : l₁ <+: l₂) (hne : l₁ ≠ []) (h : Valid (X := X) op l₂) :
    Valid (X := X) op l₁ := by
  induction l₂ using stepOutput?.induct generalizing l₁ with
  | case1 =>
      exact absurd (List.prefix_nil.mp hp) hne
  | case2 x =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · obtain rfl := List.prefix_nil.mp ht
        simp [Valid, stepOutput?]
  | case3 x y₁ =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [Valid, stepOutput?]
        · obtain rfl := List.prefix_nil.mp ht'
          simp [Valid, stepOutput?]
  | case4 x y₁ y₂ =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [Valid, stepOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [Valid, stepOutput?]
          · obtain rfl := List.prefix_nil.mp ht''
            simp [Valid, stepOutput?]
  | case5 x y₁ y₂ x' rest ih =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [Valid, stepOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [Valid, stepOutput?]
          · by_cases htEmpty : t'' = []
            · subst t''
              simp [Valid, stepOutput?]
            · have hrest :
                Valid (X := X) op (Sum.inl (InLabel.outside, x') :: rest) := by
                simpa [Valid, stepOutput?] using h
              have htail : Valid (X := X) op t'' := ih ht'' htEmpty hrest
              rcases List.prefix_cons_iff.mp ht'' with rfl | ⟨tail, rfl, _⟩
              · exact False.elim (htEmpty rfl)
              · simpa [Valid, stepOutput?] using htail
  | case6 x y₁ y₂ y' rest =>
      simp [Valid, stepOutput?] at h
  | case7 x y₁ y₂ rest rest'' hne₂ =>
      simp [Valid, stepOutput?, hne₂] at h
  | case8 x y₁ i₂ y₂ =>
      simp [Valid, stepOutput?] at h
  | case9 x y₁ rest rest'' hne₁ =>
      exfalso
      fin_cases y₁
      · exact hne₁ rfl
      · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
        cases rest'' with
        | nil =>
            simp [Valid, stepOutput?, h10] at h
        | cons head tail =>
            cases head with
            | inl p =>
                cases p
                simp [Valid, stepOutput?, h10] at h
            | inr p =>
                cases p
                rename_i side oy
                cases side <;> cases oy <;> simp [Valid, stepOutput?, h10] at h
  | case10 x i₁ y₁ =>
      simp [Valid, stepOutput?] at h
  | case11 i rest =>
      simp [Valid, stepOutput?] at h

def pair (S T : PFunDDS.DDS X Y) :
    (i : Fin 2) → PFunDDS.DDS ((fun _ : Fin 2 => X) i) ((fun _ : Fin 2 => Y) i) :=
  fun i => if i = (0 : Fin 2) then S else T

def roundsTrace :
    List (X × Y × Y) →
      List ((InLabel × X) ∪ₜ (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))
  | [] => []
  | (x, y₁, y₂) :: r =>
      Sum.inl (InLabel.outside, x) ::
      Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), y₁⟩) ::
      Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), y₂⟩) ::
      roundsTrace r

def roundsInner :
    List (X × Y × Y) → List (Sigma (fun _ : Fin 2 => X))
  | [] => []
  | (x, _y₁, _y₂) :: r =>
      ⟨(0 : Fin 2), x⟩ :: ⟨(1 : Fin 2), x⟩ :: roundsInner r

def roundsInputs (r : List (X × Y × Y)) : List X :=
  r.map fun p => p.1

def roundsOutputs (op : Y → Y → Y) (r : List (X × Y × Y)) : List Y :=
  r.map fun p => op p.2.1 p.2.2

theorem roundsTrace_append (r₁ r₂ : List (X × Y × Y)) :
    roundsTrace (r₁ ++ r₂) = roundsTrace r₁ ++ roundsTrace r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsTrace, ih]

theorem roundsInner_append (r₁ r₂ : List (X × Y × Y)) :
    roundsInner (r₁ ++ r₂) = roundsInner r₁ ++ roundsInner r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsInner, ih]

theorem roundsInputs_append (r₁ r₂ : List (X × Y × Y)) :
    roundsInputs (r₁ ++ r₂) = roundsInputs r₁ ++ roundsInputs r₂ := by
  simp [roundsInputs, List.map_append]

theorem roundsOutputs_append (op : Y → Y → Y) (r₁ r₂ : List (X × Y × Y)) :
    roundsOutputs op (r₁ ++ r₂) = roundsOutputs op r₁ ++ roundsOutputs op r₂ := by
  simp [roundsOutputs, List.map_append]

theorem stepOutput?_roundsTrace_append (op : Y → Y → Y)
    (r : List (X × Y × Y))
    {x : X}
    {tail : List ((InLabel × X) ∪ₜ
      (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))}
    (htail : tail.head? = some (Sum.inl (InLabel.outside, x))) :
    stepOutput? (X := X) op (roundsTrace r ++ tail) =
      stepOutput? (X := X) op tail := by
  induction r with
  | nil =>
      simp [roundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      obtain ⟨x', rest', heq⟩ :
          ∃ (x' : X)
            (rest' : List ((InLabel × X) ∪ₜ
              (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))),
            roundsTrace r ++ tail = Sum.inl (InLabel.outside, x') :: rest' := by
        cases r with
        | nil =>
            cases tail with
            | nil =>
                simp at htail
            | cons i tl =>
                have hi : i = Sum.inl (InLabel.outside, x) := by
                  simpa using htail
                exact ⟨x, tl, by simp [roundsTrace, hi]⟩
        | cons q r' =>
            obtain ⟨a', b', c'⟩ := q
            exact ⟨a',
              Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), b'⟩) ::
              Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), c'⟩) ::
              (roundsTrace r' ++ tail), by simp [roundsTrace]⟩
      rw [show roundsTrace ((a, b, c) :: r) ++ tail =
          Sum.inl (InLabel.outside, a) ::
          Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), b⟩) ::
          Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), c⟩) ::
          (roundsTrace r ++ tail) from by simp [roundsTrace], heq]
      rw [show stepOutput? (X := X) op
            (Sum.inl (InLabel.outside, a) ::
            Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), b⟩) ::
            Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), c⟩) ::
            Sum.inl (InLabel.outside, x') :: rest') =
          stepOutput? (X := X) op
            (Sum.inl (InLabel.outside, x') :: rest') from by
        simp [stepOutput?]]
      rw [← heq]
      exact ih

theorem valid_roundsTrace_two_iff (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X)
    (a : Option (Sigma (fun _ : Fin 2 => Y))) :
    Valid (X := X) op
        (roundsTrace r ++
          [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, a)]) ↔
      ∃ y₁ : Y, a = some (Sigma.mk (0 : Fin 2) y₁) := by
  rw [Valid, stepOutput?_roundsTrace_append op r rfl]
  cases a with
  | none =>
      simp [stepOutput?]
  | some s =>
      cases s with
      | mk i y₁ =>
          fin_cases i <;> simp [stepOutput?]

theorem valid_roundsTrace_three_iff (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X) (y₁ : Y)
    (a : Option (Sigma (fun _ : Fin 2 => Y))) :
    Valid (X := X) op
        (roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
           Sum.inr (InLabel.inside, a)]) ↔
      ∃ y₂ : Y, a = some (Sigma.mk (1 : Fin 2) y₂) := by
  rw [Valid, stepOutput?_roundsTrace_append op r rfl]
  cases a with
  | none =>
      simp [stepOutput?]
  | some s =>
      cases s with
      | mk i y₂ =>
          fin_cases i <;> simp [stepOutput?]

theorem restrict_roundsInner_zero (r : List (X × Y × Y)) :
    PFunDDS.restrict (Xs := fun _ : Fin 2 => X) (0 : Fin 2) (roundsInner r) =
      roundsInputs r := by
  induction r with
  | nil =>
      rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsInner, roundsInputs, PFunDDS.restrict]
      simpa [PFunDDS.restrict, roundsInputs] using ih

theorem restrict_roundsInner_one (r : List (X × Y × Y)) :
    PFunDDS.restrict (Xs := fun _ : Fin 2 => X) (1 : Fin 2) (roundsInner r) =
      roundsInputs r := by
  induction r with
  | nil =>
      rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsInner, roundsInputs, PFunDDS.restrict]
      simpa [PFunDDS.restrict, roundsInputs] using ih

end Combine

/-- CR18 Definition 3.12: the deterministic converter `comb⋆`.

It has outside interface `(X,Y)` and inner parallel access to two `(X,Y)`
systems. On an outside input `x`, it queries the first inner system on `x`, then
the second inner system on `x`, then outputs `op y₁ y₂`. -/
def combineConverter (op : Y → Y → Y) :
    DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)) :=
  ⟨(fun l : List ((InLabel × X) ∪ₜ
        (InLabel × Option (Sigma (fun _ : Fin 2 => Y)))) =>
      (⟨Combine.Valid (X := X) op l,
        fun h => (Combine.stepOutput? (X := X) op l).get
          h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × Sigma (fun _ : Fin 2 => X))))),
    ⟨by simp [Combine.Valid, Combine.stepOutput?], by
      intro l₁ l₂ hp hne hdom
      exact Combine.valid_prefix (X := X) op hp hne hdom⟩⟩

/-- CR18 notation for the `comb⋆` converter. -/
scoped notation "comb⋆ᶜ[" op "]" => combineConverter op

theorem combineConverter_output_two (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X) (y₁ : Y)
    (hc :
      Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁))] ∈
        PFunDDS.dom (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))) :
    PFunDDS.output
        (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))
        (Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁))]) hc =
      Sum.inr (InLabel.inside, Sigma.mk (1 : Fin 2) x) := by
  change (Combine.stepOutput? (X := X) op _).get _ = _
  have hct :
      Combine.stepOutput? (X := X) op
          (Combine.roundsTrace r ++
            [Sum.inl (InLabel.outside, x),
             Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁))]) =
        some (Sum.inr (InLabel.inside, Sigma.mk (1 : Fin 2) x)) := by
    rw [Combine.stepOutput?_roundsTrace_append op r rfl]
    simp [Combine.stepOutput?]
  simp [hct]

theorem combineConverter_output_three (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X) (y₁ y₂ : Y)
    (hc :
      Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
           Sum.inr (InLabel.inside, some (Sigma.mk (1 : Fin 2) y₂))] ∈
        PFunDDS.dom (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))) :
    PFunDDS.output
        (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))
        (Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
           Sum.inr (InLabel.inside, some (Sigma.mk (1 : Fin 2) y₂))]) hc =
      Sum.inl (InLabel.outside, op y₁ y₂) := by
  change (Combine.stepOutput? (X := X) op _).get _ = _
  have hct :
      Combine.stepOutput? (X := X) op
          (Combine.roundsTrace r ++
            [Sum.inl (InLabel.outside, x),
             Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
             Sum.inr (InLabel.inside, some (Sigma.mk (1 : Fin 2) y₂))]) =
        some (Sum.inl (InLabel.outside, op y₁ y₂)) := by
    rw [Combine.stepOutput?_roundsTrace_append op r rfl]
    simp [Combine.stepOutput?]
  simp [hct]

/-- CR18 §3.4.5 converter-side construction: `comb⋆[S,T]`.

As with cascade, this is the semantic DDS-level application of the paper
converter, not the raw labeled-history interpreter. -/
noncomputable def combineViaConverter
    (op : Y → Y → Y) (S T : PFunDDS.DDS X Y) : PFunDDS.DDS X Y :=
  PFunDDS.combine op S T

scoped notation "comb⋆ᶜ[" op "][" S "," T "]" => combineViaConverter op S T

/-- CR18 Definition 3.12, DDS-level converter equation:
`comb⋆[S,T] = S ⋆ T`. -/
theorem combineViaConverter_eq_combine
    (op : Y → Y → Y) (S T : PFunDDS.DDS X Y) :
    combineViaConverter op S T = PFunDDS.combine op S T := by
  rfl

/-!
### CR18 Lemma 3.1: appending converters at distinct interfaces

This is the PFun-native, paper-facing attachment model.  A converter attached
at one interface is represented by the pure functions it induces on that
interface:

* `αin : X → Option X`, the partial input sent to the inner resource;
* `αout : X → Y → Y`, the outside output transformation after the resource
  answers.

Attaching at interface `i` is therefore just a coordinate-wise partial
translation of resource histories, followed by a last-output transformation at
interface `i`.  No trace language or driver loop is involved.
-/

section Attach

variable {P : Type u} [DecidableEq P]

/-- Entrywise input translation for attaching a converter at interface `i`. -/
def attachEntry (i : P) (αin : X → Option X) (e : P × X) : Option (P × X) :=
  if e.1 = i then
    (αin e.2).map fun x => (i, x)
  else
    some e

/-- Total form of `attachEntry`, used only for histories whose entries are
known to translate. -/
def attachEntryD (i : P) (αin : X → Option X) (e : P × X) : P × X :=
  (attachEntry i αin e).getD e

/-- A history is translatable at interface `i` when every `i`-entry is accepted
by the attached converter's input translation. -/
def attachDefined (i : P) (αin : X → Option X) (l : List (P × X)) : Prop :=
  ∀ e ∈ l, (attachEntry i αin e).isSome

/-- The resource history seen after attaching a converter at interface `i`. -/
def attachHistory (i : P) (αin : X → Option X) (l : List (P × X)) :
    List (P × X) :=
  l.map (attachEntryD i αin)

/-- The output transformation induced by an attached converter at the last
interface queried by the resource history. -/
def attachOutput (i : P) (αout : X → Y → Y) (l : List (P × X)) (y : Y) : Y :=
  match l.getLast? with
  | some (p, x) => if p = i then αout x y else y
  | none => y

@[simp]
theorem attachEntryD_fst (i : P) (αin : X → Option X) (e : P × X) :
    (attachEntryD i αin e).1 = e.1 := by
  unfold attachEntryD attachEntry
  by_cases he : e.1 = i
  · simp [he]
    cases αin e.2 <;> simp [he]
  · simp [he]

theorem attachEntryD_of_ne (i : P) (αin : X → Option X) {e : P × X}
    (he : e.1 ≠ i) :
    attachEntryD i αin e = e := by
  unfold attachEntryD attachEntry
  simp [he]

theorem attachEntryD_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (e : P × X) :
    attachEntryD i αin (attachEntryD j βin e) =
      attachEntryD j βin (attachEntryD i αin e) := by
  by_cases hei : e.1 = i
  · have hej : e.1 ≠ j := by
      intro h
      exact hij (hei.symm.trans h)
    rw [attachEntryD_of_ne j βin hej]
    have hnotj : (attachEntryD i αin e).1 ≠ j := by
      rw [attachEntryD_fst]
      exact hej
    rw [attachEntryD_of_ne j βin hnotj]
  · by_cases hej : e.1 = j
    · rw [attachEntryD_of_ne i αin hei]
      have hnoti : (attachEntryD j βin e).1 ≠ i := by
        rw [attachEntryD_fst]
        exact hei
      rw [attachEntryD_of_ne i αin hnoti]
    · simp [attachEntryD_of_ne i αin hei, attachEntryD_of_ne j βin hej]

theorem attachHistory_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (l : List (P × X)) :
    attachHistory i αin (attachHistory j βin l) =
      attachHistory j βin (attachHistory i αin l) := by
  simp [attachHistory, List.map_map, attachEntryD_comm i j hij αin βin]

theorem attachEntry_isSome_of_ne (i : P) (αin : X → Option X) {e : P × X}
    (he : e.1 ≠ i) :
    (attachEntry i αin e).isSome := by
  simp [attachEntry, he]

theorem attachEntry_isSome_attachEntryD (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (e : P × X) :
    (attachEntry i αin (attachEntryD j βin e)).isSome =
      (attachEntry i αin e).isSome := by
  by_cases hei : e.1 = i
  · have hej : e.1 ≠ j := by
      intro h
      exact hij (hei.symm.trans h)
    rw [attachEntryD_of_ne j βin hej]
  · have htag : (attachEntryD j βin e).1 ≠ i := by
      rw [attachEntryD_fst]
      exact hei
    rw [attachEntry_isSome_of_ne i αin htag,
      attachEntry_isSome_of_ne i αin hei]

theorem attachDefined_history_iff (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (l : List (P × X)) :
    attachDefined i αin (attachHistory j βin l) ↔
      attachDefined i αin l := by
  constructor
  · intro h e he
    have hmem : attachEntryD j βin e ∈ attachHistory j βin l := by
      simpa [attachHistory] using List.mem_map_of_mem he
    have := h (attachEntryD j βin e) hmem
    simpa [attachEntry_isSome_attachEntryD i j hij αin βin e] using this
  · intro h e he
    rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩
    simpa [attachEntry_isSome_attachEntryD i j hij αin βin e₀] using h e₀ he₀

theorem attachOutput_history_eq (i j : P) (hij : i ≠ j)
    (αout : X → Y → Y) (βin : X → Option X) (l : List (P × X)) (y : Y) :
    attachOutput i αout (attachHistory j βin l) y =
      attachOutput i αout l y := by
  have hlast :
      (attachHistory j βin l).getLast? =
        l.getLast?.map (attachEntryD j βin) := by
    simp [attachHistory, List.getLast?_map]
  cases hl : l.getLast? with
  | none =>
      simp [attachOutput, hlast, hl]
  | some e =>
      rcases e with ⟨p, x⟩
      by_cases hpi : p = i
      · have hpj : i ≠ j := hij
        have hfix : attachEntryD j βin (i, x) = (i, x) :=
          attachEntryD_of_ne j βin hpj
        simp [attachOutput, hlast, hl, hpi, hfix]
      · have htag : (attachEntryD j βin (p, x)).1 ≠ i := by
          rw [attachEntryD_fst]
          exact hpi
        simp [attachOutput, hlast, hl, hpi]

theorem attachOutput_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (αout βout : X → Y → Y)
    (l : List (P × X)) (y : Y) :
    attachOutput i αout l
        (attachOutput j βout (attachHistory i αin l) y) =
      attachOutput j βout l
        (attachOutput i αout (attachHistory j βin l) y) := by
  rw [attachOutput_history_eq j i hij.symm βout αin,
    attachOutput_history_eq i j hij αout βin]
  cases hl : l.getLast? with
  | none =>
      simp [attachOutput, hl]
  | some e =>
      rcases e with ⟨p, x⟩
      by_cases hpi : p = i
      · simp [attachOutput, hl, hpi, hij]
      · by_cases hpj : p = j
        · simp [attachOutput, hl, hpj, hij.symm]
        · simp [attachOutput, hl, hpi, hpj]

/-- CR18 Definition 3.13, PFun-native semantic attachment at one interface. -/
noncomputable def attachAt (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : PFunDDS.Resource P X Y) : PFunDDS.Resource P X Y :=
  ⟨(fun l : List (P × X) =>
      (⟨attachDefined i αin l ∧ attachHistory i αin l ∈ PFunDDS.dom S,
        fun h =>
          attachOutput i αout l
            (PFunDDS.output S (attachHistory i αin l) h.2)⟩ : Part Y)),
    ⟨by
      intro h
      exact PFunDDS.empty_not_mem S h.2,
    by
      intro l₁ l₂ hprefix hne hdom
      refine ⟨?_, ?_⟩
      · intro e he
        exact hdom.1 e (hprefix.subset he)
      · exact PFunDDS.prefix_closed S (hprefix.map (attachEntryD i αin)) (by
          intro hnil
          exact hne (List.map_eq_nil_iff.mp hnil)) hdom.2⟩⟩

@[simp]
theorem attachAt_dom_iff (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : PFunDDS.Resource P X Y) (l : List (P × X)) :
    l ∈ PFunDDS.dom (attachAt i αin αout S) ↔
      attachDefined i αin l ∧ attachHistory i αin l ∈ PFunDDS.dom S :=
  Iff.rfl

@[simp]
theorem attachAt_output (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : PFunDDS.Resource P X Y) (l : List (P × X))
    (h : l ∈ PFunDDS.dom (attachAt i αin αout S)) :
    PFunDDS.output (attachAt i αin αout S) l h =
      attachOutput i αout l
        (PFunDDS.output S (attachHistory i αin l)
          ((attachAt_dom_iff i αin αout S l).mp h).2) :=
  rfl

theorem attachAt_mem_iff (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : PFunDDS.Resource P X Y) (l : List (P × X)) (y : Y) :
    y ∈ (↑(attachAt i αin αout S) : PFunDDS.Raw (P × X) Y) l ↔
      attachDefined i αin l ∧
        ∃ hS : attachHistory i αin l ∈ PFunDDS.dom S,
          attachOutput i αout l
            (PFunDDS.output S (attachHistory i αin l) hS) = y := by
  constructor
  · rintro ⟨hdom, hout⟩
    exact ⟨hdom.1, hdom.2, hout⟩
  · rintro ⟨hdef, hS, hout⟩
    exact ⟨⟨hdef, hS⟩, hout⟩

/-- CR18 Lemma 3.1: appending converters at distinct interfaces commutes. -/
theorem attachAt_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (αout βout : X → Y → Y)
    (S : PFunDDS.Resource P X Y) :
    attachAt i αin αout (attachAt j βin βout S) =
      attachAt j βin βout (attachAt i αin αout S) := by
  -- Functional equality of two partial functions: same domain, same value.
  -- The two memoryless operators commute because they act on disjoint
  -- interfaces (`i ≠ j`), reduced to the three algebraic facts below.
  apply Subtype.ext
  funext l
  apply Part.ext'
  · -- domains agree
    show l ∈ PFunDDS.dom (attachAt i αin αout (attachAt j βin βout S)) ↔
        l ∈ PFunDDS.dom (attachAt j βin βout (attachAt i αin αout S))
    simp only [attachAt_dom_iff, attachDefined_history_iff i j hij αin βin l,
      attachDefined_history_iff j i hij.symm βin αin l,
      attachHistory_comm i j hij αin βin l]
    tauto
  · -- values agree
    intro h₁ h₂
    have pL : attachHistory j βin (attachHistory i αin l) ∈ PFunDDS.dom S :=
      ((attachAt_dom_iff j βin βout S (attachHistory i αin l)).mp
        ((attachAt_dom_iff i αin αout (attachAt j βin βout S) l).mp h₁).2).2
    have pR : attachHistory i αin (attachHistory j βin l) ∈ PFunDDS.dom S :=
      ((attachAt_dom_iff i αin αout S (attachHistory j βin l)).mp
        ((attachAt_dom_iff j βin βout (attachAt i αin αout S) l).mp h₂).2).2
    show PFunDDS.output (attachAt i αin αout (attachAt j βin βout S)) l h₁ =
        PFunDDS.output (attachAt j βin βout (attachAt i αin αout S)) l h₂
    simp only [attachAt_output]
    rw [PFunDDS.output_congr S (attachHistory_comm i j hij αin βin l).symm pL pR]
    exact attachOutput_comm i j hij αin βin αout βout l _

end Attach

/-! ### CR18 Definition 3.13 / Lemma 3.1 — general stateful interface attachment

The `Attach` section above models only *memoryless* interface converters (a pure
input map `αin` and output map `αout`, one inner query per outside query). Here
is the faithful general form: an arbitrary stateful `((X,Y),(X,Y))`-DDC `α`
attached at interface `i` of a `(P × X, Y)`-resource, exactly as CR18
Definition 3.13 describes — an `i`-query runs `α`, routing each of `α`'s inner
queries to interface `i` of the resource (via `s⊥`) and feeding the answers back
until `α` outputs; queries at other interfaces pass straight through. It is built
on the function-native `resolve`/`PFun.fix` machinery, with no driver loop. -/

namespace General

open DDC

variable {P : Type u} [DecidableEq P]

/-- CR18 Definition 3.13, one connection step of a general `((X,Y),(X,Y))`-DDC
`α` attached at interface `i`: read `α`'s next move; finish with its outside
output `y`, or route its inner query `x` to interface `i` of the resource (via
`s⊥`) and continue. State is `(α-history, resource-history)`.

Faithful to CR18 Definition 3.3: `α` always receives an answer (the `s⊥` value,
`some y` or `⊥ = none`), but the *recorded* resource history only retains the
query when `s` is actually defined on it — an undefined query is deleted from the
history (`keptPrefix`), so a later pass-through at another interface reads `s.1`
on a genuine element of `dom s`. -/
noncomputable def attachStep (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) :
    (List (CIn X Y) × List (P × X)) →.
      (Y × (List (CIn X Y) × List (P × X))) ⊕ (List (CIn X Y) × List (P × X)) :=
  fun st =>
    (α.1 st.1).bind fun o =>
      match o with
      | Sum.inl (InLabel.outside, y) => Part.some (Sum.inl (y, st))
      | Sum.inr (InLabel.inside, x) =>
          let ans : Option Y :=
            PFunDDS.output (PFunDDS.fullyDefined s) (st.2 ++ [(i, x)])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
          Part.some (Sum.inr
            (st.1 ++ [Sum.inr (InLabel.inside, ans)],
             match ans with
             | some _ => st.2 ++ [(i, x)]
             | none => st.2))
      | _ => Part.none

/-- The inner resolution of one `i`-round: least fixed point of `attachStep`. -/
noncomputable def attachResolve (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) :
    (List (CIn X Y) × List (P × X)) →. (Y × (List (CIn X Y) × List (P × X))) :=
  (attachStep i α s).fix

omit [DecidableEq P] in
/-- CR18 Def 3.13 output rule (= `PFun.fix_stop`): if `α` outputs `(out, y)`, the
`i`-round returns `y` with histories unchanged. -/
theorem attachResolve_out (i : P) (α : DDC X Y X Y) (s : PFunDDS.Resource P X Y)
    {c : List (CIn X Y)} {rs : List (P × X)} {y : Y}
    (h : Sum.inl (InLabel.outside, y) ∈ α.1 c) :
    (y, (c, rs)) ∈ attachResolve i α s (c, rs) := by
  refine PFun.fix_stop (f := attachStep i α s) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

omit [DecidableEq P] in
/-- CR18 Def 3.13 query rule (= `PFun.fix_fwd_eq`): if `α` outputs `(in, x)`, the
`i`-round continues with `α`'s history extended by `s⊥`'s answer; the resource
history is extended by `(i, x)` only when `s` is defined there (`keptPrefix`). -/
theorem attachResolve_in (i : P) (α : DDC X Y X Y) (s : PFunDDS.Resource P X Y)
    {c : List (CIn X Y)} {rs : List (P × X)} {x : X}
    (h : Sum.inr (InLabel.inside, x) ∈ α.1 c) :
    attachResolve i α s (c, rs) =
      attachResolve i α s
        (c ++ [Sum.inr (InLabel.inside,
            PFunDDS.output (PFunDDS.fullyDefined s) (rs ++ [(i, x)])
              (by rw [PFunDDS.dom_fullyDefined]; simp))],
          match PFunDDS.output (PFunDDS.fullyDefined s) (rs ++ [(i, x)])
              (by rw [PFunDDS.dom_fullyDefined]; simp) with
          | some _ => rs ++ [(i, x)]
          | none => rs) := by
  refine PFun.fix_fwd_eq (f := attachStep i α s) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

/-- Process one outside entry: an `i`-entry runs `α`'s round (`attachResolve`);
any other entry passes straight through to the resource. -/
noncomputable def attachEntryStep (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (e : P × X) :
    Part (Y × (List (CIn X Y) × List (P × X))) :=
  if e.1 = i then
    attachResolve i α s (st.1 ++ [Sum.inl (InLabel.outside, e.2)], st.2)
  else
    (s.1 (st.2 ++ [e])).map fun y => (y, (st.1, st.2 ++ [e]))

/-- CR18 Definition 3.13 outer iteration: thread the `(α-history, resource-
history)` state through the outside history, collecting outputs. -/
noncomputable def attachDrive (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) :
    (List (CIn X Y) × List (P × X)) → List (P × X) →.
      (List Y × (List (CIn X Y) × List (P × X)))
  | st, [] => Part.some ([], st)
  | st, e :: rest =>
      (attachEntryStep i α s st e).bind fun r =>
        (attachDrive i α s r.2 rest).map fun rr => (r.1 :: rr.1, rr.2)

theorem attachDrive_length (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (l : List (P × X))
    {r : List Y × (List (CIn X Y) × List (P × X))}
    (h : r ∈ attachDrive i α s st l) : r.1.length = l.length := by
  induction l generalizing st r with
  | nil => simp only [attachDrive, Part.mem_some_iff] at h; subst h; simp
  | cons e rest ih =>
      simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _hr', rr, hrr, rfl⟩ := h
      simp [ih r'.2 hrr]

theorem attachDrive_append (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (a b : List (P × X)) :
    attachDrive i α s st (a ++ b) =
      (attachDrive i α s st a).bind fun ra =>
        (attachDrive i α s ra.2 b).map fun rb => (ra.1 ++ rb.1, rb.2) := by
  induction a generalizing st with
  | nil =>
      simp only [List.nil_append, attachDrive, Part.bind_some]
      refine (Part.map_id' ?_ _).symm
      intro rb; rfl
  | cons e rest ih =>
      simp only [List.cons_append, attachDrive, ih, Part.bind_assoc, Part.bind_map,
        Part.map_bind, Part.map_map, Function.comp_def, List.cons_append]

/-- The applied resource as a raw partial function: replay the whole interaction
and return the last entry's output. -/
noncomputable def attachRaw (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) : PFunDDS.Raw (P × X) Y :=
  fun l => (attachDrive i α s ([], []) l).bind fun r =>
    match r.1.getLast? with
    | some y => Part.some y
    | none => Part.none

/-- CR18 Definition 3.13: a general stateful converter `α` attached at interface
`i` of a resource `s`. Faithful to Maurer's multi-query, stateful description;
`Valid` (Maurer's "one would have to show αⁱs is a `(P×X,Y)`-DDS") is discharged
from the structural driver lemmas. -/
noncomputable def attachAt (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) : PFunDDS.Resource P X Y :=
  ⟨attachRaw i α s, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]; rintro ⟨v, hv⟩
      simp [attachRaw, attachDrive] at hv
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨suf, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      simp only [attachRaw, Part.mem_bind_iff] at hv
      obtain ⟨r, hr, _hvr⟩ := hv
      rw [attachDrive_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _hr2⟩ := hr
      have hlen : ra.1.length = l₁.length :=
        attachDrive_length i α s ([], []) l₁ hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil; apply hne; apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      simp only [attachRaw, Part.mem_bind_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]; exact Part.mem_some _⟩

/-- Transparency: appending a non-`j` entry `e` to the input of `attachAt j β`
just passes `e` straight through to the base resource `s` (it is *not* expanded
by `β`). Immediate from `attachDrive_append` and the pass-through branch. -/
theorem attachDrive_passthrough (j : P) (β : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (e : P × X) (hej : e.1 ≠ j)
    (st : List (CIn X Y) × List (P × X)) (h : List (P × X)) :
    attachDrive j β s st (h ++ [e]) =
      (attachDrive j β s st h).bind fun r =>
        (s.1 (r.2.2 ++ [e])).map fun y => (r.1 ++ [y], (r.2.1, r.2.2 ++ [e])) := by
  rw [attachDrive_append]
  have hbody :
      (fun ra : List Y × (List (CIn X Y) × List (P × X)) =>
          (attachDrive j β s ra.2 [e]).map fun rb => (ra.1 ++ rb.1, rb.2)) =
        (fun r : List Y × (List (CIn X Y) × List (P × X)) =>
          (s.1 (r.2.2 ++ [e])).map fun y => (r.1 ++ [y], (r.2.1, r.2.2 ++ [e]))) := by
    funext ra
    simp [attachDrive, attachEntryStep, hej, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def]
  rw [hbody]

/-- Raw pass-through for the *applied* resource: a `k`-query (`k ≠ m`) to
`attachAt m δ s`, after a history `hΓ` that `δ`-drives to base history `hbase`,
reads exactly `s` at `hbase ++ [(k, x)]`. -/
theorem attachAt_apply_passthrough (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (e : P × X) (hem : e.1 ≠ m)
    {hΓ hbase : List (P × X)} {cδ : List (CIn X Y)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase))) :
    (attachAt m δ s).1 (hΓ ++ [e]) = s.1 (hbase ++ [e]) := by
  change attachRaw m δ s (hΓ ++ [e]) = s.1 (hbase ++ [e])
  rw [attachRaw, attachDrive_passthrough m δ s e hem ([], []) hΓ, hdrive]
  simp [Part.bind_some, Part.bind_some_right]

/-- A history that successfully `δ`-drives is in the domain of the applied
resource (or empty); needed to evaluate `keptPrefix`. -/
theorem attachAt_dom_or_nil (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y)
    {hΓ hbase : List (P × X)} {cδ : List (CIn X Y)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase))) :
    hΓ ∈ PFunDDS.dom (attachAt m δ s) ∨ hΓ = [] := by
  rcases List.eq_nil_or_concat hΓ with rfl | ⟨hΓ', e, rfl⟩
  · exact Or.inr rfl
  · left
    rw [List.concat_eq_append] at hdrive ⊢
    have hmem : (vsδ, (cδ, hbase)) ∈ attachDrive m δ s ([], []) (hΓ' ++ [e]) := by
      rw [hdrive]; exact Part.mem_some _
    have hlen : vsδ.length = (hΓ' ++ [e]).length :=
      attachDrive_length m δ s ([], []) (hΓ' ++ [e]) hmem
    have hvsne : vsδ ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen
      simp at hlen
    rw [PFunDDS.dom_def, PFun.mem_dom]
    refine ⟨vsδ.getLast hvsne, ?_⟩
    show vsδ.getLast hvsne ∈ attachRaw m δ s (hΓ' ++ [e])
    simp only [attachRaw, Part.mem_bind_iff]
    refine ⟨(vsδ, (cδ, hbase)), hmem, ?_⟩
    rw [List.getLast?_eq_some_getLast hvsne]; exact Part.mem_some _

/-- Transparency at `⊥`: the fully-defined answer to a `k`-query (`k ≠ m`) of the
applied resource equals `s`'s own `⊥`-answer at the base history. Pure function
evaluation via `attachAt_apply_passthrough` and CR18 Definition 3.3. -/
theorem attachAt_fullyDefined_passthrough (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (k : P) (x : X) (hkm : k ≠ m)
    {hΓ hbase : List (P × X)} {cδ : List (CIn X Y)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase)))
    (hbaseDom : hbase ∈ PFunDDS.dom s ∨ hbase = []) :
    PFunDDS.output (PFunDDS.fullyDefined (attachAt m δ s)) (hΓ ++ [(k, x)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      PFunDDS.output (PFunDDS.fullyDefined s) (hbase ++ [(k, x)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) := by
  have hpt : (attachAt m δ s).1 (hΓ ++ [(k, x)]) = s.1 (hbase ++ [(k, x)]) :=
    attachAt_apply_passthrough m δ s (k, x) hkm hdrive
  have hΓdom : hΓ ∈ PFunDDS.dom (attachAt m δ s) ∨ hΓ = [] :=
    attachAt_dom_or_nil m δ s hdrive
  by_cases hmem : hbase ++ [(k, x)] ∈ PFunDDS.dom s
  · have hmemΓ : hΓ ++ [(k, x)] ∈ PFunDDS.dom (attachAt m δ s) := by
      show (((attachAt m δ s).1) (hΓ ++ [(k, x)])).Dom
      rw [hpt]; exact hmem
    rw [PFunDDS.output_fullyDefined_append_of_mem (attachAt m δ s) hΓ (k, x) hΓdom hmemΓ,
        PFunDDS.output_fullyDefined_append_of_mem s hbase (k, x) hbaseDom hmem]
    congr 1
    have hv1 : PFunDDS.output (attachAt m δ s) (hΓ ++ [(k, x)]) hmemΓ ∈
        (attachAt m δ s).1 (hΓ ++ [(k, x)]) := Part.get_mem _
    have hv2 : PFunDDS.output s (hbase ++ [(k, x)]) hmem ∈ s.1 (hbase ++ [(k, x)]) :=
      Part.get_mem _
    rw [hpt] at hv1
    exact Part.mem_unique hv1 hv2
  · have hmemΓ_not : hΓ ++ [(k, x)] ∉ PFunDDS.dom (attachAt m δ s) := by
      show ¬ (((attachAt m δ s).1) (hΓ ++ [(k, x)])).Dom
      rw [hpt]; exact hmem
    have hnoneR : PFunDDS.output (PFunDDS.fullyDefined s) (hbase ++ [(k, x)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      rcases Option.eq_none_or_eq_some
          (PFunDDS.output (PFunDDS.fullyDefined s) (hbase ++ [(k, x)])
            (by rw [PFunDDS.dom_fullyDefined]; simp)) with h | ⟨y, hy⟩
      · exact h
      · obtain ⟨hmem', _⟩ :=
          PFunDDS.mem_of_output_fullyDefined_append_eq_some s hbase (k, x) hbaseDom hy
        exact absurd hmem' hmem
    have hnoneL : PFunDDS.output (PFunDDS.fullyDefined (attachAt m δ s)) (hΓ ++ [(k, x)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      rcases Option.eq_none_or_eq_some
          (PFunDDS.output (PFunDDS.fullyDefined (attachAt m δ s)) (hΓ ++ [(k, x)])
            (by rw [PFunDDS.dom_fullyDefined]; simp)) with h | ⟨y, hy⟩
      · exact h
      · obtain ⟨hmem', _⟩ :=
          PFunDDS.mem_of_output_fullyDefined_append_eq_some (attachAt m δ s) hΓ (k, x) hΓdom hy
        exact absurd hmem' hmemΓ_not
    rw [hnoneL, hnoneR]

omit [DecidableEq P] in
/-- Membership characterization of `attachStep` terminating (`inl`): `α` output an
outside value, leaving the state unchanged. -/
theorem attachStep_mem_inl (k : P) (γ : DDC X Y X Y) (R : PFunDDS.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (b : Y × (List (CIn X Y) × List (P × X))) :
    Sum.inl b ∈ attachStep k γ R st ↔
      Sum.inl (InLabel.outside, b.1) ∈ γ.1 st.1 ∧ b.2 = st := by
  rw [attachStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hb_o⟩
    rcases o with ⟨lbl, y0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;> simp_all
  · rintro ⟨hmemγ, hst⟩
    exact ⟨Sum.inl (InLabel.outside, b.1), hmemγ, by rw [← hst]; cases b; simp⟩

omit [DecidableEq P] in
/-- Membership characterization of `attachStep` continuing (`inr`): `α` issued an
inside query `x0`; the resource history is extended by `(k, x0)` only when `R` is
defined there. -/
theorem attachStep_mem_inr (k : P) (γ : DDC X Y X Y) (R : PFunDDS.Resource P X Y)
    (st st'' : List (CIn X Y) × List (P × X)) :
    Sum.inr st'' ∈ attachStep k γ R st ↔
      ∃ x0, Sum.inr (InLabel.inside, x0) ∈ γ.1 st.1 ∧
        st'' = (st.1 ++ [Sum.inr (InLabel.inside,
                  PFunDDS.output (PFunDDS.fullyDefined R) (st.2 ++ [(k, x0)])
                    (by rw [PFunDDS.dom_fullyDefined]; simp))],
                match PFunDDS.output (PFunDDS.fullyDefined R) (st.2 ++ [(k, x0)])
                    (by rw [PFunDDS.dom_fullyDefined]; simp) with
                | some _ => st.2 ++ [(k, x0)]
                | none => st.2) := by
  rw [attachStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, ho''⟩
    rcases o with ⟨lbl, y0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;>
      simp only [Part.mem_some_iff, Part.notMem_none, reduceCtorEq, Sum.inr.injEq] at ho''
    exact ⟨x0, ho, ho''⟩
  · rintro ⟨x0, hmemγ, rfl⟩
    refine ⟨Sum.inr (InLabel.inside, x0), hmemγ, ?_⟩
    simp only [Part.mem_some_iff]

omit [DecidableEq P] in
/-- CR18 Definition 3.3 (`keptPrefix`): one `m`-round records only `s`-defined
queries, so the base history it produces stays in `dom s` (or is empty). -/
theorem attachResolve_base_dom (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y)
    {st : List (CIn X Y) × List (P × X)}
    (hst : st.2 ∈ PFunDDS.dom s ∨ st.2 = [])
    {r : Y × (List (CIn X Y) × List (P × X))} (hr : r ∈ attachResolve m δ s st) :
    r.2.2 ∈ PFunDDS.dom s ∨ r.2.2 = [] := by
  refine PFun.fixInduction hr
    (C := fun a => (a.2 ∈ PFunDDS.dom s ∨ a.2 = []) →
      r.2.2 ∈ PFunDDS.dom s ∨ r.2.2 = []) ?_ hst
  rintro a' hbfix IH ha'
  rw [PFun.mem_fix_iff] at hbfix
  rcases hbfix with hterm | ⟨a'', hstep, _⟩
  · rw [attachStep_mem_inl] at hterm
    obtain ⟨_, hsteq⟩ := hterm
    rw [hsteq]; exact ha'
  · apply IH a'' hstep
    have hstep' := hstep
    rw [attachStep_mem_inr] at hstep'
    obtain ⟨x0, _, ha''eq⟩ := hstep'
    rw [ha''eq]
    rcases Option.eq_none_or_eq_some
        (PFunDDS.output (PFunDDS.fullyDefined s) (a'.2 ++ [(m, x0)])
          (by rw [PFunDDS.dom_fullyDefined]; simp)) with hnone | ⟨yval, hyval⟩
    · rw [hnone]; exact ha'
    · rw [hyval]
      exact Or.inl
        (PFunDDS.mem_of_output_fullyDefined_append_eq_some s a'.2 (m, x0) ha' hyval).choose

/-- The base history produced by driving a converter `δ` at interface `m`
through a resource `s` stays in `dom s` (or empty); `keptPrefix` again. -/
theorem attachDrive_base_dom (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (H : List (P × X)) :
    ∀ {st : List (CIn X Y) × List (P × X)}, (st.2 ∈ PFunDDS.dom s ∨ st.2 = []) →
      ∀ {r : List Y × (List (CIn X Y) × List (P × X))},
        r ∈ attachDrive m δ s st H → r.2.2 ∈ PFunDDS.dom s ∨ r.2.2 = [] := by
  induction H with
  | nil =>
      intro st hst r hr
      simp only [attachDrive, Part.mem_some_iff] at hr
      subst hr; exact hst
  | cons e rest ih =>
      intro st hst r hr
      simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r', hr', rr, hrr, rfl⟩ := hr
      have hr'dom : r'.2.2 ∈ PFunDDS.dom s ∨ r'.2.2 = [] := by
        rw [attachEntryStep] at hr'
        by_cases hem : e.1 = m
        · rw [if_pos hem] at hr'
          exact attachResolve_base_dom m δ s
            (st := (st.1 ++ [Sum.inl (InLabel.outside, e.2)], st.2)) hst hr'
        · rw [if_neg hem, Part.mem_map_iff] at hr'
          obtain ⟨yy, hyy, rfl⟩ := hr'
          left; rw [PFunDDS.dom_def, PFun.mem_dom]; exact ⟨yy, hyy⟩
      show rr.2.2 ∈ PFunDDS.dom s ∨ rr.2.2 = []
      exact ih hr'dom hrr

/-- The bisimulation relation behind the resolve correspondence: the `γ`-histories
agree, the `attachAt`-side resource history `δ`-drives to the `s`-side base
history, and that base is in `dom s` (or empty). -/
def Rel (m : P) (δ : DDC X Y X Y) (s : PFunDDS.Resource P X Y)
    (cδ : List (CIn X Y)) (a a' : List (CIn X Y) × List (P × X)) : Prop :=
  a.1 = a'.1 ∧
    (∃ vsd, attachDrive m δ s ([], []) a.2 = Part.some (vsd, (cδ, a'.2))) ∧
    (a'.2 ∈ PFunDDS.dom s ∨ a'.2 = [])

/-- The single step of the bisimulation, written once and used in *both*
directions: from `Rel`-related states an inside query `x0` drives both sides to
`Rel`-related successors. The only mathematical content is
`attachAt_fullyDefined_passthrough` (transparency of `δ` at interface `m`). -/
theorem passthrough_step_rel (k : P) (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (hkm : k ≠ m) (cδ : List (CIn X Y))
    {a a' : List (CIn X Y) × List (P × X)} (hRc : a.1 = a'.1) {vsd : List Y}
    (hRd : attachDrive m δ s ([], []) a.2 = Part.some (vsd, (cδ, a'.2)))
    (hRdom : a'.2 ∈ PFunDDS.dom s ∨ a'.2 = []) (x0 : X) :
    Rel m δ s cδ
      (a.1 ++ [Sum.inr (InLabel.inside,
          PFunDDS.output (PFunDDS.fullyDefined (attachAt m δ s)) (a.2 ++ [(k, x0)])
            (by rw [PFunDDS.dom_fullyDefined]; simp))],
        match PFunDDS.output (PFunDDS.fullyDefined (attachAt m δ s)) (a.2 ++ [(k, x0)])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with
          | some _ => a.2 ++ [(k, x0)] | none => a.2)
      (a'.1 ++ [Sum.inr (InLabel.inside,
          PFunDDS.output (PFunDDS.fullyDefined s) (a'.2 ++ [(k, x0)])
            (by rw [PFunDDS.dom_fullyDefined]; simp))],
        match PFunDDS.output (PFunDDS.fullyDefined s) (a'.2 ++ [(k, x0)])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with
          | some _ => a'.2 ++ [(k, x0)] | none => a'.2) := by
  have htrans := attachAt_fullyDefined_passthrough m δ s k x0 hkm hRd hRdom
  refine ⟨by rw [hRc, htrans], ?_, ?_⟩
  · rcases Option.eq_none_or_eq_some
        (PFunDDS.output (PFunDDS.fullyDefined s) (a'.2 ++ [(k, x0)])
          (by rw [PFunDDS.dom_fullyDefined]; simp)) with hnone | ⟨yval, hyval⟩
    · rw [htrans, hnone]; exact ⟨vsd, hRd⟩
    · rw [htrans, hyval]
      have hmemHb : a'.2 ++ [(k, x0)] ∈ PFunDDS.dom s :=
        (PFunDDS.mem_of_output_fullyDefined_append_eq_some s a'.2 (k, x0) hRdom hyval).choose
      have hsval : s.1 (a'.2 ++ [(k, x0)]) =
          Part.some (PFunDDS.output s (a'.2 ++ [(k, x0)]) hmemHb) :=
        Part.eq_some_iff.mpr (Part.get_mem _)
      refine ⟨vsd ++ [PFunDDS.output s (a'.2 ++ [(k, x0)]) hmemHb], ?_⟩
      rw [attachDrive_passthrough m δ s (k, x0) hkm ([], []) a.2, hRd]
      simp only [Part.bind_some, hsval, Part.map_some]
  · rcases Option.eq_none_or_eq_some
        (PFunDDS.output (PFunDDS.fullyDefined s) (a'.2 ++ [(k, x0)])
          (by rw [PFunDDS.dom_fullyDefined]; simp)) with hnone | ⟨yval, hyval⟩
    · rw [hnone]; exact hRdom
    · rw [hyval]
      exact Or.inl
        (PFunDDS.mem_of_output_fullyDefined_append_eq_some s a'.2 (k, x0) hRdom hyval).choose

/-- Forward half of the resolve correspondence: a `k`-round of `γ` against the
applied resource `attachAt m δ s` is mirrored, step for step, by a `k`-round of
`γ` against `s` itself — same outside output and `γ`-history, and the resource
history `δ`-drives to the base history throughout (`k ≠ m`, so `γ`'s queries pass
through `δ`). Now a thin instance of `fix_bisim` with `passthrough_step_rel`. -/
theorem attachResolve_passthrough_fwd
    (k : P) (γ : DDC X Y X Y) (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (hkm : k ≠ m) (cδ : List (CIn X Y))
    {y : Y} {c' : List (CIn X Y)} {hΓ'' : List (P × X)}
    {c : List (CIn X Y)} {hΓ hbase : List (P × X)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase)))
    (hbaseDom : hbase ∈ PFunDDS.dom s ∨ hbase = [])
    (hmem : (y, (c', hΓ'')) ∈ attachResolve k γ (attachAt m δ s) (c, hΓ)) :
    ∃ hbase'' vsδ'', (y, (c', hbase'')) ∈ attachResolve k γ s (c, hbase) ∧
      attachDrive m δ s ([], []) hΓ'' = Part.some (vsδ'', (cδ, hbase'')) := by
  -- Terminated step: `γ` outputs, states unchanged, outputs `Q`-related.
  have hstop : ∀ a a', Rel m δ s cδ a a' → ∀ b,
      Sum.inl b ∈ attachStep k γ (attachAt m δ s) a →
      ∃ b', Sum.inl b' ∈ attachStep k γ s a' ∧
        b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧
        ∃ vsd, attachDrive m δ s ([], []) b.2.2 = Part.some (vsd, (cδ, b'.2.2)) := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, -⟩ b hb
    rw [attachStep_mem_inl] at hb
    obtain ⟨houtγ, hbeq⟩ := hb
    exact ⟨(b.1, a'), by rw [attachStep_mem_inl]; exact ⟨hRc ▸ houtγ, rfl⟩,
      rfl, by rw [hbeq]; exact hRc, vsd0, by rw [hbeq]; exact hRd⟩
  -- Inside step: delegate to the shared `passthrough_step_rel`.
  have hstep : ∀ a a', Rel m δ s cδ a a' → ∀ a₁,
      Sum.inr a₁ ∈ attachStep k γ (attachAt m δ s) a →
      ∃ a₁', Sum.inr a₁' ∈ attachStep k γ s a' ∧ Rel m δ s cδ a₁ a₁' := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, hRdom⟩ a₁ ha₁
    rw [attachStep_mem_inr] at ha₁
    obtain ⟨x0, hqueryγ, rfl⟩ := ha₁
    exact ⟨_, by rw [attachStep_mem_inr]; exact ⟨x0, hRc ▸ hqueryγ, rfl⟩,
      passthrough_step_rel k m δ s hkm cδ hRc hRd hRdom x0⟩
  obtain ⟨⟨by_, bc, bh⟩, hb'mem, hy, hc, vsd'', hd⟩ :=
    PFun.fix_bisim hstop hstep hmem (c, hbase) ⟨rfl, ⟨vsδ, hdrive⟩, hbaseDom⟩
  obtain rfl := hy; obtain rfl := hc
  exact ⟨bh, vsd'', hb'mem, hd⟩

/-- Backward half of the resolve correspondence: every `k`-round of `γ` against
`s` is realized by a `k`-round of `γ` against `attachAt m δ s`, with the resource
history `δ`-driving to the base history. The same `fix_bisim`/`passthrough_step_rel`
as the forward half, run with the relation flipped. -/
theorem attachResolve_passthrough_bwd
    (k : P) (γ : DDC X Y X Y) (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (hkm : k ≠ m) (cδ : List (CIn X Y))
    {y : Y} {c' : List (CIn X Y)} {hbase'' : List (P × X)}
    {c : List (CIn X Y)} {hΓ hbase : List (P × X)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase)))
    (hbaseDom : hbase ∈ PFunDDS.dom s ∨ hbase = [])
    (hmem : (y, (c', hbase'')) ∈ attachResolve k γ s (c, hbase)) :
    ∃ hΓ'' vsδ'', (y, (c', hΓ'')) ∈ attachResolve k γ (attachAt m δ s) (c, hΓ) ∧
      attachDrive m δ s ([], []) hΓ'' = Part.some (vsδ'', (cδ, hbase'')) := by
  have hstop : ∀ a a', Rel m δ s cδ a' a → ∀ b,
      Sum.inl b ∈ attachStep k γ s a →
      ∃ b', Sum.inl b' ∈ attachStep k γ (attachAt m δ s) a' ∧
        b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧
        ∃ vsd, attachDrive m δ s ([], []) b'.2.2 = Part.some (vsd, (cδ, b.2.2)) := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, -⟩ b hb
    rw [attachStep_mem_inl] at hb
    obtain ⟨houtγ, hbeq⟩ := hb
    exact ⟨(b.1, a'), by rw [attachStep_mem_inl]; exact ⟨by rw [hRc]; exact houtγ, rfl⟩,
      rfl, by rw [hbeq]; exact hRc.symm, vsd0, by rw [hbeq]; exact hRd⟩
  have hstep : ∀ a a', Rel m δ s cδ a' a → ∀ a₁,
      Sum.inr a₁ ∈ attachStep k γ s a →
      ∃ a₁', Sum.inr a₁' ∈ attachStep k γ (attachAt m δ s) a' ∧ Rel m δ s cδ a₁' a₁ := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, hRdom⟩ a₁ ha₁
    rw [attachStep_mem_inr] at ha₁
    obtain ⟨x0, hqueryγ, rfl⟩ := ha₁
    exact ⟨_, by rw [attachStep_mem_inr]; exact ⟨x0, by rw [hRc]; exact hqueryγ, rfl⟩,
      passthrough_step_rel k m δ s hkm cδ hRc hRd hRdom x0⟩
  obtain ⟨⟨by_, bc, bh⟩, hb'mem, hy, hc, vsd'', hd⟩ :=
    PFun.fix_bisim hstop hstep hmem (c, hΓ) ⟨rfl, ⟨vsδ, hdrive⟩, hbaseDom⟩
  obtain rfl := hy; obtain rfl := hc
  exact ⟨bh, vsd'', hb'mem, hd⟩

/-- One outer step of the commutativity induction, for an entry `e` at the
*resolving* interface `k` (`k ≠ m`): the side that runs `γ` at `k` (against
`attachAt m δ s`) and the side that passes `e` through `δ` to `attachAt k γ s`'s
own `k`-round agree on the head output and reduce, via the symmetric induction
hypothesis `sih`, to the tails. This is the single argument behind *both* the
`i` and `j` branches of `attachAt_comm` — the latter feeds `(ih …).symm`. -/
theorem cons_step_eq (k : P) (γ : DDC X Y X Y) (m : P) (δ : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (hkm : k ≠ m)
    (rest : List (P × X)) (e : P × X) (hek : e.1 = k)
    (cγ cδ : List (CIn X Y)) (hΓ hΔ hs : List (P × X)) (vsγ vsδ : List Y)
    (hΓeq : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hs)))
    (hΔeq : attachDrive k γ s ([], []) hΔ = Part.some (vsγ, (cγ, hs)))
    (sih : ∀ (cγ' cδ' : List (CIn X Y)) (hΓ' hΔ' : List (P × X)),
        (∃ hs' vsδ' vsγ',
            attachDrive m δ s ([], []) hΓ' = Part.some (vsδ', (cδ', hs')) ∧
            attachDrive k γ s ([], []) hΔ' = Part.some (vsγ', (cγ', hs'))) →
        Part.map Prod.fst (attachDrive k γ (attachAt m δ s) (cγ', hΓ') rest) =
          Part.map Prod.fst (attachDrive m δ (attachAt k γ s) (cδ', hΔ') rest)) :
    Part.map Prod.fst (attachDrive k γ (attachAt m δ s) (cγ, hΓ) (e :: rest)) =
      Part.map Prod.fst (attachDrive m δ (attachAt k γ s) (cδ, hΔ) (e :: rest)) := by
  have hem : ¬ e.1 = m := by rw [hek]; exact hkm
  simp only [attachDrive, attachEntryStep]
  rw [if_pos hek, if_neg hem]
  have hΔres : (attachAt k γ s).1 (hΔ ++ [e]) =
      (attachResolve k γ s (cγ ++ [Sum.inl (InLabel.outside, e.2)], hs)).map Prod.fst := by
    change attachRaw k γ s (hΔ ++ [e]) = _
    rw [attachRaw, attachDrive_append k γ s ([], []) hΔ [e], hΔeq]
    simp [attachDrive, attachEntryStep, hek, Part.bind_some, Part.map_map,
      Function.comp_def, Part.bind_some_eq_map]
  rw [hΔres]
  have hsDom : hs ∈ PFunDDS.dom s ∨ hs = [] :=
    attachDrive_base_dom m δ s hΓ (Or.inr rfl) (by rw [hΓeq]; exact Part.mem_some _)
  have hΔe : attachDrive k γ s ([], []) (hΔ ++ [e]) =
      (attachResolve k γ s (cγ ++ [Sum.inl (InLabel.outside, e.2)], hs)).map
        (fun q => (vsγ ++ [q.1], q.2)) := by
    rw [attachDrive_append k γ s ([], []) hΔ [e], hΔeq, Part.bind_some]
    simp only [attachDrive, attachEntryStep, if_pos hek,
      Part.bind_some_eq_map, Part.map_map, Function.comp_def, Part.map_some]
  have htail : ∀ (qy : Y) (qc : List (CIn X Y)) (hΓ'' qh : List (P × X)) (vv : List Y),
      attachDrive m δ s ([], []) hΓ'' = Part.some (vv, (cδ, qh)) →
      (qy, (qc, qh)) ∈ attachResolve k γ s (cγ ++ [Sum.inl (InLabel.outside, e.2)], hs) →
      Part.map Prod.fst (attachDrive k γ (attachAt m δ s) (qc, hΓ'') rest) =
        Part.map Prod.fst (attachDrive m δ (attachAt k γ s) (cδ, hΔ ++ [e]) rest) := by
    intro qy qc hΓ'' qh vv hmdrive hq
    refine sih qc cδ hΓ'' (hΔ ++ [e]) ⟨qh, vv, vsγ ++ [qy], hmdrive, ?_⟩
    rw [hΔe, Part.eq_some_iff.mpr hq, Part.map_some]
  simp only [Part.map_bind, Part.bind_map, Part.map_map, Function.comp_def]
  apply Part.ext
  intro z
  simp only [Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨⟨ry, rc, rh⟩, hr, w, hw, rfl⟩
    obtain ⟨hbase'', vsδ'', hq, hmdrive⟩ :=
      attachResolve_passthrough_fwd k γ m δ s hkm cδ hΓeq hsDom hr
    have htl := htail ry rc rh hbase'' vsδ'' hmdrive hq
    have hw' : w.1 ∈ Part.map Prod.fst
        (attachDrive m δ (attachAt k γ s) (cδ, hΔ ++ [e]) rest) := by
      rw [← htl]; exact Part.mem_map _ hw
    rw [Part.mem_map_iff] at hw'
    obtain ⟨w2, hw2, hw2eq⟩ := hw'
    exact ⟨(ry, (rc, hbase'')), hq, w2, hw2, by rw [hw2eq]⟩
  · rintro ⟨⟨qy, qc, qh⟩, hq, w, hw, rfl⟩
    obtain ⟨hΓ'', vsδ'', hr, hmdrive⟩ :=
      attachResolve_passthrough_bwd k γ m δ s hkm cδ hΓeq hsDom hq
    have htl := htail qy qc hΓ'' qh vsδ'' hmdrive hq
    have hw' : w.1 ∈ Part.map Prod.fst
        (attachDrive k γ (attachAt m δ s) (qc, hΓ'') rest) := by
      rw [htl]; exact Part.mem_map _ hw
    rw [Part.mem_map_iff] at hw'
    obtain ⟨w2, hw2, hw2eq⟩ := hw'
    exact ⟨(qy, (qc, hΓ'')), hr, w2, hw2, by rw [hw2eq]⟩

/-- CR18 Lemma 3.1 (general stateful converters): attaching at distinct
interfaces commutes — operator commutativity `αⁱ ∘ βʲ = βʲ ∘ αⁱ`. -/
theorem attachAt_comm (i : P) (α : DDC X Y X Y) (j : P) (β : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (hij : i ≠ j) :
    attachAt i α (attachAt j β s) = attachAt j β (attachAt i α s) := by
  apply Subtype.ext
  funext l
  show attachRaw i α (attachAt j β s) l = attachRaw j β (attachAt i α s) l
  -- The output lists of the two drives agree, under the cross-tied invariant
  -- relating the two nestings through the shared base-`s` history.
  have key : ∀ (l : List (P × X)) (cα cβ : List (CIn X Y)) (hT hU : List (P × X)),
      (∃ (hs : List (P × X)) (vsβ vsα : List Y),
          attachDrive j β s ([], []) hT = Part.some (vsβ, (cβ, hs)) ∧
          attachDrive i α s ([], []) hU = Part.some (vsα, (cα, hs))) →
      (attachDrive i α (attachAt j β s) (cα, hT) l).map Prod.fst =
        (attachDrive j β (attachAt i α s) (cβ, hU) l).map Prod.fst := by
    intro l
    induction l with
    | nil => intro cα cβ hT hU _; simp [attachDrive]
    | cons e rest ih =>
        intro cα cβ hT hU hInv
        obtain ⟨hs, vsβ, vsα, hTeq, hUeq⟩ := hInv
        by_cases hei : e.1 = i
        · -- e at the resolving interface i: one `cons_step_eq`, ih directly.
          exact cons_step_eq i α j β s hij rest e hei cα cβ hT hU hs vsα vsβ hTeq hUeq ih
        · by_cases hej : e.1 = j
          · -- e at the resolving interface j: same lemma with (i,α)↔(j,β), fed
            -- the transposed induction hypothesis `(ih …).symm`.
            refine (cons_step_eq j β i α s hij.symm rest e hej cβ cα hU hT hs vsβ vsα
                hUeq hTeq (fun cγ' cδ' hΓ' hΔ' h => ?_)).symm
            obtain ⟨hs', v1, v2, h1, h2⟩ := h
            exact (ih cδ' cγ' hΔ' hΓ' ⟨hs', v2, v1, h2, h1⟩).symm
          · -- else: e is at an interface other than i and j; both sides pass it
            -- straight through to the shared base `s` (one lemma, used twice).
            simp only [attachDrive, attachEntryStep]
            rw [if_neg hei, if_neg hej,
              attachAt_apply_passthrough j β s e hej hTeq,
              attachAt_apply_passthrough i α s e hei hUeq]
            rcases Part.eq_none_or_eq_some (s.1 (hs ++ [e])) with h0 | ⟨y0, h0⟩
            · rw [h0]; simp
            · rw [h0]
              simp only [Part.map_some, Part.bind_some, Part.map_map, Function.comp_def]
              have hInv' : ∃ (hs' : List (P × X)) (vsβ' vsα' : List Y),
                  attachDrive j β s ([], []) (hT ++ [e]) = Part.some (vsβ', (cβ, hs')) ∧
                  attachDrive i α s ([], []) (hU ++ [e]) = Part.some (vsα', (cα, hs')) := by
                refine ⟨hs ++ [e], vsβ ++ [y0], vsα ++ [y0], ?_, ?_⟩
                · rw [attachDrive_passthrough j β s e hej ([], []) hT, hTeq]
                  simp [Part.bind_some, h0]
                · rw [attachDrive_passthrough i α s e hei ([], []) hU, hUeq]
                  simp [Part.bind_some, h0]
              have hih := ih cα cβ (hT ++ [e]) (hU ++ [e]) hInv'
              rw [show (fun rr : List Y × (List (CIn X Y) × List (P × X)) => y0 :: rr.1) =
                  (fun z : List Y => y0 :: z) ∘ Prod.fst from rfl]
              rw [← Part.map_map, ← Part.map_map, hih]
  have hk := key l [] [] [] [] ⟨[], [], [], rfl, rfl⟩
  have hconv : ∀ d : Part (List Y × (List (CIn X Y) × List (P × X))),
      (d.bind fun r => match r.1.getLast? with
        | some y => Part.some y | none => Part.none) =
      (Part.map Prod.fst d).bind fun vs => match vs.getLast? with
        | some y => Part.some y | none => Part.none := by
    intro d; rw [Part.bind_map]
  simp only [attachRaw]
  rw [hconv, hconv, hk]

end General

end PFunConverter

end RandomSystems.CR18
