/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedTensor

/-!
# Attachment is local in the interface set: the pull-back calculus

A converter attached at one interface never reads, writes, or even names any
other interface.  `PFunConverter.General.attachAt` dispatches on the interface
tag of each outside entry (`attachEntryStep`), and routes its own inner queries
to its own interface and nowhere else.  So *re-addressing the interface set*
commutes with attachment, provided the re-addressing carries the converter's
own interface identically and carries no other query onto it.

The re-addressing is described here as a **pull-back**.  A resource `far` with
interface set `Q` is the pull-back of a resource `near` with interface set `P`
along a translation `route : Q × X → P × X` of interface-tagged queries when

```
far (history ++ [entry]) = (near (history.map route ++ [route entry])).map (recode entry)
```

— every `Q`-history is answered by re-addressing it into a `P`-history and
recoding the answer, and the recoding depends only on the active query.  This
is exactly the relationship between a re-indexed dependent resource and the
resource it came from once both are read in the boundary-independent ambient
chart, and it is *not* a relabelling: `route` need not be injective and `recode`
need not be, so the re-addressing may merge several interfaces into one — which
is what `DependentDDS.mergeTwo` does, and the ambient alphabets of two
boundaries with different interface sets need not even be equinumerous.

The results:

* `IsPullback.attachAt` — attachment respects the pull-back, in the uniform
  chart, provided the translation carries the converter's interface identically
  and sends nothing else onto it;
* `IsPullback.unique` — a pull-back is determined by what it pulls back, which
  is what turns two pull-back facts into an equality of resources;
* `DependentDDS.isPullback_embed_reindex` — every re-indexing of a dependent
  resource is a pull-back, given an ambient translation for it;
* `DependentDDS.isPullback_embed_reindex_of_rename` and
  `DependentDDS.isPullback_embed_mergeTwo` — the two instances: renaming the
  interface set, and merging two interfaces into one.

Together they say: **re-indexing the interfaces a converter does not touch is
invisible to the converter.**
-/

namespace RandomSystems.CR18

open PFunDDS
open scoped Classical

noncomputable section

namespace PFunConverter.General

open DDC

universe up uq ux uy

/-! ## Conjugating a least fixed point -/

/-- **A simulation carries a least fixed point.**  If a state translation `σ`
and a result translation `μ` turn every step of `far` into the corresponding
step of `near` — `near (σ a) = (far a).map (Sum.map μ σ)` — then they turn the
whole least fixed point into the corresponding one.  Neither translation need
be injective: the simulation is exact in both directions because the step
equation is an equation, not an inclusion. -/
theorem fix_simulation {A B A' B' : Type*} {near : A →. B ⊕ A} {far : A' →. B' ⊕ A'}
    (σ : A' → A) (μ : B' → B)
    (step : ∀ state, near (σ state) = (far state).map (Sum.map μ σ))
    (state : A') :
    near.fix (σ state) = (far.fix state).map μ := by
  apply Part.ext
  intro result
  constructor
  · intro member
    refine PFun.fixInduction
      (C := fun current => ∀ source : A', σ source = current →
        result ∈ (far.fix source).map μ) member ?_ state rfl
    rintro current reached recurse source rfl
    rcases PFun.mem_fix_iff.mp reached with stopped | ⟨next, stepped, continued⟩
    · rw [step, Part.mem_map_iff] at stopped
      obtain ⟨move, moveMember, moveEq⟩ := stopped
      cases move with
      | inl value =>
          exact (Part.mem_map_iff _).mpr ⟨value, PFun.fix_stop moveMember,
            Sum.inl.inj moveEq⟩
      | inr other => exact absurd moveEq (by simp)
    · have stepped' := stepped
      rw [step, Part.mem_map_iff] at stepped'
      obtain ⟨move, moveMember, moveEq⟩ := stepped'
      cases move with
      | inl value => exact absurd moveEq (by simp)
      | inr other =>
          have sameState : σ other = next := Sum.inr.inj moveEq
          rw [PFun.fix_fwd_eq moveMember]
          exact recurse next stepped other sameState
  · intro member
    obtain ⟨value, valueMember, rfl⟩ := (Part.mem_map_iff _).mp member
    refine PFun.fixInduction (C := fun current => μ value ∈ near.fix (σ current))
      valueMember ?_
    intro current reached recurse
    rcases PFun.mem_fix_iff.mp reached with stopped | ⟨next, stepped, continued⟩
    · refine PFun.fix_stop ?_
      rw [step]
      exact (Part.mem_map_iff _).mpr ⟨Sum.inl value, stopped, rfl⟩
    · have advance : Sum.inr (σ next) ∈ near (σ current) := by
        rw [step]
        exact (Part.mem_map_iff _).mpr ⟨Sum.inr next, stepped, rfl⟩
      rw [PFun.fix_fwd_eq advance]
      exact recurse next stepped

/-! ## The pull-back of a resource along an interface translation -/

section Pullback

variable {P : Type up} {Q : Type uq} {X : Type ux} {Y : Type uy}
variable [DecidableEq P] [DecidableEq Q]

/-- The driver state translated along an interface translation: the converter's
own history is untouched, the recorded resource history is re-addressed. -/
def pullState (route : Q × X → P × X) :
    List (CIn X Y) × List (Q × X) → List (CIn X Y) × List (P × X) :=
  fun state => (state.1, state.2.map route)

variable {route : Q × X → P × X} {recode : Q × X → Y → Y}
variable {near : PFunDDS.Resource P X Y} {far : PFunDDS.Resource Q X Y}

/-- **The pull-back hypothesis.**  `far` answers a `Q`-history by re-addressing
it along `route` and recoding `near`'s answer; the recoding is a function of the
active query alone. -/
def IsPullback (route : Q × X → P × X) (recode : Q × X → Y → Y)
    (near : PFunDDS.Resource P X Y) (far : PFunDDS.Resource Q X Y) : Prop :=
  ∀ (history : List (Q × X)) (entry : Q × X),
    far.1 (history ++ [entry]) =
      (near.1 (history.map route ++ [route entry])).map (recode entry)

omit [DecidableEq P] [DecidableEq Q] in
theorem IsPullback.mem_dom_iff (pull : IsPullback route recode near far)
    (history : List (Q × X)) :
    history ∈ PFunDDS.dom far ↔ history.map route ∈ PFunDDS.dom near := by
  rcases List.eq_nil_or_concat history with rfl | ⟨front, entry, rfl⟩
  · simp only [List.map_nil]
    constructor
    · intro member; exact absurd member (PFunDDS.empty_not_mem far)
    · intro member; exact absurd member (PFunDDS.empty_not_mem near)
  · rw [List.concat_eq_append]
    have translated : (front ++ [entry]).map route = front.map route ++ [route entry] := by
      simp
    rw [translated]
    show (far.1 (front ++ [entry])).Dom ↔ (near.1 (front.map route ++ [route entry])).Dom
    rw [pull front entry]
    rfl

omit [DecidableEq P] [DecidableEq Q] in
/-- Pull-backs compose: re-addressing twice is re-addressing once, along the
composed translation, with the two recodings applied in order. -/
theorem IsPullback.trans {R : Type*}
    {routeOuter : R × X → Q × X} {recodeOuter : R × X → Y → Y}
    {beyond : PFunDDS.Resource R X Y}
    (inner : IsPullback route recode near far)
    (outer : IsPullback routeOuter recodeOuter far beyond) :
    IsPullback (route ∘ routeOuter)
      (fun entry => recodeOuter entry ∘ recode (routeOuter entry)) near beyond := by
  intro history entry
  rw [outer history entry, inner (history.map routeOuter) (routeOuter entry),
    Part.map_map, List.map_map]
  rfl

omit [DecidableEq P] [DecidableEq Q] in
/-- **A pull-back is determined by what it pulls back.**  The translation and
the recoding fix every answer of the re-addressed resource on every nonempty
history, and no deterministic system answers the empty one.  This is what turns
the two pull-back facts below into an equality of resources rather than a pair
of inclusions. -/
theorem IsPullback.unique {other : PFunDDS.Resource Q X Y}
    (pull : IsPullback route recode near far)
    (pull' : IsPullback route recode near other) : far = other := by
  apply Subtype.ext
  funext history
  rcases List.eq_nil_or_concat history with rfl | ⟨front, entry, rfl⟩
  · rw [Part.eq_none_iff'.mpr (PFunDDS.empty_not_mem far),
      Part.eq_none_iff'.mpr (PFunDDS.empty_not_mem other)]
  · rw [List.concat_eq_append, pull front entry, pull' front entry]

omit [DecidableEq P] [DecidableEq Q] in
/-- The deletion scan of CR18 Definition 3.3 commutes with the translation:
which next queries survive is decided by the domains, and the domains
correspond. -/
theorem IsPullback.keptPrefix (pull : IsPullback route recode near far)
    (history : List (Q × X)) :
    PFunDDS.keptPrefix near (history.map route) =
      (PFunDDS.keptPrefix far history).map route := by
  suffices general : ∀ (rest accumulator : List (Q × X)),
      List.foldl
          (fun acc next => if acc ++ [next] ∈ PFunDDS.dom near then acc ++ [next] else acc)
          (accumulator.map route) (rest.map route) =
        (List.foldl
          (fun acc next => if acc ++ [next] ∈ PFunDDS.dom far then acc ++ [next] else acc)
          accumulator rest).map route by
    simpa [PFunDDS.keptPrefix] using general history []
  intro rest
  induction rest with
  | nil => intro accumulator; rfl
  | cons next rest recurse =>
      intro accumulator
      simp only [List.map_cons, List.foldl_cons]
      have domains : accumulator.map route ++ [route next] ∈ PFunDDS.dom near ↔
          accumulator ++ [next] ∈ PFunDDS.dom far := by
        rw [pull.mem_dom_iff]
        simp
      by_cases member : accumulator ++ [next] ∈ PFunDDS.dom far
      · rw [if_pos (domains.mpr member), if_pos member,
          show accumulator.map route ++ [route next] = (accumulator ++ [next]).map route by simp]
        exact recurse (accumulator ++ [next])
      · rw [if_neg fun contra => member (domains.mp contra), if_neg member]
        exact recurse accumulator


omit [DecidableEq P] [DecidableEq Q] in
/-- The pull-back seen at one interface that the translation carries
identically: the completed answers agree on the nose. -/
theorem IsPullback.output_fullyDefined {inner : P} {outer : Q}
    (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (history : List (Q × X)) (value : X) :
    PFunDDS.output (PFunDDS.fullyDefined far) (history ++ [(outer, value)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      PFunDDS.output (PFunDDS.fullyDefined near) (history.map route ++ [(inner, value)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) := by
  classical
  have translated : (history ++ [(outer, value)]).map route =
      history.map route ++ [(inner, value)] := by
    simp [carry]
  have answers : far.1 (PFunDDS.keptPrefix far history ++ [(outer, value)]) =
      near.1 ((PFunDDS.keptPrefix far history).map route ++ [(inner, value)]) := by
    rw [pull (PFunDDS.keptPrefix far history) (outer, value), carry, transparent]
    exact Part.map_id' (fun _ => rfl) _
  have candidates : (PFunDDS.keptPrefix far history).map route ++ [(inner, value)] =
      (PFunDDS.keptPrefix far history ++ [(outer, value)]).map route := by
    simp [carry]
  have dropFar : (history ++ [(outer, value)]).dropLast = history := by simp
  have dropNear : (history.map route ++ [(inner, value)]).dropLast = history.map route := by
    simp
  have lastFar : (history ++ [(outer, value)]).getLast (by simp) = (outer, value) := by simp
  have lastNear : (history.map route ++ [(inner, value)]).getLast (by simp) =
      (inner, value) := by simp
  rw [PFunDDS.output_fullyDefined, PFunDDS.output_fullyDefined]
  rw [dropFar, dropNear, lastFar, lastNear, pull.keptPrefix history]
  by_cases member : PFunDDS.keptPrefix far history ++ [(outer, value)] ∈ PFunDDS.dom far
  · have memberNear : (PFunDDS.keptPrefix far history).map route ++ [(inner, value)] ∈
        PFunDDS.dom near := by
      rw [candidates]
      exact (pull.mem_dom_iff _).mp member
    rw [dif_pos member, dif_pos memberNear]
    refine congrArg some ?_
    show (far.1 _).get member = (near.1 _).get memberNear
    congr 1
  · have memberNear : ¬ ((PFunDDS.keptPrefix far history).map route ++ [(inner, value)] ∈
        PFunDDS.dom near) := by
      rw [candidates]
      exact fun contra => member ((pull.mem_dom_iff _).mpr contra)
    rw [dif_neg member, dif_neg memberNear]

/-! ### Attachment respects the pull-back -/

variable {inner : P} {outer : Q} (α : DDC X Y X Y)

omit [DecidableEq P] [DecidableEq Q] in
/-- One connection step of the converter, translated.  The converter's own
history is common to the two runs; the recorded resource history is
re-addressed; and the answer the converter is fed is literally the same on both
sides, because the translation carries the attachment interface identically. -/
theorem IsPullback.attachStep (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (state : List (CIn X Y) × List (Q × X)) :
    attachStep inner α near (pullState route state) =
      (attachStep outer α far state).map
        (Sum.map (Prod.map id (pullState route)) (pullState route)) := by
  show (α.1 state.1).bind _ = ((α.1 state.1).bind _).map _
  rw [Part.map_bind]
  congr 1
  funext move
  match move with
  | Sum.inl (InLabel.outside, _) => simp [pullState]
  | Sum.inl (InLabel.inside, _) => simp
  | Sum.inr (InLabel.outside, _) => simp
  | Sum.inr (InLabel.inside, query) =>
      have answers :
          PFunDDS.output (PFunDDS.fullyDefined near)
              ((pullState route state).2 ++ [(inner, query)])
              (by rw [PFunDDS.dom_fullyDefined]; simp) =
            PFunDDS.output (PFunDDS.fullyDefined far) (state.2 ++ [(outer, query)])
              (by rw [PFunDDS.dom_fullyDefined]; simp) :=
        (pull.output_fullyDefined carry transparent
          state.2 query).symm
      show Part.some _ = (Part.some _).map _
      rw [Part.map_some]
      refine congrArg Part.some ?_
      show Sum.inr _ = Sum.inr _
      refine congrArg Sum.inr ?_
      rw [answers]
      show (_, _) = pullState route (_, _)
      cases outcome : PFunDDS.output (PFunDDS.fullyDefined far)
          (state.2 ++ [(outer, query)]) (by rw [PFunDDS.dom_fullyDefined]; simp) with
      | none => simp [pullState]
      | some _ => simp [pullState, carry]

omit [DecidableEq P] [DecidableEq Q] in
/-- One resolving round of the converter, translated: the least fixed point of
the connection step is carried by the same translation
(`fix_simulation`). -/
theorem IsPullback.attachResolve (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (state : List (CIn X Y) × List (Q × X)) :
    attachResolve inner α near (pullState route state) =
      (attachResolve outer α far state).map (Prod.map id (pullState route)) :=
  fix_simulation (pullState route) (Prod.map id (pullState route))
    (pull.attachStep α carry transparent) state

/-- Processing one outside entry, translated — the driver-state half. -/
theorem IsPullback.attachEntryStep_snd (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (reflect : ∀ entry : Q × X, entry.1 ≠ outer → (route entry).1 ≠ inner)
    (state : List (CIn X Y) × List (Q × X)) (entry : Q × X) :
    (attachEntryStep inner α near (pullState route state) (route entry)).map Prod.snd =
      (attachEntryStep outer α far state entry).map fun r => pullState route r.2 := by
  obtain ⟨tag, value⟩ := entry
  by_cases selected : tag = outer
  · subst selected
    rw [carry value]
    simp only [attachEntryStep]
    rw [show ((pullState route state).1 ++ [Sum.inl (InLabel.outside, value)],
        (pullState route state).2) =
      pullState route (state.1 ++ [Sum.inl (InLabel.outside, value)], state.2) from rfl,
      pull.attachResolve α carry transparent]
    simp [Part.map_map, Function.comp_def]
  · simp only [attachEntryStep]
    rw [if_neg selected, if_neg (reflect (tag, value) selected), pull state.2 (tag, value)]
    simp [Part.map_map, Function.comp_def, pullState]

/-- Processing one outside entry, translated — the answer half.  This is where
the recoding appears: an entry at any interface other than the converter's is
answered by the resource itself, and the resource's two answers differ by the
recoding. -/
theorem IsPullback.attachEntryStep_fst (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (reflect : ∀ entry : Q × X, entry.1 ≠ outer → (route entry).1 ≠ inner)
    (state : List (CIn X Y) × List (Q × X)) (entry : Q × X) :
    (attachEntryStep outer α far state entry).map Prod.fst =
      ((attachEntryStep inner α near (pullState route state) (route entry)).map
        Prod.fst).map (recode entry) := by
  obtain ⟨tag, value⟩ := entry
  by_cases selected : tag = outer
  · subst selected
    rw [carry value]
    simp only [attachEntryStep]
    rw [show ((pullState route state).1 ++ [Sum.inl (InLabel.outside, value)],
        (pullState route state).2) =
      pullState route (state.1 ++ [Sum.inl (InLabel.outside, value)], state.2) from rfl,
      pull.attachResolve α carry transparent, transparent value]
    simp [Part.map_map, Function.comp_def]
  · simp only [attachEntryStep]
    rw [if_neg selected, if_neg (reflect (tag, value) selected), pull state.2 (tag, value)]
    simp [Part.map_map, Function.comp_def, pullState]

/-- The whole outer iteration, translated — driver-state half.  The answers are
dropped here on purpose: only the last one is ever read back, and it is
recovered by `attachEntryStep_fst` at the very end. -/
theorem IsPullback.attachDrive_snd (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (reflect : ∀ entry : Q × X, entry.1 ≠ outer → (route entry).1 ≠ inner)
    (history : List (Q × X)) (state : List (CIn X Y) × List (Q × X)) :
    (attachDrive inner α near (pullState route state) (history.map route)).map Prod.snd =
      (attachDrive outer α far state history).map fun r => pullState route r.2 := by
  induction history generalizing state with
  | nil => simp [attachDrive]
  | cons entry rest recurse =>
      simp only [List.map_cons, attachDrive, Part.map_bind, Part.map_map,
        Function.comp_def]
      rw [← Part.bind_map (f := Prod.snd)
          (g := fun st => (attachDrive inner α near st (rest.map route)).map Prod.snd),
        pull.attachEntryStep_snd α carry transparent reflect
          state entry,
        Part.bind_map]
      refine congrArg _ ?_
      funext result
      exact recurse result.2

/-- **Attachment respects the pull-back.**  If `far` is `near` re-addressed
along a translation that carries the converter's interface identically
(`carry`), recodes nothing there (`transparent`) and sends no other query onto
it (`reflect`), then attaching the converter at the corresponding interfaces
again gives a resource and its re-addressed copy — same translation, same
recoding.

This is the exact sense in which a converter is blind to the addressing of the
interfaces it does not touch: the re-addressing may even merge several of them
into one. -/
theorem IsPullback.attachAt (pull : IsPullback route recode near far)
    (carry : ∀ value : X, route (outer, value) = (inner, value))
    (transparent : ∀ value : X, recode (outer, value) = id)
    (reflect : ∀ entry : Q × X, entry.1 ≠ outer → (route entry).1 ≠ inner) :
    IsPullback route recode (General.attachAt inner α near)
      (General.attachAt outer α far) := by
  intro history entry
  show attachRaw outer α far (history ++ [entry]) =
    (attachRaw inner α near (history.map route ++ [route entry])).map (recode entry)
  rw [attachRaw_append_singleton, attachRaw_append_singleton, Part.map_bind,
    ← Part.bind_map Prod.snd _
      (fun base => ((attachEntryStep inner α near base (route entry)).map
        Prod.fst).map (recode entry)),
    show (([], []) : List (CIn X Y) × List (P × X)) = pullState route ([], []) from rfl,
    pull.attachDrive_snd α carry transparent reflect history ([], []),
    Part.bind_map]
  refine congrArg _ ?_
  funext result
  exact pull.attachEntryStep_fst α carry transparent reflect
    result.2 entry

end Pullback

end PFunConverter.General

/-! ## Re-indexing a dependent resource is a pull-back -/

namespace TypedResource

open PFunConverter.General

/-- Two pushforwards of one partial value agree as soon as the two maps agree
on the values that partial value can take. -/
theorem _root_.Part.map_congr_of_mem {A B : Type*} {value : Part A} {left right : A → B}
    (agree : ∀ element ∈ value, left element = right element) :
    value.map left = value.map right := by
  apply Part.ext
  intro image
  simp only [Part.mem_map_iff]
  constructor
  · rintro ⟨element, member, rfl⟩
    exact ⟨element, member, (agree element member).symm⟩
  · rintro ⟨element, member, rfl⟩
    exact ⟨element, member, agree element member⟩

variable {K K' : Type*} {U : SignatureUniverse}
variable {boundary : Boundary U K} {boundary' : Boundary U K'}

/-- **A re-indexed dependent resource is the pull-back of the original.**  Read
in the boundary-independent ambient chart, re-indexing is exactly a
re-addressing of interface-tagged queries together with a recoding of answers:

* `routeEncode` says the ambient translation *is* the re-indexing, on the
  conforming queries — the only ones either resource ever answers;
* `routeReflect` says it takes ill-coded queries to ill-coded queries, which is
  what makes the pull-back hold off the conforming histories, where both sides
  are undefined;
* `recodeEncode` says the ambient answer translation is the re-indexing's own
  answer equivalence, on the answers tag-faithfulness allows.

Neither translation is a bijection in general: the ambient alphabets of two
boundaries with different interface sets need not even be equinumerous, which is
exactly why re-indexing is a pull-back and not a relabelling. -/
theorem DependentDDS.isPullback_embed_reindex
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE)
    (route : AmbientQuery K' U → AmbientQuery K U)
    (recode : AmbientQuery K' U → AmbientOutput U → AmbientOutput U)
    (routeEncode : ∀ query : Query U boundary,
      route (encodeQuery (queryE query)) = encodeQuery query)
    (routeReflect : ∀ query : AmbientQuery K' U,
      QueryConforms boundary (route query) → QueryConforms boundary' query)
    (recodeEncode : ∀ (query : Query U boundary) (answer : FlatAnswer U boundary),
      answer.1 = query.1 →
        recode (encodeQuery (queryE query)) (encodeAnswer answer) =
          encodeAnswer (answerE answer))
    (system : DependentDDS U boundary) :
    IsPullback route recode system.embed (system.reindex compatible).embed := by
  replace routeEncode : ∀ query : Query U boundary',
      route (encodeQuery query) = encodeQuery (queryE.symm query) := by
    intro query
    have step := routeEncode (queryE.symm query)
    rwa [Equiv.apply_symm_apply] at step
  replace recodeEncode : ∀ (query : Query U boundary') (answer : FlatAnswer U boundary),
      answer.1 = (queryE.symm query).1 →
        recode (encodeQuery query) (encodeAnswer answer) = encodeAnswer (answerE answer) := by
    intro query answer tag
    have step := recodeEncode (queryE.symm query) answer tag
    rwa [Equiv.apply_symm_apply] at step
  intro history entry
  have translated : (history ++ [entry]).map route = history.map route ++ [route entry] := by
    simp
  rw [← translated]
  by_cases conforms : HistoryConforms boundary' (history ++ [entry])
  · set decoded := decodeHistory boundary' (history ++ [entry]) conforms with decodedDef
    have encoded : decoded.map encodeQuery = history ++ [entry] :=
      encode_history_decode boundary' (history ++ [entry]) conforms
    have decodedNonempty : decoded ≠ [] := by
      intro empty
      rw [empty] at encoded
      exact absurd encoded.symm (by simp)
    have lastEntry : entry = encodeQuery (decoded.getLast decodedNonempty) := by
      have right : (decoded.map encodeQuery).getLast? =
          some (encodeQuery (decoded.getLast decodedNonempty)) := by
        rw [List.getLast?_map, List.getLast?_eq_some_getLast decodedNonempty]
        rfl
      rw [encoded, show (history ++ [entry]).getLast? = some entry by simp] at right
      exact Option.some.inj right
    have pulled : (decoded.map ⇑queryE.symm).map encodeQuery =
        (history ++ [entry]).map route := by
      rw [← encoded, List.map_map, List.map_map]
      exact List.map_congr_left fun query _ => (routeEncode query).symm
    calc (system.reindex compatible).embed.1 (history ++ [entry])
        = (system.reindex compatible).embed.1 (decoded.map encodeQuery) := by rw [encoded]
      _ = ((system.reindex compatible).flatten.1 decoded).map encodeAnswer :=
            DependentDDS.embed_apply_encoded _ decoded
      _ = ((system.flatten.1 (decoded.map ⇑queryE.symm)).map ⇑answerE).map encodeAnswer := by
            rw [DependentDDS.flatten_reindex]
            rfl
      _ = (system.flatten.1 (decoded.map ⇑queryE.symm)).map
            fun answer => encodeAnswer (answerE answer) := by
            rw [Part.map_map]
            rfl
      _ = (system.flatten.1 (decoded.map ⇑queryE.symm)).map
            fun answer => recode entry (encodeAnswer answer) := by
            refine Part.map_congr_of_mem fun answer member => ?_
            have memberDom : decoded.map ⇑queryE.symm ∈ PFunDDS.dom system.flatten :=
              Part.dom_iff_mem.mpr ⟨answer, member⟩
            have tagged := system.flatten_tag_faithful (decoded.map ⇑queryE.symm) memberDom
            have valueEq : answer = PFunDDS.output system.flatten _ memberDom :=
              (Part.get_eq_of_mem member memberDom).symm
            have tag : answer.1 = (queryE.symm (decoded.getLast decodedNonempty)).1 := by
              rw [valueEq, tagged]
              exact congrArg Sigma.fst (List.getLast_map _)
            rw [lastEntry]
            exact (recodeEncode (decoded.getLast decodedNonempty) answer tag).symm
      _ = ((system.flatten.1 (decoded.map ⇑queryE.symm)).map encodeAnswer).map
            (recode entry) := by
            rw [Part.map_map]
            rfl
      _ = (system.embed.1 ((decoded.map ⇑queryE.symm).map encodeQuery)).map (recode entry) := by
            rw [DependentDDS.embed_apply_encoded]
      _ = (system.embed.1 ((history ++ [entry]).map route)).map (recode entry) := by
            rw [pulled]
  · have farNone : (system.reindex compatible).embed.1 (history ++ [entry]) = Part.none := by
      rw [Part.eq_none_iff']
      intro defined
      exact conforms defined.1
    have nearNone : system.embed.1 ((history ++ [entry]).map route) = Part.none := by
      rw [Part.eq_none_iff']
      intro defined
      refine conforms fun query member => routeReflect query ?_
      exact defined.1 (route query) (List.mem_map_of_mem member)
    rw [farNone, nearNone]
    simp

/-- **A re-indexing that only renames interfaces is a pull-back along the
renaming.**  The hypotheses say exactly that in the ambient chart the
re-indexing is `Prod.map rename id` — the payload of every query and every
answer travels untouched, only its address changes — so nothing has to be
recoded. -/
theorem DependentDDS.isPullback_embed_reindex_of_rename
    {queryE : Query U boundary ≃ Query U boundary'}
    {answerE : FlatAnswer U boundary ≃ FlatAnswer U boundary'}
    (compatible : TagCompatible queryE answerE) (rename : K ≃ K')
    (codes : ∀ interface : K, boundary' (rename interface) = boundary interface)
    (ambientQuery : ∀ query : Query U boundary,
      encodeQuery (queryE query) = Prod.map rename id (encodeQuery query))
    (ambientAnswer : ∀ answer : FlatAnswer U boundary,
      encodeAnswer (answerE answer) = encodeAnswer answer)
    (system : DependentDDS U boundary) :
    IsPullback (Prod.map ⇑rename.symm id) (fun _ => id)
      system.embed (system.reindex compatible).embed := by
  refine DependentDDS.isPullback_embed_reindex compatible _ _ ?_ ?_ ?_ system
  · intro query
    rw [ambientQuery query]
    obtain ⟨interface, payload⟩ := query
    simp [encodeQuery, Prod.map]
  · rintro ⟨interface, code, payload⟩ conforms
    show code = boundary' interface
    have transported := codes (rename.symm interface)
    rw [Equiv.apply_symm_apply] at transported
    rw [transported]
    exact conforms
  · intro query answer _
    exact (ambientAnswer answer).symm

end TypedResource

/-! ### Merging two interfaces into one -/

namespace TypedResource

open PFunConverter.General

variable {M : Type*} {U : SignatureUniverse} [HasSumCode U]

/-- **The ambient re-addressing behind `DependentDDS.mergeTwo`.**  A query at
the merged interface carries a sum-coded payload; the route decodes it and
sends it back to whichever of the two block interfaces it came from, while a
query at any base interface travels untouched.

The three fall-through branches matter: a query whose payload is *not*
sum-coded is ill-coded at the merged interface, and the route must send it to a
query that is ill-coded at the block — otherwise a history the merged resource
refuses would be answered by the original.  Whichever of the two block codes
differs from the payload's code does the job; if both coincide with it, then the
sum code does not (or the query would have been well-coded), and the sum code
itself does. -/
def mergeTwoRoute (codeA codeB : U.Code) :
    AmbientQuery (M ⊕ Unit) U → AmbientQuery (M ⊕ (Unit ⊕ Unit)) U :=
  fun query =>
    match query with
    | (Sum.inl interface, payload) => (Sum.inl interface, payload)
    | (Sum.inr _, ⟨code, value⟩) =>
        if coded : code = HasSumCode.sumCode codeA codeB then
          match HasSumCode.inputEquiv codeA codeB (cast (congrArg U.input coded) value) with
          | Sum.inl left => (Sum.inr (Sum.inl ()), ⟨codeA, left⟩)
          | Sum.inr right => (Sum.inr (Sum.inr ()), ⟨codeB, right⟩)
        else if first : code = codeA then
          if code = codeB then
            (Sum.inr (Sum.inl ()), ⟨HasSumCode.sumCode codeA codeB,
              (HasSumCode.inputEquiv codeA codeB).symm
                (Sum.inl (cast (congrArg U.input first) value))⟩)
          else (Sum.inr (Sum.inr ()), ⟨code, value⟩)
        else (Sum.inr (Sum.inl ()), ⟨code, value⟩)

/-- The answer half of the same re-addressing: the merged interface answers with
the sum coding of whichever block interface actually answered, and the active
query says which one that was. -/
def mergeTwoRecode (codeA codeB : U.Code) :
    AmbientQuery (M ⊕ Unit) U → AmbientOutput U → AmbientOutput U :=
  fun query answer =>
    match query with
    | (Sum.inl _, _) => answer
    | (Sum.inr _, ⟨code, value⟩) =>
        if coded : code = HasSumCode.sumCode codeA codeB then
          match HasSumCode.inputEquiv codeA codeB (cast (congrArg U.input coded) value) with
          | Sum.inl _ =>
              if first : answer.1 = codeA then
                ⟨HasSumCode.sumCode codeA codeB,
                  (HasSumCode.outputEquiv codeA codeB).symm
                    (Sum.inl (cast (congrArg U.output first) answer.2))⟩
              else answer
          | Sum.inr _ =>
              if second : answer.1 = codeB then
                ⟨HasSumCode.sumCode codeA codeB,
                  (HasSumCode.outputEquiv codeA codeB).symm
                    (Sum.inr (cast (congrArg U.output second) answer.2))⟩
              else answer
        else answer

/-- A base interface is untouched by the merge's re-addressing. -/
@[simp]
theorem mergeTwoRoute_inl (codeA codeB : U.Code) (interface : M)
    (payload : AmbientInput U) :
    mergeTwoRoute codeA codeB (Sum.inl interface, payload) =
      (Sum.inl interface, payload) :=
  rfl

/-- …and the merged interface is re-addressed *into the block*, whichever
branch of the coding it takes. -/
theorem mergeTwoRoute_inr (codeA codeB : U.Code) (merged : Unit)
    (payload : AmbientInput U) :
    ∃ block : Unit ⊕ Unit,
      (mergeTwoRoute (M := M) codeA codeB (Sum.inr merged, payload)).1 = Sum.inr block := by
  obtain ⟨code, value⟩ := payload
  by_cases coded : code = HasSumCode.sumCode codeA codeB
  · simp only [mergeTwoRoute, dif_pos coded]
    cases HasSumCode.inputEquiv codeA codeB (cast (congrArg U.input coded) value)
    · exact ⟨Sum.inl (), rfl⟩
    · exact ⟨Sum.inr (), rfl⟩
  · simp only [mergeTwoRoute, dif_neg coded]
    by_cases first : code = codeA
    · simp only [dif_pos first]
      by_cases second : code = codeB
      · simp only [if_pos second]
        exact ⟨Sum.inl (), rfl⟩
      · simp only [if_neg second]
        exact ⟨Sum.inr (), rfl⟩
    · simp only [dif_neg first]
      exact ⟨Sum.inl (), rfl⟩

/-- The merge's answer recoding leaves a base interface's answers alone. -/
@[simp]
theorem mergeTwoRecode_inl (codeA codeB : U.Code) (interface : M)
    (payload : AmbientInput U) :
    mergeTwoRecode (M := M) codeA codeB (Sum.inl interface, payload) = id :=
  rfl

section Computation

variable (base : Boundary U M) (codeA codeB : U.Code)

/-- The merge leaves a base query where it was. -/
theorem mergeQueryEquiv_base (interface : M) (value : U.input (base interface)) :
    mergeQueryEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockInputCode codeA codeB)
        ⟨Sum.inl interface, value⟩ =
      ⟨Sum.inl interface, value⟩ :=
  rfl

/-- A query at the first merged interface becomes a left-tagged sum-coded query
at the merged one. -/
theorem mergeQueryEquiv_first (value : U.input codeA) :
    mergeQueryEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockInputCode codeA codeB)
        ⟨Sum.inr (Sum.inl ()), value⟩ =
      ⟨Sum.inr (), (HasSumCode.inputEquiv codeA codeB).symm (Sum.inl value)⟩ :=
  rfl

/-- …and at the second, a right-tagged one. -/
theorem mergeQueryEquiv_second (value : U.input codeB) :
    mergeQueryEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockInputCode codeA codeB)
        ⟨Sum.inr (Sum.inr ()), value⟩ =
      ⟨Sum.inr (), (HasSumCode.inputEquiv codeA codeB).symm (Sum.inr value)⟩ :=
  rfl

/-- The answer half at a base interface. -/
theorem mergeAnswerEquiv_base (interface : M) (value : U.output (base interface)) :
    mergeAnswerEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockOutputCode codeA codeB)
        ⟨Sum.inl interface, value⟩ =
      ⟨Sum.inl interface, value⟩ :=
  rfl

/-- The answer half at the first merged interface. -/
theorem mergeAnswerEquiv_first (value : U.output codeA) :
    mergeAnswerEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockOutputCode codeA codeB)
        ⟨Sum.inr (Sum.inl ()), value⟩ =
      ⟨Sum.inr (), (HasSumCode.outputEquiv codeA codeB).symm (Sum.inl value)⟩ :=
  rfl

/-- The answer half at the second merged interface. -/
theorem mergeAnswerEquiv_second (value : U.output codeB) :
    mergeAnswerEquiv base (HasSumCode.sumCode codeA codeB)
        (twoBlockOutputCode codeA codeB)
        ⟨Sum.inr (Sum.inr ()), value⟩ =
      ⟨Sum.inr (), (HasSumCode.outputEquiv codeA codeB).symm (Sum.inr value)⟩ :=
  rfl

end Computation

/-- **Merging two interfaces into one is a pull-back**, in the ambient chart. -/
theorem DependentDDS.isPullback_embed_mergeTwo (base : Boundary U M)
    (codeA codeB : U.Code)
    (system : DependentDDS U (Sum.elim base (twoBlock codeA codeB))) :
    IsPullback (mergeTwoRoute codeA codeB) (mergeTwoRecode codeA codeB)
      system.embed (DependentDDS.mergeTwo base codeA codeB system).embed := by
  refine DependentDDS.isPullback_embed_reindex
    (tagCompatible_mergeTwo base codeA codeB) _ _ ?_ ?_ ?_ system
  · rintro ⟨interface | (⟨⟩ | ⟨⟩), value⟩
    · rfl
    · rw [mergeQueryEquiv_first]
      show mergeTwoRoute codeA codeB
          (Sum.inr (), ⟨HasSumCode.sumCode codeA codeB,
            (HasSumCode.inputEquiv codeA codeB).symm (Sum.inl value)⟩) = _
      simp only [mergeTwoRoute, cast_eq, Equiv.apply_symm_apply]
      rfl
    · rw [mergeQueryEquiv_second]
      show mergeTwoRoute codeA codeB
          (Sum.inr (), ⟨HasSumCode.sumCode codeA codeB,
            (HasSumCode.inputEquiv codeA codeB).symm (Sum.inr value)⟩) = _
      simp only [mergeTwoRoute, cast_eq, Equiv.apply_symm_apply]
      rfl
  · rintro ⟨interface | ⟨⟩, code, value⟩ conforms
    · exact conforms
    · show code = HasSumCode.sumCode codeA codeB
      by_cases coded : code = HasSumCode.sumCode codeA codeB
      · exact coded
      · exfalso
        revert conforms
        show QueryConforms _ (mergeTwoRoute codeA codeB (Sum.inr (), ⟨code, value⟩)) → False
        simp only [mergeTwoRoute, dif_neg coded]
        by_cases first : code = codeA
        · simp only [dif_pos first]
          by_cases second : code = codeB
          · simp only [if_pos second]
            exact fun conforms => coded (first.trans conforms.symm)
          · simp only [if_neg second]
            exact fun conforms => second conforms
        · simp only [dif_neg first]
          exact fun conforms => first conforms
  · rintro ⟨interface | (⟨⟩ | ⟨⟩), value⟩ ⟨answerInterface, answer⟩ tag
    · cases tag
      rfl
    · cases tag
      rw [mergeQueryEquiv_first, mergeAnswerEquiv_first]
      show mergeTwoRecode codeA codeB
          (Sum.inr (), ⟨HasSumCode.sumCode codeA codeB,
            (HasSumCode.inputEquiv codeA codeB).symm (Sum.inl value)⟩)
          (⟨codeA, answer⟩ : AmbientOutput U) = _
      simp only [mergeTwoRecode, cast_eq, Equiv.apply_symm_apply]
      rfl
    · cases tag
      rw [mergeQueryEquiv_second, mergeAnswerEquiv_second]
      show mergeTwoRecode codeA codeB
          (Sum.inr (), ⟨HasSumCode.sumCode codeA codeB,
            (HasSumCode.inputEquiv codeA codeB).symm (Sum.inr value)⟩)
          (⟨codeB, answer⟩ : AmbientOutput U) = _
      simp only [mergeTwoRecode, cast_eq, Equiv.apply_symm_apply]
      rfl

end TypedResource

end

end RandomSystems.CR18
