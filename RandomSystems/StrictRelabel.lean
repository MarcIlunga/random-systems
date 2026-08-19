/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictContext

/-!
# Strict behavior transport along alphabet relabellings

Bijective relabelling of the query and answer alphabets is invisible to the
strict contextual metric.  A deterministic system over `(X, Y)` is relabelled
along equivalences `e : X ≃ X'` and `f : Y ≃ Y'` by translating each incoming
query back through `e.symm` and each produced answer forward through `f`
(`DDS.relabel`); a strict test over `(X', Y')` pulls back to a test over
`(X, Y)` by the inverse translation on its interaction alphabet
(`pullbackFn` / `testPullback`).  The two translations cancel against each
other inside the transcript equations (`applyRaw_relabel`), so acceptance
masses transport exactly (`accept_mass_relabel`), the test pullback is a
bijection (`testEquiv`), and the strict supremum metric is invariant on the
nose (`maxEDist_relabel`).  Consequently relabelling descends to strict
behavior (`System.relabel`) as an isometry (`System.edist_relabel`) — the
transport lemma needed to install parallel composition on the typed carrier —
and as a bijection (`System.relabelEquiv`, `System.relabel_inj`), which is what
carries the strict cancellation theorem across a boundary transport that is
only an isomorphism of alphabets rather than an equality of them.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped Classical

noncomputable section

universe u v w z a b c d

namespace PFunDDS

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  {X'' : Type c} {Y'' : Type d}

/-- Relabel a deterministic system along alphabet equivalences: a history is
accepted exactly when its `e.symm`-translation is, and the answer is the
`f`-translation of the original answer.  Both `Valid` clauses transport
because `List.map` preserves prefixes and nonemptiness. -/
def DDS.relabel (e : X ≃ X') (f : Y ≃ Y') (system : DDS X Y) : DDS X' Y' :=
  ⟨fun history => (system.1 (history.map ⇑e.symm)).map ⇑f,
    ⟨fun h => empty_not_mem system h, by
      intro l₁ l₂ hprefix hne hdom
      exact prefix_closed system (hprefix.map ⇑e.symm)
        (by simpa using hne) hdom⟩⟩

@[simp]
theorem DDS.relabel_raw (e : X ≃ X') (f : Y ≃ Y') (system : DDS X Y)
    (history : List X') :
    (DDS.relabel e f system).1 history =
      (system.1 (history.map ⇑e.symm)).map ⇑f :=
  rfl

/-- Domain transport: a relabelled history is in the relabelled domain iff the
back-translated history is in the original domain. -/
@[simp]
theorem DDS.mem_dom_relabel (e : X ≃ X') (f : Y ≃ Y') (system : DDS X Y)
    (history : List X') :
    history ∈ dom (DDS.relabel e f system) ↔
      history.map ⇑e.symm ∈ dom system :=
  Iff.rfl

/-- Output transport: the relabelled system answers with the `f`-translation
of the original answer on the back-translated history. -/
theorem DDS.output_relabel (e : X ≃ X') (f : Y ≃ Y') (system : DDS X Y)
    (history : List X') (h : history ∈ dom (DDS.relabel e f system)) :
    output (DDS.relabel e f system) history h =
      f (output system (history.map ⇑e.symm) h) :=
  rfl

/-- Relabelling is functorial: consecutive relabellings compose to the
relabelling along the composed equivalences. -/
theorem DDS.relabel_relabel (e : X ≃ X') (f : Y ≃ Y')
    (e' : X' ≃ X'') (f' : Y' ≃ Y'') (system : DDS X Y) :
    DDS.relabel e' f' (DDS.relabel e f system) =
      DDS.relabel (e.trans e') (f.trans f') system := by
  apply Subtype.ext
  funext history
  show ((system.1 ((history.map ⇑e'.symm).map ⇑e.symm)).map ⇑f).map ⇑f' =
    (system.1 (history.map ⇑(e.trans e').symm)).map ⇑(f.trans f')
  rw [Part.map_map, List.map_map]
  rfl

/-- Relabelling along the identity equivalences is the identity. -/
theorem DDS.relabel_refl (system : DDS X Y) :
    DDS.relabel (Equiv.refl X) (Equiv.refl Y) system = system := by
  apply Subtype.ext
  funext history
  show (system.1 (history.map ⇑(Equiv.refl X).symm)).map ⇑(Equiv.refl Y) =
    system.1 history
  rw [show ⇑(Equiv.refl X).symm = id from rfl, List.map_id]
  exact Part.map_id' (fun _ => rfl) _

/-- The inverse relabelling undoes the relabelling. -/
theorem DDS.relabel_symm_relabel (e : X ≃ X') (f : Y ≃ Y')
    (system : DDS X Y) :
    DDS.relabel e.symm f.symm (DDS.relabel e f system) = system := by
  rw [DDS.relabel_relabel, Equiv.self_trans_symm, Equiv.self_trans_symm,
    DDS.relabel_refl]

/-- The relabelling undoes the inverse relabelling. -/
theorem DDS.relabel_relabel_symm (e : X ≃ X') (f : Y ≃ Y')
    (system : DDS X' Y') :
    DDS.relabel e f (DDS.relabel e.symm f.symm system) = system := by
  rw [DDS.relabel_relabel, Equiv.symm_trans_self, Equiv.symm_trans_self,
    DDS.relabel_refl]

/-- Relabelling is a bijection on deterministic systems. -/
def DDS.relabelEquiv (e : X ≃ X') (f : Y ≃ Y') : DDS X Y ≃ DDS X' Y' where
  toFun := DDS.relabel e f
  invFun := DDS.relabel e.symm f.symm
  left_inv := DDS.relabel_symm_relabel e f
  right_inv := DDS.relabel_relabel_symm e f

/-- The Definition 3.3 deletion scan commutes with relabelling: relabelling
never changes which next queries are kept, only their names. -/
theorem keptPrefix_relabel (e : X ≃ X') (f : Y ≃ Y') (system : DDS X Y)
    (history : List X) :
    keptPrefix (DDS.relabel e f system) (history.map ⇑e) =
      (keptPrefix system history).map ⇑e := by
  suffices h : ∀ (rest acc : List X),
      List.foldl
          (fun acc next =>
            if acc ++ [next] ∈ dom (DDS.relabel e f system) then acc ++ [next]
            else acc)
          (acc.map ⇑e) (rest.map ⇑e) =
        (List.foldl
          (fun acc next =>
            if acc ++ [next] ∈ dom system then acc ++ [next] else acc)
          acc rest).map ⇑e by
    simpa [keptPrefix] using h history []
  intro rest
  induction rest with
  | nil => intro acc; rfl
  | cons next rest ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      have hdom : acc.map ⇑e ++ [e next] ∈ dom (DDS.relabel e f system) ↔
          acc ++ [next] ∈ dom system := by
        rw [DDS.mem_dom_relabel]
        have hback : (acc.map ⇑e ++ [e next]).map ⇑e.symm = acc ++ [next] := by
          simp
        rw [hback]
      by_cases hmem : acc ++ [next] ∈ dom system
      · rw [if_pos (hdom.mpr hmem), if_pos hmem,
          show acc.map ⇑e ++ [e next] = (acc ++ [next]).map ⇑e by simp]
        exact ih (acc ++ [next])
      · rw [if_neg (fun hc => hmem (hdom.mp hc)), if_neg hmem]
        exact ih acc

open scoped PFunDDS in
/-- The Definition 3.3 completion commutes with relabelling: the completed
relabelled system answers with the `Option.map f` translation of the
completed original answer. -/
theorem output_fullyDefined_relabel (e : X ≃ X') (f : Y ≃ Y')
    (system : DDS X Y) (history : List X) (hne : history ≠ []) :
    output ((DDS.relabel e f system)⊥) (history.map ⇑e)
        (by rw [dom_fullyDefined]; simpa using hne) =
      Option.map ⇑f
        (output (system⊥) history (by rw [dom_fullyDefined]; exact hne)) := by
  have hmapne : history.map ⇑e ≠ [] := by simpa using hne
  rw [output_fullyDefined, output_fullyDefined]
  have hdrop : (history.map ⇑e).dropLast = history.dropLast.map ⇑e :=
    List.map_dropLast.symm
  have hlast : (history.map ⇑e).getLast hmapne = e (history.getLast hne) :=
    List.getLast_map _
  have hcands :
      keptPrefix (DDS.relabel e f system) (history.map ⇑e).dropLast ++
          [(history.map ⇑e).getLast hmapne] =
        (keptPrefix system history.dropLast ++ [history.getLast hne]).map ⇑e := by
    rw [hdrop, keptPrefix_relabel, hlast, List.map_append]
    rfl
  set candidate := keptPrefix system history.dropLast ++ [history.getLast hne]
    with hcandidate
  have hCiff : candidate.map ⇑e ∈ dom (DDS.relabel e f system) ↔
      candidate ∈ dom system := by
    rw [DDS.mem_dom_relabel]
    have hback : (candidate.map ⇑e).map ⇑e.symm = candidate := by simp
    rw [hback]
  simp only [hcands]
  by_cases hC : candidate ∈ dom system
  · rw [dif_pos (hCiff.mpr hC), dif_pos hC, Option.map_some]
    refine congrArg some ?_
    rw [DDS.output_relabel]
    refine congrArg f (output_congr system ?_ _ _)
    simp only [List.map_map, Equiv.symm_comp_self, List.map_id]
    exact hcandidate
  · rw [dif_neg (fun hc => hC (hCiff.mp hc)), dif_neg hC]
    rfl

end PFunDDS

namespace PFunConverter

open scoped PFunDDS

variable {U : Type a} {V : Type b} {X : Type u} {Y : Type v}
  {X' : Type w} {Y' : Type z} {X'' : Type c} {Y'' : Type d}

/-- Pull a protocol function on the relabelled inner interface `(X', Y')`
back to the original interface `(X, Y)`: consult the protocol on the
`Option.map f`-translated answer history, and translate an issued query back
through `e.symm` (outer moves are untouched). -/
def pullbackFn (e : X ≃ X') (f : Y ≃ Y') (protocol : ProtocolFn U V X' Y') :
    ProtocolFn U V X Y :=
  fun pair =>
    (protocol (pair.1, pair.2.map (Option.map ⇑f))).map (Sum.map ⇑e.symm id)

/-- The pullback is consulted exactly where the original protocol is. -/
theorem pullbackFn_dom_iff (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (pair : List U × List (Option Y)) :
    (pullbackFn e f protocol pair).Dom ↔
      (protocol (pair.1, pair.2.map (Option.map ⇑f))).Dom :=
  Iff.rfl

/-- Query moves of the pullback are back-translated query moves. -/
theorem inl_mem_pullbackFn_iff (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (pair : List U × List (Option Y))
    (query : X) :
    Sum.inl query ∈ pullbackFn e f protocol pair ↔
      Sum.inl (e query) ∈ protocol (pair.1, pair.2.map (Option.map ⇑f)) := by
  simp only [pullbackFn, Part.mem_map_iff]
  constructor
  · rintro ⟨move, hmove, hmap⟩
    cases move with
    | inl issued =>
        simp only [Sum.map_inl, Sum.inl.injEq] at hmap
        rwa [show e query = issued from by rw [← hmap]; simp]
    | inr answered => simp at hmap
  · intro hmove
    exact ⟨Sum.inl (e query), hmove, by simp⟩

/-- Answer moves of the pullback are exactly the original answer moves. -/
theorem inr_mem_pullbackFn_iff (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (pair : List U × List (Option Y))
    (answer : V) :
    Sum.inr answer ∈ pullbackFn e f protocol pair ↔
      Sum.inr answer ∈ protocol (pair.1, pair.2.map (Option.map ⇑f)) := by
  simp only [pullbackFn, Part.mem_map_iff]
  constructor
  · rintro ⟨move, hmove, hmap⟩
    cases move with
    | inl issued => simp at hmap
    | inr answered =>
        simp only [Sum.map_inr, id_eq, Sum.inr.injEq] at hmap
        rwa [← hmap]
  · intro hmove
    exact ⟨Sum.inr answer, hmove, by simp⟩

/-- Pulling back is functorial in the pair of equivalences. -/
theorem pullbackFn_pullbackFn (e : X ≃ X') (f : Y ≃ Y')
    (e' : X' ≃ X'') (f' : Y' ≃ Y'') (protocol : ProtocolFn U V X'' Y'') :
    pullbackFn e f (pullbackFn e' f' protocol) =
      pullbackFn (e.trans e') (f.trans f') protocol := by
  funext pair
  simp only [pullbackFn, Part.map_map, List.map_map]
  have hsum : (Sum.map (⇑e.symm) id ∘ Sum.map (⇑e'.symm) id : X'' ⊕ V → X ⊕ V) =
      Sum.map (⇑(e.trans e').symm) id := by
    funext move
    cases move <;> rfl
  have hopt : (Option.map ⇑f' ∘ Option.map ⇑f : Option Y → Option Y'') =
      Option.map ⇑(f.trans f') := by
    funext answer
    cases answer <;> rfl
  rw [hsum, hopt]

/-- Pulling back along the identity equivalences is the identity. -/
theorem pullbackFn_refl (protocol : ProtocolFn U V X Y) :
    pullbackFn (Equiv.refl X) (Equiv.refl Y) protocol = protocol := by
  funext pair
  show (protocol (pair.1, pair.2.map (Option.map ⇑(Equiv.refl Y)))).map
      (Sum.map ⇑(Equiv.refl X).symm id) = protocol pair
  rw [show Option.map ⇑(Equiv.refl Y) = id from funext fun o => by
      cases o <;> rfl,
    List.map_id]
  exact Part.map_id' (fun move => by cases move <;> rfl) _

/-- Trace-tree transport: the pullback reaches a pair exactly when the
original protocol reaches its answer-translated pair. -/
theorem reach_pullbackFn_iff (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (pair : List U × List (Option Y)) :
    Reach (pullbackFn e f protocol) pair ↔
      Reach protocol (pair.1, pair.2.map (Option.map ⇑f)) := by
  have hforward : ∀ {p : List U × List (Option Y)},
      Reach (pullbackFn e f protocol) p →
        Reach protocol (p.1, p.2.map (Option.map ⇑f)) := by
    intro p h
    induction h with
    | first u => exact Reach.first u
    | answer hr hx y ih =>
        have hx' := (inl_mem_pullbackFn_iff e f protocol _ _).mp hx
        have hnext := Reach.answer ih hx' (Option.map ⇑f y)
        simpa using hnext
    | next hr hv u ih =>
        exact Reach.next ih ((inr_mem_pullbackFn_iff e f protocol _ _).mp hv) u
  have hbackward : ∀ {p : List U × List (Option Y')},
      Reach protocol p →
        Reach (pullbackFn e f protocol) (p.1, p.2.map (Option.map ⇑f.symm)) := by
    intro p h
    induction h with
    | first u => exact Reach.first u
    | answer hr hx y ih =>
        rename_i us ys x
        have hx' : Sum.inl (e.symm x) ∈
            pullbackFn e f protocol (us, ys.map (Option.map ⇑f.symm)) := by
          rw [inl_mem_pullbackFn_iff]
          simpa using hx
        have hnext := Reach.answer ih hx' (Option.map ⇑f.symm y)
        simpa using hnext
    | next hr hv u ih =>
        rename_i us ys v
        have hv' : Sum.inr v ∈
            pullbackFn e f protocol (us, ys.map (Option.map ⇑f.symm)) := by
          rw [inr_mem_pullbackFn_iff]
          simpa using hv
        exact Reach.next ih hv' u
  constructor
  · exact hforward
  · intro h
    have := hbackward h
    simpa using this

/-- The pullback never moves past a completion symbol when the original
protocol does not: CR18 Definition 3.8's input-alphabet clause transports. -/
theorem answersInY_pullbackFn (e : X ≃ X') (f : Y ≃ Y')
    {protocol : ProtocolFn U V X' Y'} (h : AnswersInY protocol) :
    AnswersInY (pullbackFn e f protocol) := by
  intro pair hreach hnone hdom
  refine h (pair.1, pair.2.map (Option.map ⇑f))
    ((reach_pullbackFn_iff e f protocol pair).mp hreach)
    (List.mem_map.mpr ⟨none, hnone, rfl⟩) ?_
  exact ((pullbackFn_dom_iff e f protocol pair).mp hdom)

/-- The pullback never opens a longer query streak than the original
protocol: CR18 Definition 3.8's finite-bound clause transports. -/
theorem answersWithin_pullbackFn (e : X ≃ X') (f : Y ≃ Y')
    {protocol : ProtocolFn U V X' Y'} {bound : ℕ}
    (h : AnswersWithin protocol bound) :
    AnswersWithin (pullbackFn e f protocol) bound := by
  intro pair hreach ext hlen hall
  refine h (pair.1, pair.2.map (Option.map ⇑f))
    ((reach_pullbackFn_iff e f protocol pair).mp hreach)
    (ext.map (Option.map ⇑f)) (by simpa using hlen) ?_
  intro k hk
  obtain ⟨query, hquery⟩ := hall k (by simpa using hk)
  refine ⟨e query, ?_⟩
  have := (inl_mem_pullbackFn_iff e f protocol _ _).mp hquery
  simpa [List.map_take] using this

/-- CR18 Definition 3.8 membership transports along the pullback. -/
theorem isDDC_pullbackFn (e : X ≃ X') (f : Y ≃ Y')
    {protocol : ProtocolFn U V X' Y'} (h : IsDDC protocol) :
    IsDDC (pullbackFn e f protocol) :=
  ⟨answersInY_pullbackFn e f h.1,
    h.2.choose, answersWithin_pullbackFn e f h.2.choose_spec⟩

/-- The transcript-equation driver cannot see a relabelling: driving a
protocol against the relabelled system is driving its pullback against the
original system, with the inner histories translated. -/
theorem drive_relabel (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (system : PFunDDS.DDS X Y) :
    ∀ (fuel : ℕ) (outer : List U) (inner : List X)
      (answers : List (Option Y)),
      drive protocol (PFunDDS.DDS.relabel e f system) fuel outer
          (inner.map ⇑e) (answers.map (Option.map ⇑f)) =
        (drive (pullbackFn e f protocol) system fuel outer inner answers).map
          (fun result =>
            (result.1, result.2.1.map ⇑e, result.2.2.map (Option.map ⇑f))) := by
  intro fuel
  induction fuel with
  | zero => intro outer inner answers; simp [drive]
  | succ fuel ih =>
      intro outer inner answers
      simp only [drive, pullbackFn]
      rw [Part.map_bind, ← Part.bind_some_eq_map, Part.bind_assoc]
      refine congrArg (Part.bind _) (funext fun move => ?_)
      cases move with
      | inl query =>
          simp only [Sum.map_inl, Part.bind_some]
          have hlist : (inner ++ [e.symm query]).map ⇑e =
              inner.map ⇑e ++ [query] := by simp
          have hanswer :
              PFunDDS.output ((PFunDDS.DDS.relabel e f system)⊥)
                  (inner.map ⇑e ++ [query])
                  (by rw [PFunDDS.dom_fullyDefined]; simp) =
                Option.map ⇑f
                  (PFunDDS.output (system⊥) (inner ++ [e.symm query])
                    (by rw [PFunDDS.dom_fullyDefined]; simp)) := by
            rw [← PFunDDS.output_fullyDefined_relabel e f system
              (inner ++ [e.symm query]) (by simp)]
            exact PFunDDS.output_congr _ hlist.symm _ _
          have hanswers : answers.map (Option.map ⇑f) ++
              [Option.map ⇑f
                (PFunDDS.output (system⊥) (inner ++ [e.symm query])
                  (by rw [PFunDDS.dom_fullyDefined]; simp))] =
            (answers ++
              [PFunDDS.output (system⊥) (inner ++ [e.symm query])
                (by rw [PFunDDS.dom_fullyDefined]; simp)]).map
              (Option.map ⇑f) := by simp
          rw [hanswer, hanswers, ← hlist]
          exact ih outer (inner ++ [e.symm query]) _
      | inr answer =>
          simp [Part.bind_some, Part.map_some]

/-- The outer fold cannot see a relabelling either. -/
theorem driveOuter_relabel (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (system : PFunDDS.DDS X Y)
    (fuel : ℕ) :
    ∀ (rest outerPrefix : List U) (inner : List X)
      (answers : List (Option Y)),
      driveOuter protocol (PFunDDS.DDS.relabel e f system) fuel outerPrefix
          (inner.map ⇑e) (answers.map (Option.map ⇑f)) rest =
        (driveOuter (pullbackFn e f protocol) system fuel outerPrefix inner
            answers rest).map
          (fun result =>
            (result.1, result.2.1.map ⇑e, result.2.2.map (Option.map ⇑f))) := by
  intro rest
  induction rest with
  | nil =>
      intro outerPrefix inner answers
      simp [driveOuter, Part.map_some]
  | cons next rest ih =>
      intro outerPrefix inner answers
      simp only [driveOuter]
      rw [drive_relabel, Part.map_bind, ← Part.bind_some_eq_map,
        Part.bind_assoc]
      refine congrArg (Part.bind _) (funext fun result => ?_)
      rw [Part.bind_some, ih (outerPrefix ++ [next]) result.2.1 result.2.2,
        Part.map_map, Part.map_map]
      rfl

/-- **Relabelling transport for transcript-equation application** (raw form):
applying a protocol to the relabelled system is applying its pullback to the
original system. -/
theorem applyRaw_relabel (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (system : PFunDDS.DDS X Y) :
    applyRaw protocol (PFunDDS.DDS.relabel e f system) =
      applyRaw (pullbackFn e f protocol) system := by
  funext outer
  apply Part.ext
  intro answer
  rw [mem_applyRaw, mem_applyRaw]
  refine exists_congr fun fuel => ?_
  rw [mem_applyRawAt_iff, mem_applyRawAt_iff]
  have hdo := driveOuter_relabel e f protocol system fuel outer [] [] []
  simp only [List.map_nil] at hdo
  rw [hdo]
  constructor
  · rintro ⟨result, hresult, hlast⟩
    rw [Part.mem_map_iff] at hresult
    obtain ⟨original, horiginal, rfl⟩ := hresult
    exact ⟨original, horiginal, hlast⟩
  · rintro ⟨original, horiginal, hlast⟩
    refine ⟨(original.1, original.2.1.map ⇑e,
      original.2.2.map (Option.map ⇑f)), ?_, hlast⟩
    rw [Part.mem_map_iff]
    exact ⟨original, horiginal, rfl⟩

/-- **Relabelling transport for transcript-equation application**: applying a
protocol to the relabelled system is applying its pullback to the original
system. -/
theorem apply_relabel (e : X ≃ X') (f : Y ≃ Y')
    (protocol : ProtocolFn U V X' Y') (system : PFunDDS.DDS X Y) :
    apply protocol (PFunDDS.DDS.relabel e f system) =
      apply (pullbackFn e f protocol) system :=
  Subtype.ext (applyRaw_relabel e f protocol system)

end PFunConverter

namespace PFunPDS

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  {X'' : Type c} {Y'' : Type d}

/-- Relabel a probabilistic system: push the deterministic relabelling
through the distribution over deterministic representatives. -/
def relabel (e : X ≃ X') (f : Y ≃ Y') (law : PFunPDS X Y) : PFunPDS X' Y' :=
  Dist.fTransform (PFunDDS.DDS.relabel e f) law

/-- Relabelling preserves and reflects total probability mass. -/
@[simp]
theorem isProbDist_relabel_iff (e : X ≃ X') (f : Y ≃ Y') (law : PFunPDS X Y) :
    (relabel e f law).isProbDist ↔ law.isProbDist :=
  Dist.isProbDist_fTransform_of_injective
    (Function.LeftInverse.injective
      (PFunDDS.DDS.relabel_symm_relabel e f)) law

/-- Law-level functoriality of relabelling. -/
theorem relabel_relabel (e : X ≃ X') (f : Y ≃ Y')
    (e' : X' ≃ X'') (f' : Y' ≃ Y'') (law : PFunPDS X Y) :
    relabel e' f' (relabel e f law) =
      relabel (e.trans e') (f.trans f') law := by
  unfold relabel
  rw [Dist.fTransform_comp]
  exact congrArg (fun step => Dist.fTransform step law)
    (funext fun system => PFunDDS.DDS.relabel_relabel e f e' f' system)

/-- Law-level identity relabelling. -/
theorem relabel_refl (law : PFunPDS X Y) :
    relabel (Equiv.refl X) (Equiv.refl Y) law = law := by
  unfold relabel
  rw [show PFunDDS.DDS.relabel (Equiv.refl X) (Equiv.refl Y) =
      (id : PFunDDS.DDS X Y → PFunDDS.DDS X Y)
    from funext fun system => PFunDDS.DDS.relabel_refl system]
  exact Dist.fTransform_id law

/-- The inverse relabelling undoes the relabelling at the law level. -/
theorem relabel_symm_relabel (e : X ≃ X') (f : Y ≃ Y') (law : PFunPDS X Y) :
    relabel e.symm f.symm (relabel e f law) = law := by
  rw [relabel_relabel, Equiv.self_trans_symm, Equiv.self_trans_symm,
    relabel_refl]

/-- The relabelling undoes the inverse relabelling at the law level. -/
theorem relabel_relabel_symm (e : X ≃ X') (f : Y ≃ Y')
    (law : PFunPDS X' Y') :
    relabel e f (relabel e.symm f.symm law) = law := by
  rw [relabel_relabel, Equiv.symm_trans_self, Equiv.symm_trans_self,
    relabel_refl]

/-- Relabelling restricted to probability laws. -/
def Prob.relabel (e : X ≃ X') (f : Y ≃ Y') (law : Prob X Y) : Prob X' Y' :=
  ⟨PFunPDS.relabel e f law.val,
    (isProbDist_relabel_iff e f law.val).2 law.property⟩

end PFunPDS

namespace StrictContext

open PFunConverter

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  {X'' : Type c} {Y'' : Type d}

/-- Pull a strict test on the relabelled interface back to the original
interface.  `IsDDC` transports (`isDDC_pullbackFn`). -/
def testPullback (e : X ≃ X') (f : Y ≃ Y') (test : Test X' Y') : Test X Y :=
  ⟨pullbackFn e f test.val, isDDC_pullbackFn e f test.property⟩

/-- Observation transport: observing the relabelled deterministic system is
observing the original system with the pulled-back test. -/
theorem observe_relabel (e : X ≃ X') (f : Y ≃ Y') (test : Test X' Y')
    (system : PFunDDS.DDS X Y) :
    observe test (PFunDDS.DDS.relabel e f system) =
      observe (testPullback e f test) system := by
  unfold observe testPullback
  rw [applyRaw_relabel]

/-- Acceptance-mass transport: the relabelled law accepts a test exactly as
often as the original law accepts its pullback. -/
theorem accept_mass_relabel (e : X ≃ X') (f : Y ≃ Y') (test : Test X' Y')
    (law : PFunPDS X Y) :
    acceptMass test (PFunPDS.relabel e f law) =
      acceptMass (testPullback e f test) law := by
  unfold acceptMass PFunPDS.relabel
  rw [Dist.mass_fTransform]
  exact Dist.mass_congr law fun system => by rw [observe_relabel]

/-- The test pullback is a bijection; its inverse is the pullback along the
inverse equivalences.  This is what turns the acceptance-mass transport into
an exact reindexing of the strict supremum. -/
def testEquiv (e : X ≃ X') (f : Y ≃ Y') : Test X' Y' ≃ Test X Y where
  toFun := testPullback e f
  invFun := testPullback e.symm f.symm
  left_inv test := Subtype.ext (by
    show pullbackFn e.symm f.symm (pullbackFn e f test.val) = test.val
    rw [pullbackFn_pullbackFn, Equiv.symm_trans_self, Equiv.symm_trans_self,
      pullbackFn_refl])
  right_inv test := Subtype.ext (by
    show pullbackFn e f (pullbackFn e.symm f.symm test.val) = test.val
    rw [pullbackFn_pullbackFn, Equiv.self_trans_symm, Equiv.self_trans_symm,
      pullbackFn_refl])

/-- **The strict contextual metric is invariant under relabelling.**  The
supremum over relabelled-interface tests is the supremum over original
tests, reindexed along the pullback bijection. -/
theorem maxEDist_relabel (e : X ≃ X') (f : Y ≃ Y')
    (left right : PFunPDS X Y) :
    maxEDist (PFunPDS.relabel e f left) (PFunPDS.relabel e f right) =
      maxEDist left right := by
  unfold maxEDist
  rw [← Equiv.iSup_comp
    (g := fun test : Test X Y =>
      edist (acceptMass test left) (acceptMass test right))
    (testEquiv e f)]
  exact iSup_congr fun test => by
    rw [accept_mass_relabel, accept_mass_relabel]
    rfl

/-- Relabelling preserves strict contextual equivalence. -/
theorem equivalent_relabel (e : X ≃ X') (f : Y ≃ Y')
    {left right : PFunPDS X Y} (equivalent : Equivalent left right) :
    Equivalent (PFunPDS.relabel e f left) (PFunPDS.relabel e f right) := by
  intro test
  rw [accept_mass_relabel, accept_mass_relabel]
  exact equivalent (testPullback e f test)

/-- Relabelling preserves and reflects strict contextual equivalence: the
inverse relabelling undoes it. -/
theorem equivalent_relabel_iff (e : X ≃ X') (f : Y ≃ Y')
    (left right : PFunPDS X Y) :
    Equivalent (PFunPDS.relabel e f left) (PFunPDS.relabel e f right) ↔
      Equivalent left right := by
  constructor
  · intro equivalent
    have hback := equivalent_relabel e.symm f.symm equivalent
    rwa [PFunPDS.relabel_symm_relabel, PFunPDS.relabel_symm_relabel] at hback
  · exact equivalent_relabel e f

namespace System

/-- Relabelling of strict behavior along alphabet equivalences.  Descends
from `PFunPDS.relabel` because relabelling preserves contextual
equivalence. -/
def relabel (e : X ≃ X') (f : Y ≃ Y') : System X Y → System X' Y' :=
  fun behavior => Quotient.liftOn behavior
    (fun law => ofProb (PFunPDS.Prob.relabel e f law))
    (fun _ _ equivalent =>
      Quotient.sound (equivalent_relabel e f equivalent))

@[simp]
theorem relabel_ofProb (e : X ≃ X') (f : Y ≃ Y') (law : PFunPDS.Prob X Y) :
    relabel e f (ofProb law) = ofProb (PFunPDS.Prob.relabel e f law) :=
  rfl

/-- **Relabelling is an isometry of strict behavior.** -/
@[simp]
theorem edist_relabel (e : X ≃ X') (f : Y ≃ Y')
    (left right : System X Y) :
    edist (relabel e f left) (relabel e f right) = edist left right := by
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => exact maxEDist_relabel e f left.val right.val

/-- Behavior-level functoriality of relabelling. -/
theorem relabel_relabel (e : X ≃ X') (f : Y ≃ Y')
    (e' : X' ≃ X'') (f' : Y' ≃ Y'') (behavior : System X Y) :
    relabel e' f' (relabel e f behavior) =
      relabel (e.trans e') (f.trans f') behavior := by
  induction behavior using Quotient.inductionOn with
  | _ law =>
      exact congrArg ofProb (Subtype.ext
        (PFunPDS.relabel_relabel e f e' f' law.val))

/-- Relabelling along the identity equivalences is the identity on strict
behavior. -/
theorem relabel_refl (behavior : System X Y) :
    relabel (Equiv.refl X) (Equiv.refl Y) behavior = behavior := by
  induction behavior using Quotient.inductionOn with
  | _ law =>
      exact congrArg ofProb (Subtype.ext (PFunPDS.relabel_refl law.val))

/-- The inverse relabelling undoes the relabelling on strict behavior. -/
theorem relabel_symm_relabel (e : X ≃ X') (f : Y ≃ Y')
    (behavior : System X Y) :
    relabel e.symm f.symm (relabel e f behavior) = behavior := by
  rw [relabel_relabel, Equiv.self_trans_symm, Equiv.self_trans_symm,
    relabel_refl]

/-- The relabelling undoes the inverse relabelling on strict behavior. -/
theorem relabel_relabel_symm (e : X ≃ X') (f : Y ≃ Y')
    (behavior : System X' Y') :
    relabel e f (relabel e.symm f.symm behavior) = behavior := by
  rw [relabel_relabel, Equiv.symm_trans_self, Equiv.symm_trans_self,
    relabel_refl]

/-- **Relabelling is injective on strict behavior.**  Together with
`System.edist_relabel` this is what carries the strict cancellation theorem
(`System.parallel_inj`) and the metric across a boundary transport that is
only an isomorphism of alphabets rather than an equality of them — the
equality-only transport this replaced could do neither for such a
boundary. -/
theorem relabel_inj (e : X ≃ X') (f : Y ≃ Y') {left right : System X Y}
    (h : relabel e f left = relabel e f right) : left = right := by
  have transported := congrArg (relabel e.symm f.symm) h
  rwa [relabel_symm_relabel, relabel_symm_relabel] at transported

/-- Relabelling is a bijection on strict behavior; its inverse is the
relabelling along the inverse equivalences. -/
def relabelEquiv (e : X ≃ X') (f : Y ≃ Y') : System X Y ≃ System X' Y' where
  toFun := relabel e f
  invFun := relabel e.symm f.symm
  left_inv := relabel_symm_relabel e f
  right_inv := relabel_relabel_symm e f

end System

end StrictContext

end

end RandomSystems.CR18
