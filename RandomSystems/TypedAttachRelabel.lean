/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedInterfaceRelabel

/-!
# Renaming interfaces commutes with attaching a converter

`TypedInterfaceRelabel.lean` installs the action of a bijection of the
interface set on the bundled carrier (`Resource.relabelInterfaces`) and shows
it is an isometry.  This module proves that the action is also *equivariant
for the primitives*: renaming the interfaces of a resource and then attaching
a converter at the renamed interface is attaching the converter first and
renaming afterwards (`Resource.relabelInterfaces_act`).  Because
`Primitive.act` is total — the identity when the boundary does not provide the
converter's source — and a renaming never changes which code an interface
advertises, the statement needs no side condition and no transport: the two
boundaries it compares are equal on the nose after
`relabelBoundary_replaceBoundary`.

The proof runs entirely in the **uniform ambient chart** of
`TypedAttachment.lean`, where the query alphabet is `K × AmbientInput U` and
the answer alphabet `AmbientOutput U` is boundary-independent.  Two facts
carry it:

* `DependentDDS.embed_reindex` — a bijective interface re-indexing *is* a
  plain alphabet relabelling in the chart, namely the product relabelling of
  the interface factor with the answer alphabet fixed.  Renaming interfaces
  moves no payload alphabet, so nothing but the tag travels.
* `PFunConverter.General.attachAt_relabelInterface` — CR18 Definition 3.13
  attachment commutes with that product relabelling.  This is the reusable,
  boundary-free half: it is proved by a bisimulation of the `PFun.fix` round
  (`attachResolve_relabel_mem`), then structurally along the outer driver.

The remaining layers (`DependentPDS`, the contextual quotient, the bundled
carrier) are the standard `Dist.fTransform` / `Quotient.inductionOn` lifts,
with the single boundary transport supplied by
`DependentDDS.heq_of_boundary_eq_of_embed_eq` and its companions.
-/

namespace RandomSystems.CR18

noncomputable section

universe uP uP' uX uY iK iK'

/-- The companion of `PFunDDS.output_congr`: that one holds the system fixed
and varies the history, this one holds the history fixed and varies the
system.  Both exist for the same reason — the in-domain proof is an argument
of `output`, so a plain `rw` on either side hits a dependent motive.

CONSOLIDATE: `RandomSystems.CR18.PFunConverter.output_congr_system`
(`CombineRealization.lean`) is the same statement with the second membership
proof transported rather than given; that module is not in this one's import
closure, and the shared home for both is `PFunDDS.lean`, beside
`PFunDDS.output_congr`. -/
theorem PFunDDS.output_congr_system {X : Type uX} {Y : Type uY}
    {left right : PFunDDS.DDS X Y} (same : left = right) (history : List X)
    (leftMember : history ∈ PFunDDS.dom left)
    (rightMember : history ∈ PFunDDS.dom right) :
    PFunDDS.output left history leftMember =
      PFunDDS.output right history rightMember := by
  subst same
  rfl

namespace PFunConverter.General

open PFunConverter DDC

variable {P : Type uP} {P' : Type uP'} {X : Type uX} {Y : Type uY}
variable [DecidableEq P] [DecidableEq P']

omit [DecidableEq P] [DecidableEq P'] in
/-- The completed (`s⊥`) answer to a query is blind to an interface renaming:
the renamed resource, asked at `π k` after the renamed history, returns
exactly what the original returns at `k` after the original history.  This is
`PFunDDS.output_fullyDefined_relabel` specialised to the renaming pair and
with the `List.map`/`++` bookkeeping already done, which is the form the
attachment fixpoint consumes. -/
theorem output_fullyDefined_relabelInterface (π : P ≃ P')
    (s : PFunDDS.Resource P X Y) (history : List (P × X)) (entry : P × X) :
    PFunDDS.output
        (PFunDDS.fullyDefined
          (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s))
        (history.map ⇑(π.prodCongr (Equiv.refl X)) ++ [(π entry.1, entry.2)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      PFunDDS.output (PFunDDS.fullyDefined s) (history ++ [entry])
        (by rw [PFunDDS.dom_fullyDefined]; simp) := by
  have shape : (history ++ [entry]).map ⇑(π.prodCongr (Equiv.refl X)) =
      history.map ⇑(π.prodCongr (Equiv.refl X)) ++ [(π entry.1, entry.2)] := by
    cases entry
    simp [Prod.map]
  have transported := PFunDDS.output_fullyDefined_relabel
    (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s (history ++ [entry])
    (by simp)
  rw [← PFunDDS.output_congr _ shape (by rw [PFunDDS.dom_fullyDefined]; simp)
    (by rw [PFunDDS.dom_fullyDefined]; simp), transported]
  cases PFunDDS.output (PFunDDS.fullyDefined s) (history ++ [entry])
      (by rw [PFunDDS.dom_fullyDefined]; simp) <;> rfl

omit [DecidableEq P] [DecidableEq P'] in
/-- **One converter round is a bisimulation across an interface renaming.**
The state of a round is `(α-history, resource-history)`; renaming acts on the
second component only, and every `attachStep` move is reproduced verbatim —
`α`'s next move reads only the first component, and the answer it is fed is
the same by `output_fullyDefined_relabelInterface`.  Proved by
`PFun.fixInduction`, which is why this is a membership implication rather than
an equation; the equation is `attachResolve_relabelInterface`. -/
theorem attachResolve_relabel_mem (π : P ≃ P') (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y)
    {state : List (CIn X Y) × List (P × X)}
    {result : Y × (List (CIn X Y) × List (P × X))}
    (member : result ∈ attachResolve i α s state) :
    (result.1, (result.2.1, result.2.2.map ⇑(π.prodCongr (Equiv.refl X)))) ∈
      attachResolve (π i) α
        (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s)
        (state.1, state.2.map ⇑(π.prodCongr (Equiv.refl X))) := by
  refine PFun.fixInduction member
    (C := fun current =>
      (result.1, (result.2.1, result.2.2.map ⇑(π.prodCongr (Equiv.refl X)))) ∈
        attachResolve (π i) α
          (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s)
          (current.1, current.2.map ⇑(π.prodCongr (Equiv.refl X)))) ?_
  intro current fixed induction
  rw [PFun.mem_fix_iff] at fixed
  rcases fixed with stopped | ⟨next, stepped, _continued⟩
  · rw [attachStep_mem_inl] at stopped
    rw [stopped.2]
    exact attachResolve_out (π i) α _ stopped.1
  · have step := stepped
    rw [attachStep_mem_inr] at step
    obtain ⟨query, queryMember, nextEquation⟩ := step
    rw [attachResolve_in (π i) α _ queryMember,
      output_fullyDefined_relabelInterface π s current.2 (i, query)]
    have goalNext := induction next stepped
    rw [nextEquation] at goalNext
    obtain ⟨answer, answerEquation⟩ :
        ∃ answer, PFunDDS.output (PFunDDS.fullyDefined s)
          (current.2 ++ [(i, query)])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = answer := ⟨_, rfl⟩
    rw [answerEquation] at goalNext ⊢
    cases answer <;>
      simpa only [List.map_append, List.map_cons, List.map_nil] using goalNext

omit [DecidableEq P] [DecidableEq P'] in
/-- The round of `attachResolve` at the renamed interface **is** the original
round, with its recorded resource history renamed.  The reverse membership
comes free from `attachResolve_relabel_mem` at `π.symm`, since a renaming is
invertible — which is exactly what a merge of interfaces would not give. -/
theorem attachResolve_relabelInterface (π : P ≃ P') (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (state : List (CIn X Y) × List (P × X)) :
    attachResolve (π i) α
        (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s)
        (state.1, state.2.map ⇑(π.prodCongr (Equiv.refl X))) =
      (attachResolve i α s state).map
        (fun round =>
          (round.1, (round.2.1,
            round.2.2.map ⇑(π.prodCongr (Equiv.refl X))))) := by
  have roundTrip : PFunDDS.DDS.relabel (π.symm.prodCongr (Equiv.refl X))
      (Equiv.refl Y)
      (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s) = s :=
    PFunDDS.DDS.relabel_symm_relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s
  have cancel : ∀ history : List (P × X),
      (history.map ⇑(π.prodCongr (Equiv.refl X))).map
        ⇑(π.symm.prodCongr (Equiv.refl X)) = history := fun history => by
    rw [List.map_map,
      show ⇑(π.symm.prodCongr (Equiv.refl X)) ∘ ⇑(π.prodCongr (Equiv.refl X)) = id from
        Equiv.symm_comp_self (π.prodCongr (Equiv.refl X)),
      List.map_id]
  have cancel' : ∀ history : List (P' × X),
      (history.map ⇑(π.symm.prodCongr (Equiv.refl X))).map
        ⇑(π.prodCongr (Equiv.refl X)) = history := fun history => by
    rw [List.map_map,
      show ⇑(π.prodCongr (Equiv.refl X)) ∘ ⇑(π.symm.prodCongr (Equiv.refl X)) = id from
        Equiv.self_comp_symm (π.prodCongr (Equiv.refl X)),
      List.map_id]
  apply Part.ext
  intro round
  rw [Part.mem_map_iff]
  constructor
  · intro member
    refine ⟨(round.1, (round.2.1,
      round.2.2.map ⇑(π.symm.prodCongr (Equiv.refl X)))), ?_, ?_⟩
    · have back := attachResolve_relabel_mem π.symm (π i) α _ member
      rw [roundTrip, Equiv.symm_apply_apply] at back
      rw [cancel] at back
      exact back
    · rw [cancel']
  · rintro ⟨earlier, member, rfl⟩
    exact attachResolve_relabel_mem π i α s member

/-- One outer driver entry transports: an entry at `π i` still runs the
converter's round (`π` is injective, so a renamed entry hits the attachment
point iff the original did), and every other entry still passes straight
through to the renamed resource. -/
theorem attachEntryStep_relabelInterface (π : P ≃ P') (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) (state : List (CIn X Y) × List (P × X))
    (entry : P × X) :
    attachEntryStep (π i) α
        (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s)
        (state.1, state.2.map ⇑(π.prodCongr (Equiv.refl X)))
        (π entry.1, entry.2) =
      (attachEntryStep i α s state entry).map
        (fun round =>
          (round.1, (round.2.1,
            round.2.2.map ⇑(π.prodCongr (Equiv.refl X))))) := by
  have shape : (state.2 ++ [entry]).map ⇑(π.prodCongr (Equiv.refl X)) =
      state.2.map ⇑(π.prodCongr (Equiv.refl X)) ++ [(π entry.1, entry.2)] := by
    cases entry
    simp [Prod.map]
  by_cases same : entry.1 = i
  · rw [attachEntryStep, attachEntryStep, if_pos (congrArg π same), if_pos same]
    exact attachResolve_relabelInterface π i α s
      (state.1 ++ [Sum.inl (InLabel.outside, entry.2)], state.2)
  · rw [attachEntryStep, attachEntryStep,
      if_neg (fun collapse => same (π.injective collapse)), if_neg same,
      PFunDDS.DDS.relabel_raw, ← shape, List.map_map, Equiv.symm_comp_self,
      List.map_id, Part.map_map]
    rfl

/-- The complete CR18 Definition 3.13 driver transports, by induction along
the outside history: outputs are untouched, and the threaded state is renamed
in its resource component. -/
theorem attachDrive_relabelInterface (π : P ≃ P') (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) :
    ∀ (outside : List (P × X)) (state : List (CIn X Y) × List (P × X)),
      attachDrive (π i) α
          (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s)
          (state.1, state.2.map ⇑(π.prodCongr (Equiv.refl X)))
          (outside.map ⇑(π.prodCongr (Equiv.refl X))) =
        (attachDrive i α s state outside).map
          (fun round =>
            (round.1, (round.2.1,
              round.2.2.map ⇑(π.prodCongr (Equiv.refl X))))) := by
  intro outside
  induction outside with
  | nil => intro state; simp [attachDrive]
  | cons entry rest induction =>
      intro state
      obtain ⟨entryInterface, entryValue⟩ := entry
      rw [List.map_cons, attachDrive, attachDrive,
        show ⇑(π.prodCongr (Equiv.refl X)) (entryInterface, entryValue) =
          (π (entryInterface, entryValue).1, (entryInterface, entryValue).2) from rfl,
        attachEntryStep_relabelInterface, Part.bind_map, Part.map_bind]
      refine congrArg (Part.bind _) (funext fun round => ?_)
      rw [induction round.2, Part.map_map, Part.map_map]
      rfl

/-- **Attaching a converter commutes with renaming the interfaces of the
resource** (CR18 Definition 3.13, fixed-alphabet chart).  A bijection `π` of
the interface set acts on a `(P × X, Y)`-resource by relabelling the interface
factor of its query alphabet and nothing else; attaching `α` at `π i` of the
renamed resource is the renaming of `α` attached at `i`.

This is the boundary-free half of `Resource.relabelInterfaces_act`, and it is
stated for an arbitrary stateful DDC — no converter subclass, no typing
assumption on the resource.  It is the re-addressing analogue of
`attachAt_comm`: that one says two attachments at *distinct* interfaces do not
see each other, this one says an attachment does not see the *names* of the
interfaces at all. -/
theorem attachAt_relabelInterface (π : P ≃ P') (i : P) (α : DDC X Y X Y)
    (s : PFunDDS.Resource P X Y) :
    attachAt (π i) α
        (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s) =
      PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y)
        (attachAt i α s) := by
  apply Subtype.ext
  funext history
  obtain ⟨original, rfl⟩ : ∃ original : List (P × X),
      original.map ⇑(π.prodCongr (Equiv.refl X)) = history :=
    ⟨history.map ⇑(π.symm.prodCongr (Equiv.refl X)), by
      rw [List.map_map,
        show ⇑(π.prodCongr (Equiv.refl X)) ∘
            ⇑(π.symm.prodCongr (Equiv.refl X)) = id from
          Equiv.self_comp_symm (π.prodCongr (Equiv.refl X)),
        List.map_id]⟩
  rw [PFunDDS.DDS.relabel_raw, List.map_map,
    show ⇑(π.prodCongr (Equiv.refl X)).symm ∘
        ⇑(π.prodCongr (Equiv.refl X)) = id from
      Equiv.symm_comp_self (π.prodCongr (Equiv.refl X)),
    List.map_id]
  have drive := attachDrive_relabelInterface π i α s original ([], [])
  simp only [List.map_nil] at drive
  show attachRaw (π i) α
      (PFunDDS.DDS.relabel (π.prodCongr (Equiv.refl X)) (Equiv.refl Y) s)
      (original.map ⇑(π.prodCongr (Equiv.refl X))) =
    Part.map ⇑(Equiv.refl Y) (attachRaw i α s original)
  simp only [attachRaw]
  rw [drive, Part.bind_map, Part.map_bind]
  refine congrArg (Part.bind _) (funext fun round => ?_)
  cases round.1.getLast? <;> simp

end PFunConverter.General

namespace TypedResource

variable {U : SignatureUniverse} {K : Type iK} {K' : Type iK'}

/-- **The ambient chart does not see an interface renaming at all.**  A flat
answer is coded by the signature its interface advertises, and a renaming
leaves that signature alone — so the two encodings coincide on the nose. -/
theorem encodeAnswer_relabelAnswerEquiv (relabel : K ≃ K')
    (boundary : Boundary U K) (answer : FlatAnswer U boundary) :
    encodeAnswer (relabelAnswerEquiv relabel boundary answer) =
      encodeAnswer answer := by
  obtain ⟨interface, value⟩ := answer
  have rebuild : ∀ (code code' : U.Code) (same : code = code')
      (payload : U.output code),
      (⟨code', cast (congrArg U.output same) payload⟩ : AmbientOutput U) =
        ⟨code, payload⟩ := by
    intro code code' same payload
    cases same
    rfl
  exact rebuild _ _ (relabelBoundary_apply relabel boundary interface).symm value

/-- Decoding a uniform query and then renaming its interface is decoding the
renamed uniform query: both sides transport the same payload along proofs of
the same code equation, so proof irrelevance closes the square. -/
theorem relabelQueryEquiv_decodeQuery (relabel : K ≃ K')
    (boundary : Boundary U K) (query : AmbientQuery K U)
    (conforms : QueryConforms boundary query)
    (renamedConforms : QueryConforms (relabelBoundary relabel boundary)
      (relabel.prodCongr (Equiv.refl (AmbientInput U)) query)) :
    relabelQueryEquiv relabel boundary (decodeQuery boundary query conforms) =
      decodeQuery (relabelBoundary relabel boundary)
        (relabel.prodCongr (Equiv.refl (AmbientInput U)) query)
        renamedConforms := by
  obtain ⟨interface, code, value⟩ := query
  change code = boundary interface at conforms
  subst code
  rfl

/-- Conformance to the renamed boundary is conformance to the original one:
the renamed interface advertises exactly the code its original advertised. -/
theorem queryConforms_relabelInterfaces (relabel : K ≃ K')
    (boundary : Boundary U K) (query : AmbientQuery K U) :
    QueryConforms (relabelBoundary relabel boundary)
        (relabel.prodCongr (Equiv.refl (AmbientInput U)) query) ↔
      QueryConforms boundary query := by
  obtain ⟨interface, payload⟩ := query
  change payload.1 = boundary (relabel.symm (relabel interface)) ↔
    payload.1 = boundary interface
  rw [relabel.symm_apply_apply]

/-- …and the same holds along a whole uniform history. -/
theorem historyConforms_relabelInterfaces (relabel : K ≃ K')
    (boundary : Boundary U K) (history : List (AmbientQuery K U)) :
    HistoryConforms (relabelBoundary relabel boundary)
        (history.map ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U)))) ↔
      HistoryConforms boundary history := by
  constructor
  · intro conforms query member
    exact (queryConforms_relabelInterfaces relabel boundary query).mp
      (conforms _ (List.mem_map_of_mem member))
  · intro conforms renamed member
    rw [List.mem_map] at member
    obtain ⟨query, member, rfl⟩ := member
    exact (queryConforms_relabelInterfaces relabel boundary query).mpr
      (conforms query member)

/-- Decoding the renamed uniform history is renaming the decoded history. -/
theorem decodeHistory_relabelInterfaces (relabel : K ≃ K')
    (boundary : Boundary U K) :
    ∀ (history : List (AmbientQuery K U))
      (conforms : HistoryConforms boundary history)
      (renamedConforms : HistoryConforms (relabelBoundary relabel boundary)
        (history.map ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))))),
      decodeHistory (relabelBoundary relabel boundary)
          (history.map ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))))
          renamedConforms =
        (decodeHistory boundary history conforms).map
          ⇑(relabelQueryEquiv relabel boundary) := by
  intro history
  induction history with
  | nil => intro _ _; rfl
  | cons query rest induction =>
      intro conforms renamedConforms
      simp only [List.map_cons, decodeHistory]
      refine congrArg₂ List.cons ?_ (induction _ _)
      exact (relabelQueryEquiv_decodeQuery relabel boundary query _ _).symm

/-- **A bijective interface re-indexing is a plain alphabet relabelling in the
uniform ambient chart.**  Renaming interfaces moves neither the input nor the
output alphabet — `AmbientQuery K U = K × AmbientInput U` and `AmbientOutput U`
are both boundary-independent — so the whole re-indexing is the product
relabelling of the interface factor, with the answer alphabet fixed.  This is
the seam through which every ambient-chart theorem (attachment, in particular)
reaches a re-indexed resource. -/
theorem DependentDDS.embed_reindex (relabel : K ≃ K')
    {boundary : Boundary U K} (system : DependentDDS U boundary) :
    (system.reindex (tagCompatible_relabelInterfaces relabel boundary)).embed =
      PFunDDS.DDS.relabel (relabel.prodCongr (Equiv.refl (AmbientInput U)))
        (Equiv.refl (AmbientOutput U)) system.embed := by
  apply Subtype.ext
  funext ambient
  obtain ⟨history, rfl⟩ : ∃ history : List (AmbientQuery K U),
      history.map ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))) = ambient :=
    ⟨ambient.map ⇑(relabel.symm.prodCongr (Equiv.refl (AmbientInput U))), by
      rw [List.map_map,
        show ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))) ∘
            ⇑(relabel.symm.prodCongr (Equiv.refl (AmbientInput U))) = id from
          Equiv.self_comp_symm (relabel.prodCongr (Equiv.refl (AmbientInput U))),
        List.map_id]⟩
  rw [PFunDDS.DDS.relabel_raw, List.map_map,
    show ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))).symm ∘
        ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))) = id from
      Equiv.symm_comp_self (relabel.prodCongr (Equiv.refl (AmbientInput U))),
    List.map_id]
  apply Part.ext'
  · change EmbeddedDomain
        (system.reindex (tagCompatible_relabelInterfaces relabel boundary))
        (history.map ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U)))) ↔
      EmbeddedDomain system history
    constructor
    · rintro ⟨renamedConforms, member⟩
      refine ⟨(historyConforms_relabelInterfaces relabel boundary history).mp
        renamedConforms, fun conforms => ?_⟩
      have decoded : (decodeHistory boundary history conforms).map
          ⇑(relabelQueryEquiv relabel boundary) ∈
            PFunDDS.dom (PFunDDS.DDS.relabel
              (relabelQueryEquiv relabel boundary)
              (relabelAnswerEquiv relabel boundary) system.flatten) := by
        rw [← decodeHistory_relabelInterfaces relabel boundary history conforms
          renamedConforms]
        exact member renamedConforms
      rwa [PFunDDS.DDS.mem_dom_relabel, List.map_map, Equiv.symm_comp_self,
        List.map_id] at decoded
    · rintro ⟨conforms, member⟩
      refine ⟨(historyConforms_relabelInterfaces relabel boundary history).mpr
        conforms, fun renamedConforms => ?_⟩
      show decodeHistory (relabelBoundary relabel boundary) _ renamedConforms ∈
        PFunDDS.dom (PFunDDS.DDS.relabel (relabelQueryEquiv relabel boundary)
          (relabelAnswerEquiv relabel boundary) system.flatten)
      rw [decodeHistory_relabelInterfaces relabel boundary history conforms
          renamedConforms,
        PFunDDS.DDS.mem_dom_relabel, List.map_map, Equiv.symm_comp_self,
        List.map_id]
      exact member conforms
  · intro left right
    change encodeAnswer (PFunDDS.output
        (system.reindex (tagCompatible_relabelInterfaces relabel boundary)).flatten
        (decodeHistory (relabelBoundary relabel boundary)
          (history.map ⇑(relabel.prodCongr (Equiv.refl (AmbientInput U))))
          left.1)
        (left.2 left.1)) =
      encodeAnswer (PFunDDS.output system.flatten
        (decodeHistory boundary history right.1) (right.2 right.1))
    rw [PFunDDS.output_congr_system
        (DependentDDS.flatten_reindex
          (tagCompatible_relabelInterfaces relabel boundary) system) _
        (left.2 left.1) (left.2 left.1),
      PFunDDS.DDS.output_relabel, encodeAnswer_relabelAnswerEquiv]
    refine congrArg encodeAnswer (PFunDDS.output_congr system.flatten ?_ _ _)
    rw [decodeHistory_relabelInterfaces relabel boundary history
        ((historyConforms_relabelInterfaces relabel boundary history).mp left.1)
        left.1,
      List.map_map, Equiv.symm_comp_self, List.map_id]

section Attach

variable [DecidableEq K] [DecidableEq K'] [DecidableEq U.Code]

omit [DecidableEq U.Code] in
/-- Renaming the interfaces of a boundary and then changing the code at the
renamed interface is changing the code at the original interface and then
renaming.  This is the one boundary transport the whole file needs. -/
theorem relabelBoundary_replaceBoundary (relabel : K ≃ K')
    (boundary : Boundary U K) (interface : K) (code : U.Code) :
    relabelBoundary relabel (replaceBoundary boundary interface code) =
      replaceBoundary (relabelBoundary relabel boundary) (relabel interface)
        code := by
  funext renamed
  by_cases same : renamed = relabel interface
  · subst same
    show replaceBoundary boundary interface code
      (relabel.symm (relabel interface)) = _
    rw [Equiv.symm_apply_apply, replace_boundary_same, replace_boundary_same]
  · show replaceBoundary boundary interface code (relabel.symm renamed) = _
    rw [replace_boundary_ne _ same,
      replace_boundary_ne boundary (fun collapse => same (by
        rw [← collapse, Equiv.apply_symm_apply]))]

/-- **Renaming interfaces commutes with attaching a converter — deterministic
level, read in the ambient chart.**  Both sides land at boundaries that are
equal but not definitionally so; the ambient chart is boundary-independent, so
this equation is the whole mathematical content, and the transport is supplied
once and for all by `relabelBoundary_replaceBoundary`. -/
theorem DependentDDS.embed_reindex_attach {source target : U.Code}
    (relabel : K ≃ K') (interface : K)
    (converter : DeterministicConverter U source target)
    {boundary : Boundary U K} (sourceMatches : boundary interface = source)
    (renamedMatches :
      relabelBoundary relabel boundary (relabel interface) = source)
    (system : DependentDDS U boundary) :
    ((system.attach interface converter sourceMatches).reindex
        (tagCompatible_relabelInterfaces relabel
          (replaceBoundary boundary interface target))).embed =
      ((system.reindex
          (tagCompatible_relabelInterfaces relabel boundary)).attach
        (relabel interface) converter renamedMatches).embed := by
  rw [DependentDDS.embed_reindex, DependentDDS.embed_attach,
    DependentDDS.embed_attach]
  unfold DeterministicConverter.attachAmbient
  rw [DependentDDS.embed_reindex]
  exact (PFunConverter.General.attachAt_relabelInterface relabel interface
    converter.embeddedDDC system.embed).symm

/-- The same square one layer up, on native finite-support laws. -/
theorem DependentPDS.embed_reindex_attach {source target : U.Code}
    (relabel : K ≃ K') (interface : K)
    (converter : DeterministicConverter U source target)
    {boundary : Boundary U K} (sourceMatches : boundary interface = source)
    (renamedMatches :
      relabelBoundary relabel boundary (relabel interface) = source)
    (law : DependentPDS U boundary) :
    DependentPDS.embed (DependentPDS.reindex
        (tagCompatible_relabelInterfaces relabel
          (replaceBoundary boundary interface target))
        (DependentPDS.attach interface converter sourceMatches law)) =
      DependentPDS.embed (DependentPDS.attach (relabel interface) converter
        renamedMatches
        (DependentPDS.reindex
          (tagCompatible_relabelInterfaces relabel boundary) law)) := by
  unfold DependentPDS.embed DependentPDS.reindex DependentPDS.attach
  rw [Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp,
    Dist.fTransform_comp]
  exact congrArg (fun step => Dist.fTransform step law)
    (funext fun deterministic =>
      DependentDDS.embed_reindex_attach relabel interface converter
        sourceMatches renamedMatches deterministic)

/-- **Renaming interfaces commutes with attaching a converter — behavioral
level.**  The two contextual classes sit at the two boundaries identified by
`relabelBoundary_replaceBoundary`, so the statement is heterogeneous; its
content is the ambient-chart equation. -/
theorem DependentRandomSystem.heq_reindex_attach {source target : U.Code}
    (relabel : K ≃ K') (interface : K)
    (converter : DeterministicConverter U source target)
    {boundary : Boundary U K} (sourceMatches : boundary interface = source)
    (renamedMatches :
      relabelBoundary relabel boundary (relabel interface) = source)
    (behavior : DependentRandomSystem U boundary) :
    HEq
      (DependentRandomSystem.reindex
        (tagCompatible_relabelInterfaces relabel
          (replaceBoundary boundary interface target))
        (DependentRandomSystem.attach interface converter sourceMatches
          behavior))
      (DependentRandomSystem.attach (relabel interface) converter
        renamedMatches
        (DependentRandomSystem.reindex
          (tagCompatible_relabelInterfaces relabel boundary) behavior)) := by
  induction behavior using Quotient.inductionOn with
  | _ law =>
      apply DependentRandomSystem.of_prob_heq_of_boundary_eq
        (relabelBoundary_replaceBoundary relabel boundary interface target)
      apply DependentPDS.Prob.heq_of_boundary_eq_of_val_heq
        (relabelBoundary_replaceBoundary relabel boundary interface target)
      exact DependentPDS.heq_of_boundary_eq_of_embed_eq
        (relabelBoundary_replaceBoundary relabel boundary interface target)
        (DependentPDS.embed_reindex_attach relabel interface converter
          sourceMatches renamedMatches law.val)

/-- **Renaming the interfaces of a resource commutes with attaching a
converter at one of them.**  `Primitive.act` is total — it is the identity
when the boundary does not provide the converter's source — and a renaming
does not change which code an interface advertises, so the two sides agree
both when the primitive fires and when it does not, with no side condition and
no transport in the statement. -/
theorem Resource.relabelInterfaces_act (relabel : K ≃ K')
    {source target : U.Code}
    (converter : DeterministicConverter U source target) (interface : K)
    (resource : Resource K U) :
    Resource.relabelInterfaces relabel
        ((Primitive.mk source target converter :
            Primitive K U interface).act resource) =
      (Primitive.mk source target converter :
          Primitive K' U (relabel interface)).act
        (Resource.relabelInterfaces relabel resource) := by
  rcases resource with ⟨boundary, behavior⟩
  by_cases sourceMatches : boundary interface = source
  · have renamedMatches :
        relabelBoundary relabel boundary (relabel interface) = source :=
      (relabelBoundary_apply relabel boundary interface).trans sourceMatches
    rw [Primitive.act_of_matches _ boundary sourceMatches]
    show Resource.mk _ _ =
      (Primitive.mk source target converter :
        Primitive K' U (relabel interface)).act
          (Resource.mk (relabelBoundary relabel boundary) _)
    rw [Primitive.act_of_matches _ (relabelBoundary relabel boundary)
      renamedMatches, Resource.mk.injEq]
    exact ⟨relabelBoundary_replaceBoundary relabel boundary interface target,
      DependentRandomSystem.heq_reindex_attach relabel interface converter
        sourceMatches renamedMatches behavior⟩
  · have renamedMismatch :
        relabelBoundary relabel boundary (relabel interface) ≠ source :=
      fun collapse => sourceMatches
        ((relabelBoundary_apply relabel boundary interface).symm.trans collapse)
    rw [Primitive.act_of_not_matches _ boundary sourceMatches]
    show Resource.mk _ _ =
      (Primitive.mk source target converter :
        Primitive K' U (relabel interface)).act
          (Resource.mk (relabelBoundary relabel boundary) _)
    rw [Primitive.act_of_not_matches _ (relabelBoundary relabel boundary)
      renamedMismatch]

end Attach

end TypedResource

end

end RandomSystems.CR18

#print axioms RandomSystems.CR18.TypedResource.Resource.relabelInterfaces_act
